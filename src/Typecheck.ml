(* The purpose of this module is type checking, type inferrence *)

open GT
open Language
open Language.Typing

(* Context *)
module Context =
  struct

    @type ctxLayer = CtxLayer of (string * Typing.t) list with show, html

    (* Context: initial (empty), scope context *)
    @type t =
    | ZeroCtx
    | SuccCtx of ctxLayer * t
    with show, html
    (* Q: Why not just list of string * Typing.t?
       A: Because of redefinitions control! *)

    (* Get the depth level of a state *)
    let rec level = function
    | ZeroCtx         -> 0
    | SuccCtx (_, st) -> 1 + level st

    (* 26.26 -- List operations
       https://ocaml.org/releases/4.11/ocaml-4.11-refman.pdf *)
    let rec get_type ctx name
      = match ctx with
        | ZeroCtx               -> TAny  (* Dilemma: it is either error, or this name can be external symbol *)
        | SuccCtx (CtxLayer scope, ctx') ->
          match List.assoc_opt name scope with
          | None        -> get_type ctx' name (* Try to find type in upper instances *)
          | Some typing -> typing            (* Or return found one *)


    let extend_layer, extend =
      (* Extend one context layer with the typing information: the [name] has the type [typing] *)
      let extend_layer ctx_layer name typing
        = match ctx_layer with
          | CtxLayer ctx_layer ->
            match List.find_opt (fun (pname, _) -> pname = name ) ctx_layer with
            | None               -> CtxLayer (List.cons (name, typing) ctx_layer) (* Successfully added type to scope *)
            | Some ((_, typing)) -> report_error ~loc:(Loc.get name) ("redefinition of typing for " ^ name ^ " in the same scope")
      in
      (* Extend current typing scope with the typing information: the [name] has the type [typing] *)
      let extend ctx name typing
        = match ctx with
          | ZeroCtx                   -> report_error("FATAL. Cannot add type to empty context! Should be created context scope.")
          | SuccCtx (ctx_layer, ctx') -> SuccCtx (extend_layer ctx_layer name typing, ctx') (* Added type to layer *)

      in extend_layer, extend

    (* Expand context when entering scope. Thus typings can be reassigned *)
    let expand ctx = SuccCtx(CtxLayer [], ctx)
    let expandWith ctx_layer ctx = SuccCtx(ctx_layer, ctx)

  end


module Conformity =
  struct
    let tru, fls = Expr.Const 1, Expr.Const 0
    let tmp_name = "tmp" (* name for variable that stores everything *)
    let loc = (0, 0) (* TODO need to know real location, not fake one *)


    (* check that type 'lhs' can be used as type 'rhs': "lhs conforms rhs"
       returns boolean (conformity) of two types *)
    let rec conforms lhs rhs
      = match (lhs, rhs) with
      | (_   , TAny) -> true
      | (TAny, _   ) -> true
      | (TArr l, TArr r)
      | (TRef l, TRef r) -> conforms l r
      | (TSexp(name_l, types_l), TSexp(name_r, types_r)) ->    name_l = name_r
                                                            && List.length types_l = List.length types_r
                                                            && List.compare_lengths types_l types_r == 0
                                                            && List.for_all2 conforms types_l types_r
      (* Note: right now implemented as CONTRAVARIANT by the arguments *)
      | (TLambda(args_l, body_l), TLambda(args_r, body_r)) ->
                    List.compare_lengths args_l args_r == 0
                 && List.for_all2 conforms args_r args_l
                 && conforms body_l body_r

                                 (* For all lel \in ls Exists rel \in rs such that `conforms lel rel` *)
      | (TUnion ls, TUnion rs) -> List.for_all (fun lel -> List.exists (conforms lel) rs) ls
      | (tl       , TUnion rs) -> List.exists (conforms tl) rs
      | (TUnion ls, tr       ) -> List.for_all (fun tl ->  conforms tl tr) ls

      | (l, r) -> l = r (* TString, TConst, TVoid *)

    (* This function generates dynamic code check for target type 'ttype' with input open variable 'name' *)
    let rec plain_gen name ttype =
      match ttype with
      | TAny    -> tru (* OK, expression is of type Any *)
      | TConst  -> Expr.Case(Var(name), [(Pattern.UnBoxed,   tru); (Pattern.Wildcard, fls)], loc, Expr.Val)
      | TString -> Expr.Case(Var(name), [(Pattern.StringTag, tru); (Pattern.Wildcard, fls)], loc, Expr.Val)
      | TArr t     (* TODO think about making loop *)
      | TRef t  -> Expr.Case(Var(name), [(Pattern.ArrayTag,  tru); (Pattern.Wildcard, fls)], loc, Expr.Val)
      (* For lambdas we can only check that incoming object is really a function
         It seems that there is NO WAY to check amount of args and return type in runtime.
         Even more, function can accept value of any type by design *)
      | TLambda (_, _) -> Expr.Case(Var(name), [(Pattern.ClosureTag, tru); (Pattern.Wildcard, fls)], loc, Expr.Val)
      | TSexp(name, types) ->
             (* Generate names for new closure *)
             let gen_names = List.mapi (fun i _ -> Printf.sprintf "gen_%d" i) types in
             let gen_names_patterns = List.map (fun name -> Pattern.Named(name, Pattern.Wildcard)) gen_names in
             (* This one is generated AST's binded by '&&' binary operation *)
             let ast = List.fold_right2 (fun nm typ bool -> Expr.Binop("&&", plain_gen nm typ, bool)) gen_names types tru in
             (* Insert check in case body *)
             Expr.Case(Var(name), [(Pattern.Sexp(name, gen_names_patterns), ast); (Pattern.Wildcard, fls)], loc, Expr.Val)
      | TUnion(types) -> List.fold_right (fun typ els -> Expr.If(plain_gen name typ, tru, els)) types fls
      | TVoid   -> tru (* Not sure what to do with no real value :) *)

    (* Function inserts dynamic cast code for checking that 'expr' having known type 'lhs' would be casted to 'rhs' at runtime
       Returns Some expression on successfull cast, and None otherwise *)
    let generate_cast expr lhs rhs =
      (* Wrap check if needed with apropriate anonymous function call *)
      let var_name = "expr" in
      if conforms lhs rhs
      then
        if rhs = TAny
        (* lhs conforms rhs, but check is trivial *)
        then Some(expr)
        (* lhs conforms rhs with nontrivial check *)
        else
          let expr_checker = plain_gen var_name rhs in
          Some (
            Expr.Call(
              Expr.Lambda([var_name],
                Expr.Seq(
                  Expr.Ignore(
                    Expr.If(expr_checker, (* initiate checking *)
                          Skip,           (* if checker returns true, that's OK runtime expression *)
                          Expr.Call(Expr.Var("failure"),
                          [
                            Expr.String "Dynamic cast failed of expression \"%s\" to type \"%s\"!";
                            Expr.StringVal(Expr.Var(var_name));
                            Expr.String (show(Typing.t) rhs)
                          ])))
                , Expr.Var(var_name))) (* return value after check *)
              , [expr] (* Idea: calculate expr once, isolate variables from hiding and changing inside function *)
            )
          )
      (* lhs does not conforms rhs *)
      else None

  end

open Conformity

(* Union contraction function *)
(* See also: MyPy: https://github.com/python/mypy/blob/master/mypy/join.py *)
(* PyType (PyPI) : https://github.com/google/pytype/blob/cf969bca963c56fabbf9cdc2ed39548c843979dc/pytype/pytd/pytd_utils.py#L70 *)
(* This implementation doesn't contract this: TUnion[A(TAny, Y(TConst)), A(X(TConst), TAny)] -> TUnion[A(TAny, TAny)] *)
let rec union_contraction utype =
  let rec union_contraction_pass res types = match types with
    | t :: ts -> if t = TAny
                 then [TAny]
                 else if List.exists (conforms t) ts then union_contraction_pass res ts
                 else if List.exists (conforms t) res then union_contraction_pass res ts
                 else union_contraction_pass (t :: res) ts
    | []      -> res
  in match utype with
  | TUnion (tts) -> TUnion(List.rev(union_contraction_pass [] tts))
  | _            -> report_error("Union contraction expects TUnion")

(* Infer type of one pattern (see Pattern.t in Language.ml
   Returns pair of Typing.t * ctx_layer' *)
let rec infer_pattern_type pattern =
  let empty_layer = Context.CtxLayer [] in
  match pattern with
  | Pattern.Wildcard -> (TAny, empty_layer)
  | Pattern.Sexp(name, patterns) -> let inferred_patterns = List.map infer_pattern_type patterns in
                                    let ctx_layer = List.fold_right (
                                          fun (typing, Context.CtxLayer ctx_layer) acc ->
                                            List.fold_right (fun (n, t) acc_in -> Context.extend_layer acc_in n t) ctx_layer acc
                                    ) inferred_patterns empty_layer
                                    in (TSexp (name, List.map fst inferred_patterns), ctx_layer)
  | Pattern.Array(patterns)        -> let inferred_patterns = List.map infer_pattern_type patterns in
                                      let ctx_layer = List.fold_right (
                                          fun (typing, Context.CtxLayer ctx_layer) acc ->
                                            List.fold_right (fun (n, t) acc_in -> Context.extend_layer acc_in n t) ctx_layer acc
                                      ) inferred_patterns empty_layer
                                      in (TArr(union_contraction (TUnion (List.map fst inferred_patterns))), ctx_layer)
  | Pattern.Named(name, pattern)   -> let (typing, ctx_layer) = infer_pattern_type pattern
                                      in (typing, Context.extend_layer ctx_layer name typing)
  | Pattern.Const(_)               -> (TConst, empty_layer)
  | Pattern.String(_)              -> (TString, empty_layer)
  | Pattern.Boxed                  -> (TAny, empty_layer) (* Should be smth like: TUnion [TString, TArray[TAny], TSexp("", ...)]
                                                  But we cannot express it right now.
                                                  The second option: typing like Not[TConst], but negative information
                                                  typing is even worse than introducing new constructors to data type *)
  | Pattern.UnBoxed                -> (TConst, empty_layer) (* Straightforward by interpretation of pattern matching in Language.ml *)
  | Pattern.StringTag              -> (TString, empty_layer)
  | Pattern.SexpTag                -> (TAny, empty_layer) (* See Pattern.Boxed, same issue: cannot express all Sexprs right now *)
  | Pattern.ArrayTag               -> (TArr TAny, empty_layer)
  | Pattern.ClosureTag             -> (TAny, empty_layer) (* Should be smth like: TLambda(TVariadic, TAny)
                                                    In addition it is a step forward for expressing Boxed type!
                                                    But TVariadic is hard to typecheck right now, we need to rewrite it *)

(* Function for type checking: accepts context and expression, returns it's type and new expression *)
(* TODO optimization needed: watch the type of the subtrees lazily *)
let rec type_check ctx expr
  = (* Printf.printf "Type checking \"%s\"...\n" (show(Expr.t) expr); *)
    match expr with
    | Expr.Const _               -> TConst, expr
    | Expr.Array values          -> let types, exprs = List.split( List.map (fun exp -> type_check ctx exp) values) in
                                    TArr (union_contraction (TUnion types)), Expr.Array exprs
    | Expr.String _              -> TString, expr
    | Expr.Sexp (name, subexprs) -> let types, exprs = List.split ( List.map (fun exp -> type_check ctx exp) subexprs) in
                                    TSexp(name, types), Sexp(name, exprs)
    | Expr.Var   name            -> Context.get_type ctx name, expr
    | Expr.Ref   name            -> TRef (Context.get_type ctx name), expr
    | Expr.Binop (op, exp1, exp2)-> let t1, e1 = type_check ctx exp1 in
                                    let t2, e2 = type_check ctx exp2 in
                                    if conforms t1 TConst && conforms t2 TConst
                                    then
                                      (* Already checked conformity, so we can safely match with 'Some' value *)
                                      let Some cst_e1 = generate_cast e1 t1 TConst in
                                      let Some cst_e2 = generate_cast e2 t2 TConst in
                                      TConst, Expr.Binop(op, cst_e1, cst_e2)
                                    (* TODO not enough info + NO LOCATION in 'report_error' *)
                                    else report_error("Binary operations can be applied only to integers")
    | Expr.ElemRef (arr, index) (* Both normal and inplace versions, but I don't know result type of ElemRef... *)
    | Expr.Elem (arr, index)     -> let t_arr, e_arr     = type_check ctx arr   in
                                    let t_index, e_index = type_check ctx index in
                                    if conforms t_index TConst
                                    then
                                      (* Cast index to integer and repack AST *)
                                      let Some e_index_cst = generate_cast e_index t_index TConst in
                                      let repacked_ast = match expr with
                                          | Expr.ElemRef (arr, index) -> Expr.ElemRef(arr, e_index_cst)
                                          | Expr.Elem    (arr, index) -> Expr.Elem   (arr, e_index_cst)
                                      in
                                      match t_arr with
                                           | TAny            -> TAny, repacked_ast
                                       (* Indexing to string returns char code, see ".elem" in Language.ml *)
                                           | TString         -> TConst, repacked_ast
                                           | TArr(elem_type) -> elem_type, repacked_ast
                                        (* TODO constant propagation for retrieving type like this: *)
                                        (*  | TSexp(name, typeList)  -> List.nth_opt typeList (Language.eval index []) *)

                                           | TSexp(name, type_list)  -> TUnion (type_list), repacked_ast (* Breaks type safety: UB when index out of bounds *)

                                           | _ -> report_error("Indexing can be performed on strings, arrays and S-expressions only") (* TODO NO LOCATION *)
                                    else report_error("Indexing can be done only with integers") (* TODO NO LOCATION *)
    | Expr.Length (exp)          -> let t_exp, e_exp = type_check ctx exp in
                                    let ret_type = match t_exp with
                                                   | TString | TArr(_) | TSexp(_, _) | TAny -> TConst
                                                   | _ -> report_error("Length has only strings, arrays and S-expressions")
                                    in ret_type, e_exp
    | Expr.StringVal (exp)       -> let _, e_exp = type_check ctx exp in
                                    TString, e_exp (* The most plesant rule: anything can be matched to a string *)
    | Expr.Call(f, args)         -> let t_f, e_f = type_check ctx f in
                                    let t_args, e_args = List.split (List.map (fun arg -> type_check ctx arg) args) in
                                    let rec ret_func ff =
                                      match ff with
                                      | TAny -> TAny, Expr.Call(e_f, e_args)
                                      | TLambda (premise, conclusion) ->
                                        if try List.for_all2 conforms t_args premise
                                           with Invalid_argument(_) -> report_error("Arity mismatch in function call") (* TODO NO 'TVariadic' SUPPORT *)
                                        then conclusion,  (* Each expression from t_args conform to the premise of function *)
                                             Expr.Call(e_f, List.map2 (fun (ex, tl) tr -> let Some ex_cst = generate_cast ex tl tr in ex_cst)
                                                                      (List.combine e_args t_args) premise)

                                        else report_error("Argument type mismatch in function call") (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
                                      | TUnion (ffs) -> union_contraction (TUnion (
                                                          List.filter_map (* Combine filtering and mapping at the same time *)
                                                          (* If no exception comes out, give out type as is, otherwise nothing returned *)
                                                          (fun f -> try Some (fst (ret_func f)) with _ -> None)
                                                          ffs
                                                        )), Expr.Call(e_f, e_args)
                                      | _ -> report_error("Cannot perform a call for non-callable object")
                                    in ret_func t_f
    | Expr.Assign(reff, exp)     -> let t_reff, e_reff = type_check ctx reff in
                                    let t_exp, e_exp  = type_check ctx exp  in
                                    let ret =
                                      match t_reff with
                                      | TAny -> TAny, Expr.Assign(e_reff, e_exp)
                                      | TRef (t_x) -> if conforms t_exp t_x
                                                      then
                                                        let Some e_exp_cst = generate_cast e_exp t_exp t_x in
                                                        t_x, Expr.Assign(e_reff, e_exp_cst)
                                                      else report_error("Cannot assign a value with inappropriate type")
                                    in ret
                                     (* Ignore whatever the 'step1' type is, but we still need to typecheck it! *)
    | Expr.Seq(step1, step2)         -> let _, step1_ast = type_check ctx step1 in
                                        let t, step2_ast = type_check ctx step2 in
                                        t, Expr.Seq(step1_ast, step2_ast)
    | Expr.Skip                  -> TVoid, expr                (* Skip has NO return value *)
    | Expr.If(cond, lbr, rbr)    -> let t_cond, e_cond = type_check ctx cond in
                                    let t_lbr,  e_lbr  = type_check ctx lbr  in
                                    let t_rbr,  e_rbr  = type_check ctx rbr  in
                                    if conforms t_cond TConst
                                    then
                                      let Some e_cond_cst = generate_cast e_cond t_cond TConst in
                                      union_contraction (TUnion(t_lbr :: t_rbr :: []))
                                      , Expr.If(e_cond_cst, e_lbr, e_rbr)
                                    else report_error("If condition should be logical value class") (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
    | Expr.While(cond, body)
    | Expr.Repeat(body, cond)    -> let t_cond, e_cond = type_check ctx cond in
                                    let t_body, e_body = type_check ctx body in
                                    if conforms t_cond TConst
                                    then
                                      let Some e_cond_cst = generate_cast e_cond t_cond TConst in
                                      let repacked_ast = match expr with
                                      | Expr.While (cond, body) -> Expr.While (e_cond_cst, e_body)
                                      | Expr.Repeat(body, cond) -> Expr.Repeat(e_body, e_cond_cst)
                                      in
                                      TVoid, repacked_ast (* Assumed the result type of such cycles is empty *)
                                    else report_error("Loop condition should be logical value class") (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
    (* TODO very difficult branch. But no dynamic checks needed though! *)
    | Expr.Case(match_expr, branches, loc, return_kind)
                                 -> let t_match_expr, e_match_expr = type_check ctx match_expr in
                                 (* Then, we analyze each branch in imperative style. O(n^2) * O(Complexity of confomrs) *)
                                    let len = List.length branches in
                                    let pattern_types = Array.make len TAny in
                                    let returns = Array.make len (TAny, Expr.Const 0) in
                                    for i = 0 to len - 1 do
                                      let (pattern, implementation) = (List.nth branches i) in
                                      let (pattern_type, ctx_layer) = infer_pattern_type pattern in
                                      (* Check conformity with main pattern *)
                                      if not (conforms pattern_type t_match_expr)
                                      then report_error ~loc:(Some loc) "Branch does not match anything (useless)"
                                      else begin
                                        (* Then check conformity with upper patterns *)
                                        for j = 0 to i - 1 do
                                          if conforms pattern_type pattern_types.(j)
                                          then report_error ~loc:(Some loc) "Branch is unreachable (already covered)"
                                          else ();
                                        done;
                                        (* We have useful branch here *)
                                        pattern_types.(i) <- pattern_type;
                                        returns.(i) <- type_check (Context.expandWith ctx_layer ctx) implementation
                                      end
                                    done;
                                    let return_types, e_branches_impl = List.split (Array.to_list returns) in
                                    let e_branches = List.map2 (fun (pat, _) impl -> pat, impl) branches e_branches_impl in
                                    (* Then return accumulated return types in one TUnion type *)
                                    union_contraction (TUnion(return_types))
                                    , Expr.Case(e_match_expr, e_branches, loc, return_kind)
    | Expr.Return(eopt)             -> (* TODO Return should yield the result type of inner expression (see Expr.Lambda) *)
                                       (match eopt with
                                       | Some ee -> let _, e_expr = type_check ctx ee in
                                                    TVoid, Expr.Return(Some e_expr)
                                       | None    -> TVoid, expr)
    | Expr.Ignore(expr)             -> let _, e_expr = type_check ctx expr in
                                       TVoid, Expr.Ignore(e_expr)
    (* decided, that Scope does not affect structure of the AST *)
    | Expr.Scope(decls, expr)    -> let ctx_layer = List.fold_left (
                                                      fun acc (name, decl) ->
                                                        let expanded_ctx = Context.expandWith acc ctx in
                                                        let type_in_expanded_ctx = Context.get_type expanded_ctx name in
                                                        match decl with
                                                        | (_, `Fun (args, body))
                                                              -> let type_body, _ =  type_check (Context.expand expanded_ctx) body; in
                                                                 let tc = TLambda (List.map (fun _ -> TAny) args, type_body)
                                                                 in if not (conforms tc type_in_expanded_ctx)
                                                                    then report_error (
                                                                      Printf.sprintf "Function \"%s\" doesn't conforms declared type %s."
                                                                      name (show(Typing.t) type_in_expanded_ctx)
                                                                    );
                                                                 acc
                                                        | (_, `Variable (maybe_def))
                                                              -> let tc = match maybe_def with | Some def -> fst (type_check expanded_ctx def) | None -> TAny;
                                                                 in if not (conforms tc type_in_expanded_ctx)
                                                                    then report_error (
                                                                      Printf.sprintf "Variable \"%s\" initialized with expression of type %s doesn't conforms declared type %s."
                                                                      name (show(Typing.t) tc) (show(Typing.t) type_in_expanded_ctx)
                                                                    );
                                                                 acc
                                                        | (_, `UseWithType (typing)) -> Context.extend_layer acc name typing
                                                      ) (Context.CtxLayer []) decls in
                                    let t_expr, e_expr = type_check (Context.expandWith ctx_layer ctx) expr in
                                    t_expr, Expr.Scope(decls, e_expr)
    | Expr.Lambda(args, body)    ->  (* TODO collect return yielding types and join with this type with TUnion *)
                                    let t_body, e_body = type_check (Context.expand ctx) body
                                    in TLambda(List.map (fun _ -> TAny) args, t_body), Expr.Lambda(args, e_body)
    | Expr.Leave                 -> report_error("Cannot infer the type for internal compiler node 'Expr.Leave'")
    | Expr.Intrinsic (_)         -> report_error("Cannot infer the type for internal compiler node 'Expr.Intrinsic'")
    | Expr.Control   (_)         -> report_error("Cannot infer the type for internal compiler node 'Expr.Control'")




(* Top level typechecker *)
let typecheck ((imports, infixes), ast) = type_check Context.ZeroCtx ast