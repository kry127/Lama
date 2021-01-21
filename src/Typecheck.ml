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


    (* Extend one context layer with the typing information: the [name] has the type [typing] *)
    let extend_layer, extend =
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

(* check that type 'lhs' can be used as type 'rhs': "lhs conforms rhs" *)
let rec conforms lhs rhs
  = match (lhs, rhs) with
  | (TAny, _   ) -> true
  | (_   , TAny) -> true
  | (TArr l, TArr r)
  | (TRef l, TRef r) -> conforms l r
  | (TSexp(name_l, types_l), TSexp(name_r, types_r)) ->    name_l = name_r
                                                        && List.length types_l = List.length types_r
                                                        && List.for_all2 conforms types_l types_r
  (* Note: right now implemented as CONTRAVARIANT by the arguments *)
  | (TLambda(args_l, body_l), TLambda(args_r, body_r)) -> List.for_all2 conforms args_r args_l && conforms body_l body_r
                             (* For all lel \in ls Exists rel \in rs such that `conforms lel rel` *)
  | (TUnion ls, TUnion rs) -> List.for_all (fun lel -> List.exists (conforms lel) rs) ls
  | (tl       , TUnion rs) -> List.exists (conforms tl) rs
  | (TUnion ls, tr       ) -> List.for_all (fun tl ->  conforms tl tr) ls
  | (l, r) -> l = r (* TString, TConst, TVoid *)

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

(* Function for type checking: accepts context and expression, returns it's type or fails *)
(* TODO optimization needed: watch the type of the subtrees lazily *)
let rec type_check ctx expr
  = (* Printf.printf "Type checking \"%s\"...\n" (show(Expr.t) expr); *)
    match expr with
    | Expr.Const _      -> TConst
    | Expr.Array values          -> TArr (union_contraction (TUnion (List.map (fun exp -> type_check ctx exp) values)))
    | Expr.String _              -> TString
    | Expr.Sexp (name, subexprs) -> TSexp(name, List.map (fun exp -> type_check ctx exp) subexprs)
    | Expr.Var   name            -> Context.get_type ctx name
    | Expr.Binop (_, exp1, exp2) -> let t1 = type_check ctx exp1 in
                                    let t2 = type_check ctx exp2 in
                                    if conforms t1 TConst && conforms t2 TConst
                                    then TConst
                                    (* TODO not enough info + NO LOCATION *)
                                    else report_error("Binary operations can be applied only to integers")
    | Expr.ElemRef (arr, index) (* Both normal and inplace versions, but I don't know result type of ElemRef... *)
    | Expr.Elem (arr, index)     -> let t_arr = type_check ctx arr in
                                    let t_index = type_check ctx index in
                                    if conforms t_index TConst
                                    then match t_arr with
                                         | TAny            -> TAny
                                     (* Indexing to string returns char code, see ".elem" in Language.ml *)
                                         | TString         -> TConst
                                         | TArr(elem_type) -> elem_type
                                      (* TODO constant propagation for retrieving type like this: *)
                                      (*  | TSexp(name, typeList)  -> List.nth_opt typeList (Language.eval index []) *)
                                         | TSexp(name, type_list)  -> TUnion (type_list) (* Breaks type safety: UB when index out of bounds *)
                                         (* TODO NO LOCATION *)
                                         | _ -> report_error("Indexing can be performed on strings, arrays and S-expressions only")
                                    (* TODO NO LOCATION *)
                                    else report_error("Indexing can be done only with integers")
    | Expr.Length (exp)          -> let t_exp = type_check ctx exp in
                                    let ret_type = match t_exp with
                                                   | TString | TArr(_) | TSexp(_, _) | TAny -> TConst
                                                   | _ -> report_error("Length has only strings, arrays and S-expressions")
                                    in ret_type
    | Expr.StringVal (_)         -> TString (* The most plesant rule: anything can be matched to a string *)
    | Expr.Call(f, args)         -> let t_f = type_check ctx f in
                                    let t_args = List.map (fun arg -> type_check ctx arg) args in
                                    let rec ret_type_func ff =
                                      match ff with
                                      | TAny -> TAny
                                      | TLambda (premise, conclusion) ->
                                        if try List.for_all2 conforms t_args premise
                                           with Invalid_argument(_) -> report_error("Arity mismatch in function call") (* TODO NO 'TVariadic' SUPPORT *)
                                        then conclusion (* Each expression from t_args conform to the premise of function *)
                                        (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
                                        else report_error("Argument type mismatch in function call")
                                      | TUnion (ffs) -> union_contraction (TUnion (
                                                          List.filter_map (* Combine filtering and mapping at the same time *)
                                                          (* If no exception comes out, give out type as is, otherwise nothing returned *)
                                                          (fun f -> try Some (ret_type_func f) with _ -> None)
                                                          ffs
                                                        ))
                                      | _ -> report_error("Cannot perform a call for non-callable object")
                                    in ret_type_func t_f
    | Expr.Assign(reff, exp)     -> let t_reff = type_check ctx reff in
                                    let t_exp  = type_check ctx exp  in
                                    let ret_type =
                                      match t_reff with
                                      | TAny -> TAny
                                      | TRef (t_x) -> if conforms t_exp t_x
                                                      then t_x
                                                      else report_error("Cannot assign a value with inappropriate type")
                                    in ret_type
                                     (* Ignore whatever the 'step1' type is, but we still need to typecheck it! *)
    | Expr.Seq(step1, step2)         -> type_check ctx step1; type_check ctx step2
    | Expr.Skip                  -> TVoid                (* Skip has NO return value *)
    | Expr.If(cond, lbr, rbr)    -> let t_cond = type_check ctx cond in
                                    let t_lbr  = type_check ctx lbr  in
                                    let t_rbr  = type_check ctx rbr  in
                                    if conforms t_cond TConst
                                    then union_contraction (TUnion(t_lbr :: t_rbr :: []))
                                    (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
                                    else report_error("If condition should be logical value class")
    | Expr.While(cond, body)
    | Expr.Repeat(body, cond)    -> let t_cond = type_check ctx cond in
                                    let t_body = type_check ctx body in
                                    if conforms t_cond TConst
                                    then TVoid (* I assume the result type of such cycles is empty *)
                                    (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
                                    else report_error("Loop condition should be logical value class")
    (* TODO very difficult branch *)
    | Expr.Case(match_expr, branches, loc, return_kind)
                                 -> let t_match_expr = type_check ctx match_expr in
                                 (* Then, we analyze each branch in imperative style. O(n^2) * O(Complexity of confomrs) *)
                                    let len = List.length branches in
                                    let pattern_types = Array.make len TAny in
                                    let return_types = Array.make len TAny in
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
                                        return_types.(i) <- type_check (Context.expandWith ctx_layer ctx) implementation
                                      end
                                    done;
                                    (* Then return accumulated return types in one TUnion type *)
                                    union_contraction (TUnion(Array.to_list return_types))
    | Expr.Return(eopt)             -> (match eopt with | Some ee -> type_check ctx ee | None -> TVoid); TVoid (* TODO Return should yield the result type of inner expression (see Expr.Lambda) *)
    | Expr.Ignore(expr)             -> type_check ctx expr; TVoid (* Neither ignore hasn't *)
    | Expr.Scope(decls, expr)    -> let ctx_layer = List.fold_right (
                                                      fun (name, decl) acc -> match decl with
                                                      | (_, `Fun (args, body))
                                                            -> type_check (Context.expand ctx) body;
                                                               acc
                                                      | (_, `Variable (maybe_def))
                                                            -> let tc = match maybe_def with | Some def -> type_check ctx def | None -> TAny;
                                                               in ();
                                                               acc
                                                      | (_, `UseWithType (typing)) -> Context.extend_layer acc name typing
                                                    ) decls (Context.CtxLayer []) in
                                    type_check (Context.expandWith ctx_layer ctx) expr
    | Expr.Lambda(args, body)    -> type_check (Context.expand ctx) body (* TODO collect return yielding types and join with this type with TUnion *)
    | Expr.Leave                 -> report_error("Cannot infer the type for internal compiler node 'Expr.Leave'")
    | Expr.Intrinsic (_)         -> report_error("Cannot infer the type for internal compiler node 'Expr.Intrinsic'")
    | Expr.Control   (_)         -> report_error("Cannot infer the type for internal compiler node 'Expr.Control'")




(* Top level typechecker *)
let typecheck ((imports, infixes), ast) = type_check Context.ZeroCtx ast