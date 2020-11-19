(* The purpose of this module is type checking, type inferrence *)

open GT
open Language
open Language.Typing

(* Context *)
module Context =
  struct

    (* Context: initial (empty), scope context *)
    @type t =
    | ZeroCtx
    | SuccCtx of (string * Typing.t) list * t
    with show, html
    (* Q: Why not just list of string * Typing.t?
       A: Because of redefinitions control! *)

    (* Get the depth level of a state *)
    let rec level = function
    | ZeroCtx         -> 0
    | SuccCtx (_, st) -> 1 + level st

    (* 26.26 -- List operations
       https://ocaml.org/releases/4.11/ocaml-4.11-refman.pdf *)
    let rec getType ctx name
      = match ctx with
        | ZeroCtx               -> TAny  (* Dilemma: it is either error, or this name can be external symbol *)
        | SuccCtx (scope, ctx') ->
          match List.assoc_opt name scope with
          | None        -> getType ctx' name (* Try to find type in upper instances *)
          | Some typing -> typing            (* Or return found one *)

    (* Extend current typing scope with the typing information: the [name] has the type [typing] *)
    let extend ctx name typing
      = match ctx with
        | ZeroCtx               -> report_error("FATAL. Cannot add type to empty context! Should be created context scope.")
        | SuccCtx (scope, ctx') ->
          match List.find_opt (fun (pname, _) -> pname = name ) scope with
          | None               -> SuccCtx (List.cons (name, typing) scope, ctx') (* Successfully added type to scope *)
          | Some ((_, typing)) -> report_error ~loc:(Loc.get name) ("redefinition of typing for " ^ name ^ " in the same scope")

    (* Expand context when entering scope. Thus typings can be reassigned *)
    let expand ctx = SuccCtx([], ctx)

  end

(* check that type 'lhs' can be used as type 'rhs': "lhs conforms rhs" *)
let rec conforms lhs rhs
  = match (lhs, rhs) with
  | (TAny, _   ) -> true
  | (_   , TAny) -> true
  | (l, r) -> l = r (* TODO complete definition for all cases necessary *)

(* Function for type checking: accepts context and expression, returns it's type or fails *)
(* TODO optimization needed: watch the type of the subtrees lazily *)
let rec type_check ctx expr
  = match expr with
    | Expr.Const _      -> TConst
     (* TODO should we infer EVERY SINGLE element and generalize most common type? Guess not, but maybe yes? *)
    | Expr.Array values          -> TArr (TAny)
    | Expr.String _              -> TString
    | Expr.Sexp (name, subexprs) -> TSexp(name, List.map (fun exp -> type_check ctx exp) subexprs)
    | Expr.Var  (name, _)        -> Context.getType ctx name
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
                                      (* TODO This is hard but worthy task: should carry computational context as well *)
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
                                    let ret_type =
                                      match t_f with
                                      | TAny -> TAny
                                      | TLambda (premise, conclusion) ->
                                        if try List.for_all2 conforms t_args premise
                                           with Invalid_argument(_) -> report_error("Arity mismatch in function call")
                                        then conclusion (* Each expression from t_args conform to the premise of function *)
                                        (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
                                        else report_error("Argument type mismatch in function call")
                                      | _ -> report_error("Cannot perform a call for non-callable object")
                                    in ret_type
    | Expr.Assign(reff, exp)     -> let t_reff = type_check ctx reff in
                                    let t_exp  = type_check ctx exp  in
                                    let ret_type =
                                      match t_reff with
                                      | TAny -> TAny
                                      | TRef (t_x) -> if conforms t_exp t_x
                                                      then t_x
                                                      else report_error("Cannot assign a value with inappropriate type")
                                    in ret_type
    | Expr.Seq(_, step2)         -> type_check ctx step2 (* Ignore whatever the 'step1' type is *)
    | Expr.Skip                  -> TVoid                (* Skip has NO return value *)
    | Expr.If(cond, lbr, rbr)    -> let t_cond = type_check ctx cond in
                                    let t_lbr  = type_check ctx lbr  in
                                    let t_rbr  = type_check ctx rbr  in
                                    if conforms t_cond TConst
                                    then TUnion(t_lbr :: t_rbr :: []) (* TODO think about union flatten should be performed *)
                                    (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
                                    else report_error("If condition should be logical value class")
    | Expr.While(cond, body)
    | Expr.Repeat(body, cond)     -> let t_cond = type_check ctx cond in
                                    let t_body = type_check ctx body in
                                    if conforms t_cond TConst
                                    then TVoid (* I assume the result type of such cycles is empty *)
                                    (* TODO NO LOCATION, NO SPECIFIC MISMATCH TYPE *)
                                    else report_error("Loop condition should be logical value class")
    | Expr.Return(_)               -> TVoid                (* TODO Return has NO return value (paradox detected) *)
    | Expr.Ignore(_)               -> TVoid                (* Neither ignore hasn't *)




(* Traverse program and assign types to Variables and Functions *)
let type_traverse cmd ((imports, infixes), ast) =
  let z = 3 in 5