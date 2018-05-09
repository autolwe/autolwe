(* * Non-core functions for normal form *)

(* ** Imports *)

open Expr
open ExprUtils
open Norm
open Type

(* ** Remove tuple projections
 * ----------------------------------------------------------------------- *)

let rm_tuple_proj e es =
  match es with
  | e1::es ->
    begin
      try
        let i, e2 = destr_Proj e1 in
        if i <> 0 then raise Not_found;
        if List.length es + 1 <> List.length (destr_Prod_exn e2.e_ty) then
          raise Not_found;
        List.iteri (fun i e ->
          let i',e' = destr_Proj e in
          if i + 1 <> i' || not (equal_expr e2 e') then raise Not_found) es;
        e2
      with Not_found | Destr_failure _ -> e
    end
  | _ -> e

(* FIXME: clarify name *)
let rec remove_tuple_proj e =
  let e = e_sub_map remove_tuple_proj e in
  match e.e_node with
  | Tuple es -> rm_tuple_proj e es
  | _ -> e

(* ** Abbreviate g^1 = g and g^log(A) = A
 * ----------------------------------------------------------------------- *)

let rec abbrev_ggen e =
  let e = e_sub_map abbrev_ggen e in
  match e.e_node with
  | App(GExp _,[a;b]) ->
    if is_GGen a then (
       if equal_expr b mk_FOne then a
       else if is_GLog b then destr_GLog b
      else e)
    else e
  | _ -> e

let norm_expr_nice e = remove_tuple_proj (abbrev_ggen (norm_expr_weak e))

let destr_Eq_norm e =
  match e.e_node with
  | App(Eq,[e1;e2]) ->
    begin match e1.e_ty.ty_node with
    | G(_gid) -> Some (norm_expr_strong (mk_FMinus (mk_GLog e1) (mk_GLog e2)))
    | Fq      -> Some (norm_expr_strong (mk_FMinus e1 e2))
    | _       -> None
    end
  | _ ->
    None

let destr_Neq_norm e =
  match e.e_node with
  | App(Not,[e1]) -> destr_Eq_norm e1
  | _             -> None
