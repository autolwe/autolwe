(* * Deducibility for field expressions. *)

(* ** Imports *)
open Abbrevs
open Util
open Syms
open Type
open Expr
open ExprUtils
open NormField
open Norm

(* ** Special purpose routines
 * ----------------------------------------------------------------------- *)

(** Special purpose routine to deduce a variable [v] from an expression [e]
    assuming all other variables are known. *)
let solve_fq_vars_known e v =
  let ev = mk_V v in
  let v_occurs p =
    L.exists (fun (m,_) ->
      L.exists (fun (e,_) -> Se.mem ev (e_vars e)) m)
      (EP.to_terms p)
  in
  let (num,mdenom) = polys_of_field_expr (CAS.norm id e) in
  let (g,h) = factor_out ev num in
  if not (EP.equal g EP.zero) then (
    match mdenom with
    | None ->
      (*i v = v' * g + h => v' = (v - h) / g i*)
      let e' = mk_FDiv (mk_FMinus ev (exp_of_poly h)) (exp_of_poly g) in
      Norm.norm_expr_strong e'
    | Some(denom) when not (v_occurs denom) ->
      (*i v = (v' * g + h) / denom => v' = (v * denom - h) / g i*)
      let (g,h) = factor_out ev num in
      let e' = mk_FDiv
                 (mk_FMinus
                    (mk_FMult [ev; exp_of_poly denom])
                    (exp_of_poly h))
                 (exp_of_poly g)
      in
      Norm.norm_expr_strong e'
    | Some(_denom) ->
      raise Not_found
  ) else (
    raise Not_found
  )

let solve_fq_var (ecs : (expr * inverter) list) e =
  if not (is_V e) then raise Not_found;
  let v = destr_V e in
  let ecs_v,ecs_poly =
    L.partition (fun (e,_w) -> is_V e || is_RoCall e || is_MapLookup e || is_FunCall e) ecs
  in
  match L.filter (fun (f,_) -> Se.mem e (e_vars f)) ecs_poly with
  | [(f,w_f)] ->
    (* to check {w1->x1,...,wk->xk,wk+1->f} |- v, we take f and replace
       xi by wi and v by wk+1 in f, then we know that (f - g)/h = v. *)
    let f =
      L.fold_right
        (fun (x,w) f -> e_replace x (expr_of_inverter w) f)
        ecs_v
        f
    in
    let c = solve_fq_vars_known f v in
    let c = norm_expr_strong (e_replace e (expr_of_inverter w_f) c) in
    c
  | _ -> raise Not_found

(* If recipes for all variables in secret e are
   known, we can just substitute the recipes in. *)
let solve_fq_poly (ecs : (expr * inverter) list) e =
  let subst =
    L.fold_right
      (fun (x,I w) m -> Me.add w x  m)
      ecs
      Me.empty
  in
  let res = e_subst subst e
  in res

let solve_fq (ecs : (expr * inverter) list) e =
  let vars = e_vars e in
  let known_vars = se_of_list (L.filter is_V (L.map fst ecs)) in
  let known_occ_vars =
    L.fold_right (fun e s -> Se.union s (e_vars (fst e))) ecs Se.empty
  in
  if Se.subset vars known_vars then (
    I (solve_fq_poly ecs e)
  ) else if not (Se.is_empty (Se.diff vars known_occ_vars)) then (
    raise Not_found
  ) else (
    I (solve_fq_var ecs e)
  )

(* ** Solving for mixed types
 * ----------------------------------------------------------------------- *)

let solve_mixed_type k s =
  let ty_k, ty_s = k.e_ty, s.VarSym.ty in
  match ty_k.ty_node, ty_s.ty_node with (* TODO: make Matrix version. should be
  easy *)
  | Fq, Fq ->
    (s,solve_fq_vars_known k s)

  (* example: ga -> ga^b
     1. try to deduce log(ga) from log(ga^b) = log(ga)*b
     2. abstract log(ga) by v: v*b |-> v ==> get v/b.
     3. translate as ga -> g^(log(ga)/b)  *)
  | G n1, G n2 when Groupvar.equal n1 n2 ->
    let v_fq = VarSym.mk ("v_fq_"^(Id.name s.VarSym.id)) mk_Fq in
    let to_gn1 e = mk_GExp (mk_GGen n1) e in
    let k_fq =
      norm_expr_strong (mk_GLog k)
      |> e_replace (mk_V s) (to_gn1 (mk_V v_fq))
      |> norm_expr_strong
    in
    let ce = solve_fq_vars_known k_fq v_fq in
    (s, to_gn1 (e_replace (mk_V v_fq) (mk_GLog (mk_V s)) ce))
                                 
  (* example: a -> g^a*b
     1. try to deduce a from log(g^a*b) = a*b, get a/b.
     2. we get ga -> log(ga)/b *)
  | G _, Fq ->
    let _,k_fq = destr_GExp (norm_expr_strong k) in
    let ce = solve_fq_vars_known k_fq s in
    let v_g = VarSym.mk ("v_g_"^(Id.name s.VarSym.id)) ty_k in
    (v_g, e_replace (mk_V s) (mk_GLog (mk_V v_g)) ce)

  (* example: ga -> log(ga)*b
     1. try to deduce log(ga) from log(ga)*b
     2. abstract log(ga) by v: v*b |-> v ==> get v/b.
     3. translate as v -> g^(v/b) *)
  | Fq, G n1 ->
    let v_fq = VarSym.mk ("v_fq_"^(Id.name s.VarSym.id)) mk_Fq in
    let to_gn1 e = mk_GExp (mk_GGen n1) e in
    let k_fq =
      e_replace (mk_V s) (to_gn1 (mk_V v_fq)) k
      |> norm_expr_strong
    in
    let ce = solve_fq_vars_known k_fq v_fq in
    (v_fq, to_gn1 ce)

  | BS l1, BS l2 when Lenvar.equal l1 l2 ->
    if Expr.equal_expr (mk_V s) (Norm.norm_expr_strong (e_replace (mk_V s) k k)) then
      (s,k)
    else
      tacerror "t_rnd_pos: cannot invert for BS_n, (%a -> %a) not self-inverse"
        VarSym.pp s
        pp_expr k

  | _ ->
    tacerror "t_rnd_pos: cannot invert for given types, known %a, secret %a"
      pp_ty ty_k pp_ty ty_s
