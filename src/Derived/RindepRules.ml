(* * Derived rules for dealing with random independence. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open Nondet
open Syms
open Expr
open ExprUtils
open Norm
open Game
open Rules
open CoreTypes
open RewriteRules

module Ht = Hashtbl
module CR = CoreRules
module T  = Tactic

let mk_log level = mk_logger "Derive.RindepRules" level "RindepRules.ml"
let log_t  = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG

(* ** Merging equalities in event.
 * ----------------------------------------------------------------------- *)

(** Merging equalities in conjuncts of event. *)
let t_merge_ev tomerge ju =
  let tomerge = List.sort Pervasives.compare tomerge in
  let rec tac k tomerge ju =
    match tomerge with
    | [] | [_]-> T.t_id ju
    | i::j::tomerge ->
      (T.t_merge_ev (i-k) (j-k) @> tac (k+1) (j::tomerge)) ju in
  tac 0 tomerge ju

(* ** Automate random independence.
 * ----------------------------------------------------------------------- *)

(* We know a set of facts
   e1 = e2
   exists x in L | e1 = e2
   and inequalities
   We collect all the term we known and we try to invert the term we want.
   Assume we known e1 = e2 then we known e1 - e2 = 0
   as well for exists x in L | e1 = e2
   Then we try to invert the random variable, using the equality.
   We get an inverter.
   We look the equality which are used and we merge then in a single equivalent
   equality, again we build the inverter (this should works).
   We apply the inverter.
*)

let init_inverter test =
  let e1, e2, bd =
    if is_Eq test then let e1,e2 = destr_Eq test in e1,e2,[]
    (* else if is_Exists test then destr_Exists test *)
    else raise Not_found
  in
  let (x1,c), z = sub e2.e_ty in
  let c = (x1, inst_ctxt c e2) in
  let e = norm_expr_strong (inst_ctxt c e1) in
  (bd, e, c, z)

let init_inverters test =
  let ts = destr_Land_nofail test in
  let bds = ref [] in
  let rec aux i ts =
    match ts with
    | [] -> []
    | t::ts ->
      try
        let bd,e1me2,inv,z = init_inverter t in
        bds := bd @ !bds;
        (i,e1me2,inv, z, mk_V (VarSym.mk "x" e1me2.e_ty)) :: aux (i+1) ts
      with Not_found -> aux (i+1) ts
  in
  let l = aux 0 ts in
  !bds, l

let t_last_random_indep ts ju =
  let se = ju.ju_se in
  match List.rev se.se_gdef with
  | Game.GSamp (r,_) :: _ ->
    let ev = se.se_ev in
    let fv = e_vars ev in
    let er = mk_V r in
    let bds, ms = init_inverters ev in
    let msv = List.map (fun (_,e1me2,_,_,x) -> (e1me2, I x)) ms in
    let vs = L.map (fun x -> (x, I x)) (Se.elements (Se.remove er fv)) in
    let bds = List.map (fun (x,_) -> let e = mk_V x in (e, I e)) bds in
    let known = vs@bds@msv in
    log_t (lazy (fsprintf ">>>>> trying to deduce %a from %a@\n"
                   pp_expr er (pp_list "," (pp_pair pp_expr pp_expr))
                   (L.map (fun (a,b) -> (a,expr_of_inverter b)) known)));
    begin match exc_to_opt (fun () -> Deduc.invert ts known er) with
    | None -> T.t_fail "cannot find inverter" ju
    | Some (I inv) ->
      let used = e_vars inv in
      let tomerge = List.filter (fun (_,_,_,_,x) -> Se.mem x used) ms in
      let tomergei = List.map (fun (i,_,_,_,_) -> i) tomerge in
      let ctxt =
        if List.length tomerge = 1 then
          let  (_,_,c,_,x1) = List.hd tomerge in
          let x = destr_V x1 in
          fst c, inst_ctxt (x,inv) (snd c)
        else
          let e = Expr.mk_Tuple (List.map (fun (_,e,_,_,_) -> e) tomerge) in
          let vx = VarSym.mk "x" e.e_ty in
          let x = mk_V vx in
          let projs = L.mapi (fun i _ -> mk_Proj i x) tomerge in
          let app_proj inv (_,_,c,_,y) p =
            let y = destr_V y in
            inst_ctxt (y,inv) (inst_ctxt c p)
          in
          let inv = L.fold_left2 app_proj inv tomerge projs in
          vx, inv
      in
      let pos = match L.rev tomerge with
        | (i,_,_,_,_) :: _ -> i
        | _ -> assert false
      in
      let pos = pos - (L.length tomerge - 1) in
      (t_merge_ev tomergei @>
        T.t_ctxt_ev pos ctxt @>
        t_norm_tuple_proj  @>
        T.t_random_indep) ju
    end
  | _ -> T.t_fail "The last instruction is not a sampling" ju

let t_random_indep_exact ju =
  T.t_random_indep ju

let t_random_indep_no_exact emaps ju =
  let se = ju.ju_se in
  log_t (lazy "###############################");
  log_t (lazy "t_random_indep\n");
  let ev_vars = e_vars se.se_ev in
  let rec aux i rc =
    match rc with
    | Game.GSamp(v,_) :: rc ->
      if Se.mem (mk_V v) ev_vars then (
        log_t (lazy (fsprintf "trying variable %a" VarSym.pp v));
        (T.t_move (L.length rc) i @> (T.t_random_indep @|| t_last_random_indep emaps)) @||
        (aux (i+1) rc)
      ) else (
        aux (i+1) rc
      )
    | _ :: rc -> aux (i+1) rc
    | [] ->
      fun _ -> mfail (lazy "rindep auto: can not find an independent random variable")
  in
  (T.t_random_indep @|| aux 0 (L.rev se.se_gdef)) ju

let t_random_indep ts exact ju =
  if exact
  then t_random_indep_exact ju
  else t_random_indep_no_exact ts ju
