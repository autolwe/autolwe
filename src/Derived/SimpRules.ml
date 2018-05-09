(* * Simplification rules *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open Nondet
open Syms
open Expr
open ExprUtils
open Type
open Game
open Rules
open CoreTypes
open RewriteRules

module CR = CoreRules
module T  = Tactic
module Ht = Hashtbl

let mk_log level = mk_logger "Derive.SimpRules" level "SimpRules.ml"
let _log_t = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG
let log_i  = mk_log Bolt.Level.INFO

(* ** Simplification
 * ----------------------------------------------------------------------- *)

let t_split_ev_maybe mi ju =
  let ev = ju.ju_se.se_ev in
  (match mi with
  | Some i -> ret i
  | None   ->
    guard (is_Land ev) >>= fun _ ->
    mconcat (L.mapi (fun i e -> (i,e)) (destr_Land ev)) >>= fun (i,e) ->
    guard (is_Eq e) >>= fun _ ->
    let (a,b) = destr_Eq e in
    guard (is_Tuple a && is_Tuple b) >>= fun _ ->
    guard (L.length (destr_Tuple a) = L.length (destr_Tuple b)) >>= fun _ ->
    ret i
  ) >>= fun i ->
  T.t_split_ev i ju

let t_rewrite_ev_maybe mi mdir ju =
  let ev = ju.ju_se.se_ev in
  (match mi with
  | Some i ->
    begin match mdir with
    | Some d -> ret (i,d)
    | None   -> mplus (ret (i,LeftToRight)) (ret (i,RightToLeft))
    end
  | None ->
    guard (is_Land ev) >>= fun _ ->
    let conjs = L.mapi (fun i e -> (i,e)) (destr_Land ev) in
    mconcat conjs >>= fun (i,e) ->
    let others = L.filter (fun (j,_) -> i <> j) conjs in
    let occ_others e' = L.exists (fun (_,e) -> e_exists (equal_expr e') e) others in
    guard (is_Eq e) >>= fun _ ->
    let (a,b) = destr_Eq e in
    let var_ord u v = not (is_V v) || compare_expr u v > 0 in
    msum
      [ if    (is_V a && occ_others a && var_ord a b)
           || (is_FunCall a && is_FunCall b && occ_others a && compare_expr a b > 0)
        then ret LeftToRight else mempty
      ; if    (is_V b && occ_others b && var_ord b a)
           || (is_FunCall a && is_FunCall b && occ_others b && compare_expr b a > 0)
        then ret RightToLeft else mempty ] >>= fun dir ->
    ret (i,dir)
  ) >>= fun (i,dir) ->
  (T.t_ensure_progress (T.t_rw_ev i dir)) ju

let t_ctx_ev_maybe mi ju =
  log_i (lazy (fsprintf "ctx_ev_maybe: %i" (O.default (-1) mi)));
  let ev = ju.ju_se.se_ev in
  (match mi with
  | Some i ->
    let conjs = destr_Land_nofail ev in
    let e = L.nth conjs i in
    ret (i,e)
  | None ->
    guard (is_Land ev) >>= fun _ ->
    let conjs = L.mapi (fun i e -> (i,e)) (destr_Land ev) in
    mconcat conjs >>= fun (i,e) ->
    ret (i,e)
  ) >>= fun (i,e) ->
  guard (is_Eq e) >>= fun _ ->
  let (e1,e2) = destr_Eq e in
  guard (equal_ty e1.e_ty mk_Fq) >>= fun _ ->
  let cv = VarSym.mk (CR.mk_name ~name:"w__" ju.ju_se) mk_Fq in
  let ce = mk_V cv in
  let diff,cdiff = if is_FZ e2 then (e1,ce) else (mk_FMinus e1 e2,mk_FMinus ce e2) in
  let c = mk_FDiv cdiff diff in
  log_i (lazy (fsprintf "ctx_ev_maybe: %i, %a" i pp_expr e));
  (T.t_ctxt_ev i (cv,c) @> t_norm ~fail_eq:false) ju

let t_rewrite_oracle_maybe mopos mdir ju =
  (match mopos with
  | Some opos ->
    begin match mdir with
    | Some d -> ret (opos,d)
    | None   -> mplus (ret (opos,LeftToRight)) (ret (opos,RightToLeft))
    end
  | None ->
    mconcat (oguards ju.ju_se.se_gdef) >>= fun (opos,e) ->
    guard (is_Eq e) >>= fun _ ->
    let (a,b) = destr_Eq e in
    msum
      [ if (is_V a || is_GLog a) then (ret LeftToRight) else mempty
      ; if (is_V b || is_GLog b) then (ret RightToLeft) else mempty ] >>= fun dir ->
    ret (opos,dir)
  ) >>= fun (opos,dir) ->
  (T.t_ensure_progress (T.t_rewrite_oracle opos dir)) ju

let t_fix must_finish max t ju =
  let ps0 = first (T.t_id ju) in
  let rec aux i ps =
    let gs = ps.CR.subgoals in
    let npss = mapM t gs in
    if (is_nil npss || i < 0)
    then (
      guard (not must_finish || ps.CR.subgoals = []) >>= fun _ ->
      ret ps
    ) else (
      npss >>= fun pss ->
      let ps2 = CR.merge_proof_states pss ps.CR.validation in
      if equal_list equal_judgment ps2.CR.subgoals ps.CR.subgoals then
        ret ps
      else
        aux (i - 1) ps2
    )
  in
  aux max ps0

(* ** Simp and split inequality on n-tuples to obtain n proof obligations
 * ----------------------------------------------------------------------- *)

let rec t_split_ineq i ju =
  let rn = "split_ev" in
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev in
  if i < 0 || i >= L.length evs then
    tacerror "%s: invalid event position %i" rn i;
  let b = L.nth evs i in
  let eqs =
    if not (is_InEq b)
      then tacerror "rsplit_ev: bad event, expected equality";
    let (e1,e2) = destr_Eq (destr_Not b) in
    if not (is_Tuple e1 && is_Tuple e2)
      then tacerror "rsplit_ev: bad event, expected tuples, %a and %a" pp_expr e1 pp_expr e2;
    let es1, es2 = destr_Tuple e1, destr_Tuple e2 in
    if not (L.length es1 = L.length es2) then
      tacerror "rsplit_ev: bad event, got tuples of different lengths, %a and %a"
        pp_expr e1 pp_expr e2;
    L.map (fun (e1,e2) -> mk_Eq e1 e2) (L.combine es1 es2)
  in
  (* delay inequalities with too many variables *)
  let eqs,deqs = L.partition (fun e -> Se.cardinal (e_vars e) < 10) eqs in
  let rec tac eqs =
    match eqs with
    | []      -> t_simp true 20
    | eq::eqs -> T.t_case_ev eq @>> [ tac eqs; T.t_id ]
  in
  tac (eqs@deqs) ju

and t_simp i must_finish ju =
  let step =
    (   (t_norm ~fail_eq:true @|| T.t_id)
     @> (    T.t_false_ev
         @|| t_rewrite_oracle_maybe None None
         @|| t_split_ev_maybe None
         @|| t_ctx_ev_maybe None
         @|| t_rewrite_ev_maybe None None))
  in
  t_fix i must_finish step ju
