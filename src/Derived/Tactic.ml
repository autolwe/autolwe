(* * Tactics and Tacticals *)

(* ** Imports and abbreviations
 * ----------------------------------------------------------------------- *)
open CoreRules
open Nondet
open Abbrevs
open Util
open CoreTypes

let mk_log level = mk_logger "Derive.Tactic" level "Tactic.ml"
let log_t  = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG
let _log_i = mk_log Bolt.Level.INFO

(* ** Types
 * ----------------------------------------------------------------------- *)

(** A tactic takes a goal and returns a proof state. *)
type tactic = goal -> proof_state nondet

(** A tactic that takes a goal and returns a result and a proof state. *)
type 'a rtactic = goal -> ('a * proof_state) nondet

exception NoOpenGoal

(* ** Simple tactics and tacticals
 * ----------------------------------------------------------------------- *)

(** Identity tactic. *)
let t_id g = ret (
  { subgoals = [g];
    validation = fun pts -> match pts with [pt] -> pt | _ -> assert false })

(** Apply the given tactic and cut the search space by returning
    only the first possible proof state. *)
let t_cut t g =
  let pss = t g in
  match pull pss with
  | Left(Some s) -> mfail s
  | Left None    -> mfail (lazy "t_cut: mempty")
  | Right(x,_)   -> ret x

(** Sequential composition of the tactic [t1] with the tactic [t2]. *)
let t_seq t1 t2 g =
  t1 g >>= fun ps1 ->
  mapM t2 ps1.subgoals >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

(** Sequential composition of the tactic [t1] with the tactics [t2s]:
    apply [t1] to get $|t2s|$ new proof states [ps2s], then
    apply the i-th element of [t2s] to the i-th proof state in [ps2s]. *)
let t_seq_list t1 t2s g =
  t1 g >>= fun ps1 ->
  assert (L.length t2s = L.length ps1.subgoals);
  mapM (fun (t2,g) -> t2 g) (L.combine t2s ps1.subgoals) >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

(** Apply tactic [t1] to goal [g] or apply [t2] in case of failure. *)
let t_or tn1 tn2 g = Nondet.mplus (tn1 g)  (tn2 g)

(** Apply tactic [t] or [t_id] in case of failure. *)
let t_try t g = t_or t t_id g

(** Tactic that ignore the goal and fails with given format string. *)
let t_fail fs _g =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      log_t (lazy s);
      mfail (lazy s))
    fbuf fs

(** Tactical that fails if the given tactic returns the same proof state. *)
let t_ensure_progress t g =
  t g >>= fun ps ->
  guard (not (L.length ps.subgoals = 1 && equal_judgment (L.hd ps.subgoals) g)) >>= fun _ ->
  ret ps

(** Monadic bind for rtactics, expects that [t1] returns a single goal. *)
let t_bind (t1 : 'a rtactic) (ft2 : 'a -> 'b rtactic) g =
  t1 g >>= fun (x,ps1) ->
  mapM (ft2 x) ps1.subgoals >>= fun ps2s ->
  match ps2s with
  | [y,ps2] ->
    ret (y,merge_proof_states [ps2] ps1.validation)
  | _ ->
    mfail (lazy "t_bind: expected exactly one goal")

(** Monadic bind for an rtactic and a tactic. *)
let t_bind_ignore (t1 : 'a rtactic) (ft2 : 'a -> tactic) g =
  t1 g >>= fun (x,ps1) ->
  mapM (ft2 x) ps1.subgoals >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

(* ** Tactic application
 * ----------------------------------------------------------------------- *)

(** Tactic that moves the first subgoal to the last position. *)
let move_first_last ps =
  match ps.subgoals with
  | [] -> tacerror "last: no goals"
  | ju :: jus ->
    let validation pts =
      match L.rev pts with
      | pt :: pts -> ps.validation (pt::L.rev pts)
      | _ -> assert false
    in
    { subgoals = jus @ [ju];
      validation = validation }

(** Apply the tactic [t] to the [n]-th subgoal of proof state [ps]. *)
let apply_on_n n t ps =
  let len = L.length ps.subgoals in
  if len = 0 then raise NoOpenGoal;
  if len <= n then tacerror "expected %i, got %i subgoal(s)" n len;
  let hd, g, tl = Util.split_n n ps.subgoals in
  t g >>= fun gsn ->
  let validation pts =
    let hd, tl = Util.cut_n n pts in
    let ptn, tl = Util.cut_n (L.length gsn.subgoals) tl in
    ps.validation (L.rev_append hd (gsn.validation (L.rev ptn) :: tl))
  in
  ret { subgoals = L.rev_append hd (gsn.subgoals @ tl);
        validation = validation }

(** Apply the tactic [t] to the first subgoal in proof state [ps]. *)
let apply_first t ps = apply_on_n 0 t ps

(** Apply the tactic [t] to all subgoals in proof state [ps]. *)
let apply_all t ps =
  mapM t ps.subgoals >>= fun pss ->
  ret (merge_proof_states pss ps.validation)

(** Apply the rtactic [t] to all subgoals in proof state [ps]
    and returns [t's] result. *)
let rapply_all rt ps =
  mapM rt ps.subgoals >>= fun pss ->
  match pss with
  | [y,ps2] ->
    ret (y,merge_proof_states [ps2] ps.validation)
  | _ ->
    mfail (lazy "t_bind: expected exactly one goal")

(* ** Lifting core tactics
 * ----------------------------------------------------------------------- *)

(* Convert core tactic to regular tactic *)
let core_tactic ct g =
  let open BatResult in
  match ct g with
  | Ok ps -> ret ps
  | Bad s -> mfail s

let t_conv do_norm new_se = core_tactic (ct_conv do_norm new_se)

let t_matfold which ia ib m = core_tactic (ct_matfold m which ia ib)

let t_matunfold which i p = core_tactic (ct_matunfold p which i)

let t_assm_comp assm ev_e subst = core_tactic (ct_assm_comp assm ev_e subst)

let t_assm_dec dir ren rngs assm = core_tactic (ct_assm_dec dir ren rngs assm)

let t_sep_dom ms1 ms2 = core_tactic (ct_sep_dom ms1 ms2)

let t_move i delta = core_tactic (ct_move i delta)

let t_except p es = core_tactic (ct_except p es)

let t_remove_ev rm = core_tactic (ct_remove_ev rm)

let t_case_ev ?flip:(flip=false) ?allow_existing:(ae=false) e =
  core_tactic (ct_case_ev ~flip ~allow_existing:ae e)

let t_rewrite_oracle op dir = core_tactic (ct_rewrite_oracle op dir)

let t_guard p tnew = core_tactic (ct_guard p tnew)

let t_move_oracle i delta = core_tactic (ct_move_oracle i delta)

let t_guess asym fvs = core_tactic (ct_guess asym fvs)

let t_split_ev i = core_tactic (ct_split_ev i)

let t_false_ev = core_tactic ct_false_ev

let t_rw_ev i d = core_tactic (ct_rw_ev i d)

let t_ctxt_ev i c = core_tactic (ct_ctxt_ev i c)

let t_rnd_oracle opos ctxt1 ctxt2 = core_tactic (ct_rnd_oracle opos ctxt1 ctxt2)

let t_rnd pos ctxt1 ctxt2 = core_tactic (ct_rnd pos ctxt1 ctxt2)

let t_merge_ev i j = core_tactic (ct_merge_ev i j)

let t_random_indep = core_tactic ct_random_indep

let t_trans se = core_tactic (ct_trans se)

let t_except_oracle opos es = core_tactic (ct_except_oracle opos es)

let t_admit s = core_tactic (ct_admit s)

let t_dist_sym = core_tactic ct_dist_sym

let t_dist_eq = core_tactic ct_dist_eq

let t_assert gpos e = core_tactic (ct_assert gpos e)

let t_move_main ope s = core_tactic (ct_move_main ope s)

let t_hybrid gpos i lcmds e = core_tactic (ct_hybrid gpos i lcmds e)

let t_find vse e asym vss = core_tactic (ct_find vse e asym vss)

let t_add_test opos e asym vss = core_tactic (ct_add_test opos e asym vss)
