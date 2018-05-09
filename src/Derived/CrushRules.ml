(* * Automated derived rules *)

(* ** Imports and Abbreviations *)
open Abbrevs
open Util
open Nondet
open Syms
open Expr
open Game
open Rules
open CoreTypes
open RewriteRules
open Assumption
open AssumptionRules
open RandomRules
open RindepRules
open CaseRules
open SimpRules

module CR = CoreRules
module T = Tactic
module CT = CoreTypes
module Ht = Hashtbl

let mk_log level = mk_logger "Derive.CrushRules" level "CrushRules.ml"
let log_t  = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG
let log_i  = mk_log Bolt.Level.INFO


(* ** Automated crush tactic
 * ----------------------------------------------------------------------- *)

type proof_search_info = {
  psi_assms  : Sstring.t;
  psi_rvars  : VarSym.S.t;
  psi_orvars : VarSym.S.t;
  psi_cases  : Se.t
}

let psi_empty = {
  psi_assms = Sstring.empty;
  psi_rvars = VarSym.S.empty;
  psi_orvars = VarSym.S.empty;
  psi_cases  = Se.empty
}

(* compute proof search information on path of each admit for given proof tree *)
let psis_of_pt pt =
  let admit_psis = ref [] in
  let rec aux psi pt =
    let gd = pt.CR.pt_ju.ju_se.se_gdef in
    let children = pt.CR.pt_children in
    match pt.CR.pt_rule with
    | CT.Rassm_dec(_,_,_,ad) ->
      let psi =
        { psi with psi_assms = Sstring.add ad.ad_name psi.psi_assms }
      in
      L.iter (aux psi) children
    | CT.Rcase_ev(_,e) ->
      let psi =
        { psi with psi_cases = Se.add e psi.psi_cases }
      in
      L.iter (aux psi) children
    | CT.Rrnd(pos,_,_,_) ->
      let rands = samplings gd in
      let (rv,_) = L.assoc pos rands in
      let psi =
        { psi with psi_rvars = VarSym.S.add rv psi.psi_rvars }
      in
      L.iter (aux psi) children
    | CT.Rrnd_orcl(opos,_,_) ->
      let orands = osamplings gd in
      let (orv,_) = L.assoc opos orands in
      let psi =
        { psi with psi_orvars = VarSym.S.add orv psi.psi_orvars }
      in
      L.iter (aux psi) children
    | CT.Radmit "current" ->
      (* we ignore admits with label other from other branches of the proof *)
      admit_psis := psi::!admit_psis
    | _ ->
      L.iter (aux psi) children
  in
  aux psi_empty pt;
  !admit_psis

type stats = {
  nstates   : int;
  unqstates : int;
  ses       : sec_exp list
}

let log_games = false

let rec t_crush_step depth stats ts must_finish finish_now psi =
  let gdir = "games_h" in
  let ias = psi.psi_assms in
  let irvs = psi.psi_rvars in
  let iorvs = psi.psi_rvars in
  let icases = psi.psi_cases in
  let count_except ju =
    L.length (L.filter (function GSamp(_,(_,excs)) -> excs<>[] | _ -> false) ju.ju_se.se_gdef)
  in
  (*i let t_norm_xor_id = t_norm ~fail_eq:true @|| CR.t_id in i*)
  let t_after_simp ju =
    let (ses,unqstates,is_old) =
      let se = ju.ju_se in
      let se = { se with se_gdef = L.sort compare se.se_gdef } in
      log_t (lazy (fsprintf "+++++ state: %i, unique state: %i@\n%a"
                     !stats.nstates !stats.unqstates pp_se se));
      if not (L.mem se !stats.ses)
      then (se::!stats.ses, !stats.unqstates + 1,false)
      else (!stats.ses, !stats.unqstates,true)
    in
    let s = fsprintf "%a" pp_ju ju in
    stats := { nstates = !stats.nstates + 1; unqstates = unqstates; ses = ses };
    (* if !stats.nstates > 20 then
         tacerror "Ressource bounds exhausted, please install ZooCrypt locally"; *)
    if log_games then (
      Util.output_file (F.sprintf "%s/g%i.zc" gdir !stats.nstates)
        (s^(F.sprintf "\n depth %i\n" depth))
    );
    if is_old
    then T.t_fail "state already explored!" ju
    else T.t_id ju
  in
  let t_log s ju =
    if log_games then
      Util.append_file (F.sprintf "%s/g%i.zc" gdir !stats.nstates) s;
    T.t_id ju
  in
  let t_prepare =
    (   (T.t_ensure_progress (t_simp false 40) @|| T.t_id)
        @> (t_norm ~fail_eq:true @|| T.t_id))
  in
  let t_close ju =
    ((T.t_try (GuardRules.t_guess_maybe None None)
      @> (    t_random_indep ts false @> t_log "random_indep"
          @|| t_simp true 40))
     @|| (t_assm_comp ~icases ts false None None @> t_log "assm_comp")) ju
  in
  let t_progress =
       (t_assm_dec ~i_assms:ias ts false None (Some LeftToRight) None None
        @> t_log "\nassm_dec")
    @| (fun ju
        -> if count_except ju < 3 then (t_rexcept_maybe None None @> t_log "\nrexcept") ju
           else T.t_id ju)
    @| (t_rnd_maybe ~i_rvars:irvs ts false None None None None @> t_log "\nrnd")
    @| (fun ju
        -> if count_except ju >= 3 then (t_rexcept_maybe None None @> t_log "\nrexcept") ju
           else T.t_id ju)
    @| (t_rnd_oracle_maybe ~i_rvars:iorvs ts None None None @> t_log "\nrnd_oracle")
    @| (t_guard_maybe @> t_log "\nadd_test")
    @| (t_case_ev_maybe @> t_log "\ncase_ev")
  in
      (t_prepare @> t_after_simp)
   @> (    t_close
       @|| (if must_finish && finish_now then T.t_fail "not finished" else t_progress))

and bycrush stats ts get_pt j ps1 =
  let step = t_crush_step j stats ts true in
  let psis = psis_of_pt (get_pt (prove_by_admit "current" ps1)) in
  let gs = ps1.CR.subgoals in
  assert (L.length gs = L.length psis);
  mapM (fun (psi,g) -> step (j <= 0) psi g) (L.combine psis gs) >>= fun pss ->
  let ps2 = CR.merge_proof_states pss ps1.CR.validation in
  if j > 1 then (
    mplus
      (guard (ps2.CR.subgoals = []) >>= fun _ -> ret ps2)
      (guard (ps2.CR.subgoals <> []) >>= fun _ -> bycrush stats ts get_pt (j - 1) ps2)
  ) else (
    (* return only finished pstates *)
    guard (ps2.CR.subgoals = []) >>= fun _ ->
    ret ps2
  )

and crush stats ts get_pt j ps1 =
  let step = t_crush_step j stats ts false in
  let psis = psis_of_pt (get_pt (prove_by_admit "current" ps1)) in
  let gs = ps1.CR.subgoals in
  assert (L.length gs = L.length psis);
  mapM (fun (psi,g) -> step (j <= 0) psi g) (L.combine psis gs) >>= fun pss ->
  let ps2 = CR.merge_proof_states pss ps1.CR.validation in
  if j > 1 then (
    (* return only proof states with exactly i steps *)
    crush stats ts get_pt (j - 1) ps2
  ) else (
    ret ps2
  )

and t_crush must_finish mi ts ps ju =
  let i = O.default 5 mi in
  let get_pt ps' =
    CR.get_proof
      (prove_by_admit "others" (first (T.apply_first (fun _ -> ret ps') ps)))
  in
  let stats = ref { nstates = 0; unqstates = 0; ses = [] } in
  if i > 0 then (
    let res =
      if must_finish then
        bycrush stats ts get_pt i (first (T.t_id ju))
      else
        crush stats ts get_pt i (first (T.t_id ju))
    in
    let s = match pull res with
      | Left _  -> "proof failed"
      | Right _ -> "proof found"
    in
    log_i
      (lazy (fsprintf "%s, visited %i proof states (%i unique).@\n%!"
               s !stats.nstates !stats.unqstates));
    res
  ) else (
    T.t_fail "crush: number of steps cannot be smaller than one" ju
  )
