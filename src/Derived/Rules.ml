(* * Infrastructure for defining derived rules. *)

(* ** Imports and abbreviations *)
open Nondet
open Abbrevs
open Util
open Syms
open Type
open Expr
open ExprUtils
open Game
open Assumption
open CoreTypes
open CoreRules
open Tactic

module Ht = Hashtbl

(* ** Operators for tacticals
 * ----------------------------------------------------------------------- *)

let ( @> ) = t_seq

let ( @>> ) = t_seq_list

let ( @>>= ) = t_bind

let ( @>= ) = t_bind_ignore

let ( @| ) = t_or

let (@||) t1 t2 ju =
  let pss = t1 ju in
  match pull pss with (* try to preserve error from first call *)
  | Left (Some s) -> mplus (t2 ju) (mfail s)
  | Left None -> t2 ju
  | Right(_) -> pss

let rec t_seq_fold = function
  | []    -> t_id
  | t::ts -> t @> t_seq_fold ts

let rec t_or_fold = function
  | []    -> t_id
  | t::ts -> t @| t_or_fold ts

let t_print log s ju =
  log (lazy (fsprintf "%s:@\n%a" s pp_ju ju));
  t_id ju

let t_debug log s g =
  log (lazy s);
  t_id g

let t_guard f ju =
  if f ju then t_id ju else mempty

let t_dist_eq ju =
  match ju.ju_pr with
  | Pr_Dist _se' ->
    (* let se = ju.ju_se in *)
    (* if equal_sec_exp se se' then *)
      core_tactic CoreRules.ct_dist_eq ju
    (* else
      (Tactic.t_conv true se' @> core_tactic CoreRules.ct_dist_eq) ju *)
  | _ ->
    tacerror "dist_eq: Dist judgment expected"

let t_occurs is_in e oi ju =
  let ne = Norm.norm_expr_strong e in
  let occurs_expr e' =
    e_exists (equal_expr e) e'
    || e_exists (equal_expr ne) (Norm.norm_expr_strong e')
  in
  let occurs_cmd ju =
    let occ = ref false in
    let se = ju.ju_se in
    (match oi with
     | Some i ->
       let cmd,_ = get_se_ctxt se i in
       iter_gcmd_exp (fun e -> occ := !occ || occurs_expr e) cmd
     | None ->
       iter_se_exp (fun e -> occ := !occ || occurs_expr e) se);
    if is_in then !occ else not !occ
  in
  t_guard occurs_cmd ju

(* ** Extracting samplings, lets, and guards from game
 * ----------------------------------------------------------------------- *)

let pp_samp fmt (i,(vs,d)) =
  F.fprintf fmt "%i: %a from %a" i VarSym.pp vs (pp_distr ~qual:Unqual) d

let pp_osamp fmt ((i,j,k,otype),(vs,d)) =
  F.fprintf fmt "(%i,%i,%i,%a): %a from %a" i j k VarSym.pp vs (pp_distr ~qual:Unqual) d pp_otype otype

let pp_let fmt (i,(vs,e)) =
  F.fprintf fmt "%i: %a = %a" i VarSym.pp vs pp_expr e

let samplings gd =
  let samp i = function
    | GSamp(vs,(t,e)) -> Some (i,(vs,(t,e)))
    | _               -> None
  in
  cat_Some (L.mapi samp gd)

let osamplings gd =
  let lcmds_samplings gpos opos otype lcmds =
    let samp i = function
    | LSamp(vs,(t,e)) -> Some ((gpos,opos,i,otype),(vs,(t,e)))
    | _               -> None
    in
    cat_Some (L.mapi samp lcmds)
  in
  let obody_samplings i opos otype (lcmds,_) =
    lcmds_samplings i opos otype lcmds
  in
  let odecl_samplings i opos od =
    match od with
    | Oreg ob -> obody_samplings i opos Onothyb ob
    | Ohyb oh ->
        obody_samplings i opos (Oishyb OHless)    oh.oh_less
      @ obody_samplings i opos (Oishyb OHeq)      oh.oh_eq
      @ obody_samplings i opos (Oishyb OHgreater) oh.oh_greater
  in
  let samp i = function
    | GCall(_,_,_,odefs) ->
      L.concat (L.mapi (fun opos (_,_,od,_) -> odecl_samplings i opos od) odefs)
    | _ -> []
  in
  L.concat (L.mapi samp gd)

let oguards gd =
  let lcmds_guards gpos opos otype lcmds =
    let samp i = function
    | LGuard(e) -> Some ((gpos,opos,i,otype),e)
    | _              -> None
    in
    cat_Some (L.mapi samp lcmds)
  in
  let obody_guards i opos otype (lcmds,_) =
    lcmds_guards i opos otype lcmds
  in
  let odecl_guards i opos od =
    match od with
    | Oreg ob -> obody_guards i opos Onothyb ob
    | Ohyb oh ->
        obody_guards i opos (Oishyb OHless)    oh.oh_less
      @ obody_guards i opos (Oishyb OHeq)      oh.oh_eq
      @ obody_guards i opos (Oishyb OHgreater) oh.oh_greater
  in
  let samp i = function
    | GCall(_,_,_,odefs) ->
      L.concat (L.mapi (fun opos (_,_,odecl,_) -> odecl_guards i opos odecl) odefs)
    | _ -> []
  in
  L.concat (L.mapi samp gd)

let lets gd =
  let get_let i = function
    | GLet(vs,e) -> Some (i,(vs,e))
    | _          -> None
  in
  cat_Some (L.mapi get_let gd)

(* ** Move maximum amount forward and backward
 * ----------------------------------------------------------------------- *)

let rec parallel_moves old_new_pos =
  let upd_pos op np p =
    (* op .. p .. np, if p = np before then p moves one to the right *)
    if op < np && op < p && p <= np then p - 1
    (* np .. p .. op, if p = np before then p moves one to the left *)
    else if np < op && np <= p && p < op then p + 1
    else p
  in
  match old_new_pos with
  | [] -> []
  | (op,np)::old_new_pos ->
    (op,np - op)::parallel_moves (L.map (fun (op',np') -> (upd_pos op np op',np')) old_new_pos)

type dir = ToFront | ToEnd

let vars_dexc rv es = e_vars (mk_Tuple ((mk_V rv)::es))

let move_max dir i se vs =
  let step = if dir=ToEnd then 1 else -1 in
  let rec aux j =
    if i+j < L.length se.se_gdef && 0 <= i+j then (
      let gcmd = get_se_gcmd se (i+j) in
      let cmd_vars = Se.union (write_gcmd gcmd) (read_gcmd gcmd) in
      if not (Se.is_empty (Se.inter vs cmd_vars)) then j - step else aux (j+step)
    ) else (
      j - step
    )
  in
  aux step

let t_move_max dir i vs ju =
  let se = ju.ju_se in
  let offset = move_max dir i se vs in
  let move_samp =
    if offset = 0
    then t_id
    else core_tactic (ct_move i offset)
  in
  move_samp ju >>= fun ps -> ret (i+offset,ps)

let t_move_others_max dir i ju =
  let se = ju.ju_se in
  let samps = samplings se.se_gdef in
  let samp_others =
    L.filter_map
      (fun (j,(rv,(ty,es))) ->
        if ((j > i && dir=ToFront) || (j < i && dir=ToEnd)) && equal_ty ty mk_Fq
        then Some (j,(rv,vars_dexc rv es)) else None)
      samps
  in
  let samp_others =
    (* when pushing forward, we start with the last sampling to keep indices valid *)
    if dir=ToEnd then L.sort (fun a b -> - (compare (fst a) (fst b))) samp_others
    else samp_others
  in
  let rec aux i samp_others =
    match samp_others with
    | [] ->
      (fun ju ->
        t_id ju >>= fun ps ->
        ret (i,ps))
    | (j,(_rv,vs))::samp_others ->
      (fun ju ->
        t_move_max dir j vs ju >>= fun (j',ps) ->
        let i' =
          if (j > i && j' <= i) then i + 1
          else if (j < i && j' >= i) then i - 1
          else i
        in
        ret (i', ps)
      ) @>>= fun i -> aux i samp_others
  in
  aux i samp_others ju

(* ** Simplification and pretty printing
 * ----------------------------------------------------------------------- *)

let pp_rule ?hide_admit:(hide_admit=false) fmt ru =
  let open Game in
  match ru with
  | Rconv ->
    F.fprintf fmt "rconv"
  | Rmatfold (_wh,i,j) ->
    F.fprintf fmt "mat_fold %i %i" i j
  | Rmatunfold (_wh,i) ->
    F.fprintf fmt "mat_unfold %i" i
  | Rsep_dom(_,_) ->
    F.fprintf fmt "rsep_dom"
  | Rassert(p,e) ->
    F.fprintf fmt "rassert %i %a" p pp_expr e
  | Rtrans ->
    F.fprintf fmt "rtrans"
  | Rdist_eq ->
    F.fprintf fmt "dist_eq"
  | Rdist_sym ->
    F.fprintf fmt "dist_sym"
  | Rhybrid ->
    F.fprintf fmt "hybrid"
  | Rmove_main _ ->
    F.fprintf fmt "move_main"
  | Rmove(pos,delta) ->
    F.fprintf fmt "move %i %i" pos delta
  | Rexc(pos,es) ->
    F.fprintf fmt "except %i %a" pos (pp_list "," pp_expr) es
  | Rrnd(pos,vs,_,(v2,c2)) ->
    F.fprintf fmt "rnd %i %a@[<v>  %a -> %a@]" pos VarSym.pp vs VarSym.pp v2 pp_expr c2
  | Rrw_orcl((i,j,k,otype),_dir) ->
    F.fprintf fmt "rw_orcl (%i,%i,%i,%a)" i j k pp_otype otype
  | Rmove_orcl((i,j,k,otype),_i) ->
    F.fprintf fmt "move_orcl (%i,%i,%i,%a)" i j k pp_otype otype
  | Rrnd_orcl((i,j,k,otype),_c1,_c2)      ->
    F.fprintf fmt "rnd_orcl (%i,%i,%i,%a)" i j k pp_otype otype
  | Rexc_orcl((i,j,k,otype),_es)          ->
    F.fprintf fmt "exc_orcl (%i,%i,%i,%a)" i j k pp_otype otype
  | Radd_test((i,j,k,otype),e,_ads,_vss) ->
    F.fprintf fmt "add_test (%i,%i,%i,%a) (%a)" i j k pp_expr e pp_otype otype
  | Rcase_ev(_,e)   ->
    F.fprintf fmt "case @[<v 2>%a@]" pp_expr e
  | Rbad(i,_,_) | RbadOracle(i,_,_) ->
    F.fprintf fmt "bad%i" i
  | Rcheck_hash_args(i,j,k,_) ->
    F.fprintf fmt "check_hash_args (%i,%i,%i)" (i+1) (j+1) (k+1)
  | Rctxt_ev(_i,_c) ->
    F.fprintf fmt "ctxt %i" _i
  | Rinjective_ctxt_ev(_i,_c,_) ->
    F.fprintf fmt "injective_ctxt_ev %i" (_i+1)
  | Runwrap_quant_ev(_i) ->
    F.fprintf fmt "unwrap_quant_ev %i" (_i+1)
  | Rmove_quant_ev(_i) ->
    F.fprintf fmt "move_quant_ev %i" (_i+1)
  | Rremove_ev(is) ->
    F.fprintf fmt "remove [%a]" (pp_list "," pp_int) is
  | Rmerge_ev(_i,_j) ->
    F.fprintf fmt "merge"
  | Rsplit_ev(i) ->
    F.fprintf fmt "split %i" i
  | Rrw_ev(i,_dir) ->
    F.fprintf fmt "rw_ev %i" i
  | Rassm_dec(_rngs,_dir,_ren,assm) ->
    F.fprintf fmt "assm_dec(%s)" assm.ad_name
  | Rassm_comp(_,_ren,assm) ->
    F.fprintf fmt "assm_comp(%s)" assm.ac_name
  | Radmit _ ->
    if not hide_admit then F.fprintf fmt "radmit"
  | Rfalse_ev ->
    F.fprintf fmt "false_ev"
  | Rrnd_indep(b,i) ->
    F.fprintf fmt "rnd_indep %b %i" b i
  | Rguard ((i,j,k,otype),Some e) ->
    F.fprintf fmt "guard (%i,%i,%i,%a) (%a)" i j k pp_expr e pp_otype otype
  | Rguard ((i,j,k,otype),None) ->
    F.fprintf fmt "guard (%i,%i,%i) (%a)" i j k pp_otype otype
  | Rguess _ ->
    F.fprintf fmt "guess"
  | Rfind _ ->
    F.fprintf fmt "find"

let pp_path fmt path =
  let compressed_path =
    L.group_consecutive (=) path
    |> L.map (fun xs -> (L.hd xs, L.length xs))
  in
  let pp_entry fmt (p,l) =
    if l = 1
    then pp_int fmt p
    else F.fprintf fmt "%ix%i" p l
  in
  pp_list "_" pp_entry fmt compressed_path

let pp_unit fmt () = pp_string fmt ""

let wrap_info pp info =
  let s = fsprintf "%a" pp info in
  if s = "" then "" else "["^s^"]:"

let pp_proof_tree_verbose pp_info ?hide_admit:(hide_admit=false) fmt pt =
  let rec aux n pt =
    F.fprintf fmt
      ("@[%s@[<v 0>##########################@\n%a@\n##########################@\n"^^
          "%sapply %a@]@]@\n%!")
      (String.make n ' ')
      pp_ju pt.pt_ju
      (wrap_info pp_info pt.pt_info)
      (pp_rule ~hide_admit) pt.pt_rule;
    let len = L.length pt.pt_children in
    (* use indentation that reflects remaining proof obligations *)
    List.iteri (fun i pt -> aux (n + (len - 1 - i)*2) pt) pt.pt_children
  in
  aux 0 pt

let pp_proof_tree_non_verbose pp_info ?hide_admit:(hide_admit=false) fmt pt =
  let rec aux n pt =
    F.fprintf fmt "@[%s@[<v 0>%s%a@]@]@\n%!"
      (String.make n ' ')
      (wrap_info pp_info pt.pt_info)
      (pp_rule ~hide_admit) pt.pt_rule;
    let len = L.length pt.pt_children in
    (* use indentation that reflects remaining proof obligations *)
    List.iteri (fun i pt -> aux (n + (len - 1 - i)*2) pt) pt.pt_children
  in
  aux 0 pt

let pp_proof_tree pp_info ?hide_admit:(hide_admit=false) verbose =
  if verbose then pp_proof_tree_verbose pp_info ~hide_admit
  else pp_proof_tree_non_verbose pp_info ~hide_admit
(*i*)

let simplify_proof_tree pt =
  let rec simp pt =
    let children = L.map simp pt.pt_children in
    let pt = pt_replace_children pt children () in
    match pt.pt_rule, pt.pt_children with
    | Rconv,[pt1] ->
      begin match pt1.pt_rule, pt1.pt_children with
      | Rconv,[pt11] ->
        (* skip intermediate judgment *)
        let pss = t_conv true pt11.pt_ju.ju_se pt.pt_ju in
        let ps = Nondet.first pss in
        ps.validation [pt11]
      | _ ->
        pt
      end
    | _ -> pt
  in
  simp pt

let decorate_proof_tree pt =
  let rec go pos pt =
    let children =
      L.mapi (fun i pt -> go (pos@[i]) pt) pt.pt_children
    in
    pt_replace_children pt children pos
  in
  go [0] pt

let rec prove_by_admit s ps =
  if ps.subgoals = [] then
    ps
  else
    let ps = Nondet.first (apply_first (core_tactic (ct_admit s)) ps) in
    prove_by_admit s ps

let rec diff_proof_tree (pt1,pt2) =
  let is_Radmin ru = match ru with Radmit _ -> true | _ -> false in
  match pt1.pt_rule, pt2.pt_rule with
  | Radmit _, ru2 when not (is_Radmin ru2)  ->
    [ pt2 ]
  | _ ->
    conc_map diff_proof_tree (L.combine pt1.pt_children pt2.pt_children)
