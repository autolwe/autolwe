(* * Types for core rules *)

(* ** Imports *)
open Abbrevs
open Util
open Game
open Assumption
open Expr
open Syms
open ExprUtils

(* ** Judgments
 * ----------------------------------------------------------------------- *)

(** A probability tag associates a real number in [0,1] to a
    security experiment. The three tags are interpreted as follows
    for some $G : E$:
    - [Pr_Succ] stands for $Pr[ G : E ]$
    - [Pr_Adv] stands for $2 * Pr[ G : E ] - 1$
    - [Pr_Dist(G',E')] stands for $|Pr[ G:E ] - Pr[ G':E']|$
*)
type pr_tag =
  | Pr_Succ
  | Pr_Adv
  | Pr_Dist of sec_exp
  with compare

let pr_exp_equal pre1 pre2 =
  match pre1, pre2 with
  | Pr_Adv,Pr_Adv | Pr_Succ,Pr_Succ -> true
  | Pr_Dist(se1),Pr_Dist(se2) -> equal_sec_exp se1 se2
  | _ -> false

(** The judgment [(G:Ev, pt)] is valid if the corresponding
    probability (see above) is negligible. A proof additionally
    establishes a concrete relation between judgments. *)
type judgment = { ju_se : sec_exp; ju_pr : pr_tag }
  with compare

let equal_judgment ju1 ju2 =
  compare_judgment ju1 ju2 = 0

let pp_ju fmt ju =
  match ju.ju_pr with
  | Pr_Succ ->
    F.fprintf fmt "Pr[ G : E ] negligible where@\nG : E :=@\n@[<hv 2>  %a@\n  : %a@]"
      (pp_gdef ~nonum:false) ju.ju_se.se_gdef pp_expr ju.ju_se.se_ev
  | Pr_Adv ->
    F.fprintf fmt
      "Pr[ G : E ] - 1/2 negligible where@\nG : E :=@\n@[<hv 2>  %a@\n  : %a@]"
      (pp_gdef ~nonum:false) ju.ju_se.se_gdef pp_expr ju.ju_se.se_ev
  | Pr_Dist se ->
    F.fprintf fmt
      ("| Pr[ G : E ] - Pr[ G' : E' ] | negligible where@\n"^^
       "G : E := @\n@[<hv 2>  %a@\n  : %a@]@\n"^^
       "and G' : E' := @\n@[<hv 2>  %a@\n  : %a@]")
      (pp_gdef ~nonum:false) ju.ju_se.se_gdef pp_expr ju.ju_se.se_ev
      (pp_gdef ~nonum:false) se.se_gdef pp_expr se.se_ev

(* ** Low-level rules (extractable to EasyCrypt)
 * ----------------------------------------------------------------------- *)

type bad_version = UpToBad | CaseDist

type rng_orcl = 
  | RO_rng of int * int * OrclSym.t
  | RO_orcl of int * (int -> otype  -> ((int * int * OrclSym.t) list))

type rng = {
  r_start : int;
  r_end   : int;
  r_orcl  : rng_orcl list;
}

type rule_name =

(* *** Equivalence/small statistical distance: main *)

  (* Rename, unfold let, and normalize. *)
  | Rconv

  | Rmatfold of bool * int * int

  | Rmatunfold of bool * int

  (* [Rmove(p,i)]: move statement at [p] forward by [i]. *)
  | Rmove of gcmd_pos * int

  (* [Rnd(p,c_1,c_2,v)]: Perform optimistic sampling with
     bijection [c_1=c_2^{-1}] for [v] at position [p]. *)
  | Rrnd of gcmd_pos * vs  * ctxt * ctxt

  (* [Rexc(p,es)]: change sampling at $p$ to exclude expressions [es]. *)
  | Rexc of gcmd_pos * expr list


(* *** Equivalence/small statistical distance: oracle *)

  (* [Rrw_orcl(p,dir)]: rewrite oracle with equality test at [p] in [dir]. *)
  | Rrw_orcl   of ocmd_pos * direction

  (* [Rmove_orcl(op,i)]: swap statement at [p] forward by [i]. *)
  | Rmove_orcl of ocmd_pos * int

  (* [Rnd_orcl(p,c_1,c_2,v)]: rnd with [c_1=c_2^{-1}] for [v] at [p]. *)
  | Rrnd_orcl  of ocmd_pos * ctxt * ctxt

  (* [Rexc_orcl(p,es)]: change sampling at [p] to exclude $es$. *)
  | Rexc_orcl  of ocmd_pos * expr list

(* *** Case distinctions, up-to *)

  (* [Rcase(e)]: refine event by performing case distinction on [e]. *)
  | Rcase_ev  of bool * expr

  (* [Radd_test(p,e,a,vs)]: add test $e$ at position [p] to oracle,
     adversary [a] and [vs] used for bounding bad. *)
  | Radd_test of ocmd_pos * expr * ads * vs list

  (* [Rbad(p,v)]: Replace hash call at position [p] by random variable [v]. *)
  | Rbad             of int * gcmd_pos * vs
  | Rcheck_hash_args of ocmd_pos
  | RbadOracle       of int * ocmd_pos * vs

(* *** Implication rules for events *)

  (* [Rctxt_ev(i,c)]: apply context [c] to [i]-th conjunct in event. *)
  | Rctxt_ev   of int * ctxt

  (* [Rbijection_ev(i,c1,c2)]: apply bijective context [c1] to [i]-th conjunct in event *)
  | Rinjective_ctxt_ev of int * ctxt * ctxt

  | Runwrap_quant_ev of int
  | Rmove_quant_ev   of int

  (* [Rremove_ev(is)]: Remove given conjuncts. *)
  | Rremove_ev of int list

  (* [Rmerge_ev(i,j)]: Merge given conjuncts as equality on tuples. *)
  | Rmerge_ev  of int * int

  (* [Rsplit_ev(i)]: Split [i]-th event into separate equalities
     if it an equality on a tuple type. *)
  | Rsplit_ev  of int

  (* [Rrw_ev(i,d)]: Rewrite event using [i]-th conjunct in direction [d].
     If the conjunct is an inequality [a <> b], rewrite witb [(a=b) = false]. *)
  | Rrw_ev     of int * direction

  (* [Rassert(e)]: add [assert(e)] at position [e] after proving that [G : ev /\ not e] negl.
     Requires that evaluating [e] is stable after position [p]. *)
  | Rassert of gcmd_pos * expr

(* *** Apply assumption *)

  | Rassm_dec  of rng list * direction * renaming * assm_dec

  | Rassm_comp of (int * int) list * renaming * assm_comp

(* *** Terminal rules *)

  | Radmit of string

  | Rfalse_ev

  | Rrnd_indep of bool * int

  | Rdist_sym

  | Rdist_eq

  | Rtrans

  | Rhybrid (* FIXME: add arguments *)

  | Rmove_main of ocmd_pos_eq

(* *** Rules for finite maps *)

  | Rsep_dom of MapSym.t * MapSym.t

(* *** Rules for add test *)

  | Rguard  of ocmd_pos * expr option

  | Rguess  of ads

  | Rfind   of ads * (vs list * expr)
