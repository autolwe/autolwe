(* * Core rules of the logic. *)

(* ** Imports and abbreviations *)
open Game
open Syms
open Expr
open ExprUtils
open Assumption
open Util
open CoreTypes

(* ** Types for proofs and tactics
 * ----------------------------------------------------------------------- *)

type 'info iproof_tree = private {
  pt_children : ('info iproof_tree) list;
  pt_rule     : rule_name;
  pt_ju       : judgment;
  pt_info     : 'info
}

type proof_tree = unit iproof_tree

val pt_replace_children :
  'b iproof_tree -> ('a iproof_tree) list -> 'a -> 'a iproof_tree

type goal = judgment

type validation = proof_tree list -> proof_tree

type proof_state = {
  subgoals   : goal list;
  validation : validation
}

type core_tactic = goal -> (proof_state, string lazy_t) BatResult.t

(* ** Simple tactics and tacticals
 * ----------------------------------------------------------------------- *)

val mk_name : ?name:string -> sec_exp -> string
val get_proof : proof_state -> proof_tree
val merge_proof_states : proof_state list -> (proof_tree list -> proof_tree) -> proof_state

(* ** Core rules of the logic
 * ----------------------------------------------------------------------- *)

val ct_conv : bool -> sec_exp -> core_tactic

(* Matrix fold/unfold sampling *)

val ct_matfold : string option -> bool -> int -> int -> core_tactic

val ct_matunfold : (string * string) option -> bool -> int -> core_tactic

(** [rtans new_se] an be used to replace the current security
    experiment [se] with [new_se] after proving that [se] and
    [new_se] are indistinguishable *)
val ct_trans : sec_exp -> core_tactic

(** [ct_sep_dom ms1 ms2 ju] returns the judgment resulting from
    ... *)
val ct_sep_dom : MapSym.t -> MapSym.t -> core_tactic

(** [ct_move p i ju] returns the judgment resulting from moving the
    command at position [p] [i] positions forward. *)
val ct_move : gcmd_pos -> int -> core_tactic

(** [r_rnd p ctx1 ctx2 ju] returns the judgment resulting
    from replacing the sampling [r <- d] at position [p]
    with [r <- d; let r = ctx1]. The rule checks that [ctx2]
    is the inverse of [ctx1]. *)
val r_rnd : gcmd_pos -> ctxt -> ctxt -> goal -> rule_name * goal list
val ct_rnd : gcmd_pos -> ctxt -> ctxt -> core_tactic

val ct_assert : gcmd_pos -> expr -> core_tactic

(** [ct_ctxt_ev i ctx ju] returns the judgment resulting from
    replacing the [i]-th conjunct in the event of [ju]
    with (a) [ctx(a) = ctx(b)] if it is equal to [a = b]
    and (b) [ ctx(a) in \[ ctx(b) | x in l \] ] if it
    is equal to [ a in \[ b | x in l\]]. *)
val ct_ctxt_ev : int -> ctxt -> core_tactic

val ct_injective_ctxt_ev : int -> ctxt -> ctxt -> core_tactic

val ct_case_ev : ?flip:bool -> ?allow_existing:bool -> expr -> core_tactic

val ct_remove_ev : int list -> core_tactic

val ct_false_ev : core_tactic

val ct_admit : string -> core_tactic

val ct_dist_sym : core_tactic

val ct_dist_eq : core_tactic

val ct_rw_ev  : int -> direction -> core_tactic

val ct_split_ev  : int -> core_tactic

val ct_merge_ev  : int -> int -> core_tactic

(** [rrandom p ctx1 ctx2 v ju] returns the judgment resulting
    from replacing the sampling [r <- d] at oracle position [p]
    with [r <- d; let v = ctx1[r]] and substituting v for r
    in the judgment. The rule checks that [ctx2] is the inverse
    of [ctx1]. *)
val ct_rnd_oracle : ocmd_pos -> ctxt -> ctxt -> core_tactic

(** [rexcept p es ju] returns the judgment resulting from replacing
    the sampling [r <- d \ es'] at position [p] in [ju] with the
    sampling [r <- d \ es], i.e., it replaces the (possibly empty)
    set of excepted values [es'] with [es]. *)
val ct_except : gcmd_pos -> expr list -> core_tactic

(** [rexcept_oracle p es ju] returns the judgment resulting from
    replacing the sampling [r <- d \ es'] at oracle position [p]
    in [ju] with the sampling [r <- d \ es], i.e., it replaces the
    (possibly empty) set of excepted values [es'] with [es]. *)
val ct_except_oracle : ocmd_pos -> expr list -> core_tactic

(** [radd_test p tnew asym vs ju] returns the judgments resulting from
    adding the test [tnew] at oracle position [p = (i,j,k)]. The two new
    judgments for [ju = G : E] are (1) [ G' : E ] where [G'] is obtained
    from [G] by adding the test [tnew] to the oracle
    and (2) [ G'_{1..i}; vs <- A() : t /\ not tnew]
    where [G'_{1..i}] is the prefix of [G'] including [i] and [t] is
    the original test in the oracle. *)
val ct_add_test : ocmd_pos -> expr -> AdvSym.t -> vs list -> core_tactic

val ct_hybrid : gcmd_pos -> int -> lcmd list -> expr -> core_tactic

(** [rrewrite_oracle p d j] returns the judgment resulting from rewriting
    commands after oracle position [p] with the equality at position [p]
    in direction [d]. *)
val ct_rewrite_oracle : ocmd_pos -> direction -> core_tactic

(** [ct_move p i ju] returns the judgment resulting from swapping
    the command at oracle positions [p] [i] positons forward. *)
val ct_move_oracle : ocmd_pos -> int -> core_tactic

val ct_move_main : ocmd_pos_eq -> string -> core_tactic

(** [rrandom_indep ju] completes the proof of judgments of the
     form [(G; r <- d) : E] where [E = /\_i ci] and
     (a) [ci = (r = e)]  where r does not occur in e,
     (b) [ci = (e = r)]  where r does not occur in e, or
     (c) [ci = (r in L)] where r does not occur in L. *)
val ct_random_indep : core_tactic

(** [rassm_dec dir vmap assm ju] returns the judgment resulting from
    applying the decisional assumption [assm] with the variable renaming
    [vmap] in direction [dir] to [ju]. *)
val ct_assm_dec : direction -> renaming -> rng list -> assm_dec -> core_tactic

val ct_assm_comp : assm_comp -> (int * int) list  -> renaming -> core_tactic

(** [guard pos None] remove the test at position [pos].
    [guard pos (Some t)] add a test at postion  [pos]. *)
val ct_guard : ocmd_pos -> expr option -> core_tactic

val ct_guess : AdvSym.t -> vs list ->  core_tactic

val ct_find : vs list * expr -> expr -> AdvSym.t -> vs list ->  core_tactic
