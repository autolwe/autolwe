(* * Tactics and Tacticals *)

(* ** Imports and abbreviations
 * ----------------------------------------------------------------------- *)
open CoreRules
open Nondet
open Abbrevs
open Game
open Expr
open ExprUtils
open Util
open Assumption
open Syms

(* ** Types
 * ----------------------------------------------------------------------- *)

(** A tactic takes a goal and returns a proof state. *)
type tactic = goal -> proof_state nondet

(** A tactic that takes a goal and returns a result and a proof state. *)
type 'a rtactic = goal -> ('a * proof_state) nondet

exception NoOpenGoal

(* ** Simple tactics and tacticals
 * ----------------------------------------------------------------------- *)

val move_first_last : proof_state -> proof_state
val apply_on_n : int -> tactic -> proof_state -> proof_state nondet
val apply_first : tactic -> proof_state -> proof_state nondet
val apply_all : tactic -> proof_state -> proof_state nondet
val rapply_all : 'a rtactic -> proof_state -> ('a * proof_state) nondet

val t_id : tactic
val t_seq : tactic -> tactic -> tactic
val t_seq_list : tactic -> tactic list -> tactic
val t_cut : tactic -> tactic

val t_try : tactic -> tactic
val t_or  : tactic -> tactic -> tactic
val t_fail : ('a, F.formatter, unit, 'b nondet) format4 -> 'c -> 'a
val t_ensure_progress : tactic -> tactic

val t_bind : 'a rtactic -> ('a -> 'b rtactic) -> 'b rtactic
val t_bind_ignore : 'a rtactic -> ('a -> tactic) -> tactic

(* ** Lifting core tactics
 * ----------------------------------------------------------------------- *)

val core_tactic : core_tactic -> tactic

val t_conv : bool -> sec_exp -> tactic

val t_matfold : bool -> int -> int -> string option -> tactic

val t_matunfold : bool -> int -> (string * string) option -> tactic

val t_assm_dec : direction -> renaming -> CoreTypes.rng list -> assm_dec -> tactic

val t_assm_comp : assm_comp -> (int * int) list  -> renaming -> tactic

val t_move : gcmd_pos -> int -> tactic

val t_sep_dom : MapSym.t -> MapSym.t -> tactic

val t_except : gcmd_pos -> expr list -> tactic

val t_remove_ev : int list -> tactic

val t_case_ev : ?flip:bool -> ?allow_existing:bool -> expr -> tactic

val t_guard : ocmd_pos -> expr option -> tactic

val t_move_oracle : ocmd_pos -> int -> tactic

val t_rewrite_oracle : ocmd_pos -> direction -> tactic

val t_guess : AdvSym.t -> vs list ->  tactic

val t_split_ev  : int -> tactic

val t_rw_ev  : int -> direction -> tactic

val t_ctxt_ev : int -> ctxt -> tactic

val t_false_ev : tactic

val t_rnd_oracle : ocmd_pos -> ctxt -> ctxt -> tactic

val t_rnd : gcmd_pos -> ctxt -> ctxt -> tactic

val t_merge_ev  : int -> int -> tactic

val t_random_indep : tactic

val t_trans : sec_exp -> tactic

val t_except_oracle : ocmd_pos -> expr list -> tactic

val t_admit : string -> tactic

val t_dist_sym : tactic

val t_dist_eq : tactic

val t_assert : gcmd_pos -> expr -> tactic

val t_move_main : ocmd_pos_eq -> string -> tactic

val t_hybrid : gcmd_pos -> int -> lcmd list -> expr -> tactic

val t_find : vs list * expr -> expr -> AdvSym.t -> vs list -> tactic

val t_add_test : ocmd_pos -> expr -> AdvSym.t -> vs list -> tactic
