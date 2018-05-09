(* * Utility functions
 * This module defines types tagged with [int]s, some convenience functor
 * applications for maps, sets, hashtables, and some convenience functions
 * for lists and pretty printing. *)

(* ** Imports *)
open Abbrevs

(* ** Convenience Functors
 * ----------------------------------------------------------------------- *)

(** [tag] converts [t] into an [int]. The function must be injective. *)
module type Tagged = sig type t val tag : t -> int end

(** Ordered and hashable (to [int]) types.
    Equal [hash] does not have to imply that [equal] returns [true]. *)
module type OrderedHash =
  sig
    type t
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
  end

(** Create [OrderedHash] from [Tagged]. Assumes that the [tag] function is injective. *)
module OrderedHash :
  functor (X : Tagged) ->
    sig
      type t = X.t
      val hash : t -> int
      val equal : t -> t -> bool
      val compare : t -> t -> int
    end

(** Convenience functor that creates [OrderedHash], [Map], [Set], and [Hashtbl] at once. *)
module StructMake : functor (X:Tagged) ->
  sig
    module T : OrderedHash with type t=X.t
    module M : Map.S with type key = T.t
    module S : Set.S with type elt=T.t
    module H : Hashtbl.S with type key = T.t
  end

module Mint : Map.S with type key = int
module Sint : Set.S with type elt = int
module Hint : Hashtbl.S with type key = int

module Sstring : Set.S with type elt = string
module Mstring : Map.S with type key = string

(* ** Misc functions
 * ----------------------------------------------------------------------- *)

(* placeholder for incomplete code *)
val fixme: string -> 'a

(** Returns a unique (in a program execution) [int]. *)
val unique_int : unit -> int

val swap : 'a * 'b -> 'b * 'a

(** [compare_on f x y] yields the comparison [compare (f x) (f y)] *)
val compare_on : ('a -> 'b) -> 'a -> 'a -> int

val assert_msg : bool -> string -> unit

type ('a,'b) either = Left of 'a | Right of 'b

type direction = LeftToRight | RightToLeft

val string_of_dir : direction -> string

val id : 'a -> 'a

val eq_on : ('a -> 'b) -> 'a -> 'a -> bool

(* ** File I/O
 * ----------------------------------------------------------------------- *)

val input_file : string -> string

val output_file : string -> string -> unit

val append_file : string -> string -> unit

(* ** Options
 * ----------------------------------------------------------------------- *)

(** [exc_to_opt f] returns [None] if [f ()] raises an
    exception and [Some (f ())] otherwise. *)
val exc_to_opt : (unit -> 'a) -> 'a option

(* ** List functions
 * ----------------------------------------------------------------------- *)

(** Same as [List.list_for_all2], but returns [false] if lists have different lengths. *)
val list_eq_for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

(**  [smart_map f l] returns the same result as [map f l], but
     ensures that sharing is preserved. For example,
     [smart_map (fun x -> x) l == l] *)
val smart_map : ('a -> 'a) -> 'a list -> 'a list

(** [drop k l] drop last [k] elements of [l]. If [l] is
     shorter than [k], the empty list is returned. *)
val drop_last : int -> 'a list -> 'a list

(** [split_n k l] returns [(rhd,a,tl)] such that
    [l = rev_append rhd (a::tl)] and [k = length rhd] *)
val split_n : int -> 'a list -> 'a list * 'a * 'a list

(** [cut_n k l] returns [(rhd,tl)] such that
    [l = List.rev_append rhd tl] and [k = List.length rhd] *)
val cut_n : int -> 'a list -> 'a list * 'a list

(** [list_from_to i j] returns the list with all natural
     numbers from [i] to [j-1]. *)
val list_from_to : int -> int -> int list

val find_at : ('a -> bool) -> 'a list -> int

val replicate_r : 'a list -> int -> 'a -> 'a list

val replicate   : int -> 'a -> 'a list

val lefts : (('a,'b) either) list -> 'a list

val rights : (('a,'b) either) list -> 'b list

val lefts_rights : (('a,'b) either) list -> ('a list * 'b list)

val cat_Some : 'a option list -> 'a list

val conc_map : ('a -> 'b list) -> 'a list -> 'b list

val move_front : ('a -> bool) -> 'a list -> 'a list

(**[list_equal e_equal l1 l2] returns true if the two lists are
   equal with respect to [e_equal]. *)
val equal_list : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

val compare_list :('a -> 'b -> int) -> 'a list -> 'b list -> int

(**[pair_equal e_equal l1 l2] returns true if the two pairs are
   equal with respect to [e_equal]. *)
val equal_pair : ('a -> 'b -> bool) -> ('c -> 'd -> bool) -> 'a * 'c -> 'b * 'd -> bool

val compare_pair :('a -> 'b -> int) -> ('c -> 'd -> int) -> 'a * 'c -> 'b * 'd -> int

val num_list : 'a list -> (int * 'a) list

val map_accum : ('b -> 'a -> 'b * 'c) -> 'b -> 'a list -> 'b * 'c list

(* ** String functions
 * ----------------------------------------------------------------------- *)

val splitn_by : string -> (string -> int -> bool) -> string list

val string_find_from : string -> string -> int -> int option

val string_rfind_from : string -> string -> int -> int option

val split : string -> string -> (string * string) option

(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

(** [pplist sep pp_elt f l] takes a formatter [f], a separator
    [sep], and a pretty printer for ['e] and returns a
    pretty printer for lists of elements from ['e] *)
val pp_list : ('a, 'b, 'c, 'd, 'd, 'a) format6 ->
  (F.formatter -> 'e -> unit) -> F.formatter -> 'e list -> unit

(** [pplist_c] is equivalent to [pp_list ","] *)
val pp_list_c : (F.formatter -> 'a -> unit) -> F.formatter -> 'a list -> unit

(** [pplist_s] pretty prints a list of strings *)
val pp_list_s : F.formatter -> string list -> unit

val pp_string : F.formatter -> string -> unit

val pp_int : F.formatter -> int -> unit

val pp_opt : (F.formatter -> 'a -> unit) -> F.formatter -> 'a option -> unit

val pp_if : bool -> ('a -> 'b -> 'c) -> ('a -> 'b -> 'c) -> 'a -> 'b -> 'c

val pp_around :
  string -> string -> (F.formatter -> 'a -> unit) -> F.formatter -> 'a -> unit

val pp_pair : (F.formatter -> 'a -> unit) -> (F.formatter -> 'b -> unit) -> F.formatter -> 'a * 'b -> unit

(** [fsprintf f] executes the format function with the standard
    string formatter. *)
val fsprintf : ('a, F.formatter, unit, string) format4 -> 'a

(* ** Logging and exceptions for Logic module
 * ----------------------------------------------------------------------- *)

exception Invalid_rule of string

(** [tacerror s] raises a rule application error with information [s]. *)
val tacerror : ('a, F.formatter, unit, 'b) format4 -> 'a

val fail_opt : 'a option -> string -> 'a

val mk_logger : string -> Bolt.Level.t -> string -> string Lazy.t -> unit

val log_ig : string Lazy.t -> unit

val get_buffer_log : unit -> string
