(* * Unique identifiers. *)

open Abbrevs

(* module type ID = sig *)
(** Unique identifier. *)
type id

(** Returns the name. *)
val name : id -> string

(** Returns the tag. *)
val tag : id -> int

(** Pretty printer for [gid]. *)
val pp : F.formatter -> id -> unit

(** [equal] uses physical equality. *)
val equal : id -> id -> bool

(** The [hash] function is injective. *)
val hash : id -> int

(** Uses the [hash] function. *)
val compare : id -> id -> int

(** Create a new [id] with the given name, the assigned tag is guaranteed
    to be unique (in a program run). *)
val mk : string -> id

module M : Map.S     with type key = id
module S : Set.S     with type elt = id
module H : Hashtbl.S with type key = id
