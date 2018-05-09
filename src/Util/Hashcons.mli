(* * Hash consing of values
 * Hash-consing registers all values of a given type in a hashtable.
 * If all values of the type are obtained using [S.hashcons] then this
 * guarantees that structural equality implies physical equality.
 * Additionally, the hash table maintains unique integer [tag]s
 * for each value of the type that can be used for [Map]s, [Set]s,
 * and [Hashtbl]s. *)

(** We can hashcons values for which the {!HashedType} interface is implemented. *)
module type HashedType = sig
  type t

  (** Equality function used for type. *)
  val equal : t -> t -> bool

  (** Return [int] hash of value used for hashtable storage and retrieval.
      Can be noninjective which degrades performance (collisions in hashtable). *)
  val hash : t -> int

  (** Function to assign tags to values. Usually, t is a record with an [int] field.
      The tag is unrelated to the hash and usually depends on the content of the hash
      table. *)
  val tag : int -> t -> t
end

(** The hashcons interface. *)
module type S = sig
  type t

  (** Register value in hashtable and set tag. *)
  val hashcons : t -> t
end

(** Make hashcons module for [HashedType]. *)
module Make : functor (H : HashedType) -> S with type t = H.t

(** Combine two integers for hash. *)
val combine : int -> int -> int

(** Combine three integers for hash. *)
val combine2 : int -> int -> int -> int

(** Combine list of integers for hash. *)
val combine_list : ('a -> int) -> int -> 'a list -> int

(** Combine list of integers for hash. *)
val combine_hashes : int list -> int
