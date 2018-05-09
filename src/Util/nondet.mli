(* * Nondeterministic computations (aka lazy lists) *)

(* ** Imports *)
open Util

(* ** Nondeterminism Monad
 * ----------------------------------------------------------------------- *)

type 'a stream

type 'a nondet

val ret : 'a -> 'a nondet

val mempty : 'a nondet

(** Combine results returned by [a] with results returned by [b].
    [mplus] preserves order, i.e., results from [a] occur before
    results from [b]. *)
val mplus : 'a nondet -> 'a nondet -> 'a nondet

val fmap : ('a -> 'b) -> 'a nondet -> 'b nondet

val bind : 'a nondet -> ('a -> 'b nondet) -> 'b nondet

val guard : bool -> unit nondet

(** Execute and get first [n] results as list, use [n=-1] to get all values. *)
val run : int -> 'a nondet -> 'a list

(* ** Useful functions
 * ----------------------------------------------------------------------- *)

(** Apply function [f] to the first n values, use [n=-1] to apply [f] to all values. *)
val iter : int -> 'a nondet -> ('a -> unit) -> unit

val sequence : ('a nondet) list -> ('a list) nondet

val mapM : ('a -> 'b nondet) -> 'a list -> ('b list) nondet

val foreachM : 'a list -> ('a -> 'b nondet) -> ('b list) nondet

val mconcat : 'a list -> 'a nondet

val msum : ('a nondet) list -> 'a nondet

val (>>=) : 'a nondet -> ('a -> 'b nondet) -> 'b nondet

(** Return all subsets $S$ of $m$ such that $|S| \leq k$. *)
val pick_set : int -> 'a nondet -> ('a list) nondet

(** Return all subsets $S$ of $m$ such that $|S| = k$. *)
val pick_set_exact : int -> 'a nondet -> ('a list) nondet

(** Return the cartesian product of $m1$ and $m2$. *)
val cart : 'a nondet -> 'b nondet -> ('a * 'b) nondet

(** Return the cartesian product of $m$. *)
val prod : 'a nondet -> ('a * 'a) nondet

(** Return the $n$-fold cartesian product of $ms$. *)
val ncart : 'a nondet list -> ('a list) nondet

(** Return the $n$-fold cartesian product of $m$. *)
val nprod : 'a nondet -> int -> ('a list) nondet

val insertions : 'a list -> 'a -> 'a list -> 'a list nondet

val permutations : 'a list -> 'a list nondet

val is_nil : 'a nondet -> bool

val pull : 'a nondet -> ((string lazy_t) option, ('a * 'a nondet)) either

val first : 'a nondet -> 'a

val mfail : string lazy_t -> 'a nondet
