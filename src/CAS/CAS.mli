(* * Use Factory to perform computations on polynomials *)

open Expr

(** [mod_reduce a b] returns [true] if
    [a mod b = 0] for polynomials [a] and [b].
    The result is undefined if one of the arguments
    is not a polynomial after abstracting away all
    non-field subexpressions. *)
val mod_reduce : expr -> expr -> bool

(** [check_nz is_nz:a b] returns [true] if
    [b = 0] implies [a = 0].
    The result is undefined if one of the arguments
    is not a polynomial after abstracting away all
    non-field subexpressions. *)
val check_nz : is_nz:expr -> expr -> bool

(** [norm f e] returns the normal-form of [e]
    using [f] recursively to normalize all non-field
    subexpressions. *)
val norm : (expr -> expr) -> expr -> expr 
