(* * Bindings to factory C++ library for polynomial arithmetic (used in Singular) *)

open Poly

val div : ipoly -> ipoly -> ipoly

val gcd : ipoly -> ipoly -> ipoly

val gcd_div : ipoly -> ipoly -> ipoly * ipoly * ipoly

val factor : ipoly -> (ipoly * int) list

val reduce : ipoly -> ipoly -> ipoly

val reduce_zero : ipoly -> ipoly -> bool
