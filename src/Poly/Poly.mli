(* * [IntRing] implementation of [Ring] and [MakePoly] functor. *)

open PolyInterfaces

module IntRing : (Ring with type t = Big_int.big_int)

module MakePoly (V : Var) (C : Ring) : Poly with type var = V.t and type coeff = C.t 

module SP : (Poly with type var := string and type coeff := Big_int.big_int)

module IP : (Poly with type var := int and type coeff := Big_int.big_int)

type ipoly = IP.t
