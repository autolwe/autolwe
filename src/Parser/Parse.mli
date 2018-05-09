(* * Wrapper functions for parser with error handling. *)

open ParserTypes

val odef : string -> odef

val instruction : string -> instr list

val theory : string -> theory
