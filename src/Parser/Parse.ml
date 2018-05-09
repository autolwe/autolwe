(* * Wrapper functions for parser with error handling. *)

module S = String
module PT = ParserTools

let convert_error f =
  PT.wrap_error_exn
    (fun sbuf ->
      try  f sbuf
      with Parser.Error -> raise PT.ParserError)

(** Parse oracle definition. *)
let odef = convert_error (Parser.odef Lexer.lex)

(** Parse instruction definition. *)
let instruction = convert_error (Parser.instruction Lexer.lex)

(** Parse theory definition. *)
let theory = convert_error (Parser.theory Lexer.lex)
