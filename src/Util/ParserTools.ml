(* * Useful functions for parsers and error messages *)

open Abbrevs

(* Use this in your lexer *)
exception LexerError of string

exception ParserError

type parse_error =
  { pe_char_start      : int
  ; pe_char_end        : int
  ; pe_line_start      : int
  ; pe_line_char_start : int
  ; pe_line_char_end   : int
  ; pe_line            : string
  ; pe_msg             : string }

exception ParseError of parse_error

let charpos_to_linepos s cp =
  let module E = struct exception Found of int * int * string end in
  let lines = BatString.nsplit s ~by:"\n" in
  let cur_line = ref 1 in
  let cur_cp = ref cp in
  try
    List.iter
      (fun ls ->
            let len = String.length ls in
            if !cur_cp < len then
              raise (E.Found(!cur_line,!cur_cp,ls));
            incr cur_line;
            cur_cp := !cur_cp - len - 1
       )
       lines;
    assert false
  with
    E.Found(l,cp,s) -> (l,cp,s)

let wrap_error f s =
  let sbuf = Lexing.from_string s in
  try
    `ParseOk (f sbuf)
  with
  | LexerError msg ->
    let start_pos = Lexing.lexeme_start sbuf in
    let end_pos = Lexing.lexeme_start sbuf in
    let len = end_pos - start_pos in
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    `ParseError
      { pe_char_start      =  start_pos
      ; pe_char_end        = end_pos
      ; pe_line_start      = line_pos
      ; pe_line_char_start = lstart_pos
      ; pe_line_char_end   = lstart_pos+len
      ; pe_line            = line
      ; pe_msg             = msg }
  | ParserError ->
    let start_pos = Lexing.lexeme_start sbuf in
    let end_pos = Lexing.lexeme_start sbuf in
    let len = end_pos - start_pos in
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    `ParseError
      { pe_char_start      =  start_pos
      ; pe_char_end        = end_pos
      ; pe_line_start      = line_pos
      ; pe_line_char_start = lstart_pos
      ; pe_line_char_end   = lstart_pos+len
      ; pe_line            = line
      ; pe_msg             = "parse error" }
  | e ->
    failwith
      (F.sprintf "Unexpected error while lexing/parsing: %s,\n%s"
         (Printexc.to_string e)
         (Printexc.get_backtrace ()))

let error_string file pe =
  (F.sprintf "%s:%i:%i %i:%i error: %s\n"
     file
     pe.pe_line_start pe.pe_line_char_start
     pe.pe_line_start pe.pe_line_char_end
     pe.pe_msg)
  ^(F.sprintf "%s\n" pe.pe_line)
  ^(F.sprintf "%s%s\n" (String.make pe.pe_line_char_start ' ') "^")

let wrap_error_exn f s =
  match wrap_error f s with
  | `ParseOk pres -> pres
  | `ParseError(pinfo) ->
    raise (ParseError(pinfo))

let parse ~parse file s =
  begin match parse s with
  | `ParseOk pres -> pres
  | `ParseError(pinfo) ->
    let s = error_string file pinfo in
    failwith s
  end
