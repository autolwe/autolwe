{
  open Parser
  open ParserTools

  let unterminated_comment () =
    raise (LexerError "unterminated comment")
  let unterminated_string () =
    raise (LexerError "unterminated string")

  let keyword_table = Hashtbl.create 53
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      [ (* declarations *)
        "random_function",          RANDOM_FUN                (* kw: decl        *)
      ; "random_oracle",            RANDOM_ORCL               (* kw: decl        *)
      ; "finite_map",               FINMAP                    (* kw: decl        *)
      ; "oracle",                   ORACLE                    (* kw: decl        *)
      ; "include",                  INCLUDE                   (* kw: decl        *)
      ; "bilinear_map",             BILINEAR_MAP              (* kw: decl        *)
      ; "succ",                     SUCC                      (* kw: decl        *)
      ; "adv",                      ADV                       (* kw: decl        *)
      ; "counter",                  COUNTER                   (* kw: decl        *)
      ; "once",                     ONCE                      (* kw: decl        *)
      ; "bound_dist",               BOUNDDIST                 (* kw: decl        *)
      ; "bound_succ",               BOUNDSUCC                 (* kw: decl        *)  
      ; "bound_adv",                BOUNDADV                  (* kw: decl        *)
      ; "game",                     GAME                      (* kw: decl        *)  
      ; "inf",                      INFTHEO                   (* kw: decl        *)
      ; "ppt",                      PPT                       (* kw: decl        *)
      ; "adversary",                ADVERSARY                 (* kw: decl        *)
      ; "operator",                 OPERATOR                  (* kw: decl        *)
      ; "type",                     TYPE                      (* kw: decl        *)
      ; "bound",                    BOUND                     (* kw: decl        *)
      ; "for",                      FOR                       (* kw: decl        *)
      ; "assumption",               ASSUMPTION                (* kw: decl        *)

      (* commands *)
      ; "extract",                  EXTRACT                   (* kw: cmd         *)
      ; "print_goals",              PRINTGOALS                (* kw: cmd         *)
      ; "print_goal",               PRINTGOAL                 (* kw: cmd         *)
      ; "print_proof",              PRINTPROOF                (* kw: cmd         *)
      ; "print_debug",              PRINTDEBUG                (* kw: cmd         *)
      ; "print_games",              PRINTGAMES                (* kw: cmd         *)
      ; "print_game",               PRINTGAME                 (* kw: cmd         *)
      ; "admit",                    ADMIT                     (* kw: cmd         *)
      ; "last",                     LAST                      (* kw: cmd         *)
      ; "qed",                      QED                       (* kw: cmd         *)
      ; "restart",                  RESTART                   (* kw: cmd         *)
      ; "back",                     BACK                      (* kw: cmd         *)
      ; "undo_back",                UNDOBACK                  (* kw: cmd         *)

      (* tactics *)
      ; "norm",                     RNORM                     (* kw: tactic      *)
      ; "norm_nounfold",            RNORM_NOUNFOLD            (* kw: tactic      *)
      ; "norm_unknown",             RNORM_UNKNOWN             (* kw: tactic      *)
      ; "norm_solve",               RNORM_SOLVE               (* kw: tactic      *)

      ; "ensure",                   RENSURE                   (* kw: tactic      *)
      ; "conv",                     RCONV                     (* kw: tactic      *)
      ; "sep_dom",                  SEP_DOM                   (* kw: tactic      *)
      ; "trans",                    RTRANS                    (* kw: tactic      *)
      ; "subst",                    RSUBST                    (* kw: tactic      *)
      ; "rename",                   RRENAME                   (* kw: tactic      *)
      ; "insert",                   RINSERT                   (* kw: tactic      *)
      ; "unfold" ,                  RLET_UNFOLD               (* kw: tactic      *)
      ; "abstract",                 RLET_ABS                  (* kw: tactic      *)


      ; "mat_fold",                 RMATFOLD
      ; "mat_unfold",               RMATUNFOLD

      ; "move",                     RMOVE                     (* kw: tactic      *)
      ; "move_main",                RMOVE_MAIN                (* kw: tactic      *)

      ; "rnd",                      RRND                      (* kw: tactic      *)
      ; "rnd_exp",                  RRND_EXP                  (* kw: tactic      *)

      ; "except",                   REXC                      (* kw: tactic      *)
      ; "except_oracle",            REXC_ORCL                 (* kw: tactic      *)


      ; "assumption_decisional",    ASSUMPTION_DECISIONAL     (* kw: tactic      *)
      ; "assumption_computational", ASSUMPTION_COMPUTATIONAL  (* kw: tactic      *)

      ; "dist_sym",                 RDIST_SYM                 (* kw: tactic      *)
      ; "dist_eq",                  RDIST_EQ                  (* kw: tactic      *)

      ; "simp",                     RSIMP                     (* kw: tactic      *)
      ; "bysimp",                   BYSIMP                    (* kw: tactic      *)
      ; "crush",                    RCRUSH                    (* kw: tactic      *)
      ; "bycrush",                  BYCRUSH                   (* kw: tactic      *)

      ; "rewrite_oracle" ,          RREWRITE_ORCL             (* kw: tactic      *)
      ; "bad1",                     RBAD1                     (* kw: tactic      *)
      ; "bad2",                     RBAD2                     (* kw: tactic      *)
      ; "check_hash_args",          RCHECK_HASH_ARGS          (* kw: tactic      *)
      ; "guess",                    RGUESS                    (* kw: tactic      *)
      ; "find",                     RFIND                     (* kw: tactic      *)
      ; "hybrid",                   RHYBRID                   (* kw: tactic      *)
      ; "add_test",                 RADD_TEST                 (* kw: tactic      *)

      ; "remove_ev",                RREMOVE_EV                (* kw: tactic      *)
      ; "split_ev",                 RSPLIT_EV                 (* kw: tactic      *)
      ; "split_ineq",               RSPLIT_INEQ_EV            (* kw: tactic      *)
      ; "case_ev",                  RCASE_EV                  (* kw: tactic      *)
      ; "rewrite_ev",               RREWRITE_EV               (* kw: tactic      *)
      ; "ctxt_ev",                  RCTXT_EV                  (* kw: tactic      *)

      ; "indep",                    RINDEP                    (* kw: tactic      *)
      ; "false_ev",                 RFALSE_EV                 (* kw: tactic      *)

      ; "deduce",                   DEDUCE                    (* kw: tactic      *)
      ; "field_exprs",              LISTFE                    (* kw: tactiv      *)

      (* programs *)
      ; "return",                   RETURN                    (* kw: prog        *)
      ; "assert",                   ASSERT                    (* kw: proc/tactic *)
      ; "guard",                    GUARD                     (* kw: prog/tactic *)
      ; "let",                      LET                       (* kw: prog        *)
      ; "with" ,                    WITH                      (* kw: prog        *)

      (* types *)
      ; "Fq",                       TFQ                       (* kw: type        *)
      ; "Zq",                       TFQ                       (* kw: type        *)
      ; "Bool",                     TBOOL                     (* kw: type        *)

      (* operators *)
      ; "forall",                   FORALL                    (* kw: op          *)
      ; "exists",                   EXISTS                    (* kw: op          *)
      ; "in",                       IN                        (* kw: op          *)
      ; "notin",                    NOTIN                     (* kw: op          *)
      ; "not",                      NOT                       (* kw: op          *)
      ; "in_dom",                   IN_DOM                    (* kw: dom         *)
      ; "is_set",                   IS_SET                    (* kw: dom         *)
      ; "log",                      LOG                       (* kw: op          *)
      ; "true",                     TRUE                      (* kw: op          *)
      ; "false",                    FALSE                     (* kw: op          *)
      ; "tr",                       TRANS
      ; "sl",                       SPLITLEFT
      ; "sr",                       SPLITRIGHT
      ]
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'
let simple_id = ['a'-'z']['a'-'z' '0'-'9']*
let mat_dim = '1' | simple_id
let number_id = ['a'-'z' '0'-'9']*
let ident = ['a'-'z' 'A'-'Z' ] ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*

rule lex = parse
  | blank+      { lex lexbuf }
  | "(*"        { comment lexbuf; lex lexbuf }
  | "(**"       { comment lexbuf; lex lexbuf }
  | "\""        { STRING (Buffer.contents (string (Buffer.create 0) lexbuf)) }
  | [' ' '\t']
  | newline     { Lexing.new_line lexbuf; lex lexbuf }
  | eof         { EOF }
  | "("         { LPAR }
  | ")"         { RPAR }
  | "{"         { LCBRACE }
  | "}"         { RCBRACE }
  | "!"         { EXCL }
  | ":"         { COLON }
  | ":="        { COLONEQ }
  | ";"         { SEMICOLON }
  | "?"         { QUESTION }
  | ","         { COMMA }
  | "/"         { SLASH }                                     (* kw: tactic *)
  | "//"        { SLASH2 }                                    (* kw: tactic *)
  | "/="        { SLASHEQ }                                   (* kw: tactic *)
  | "//="       { SLASH2EQ }                                  (* kw: tactic *)
  | "///="      { SLASH3EQ }                                  (* kw: tactic *)
  | "<-"        { LEFTARROW }                                 (* kw: prog   *)
  | "<-$"       { SAMP }                                      (* kw: prog   *)
  | "\\"        { BACKSLASH }                                 (* kw: prog   *)
  | "/\\"       { LAND }                                      (* kw: op     *)
  | "\\/"       { LOR }                                       (* kw: op     *)
  | "<>"        { NEQ }                                       (* kw: op     *)
  | "+"         { PLUS }                                      (* kw: op     *)
  | "++"        { XOR }                                       (* kw: op     *)
  | "-"         { MINUS }                                     (* kw: op     *)
  | "*"         { STAR }                                      (* kw: op     *)
  | "^"         { CARET }                                     (* kw: op     *)
  | "#"         { SHARP }                                     (* kw: op     *)
  | "`"         { BACKTICK }
  | "["         { LBRACK }
  | "]"         { RBRACK }
  | "="         { EQUAL }
  | "->"        { TO }
  | "<"         { LESS }
  | ">"         { GREATER }
  | "."         { DOT }
  | "_"         { UNDERSCORE }
  | "||"        { CONCAT }

  (* Keywords with special characters *)
  | "R:"        { INRIGHT }
  | "LR:"       { INBOTH }
  | "abstract*" { RLET_ABS_DED }                              (* kw: tactic *)
  | "trans*"    { RTRANSSTAR }                                (* kw: tactic *)

  (* Indexed types *)
  | "BS_"(simple_id as s)       { TBS(s) }                    (* kw: type   *)
  | "G"                         { TG("") }                    (* kw: type   *)
  | "Matrix_"                   {TMAT}
  | "G_"(number_id as s)        { TG(s) }                     (* kw: type   *)

  (* Type constructors *)
  | "List_"                     { TLIST }

  (* Indexed constants *)
  | "L_"(ident as s)            { LIST(s) }                   (* kw: op     *)
  | "0_"(number_id as s)        { ZBS(s) }                    (* kw: op     *)
  | "0_{"                        { MATZERO }
  | "I_{"                        { MATID }
  | "g"                         { GEN("") }                   (* kw: op     *)
  | "g_"(number_id as s)        { GEN(s) }                    (* kw: op     *)

  (* Nats and identifiers/keywords *)
  | ['0'-'9']['0'-'9']* as s    { NAT(int_of_string(s)) }
  | (ident as s)"["             { MGET_ID(s) } (* FIXME: hack *)
  | (ident as s)"[]"            { MVAR_ID(s) } (* FIXME: hack *)
  | ident as s
                                { try Hashtbl.find keyword_table s
                                  with Not_found -> ID s }


and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and string buf = parse
  | "\""          { buf }
  | "\\n"         { Buffer.add_char buf '\n'; string buf lexbuf }
  | "\\r"         { Buffer.add_char buf '\r'; string buf lexbuf }
  | "\\" (_ as c) { Buffer.add_char buf c   ; string buf lexbuf }
  | newline       { Buffer.add_string buf (Lexing.lexeme lexbuf); string buf lexbuf }
  | _ as c        { Buffer.add_char buf c   ; string buf lexbuf }
  | eof           { unterminated_string () }
