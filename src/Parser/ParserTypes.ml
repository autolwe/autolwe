(* * Types for parser *)

(* ** Imports and abbreviations *)
open Game
open Syms
open Assumption
open Util

(* ** Types for parsed types, expressions, and games
 * ----------------------------------------------------------------------- *)
type parsedim =
  | PDBase of string
  | PDPlus of parsedim * parsedim

type parse_ty =
  | Bool
  | Fq
  | BS      of string
  | Mat     of parsedim * parsedim
  | List    of parsedim * parse_ty
  | G       of string
  | TySym   of string
  | Prod    of parse_ty list

let mk_Prod = function [t] -> t | ts -> Prod ts

type parse_expr =
  | V           of string qual * string
  | SApp        of string * parse_expr list
  | SLookUp     of string * parse_expr list
  | SIndom      of string * parse_expr
  | Tuple       of parse_expr list
  | Proj        of int * parse_expr
  | CB          of bool
  | CZ          of string
  | CGen        of string
  | MatZ        of parsedim * parsedim
  | MatI        of parsedim * parsedim
  | CFNat       of int
  | Mult        of parse_expr * parse_expr
  | Plus        of parse_expr * parse_expr
  | Exp         of parse_expr * parse_expr
  | Log         of parse_expr
  | Opp         of parse_expr
  | Trans       of parse_expr
  | SplitLeft   of parse_expr
  | SplitRight  of parse_expr
  | PListOf     of parse_expr * parsedim
  | Minus       of parse_expr * parse_expr
  | Inv         of parse_expr
  | Div         of parse_expr * parse_expr
  | Eq          of parse_expr * parse_expr
  | Not         of parse_expr
  | Ifte        of parse_expr * parse_expr * parse_expr
  | Land        of parse_expr * parse_expr
  | Lor         of parse_expr * parse_expr
  | Xor         of parse_expr * parse_expr
  | Quant       of Expr.quant * (string list * string) list *  parse_expr
  | Concat       of parse_expr * parse_expr

let mk_Tuple = function [t] -> t | ts -> Tuple ts

type parse_ctx = string * parse_ty option * parse_expr

type lcmd =
  | LLet   of string * parse_expr
  | LMSet  of string * parse_expr list * parse_expr
  | LBind  of string list * string
  | LSamp  of string * parse_ty * parse_expr list
  | LGuard of parse_expr

type lcomp = lcmd list * parse_expr

type odec = Odef of lcomp | Ohybrid of (lcomp * lcomp * lcomp)

type odef = string * string list * odec * ([ `Counter of string | `Once ] option)

type gcmd =
  | GLet    of string * parse_expr
  | GMSet   of string * parse_expr list * parse_expr
  | GAssert of parse_expr
  | GSamp   of string * parse_ty * parse_expr list
  | GCall   of string list * string * parse_expr * odef list

type gdef = CmdList of gcmd list | Gname of string


(* ** Types for parsed proof scripts and tactics
 * ----------------------------------------------------------------------- *)

type assgn_pos =
  | Pos    of int
  | Var    of string
  | AbsPos of int

type diff_cmd =
  | Drename of string * string * assgn_pos option
  | Dinsert of assgn_pos * gcmd list
  | Dsubst  of assgn_pos * parse_expr * parse_expr

type selector = InRight | InBoth (* InLeft is default *)

type range_pos = assgn_pos option * assgn_pos option

type range = int * int
type ranges = range_pos list


type range_oracle = 
  | RO_main of int * int * string
  | RO_in_o of int * (int * otype * (int * int * string) list) list

type range_o =  
  int * int * range_oracle list 
  
type renaming = (string qual * string) * (string qual * string)


type parse_ev = parse_expr

type tactic =
  | Rmatunfold     of bool option * int * (string * string) option
  | Rmatfold       of bool option * int * int * string option
  | Rnorm of bool
  | Rdist_eq
  | Rdist_sym
  | Rfalse_ev
  | Rnorm_nounfold
  | Rseq           of tactic list
  | Rrename        of string * string
  | Rsimp          of bool
  | Rnorm_unknown  of string list
  | Rnorm_solve    of parse_expr
  | Rensure        of assgn_pos option * bool * parse_expr
  | Rmove          of range_pos * assgn_pos
  | Rmove_oracle   of ocmd_pos * int
  | Rmove_to_main  of ocmd_pos_eq * string
  | Rmove_to_orcl  of assgn_pos * ocmd_pos_eq * string
  | Rctxt_ev       of int option * parse_ctx option
  | Rrnd           of bool * assgn_pos option * parse_ctx option *
                      parse_ctx option * parse_expr option
  | Rrnd_exp       of bool * (string * string option) list
  | Rrnd_orcl      of ocmd_pos option * parse_ctx option * parse_ctx option
  | Rconv          of gdef option * parse_ev
  | Rtrans         of gdef * parse_ev
  | Rtrans_diff    of diff_cmd list
  | Rassm_dec      of bool * string option * direction option * ranges *
                      (string list) option
  | Rassm_dec_o    of string * direction * renaming list * 
                        range_o list
  | Rassm_comp     of bool * string option * ranges
  | Rlet_abs       of assgn_pos option * string * parse_expr option *
                      assgn_pos option * bool
  | Rlet_abs_orcl  of ocmd_pos * string * parse_expr * int option * bool
  | Rlet_abs_ded   of bool * assgn_pos * string * parse_expr * assgn_pos option
  | Rassert        of assgn_pos * parse_expr option
  | Rsubst         of assgn_pos option * parse_expr * parse_expr * assgn_pos option
  | Rlet_unfold    of assgn_pos list
  | Rindep         of bool
  | Rcrush         of bool * int option
  | Rbad           of int * assgn_pos option * string
  | Rcheck_hash_args of ocmd_pos
  | Rexcept        of assgn_pos option * (parse_expr list) option
  | Rexcept_orcl   of ocmd_pos * parse_expr list
  | Radd_test      of ocmd_pos option * parse_expr option * string option *
                      (string list) option
  | Rhybrid        of (int * int) * lcomp
  | Rrewrite_orcl  of ocmd_pos * direction
  | Rcase_ev       of parse_expr option
  | Rremove_ev     of int list
  | Rrewrite_ev    of int * direction
  | Rsplit_ev      of int
  | Rsplit_ineq    of int
  | Deduce         of bool * parse_expr list * parse_expr
  | FieldExprs     of parse_expr list
  | Rguard         of ocmd_pos * parse_expr option
  | Rguess         of string * string list
  | Rfind          of (string list * parse_expr) * parse_expr * string * string list
  | Rsep_dom       of string * string

type instr =
  | Include    of string
  | BoundDecl  of string * string
  | TyDecl     of string
  | RODecl     of string * parse_ty * parse_ty
  | RFDecl     of string * parse_ty * parse_ty
  | FMDecl     of string * parse_ty * parse_ty
  | FunDecl    of string * parse_ty * parse_ty
  | EMDecl     of string * string * string * string
  | ODecl      of string * parse_ty * parse_ty
  | ADecl      of string * parse_ty * parse_ty
  | AssmDec    of string * bool * gcmd list * gcmd list * (string list) list
  | AssmComp   of string * bool * assm_type * gcmd list * parse_ev * string list list
  | JudgSucc   of gdef * parse_ev
  | JudgAdv    of gdef * parse_ev
  | JudgDist   of gdef * parse_ev * gdef * parse_ev
  | GameDef    of string * gdef
  | PrintGoal  of string
  | PrintGoals of string
  | PrintProof of bool * string option
  | Apply      of tactic
  | UndoBack   of bool
  | Extract    of string
  | Debug      of string
  | PrintGame  of string
  | PrintGames of string * string
  | Admit
  | Last
  | Back
  | Qed
  | Restart

type theory = instr list
