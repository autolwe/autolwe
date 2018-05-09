(* * Goals and mappings from strings to variables/symbols. *)

(* ** Imports and abbreviations *)
open Util
open TheoryTypes

module Ht = Hashtbl
module T = Type
module G = Game

(* ** Proof state creation and manipulation
 * ----------------------------------------------------------------------- *)

let mk_ts () = {
  ts_lvars      = Hashtbl.create 20;
  ts_gvars      = Hashtbl.create 20;
  ts_rodecls    = Mstring.empty;
  ts_constdecls = Mstring.empty;
  ts_tydecls    = Mstring.empty;
  ts_odecls     = Mstring.empty;
  ts_adecls     = Mstring.empty;
  ts_emdecls    = Mstring.empty;
  ts_fmapdecls  = Mstring.empty;
  ts_assms_dec  = Mstring.empty;
  ts_assms_comp = Mstring.empty;
  ts_game_defs  = Mstring.empty;
  ts_ps         = BeforeProof
}

let get_proof_state ts =
  match ts.ts_ps with
  | ActiveProof (g,_,_,_) -> g
  | BeforeProof           -> tacerror "cannot apply tactic: no active proof"
  | ClosedTheory _        -> tacerror "cannot apply tactic: theory closed"

let get_proof_state_back ts =
  match ts.ts_ps with
  | ActiveProof (_,_,bg,_)  -> bg
  | BeforeProof             -> tacerror "cannot apply tactic: no active proof"
  | ClosedTheory _          -> tacerror "cannot apply tactic: theory closed"

let get_proof_tree ts =
  match ts.ts_ps with
  | ActiveProof _   -> tacerror "cannot obtain proof tree, finish proof with qed "
  | BeforeProof     -> tacerror "cannot obtain proof, no proof started yet"
  | ClosedTheory pt -> pt

let create_lenvar ts s =
  try Ht.find ts.ts_lvars s
  with Not_found ->
    let lv = T.Lenvar.mk s in
    Ht.add ts.ts_lvars s lv;
    lv

let create_groupvar ps s =
  try Ht.find ps.ts_gvars s
  with Not_found ->
    let gv = T.Groupvar.mk s in
    Ht.add ps.ts_gvars s gv;
    gv

(*
let create_psym ps s ty_dom =
  try
    let ps = Ht.find ps.ts_permdecls s in
    assert (equal_ty ps.Psym.dom ty_dom);
    ps
  with Not_found ->
    let pid = T.Permvar.mk s in
    Ht.add ps.ts_permvars s pid;
    pid
*)
