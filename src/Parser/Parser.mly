%{
  (* Parser for expressions, games, judgments, and tactic command. *)
  open ParserTypes
  open Syms
  open Abbrevs
  open Assumption
  open Util

  module G = Game

%}

/*======================================================================
(* * Tokens *) */

/*----------------------------------------------------------------------
(* ** Misc Tokens *) */

%token EOF
%token <string> STRING
%token <int> NAT
%token UNDERSCORE DOT EXCL SHARP BACKTICK BACKSLASH SLASH
%token COLON QUESTION COLONEQ
%token LPAR RPAR LBRACK RBRACK LCBRACE RCBRACE

/*----------------------------------------------------------------------
(* ** Tokens for types *) */

%token <string> TBS
%token TMAT
%token TLIST
%token TBOOL TFQ 
%token <string> TG

/*----------------------------------------------------------------------
(* ** Tokens for expressions *) */

%token <string> ID

%token PLUS XOR MINUS CONCAT
%left PLUS XOR MINUS CONCAT

%token TRANS SPLITLEFT SPLITRIGHT

%token STAR
%left  STAR

%token LAND %left  LAND

%token LOR
%left  LOR

%token NOT

%token EQUAL NEQ GREATER LESS

%token CARET
%token LOG
%token TRUE FALSE
%token FORALL EXISTS


%token IN NOTIN

%token COMMA 

%token <string> MGET_ID
%token <string> MVAR_ID

%token MATZERO MATID
%token <string> GEN
%token <string> ZBS

/*----------------------------------------------------------------------
(* ** Tokens for games *) */

%token LEFTARROW LET RETURN SAMP SEMICOLON WITH ASSERT GUARD
%token <string> LIST
%token COUNTER ONCE
(* %token <string> LOOKUP *)

/*----------------------------------------------------------------------
(* ** Tokens for theories *) */

%token TO IN_DOM IS_SET INCLUDE
%token ADVERSARY ORACLE OPERATOR TYPE
%token ASSUMPTION
%token RANDOM_ORCL RANDOM_FUN FINMAP
%token BILINEAR_MAP
%token SUCC ADV
%token BOUNDDIST BOUNDSUCC BOUNDADV
%token PPT INFTHEO
%token BOUND FOR GAME

/*----------------------------------------------------------------------
(* ** Tokens for commands *) */

%token ADMIT LAST BACK UNDOBACK QED EXTRACT RESTART
%token PRINTGOALS PRINTGOAL PRINTPROOF PRINTDEBUG PRINTGAME PRINTGAMES
%token INRIGHT INBOTH

/*----------------------------------------------------------------------
(* ** Tokens for tactics *) */

%token RMATFOLD RMATUNFOLD

%token SLASH2 SLASHEQ SLASH2EQ SLASH3EQ
%token RNORM RNORM_UNKNOWN RNORM_SOLVE RNORM_NOUNFOLD
%token RRND RRND_EXP REXC
%token RMOVE RMOVE_MAIN
%token RTRANS RTRANSSTAR
%token RDIST_SYM RDIST_EQ RINDEP
%token RCRUSH BYCRUSH
%token RSIMP BYSIMP
%token RBAD1 RBAD2 RCHECK_HASH_ARGS
%token RCASE_EV RFALSE_EV RREWRITE_EV RSPLIT_EV RREMOVE_EV RCTXT_EV
%token RCTXT_EV_INJ RSPLIT_INEQ_EV
%token RLET_ABS RLET_ABS_DED RLET_UNFOLD
%token RSUBST RINSERT RCONV RRENAME
%token ASSUMPTION_DECISIONAL ASSUMPTION_COMPUTATIONAL
%token RHYBRID RADD_TEST
%token RGUESS RFIND
%token REXC_ORCL RREWRITE_ORCL
%token DEDUCE LISTFE RENSURE
%token SEP_DOM

/*======================================================================
(* * Production types *) */

%type <ParserTypes.lcmd list> lcmd

%type <ParserTypes.odef> odef

%type <ParserTypes.gcmd list> gcmd

%type <ParserTypes.theory> theory

%type <ParserTypes.instr list> instruction

/*======================================================================
(* * Start productions *) */

%start odef

%start instruction

%start theory

%%

/*======================================================================
(* * Helper definitions *) */

%public uopt(X):
| UNDERSCORE { None }
| x=X        { Some x }

%public seplist0(S,X):
| l=separated_list(S,X) {l}

%public seplist1(S,X):
| l=separated_nonempty_list(S,X) { l }

%public termlist0(S,X):
| l=list(terminated(X,S)) {l}

%public termlist1(S,X):
| l=nonempty_list(terminated(X,S)) { l }

%public paren_list0(S,X):
| l=delimited(LPAR,separated_list(S,X),RPAR) {l}

%public paren_list1(S,X):
| l=delimited(LPAR,separated_nonempty_list(S,X),RPAR) {l}

%public bracket_list0(S,X):
| l=delimited(LBRACK,separated_list(S,X),RBRACK) {l}

%public bracket_list1(S,X):
| l=delimited(LBRACK,separated_nonempty_list(S,X),RBRACK) {l}

/*======================================================================
(* * Types *) */

dimexp :
| b=ID                           {PDBase(b)}
| i=NAT                            {PDBase("1")}
| d1=dimexp PLUS d2=dimexp       {PDPlus(d1,d2)}

typ :
| i=TBS                          { BS(i) }
| TBOOL                          { Bool }
| i=TG                           { G(i) }
| TFQ                            { Fq }
| TMAT LCBRACE d1=dimexp COMMA d2=dimexp RCBRACE { Mat(d1,d2)}
| TLIST LCBRACE d=dimexp RCBRACE t=typ           { List(d,t) }
| LPAR l=seplist0(STAR,typ) RPAR { mk_Prod l }
| i=ID                           { TySym(i) }
| t=typ CARET n=NAT              { Prod(Util.replicate n t) }

/*======================================================================
(* * Expressions *) */

expr :
| e1=expr1 QUESTION e2=expr1 COLON e3=expr1        { Ifte(e1, e2, e3) }
| EXISTS l=seplist1(COMMA,binding1) COLON e1=expr1 { Quant(Expr.Exists,l,e1) }
| FORALL l=seplist1(COMMA,binding1) COLON e1=expr1 { Quant(Expr.All,l,e1) }
| e=expr1                                          { e }

expr1 :
| e1=expr1 LAND e2=expr1 { Land(e1,e2) }
| e1=expr1 LOR  e2=expr1 { Lor(e1,e2) }
| e=expr2                { e }

(* | e1=expr1 IN QUERIES LPAR oname=ID RPAR    { InLog(e1,oname) }  *)

expr2 :
| e1=expr2 EQUAL e2=expr2 { Eq(e1,e2) }
| e1=expr2 NEQ   e2=expr2 { Not(Eq(e1,e2)) }
| e1=expr2 CONCAT e2=expr2 { Concat(e1,e2) }
| e=expr3                 { e }

expr3 :
| e1=expr3 PLUS e2=expr3 { Plus(e1, e2) }
| e1=expr3 XOR  e2=expr3 { Xor (e1, e2) }
| e=expr4                { e }

expr4 :
| e1=expr4 MINUS e2=expr4 { Minus(e1, e2) }
| e=expr5                 { e }

expr5:
| e1=expr5 SLASH e2=expr5 { Div(e1, e2) }
| e=expr6                 { e }

expr6 :
| e1=expr6 STAR e2=expr6 { Mult(e1,e2) }
| e=expr7                { e }

expr7:
| e1=expr8 CARET e2=expr8 { Exp(e1, e2) }
| e=expr8                 { e }

(* FIXME: check how unary/binary minus handled in Haskell/OCaml *)
expr8 :
| s=ID                                    { V(Unqual,s) }
| s1=ID BACKTICK s2=ID                    { V(Qual s1, s2) }
| i=NAT                                   { CFNat(i) }
| i=GEN                                   { CGen(i) }
| MATZERO d1=dimexp COMMA d2=dimexp RCBRACE { MatZ(d1,d2)}                        
| MATID d1=dimexp COMMA d2=dimexp RCBRACE { MatI(d1,d2)}                        
| i=ZBS                                   { CZ(i) }
| TRUE                                    { CB(true) }
| FALSE                                   { CB(false) }
| s=ID l=paren_list1(COMMA,expr)          { SApp(s,l) }
| MINUS e1=expr8                          { Opp(e1) }
| SPLITLEFT e=expr8                       { SplitLeft(e) }
| SPLITRIGHT e=expr8                      { SplitRight(e) }
| LBRACK e=expr8 RBRACK UNDERSCORE LCBRACE d=dimexp RCBRACE { PListOf (e,d) }
| NOT e=expr8                             { Not(e) }
| LOG LPAR e1=expr RPAR                   { Log(e1) }
| l=paren_list0(COMMA,expr)               { mk_Tuple l }
| e1=expr7 SHARP i=NAT                    { Proj(i,e1) }
| IN_DOM LPAR e=expr COMMA i=ID RPAR      { SIndom(i,e) }
| IS_SET LPAR i=ID RPAR                   { SIndom(i,mk_Tuple []) }
| i=MGET_ID l=seplist1(COMMA,expr) RBRACK { SLookUp(i,l) }
| i=MVAR_ID                               { SLookUp(i,[mk_Tuple []]) }
| TRANS e=expr8                           { Trans(e) }

/*======================================================================
(* * Oracle definitions *) */

except_exprs :
| BACKSLASH LCBRACE es=seplist0(COMMA,expr) RCBRACE { es }
| BACKSLASH         es=seplist1(COMMA,expr)         { es }

lcmd :
| LET i=ID EQUAL e=expr                             { [ LLet(i,e) ] }
| is=seplist0(COMMA,ID) LEFTARROW hsym=LIST         { [ LBind(is,hsym) ] }
| is=seplist1(COMMA,ID) SAMP t=typ
    es=loption(except_exprs)                        { L.map (fun i -> LSamp(i,t,es)) is }
| GUARD LPAR e=expr RPAR                            { [ LGuard(e) ] }
| i=MGET_ID l=seplist1(COMMA,expr) RBRACK
    COLONEQ e=expr                                { [ LMSet(i,l,e) ] }
| i=ID COLONEQ e=expr                             { [ LMSet(i,[mk_Tuple []],e) ] }

obody :
| LCBRACE cmds=termlist0(SEMICOLON,lcmd)
    RETURN e=expr SEMICOLON? RCBRACE     { (L.concat cmds, e) }

odecl :
| lc=obody                                    { Odef lc}
| LBRACK lc1=obody lc2=obody lc3=obody RBRACK { Ohybrid(lc1,lc2,lc3) }

counter :
| LBRACK COUNTER EQUAL i=ID RBRACK { `Counter i }
| LBRACK ONCE RBRACK               { `Once }

odef :
| oname=ID args=paren_list0(COMMA,ID) c=counter? EQUAL od=odecl { (oname, args, od, c) }

/*======================================================================
(* * Games *) */

arglist0 :
| l=paren_list0(COMMA,expr) { mk_Tuple l }

odefs :
| WITH os=seplist1(COMMA,odef) { os }

var_pat :
| i = ID                                { [i] }
| LPAR is=separated_list(COMMA,ID) RPAR { is }

gcmd :
| LET i=ID EQUAL e=expr                                      { [ GLet(i,e) ] }
| i=MGET_ID l=seplist1(COMMA,expr) RBRACK COLONEQ e=expr     { [ GMSet(i,l,e) ] }
| i=ID COLONEQ e=expr                                        { [ GMSet(i,[mk_Tuple []],e) ] }
| is=var_pat LEFTARROW asym=ID e=arglist0 ods=loption(odefs) { [ GCall(is,asym,e,ods) ] }
| ASSERT LPAR e=expr RPAR                                    { [ GAssert(e) ] }
| ids=seplist1(COMMA,ID) SAMP t=typ es=loption(except_exprs) { L.map (fun i -> GSamp(i,t,es)) ids }

gcmds:
| cs = termlist0(SEMICOLON,gcmd) { L.concat cs }

gdef :
| cs=gcmds { CmdList(cs) }
| gid=ID  { Gname(gid) }

/*======================================================================
(* * Instructions *) */

/*----------------------------------------------------------------------
(* ** helper definitions *) */

offset:
| PLUS  i=NAT { i }
| MINUS i=NAT { -i }

int:
| i=NAT       { i }
| MINUS i=NAT { -i }

binding1:
| x=ID IN o=LIST                            { [x], o }
| LPAR xs=seplist1(COMMA,ID) RPAR IN o=LIST { xs, o }

bind_event:
| COLON e=expr {e}

dir:
| LEFTARROW { Util.RightToLeft }
| TO        { Util.LeftToRight }

otype:
| LESS    { G.OHless}
| EQUAL   { G.OHeq }
| GREATER { G.OHgreater }

opos:
| LPAR i=NAT COMMA j=NAT COMMA k=NAT RPAR                { (i-1, j-1, k-1, G.Onothyb) }
| LPAR i=NAT COMMA j=NAT COMMA k=NAT COMMA ot=otype RPAR { (i-1, j-1, k-1, G.Oishyb ot) }

opos_partial:
| LPAR i=NAT COMMA j=NAT COMMA k=NAT RPAR { (i-1, j-1, k-1) }

uopos:
| op = opos                                              { Some(op) }
| LPAR UNDERSCORE COMMA UNDERSCORE COMMA UNDERSCORE RPAR { None }

n_in :
| IN    { true }
| NOTIN { false }

ty_anno :
| COLON  t=typ { t }

ctx :
| LPAR i=ID ot=option(ty_anno) TO e=expr RPAR { (i, ot, e) }

ctx_noty :
| LPAR i=ID TO e=expr RPAR { (i,None,e) }

sym_class:
| LBRACK vs=separated_nonempty_list(COMMA,ID) RBRACK { vs }

sym_vars:
| LPAR symclass=sym_class* RPAR {symclass}

/*----------------------------------------------------------------------
(* ** declarations *) */

atype:
| SUCC { A_Succ }
| ADV  { A_Adv }

decl :
| ADVERSARY i=ID  COLON t1=typ TO t2=typ         { ADecl(i, t1, t2)   }
| ORACLE    i=ID  COLON t1=typ TO t2=typ         { ODecl(i, t1, t2)   }
| TYPE      i=ID                                 { TyDecl(i)          }
| BOUND b=ID FOR i=ID                            { BoundDecl(b,i)     }
| RANDOM_ORCL i=ID COLON t1=typ TO t2=typ        { RODecl(i, t1, t2)  }
| RANDOM_FUN  i=ID COLON t1=typ TO t2=typ        { RFDecl(i, t1, t2)  }
| FINMAP      i=ID COLON t1=typ TO t2=typ        { FMDecl(i, t1, t2)  }
| OPERATOR i=ID COLON t1=typ TO t2=typ           { FunDecl(i, t1, t2) }
| BILINEAR_MAP i=ID COLON
    g1=TG STAR g2=TG TO g3=TG                    { EMDecl(i, g1, g2, g3) }
| ASSUMPTION
    it=boption(delimited(LBRACK,INFTHEO,RBRACK))
    i=ID sym=loption(sym_vars)
    LBRACK g0=gcmds RBRACK
    LBRACK g1=gcmds RBRACK                       { AssmDec(i, it, g0, g1, sym) }
| ASSUMPTION
    it=boption(delimited(LBRACK,INFTHEO,RBRACK))
    i1=ID at=atype sym=loption(sym_vars)
    LBRACK g=gcmds RBRACK e=bind_event           { AssmComp(i1, it, at, g, e, sym) }
| BOUNDSUCC LBRACK g=gdef RBRACK e=bind_event    { JudgSucc(g, e) }
| BOUNDADV LBRACK g=gdef RBRACK e=bind_event     { JudgAdv(g, e) }
| BOUNDDIST LBRACK g1=gdef RBRACK e1=bind_event
    LBRACK g2=gdef RBRACK e2=bind_event          { JudgDist(g1, e1, g2, e2) }
| GAME i=ID COLONEQ LBRACK g = gdef RBRACK       { GameDef(i,g) }
| INCLUDE i=ID                                   { Include(i) }

/*----------------------------------------------------------------------
(* ** proof commands *) */

proof_command :
| ADMIT                                { Admit }
| LAST                                 { Last }
| BACK                                 { Back }
| UNDOBACK b=boption(EXCL)             { UndoBack(b) }
| QED                                  { Qed }
| RESTART                              { Restart }
| EXTRACT s=STRING                     { Extract s }
| PRINTGOALS COLON i=ID                { PrintGoals(i) }
| PRINTGOAL COLON i=ID                 { PrintGoal(i) }
| PRINTPROOF b=boption(EXCL) s=STRING? { PrintProof(b,s) }
| PRINTGOALS                           { PrintGoals("") }
| PRINTDEBUG s=STRING                  { Debug s }
| PRINTGAME s=STRING                   { PrintGame s }
| PRINTGAMES s1=STRING s2=STRING       { PrintGames(s1,s2) }

/*----------------------------------------------------------------------
(* ** helpers for tactics *) */

br_exprlist0:
| LBRACK es=separated_list(COMMA,expr) RBRACK { es }

gpos:
| i=NAT { i - 1 }
| LBRACK i=NAT RBRACK { i - 1 }
| LBRACK MINUS i=NAT RBRACK { (-i) - 1}

assgn_pos:
| n=offset { Pos(n) }
| i=ID     { Var(i) }
| n=NAT    { AbsPos(n-1) }

inter_pos:
| LBRACK i1=assgn_pos i2=assgn_pos? RBRACK { Some i1, i2 }

move_pos:
| i=inter_pos  { i }
| i1=assgn_pos { Some i1 , Some i1 }

diff_cmd:
| RRENAME i1=ID i2=ID mupto=assgn_pos?            { Drename(i1,i2,mupto) }
| RINSERT p=assgn_pos LBRACK gd=gcmds RBRACK      { Dinsert(p,gd) }
| RSUBST p=assgn_pos LPAR e1=expr TO e2=expr RPAR { Dsubst(p,e1,e2) }

id_pair:
| id = ID { (id,None) }
| LPAR id1=ID id2=ID RPAR { (id1,Some id2) }

strict_id_pair:
| id1=ID id2=ID { (id1, id2) }

maybe_upto:
| COLON ap=assgn_pos { ap }

maybe_len:
| COLON ap=int { ap }


/*----------------------------------------------------------------------*/

qual_id:
| s=ID                                    { (Unqual,s) }
| s1=ID BACKTICK s2=ID                    { (Qual s1, s2) }

renaming1:
| id1=qual_id COMMA id2=qual_id                 { id1,id2 }

renaming: 
| LBRACK l=seplist0(SEMICOLON, renaming1) RBRACK { l }

oinrng:
| i=NAT j=NAT o=ID  { i, j, o }

oinrngs:
| LPAR k=NAT t=otype? l=oinrng* RPAR { 
      let t = match t with None -> Game.Onothyb | Some t -> Game.Oishyb t in 
      k, t, l }

orng:
| i=NAT j=NAT o=ID { RO_main(i, j, o) }
| i=NAT LBRACK l=oinrngs* RBRACK { RO_in_o(i,l) }

orngs:
| LBRACK o=orng* RBRACK {o}

adv_o_rng:
| i=NAT j=NAT o=orngs {i,j,o} 

adv_o_rngs:
| l=adv_o_rng* { l }

/*----------------------------------------------------------------------
(* ** tactics *) */

tactic :

/* norm variants */
| RNORM                { Rnorm(false) }
| RNORM EXCL           { Rnorm(true) }
| SLASH2               { Rnorm(false) }
| RNORM_NOUNFOLD       { Rnorm_nounfold }
| SLASHEQ              { Rnorm_nounfold }
| RNORM_UNKNOWN is=ID* { Rnorm_unknown(is) }
| SLASH2EQ is=ID*      { Rnorm_unknown(is) }
| SLASH3EQ is=ID*      { Rseq [Rnorm(false); Rnorm_unknown(is)] }
| RNORM_SOLVE e=expr   { Rnorm_solve(e) }

/* conversion */
| RCONV gd=uopt(delimited(LBRACK,gdef,RBRACK))
    e=bind_event                               { Rconv(gd,e) }
| RTRANS LBRACK gd=gdef RBRACK e=bind_event    { Rtrans(gd,e) }
| RTRANSSTAR LBRACK
   dcmds=seplist1(COMMA,diff_cmd) RBRACK       { Rtrans_diff(dcmds) }
| RSUBST i=inter_pos?
    LPAR e1=expr TO e2=expr RPAR               { let i,mup = O.default (None,None) i in
                                                 Rsubst(i,e1,e2,mup) }
| RRENAME v1=ID v2=ID                          { Rrename(v1,v2) }
| RLET_UNFOLD i=assgn_pos*                     { Rlet_unfold(i) }
| RLET_ABS excl=EXCL? i=uopt(assgn_pos)
    i1=ID e1=uopt(expr) mup=maybe_upto?        { Rlet_abs(i,i1,e1,mup,excl=None) }
| RLET_ABS excl=EXCL? op=opos
    i1=ID e1=expr len=maybe_len?               { Rlet_abs_orcl(op,i1,e1,len,excl=None) }
| RLET_ABS_DED excl=EXCL? i=assgn_pos
    i1=ID e1=expr mup=maybe_upto?              { Rlet_abs_ded(excl<>None,i,i1,e1,mup) }
| ASSERT i=assgn_pos e=expr?                   { Rassert(i,e) }

| RMATUNFOLD i=gpos p=option(strict_id_pair)   { Rmatunfold(None,i, p) }
| RMATFOLD i=gpos j=gpos m=option(ID)          { Rmatfold(None,i,j, m) }

/* moving lines */
| RMOVE i=move_pos j=assgn_pos                 { Rmove(i,j) }
| RENSURE e = expr nin=n_in io=uopt(assgn_pos) { Rensure(io,nin,e) }
| RMOVE op=opos j=offset                       { Rmove_oracle(op,j) }
| RMOVE_MAIN op=opos_partial v=ID              { Rmove_to_main(op,v) }
| RMOVE_MAIN i=assgn_pos op=opos_partial v=ID  { Rmove_to_orcl(i,op,v) }

/* random samplings */
| RRND excl=EXCL?  mi=uopt(assgn_pos)
    mc1=uopt(ctx) mc2=uopt(ctx) mgen=expr?     { Rrnd(excl=None,mi,mc1,mc2,mgen) }
| RRND_EXP excl=EXCL? ids=id_pair+             { Rrnd_exp(excl=None,ids) }
| REXC i=uopt(assgn_pos) es=uopt(br_exprlist0) { Rexcept(i,es) }
| REXC_ORCL op=opos es=br_exprlist0            { Rexcept_orcl(op,es) }

/* assumptions */
| ASSUMPTION_DECISIONAL excl=EXCL? s=uopt(ID)
    d=uopt(dir) rngs=inter_pos* xs=option(ID+)   { Rassm_dec(excl=None,s,d,rngs,xs) }

| ASSUMPTION_DECISIONAL STAR s=ID d=uopt(dir) 
     ren=renaming rngs=adv_o_rngs { 
       let d = match d with None -> Util.LeftToRight | Some d -> d in
       Rassm_dec_o(s, d, ren, rngs) }

| ASSUMPTION_COMPUTATIONAL excl=EXCL? s=uopt(ID)
    rngs=inter_pos*                              { Rassm_comp(excl=None,s,rngs) }

/* automated rules */
| RSIMP                { Rsimp(false) }
| BYSIMP               { Rsimp(true) }
| RCRUSH  mi=uopt(NAT) { Rcrush(false,mi) }
| RCRUSH               { Rcrush(false,Some(1)) }
| BYCRUSH              { Rcrush(true,None) }
| BYCRUSH mi=uopt(NAT) { Rcrush(true,mi) }

/* finite maps */
| SEP_DOM mid1=ID mid2=ID { Rsep_dom(mid1,mid2) }

/* oracles */
| RRND op=uopos c1=uopt(ctx) c2=uopt(ctx)           { Rrnd_orcl(op,c1,c2) }
| RREWRITE_ORCL op=opos d=dir                       { Rrewrite_orcl(op,d) }
| RBAD1 i=uopt(assgn_pos) s=ID                      { Rbad (1,i,s)        }
| RBAD2 i=uopt(assgn_pos) s=ID                      { Rbad (2,i,s)        }
| RCHECK_HASH_ARGS op=opos                          { Rcheck_hash_args op }
| GUARD op=opos e=expr?                             { Rguard(op,e) }
| RGUESS asym=ID fvs=ID*                            { Rguess(asym,fvs) }
| RFIND LPAR bd=ID* TO body=expr RPAR
    e=expr asym=ID fvs=ID*                          { Rfind((bd,body),e,asym,fvs) }
| RHYBRID LPAR i=NAT COMMA j=NAT RPAR lc=obody      { Rhybrid((i-1,j-1),lc) }
| RADD_TEST UNDERSCORE                              { Radd_test(None,None,None,None) }
| RADD_TEST op=opos e=expr asym=ID fvs=ID*          { Radd_test(Some(op),Some(e),Some(asym),Some(fvs)) }

/* events */
| RREMOVE_EV is=gpos+                               { Rremove_ev(is) }
| RSPLIT_EV i=gpos                                  { Rsplit_ev(i) }
| RSPLIT_INEQ_EV i=gpos                             { Rsplit_ineq(i) }
| RCASE_EV e=uopt(expr)                             { Rcase_ev(e) }
| RREWRITE_EV i=gpos d=dir?                         { Rrewrite_ev(i,O.default LeftToRight d) }
| RCTXT_EV oj=uopt(gpos) c=uopt(ctx)                { Rctxt_ev(oj,c) }

/* probability bounding rules */
| RINDEP excl=EXCL? { Rindep(excl=None) }
| RFALSE_EV         { Rfalse_ev }

/* bounding distinguishing probability */
| RDIST_EQ  { Rdist_eq }
| RDIST_SYM { Rdist_sym }

/* debugging */
| DEDUCE  ppt=PPT?
    LBRACK es=seplist1(COMMA,expr) RBRACK e=expr { Deduce(ppt<>None,es,e) }
| LISTFE LBRACK es=seplist1(COMMA,expr) RBRACK   { FieldExprs(es) }

/*----------------------------------------------------------------------
(* ** instructions and theories *) */

selector:
| INRIGHT { InRight }
| INBOTH { InBoth }

instr :
| i=decl { [i] }
| i=proof_command { [i] }
| ir=selector? is=separated_nonempty_list(SEMICOLON,tactic)
  { let tacs =
      match is with
      | [i] -> [Apply(i)]
      | _ -> [Apply(Rseq(is))]
    in
    match ir with
    | None -> tacs
    | Some InBoth -> tacs@[Apply(Rdist_sym)]@tacs@[Apply(Rdist_sym)]
    | Some InRight -> [Apply(Rdist_sym)]@tacs@[Apply(Rdist_sym)]
  }

instruction:
| i=instr DOT EOF { i }

theory :
| i=instr DOT EOF { i }
| i=instr DOT t=theory { i@t }
