open Abbrevs
open Util
open Type
open File
open Syms

(* -------------------------------------------------------------------- *)
let pp_if c pp1 pp2 fmt x =
  match c with
  | true  -> pp1 fmt x
  | false -> pp2 fmt x

let pp_maybe c tx pp fmt x =
  pp_if c (tx pp) pp fmt x

let pp_enclose ~pre ~post pp fmt x =
  F.fprintf fmt "%(%)%a%(%)" pre pp x post

let pp_paren pp fmt x =
  pp_enclose ~pre:"(" ~post:")" pp fmt x

let maybe_paren outer inner pp =
  pp_maybe (outer < inner) pp_paren pp
    
let next_lvl lvl = lvl + 10
let   min_lvl = 0       
let  proj_lvl = next_lvl min_lvl 
let   app_lvl = next_lvl proj_lvl
let   pow_lvl = next_lvl app_lvl 
let   opp_lvl = next_lvl pow_lvl 
let  cons_lvl = next_lvl pow_lvl
let   mul_lvl = next_lvl cons_lvl 
let   add_lvl = next_lvl mul_lvl 
let    eq_lvl = next_lvl add_lvl 
let   not_lvl = next_lvl eq_lvl
let   iff_lvl = next_lvl not_lvl
let   and_lvl = next_lvl iff_lvl 
let    or_lvl = next_lvl and_lvl
let   imp_lvl = next_lvl or_lvl 
let    if_lvl = next_lvl imp_lvl 
let quant_lvl = next_lvl if_lvl 
let   max_lvl = max_int 
  
let pp_infix pp lvl assoc op e1 e2 fmt () = 
  let l1, l2 = 
    match assoc with
    | `LeftA  -> lvl, lvl-1
    | `NoA    -> lvl-1, lvl-1
    | `RightA -> lvl-1, lvl in
  F.fprintf fmt "@[%a %s@ %a@]" (pp l1) e1 op (pp l2) e2

let pp_infix_l pp lvl = pp_infix pp lvl `LeftA
let pp_infix_n pp lvl = pp_infix pp lvl `NoA
let pp_infix_r pp lvl = pp_infix pp lvl `RightA

(* -------------------------------------------------------------------- *)

let pp_pvar fmt (ms,s) =
  if ms = [] then F.fprintf fmt "%s" s
  else F.fprintf fmt "%a.%s" (pp_list "." F.pp_print_string) ms s

let pp_mem fmt s = F.fprintf fmt "&%s" s

let rec pp_mod_name fmt mn = 
  if mn.ma = [] then F.fprintf fmt "%s" mn.mn
  else 
    F.fprintf fmt "%s(@[<hov 1>%a@])" 
      mn.mn (pp_list ",@ " pp_mod_name) mn.ma

let pp_fun_name fmt (mn,s) = 
  F.fprintf fmt "%a.%s" pp_mod_name mn s

let pp_tvar fmt i = 
  let m =  {mn = i.tvar_mod; ma = []} in
  F.fprintf fmt "%a.%s" pp_mod_name m i.tvar_ty

let rec pp_type file fmt ty = 
  match ty.ty_node with
  | BS lv    -> pp_tvar fmt (get_lvar file lv)
  | Bool     -> F.fprintf fmt "bool"
  | G gv     -> pp_tvar fmt (get_gvar file gv)
  | Fq       -> F.fprintf fmt "F.t"
  | Prod tys ->
    begin match tys with
    | []  -> F.fprintf fmt "unit"
    | [t] -> pp_type file fmt t
    | _   -> 
      F.fprintf fmt "(@[%a@])" (pp_list " *@ " (pp_type file)) tys
    end
  | Int -> F.fprintf fmt "int"
  | KeyPair _ | KeyElem _ -> assert false

let pp_pvar_decl file fmt (x,ty) = 
  F.fprintf fmt "@[<hov 2>%a:@ %a@]"
    pp_pvar x (pp_type file) ty

let pp_at_mem fmt = function
  | None -> ()
  | Some m -> F.fprintf fmt "{%s}" m

let pp_let_quant_bd fmt bd =
  match bd with
  | [x] -> F.fprintf fmt "%s" x
  | _ -> 
    F.fprintf fmt "(%a)" 
      (pp_list "," (fun fmt -> F.fprintf fmt "%s")) bd 

let rec pp_form_lvl outer fmt = function
  | Fv (v, m)     -> F.fprintf fmt "%a%a" pp_pvar v pp_at_mem m 
  | Feqglob a     -> F.fprintf fmt "={glob %s}" a
  | Ftuple es     ->
    F.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " pp_form) es
  | Fproj (i,e)   ->
    let pp fmt e = 
      F.fprintf fmt "%a.`%i" (pp_form_lvl proj_lvl) e i in
    maybe_paren outer proj_lvl pp fmt e
  | Fcnst c       -> F.fprintf fmt "%s" c
  | Fapp(op,es)   -> 
    let pp_form_lvl = pp_form_lvl in
    let pp, inner = 
      match op, es with
      | Oopp, [e] -> 
        let pp fmt () = 
          F.fprintf fmt "@[-@ %a@]" (pp_form_lvl opp_lvl) e in
        pp, opp_lvl
      | Onot, [e] ->
        let pp fmt () = 
          F.fprintf fmt "@[!@ %a@]" (pp_form_lvl not_lvl) e in
        pp, not_lvl
      | Opow, [e1;e2] -> pp_infix_l pp_form_lvl pow_lvl "^" e1 e2, pow_lvl
      | Osub, [e1;e2] -> pp_infix_l pp_form_lvl add_lvl "-" e1 e2, add_lvl
      | Oadd, [e1;e2] -> pp_infix_l pp_form_lvl add_lvl "+" e1 e2, add_lvl
      | Omul, [e1;e2] -> pp_infix_l pp_form_lvl mul_lvl "*" e1 e2, mul_lvl
      | Odiv, [e1;e2] -> pp_infix_l pp_form_lvl mul_lvl "/" e1 e2, mul_lvl
      | Oeq,  [e1;e2] -> pp_infix_n pp_form_lvl eq_lvl  "=" e1 e2, eq_lvl
      | Ole,  [e1;e2] -> pp_infix_n pp_form_lvl eq_lvl  "<=" e1 e2, eq_lvl
      | Olt,  [e1;e2] -> pp_infix_n pp_form_lvl eq_lvl  "<" e1 e2, eq_lvl
      | Oiff, [e1;e2] -> pp_infix_n pp_form_lvl iff_lvl "<=>" e1 e2, max_lvl
      | Oand, [e1;e2] -> pp_infix_r pp_form_lvl and_lvl "/\\" e1 e2, and_lvl
      | Oor,  [e1;e2] -> pp_infix_r pp_form_lvl or_lvl "\\/" e1 e2, or_lvl
      | Oimp, [e1;e2] -> pp_infix_r pp_form_lvl imp_lvl "=>" e1 e2, imp_lvl
      | Ocons,[e1;e2] -> pp_infix_r pp_form_lvl cons_lvl "::" e1 e2, cons_lvl
      | (Oopp | Opow | Oadd | Osub | Omul | Odiv | Oeq | Ole | Olt | Oand | Oor | Onot | Oiff | Oimp | Ocons), _ -> 
        assert false
      | Ostr op, es ->
        let pp fmt () = 
          F.fprintf fmt "@[<hov 2>%s@ %a@]" op 
            (pp_list "@ " (pp_form_lvl (app_lvl - 1))) es in
        pp, app_lvl
      | Olength, [e] -> 
        let pp fmt () = 
          F.fprintf fmt "`|%a|" pp_form e in
        pp, min_lvl
      | Olength, _ -> assert false

    in
    maybe_paren outer inner pp fmt ()
  | Fif(e1,e2,e3) ->
    F.fprintf fmt "(@[<hov 2>(%a)?@ (%a) :@ (%a)@])" 
      (pp_form_lvl if_lvl) e1 (pp_form_lvl if_lvl) e2
      (pp_form_lvl if_lvl) e3 
  | Fabs e -> F.fprintf fmt "`|%a|" pp_form e
(*  | Fexists of (lvar * hvar) list * form *)
  | Fforall_mem(m,e) ->
    let pp fmt () = 
      F.fprintf fmt "@[<hov 2>forall &%s,@ %a@]" 
        m (pp_form_lvl quant_lvl) e 
    in
    maybe_paren outer quant_lvl pp fmt () 
  | Fpr(f,m,args,ev) ->
    F.fprintf fmt "@[<hov 2>Pr[%a(@[%a@]) @@ &%s:@ %a]@]"
      pp_fun_name f 
      (pp_list ",@ " pp_form) args
      m
      pp_form ev
  | Frofi f -> 
    let pp fmt () = 
      F.fprintf fmt "%a%s" (pp_form_lvl proj_lvl) f "%r" in
    maybe_paren outer proj_lvl pp fmt ()
  | Fquant_in(q,f,log) ->
    let pp_fun fmt (bd, ty, body) = 
      F.fprintf fmt "fun (__elem__:%s),@ " ty;
      List.iteri (fun i v ->
          F.fprintf fmt "let %s = __elem__.`%i in@ " v (i+1)) bd;
      pp_form fmt body in
    F.fprintf fmt "(%s (@[<hov>%a@]) %a)"
      (if q = Expr.All then "all" else "any")
      pp_fun f
      (pp_form_lvl min_lvl) log


and pp_form fmt e = pp_form_lvl max_lvl fmt e

let rec pp_exp_lvl file outer fmt = function
  | Epv v         -> pp_pvar fmt v
  | Etuple es     -> 
    F.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " (pp_exp file)) es
  | Eproj(i,e)    -> 
    let pp fmt e = 
      F.fprintf fmt "%a.`%i" (pp_exp_lvl file proj_lvl) e i in
    maybe_paren outer proj_lvl pp fmt e
  | Ecnst c       -> F.fprintf fmt "%s" c
  | Eapp(op,es)   -> 
    let pp, inner = 
      let pp_exp_lvl = pp_exp_lvl file in
      match op, es with
      | Oopp, [e] -> 
        let pp fmt () = 
          F.fprintf fmt "@[-@ %a@]" (pp_exp_lvl opp_lvl) e in
        pp, opp_lvl
      | Onot, [e] -> 
        let pp fmt () = 
          F.fprintf fmt "@[!@ %a@]" (pp_exp_lvl not_lvl) e in
        pp, not_lvl
 
      | Opow, [e1;e2] -> pp_infix_l pp_exp_lvl pow_lvl "^" e1 e2, pow_lvl
      | Osub, [e1;e2] -> pp_infix_l pp_exp_lvl add_lvl "-" e1 e2, add_lvl
      | Oadd, [e1;e2] -> pp_infix_l pp_exp_lvl add_lvl "+" e1 e2, add_lvl
      | Omul, [e1;e2] -> pp_infix_l pp_exp_lvl mul_lvl "*" e1 e2, mul_lvl
      | Odiv, [e1;e2] -> pp_infix_l pp_exp_lvl mul_lvl "/" e1 e2, mul_lvl
      | Oeq,  [e1;e2] -> pp_infix_n pp_exp_lvl eq_lvl  "=" e1 e2, eq_lvl
      | Ole,  [e1;e2] -> pp_infix_n pp_exp_lvl eq_lvl  "<=" e1 e2, eq_lvl
      | Olt,  [e1;e2] -> pp_infix_n pp_exp_lvl eq_lvl  "<" e1 e2, eq_lvl
      | Oiff, [e1;e2] -> pp_infix_n pp_exp_lvl iff_lvl "<=>" e1 e2, iff_lvl
      | Oand, [e1;e2] -> pp_infix_r pp_exp_lvl and_lvl "/\\" e1 e2, and_lvl
      | Oor, [e1;e2]  -> pp_infix_r pp_exp_lvl or_lvl "/\\" e1 e2, or_lvl
      | Oimp, [e1;e2] -> pp_infix_r pp_exp_lvl imp_lvl "=>" e1 e2, imp_lvl
      | Ocons,[e1;e2] -> pp_infix_r pp_exp_lvl cons_lvl "::" e1 e2, cons_lvl
      | (Oopp | Opow | Oadd | Osub | Omul | Odiv | Oeq | Ole | Olt | Oand | Oor | Onot | Oiff | Oimp | Ocons), _ -> 
        assert false
      | Ostr op, es ->
        let pp fmt () = 
          F.fprintf fmt "@[<hov 2>%s@ %a@]" op 
            (pp_list "@ " (pp_exp_lvl (app_lvl - 1))) es in
        pp, app_lvl
      | Olength, [e] -> 
        let pp fmt () = F.fprintf fmt "`|%a|" (pp_exp file) e in
        pp, min_lvl
      | Olength, _ -> assert false
 
    in
    maybe_paren outer inner pp fmt ()

  | Eif(e1,e2,e3) ->
      F.fprintf fmt "(@[<hov 2>(%a)?@ (%a) :@ (%a)@])" 
        (pp_exp_lvl file if_lvl) e1 
        (pp_exp_lvl file if_lvl) e2 
        (pp_exp_lvl file if_lvl) e3 
  | Efun(vs, e) ->
    F.fprintf fmt "(@[<hov 2>fun %a,@ %a@])"
      (pp_list " " 
         (fun fmt pv-> F.fprintf fmt "(%a)" 
           (pp_pvar_decl file) pv)) vs 
      (pp_exp file) e
  | Elet ([x], e1, e2) ->
    F.fprintf fmt "@[<hov 0>(let %a = %a in@ %a)@]"
      pp_pvar x (pp_exp file) e1 (pp_exp file) e2
  | Elet (bd, e1, e2) ->
    F.fprintf fmt "@[<hov 0>(let (%a) = %a in@ %a)@]"
      (pp_list "," pp_pvar) bd (pp_exp file) e1 (pp_exp file) e2


and pp_exp file fmt e = pp_exp_lvl file max_lvl fmt e

let pp_lvalue fmt lv = 
  match lv with
  | [] -> assert false
  | [v] -> pp_pvar fmt v
  | _ -> F.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " pp_pvar) lv


let pp_ty_distr file fmt ty = 
  match ty.ty_node with
  | BS lv -> F.fprintf fmt "%a.Dword.dword" pp_mod_name (mod_lvar file lv)
  | Bool  -> F.fprintf fmt "{0,1}"
  | G gv  -> F.fprintf fmt "%s.Distr.dt" (get_gvar file gv).tvar_mod
  | Fq    -> F.fprintf fmt "FDistr.dt"
  | Prod _
  | Int
  | KeyPair _
  | KeyElem _ -> assert false

  
let rec pp_instr file fmt = function
  | Iasgn(lv,e) ->
    F.fprintf fmt "@[<hov 2>%a =@ %a;@]" 
      pp_lvalue lv (pp_exp file) e
  | Irnd(lv,ty,[]) ->
    F.fprintf fmt "@[<hov 2>%a =@ $%a;@]" 
      pp_lvalue lv (pp_ty_distr file) ty
  | Irnd(lv,ty,[e]) -> 
    F.fprintf fmt "@[<hov 2>%a =@ $(@[%a \\@ FSet.single %a@]);@]" 
      pp_lvalue lv (pp_ty_distr file) ty (pp_exp_lvl file (app_lvl - 1)) e
  | Irnd(_lv,_ty,_l) -> 
    F.eprintf "multiple restriction not implemented@.";
    assert false
  | Irnd_int(lv,e1,e2) ->
    F.fprintf fmt "@[<hov 2>%a =@ $[%a .. %a];@]" 
      pp_lvalue lv (pp_exp file) e1 (pp_exp file) e2
  | Icall([],f,e) ->
    F.fprintf fmt "%a(@[<hov>%a@]);" 
      pp_fun_name f (pp_list ",@ " (pp_exp file)) e
  | Icall(lv,f,e) ->
    F.fprintf fmt "@[<hov 2>%a =@ %a(@[<hov>%a@]);@]" 
      pp_lvalue lv pp_fun_name f (pp_list ",@ " (pp_exp file)) e
  | Iif(e,c1,c2) ->
    let pp_b2 fmt c2 = 
      if c2 <> [] then 
        F.fprintf fmt " else {@   %a@ }" (pp_block file) c2 in
    F.fprintf fmt "@[<v>if (%a) {@   %a@ }%a@]" 
      (pp_exp file) e (pp_block file) c1 pp_b2 c2

and pp_block file fmt c = 
  F.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_instr file)) c


let pp_gtype file fmt = function
  | Tzc ty -> pp_type file fmt ty
  | List ty -> Format.fprintf fmt "%a list" (pp_type file) ty 

let pp_pvar_gdecl file fmt (x,ty) = 
  F.fprintf fmt "@[<hov 2>%a:@ %a@]"
    pp_pvar x (pp_gtype file) ty

let pp_fun_def file fmt fd = 
  let pp_params fmt p = 
    F.fprintf fmt "@[<hov 2>%a@]" 
      (pp_list ",@ " (pp_pvar_decl file)) p in 
  let pp_rettyp fmt = function
    | None -> F.fprintf fmt "unit"
    | Some(_,ty) -> pp_gtype file fmt ty in
  let pp_vard fmt d = 
    F.fprintf fmt "var %a;" (pp_pvar_decl file) d in
  let pp_local fmt loc = 
    if loc <> [] then
      F.fprintf fmt "%a@ " (pp_list "@ " pp_vard) loc in
  let pp_ret fmt = function
    | None -> ()
    | Some(v,_) -> F.fprintf fmt "return %a;" pp_pvar v in
  F.fprintf fmt "(%a) : %a = {@   @[<v>%a%a@ %a@]@ }"
    pp_params fd.f_param
    pp_rettyp fd.f_res
    pp_local fd.f_local
    (pp_block file) fd.f_body
    pp_ret fd.f_res

let pp_fun_def1 file fmt = function
  | Fbody fd   -> pp_fun_def file fmt fd
  | Falias fn  -> F.fprintf fmt " = %a" pp_fun_name fn

let pp_fundef file fmt fd = 
  F.fprintf fmt "@[<v>proc %s%a@]" fd.f_name (pp_fun_def1 file) fd.f_def

  
  
let pp_mod_param fmt (name,ty) = 
  F.fprintf fmt "%s:%s" name ty

let pp_mod_params fmt = function
  | [] -> ()
  | l -> 
    F.fprintf fmt "(@[<hov 2>%a@])"
      (pp_list ",@ " pp_mod_param) l

let rec pp_mod_body file fmt = function
  | Mod_def mc ->
    let isMCvar = function MCvar _ -> true | _ -> false in
    let vars, other = List.partition isMCvar mc in
    (* We try to merge the declaration of global variables *)
    let ht = Hashtbl.create 7 in
    let add = function
      | MCvar (x, ty) -> 
        let l = try Hashtbl.find ht ty with Not_found -> [] in
        Hashtbl.replace ht ty (x::l)
      | _ -> assert false in
    List.iter add vars;
    let vars = Hashtbl.fold (fun ty l vars -> (l,ty) :: vars) ht [] in
    let pp_var fmt (l,ty) = 
      F.fprintf fmt "@[<hov 2>var %a: %a@]"
        (pp_list ",@ " pp_pvar) l (pp_gtype file) ty in
    let pp_vars fmt vars = 
      if vars <> [] then
        F.fprintf fmt "%a@ @ " (pp_list "@ " pp_var) vars in
    F.fprintf fmt "{@   @[<v>%a%a@]@ }"
      pp_vars vars (pp_list "@ @ " (pp_mod_comp file)) other
  | Mod_alias mn -> pp_mod_name fmt mn

and pp_mod_comp file fmt = function
  | MCmod md -> pp_mod_def file fmt md
  | MCfun fd -> pp_fundef file fmt fd
  | MCvar (v,ty) -> F.fprintf fmt "var %a" (pp_pvar_gdecl file) (v,ty)

and pp_mod_def ?(local=false) file fmt md = 
  F.fprintf fmt "@[<v>%smodule %s%a = %a@]"
    (if local then "local " else "")
    md.mod_name pp_mod_params md.mod_param (pp_mod_body file) md.mod_body

let pp_lvars_mod fmt lvars = 
  if Lenvar.H.length lvars <> 0 then 
    let out _ {tvar_mod = name} = 
      F.fprintf fmt "clone import AWord as %s.@ " name
    in
    F.fprintf fmt "(** { Bitstring declarations. } *)@ @ ";
    F.fprintf fmt "require AWord.@ @ ";
    Lenvar.H.iter out lvars;
    F.fprintf fmt "@ "

let pp_gvars_mod fmt gvars = 
  F.fprintf fmt "(** { Field declarations. } *)@ @ ";
  F.fprintf fmt "require import PrimeField.@ ";
  F.fprintf fmt "require SDField.@ ";
  F.fprintf fmt "import FSet.Dexcepted.@ ";
  F.fprintf fmt "import F.@ ";
  F.fprintf fmt "@ ";

  if Groupvar.H.length gvars <> 0 then 
    let out _ {tvar_mod = name} = 
      F.fprintf fmt "clone import CyclicGroup.CG as %s.@ " name
    in
    F.fprintf fmt "(** { Group declarations. } *)@ @ ";
    F.fprintf fmt "require CyclicGroup.@ @ ";
    Groupvar.H.iter out gvars;
    F.fprintf fmt "@ "

(** {3 Bilinear map } *)

let pp_bilinear_mod file fmt bvars = 
  if Esym.H.length bvars <> 0 then
    let out bv s = 
      let g1 = gvar_mod file bv.Esym.source1 in
      let g2 = gvar_mod file bv.Esym.source2 in
      let gt = gvar_mod file bv.Esym.target in
      let pp_with g wg =
         F.fprintf fmt "     type %s.group <- %s.group,@ " g wg;
         F.fprintf fmt "     op   %s.( * ) <- %s.( * ),@ " g wg;
         F.fprintf fmt "     op   %s.([-]) <- %s.([-]),@ " g wg;
         F.fprintf fmt "     op   %s.( / ) <- %s.( / ),@ " g wg;
         F.fprintf fmt "     op   %s.( ^ ) <- %s.( ^ ),@ " g wg;
         F.fprintf fmt "     op   %s.log   <- %s.log"      g wg in
      F.fprintf fmt "clone Bilinear.Bl as %s with@ " s;
      pp_with "GS1" g1;
      F.fprintf fmt ",@ ";
      pp_with "GS2" g2;
      F.fprintf fmt ",@ ";
      pp_with "GT" gt;
      F.fprintf fmt ".@ @ " in

    F.fprintf fmt "(** { Bilinear Map declarations. } *)@ @ ";
    F.fprintf fmt "require Bilinear.@ @ ";
    Esym.H.iter out bvars;
    F.fprintf fmt "@ "

let pp_hash_mod fmt file = 
  if Fsym.H.length file.hvar <> 0 then 
    let out h info =
      match info.h_kind with
      | Hop oinfo ->
        F.fprintf fmt "@[<hov 2>op %s :@ %a ->@ %a.@]@ "
          oinfo.o_name (pp_type file) h.Fsym.dom (pp_type file) h.Fsym.codom in
    F.fprintf fmt "(** { operators declarations. } *)@ @ ";
    Fsym.H.iter out file.hvar;
    F.fprintf fmt "@ "
  



let pp_var_decl file fmt x = 
  F.fprintf fmt "%a:%a"
    Vsym.pp x (pp_type file) (x.Vsym.ty)

  
let pp_oname1 fmt name = F.fprintf fmt "o%a" Osym.pp name
let pp_oname fmt name = F.fprintf fmt "O.%a" pp_oname1 name

let obinding tbl = 
  Osym.H.fold (fun k v l -> (k,v)::l) tbl [] 

let abinding tbl = 
  Asym.H.fold (fun k v l -> (k,v)::l) tbl [] 

let pp_modty file fmt modt =
  let pp_modtparam fmt params =
    if params <> [] then
      let pp_param fmt (s1,s2) = 
        F.fprintf fmt "%s:%s" s1 s2 in
      F.fprintf fmt "(@[<hov>%a@])"
        (pp_list ",@ " pp_param) params in
  let pp_modtproc fmt procs = 
    let pp_arg fmt (ox, ty) = 
      let pp_ox fmt ox = 
        match ox with
        | None -> F.fprintf fmt "_"
        | Some s -> F.fprintf fmt "%s" s in
      F.fprintf fmt "@[<hov>%a:@ %a@]"
        pp_ox ox 
        (pp_type file) ty in
    let pp_proc fmt (name,args,ty,restr) =
      F.fprintf fmt "@[<hov 2>proc %s(@[<hov>%a@]):@ %a@ {@[<hov>%a@]}@]"
        name 
        (pp_list ",@ " pp_arg) args  
        (pp_type file) ty
        (pp_list "@ " pp_fun_name) restr
    in 
    (pp_list "@ " pp_proc) fmt procs
  in
    
  F.fprintf fmt "module type %s%a = {@   @[<v>%a@]@ }."
    modt.modt_name
    pp_modtparam modt.modt_param
    pp_modtproc  modt.modt_proc

let pp_assumption_dec fmt file _name assum =
  F.fprintf fmt "@[<v>%a@ %a.@ @ %a.@]@ @ "
    (pp_modty file) assum.ad_advty
    (pp_mod_def file) assum.ad_cmd1
    (pp_mod_def file) assum.ad_cmd2

let pp_assumption_comp fmt file _name assum =
  F.fprintf fmt "@[<v>%a@ @ %a.@]@ @ "
    (pp_modty file) assum.ac_advty
    (pp_mod_def file) assum.ac_cmd
    
let pp_assumptions fmt file = 
  if Ht.length file.assump_dec <> 0 then begin
    F.fprintf fmt "(** { Decisional Assumptions. } *)@ @ ";
    Ht.iter (pp_assumption_dec fmt file) file.assump_dec
  end;
  if Ht.length file.assump_comp <> 0 then begin
    F.fprintf fmt "(** { Computational Assumptions. } *)@ @ ";
    Ht.iter (pp_assumption_comp fmt file) file.assump_comp
  end

let pp_clone file fmt info = 
  let pp_local fmt local = 
    if local then F.fprintf fmt "local " in
  let pp_import fmt import = 
    if import then F.fprintf fmt "import " in
  let pp_with_to fmt = function
    | CWtype (s,ty) ->
      F.fprintf fmt "type %s <- %a" s (pp_type file) ty
    | CWop(s,None,e) ->
      F.fprintf fmt "op %s <- %a" s (pp_exp file) e 
    | CWop(s,Some(v,ty,vs), e) ->
      let pp_let_b fmt vs = 
        match vs with
        | [] -> assert false
        | [x] -> pp_pvar fmt x
        | _ -> F.fprintf fmt "(@[<hov>%a@])" (pp_list ",@ " pp_pvar) vs in
      F.fprintf fmt 
        "@[<v>op %s <-@   @[<v>fun (%a),@   let %a = %a in@   %a@]@]"
        s (pp_pvar_decl file) (v,ty)
        pp_let_b vs pp_pvar v
        (pp_exp file) e in

  let pp_with fmt info =
    if info.ci_with <> [] then 
      F.fprintf fmt " with@   @[<v>%a@]" 
        (pp_list ",@ " pp_with_to) info.ci_with in

  let pp_proof fmt info = 
    if info.ci_proof <> [] then
      let pp_pr fmt (s,p) = F.fprintf fmt "%s by %a" s p () in
      F.fprintf fmt "@   proof @[<v>%a@]"
        (pp_list",@ " pp_pr) info.ci_proof in

  F.fprintf fmt "@[<v>%aclone %a%s as %s%a%a.@]"
    pp_local info.ci_local
    pp_import info.ci_import
    info.ci_from info.ci_as
    pp_with info
    pp_proof info
    
let rec pp_cmd file fmt = function
  | Ccomment s -> F.fprintf fmt "(** %s *)" s
  | Cbound s -> F.fprintf fmt "op %s: int." s
  | Cmodty modty -> pp_modty file fmt modty 
  | Cmod (local,md) -> 
    F.fprintf fmt "%a." (pp_mod_def ~local file) md
  | Cclone info -> pp_clone file fmt info
  | Clemma(loc,name,f,Some proof) ->
    F.fprintf fmt "%slemma %s:@   @[%a@]."
      (if loc then "local " else "") name pp_form f;
    F.fprintf fmt "@ proof.@   @[<v>%a@]@ qed." proof ()
      
  | Clemma(loc,name,f,None) ->
    assert (loc = false);
    F.fprintf fmt "@[<v>axiom %s:@   @[%a@].@]" name pp_form f 

  | Csection s -> pp_section file fmt s

and pp_cmds file fmt cmds = 
  pp_list "@ @ " (pp_cmd file) fmt (List.rev cmds)

and pp_section file fmt s =
  let pp_locals fmt = function
    | None -> ()
    | Some l ->
      let pp_adv_info fmt a = 
        F.fprintf fmt "declare module %s: %s { @[<hov>%a @]}."
          a.adv_name a.adv_ty
          (pp_list ",@ " (fun fmt (_,s) -> F.fprintf fmt "%s" s)) a.adv_restr
      in
      F.fprintf fmt "section.@   @[<v>%a@ %a@ @ %a@]@ @ end section."
        pp_adv_info l.adv_info
        (pp_list "@ " (fun fmt -> F.fprintf fmt "%s")) l.adv_info.adv_ll
        (pp_cmds file) l.loca_decl
  in
  F.fprintf fmt "theory %s.@   @[<v>%a@ @ theory Local.@ @ %a@ @ %a@ end Local.@]@ end %s." 
    s.section_name 
     (pp_cmds file) s.section_top 
     (pp_cmds file) s.section_glob 
      pp_locals     s.section_loc
    s.section_name
    

 
      
(*let pp_adv_decl fmt file = 
  let r = [] in
  (*  Fsym.H.fold (fun _ info r -> (info.h_th^"."^info.h_mod)::r)
      file.hvar [] in *)
  let add_mod r = function
    | Cmod md -> md.mod_name :: r
    | _ -> r in
  let r = List.fold_left add_mod r file.glob_decl in      
  let r = 
    if Groupvar.H.length file.grvar <> 0 then "SDF.SD1query.SDN.Count" :: r 
    else r in
  let name,ty = adv_decl file in
  F.fprintf fmt "declare module %s : %s {@[<hov 2>%a@]}.@ @ "
    name ty (pp_list ", " F.pp_print_string) r 
*)

let pp_main_section fmt file =
  assert (file.open_section = []);
  pp_cmds file fmt file.top_decl

let pp_file fmt file = 
  F.fprintf fmt "@[<v>require import Option.@ ";
  F.fprintf fmt "require import List.@ ";
  F.fprintf fmt "require import Int.@ ";
  F.fprintf fmt "require import Real.@ ";
  F.fprintf fmt "require import ZooUtil.@ ";
  F.fprintf fmt "require OrclTest.@ ";
  F.fprintf fmt "require Guess.@ @ ";
  pp_lvars_mod fmt file.levar;
  pp_gvars_mod fmt file.grvar;
  pp_bilinear_mod file fmt file.bvar;
  pp_hash_mod fmt file;
  pp_assumptions fmt file;
  pp_main_section fmt file;
  F.fprintf fmt "@]@."
  
    




  
