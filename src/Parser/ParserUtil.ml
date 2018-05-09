(* * Types and conversion functions for parsed types, expressions, ... *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open TheoryTypes
open TheoryState
open Syms
open ParserTypes

module E = Expr
module EU = ExprUtils
module Ht = Hashtbl
module G = Game
module GU = GameUtils
module F = Format
module T = Type
module S = String


(* ** Utility functions
 * ----------------------------------------------------------------------- *)

(** Parser error with explanation. *)
exception ParseError of string

let fail_parse s = raise (ParseError s)

let create_var (vmap : GU.vmap) ts (qual : string qual) s ty =
  if Ht.mem vmap (qual,s) then (
    tacerror "create_var: variable %s already defined" s
  ) else (
    let q = map_qual (fun s -> Mstring.find s ts.ts_odecls) qual in
    let v = VarSym.mk_qual s q ty in
    Ht.add vmap (qual,s) v;
    v
  )

let get_oname_from_opos (se : G.sec_exp) (opos : G.ocmd_pos) : string =
  let (i,j,_,_) = opos in
  match G.get_se_ctxt se i with
  | G.GCall(_,_,_,os), _ ->
     let (_,od,_) = split_n j os in
     let (os,_,_,_) = od in
     Id.name os.OrclSym.id
  | _ -> tacerror "Error, no Oracle definition at line %i" (i+1)

(* ** Conversion functions for parser-types
 * ----------------------------------------------------------------------- *)

let rec create_dimvar ts d = match d with
| PDBase(s) -> T.MDBase(create_lenvar ts s)
| PDPlus(d1,d2) -> T.MDPlus(create_dimvar ts d1, create_dimvar ts d2)

let ty_of_parse_ty ts pty =
  let rec go pty =
    match pty with
    | Bool      -> T.mk_Bool
    | Fq        -> T.mk_Fq
    | Prod(pts) -> T.mk_Prod (L.map go pts)
    | BS(s)     -> T.mk_BS(create_lenvar ts s)
    | Mat(a,b)  -> T.mk_Mat (create_dimvar ts a) (create_dimvar ts b)
    | List(d,t) -> T.mk_List (create_dimvar ts d) (go t)
    | TySym(s)  ->
       (try
          let ts = Mstring.find s ts.ts_tydecls in
          T.mk_TySym(ts)
        with Not_found -> tacerror "Undefined type %s" s)
    | G(s)      -> T.mk_G(create_groupvar ts s)
  in
  go pty

let mk_Tuple es =
  match es with
  | [e] -> e
  | _ -> E.mk_Tuple es

let bind_of_parse_bind (vmap : GU.vmap) ts lH =
  L.map
    (fun (s,h) ->
       let h =
         try Mstring.find h ts.ts_rodecls
         with Not_found ->
           fail_parse (F.sprintf "undefined random oracle %s" h)
       in
       let x = create_var vmap ts Unqual s h.RoSym.dom in
       (x, h))
    lH

let string_of_qvar (qual,s) =
  match qual with
  | Unqual -> s
  | Qual q -> q^"`"^s

let init_odef_params vmap_g ts ?(qual=true) oname vs =
  let osym =
    try E.Olist.Olist(Mstring.find oname ts.ts_odecls)
    with Not_found ->
      try E.Olist.ROlist(Mstring.find oname ts.ts_rodecls)
      with Not_found ->
        fail_parse (F.sprintf "oracle name %s not declared" oname)
  in
  let qual = if qual then (Qual oname) else Unqual in
  let vs =
    match (E.Olist.dom osym).Type.ty_node, vs with
    | Type.Prod([]), [] -> []
    | Type.Prod(tys), vs when L.length tys = L.length vs ->
      L.map
        (fun (v,t) -> create_var vmap_g ts qual v t)
        (L.combine vs tys)
    | _, [v] ->
      [create_var vmap_g ts qual v (E.Olist.dom osym)]
    | _ ->
      tacerror "Pattern matching in oracle definition invalid: %a"
        E.Olist.pp osym
  in
  vs,osym

let rec expr_of_parse_expr (vmap : GU.vmap) ts (qual : string qual) pe0 =
  let rec go pe =
    match pe with
    | V(vqual,s) ->
      let v =
        try
          (try
             (* if not qualified, then search in current context *)
             (if vqual=Unqual then Ht.find vmap (qual,s) else raise Not_found)
           with Not_found ->
             (* search with the given qualifier next *)
             Ht.find vmap (vqual,s))
        with Not_found ->
          fail_parse (F.sprintf "undefined variable %s (not in %s)"
                        (string_of_qvar (qual,s))
                        (S.concat ","
                           (Ht.fold (fun qv _ acc -> (string_of_qvar qv)::acc) vmap [])))
      in
      E.mk_V v
    | Tuple(es) -> E.mk_Tuple (L.map go es)
    | Proj(i,e) -> E.mk_Proj i (go e)
    | SLookUp(s,es) ->
       let m = try Mstring.find s ts.ts_fmapdecls with
                 Not_found -> fail_parse (F.sprintf "Undefined finite map %s" s) in
       let es = mk_Tuple (L.map go es) in
       E.mk_MapLookup m es

    | SIndom(s,e) ->
       let m = try Mstring.find s ts.ts_fmapdecls with
                 Not_found -> fail_parse (F.sprintf "Undefined finite map %s" s) in
       let e = go e in
       E.mk_MapIndom m e

    | SApp(s,es) when Mstring.mem s ts.ts_rodecls ->
      let h = Mstring.find s ts.ts_rodecls in
      let es = mk_Tuple (L.map go es) in
      E.mk_RoCall h es

    | SApp(s,es) when Mstring.mem s ts.ts_constdecls ->
      let h = Mstring.find s ts.ts_constdecls in
      let es = mk_Tuple (L.map go es) in
      E.mk_FunCall h es

    | SApp(s,[a;b]) when Mstring.mem s ts.ts_emdecls ->
      let es = Mstring.find s ts.ts_emdecls in
      E.mk_EMap es (go a) (go b)
    | SApp(s,_) when Mstring.mem s ts.ts_emdecls ->
      fail_parse (F.sprintf "bilinear map %s expects two arguments" s)
    | SApp(s,_) ->
      fail_parse (F.sprintf "undefined function symbol %s" s)
    | CFNat(i)       -> E.mk_FNat i
    | CB b           -> E.mk_B b
    | Plus(e1,e2)    -> 
            let e1 = go e1 in
            let e2 = go e2 in
            begin match e1.E.e_ty.T.ty_node with
            | T.Fq -> E.mk_FPlus [e1; e2]
            | T.Mat _ -> E.mk_MatPlus [e1; e2] 
            | T.List (_, t) -> begin match t.T.ty_node with 
                               | T.Mat _ -> E.mk_ListNop E.MatPlus [e1; e2] 
                               | _ -> tacerror "type error in addition of %a + %a" EU.pp_expr e1 EU.pp_expr e2
                               end
            | _     -> tacerror "type error in addition of %a + %a" EU.pp_expr e1 EU.pp_expr e2
            end
    | Minus(e1,e2)   -> 
            let e1 = go e1 in
            let e2 = go e2 in
            begin match e1.E.e_ty.T.ty_node with
            | T.Fq -> E.mk_FMinus (e1) (e2)
            | T.Mat _ -> E.mk_MatPlus [e1; E.mk_MatOpp e2]
            | T.List (_, t) -> begin match t.T.ty_node with
                               | T.Mat _ -> E.mk_ListNop E.MatPlus [e1;
                               E.mk_ListMatOpp e2]
                               | _ -> tacerror "subtract list err"
                               end
            | _ -> tacerror "type error in subtraction of %a - %a" EU.pp_expr e1
            EU.pp_expr e2
            end
    | Land(e1,e2)    -> E.mk_Land [go e1; go e2]
    | Lor(e1,e2)     -> E.mk_Lor [go e1; go e2]
    | Xor(e1,e2)     -> E.mk_Xor [go e1; go e2]
    | Eq(e1,e2)      -> E.mk_Eq (go e1) (go e2)
    | Concat(e1,e2)  -> E.mk_MatConcat (go e1) (go e2)
    | Ifte(e1,e2,e3) -> E.mk_Ifte (go e1) (go e2) (go e3)
    | Opp(e)         -> let e = go e in begin 
                        match e.E.e_ty.T.ty_node with
                        | T.Fq -> E.mk_FOpp e
                        | T.Mat _ -> E.mk_MatOpp e
                        | T.List (_, t) -> begin match t.T.ty_node with
                                           | T.Mat _ -> E.mk_ListMatOpp e
                                           | _ -> tacerror "opp err"
                                           end
                        | _ -> tacerror "type error in opp: %a" EU.pp_expr e
                        end
    | Inv(e)         -> E.mk_FInv (go e)
    | Not(e)         -> E.mk_Not (go e)
    | Log(e)         -> E.mk_GLog (go e)
    | Exp(e1,e2)     -> E.mk_GExp (go e1) (go e2)
    | CGen(s)        -> E.mk_GGen (create_groupvar ts s)
    | MatZ(s1,s2)    -> E.mk_MatZero (create_dimvar ts s1) (create_dimvar ts s2)
    | MatI(s1,s2)    -> E.mk_MatId  (create_dimvar ts s1) (create_dimvar ts s2)
    | CZ(s)          -> E.mk_Z (create_lenvar ts s)
    | Trans(e)       -> 
            let e = go e in begin
                match e.E.e_ty.T.ty_node with
                | T.Mat _ -> E.mk_MatTrans e
                | T.List (_, t) -> begin match t.T.ty_node with
                                   | T.Mat _ -> E.mk_ListOp E.MatTrans [e]
                                   | _ -> tacerror "op err"
                                    end
                | _ -> tacerror "type error"
            end
    | SplitLeft(e)   -> 
            let e = go e in begin
                match e.E.e_ty.T.ty_node with
                | T.Mat _ -> E.mk_MatSplitLeft e
                | T.List (_, t) -> begin match t.T.ty_node with
                                   | T.Mat _ -> E.mk_ListOp E.MatSplitLeft [e]
                                   | _ -> tacerror "op err"
                                    end
                | _ -> tacerror "type error"
            end
    | SplitRight(e)   -> 
            let e = go e in begin
                match e.E.e_ty.T.ty_node with
                | T.Mat _ -> E.mk_MatSplitRight e
                | T.List (_, t) -> begin match t.T.ty_node with
                                   | T.Mat _ -> E.mk_ListOp E.MatSplitRight [e]
                                   | _ -> tacerror "op err"
                                    end
                | _ -> tacerror "type error"
            end
    | PListOf (e,d) -> E.mk_ListOf (create_dimvar ts d) (go e)
    | Quant(q,bd,pe) ->
      let b =
        List.map (fun (vs,oname) -> init_odef_params vmap ts ~qual:false oname vs) bd
      in
      let e = expr_of_parse_expr vmap ts qual pe in
      List.fold_left (fun acc x -> Expr.mk_Quant q x acc) e b

    | Div(e1,e2)   ->
      let e1 = go e1 in
      let e2 = go e2 in
      begin match e1.E.e_ty.T.ty_node with
      | T.Fq  -> E.mk_FDiv e1 e2
      | T.G _ -> E.mk_GMult [e1; E.mk_GInv e2]
      | _     -> tacerror "type error in division of %a / %a" EU.pp_expr e1 EU.pp_expr e2
      end
    | Mult(e1,e2)  ->
      let e1 = go e1 in
      let e2 = go e2 in
      begin match e1.E.e_ty.T.ty_node with
      | T.Fq  -> E.mk_FMult [e1;e2]
      | T.G _ -> E.mk_GMult [e1;e2]
      | T.Mat _ -> E.mk_MatMult e1 e2
      | T.List (_, t) -> begin match t.T.ty_node with
                         | T.Mat _ -> E.mk_ListOp E.MatMult [e1;e2]
                         | _ -> tacerror "type error in multiplication of %a / %a" EU.pp_expr e1 EU.pp_expr e2
                         end
      | _     -> tacerror "type error in multiplication of %a / %a" EU.pp_expr e1 EU.pp_expr e2
      end
  in
  go pe0

let lcmd_of_parse_lcmd (vmap : GU.vmap) ts ~oname lcmd =
  let qual = Qual oname in
  match lcmd with
  | LLet(s,e) ->
    let e = expr_of_parse_expr vmap ts qual e in
    let v = create_var vmap ts qual s e.E.e_ty in
    G.LLet(v,e)
  | LMSet(m,es,e) ->
    let m =
      try Mstring.find m ts.ts_fmapdecls
      with Not_found -> fail_parse (F.sprintf "finite map %s" m)
    in
    let ek = mk_Tuple (L.map (expr_of_parse_expr vmap ts qual) es) in
    let e  = expr_of_parse_expr vmap ts qual e  in
    G.LMSet(m,ek,e)
  | LSamp(s,t,es) ->
    let t = ty_of_parse_ty ts t in
    let es = L.map (expr_of_parse_expr vmap ts qual) es in
    let v = create_var vmap ts qual s t in
    G.LSamp(v,(t,es))
  | LGuard(e) ->
    G.LGuard (expr_of_parse_expr vmap ts qual e)
  | LBind(_) ->
    assert false (* not implemented yet *)

let obody_of_parse_obody vmap ts ~oname (m,e) =
  let m = L.map (lcmd_of_parse_lcmd vmap ts ~oname) m in
  let e = expr_of_parse_expr vmap ts (Qual oname) e in
  (m,e)

let odec_of_parse_odec vmap_g ts ~oname od =
  (* create local vmap and use everywhere except in eq-hybrid-oracle *)
  let vmap_l = Ht.copy vmap_g in
  match od with
  | Odef ob ->
    G.Oreg (obody_of_parse_obody vmap_l ts ~oname ob)
  | Ohybrid (ob1,ob2,ob3) ->
    G.Ohyb
      { G.oh_less    = obody_of_parse_obody vmap_l ts ~oname ob1;
        G.oh_eq      = obody_of_parse_obody vmap_g ts ~oname ob2;
        G.oh_greater = obody_of_parse_obody vmap_l ts ~oname ob3; }

let odef_of_parse_odef vmap_g ts (oname, vs, odec, oc) =
  let counter = match oc with
    | None              -> G.NoCounter
    | Some `Once        -> G.Once
    | Some (`Counter i) -> G.CountVar i
  in
  let vs,osym = match init_odef_params vmap_g ts oname vs with
    | vs, E.Olist.Olist os -> vs, os
    | _                    -> fail_parse "fixme"
  in
  let od = odec_of_parse_odec vmap_g ts ~oname odec in
  osym, vs, od, counter

let gcmd_of_parse_gcmd (vmap : GU.vmap) ts gc =
  match gc with
  | GLet(s,e) ->
    let e = expr_of_parse_expr vmap ts Unqual e in
    let v = create_var vmap ts Unqual s e.E.e_ty in
    G.GLet(v,e)
  | GMSet(m,es,e) ->
    let m =
      try Mstring.find m ts.ts_fmapdecls
      with Not_found -> fail_parse (F.sprintf "finite map %s" m)
    in
    let ek = mk_Tuple (L.map (expr_of_parse_expr vmap ts Unqual) es) in
    let e  = expr_of_parse_expr vmap ts Unqual e in
    G.GMSet(m,ek,e)
  | GAssert(e) ->
    let e = expr_of_parse_expr vmap ts Unqual e in
    G.GAssert(e)
  | GSamp(s,t,es) ->
    let t = ty_of_parse_ty ts t in
    let es = L.map (expr_of_parse_expr vmap ts Unqual) es in
    let v = create_var vmap ts Unqual s t in
    G.GSamp(v,(t,es))
  | GCall(vs,aname,e,os) ->
    let asym =
      try Mstring.find aname ts.ts_adecls
      with Not_found -> fail_parse "adversary name not declared"
    in
    let e = expr_of_parse_expr vmap ts Unqual e in
    if not (Type.equal_ty e.E.e_ty asym.AdvSym.dom) then
      tacerror "Parser: adversary argument has wrong type: got %a, expected %a" Type.pp_ty
      e.E.e_ty Type.pp_ty asym.AdvSym.dom;
    let os = L.map (odef_of_parse_odef vmap ts) os in
    let cty = asym.AdvSym.codom in
    begin match cty.Type.ty_node, vs with
    | Type.Prod([]), [] ->
      G.GCall([], asym, e, os)
    | _, [v] ->
      let v = create_var vmap ts Unqual v asym.AdvSym.codom in
      G.GCall([v], asym, e, os)
    | Type.Prod(tys), vs ->
      if L.length tys <> L.length vs then
        tacerror
          "Parser: wrong argument for adversary return value, expected %i variables for type %a"
          (L.length vs) Type.pp_ty cty;
      let vts = L.combine vs tys in
      let vs = L.map (fun (v,t) -> create_var vmap ts Unqual v t) vts in
      G.GCall(vs, asym, e, os)
    | (Type.BS _|Type.Bool|Type.G _|Type.Fq|Type.Int|Type.TySym _ | Type.Mat
    _|Type.List _)
      , ([] | _ :: _ :: _) ->
      tacerror
        "Parser: wrong argument for adversary return value, expected one variable (type %a), got %i"
        Type.pp_ty cty (L.length vs)
    end

let gdef_of_parse_gdef (vmap : GU.vmap) ts gd =
  L.map (fun gc -> gcmd_of_parse_gcmd vmap ts gc) gd

let ev_of_parse_ev vmap ts pe =
  expr_of_parse_expr vmap ts Unqual pe

let se_of_parse_se (vmap : GU.vmap) ts gd ev =
  let gd = gdef_of_parse_gdef vmap ts gd in
  let ev  = ev_of_parse_ev vmap ts ev in
  let se = { G.se_gdef = gd; G.se_ev = ev } in
  Wf.wf_se Wf.NoCheckDivZero se;
  se
