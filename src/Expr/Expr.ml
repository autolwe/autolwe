(* * Typed algebraic expressions *)

(* ** Imports *)
open Abbrevs
open Util
open Type
open Syms

(* ** Expressions (hashconsed)
 * ----------------------------------------------------------------------- *)

(* *** Quantifiers *)

type quant = All | Exists

let neg_quant = function All -> Exists | Exists -> All

module Olist = struct
  type t =
    | ROlist of RoSym.t   (* list of adversary queries to random oracle *)
    | Olist  of OrclSym.t (* list of adversary queries to ordinary oracle *)
    with compare

  let dom = function
    | ROlist ros -> ros.RoSym.dom
    | Olist  os  -> os.OrclSym.dom

  let hash = function
    | ROlist ros -> hcomb 1 (RoSym.hash ros)
    | Olist  os  -> hcomb 2 (OrclSym.hash  os)

  let equal ol1 ol2 = compare ol1 ol2 = 0

  let pp fmt = function
    | ROlist ros -> RoSym.pp fmt ros
    | Olist  os  -> OrclSym.pp fmt  os

end

(* *** Types *)

type proj_type = ty * ty * ty

type perm_type = IsInv | NotInv

type cnst =
  | GGen        (* generator of $\group$ (type defines group) *)
  | FNat of int (* Natural number in field, always $\geq 0$ *)
  | Z           (* $0$ bitstring (type defines length) *)
  | B of bool   (* boolean value *)
  | MatZero
  | MatId

type op =
  (* bilinear groups *)
  | GExp of Groupvar.id          (* exponentiation in $\group_i$ *)
  | GLog of Groupvar.id          (* discrete logarithm in $\group_i$ *)
  | GInv                         (* inverse in group *)
  | EMap of EmapSym.t            (* bilinear map *)
  (* prime field *)
  | FOpp                         (* additive inverse in $\field$ *)
  | FMinus                       (* subtraction in $\field$ *)
  | FInv                         (* mult. inverse in $\field$ *)
  | FDiv                         (* division in $\field$ *)
  (* logical operators *)
  | Eq                            (* equality *)
  | Not                           (* negation *)
  | Ifte                          (* if then else *)
  (* uninterpreted functions, random oracles, and maps *)
  | FunCall   of FunSym.t         (* function call (uninterpreted) *)
  | RoCall    of RoSym.t          (* random oracle call *)
  | MapLookup of MapSym.t         (* map lookup *)
  | MapIndom  of MapSym.t         (* map defined for given value *)
  | MatMult
  | MatOpp
  | MatTrans
  | MatConcat
  | MatSplitLeft
  | MatSplitRight
  | ListOp of op
  | ListOf

type nop =
  | GMult      (* multiplication in G (type defines group) *)
  | FPlus      (* plus in Fq *)
  | FMult      (* multiplication in Fq *)
  | MatPlus
  | Xor        (* Xor of bitstrings *)
  | Land       (* logical and *)
  | Lor        (* logical or *)
  | ListNop of nop

type binding = VarSym.t list * Olist.t

type expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_tag  : int
}
and expr_node =
  | V     of VarSym.t               (* variables (program/logic/...) *)
  | Tuple of expr list              (* tuples *)
  | Proj  of int * expr             (* projection *)
  | Cnst  of cnst                   (* constants *)
  | App   of op * expr list         (* fixed arity operators *)
  | Nary  of nop * expr list        (* variable arity AC operators *)
  | Quant of quant * binding * expr (* quantifier *)

(* *** Equality, hashing, hash consing *)

let perm_type_hash = function
  | IsInv  -> 1
  | NotInv -> 2

let cnst_hash = function
  | GGen   -> 1
  | FNat n -> Hashcons.combine 2 n
  | Z      -> 3
  | B b    -> if b then 4 else 5
  | MatZero-> 6
  | MatId -> 7

let rec op_hash = function
  | GExp gv        -> hcomb 1 (Groupvar.hash gv)
  | GLog gv        -> hcomb 2 (Groupvar.hash gv)
  | GInv           -> 3
  | FOpp           -> 4
  | FMinus         -> 5
  | FInv           -> 6
  | FDiv           -> 7
  | Eq             -> 8
  | ListOp o       -> hcomb 24 (op_hash o)
  | ListOf         -> 25
  | MatMult        -> 18
  | MatOpp         -> 19
  | MatTrans       -> 20
  | MatConcat      -> 21
  | MatSplitLeft   -> 22
  | MatSplitRight  -> 23 
  | Not            -> 9
  | Ifte           -> 10
  | EMap es        -> hcomb 11 (EmapSym.hash es)
  | FunCall fs     -> hcomb 14 (FunSym.hash fs)
  | RoCall ros     -> hcomb 15 (RoSym.hash ros)
  | MapLookup ms   -> hcomb 16 (MapSym.hash ms)
  | MapIndom ms    -> hcomb 17 (MapSym.hash ms)

let rec nop_hash = function
  | FPlus  -> 1
  | FMult  -> 2
  | MatPlus -> 7
  | Xor    -> 3
  | Land   -> 4
  | Lor    -> 6
  | GMult  -> 5
  | ListNop n -> hcomb 8 (nop_hash n)

let quant_hash= function
  | All    -> 1
  | Exists -> 2

let equal_expr : expr -> expr -> bool = (==)
let hash_expr e = e.e_tag
let compare_expr e1 e2 = e1.e_tag - e2.e_tag

module Hse = Hashcons.Make (struct
  type t = expr

  let equal e1 e2 =
    equal_ty e1.e_ty e2.e_ty &&
    match e1.e_node, e2.e_node with
    | V v1, V v2                       -> VarSym.equal v1 v2
    | Tuple es1, Tuple es2             -> list_eq_for_all2 equal_expr es1 es2
    | Proj(i1,e1), Proj(i2,e2)         -> i1 = i2 && equal_expr e1 e2
    | Cnst c1, Cnst c2                 -> c1 = c2
    | App(o1,es1), App(o2,es2)         -> o1 = o2 && list_eq_for_all2 equal_expr es1 es2
    | Nary(o1,es1), Nary(o2,es2)       -> o1 = o2 && list_eq_for_all2 equal_expr es1 es2
    | Quant(q1,b1,e1), Quant(q2,b2,e2) ->
      q1 = q2 &&
        (equal_pair (equal_list VarSym.equal) Olist.equal) b1 b2 &&
        equal_expr e1 e2
    | _, _ -> false

  let hash_node = function
    | V(v)              -> VarSym.hash v
    | Tuple(es)         -> hcomb_l hash_expr 3 es
    | Proj(i,e)         -> hcomb i (hash_expr e)
    | Cnst(c)           -> cnst_hash c
    | App(o,es)         -> hcomb_l hash_expr (op_hash o) es
    | Nary(o,es)        -> hcomb_l hash_expr (nop_hash o) es
    | Quant(q,(vs,o),e) ->
      hcomb_h
        [ quant_hash q
        ; hcomb_h (List.map VarSym.hash vs)
        ; Olist.hash o
        ; hash_expr e ]

  let hash e = hcomb (hash_ty e.e_ty) (hash_node e.e_node)

  let tag n e = { e with e_tag = n }
end)

let mk_e n ty = Hse.hashcons {
  e_node = n;
  e_ty   = ty;
  e_tag  = (-1)
}

module E = StructMake (struct
  type t = expr
  let tag = hash_expr
end)
module Me = E.M
module Se = E.S
module He = E.H

(* ** Constructor functions
 * ----------------------------------------------------------------------- *)

(* *** Type checking *)

exception TypeError of (ty * ty * expr * expr option * string)

let ensure_mdim_equal n m =
   match (mdim_equal n m) with
   | true -> ()
   | _ -> failwith (fsprintf "Identity requires equal mdim")

let ensure_ty_equal ty1 ty2 e1 e2 s =
  ignore (equal_ty ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

let ensure_listmult_compat ty1 ty2 e1 e2 s =
    ignore (listmult_compat_ty ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

let ensure_listconcat_compat ty1 ty2 e1 e2 s =
    ignore (listconcat_compat_ty ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

let ensure_matmult_compat ty1 ty2 e1 e2 s =
    ignore (matmult_compat_ty ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

let ensure_concat_compat ty1 ty2 e1 e2 s =
    ignore (concat_compat_ty ty1 ty2 || raise (TypeError(ty1, ty2, e1, e2, s)))

let ensure_split_compat ty e s =
    ignore (split_compat ty || raise (TypeError(ty, ty, e, None, s)))

let ensure_listsplit_compat ty e s =
    match ty.ty_node with
    | List (_, t) -> ensure_split_compat t e s
    | _ -> assert false

let ensure_mat_ty ty = 
    match ty.ty_node with
    | Mat (n,m) -> (n,m)
    | _ -> failwith (fsprintf "Matrix expected: got %a" pp_ty ty)

let ensure_list_ty ty s =
    match ty.ty_node with
    | List (d, t) -> (d,t)
    | _ -> failwith (fsprintf "List expected: got %a from %s" pp_ty ty s) 

let rec get_mat_mdims ty =
    match ty.ty_node with
    | Mat (n,m) -> (n,m)
    | List (_, t) -> get_mat_mdims t
    | _ -> failwith (fsprintf "Matrix or list of matrices expected: got %a" pp_ty ty)

let ensure_ty_G ty s =
  match ty.ty_node with
  | G gv -> gv
  | _    -> failwith (fsprintf "%s: expected group type, got %a" s pp_ty ty)

(* *** Constant mk functions *)

let mk_Cnst c ty = mk_e (Cnst c) ty

let mk_GGen gv = mk_Cnst GGen (mk_G gv)

let mk_FNat n = assert (n >= 0); mk_Cnst (FNat n) mk_Fq

let mk_FOne = mk_Cnst (FNat 1) mk_Fq

let mk_FZ = mk_Cnst (FNat 0) mk_Fq

let mk_Z lv = mk_Cnst Z (mk_BS lv)

let mk_B  b = mk_Cnst (B b) mk_Bool

let mk_True = mk_B true

let mk_False = mk_B false


let mk_MatZero n m = mk_Cnst MatZero (mk_Mat n m)


let mk_MatId n m =
    ensure_mdim_equal n m;
    mk_Cnst MatId (mk_Mat n m)


(* *** Fixed arity mk functions *)

let mk_App o es ty = mk_e (App(o,es)) ty

let mk_GExp a b =
  let gv = ensure_ty_G a.e_ty "mk_GExp" in
  ensure_ty_equal b.e_ty mk_Fq b None "mk_GExp";
  mk_App (GExp gv) [a;b] a.e_ty

let mk_GOne gn =
  mk_GExp (mk_GGen gn) mk_FZ

let mk_GLog a =
  let gv = ensure_ty_G a.e_ty "mk_GLog" in
  mk_App (GLog gv) [a] mk_Fq

let mk_GInv a =
  let _gv = ensure_ty_G a.e_ty "mk_GInv" in
  mk_App GInv  [a] a.e_ty

let mk_EMap es a b =
  ensure_ty_equal a.e_ty (mk_G es.EmapSym.source1) a None "mk_EMap";
  ensure_ty_equal b.e_ty (mk_G es.EmapSym.source2) b None "mk_EMap";
  mk_App (EMap es) [a;b] (mk_G es.EmapSym.target)

let mk_FOpp a =
  ensure_ty_equal a.e_ty mk_Fq a None "mk_FOpp";
  mk_App FOpp [a] mk_Fq

let mk_FMinus a b =
  ensure_ty_equal a.e_ty mk_Fq a None "mk_FMinus";
  ensure_ty_equal b.e_ty mk_Fq b None "mk_FMinus";
  mk_App FMinus [a;b] mk_Fq

let mk_FInv a =
  ensure_ty_equal a.e_ty mk_Fq a None "mk_FInv";
  mk_App FInv [a] mk_Fq

let mk_FDiv a b =
  ensure_ty_equal a.e_ty mk_Fq a None "mk_FDiv";
  ensure_ty_equal b.e_ty mk_Fq b None "mk_FDiv";
  mk_App FDiv [a;b] mk_Fq

let mk_Eq a b =
  ensure_ty_equal a.e_ty b.e_ty a (Some b) "mk_Eq";
  mk_App Eq [a;b] mk_Bool

let mk_Not a =
  ensure_ty_equal a.e_ty mk_Bool a None "mk_Not";
  mk_App Not [a] mk_Bool

let mk_Ifte a b c =
  ensure_ty_equal a.e_ty mk_Bool a None "mk_Ifte";
  ensure_ty_equal b.e_ty c.e_ty b (Some c) "mk_Ifte";
  mk_App Ifte [a;b;c] b.e_ty


(* FIXME: check types? *)
let mk_FunCall f e =
  ensure_ty_equal e.e_ty f.FunSym.dom e None "mk_FunCall";
  mk_App (FunCall(f)) [e] f.FunSym.codom

let mk_RoCall h e =
  ensure_ty_equal e.e_ty h.RoSym.dom e None "mk_RoCall";
  mk_App (RoCall(h)) [e] h.RoSym.codom

let mk_MapLookup h e =
  ensure_ty_equal e.e_ty h.MapSym.dom e None "mk_MapLookup";
  mk_App (MapLookup(h)) [e] h.MapSym.codom

let mk_MapIndom h e =
  ensure_ty_equal e.e_ty h.MapSym.dom e None "mk_MapIndom";
  mk_App (MapIndom(h)) [e] mk_Bool

let rec flatten nop es =
  let go e =
    match e.e_node with
    | Nary(nop1, es1) when nop1 = nop -> flatten nop es1
    | _                               -> [e]
  in
  L.concat (L.map go es)

let mk_nary s sort o es ty =
  let es = flatten o es in
  let es = if sort then L.sort compare_expr es else es in
  match es with
  | []  -> failwith (F.sprintf "%s: empty list given" s);
  | [a] -> a
  | _   ->
    L.iter (fun e -> ensure_ty_equal e.e_ty ty e None s) es;
    mk_e (Nary(o,es)) ty

let mk_ListNop nop es =
    match nop, es with
    | MatPlus, e :: _ ->
        begin match e.e_ty.ty_node with
        | List (d,t) -> 
                begin match t.ty_node with
                | Mat (n,m) -> mk_nary "mk_ListPlus" true (ListNop MatPlus) es (mk_List d (mk_Mat n m))
                | _ -> failwith (F.sprintf "Type error in listplus1")
                end
        | _ -> failwith (F.sprintf "Type error in listplus2")
        end
    | _ -> failwith (F.sprintf "Unrecognized list nop")

let mk_ListOp op es =
    match op,es with
    | MatMult, [a;b] -> 
        ensure_listmult_compat a.e_ty b.e_ty a (Some b) "mk_ListMult";
        let (d1, t1) = ensure_list_ty a.e_ty "" in
        let (_, t2) = ensure_list_ty b.e_ty "" in
        let (n,m) = matmult_get_dim t1 t2 in
        mk_App (ListOp MatMult) [a;b] (mk_List d1 (mk_Mat n m))
    | MatOpp, [a] -> 
            let (d,_) = ensure_list_ty a.e_ty "" in
            let (n,m) = get_mat_mdims a.e_ty in
            mk_App (ListOp MatOpp) [a] (mk_List d (mk_Mat n m))
    | MatTrans, [a] ->
            let (d,_) = ensure_list_ty a.e_ty "" in
            let (n,m) = get_mat_mdims a.e_ty in
            mk_App (ListOp MatTrans) [a] (mk_List d (mk_Mat m n))
    | MatConcat, [a;b] -> 
            ensure_listconcat_compat a.e_ty b.e_ty a (Some b) "mk_ListConcat";
            let (d, t1) = ensure_list_ty a.e_ty "" in
            let (_, t2) = ensure_list_ty b.e_ty "" in
            let (n,m1) = get_mat_mdims a.e_ty in
            let (_, m2) = get_mat_mdims b.e_ty in
            mk_App (ListOp MatConcat) [a;b] (mk_List d (mk_Mat n
            (MDPlus(m1,m2))))

    | MatSplitLeft, [a] -> 
            ensure_listsplit_compat a.e_ty a "mk_ListSplitLeft";
            let (d, t) = ensure_list_ty a.e_ty "" in
            let (n,_) = ensure_mat_ty t in
            let (d1, _) = get_split_dim t in
            mk_App (ListOp MatSplitLeft) [a] (mk_List d (mk_Mat n d1))

    | MatSplitRight, [a] -> 
            ensure_listsplit_compat a.e_ty a "mk_ListSplitRight";
            let (d, t) = ensure_list_ty a.e_ty "" in
            let (n,_) = ensure_mat_ty t in
            let (_, d2) = get_split_dim t in
            mk_App (ListOp MatSplitRight) [a] (mk_List d (mk_Mat n d2))

    | _ -> failwith "unsupported list op"


let mk_ListMatMult e1 e2 = mk_ListOp MatMult [e1;e2]
let mk_ListMatConcat e1 e2 = mk_ListOp MatConcat [e1;e2]
let mk_ListMatTrans e1 = mk_ListOp MatTrans [e1]
let mk_ListMatOpp e1 = mk_ListOp MatOpp [e1]
let mk_ListMatSplitLeft e1 = mk_ListOp MatSplitLeft [e1]
let mk_ListMatSplitRight e1 = mk_ListOp MatSplitRight [e1]

let mk_ListOf d e = mk_App ListOf [e] (mk_List d e.e_ty)

let mk_ListOfMatZero a n m = mk_ListOf a (mk_MatZero n m)


let mk_MatMult a b =
    ensure_matmult_compat a.e_ty b.e_ty a (Some b) "mk_MatMult";
    let (n,m) = matmult_get_dim a.e_ty b.e_ty in
    mk_App (MatMult) [a;b] (mk_Mat n m)

let mk_MatOpp a =
    let (n,m) = ensure_mat_ty a.e_ty in
    mk_App (MatOpp) [a] (mk_Mat n m)

let mk_MatTrans a =
    let (n,m) = ensure_mat_ty a.e_ty in
    mk_App (MatTrans) [a] (mk_Mat m n)

let mk_Trans a =
    match a.e_ty.ty_node with
    | Mat _ -> mk_MatTrans a
    | List _ -> mk_ListMatTrans a
    | _ -> failwith "bad trans argument"


let mk_MatSplitLeft a =
    ensure_split_compat a.e_ty a "mk_MatSplitLeft";
    let (n, _) = ensure_mat_ty a.e_ty in
    let (d1, _) = get_split_dim a.e_ty in
    mk_App (MatSplitLeft) [a] (mk_Mat n d1)
 
let mk_MatSplitRight a =
    ensure_split_compat a.e_ty a "mk_MatSplitLeft";
    let (n, _) = ensure_mat_ty a.e_ty in
    let (_, d2) = get_split_dim a.e_ty in
    mk_App (MatSplitRight) [a] (mk_Mat n d2)

let mk_SplitLeft a =
    match a.e_ty.ty_node with
    | Mat _ -> mk_MatSplitLeft a
    | List _ -> mk_ListMatSplitLeft a
    | _ -> failwith "bad trans argument"

let mk_SplitRight a =
    match a.e_ty.ty_node with
    | Mat _ -> mk_MatSplitRight a
    | List _ -> mk_ListMatSplitRight a
    | _ -> failwith "bad trans argument"


let mk_MatConcat a b =
    ensure_concat_compat a.e_ty b.e_ty a (Some b) "mk_MatConcat";
    let (n,m1) = ensure_mat_ty a.e_ty in
    let (_,m2) = ensure_mat_ty b.e_ty in
    mk_App (MatConcat) [a;b] (mk_Mat n (MDPlus(m1,m2)))

let mk_Concat a b =
    match a.e_ty.ty_node with
    | Mat _ -> mk_MatConcat a b
    | List _ -> mk_ListOp (MatConcat) [a;b]
    | _ -> failwith "bad trans argument"


(* *** Nary mk functions *)



let mk_FPlus es = mk_nary "mk_FPlus" true FPlus es mk_Fq

let mk_FMult es = mk_nary "mk_FMult" true FMult es mk_Fq


let mk_MatPlus es =
    match es with
    | e :: _ ->
       begin match e.e_ty.ty_node with
       | Mat (n,m) -> mk_nary "mk_MatPlus" true MatPlus es (mk_Mat n m)
       | _ -> failwith (F.sprintf "not matrix")
       end
    | _ -> failwith (F.sprintf "empty matplus")

let mk_MatPlus_safe es ty = match es with
    | [] -> let (n,m) = ensure_mat_ty ty in mk_MatZero n m
    | _ -> mk_MatPlus es

let mk_ListMatPlus_safe es ty = match es with
    | [] -> let (n,m) = get_mat_mdims ty in let (a,_) = ensure_list_ty ty "" in mk_ListOfMatZero a n m
    | _ -> mk_ListNop MatPlus es

let valid_Xor_type ty =
  let rec valid ty =
    match ty.ty_node with
    | BS _ | Bool -> true
    | Prod tys    -> L.for_all valid tys
    | _           -> false
  in
  valid ty

let mk_Xor = function
  | e::_ as es ->
    if (valid_Xor_type e.e_ty) then
      mk_nary "mk_Xor" true Xor es e.e_ty
    else
      failwith "mk_Xor: invalid type, expected (nested) tuples of bitstrings/bools."
  | _ -> failwith "mk_Xor: expected non-empty list"

let mk_Land es = mk_nary "mk_Land" false Land es mk_Bool
let mk_Lor es = mk_nary "mk_Lor" false Lor es mk_Bool

let mk_GMult es =
  match es with
  | e::_ ->
    begin match e.e_ty.ty_node with
    | G gv -> mk_nary "mk_GMult" true GMult es (mk_G gv)
    | _    -> assert false
    end
  | _ -> assert false

let mk_Nary op es =
  match op with
  | FPlus -> mk_FPlus es
  | FMult -> mk_FMult es
  | MatPlus -> mk_MatPlus es
  | Xor   -> mk_Xor   es
  | Land  -> mk_Land  es
  | Lor   -> mk_Lor  es
  | GMult -> mk_GMult es
  | ListNop nop -> mk_ListNop nop es

(* *** Remaining mk functions *)

let mk_V v = mk_e (V v) v.VarSym.ty

(*
let mk_F h e =
  ensure_ty_equal h.Fsym.dom e.e_ty e None (fsprintf "mk_F for %a" Fsym.pp h);
  mk_e (F(h,e)) h.Fsym.codom
 *)

let mk_Quant q b e =
  mk_e (Quant(q,b,e)) mk_Bool

let mk_All = mk_Quant All

let mk_Exists = mk_Quant Exists

let mk_Tuple es =
  match es with
  | [e] -> e
  | _   -> mk_e (Tuple es) (mk_Prod (L.map (fun e -> e.e_ty) es))

let mk_Proj i e =
  match e.e_ty.ty_node with
  | Prod(tys) when i >= 0 && L.length tys > i ->
    mk_e (Proj(i,e)) (L.nth tys i)
  | _ ->
    let s = F.sprintf "mk_Proj: expected product type with >= %i components" (i+1) in
    raise (TypeError(e.e_ty,e.e_ty,e,None,s))

let mk_InEq a b =
  mk_Not (mk_Eq a b)


let listForgetOp op =  match op with
    | ListOp o -> o
    | o -> o

let listForgetNop nop =  match nop with
    | ListNop o -> o
    | o -> o

let listForgetExp e = 
    let {e_node = enode; e_ty = ety; e_tag = etag} = e in
    let new_enode = match enode with
                    | App (op, es) -> App (listForgetOp op, es)
                    | Nary (nop, es) -> Nary (listForgetNop nop, es)
                    | _ -> enode in
    {e_node = new_enode; e_ty = ety; e_tag = etag}



let listRememberOp op = ListOp op
let listRememberNop nop = ListNop nop

let listRememberExp e = 
    let {e_node = enode; e_ty = ety; e_tag = etag} = e in
    let new_enode = match ety.ty_node, enode with
                    | List _, App (op, es) -> App (listRememberOp op, es)
                    | List _, Nary (op, es) -> Nary (listRememberNop op, es)
                    | _, _ -> enode in
    {e_node = new_enode; e_ty = ety; e_tag = etag}






(* ** Generic functions on expressions
 * ----------------------------------------------------------------------- *)

let sub_map g e =
  match e.e_node with
  | V _ | Cnst _ -> e
  | Tuple(es) ->
    let es' = smart_map g es in
    if es == es' then e
    else mk_e (Tuple es') e.e_ty
  | Proj(i, e1) ->
    let e1' = g e1 in
    if e1 == e1' then e
    else mk_e (Proj(i, e1')) e.e_ty
  | App(o, es) ->
    let es' = smart_map g es in
    if es == es' then e
    else mk_e (App(o, es')) e.e_ty
  | Nary(o, es) ->
    let es' = smart_map g es in
    if es == es' then e
    else mk_e (Nary(o, es')) e.e_ty
  | Quant(q,b,e1) ->
    let e' = g e1 in
    if e1 == e' then e
    else mk_Quant q b e'

let check_fun g e =
  let e' = g e in
  ensure_ty_equal e'.e_ty e.e_ty e (Some e') "check_fun";
  e'

let e_sub_map g = sub_map (check_fun g)

let e_sub_fold g acc e =
  match e.e_node with
  | V _ | Cnst _ -> acc
  | Proj(_, e) | Quant(_,_,e) -> g acc e
  | Tuple(es) | App(_, es) | Nary(_, es)-> L.fold_left g acc es

let e_sub_iter g e =
  match e.e_node with
  | V _ | Cnst _ -> ()
  | Proj(_, e) | Quant(_,_,e) -> g e
  | Tuple(es) | App(_, es) | Nary(_, es)-> L.iter g es

let rec e_iter g e =
  g e; e_sub_iter (e_iter g) e

let e_sub_exists f =
  e_sub_fold (fun acc e -> acc || f e) false

let rec e_exists f e =
  f e || e_sub_exists (e_exists f) e

let e_sub_forall f =
  e_sub_fold (fun acc e -> acc && f e) true

let rec e_forall f e =
  f e && e_sub_forall (e_forall f) e

let e_find f (e : expr) =
  let module E = struct exception Found of expr end in
  let rec aux e =
    if f e then raise (E.Found e)
    else e_sub_iter aux e in
  try aux e; raise Not_found with E.Found e -> e

let e_find_all f e =
  let rec aux s e =
    let s = if f e then Se.add e s else s in
    e_sub_fold aux s e in
  aux Se.empty e

let e_map f =
  let tbl = He.create 103 in
  let rec aux e =
    try He.find tbl e
    with _ ->
      let e' = f (sub_map aux e) in
      ensure_ty_equal e'.e_ty e.e_ty e (Some e') "e_rec_map";
      He.add tbl e e';
      e' in
  aux

let e_map_ty_maximal ty g e0 =
  let rec go ie e =
    (* me = e is a maximal expression of the desired type *)
    let me = not ie && equal_ty e.e_ty ty in
    (* ie = immediate subterms of e inside larger expression of the desired type *)
    let ie = me || (ie && equal_ty e.e_ty ty) in
    let trans = if me then g else id in
    match e.e_node with
    | V(_) | Cnst(_) -> e
    | Tuple(es) ->
      let es = L.map (go ie) es in
      trans (mk_Tuple es)
    | Quant (q,b,e) ->
      let e = go ie e in
      trans (mk_Quant q b e)
    | Proj(i,e) ->
      let e = go ie e in
      trans (mk_Proj i e)
    | App(o,es) ->
      let es = L.map (go ie) es in
      trans (mk_App o es e.e_ty)
    | Nary(o,es) ->
      let es = L.map (go ie) es in
      trans (mk_Nary o es)
  in
  go false e0

let e_map_top f =
  let tbl = He.create 103 in
  let rec aux e =
    try He.find tbl e
    with Not_found ->
      let e' = try check_fun f e with Not_found -> sub_map aux e in
      He.add tbl e e';
      e'
  in
  aux

let e_replace e1 e2 =
  e_map_top (fun e -> if equal_expr e e1 then e2 else raise Not_found)

let e_subst s =
  e_map_top (fun e -> Me.find e s)


let listForgetExprs = e_map listForgetExp
let listRememberExprs = e_map listRememberExp
