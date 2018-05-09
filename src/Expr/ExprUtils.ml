(* * Additional functions on expressions
 * These functions do not require access to expression internals. *)

(* ** Imports *)
open Expr
open Type
open Syms
open Abbrevs
open Util

let ty_prod_vs vs =
  match List.map (fun vs -> vs.VarSym.ty) vs with
  | [a] -> a
  | ts  -> mk_Prod ts

let mk_GExp_Gen gv p = mk_GExp (mk_GGen gv) p

let mk_Land_nofail = function
  | [] -> mk_True
  | l  -> mk_Land l


let mk_Lor_nofail = function
  | [] -> mk_False
  | l  -> mk_Lor l

(* ** Indicator functions
 * ----------------------------------------------------------------------- *)

let is_V e = match e.e_node with V _ -> true | _ -> false

let is_Quant e = match e.e_node with Quant(_,_,_) -> true | _ -> false

let is_Quant_fixed q e =
  match e.e_node with
  | Quant(q',_,_) when q=q' -> true
  | _ -> false

let is_All = is_Quant_fixed All

let is_Exists = is_Quant_fixed Exists

let is_Tuple e = match e.e_node with Tuple _ -> true | _ ->  false

let is_Unit e = match e.e_node with Tuple [] -> true | _ ->  false

let is_Proj e = match e.e_node with Proj _ -> true | _ ->  false

let is_Cnst e = match e.e_node with Cnst _ -> true | _ -> false

let is_FNat e = match e.e_node with Cnst (FNat _) -> true | _ -> false

let is_FOne e = match e.e_node with Cnst (FNat 1) -> true | _ -> false

let is_FZ e = match e.e_node with Cnst (FNat 0) -> true | _ -> false

let is_Cnst_fixed c e =
  match e.e_node with
  | Cnst c' -> c = c'
  | _ -> false

let is_True e = is_Cnst_fixed (B true) e

let is_False e = is_Cnst_fixed (B false) e

let is_GGen e = is_Cnst_fixed GGen e

let is_GOne e = is_G e.e_ty && equal_expr e (mk_GOne (destr_G_exn e.e_ty))

let is_some_App e = match e.e_node with App _ -> true | _ -> false

let is_App o e = match e.e_node with App(o',_) -> o = o' | _ -> false

let is_MapLookup e = match e.e_node with App(MapLookup _,_) -> true | _ -> false

let is_FunCall e = match e.e_node with App(FunCall _,_) -> true | _ -> false

let is_FDiv e = is_App FDiv e

let is_FOpp e = is_App FOpp e

let is_Ifte e = is_App Ifte e

let is_GExp e = match e.e_node with App(GExp _,_) -> true | _ -> false

let is_some_Nary e = match e.e_node with Nary _ -> true | _ -> false

let is_Nary o e = match e.e_node with Nary(o',_) -> o' = o | _ -> false

let is_FPlus e = is_Nary FPlus e

let is_FMult e = is_Nary FMult e

let is_Xor e = is_Nary Xor e

let is_Land e = is_Nary Land e

let is_Lor e = is_Nary Lor e

let is_GLog e = match e.e_node with App(GLog _, _) -> true | _ -> false

let is_RoCall e = match e.e_node with App(RoCall _, _) -> true | _ -> false

let is_RoCall_ros e ros =
  match e.e_node with App(RoCall ros', _) -> RoSym.equal ros ros' | _ -> false

let is_GLog_gv gv e =
  match e.e_node with App(GLog gv', _) -> Groupvar.equal gv gv' | _ -> false

let is_Eq e = is_App Eq e

let is_Not e = is_App Not e

let is_field_op = function
  | FOpp | FMinus | FInv | FDiv -> true
  | GExp _ | GLog _ | GInv
  | EMap _ 
  | RoCall _ | MapLookup _
  | MapIndom _ | Eq
  | Ifte | Not
  | FunCall _  | MatMult | MatOpp | MatTrans | MatConcat |
  MatSplitLeft | MatSplitRight -> false
  | ListOp _ -> false
  | ListOf -> false

let is_field_nop = function
  | FPlus | FMult -> true
  | Xor | Land | Lor | GMult | MatPlus | ListNop _ -> false

let is_field_exp e = match e.e_node with
  | Cnst(FNat _) -> true
  | App(o,_)     -> is_field_op o
  | Nary(o,_)    -> is_field_nop o
  | _            -> false

let is_list_op = function
    | ListOp _ -> true
    | ListOf -> true
    | _ -> false

let is_list_nop = function
    | ListNop _ -> true
    | _ -> false

let is_mat_op = function
  | MatMult | MatOpp | MatTrans | MatConcat | MatSplitLeft |
  MatSplitRight -> true
  | _ -> false

let is_matplus e = match e.e_node with
  | Nary(MatPlus, _) -> true
  | _ -> false

let is_mat_nop = fun x -> x = MatPlus

let is_mat_exp e = match e.e_node with
  | App(o,_) -> is_mat_op o
  | Nary(o,_)-> is_field_nop o
  | _ -> false

let is_list_exp e = match e.e_node with
  | App(o,_) -> is_list_op o
  | Nary(o,_) -> is_field_nop o
  | _ -> false
 
(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

let pp_sort_expensive = ref false

let pp_number_tuples = ref false

(* The term $*(+(a,b),c)$ can be printed as $(a + b) * c$
   or $a + b * c$.
   We pass enough information to the function call
   printing $a + b$ to decide if parentheses are
   required around this expression or not.
*)

(** Pretty print constant. *)
let pp_cnst fmt c ty =
  match c with
  | GGen   -> if Groupvar.name (destr_G_exn ty) <> ""
              then F.fprintf fmt "g_%a" Groupvar.pp (destr_G_exn ty)
              else F.fprintf fmt "g"
  | FNat n -> F.fprintf fmt "%i" n
  | Z      -> F.fprintf fmt "0%%%a" pp_ty ty
  | B b    -> F.fprintf fmt "%b" b
  | MatZero -> F.fprintf fmt "0" 
  | MatId  -> F.fprintf fmt "I" 

(** Constructor above the current expression. *)
type 'a above =
    PrefixApp          (*r prefix function application: $f(\ldots)$ *)
  | Top                (*r topmost, nothing above *)
  | Infix  of op * int (*r infix operator, i-th argument *)
  | NInfix of nop      (*r n-ary infix operator *)
  | Tup                (*r tuple constructor *)

(** Above does not have separators that allow to leave out parentheses. *)
let notsep above = above <> Top && above <> PrefixApp && above <> Tup

(** Surround with an [hv] or [hov] box. *)
let pp_box hv pp fmt =
  if hv
  then F.fprintf fmt "@[<hv>%a@]" pp
  else F.fprintf fmt "@[<hov>%a@]" pp

(** Enclose with given format strings. *)
let pp_enclose hv ~pre ~post pp fmt x =
  F.fprintf fmt "%(%)%a%(%)" pre (pp_box hv pp) x post

(** Enclose with parens. *)
let pp_paren hv = pp_enclose hv ~pre:"(" ~post:")"

(** Enclose with parens depending on boolean argument. *)
let pp_maybe_paren hv c = pp_if c (pp_paren hv) (pp_box hv)

let pp_binder fmt (vs,o) =
  let l_paren,r_paren =
    match vs with
    | [_] -> "",""
    | _   -> "(",")"
  in
  F.fprintf fmt "%s%a%s in L_%a"
    l_paren (pp_list "," VarSym.pp) vs r_paren Olist.pp o

(** Pretty-prints expression assuming that
    the expression above is of given type. *)
let rec pp_exp_p ~qual above fmt e =
  (* F.fprintf fmt "%i$" e.e_tag; *)
  match e.e_node with
  | V(v)       ->
    (* F.fprintf fmt "%a.%i" VarSym.pp v (VarSym.hash v) *)
    F.fprintf fmt "%a" (VarSym.pp_qual ~qual) v
  | Tuple([]) ->
    pp_string fmt "()"
  | Tuple(es) ->
    let pp_entry fmt (i,e) =
      F.fprintf fmt "%i := %a" i (pp_exp_p ~qual Tup) e
    in
    let pp fmt es =
      if !pp_number_tuples then
        F.fprintf fmt "@[<hov>%a@]"
          (pp_list ",@\n" pp_entry)
          (num_list es)
      else
        F.fprintf fmt "@[<hov>%a@]"
          (pp_list ",@," (pp_exp_p ~qual Tup))
          es
    in
    pp_maybe_paren false (above <> PrefixApp) pp fmt es
  | Quant(q,b,e) ->
     F.fprintf fmt "%s %a: %a" (match q with All -> "forall" | Exists -> "exists")
       pp_binder b (pp_exp_p ~qual Top) e
  | Proj(i,e) ->
    F.fprintf fmt "%a#%i" (pp_exp_p ~qual Tup) e i
  | Cnst(c)    -> pp_cnst fmt c e.e_ty
  | App(o,es)  -> pp_op_p ~qual above fmt (o,es)
  | Nary(o,es) ->
    let es =
      if !pp_sort_expensive then (
        L.map (fun e -> (e, fsprintf "%a" (pp_exp_p ~qual Top) e)) es
        |> L.sort (fun (e1,s1) (e2,s2) ->
             let cmp = compare s1 s2 in
             if cmp<>0 then cmp else compare_expr e1 e2)
        |> L.map fst
      ) else (
        es
      )
    in
    pp_nop_p ~qual above fmt (o,es)

(** Pretty-prints operator assuming that
    the expression above is of given type. *)
and pp_op_p ~qual above fmt (op, es) =
  let pp_bin p op ops a b =
    let pp fmt () =
      F.fprintf fmt ("@[<hv>%a"^^ops^^"%a@]")
        (pp_exp_p ~qual (Infix(op,0))) a
        (pp_exp_p ~qual (Infix(op,1))) b in
    pp_maybe_paren true p pp fmt ()
  in
  let pp_prefix op before after a =
    F.fprintf fmt "%s%a%s" before (pp_exp_p ~qual (Infix(op,0))) a after
  in
  match op, es with
  | ListOf, [a] ->
    pp_prefix ListOf "[" "]" a
  | (MatSplitLeft | ListOp MatSplitLeft),   [a]   ->
    pp_prefix MatSplitLeft  "sl ("     ")"    a
  | (MatSplitRight | ListOp MatSplitRight),   [a]   ->
    pp_prefix MatSplitRight  "sr ("     ")"    a
  | (MatConcat | ListOp MatConcat), [a;b] ->
    pp_bin (notsep above && above<>Infix(MatConcat,0)) MatConcat "@ || " a b
  | ListOp MatMult, [a;b] ->
    pp_bin (notsep above && above<>Infix(ListOp MatMult,0)) (ListOp MatMult) "@ * " a b
  | MatMult, [a;b] ->
    pp_bin (notsep above && above<>Infix(MatMult,0)) MatMult "@ * " a b
  | (MatOpp | ListOp MatOpp),   [a]   ->
    pp_prefix MatOpp  "-("     ")"    a
  | (MatTrans | ListOp MatTrans),   [a]   ->
    pp_prefix MatTrans  "tr ("     ")"    a
  | GExp _,   [a;b] ->
    pp_bin (notsep above && above<>NInfix(GMult) && above<>NInfix(GMult)
            && above<>Infix(Eq,0) && above<>Infix(Eq,1))
      op "^" a b
  | FDiv,   [a;b] ->
    pp_bin (notsep above) FDiv "@ / " a b
  | FMinus, [a;b] ->
    pp_bin (notsep above && above<>Infix(FMinus,0)) FMinus "@ - " a b
  | Eq,     [a;b] ->
    pp_bin (notsep above && above<>NInfix(Land) && above<>NInfix(Lor)) Eq "@ = " a b
  | GLog _, [a]   ->
    F.fprintf fmt "@[<hov>log(%a)@]" (pp_exp_p ~qual PrefixApp) a
  | FOpp,   [a]   ->
    pp_prefix FOpp  "-"     ""    a
  | FInv,   [a]   ->
    pp_prefix FInv  ""      "^-1" a
  | Not,    [a]   ->
    begin match a.e_node with
    | App(Eq,[e1;e2]) ->
      pp_bin (notsep above && above<>NInfix(Land) && above<>NInfix(Lor)) Eq "@ <> " e1 e2
    | _ ->
      pp_prefix Not   "not "  ""    a
    end
  | EMap _,[a;b] ->
    let ppe = pp_exp_p ~qual PrefixApp in
    F.fprintf fmt "e(%a,%a)" ppe a ppe b
  | Ifte, [a;b;d] ->
    let ppe i = pp_exp_p ~qual (Infix(Ifte,i)) in
    let pp fmt () =
      F.fprintf fmt "@[<hv>%a?%a:%a@]" (ppe 0) a (ppe 1) b (ppe 2) d
    in
    pp_maybe_paren true (notsep above) pp fmt ()
  | GInv, [a] ->
    pp_prefix GInv  ""      "^-1" a
  | FunCall f, [e] ->
    F.fprintf fmt "%a(%a)" FunSym.pp f (pp_exp_p ~qual PrefixApp) e
  | RoCall h, [e] ->
    F.fprintf fmt "%a(%a)" RoSym.pp h (pp_exp_p ~qual PrefixApp) e
  | MapLookup h, [e] ->
    F.fprintf fmt "%a[%a]" MapSym.pp h (pp_exp_p ~qual PrefixApp) e
  | MapIndom h, [e] when is_Unit e ->
    F.fprintf fmt "is_set(%a)" MapSym.pp h
  | MapIndom h, [e] ->
    F.fprintf fmt "in_dom(%a,%a)" (pp_exp_p ~qual PrefixApp) e MapSym.pp h
  | (FunCall _ | RoCall _ | MapLookup _ | MapIndom _), ([] | _::_::_)
  | (FOpp | FInv | Not | GInv | GLog _ | MatOpp | MatTrans | MatSplitRight |
  MatSplitLeft), ([] | _::_::_)
  | (FMinus | FDiv | Eq | EMap _ | GExp _ | MatConcat), ([] | [_] | _::_::_::_)
  | Ifte, ([] | [_] | [_;_] | _::_::_::_::_)
  | MatMult, ([] | [_] | _::_::_) 
  | _ ->
    failwith "pp_op: invalid expression"

(** Pretty-prints n-ary operator assuming that
    the expression above is of given type. *)
and pp_nop_p ~qual above fmt (op,es) =
  let pp_nary hv op ops p =
    pp_maybe_paren hv p (pp_list ops (pp_exp_p ~qual (NInfix(op)))) fmt es
  in
  match op with
  | ListNop MatPlus -> pp_nary true (ListNop MatPlus) "@ + " (notsep above)
  | MatPlus -> pp_nary true MatPlus "@ + " (notsep above)
  | GMult  -> pp_nary true GMult  "@ * "   (notsep above)
  | FPlus  -> pp_nary true FPlus  "@ + "   (notsep above)
  | Xor    -> pp_nary true Xor    "@ ++ " (notsep above)
  | Land   -> pp_nary true Land   "@ /\\ " (notsep above)
  | Lor    -> pp_nary true Lor    "@ \\/ " (notsep above)
  | FMult  ->
    let p =
      match above with
      | NInfix(FPlus) | Infix(FMinus,_) -> false
      | _ -> notsep above in
    pp_nary false FMult "@,*" p
  | ListNop _ -> failwith "bad list nop"

(** Pretty-print expressions/operators assuming they are topmost. *)
let pp_expr fmt e = pp_exp_p ~qual:Unqual Top fmt e
let pp_expr_qual ~qual fmt e = pp_exp_p ~qual Top fmt e
let pp_op  fmt x = pp_op_p ~qual:Unqual Top fmt x
let pp_nop fmt x = pp_nop_p ~qual:Unqual Top fmt x

(** Pretty-printing without parens around tuples. *)
let pp_expr_tnp fmt e =
  if is_Unit e then pp_string fmt ""
  else pp_exp_p ~qual:Unqual PrefixApp fmt e

let pp_ctxt fmt (v,e) =
  F.fprintf fmt "@[<hov>(%a ->@ %a)@]" VarSym.pp v pp_expr e

(* ** Destructor functions
 * ----------------------------------------------------------------------- *)

exception Destr_failure of string

let destr_V e = match e.e_node with V v -> v | _ -> raise (Destr_failure "V")

let destr_Quant e =
  match e.e_node with Quant(q,b,e) -> (q,b,e) | _ -> raise (Destr_failure "Quant")

let destr_All e =
  match e.e_node with Quant(All,b,e) -> (b,e) | _ -> raise (Destr_failure "forall")

let destr_Exists e =
  match e.e_node with Quant(Exists,b,e) -> (b,e) | _ -> raise (Destr_failure "forall")

let destr_Tuple e =
  match e.e_node with Tuple(es) -> (es) | _ -> raise (Destr_failure "Tuple")

let destr_Proj e =
  match e.e_node with Proj(i,e) -> (i,e) | _ -> raise (Destr_failure "Proj")

let destr_Cnst e =
  match e.e_node with Cnst(c) -> (c) | _ -> raise (Destr_failure "Cnst")

let destr_FNat e =
  match e.e_node with
  | Cnst (FNat n) -> n
  | _ -> raise (Destr_failure "FNat")

let destr_App e =
  match e.e_node with App(o,es) -> (o,es) | _ -> raise (Destr_failure "App")

let destr_App_uop s o e =
  match e.e_node with
  | App(o',[e1]) when o = o' -> e1
  | _ -> raise (Destr_failure s)

let destr_App_bop s o e =
  match e.e_node with
  | App(o',[e1;e2]) when o = o' -> (e1,e2)
  | _ -> raise (Destr_failure s)

let destr_Nary s o e =
  match e.e_node with
  | Nary(o',es) when o = o' -> es
  | _ -> raise (Destr_failure s)

let destr_GMult e = destr_Nary "GMult"  GMult e

let destr_GExp e =
  match e.e_node with
  | App(GExp _,[e1;e2]) -> e1,e2
  | _ -> raise (Destr_failure "GExp")

let destr_RoCall e =
  match e.e_node with
  | App(RoCall ros,[e1]) -> ros,e1
  | _ -> raise (Destr_failure "GLog")

let destr_GLog e =
  match e.e_node with
  | App(GLog _,[e1]) -> e1
  | _ -> raise (Destr_failure "GLog")

let destr_EMap e =
  match e.e_node with
  | App(EMap es,[e1;e2]) -> es,e1,e2
  | _ -> raise (Destr_failure (fsprintf "EMap for %a" pp_expr e))

let destr_FOpp   e = destr_App_uop "FOpp"   FOpp e
let destr_FMinus e = destr_App_bop "FMinus" FMinus e
let destr_FInv   e = destr_App_uop "FInv"   FInv e
let destr_FDiv   e = destr_App_bop "FDiv"   FDiv e
let destr_FPlus  e = destr_Nary    "FPlus"  FPlus e
let destr_FMult  e = destr_Nary    "FMult"  FMult e

let destr_Eq   e = destr_App_bop "Eq"   Eq e
let destr_Not  e = destr_App_uop "Not"  Not e
let destr_Xor  e = destr_Nary    "Xor"  Xor e
let destr_Land e = destr_Nary    "Land" Land e
let destr_Lor  e = destr_Nary    "Lor"  Lor e

let is_InEq e = is_Not e && is_Eq (destr_Not e)

let destr_Ifte e =
  match e.e_node with
  | App(Ifte,[a;b;c]) -> (a,b,c)
  | _ -> raise (Destr_failure "Ifte")

let rec destr_Quant_nofail e = match e.e_node with
  | Quant(_,_,e) -> destr_Quant_nofail e
  | _ -> e

let destr_Xor_nofail e =
  match e.e_node with
  | Nary(Xor,es) -> es
  | _ -> [e]

let destr_Land_nofail e =
  match e.e_node with
  | Nary(Land,es) -> es
  | _ -> [e]

let destr_Lor_nofail e =
  match e.e_node with
  | Nary(Lor,es) -> es
  | _ -> [e]

let destr_Tuple_nofail e =
  match e.e_node with
  | Tuple(es) -> es
  | _ -> [e]

let destr_GExp_Gen gv g =
  let (g1,p) = try destr_GExp g with _ ->
    F.printf "destr_gexp %a@." pp_expr g;
    assert false
  in
  assert (equal_expr g1 (mk_GGen gv));
  p

(* ** Useful functions on [expr]
 * ----------------------------------------------------------------------- *)

let e_iter_ty_maximal ty g e0 =
  let rec go ie e0 =
    (* me = e is a maximal expression of the desired type *)
    let me = not ie && equal_ty e0.e_ty ty in
    (* ie = immediate subterms of e inside a larger expression of the desired type *)
    let ie = me || (ie && equal_ty e0.e_ty ty) in
    let run = if me then g else fun _ -> () in
    match e0.e_node with
    | V(_) | Cnst(_)  -> ()
    | Proj(_,e) | Quant(_,_,e)->
      go ie e; run e0
    | Tuple(es) | App(_,es) | Nary(_,es) ->
      L.iter (go ie) es;  run e0
  in
  go false e0

let e_vars = e_find_all is_V

(* let e_hash_calls = e_find_all is_H *)

let has_log e = e_exists (fun e -> is_GLog e) e

let is_ppt e = not (has_log e)

let typeError_to_string (ty1,ty2,e1,me2,s) =
  match me2 with
  | Some e2 ->
    fsprintf
      "incompatible types `%a' vs. `%a' for expressions `%a' and `%a' in %s"
      pp_ty ty1 pp_ty ty2 pp_expr e1 pp_expr e2 s
  | None when equal_ty ty1 ty2 ->
    fsprintf "type error in `%a' of type %a: %s" pp_expr e1 pp_ty ty1 s
  | None ->
    fsprintf
      "expected type `%a', got  `%a' for Expression `%a': %s"
      pp_ty ty2 pp_ty ty1 pp_expr e1 s

let catch_TypeError f =
  try f()
  with TypeError(ty1,ty2,e1,me2,s) ->
    print_string (typeError_to_string (ty1,ty2,e1,me2,s));
    raise (TypeError(ty1,ty2,e1,me2,s))

let se_of_list = L.fold_left (fun s e -> Se.add e s) Se.empty

let he_keys he = He.fold (fun k _ s -> Se.add k s) he Se.empty

let se_disjoint s1 s2 = Se.is_empty (Se.inter s1 s2)

let me_of_list es = L.fold_left (fun s (k,v) -> Me.add k v s) Me.empty es

let he_to_list he = He.fold (fun k v l -> (k,v)::l) he []

type ctxt = VarSym.t * expr

let ctxt_ty (v,e) = v.VarSym.ty, e.e_ty

let inst_ctxt (v, e') e = e_replace (mk_V v) e e'

let sub t =
  let rec aux e1 e2 =
    match e2.e_ty.ty_node with (* FIXME *) (* TODO : Permutations handling *)
    | Bool -> mk_Xor [e1;e2], mk_False
    | BS t -> mk_Xor [e1;e2], mk_Z t
    | G  id ->
      let g = mk_GGen id in
      mk_GExp g (mk_FMinus (mk_GLog e1) (mk_GLog e2)), mk_GExp g mk_FZ
    | Fq   -> mk_FMinus e1 e2, mk_FZ
    | Prod lt ->
      let es, zs =
        L.split
          (L.mapi (fun i _ -> aux (mk_Proj i e1) (mk_Proj i e2)) lt) in
      mk_Tuple es, mk_Tuple zs
    | Mat _ -> failwith "mat sub" (* TODO *)
    | List _ -> failwith "list sub"
    | Int | TySym _ -> assert false
  in
  let x1 = VarSym.mk "x" t in
  let x2 = VarSym.mk "x" t in
  let e, z = aux (mk_V x1) (mk_V x2) in
  (x1,(x2,e)), z

let mk_Zero t = snd (sub t)

let rec is_Zero e =
  match e.e_node with
  | Cnst (B false)       -> true
  | Cnst (FNat 0)        -> true
  | Cnst Z               -> true
  | Tuple es             -> L.for_all is_Zero es
  | App(GExp _, [e1;e2]) -> is_Zero e2 || is_Zero e1
  | Cnst (MatZero)       -> true
  | _                    -> false

type inverter = I of expr

let expr_of_inverter (I e) = e

let pp_inverter fmt i = pp_expr fmt (expr_of_inverter i)

let e_size e =
  let size = ref 0 in
  e_iter (fun _ -> incr size) e;
  !size
