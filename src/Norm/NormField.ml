(* * Compute normal form of field expressions *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open Expr
open ExprUtils
open Poly
open Factory

let mk_log level = mk_logger "Norm.NormField" level "NormField.ml"
let _log_t = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG
let log_i  = mk_log Bolt.Level.INFO

(** We use expressions as variables here. *)
module EP = MakePoly(
  struct
    type t = expr
    let pp fmt e = F.fprintf fmt "[%a]" pp_expr e
    let equal = equal_expr
    let compare = compare
  end) (IntRing)

(** Create Map, Set, and HashTable modules. *)
module Hep = Hashtbl.Make (struct
  type t = EP.t
  let equal = EP.equal
  let hash = Hashtbl.hash
end)

module Ht = Hashtbl

(* ** Convert expr into polynomials over expr
 * ----------------------------------------------------------------------- *)

(** Takes a term in normal form and returns the corresponding polynomial
    fails if given term is not in normal-form. *)
let polys_of_field_expr e =
  let to_bi = Big_int.big_int_of_int in
  let rec conv_fe0 e =
    if is_FPlus e
    then L.map conv_mon (destr_FPlus e)
    else [ conv_mon e ]
  and conv_mon e =
    if is_FOpp e
    then conv_mon0 (fun x -> - x) (destr_FOpp e)
    else conv_mon0 (fun x -> x) e
  and conv_mon0 minv e =
    let add_exponents es = L.map (fun e -> (e,1)) es in
    if is_FMult e then
      (match destr_FMult e with
       | _::_ as xs->
           let (ys,zs) = L.partition is_FNat xs in
           begin match ys with
           | [x] ->
               (match x.e_node with
                | Cnst(FNat n) -> (add_exponents zs, to_bi (minv n))
                | _ -> assert false)
           | [] -> (add_exponents xs, to_bi (minv 1))
           | _::_::_ -> assert false
           end
       | _ -> assert false)
    else
      (match e.e_node with
       | Cnst(FNat n) -> ([], to_bi (minv n))
       | _            -> (add_exponents [e], to_bi (minv 1)))
  in
  if is_FDiv e then
    let (e1,e2) = destr_FDiv e in
    (EP.from_terms (conv_fe0 e1), Some(EP.from_terms (conv_fe0 e2)))
  else (EP.from_terms (conv_fe0 e), None)

let ep_to_ip eps =
  let c = ref 1 in
  let he = He.create 17 in
  let lookup e =
    try He.find he e
    with Not_found ->
      let n = !c in
      incr c;
      He.add he e n;
      n
  in
  let conv_monom (e,i) = (lookup e,i) in
  let conv_poly p =
    L.map (fun (m,c) -> (L.map conv_monom m, c)) (EP.to_terms p)
  in
  let ps = L.map conv_poly eps in
  let hr = Ht.create 17 in
  He.iter (fun e i -> Ht.add hr i e) he;
  (L.map IP.from_terms ps, hr)

(* ** Factoring out polynomials
 * ----------------------------------------------------------------------- *)

let factor_out a (p : EP.t) =
  let xs, zs =
    lefts_rights
      (L.map
        (fun (es,c) ->
           match L.partition (fun (e,_) -> equal_expr e a) es with
           | ([(_,1)],others) -> Left(others,c)
           | ([],others)      -> Right(others,c)
           | _ ->
             log_i (lazy (fsprintf "cannot factor out %a\n%!" pp_expr a));
             raise Not_found)
        (EP.to_terms p))
  in
  (EP.from_terms xs, EP.from_terms zs)

(* ** Pure field expressions without other operators
 * ----------------------------------------------------------------------- *)

(** Field expression. *)
type fexp =
  | SV of int
  | SNat of int
  | SOpp of fexp
  | SInv of fexp
  | SPlus of fexp * fexp
  | SMult of fexp * fexp

let norm_fe fe =
  let is_neg c =
    Big_int.lt_big_int c Big_int.zero_big_int
  in
  let norm_gcd (n,d) =
    let (_,n,d) = gcd_div n d in
    (n,d)
  in
  let norm_sign (n,d) =
    if is_neg (IP.lc d) then (IP.opp n, IP.opp d) else (n,d)
  in
  let rec go fe =
    match fe with
    | SV(i)   -> (IP.var i, IP.one)
    | SNat(i) -> (IP.from_int i, IP.one)
    | SOpp(fe) ->
      let (n,d) = go fe in (IP.opp n,d)
    | SInv(fe) ->
      let (n,d) = go fe in (d,n)
    | SPlus(fe1,fe2) ->
      let (n1,d1) = go fe1 in
      let (n2,d2) = go fe2 in
      let (h,d1,d2)  = gcd_div d1 d2 in
      let d  = IP.(h *@ d1 *@ d2) in
      let n  = IP.(n1 *@ d2 +@ n2 *@ d1) in
      norm_gcd (n,d)
    | SMult(fe1,fe2) ->
      let (n1,d1) = go fe1 in
      let (n2,d2) = go fe2 in
      let (_,n1,d2) = gcd_div n1 d2 in
      let (_,n2,d1) = gcd_div n2 d1 in
      IP.(n1 *@ n2, d1 *@ d2)
  in
  norm_sign (go fe)

let exps_of_monom (m : (expr * int) list) =
  let go acc (x,k) = replicate_r acc k x in
  let l = L.fold_left go [] m in
  L.sort compare_expr l

let exp_of_polyl p =
  let to_i = Big_int.int_of_big_int in
  let summand (m,i) =
    let i = to_i i in
    match i, exps_of_monom m with
    | _,[]   -> if i < 0 then mk_FOpp (mk_FNat (-i)) else mk_FNat i
    | 1,mes  -> mk_FMult mes
    | -1,mes -> mk_FOpp (mk_FMult mes)
    | _,mes  ->
      assert (i <> 0 && i <> 1 && i <> -1);
      if i > 0 then mk_FMult (mk_FNat i    :: mes)
      else mk_FOpp (mk_FMult (mk_FNat (-i) :: mes))
  in
  let s = L.map summand p in
  let e = if s = [] then mk_FZ else mk_FPlus (L.sort compare_expr s) in
  e

let import_ipoly_aux (caller : string) poly (hv : (int, expr) Ht.t) =
  let ts = IP.to_terms poly in
  let inst i =
    try Ht.find hv i
    with Not_found ->
      failwith ("invalid variable "^(string_of_int i)^" returned by "^caller)
  in
  let conv_term (m,c) =
    (L.map (fun (v,e) -> (inst v,e)) m, c)
  in
  L.map conv_term ts

let import_ipoly (caller : string) poly (hv : (int, expr) Ht.t) =
  import_ipoly_aux caller poly hv |> exp_of_polyl

let import_ipoly_EP (caller : string) poly (hv : (int, expr) Ht.t) =
  import_ipoly_aux caller poly hv |> EP.from_terms

let exp_of_poly p = EP.to_terms p |> exp_of_polyl

(** Pretty-printer function for already abstracted field expression. *)
let _string_of_fexp e =
  let buf = Buffer.create 120 in
  let putc c = Buffer.add_char buf c in
  let puts s = Buffer.add_string buf s in
  let puti i = Buffer.add_string buf (string_of_int i) in
  let rec aux e =
    match e with
    | SV i       -> puts "x";  puti i
    | SNat(n)    -> puti n
    | SOpp(a)    -> puts "-("; aux a; putc ')'
    | SInv(a)    -> puts "1/("; aux a; putc ')'
    | SPlus(a,b) -> putc '('; aux a; puts " + "; aux b; putc ')'
    | SMult(a,b) -> putc '('; aux a; puts " * "; aux b; putc ')'
  in
  aux e; Buffer.contents buf

(** Abstraction of [Expr.expr] to [sfexp]. *)
let rec rename hr = function
  | SV i -> SV (Ht.find hr i)
  | (SNat _) as e -> e
  | SOpp e -> SOpp (rename hr e)
  | SInv e -> SInv (rename hr e)
  | SPlus(e1,e2) -> SPlus (rename hr e1, rename hr e2)
  | SMult(e1,e2) -> SMult (rename hr e1, rename hr e2)

(** [abstract_non_field_multiple before es] abstracts all
    expressions in [es] at once sharing variables for
    common non-field subexpression. It also applies the
    [before] function to expressions beforehand. *)
let abstract_non_field_multiple before es =
  let c = ref 1 in
  let he = He.create 17 in
  let lookup e =
    try He.find he e
    with Not_found ->
      let n = !c in
      incr c;
      He.add he e n;
      n
  in
  let rec go e =
    let e = before e in
    match e.e_node with
    | Cnst (FNat n)       -> SNat n
    | App (FOpp,[a])      -> SOpp(go a)
    | App (FInv,[a])      -> SInv(go a)
    | App (FMinus,[a;b])  -> SPlus(go a, SOpp (go b))
    | App (FDiv,[a;b])    -> SMult(go a, SInv (go b))
    | Nary (FPlus, a::es) ->
      List.fold_left (fun acc e -> SPlus(acc, go e)) (go a) es
    | Nary (FMult, a::es) ->
      List.fold_left (fun acc e -> SMult(acc, go e)) (go a) es
    | _ -> SV (lookup e)
  in
  let ses = List.map go es in
  let binding = List.sort compare_expr (He.fold (fun e _ l -> e::l) he []) in
  let hr = Ht.create 17 in
  let hv = Ht.create 17 in
  let c = ref 1 in
  List.iter (fun e -> let i = !c in incr c;
                      Ht.add hr (He.find he e) i;
                      Ht.add hv i e) binding;
  (List.map (rename hr) ses, !c, hv)

(** See [abstract_non_field] *)
let abstract_non_field before e =
  match abstract_non_field_multiple before [e] with
  | ([e],c,hv) -> (e,c,hv)
  | _ -> assert false

let div pe1 pe2 =
  match ep_to_ip [pe1; pe2] with
  | [p1;p2], hr ->
    let p3 = Factory.div p1 p2 in
    import_ipoly "div" p3 hr
  | _ -> assert false

let div_factor pe1 pe2 =
  match ep_to_ip [pe1; pe2] with
  | [p1;p2], hr ->
    let p3 = Factory.div p1 p2 in
    let facs = Factory.factor p3 in
    let es = L.map (fun (p,exp) -> (import_ipoly "div" p hr,exp)) facs in
    begin match es with
    | [] -> mk_FNat 0
    | [(a,1)] -> a
    | _ ->
      let is_minus_one (e,exp) = equal_expr (mk_FOpp mk_FOne) e && exp = 1 in
      let mopp =
        if L.exists is_minus_one es then (fun x -> mk_FOpp x) else id
      in
      let es = L.filter (fun x -> not (is_minus_one x)) es in
      mopp (mk_FMult (conc_map (fun (e,exp) -> replicate exp e) es))
    end
  | _ -> assert false

let div_factors pe1 pe2 =
  match ep_to_ip [pe1; pe2] with
  | [p1; p2], hr  ->
    let p3 = Factory.div p1 p2 in
    if (IP.equal p3 IP.zero)
    then None
    else (
      let facs = Factory.factor p3 in
      Some (L.map (fun (p,_exp) -> (import_ipoly "div" p hr)) facs)
    )
  | _ ->
    None

let reduce pe1 pe2 =
  match ep_to_ip [pe1; pe2] with
  | [p1;p2], hr ->
    let p3 = Factory.reduce p1 p2 in
    import_ipoly "reduce" p3 hr
  | _ -> assert false

let div_reduce pe1 pe2 =
  match ep_to_ip [pe1; pe2] with
  | [p1;p2], hr ->
    let p3 = Factory.div p1 p2 in
    let p4 = Factory.reduce p1 p2 in
    (import_ipoly "div" p3 hr,import_ipoly "reduce" p4 hr)
  | _ -> assert false

let div_EP pe1 pe2 =
  match ep_to_ip [pe1; pe2] with
  | [p1;p2], hr ->
    let p3 = Factory.div p1 p2 in
    import_ipoly_EP "div" p3 hr
  | _ -> assert false
