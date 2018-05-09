(* * Use Factory to perform computations on polynomials *)

(* ** Imports and abbreviations *)
open Util
open Expr
open NormField
open Poly

module Ht = Hashtbl

let mk_log level = mk_logger "CAS.CAS" level "CAS.ml"
let log_i = mk_log Bolt.Level.INFO

(* ** Using CAS to perform polynomial computations
 * ----------------------------------------------------------------------- *)

let cache_norm_factory = Ht.create 17

let norm_factory se hv =
  let convert_polys (p1,p2) =
    let num   = import_ipoly "norm_factory" p1 hv in
    let denom = import_ipoly "norm_factory" p2 hv in
    if equal_expr denom mk_FOne then num
    else mk_FDiv num denom
  in
  try
    convert_polys (Ht.find cache_norm_factory se)
  with
    Not_found ->
      let (p1,p2) = norm_fe se in
      Ht.add cache_norm_factory se (p1,p2);
      convert_polys (p1,p2)

let ht_mod_reduce_factory = Ht.create 17

let mod_reduce a b =
  let (sa,sb,_Xc) =
    match abstract_non_field_multiple (fun x -> x) [a;b] with
    | ([sa; sb],c,_) -> (sa,sb,c)
    | _ -> assert false
  in
  try
    Ht.find ht_mod_reduce_factory (sa,sb)
  with
    Not_found -> 
      let (sa_n,sa_d) = norm_fe sa in
      let (sb_n,sb_d) = norm_fe sb in
      assert (IP.equal sa_d IP.one && IP.equal sb_d IP.one);
      let res = Factory.reduce_zero sa_n sb_n in
      Ht.add ht_mod_reduce_factory (sa,sb) res;
      res

let ht_check_nz = Ht.create 17

let rec check_nz_ipoly ~is_nz:a b0 =
  let open Util in
  let (h,_,b) = Factory.gcd_div a b0 in
  log_i (lazy (fsprintf "a=%a b0=%a h=%a b=%a" IP.pp a IP.pp b0 IP.pp h IP.pp b));
  if IP.equal IP.one h
  then false
  else if IP.equal IP.one b || IP.equal (IP.from_int (-1)) b then true
  else check_nz_ipoly ~is_nz:a b

let check_nz ~is_nz:a b =
  let (sa,sb,_Xc) =
    match abstract_non_field_multiple (fun x -> x) [a; b] with
    | ([sa; sb],c,_) -> (sa,sb,c)
    | _ -> assert false
  in
  try
    Ht.find ht_check_nz (sa,sb)
  with
    Not_found -> 
      let (sa_n,sa_d) = norm_fe sa in
      let (sb_n,sb_d) = norm_fe sb in
      assert (IP.equal sa_d IP.one && IP.equal sb_d IP.one);
      let res = check_nz_ipoly ~is_nz:sa_n sb_n in
      Ht.add ht_check_nz (sa,sb) res;
      res

(* ** Computing the normal form and reducing modulo a polynomial
 * ----------------------------------------------------------------------- *)

let norm before e =
  let (se,_c,hv) = abstract_non_field before e in
  (* handle some simple special cases without expensive computations *)
  match se with
  (*
  | SV i                  -> Ht.find hv i
  | SNat n                -> mk_FNat n
  | SOpp(SNat n)          -> mk_FOpp (mk_FNat n)
  | SOpp(SV i)            -> mk_FOpp (Ht.find hv i)
  | SMult(SNat 1, SV i)
  | SMult(SV i, SNat 1)   -> Ht.find hv i
  | SMult(SNat i, SNat j) -> mk_FNat (i * j)
  | SMult(SV i, SV j)     -> mk_FMult (List.sort compare_expr [Ht.find hv i; Ht.find hv j])
   *)
  | _                     -> norm_factory se hv
