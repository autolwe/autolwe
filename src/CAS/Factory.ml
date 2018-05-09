(* * Bindings to factory C++ library for polynomial arithmetic (used in Singular) *)

(* ** Imports and abbreviations *)
open Util
open Ctypes
open Foreign
open Poly
open Abbrevs

let mk_log level = mk_logger "CAS.Factory" level "Factory.ml"
let _log_i = mk_log Bolt.Level.INFO

module US = Unsigned.Size_t
module UL = Unsigned.ULong
module L  = List

(* ** Type definitions
 * ------------------------------------------------------------------------ *)

let cexpvecs = ptr (ptr long)
let ccoeffs  = ptr long

type distr_poly
let distr_poly : distr_poly structure typ = structure "DistrPoly"
let dp_maxvar  = field distr_poly "maxvar" int
let dp_nterms  = field distr_poly "nterms" int
let dp_expvecs = field distr_poly "expvecs" cexpvecs
let dp_coeffs  = field distr_poly "coeffs" ccoeffs
let () = seal distr_poly

type dpoly_list
let dpoly_list : dpoly_list structure typ = structure "DPolyList"
let dpl_head     = field dpoly_list "head" (ptr distr_poly)
let dpl_head_aux = field dpoly_list "head_aux" int
let dpl_tail     = field dpoly_list "tail" (ptr_opt dpoly_list)
let () = seal dpoly_list


(* ** Function bindings
 * ------------------------------------------------------------------------ *)

let c_print_cpoly =
  foreign "wrap_print" (int @-> int @-> cexpvecs @-> ccoeffs @-> returning void)

let c_new_expvecs =
  foreign "wrap_new_expvecs" (int @-> int @-> returning cexpvecs)

let c_free_expvecs =
  foreign "wrap_free_expvecs" (cexpvecs @-> int @-> returning void)

let c_free_dpoly_list =
  foreign "free_DPolyList" (ptr dpoly_list @-> returning void)

let c_new_coeffs = foreign "wrap_new_coeffs" (int @-> returning ccoeffs)

let c_free_coeffs = foreign "wrap_free_coeffs" (ccoeffs @-> returning void)

let c_gcd = foreign "wrap_gcd"
  (int @-> int @-> cexpvecs @-> ccoeffs @->
   int @-> int @-> cexpvecs @-> ccoeffs @->
   returning distr_poly)

let c_reduce = foreign "wrap_reduce"
  (int @-> int @-> cexpvecs @-> ccoeffs @->
   int @-> int @-> cexpvecs @-> ccoeffs @->
   returning distr_poly)

let c_reduce_zero = foreign "wrap_reduce_zero"
  (int @-> int @-> cexpvecs @-> ccoeffs @->
   int @-> int @-> cexpvecs @-> ccoeffs @->
   returning int)

let c_div = foreign "wrap_div"
  (int @-> int @-> cexpvecs @-> ccoeffs @->
   int @-> int @-> cexpvecs @-> ccoeffs @->
   returning distr_poly)

let c_gcd_div = foreign "wrap_gcd_div"
  (int @-> int @-> cexpvecs @-> ccoeffs @->
   int @-> int @-> cexpvecs @-> ccoeffs @->
   returning (ptr dpoly_list))

let c_factor = foreign "wrap_factor"
  (int @-> int @-> cexpvecs @-> ccoeffs @->
   returning (ptr dpoly_list))

(* ** Conversions
 * ------------------------------------------------------------------------ *)

let _print_cpoly (maxvar,nterms,cexpvecs,ccoeffs) =
  c_print_cpoly maxvar nterms cexpvecs ccoeffs

(** The order of coefficients / exponent vectors does not matter,
    but has to be consistent in both.
    The order in the exponent vector e is
    e[0]: exponent of $v_1$
    ... 
*)
let ipoly_to_cpoly ip =
  if IP.equal ip IP.zero then
    (0,0,from_voidp (ptr long) null, from_voidp long null)
  else (
    let maxvar =
      match L.sort (fun a b -> - (compare a b)) (IP.vars ip) with
      | []   -> 1 (* we treat this case like 1 variable *)
      | x::_ ->
        if x < 1 then
          failwith (F.sprintf "only variables >= 1 supported, got %i" x)
        else
          x
    in
    let terms = IP.to_terms ip in
    let nterms = L.length terms in
    let ccoeffs = c_new_coeffs nterms in
    let cexpvecs = c_new_expvecs maxvar nterms in
    L.iteri (fun i (evec,coeff) ->
      let v = Big_int.int64_of_big_int coeff in (* should raise Failure on overflow *)
      ccoeffs +@ i <-@ Signed.Long.of_int64 v;  (* FIXME: are these types always convertible? *)
      let cexpvec = !@ (cexpvecs +@ i) in
      for j = 0 to maxvar - 1 do
        let e = try L.assoc (j+1) evec with Not_found -> 0 in
        cexpvec +@ j <-@ Signed.Long.of_int e
      done)
      terms;
    (maxvar, nterms, cexpvecs, ccoeffs)
  )

let cpoly_to_ipoly (maxvar, nterms, cexpvecs, ccoeffs) =
  if nterms = 0 then IP.zero
  else (
    assert (maxvar > 0);
    let res = ref [] in
    for i = 0 to nterms - 1 do
      let c = !@ (ccoeffs +@ i) in
      let cexpvec = !@ (cexpvecs +@ i) in
      let vs = ref [] in
      for j = 0 to maxvar - 1 do
        let e = !@ (cexpvec +@ j) in
        vs := (j+1,Signed.Long.to_int e)::!vs;
      done;
      let e = Signed.Long.to_int64 c in (* FIXME: are these types always convertible? *)
      res := (!vs,Big_int.big_int_of_int64 e)::!res;
    done;
    IP.from_terms !res
  )

let free_cpoly (_maxvar, nt, cevs, cos) =
  if nt > 0 then (
    c_free_coeffs cos;
    c_free_expvecs cevs nt
  )

let wrap c_f verbose p1 p2 =
  if verbose then F.printf "p1 = %a, p2 = %a\n%!" IP.pp p1 IP.pp p2;
  let (maxvar1, nt1, cevs1, cos1) = ipoly_to_cpoly p1 in
  let (maxvar2, nt2, cevs2, cos2) = ipoly_to_cpoly p2 in
  let res = c_f maxvar1 nt1 cevs1 cos1 maxvar2 nt2 cevs2 cos2 in
  let maxvar_res = getf res dp_maxvar in
  let nt_res = getf res dp_nterms in
  let cevs_res = getf res dp_expvecs in
  let cos_res = getf res dp_coeffs in
  let pres = cpoly_to_ipoly (maxvar_res,nt_res,cevs_res,cos_res) in
  free_cpoly (maxvar_res, nt_res, cevs_res, cos_res);
  free_cpoly (maxvar1, nt1, cevs1, cos1);
  free_cpoly (maxvar2, nt2, cevs2, cos2);
  pres

let gcd p1 p2 =
  if IP.equal IP.one p1 || IP.equal IP.one p2 then IP.one else wrap c_gcd false p1 p2

let reduce = wrap c_reduce false

let div p1 p2 =
  if IP.equal p2 IP.one then p1 else wrap c_div false p1 p2

let reduce_zero p1 p2 =
  let (maxvar1, nt1, cevs1, cos1) = ipoly_to_cpoly p1 in
  let (maxvar2, nt2, cevs2, cos2) = ipoly_to_cpoly p2 in
  let res = c_reduce_zero maxvar1 nt1 cevs1 cos1 maxvar2 nt2 cevs2 cos2 in
  free_cpoly (maxvar1, nt1, cevs1, cos1);
  free_cpoly (maxvar2, nt2, cevs2, cos2);
  log_ig (lazy (fsprintf "reduce %a %a %i" IP.pp p1 IP.pp p2 res));
  (res = 1)

let gcd_div p1 p2 =
  if IP.equal IP.one p1 || IP.equal IP.one p2 then (IP.one,p1,p2) else
  let get_item li =
    let head = !@ (getf li dpl_head) in
    let tail = match getf li dpl_tail with None -> None | Some p -> Some (!@ p) in
    let maxvar = getf head dp_maxvar in
    let nt     = getf head dp_nterms in
    let cevs   = getf head dp_expvecs in
    let cos    = getf head dp_coeffs in
    (tail,cpoly_to_ipoly (maxvar,nt,cevs,cos))
  in
  let (maxvar1, nt1, cevs1, cos1) = ipoly_to_cpoly p1 in
  let (maxvar2, nt2, cevs2, cos2) = ipoly_to_cpoly p2 in
  let res = c_gcd_div maxvar1 nt1 cevs1 cos1 maxvar2 nt2 cevs2 cos2 in
  let (oli,h) = get_item (!@ res) in
  match oli with
  | None -> assert false
  | Some li ->
    let (oli,p1) = get_item li in
    begin match oli with
    | None -> assert false
    | Some li ->
      let (oli,p2) = get_item li in
      assert (oli = None);
      c_free_dpoly_list res;
      free_cpoly (maxvar1, nt1, cevs1, cos1);
      free_cpoly (maxvar2, nt2, cevs2, cos2);
      (h,p1,p2)
    end

let factor p =
  let rec get_factors li =
    let head = !@ (getf li dpl_head) in
    let exp = getf li dpl_head_aux in
    let tail = getf li dpl_tail in
    let maxvar = getf head dp_maxvar in
    let nt     = getf head dp_nterms in
    let cevs   = getf head dp_expvecs in
    let cos    = getf head dp_coeffs in
    let others =
      match tail with
      | None   -> []
      | Some p -> get_factors (!@ p)
    in
    (cpoly_to_ipoly (maxvar,nt,cevs,cos), exp)::others
  in
  let (maxvar, nt, cevs, cos) = ipoly_to_cpoly p in
  let res = c_factor maxvar nt cevs cos in
  let facs = get_factors (!@ res) in
  c_free_dpoly_list res;
  free_cpoly (maxvar, nt, cevs, cos);
  if L.length facs > 0 then
    L.filter (fun (f,_) -> not (IP.equal f IP.one)) facs
  else
    facs

(* ** Testing
 * ------------------------------------------------------------------------ *)

let test_gcd_1 () =
  let open IP in
  let v1 = var 1 in
  let v2 = var 2 in
  let v3 = var 3 in
  let p1 = (v1 *@ v1 -@ (from_int 4)) *@ (v3 +@ one) in
  let p2 = (v1  +@ (from_int 2)) *@ v2 in
  let p3 = gcd p1 p2 in
  assert (equal p3 (v1 +@ (from_int 2)))

let test_gcd_div_1 () =
  let open IP in
  let v1 = var 1 in
  let v2 = var 2 in
  let v3 = var 3 in
  let p1 = (v1 *@ v1 -@ (from_int 4)) *@ (v3 +@ one) in
  let p2 = (v1  +@ (from_int 2)) *@ v2 in
  let p3 = gcd p1 p2 in
  let (p3',p4,p5) = gcd_div p1 p2 in
  assert (equal p3 p3' && equal (div p1 p3) p4 && equal (div p2 p3) p5)

let test_gcd_2 () =
  let open IP in
  let p1 = (from_int 4) in
  let p2 = (from_int 6) in
  let p3 = gcd p1 p2 in
  assert (equal p3 (from_int 2))

let test_conversion () =
  let open IP in
  let v1 = var 1 in
  let v2 = var 2 in
  let v3 = var 3 in
  let p1 = v1 *@ v2 -@ (from_int 4) in
  let p2 = v3 +@ (from_int 7) in
  let p3 = v3 *@ v2 *@ v1 +@ (from_int 99) in
  let p4 = p1 *@ p1 +@ p3 in
  let p5 = IP.from_int 0 in
  let p6 = from_int 1 in
  let cp1 = ipoly_to_cpoly p1 in
  let cp2 = ipoly_to_cpoly p2 in
  let cp3 = ipoly_to_cpoly p3 in
  let cp4 = ipoly_to_cpoly p4 in
  let cp5 = ipoly_to_cpoly p5 in
  let cp6 = ipoly_to_cpoly p6 in
  let p1' = cpoly_to_ipoly cp1 in
  let p2' = cpoly_to_ipoly cp2 in
  let p3' = cpoly_to_ipoly cp3 in
  let p4' = cpoly_to_ipoly cp4 in
  let p5' = cpoly_to_ipoly cp5 in
  let p6' = cpoly_to_ipoly cp6 in
  assert (equal p1' p1 && equal p2' p2 && equal p3' p3 &&
          equal p4' p4 && equal p5' p5 && equal p6' p6)

let test_reduce_div () =
  let open IP in
  let v1 = var 1 in
  let v2 = var 2 in
  let v3 = var 3 in
  let u = v1 *@ v2 -@ (from_int 4) in
  let v = v3 +@ (from_int 7) in
  let q = v3 *@ v2 *@ v1 +@ (from_int 99) in
  let w = u *@ v +@ q in
  let r = reduce w u in
  let d = div w u in
  let w' = d *@ u +@ r in
  assert (equal w' w)

let test_factor () =
  let open IP in
  let v1 = var 1 in
  let v2 = var 2 in
  let v3 = var 3 in
  let u = v1 *@ v2 -@ (from_int 4) in
  let v = v3 +@ (from_int 7) in
  let q = v3 *@ v2 *@ v1 +@ (from_int 99) in
  let w = u *@ v *@ q in
  let ps = factor w in
  let res = L.fold_right (fun (f,e) g -> ring_exp f e *@ g) ps one in
  assert (equal res w)

let _test () =
  test_conversion ();
  test_gcd_1 ();
  test_gcd_2 ();
  test_gcd_div_1 ();
  test_reduce_div ();
  test_factor ()
