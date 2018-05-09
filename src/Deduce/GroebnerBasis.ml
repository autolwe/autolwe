(* Grobner basis computations for K[X]-module *)

(* Imports and abbreviations *)

    
open List;;
open Num;;
open NormField;;
open Util;;
open ExprUtils;;
open Expr;;
open Type;;

let log_i _ls  = ()

(* ------------------------------------------------------------------------- *)
(*  Utility functions                                                        *)
(* ------------------------------------------------------------------------- *)
  
let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec lexord ord l1 l2 =
  match (l1,l2) with
    (h1::t1,h2::t2) -> if ord h1 h2 then length t1 = length t2
                       else h1 = h2 && lexord ord t1 t2
  | _ -> false;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;


let rec distinctpairs l =
  match l with
   x::t -> itlist (fun y a -> (x,y) :: a) t (distinctpairs t)
  | [] -> [];;


let gexp e h =
  if is_FOne h then e
  else if is_FZ h then mk_GExp (mk_GGen (destr_G_exn e.e_ty)) h
  else mk_GExp e h;;

let gmult e1 e2 =
  if is_GOne e1 then e2
  else if is_GOne e2 then e1
  else mk_GMult [e1; e2]  ;;

(* ------------------------------------------------------------------------- *)
(* Defining polynomial types                                                 *)
(* ------------------------------------------------------------------------- *)

type mon = Num.num * int list;;

type pol = mon list;;

type pol_i = mon list * Expr.expr;;

type i_var_set = int list;;
  
(* ------------------------------------------------------------------------- *)
(* Conversions functions                                                     *)
(* ------------------------------------------------------------------------- *)

let poly_to_ipoly vars (p:pol) : Poly.ipoly =
  Poly.IP.from_terms @@ map (fun (c,m) -> ((map2 (fun pow t-> (t,pow)) m vars, ((big_int_of_num c)))) ) p;;
                                         
let polys_to_eps polys vars mp =
  let polys,invs = List.split polys in
  let ipolys = map (poly_to_ipoly vars) polys in
      combine (map (fun p -> import_ipoly "Groebner converter" p mp) ipolys) invs;;

  
(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let mmul ((c1,m1):mon) ((c2,m2):mon) :mon  = (c1*/c2,map2 (+) m1 m2);;

let mdiv (pvars:i_var_set)=
  let index_sub n1 n2 = if n1 < n2 then failwith "mdiv" else n1-n2 in
  fun ((c1,m1):mon) ((c2,m2):mon) -> let pows = map2 index_sub m1 m2 in
                                     let checker = List.combine pows pvars in
                         if (List.fold_left (fun  a (x,y) -> (y=1 && x>0)|| a ) false checker) then failwith "mdiv" else
                         ((c1//c2,pows):mon);;

let mlcm ((_,m1):mon) ((_,m2):mon) :mon= (Num.Int 1,map2 max m1 m2);;
  
let expr_of_monom vars mp k_Fq (m:mon)=
  let expr =  (fst (hd (polys_to_eps [([m],mk_FNat 0)] vars mp)))
              |> Expr.e_subst (me_of_list  (k_Fq)) in
    expr;;
  
(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
  let n1 = itlist (+) m1 0 and n2 = itlist (+) m2 0 in
  n1 < n2 || n1 = n2 &&  lexord(>) m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)

let mpoly_mmul vars mp k_fQ cm ((pol,inv):pol_i) :pol_i= (map (mmul cm) pol, gexp inv (expr_of_monom vars mp k_fQ cm));;

let mpoly_neg ((pol,inv):pol_i) :pol_i= map (fun (c,m) -> (minus_num c,m)) pol , gexp inv (mk_FOpp (mk_FNat (1)));;

let mpoly_const (vars) c :pol=
  if c =/ Num.Int 0 then [] else [c,map (fun _ -> 0) vars];;

let rec mpoly_add_aux (l1:pol) (l2:pol):pol =
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | ((c1,m1)::o1,(c2,m2)::o2) ->
        if m1 = m2 then
          let c = c1+/c2 and rest = mpoly_add_aux o1 o2 in
          if c = Num.Int 0 then rest else (c,m1)::rest
        else if morder_lt m2 m1 then (c1,m1)::(mpoly_add_aux o1 l2)
        else (c2,m2)::(mpoly_add_aux l1 o2);;

let mpoly_add ((l1,i1):pol_i) ((l2,i2):pol_i):pol_i =
  (mpoly_add_aux l1 l2, gmult i1 i2);;

let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;

let ipoly_to_poly vars (p:Poly.ipoly) : pol =
  let pol = Poly.IP.to_terms p in
  fold_right (fun (m,c) acc -> mpoly_add_aux [(num_of_big_int c, map (fun i  -> try assoc (i) m
                                                        with Not_found -> 0
                                            ) vars  )] acc ) pol (mpoly_const vars (Num.Int 0));;

let eps_to_polys (eps:(NormField.EP.t * Expr.expr) list )=
  let exprs,invs = List.split eps in                         
  let ipolys, mp = ep_to_ip exprs in
  let vars = Hashtbl.fold (fun i _ acc -> i::acc) mp [] in
  (combine (map (ipoly_to_poly vars) ipolys) invs),vars,mp;;

(* ------------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.       *)
(* ------------------------------------------------------------------------- *)

let reduce1 vars mp k_fQ cm ((pol,i),pvars) =
  match pol with
    [] -> failwith "reduce1"
  | hm::cms -> let c,m = mdiv pvars cm hm in mpoly_mmul vars mp k_fQ (minus_num c,m) (cms,i);;

(* ------------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                  *)
(* ------------------------------------------------------------------------- *)

let reduceb vars mp k_fQ cm pols = let res = tryfind (reduce1 vars mp k_fQ cm) pols in
                                              res;;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).     *)
(* ------------------------------------------------------------------------- *)

let rec reduce vars mp k_fQ pols (pol,i) :pol_i=
  match pol with
    [] -> ([],i)
  | cm::ptl -> try reduce vars mp k_fQ pols (mpoly_add (reduceb  vars mp k_fQ cm pols) (ptl,i))
               with Failure _ -> let pol,inv = (reduce  vars mp k_fQ pols (ptl,i)) in
                                 cm::pol,inv;;

(* ------------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                  *)
(* ------------------------------------------------------------------------- *)

let spoly vars mp k_fQ  ((pol1,i1),pvar1) ((pol2,i2),pvar2) :pol_i=
  let gt = destr_G_exn i1.e_ty in
  match (pol1,pol2) with
    ([],_) -> ([],gexp (mk_GGen gt) (mk_FNat 0))
  | (_,[]) -> ([],gexp (mk_GGen gt) (mk_FNat 0))
  | (m1::ptl1,m2::ptl2) ->
     let m = mlcm m1 m2 in
        let res = mpoly_sub (mpoly_mmul vars mp k_fQ  (mdiv pvar1 m m1) (ptl1,i1))
                            (mpoly_mmul vars mp k_fQ  (mdiv pvar2 m m2) (ptl2,i2)) in
        res;;

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm for free multi-module                             *)
(* ------------------------------------------------------------------------- *)
  
  
let rec grobner vars mp k_fQ basis pairs =
  match pairs with
    [] -> basis
  | (p1,p2)::opairs ->
        try
          let sp = reduce vars mp k_fQ basis (spoly vars mp k_fQ p1 p2) in
          if fst sp = [] then grobner vars mp k_fQ basis opairs                              
          else 
            let sp_pvars = map2 (fun x y -> x +y - x*y) (snd p1) (snd p2) in
            let newcps = map (fun p -> p,(sp,sp_pvars)) basis in
              grobner vars mp k_fQ ((sp,sp_pvars)::basis) (opairs @ newcps)    
        with Failure _ -> grobner vars mp k_fQ basis opairs;;
  
(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let groebner vars mp k_fQ basis = grobner vars mp k_fQ basis (distinctpairs basis);;

let get_inverter vars mp k_fQ basis pol =
  let red,inverter =  reduce vars mp k_fQ basis pol in
                       (red= [],inverter);;
