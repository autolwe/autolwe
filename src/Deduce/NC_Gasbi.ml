(* Grobner basis computations for K[X]-module *)
#use "topfind";;
#require "num";;
 (* Imports and abbreviations *)

    
open List;;
open Num;;

(*
open NormField;;
open Util;;
open ExprUtils;;
open Expr;;
open Type;;

let log_i _ls  = ()
*)
(* ------------------------------------------------------------------------- *)
(*  Utility functions                                                        *)
(* ------------------------------------------------------------------------- *)
  
let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec lexord_lt ord l1 l2 =
  match (l1,l2) with
    ([],[]) -> false
   |([],_) -> true
   |(_,[]) -> false
   | (h1::t1,h2::t2) -> if ord h1 h2 then true
                       else h1 = h2 && lexord_lt ord t1 t2;;
let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;


let rec distinctpairs l =
  match l with
   x::t -> itlist (fun y a -> (x,y) :: a) t (distinctpairs t)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* Defining polynomial types                                                 *)
(* ------------------------------------------------------------------------- *)

type id_var = int;;

type id_size = int;;

type vars = id_var list;;

type mon =
  { coeff : Num.num;
    vars : vars;
    length : int;
    size : id_size * id_size;
  };;

type pol = mon list;;

(* type pol_i = mon list * Expr.expr; *)

type i_var_set = int list;;

let mk_vmon (i:id_var) (size: id_size*id_size) :mon=
  {coeff = Num.Int 1; vars = [i]; length = 1; size};;

let is_null_mon (m:mon) =
   m.length=0 || (List.for_all (fun var -> var<0) m.vars)

let is_null (p:pol) : bool =
  match p with
  |[]-> true
  |m::_ -> is_null_mon m

let get_hd (p:pol) =
  if is_null p then
    None
  else
    Some (List.hd p)

let rec equals (p1:pol) (p2:pol) =
  match (get_hd p1,get_hd p2) with
       |None,None -> true
       |None, _ -> false
       |_,None -> false
       |Some m1,Some m2 -> m1=m2 && equals (List.tl p1) (List.tl p2)

let rec remainder (p:pol) =
  match p with
  |[] -> []
  |m::q -> if is_null_mon m then
             p
           else
             remainder q

let null_mon =
   { coeff = Int 0;
    vars = [];
    length = 0;
    size = (1,1);
  };;
(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let veq_mon (m1:mon) (m2:mon) =
  (m1.length = m2.length ) && m1.vars=m2.vars;;

let mmul (m1:mon) (m2:mon) :mon  =
  if snd(m1.size) = fst(m2.size) then
  { coeff = m1.coeff*/m2.coeff;
    vars = m1.vars@m2.vars;
    length = m1.length + m2.length;
    size = (fst(m1.size),snd(m2.size));
  }
 else if m2.size=(-1,-1) then
   null_mon 
 else if m1.size=(-1,-1) then
   null_mon 
 else
   failwith "Monoms sizes uncompatible";;

exception NotPrefix;;

let rec is_prefix (m1:id_var list) (m2:id_var list) =
  match (m1,m2) with
     ([],[])-> ([],[])
    |([],m)-> ([],m)
    |(m,[]) -> (m,[])
    |(p1::q1,p2::q2) -> if p1 = p2 then 
                            is_prefix q1 q2
                        else
                           raise NotPrefix;;


(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
   m1.length < m2.length || (m1.length = m2.length &&  lexord_lt(<) m1.vars m2.vars);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)

let mpoly_cmul c (pol:pol) :pol =
  if c = Int 0 then []
  else map (fun m -> {m with coeff=c*/m.coeff}) pol;;

let mpoly_mmul cm (pol:pol) :pol = map (mmul cm) pol;;

let mpoly_neg (pol) :pol = map (fun m -> {m with coeff=minus_num m.coeff}) pol ;;

let rec remove_null_mon (p:pol) =
  match p with
  |[] -> []
  |m::q -> if m.coeff = Int 0 then
             remove_null_mon q
           else
             m::(remove_null_mon q);;

let rec mpoly_add (l1:pol) (l2:pol):pol =
  match (l1,l2) with
    ([],_) -> remove_null_mon l2
  | (_,[]) -> remove_null_mon l1
  | (m1::o1,m2::o2) ->
        if veq_mon m1 m2 then
          let c = m1.coeff+/m2.coeff and rest = mpoly_add o1 o2 in
          if c = Num.Int 0 then rest
          else {m1 with coeff=c}::rest
        else if morder_lt m2 m1 then m1::(mpoly_add o1 l2)
        else m2::(mpoly_add l1 o2);;


let mpoly_mul l1 l2 =
  let rec aux_mul l1 l2 =
    match (l1,l2) with
      (_,[]) -> []
     |([],_)-> []
     |(p::q,l2) ->mpoly_add (mpoly_mmul p l2) (aux_mul q l2) in
  match (is_null l1, is_null l2) with
          |(false,false) ->  aux_mul l1 l2
          |_,_ -> [];;


let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;

let polys_mul (l:pol list) =
  match l with
  |[] -> []
  |p::pols ->
    List.fold_right (fun pol acc -> mpoly_mul pol acc) pols p;;

let mpoly_muls ps = 
  match ps with
  | []      -> []
  | p :: ps -> 
     List.fold_left (fun p acc -> mpoly_mul p acc ) p ps;;


mpoly_muls  [[{coeff = Int 1; vars = [1]; length = 1; size = (2, 2)};
    {coeff = Int (-1); vars = [-1]; length = 0; size = (-1, -1)};
    {coeff = Int 1; vars = [-2]; length = 0; size = (-1, -1)}];
   [{coeff = Int 1; vars = [1]; length = 1; size = (2, 2)};
    {coeff = Int (-1); vars = [-1]; length = 0; size = (-1, -1)};
    {coeff = Int 1; vars = [-2]; length = 0; size = (-1, -1)}]];;

let s_poly (p1:pol) (p2:pol) =
  match (p1,p2) with
  |_,[] -> p1
  |[],_ -> p2
  |m1::_,m2::_-> match (m1.coeff,m2.coeff) with
                    |Int 0,_ -> p2
                    |_, Int 0 -> p1
                    |c1,c2 -> mpoly_sub p1 (mpoly_cmul (c1//c2) p2);;
(* ------------------------------------------------------------------------- *)

module DBase : sig 
 type t = 
    { mutable t_pols : pol list;
      mutable t_allp : (pol*vars) list;
              t_sons : (id_var, t) Hashtbl.t }

  val create : unit -> t
  val add : t -> pol -> unit
  val mem : t -> pol -> bool
  val get_all_prefix_lt : t -> vars -> (pol list * vars) list
  val get_all_prefix_gt : t -> vars -> (pol*vars) list
  val from_list : pol list -> t
  val get_vson : t -> id_var -> t option
end = struct 

  type t = 
    { mutable t_pols : pol list;
      mutable t_allp : (pol*vars) list;
              t_sons : (id_var, t) Hashtbl.t }

  let create () = 
    { t_pols = [];
      t_allp = [];
      t_sons = Hashtbl.create 17; }

  let get_vson t v =
    try Some (Hashtbl.find t.t_sons v)
    with Not_found -> None 

  let getupd_vson t v =
    try Hashtbl.find t.t_sons v 
    with Not_found ->
      let t' = create () in
      Hashtbl.add t.t_sons v t';
      t'
    
  let add t p = 
    match p with
    | [] -> ()
    | m::_ ->
      let rec aux t vs = 
        t.t_allp <- (p,vs) :: t.t_allp;
        match vs with
        | []      -> t.t_pols <- p :: t.t_pols
        | v :: vs -> aux (getupd_vson t v) vs in
      aux t m.vars
                 
  let get_all_prefix_lt =
    let rec aux ps t vs = 
      match vs with 
      | [] -> ps 
      | v:: vs ->
        match get_vson t v with 
        | None -> ps
        | Some t -> 
          let ps = (t.t_pols,vs) :: ps in
          aux ps t vs in
    aux []

   let mem t p =
    let rec aux t vs = 
      match vs with 
      | [] -> List.mem p t.t_pols
      | v::vs ->
        match get_vson t v with 
        | None -> false
        | Some t -> aux t vs in
    match p with
    |[] -> List.mem p t.t_pols
    |mon::_ -> aux t mon.vars

  let rec get_all_prefix_gt t vs =
    match vs with 
    | [] -> t.t_allp
    | v:: vs ->
      match get_vson t v with 
      | None -> []
      | Some t -> get_all_prefix_gt t vs 

  let from_list (polys:pol list)=
    let t = create () in
    List.iter (add t) polys;
    t

end


(* ------------------------------------------------------------------------- *)
(* Reduction of a monom with respect to a base.                            *)
(* ------------------------------------------------------------------------- *)

let rec get_all_products (m:vars) (polys:DBase.t) : pol list list =
  let rec sub_sol (m:vars) (pol_prefs: (pol list * vars) list) =
    match pol_prefs with
    | [] -> []
    | (ps,r)::q -> 
       if r = [] then 
         List.map (fun p -> [p]) ps @ (sub_sol m q) 
       else 
         let subsols = get_all_products r polys in
         let sols =
           List.map (fun pol -> 
               List.map (fun a -> pol::a) subsols) ps
         in
         let sols = List.flatten sols in
         sols@(sub_sol m q)
  in
  sub_sol m (DBase.get_all_prefix_lt polys m);;

(* ------------------------------------------------------------------------- *)
(* Computation of critical pairs.                                            *)
(* ------------------------------------------------------------------------- *)


let rec monom_critical_pairs (m:vars) (polys:DBase.t) : (pol list * pol list) list =
  let products = get_all_products m polys in
  if products <> [] then
    List.map (fun l -> (l,[])) products
  else
    let rec sub_sol (pref: (pol list * vars) list) (suf: (pol * vars) list) =
      match pref,suf with
      |[],[] -> [([],[])]
      |[],(ss,r)::q -> let subsols = monom_critical_pairs r polys in
                        let sols =
                              List.map (fun (l1,l2)-> ss::l2,l1) subsols
                        in
                        if sols != [] then
                          sols
                        else
                          sub_sol pref q
      |(ps,r)::q,sufs -> let subsols = monom_critical_pairs r polys in
                        let sols =
                          List.map (fun pol ->
                              List.map (fun (l1,l2)-> pol::l1,l2) subsols) ps
                        in
                        if sols != [] then
                          List.flatten sols
                        else
                          sub_sol q sufs
    in
    let sols = sub_sol (DBase.get_all_prefix_lt polys m) ((DBase.get_all_prefix_gt polys m)) in
    sols;;


(* ------------------------------------------------------------------------- *)
(* Computation of the S polynoms.                                            *)
(* ------------------------------------------------------------------------- *)


let new_Spolys (p:pol)  (polys:DBase.t) : pol list =
  match (get_hd p) with
  |None -> []
  |Some mon ->
    let pairs = monom_critical_pairs mon.vars polys in 
    List.map (fun (ps1,ps2) -> s_poly (mpoly_muls ps1) (mpoly_muls (p::ps2)) ) pairs;;
   



(* ------------------------------------------------------------------------- *)
(* Computation of the S polynoms.                                            *)
(* ------------------------------------------------------------------------- *)

(* return all the possible one step reductions of a polynom wrt a base *)
let reduce_1 (p:pol) (polys:DBase.t) =
  match (get_hd p) with
  | None -> []
  | Some m -> 
    let prods = get_all_products m.vars polys in
    if prods = [] then
      [p]
    else
      (
      let prods = List.map mpoly_muls prods in
      let sub_prod prod = 
        match (get_hd prod) with
        | None    -> p 
        | Some m1 -> mpoly_sub p (mpoly_cmul (m.coeff//m1.coeff) prod) in
      List.map sub_prod prods
      );;

              
(* compute all the possible reductions of p wrt polys *)
let rec reduce (p:pol) (polys:DBase.t)=
  if DBase.mem polys p then
    [[]]
  else
    let reduced_1 = reduce_1 p polys in
    match reduced_1 with
    |[] -> [p]
    |[q] -> if equals p q then [p]
            else
              List.flatten (List.map (fun p -> reduce p polys) reduced_1)
    |_ ->  List.flatten (List.map (fun p -> reduce p polys) reduced_1);;


(* ------------------------------------------------------------------------- *)
(* Is a polynom deducible ?                                                  *)
(* ------------------------------------------------------------------------- *)

let deduce (p:pol) (polys:pol list)=
  let rec aux (p:pol) (base:DBase.t) (acc:pol list) =
    let reduces = reduce p base in
    if (List.exists is_null reduces) then
      true          (* if the polynom reduces to 0, we have a base *)
    else
      (
        match acc with
        |[] -> false   (* if we already considered all the possible critical pairs, it is over *)
        |[]::accs -> aux p base accs
        |pol::accs ->
          let s_polys = new_Spolys pol base in
          (* for each s_polys, we compute its different reductions, and if they are not null
             we add them to the base and to the accumulators *)
          let new_acc = List.fold_right
                          (fun s_poly acc ->
                              let reduces = reduce s_poly base in
                              let res = ref acc in
                              List.iter (fun reduced ->
                                  if not(is_null reduced) then
                                    DBase.add base reduced;
                                    res := reduced::!res    
                                ) reduces;
                                !res
                              
                          ) s_polys [] in
          aux p base (accs @ new_acc)
      ) in
  aux p (DBase.from_list polys) polys;;
    


 let rec aux_get_inv (p:pol) (base:DBase.t) (acc:pol list) =
   let reduces = reduce p base in
   let rec get_null (reduced:pol list) =
     match reduced with
     |[] -> None
     |p::q -> if is_null p then Some (p) else get_null q
   in
   match (get_null reduces) with
   | Some (p) -> p
   | None ->
      (
        match acc with
        |[] -> failwith "No inverter found"   (* if we already considered all the possible critical pairs, it is over *)
        |[]::accs -> aux_get_inv p base accs
        |pol::accs ->
          let s_polys = new_Spolys pol base in
          (* for each s_polys, we compute its different reductions, and if they are not null
             we add them to the base and to the accumulators *)
          let new_acc = List.fold_right
                          (fun s_poly acc ->
                            let reduces = reduce s_poly base in
                            let res = ref acc in
                            List.iter (fun reduced ->
                                if not(is_null reduced) then
                                  DBase.add base reduced;
                                res := reduced::!res    
                              ) reduces;
                            !res
                             
                          ) s_polys [] in
          aux_get_inv p base (accs @ new_acc)
      );;


let sort_poly : pol -> pol = fun p ->
        sort (fun m1 m2 -> 
        match (morder_lt m1 m2, morder_lt m2 m1) with
        | (false, true) -> -1
        | (true, false) -> 1
        | (false, false) -> 0
        | (true, true) -> failwith "unreach"
        ) p


let sort_polys : pol list -> pol list =
    map sort_poly

let inverter (p:pol) (polys:pol list)=
  let acc = ref 0 in
  let polys = List.map (fun pol ->
                  acc := !acc - 1;
                pol@[{coeff=Num.Int 1; vars=[!acc]; size=(-1,-1);length=0}])
  (sort_polys polys)
  in
  let inv = aux_get_inv (sort_poly p) (DBase.from_list polys) polys in
  mpoly_cmul (Int (-1)) inv;;

(* Exemples *)
(*
let m1 = {coeff=Num.Int 1; vars=[27]; size=(2,2); length=1};;
let m2 = {coeff=Num.Int 1; vars=[27;78]; size=(2,4); length=2};;
let m3 = {coeff=Num.Int 1; vars=[27;27;78]; size=(2,4); length=3};;
let m4 = {coeff=Num.Int 1; vars=[27;27]; size=(2,2); length=2};;
let m5 = {coeff=Num.Int 1; vars=[78]; size=(2,4); length=1};;

let p1 = mpoly_add [m1] [m2];;
mpoly_mul [m1] [m2;m1];;

let base = DBase.from_list [[m1];[m2];[m2;m1];[m4];[m5]];;
DBase.get_all_prefix_lt base [1;2] ;;

get_all_products [1;2]   (DBase.from_list [[m1];[m2];[m2;m1];[m4];[m5]]);;

let base2 =  DBase.from_list [[m3];[m5]];;

monom_critical_pairs [1;1] base;;
monom_critical_pairs [1;1] base2;;

reduce_1 [m3] (DBase.from_list [[m2;m4];[m5;m3]]);;
reduce [m3;m1] (DBase.from_list [[m4;m1];[m5];[m2;m1];[m1]]);;


let lb =  [[m2];[m2;m1]];;
get_all_products m1.vars (DBase.from_list lb);;
reduce_1 [m1] (DBase.from_list lb);;
deduce [m1] lb;;
deduce [m2] lb;;
deduce [m3] lb;;
deduce [m4] lb;;
deduce [m5] lb;;
inverter [m1] lb;;
inverter [m2] lb;;
inverter [m3] lb;;
inverter [m4] lb;;
(*inverter [m5] lb;;*)

*)


let (x:mon) = {coeff=Num.Int 1; vars = [1]; size=(2,3); length=1};;
let (yz : mon) = {coeff=Num.Int 1; vars = [2;3]; size=(2,3); length=2};;
let (a : mon) = {coeff=Num.Int 1; vars = [4]; size=(3,4); length=1};;
 
let xa = {coeff=Num.Int 1; vars=[1;4]; size=(2,4); length=2};;
let yza = {coeff = Num.Int 1; vars=[2;3;4]; size=(2,4); length = 3};;
 
inverter ([xa; yza]) [[x; yz]; [a]];;


(*
let oldp = 
    [{coeff=Num.Int 1; vars = [77;47;48]; size=(1,1); length=3}];;

let mybase = 
    [[{coeff=Num.Int 1; vars = [1]; size=(2,3); length=1}];


    let m = 23 in
    let n = 17 in
[[{coeff=Num.Int 1; vars = [30]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [33]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [36]; size=(n,m); length=1}];
[{coeff=Num.Int 1; vars = [40]; size=(m+1,1); length=1}];
[{coeff=Num.Int 1; vars = [66]; size=(1,m); length=1}];
[{coeff=Num.Int 1; vars = [68]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [47]; size=(m,n); length=1}];
[{coeff=Num.Int 1; vars = [48]; size=(n,1); length=1}];
[{coeff=Num.Int 1; vars = [36;35]; size=(n,1); length=2}];
[{coeff=Num.Int 1; vars = [68]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [69]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [77;47]; size=(1,n); length=2}];
[{coeff=Num.Int 1; vars = [92]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [93]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [47]; size=(m,n); length=1}];
[{coeff=Num.Int 1; vars = [41]; size=(1,m+1); length=1}];
[{coeff=Num.Int 1; vars = [67]; size=(m,1); length=1}];
[{coeff=Num.Int 1; vars = [69]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [36]; size=(n,m); length=1}];
[{coeff=Num.Int 1; vars = [94]; size=(1,n); length=1}];
[{coeff=Num.Int 1; vars = [77;47]; size=(1,n); length=2}];
[{coeff=Num.Int 1; vars = [69]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [68]; size=(1,1); length=1}];
[{coeff=Num.Int 1; vars = [36;35]; size=(n,1); length=2}]];;

inverter oldp mybase;;
*)
