(* * Deducibility for group expressions. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open Syms
open Type
open Expr
open ExprUtils
open NormField
open GroebnerBasis
       
let mk_log level = mk_logger "Deduce.DeducGroup" level "DeducGroup.ml"
let log_i = mk_log Bolt.Level.INFO

(* ** Solving function
 * ----------------------------------------------------------------------- *)

(* NOTE: For now, we do not deal with rational functions in the
   exponent. It might be possible to generalize the current algorithm
   by performing something similar to the cross-multiplication used to
   reduce equality of field-expressions to equality of ring-expressions. *)
let solve_group (emaps : EmapSym.t list) (ecs : (expr * inverter) list) e =
  log_i (lazy (fsprintf "solve_group %a |- %a"
                 (pp_list "," (pp_pair pp_expr pp_inverter)) ecs pp_expr e));

  (* helper functions *)
  let gexp e h =
    if is_FOne h then e
    else if is_FZ h then mk_GExp (mk_GGen (destr_G_exn e.e_ty)) h
    else mk_GExp e h
  in
  let gmult e1 e2 =
    if is_GOne e1 then e2
    else if is_GOne e2 then e1
    else mk_GMult [e1; e2]
  in
  (* returns polynomial and inverter polynomial *)
  let subtract_known f k_Fq =
    let covered_terms, remaining_terms =
      L.partition
        (fun (m,_i) ->
          Se.subset (se_of_list (L.map fst m)) (he_keys k_Fq))
        (EP.to_terms f)
    in
    if covered_terms<>[] then (
      let i_poly =
        exp_of_poly (EP.from_terms covered_terms)
        |> e_subst (me_of_list (L.map (fun (e,I e') -> (e,e')) (he_to_list k_Fq)))
      in
      let f = EP.from_terms remaining_terms in
      (f,i_poly)
    ) else (
      (f,mk_FZ)
    )
  in
  (* returns polynomial and inverter transformer *)
  let group_to_poly_simp subtract e gn k_Fq =
    let exp = if is_GExp e then (snd (destr_GExp e)) else mk_GLog e in
    let (f, mh) = polys_of_field_expr (CAS.norm id exp) in
    let sub_f =
      let (f,i_poly) = subtract_known f k_Fq in
      if is_FNat i_poly
      then (f, None)
      else
        let i_poly = if subtract then mk_FOpp i_poly else i_poly in
        let inv = gexp (mk_GGen gn) i_poly in
        (f, Some inv)
    in
    (* NOTE: for now, we don't perform divide_known since this requires non-zero constraints *)
    match mh with
    | None ->
      let (f,minv) = sub_f in
      (f, O.map_default (fun inv -> fun i -> I (gmult (expr_of_inverter i) inv)) id minv)
    | Some h0 ->
      let (h,i_poly_h) = subtract_known h0 k_Fq in
      let (f,minv) = sub_f in
      if not (EP.equal EP.zero h)
      then (
        log_i (lazy (fsprintf "unknown denominator %a" EP.pp h0));
        raise Not_found
      ) else (
        log_i (lazy (fsprintf "deduced denominator %a" EP.pp h0));
        let inv_f = O.map_default (fun inv -> fun i -> I (gmult (expr_of_inverter i) inv)) id minv in
        (f, fun i -> I (gexp (expr_of_inverter (inv_f i)) (mk_FInv i_poly_h)))
      )
  in
  let gt = destr_G_exn e.e_ty in

  (* known expressions / polynomials *)
  let known_Fq  = He.create 17 in
  let known_Gt  = Hep.create 17 in (* the group gt: always the group where e must be deduced *)
  let known_Gs1 = Hep.create 17 in (* left source group for e : _ x _ -> gt (if exists) *)
  let known_Gs2 = Hep.create 17 in (* right source group *)

  (* register known expressions in Fq *)
  let register_known_fq (e,i) =
    if (is_FPlus e || is_FOpp e || is_FMult e) then (
      log_i (lazy (fsprintf "solve_group: known polynomial %a in Fq ignored" pp_expr e))
    ) else if is_Fq e.e_ty then (
      He.add known_Fq e i
    )
  in
  L.iter register_known_fq ecs;

  (* register known expressions in Gn *)
  let register_known k gn ((e,i) : expr * inverter) =
    if equal_ty e.e_ty (mk_G gn) then (
      let (f,i_trans) = group_to_poly_simp true e gn known_Fq in
      Hep.add k f (i_trans i)
    )
  in
  L.iter (register_known known_Gt gt) ecs;

  (* register expressions that can be computed by pairing expressions from source groups *)
  let em =
    try Some (L.find (fun es -> Groupvar.equal gt es.EmapSym.target) emaps)
    with Not_found -> None
  in
  begin match em with
  | None -> ()
  | Some em ->
    begin
      log_i (lazy (fsprintf "relevant map: %a" EmapSym.pp em));
      L.iter (register_known known_Gs1 em.EmapSym.source1) ecs;
      L.iter (register_known known_Gs2 em.EmapSym.source2) ecs;
      (* apply pairing to known group elements in source groups *)
      Hep.iter (fun f1 i1 ->
        Hep.iter (fun f2 i2 ->
          let ie1 = expr_of_inverter i1 in
          let ie2 = expr_of_inverter i2 in
          Hep.add known_Gt (EP.mult f1 f2) (I (mk_EMap em ie1 ie2)))
          known_Gs2)
        known_Gs1;
      (* known in source groups => known in target group (pair with generator) *)
      Hep.iter (fun f1 i1 ->
        let ie1 = expr_of_inverter i1 in
        Hep.add known_Gt f1 (I (mk_EMap em ie1 (mk_GGen em.EmapSym.source2))))
        known_Gs1;
      Hep.iter (fun f2 i2 ->
        let ie2 = expr_of_inverter i2 in
        Hep.add known_Gt f2 (I (mk_EMap em (mk_GGen em.EmapSym.source1) ie2)))
        known_Gs2
    end
  end;

  Hep.iter
    (fun f i -> log_i (lazy (fsprintf "known in exponent: %a with %a" EP.pp f pp_inverter i)))
    known_Gt;

  (* simplify secret by subtracting known (in Fq) terms *)
  let (f,i_trans) = group_to_poly_simp false e gt known_Fq in
  log_i (lazy (fsprintf "searching for exponent: %a @\n  with %a"
                 EP.pp f pp_inverter (i_trans (I (mk_V (VarSym.mk "[_]" e.e_ty))))));

  (* search for inverter by using Grobner Basis *)                

  (* we build the list of known polynomials, along with the corresponding inverter *)
  let known_polys = Hep.fold (fun fe i acc -> (fe,expr_of_inverter i) ::acc) known_Gt [] in
  (* we construct the list of fully known variables in the field *)
  let k_fQ =  He.fold (fun fe i acc -> (fe,expr_of_inverter i)::acc) known_Fq [] in
  (* we convert the expressions to our polynomial type *)  
  let (secret::polys),vars,mh = eps_to_polys ((f,gexp (mk_GGen gt) (mk_FNat 0))::known_polys) in
  (* we construct the set of private vars *)
  let private_vars = List.map (fun i-> if List.mem (Hashtbl.find mh i) (List.map fst k_fQ) then 0 else 1 ) vars in
  (* we can then run the groebner algorithm *)
  let groebner_basis = GroebnerBasis.groebner vars mh k_fQ (List.map (fun p-> (p,private_vars)) polys) in
  let success,inver = GroebnerBasis.get_inverter vars mh k_fQ  groebner_basis secret in
  let final_inv=  expr_of_inverter (i_trans (I( gexp (inver)(mk_FOpp (mk_FNat 1)) ))) in
   if success then
    (
      I(final_inv)
    )

  else
       raise Not_found

