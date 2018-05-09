(* * Derived tactics for rewriting. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open Type
open Syms
open Expr
open ExprUtils
open Norm
open NormUtils
open NormField
open Game
open CoreTypes
open Tactic
open TheoryTypes

module Ht = Hashtbl

let mk_log level = mk_logger "Derive.RewriteRules" level "RewriteRules.ml"
let log_t = mk_log Bolt.Level.TRACE
let log_i = mk_log Bolt.Level.INFO

(* ** Derived rewriting tactics
 * ----------------------------------------------------------------------- *)

(** Unfold all lets and norm. *)
let t_norm ?fail_eq:(fe=false) ?strong:(strong=false) ju =
  let se = ju.ju_se in
  let norm = if strong then norm_expr_strong else norm_expr_nice in
  let new_se = norm_se ~norm se in
  if fe && equal_sec_exp se new_se
  then t_fail "t_norm: equal judgments" ju
  else t_conv true new_se ju

(** Unfold all lets and norm, also remove tuple projection. *)
let t_norm_tuple_proj ju =
  let se = ju.ju_se in
  let norm e = NormUtils.(remove_tuple_proj (norm_expr_nice e)) in
  let new_se = norm_se ~norm se in
  t_conv true new_se ju

(** Norm without unfolding. *)
let t_norm_nounfold ju =
  let se = ju.ju_se in
  let new_se = map_se_exp NormUtils.norm_expr_nice se in
  t_conv true new_se ju

(** Unfold without norm. *)
let t_unfold_only ju =
  let se = ju.ju_se in
  let new_se = norm_se ~norm:id se in
  t_conv false new_se ju

(** split exponent expression into a base and known/unknown terms *)
let split_exponent ts e gv unknown =
  let is_unknown e = Se.mem e unknown in
  (* split into: base (from expression(s) log(a)), unknown and known exponents *)
  let rec split_unknown e =
    match e.e_node with
    | Nary(FMult,es) ->
      let mk_split b uk kn =
        match uk,kn with
        | [],ke -> (b,mk_FMult ke,None)
        | ue,[] -> (b,mk_FMult ue,None)
        | ue,ke -> (b,mk_FMult ue,Some(mk_FMult ke))
      in
      let base,remaining =
        match List.partition (is_GLog_gv gv) es with
        | (b::bs,cs) -> (* find log(a) s.t. a in group gv  *)
          (Some (destr_GLog b),bs@cs)
        | ([],_) -> (* find log(a) and log(b) s.t. e(a,b) in group gv *)
          let emaps =
            L.filter
              (fun esym -> Groupvar.equal esym.EmapSym.target gv)
              (L.map snd (Mstring.bindings ts.ts_emdecls))
          in
          begin match emaps with
          | esym::_ ->
            let (gv1,gv2) = (esym.EmapSym.source1,esym.EmapSym.source2) in
            if Groupvar.equal gv1 gv2 then (
              let es_gv1,others = List.partition (is_GLog_gv gv1) es in
              begin match es_gv1 with
              | b1::b2::es_gv1 ->
                (Some (mk_EMap esym (destr_GLog b1) (destr_GLog b2))
                ,es_gv1@others)
              | _ -> (None,es)
              end
            ) else (
              let es_gv1,others = List.partition (is_GLog_gv gv1) es in
              let es_gv2,others = List.partition (is_GLog_gv gv2) others in
              begin match es_gv1,es_gv2 with
              | b1::es_gv1, b2::es_gv2 ->
                (Some (mk_EMap esym (destr_GLog b1) (destr_GLog b2))
                ,es_gv1@es_gv2@others)
              | [],_ | _,[] -> (None,es)
              end
            )
          | [] -> (None,es)
          end
      in
      let ue,ke = List.partition is_unknown remaining in
      mk_split base ue ke
    | App(FOpp,[a]) ->
      begin match split_unknown a with
      | (b,e1,None)    -> (b,mk_FOpp e1,None)
      | (b,e1,Some e2) -> (b,e1,Some(mk_FOpp e2))
      end
    | _ -> (None,e,None)
  in
  (* extract list of summands and (possibly) denominator *)
  let (sum,denom) =
    match e.e_node with
    | Nary(FPlus,es)  -> (es,None)
    | App(FDiv,[a;b]) ->
      begin match a.e_node with
      | Nary(FPlus,es) -> (es,Some b)
      | _ -> ([e],Some b)
      end
    | _ -> ([e], None)
  in
  (List.map split_unknown sum, denom)

let rewrite_exps ts unknown e0 =
  let rec go e =
    let e = e_sub_map go e in
    match e.e_node with
    | App(GExp gv,[a;b]) ->
      assert (is_GGen a);
      let gen = a in
      let (ies,ce) = split_exponent ts b gv unknown in
      (*
      let to_exp (a,b,c) =
        mk_GExp (mk_GExp (from_opt gen a) b) (from_opt mk_FOne c)
      in *)
      (* log_t (lazy (fsprintf "norm_unknown: %a, ce = %a" (pp_list ", " pp_exp)
                     (L.map to_exp ies) (pp_opt pp_exp) ce)); *)
      let get_gen og = match og with None -> gen | Some a -> a in
      let expio b ie moe =
        let g = get_gen b in
        match moe with
        | Some oe -> mk_GExp (mk_GExp g ie) oe
        | None    -> mk_GExp g ie
      in
      let a =
        match ies with
        | []         -> gen
        | [b,ie,moe] -> expio b ie moe
        | ies        ->
          (* merge elements with the same base *)
          let iess =
            L.group_consecutive
              (fun (e1,u1,oe1) (e2,u2,oe2) ->
                oe1 = None && oe2 = None && equal_expr (get_gen e1) (get_gen e2)
                  && ((not (is_GLog u1) && not (is_GLog u2)) || equal_expr u1 u2))
              ies
          in
          let combine_group ies =
            match ies with
            | (b,_,None)::_ ->
              let es = L.map (fun (_,ie,moe) -> assert (moe = None); ie) ies in
              expio b (mk_FPlus es) None
            | [ (b,ie,moe)]  ->
              expio b ie moe
            | _ -> assert false
          in
          mk_GMult (List.map combine_group iess)
      in
      begin match ce with
      | None    -> a
      | Some oe -> mk_GExp a (mk_FInv oe)
      end
    | _ -> e
  in
  go e0

(*i norm and try to rewrite all exponentiations as products of
   (g^i)^o or X where i might be unknown, but o is not unknown.
   If there is a "let z=g^i" we can replace g^i by z in the next
   step. i*)
let t_norm_unknown ts unknown ju =
  let se = ju.ju_se in
  let norm e =
    rewrite_exps ts (se_of_list unknown) (norm_expr_weak e)
    |> abbrev_ggen |> remove_tuple_proj
  in
  let new_se = map_se_exp norm se in
  t_conv true new_se ju

let rewrite_div_reduce a e =
  let solve a e =
    assert (Type.is_Fq e.e_ty);
    let (p1,p2) = polys_of_field_expr e in
    let (a1,a2) = polys_of_field_expr a in
    if a2 <> None then e
    else
      let g = div_factor p1 a1 in
      let f = reduce p1 a1 in
      let mult = if equal_expr (mk_FNat 1) g then a else mk_FMult [g; a] in
      let res =
        if equal_expr (mk_FNat 0) g then (exp_of_poly p1)
        else if equal_expr (mk_FNat 0) f then mult
        else mk_FPlus [mult; f]
      in
      match p2 with
      | None -> res
      | Some d ->
        let e' = mk_FDiv res (exp_of_poly d) in
        e'
  in
  e_map_ty_maximal Type.mk_Fq (solve a) e

(*i normalize field expressions (in exponents and elsewhere such that
    polynomials are expressed as a*f + g i*)
let t_norm_solve a ju =
  let se = ju.ju_se in
  let norm e =
    abbrev_ggen (rewrite_div_reduce (norm_expr_weak a) (norm_expr_weak e))
  in
  let new_se = map_se_exp norm se in
  t_conv true new_se ju

let t_let_abstract p vs e0 mupto do_norm_expr ju =
  let se = ju.ju_se in
  let v = mk_V vs in
  let e = if do_norm_expr then norm_expr_nice e0 else e0 in
  let subst a =
    if is_Tuple e then (
      let subst =
        me_of_list (L.mapi (fun i a -> (a,mk_Proj i v)) (destr_Tuple e))
      in
      e_subst subst a
    ) else (
      e_replace e v a
    )
  in
  log_t (lazy (fsprintf "t_let_abstr: %a" pp_expr e0));
  let l,r = Util.cut_n p se.se_gdef in
  let new_se =
    match mupto with
    | Some j ->
      log_t (lazy (fsprintf "<< %i" j));
      if (j < p) then tacerror "t_let_abstract: invalid upto %i" j;
      let cl = j - p in
      if (cl > L.length r) then tacerror "t_let_abstract: invalid upto %i" j;
      let r1,r2 = Util.cut_n cl r in
      let r = List.rev_append (map_gdef_exp subst r1) r2 in
      { se_gdef = List.rev_append l (GLet(vs,e0)::r);
        se_ev = se.se_ev }
    | None ->
      { se_gdef = List.rev_append l (GLet(vs,e0)::map_gdef_exp subst r);
        se_ev = subst se.se_ev }
  in
  t_conv true new_se ju


let t_let_abstract_oracle opos vs e0 len do_norm_expr ju =
  let se = ju.ju_se in
  let v = mk_V vs in
  let e = if do_norm_expr then norm_expr_nice e0 else e0 in
  let subst a =
    if is_Tuple e then (
      let subst =
        me_of_list (L.mapi (fun i a -> (a,mk_Proj i v)) (destr_Tuple e))
      in
      e_subst subst a
    ) else (
      e_replace e v a
    )
  in
  log_t (lazy (fsprintf "t_let_abstr_oracle: %a" pp_expr e0));
  let nlen = match len with Some nlen -> nlen | _ -> 0 in
  let cmds,octxt =
    try get_se_octxt_len se opos nlen
    with _ -> tacerror "Error, couldn't get octxt, probably due to given opos being wrong."
  in
  let cur_scope_cmds,out_of_scope_cmds = if (len <> None)
                    then cmds,octxt.seoc_cright
                    else octxt.seoc_cright,[] in
  let new_cmds = LLet(vs,e0)::(L.map (map_lcmd_exp subst) cur_scope_cmds) in
  let new_seoc_return = if (len = None)
                        then subst octxt.seoc_return
                        else octxt.seoc_return in
  let new_octxt = {octxt with seoc_cright = out_of_scope_cmds;
                              seoc_return = new_seoc_return} in
  let new_se = set_se_octxt new_cmds new_octxt in
  t_conv true new_se ju


let t_rename v1 v2 ju =
  let se = ju.ju_se in
  let new_se = subst_v_se (fun v -> if VarSym.equal v v1 then v2 else v) se in
  t_conv true new_se ju

let t_subst p e1 e2 mupto ju =
  let se = ju.ju_se in
  let subst a = e_replace e1 e2 a in
  let l,r = cut_n p se.se_gdef in
  let new_se =
    match mupto with
    | Some j ->
      if (j < p) then tacerror "t_let_abstract: invalid upto %i" j;
      let cl = j - p in
      if (cl > L.length r) then tacerror "t_let_abstract: invalid upto %i" j;
      let r1,r2 = Util.cut_n cl r in
      let r = List.rev_append (map_gdef_exp subst r1) r2 in
      { se_gdef = List.rev_append l r;
        se_ev = se.se_ev }
    | None ->
      { se_gdef = L.rev_append l (map_gdef_exp subst r);
        se_ev   = subst se.se_ev }
  in
  log_t (lazy (fsprintf "t_subst before:@\n  %a@\n" pp_se se));
  log_t (lazy (fsprintf "t_subst after:@\n  %a@\n" pp_se new_se));
  t_conv true new_se ju

let t_let_unfold p ju =
  let se = ju.ju_se in
  match get_se_ctxt se p with
  | GLet(vs,e), sec ->
    let subst a = e_replace (mk_V vs) e a in
    let sec = { sec with
                sec_right = map_gdef_exp subst sec.sec_right;
                sec_ev = subst sec.sec_ev }
    in
    t_conv false (set_se_ctxt [] sec) ju
  | _ -> tacerror "rlet_unfold: no let at given position"

let t_abstract_deduce ~keep_going ts gpos v e mupto ju =
  let sep = "====================================" in
  let se = ju.ju_se in
  let ve = mk_V v in
  let frame = [(Norm.norm_expr_strong e,I ve)] in
  let maxlen = L.length se.se_gdef in
  let cache = He.create 17 in
  if not (O.map_default (fun upto -> gpos <= upto && upto < maxlen) true mupto) then
    tacerror "invalid upto-value %a, value must be >= %i and < %i"
      (pp_opt pp_int) (O.map ((+) 1) mupto) (gpos + 1) (maxlen + 1);
  let abstract_len = O.map_default (fun upto -> upto - gpos + 1) (maxlen - gpos) mupto in
  let a_cmds, sec = get_se_ctxt_len se ~pos:gpos ~len:abstract_len in
  log_i (lazy (fsprintf "@[%s@\nAbstracting in@\n%a@]"
                 sep (pp_gdef ~nonum:true) a_cmds));
  let secret_vars =
    L.map (function GSamp(vs,_) -> Some (mk_V vs) | _ -> None) sec.sec_left
    |> cat_Some |> se_of_list
  in
  let deduce_non_tuple e =
    log_i (lazy (fsprintf "@[<hov>@\nSearching for@ @[<hov 2>%a@]@]" pp_expr e));
    try
      let recipe = He.find cache e in
      log_i (lazy (fsprintf "@[<hov>%s@\nFound @[<hov 2>%a@] for@ @[<hov 2>%a@] in cache@]"
                     sep pp_expr recipe pp_expr e));
      recipe
    with
      Not_found ->
        let k_vars =
          L.map (fun v -> (v, I v)) (Se.elements (Se.diff (e_vars e) secret_vars))
        in
        let (I recipe) = Deduc.invert ~ppt_inverter:true ts (frame@k_vars) e in
        He.add cache e recipe;
        log_i (lazy (fsprintf "@[<hov>%s@\nFound @[<hov 2>%a@] for@ @[<hov 2>%a@]@]"
                       sep pp_expr recipe pp_expr e));
        recipe
  in
  let rec deduce e =
    if is_Tuple e
    then mk_Tuple (L.map deduce (destr_Tuple e))
    else
      try
        deduce_non_tuple e
      with
      | Not_found when keep_going -> e
      | Not_found -> tacerror "t_abstract_deduce: cannot deduce %a" pp_expr e
  in
  log_i (lazy (fsprintf "Abstracting %i lines@\n" abstract_len));
  let a_cmds = map_gdef_exp deduce a_cmds in
  let se_ev =
    match mupto with
    | None   -> deduce sec.sec_ev
    | Some _ -> sec.sec_ev
  in
  let sec = {sec with sec_ev = se_ev} in
  t_conv true (set_se_ctxt (GLet(v,e)::a_cmds) sec) ju
