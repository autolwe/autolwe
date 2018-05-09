(* *  Derived rules for dealing with [add_test], [case_ev], and [except]. *)

(* ** Imports and abbrivations *)
open Abbrevs
open Util
open Type
open Expr
open ExprUtils
open Game
open GameUtils
open Syms
open Nondet
open Rules
open TheoryState
open CoreTypes
open CoreRules
open NormField

module Ht = Hashtbl
module CR = CoreRules
module T = Tactic

let mk_log level = mk_logger "Derive.CaseRules" level "CaseRules.ml"
let _log_t = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG

(* ** Types for useful cases
 * ----------------------------------------------------------------------- *)

(* Useful (in)equalities that can be obtained by applying one of the three rules *)
type useful_cases =
  | AppAddTest    of ocmd_pos * expr * ty * ty
  | AppExcept     of gcmd_pos * expr
  | AppCaseEv     of expr
(* | AppExceptOrcl of ocmd_pos * expr *)
  with compare

let uc_exp uc = match uc with
  | AppAddTest(_,e,_,_) (* | AppExceptOrcl(_,e)  *)
  | AppExcept(_,e) | AppCaseEv(e) -> e

let pp_useful_cases fmt uc =
  match uc with
  | AppAddTest((g_idx,oi,o_idx,otype),e,_,_) ->
    F.fprintf fmt "app(raddtest (%i,%i,%i,%a)) %a)" g_idx oi o_idx pp_otype otype pp_expr e
  | AppExcept(g_idx,e) ->
    F.fprintf fmt "app(rexcept (%i) %a)" g_idx pp_expr e
  | AppCaseEv(e) ->
    F.fprintf fmt "app(rcase_ev %a)" pp_expr e
(*i  | AppExceptOrcl((g_idx,oi,o_idx),e) ->
      F.fprintf fmt "app(rexcept_orcl (%i,%i,%i)) %a)" g_idx oi o_idx pp_exp e i*)

let is_Useless e =
  is_FNat e || (is_FOpp e && is_FNat (destr_FOpp e))
  || is_RoCall e || is_FunCall e || is_MapLookup e

(* ** Compute and collect useful cases
 * ----------------------------------------------------------------------- *)

let compute_case gdef mhidden _fbuf ctx e =
  let cases = ref [] in
  let fes = ref Se.empty in
  e_iter_ty_maximal mk_Fq (fun e -> fes := Se.add e !fes) e;
  let facs = ref Se.empty in
  L.iter
    (fun v ->
      L.iter (fun e ->
        let ve = mk_V v in
        let (num,_denom) = NormField.polys_of_field_expr (Norm.norm_expr_weak e) in
        if Se.mem ve (e_vars e) then
          match NormField.div_factors num (EP.var ve) with
          | Some fs ->
            let fs = L.filter (fun e -> not (is_Useless e)) fs in
            facs := Se.union (se_of_list fs) !facs;
          | None -> ())
        (Se.elements !fes))
    mhidden;
  let facs = Se.diff !facs (se_of_list (ctx.ic_nonZero @ ctx.ic_isZero)) in
  let samps = samplings gdef in
  let rvars = se_of_list (L.map (fun (_,(v,_)) -> mk_V v) samps) in
  let is_invertible e =
    (not (is_Zero e)) &&
      (is_FNat e || (is_FOpp e && is_FNat (destr_FOpp e)))
  in
  (* NOTE: we could also take into account that v can be moved forward and
           the required variables could be moved forward *)
  let used_vars_defined uvs j =
    L.for_all
      (fun uv ->
        L.mem (destr_V uv)
          (cat_Some (L.map (fun (i,(v,_)) -> if i < j then Some(v) else None) samps)))
      (Se.elements uvs)
  in
  let add_case e =
    let (num,denom) = polys_of_field_expr e in
    if denom = None then (
      (* check if num solvable for random variable, then we can possibly
         ensure that num <> 0 by applying rexcept *)
      L.iter
        (fun (j,(v,_)) ->
          let ve = mk_V v in
          let (coeff,rem) = NormField.div_reduce num (EP.var ve) in
          let uvs = e_vars rem in
          if is_invertible coeff && used_vars_defined uvs j then (
            let exce = Norm.norm_expr_weak (mk_FDiv rem (mk_FOpp coeff)) in
            if not (is_Zero exce) then cases := AppExcept(j,exce) :: !cases
          )
        )
        samps
    );
    (* Schwartz-Zippel tells us that we cannot make the value zero in the other case *)
    if not (Se.subset (e_vars e) rvars) then (
      match ctx.ic_pos with
      | InEv                  ->
        cases := AppCaseEv(e) :: !cases
      | InOrcl(opos,aty,oty) ->
        cases := AppAddTest(opos,e,aty,oty) :: !cases
      | InOrclReturn(opos,aty,oty) ->
        cases := AppAddTest(opos,e,aty,oty) :: !cases
      | InMain(_gpos)         -> ()
        (* can we do anything above? rexcept is already handled above if possible *)
    )
  in
  if not (Se.is_empty facs) then (
    L.iter add_case (Se.elements facs)
  );
  !cases

let destr_Rev_Var e =
  match e.e_node with
  | App(GExp _,[e1;e2]) when is_GGen e1 && is_V e2 ->
    Some (destr_V e2)
  | _ when is_V e ->
    Some (destr_V e)
  | _ -> None
 
let maybe_hidden_rvars gdef =
  let rec go hidden gdef =
    match gdef with
    | [] -> hidden
    | GSamp(v,_) :: gdef ->
      go (v::hidden) gdef
    | GCall(_,_,e,_) :: gdef ->
      let es = if is_Tuple e then destr_Tuple e else [e] in
      let revealed_vars = cat_Some (L.map destr_Rev_Var es) in 
      let hidden = L.filter (fun v -> not (L.mem v revealed_vars)) hidden in
      go hidden gdef
    | _ :: gdef ->
      go hidden gdef
  in
  go [] gdef

let get_cases fbuf ju =
  let se = ju.ju_se in
  let maybe_hidden = maybe_hidden_rvars se.se_gdef in
  let cases = ref [] in
  F.fprintf fbuf "@[maybe hidden: %a@\n@\n@]" (pp_list ", " VarSym.pp) maybe_hidden;
  (*i write function that computes non-hidden variables (given out in exponent)
      and potentially hidden variables i*)
  (*i write function that traverses all maximal expression of type F_p together
      with position and determines useful case rule applications i*)
  iter_ctx_se_exp
    (fun ctx e ->
      let cs = compute_case se.se_gdef maybe_hidden fbuf ctx e in
      cases := cs @ !cases)
    se;
  let cases = L.sort_uniq compare_useful_cases !cases in
  (* we choose the earliest position if there are multiple occurences with the
     same expression *)
  let cases =
    L.group_consecutive (fun uc1 uc2 -> equal_expr (uc_exp uc1) (uc_exp uc2)) cases
    |> L.map L.hd
  in
  cases

let print_cases ts =
  let ju   =  L.hd (get_proof_state ts).subgoals in
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let cases = get_cases fbuf ju in
  F.fprintf fbuf "@[cases after:@\n  %a@\n@\n@]" (pp_list ",@\n  " pp_useful_cases) cases;
  (ts, "Here:\n\n"^(Buffer.contents buf))

(* ** Apply except with useful case
 * ----------------------------------------------------------------------- *)

let t_rexcept_maybe mi mes ju =
  if mes <> None
  then failwith "rexcept: placeholder for index, but not for expression not supported";
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let cases = get_cases fbuf ju in
  let except =
    cat_Some (L.map (function AppExcept(i,e) -> Some(i,e) | _ -> None) cases)
  in
  mconcat except >>= fun (j,e) ->
  guard (match mi with Some i -> i = j | None -> true) >>= fun _ ->
  T.t_except j [e] ju

(* ** Apply case_ev with useful case
 * ----------------------------------------------------------------------- *)

let simp_eq e =
  assert (is_Fq e.e_ty);
  let sort_pair (a,b) =
    if compare_expr a b > 0 then (a,b) else (b,a)
  in
  let res =
    match e.e_node with
    | Nary(FPlus,[a;b]) when is_FOpp a ->
      let (e1,e2) = sort_pair (destr_FOpp a, b) in
      mk_Eq e1 e2
    | Nary(FPlus,[a;b]) when is_FOpp b ->
      let (e1,e2) = sort_pair (destr_FOpp b, a) in
      mk_Eq e1 e2
    | _ ->
      mk_Eq e mk_FZ
  in
  NormUtils.norm_expr_nice res

let t_case_ev_maybe ju =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let cases = get_cases fbuf ju in
  let except = cat_Some (L.map (function AppCaseEv(e) -> Some(e) | _ -> None) cases) in
  mconcat except >>= fun e ->
  T.t_case_ev (simp_eq e) ju

let simp_eq_group e =
  let both_args e1 e2 =
       (is_FunCall e1 && is_FunCall e2)
    || (is_MapLookup e1 && is_MapLookup e2)
    || (is_RoCall e1 && is_RoCall e2) 
  in
  let to_g =
    match (destr_GLog (e_find is_GLog e)).e_ty.ty_node with
    | Type.G gn ->
      (fun fe -> mk_GExp (mk_GGen gn) fe)
    | _         -> id
  in
  assert (is_Fq e.e_ty);
  let sort_pair (a,b) =
    if compare_expr a b > 0 then (a,b) else (b,a)
  in
  let res =
    match e.e_node with
    | Nary(FPlus,[a;b]) when is_FOpp a ->
      let (e1,e2) = sort_pair (destr_FOpp a, b) in
      if both_args e1 e2 then
        mk_Eq e1 e2
      else
        mk_Eq (to_g e1) (to_g e2)
    | Nary(FPlus,[a;b]) when is_FOpp b ->
      let (e1,e2) = sort_pair (destr_FOpp b, a) in
      if both_args e1 e2 then
        mk_Eq e1 e2
      else
        mk_Eq (to_g e1) (to_g e2)
    | _ ->
      mk_Eq e mk_FZ
  in
  Norm.norm_expr_strong res

(* ** Apply guard with useful case
 * ----------------------------------------------------------------------- *)

let t_guard_maybe ju =
  let se = ju.ju_se in
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let cases = get_cases fbuf ju in
  let except =
    L.map
      (function AppAddTest(opos,e,aty,oty) -> Some(opos,e,aty,oty,NoCounter) | _ -> None)
      cases
    |> cat_Some
  in
  mconcat except >>= fun (opos,t,_aty,_oty,_c) ->
  let (i,j,k,l) = opos in
  let rec get_k k =
    try
      match get_se_lcmd ju.ju_se (i,j,k,l) with
      | _,_,(_,LGuard _,_),_,_ -> get_k (k+1)
      | _ -> k
    with
      _ -> k
  in
  let k = get_k k in
  let opos = (i,j,k,l) in
  let wvars = write_gcmds se.se_gdef in
  (* test must contain oracle arguments, otherwise useless for type
     of examples we consider *)
  guard (not (Se.subset (e_vars t) wvars)) >>= fun _ ->
  let test = simp_eq_group t in
  (T.t_guard opos (Some (NormUtils.norm_expr_nice test))
   @> T.t_move_oracle opos (-k)
   @> T.t_rewrite_oracle opos LeftToRight) ju
