open Expr
open MatData
open ExprUtils
open Util
open NCGroebner
open MatSig
open MatData
open Num
open Abbrevs

module type MATDEDUC = functor (M : MATDATA) -> sig
    type split_subgoals = SSBase of M.mat | SSConcatR of (split_subgoals *
    split_subgoals) | SSConcatL of (split_subgoals * split_subgoals)

    val solve_mat : (expr * inverter) list -> expr -> inverter
end


module MatDeduc : MATDEDUC = functor (M : MATDATA) -> struct
    module MatRules = MkMat (M)
    module MatMon = MkMon (M)
    module MatGasbi = MkGasbi (MatMon)
    open MatMon


type split_subgoals = SSBase of M.mat | SSConcatR of (split_subgoals *
split_subgoals) | SSConcatL of (split_subgoals * split_subgoals)



let solve_mat eis e = 
    let mk_log level = mk_logger "Core.CoreRules" level "CoreRules.ml" in
    let log_i = mk_log Bolt.Level.INFO in

let mkSplitLeft e =
    M.expr_of_mat (M.MSplitLeft (M.mat_of_expr e)) in

let mkSplitRight e =
    M.expr_of_mat (M.MSplitRight (M.mat_of_expr e)) in

let mkTrans e =
    M.expr_of_mat (M.MTrans (M.mat_of_expr e)) in

let mkOpp e =
    M.expr_of_mat (M.MOpp (M.mat_of_expr e)) in

let mkMult e1 e2 =
    M.expr_of_mat (M.MMult (M.mat_of_expr e1, M.mat_of_expr e2))
in

let mkPlus es =
    M.expr_of_mat (M.MPlus (M.shape_of_expr (List.hd es), List.map M.mat_of_expr es))
in

let mkConcat e1 e2 =
    M.expr_of_mat (M.MConcat (M.mat_of_expr e1, M.mat_of_expr e2)) in


let expr_to_id (e : expr) : int = e.e_tag in
let pol_of_base (elt : M.elt) : MatMon.pol = 
    let e = M.expr_of_elt elt in
    [MatGasbi.mk_vmon (expr_to_id e) (MatMon.shape_of_expr e)]
in

let i_op (f : expr -> expr) (i : inverter) =
    match i with
    | I e -> I (f e)
in

let sl_mi (mi : (M.mat * inverter)) : M.mat * inverter =
    (M.MSplitLeft (fst mi), (i_op mkSplitLeft (snd mi)))
in
    
let sr_mi (mi : (M.mat * inverter)) : M.mat * inverter =
    (M.MSplitRight (fst mi), (i_op mkSplitRight (snd mi)))
in

let tr_mi (mi : (M.mat * inverter)) : M.mat * inverter =
    (M.MTrans (fst mi), i_op mkTrans (snd mi))
in


let rec full_split_mi (mi : (M.mat * inverter)) : (M.mat * inverter) list =
    let mshape = M.shape_of_expr (M.expr_of_mat (fst mi)) in
    if M.shape_splittable mshape then
        List.concat (List.map full_split_mi [sl_mi mi; sr_mi mi])
    else if M.shape_leftsplittable mshape then
        List.concat (List.map full_split_mi
          [tr_mi (sl_mi (tr_mi mi)); tr_mi (sr_mi (tr_mi mi))])
    else [mi]
in

let mis_decomp (mis : (M.mat * inverter) list) : (M.mat * inverter) list =
    List.concat (List.map full_split_mi mis)
in

let mis_add_trans (mis : (M.mat * inverter) list) =
    mis @ (List.map tr_mi mis)
in

let mi_of_ei (ei : expr * inverter) =
    ((MatRules.norm_mat (M.mat_of_expr (fst ei))), snd ei)
in

let norm_mis (mis : (M.mat * inverter) list) =
    List.map (fun mi -> ((MatRules.norm_mat (fst mi), snd mi))) mis
in

let ei_of_mi (mi : M.mat * inverter) =
    ((M.expr_of_mat (fst mi), snd mi))
in

(* pol_of_mat : translate splitleft, splitright, trans as atomic *)



let rec pol_of_mat : M.mat -> MatMon.pol = function
    | M.MPlus (_, ms) -> List.concat (List.map pol_of_mat ms)
    | M.MOpp m -> MatGasbi.mpoly_cmul (Num.Int (-1)) (pol_of_mat m)
    | M.MMult (m1,m2) -> 
            MatGasbi.mpoly_mul (pol_of_mat m1) (pol_of_mat m2)
    | M.MTrans m -> 
            pol_of_base (M.elt_of_expr (mkTrans (M.expr_of_mat m)))
    | M.MConcat (m1, m2) -> 
            log_i (lazy (fsprintf "translating concat"));
            failwith "concat"
    | M.MSplitLeft m -> 
            pol_of_base (M.elt_of_expr (mkSplitLeft (M.expr_of_mat m)))
    | M.MSplitRight m -> 
            pol_of_base (M.elt_of_expr (mkSplitRight (M.expr_of_mat m)))
    | M.MId s -> 
            pol_of_base (M.elt_of_expr (M.expr_of_mat (M.MId s)))
    | M.MZero s -> 
            pol_of_base (M.elt_of_expr (M.expr_of_mat (M.MZero s)))
    | M.MBase exp -> pol_of_base exp
in


let pi_of_mi (mi : M.mat * inverter) =
    (pol_of_mat (fst mi), snd mi)
in


let rec subgoals_of_targ (m : M.mat) =
    let s = M.shape_of_expr (M.expr_of_mat m) in
    if M.shape_splittable s then
        let m_sl = M.MSplitLeft m in
        let m_sr = M.MSplitRight m in
        SSConcatR (subgoals_of_targ m_sl, subgoals_of_targ m_sr)
    else if M.shape_leftsplittable s then
        let m_lsl = M.MTrans (M.MSplitLeft (M.MTrans m)) in
        let m_lsr = M.MTrans (M.MSplitRight (M.MTrans m)) in
        SSConcatL (subgoals_of_targ m_lsl, subgoals_of_targ m_lsr)
    else
        SSBase m
in

let rec norm_subgoals : split_subgoals -> split_subgoals = function
    | SSBase m -> SSBase (M.mat_of_expr (Norm.norm_expr_strong (M.expr_of_mat m)))
    | SSConcatL (s1, s2) -> SSConcatL (norm_subgoals s1, norm_subgoals s2)
    | SSConcatR (s1, s2) -> SSConcatR (norm_subgoals s1, norm_subgoals s2)
in


let rec pp_subgoals (fmt : F.formatter) (sg : split_subgoals) =
    match sg with
    | SSBase m -> F.fprintf fmt "%a" pp_expr (M.expr_of_mat m)
    | SSConcatL (s1, s2) -> pp_subgoals fmt s1; F.fprintf fmt ", "; pp_subgoals fmt s2
    | SSConcatR (s1, s2) -> pp_subgoals fmt s1; F.fprintf fmt ", "; pp_subgoals fmt s2
in
    


(* --- actual deducibility --- *)



let inverter_of_pol (p : MatMon.pol)  (base : expr list) =
    let expr_of_mon (m : MatMon.mon) =
        let rec build_mult (is : int list) (s : MatMon.shape) : expr =
            match is with
            | i :: [] -> List.nth base ((-i) - 1)
            | (i1 :: i2 :: []) -> mkMult (List.nth base ((-i1) - 1)) (List.nth base ((-i2) - 1))
            | i :: is' -> mkMult (List.nth base ((-i) - 1)) (build_mult is' s)
            | [] -> failwith "bad monomial"
        in
        match m.MatMon.coeff with
        | Int 1 -> (build_mult (m.MatMon.vars) (m.MatMon.size))
        | Int (-1) -> mkOpp (build_mult (m.MatMon.vars) (m.MatMon.size))
        | _ -> tacerror "unknown coeff type"
   in
   match p with
   | [] -> tacerror "empty p?"
   | _ ->
       I (mkPlus (List.map (expr_of_mon) p))
in

let rec deduc_subgoals (sg : split_subgoals) (base : (MatMon.pol * inverter) list) =
    match sg with
    | SSConcatR (sg1,sg2) ->
            (match (deduc_subgoals sg1 base, deduc_subgoals sg2 base) with
            | (I i1, I i2) -> I (mkConcat i1 i2))
    | SSConcatL (sg1,sg2) ->
            (match (deduc_subgoals sg1 base, deduc_subgoals sg2 base) with
            | (I i1, I i2) -> I (mkTrans (mkConcat (mkTrans i1)
            (mkTrans i2))))
    | SSBase m ->
            let targ_pol = pol_of_mat m in
            try
                let targ_invpol = MatGasbi.inverter targ_pol (List.map fst base) in
                inverter_of_pol targ_invpol (List.map expr_of_inverter (List.map snd base)) 
            with
                Not_found ->
                    log_i (lazy (fsprintf "failed deducing %a" pp_expr
                    (M.expr_of_mat m)));
                    raise Not_found
in

let rec constant_pis (s : M.shape) : (MatMon.pol * inverter) list =
    List.map (fun ce -> let p = pol_of_base (M.elt_of_expr ce) in (p, I ce))
    (M.all_constants_of_shape s)
in

    (* compute target pol, split into subgoals *)
    let targ_m' = (M.mat_of_expr e) in
    let targ_sgs = norm_subgoals (subgoals_of_targ targ_m') in
    
    (* compute input mats *)
    let mis = List.map mi_of_ei eis in
    (* norm *)
    let mis = norm_mis mis in
    (* fullly split *)
    let mis = mis_decomp mis in
    (* add trans *)
    let mis = mis_add_trans mis in
    (* norm *)
    let mis = norm_mis mis in

    log_i (lazy (fsprintf "Begin deducing with inputs %a" (pp_list "," pp_expr)
    (List.map fst (List.map ei_of_mi mis))));


    let pis = List.map pi_of_mi mis in

    (* throw in constants *)
    let pis = pis @ constant_pis (M.shape_of_expr e) in
    
    try
        deduc_subgoals targ_sgs pis
    with
        Not_found ->
            log_i (lazy (fsprintf "End deduce"));
          raise Not_found
         
end



