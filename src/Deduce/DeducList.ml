open Expr
open ExprUtils
open MatData
open DeducMatSig

module ListD = MatDeduc (ListMat)
let solve_mat_list eis e = 
    let (d, _) = Expr.ensure_list_ty e.e_ty "hi" in

    let eis' = List.map (fun ei ->
        match ((fst ei).e_ty.ty_node) with
        | List _ -> ei
        | _ -> (mk_ListOf d (fst ei), I (mk_ListOf d (expr_of_inverter (snd ei))))) eis in

    ListD.solve_mat eis' e

let solve_other_list eis e = failwith "unimp"
