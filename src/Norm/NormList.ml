open MatData
open Expr
open Type

module ListMatRules = MatSig.MkMat(ListMat)

let rec norm_list_expr nftop e = 
    let nf = norm_list_expr nftop in
    let rewr x = ListMat.expr_of_mat (ListMatRules.norm_mat (ListMat.mat_of_expr x)) in
    let ans = (match e.e_node with
    | App(op,es) when ExprUtils.is_list_op op -> rewr (Expr.mk_App op (List.map nf es) e.Expr.e_ty)
    | Nary(nop, es) when ExprUtils.is_list_nop nop -> rewr (Expr.mk_Nary nop (List.map nf es))
    | _ -> nftop e) in
    if (Expr.equal_expr ans e) then
        ans
    else
        nf ans


let norm_list_ifte nftop e e1 e2 = 
    let nf = norm_list_expr nftop in
    Expr.mk_Ifte (nf e) (nf e1) (nf e2)
