open MatData
open Expr
open Type

module MatRules = MatSig.MkMat(Mat)


let rec norm_mat_expr nftop e = 
    let nf = norm_mat_expr nftop in
    let rewr x = Mat.expr_of_mat (MatRules.norm_mat (Mat.mat_of_expr x)) in
    let ans = (match e.e_node with
    | App(op,es) when ExprUtils.is_mat_op op -> rewr (Expr.mk_App op (List.map nf es) e.Expr.e_ty)
    | Nary(nop, es) when ExprUtils.is_mat_nop nop -> rewr (Expr.mk_Nary nop (List.map nf es))
    | _ -> nftop e) in
    if (Expr.equal_expr ans e) then
        ans
    else
        nf ans


let norm_ifte nfo e e1 e2 =
    (* need to do the pulling out add thing *)
    let nf = norm_mat_expr nfo in
    Expr.mk_Ifte (nf e) (nf e1) (nf e2) 

(*



*)
