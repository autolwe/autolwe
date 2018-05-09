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

module MatDeduc : MATDEDUC
