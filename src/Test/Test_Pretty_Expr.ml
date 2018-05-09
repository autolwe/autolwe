(* tests for pretty printer *)
open ExprSyntax
open Type
open Expr

let main =
  let fpr fs pp e = Format.printf fs pp e in
  let h = Hsym.mk "H" (mk_Prod [mk_Fq;mk_Fq;mk_Fq]) mk_Fq in
  let gv1 = Groupvar.mk "1" in
  let gv2 = Groupvar.mk "2" in
  let gv3 = Groupvar.mk "3" in
  let es = Esym.mk "e" gv1 gv2 gv3 in
  (* no redundant parentheses around tuple *)
  fpr "%a  =?  H(0,1,0)\n\n" pp_exp (mk_H h (mk_Tuple [f0;f1;f0]));
  (* '*' and - *)
  fpr "%a  =?  0-0*1\n\n" pp_exp (f0 -: (f0 *: f1));
  fpr "%a  =?  (0-1)*1\n\n" pp_exp ((f0 -: f1) *: f1);
  (* 'x' and '^' *)
  fpr "%a  =?  (g_1 * g_1)^(1*1)\n\n" pp_exp ((mk_GMult [mk_GGen gv1; mk_GGen gv1]) ^: (f1 *: f1));
  fpr "%a  =?  g_2 * g_2 ^ (1*1)\n\n" pp_exp (mk_GMult [mk_GGen gv2; (mk_GGen gv2) ^: (f1 *: f1)]);
  fpr "%a  =?  g x g x g\n\n" pp_exp (mk_GMult [mk_GGen gv1; mk_GGen gv1; mk_GGen gv1]);
  fpr "%a  =?  e(g_1,g_2) * g_3\n\n" pp_exp (mk_GMult [ mk_EMap es (mk_GGen gv1) (mk_GGen gv2); mk_GGen gv3]);
  (* '-' and '/' *)
  fpr "%a  =?  1-(1-1)\n\n" pp_exp (mk_FMinus f1 (mk_FMinus f1 f1));
  fpr "%a  =?  1-1-1\n\n" pp_exp (mk_FMinus (mk_FMinus f1  f1) f1);
  fpr "%a  =?  (1/1)/0\n\n" pp_exp (mk_FDiv (mk_FDiv f1  f1) f0);
  fpr "%a  =?  0/(1/1)\n\n" pp_exp (mk_FDiv f0 (mk_FDiv f1  f1))
