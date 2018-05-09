open CAS
open Expr
open ExprSyntax
open Type
open Util

module F = Format

let main =
  let vs = Vsym.mk "x" mk_Fq in
  let v = mk_V vs in
  let gv = Groupvar.mk "1" in
  let h = Hsym.mk "h" (mk_G gv) mk_Fq in
  let e =  ((v +: (fint 2)) /: ((fpow v 2) -: (fint 4))) +: mk_H h (mk_GGen gv) in
  F.printf "%a\n" pp_exp (norm (fun e -> e) e)
