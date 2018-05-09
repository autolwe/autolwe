open Norm
open Type
open Expr
open DeducField
open OUnit

let vx = Vsym.mk "x" mk_Fq
let vy = Vsym.mk "y" mk_Fq
let vz = Vsym.mk "z" mk_Fq
let vu = Vsym.mk "u" mk_Fq
let vv = Vsym.mk "v" mk_Fq
let vw = Vsym.mk "w" mk_Fq
let vhh = Vsym.mk "hh" mk_Fq
let (x,y,z) = (mk_V vx, mk_V vy, mk_V vz)
let (u,v,w) = (mk_V vu, mk_V vv, mk_V vw)
let hh = mk_V vhh
let vx2 = Vsym.mk "x2" mk_Fq
let vy2 = Vsym.mk "y2" mk_Fq
let vz2 = Vsym.mk "z2" mk_Fq
let vu2 = Vsym.mk "u2" mk_Fq
let vv2 = Vsym.mk "v2" mk_Fq
let vw2 = Vsym.mk "w2" mk_Fq
let (x2,y2,z2) = (mk_V vx2, mk_V vy2, mk_V vz2 )
let (u2,v2,w2) = (mk_V vu2, mk_V vv2, mk_V vw2)


let p1 = mk_V (Vsym.mk "p1" mk_Fq)
let p2 = mk_V (Vsym.mk "p2" mk_Fq)
let p3 = mk_V (Vsym.mk "p3" mk_Fq)
let p4 = mk_V (Vsym.mk "p4" mk_Fq)
let p5 = mk_V (Vsym.mk "p5" mk_Fq)
let p6 = mk_V (Vsym.mk "p6" mk_Fq)
let p7 = mk_V (Vsym.mk "p7" mk_Fq)
let p8 = mk_V (Vsym.mk "p8" mk_Fq)

let eval_ctx known ctx =
  let m = me_of_list known in
  norm_expr (e_subst m ctx)

let test1 _ =
  let a   = x in
  let b   = mk_FPlus [x;z] in  
  let sec = z in
  let known = [ (p1,a); (p2,b) ] in
  let ctx = solve_fq known sec in
  assert_equal ~msg:"test1: solution valid" (eval_ctx known ctx) sec

let test2 _ =
  let a   = mk_FPlus [x;y] in
  let b   = mk_FPlus [x;z] in
  let sec = z in
  let known = [ (p1,a); (p2,b) ] in
  assert_raises ~msg:"test2: no solution" Not_found (fun () -> solve_fq known sec)

let test3 _ = 
  let a   = x in
  let b   = mk_FPlus [x;z] in  
  let c   = y in  
  let sec = mk_FMult [z;y] in
  let known = [ (p1,a); (p2,b); (p3,c) ] in
  let ctx = solve_fq known sec in
  assert_equal ~msg:"test3: solution valid" (eval_ctx known ctx) sec

(* test cases from rrandom for Cramer-Shoup (modulo renaming) *)

(* x -> y*z + x *)
let test4 _ = 
  let e1   = y in
  let e2   = z in  
  let e3   = mk_FPlus [x; mk_FMult [y;z]] in  
  let sec  = x in
  let known = [ (p1,e1); (p2,e2); (p3,e3) ] in
  let ctx = solve_fq known sec in
  assert_equal ~msg:"test4: solution valid" (eval_ctx known ctx) sec

(* y -> x*z + y*v + u - w*y*z *)
let test5 _ = 
  let e1   = x in
  let e2   = z in  
  let e3   = u in  
  let e4   = v in    
  let e5   = w in    
  let e6   = mk_FPlus [mk_FMult [x;z]; mk_FMult [y;v]; u; mk_FOpp (mk_FMult [w; y; z])] in
  let sec  = y in
  let known = [ (p1,e1); (p2,e2); (p3,e3); (p4,e4); (p5,e5); (p6,e6) ] in
  let ctx = solve_fq known sec in
  assert_equal ~msg:"test5: solution valid" (eval_ctx known ctx) sec

(* y -> x*u + y*v - w*y*u - w*y2*u*hh + z*u*hh + y2*v*hh *)
let test6 _ = 
  let e1   = x in
  let e2   = u in
  let e3   = v in  
  let e4   = w in    
  let e5   = y2 in    
  let e6   = hh in
  let e7   = z in
  let e8   = mk_FPlus [ mk_FMult [x;u]
                      ; mk_FMult [y;v]
                      ; mk_FOpp (mk_FMult [w;y;u])
                      ; mk_FOpp (mk_FMult [w;y2;u;hh])
                      ; mk_FMult [z;u;hh]
                      ; mk_FMult [y2;v;hh]
                      ]
  in
  let sec  = y in
  let known = [ (p1,e1); (p2,e2); (p3,e3); (p4,e4); (p5,e5); (p6,e6); (p7,e7); (p8,e8) ] in
  let ctx = solve_fq known sec in
  assert_equal ~msg:"test6: solution valid" (eval_ctx known ctx) sec

let suite =
  "Solve_fq" >::: [ "test_solve_fq_1" >:: test1
                  ; "test_solve_fq_2" >:: test2
                  ; "test_solve_fq_3" >:: test3
                  ; "test_solve_fq_4" >:: test4
                  ; "test_solve_fq_5" >:: test5
                  ; "test_solve_fq_6" >:: test6
                  ]

let _ = run_test_tt_main suite
