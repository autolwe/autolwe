open Type
open OUnit

let test_type _ =
  let tv = Lenvar.mk "l" in
  Format.printf "tyvar: %a\n" Lenvar.pp tv;

  let ty1_a = mk_ty (BS tv) in
  let ty1 = mk_ty (Prod [ty1_a; ty1_a]) in
  Hsty.clear (); (* restart the program and load ty1 from storage. *) 
  let ty2_a = mk_ty (BS tv) in
  let ty2 = mk_ty (Prod [ty2_a; ty2_a]) in (* create the same type *)
  (* ty1 not equal ty2*)
  Format.printf "ty1=%a,  ty2=%a,  equal=%b \n" pp_ty ty1 pp_ty ty2 (ty_equal ty1 ty2);
  assert_equal ~msg:"ty1 and ty2 not equal" (ty_equal ty1 ty2) false;

  let ety1 = ty_export ty1 in
  let ety2 = ty_export ty2 in
  (* ety1 equal ety2 *)
  Format.printf "ety1=%a, ety2=%a, equal=%b \n" pp_ty ety1 pp_ty ety2 (ety1 = ety2);
  assert_equal ~msg:"ety1 and ety2 equal" ety1  ety2

let suite = "Type" >::: ["test_type" >:: test_type ]

let _ =
  run_test_tt_main suite