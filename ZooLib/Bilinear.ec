require import PrimeField.
require CyclicGroup.

theory Bl.

clone import CyclicGroup.CG as GS1.
clone import CyclicGroup.CG as GS2.
clone import CyclicGroup.CG as GT.

op e : GS1.group -> GS2.group -> GT.group.

axiom e_g_g : e GS1.g GS2.g = GT.g.

axiom eND : e GS1.g GS2.g <> GT.g1.


axiom e_pow1 (g:GS1.group) (x:t) f: e (g^x) f = (e g f)^x.
axiom e_pow2 (f:GS2.group) x g: e g (f^x) = (e g f)^x.

lemma e_pow (g:GS1.group) (f:GS2.group) (x y:t) : e (g^x) (f^y) =  (e g f)^(x*y).
proof.
  by rewrite e_pow2 e_pow1 GT.pow_pow.
qed.

lemma e_mul1 x y g2: e x g2 * e y g2 = e (x*y) g2.
proof.
  by rewrite -(GS1.gpow_log x) -(GS1.gpow_log y) GS1.mul_pow !e_pow1 GT.mul_pow.
qed.

lemma e_mul2 g1 x y: e g1 x * e g1 y = e g1 (x*y).
proof.
  by rewrite -(GS2.gpow_log x) -(GS2.gpow_log y) GS2.mul_pow !e_pow2 GT.mul_pow.
qed.

lemma log_e (x:GS1.group) (y:GS2.group):
  log (e x y) = log x * log y.
proof.
  rewrite -{1}(GS1.gpow_log x) -{1}(GS2.gpow_log y) e_pow GT.log_pow F.mulA e_g_g GT.log_g;ringeq.
qed.

hint rewrite Ring.rw_algebra : e_g_g log_e.

end Bl.
   
