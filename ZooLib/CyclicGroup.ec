require import Distr.
require import ZooUtil.
require import PrimeField.

theory CG.
type group.

op g:group. (* the generator *)
op ( * ): group -> group -> group.   (* multiplication of group elements *)
op [-]  : group -> group.            (* inverse of the multiplication *) (* Why [/] do not work? *)
op ( / ): group -> group -> group.   (* division *)
op ( ^ ): group -> t -> group.       (* exponentiation *)
op log  : group -> t.                (* discrete logarithm *)
op g1 = g ^ F.zero.

axiom gpow_log (a:group): g ^ (log a) = a.
axiom log_gpow x : log (g ^ x) = x.

lemma nosmt log_bij x y: x = y <=> log x = log y by [].
lemma nosmt pow_bij (x y:F.t): x = y <=> g^x =g^y by [].


axiom inv_def (a:group): - a = g ^ (-log a).
axiom div_def (a b:group): g^(log a - log b) = a / b.

axiom mul_pow g (x y:t): g ^ x * g ^ y = g ^ (x + y).

axiom pow_pow g (x y:t): (g ^ x) ^ y = g ^ (x * y).

lemma log_pow (g1:group) x: log (g1 ^ x) = log g1 * x by [].

lemma log_mul (g1 g2:group): log (g1 * g2) = log g1 + log g2 by [].

lemma pow_mul (g1 g2:group) x: g1^x * g2^x = (g1*g2)^x.
proof.
  rewrite -{1}(gpow_log g1) -{1}(gpow_log g2) !pow_pow mul_pow.
  by rewrite !(F.mulC _ x) mulfDl F.mulC -pow_pow -mul_pow !gpow_log.
qed.

lemma pow_opp (x:group) (p:F.t): x^(-p) = -(x^p).
proof.
  rewrite inv_def. 
  cut -> : -p = (-F.one) * p by ringeq.
  cut -> : -log (x ^ p) = (-F.one) * log(x^p) by ringeq.
  by rewrite !(F.mulC (-F.one)) -!pow_pow gpow_log.
qed.

lemma mulC (x y: group): x * y = y * x.
proof. 
  by rewrite -(gpow_log x) -(gpow_log y) mul_pow;smt. 
qed.

lemma mulA (x y z: group): x * (y * z) = x * y * z.
proof. 
  by rewrite -(gpow_log x) -(gpow_log y) -(gpow_log z) !mul_pow;smt. 
qed.

lemma mul1 x: g1 * x = x.
proof.
  by rewrite /g1 -(gpow_log x) mul_pow;smt.
qed.

lemma divK (a:group): a / a = g1.
proof strict.
  by rewrite -div_def sub_def addfN.
qed.

lemma log_g : log g = F.one.
proof strict.
 cut H: log g - log g = F.one + -log g by smt.
 cut H1: log g = log g + F.one + -log g; smt.
qed.

lemma g_neq0 : g1 <> g.
proof.
  rewrite /g1 -{2}(gpow_log g) log_g -pow_bij;smt.
qed.

lemma mulN (x:group): x * -x = g1.
proof.
  rewrite inv_def -{1}(gpow_log x) mul_pow;smt. 
qed.

(*
lemma log_oif b (x y : group) :
  log (oif b x y) = oif b (log x) (log y) by case b.
hint rewrite Ring.rw_algebra : log_oif.
*)
lemma log_if b (x y : group) :
  log (if b then x else y) = if b then (log x) else (log y) by case b.
hint rewrite Ring.rw_algebra : log_if.

require Ring. 

lemma inj_gpow_log (a:group): a = g ^ (log a) by smt.

hint rewrite Ring.inj_algebra : inj_gpow_log.
hint rewrite Ring.rw_algebra : log_g log_pow log_mul log_bij.

theory Distr.
  op dt : group distr.

  import Real.

  axiom supp_def: forall (s:group),
    in_supp s dt.

  axiom mu_x_def_in: forall (s:group),
    mu_x dt s = (1%r/q%r).

  axiom lossless: weight dt = 1%r.

  require import FSet.
  import Dexcepted.
  axiom loosless_excp x : weight (dt \ single x) = 1%r.

end Distr.

end CG.