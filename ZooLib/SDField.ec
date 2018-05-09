require import FSet.
import Dexcepted.
require SD.
require import PrimeField.
import Int.
import Real.


clone SD as SDF with
   type init <- unit,
   type input <- F.t,
   type output <- F.t,
   type adv_output <- unit,
   op witness <- F.zero
   proof finite_output.
realize finite_output. 
proof. 
  exists (FSet.img F.ofint (Interval.interval 0 (q-1))) => x.
  rewrite ISet.mem_univ /= img_def;exists (F.toint x). 
  by smt.
qed. 
 
module S = {
  proc init () : unit = {}
  proc sample (e1:F.t) : F.t = {
    var r;
    r = $FDistr.dt;
    return r;
  }
}.   
 
module SE = {
  proc init () : unit = {}
  proc sample (e1:F.t) : F.t = {
    var r;
    r = $ (FDistr.dt \ FSet.single e1);
    return r;
  }
}.   
 
section.

  local module S2 = {
    proc init () : unit = {}
    proc sample1 = S.sample
    proc sample2 = SE.sample
  }.

  local lemma pr_sample1 &m e0 a : Pr[S2.sample1(e0) @ &m : res = a] = 1%r/q%r.
  proof.
    byphoare (_: e1 = e0 ==> a = res) => //.
    by proc;rnd ((=) a) => /=;auto;progress;smt.  
  qed.

  local lemma pr_sample2 &m e0 a : a <> e0 => 
      Pr[S2.sample2(e0) @ &m : res = a] = 1%r/(q%r - 1%r).
  proof.
    intros Hd.
    byphoare (_: e1 = e0 ==> a = res) => //.
    proc; rnd ((=) a) => /=;auto.
    intros &m1 ->.
    change (Distr.mu_x ((FDistr.dt)%FDistr \ single e0) a = 1%r / (q%r - 1%r)).
    rewrite Dexcepted.mu_x_def.
    cut -> /= : Distr.in_supp a ((FDistr.dt)%FDistr \ single e0) = true;
      first by rewrite eqT supp_def; smt.
    rewrite (mu_cpMem _ _ (1%r/q%r)) 2:card_single;first by smt.
    rewrite FDistr.mu_x_def_in FDistr.lossless.
    by algebra;smt.
  qed.

  local lemma pr_sum &m e0 :
     Monoid.Mrplus.sum
       (fun (a : t),
          `|(Pr[S2.sample1(e0) @ &m : res = a] -
              Pr[S2.sample2(e0) @ &m : res = a])|)
       (ISet.Finite.toFSet (ISet.univ)) <= 2%r * 1%r / q%r.
  proof.
    cut -> : 
      ISet.Finite.toFSet (ISet.univ) = (FSet.img F.ofint (Interval.interval 0 (q-1))).
     apply FSet.set_ext => x.
     rewrite ISet.Finite.mem_toFSet.
       exists (FSet.img F.ofint (Interval.interval 0 (q-1))) => y.
       by rewrite ISet.mem_univ /= img_def;exists (F.toint y); smt.
     by rewrite ISet.mem_univ /= img_def;exists (F.toint x); smt.
    pose f :=
      (fun (x:int),
          let a = ofint x in
          `|Pr[S2.sample1(e0) @ &m : res = a] - Pr[S2.sample2(e0) @ &m : res = a]|).
    cut -> := 
      Monoid.Mrplus.sum_eq 
        (fun (a:t),
          `|Pr[S2.sample1(e0) @ &m : res = a] - Pr[S2.sample2(e0) @ &m : res = a]|)
        (fun (a:t), f (toint a)).
      by move => x /=;rewrite /f /= oftoint.
    rewrite -(Monoid.Mrplus.sum_chind f F.ofint F.toint);first smt.
    rewrite -(add_rm_in (F.toint e0) (Interval.interval 0 (q - 1)));first smt.
    rewrite Monoid.Mrplus.sum_add /=;first by smt.
    rewrite {1}/f /= oftoint.
    rewrite (pr_sample1 &m e0 e0).
    cut -> : Pr[S2.sample2(e0) @ &m : res = e0] = 0%r.
      byphoare (_: e1 = e0 ==> e0 = res) => //.
      by proc;rnd ((=) e0) => /=;auto;progress;smt.
    cut Hq : 0%r <> q%r by smt.
    cut Hq1 : 0%r <> (q%r - 1%r) by smt.
    rewrite (Monoid.Mrplus.NatMul.sum_const (1%r/(q%r*(q%r - 1%r)))).
      intros x Hx /=.
      rewrite /f /= (pr_sample1 &m e0 (ofint x)).
      rewrite (pr_sample2 &m e0 (ofint x));first by smt.
      algebra Hq Hq1.
      (* FIXME *) admit.
    rewrite card_rm_in;first smt.
    rewrite Interval.card_interval_max.
    rewrite /max (_ : (q - 1 - 0 + 1 < 0) = false) /=;first by smt.
    rewrite Monoid.NatMul_mul. smt.
    cut -> : `|1%r / q%r| = 1%r / q%r. 
      (* FIXME *) admit. 
    algebra Hq Hq1.
  qed.

  lemma SD_conseq_abs (A <: SDF.SD_Adv{SDF.SDNquery.Count}) &m
     (EV : (glob A) -> unit -> bool) :
     `| Pr[SDF.SDNquery.SD(A, S).main() @ &m : EV (glob A) res ] -
        Pr[SDF.SDNquery.SD(A, SE).main() @ &m : EV (glob A) res ]| <=
      SDF.SDNquery.q%r /q%r.
  proof.
   cut -> : 
     Pr[SDF.SDNquery.SD(A, S).main() @ &m : EV (glob A) res ] = 
     Pr[SDF.SDNquery.SD(A, SDF.S1(S2)).main() @ &m : EV (glob A) res].
    byequiv (_ : ={glob A} ==> ={glob A,res}) => //;sim.
   cut -> : 
     Pr[SDF.SDNquery.SD(A, SE).main() @ &m : EV (glob A) res] = 
     Pr[SDF.SDNquery.SD(A, SDF.S2(S2)).main() @ &m : EV (glob A) res ].
    byequiv (_ : ={glob A} ==> ={glob A,res}) => //;sim.
   apply (SDF.SDNquery.SD_conseq_abs S2 (1%r/q%r) (fun x, true) _ _ _ _ A &m EV);auto.
   apply pr_sum.
  qed.

  lemma SD_conseq_add (A <: SDF.SD_Adv{SDF.SDNquery.Count}) &m
      (EV : (glob A) -> unit -> bool) :
      Pr[SDF.SDNquery.SD(A, S).main() @ &m : EV (glob A) res] <= 
         Pr[SDF.SDNquery.SD(A, SE).main() @ &m : EV (glob A) res] + 
         SDF.SDNquery.q%r /q%r.
  proof. cut H5 := SD_conseq_abs A &m EV => //;smt. qed.

  lemma SD_conseq_add_E (A <: SDF.SD_Adv{SDF.SDNquery.Count}) &m
      (EV : (glob A) -> unit -> bool) :
      Pr[SDF.SDNquery.SD(A, SE).main() @ &m : EV (glob A) res] <= 
         Pr[SDF.SDNquery.SD(A, S).main() @ &m : EV (glob A) res] + 
         SDF.SDNquery.q%r /q%r.
  proof. cut H5 := SD_conseq_abs A &m EV => //;smt. qed.

  lemma SD1_conseq_abs
    (A <: SDF.SD1query.SD1_Adv{SDF.SD1query.SDN.Count}) &m 
    (EV : (glob A) -> unit -> bool):
      `|Pr[SDF.SD1query.SD1(A, S).main() @ &m : EV (glob A) res] -
        Pr[SDF.SD1query.SD1(A, SE).main() @ &m : EV (glob A) res]| <=
      1%r/q%r.
  proof.
    cut -> : 
      Pr[SDF.SD1query.SD1(A, S).main() @ &m : EV (glob A) res] = 
      Pr[SDF.SD1query.SD1(A, SDF.S1(S2)).main() @ &m : EV (glob A) res].
     byequiv (_ : ={glob A} ==> ={glob A,res}) => //;sim.
    cut -> : 
      Pr[SDF.SD1query.SD1(A, SE).main() @ &m : EV (glob A) res] = 
      Pr[SDF.SD1query.SD1(A, SDF.S2(S2)).main() @ &m : EV (glob A) res].
     byequiv (_ : ={glob A} ==> ={glob A,res}) => //;sim.
    apply (SDF.SD1query.SD1_conseq_abs S2 A (1%r/q%r)(fun x,true) _ _ _ _ &m EV);auto.
    apply pr_sum.
  qed.

  lemma SD1_conseq_add
    (A <: SDF.SD1query.SD1_Adv{SDF.SD1query.SDN.Count}) &m 
    (EV : (glob A) -> unit -> bool):
      Pr[SDF.SD1query.SD1(A, S).main() @ &m : EV (glob A) res] <= 
      Pr[SDF.SD1query.SD1(A, SE).main() @ &m : EV (glob A) res] + 
      1%r/q%r.
  proof. cut H5 := SD1_conseq_abs A &m EV => //;smt. qed.
   
  lemma SD1_conseq_add_E
    (A <: SDF.SD1query.SD1_Adv{SDF.SD1query.SDN.Count}) &m 
    (EV : (glob A) -> unit -> bool):
      Pr[SDF.SD1query.SD1(A, SE).main() @ &m : EV (glob A) res] <= 
      Pr[SDF.SD1query.SD1(A, S).main() @ &m : EV (glob A) res] + 
      1%r/q%r.
  proof. cut H5 := SD1_conseq_abs A &m EV => //;smt. qed.

end section.


