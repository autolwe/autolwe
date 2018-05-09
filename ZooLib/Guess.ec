require import Option.
require import Int.
require import FSet.
require import Real.
require import Distr.

require import Monoid.
require import ISet.
require import List.
require import Pair.
require Means.
require import ZooUtil.

type output.
op q : int.
axiom q_pos : 0 < q.

module type Adv = {
  proc main () : output list
}.

module Arand (A:Adv) = {
  proc main () : output = {
    var i, l;
    l = A.main();
    i = $[0.. q-1];
    return oget (nth l i);
  }
}.

section.

  declare module A:Adv. 

  local clone import Means as LMeans with
    type input <- int,
    type output <- output list,
    op d <- [0 .. q-1]
    proof *.

  local module W = {
    proc work (i:int) : output list = {
      var l;
      l = A.main();
      return l;
    } 
  }.

  local lemma finite_inter : Finite.finite (create (support [0..q - 1])).
  proof.
    rewrite /Finite.finite; exists (Interval.interval 0 (q-1))=> x; rewrite mem_create;smt.
  qed.

  local lemma Muni &m (P:glob A -> output -> bool) : 
      Mrplus.sum
       (fun (v : int), Pr[W.work(v) @ &m : P (glob A) (oget (nth res v))])
       (Interval.interval 0 (q-1)) = 
     q%r * Pr[Rand(W).main() @ &m : P (glob A) (oget (nth (snd res) (fst res)))].
  proof.
    cut := Mean_uni W &m (fun i gl l, P gl (oget (nth l i))) (1%r/q%r) _ _ => /=.
    + smt. + apply finite_inter.
    move=> ->.
    cut -> : Finite.toFSet (create (support [0..q - 1])) = Interval.interval 0 (q - 1).
    + apply FSet.set_ext=> x.
      rewrite Finite.mem_toFSet;[apply finite_inter | ].
      rewrite mem_create;smt.
    fieldeq. smt.
  qed.

  axiom length_bounded : hoare[A.main : true ==> `|res| <= q].
     
  local lemma sum_exists &m (P:glob A -> output -> bool) : 
     Pr[A.main() @ &m : any (P (glob A)) res] <=
     Mrplus.sum
       (fun (v : int), Pr[W.work(v) @ &m : P (glob A) (oget (nth res v))])
       (Interval.interval 0 (q-1)).
  proof.
    cut -> : (Mrplus.sum
                (fun (v : int), Pr[W.work(v) @ &m : P (glob A) (oget (nth res v))])
                (Interval.interval 0 (q - 1))) = 
             (Mrplus.sum
                (fun (v : int), Pr[A.main() @ &m : P (glob A) (oget (nth res v))])
                (Interval.interval 0 (q - 1))).
    + apply Mrplus.sum_eq=> v H {H} /=.
      byequiv (_: ={glob A} ==> ={glob A,res})=> //. 
      proc*;inline W.work; sim.
    apply (Real.Trans _ 
      Pr[A.main() @ &m : 
           cpOrs (img (fun v r,  P (glob A) (oget (nth r v))) (Interval.interval 0 (q-1)))
                 res]).
    byequiv (_: ={glob A} ==> `|res{1}| <= q /\ ={glob A, res}) => //.
    conseq * (_:_ ==> ={glob A, res}) length_bounded => //; sim.
    move=> &m1 &m2 [Hle [_ _]];subst;rewrite /List.any=> [x [Hm Hp]].
    cut := mem_ex_nth x res{m2} Hm => [[n [Hn H]]].
    cut -> : Interval.interval 0 (q - 1) = FSet.add n (Interval.interval 0 (q - 1)).
    + apply FSet.set_ext=> i;smt.
    rewrite img_add cpOrs_add;left=> /=;rewrite H;smt.
    move: (Interval.interval 0 (q - 1)).
    elim/set_ind.
    rewrite Mrplus.sum_empty.
    byphoare (_ : _ ==> false)=> //;progress;by rewrite img_empty cpOrs0.
    move=> x s Hx Hrec.
    rewrite Mrplus.sum_add => //=.
    cut -> : 
     Pr[A.main() @ &m :
       cpOrs
         (img (fun (v : int) (r : output list), P (glob A) (oget (nth r v)))
           (add x s)) res] = 
      Pr[A.main() @ &m :
       P (glob A) (oget (nth res x)) \/
       cpOrs
         (img (fun (v : int) (r : output list), P (glob A) (oget (nth r v))) s) res].
    + rewrite Pr [mu_eq] // => &hr;rewrite img_add cpOrs_add //.
    rewrite Pr [mu_or].  
    by apply le_trans_sub;[ smt | apply Real.addleM].
  qed.

  lemma conclusion &m (P:glob A -> output -> bool) : 
    Pr[A.main() @ &m : any (P (glob A)) res] <=
    q%r * Pr[Arand(A).main() @ &m : P (glob A) res].
  proof.
    cut -> : Pr[Arand(A).main() @ &m : P (glob A) res] =
             Pr[Rand(W).main() @ &m : P (glob A) (oget (nth (snd res) (fst res)))].
    + byequiv (_ : _ ==> _) => //.
      proc;inline W.work. swap{1} 2 -1;wp.
      by call (_: true);auto.
    apply (Real.Trans _ ( Mrplus.sum
       (fun (v : int), Pr[W.work(v) @ &m : P (glob A) (oget (nth res v))])
       (Interval.interval 0 (q-1)))).
    + apply (sum_exists &m P).
    by rewrite (Muni &m P).
  qed.

end section.

