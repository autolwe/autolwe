require import Int.
require import Real.
require (*--*) Monoid.
(*---*) import Monoid.Mrplus.

type init.
type adv_output.
type input.
type output.
op witness : output.
axiom finite_output : ISet.Finite.finite (ISet.univ<:output>).

module type Sample2 = {
  proc init () : init
  proc sample1(_:input) : output
  proc sample2(_:input) : output
}.

module type Sample = {
  proc init () : init
  proc sample(_:input) : output
}.

module type Osample = {
  proc sample (_:input) : output
}.
     
module type SD_Adv(S:Osample) = {
  proc main (_:init) : adv_output 
}.

module S1 (S:Sample2) = {
  proc init = S.init
  proc sample = S.sample1
}.

module S2 (S:Sample2) = {
  proc init = S.init
  proc sample = S.sample2
}.

theory SDNquery.

  op q : int.
  axiom qpos : 0 <= q.

  module Count (S:Sample) = {
    var c:int
    
    proc init () : init = {
      var r;
      c = 0;
      r = S.init();
      return r;
    }

    proc sample (inp: input) : output = {
      var r = witness;
      if (c < q) {
        r = S.sample(inp);
        c = c + 1;
      }
      return r;
    }
  }.

  module SD (A:SD_Adv, S:Sample) = {

    module S = Count(S)
    module A = A(S)

    proc main():adv_output = {
      var i, b;
      i = S.init ();
      b = A.main (i);
      return b;
    }
  }.

  axiom SD_conseq_abs (S<:Sample2) eps (inv: glob S -> bool):
    hoare [S.init:true ==> inv (glob S)] =>
    hoare [S.sample1 : inv (glob S) ==> inv (glob S)] =>
    hoare [S.sample2 : inv (glob S) ==> inv (glob S)] =>
    (forall &m i, 
       inv (glob S){m} =>
       sum (fun (a:output), 
              `|Pr[S.sample1(i) @ &m : res = a ] - Pr[S.sample2(i) @ &m : res = a ]|) 
           (ISet.Finite.toFSet ISet.univ<:output>) <= 2%r * eps) =>
    forall (A <: SD_Adv {S, Count}) &m (EV:glob A -> adv_output -> bool),
      `|Pr[SD(A,S1(S)).main() @ &m : EV (glob A) res] - 
        Pr[SD(A,S2(S)).main() @ &m : EV (glob A) res]| <= q%r * eps.

  lemma SD_conseq_add (S<:Sample2) eps (inv: glob S -> bool):
    hoare [S.init:true ==> inv (glob S)] =>
    hoare [S.sample1 : inv (glob S) ==> inv (glob S)] =>
    hoare [S.sample2 : inv (glob S) ==> inv (glob S)] =>
    (forall &m i, 
       inv (glob S){m} =>
       sum (fun (a:output), 
              `|Pr[S.sample1(i) @ &m : res = a ] - Pr[S.sample2(i) @ &m : res = a ]|) 
           (ISet.Finite.toFSet ISet.univ<:output>) <= 2%r * eps) =>
    forall (A <: SD_Adv {S, Count}) &m (EV:glob A -> adv_output -> bool),
       Pr[SD(A,S1(S)).main() @ &m : EV (glob A) res] <= 
        Pr[SD(A,S2(S)).main() @ &m : EV (glob A) res] + q%r * eps.
  proof.
    intros H1 H2 H3 H4 A &m EV; cut H5 := SD_conseq_abs S eps inv _ _ _ _ A &m EV => //.
    smt.
  qed.
  
end SDNquery.

theory SD1query.

  module type SD1_Adv = {
    proc a1 (_:init) : input
    proc a2 (_:output) : adv_output
  }.

  module SD1 (A:SD1_Adv, S:Sample) = {

    proc main():adv_output = {
      var i, inp, s, r;
      i = S.init ();
      inp = A.a1(i);
      s   = S.sample(inp);
      r   = A.a2(s);
      return r;
    }
  }.

  clone SDNquery as SDN with 
     op q <- 1
  proof qpos by trivial.

  section. 

   declare module S:Sample2 {SDN.Count}.
   declare module A:SD1_Adv {S, SDN.Count}.

   local module Adv(S:Osample) = {
      proc main (i:init) : adv_output = {
        var inp, s, r;
        inp = A.a1(i);
        s   = S.sample(inp);
        r   = A.a2(s);
        return r;
      }
   }.

   import SDN.

   lemma SD1_conseq_abs eps (inv: glob S -> bool):
     hoare [S.init:true ==> inv (glob S)] =>
     hoare [S.sample1 : inv (glob S) ==> inv (glob S)] =>
     hoare [S.sample2 : inv (glob S) ==> inv (glob S)] =>
     (forall &m i, 
        inv (glob S){m} =>
        sum (fun (a:output), 
               `|Pr[S.sample1(i) @ &m : res = a ] - Pr[S.sample2(i) @ &m : res = a ]|) 
            (ISet.Finite.toFSet ISet.univ<:output>) <= 2%r * eps) =>
     forall &m (EV:glob A -> adv_output -> bool),
       `|Pr[SD1(A,S1(S)).main() @ &m : EV (glob A) res] - 
          Pr[SD1(A,S2(S)).main() @ &m : EV (glob A) res]| <= eps.
   proof.
     intros H1 H2 H3 H4 &m EV.    
     cut -> : Pr[SD1(A, S1(S)).main(tt) @ &m : EV (glob A) res] =
                  Pr[SD(Adv, S1(S)).main(tt) @ &m : EV (glob A) res].
       byequiv (_: ={glob A, glob S} ==> ={glob A, glob S, res}) => //.
       proc;inline *.
       rcondt{2} 8; first by intros &m1;swap 1 6;auto.
       by do ! (auto;call (_:true)).
     cut -> : Pr[SD1(A, S2(S)).main(tt) @ &m : EV (glob A) res] =
                  Pr[SD(Adv, S2(S)).main(tt) @ &m : EV (glob A) res].
       byequiv (_: ={glob A, glob S} ==> ={glob A, glob S, res}) => //.
       proc;inline *.
       rcondt{2} 8; first by intros &m1;swap 1 6;auto.
       by do ! (auto;call (_:true)).
     by apply (SDN.SD_conseq_abs S eps inv _ _ _ _ Adv &m EV).
   qed.
 
 
   lemma SD1_conseq_add eps (inv: glob S -> bool):
     hoare [S.init:true ==> inv (glob S)] =>
     hoare [S.sample1 : inv (glob S) ==> inv (glob S)] =>
     hoare [S.sample2 : inv (glob S) ==> inv (glob S)] =>
     (forall &m i, 
        inv (glob S){m} =>
        sum (fun (a:output), 
               `|Pr[S.sample1(i) @ &m : res = a ] - Pr[S.sample2(i) @ &m : res = a ]|) 
            (ISet.Finite.toFSet ISet.univ<:output>) <= 2%r * eps) =>
     forall &m (EV:glob A -> adv_output -> bool),
        Pr[SD1(A,S1(S)).main() @ &m : EV (glob A) res] <= 
         Pr[SD1(A,S2(S)).main() @ &m : EV (glob A) res] + eps.
    proof.
      intros H1 H2 H3 H4 &m EV; cut H5 := SD1_conseq_abs eps inv _ _ _ _ &m EV => //.
      smt.
    qed.

  end section.

end SD1query.


   



