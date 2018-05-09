require import Option.
require import Real.
require import Int.
require Distr.
type U.
op t1 : U -> bool.
op t2 : U -> bool.
op q : int.

module type OT = {
  proc o (_:U) : bool
}.

module type Adv (O:OT) = {
  proc a1 () : unit {O.o}
  proc a2 () : unit {}
}.

module C = { 
  var c : int
  proc init () : unit = {
    c = 0;
  }
  proc incr () : unit = {
    c = c + 1;
  }
}.

module Orclc(O:OT) = {
  proc o(u:U) : bool = {
    var r : bool;
    r = false;
    if (C.c < q) { 
      r = O.o(u);
      C.incr();
    }
    return r;
  }
}.

module M (O:OT, A:Adv) = {
  module Oc = Orclc(O)
  module A = A(Oc)
  proc main () : unit = {
    C.init();
    A.a1();
    A.a2();
  }
}.

module Ot1 = {
  proc o (u:U) : bool = { return t1 u; }
}.

module Ot2 = {
  proc o (u:U) : bool = { return t2 u; }
}.

module type AdvU(O:OT) = {
  proc a1 () : U option {O.o}
}.
  
module B(A:Adv) = {
  var i : int
  var gu : U option
  module O = {
    proc o (u:U) : bool = {
      var r : bool;
      if (C.c = i) gu = Some u;
      r = Ot2.o(u);
      return r;
    }
  }
  module A = A(Orclc(O))

  proc main () : bool = {
    C.init();
    i = $[0..q-1];
    gu = None;
    A.a1();
    return  (gu <> None && t1 (oget gu) <> t2 (oget gu));
  }
}.

axiom add_test (A<:Adv{C,B}) &m (E:glob A -> bool): 
    Pr[M(Ot1, A).main() @ &m : E (glob A)] <= 
       Pr[M(Ot2, A).main() @ &m : E (glob A)] + 
  q%r * Pr[B(A).main() @ &m : res].


  

 
      
      



