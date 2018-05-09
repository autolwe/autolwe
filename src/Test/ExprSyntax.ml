open Expr
open Util

let g = mk_GGen
let (^:) a b = mk_GExp a b

let pi(i,e) = mk_Proj i e

let em(x,y) = mk_EMap x y

let fint n =
  if n = 0 then mk_FZ
  else if n > 0 then mk_FPlus (replicate n mk_FOne)
  else mk_FOpp (mk_FPlus (replicate n mk_FOne))

let fpow e n = mk_FMult (replicate n e)

let f1 = mk_FOne
let f0 = mk_FZ

let (/:) = mk_FDiv
let (-:) = mk_FMinus
let (+:) a b = mk_FPlus [a;b]
let ( *:) a b = mk_FMult [a;b]

let ( **: ) a b = mk_GMult [a;b]

let ifte a b c = mk_Ifte a b c

let tuple = mk_Tuple

let v = mk_V
