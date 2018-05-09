(* * Nondeterministic computations (aka lazy lists) *)

(* ** Imports and logging*)
open Lazy
open Abbrevs
open Util

let mk_log level = mk_logger "Util.Nondet" level "nondet.ml"
let log_i = mk_log Bolt.Level.INFO

(* ** Nondeterminism Monad
 * ----------------------------------------------------------------------- *)

type 'a stream =
  | Nil  of (string lazy_t) option
  | Cons of 'a * ('a stream) lazy_t

type 'a nondet = 'a stream lazy_t

let mempty = lazy (Nil None)

let mfail ls = lazy (Nil (Some ls))

let ret a = lazy (Cons (a, mempty))

let guard pred =
  if pred then ret () else mempty

let sforce x =
  try
    force x
  with
  | Failure s ->
    failwith s
  | e ->
    let err = Printexc.to_string e in
    let bt = Printexc.get_backtrace () in
    log_i (lazy (F.sprintf "sforce: exception %s\n%s%!" err bt));
    Nil None

let rec mplus a b = from_fun (fun () ->
  match sforce a with
  | Cons (a1, a2) -> Cons (a1, mplus a2 b)
  | Nil _         -> sforce b)

let rec bind m f = from_fun (fun () ->
  match sforce m with
  | Nil s       -> Nil s
  | Cons (a, b) -> sforce (mplus (f a) (bind b f)))

let fmap f m = bind m (fun x -> ret (f x))

let run n m =
  let rec go n m acc =
    if n = 0 then List.rev acc
    else
      match sforce m with
      | Nil _       -> List.rev acc
      | Cons (a, b) -> go (pred n) b (a::acc)
  in
  go n m []

(* ** Useful functions
 * ----------------------------------------------------------------------- *)

let iter n m f =
  let rec go n m =
    if n = 0 then ()
    else
      match sforce m with
      | Nil _       -> ()
      | Cons (a, b) -> f a; go (pred n) b
  in
  go n m

let pull m =
  match sforce m with
  | Nil e       -> Left e
  | Cons (a, b) -> Right (a,b)

let first m =
  match sforce m with
  | Nil _       -> failwith "first: empty sequence"
  | Cons (a, _) -> a

let is_nil m =
  match sforce m with
  | Nil _       -> true
  | Cons (_, _) -> false

let sequence ms =
  let go m1 m2 =
    bind m1 (fun x ->
    bind m2 (fun xs ->
    ret (x::xs)))
  in
  List.fold_right go ms (ret [])

let mapM f ms = sequence (List.map f ms)

let foreachM ms f = mapM f ms

let rec msum ms =
  match ms with
  | m::ms -> mplus m (msum ms)
  | []    -> mempty

let rec mconcat ms =
  match ms with
  | m::ms -> mplus (ret m) (mconcat ms)
  | []    -> mempty

let (>>=) = bind

let pick_set k m0 =
  let rec go m k acc =
    guard (k <> 0) >>= fun _ ->
    match sforce m with
    | Nil _ -> ret acc
    | Cons(a,m') ->
      msum [ ret (a::acc)
           ; go m' (k-1) (a::acc)
           ; go m' k     acc ]
  in
  mplus (ret []) (go m0 k [])

let pick_set_exact k m0 =
  let rec go m k acc =
    if k = 0
    then ret acc
    else
      match sforce m with
      | Nil _ -> mempty
      | Cons(a,m') ->
        mplus
          (go m' (k-1) (a::acc))
          (go m' k     acc)
  in
  go m0 k []

let rec insertions left z right =
  mplus
    (ret (L.rev_append left (z::right)))
    (match right with
     | []    -> mempty
     | x::xs -> insertions (x::left) z xs)

let rec permutations xs =
  match xs with
  | []    -> ret []
  | x::xs ->
    permutations xs >>= fun xs ->
    insertions [] x xs

let cart m1 m2 =
  m1 >>= fun x1 ->
  m2 >>= fun x2 ->
  ret (x1,x2)

let prod m = cart m m

let rec ncart ms =
  match ms with
  | []    -> ret []
  | m::ms ->
    m >>= fun x ->
    ncart ms >>= fun xs ->
    ret (x::xs)

let nprod m n =
  let rec go n acc =
    if n <= 0 then ret acc
    else m >>= fun x -> go (n-1) (x::acc)
  in
  go n []
