(* * Utility functions
 * This module defines types tagged with [int]s, some convenience functor
 * applications for maps, sets, hashtables, and some convenience functions
 * for lists and pretty printing.
 *)

open Abbrevs

(* ** Convenience Functors
 * ----------------------------------------------------------------------- *)

module type Tagged = sig
  type t
  val tag : t -> int
end

module type OrderedHash = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHash (X : Tagged) : OrderedHash with type t = X.t = struct
  type t = X.t
  let hash t = X.tag t
  let equal t1 t2 = X.tag t1 = X.tag t2
  let compare t1 t2 = Pervasives.compare (X.tag t1) (X.tag t2)
end

module StructMake (X : Tagged) = struct
  module T = OrderedHash(X)
  module M = Map.Make(T)
  module S = Set.Make(T)
  module H = Hashtbl.Make(T)
end

module Ints = StructMake (struct
  type t = int
  let tag x = x
end)

module Mint = Ints.M
module Sint = Ints.S
module Hint = Ints.H

module Mstring = Map.Make(String)
module Sstring = Set.Make(String)

(* ** Misc functions
 * ----------------------------------------------------------------------- *)

let fixme s = failwith ("FIXME: "^s)

let unique_int () = Oo.id (object end)

let exc_to_opt f = try Some (f ()) with _ -> None

let swap (x,y) = (y,x)

let compare_on f x y = compare (f x) (f y)

let eq_on f x y = f x = f y

let input_file file_name =
  let in_channel = open_in file_name in
  let rec go lines =
    try
      let l = input_line in_channel in
      go (l :: lines)
    with
      End_of_file -> lines
  in
  let lines = go [] in
  let _ = close_in_noerr in_channel in
  String.concat "\n" (List.rev lines)

let output_file file_name content =
  let out_channel = open_out file_name in
  output_string out_channel content;
  close_out_noerr out_channel

let append_file file_name content =
  let s = input_file file_name in
  output_file file_name (s^content)

let assert_msg b m = if not b then failwith m

type ('a,'b) either = Left of 'a | Right of 'b

type direction = LeftToRight | RightToLeft

let string_of_dir = function
  | LeftToRight -> "->"
  | RightToLeft -> "<-"

let id x = x

(* ** List functions
 * ----------------------------------------------------------------------- *)

let find_at f l =
  let i = ref 0 in
  let t a = if f a then true else (incr i; false) in
  ignore (List.find t l);
  !i

let list_eq_for_all2 f l1 l2 =
  try List.for_all2 f l1 l2 with _ -> false

let smart_map f l =
  let rec aux r l' =
    match l' with
    | [] -> l
    | hd::tl ->
        let hd' = f hd in
        if hd == hd' then aux (hd::r) tl
        else List.rev_append r (hd' :: List.map f tl) in
  aux [] l

let split_n i0 l =
  assert (i0 >= 0);
  let rec aux i r l =
    match l with
    | [] -> failwith (Printf.sprintf "split_n: invalid index %i" i0)
    | x::xs ->
      if i = 0 then r,x,xs
      else aux (i-1) (x::r) xs
  in
  aux i0 [] l

let cut_n i0 l =
  let rec aux i r l =
    match  l with
    | _ when i <= 0 -> r, l
    | [] -> failwith (Printf.sprintf "cut_n: invalid index %i" i0)
    | a::l -> aux (i-1) (a::r) l
  in
  aux i0 [] l

let list_from_to i j =
  let rec go aux i = if i >= j then aux else go (i::aux) (i+1)
  in List.rev (go [] i)

let rec replicate_r acc i x =
  if i <= 0 then acc
  else replicate_r (x::acc) (i-1) x

let replicate i x = replicate_r [] i x

let lefts l =
  let rec go acc xs = match xs with
    | Left(x)::xs  -> go (x::acc) xs
    | Right(_)::xs -> go acc      xs
    | [] -> List.rev acc
  in go [] l

let rights l =
  let rec go acc xs = match xs with
    | Left(_)::xs  -> go acc      xs
    | Right(x)::xs -> go (x::acc) xs
    | [] -> List.rev acc
  in go [] l

let lefts_rights l =
  let rec go lacc racc xs = match xs with
    | Left(x)::xs  -> go (x::lacc) racc      xs
    | Right(x)::xs -> go lacc      (x::racc) xs
    | []           -> (List.rev lacc, List.rev racc)
  in go [] [] l

let cat_Some l =
  let rec go acc = function
    | Some(x)::xs  -> go (x::acc) xs
    | None::xs     -> go acc      xs
    | []           -> List.rev acc
  in
  go [] l

let conc_map f xs =
  L.concat (L.map f xs)

let map_accum f init xs =
  let rec go acc res = function
    | []    -> (acc,L.rev res)
    | x::xs ->
      let (acc,y) = f acc x in
      go acc (y::res) xs
  in
  go init [] xs

let move_front p xs = let (u,v) = L.partition p xs in u @ v

let equal_list eq xs0 ys0 =
  let rec go xs ys =
    match xs,ys with
    | [], []       -> true
    | x::xs, y::ys -> eq x y && go xs ys
    | _            -> assert false
  in
  (L.length xs0 = L.length ys0) && go xs0 ys0

let compare_list cmp xs0 ys0 =
  let rec go xs ys =
    match xs, ys with
    | [], []       -> 0
    | x::xs, y::ys ->
      let d = cmp x y in
      if d <> 0 then d
      else go xs ys
    | _            -> assert false
  in
  let d = L.length xs0 - L.length ys0 in
  if d > 0 then 1
  else if d < 0 then -1
  else go xs0 ys0

let equal_pair eq1 eq2 (x1,x2) (y1,y2) =
  eq1 x1 y1 && eq2 x2 y2

let compare_pair cmp1 cmp2 (x1,x2) (y1,y2) =
  let r1 = cmp1 x1 y1 in
  if r1 <> 0 then r1
  else cmp2 x2 y2

let num_list l = L.mapi (fun i a -> i+1,a) l

let drop_last n xs = L.rev xs |> BatList.drop n |> L.rev

(* ** String functions
 * ----------------------------------------------------------------------- *)

let splitn_by s f =
  let rec go acc i len =
    if i + len < String.length s then (
      if f s (i+len)
        then go ((String.sub s i len)::acc) (i+len+1) 0
        else go acc i (len + 1)
    ) else (
      (String.sub s i len)::acc
    )
  in
  List.rev (go [] 0 0)

let string_find_from s t from =
  let len_s = String.length s in
  let len_t = String.length t in
  let rec go i =
    if i < len_s && len_s - i >= len_t then (
      if String.sub s i len_t = t
        then Some i
        else go (i+1)
    ) else (
      None
    )
  in go from

let string_rfind_from s t from =
  let len_s = String.length s in
  let len_t = String.length t in
  let rec go i =
    if i >= 0 then (
      if len_s - i >= len_t && String.sub s i len_t = t
        then Some i
        else go (i-1)
    ) else (
      None
    )
  in go from

let split s sep =
  try Some (BatString.split s ~by:sep)
  with Not_found -> None

(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let pp_list_c pe = (pp_list "," pe)
let pp_list_s = pp_list_c (fun fmt -> F.fprintf fmt "%s")

let pp_opt pp fmt o =
  match o with
  | Some x -> pp fmt x
  | None    -> F.fprintf fmt "--"

let pp_around before after pp fmt x =
  F.fprintf fmt "%s%a%s" before pp x after

let pp_string fmt s = F.fprintf fmt "%s" s

let pp_int fmt i = F.fprintf fmt "%i" i

let pp_if c pp1 pp2 fmt x =
  if c then pp1 fmt x else pp2 fmt x

let pp_pair pp1 pp2 fmt (a,b) =
  F.fprintf fmt "(%a,%a)" pp1 a pp2 b

let fsprintf fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      (Buffer.contents buf))
    fbuf fmt

(* ** Logging and exceptions for Logic module
 * ----------------------------------------------------------------------- *)

let no_log = ref false

let my_log_buf = Buffer.create 127

let get_buffer_log () =
  let res = Buffer.contents my_log_buf in
  Buffer.clear my_log_buf;
  res

let mk_logger _logger_name _level _file ls =
  if not !no_log then
    Buffer.add_string my_log_buf (Lazy.force ls);
    Buffer.add_string my_log_buf "\n"
   (*
    let lines = BatString.nsplit (Lazy.force ls) ~by:"\n" in
    L.iter
      (fun s -> Bolt.Logger.log logger_name level ~file s)
      lines
   *)

let log_ig _ls = ()

let log = mk_logger "Tacerror" Bolt.Level.INFO "Tacerror"

exception Invalid_rule of string

let tacerror fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      log (lazy s);
      raise (Invalid_rule s))
    fbuf fmt

let fail_opt ox s =
  match ox with
  | Some x -> x
  | None   -> tacerror "%s" s
