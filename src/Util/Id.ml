(* * The Id module. *)

open Util
open Abbrevs

type id = {
  name_ : string;
  tag_ : int;
}

let name i = i.name_

let tag i = i.tag_

let pp fmt i =
  if true || i.tag_ = 0 then
    F.fprintf fmt "%s" i.name_
  else
    F.fprintf fmt "%s.%i" i.name_ i.tag_

let equal : id -> id -> bool = (==)
let hash i = i.tag_
let compare x y = Pervasives.compare (hash x) (hash y)

let mk s = { name_ = s; tag_ = unique_int ()}

module SM = StructMake (struct
  type t = id
  let  tag i = i.tag_
end)

module M = SM.M
module S = SM.S
module H = SM.H
