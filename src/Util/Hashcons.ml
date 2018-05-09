(* * Hash consing of values. *)

(* Documented in mli file. *)
module type HashedType = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val tag : int -> t -> t
end

(* Documented in mli file *)
module type S = sig
  type t
  val hashcons : t -> t
end

module Make(H : HashedType) : (S with type t = H.t) = struct
  type t = H.t

  module WH = Hashtbl.Make (H)

  let next_tag = ref 0

  let htable = WH.create 5003

  let merge tbl d =
    try WH.find tbl d
    with Not_found ->
      WH.add tbl d d;
      d

  let hashcons d =
    let d = H.tag !next_tag d in
    let o = merge htable d in
    if o == d then incr next_tag;
    o
end

let combine acc n = n * 65599 + acc

let combine2 acc n1 n2 = combine acc (combine n1 n2)

let combine_list f = List.fold_left (fun acc x -> combine acc (f x))

let combine_hashes = function
  | [] -> assert false
  | h::hs -> List.fold_left (fun acc h -> combine acc h) h hs
