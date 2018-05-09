(* * Symbols for variables and other objects *)

(* ** Imports *)
open Abbrevs
open Util
open Id
open Type

(* ** Typed symbols
 * ----------------------------------------------------------------------- *)

(* *** Definition
 * ----------------------------------------------------------------------- *)

module TypedSym = struct
  type t = {
    id    : Id.id;
    dom   : ty;
    codom : ty;
  }

  let hash os = Id.hash os.id
  let equal os1 os2 = Id.equal os1.id os2.id
  let compare x y = Id.tag x.id - Id.tag y.id

  type tt = t
  module Os = StructMake (struct
    type t = tt
    let tag = hash
  end)

  module M = Os.M
  module S = Os.S
  module H = Os.H

  let mk name dom codom = {
    id    = Id.mk name;
    dom   = dom;
    codom = codom;
  }

  let pp fmt os = F.fprintf fmt "%s" (Id.name os.id)

  let pp_long fmt os =
    F.fprintf fmt "%s : %a -> %a" (Id.name os.id) pp_ty os.dom pp_ty os.codom

  let to_string os = Id.name os.id
end

(* *** Oracle symbols
 * ----------------------------------------------------------------------- *)

module OrclSym : (module type of TypedSym) = TypedSym

(* *** Adversary procedure symbols
 * ----------------------------------------------------------------------- *)

module AdvSym : (module type of TypedSym) = TypedSym

(* *** Uninterpreted function symbols
 * ----------------------------------------------------------------------- *)

module FunSym : (module type of TypedSym) = TypedSym

(* *** Random oracle symbols
 * ----------------------------------------------------------------------- *)

module RoSym : (module type of TypedSym) = TypedSym

(* *** Map symbols
 * ----------------------------------------------------------------------- *)

module MapSym : (module type of TypedSym) = TypedSym

(* ** Bilinear map symbols
 * ----------------------------------------------------------------------- *)

module EmapSym = struct
  type t = {
    id      : Id.id;
    source1 : Groupvar.id;
    source2 : Groupvar.id;
    target  : Groupvar.id;
  }

  let hash es = Id.hash es.id
  let equal es1 es2 = Id.equal es1.id es2.id
  let compare x y = Id.tag x.id - Id.tag y.id

  type tt = t
  module Es = StructMake (struct
    type t = tt
    let tag = hash
  end)

  module M = Es.M
  module S = Es.S
  module H = Es.H

  let mk name source1 source2 target = {
    id      = Id.mk name;
    source1 = source1;
    source2 = source2;
    target  = target;
  }

  let pp fmt hs = F.fprintf fmt "%s" (Id.name hs.id)

  let name hs = Id.name hs.id
end

(* ** Permutation symbols
 * ----------------------------------------------------------------------- *)

module PermSym = struct
  (* We ensure that same id implies same dom. *)
  type t = {
    id  : Permvar.id;
    dom : ty;
  }

  let hash ps = Permvar.hash ps.id
  let equal ps1 ps2 = Permvar.equal ps1.id ps2.id
  let compare x y = Permvar.tag x.id - Permvar.tag y.id

  type tt = t
  module Ps = StructMake (struct
    type t = tt
    let tag = hash
  end)

  module M = Ps.M
  module S = Ps.S
  module H = Ps.H

  let mk s dom = { id = Permvar.mk s; dom = dom }
  let pp fmt hs = F.fprintf fmt "%s" (Permvar.name hs.id)

  let name hs = Permvar.name hs.id
end

(* ** Qualified symbols
 * ----------------------------------------------------------------------- *)

type 'a qual = Unqual | Qual of 'a

let map_qual f = function
  | Unqual -> Unqual
  | Qual x -> Qual (f x)

(* ** Variable symbols
 * ----------------------------------------------------------------------- *)

module VarSym = struct

  type t = {
    id   : id;
    qual : OrclSym.t qual; (* we allow qualified variables for eq-Hybrid-oracles *)
    ty   : ty;
  }

  let hash ps = Id.hash ps.id
  let equal vs1 vs2 = Id.equal vs1.id vs2.id
  let compare x y = Id.tag x.id - Id.tag y.id

  type tt = t
  module Ps = StructMake (struct
    type t = tt
    let tag = hash
  end)

  module M = Ps.M
  module S = Ps.S
  module H = Ps.H

  let mk name ty = { id = Id.mk name; qual = Unqual; ty = ty; }

  let mk_qual name qual ty = { id = Id.mk name; qual = qual; ty = ty; }

  let pp_tag fmt _t =
    pp_string fmt ""
    (* F.fprintf fmt ".%i" t *)

  let pp_qual ?qual:(qual=Unqual) fmt vs =
    let open Id in
    let qual_eq o =
      match qual with
      | Unqual  -> false
      | Qual o' -> OrclSym.equal o o'
    in
    match vs.qual with
    | Unqual ->
      F.fprintf fmt "%s%a" (name vs.id) pp_tag (tag vs.id)
    | Qual o when qual_eq o ->
      F.fprintf fmt "%s%a" (name vs.id) pp_tag (tag vs.id)
    | Qual q ->
      F.fprintf fmt "%s`%s%a" (name q.OrclSym.id) (name vs.id) pp_tag (tag vs.id)

  let pp fmt = pp_qual ~qual:Unqual fmt

  let to_string ps = Id.name ps.id

  let set_of_list l =
    L.fold_right
      (fun vs acc -> S.add vs acc)
      l
      S.empty
end
