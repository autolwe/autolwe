(* * Types (hashconsed) *)

(* ** Imports *)
open Abbrevs
open Util

(* ** Identifiers *)

module Lenvar : (module type of Id) = Id

module Tysym : (module type of Id) = Id

module Groupvar : (module type of Id) = Id

module Permvar : (module type of Id) = Id


(* ** Types and type nodes *)

type mdim =
  | MDBase of Lenvar.id
  | MDPlus of mdim * mdim

let rec mdim_equal d1 d2 = match d1,d2 with
| MDBase(a), MDBase(b) ->  (Lenvar.name a) = (Lenvar.name b)
| MDPlus(a,b), MDPlus(c,d) -> (mdim_equal a c) && (mdim_equal b d)
                              || ( (mdim_equal a d) && (mdim_equal b c))
| _, _ -> false

let rec mdim_str d = match d with
| MDBase (a) -> Lenvar.name a
| MDPlus (a,b) -> (mdim_str a) ^ "+" ^ (mdim_str b)

let pp_mdim = mdim_str

let rec mdim_hash d = match d with
| MDBase(a) -> Lenvar.hash a
| MDPlus(a,b) -> hcomb (mdim_hash a) (mdim_hash b)


type ty = {
  ty_node : ty_node;
  ty_tag : int
}
and ty_node =
  | BS of Lenvar.id
  | Bool
  | Mat of (mdim * mdim)
  | List of (mdim * ty)
  | G of Groupvar.id
  | TySym of Tysym.id
  | Fq
  | Prod of ty list
  | Int

(* ** Equality, hashing, and hash consing *)

let equal_mat_ty t1 t2 =
    match t1.ty_node, t2.ty_node with
    | Mat (a,b), Mat(c,d) -> mdim_equal a c && mdim_equal b d
    | _ -> false

let equal_ty t1 t2 =
    match t1.ty_node with
    | Mat _ -> equal_mat_ty t1 t2
    | _ -> (t1 == t2)

let matmult_compat_ty t1 t2 = 
    match t1.ty_node with
    | Mat (_,b) -> (match t2.ty_node with
                    | Mat (c,_) -> mdim_equal b c 
                    | _ -> false)
    | _ -> false

let listmult_compat_ty t1 t2 =
    match t1.ty_node with
    | List (d1, t) -> (match t2.ty_node with
                      | List (d2, tp) -> (mdim_equal d1 d2) &&
                      (matmult_compat_ty t tp)
                      | _ -> false)
    | _ -> false

let concat_compat_ty t1 t2 =
    match t1.ty_node with
    | Mat (a,_) -> (match t2.ty_node with
                    | Mat (c,_) -> mdim_equal a c
                    | _ -> false)
    | _ -> false

let listconcat_compat_ty t1 t2 =
    match t1.ty_node with
    | List (d1, t) -> (match t2.ty_node with
                      | List (d2, tp) -> (mdim_equal d1 d2) &&
                      (concat_compat_ty t tp)
                      | _ -> false)
    | _ -> false

let split_compat t =
    match t.ty_node with
    | Mat (_,a) -> (match a with 
                    | MDBase(_) -> false
                    | MDPlus(_) -> true)
    | _ -> false

let get_split_dim t =
    match t.ty_node with
    | Mat (_,a) -> (match a with
                    | MDPlus(d1,d2) -> (d1,d2)
                    | _ -> assert false)
    | _ -> assert false

let dim_of_mat t =
    match t.ty_node with
    | Mat (x,y) -> (x,y)
    | _ ->
            assert false

let hash_ty t = t.ty_tag
let compare_ty t1 t2 = t1.ty_tag - t2.ty_tag

let get_list_ty t =
    match t.ty_node with
    | List p -> p
    | _ -> assert false

let matmult_get_dim t1 t2 =
    match t1.ty_node with
    | Mat (a,_) -> (match t2.ty_node with
                    | Mat (_,d) ->  (a,d)
                    | _ -> assert false)
    | _ -> assert false


module Hsty = Hashcons.Make (struct
  type t = ty

  let equal t1 t2 =
    match t1.ty_node, t2.ty_node with
    | BS lv1, BS lv2                 -> Lenvar.equal lv1 lv2
    | Bool, Bool                     -> true
    | G gv1, G gv2                   -> Groupvar.equal gv1 gv2
    | TySym ts1, TySym ts2           -> Tysym.equal ts1 ts2
    | Fq, Fq                         -> true
    | Mat (a,b), Mat (c,d)           -> (mdim_equal a c) && (mdim_equal b d)
    | List (d,tp), List (d2, tp2)    -> (mdim_equal d d2) && (equal_ty tp tp2)
    | Prod ts1, Prod ts2             -> list_eq_for_all2 equal_ty ts1 ts2
    | _                              -> false

  let rec hash t =
    match t.ty_node with
    | BS lv         -> hcomb 1 (Lenvar.hash lv)
    | Bool          -> 2
    | G gv          -> hcomb 3 (Groupvar.hash gv)
    | TySym gv      -> hcomb 4 (Tysym.hash gv)
    | Fq            -> 5
    | Prod ts       -> hcomb_l hash_ty 6 ts
    | Mat (a,b)     -> hcomb 8 (hcomb (mdim_hash a) (mdim_hash b))  
    | Int           -> 7
    | List (d, tp)   -> hcomb 9 (hcomb (mdim_hash d) (hash tp))

  let tag n t = { t with ty_tag = n }
end)

(** Create [Map], [Set], and [Hashtbl] modules for types. *)
module Ty = StructMake (struct
  type t = ty
  let tag = hash_ty
end)
module Mty = Ty.M
module Sty = Ty.S
module Hty = Ty.H

(* ** Constructor functions *)

let mk_ty n = Hsty.hashcons {
  ty_node = n;
  ty_tag  = (-1)
}

let mk_BS lv = mk_ty (BS lv)

let mk_G gv = mk_ty (G gv)

let mk_Mat n m = mk_ty (Mat (n,m)) 

let mk_List d t = mk_ty (List (d,t))

let mk_TySym ts = mk_ty (TySym ts)

let mk_Fq = mk_ty Fq

let mk_Bool = mk_ty Bool

let mk_Int = mk_ty Int

let mk_Prod tys =
  match tys with
  | [t] -> t
  | _   -> mk_ty (Prod tys)

(* ** Indicator and destructor functions *)

let is_G ty = match ty.ty_node with
  | G _ -> true
  | _   -> false

let is_BS ty = match ty.ty_node with
  | BS _ -> true
  | _   -> false
let is_Fq ty = match ty.ty_node with
  | Fq -> true
  | _  -> false

let is_Prod ty = match ty.ty_node with
  | Prod _ -> true
  | _      -> false


let is_List ty = match ty.ty_node with
  | List _ -> true
  | _ -> false


let is_Mat ty = match ty.ty_node with
  | Mat _ -> true
  | _ -> false

let is_ListOfTy t1 ty = 
    match ty.ty_node with
    | List (_, t2) -> equal_ty t1 t2
    | _ -> false

let is_MatList ty = match ty.ty_node with
  | List (_, t) -> is_Mat t
  | _ -> false

let is_Mat_splittable ty = match ty.ty_node with
  | Mat (_, MDPlus(_)) -> true
  | _ -> false

let destr_G_exn ty =
  match ty.ty_node with
  | G gv -> gv
  | _    -> raise Not_found

let destr_BS_exn ty =
  match ty.ty_node with
  | BS lv -> lv
  | _     -> raise Not_found


let destr_Prod_exn ty =
  match ty.ty_node with
  | Prod ts -> ts
  | _       -> raise Not_found

let destr_Prod ty =
  match ty.ty_node with
  | Prod ts -> Some ts
  | _       -> None

(* ** Pretty printing *)

let pp_group fmt gv =
  if Groupvar.name gv = ""
  then F.fprintf fmt "G"
  else F.fprintf fmt "G_%s" (Groupvar.name gv)




let rec pp_ty fmt ty =
  match ty.ty_node with
  | BS lv             -> F.fprintf fmt "BS_%s" (Lenvar.name lv)
  | Mat (a,b)         -> F.fprintf fmt "Matrix_{%s}" ((mdim_str a) ^ "," ^
  (mdim_str b))
  | Bool              -> F.fprintf fmt "Bool"
  | List (d, tp)      -> F.fprintf fmt "List_{%s} %a" (mdim_str d) pp_ty tp
  | Fq                -> F.fprintf fmt "Fq"
  | TySym ts          -> F.fprintf fmt "%s" (Tysym.name ts)
  | Prod ts           -> F.fprintf fmt "(%a)" (pp_list " * " pp_ty) ts
  | Int               -> F.fprintf fmt "Int"
  | G gv ->
    if Groupvar.name gv = ""
    then F.fprintf fmt "G"
    else F.fprintf fmt "G_%s" (Groupvar.name gv)
