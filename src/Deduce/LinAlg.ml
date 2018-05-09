(* * Simple linear algebra (equation solving) over $F_2$. *)

(* ** Imports *)

open Abbrevs
open Util
open Array

(* ** Types and utility functions
 * ----------------------------------------------------------------------- *)

type col = int

type row = int

type solved =
    Pivot of row * col
  | Solved of (bool list) option

let cols m = length m.(0) - 1 (* the last column is the solution *)

let rows m = length m

let sol_col m = cols m

let _col_to_list m c =
  let res = ref [] in
  for r = rows m - 1 downto 0 do
    res := m.(r).(c)::!res
  done;
  !res

let pp_row_vec pp_entry fmt v =
  let entries = to_list v in
  F.fprintf fmt "[%a]" (pp_list ";" pp_entry) entries

let pp_matrix pp_entry fmt m =
  let rows = to_list m in
  F.fprintf fmt "@[<hov 1>[%a]@]" (pp_list ";@. " (pp_row_vec pp_entry)) rows

let iter_rows m f =
  for r = 0 to rows m - 1 do
    f r
  done

let _iter_cols m f =
  for c = 0 to cols m - 1 do
    f c
  done

let iter_cols_with_sol m f =
  for c = 0 to cols m do
    f c
  done

(* ** Equation solving
 * ----------------------------------------------------------------------- *)

(** Find all-zero columns and columns that only have one non-zero entry. *)
let classify_cols m =
  let col_is_z    = make (cols m + 1) false in (* i-th column is zero vector, also track for solution *)
  let col_is_std  = make (cols m + 1) false in (* i-th column is standard basis vector *)
  let std_has_col = make (rows m) None      in (* i-th standard basis vector is equal to given column of m *)
  iter_cols_with_sol m (fun c ->
    let one_rowidx = ref None in
    (try
       iter_rows m (fun r ->
         if m.(r).(c) = true then (
           if !one_rowidx = None
           then one_rowidx := Some(r)
           else raise Not_found (*i two non-zero entries i*)));
       match !one_rowidx with
       | None ->
         col_is_z.(c) <- true
       | Some(ri) ->
         if c <> sol_col m then (
           col_is_std.(c)   <- true;
           std_has_col.(ri) <- Some(c))
    with Not_found -> ()));
  (col_is_z, col_is_std, std_has_col)

let is_solved m =
  let (col_is_z,col_is_std,std_has_col) = classify_cols m in
  let module M = struct exception Found of solved end in
  try
    iter_cols_with_sol m (fun c ->
      if not (col_is_z.(c) || col_is_std.(c)) then (
        iter_rows m (fun r ->
          if m.(r).(c) = true && std_has_col.(r) = None then (
            if c <> sol_col m then raise (M.Found(Pivot(r,c)))
            else raise (M.Found(Solved None))))));
    let sol = make (cols m) false in
    iter_rows m (fun r ->
      if m.(r).(sol_col m) = true then
        match std_has_col.(r) with
        | Some c -> sol.(c) <- true
        | None -> failwith "impossible");
    Solved(Some (to_list sol))
  with
    M.Found sol -> sol

let add_row_to m r1 r2 =
  iter_cols_with_sol m (fun c ->
    m.(r1).(c) <- m.(r1).(c) <> m.(r2).(c))

let reduce_pivot m r c =
  iter_rows m (fun r' ->
    if r' <> r && m.(r').(c) = true then
      add_row_to m r' r)


let transpose m =
  let rownum = length m in
  let colnum = length m.(0) in
  let newrow = make rownum false in
  let m'     = make colnum newrow in
  iter_rows m' (fun r ->
    m'.(r) <- make rownum false;
    iter_cols_with_sol m' (fun c ->
      m'.(r).(c) <- m.(c).(r)));
  m'

let solve (m0 : (bool array) list) (b : bool array) =
  let m = of_list (m0 @ [b]) in
  let m = transpose m in
  let rec go () =
    match is_solved m with
    | Pivot(r,c) ->
      reduce_pivot m r c;
      go ()
    | Solved s -> s
  in go ()

(* ** Tests
 * ----------------------------------------------------------------------- *)

(* FIXME: move to separate file *)
let _test () =
  let m = make_matrix 3 2 false in
  let b = make 3 false in  

  (* e1 *)
  m.(0).(0) <- true;
  m.(1).(0) <- true;
  
  (* e2 *)
  m.(1).(1) <- true;
  m.(2).(1) <- true;

  (* e *)
  b.(0) <- true;
  b.(2) <- true;
  F.printf "%a%!\n\n" (pp_matrix (fun fmt b -> F.fprintf fmt "%i" (if b then 1 else 0)))  m;
  ignore (solve (to_list m) b);
  F.printf "%a%!\n\n" (pp_matrix (fun fmt b -> F.fprintf fmt "%i" (if b then 1 else 0)))  m
