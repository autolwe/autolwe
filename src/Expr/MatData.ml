open MatSig
open Expr
open Type

module Mat : MATDATA = struct
    type elt = expr
    type shape = mdim * mdim
    let pp_shape (s1,s2) = "("^(pp_mdim s1)^","^(pp_mdim s2)^")"
    type mat =
        | MPlus of shape * mat list
        | MOpp of mat
        | MMult of mat * mat
        | MTrans of mat
        | MConcat of mat * mat
        | MSplitLeft of mat
        | MSplitRight of mat
        | MId of shape
        | MZero of shape
        | MBase of elt
    let mult_shape p1 p2 = (fst p1, snd p2)
    let concat_shape p1 p2 = (fst p1, Type.MDPlus (snd p1, snd p2))
    let sl_shape p = match p with | (p1, MDPlus (p2, _)) -> (p1, p2) | _ -> assert false
    let sr_shape p = match p with | (p1, MDPlus (_, p2)) -> (p1, p2) | _ ->
        assert false
    let trans_shape (a,b) = (b,a)
    let elt_eq a b = equal_expr a b
    let shape_eq p1 p2 = Type.mdim_equal (fst p1) (fst p2) && Type.mdim_equal (snd p1) (snd p2)
    let shape_of_elt e = Type.dim_of_mat e.e_ty
    let rec mat_of_expr e =
        match e.e_node with
        | App(MatMult, [e1;e2]) -> MMult (mat_of_expr e1, mat_of_expr e2)
        | App(MatOpp, [e]) -> MOpp (mat_of_expr e)
        | App(MatTrans, [e]) -> MTrans (mat_of_expr e)
        | App(MatConcat, [e1;e2]) -> MConcat (mat_of_expr e1, mat_of_expr e2)
        | App(MatSplitLeft, [e]) -> MSplitLeft (mat_of_expr e)
        | App(MatSplitRight, [e]) -> MSplitRight (mat_of_expr e)
        | Nary(MatPlus, es) -> MPlus (shape_of_elt (List.hd es), List.map mat_of_expr es)
        | Cnst(MatZero) -> let p = Type.dim_of_mat (e.e_ty) in MZero p
        | Cnst(MatId) -> MId (Type.dim_of_mat (e.e_ty))
        | _ -> MBase e
    let rec expr_of_mat m =
        match m with
        | MPlus (_,ms) -> 
                mk_MatPlus (List.map expr_of_mat ms)
        | MOpp m -> mk_MatOpp (expr_of_mat m)
        | MMult (m1,m2) -> mk_MatMult (expr_of_mat m1) (expr_of_mat m2)
        | MTrans m -> mk_MatTrans (expr_of_mat m)
        | MConcat (m1,m2) -> mk_MatConcat (expr_of_mat m1) (expr_of_mat m2)
        | MSplitLeft m -> mk_MatSplitLeft (expr_of_mat m)
        | MSplitRight m -> mk_MatSplitRight (expr_of_mat m)
        | MZero p -> mk_MatZero (fst p) (snd p)
        | MId p -> mk_MatId (fst p) (snd p)
        | MBase e -> e

    let extra_rewr m = m

    let shape_of_expr e =
        Type.dim_of_mat e.e_ty


    let default_shape = (MDBase (Lenvar.mk "1"), MDBase (Lenvar.mk "1"))
    let mult_shape_compat m1 m2 =
        mdim_equal (snd m1) (fst m2)
    let neg_shape = (MDBase (Lenvar.mk "-1"), MDBase (Lenvar.mk "-1"))

    let expr_of_elt e = e
    let elt_of_expr e = e

    let id_of_shape (a,b) = mk_MatId a b
    let shape_splittable (a,b) =
        match b with
        | MDPlus _ -> true
        | MDBase _ -> false
    let shape_leftsplittable (a,b) =
        match a with
        | MDPlus _ -> true
        | MDBase _ -> false

    let all_constants_of_shape s =
        let shape_id t = if Type.mdim_equal (fst t) (snd t) then [mk_MatId (fst t) (snd t)] else [] in
        let shape_zero t = [mk_MatZero (fst t) (snd t)] in

        let rec go s t =
            (shape_id (s,t)) @ (shape_zero (s,t)) @ (
                match s with
                | MDPlus (s1, s2) ->
                        (match t with
                         | MDPlus (t1, t2) ->
                                 (go s1 (MDPlus (t1, t2))) @
                                 (go s1 t1) @
                                 (go s1 t2) @
                                 (go s2 (MDPlus (t1, t2))) @
                                 (go s2 t1) @
                                 (go s2 t2) @
                                 (go (MDPlus (s1, s2)) t1) @
                                 (go (MDPlus (s1, s2)) t2)
                         | MDBase _ ->
                                 (go s1 t) @
                                 (go s2 t))
                | MDBase _ ->
                        (match t with
                         | MDPlus (t1, t2) ->
                                 (go s t1) @
                                 (go s t2)
                         | MDBase _ ->
                                 []))
       in

       go (fst s) (snd s)


  end

let rec pp_mat : Mat.mat -> string = function
    | Mat.MPlus (_, ms) -> String.concat " + " (List.map pp_mat ms)
    | Mat.MOpp m -> "-" ^ (pp_mat m)
    | Mat.MMult (m1,m2) -> (pp_mat m1) ^ "*" ^ (pp_mat m2)
    | Mat.MTrans m -> "tr " ^ (pp_mat m)
    | Mat.MConcat (m1,m2) -> (pp_mat m1) ^ " || " ^ (pp_mat m2)
    | Mat.MSplitLeft m -> "sl " ^ (pp_mat m)
    | Mat.MSplitRight m -> "sr " ^ (pp_mat m)
    | Mat.MId _ -> "1"
    | Mat.MZero _ -> "0"
    | Mat.MBase e -> "base"


module ListMat : MATDATA = struct
    type shape = mdim * mdim * mdim
    let pp_shape (s1,s2,s3) =
        "("^(pp_mdim s1)^","^(pp_mdim s2)^","^(pp_mdim s3)^")"
    type elt = LBase of expr | LOf of mdim * expr (* LOf only for embedded mats. *)
    type mat =
        | MPlus of shape * mat list
        | MOpp of mat
        | MMult of mat * mat
        | MTrans of mat
        | MConcat of mat * mat
        | MSplitLeft of mat
        | MSplitRight of mat
        | MId of shape
        | MZero of shape
        | MBase of elt

    let shape_splittable (_,_,f) = match f with | MDPlus _ -> true | MDBase _ ->
        false
    let shape_leftsplittable (_,f,_) = match f with | MDPlus _ -> true | MDBase _ ->
        false

    let mult_shape (a,b,_) (_,_,f) = (a, b, f)
    let concat_shape (a,b,c) (_, _, d) = (a, b, MDPlus (c,d))
    let sl_shape (a,b,c) = match c with
        | MDPlus (e, _) -> (a,b,e)
        | _ -> assert false
    let sr_shape (a,b,c) = match c with
        | MDPlus (_, e) -> (a,b,e)
        | _ -> assert false
    let trans_shape (a,b,c) = (a,c,b)

    let elt_eq e1 e2 =
        match e1,e2 with
        | LBase a, LBase b -> equal_expr a b
        | LOf (a,b), LOf (c,d) -> mdim_equal a c && equal_expr b d
        | _, _ -> false

    let shape_eq (a,b,c) (d,e,f) =
        mdim_equal a d &&
        mdim_equal b e &&
        mdim_equal c f

    let shape_of_elt e =
        match e with
        | LBase e -> 
                     let (a,f) = ensure_list_ty e.e_ty "shapeofelt" in
                     let (b,c) = dim_of_mat f in
                     (a,b,c)
        | LOf (a,t) -> let (b,c) = dim_of_mat (t.e_ty) in (a,b,c)


    let rec mat_of_expr e =
        match e.e_node with
        | App(ListOp MatMult, [e1;e2]) -> MMult (mat_of_expr e1, mat_of_expr e2)
        | App(ListOp MatOpp, [e]) -> MOpp (mat_of_expr e)
        | App(ListOp MatTrans, [e]) -> MTrans (mat_of_expr e)
        | App(ListOp MatConcat, [e1;e2]) -> MConcat (mat_of_expr e1, mat_of_expr e2)
        | App(ListOp MatSplitLeft, [e]) -> MSplitLeft (mat_of_expr e)
        | App(ListOp MatSplitRight, [e]) -> MSplitRight (mat_of_expr e)
        | Nary(ListNop MatPlus, es) -> 
                let (a,f) = ensure_list_ty (List.hd es).e_ty "matofexpr_matplus" in
                let (b,c) = dim_of_mat f in
                MPlus ((a,b,c), List.map mat_of_expr es)
        | App(ListOf, [e']) -> 
                (match e'.e_node with
                | Cnst (MatZero) -> let (a,f) = ensure_list_ty e.e_ty "matofexpr_listof" in
                                    let (b,c) = dim_of_mat f in MZero (a,b,c)
                | Cnst (MatId) ->
                    let (a,f) = ensure_list_ty e.e_ty "matofexpr_listof" in
                    let (b,c) = dim_of_mat f in MId (a,b,c)
                | _ -> 
                    match e'.e_ty.ty_node with
                    | Mat _ ->
                        let (a,_) = ensure_list_ty e.e_ty "matofexpr_listof" in    
                        MBase (LOf (a, e')))
                    | _ -> MBase (LBase e)
        | _ -> MBase (LBase e)

    let rec expr_of_mat m = 
        match m with
        | MPlus (_,xs) -> mk_ListNop MatPlus (List.map expr_of_mat xs)
        | MOpp x -> mk_ListMatOpp (expr_of_mat x)
        | MMult (x,y) -> mk_ListMatMult (expr_of_mat x) (expr_of_mat y)
        | MTrans x -> mk_ListMatTrans (expr_of_mat x)
        | MConcat (x,y) -> mk_ListMatConcat (expr_of_mat x) (expr_of_mat y)
        | MSplitLeft x -> mk_ListMatSplitLeft (expr_of_mat x)
        | MSplitRight x -> mk_ListMatSplitRight (expr_of_mat x)
        | MId (a,b,c) -> mk_ListOf a (mk_MatId b c)
        | MZero (a,b,c) -> mk_ListOf a (mk_MatZero b c)
        | MBase (LOf (d,e)) -> mk_ListOf d e
        | MBase (LBase e) -> e

    (* [a + b] -> [a] + [b] *)
    (* [a * b] -> [a] * [b] *)
    (* [tr x] -> tr [x] *)
    (* [a || b] -> [a] || [b] *)
    let extra_rewr m =
        match m with
        | MBase (LOf (d, e)) ->
                (match e.e_node with
                | Nary(MatPlus, es) -> 
                        let (b,c) = dim_of_mat (List.hd es).e_ty in
                        MPlus ((d,b,c), List.map (fun x -> MBase (LOf (d, x))) es)
                | App(MatMult, [e1;e2]) ->
                        MMult (MBase (LOf (d, e1)), MBase (LOf (d, e2)))
                | App(MatTrans, [e1]) ->
                        MTrans (MBase (LOf (d, e1)))
                | App (MatConcat, [e1;e2]) ->
                        MConcat (MBase (LOf (d, e1)), MBase (LOf (d,e2)))
                | App (MatSplitRight, [e1]) ->
                        MSplitRight (MBase (LOf (d, e1)))
                | App (MatSplitLeft, [e1]) ->
                        MSplitLeft (MBase (LOf (d, e1)))
                | App (MatOpp, [e1]) ->
                        MOpp (MBase (LOf (d, e1)))
                | _ -> m)
        | _ -> m

    let shape_of_expr e = 
        let (a,f) = ensure_list_ty e.e_ty "shapeofexpr" in
        let (b,c) = dim_of_mat f in
        (a,b,c)


    let default_shape = (MDBase (Lenvar.mk "1"), MDBase (Lenvar.mk "1"), MDBase (Lenvar.mk "1"))
    let mult_shape_compat (d1,_,n) (d2,m,_) =
        mdim_equal d1 d2 &&
        mdim_equal n m
    let neg_shape = (MDBase (Lenvar.mk "-1"), MDBase (Lenvar.mk "-1"), MDBase (Lenvar.mk "-1"))

    let expr_of_elt = function
        | LBase e -> e
        | LOf (d,e) -> mk_ListOf d e

    let elt_of_expr e = LBase e

    let id_of_shape (a,b,c) = mk_ListOf a (mk_MatId b c)

    let all_constants_of_shape (d,dx,dy) = 
        let shape_id (t1,t2,t3) = if Type.mdim_equal t2 t3 then [mk_ListOf t1 (mk_MatId t2 t3)] else [] in
        let shape_zero (t1,t2,t3) = [mk_ListOf t1 (mk_MatZero t2 t3)] in
        
        let rec go s t =
            (shape_id (d,s,t)) @ (shape_zero (d,s,t)) @ (
                match s with
                | MDPlus (s1, s2) ->
                        (match t with
                         | MDPlus (t1, t2) ->
                                 (go s1 (MDPlus (t1, t2))) @
                                 (go s1 t1) @
                                 (go s1 t2) @
                                 (go s2 (MDPlus (t1, t2))) @
                                 (go s2 t1) @
                                 (go s2 t2) @
                                 (go (MDPlus (s1, s2)) t1) @
                                 (go (MDPlus (s1, s2)) t2)
                         | MDBase _ ->
                                 (go s1 t) @
                                 (go s2 t))
                | MDBase _ ->
                        (match t with
                         | MDPlus (t1, t2) ->
                                 (go s t1) @
                                 (go s t2)
                         | MDBase _ ->
                                 []))
       in
       go dx dy

end

