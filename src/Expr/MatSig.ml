open Expr
open List
open Util



let rec remove_by (f : 'a -> bool) (xs : 'a list) =
    match xs with
    | [] -> (None, [])
    | (x :: xs') ->
            if f x then (Some x, xs') else let p = remove_by f xs' in (fst p, x :: (snd p))
           
let rec is_bijection_by (comp : 'a -> 'a -> bool) (xs : 'a list) (ys : 'a list) =
    match xs with
    | [] -> (match ys with | [] -> true | _ -> false)
    | x :: xs' ->
            (match (remove_by (comp x) ys) with
            | (Some _, ys') -> is_bijection_by comp xs' ys'
            | (None, ys) -> false)

module type MATDATA = sig
        type elt
        type shape
        val pp_shape : shape -> string
        val mult_shape : shape -> shape -> shape
        val concat_shape : shape -> shape -> shape
        val sl_shape : shape -> shape
        val sr_shape : shape -> shape
        val trans_shape : shape -> shape
        
        val elt_eq : elt -> elt -> bool
        val shape_eq : shape -> shape -> bool

        val shape_of_expr : expr -> shape
        val shape_of_elt : elt -> shape

        val expr_of_elt : elt -> expr
        val elt_of_expr : expr -> elt

        (* used for groebner basis stuff *)
        val default_shape : shape
        val mult_shape_compat : shape -> shape -> bool
        val neg_shape : shape
        val shape_splittable : shape -> bool
        val shape_leftsplittable : shape -> bool

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
        


        val mat_of_expr : expr -> mat
        val expr_of_mat : mat -> expr
        val extra_rewr : mat -> mat

        val id_of_shape : shape -> expr

        val all_constants_of_shape : shape -> expr list

    end

module type MATRULES = functor (Data : MATDATA) -> sig
    val norm_mat: Data.mat -> Data.mat
end

module MkMat : MATRULES = functor (Data : MATDATA) -> struct

    open Data

    (* TODO: let below take as argument extra rewrite rules, which ListMat can
     * hook into. *) 
    let rec norm_mat (m : Data.mat) : Data.mat = 

        let rec mat_eq  (m1 : mat) (m2 : mat) =
            match (m1,m2) with
            | (MPlus (d,xs), MPlus (d',ys)) -> 
                    Data.shape_eq d d' && is_bijection_by mat_eq xs ys
            | (MOpp x, MOpp y) -> mat_eq x y
            | (MMult (x,y), MMult (x',y')) -> (mat_eq x x') && (mat_eq y y')
            | (MTrans x, MTrans y) -> mat_eq x y
            | (MConcat (x,y), MConcat (x', y')) -> (mat_eq x x') && (mat_eq y y')
            | (MSplitLeft x, MSplitLeft y) -> mat_eq x y
            | (MSplitRight x, MSplitRight y) -> mat_eq x y
            | (MId s1, MId s2) -> Data.shape_eq s1 s2
            | (MZero s1, MZero s2) -> Data.shape_eq s1 s2
            | (MBase x, MBase y) -> Data.elt_eq x y
            | _ -> false in

        let rec shape_of_mat (m : mat) : shape =
            match m with
            | MPlus (d,xs) -> d 
            | MOpp x -> shape_of_mat x
            | MMult (x,y) -> Data.mult_shape (shape_of_mat x) (shape_of_mat y)
            | MTrans x -> Data.trans_shape (shape_of_mat x)
            | MConcat (x,y) -> Data.concat_shape (shape_of_mat x) (shape_of_mat y)
            | MSplitLeft x -> Data.sl_shape (shape_of_mat x)
            | MSplitRight x -> Data.sr_shape (shape_of_mat x)
            | MId s -> s
            | MZero s -> s
            | MBase e -> Data.shape_of_elt e in

        let flatten_plus (xs : mat list) =
            let (plusses, others) = fold_left (fun acc x ->
                (match x with
                | MPlus (_,ys) -> ((fst acc) @ ys, snd acc)
                | e -> (fst acc, e :: (snd acc)))) ([], []) xs in
            plusses @ others in

        let mat_is_zero (m : mat) = match m with | MZero _ -> true | _ -> false
        in
         
        (* given a list, remove pairs that are opposites of each other. *)
        let rec mat_remove_opps (xs : mat list) =
            match xs with
            | [] -> []
            | ((MOpp x) :: xs') ->
                    (match (remove_by (mat_eq x) xs') with
                    | (Some _, xs'') -> mat_remove_opps xs''
                    | (None,_) -> (MOpp x) :: (mat_remove_opps xs'))
            | (x :: xs') ->
                    (match (remove_by (mat_eq (MOpp x)) xs') with
                    | (Some _, xs'') -> mat_remove_opps xs''
                    | (None, _) -> x :: (mat_remove_opps xs')) in

        let is_concatpair (x : mat) (y : mat) =
            match (x,y) with
            | (MConcat (a,b), MConcat (c,d)) ->
                    Data.shape_eq (shape_of_mat a) (shape_of_mat c) &&
                    Data.shape_eq (shape_of_mat b) (shape_of_mat d) 
            | _ -> false in

        let combine_concatpair (x : mat) (y : mat) =
            match (x,y) with
            | (MConcat (a,b), MConcat (c,d)) ->
                    let da = shape_of_mat a in
                    let db = shape_of_mat b in
                    MConcat (MPlus (da, [a;c]), MPlus (db, [b;d]))
            | _ -> assert false in

        let rec combine_concats_aux (x : mat) (xs : mat list) : mat * (mat list) =
            match xs with
            | [] -> (x, [])
            | (x' :: xs') ->
                    if is_concatpair x x' then 
                        combine_concats_aux (combine_concatpair x x') xs'
                    else
                        let (a,b) = combine_concats_aux x xs' in
                        (a, x' :: b) in
        
        let rec combine_concats (xs : mat list) : mat list =
            match xs with
            | [] -> []
            | x :: xs ->
                    let (x', xs') = combine_concats_aux x xs in
                    x' :: (combine_concats xs') in

        let rewrite_plus (d : shape) (xs : mat list) : mat =
            let xs = flatten_plus xs in
            let xs = List.filter (fun x -> not (mat_is_zero x)) xs in
            let xs = mat_remove_opps xs in
            let xs = combine_concats xs in
            match xs with
            | [] -> MZero d
            | _ -> MPlus (d,xs) in

        
        let is_splitpair x y =
            match x,y with
            | MSplitLeft x', MSplitRight y' -> mat_eq x' y'
            | _ -> assert false
        in

        let rec accum_splitpair (so_far : mat list) (sls : mat list) (srs : mat list) =
            match sls, srs with
            | [], [] -> (so_far, [], [])
            | [], srs -> (so_far, [], srs)
            | sl::sls, srs ->
                    match (remove_by (is_splitpair sl) srs) with
                    | (Some _, srs) ->
                            let e = (match sl with | MSplitLeft x -> x | _ -> assert
                            false) in
                            accum_splitpair (e :: so_far) sls srs
                    | (None, srs) ->
                            let (a,b,c) = accum_splitpair so_far sls srs in
                            (a, sl::b, c)
        in

        let rem_splitpairs xs ys =
            let (sl_xs, xs') = List.partition (fun x -> match x with | MSplitLeft _ ->
                true | _ -> false) xs in
            let (sr_ys, ys') = List.partition (fun x -> match x with | MSplitRight _ ->
                true | _ -> false) ys in
            let (matched_pairs, sls, srs) = accum_splitpair [] sl_xs sr_ys in
            (matched_pairs, sls @ xs', srs @ ys')
        in
        
        let mat_concatplus_simpl d xs d' ys =
            let (pairs, xs, ys) = rem_splitpairs xs ys in
            match pairs with
            | [] -> MConcat ((MPlus (d,xs)), (MPlus (d',ys)))
            | _ -> MPlus (Data.concat_shape d d', (pairs @ [MConcat ((MPlus (d,xs)), (MPlus (d',ys)))]))
        in

        (* Note this doesn't take into account ListOf reductions for lists, which must be done
         * separately *)
        let matsig_rewrite_step (m : mat) =
            match m with
            | MMult (a, MMult (b,c)) -> MMult (MMult (a,b), c)
            | MMult (MId _, a) -> a
            | MMult (a, MId _) -> a
            | MMult (MZero p, a) -> MZero (Data.mult_shape p (shape_of_mat a))
            | MMult (a, MZero p) -> MZero (Data.mult_shape (shape_of_mat a) p)
            | MMult (MOpp a, MOpp b) -> MMult (a,b)
            | MMult (MOpp a, b) -> MOpp (MMult (a,b))
            | MMult (a, MOpp b) -> MOpp (MMult (a,b))
            | MMult (a, MConcat (b,c)) -> MConcat (MMult (a,b), MMult (a,c))
            | MMult (MConcat (a,b), c) -> 
                    (* this rule is new *)
                    let c1 = MTrans (MSplitLeft (MTrans c)) in
                    let c2 = MTrans (MSplitRight (MTrans c)) in
                    MPlus (Data.mult_shape (shape_of_mat a) (shape_of_mat c1),
                          [MMult (a, c1); MMult (b,c2)])
                           
            | MMult (MPlus (d,xs), y) -> MPlus (Data.mult_shape d (shape_of_mat y), (map (fun x -> MMult (x,y)) xs))
            | MMult (y, MPlus (d,xs)) -> MPlus (Data.mult_shape (shape_of_mat y) d, map (fun x -> MMult (y,x)) xs)
            | MOpp (MOpp e) -> e
            | MOpp (MPlus (d,xs)) -> MPlus (d, map (fun x -> MOpp x) xs)
            | MTrans (MMult (a,b)) -> MMult (MTrans b, MTrans a)
            | MTrans (MOpp a) -> MOpp (MTrans a)
            | MTrans (MPlus (d,xs)) -> MPlus (Data.trans_shape d, (map (fun x -> MTrans x) xs))
            | MTrans (MTrans a) -> a
            | MPlus (d, []) -> MZero d
            | MPlus (d, xs) -> rewrite_plus d xs
            | MConcat (MSplitLeft a, MSplitRight b) -> 
                    if mat_eq a b then a else m
            | MConcat (MZero p1, MZero p2) ->
                    MZero (Data.concat_shape p1 p2)
            | MConcat (MOpp a, MOpp b) ->
                    MOpp (MConcat (a,b))
            | MConcat (MPlus (d,xs), MPlus (d', ys)) -> mat_concatplus_simpl d xs d' ys
            | MSplitLeft (MOpp a) -> MOpp (MSplitLeft a)
            | MSplitLeft (MPlus (d,xs)) -> MPlus (Data.sl_shape d, (map (fun x -> MSplitLeft x) xs))
            | MSplitLeft (MConcat (a,_)) -> a
            | MSplitLeft (MMult (a,b)) -> MMult (a, MSplitLeft b)
            | MSplitRight (MOpp a) -> MOpp (MSplitRight a)
            | MSplitRight (MPlus (d,xs)) -> MPlus (Data.sr_shape d, (map (fun x -> MSplitRight x) xs))
            | MSplitRight (MConcat (_,b)) -> b
            | MSplitRight (MMult (a,b)) -> MMult (a, MSplitRight b)
            | _ -> m
        in

        
        let norm_matsig_rec (nf : mat -> mat) (m : mat) =
            match m with
            | MPlus (d,xs) -> MPlus (d, map nf xs)
            | MOpp x -> MOpp (nf x)
            | MMult (x,y) -> MMult (nf x, nf y)
            | MTrans x -> MTrans (nf x)
            | MConcat (x,y) -> MConcat (nf x, nf y)
            | MSplitLeft x -> MSplitLeft (nf x)
            | MSplitRight x -> MSplitRight (nf x)
            | _ -> m
        in

        let next = matsig_rewrite_step (Data.extra_rewr (norm_matsig_rec norm_mat m)) in
        if (mat_eq m next) then m else norm_mat next
    
end






