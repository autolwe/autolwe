
(* * Deducibility of expressions. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Type
open Util
open Expr
open ExprUtils

let mk_log level = mk_logger "Deduce.Deduc" level "Deduc.ml"
let log_i = mk_log Bolt.Level.INFO

(* ** Deducibility function
 * ----------------------------------------------------------------------- *)

exception Found of expr

let invert' ?ppt_inverter:(ppt=false) emaps do_div known_es to_ =
  let to_ = Norm.norm_expr_strong to_ in
  (* Will be initialized to hold known_es *)
  let known = He.create 17 in
  let progress = ref false in
  let is_in e = is_Cnst e || He.mem known e in
  let get e = if is_Cnst e then e else He.find known e in

  (* add an expression with the given inverter and also immediately
     add extractable subterms (e.g., components of tuple). *)
  let rec add_known e inv =
    (* we might deduce non-normalized Ifte expressions such as b?g^a:g^b *)
    let e = if is_Ifte e then Norm.norm_expr_strong e else e in
    if equal_expr e to_ then raise (Found inv);
    if not (He.mem known e) && not (is_Cnst e) then (
      log_i (lazy (fsprintf "@[add_known:@ @[<hov 2>%a@]@]" pp_expr e));
      He.add known e inv;
      progress := true;
      add_subterms e inv
    )

  (* Called in add_known above. Adds subterms of e to known if applicable. *)
  and add_subterms e inv =
    match e.e_node with
    | V _  | Proj _ | Cnst _ -> ()
    | Tuple es ->
      List.iteri (fun i e -> add_known e (mk_Proj i inv)) es
    | App(op, es) ->
      begin match op, es with
      | GLog g, [e]         -> add_known e (mk_GExp (mk_GGen g) inv)
      | FOpp, _             -> add_known e (mk_FOpp inv)
      | FInv, [e]           -> add_known e (mk_FInv inv)
      | Not, [e]            -> add_known e (mk_Not inv)
      | ListOf, [e]         -> 
              begin match inv.e_node with
              | App(ListOf, [i]) -> add_known e i
              | _ -> failwith "bad inverter for listof"
              end
      | ListOp MatTrans, [e]-> add_known e (mk_ListMatTrans inv)
      | MatTrans, [e]       -> add_known e (mk_MatTrans inv)
      | MatOpp, _           -> add_known e (mk_MatOpp inv)
      | ListOp MatOpp, _           -> add_known e (mk_ListMatOpp inv)
      | MatConcat, [e1; e2] -> add_known e1 (mk_MatSplitLeft inv); add_known e2
      (mk_MatSplitRight inv)
      | ListOp MatConcat, [e1; e2] -> add_known e1 (mk_ListMatSplitLeft inv);
      add_known e2 (mk_ListMatSplitRight inv)
      | (FMinus | FDiv), _  -> ()
      | (Eq| Not | Ifte), _ -> ()
      | EMap _, _           -> ()
      | GExp _, [e1;e2] when
        not ppt && is_GGen e1 -> add_known e2 (mk_GLog inv)
      | _, _ -> ()
      end
    | Nary _ -> ()
    | Quant(_) -> ()
  in

  (* Set of useful subterms that we should construct,
     also contains tuples. For examples, constructing (a,b)
     might allow us to construct h((a,b)). *)
  let sub_constr = ref Se.empty in
  let add_sub_constr e =
    if not (Se.mem e !sub_constr) then
      log_i (lazy (fsprintf "@[<hov>add_sub_constr:@ @[<hov 2>%a@]@]" pp_expr e));
      sub_constr := Se.add e !sub_constr
  in
  let rm_sub_constr e = sub_constr := Se.remove e !sub_constr in
  let reg_constr e inv = add_known e inv; rm_sub_constr e in

  (* sub_solver contains for each type a set of (known and unknown) maximal
     subterms of the given type. These are used by the type-specific
     solvers, e.g., for Xor or Fq. *)
  let sub_solver = Hty.create 7 in
  let add_sub_solver e =
    log_i (lazy (fsprintf "@[<hov>add_sub_solver[maybe]:@ @[<hov 2>%a@]" pp_expr e));
    match e.e_ty.ty_node with
    | BS _ | Fq | G _ | Bool | Mat _ | List _ ->
      if is_G e.e_ty && not ppt then () else
      begin try
        let s = Hty.find sub_solver e.e_ty in
        if not (Se.mem e s) then
          log_i (lazy (fsprintf "@[<hov>add_sub_solver:@ @[<hov 2>%a@]@]" pp_expr e));
          Hty.replace sub_solver e.e_ty (Se.add e s)
      with
        Not_found ->
          log_i (lazy (fsprintf "@[add_sub_solver[create]:@ @[<hov 2>%a@]@]"
                         pp_expr e));
          Hty.add sub_solver e.e_ty (Se.singleton e)
      end
    | TySym _ | Int | Prod _ -> ()
  in
  let add_sub e = add_sub_solver e; add_sub_constr e in
  (* for everything except field expressions, there is no nesting in the
     normal form, we therefore require only an in_field flag *)
  let rec register_subexprs in_field e =
    match e.e_node with
    | Tuple es    -> add_sub_constr e; List.iter (register_subexprs false) es
    | Quant(_,_,e1) -> add_sub e; register_subexprs true e1
    | Proj(_,e1)  -> add_sub e; (register_subexprs false) e1
    | App(op, es) ->
      begin match op with
      | (FunCall _ | RoCall _ | MapLookup _ | MapIndom _) ->
        add_sub e; List.iter (register_subexprs false) es
      | FOpp | FMinus | FInv | FDiv ->
        if not in_field then add_sub_solver e;
        List.iter (register_subexprs true) es
      | GExp _ | EMap _ ->
        (* solve_group used for ppt=true, solve_fq+construction otherwise *)
        if ppt
        then (
          add_sub_solver e; List.iter (register_subexprs true) es;
          (* also add g^u and g^v if e=g^(b?u:v) *)
          if (is_GExp e) then (
            let (a,b) = destr_GExp e in
            if (is_Ifte b) then (
              let (c,u,v) = destr_Ifte b in
              let e1 = mk_GExp a u in
              let e2 = mk_GExp a v in
              add_sub_solver e1; add_sub_solver e2;
              add_sub_constr (mk_Ifte c e1 e2);
            )
          )
        ) else (
          add_sub_constr e; List.iter (register_subexprs false) es
        )
      | GLog _ ->
        if ppt then add_sub_solver e
        else add_sub e; List.iter (register_subexprs false) es
      | Eq | Not | Ifte ->
        add_sub_constr e; List.iter (register_subexprs false) es
      | GInv -> failwith "GInv cannot occur in normal-form"
      | MatMult|MatOpp|MatTrans|MatConcat|MatSplitLeft|MatSplitRight ->
          if not in_field then add_sub_solver e; List.iter (register_subexprs true) es 
      | ListOp _ -> 
          if not in_field then add_sub_solver e; List.iter (register_subexprs true) es
      | ListOf ->
          add_sub e; List.iter (register_subexprs false) es

      (*
      | FDiv ->
        FIXME: not the case, check where/why we need this
        failwith "FDiv cannot occur in normal-form" *)
      end
    | Nary(op,es) ->
      begin match op with
      | Lor | Land | GMult -> add_sub e; List.iter (register_subexprs
      false) es 
      | FPlus | FMult ->
        if not in_field then add_sub_solver e; List.iter (register_subexprs true) es
      | Xor ->
        add_sub_solver e; List.iter (register_subexprs false) es
      | MatPlus ->
        if not in_field then add_sub_solver e; List.iter (register_subexprs true) es
      | ListNop _ ->
          if not in_field then add_sub e; List.iter (register_subexprs true) es
      end
      (* normal form is g^log(v) and must have been already added *)
    | V _ when is_G e.e_ty -> ()
    | V _                  -> add_sub_solver e
    | Cnst _               -> add_sub_constr e
  in

  (* Try to construct unknown useful expressions *)
  let construct1 e e1 mki =
    if not (is_in e) && is_in e1 then reg_constr e (mki (get e1))
  in
  let construct2 e e1 e2 mki =
    if not (is_in e) && is_in e1 && is_in e2 then
      reg_constr e (mki (get e1) (get e2))
  in
  let construct3 e e1 e2 e3 mki =
    if not (is_in e) && is_in e1 && is_in e2 && is_in e3 then
      reg_constr e (mki (get e1) (get e2) (get e3))
  in
  let constructn e es mki =
    if not (is_in e) && List.for_all is_in es then
      reg_constr e (mki (List.map get es))
  in
  let construct_div e e1 e2 =
    if not (is_in e1) && is_in e1 && is_in e2 then (
      reg_constr e (mk_FDiv (get e1) (get e2))
    );
    (* FIXME: shouldn't these cases be handled by the field solver *)
    if do_div && is_in e && not (is_in e1) && is_in e2 then (
      add_known e1 (mk_FMult [get e; get e2]); rm_sub_constr e
    )
    (*
    if do_div && is_in e && not (is_in e2) && is_in e1 then (
      add_known e2 (mk_FMult [mk_FInv (get e); get e1]); rm_sub e
    )
    *)
  in
  let construct_app e op es =
    match op, es with
    | (FOpp | FMinus), _ -> assert false
    | Not,    [e1]       -> construct1 e e1 mk_Not
    | GLog _, [e1]       -> construct1 e e1 mk_GLog
    | FInv,   [e1]       -> construct1 e e1 mk_FInv
    | Eq,     [e1;e2]    -> construct2 e e1 e2 mk_Eq
    | EMap s, [e1;e2]    -> construct2 e e1 e2 (mk_EMap s)
    | Ifte,   [e1;e2;e3] -> construct3 e e1 e2 e3 mk_Ifte
    | FDiv,   [e1;e2]    -> construct_div e e1 e2
    | FunCall f, [e1]    -> construct1 e e1 (mk_FunCall f)
    | RoCall h, [e1]     -> construct1 e e1 (mk_RoCall h)
      (* in the PPT case, we always rely on the solver for groups *)
    | GExp _, [e1;e2] when not ppt ->
      construct2 e e1 e2 mk_GExp
    | MatMult, [e1;e2]   -> construct2 e e1 e2 mk_MatMult
    | MatConcat, [e1;e2]   -> construct2 e e1 e2 mk_MatConcat
    | MatOpp, [e1] -> construct1 e e1 mk_MatOpp
    | MatTrans, [e1] -> construct1 e e1 mk_MatTrans
    | MatSplitLeft, [e1] -> construct1 e e1 mk_MatSplitLeft
    | MatSplitRight, [e1] -> construct1 e e1 mk_MatSplitRight
    | ListOp MatMult, [e1; e2] -> construct2 e e1 e2 mk_ListMatMult
    | ListOp MatConcat, [e1; e2] -> construct2 e e1 e2 mk_ListMatConcat
    | ListOp MatOpp, [e1] -> construct1 e e1 mk_ListMatOpp
    | ListOp MatTrans, [e1] -> construct1 e e1 mk_ListMatTrans
    | ListOp MatSplitLeft, [e1] -> construct1 e e1 mk_ListMatSplitLeft
    | ListOp MatSplitRight, [e1] -> construct1 e e1 mk_ListMatSplitRight
    | ListOf, [e1] -> 
            log_i (lazy (fsprintf "want to construct %a : %a from %a " pp_expr e
            pp_ty e.e_ty pp_expr e1));

            begin
            match e.e_ty.ty_node with
            | List (d, _) -> construct1 e e1 (mk_ListOf d)
            | t -> log_i (lazy (fsprintf "bad type? got %a" pp_ty (e.e_ty)));
            tacerror "type error"
            end

    | _, _ -> assert false

  in
  let construct e =
    match e.e_node with
    | Proj(i, e1) -> construct1 e e1 (mk_Proj i)
    (*
    | H(h,e1)     -> construct1 e e1 (mk_H h)
    | ProjPermKey(ke,kp) -> construct1 e kp (mk_ProjPermKey ke) *)
    | Tuple es    -> constructn e es mk_Tuple
    | App(op,es)  -> construct_app e op es
    | Quant(q,b,e1) -> construct1 e e1 (mk_Quant q b)
    | Nary(op,es) ->
      begin match op with
      | Land  -> constructn e es mk_Land
      | Lor   -> constructn e es mk_Lor
      | GMult -> constructn e es mk_GMult
      | FPlus | FMult | Xor -> ()
      | MatPlus -> () (*constructn e es mk_MatPlus (* () *) *)
      | ListNop n -> constructn e es (mk_ListNop n)
      end
    | V _
    | Cnst _ -> reg_constr e e
  in

  (* Try do deduce interesting subterms for the given type using solvers *)
  let solve ty subexprs =
    log_i (lazy (fsprintf "@[<hov>solve: started for type %a@]" pp_ty ty));
    if is_G ty && not ppt then () else
    let solver, ty_rel =
      match ty.ty_node with
      | BS _ | Bool  -> DeducXor.solve_xor, equal_ty ty
      | Fq           -> DeducField.solve_fq, equal_ty ty
      | G _          -> DeducGroup.solve_group emaps, fun t -> is_G t || is_Fq t
      | Mat _        -> DeducMat.solve_mat, fun t -> is_Mat t 
      | List p       -> 
              (match (snd p).ty_node with
              | Mat _ -> DeducList.solve_mat_list, fun t -> is_Mat t || is_MatList t
              | _ -> DeducList.solve_other_list, fun t2 -> is_ListOfTy (snd p) t2)
      | TySym _ | Prod _ | Int -> assert false
    in
    let k,u = Se.partition is_in subexprs in
    if Se.is_empty u then (
      log_i (lazy (fsprintf "@[<hov>solve: done for type %a@]" pp_ty ty));
      Hty.remove sub_solver ty
    ) else (
      let k' = Se.filter (fun e -> ty_rel e.e_ty) (he_keys known) in
      let k = Se.elements (Se.union k k') in
      let k = ref (List.map (fun e -> (e, I (get e))) k) in
      log_i (lazy (fsprintf "@[<hov>known:@ @[<hov 2>%a@]@]"
                     (pp_list "," pp_expr) (List.map fst !k)));
      log_i (lazy (fsprintf "@[<hov>unknown:@ @[<hov 2>%a@]@]"
                     (pp_list "," pp_expr) (Se.elements u)));
      Se.iter (fun u ->
        try
          let inv = solver !k u in
          add_known u (expr_of_inverter inv);
          k := (u,inv) :: !k
        with Not_found -> ()) u
    )
  in

  (* Initialisation *)
  try
    (* initialize for all known expressions *)
    let init_known (e,I i) =
      let e = Norm.norm_expr_strong e in
      log_i (lazy (fsprintf "@[<hov>init_known:@ @[<hov 2>%a@]@]" pp_expr e));
      register_subexprs false e;
      add_known e i
    in
    List.iter init_known known_es;

    (* Register subterms of expression that we want to deduce *)
    register_subexprs false to_;

    (* First try to construct all interesting subterms,
       if progress stops, call xor, group, or field solver *)
    while !progress do
      progress := false;
      Se.iter construct !sub_constr;
      if not (!progress) then Hty.iter solve sub_solver
    done;
    raise Not_found
  with
  | Found inv -> I inv
  | Not_found -> raise Not_found
  | e ->
    let err = Printexc.to_string e in
    let bt = Printexc.get_backtrace () in
    log_i (lazy (fsprintf "@[invert:@ %s@ %s@]" err bt)); raise e


(* ** Wrapper function
 * ----------------------------------------------------------------------- *)

let invert ?ppt_inverter:(ppt=false) ts known_es to_ =
  let open TheoryTypes in
  let emaps = L.map snd (Mstring.bindings ts.ts_emdecls) in
  log_i (lazy (fsprintf "Begin inverting %a from %a " pp_expr to_ (pp_list ","
  pp_expr) (List.map fst known_es)));

  invert' ~ppt_inverter:ppt emaps false known_es to_
