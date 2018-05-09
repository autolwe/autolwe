(* Grobner basis computations for K[X]-module *)

type mon
       
type pol_i = mon list * Expr.expr

       
val groebner : int list -> (int, Expr.expr) Hashtbl.t ->
           (Expr.Me.key * Expr.expr) list ->
           (pol_i * int list) list -> (pol_i * int list) list


val eps_to_polys : (NormField.EP.t * Expr.expr) list ->
           (pol_i) list * int list * (int, Expr.expr) Hashtbl.t

                                                                       
val polys_to_eps :  pol_i list ->
           int list -> (int, Expr.expr) Hashtbl.t -> (Expr.expr * Expr.expr) list

val get_inverter : int list ->
           (int, Expr.expr) Hashtbl.t ->
           (Expr.Me.key * Expr.expr) list ->
           (pol_i * int list) list ->
           pol_i -> bool * Expr.expr
