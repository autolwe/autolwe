(* * Simple linear algebra (equation solving) over $F_2$. *)

(** [solve A s] returns a solution [b] for [A b = s] if
    it exists and [None] otherwise. *)
val solve : bool array list -> bool array -> bool list option
