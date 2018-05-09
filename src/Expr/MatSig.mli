open Expr


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

module MkMat : MATRULES

