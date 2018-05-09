open MatData
open DeducMatSig

module MatD = MatDeduc (Mat)
let solve_mat = MatD.solve_mat
