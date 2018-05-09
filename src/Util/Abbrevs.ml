(* * Define some abbreviations *)

module L = BatList
module F = Format
module BL = Bolt.Logger
module O = BatOption

let hcomb = Hashcons.combine
let hcomb_l = Hashcons.combine_list
let hcomb_h = Hashcons.combine_hashes
