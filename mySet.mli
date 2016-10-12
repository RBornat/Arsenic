
(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
module type OrderedType = sig
  include Set.OrderedType
  val to_string : t -> string
end

module type S = sig
  include Set.S
  val of_list   : elt list -> t
  val to_string : t -> string
  val map       : (elt -> 'a) -> ('a list -> 'b) -> t -> 'b
end

module Make (Ord : OrderedType) : S with type elt = Ord.t
