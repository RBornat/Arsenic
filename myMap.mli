
(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
module type OrderedType = sig
  include Map.OrderedType
  val to_string : t -> string
end

module type S = sig
  include Map.S
  val to_assoc  : 'a t -> (key * 'a) list
  val of_assoc  : (key * 'a) list ->'a  t
  val to_string : ('a -> string) -> 'a t -> string
  val map       : ((key * 'a) -> 'b) -> ('b list -> 'c) -> 'a t -> 'c
  val mymerge   : ('a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val memofun   : ('b -> key) -> ('b -> 'a) -> 'b -> 'a
  val vmemofun  : bool -> string -> ('b -> string) -> ('a -> string) -> 
                    ('b -> key) -> ('b -> 'a) -> 'b -> 'a
  val memorec   : ('b -> key) -> (('b -> 'a) -> 'b -> 'a) -> 'b -> 'a
  val vmemorec  : bool -> string -> ('b -> string) -> ('a -> string) -> 
                    ('b -> key) -> (('b -> 'a) -> 'b -> 'a) -> 'b -> 'a
end

module Make (Ord : OrderedType) : S with type key = Ord.t
