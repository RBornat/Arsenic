(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type stitch 
val string_of_stitch : stitch -> string

val stitchadorn: Sourcepos.sourcepos -> Order.order -> Node.node 
                 -> Formula.formula option -> Formula.formula 
                 -> stitch

val pos_of_stitch       : stitch -> Sourcepos.sourcepos
val order_of_stitch     : stitch -> Order.order
val source_of_stitch    : stitch -> Node.node
val spopt_of_stitch     : stitch -> Formula.formula option
val assertion_of_stitch : Order.ikind -> stitch -> Formula.formula

val string_of_assertion_of_stitch : (Formula.formula -> string) -> stitch -> string
