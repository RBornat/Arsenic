open Function
open Location
open Name
open Formula
open Order
open Node

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type stitch = { stitchloc:location; stitchorder: order; stitchsource: node; stitchspopt: formula option; stitchembroidery: formula }

let string_of_stitch { stitchorder=order; stitchsource=source; stitchspopt=spopt; stitchembroidery=assertion } =
  Printf.sprintf "%s %s%s: %s" 
                 (string_of_order order) 
                 (string_of_node source)
                 (match spopt with
                  | None -> ""
                  | Some f -> Printf.sprintf " {%s}" (string_of_formula f)
                 )
                 (string_of_formula assertion)

let stitchadorn loc order source spopt assertion = 
  { stitchloc=loc; stitchorder=order; stitchsource=source; stitchspopt=spopt; stitchembroidery=assertion }

let loc_of_stitch        s = s.stitchloc
let order_of_stitch      s = s.stitchorder
let source_of_stitch     s = s.stitchsource
let spopt_of_stitch      s = s.stitchspopt

let assertion_of_stitch ikind {stitchorder=order; stitchembroidery=assertion} = 
  match order with
  | Go -> (* if not (!Settings.param_LocalSpec) then _recTrue else *)
          if ikind=External then assertion else
          Order.quotient Go ikind assertion
  | _  -> assertion

let string_of_assertion_of_stitch sof {stitchembroidery=assertion} = sof assertion