open Function
open Sourcepos
open Name
open Formula
open Location
open Order
open Node

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type stitch = { stitchpos        : sourcepos; 
                stitchorder      : order; 
                stitchsource     : node; 
                stitchlocopt     : (location * bool) option;
                stitchspopt      : formula option; 
                stitchembroidery : formula 
              }

let string_of_stitch { stitchorder      = order; 
                       stitchsource     = source;
                       stitchlocopt     = locopt;
                       stitchspopt      = spopt; 
                       stitchembroidery = assertion 
                     } =
  Printf.sprintf "%s %s%s%s: %s" 
                 (string_of_order order) 
                 (string_of_node source)
                 (match locopt with
                  | None -> ""
                  | Some (loc, b) -> Printf.sprintf "*%s(%s)"
                                        (string_of_location loc)
                                        (if b then "t" else "f")
                 )
                 (match spopt with
                  | None -> ""
                  | Some f -> Printf.sprintf " {%s}" (string_of_formula f)
                 )
                 (string_of_formula assertion)

let stitchadorn spos order source locopt spopt assertion = 
  { stitchpos        = spos; 
    stitchorder      = order; 
    stitchsource     = source; 
    stitchlocopt     = locopt;
    stitchspopt      = spopt; 
    stitchembroidery = assertion 
  }

let pos_of_stitch    s = s.stitchpos
let order_of_stitch  s = s.stitchorder
let source_of_stitch s = s.stitchsource
let locopt_of_stitch s = s.stitchlocopt
let spopt_of_stitch  s = s.stitchspopt

let assertion_of_stitch ikind {stitchorder=order; stitchembroidery=assertion} = 
  match order with
  | Go -> (* if not (!Settings.param_LocalSpec) then _recTrue else *)
          if ikind=External then assertion else
          Order.quotient Go ikind assertion
  | _  -> assertion

let string_of_assertion_of_stitch sof {stitchembroidery=assertion} = sof assertion