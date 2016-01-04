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
                stitchlocopt     : location option;
                stitchspopt      : spost option; 
                stitchembroidery : formula 
              }

and spost = 
  | SpostSimple of formula
  | SpostRes of formula
  | SpostDouble of formula * formula
  
let string_of_spost = function
  | SpostSimple f       -> "{" ^ string_of_formula f ^ "}"
  | SpostRes    f       -> "{ ?" ^ string_of_formula f ^ "}"
  | SpostDouble (f1,f2) -> "{" ^ string_of_formula f1 ^ "; ?" ^ string_of_formula f2 ^ "}"
  
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
                  | Some (loc) -> Printf.sprintf "?%s" (string_of_location loc)
                 )
                 (match spopt with
                  | None -> ""
                  | Some f -> Printf.sprintf " {%s}" (string_of_spost f)
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

let pos_of_stitch       s = s.stitchpos
let order_of_stitch     s = s.stitchorder
let source_of_stitch    s = s.stitchsource
let locopt_of_stitch    s = s.stitchlocopt
let spopt_of_stitch     s = s.stitchspopt
let assertion_of_stitch s = s.stitchembroidery

let is_go = Order.is_go <.> order_of_stitch

let is_reserved_stitch s = match locopt_of_stitch s with Some _ -> true | _ -> false
