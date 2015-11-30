open Sourcepos
open Listutils
open Order
open Stitch
open Formula

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type knot = { knotloc:sourcepos; knotnode:knotnode }

and knotnode = 
  | SimpleKnot of stitch list 
  | KnotOr     of knot * knot
  | KnotAnd    of knot * knot
  | KnotAlt    of knot * knot
  
let alt_token = "\\->/"

let knotadorn loc knotnode = { knotloc=loc; knotnode=knotnode }

let rec assertion_of_knot ikind knot =
  match knot.knotnode with
  | SimpleKnot stitches -> conjoin (List.map (assertion_of_stitch ikind) stitches)
  | KnotAnd     (k1,k2) -> conjoin (List.map (assertion_of_knot ikind) [k1;k2])
  | KnotOr      (k1,k2) 
  | KnotAlt     (k1,k2) -> disjoin (List.map (assertion_of_knot ikind) [k1;k2])

let rec string_of_knot knot = 
  match knot.knotnode with
  | SimpleKnot stitches -> "{*" ^ string_of_list string_of_stitch ";" stitches ^ "*}"
  | KnotOr      (k1,k2) -> string_of_knot k1 ^ " \\/ "  ^ string_of_knot k2
  | KnotAnd     (k1,k2) -> string_of_knot k1 ^ " /\\ "  ^ string_of_knot k2
  | KnotAlt     (k1,k2) -> string_of_knot k1 ^ " " ^ alt_token ^ " " ^ string_of_knot k2

(* ******************** a fold for knots, why not? ************************ *)

let rec fold fstitch v knot =
  match knot.knotnode with
  | SimpleKnot ss   -> List.fold_left fstitch v ss
  | KnotOr  (k1,k2)
  | KnotAnd (k1,k2) 
  | KnotAlt (k1,k2) -> List.fold_left (fold fstitch) v [k1;k2]

(* ******************** a map for knots, why not? ************************ *)

module KnotMap = MyMap.Make (struct type t = knot
                                    let compare = Pervasives.compare
                                    let to_string = string_of_knot
                             end
                            )
