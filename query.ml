open Formula
open Intfdesc
open Assign

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type query = 
  | Qassert of formula * query
  | Qtaut of formula
  | Qsat of formula
  | Qstableformula of formula * intfdesc
  | Qstableintf of intfdesc * intfdesc
  | Qspimplies of formula * assign * formula

let rec string_of_query = function
  | Qassert (f,q) -> "_assert " ^ string_of_formula f ^ "; " ^ string_of_query q
  | Qtaut f -> string_of_formula f
  | Qsat f -> "_sat " ^ string_of_formula f
  | Qstableformula (f,intf) -> string_of_formula f ^ " _against " ^ string_of_intfdesc intf
  | Qstableintf (intf1, intf2) -> string_of_intfdesc intf1 ^ " _against " ^ string_of_intfdesc intf2
  | Qspimplies (pre, assign, post) -> 
      "_sp(" ^ string_of_formula pre ^ "; " ^ string_of_assign assign ^ ") => " ^ string_of_formula post
    