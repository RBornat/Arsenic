(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015-2016 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)

(* one day there will be proper separation logic locations.

   For a while there were array locations, but under the Half-Arsed Attempt regulations 
   of January 2016, they are no more.
   
 *)

open Name
open Formula

type location = VarLoc of var

let _recFloc = function
  | VarLoc v         -> _recFname v (* due to cheating it might be a register ... *)

let locv = function
  | VarLoc v       -> v

let string_of_location = function
  | VarLoc v       -> Name.string_of_var v

let eq l1 l2 =
  match l1, l2 with
  | VarLoc v1         , VarLoc v2          -> v1=v2
  
let stripspos loc = 
  match loc with 
  | VarLoc   v       -> loc
  
let is_auxloc = function
  | VarLoc v         -> Name.is_auxvar v
  