open Name
open Intfdesc

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type rely = 
  | Rely    of intfdesc list
  | RelyVar of string

let new_RelyVar () = RelyVar (new_unknown_string ())

let is_RelyVar = function
  | RelyVar _ -> true
  | _         -> false
  
let string_of_rely = function
  | Rely intfs -> "(" ^ string_of_intfdescs intfs ^ ")"
  | RelyVar s  -> s
  
