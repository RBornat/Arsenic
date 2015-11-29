open Listutils

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
(* now just a vestige of itself *)

let string_of_map string_of_key string_of_binding kbsep elemsep bindings map =
  string_of_assoc string_of_key string_of_binding kbsep elemsep (bindings map)
  
let stringprefix s f v = s ^ f v
