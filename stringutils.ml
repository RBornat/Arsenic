open String

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let is_empty s = s=""

let starts_with s prefix =
  try let pfx = String.sub s 0 (String.length prefix) in
      pfx=prefix
  with _ -> false
  
let ends_with s suffix =
  try let sfxlength = String.length suffix in
      let sfx = String.sub s (String.length s-sfxlength) sfxlength in
      sfx=suffix
  with _ -> false
  
let rec words s =
  if length s = 0 then []
  else
  if get s 0 = ' ' then words (sub s 1 (length s-1))
  else
    try let sidx = index s ' ' in
        sub s 0 sidx :: words (sub s (sidx+1) (length s-sidx-1))
    with Not_found -> [s]