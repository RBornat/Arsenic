open Tuple
open Name 

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type sourcepos = Lexing.position * Lexing.position

let dummyloc = (Lexing.dummy_pos, Lexing.dummy_pos)

let linenum pos = pos.Lexing.pos_lnum
let charnum pos = pos.Lexing.pos_cnum-pos.Lexing.pos_bol

let startline (startpos,endpos) = linenum startpos
let endline   (startpos,endpos) = linenum endpos

let startchar (startpos,endpos) = charnum startpos
let endchar   (startpos,endpos) = charnum endpos

let startsbefore loc1 loc2 = startline loc1 < startline loc2 || 
                             (startline loc1 = startline loc2 && startchar loc1 < startchar loc2)

let endsbefore loc1 loc2 = endline loc1 < endline loc2 || 
                           (endline loc1 = endline loc2 && endchar loc1 < endchar loc2)

let compare loc1 loc2 =
  if loc1=loc2 then 0 else
  if startsbefore loc1 loc2 then (-1) else 1
  
let loc_of_locloc l1 l2 =
  if l1=dummyloc then l2 else
  if l2=dummyloc then l1 else
    let fst = if startsbefore l1 l2 then l1 else l2 in
    let snd = if endsbefore l1 l2 then l2 else l1 in
    match fst, snd with
    | (startpos,_), (_,endpos) -> (startpos, endpos)

let string_of_location (startpos,endpos) = 
  if linenum startpos=linenum endpos then
    Printf.sprintf "line %d chars %d-%d" 
      (linenum startpos) (charnum startpos) (charnum endpos)
  else
    Printf.sprintf "line %d char %d - line %d char %d"
      (linenum startpos) (charnum startpos)
      (linenum endpos) (charnum endpos)

let string_of_loc = string_of_location

let firstloc_of_locs xs =
  let rec first loc = function
    | []    -> loc
    | x::xs -> if loc=dummyloc then first x xs else loc
  in 
  first dummyloc xs

let enclosingloc_of_locs xs = 
  let rec enclosing loc = function
    | []    -> loc
    | x::xs -> enclosing (loc_of_locloc loc x) xs
  in
  enclosing dummyloc xs
  
let enclosedby locinside locoutside =
  not (startsbefore locinside locoutside) && not (endsbefore locoutside locinside)
  
type locatedlabel = {labloc: sourcepos; lablab: Name.label}

let string_of_locatedlabel loclab = 
  bracketed_string_of_pair string_of_location string_of_label (loclab.labloc, loclab.lablab)

