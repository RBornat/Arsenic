open Tuple
open Name 

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type sourcepos = Lexing.position * Lexing.position

let dummy_spos = (Lexing.dummy_pos, Lexing.dummy_pos)

let linenum spos = spos.Lexing.pos_lnum
let charnum spos = spos.Lexing.pos_cnum-spos.Lexing.pos_bol

let startline (startpos,endpos) = linenum startpos
let endline   (startpos,endpos) = linenum endpos

let startchar (startpos,endpos) = charnum startpos
let endchar   (startpos,endpos) = charnum endpos

let startsbefore pos1 pos2 = startline pos1 < startline pos2 || 
                             (startline pos1 = startline pos2 && startchar pos1 < startchar pos2)

let endsbefore pos1 pos2 = endline pos1 < endline pos2 || 
                           (endline pos1 = endline pos2 && endchar pos1 < endchar pos2)

let compare pos1 pos2 =
  if pos1=pos2 then 0 else
  if startsbefore pos1 pos2 then (-1) else 1
  
let spos_of_sposspos pos1 pos2 =
  if pos1=dummy_spos then pos2 else
  if pos2=dummy_spos then pos1 else
    let fst = if startsbefore pos1 pos2 then pos1 else pos2 in
    let snd = if endsbefore pos1 pos2 then pos2 else pos1 in
    match fst, snd with
    | (startpos,_), (_,endpos) -> (startpos, endpos)

let string_of_sourcepos (startpos,endpos) = 
  if linenum startpos=linenum endpos then
    Printf.sprintf "line %d chars %d-%d" 
      (linenum startpos) (charnum startpos) (charnum endpos)
  else
    Printf.sprintf "line %d char %d - line %d char %d"
      (linenum startpos) (charnum startpos)
      (linenum endpos) (charnum endpos)

let firstspos_of_sposs xs =
  let rec first spos = function
    | []    -> spos
    | x::xs -> if spos=dummy_spos then first x xs else spos
  in 
  first dummy_spos xs

let enclosingspos_of_sposs xs = 
  let rec enclosing spos = function
    | []    -> spos
    | x::xs -> enclosing (spos_of_sposspos spos x) xs
  in
  enclosing dummy_spos xs
  
let enclosedby posinside posoutside =
  not (startsbefore posinside posoutside) && not (endsbefore posoutside posinside)
  
type positionedlabel = {labspos: sourcepos; lablab: Name.label}

let string_of_positionedlabel poslab = 
  bracketed_string_of_pair string_of_sourcepos string_of_label (poslab.labspos, poslab.lablab)

