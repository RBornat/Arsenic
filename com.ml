open Listutils
open Sourcepos
open Formula
open Knot
open Assign

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type simplecom = {sc_pos: sourcepos; sc_ipreopt: formula option; sc_node: scomnode}

and scomnode =
  | Skip
  | Assert of formula
  | Assign of assign

and structcom = {structcompos: sourcepos; structcomnode: structcomnode}

and structcomnode = 
  | If of formula triplet * seq * seq
  | While of formula triplet * seq
  | DoUntil of seq * formula triplet 
  
and 'a triplet = 
  { tripletpos: sourcepos;
    tripletknot: knot; 
    tripletlab: positionedlabel; 
    tripletof: 'a 
  }

and com = 
  | Com of simplecom triplet
  | Structcom of structcom
  
and seq = com list

let is_simplecom = function
  | Com _ -> true
  | _     -> false

let tripletadorn spos knot lab tof = {tripletpos=spos; tripletknot=knot; tripletlab=lab; tripletof=tof}

let simplecomadorn spos ipre scomnode = {sc_pos = spos; sc_ipreopt = ipre; sc_node=scomnode}

let structsimplecomadorn spos node = {structcompos = spos; structcomnode=node}

let _simplecomrec = simplecomadorn Sourcepos.dummy_spos

let loc_of_com = function
  | Com ct       -> ct.tripletpos
  | Structcom sc -> sc.structcompos
  
let lab_of_triplet {tripletlab=lab} = lab.lablab
let knot_of_triplet {tripletknot=knot} = knot

let is_assign {tripletof=simplecom} =
  match simplecom.sc_node with
  | Assign _ -> true
  | _        -> false
  
let is_var_assign {tripletof=simplecom} =
  match simplecom.sc_node with
  | Assign a -> Assign.is_var_assign a
  | _        -> false
  
let is_aux_assign {tripletof=simplecom} =
  match simplecom.sc_node with
  | Assign a -> Assign.is_aux_assign a
  | _        -> false
  
let rec fstlab_seq = function
  | com::_ -> fstlab_com com
  | []     -> raise Not_found
  
and fstlab_com = function
  | Com triplet  -> lab_of_triplet triplet
  | Structcom sc -> fstlab_structcom sc
  
and fstlab_structcom sc =
  match sc.structcomnode with
  | If (ft,_,_)    -> lab_of_triplet ft
  | While (ft,_)   -> lab_of_triplet ft
  | DoUntil (s,ft) ->
      (try fstlab_seq s with Not_found -> lab_of_triplet ft)
        
let sot sok string_of_alpha {tripletknot=knot; tripletlab=lab; tripletof=alpha} =
  (match knot.knotnode with
   | SimpleKnot [] -> ""
   | _             -> sok knot
  ) ^ " " ^
  Name.string_of_label lab.lablab ^ ":" ^
  string_of_alpha alpha 

let string_of_triplet string_of_alpha = sot string_of_knot string_of_alpha

let string_of_iopt = function
  | None   -> ""
  | Some f -> "[*" ^ string_of_formula f ^ "*]"

let string_of_scomnode = function
  | Skip     -> "skip"
  | Assert f -> Printf.sprintf "assert %s" (Formula.string_of_formula f)
  | Assign a -> string_of_assign a

let rec string_of_simplecom {sc_ipreopt = iopt; sc_node = c} = 
  Printf.sprintf "%s"
    (match iopt with
     | None   -> string_of_scomnode c
     | Some f -> string_of_iopt iopt ^ " " ^ string_of_scomnode c
    )
  
and string_of_com indent = function
  | Com c        -> string_of_triplet string_of_simplecom c
  | Structcom sc -> string_of_structcom indent sc
  
and string_of_seq indent cs = 
  string_of_list (string_of_com indent) (";\n" ^ indent) cs

and string_of_structcom indent sc = 
  let indent' = indent ^ "  " in
  match sc.structcomnode with 
  | If (c,s1,[])        -> "if " ^ string_of_triplet string_of_formula c ^ 
                           " then\n" ^ indent' ^ string_of_seq indent' s1 ^ 
                           "\n" ^ indent ^ "fi"
  | If (c,s1,s2)        -> "if " ^ string_of_triplet string_of_formula c ^ 
                           " then\n" ^ indent' ^ string_of_seq indent' s1 ^ 
                           "\n" ^ indent ^ "else\n" ^ indent' ^ string_of_seq indent' s2 ^ 
                           "\n" ^ indent ^ "fi"
  | While (c,s)         -> "while " ^ string_of_triplet string_of_formula c ^ 
                           " do\n" ^ indent' ^ string_of_seq indent' s ^ 
                           "\n" ^ indent ^ "od"
  | DoUntil (s,c)       -> "do\n" ^ indent' ^ string_of_seq indent' s ^ 
                           "\n" ^ indent ^ "until " ^ string_of_triplet string_of_formula c 

(* *************************** folds for com ************************* *)

let rec tripletfold f3c f3f v = function
  | Com  triplet -> f3c v triplet
  | Structcom sc -> 
      (let foldf = tripletfold f3c f3f in
       match sc.structcomnode with
       | If (ft, s1, s2) -> 
           let v = f3f v ft in
           let v = List.fold_left foldf v s1 in
           List.fold_left foldf v s2
       | While (ft, s) ->
           let v = f3f v ft in
           List.fold_left foldf v s
       | DoUntil (s, ft) ->
           let v = List.fold_left foldf v s in
           f3f v ft 
      )

let rec knotfold fk v = function
  | Com  triplet -> fk v triplet.tripletknot
  | Structcom sc -> 
      (let foldf = knotfold fk in
       match sc.structcomnode with
       | If (ft, s1, s2) -> 
           let v = fk v ft.tripletknot in
           let v = List.fold_left foldf v s1 in
           List.fold_left foldf v s2
       | While (ft, s) ->
           let v = fk v ft.tripletknot in
           List.fold_left foldf v s
       | DoUntil (s, ft) ->
           let v = List.fold_left foldf v s in
           fk v ft.tripletknot 
      )

let rec simplecomfold ff v = function
  | Com       ct -> ff v ct
  | Structcom sc -> 
      (let foldf = simplecomfold ff in
       match sc.structcomnode with
       | If (_, s1, s2) -> 
           List.fold_left foldf 
             (List.fold_left foldf v s1)
             s2
       | While (ft, s) ->
           List.fold_left foldf v s
       | DoUntil (s, ft) ->
           List.fold_left foldf v s
      )
  
  