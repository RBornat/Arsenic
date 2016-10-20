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

type ipre = formula (*
  | IpreSimple of formula
  | IpreRes    of formula
  | IpreDouble of formula * formula (* normal, reserved *)
 *)  
 
let string_of_ipre = string_of_formula (* function
  | IpreSimple f       -> "[*" ^ string_of_formula f ^ "*]"
  | IpreRes    f       -> "[* *:" ^ string_of_formula f ^ "*]"
  | IpreDouble (f1,f2) -> "[*" ^ string_of_formula f1 ^ "; *:" ^ string_of_formula f2 ^ "*]"
 *)
 
type simplecom = {sc_pos: sourcepos; sc_ipreopt: ipre option; sc_node: scomnode}

and scomnode =
  | Skip
  | Assert of formula
  | Assign of assign

and structcom = {structcompos: sourcepos; structcomnode: structcomnode}

and structcomnode = 
  | If of condition * seq * seq
  | While of condition * seq
  | DoUntil of seq * condition 

and condition = 
  | CExpr of formula triplet
  | CAssign of simplecom triplet
  
and 'a triplet = 
  { tripletpos : sourcepos;
    tripletknot: knot; 
    tripletlab : positionedlabel; 
    tripletof  : 'a 
  }

and com = 
  | Com of simplecom triplet
  | Structcom of structcom
  
and seq = com list

let tripletadorn spos knot lab tof = {tripletpos=spos; tripletknot=knot; tripletlab=lab; tripletof=tof}

let simplecomadorn spos ipre scomnode = {sc_pos = spos; sc_ipreopt = ipre; sc_node=scomnode}

let structcomadorn spos node = {structcompos = spos; structcomnode=node}

let _simplecomrec = simplecomadorn Sourcepos.dummy_spos

let sot sok string_of_alpha {tripletknot=knot; tripletlab=lab; tripletof=alpha} =
  (match knot.knotnode with
   | SimpleKnot [] -> ""
   | _             -> sok knot
  ) ^ " " ^
  Name.string_of_label lab.lablab ^ ":" ^
  string_of_alpha alpha 

let string_of_triplet string_of_alpha = sot string_of_knot string_of_alpha

let string_of_scomnode = function
  | Skip     -> "skip"
  | Assert f -> Printf.sprintf "assert %s" (Formula.string_of_formula f)
  | Assign a -> string_of_assign a

let rec string_of_simplecom {sc_ipreopt = iopt; sc_node = c} = 
  Printf.sprintf "%s"
    (match iopt with
     | None      -> string_of_scomnode c
     | Some ipre -> string_of_ipre ipre ^ " " ^ string_of_scomnode c
    )
  
and string_of_com indent = function
  | Com c        -> string_of_triplet string_of_simplecom c
  | Structcom sc -> string_of_structcom indent sc
  
and string_of_seq indent cs = 
  string_of_list (string_of_com indent) (";\n" ^ indent) cs

and string_of_structcom indent sc = 
  let indent' = indent ^ "  " in
  match sc.structcomnode with 
  | If (c,s1,[])        -> "if " ^ string_of_condition c ^ 
                           " then\n" ^ indent' ^ string_of_seq indent' s1 ^ 
                           "\n" ^ indent ^ "fi"
  | If (c,s1,s2)        -> "if " ^ string_of_condition c ^ 
                           " then\n" ^ indent' ^ string_of_seq indent' s1 ^ 
                           "\n" ^ indent ^ "else\n" ^ indent' ^ string_of_seq indent' s2 ^ 
                           "\n" ^ indent ^ "fi"
  | While (c,s)         -> "while " ^ string_of_condition c ^ 
                           " do\n" ^ indent' ^ string_of_seq indent' s ^ 
                           "\n" ^ indent ^ "od"
  | DoUntil (s,c)       -> "do\n" ^ indent' ^ string_of_seq indent' s ^ 
                           "\n" ^ indent ^ "until " ^ string_of_condition c 

and string_of_condition = function
  | CExpr   ft -> string_of_triplet string_of_formula ft
  | CAssign ct -> string_of_triplet string_of_simplecom ct
  
let is_simplecom = function
  | Com _ -> true
  | _     -> false

let loc_of_com = function
  | Com ct       -> ct.tripletpos
  | Structcom sc -> sc.structcompos
  
let lab_of_triplet {tripletlab=lab} = lab.lablab
let knot_of_triplet {tripletknot=knot} = knot

let poslab_of_condition c = match c with 
                            | CExpr   ft -> ft.tripletlab
                            | CAssign ct -> ct.tripletlab     

let knot_of_condition c = match c with 
                          | CExpr   ft -> ft.tripletknot
                          | CAssign ct -> ct.tripletknot     

let is_assign {tripletof=simplecom} =
  match simplecom.sc_node with
  | Assign _ -> true
  | _        -> false
  
let is_reg_assign {tripletof=simplecom} =
  match simplecom.sc_node with
  | Assign a -> Assign.is_reg_assign a
  | _        -> false
  
let is_var_assign {tripletof=simplecom} =
  match simplecom.sc_node with
  | Assign a -> Assign.is_var_assign a
  | _        -> false
  
let is_aux_assign {tripletof=simplecom} =
  match simplecom.sc_node with
  | Assign a -> Assign.is_aux_assign a
  | _        -> false
  
(* let is_loadreserved {tripletof=simplecom} =
     match simplecom.sc_node with
     | Assign a -> Assign.is_loadreserved a
     | _        -> false
  
   let is_storeconditional {tripletof=simplecom} =
     match simplecom.sc_node with
     | Assign a -> Assign.is_storeconditional a
     | _        -> false
 *)
 
let assign ct =
  match ct.tripletof.sc_node with
  | Assign a -> a
  | _        -> raise (Invalid_argument (Printf.sprintf "%s Com.assign %s" 
                                             (string_of_sourcepos ct.tripletpos)
                                             (string_of_triplet string_of_simplecom ct)
                                        )
                      )
  
(* let reserved ct =
     match ct.tripletof.sc_node with
     | Assign a -> Assign.reserved a
     | _        -> raise (Invalid_argument (Printf.sprintf "%s Com.reserved %s" 
                                                (string_of_sourcepos ct.tripletpos)
                                                (string_of_triplet string_of_simplecom ct)
                                           )
                         )
 *)
 
let rec fstlab_seq = function
  | com::_ -> fstlab_com com
  | []     -> raise Not_found
  
and fstlab_com = function
  | Com triplet  -> lab_of_triplet triplet
  | Structcom sc -> fstlab_structcom sc
  
and fstlab_structcom sc =
  match sc.structcomnode with
  | If (c,_,_)    -> lab_of_condition c
  | While (c,_)   -> lab_of_condition c
  | DoUntil (s,c) ->
      (try fstlab_seq s with Not_found -> lab_of_condition c)

and lab_of_condition = function
  | CExpr   ft -> lab_of_triplet ft
  | CAssign ct -> lab_of_triplet ct
  
(* *************************** folds for com ************************* *)

let rec tripletfold fcom ff v com = 
  match com with
  | Com triplet  -> fcom v triplet
  | Structcom sc -> 
      (let fseq = tripletfold fcom ff in
       let fcond v c =
         match c with
         | CExpr   ft -> ff v ft
         | CAssign ct -> fcom v ct
       in
       match sc.structcomnode with
       | If (c, s1, s2) -> 
           let v = fcond v c in
           let v = List.fold_left fseq v s1 in
           List.fold_left fseq v s2
       | While (c, s) ->
           let v = fcond v c in
           List.fold_left fseq v s
       | DoUntil (s, c) ->
           let v = List.fold_left fseq v s in
           fcond v c 
      )

let rec knotfold fk v = function
  | Com  triplet -> fk v triplet.tripletknot
  | Structcom sc -> 
      (let fseq = knotfold fk in
       match sc.structcomnode with
       | If (c, s1, s2) -> 
           let v = fk v (knot_of_condition c) in
           let v = List.fold_left fseq v s1 in
           List.fold_left fseq v s2
       | While (c, s) ->
           let v = fk v (knot_of_condition c) in
           List.fold_left fseq v s
       | DoUntil (s, c) ->
           let v = List.fold_left fseq v s in
           fk v (knot_of_condition c) 
      )

let rec simplecomfold fsimplecom v = function
  | Com       ct -> fsimplecom v ct
  | Structcom sc -> 
      (let fseq = simplecomfold fsimplecom in
       let fcond v c =
         match c with 
         | CExpr   _  -> v
         | CAssign ct -> fsimplecom v ct
       in
       match sc.structcomnode with
       | If (c, s1, s2) -> 
           List.fold_left fseq 
             (List.fold_left fseq (fcond v c) s1)
             s2
       | While (c, s) ->
           List.fold_left fseq (fcond v c) s
       | DoUntil (s, c) ->
           fcond (List.fold_left fseq v s) c
      )
  
  