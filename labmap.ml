open Tuple
open Sourcepos
open Option
open Listutils
open Name
open Formula
open Com
open Knot

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type scloc = 
  | DoUntilLoc of sourcepos   
  | WhileLoc   of sourcepos   
  | IfLoc      of sourcepos
  | IfArmLoc   of bool
  | ControlLoc 

let string_of_scloc = function
  | DoUntilLoc loc -> "DoUntilLoc " ^ string_of_location loc   
  | WhileLoc   loc -> "WhileLoc " ^ string_of_location loc   
  | IfLoc      loc -> "IfLoc " ^ string_of_location loc
  | IfArmLoc   b   -> "IfArmLoc " ^ string_of_bool b
  | ControlLoc     -> "ControlLoc"

type componentid =
  | CidSimplecom of simplecom triplet
  | CidControl   of formula triplet
  | CidInit      of label * formula
  | CidFinal     of label * formula
  | CidThreadPost of knot
  
let string_of_componentid = function
  | CidSimplecom ct  -> string_of_triplet string_of_simplecom ct
  | CidControl ft    -> string_of_triplet string_of_formula ft
  | CidInit  (lab,f)
  | CidFinal (lab,f) -> Printf.sprintf "{%s:%s}"
                                       (string_of_label lab)
                                       (string_of_formula f)
  | CidThreadPost k  -> string_of_knot k
  
module LabMap = Name.LabelMap

type parentid = int * scloc

let string_of_parentid = Tuple.bracketed_string_of_pair string_of_int string_of_scloc

let string_of_parentids = bracketed_string_of_list string_of_parentid

type labelid = sourcepos * componentid * parentid list

let string_of_labelid =
  Tuple.bracketed_string_of_triple 
    string_of_location 
    string_of_componentid
    string_of_parentids

type labmap = labelid LabMap.t

let string_of_labmap = LabMap.to_string string_of_labelid

let bad s lab labmap =
  raise (Invalid_argument (Printf.sprintf "Not_found LabMap.%s %s %s"
                                          s
                                          (Name.string_of_label lab)
                                          (string_of_labmap labmap)
                          )
        )

let is_control lab labmap =
  try match sndof3 (LabMap.find lab labmap) with
      | CidControl _ -> true
      | _            -> false
  with Not_found     -> bad "is_control" lab labmap

let get_parents lab labmap =
  try thrdof3 (LabMap.find lab labmap) 
  with Not_found -> bad "get_parents" lab labmap

let get_cid lab labmap =
  try sndof3 (LabMap.find lab labmap) 
  with Not_found -> bad "get_cid" lab labmap

let strictly_encloses outer inner =
  match outer, inner with 
  | _     , [] -> false
  | []    , _  -> true
  | pid::_, _  -> outer<>inner && List.mem pid inner

let encloses outer inner =
  outer=inner || strictly_encloses outer inner
  
let rec tightest_loop parents =
  match parents with
  | []                           -> []
  | (_, ControlLoc  ) :: parents
  | (_, IfLoc      _) :: parents
  | (_, IfArmLoc   _) :: parents -> tightest_loop parents
  | (_, DoUntilLoc _) :: _ 
  | (_, WhileLoc   _) :: _       -> parents

let rec common_ancestors bparents cparents =
  let bparents = tightest_loop bparents in
  let cparents = tightest_loop cparents in
    match bparents, cparents with
    | []                      , _ 
    | _                       , []                       -> []
    | (bn, _ as bp)::bparents', (cn, _ as cp)::cparents' -> 
        if bn<cn then common_ancestors bparents cparents' else
        if cn<bn then common_ancestors bparents' cparents else
        if bp=cp then bparents                            else
          common_ancestors bparents' cparents'

(* find the loosest loop (if there is one) that is outside innerps, but
   inside the common ancestor of outerps and innerps.
 *)
let weakest_inner_loop outerps innerps =
  let outerps = common_ancestors outerps innerps in
  let rec wil ips =
    if outerps=ips then None
    else
      match ips with 
      | []                        -> None
      | (_, DoUntilLoc _) :: ips'
      | (_, WhileLoc   _) :: ips' -> wil ips' |~~ (fun _ -> Some ips)
      | _                 :: ips' -> wil ips'
  in
  wil innerps
  
let rec enclosing_if parents =
  match parents with 
  | []                   -> []
  | (_, IfArmLoc _) :: _
  | (_, IfLoc    _) :: _ -> parents
  | _ :: parents         -> enclosing_if parents
  
let pidopt = function
  | []     -> None
  | pid::_ -> Some pid 