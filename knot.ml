(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
open Function
open Sourcepos
open Listutils
open Order
open Stitch
open Name
open Formula
open Location

type knot = { knotloc:sourcepos; knotnode:knotnode }

and knotnode = 
  | SimpleKnot of stitch list 
  | KnotOr     of knot * knot
  | KnotAnd    of knot * knot
  | KnotAlt    of knot * knot
  
let alt_token = "\\->/"

let rec string_of_knot knot = 
  match knot.knotnode with
  | SimpleKnot stitches -> "{*" ^ string_of_list string_of_stitch ";" stitches ^ "*}"
  | KnotOr      (k1,k2) -> string_of_knot k1 ^ " \\/ "  ^ string_of_knot k2
  | KnotAnd     (k1,k2) -> string_of_knot k1 ^ " /\\ "  ^ string_of_knot k2
  | KnotAlt     (k1,k2) -> string_of_knot k1 ^ " " ^ alt_token ^ " " ^ string_of_knot k2

let knotadorn spos knotnode = { knotloc=spos; knotnode=knotnode }

(* ******************** a fold and iter for knots, why not? ************************ *)

let rec fold fstitch v knot =
  match knot.knotnode with
  | SimpleKnot ss   -> List.fold_left fstitch v ss
  | KnotOr  (k1,k2)
  | KnotAnd (k1,k2) 
  | KnotAlt (k1,k2) -> List.fold_left (fold fstitch) v [k1;k2]

let iter fstitch = fold (fun () -> fstitch) ()

(* let reservations =
     let srev ress stitch =
       match locopt_of_stitch stitch with
       | None     -> ress
       | Some loc -> if List.exists (Location.eq loc) ress
                     then ress 
                     else loc::ress
     in
     fold srev []
 *)
 
(* ******************** exists for knots, why not? ************************ *)

let rec exists pstitch knot =
  match knot.knotnode with
  | SimpleKnot ss   -> List.exists pstitch ss
  | KnotOr  (k1,k2)
  | KnotAnd (k1,k2) 
  | KnotAlt (k1,k2) -> List.exists (exists pstitch) [k1;k2]

(* ******************** a map for knots, why not? ************************ *)

(* knots contain formulas. Are the formulas stripspos'd? in a KnotMap?
   No, and it doesn't matter: in uses of KnotMap we are concerned about identity of knots. 
   Hmm.
 *)
 
module KnotMap = MyMap.Make (struct type t = knot
                                    let compare = Pervasives.compare
                                    let to_string = string_of_knot
                             end
                            )

(* ******************** preconditions need care ************************ *)

type pkind =
  | Elaboration
  | Interference

let string_of_pkind = function
  | Elaboration     -> "Elaboration" 
  | Interference    -> "Interference"

type pre = formula (* cutting out the lwarx stwcx. treatment *)
  (* | PreSingle of formula
     | PreDouble of formula * location list * formula (* unreserved, reservations, reserved *)
   *)

let string_of_pre = string_of_formula (* function
  | PreSingle f            -> "PreSingle(" ^ string_of_formula f ^ ")"
  | PreDouble (f1,locs,f2) -> "PreDouble(" ^ string_of_formula f1 
                                           ^ "," 
                                           ^ Listutils.bracketed_string_of_list string_of_location locs 
                                           ^ "."
                                           ^ string_of_formula f2 
                                           ^ ")"
 *)

let pre_fold fpre = fpre
(* let pre_fold fpre floc v = function
    | PreSingle pre                 -> fpre v pre
    | PreDouble (pre, locs, preres) -> let v = fpre v pre in
                                       let v = List.fold_left floc v locs in
                                       fpre v preres
 *)

let pre_iter fpre = pre_fold (fun () -> fpre) () 
(* let pre_iter fpre floc = pre_fold (fun () -> fpre) (fun () -> floc) () *)

let precondition_of_knot go_sat pkind knot =
  (* let okres withres s = 
       match locopt_of_stitch s with
       | None   -> true
       | Some _ -> withres
     in
   *)
  let rec ass_k (* withres *) withgo k = 
    match k.knotnode with
    | SimpleKnot stitches -> 
        (let join = conjoin <.> List.map assertion_of_stitch in
         let okgo = if withgo then (fun _ -> true) else not <.> Stitch.is_go in
         join (List.filter (okgo (* <&&> okres withres *)) stitches)
        )
    | KnotAnd     (k1,k2) -> conjoin (List.map (ass_k (* withres *) withgo) [k1;k2])
    | KnotOr      (k1,k2) 
    | KnotAlt     (k1,k2) -> disjoin (List.map (ass_k (* withres *) withgo) [k1;k2])
  in
  (* this wasn't ok: quotienting isn't the same as sat. I think ...
     let sat f = (* I hope this is ok ... maybe do it better one day *)
       let frees = NameSet.filter (Name.is_anyvar <||> Name.is_anyreg) (Formula.frees f) in
       Formula.bindExists frees f
     in
   *)
  let pre (* withres *) = 
    match pkind with
    | Interference   -> ass_k (* withres *) true knot
    | Elaboration    -> let e = ass_k (* withres *) false knot in
                        if exists ((* okres withres <&&> *) Stitch.is_go) knot then
                          (if go_sat knot.knotloc (ass_k (* withres *) true knot)
                           then e
                           else _recFalse (* not satisfiable with go in, so false *)
                          )
                        else e
  in
  (* if exists (function {stitchlocopt=Some _} -> true
                |        _                     -> false
               )
               knot
     then PreDouble (pre false, reservations knot, pre true)
     else PreSingle (pre false)
   *)
  pre
  
(* let unres_precondition_of_knot go_sat pkind knot =
     match precondition_of_knot go_sat pkind knot with
     | PreSingle pre       -> pre
     | PreDouble (pre,_,_) -> pre
 *)  
