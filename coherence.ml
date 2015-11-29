open Function
open Name
open Settings
open Formula
open Ftype
open Typecheck
open Listutils
open Modality

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let coherence_variables = ref NameSet.empty

(* the axioms: universally quantified for all free names *)
(* because Z3 doesn't have polymorphic functions, we have to instantiate these for
   each of the types of coherence variable that we encounter.   
 *)
(* coherence is an ordering, not a modality. Silly boy. *)
         
(* Irreflexive makes sense. Simplifies life, mostly. But careful with observer threads. *)
let irreflexive = "_c(x,A,B) => A!=B"

(* only one kind of observation. We can't deduce anything from _c(x,A,B), btw. *)
let observed = "ouat(ouat(x=A)/\\x=B)/\\A!=B/\\_cv(x)=>_c(x,A,B)"

(* it's not in the ordering if it isn't a coherence variable. But we can't say
   that writes have caught up with us so that x!=A.
 *)
let membership = "_c(x,A,B)=>_cv(x)"

(* it is transitive *)
let transitive = "_c(x,A,B)/\\_c(x,B,C)=>_c(x,A,C)"

(* and antisymmetric *)
let antisymmetric = "_c(x,A,B)=>!_c(x,B,A)"         

(* it is not safe to deduce ouat(x=A) or ouat(x=B) from _c(x,A,B). 
   In R and in 2+2W coherence may be reasoned about in the absence of prior observation.
   Operationally, _c(x,A,B) may hold even though we haven't seen its writes, so if we 
   could conclude !_c(x,A,B) from !ouat(x=A), say, we drop into a big hole. Anyway, this
   was so in the Ned proofchecker, and if we have the axiom
   
        _c(x,A,B)=>ouat(x=A/\\ouat(x=B))
        
   then we get a proof of R with bo ordering in the sender and lo in the receiver. Not
   what we want at all.
   
   Nevertheless we can deduce from _c(x,A,B) that we haven't seen A and B in the wrong
   order.
 *)
let history = "_c(x,A,B)=>!(ouat(x=A/\\ouat(x=B)))"

let coherence_axioms = 
  List.map Parseutils.parse_axiom
           [   irreflexive      ;       
               observed         ;       
               membership       ;
               transitive       ;       
               antisymmetric    ;         
               (* history          ; *)
               "true"
           ]

(* this one may be needed somewhere ... the basic fact *)
let uniquewrites =
  "_cv(x)/\\A!=B => fandw (forall (i,j,k) (0>=i>=j>=k => !((x=A)@H@i/\\(x=B)@H@j/\\(x=A)@H@k)))"
  
(* this is the pms axiom: all the writes have happened *)
let pms_axiom = Parseutils.parse_axiom "_c(x,A,B)=>_cv(x)/\\x!=A"
