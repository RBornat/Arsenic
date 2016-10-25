open Function
open Option
open Sourcepos
open Intfdesc
open Formula
open Com
open Knot

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let threadnum = ref 0
let threadcount = ref 1

type threadbody = 
  | Threadseq   of seq 
  | Threadfinal of formula

(* these things can appear in programs and in threads. Because program opens thread, 
   I have to put them here
 *)
type header = (* also trailer, actually *)
  | AssertHdr of positionedlabel * formula
  | GivenHdr  of formula
  | MacroHdr  of Name.name * Name.name list * formula
  | TMacroHdr of Name.name * Name.name list * thread
  | GuarHdr   of intfdesc list
  | RelyHdr   of intfdesc list
  
and thread = { t_pos     : sourcepos;
               t_hdrs    : header list;                            (* for tolatex *)
               t_guar    : intfdesc list;                          (* guarantee *)
               t_body    : threadbody;                             (* body *)
               t_postopt : knot option;                            (* postcondition *)
               t_relyopt : intfdesc list option;                   (* rely, maybe *)
               t_trlrs   : header list                             (* for tolatex *)
             }

let string_of_state_assertion f = "{ " ^ string_of_formula f ^ " }"

let string_of_guarantee gs =
  "guar [" ^ string_of_intfdescs gs ^ "]"
  
let string_of_define (name, formula) =
  "define " ^ Name.string_of_name name ^ " " ^ string_of_formula formula

let string_of_rely rs =
  "rely [" ^ string_of_intfdescs rs ^ "]"
  
let string_of_thread {t_guar=guarantee; t_body=body; t_postopt=postopt; t_relyopt=relyopt} =
  sofirst_list string_of_guarantee "\n" guarantee ^
  (match body with
   | Threadseq seq -> string_of_seq "" seq
   | Threadfinal f -> string_of_state_assertion f
  ) ^
  solast "\n" string_of_knot postopt ^
  solast "\n" (solast_list "\n" string_of_rely) relyopt

let threadloc {t_pos=spos} = spos

let threadseq {t_body=body} =
  match body with
  | Threadseq seq -> seq
  | _             -> []
  
(* **************************** folds for thread **************************** *)

let assertionfold af v thread =
  let nobinders = Name.NameSet.empty in
  let kf v =
    Knot.fold (fun v -> af nobinders v <.> Stitch.assertion_of_stitch) v 
  in
  let intff v intfdesc = af (Intfdesc.binders intfdesc) v (Intfdesc.pre intfdesc) in
  let v = List.fold_left intff v thread.t_guar in
  let v = 
    match thread.t_body with
    | Threadseq seq -> List.fold_left (Com.knotfold kf) v seq 
    | Threadfinal f -> af nobinders v f
  in
  let v = 
    match thread.t_postopt with
    | Some knot -> kf v knot
    | _         -> v
  in
  match thread.t_relyopt with
  | Some intfs -> List.fold_left intff v intfs
  | None       -> v

let knotfold kf v thread =
  match thread.t_body with
  | Threadseq seq -> List.fold_left (Com.knotfold kf) v seq 
  | Threadfinal f -> v

let tripletfold fcom ff v thread =
  match thread.t_body with
  | Threadseq seq -> List.fold_left (Com.tripletfold fcom ff) v seq 
  | Threadfinal f -> v

(* let substitute mapping thread =
  let doit = Formula.subst mapping in
  let do_knot =
    Knot.map (fun stitch -> doit (Stitch.assertion_of_stitch Order.External stitch)) 
  in
  let intff intfdesc = af v (Intfdesc.pre intfdesc) in
  let v = List.fold_left intff v thread.t_guar in
  let v = 
    match thread.t_body with
    | Threadseq seq -> List.fold_left (Com.knotfold kf) v (threadseq thread) 
    | Threadfinal f -> af v f
  in
  let v = 
    match thread.t_postopt with
    | Some knot -> kf v knot
    | _         -> v
  in
  match thread.t_relyopt with
  | Some intfs -> List.fold_left intff v intfs
  | None       -> v
 *)
 
 let fot frees { t_guar    = guar;
                 t_body    = body;
                 t_postopt = postopt;
                 t_relyopt = relyopt
               } =
   let frees = List.fold_left Intfdesc.fointfd frees guar in
   let frees = 
     match body with
     | Threadseq   s -> List.fold_left Com.focom frees s
     | Threadfinal f -> Formula.fof frees f
   in
   let frees =
     match postopt with
     | Some knot -> Knot.fok frees knot
     | None      -> frees
   in
   match relyopt with
   | Some rely -> List.fold_left Intfdesc.fointfd frees rely
   | None      -> frees

let frees = fot Name.NameSet.empty
