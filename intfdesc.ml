open Sourcepos
open Function
open Tuple
open Option
open Formula
open Name
open Assign
open Listutils

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
(* we now allow internal interference -- i.e. register assigns *)
type intfdesc = {ipos: sourcepos; irec: intfrec}

and intfrec = { i_binders  : NameSet.t; 
                i_pre      : formula;
                i_assign   : assign
              }
          
let string_of_binders binders =
  match NameSet.elements binders with 
  | [] -> ""
  | ns -> Printf.sprintf "[%s]." (string_of_list string_of_name "," ns)
  
let string_of_intfrec i = 
  string_of_binders  i.i_binders ^
  string_of_formula  i.i_pre     ^ 
  " | "                          ^ 
  string_of_assign i.i_assign

let string_of_intfdesc i = string_of_intfrec i.irec

let string_of_intfdescs = string_of_list string_of_intfdesc "; "

let intfadorn sourcepos irec = {ipos = sourcepos; irec=irec}

let mk_intfdesc spos pre assign =
  let freers = if is_var_assign assign then
                 let frees = NameSet.union (Formula.frees pre) (Assign.frees assign) in
                 NameSet.filter Name.is_anyreg frees 
               else
                 NameSet.empty
  in
  {ipos=spos; irec={i_binders=freers; i_pre=pre; i_assign=assign}}
  
(* we don't change v here. If you want to change it, do it in f_intf.
   And for some reason we lose the label. Hmm.
   And what do we do about bounds, eh? Better be careful in f_intf.
 *)
let optmap f_intf f_formula intfdesc =
  match f_intf intfdesc with 
  | Some _ as result -> result
  | None ->
      let i = intfdesc.irec in
      let preopt = Formula.optmap f_formula i.i_pre in
      let assignopt = Assign.optmap (fun _ _ -> None) f_formula i.i_assign in
      match preopt, assignopt with
      | None, None -> None
      | _          -> Some {intfdesc with irec = {i with i_pre    = either i.i_pre    preopt;
                                                         i_assign = either i.i_assign assignopt
                                                 }
                           }

let map f_intf f_formula = anyway (optmap f_intf f_formula)

let rec optstripspos intfdesc =
  optmap 
    (function  | {ipos=spos} when spos=dummy_spos -> None
               | intfdesc                         -> Some (stripspos {intfdesc with ipos=dummy_spos}))
    Formula.stripspos_opt 
    intfdesc
    
and stripspos intfdesc = (optstripspos ||~ id) intfdesc
  
let eq i1 i2 = stripspos i1 = stripspos i2

let sameinterferences i1s i2s =
  let striploc_and_sort = List.sort Pervasives.compare <.> List.map stripspos in
  try 
    List.for_all (uncurry2 (=)) 
                 (List.combine (striploc_and_sort i1s) (striploc_and_sort i2s))
  with Invalid_argument _ -> false

let irec intfdesc = intfdesc.irec

let assign intfdesc =  
  let i = intfdesc.irec in
  i.i_assign

let assigned = Assign.assigned <.> assign
  
let loces intfdesc =  
  let i = intfdesc.irec in
  Assign.loces (i.i_assign)

let assigned_vars intfdesc = 
  let locs, _ = List.split (loces intfdesc) in
  (* List.map Location.locv *) locs

let actualvar = List.hd <.> assigned_vars 

let binders intfdesc =  
  let i = intfdesc.irec in
  i.i_binders

let pre intfdesc = 
  let i = intfdesc.irec in
  i.i_pre
  
(* I don't know what this is about
   let preprop intfdesc =  
     let i = intfdesc.irec in
     let rec preprop f =
       match f.fnode with
       | LogArith (f1, And, f2) -> rplacAnd f (preprop f1) (preprop f2)
       | Binder (Forall, x, bf) -> rplacForall f x (preprop bf)
       | _                      -> Formula.universal NoHook f (* what the heck? *)
     in
     {intfdesc with irec={intfdesc.irec with i_pre = preprop i.i_pre}}
 *)

let fointfd frees intfdesc = 
  let ifrees = Formula.fof (Assign.foa frees (assign intfdesc)) (pre intfdesc) in
  NameSet.union frees (NameSet.diff ifrees (binders intfdesc))
  
let frees = fointfd NameSet.empty

let pre_frees intfdesc =
  NameSet.diff (Formula.frees (pre intfdesc)) (binders intfdesc)
  
let assign_frees intfdesc =
  NameSet.diff (Assign.frees (assign intfdesc)) (binders intfdesc) 
let irec_instance captures irec =
  let default () = {irec with i_binders=NameSet.empty} in
  if not (is_var_assign (irec.i_assign)) then default ()
  else
    (* make sure that binders don't clash with captures *)
    let binders = irec.i_binders in
    if NameSet.exists (fun binder -> NameSet.mem binder captures) binders then
      let mapping = 
        List.map (fun binder -> binder, _recFname (new_name binder)) (NameSet.elements binders) 
      in
      {i_binders=NameSet.empty; 
       i_pre    = Formula.substitute mapping irec.i_pre;
       i_assign = Assign.substitute mapping irec.i_assign
      }
    else
      default ()

let instance captures intfdesc =  
  let irec = intfdesc.irec in
  irec_instance captures irec
