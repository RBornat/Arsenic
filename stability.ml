open Function
open Tuple
open Option
open Settings
open Name
open Formula
open Intfdesc
open Strongestpost
open Location
open Assign

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let sat_query query =
  if !Settings.param_usesat || !Settings.param_SCloc then query else _recTrue

let sc_stable_query assertion pre assign =
  _recImplies (strongest_post true
                              (conjoin [assertion; pre])
                              assign
              )
              assertion
  
let sc_stable_query_intfdesc assertion intfdesc =
  let instance = Intfdesc.instance (Formula.frees assertion) intfdesc in
  sc_stable_query assertion instance.i_pre instance.i_assign

let ext_stable_checks with_scloc assertion irec =   
  let instance = Intfdesc.irec_instance (Formula.frees assertion) irec in
  let conjoins = 
    if with_scloc && !Settings.param_SCloc then
      List.map (function VarLoc v         -> let v = _recFname v in
                                             _recEqual v (hatted false v)
                |        ArrayLoc (v,ixf) -> let v = _recFname v in
                                             let arraysel = _recArraySel v ixf in
                                             _recEqual arraysel (hatted false arraysel)
               )
               (fstof2 (List.split (Assign.loces instance.i_assign)))
    else []
  in
  let hatted_pre = hatted false instance.i_pre in
  let ext_sp_check = _recImplies (strongest_post true
                                                 (conjoin (assertion::hatted_pre::conjoins))
                                                 instance.i_assign
                                 )
                                 assertion
  in
  sat_query (conjoin [assertion; instance.i_pre]), ext_sp_check

let bo_stable_query assertion irec =
  sndof2 (ext_stable_checks false assertion irec)

let bo_stable_query_intfdesc assertion intfdesc =
  bo_stable_query assertion (Intfdesc.irec intfdesc)

let bo_stable_query_irecs intf1 intf2 =
  let assertion = intf1.i_pre in
  let assign1 = intf1.i_assign in
  let assertion = if Assign.is_storeconditional assign1 
                  then conjoin [assertion; _recLatest Here Now (Location.locv (Assign.reserved assign1))]
                  else assertion
  in
  bo_stable_query (bindExists intf1.i_binders assertion) intf2
              
let ext_stable_queries = ext_stable_checks true

let ext_stable_queries_intfdesc assertion intfdesc =
  ext_stable_queries assertion (Intfdesc.irec intfdesc)
  
let uo_stable_checks assertion irec =
  let instance = Intfdesc.irec_instance (Formula.frees assertion) irec in
  let uo_sp_check =
    let hatted_p = hatted true assertion in
    _recImplies (strongest_post true
                                (conjoin [hatted_p; instance.i_pre])
                                instance.i_assign
                )
                hatted_p
  in
  sat_query (conjoin [assertion; instance.i_pre]), uo_sp_check

let uo_stable_queries_intfdesc assertion intfdesc =
  uo_stable_checks assertion (Intfdesc.irec intfdesc)

let uo_stable_internal assertion irec =
  sndof2 (uo_stable_checks assertion irec)
  
let uo_stable_internal_intfdesc assertion intfdesc =
  uo_stable_internal assertion (Intfdesc.irec intfdesc)
  
let uo_stable_internal_irecs irec1 irec2 =
  uo_stable_internal (bindExists irec1.i_binders irec1.i_pre) irec2