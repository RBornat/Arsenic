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

(* There's a pattern to these things. We have P and an irec for Q.
   We take P as is, and an instance of Q which doesn't clash with P.
   In case P comes from an irec we do the same thing, because registers
   in P won't clash with Q, will they?
 *)
 
(* this is SC and INT stability : sp(P/\Q, x:=E) => P *)
let sc_stable_query _P irec =
  let instance = Intfdesc.irec_instance (Formula.frees _P) irec in
  let _Q = instance.i_pre in
  let assign = instance.i_assign in
  _recImplies (strongest_post true
                              (conjoin [_P; _Q])
                              assign
              )
              _P
  
let sc_stable_query_intfdesc _P intfdesc =
  sc_stable_query _P (Intfdesc.irec intfdesc)

(* this is EXT stability : sp(P/\Qhat, x:=E) => P *)
let ext_stable_query _P irec =   
  let instance = Intfdesc.irec_instance (Formula.frees _P) irec in
  let _Qhat = enhat Hat instance.i_pre in
  let ext_sp_check = _recImplies (strongest_post true
                                                 (conjoin [_P; _Qhat])
                                                 instance.i_assign
                                 )
                                 _P
  in
  (* sat_query (conjoin [_P; instance.i_pre]), ext_sp_check *)
  ext_sp_check

let ext_stable_query_intfdesc _P intfdesc =
  ext_stable_query _P (Intfdesc.irec intfdesc)

(* this is BO stability : sp(Phat/\Qhathat, x:=E) => Phat *)
let bo_stable_query irec1 irec2 =
  let _P = irec1.i_pre in
  let instance = Intfdesc.irec_instance (Formula.frees _P) irec2 in
  let _Phat = enhat Hat _P in
  let _Qhathat = enhat DHat instance.i_pre in
  let bo_sp_check = _recImplies (strongest_post true
                                                (conjoin [_Phat; _Qhathat])
                                                instance.i_assign
                                )
                                _Phat
  in
  bo_sp_check

let bo_stable_query_intfdescs intfdesc1 intfdesc2 =
  bo_stable_query (Intfdesc.irec intfdesc1) (Intfdesc.irec intfdesc2)
  
(* this is UEXT stability : sp(Ptilde/\Q, x:=E) => Ptilde *)
let uext_stable_query _P irec =
  let instance = Intfdesc.irec_instance (Formula.frees _P) irec in
  let _Ptilde = enhat Tilde _P in
  let _Q = instance.i_pre in
  let assign = instance.i_assign in
  let sp = strongest_post true (conjoin [_Ptilde; _Q]) assign in
  (* let sp = if Assign.is_storeconditional assign 
              then conjoin [sp; 
                            _recEqual (_recLatest Here NoHook (Location.locv (Assign.reserved assign)))
                                      (Assign.conditionally_stored assign)
                           ]
              else sp
  in 
   *)
  _recImplies sp _Ptilde

let uext_stable_query_intfdesc _P intfdesc =
  uext_stable_query _P (Intfdesc.irec intfdesc)

(* this is UO stability : sp(Ptilde/\Qtildetilde, x:=E) => Ptilde *)
let uo_stable_query irec1 irec2 =
  let _P = irec1.i_pre in
  (* let assign1 = irec1.i_assign in
     let _P = if Assign.is_storeconditional assign1 
              then conjoin [_P; 
                            _recEqual (_recLatest Here NoHook (Location.locv (Assign.reserved assign1)))
                                      (Assign.conditionally_stored assign1)
                           ]
              else _P
     in
   *)
  let instance = Intfdesc.irec_instance (Formula.frees _P) irec2 in
  let _Ptilde = enhat Tilde _P in
  let _Qtildetilde = enhat DTilde irec2.i_pre in
  let uo_sp_check = _recImplies (strongest_post true
                                                (conjoin [_Ptilde; _Qtildetilde])
                                                instance.i_assign
                                )
                                _Ptilde
  in
  uo_sp_check
              
let uo_stable_query_intfdescs intfdesc1 intfdesc2 =
  uo_stable_query (Intfdesc.irec intfdesc1) (Intfdesc.irec intfdesc2)
