open Function
open Name
open Formula

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type order = So | Lo | Bo | Uo | Go

let string_of_order order = 
  match order with
  | So -> "so"
  | Lo -> "lo"
  | Bo -> "bo"
  | Uo -> "uo"
  | Go -> "go"

let combine o1 o2 =
  match o1,o2 with
  | So, So          -> So
  | Go, Uo | Uo, Go -> Uo
  | _ , So | So , _ 
  | _ , Go | Go , _ -> raise (Invalid_argument "Order.combine")
  | _ , Uo | Uo , _ -> Uo
  | _ , Bo | Bo , _ -> Bo
  | _               -> Lo
  
let is_go = function
  | Go -> true
  | _  -> false
  
(*
    type ikind = Internal | External

    let string_of_ikind = function
      | Internal -> "Internal"
      | External -> "External"

    let quotient order ikind assertion =
      match order, ikind, !Settings.param_LocalSpec with
      (* | Go, _       , false -> _recTrue *)
      | Go, Internal, _    -> 
          let frees = Formula.frees assertion in
          let binders = NameSet.filter (not <.> Name.is_logc) frees in
          bindExists binders assertion
      | _ -> assertion
*)
