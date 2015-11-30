open Function
open Tuple
open Option
open Name
open Formula
open Location
open Listutils

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type assign = 
  | RbecomesE  of reg * formula                        (* real := pure or aux := auxpure *)
  | LocbecomesEs of bool * (location * formula) list   (* bool for load logical; first real/real or aux/auxpure, rest aux/auxpure *)
  | RsbecomeLocs of bool * (reg list * location) list  (* bool for store conditional; first real/real or aux/auxpure, rest aux/aux *) 

type synchro =
  | LoadLogical      (* :=* *)
  | StoreConditional (* *:= *)
  | LocalAssign      (* := *)

let string_of_synchro = function
  | LoadLogical      -> ":=*"
  | StoreConditional -> "*:="
  | LocalAssign      -> ":= *"

let string_of_assign a =
  let soa synchro lhs rhs = Printf.sprintf "%s %s %s" lhs (string_of_synchro synchro) rhs in
  match a with
  | RbecomesE (r,f)    -> soa LocalAssign (Name.string_of_reg r) (string_of_formula f)
  | LocbecomesEs (b,locfs) -> 
      (let op = if b then StoreConditional else LocalAssign in
       match locfs with
       | [loc,f] -> soa op (string_of_location loc) (string_of_formula f)
       | _       ->
         let locs, fs = List.split locfs in
         let string_of_rhs f =
           match f.fnode with
           | Tuple _ -> "(" ^ string_of_formula f ^ ")"
           | _       -> string_of_formula f
         in
         soa op (string_of_list string_of_location "," locs) (string_of_list string_of_rhs "," fs)
      )
  | RsbecomeLocs (b,rslocs) -> 
      (let op = if b then LoadLogical else LocalAssign in
       match rslocs with
       | [rs,loc] -> soa op (string_of_list Name.string_of_reg "," rs) (string_of_location loc)
       | _        ->
         let rss, locs = List.split rslocs in
         let string_of_lhs rs =
           match rs with
           | [r] -> Name.string_of_reg r
           | _   -> "(" ^ string_of_list Name.string_of_reg "," rs ^ ")"
         in
         soa op (string_of_list string_of_lhs "," rss) (string_of_list string_of_location "," locs)
      )

let is_aux_assign = function 
  | RbecomesE  (r,_)                       -> Name.is_auxreg r 
  | LocbecomesEs (_,(VarLoc v,_)::_)       -> Name.is_auxvar v
  | LocbecomesEs (_,(ArrayLoc (v,_),_)::_) -> Name.is_auxvar v
  | RsbecomeLocs (_,((r::_),_)::_)         -> Name.is_auxreg r
  | a                                      -> raise (Invalid_argument ("Assign.is_aux_assign " ^ string_of_assign a))
  
let is_var_assign = function 
  | LocbecomesEs _ -> true
  | _              -> false
  
let is_reg_assign = function 
  | RbecomesE  _ 
  | RsbecomeLocs _ -> true
  | LocbecomesEs _ -> false
  
let loces_of_assign = function
  | LocbecomesEs (b,loces) -> loces
  | assign                 -> raise (Invalid_argument ("Assign.loces_of_assign " ^ string_of_assign assign))


let frees assign = 
  let loc_frees = function
    | VarLoc         v -> NameSet.singleton v
    | ArrayLoc (v,ixf) -> NameSet.add v (Formula.frees ixf)
  in
  match assign with
  | RbecomesE  (r,e)       -> NameSet.add r (Formula.frees e) 
  | LocbecomesEs (b,loces) -> 
      List.fold_left (fun set (location,e) -> NameSet.union set (NameSet.union (loc_frees location) (Formula.frees e)))
                     NameSet.empty
                     loces
  | RsbecomeLocs (b,rsvs)  -> 
      List.fold_left (fun set (rs,location) -> NameSet.union set (NameSet.union (loc_frees location) (NameSet.of_list rs)))
                     NameSet.empty
                     rsvs
                     
(* designed to be folded *)
let formulas fs = function
  | RbecomesE (r,e)         -> e::fs
  | LocbecomesEs (b,loces)  -> 
      List.fold_left (fun fs -> (function (VarLoc v,e)         -> e::fs
                                 |        (ArrayLoc (v,ixf),e) -> ixf::e::fs
                                )
                     )
                     fs
                     loces
  | RsbecomeLocs (b,rslocs) -> 
      List.fold_left (fun fs -> (function (_,VarLoc v)         -> fs
                                 |        (_,ArrayLoc (v,ixf)) -> ixf::fs
                                )
                     )
                     fs
                     rslocs

let assigned = function
  | RbecomesE (r,e)        -> NameSet.singleton r
  | LocbecomesEs (b,loces) -> NameSet.of_list (List.map (function (VarLoc v,e)       -> v
                                                         |        (ArrayLoc (v,_),e) -> v
                                                        )
                                                        loces
                                              )
  | RsbecomeLocs (b,rsv_s) -> NameSet.of_list (List.concat (fstof2 (List.split rsv_s)))

let optmap af ff a =
  let opmloc = function VarLoc v         -> None
               |        ArrayLoc (v,ixf) -> Formula.optmap ff ixf 
                                            &~~ (_Some <.> _ArrayLoc v)
  in
  match af ff a with
  | None -> (match a with 
             | RbecomesE (r,e)         -> optmap ff e 
                                          &~~ (fun e' -> Some (RbecomesE (r,e')))
             | LocbecomesEs (b,loces)  -> let locs, es = List.split loces in
                                          optionpair_either (optmap_any opmloc) locs
                                                            (optmap_any (Formula.optmap ff)) es
                                          &~~ (fun (locs,es) -> Some (LocbecomesEs (b,List.combine locs es)))
             | RsbecomeLocs (b,rslocs) -> let rss, locs = List.split rslocs in
                                          optmap_any opmloc locs
                                          &~~ (fun locs -> Some (RsbecomeLocs (b,List.combine rss locs))) 
            )
  | r                         -> r

let map af ff = anyway (optmap af ff)

let substitute mapping = function (* does locs as well *)
  | LocbecomesEs (b,loces) -> 
      LocbecomesEs (b,List.map (function (VarLoc v,e)         -> VarLoc v, Formula.substitute mapping e
                                |        (ArrayLoc (v,ixf),e) -> ArrayLoc (v, Formula.substitute mapping ixf),
                                                                 Formula.substitute mapping e
                               ) 
                               loces
                   ) 
  | a                    -> a

let optstriploc = optmap (fun ff a -> None) Formula.optstriploc

let striploc = optstriploc ||~ id

let eq a1 a2 = striploc a1 = striploc a2
