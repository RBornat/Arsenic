open Function
open Option
open Tuple
open Name
open Formula
open Listutils
open MySet
open MyMap

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type ftype = 
  | Bool 
  | Int 
  | TupleType of ftype list 
  | FuncType of ftype list * ftype
  | ArrayType of ftype
  | FTypeVar of ftypevarid
  | VarType of ftype (* for Z3 translation purposes *)

and ftypevarid = Name.name (* starts with '?' *)

let _TupleType ts = TupleType ts
let _FuncType ts t = FuncType (ts,t)
let _ArrayType t = ArrayType t
let _VarType t = VarType t

let rec string_of_ftype = function
  | Bool            -> "Bool"
  | Int             -> "Int"
  | TupleType    ts -> "TupleType " ^ bracketed_string_of_list string_of_ftype ts 
  | FuncType (ts,t) -> "FuncType " ^ bracketed_string_of_pair (bracketed_string_of_list string_of_ftype)
                                                              string_of_ftype 
                                                              (ts,t)
  | ArrayType     t -> "ArrayType " ^ string_of_ftype t
  | FTypeVar      s -> "FTypeVar " ^ s
  | VarType       t -> "VarType (" ^ string_of_ftype t ^ ")"
  
let string_of_ftypecxt = 
  string_of_assoc (fun n -> "\n\t" ^ string_of_name n) string_of_ftype " : " ";"

let string_of_binder_ftypecxt =
  string_of_assoc (fun f -> "\n\t" ^ string_of_formula f) string_of_ftype " : " ";" 

let optmap optf t =
  let rec trav t = 
    match optf t with
    | Some _ as result -> result
    | None             -> 
        match t with
        | Bool 
        | Int
        | FTypeVar _       -> None
        | TupleType ts     -> optmap_any trav ts &~~ (_Some <.> _TupleType) 
        | ArrayType t      -> trav t &~~ (_Some <.> _ArrayType) 
        | FuncType (ts, t) -> (optmap_any trav ts &~~ 
                                (_Some <.> (fun ts -> FuncType (ts, either t (trav t)))))
                              |~~
                              (fun () -> trav t &~~ (_Some <.> (fun t -> FuncType (ts,t))))
        | VarType t        -> trav t &~~ (_Some <.> _VarType)
  in
  trav t
  
let map optf = optmap optf ||~ id
    
module FtypeSet = MySet.Make (struct type t = ftype 
                                     let compare = Pervasives.compare 
                                     let to_string = string_of_ftype
                              end
                             )
let addftype = FtypeSet.add
let addftypes = Function.revargs (List.fold_left (Function.revargs addftype))

module FtypeMap = MyMap.Make (struct type t = ftype 
                                     let compare = Pervasives.compare 
                                     let to_string = string_of_ftype
                              end
                             )