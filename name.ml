open Function

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type name      = string 
and reg        = name
and aux        = name
and var        = name  (* alpha alphanum*: reg starts with r, aux with aux, var everything else *)
and logc       = name  (* Alpha alphanum* *)
and label      = name  (* alpha alphanum*, maybe *)

let string_of_name s = s
let string_of_reg    = string_of_name
let string_of_var    = string_of_name
let string_of_logc   = string_of_name
let string_of_label  = string_of_name

let reg_of_string     r = r
let var_of_string     v = v
let logc_of_string   lc = lc
let label_of_string lab = lab

module OrderedName = struct type t = name let compare = Pervasives.compare let to_string = string_of_name end
module NameSet = MySet.Make(OrderedName)
let addname = NameSet.add
let addnames = revargs (List.fold_left (revargs addname))
let memname = NameSet.mem
let subtractname = NameSet.remove
let subtractnames = revargs (List.fold_left (revargs subtractname)) 

module LabelSet = NameSet

module NameMap = MyMap.Make (OrderedName)
module LabelMap = NameMap

(* ********************* classifying names ********************** *)

(* registers start with r, and that's that *)
let is_anyreg  name = try name.[0]='r' with Invalid_argument _ -> false
(* auxiliary registers start with raux *)
let is_auxreg  name = is_anyreg name && (try String.sub name 0 4 = "raux" with Invalid_argument _ -> false)
(* observation registers start with robs_ *)
let is_obsreg  name = is_anyreg name && (try String.sub name 0 5 = "robs_" with Invalid_argument _ -> false)
let is_realreg name = is_anyreg name && not (is_auxreg name) && not (is_obsreg name)

let obsreg_var name =
  try String.sub name 5 (String.length name - 5)
  with _ -> raise (Invalid_argument ("obsreg_var " ^ name))
  
(* anyvar includes x, y, z, aux.., and that's that.
   Which includes functions. Probably no sensible way, unless we move to a typed language,
   to deal with that.
 *)
let is_anyvar  name = try let c = name.[0] in c<>'r' && 'a'<=c && c<='z' with Invalid_argument _ -> false
let is_auxvar  name = is_anyvar name && (try String.sub name 0 3 = "aux" with Invalid_argument _ -> false)
let is_realvar name = is_anyvar name && not (is_auxvar name)

let obsreg_of_var name = if not (is_anyvar name) then
                           raise (Invalid_argument ("obsreg_of_var " ^ name))
                         else
                           "robs_" ^ name
                           
(* all other names are logical constants, including the 0:r pmsc names *)
let is_logc       name = not (is_anyreg name || is_anyvar name) (* so that Z3 oddities are included *)
let is_parsedlogc name = try let c = name.[0] in 'A'<=c && c<='Z' with Invalid_argument _ -> false

(* the only names which start with a digit are the pmscs. They are logcs *)
let pmsc_name i r = string_of_int i ^ ":" ^ r

let pmsc_parts name = 
  try let i = String.index name ':' in
      String.sub name 0 i, String.sub name (i+1) (String.length name - i - 1)
  with _ -> raise (Invalid_argument ("pmsc_parts " ^ name))

let is_pmsc name = try let c = name.[0] in '0'<=c && c<='9' with Invalid_argument _ -> false

(* *********************** new names *********************** *)

let new_unknown_string, new_name, new_var, new_reg, new_aux, new_logc =
  (* hide the references *)
  (let undecidedcount = ref 0 in
   let new_unknown_string () = 
     let n = !undecidedcount in
     undecidedcount := n+1;
     ("?" ^ string_of_int n) (* '?' signals unknown, ok in Z3 (if it matters) *)
   in

   let namecount = ref 0 in
   let new_name s = 
     let n = !namecount in
     namecount := n+1;
     s ^ "!" ^ string_of_int n (* '!' is ok in Z3 variables *)
   in
   let new_var = new_name in 
   let new_reg = new_name in 
   let new_aux = new_name in
   let new_logc = new_name in
   
   new_unknown_string, new_name, new_var, new_reg, new_aux, new_logc
  )
