open Name
open Formula

type location = VarLoc of var | ArrayLoc of var * formula

let _recFloc = function
  | VarLoc v         -> _recFname v (* due to cheating it might be a register ... *)
  | ArrayLoc (v,ixf) -> _recArraySel (_recFname v) ixf

let locv = function
  | VarLoc v       -> v
  | ArrayLoc (v,_) -> v

let string_of_location = function
  | VarLoc v       -> Name.string_of_var v
  | ArrayLoc (v,e) -> Name.string_of_var v ^ "[" ^ string_of_formula e ^ "]"

let _ArrayLoc v e = ArrayLoc (v,e)

let eq l1 l2 =
  match l1, l2 with
  | VarLoc v1         , VarLoc v2          -> v1=v2
  | ArrayLoc (a1,idx1), ArrayLoc (a2,idx2) -> a1=a2 && Formula.eq idx1 idx2
  | _                                      -> false
  
let stripspos loc = 
  match loc with 
  | VarLoc   v       -> loc
  | ArrayLoc (a,idx) -> ArrayLoc (a, Formula.stripspos idx)
  
let is_auxloc = function
  | VarLoc v         -> Name.is_auxvar v
  | ArrayLoc (a,idx) -> Name.is_auxvar a || NameSet.exists Name.is_auxreg (Formula.frees idx)
  