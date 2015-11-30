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

