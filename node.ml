(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type node =
  | Cnode  of Name.label
  | CEnode of Name.label * bool
  
let string_of_node = function 
  | Cnode  lab      -> 
      (match lab with
       | "" -> "thread postcondition"
       | _  -> Name.string_of_label lab

      )
  | CEnode (lab, b) -> Printf.sprintf "%s(%s)"
                                      (Name.string_of_label lab)
                                      (if b then "t" else "f")

let label_of_node = function
  | Cnode  lab     -> lab
  | CEnode (lab,_) -> lab
  
let is_Cnode = function
  | Cnode  _ -> true
  | CEnode _ -> false

let is_CEnode = function
  | Cnode  _ -> false
  | CEnode _ -> true
  
module NodeSet = MySet.Make (struct type t=node 
                                    let compare = Pervasives.compare
                                    let to_string = string_of_node
                             end 
                            )

module NodeMap = MyMap.Make (struct type t=node
                                    let compare=Pervasives.compare
                                    let to_string = string_of_node
                             end
                            )
