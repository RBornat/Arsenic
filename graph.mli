type path  = Node.node list
val string_of_path: path -> string

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type opath = Order.order * path * Node.NodeSet.t
val string_of_opath: opath->string
val completepath_of_opath: Node.node -> Node.node -> opath -> path

val is_so_opath          : opath -> bool
val is_constraint_opath  : opath -> bool
val is_lo_opath          : opath -> bool
val is_bo_opath          : opath -> bool
val is_uo_opath          : opath -> bool

module OPSet: MySet.S with type elt=opath
type opset = OPSet.t


module type OPGraphsig = sig
  type opgraph
  val empty      : opgraph
  val is_empty   : opgraph -> bool
  
  val to_assoc   : opgraph -> ((Node.node * Node.node) * opset) list
  val from_assoc : ((Node.node * Node.node) * opset) list -> opgraph
  
  val to_string  : string -> opgraph -> string
  
  val add_edge   : Order.order -> Node.node -> Node.node -> opgraph -> opgraph
  val add_edges  : Order.order -> Node.node list -> Node.node list -> opgraph -> opgraph
  
  val transitive_closure : opgraph -> opgraph
  val inverse : opgraph -> opgraph

  val paths      : Node.node -> Node.node -> opgraph -> opset 
     (* not synonym for find: returns empty opset rather than raising Not_found *)
  val pathfold   : (Node.node -> Node.node -> opath -> 'a -> 'a) -> opgraph -> 'a -> 'a
  val pathfilter : (Node.node -> Node.node -> opath -> bool) -> opgraph -> opgraph
  
  val union : opgraph -> opgraph -> opgraph
end
module OPGraph: OPGraphsig
