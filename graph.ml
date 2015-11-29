open Function
open Tuple
open Listutils
open Name
open Settings
open Order
open Node

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
type order = Order.order 

(* to deal with orderings, it seems that we must deal with paths. Ho hum. 

   for any node pair a,b we need to know
     -- is there a path of this kind (po, lo, bo, uo)?
     -- what does it pass through (mostly for po, actually).

   also for po we want to know if the path is a loopback. Maybe. But we 
   can do that by having two maps, one without the loopbacks, one with.
   Ho hum.
 *)

type path = node list 
let string_of_path path = "(" ^ string_of_list string_of_node "->" path ^ ")"

(* for transitive closure. Horrid, but I need to use precomputed sets.
   Also useful, in various ways, in checking stability. I think.
 *)

type opath = order * path * NodeSet.t
let string_of_opath (order, path, set) = 
  Printf.sprintf "%s,%s,%s"
    (string_of_order order)
    (string_of_path path)
    (NodeSet.to_string set)

let completepath_of_opath source target (_,path,_) = source::path@[target]

module OPSet = 
  MySet.Make (struct type t = opath
                     let compare (o1,p1,_) (o2,p2,_) = Pervasives.compare (o1,p1) (o2,p2)
                     let to_string opath = "(" ^ string_of_opath opath ^ ")"
              end
             )
type opset = OPSet.t

let is_so_opath = function 
  | So, _, _ -> true 
  | _        -> false

let is_lo_opath = function 
  | Lo, _, _ 
  | Bo, _, _ 
  | Uo, _, _ -> true 
  | _        -> false

let is_bo_opath = function 
  | Bo, _, _ 
  | Uo, _, _ -> true 
  | _        -> false

let is_uo_opath = function 
  | Uo, _, _ -> true 
  | _        -> false

let is_constraint_opath = is_lo_opath

module TMap = NodeMap
type tmap = opset NodeMap.t

module type OPGraphsig = sig
  type opgraph
  val empty    : opgraph
  val is_empty : opgraph -> bool
  val to_assoc   : opgraph -> ((node * node) * opset) list
  val from_assoc : ((node * node) * opset) list -> opgraph
  val to_string  : string -> opgraph -> string
  val add_edge   : order -> node -> node -> opgraph -> opgraph
  val add_edges  : order -> node list -> node list -> opgraph -> opgraph
  val transitive_closure : opgraph -> opgraph

  val paths      : node -> node -> opgraph -> opset 
      (* almost-synonym for find, returns empty opset rather than raising Not_found *)
  val pathfold   : (node -> node -> opath -> 'a -> 'a) -> opgraph -> 'a -> 'a
  val pathfilter : (node -> node -> opath -> bool) -> opgraph -> opgraph
  val union : opgraph -> opgraph -> opgraph
end

module OPGraph = struct
  include NodeMap
  type opgraph = tmap t
  
  let add_opath s d op opgraph =
    let augment tmap =
      let opset =
        try TMap.find d tmap with Not_found -> OPSet.empty
      in
      TMap.add d (OPSet.add op opset) tmap
    in
    let tmap =
      try NodeMap.find s opgraph with Not_found -> TMap.empty
    in
    add s (augment tmap) opgraph
  
  let add_edge o s d = add_opath s d (o,[],NodeSet.empty)
  let add_edges o ss ds opgraph =
    let pairs = ss >< ds in
    List.fold_left (fun g (s,d) -> add_edge o s d g) opgraph pairs 
  
  let to_assoc opgraph = 
    let assoc_tmaps = bindings opgraph in
    let ap (source,tmap) =
      let assoc_opsets = TMap.bindings tmap in
      let sdop (dest,opset) =
        (source,dest),opset
      in 
      List.map sdop assoc_opsets
    in
    List.concat (List.map ap assoc_tmaps)

  let from_assoc assocs =
    List.fold_left 
      (fun opgraph ((s,d),ops) -> 
         let tmap =
           try NodeMap.find s opgraph with Not_found -> TMap.empty
         in
         let opset =
           try TMap.find d tmap with Not_found -> OPSet.empty
         in
         add s (TMap.add d (OPSet.union opset ops) tmap) opgraph
      )
      empty
      assocs

  let to_string sep opgraph =
    let string_of_assoc ((s,d),opset) =
      Printf.sprintf "%s->%s:%s"
        (string_of_node s)
        (string_of_node d)
        (OPSet.to_string opset)
    in
    Listutils.string_of_list string_of_assoc sep (to_assoc opgraph)

  let pathfilter pf opgraph =
    let pfm source tmap opg =
      let pft target opset tm =
        let opset = OPSet.filter (pf source target) opset in
        if OPSet.is_empty opset then tm else
        TMap.add target opset tm
      in
      let tmap = TMap.fold pft tmap TMap.empty in
      if TMap.is_empty tmap then opg else
      add source tmap opg
    in
    NodeMap.fold pfm opgraph empty

  let pathfold ff opgraph =
    let ffm source tmap = 
      let fft target = 
        OPSet.fold (ff source target)
      in
      TMap.fold fft tmap
    in
    fold ffm opgraph

  (* let pathmap ff opgraph =
       let ffm s tmap v =
         let fft t set v =
           TMap.add t (ff set) v
         in
         NodeMap.add s (TMap.fold fft tmap TMap.empty) v
       in
       fold ffm opgraph empty
     *)
    
  let paths source target graph =
    try TMap.find target (find source graph) with Not_found -> OPSet.empty
  
  let concat_opaths source via target opset ((o1,p1,s1),(o2,p2,s2)) =
    if NodeSet.mem source s2 || NodeSet.mem target s1 ||
       not (NodeSet.is_empty (NodeSet.inter s1 s2))
    then 
      (if !verbose_graph then 
         Printf.printf "\nrejecting %s %s {%s} -> %s -> %s %s {%s}"
           (string_of_order o1)
           (string_of_path (source::p1))
           (NodeSet.to_string s1)
           (string_of_node via)
           (string_of_order o2)
           (string_of_path (p2@[target]))
           (NodeSet.to_string s2);
       opset
      )
    else 
      try (let snew = NodeSet.add via (NodeSet.union s1 s2) in
           let r = OPSet.add (Order.combine o1 o2, p1@(via::p2),snew) opset in
           if !verbose_graph then 
             Printf.printf "\naccepting %s %s {%s} -> %s -> %s %s {%s}"
               (string_of_order o1)
               (string_of_path (source::p1))
               (NodeSet.to_string s1)
               (string_of_node via)
               (string_of_order o2)
               (string_of_path (p2@[target]))
               (NodeSet.to_string s2);
           r
          )
      with Invalid_argument "Order.combine" -> opset
  
  let concat_opsets source via target ops1 ops2 =
    let pairs = OPSet.elements ops1 >< OPSet.elements ops2 in
    List.fold_left (concat_opaths source via target) OPSet.empty pairs

  (* see warshall for the via/viatarget distinction *)
  let graph_compose source via viatarget tmapsource tmapvia =
    let tmap_augment_set target opaths tmap =
      let opset =
        try TMap.find target tmap 
        with Not_found -> OPSet.empty
      in
      TMap.add target (OPSet.union opaths opset) tmap
    in
    let source_via_paths = TMap.find viatarget tmapsource in (* bound to be ok: TMap.mem has said so *)
    let folder target via_target_paths tmapsource =
      if source=via || via=target then tmapsource else
        (let new_paths = concat_opsets source via target source_via_paths via_target_paths in
         tmap_augment_set target new_paths tmapsource
        )
    in
    let r = TMap.fold folder tmapvia tmapsource in
    if !verbose_graph then
         Printf.printf "\ngraph_compose %s %s\n  %s\n\n  %s\n=\n  %s"
                       (string_of_node source)
                       (string_of_node via)
                       ((TMap.to_string OPSet.to_string) tmapsource)
                       ((TMap.to_string OPSet.to_string) tmapvia)
                       ((TMap.to_string OPSet.to_string) r);
    r
  
  let warshall bindings =
    let column bindings b =
      (* alpha(_) is a source but never a target. Use alpha as the target *)
      let target =
        match b with
        | CEnode (lab,_) -> Cnode lab
        | _              -> b
      in
      let brange = bindings <@> b in (* we use the updated (folded) one *)
      let row (a,arange as apair) =
        (* here is where the difference hits. We use paths a->alpha as the lhs of the composition,
           paths alpha(_)->.. as the rhs, composition goes via b.
         *)
        if a<>b && TMap.mem target arange then (a, graph_compose a b target arange brange) else apair
      in
      List.map row bindings
    in
    let sources = List.map fstof2 bindings in
    List.fold_left column bindings sources

  let transitive_closure g =
    NodeMap.of_assoc 
      (warshall (NodeMap.bindings g))

  let union og1 og2 =
    mymerge (TMap.mymerge OPSet.union) og1 og2
end
