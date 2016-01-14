open Function
open Tuple
open Listutils
open Settings
open Sourcepos
open Printer
open Name
open Formula
open Program
open Com
open Thread
open Order
open Knot
open Stitch
open Graph
open Node
open Labmap
open Report

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception Crash of string
exception Abandon

let show_result name string_of stuff =
  Printf.printf "\nlace %s =\n%s\n"
                name
                (string_of_assoc string_of_int
                                 string_of 
                                 ": " "\n"
                                 (Listutils.numbered stuff)
                )

(* ********************** build inverted tree of structured commands ************************* *)

(* the thread body gives us a notion of enclosure: a command is inside a nest
   of structured commands. We can invert this tree so that we can go from a command
   to a list of the structured commands it is within. A control expression is both
   within and without its enclosing structured command; for the purposes of proof
   checking at the moment it seems that inside is what we care about.
   
   Locations give us a unique identification of structured commands. So would identity
   of nodes, but I don't want to do that, because identity is hard to debug ...
   
   At the same time as building a map from labels to nodes in the inverted tree, I can 
   check for uniqueness of labels.
 *)

let addnewlabel poslab cid parents (map : labelid LabMap.t) =
  try 
    let oldloc,_,_ = LabelMap.find poslab.lablab map in
    report 
      (Error 
         (poslab.labspos, 
          Printf.sprintf "label %s already defined at %s"
                         (string_of_label poslab.lablab)
                         (string_of_sourcepos oldloc)
         )
      );
    map
  with Not_found -> LabMap.add poslab.lablab (poslab.labspos,cid,parents) map

let pushparent p parents = (List.length parents+1,p)::parents
;;

let rec labmaps_com parents map = function
  | Com       ct -> addnewlabel ct.tripletlab (CidSimplecom ct) parents map
  | Structcom sc ->
      (let add_c c parents = 
         addnewlabel (poslab_of_condition c) (CidControl c) (pushparent ControlPos parents)
       in
       match sc.structcomnode with
       | DoUntil (seq,c) ->
           let parents = pushparent (DoUntilPos sc.structcompos) parents in
           let map = labmaps_seq parents map seq in
           add_c c parents map
       | While (c,seq) -> 
           let parents = pushparent (WhilePos sc.structcompos) parents in
           let map = add_c c parents map in
           labmaps_seq parents map seq
       | If (c,sthen,selse) ->
           let parents = pushparent (IfPos sc.structcompos) parents in
           let map = add_c c parents map in
           let map = labmaps_seq (pushparent (IfArmPos true) parents) map sthen in
           labmaps_seq (pushparent (IfArmPos false) parents) map selse
      )

and labmaps_seq parents map =
  List.fold_left (labmaps_com parents) map
  
let labmaps_thread preopt postopt t = 
  let map = LabMap.empty in
  let map = match preopt with 
            | Some (poslab, f) -> addnewlabel poslab (CidInit (poslab.lablab,f)) [] map
            | None             -> map
  in
  let map = match postopt with 
            | Some (poslab, f) -> addnewlabel poslab (CidFinal (poslab.lablab,f)) [] map
            | None             -> map
  in
  match t.t_body with
  | Threadfinal _ -> map
  | Threadseq seq -> 
      let map = labmaps_seq [] map seq in
      match t.t_postopt with
      | None      -> map
      | Some knot -> addnewlabel {labspos=knot.knotloc; lablab=""}
                                 (CidThreadPost knot)
                                 []
                                 map

let labmaps_prog {p_preopt=preopt; p_givopt=givopt; p_ts=threads; p_postopt=postopt} =
  List.map (labmaps_thread preopt postopt) threads
  
(* ********************** check knot labels for definedness ************************* *)

(* we use a map from labels to locations * scloc enclosures *)
let check_labels_thread labmap thread = 
  let check_stitch tparents stitch =
    (* here's where we check the C/CE stuff *)
    let source = source_of_stitch stitch in
    let slab = label_of_node source in
    try 
      let sparents = get_parents slab labmap in 
      match sparents with
      | (_,ControlPos)::_ ->
          (* the appropriate use of the source depends on the parentage of the triplet *)
          let gooduses, badcall = 
            match List.hd (List.tl sparents) with
            | _, IfPos _ -> 
                (match pidopt (enclosing_if tparents) with
                 | Some (_, IfArmPos b) -> 
                     [CEnode (slab,b)], ("in " ^ (if b then "then" else "else") ^ " arm of conditional")
                 | _                    -> 
                     [CEnode (slab,true); CEnode(slab,false)], ""
                )
            | _, looploc ->
                let inner, outer = 
                  match looploc with
                  | WhilePos _         -> CEnode (slab,true) , CEnode(slab,false)
                  | _ (* DoUntilPos *) -> CEnode (slab,false), CEnode(slab,true)
                in
                let encloop = pidopt (common_ancestors sparents tparents) in
                match encloop with 
                | None           -> [outer], "outside its loop"
                | Some (lparent) -> if lparent = List.hd (List.tl sparents) then 
                                      [inner], "inside its loop" 
                                    else 
                                      [outer], "outside its loop"
          in
          (match source with
           | Cnode  _ ->
               report (Error (pos_of_stitch stitch,
                              Printf.sprintf "constraint source %s is a control expression; \
                                              constraint should use %s"
                                (string_of_node source)
                                (Listutils.string_of_list string_of_node " or " gooduses)
                             )
                      )
           | CEnode _ -> 
               if List.mem source gooduses then () else
                 report (Error (pos_of_stitch stitch,
                                Printf.sprintf "constraint source %s %s; \
                                                constraint should use %s"
                                  (string_of_node source)
                                  badcall
                                  (Listutils.string_of_list string_of_node " or " gooduses)
                               )
                        )
          )
      | _ (* not ControlPos *) ->
          (match source with
           | CEnode _ ->
               report (Error (pos_of_stitch stitch,
                              Printf.sprintf "constraint source %s is not a control expression; \
                                              constraint should use %s"
                                (string_of_node source)
                                (string_of_node (Cnode slab))
                             )
                      )
           | Cnode  _ -> ()
          )
    with
    | Invalid_argument s as exn -> 
        if Stringutils.starts_with s "Not_found LabMap.get_parents" then
          report (Error ((pos_of_stitch stitch), Printf.sprintf "label %s undefined" slab))
        else raise exn
    | exn                       -> raise exn
  in
  let rec check_knot tparents knot =
    match knot.knotnode with
    | SimpleKnot stitches -> List.iter (check_stitch tparents) stitches
    | KnotOr    (pc1,pc2) 
    | KnotAnd   (pc1,pc2) 
    | KnotAlt   (pc1,pc2) -> check_knot tparents pc1; 
                             check_knot tparents pc2
  in
  let check_triplet () triplet =
    check_knot (get_parents (lab_of_triplet triplet) labmap) (knot_of_triplet triplet)
  in
  (* body of checklabels_thread *)
  match thread with
  | {t_body=Threadfinal _}                 -> ()
  | {t_body=Threadseq seq; t_postopt=postopt} -> 
      List.fold_left (Com.tripletfold check_triplet check_triplet) () seq;
      match postopt with
      | Some post -> check_knot [] post
      | _         -> ()
  
let check_labels_prog labmaps {p_preopt=preopt; p_givopt=givopt; p_ts=threads; p_postopt=postopt} =
  List.iter (uncurry2 check_labels_thread) (List.combine labmaps threads)
  
(* *********************** find po, lo, bo, uo orders **************************** *)

let add_so_edges so prevnodes nexts = OPGraph.add_edges so prevnodes nexts

let add_acso lab (prevnodes, opgraph) =
  [Cnode lab], add_so_edges So prevnodes [Cnode lab] opgraph

let add_cyso lab (prevnodes, opgraph) =
  add_so_edges So prevnodes [Cnode lab] opgraph

let graph_stitch destlab opgraph stitch =
  OPGraph.add_edge (order_of_stitch stitch) (source_of_stitch stitch) (Cnode destlab) opgraph
  
let rec graph_knot destlab opgraph knot =
  match knot.knotnode with
  | SimpleKnot stitches -> List.fold_left (graph_stitch destlab) opgraph stitches
  | KnotOr      (k1,k2) 
  | KnotAnd     (k1,k2) 
  | KnotAlt     (k1,k2) -> graph_knot destlab (graph_knot destlab opgraph k1) k2

let graph_triplet (prevnodes,opgraph) {tripletknot=knot; tripletlab={lablab=lab}} =   
  let opgraph = graph_knot lab opgraph knot in
  add_acso lab (prevnodes,opgraph) 

let rec graph_seqel prgr com =
  match com with
  | Com  triplet -> graph_triplet prgr triplet
  | Structcom sc -> graph_structcom prgr sc

and graph_seq prgr = List.fold_left graph_seqel prgr

and graph_structcom (prevnodes, opgraph) sc = 
  let graph_c pair c =
    match c with
    | CExpr   ft -> graph_triplet pair ft
    | CAssign ct -> graph_triplet pair ct
  in
  match sc.structcomnode with
  | If (c, s1, s2) -> 
      let _, opgraph = graph_c (prevnodes,opgraph) c in
      let clab = lab_of_condition c in
      let s1prevs, opgraph = graph_seq ([CEnode (clab,true)],opgraph) s1 in
      let s2prevs, opgraph = graph_seq ([CEnode (clab,false)],opgraph) s2 in
      s1prevs@s2prevs, opgraph
  | While (c, s) ->
      let _, opgraph = graph_c (prevnodes,opgraph) c in
      let clab = lab_of_condition c in
      let s_prevs, opgraph = graph_seq ([CEnode (clab,true)],opgraph) s in
      [CEnode (clab,false)], add_cyso clab (s_prevs,opgraph) (* loopback *)
  | DoUntil (s, c) ->
      let s_prevs, opgraph = graph_seq (prevnodes,opgraph) s in
      let clab = lab_of_condition c in
      let _, opgraph = graph_c (s_prevs,opgraph) c in
      [CEnode (clab,true)], add_cyso (fstlab_structcom sc) ([CEnode (clab,false)],opgraph) (* loopback *)

let graph_thread preopt postopt thread =
  let opgraph = OPGraph.empty in
  match thread.t_body with
  | Threadfinal _ ->  opgraph (* nothing interesting at all *)
  | Threadseq seq -> 
      let prevnodes = 
        match get_outerassert_lab preopt with 
        | Some pre -> [Cnode pre]
        | None     -> []
      in
      let prevnodes, opgraph = graph_seq (prevnodes, opgraph) seq in
      let prevnodes, opgraph =
        match thread.t_postopt with
        | None   -> prevnodes,opgraph
        | Some _ -> add_acso "" (prevnodes,opgraph)
      in
      let lasts, opgraph =
        match get_outerassert_lab postopt with
        | Some post -> add_acso post (prevnodes,opgraph)
        | None      -> prevnodes, opgraph
      in
      opgraph

module PassedSet = LabelSet
module PassedMap = Map.Make (struct type t = Name.label*Name.label let compare = Pervasives.compare end)
   
let graph_prog {p_preopt=preopt; p_givopt=givopt; p_ts=threads; p_postopt=postopt} =
  let opgraphs = List.map (graph_thread preopt postopt) threads in
  if !verbose then
    show_result "opgraphs" (OPGraph.to_string "\n   ") opgraphs;
  let closures = 
    List.map OPGraph.transitive_closure opgraphs
  in
  if !verbose then
    show_result "closures" (fun c -> "\n   " ^ OPGraph.to_string "\n   " c) closures;

(*  (* now make all lo/bo/uo paths properly acyclic *)

    (* first a map from constraints to passed set. *)

    let findpassings source target opset passedmap =
      let constraints = 
        OPSet.filter (function | ((Lo|Bo|Uo), [], _) -> true
                              | _                   -> false
                     )
                     opset
      in
      if OPSet.is_empty constraints then passedmap 
      else
        (let passed = OPSet.filter is_so_opath opset in
         let passed = List.concat (List.map sndof2 passed) in
         PassedMap.add (source,target) (LabelSet.of_list passed) passedmap
        )
    in  
    let cpassedmaps = 
      List.map (fun closure -> OPGraph.pathfold findpassings PassedMap.empty closure) 
               closures
    in
    if !verbose then 
      show_result "passedmap"
                  (fun map ->
                     string_of_assoc
                       (bracketed_string_of_pair string_of_label string_of_label)
                       LabelSet.to_string
                       "->" "\n  "
                       (PassedMap.bindings map)
                  )
                  cpassedmaps;
  
    (* now filter the over-cyclic paths *)
  
    let approve passedmap source target = function
      | So , _    -> true
      | _  , []   -> true
      | oo , mids -> 
        (let path = source::mids@[target] in
         let rec pairs = function
           | a::b::xs -> (a,b)::pairs (b::xs)
           | _        -> []
         in
         if !verbose then
           Printf.printf "\nseen opath %s %s, pairs [%s]"
                         (string_of_order oo)
                         (string_of_list string_of_label "->" path)
                         (string_of_list (bracketed_string_of_pair string_of_label string_of_label) ";" (pairs path));
         let passedset = 
           List.fold_left PassedSet.union PassedSet.empty 
                          (List.map (fun (a,b) -> PassedMap.find (a,b) passedmap) (pairs path)) 
         in
         let r = not (PassedSet.mem source passedset || PassedSet.mem target passedset) in
         if !verbose then
           Printf.printf "\n%s %s %sapproved: passed set is {%s}"
                         (string_of_order oo)
                         (string_of_list string_of_label "->" path)
                         (if r then "" else "dis")
                         (LabelSet.to_string passedset);
         r
        )
    in
    let closures = 
      List.map (fun (passedmap, closure) -> OPGraph.pathfilter (approve passedmap) closure) 
               (List.combine cpassedmaps closures)
    in
    if !verbose then
      show_result "filtered closures" ((OPGraph.to_string "\n   ") closures;
 *)
  closures
  
(* ***************************** check constraints ********************************** *)


   (* 1. Constraints must be within so. 
      
      2. A knot (not in a disjunction) must apply no matter what path is taken to the 
         target. That is, the sources of the constraints must appear on every so path
         from the initial state to the target.
         
      3. If there's a disjunction then paths not covered by one side must be covered
         by the other. ISWIM.
         
      4. Loopback disjunctions are allowed and cut down some internal (lo) interference.
         We partition the disjunction according to the loops it is enclosed in; if the
         disjunction of the 'loopback' constraints, in each case, is sufficient to cover
         the loop then all is well. Hmm.
    *)

let check_constraints_thread preopt postopt labmap opgraph thread =
  let initlab =
    let bad () = 
      report (Error (threadloc thread, "thread needs initial label, \
                                        from an initial assertion or a skip"));
      raise Abandon
    in
    match get_outerassert_lab preopt with
    | Some lab -> lab
    | _        -> 
      match threadseq thread with 
      | com::_ ->
          (match com with 
           | Com ct -> lab_of_triplet ct
           | _      -> bad()
          )
      | _      -> bad()
  in
  let initnode = Cnode initlab in
  let so_opaths = OPSet.filter is_so_opath in
  
  let check_constraints_stitch poslab stitch =
    let source = source_of_stitch stitch in
    let target = Cnode poslab.lablab in
    (* stitches must reinforce so *)
    if OPSet.is_empty (so_opaths (OPGraph.paths source target opgraph)) then
      report 
        (Error 
           ((pos_of_stitch stitch), 
            Printf.sprintf "%s %s->%s; %s->%s is not in so" 
                           (string_of_order (order_of_stitch stitch))
                           (string_of_node source)
                           (string_of_node target)
                           (string_of_node source)
                           (string_of_node target)
           )
        )
    ;
    
    (* ****** target stuff ******* *)

    let target_cid = get_cid poslab.lablab labmap in
    let badtarget skind s =
      report (Error (pos_of_stitch stitch, Printf.sprintf "%s targets %s" skind s))
    in

    (* go stitches must target variable assignment *)
    (match order_of_stitch stitch, target_cid with
     | Go, CidSimplecom ct 
       when Com.is_var_assign ct -> ()
     | Go, _                     -> badtarget (Order.string_of_order Go ^ " constraint")
                                              "component which is not variable assignment"
     | _  -> ()
    );
    (* load_reserved can't have a reservation stitch *)
    (match target_cid, locopt_of_stitch stitch with
     | CidSimplecom ct, Some _ 
         when Com.is_loadreserved ct  ->
           badtarget "reservation stitch" "load_reserved"
     | _                             -> ()
    );
    (* reservation stitch may not target load_reserved or thread post *)
    (match is_reserved_stitch stitch, target_cid with
     | true, CidSimplecom ct 
        when Com.is_loadreserved ct -> badtarget "reservation stitch" "load_reserved"
     | true, CidThreadPost _       -> badtarget "reservation stitch" "thread postcondition"
     | _                           -> ()
    );

    (* ****** source stuff ******* *)
    
    let source_cid = get_cid (label_of_node source) labmap in
    let badsource kind s = 
      report (Error (pos_of_stitch stitch, Printf.sprintf "%s sources %s" kind s))
    in

    (* source may not be final state or thread postcondition *)
    (match source_cid with
     | CidFinal      _ -> badsource "stitch" "final state"
     | CidThreadPost _ -> badsource "stitch" "thread postcondition"
     | _               -> ()
    );
    (* reservation stitches may not source a store-conditional or initial state. *)
    (match is_reserved_stitch stitch, source_cid with
     | true, CidControl c -> (match c with
                              | CExpr   ft -> ()
                              | CAssign _  -> badsource "reservation stitch" "store-conditional"
                             )
     | true, CidInit _    -> badsource "reservation stitch" "initial state"
     | _                  -> () 
    )
  in
  let check_constraints_knot poslab knot =
    (* check the stitches *)
    Knot.iter (check_constraints_stitch poslab) knot;
    (* check reservations *)
    let ress = Knot.reservations knot in
    let resn = List.length ress in
    if resn>1 then
      report (Error (knot.knotloc,
                     Printf.sprintf "knot appeals to reservations for %s locations -- %s"
                                    (if resn=2 then "two" else "several")
                                    (Listutils.standard_phrase_of_list Location.string_of_location (List.rev ress))
                    )
             )
  in
  let knot_coverage origin all_paths_to knot =
    let rec fka knot =
      match knot.knotnode with
      | SimpleKnot []       -> OPSet.empty (* we covered nothing *)
      | SimpleKnot stitches -> 
          let stitch_covers stitch =
            let source = source_of_stitch stitch in
            OPSet.filter (fun (_,_,through) -> source=origin || NodeSet.mem source through) all_paths_to 
          in
          List.fold_left OPSet.inter all_paths_to (List.map stitch_covers stitches)
      | KnotOr    (pc1,pc2) -> OPSet.union (fka pc1) (fka pc2)
      | KnotAnd   (pc1,pc2) -> OPSet.inter (fka pc1) (fka pc2)
      | KnotAlt   (pc1,pc2) -> raise (Invalid_argument "Lace.knot_coverage sees KnotAlt")
    in
    fka knot
  in
  let check_constraints_triplet knotmap {tripletknot=knot; tripletlab=poslab} =
    check_constraints_knot poslab knot;
    let source = initnode in
    let target = Cnode poslab.lablab in
    let all_paths_to = so_opaths (OPGraph.paths source target opgraph) in
    (* usually, a knot must cover all paths to the target *)
    let check_full_coverage knot =
      let coverage = knot_coverage source all_paths_to knot in
      if OPSet.equal all_paths_to coverage then ()
      else 
        report (Error (knot.knotloc, Printf.sprintf "knot %s doesn't work in all possible executions. \
                                            These paths to %s don't contain all the constraint sources: %s"
                                            (string_of_knot knot)
                                            (string_of_label poslab.lablab)
                                            (Listutils.string_of_list (string_of_path <.> completepath_of_opath source target) "; " 
                                               (OPSet.elements (OPSet.diff all_paths_to coverage))
                                            )
                      )
               )
    in
    (* but the 'loopback' half of a directed disjunction plays by slightly different rules *)
    let check_loop_coverage outerps knot =
      let enclosed outerps node = encloses outerps (get_parents (label_of_node node) labmap) in
      let all_loop_paths = 
        OPSet.filter (fun (_,_,nset) -> NodeSet.for_all (enclosed outerps) nset)
                     (so_opaths (OPGraph.paths target target opgraph))
      in
      (* coverage is all the paths in all_loop_paths that are covered by the disjunct *)
      let coverage = knot_coverage target all_loop_paths knot in
      (* find the paths that are entirely within a loop pierced by source->target --
         they will be internally parallel
       *)
      let targetps = get_parents (label_of_node target) labmap in
      let inner_paths = 
        match weakest_inner_loop (common_ancestors outerps targetps) targetps with
        | None             -> OPSet.empty
        | Some innerloopps -> 
              OPSet.filter (fun (_,_,nset) -> NodeSet.for_all (enclosed innerloopps) nset)
                           all_loop_paths
      in
      let discrepancy = 
        OPSet.diff (OPSet.diff all_loop_paths inner_paths) coverage
      in
      if !verbose || !Settings.verbose_knots then
        Printf.printf "\ntarget %s\nall_loop_paths %s\nouterps %s\ncoverage %s\ninner_paths%s"
                        (string_of_node target)
                        (OPSet.to_string all_loop_paths)
                        (string_of_parentids outerps)
                        (OPSet.to_string coverage)
                        (OPSet.to_string inner_paths);
      if OPSet.is_empty discrepancy then ()
      else 
        report (Error (knot.knotloc, Printf.sprintf "knot %s doesn't work in all possible executions of its loop. \
                                            These loop paths %s->%s don't contain all the constraint sources: %s"
                                            (string_of_knot knot)
                                            (string_of_label poslab.lablab)
                                            (string_of_label poslab.lablab)
                                            (Listutils.string_of_list (string_of_path <.> completepath_of_opath target target) "; " 
                                               (OPSet.elements discrepancy)
                                            )
                      )
               );
      inner_paths
    in
    match knot.knotnode with
    | SimpleKnot []   -> knotmap (* no knot is ok *)
    | KnotAlt (k1,k2) -> 
        (let cas_stitch stitch = (* common ancestors of a stitch *)
           let source = source_of_stitch stitch in
           let slab = label_of_node source in
           common_ancestors (get_parents slab labmap) (get_parents poslab.lablab labmap)
         in
         let rec cas_knot knot = (* common ancestors of a knot *)
           match knot.knotnode with 
           | SimpleKnot []       -> [] (* meaning the top level of the program *)
           | SimpleKnot stitches ->
               let ps = List.map cas_stitch stitches in
               List.fold_left common_ancestors (List.hd ps) (List.tl ps)
           | KnotOr  (k1,k2)
           | KnotAnd (k1,k2) -> common_ancestors (cas_knot k1) (cas_knot k2)
           | KnotAlt (k1,k2) -> raise (Invalid_argument "Lace.cas_knot sees KnotAlt")
         in
         let k1ps = cas_knot k1 in
         let k2ps = cas_knot k2 in
         if Listutils.null k2ps then
           (report (Error (k2.knotloc, Printf.sprintf "knot after %s should be confined to a loop"
                                                      alt_token
                          )
                   );
            knotmap
           )
         else
         if not (strictly_encloses k1ps k2ps) then
           (report (Error (k1.knotloc,  Printf.sprintf "knot before %s should start outside the loop \
                                                        that encloses knot after %s"
                                                       alt_token alt_token
                          )
                   );
            knotmap
           )
         else
         if common_ancestors k1ps (List.tl k2ps) <> k1ps then
           (report (Error (knot.knotloc, Printf.sprintf "there is more than one loop pierced by the knot \
                                                         before %s"
                                                        alt_token
                          )
                   );
            knotmap
           )
         else
           (check_full_coverage k1;
            let inner_paths = check_loop_coverage k2ps k2 in
            KnotMap.add knot inner_paths knotmap
           )
        )
    | _               -> check_full_coverage knot;
                         knotmap
  in
  let check_constraints_simplecomtriplet knotmap ct =
    (* check the arity of the ipre option *)
    (match ct.tripletof.sc_ipreopt, precondition_of_knot (fun _ _ -> true) Interference ct.tripletknot with
     | Some (IpreDouble _), PreSingle _ 
     | Some (IpreRes    _), PreSingle _ -> 
         report (Error (ct.tripletpos, "knot and command cannot generate reservation-interference precondition"))
     | _                                -> ()
    );
    check_constraints_triplet knotmap ct
  in
  Thread.tripletfold check_constraints_simplecomtriplet check_constraints_triplet KnotMap.empty thread
  
(* because of the peculiarities of KnotAlt, delivers a KnotMap *)
let check_constraints_prog {p_preopt=preopt; p_givopt=givopt; p_ts=threads; p_postopt=postopt} labmaps opgraphs =
  List.map (uncurry2 (uncurry2 (check_constraints_thread preopt postopt)))
            (List.combine (List.combine labmaps opgraphs) threads)

(* *********************** no universalised temporal coincidences **************************** *)

let check_coincidence_formula binders =
  let rec ccf_opt binders ubfopt () f =
    let reportit () =
      match ubfopt with
      | None     -> ()
      | Some ubf -> 
          report 
            (Error 
               (f.fpos,
                Printf.sprintf "formula %s contains temporal coincidence %s"
                               (string_of_formula ubf)
                               (string_of_formula f)
               )
          )
    in
    let do_sofar sf =
      let sf_frees = Formula.frees sf in
      if NameSet.cardinal (NameSet.diff sf_frees binders) > 1 then
        reportit ();
      ccf binders ubfopt sf;
      Some ()
    in
    match f.fnode with
    | Univ (_,uf)       -> Some (ccf binders (Some f) uf)
    | Bfr (_,_,bf)      -> Some (ccf binders (Some f) bf)
    | Binder (bk,n,bf)  -> Some (ccf (NameSet.add n binders) ubfopt bf)
    | Since (_,_,f1,f2) -> reportit ();
                           ccf binders ubfopt f1;
                           ccf binders ubfopt f2;
                           Some ()
    | Sofar (_,_,sf)    -> do_sofar sf
    | f                 -> 
        (match extract_ouat f with
         | Some (_,_,sf) -> do_sofar sf
         | None          -> None
        )
  and ccf binders ubfopt = Formula.fold (ccf_opt binders ubfopt) () in
  ccf binders None

let check_coincidence_thread thread =
  Thread.assertionfold (fun binders () -> check_coincidence_formula binders)
                        ()
                        thread
                        
let check_coincidence_prog {p_preopt=preopt; p_givopt=givopt; p_ts=threads; p_postopt=postopt} =
  let cca fopt = 
    match fopt with 
    | Some f -> check_coincidence_formula NameSet.empty f;
    | _      -> ()
  in
  let ccoa oaopt =
    match oaopt with
    | Some (poslab,f) -> cca (Some f)
    | _               -> ()
  in
  ccoa preopt;
  cca givopt;
  ccoa postopt;
  List.iter check_coincidence_thread threads

(* *********************** interface with arsenic.ml **************************** *)

let lace_of_prog prog =
  push_verbose !verbose_lace (fun () -> 
    (* construct structured command map, check for multi-defined labels *)
    let labmaps = labmaps_prog prog in
    if !verbose then 
      show_result "lace labmaps" string_of_labmap labmaps ;
    (* check all labels are defined *)
    check_labels_prog labmaps prog;
    if !errorcount<>0 then raise Abandon;
    (* compute so and check that constraints are within it *)
    let opgraphs = graph_prog prog in
    (* check all the knots of all the triplets *)
    let knotmaps = check_constraints_prog prog labmaps opgraphs in
    if !verbose then 
      show_result "lace knotmaps" (KnotMap.to_string OPSet.to_string) knotmaps ;
    if !errorcount<>0 then raise Abandon;
    (* check for universalised temporal coincidences *)
    check_coincidence_prog prog;
    (* and we don't abandon after that -- perhaps it should be done in checkproof ... *)
    labmaps, opgraphs, knotmaps
  )
