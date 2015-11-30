open Function
open Tuple
open Sourcepos
open Listutils
open Program
open Thread
open Com
open Knot
open Stitch
open Name
open Formula
open Graph
open Settings
open Labmap
open Order
open Node
open Report
open AskZ3
open Stability
open Intfdesc
open Location

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception Crash of string
exception ModalQFail (* internal, see below *)

let proofobs = ref 0

let notyet spos s = Printf.printf "\n\n** %s: not yet checking %s" (string_of_sourcepos spos) s

(* a type for reporting lo-parallel interference *)
type loparkind =
  | InsideLo
  | BeforeLo
  | AfterLo

let string_of_loparkind = function
  | InsideLo -> "inside"
  | BeforeLo -> "before"
  | AfterLo  -> "after"

let report_z3result r spos stringfun =
  match r with
  | Valid _        -> ()
  | Invalid _      -> report (Error (spos, ("we do not have " ^ stringfun())))
  | Undecided _    -> report (Undecided (spos, ("Z3 cannot decide " ^ stringfun())))
  | BadQuery (f,s) -> raise (Crash (Printf.sprintf "\n\n** BADQUERY ** %s: %s\n\ngenerates\n\n%s\n\n"
                                                   (string_of_sourcepos spos)
                                                   (string_of_formula f)
                                                   s
                                   )
                            )

let assign_of_triplet ct =
  match ct.tripletof.sc_node with
  | Assign a -> a
  | _        -> 
      raise (Invalid_argument ("Checkproof.assign_of_triplet " ^ string_of_triplet string_of_simplecom ct))

(* intfdescs of each simplecom *)

let string_of_intfmap_key = bracketed_string_of_pair
                                  string_of_ikind
                                  (string_of_triplet string_of_simplecom)

module IntfMap = MyMap.Make (struct type t = ikind * simplecom triplet
                                    let compare = Pervasives.compare
                                    let to_string = string_of_intfmap_key
                             end
                            )


let mkintf ik ct =
  let iopt = ct.tripletof.sc_ipreopt in
  let pre = 
    match iopt with
    | Some f -> f
    | _      -> assertion_of_knot ik ct.tripletknot 
  in
  let assign = assign_of_triplet ct in
  Intfdesc.mk_intfdesc ct.tripletpos pre assign  

(* postconditions of each ctriplet *)
module CPostMap =  MyMap.Make (struct type t = ikind * simplecom triplet
                                      let compare = Pervasives.compare
                                      let to_string = 
                                        bracketed_string_of_pair string_of_ikind
                                                                 (string_of_triplet string_of_simplecom)
                               end
                              )

let cpost ik ct =
  let pre = assertion_of_knot ik ct.tripletknot in
  match ct.tripletof.sc_node with
  | Skip     -> pre
  | Assert f -> conjoin [pre; f]
  | Assign a -> Strongestpost.strongest_post true pre a

type z3query = z3question * bool * (unit -> string) * formula * formula list
type z3key = z3question * formula * formula list

let z3key_of_z3query (q,_,_,a,gs) = q, Formula.striploc a, List.map Formula.striploc gs

let string_of_z3key (q,a,gs) =
  Printf.sprintf "%s %s %s"
      (string_of_z3question q)
      (string_of_formula a)
      (bracketed_string_of_list string_of_formula gs)

(* to use this map, apply z3key_of_z3query to a z3query *)  
module Z3Map = MyMap.Make (struct type t        = z3key
                                  let compare   = Pervasives.compare
                                  let to_string = string_of_z3key
                           end
                          )

type onode = order * node

let string_of_onode (o,n) = Printf.sprintf "%s %s" (string_of_order o) (string_of_node n)

module ONSet = MySet.Make (struct type t        = onode
                                  let compare   = Pervasives.compare
                                  let to_string = string_of_onode
                           end
                          )

module ONMap = MyMap.Make (struct type t        = onode
                                  let compare   = Pervasives.compare
                                  let to_string = string_of_onode
                           end
                          )

let onset_reorder o onset = 
  ONSet.map (fun (o',n) -> Order.combine o o',n) ONSet.of_list onset
  
let checkproof_thread check_taut ask_taut ask_sat avoided 
                      preopt postopt givopt nintfs 
                      threadnum knotmap labmap opgraph 
                      thread =
  
  Thread.threadnum := threadnum;
  
  if !verbose then 
    Printf.printf "\nstarting thread %d" threadnum;
  let intf_of_triplet = 
    curry2 (IntfMap.vmemofun !verbose "intfdesc" 
                             string_of_intfmap_key
                             string_of_intfdesc 
                             id 
                             (uncurry2 mkintf)
           )
  in
  
  let cpost_of_ct = 
    curry2 
      (CPostMap.vmemofun !verbose "sp"
        (bracketed_string_of_pair string_of_ikind (string_of_triplet string_of_simplecom))
        string_of_formula 
        id 
        (uncurry2 cpost)
      ) 
  in
  
  let sourcepost_of_stitch ik stitch =
    let order = order_of_stitch stitch in
    let source = source_of_stitch stitch in
    let lab = label_of_node source in
    let cid = get_cid lab labmap in
    (match cid with
     | CidSimplecom ct -> cpost_of_ct ik ct
     | CidControl   ft -> 
         let cassert =
           match source with
           | CEnode (_,b) -> Order.quotient order ik
                                 (if b then ft.tripletof else _recNot(ft.tripletof))
           | _            ->
               raise (Crash (Printf.sprintf "Checkproof.sourcepost_of_stitch %s %s %s %s"
                                            (string_of_order order)
                                            (string_of_ikind ik)
                                            (string_of_node source)
                                            (string_of_labelid (LabMap.find lab labmap))
                            )
                     )
         in
         conjoin [assertion_of_knot ik ft.tripletknot; cassert]
     | CidInit (_,f)    -> universal Now (sofar Here Now f)
     | CidThreadPost _  
     | CidFinal      _  -> 
         raise (Crash (Printf.sprintf "%s: stitch %s refers to thread/program postcondition"
                                      (string_of_sourcepos (pos_of_stitch stitch))
                                      (string_of_stitch stitch)
                      )
               )
    ), spopt_of_stitch stitch
  in
  
  let find_actual_ancestors memofun dummy =
    let visited = ref NodeSet.empty in
    let aa (order,node) =
      if NodeSet.mem node !visited then ONSet.empty
      else
        (let lab = label_of_node node in
         let cid = get_cid lab labmap in
         match cid with
         | CidSimplecom ct -> 
             if Com.is_aux_assign ct then
               (visited := NodeSet.add node !visited;
                let fstitch set stitch =
                  ONSet.union set 
                    (onset_reorder order 
                       (memofun dummy (order_of_stitch stitch, source_of_stitch stitch))
                    )
                in
                let r = Knot.fold fstitch ONSet.empty ct.tripletknot in
                visited := NodeSet.remove node !visited;
                r
               )
             else
               ONSet.singleton (order,node)
         | _ -> ONSet.singleton (order,node)
        )
    in
    aa
  in
  
  let rec actual_ancestors dummy = 
    ONMap.vmemofun !verbose "actual_ancestors" string_of_onode ONSet.to_string id 
      (find_actual_ancestors actual_ancestors dummy)
  in
  let actual_ancestors = actual_ancestors ()
  in
  
  let intf_from (i,_) = 
    if i<0 then "rely" else ("thread " ^ string_of_int i)
  in
  
  let check_external_stability spos assertion (_,intfdesc as intf) =
    let stringfun stabkind () = 
      Printf.sprintf "%s of %s against %s (from %s)" 
                     stabkind
                     (string_of_formula assertion) 
                     (string_of_intfdesc intfdesc)
                     (intf_from intf)
    in
    let assigned = Intfdesc.assigned intfdesc in
    let frees = Formula.frees assertion in
    if NameSet.is_empty (NameSet.inter assigned frees) then
      avoided spos "" (stringfun "external stability check")
    else
      (let satq, extq = Stability.ext_stable_queries_intfdesc assertion intfdesc in 
       (* pragmatically, satisfaction involving coherence seems to be difficult for Z3. 
          So we do it the other way round in that case.
        *)
       let ask_uo () =
         if not (Formula.exists is_recU assertion) then
           (avoided spos "Z3 check" (stringfun "UO-EXT stability");
            Valid ([],_recTrue)
           )
         else
           (let _, uoq = Stability.uo_stable_queries_intfdesc assertion intfdesc in
            ask_taut spos (stringfun "UO-EXT stability") uoq;
           )
       in
       let check_uo () =
         let r = ask_uo () in
         report_z3result r spos (stringfun "UO-EXT stability")
       in
       if Formula.exists is_recCohere satq then
         (match ask_taut spos (stringfun "EXT stability") extq with
          | Valid _     -> 
              (match ask_uo () with
               | Valid _   -> ()
               | uo_result ->
                   (match ask_sat spos (stringfun "SCLOC-EXT sat") satq with
                    | Invalid _  -> () (* we didn't need to ask *)
                    | sat_result -> report_z3result sat_result spos (stringfun "SCLOC-EXT sat");
                                    report_z3result uo_result spos (stringfun "UO-EXT stability")
                   )
              )
          | taut_result ->
              (match ask_sat spos (stringfun "SCLOC-EXT sat") satq with
               | Invalid _  -> () (* we didn't need to ask *)
               | Valid _    -> report_z3result taut_result spos (stringfun "EXT stability");
                               check_uo ();
               | sat_result -> report_z3result sat_result spos (stringfun "SCLOC-EXT sat");
                               report_z3result taut_result spos (stringfun "EXT stability");
                               check_uo ()
              )
         )
       else (* the straight way *)
         ((* try not to report undecided satq *)
          match ask_sat spos (stringfun "SCLOC-EXT sat") satq with
          | Invalid _  -> ()
          | sat_result -> 
             let taut_result = ask_taut spos (stringfun "EXT stability") extq in
             match sat_result, taut_result with
             | _      , Valid _   -> 
                 (match ask_uo () with
                  | Valid _   -> ()
                  | uo_result -> report_z3result sat_result spos (stringfun "SCLOC-EXT sat");
                                 report_z3result uo_result spos (stringfun "UO-EXT stability")
                 )
             | Valid _, _         -> report_z3result taut_result spos (stringfun "EXT stability");
                                     check_uo ()
             | _                  -> report_z3result sat_result spos (stringfun "SCLOC-EXT sat");
                                     report_z3result taut_result spos (stringfun "EXT stability");
                                     check_uo ()

         )
      )
  in
  
  (* check inclusion of interference in guarantee, rely *)
  let check_intf_included kindstring intfdesc rgs =
    let allfrees = 
      List.fold_left NameSet.union NameSet.empty (List.map Intfdesc.frees (intfdesc::rgs)) 
    in
    let freevs = NameSet.filter Name.is_anyvar allfrees in
    let newforold v = Name.var_of_string (string_of_var v ^ "&new") in
    let tranloce (loc,e) =
      match loc with
      | VarLoc v         -> _recEqual (_recFname (newforold v)) e
      | ArrayLoc (v,ixf) -> _recEqual (_recFname (newforold v))
                                             (_recArrayStore (_recFname v) ixf e)
    in
    let tranloces = conjoin <.> List.map tranloce in
    let tranextravs = 
      conjoin 
      <.> List.map (fun v -> _recEqual (_recFname (newforold v)) (_recFname v)) 
      <.> NameSet.elements
    in
    let translate intfdesc =
      let pre = Intfdesc.pre intfdesc in
      let loces = Intfdesc.loces intfdesc in
      let locs,_ = List.split loces in
      let extravs = NameSet.diff freevs (NameSet.of_list (List.map Location.locv locs)) in
      conjoin [pre; tranloces loces; tranextravs extravs]
    in
    let tranrg intfdesc =
      let f = translate intfdesc in
      bindExists (Intfdesc.binders intfdesc) f
    in
    let query = _recImplies (translate intfdesc)
                            (disjoin (tranextravs freevs :: List.map tranrg rgs))
    in
    let stringfun () = Printf.sprintf "inclusion of %s in %s"
                                      (string_of_intfdesc intfdesc)
                                      kindstring
                                   (* (Listutils.bracketed_string_of_list string_of_intfdesc rgs) *)
    in
    check_taut intfdesc.ipos stringfun query
  in
  
  (* a constraint b->c is interfered with by an assign a if there is an so-tree path
     containing (instances of) a, b and c which can be reordered so that a comes between
     b and c. In the proof checker this means that either
       1. There is an so path b..c which includes a.
          (In the cause of minimalism, a path which remains within the tightest
           loop that encloses b and c); or
       2. a is not b or c and there is an so path a->b but no lo path which follows
          that so path (i.e. doesn't visit nodes outside it); or
       3. a is not b or c and there is an so path c->a which follows that so path.
   *)
  let get_parents lab = Labmap.get_parents lab labmap in
  (* take an opset; find paths which are so without a corresponding path 
     which satisfies order_filter (checking for lo, bo or uo as appropriate) 
   *)
  let so_butnot_constraint order_filter opset =
    let okpath (_,_,soset as so) (_,_,cset as lo) = 
      let r = NodeSet.is_empty (NodeSet.diff cset soset) in
      if !verbose then
        Printf.printf "\nso=%s; lo=%s; diff=%s"
                      (string_of_opath so) (string_of_opath lo)
                      (NodeSet.to_string (NodeSet.diff cset soset));
      r 
    in 
    OPSet.filter 
      (fun path -> is_so_opath path && 
                   not (OPSet.exists (fun cpath -> order_filter cpath &&
                                                   okpath path cpath
                                     ) 
                                     opset
                       ) 
      )
      opset
  in
  let rec check_knot clab rely assigns inneropt knot = 
    let cnode = Cnode clab in
    if !verbose || !Settings.verbose_knots then 
      Printf.printf "\n%s: checking knot %s inneropt %s"
                (string_of_sourcepos knot.knotloc)
                (string_of_knot knot)
                (Option.string_of_option OPSet.to_string inneropt);
    let cstitch inneropt () stitch =
      if !verbose || !Settings.verbose_knots then
        Printf.printf "\n  -- looking at stitch %s inneropt %s" 
                        (string_of_stitch stitch)
                        (Option.string_of_option OPSet.to_string inneropt);
      let bnode = source_of_stitch stitch in
      let blab = label_of_node bnode in
      let bassert = assertion_of_stitch External stitch in (* seems to be right ... *)
      if !verbose || !Settings.verbose_knots then
        Printf.printf "\nexamining constraint %s->%s" (string_of_node bnode) (string_of_node cnode);
      
      (* inheritance of stitch -- we do External -> External *)
      (* inheritance on bo is tricky: we would like to do _B(sourcepost) => embroidery.
         When sourcepost is subst_clean (no hatted or hooked subformulas), that's ok.
         If embroidery is _B(P), just do sourcepost=>P. If embroidery is a conjunction, 
         do it piecewise. If it's forall x (B(P)), treat as B(forall x P). But otherwise 
         we're riding for a fall.
         
         The same applies, mutatis mutandis, to _U.
         
         If it turns out to be a problem, we could have a syntax to allow the user to
         say what sourcepost should be, check that's implied by the actual sourcepost, 
         and then do _B/_U(sourcepost) => embroidery.
       *)
      let modalq sourcepost is_modal wrap_modal embroidery =
        let rec mq e = 
          match is_modal e with
          | Some prop -> _recImplies sourcepost prop
          | None      ->
              match e.fnode with
              | LogArith(e1, And, e2) -> conjoin [mq e1; mq e2]
              | Binder(Forall,_,_)    -> 
                  let ns, eb = multibind Forall [] e in
                  (match is_modal eb with
                   | Some prop        -> _recImplies sourcepost (bindForall (NameSet.of_list ns) prop)
                   | None             -> raise ModalQFail
                  )
              | _                     -> raise ModalQFail
        in
        try mq embroidery
        with ModalQFail -> 
          if subst_clean sourcepost then 
            _recImplies (wrap_modal sourcepost) embroidery
          else
            (report 
               (Remark (pos_of_stitch stitch, 
                       Printf.sprintf "Arsenic cannot verify inheritance of embroidery \
                                       %s because the strongest-post of the source \
                                       %s contains hatted and/or hooked subformulas. \
                                       Give us a hint: \
                                       what does the strongest-post imply?"
                                      (string_of_formula embroidery)
                                      (string_of_formula sourcepost)
                      )
              );
             _recTrue
            )
      in
      let order = order_of_stitch stitch in
      let sourcepost, spopt = 
        match order with
        | So -> raise (Crash (Printf.sprintf "so in knot %s" (string_of_knot knot)))
        | Lo 
        | Bo -> sourcepost_of_stitch Internal stitch 
        | Go 
        | Uo -> sourcepost_of_stitch External stitch 
      in
      let sourcepost =
        match spopt with
        | None       -> sourcepost
        | Some spost -> 
            let query = _recImplies sourcepost spost in
            let stringfun () = 
              Printf.sprintf "inheritance of explicit postcondition %s from strongest_post %s"
                             (string_of_formula spost)
                             (string_of_formula sourcepost)
            in
            check_taut spost.fpos stringfun query;
            spost
      in
      let query = 
        match order with
        | So -> raise (Crash (Printf.sprintf "so in knot %s" (string_of_knot knot)))
        | Lo 
        | Go -> _recImplies sourcepost bassert
        | Bo -> modalq sourcepost 
                       (fun f -> match f.fnode with Bfr (Here,Now,f) -> Some f | _ -> None)
                       (_recBfr Here Now) 
                       bassert
        | Uo -> modalq sourcepost
                       (fun f -> match f.fnode with Univ (Now,f) -> Some f | _ -> None)
                       (_recUniv Now) 
                       bassert
      in
      let stringfun () =
        Printf.sprintf "inheritance of embroidery %s from source postcondition %s in constraint %s: %s->%s"
                       (string_of_formula bassert)
                       (string_of_formula sourcepost)
                       (string_of_order (order_of_stitch stitch))
                       (string_of_node bnode) 
                       (string_of_node cnode)
      in
      check_taut (pos_of_stitch stitch) stringfun query
      ;
      (* external stability of stitch *)
      List.iter (check_external_stability (pos_of_stitch stitch) bassert) rely;
      
      (* here goes with internal stability *)
      (* we have a constraint b->c. Find relevant so paths *)
      let bcset = OPGraph.paths bnode cnode opgraph in
      (* I _think_ it's right to filter bcset when it goes to a control expression *)
      let bcset =
        if is_control clab labmap then
          let tnode = CEnode (clab,true) in
          let fnode = CEnode (clab,false) in
          let not_through_c (_,_,nodes) = 
            not (NodeSet.mem tnode nodes) && not (NodeSet.mem fnode nodes)
          in
          OPSet.filter not_through_c bcset
        else bcset
      in
      let enclosed_filter outerps =
        (function (So,path,_) -> List.for_all (encloses outerps <.> get_parents <.> label_of_node) path
         |        _           -> false
        )
      in
      (* if a stitch pierces a loop, then the target->target so paths count too, including target ... *)
      let ccset =
        match inneropt with
        | Some inner_paths -> inner_paths
        | None             ->
            (let sourceps = get_parents blab in
             let targetps = get_parents clab in
             match weakest_inner_loop (common_ancestors sourceps targetps) targetps with
             | None         -> OPSet.empty (* can't happen, but never mind *)
             | Some innerps -> 
                 if !verbose || !Settings.verbose_knots then
                   Printf.printf "\n%s: stitch %s pierces loop %s"
                                 (string_of_sourcepos (pos_of_stitch stitch))
                                 (string_of_stitch stitch)
                                 (Option.string_of_option string_of_parentid (pidopt innerps));
                 let extra_paths = OPGraph.paths cnode cnode opgraph in
                 OPSet.filter (enclosed_filter innerps) extra_paths
            )
      in
      if !verbose || !Settings.verbose_knots then
        Printf.printf "\nbcset = %s\nccset = %s" (OPSet.to_string bcset) (OPSet.to_string ccset);
      let bcloopps = common_ancestors (get_parents blab) (get_parents clab) in
      if !verbose || !Settings.verbose_knots then
        Printf.printf "\nbcloop = %s" 
          (Option.string_of_option (bracketed_string_of_pair string_of_int string_of_scloc) (pidopt bcloopps));
      (* we need only consider paths which stay within the loop enclosing b->c *)
      let bcset = OPSet.filter (enclosed_filter bcloopps) bcset in
      if !verbose || !Settings.verbose_knots then
        Printf.printf "\nbcset filtered = %s" (OPSet.to_string bcset);
      (* concatenate bcset and ccset paths *)
      let bccset =
        if OPSet.is_empty bcset then ccset else
        if OPSet.is_empty ccset then bcset else
          (let crossprod = OPSet.elements bcset >< OPSet.elements ccset in
           let combine (_,p1,s1) (_,p2,s2) = So,p1@(cnode::p2),NodeSet.add cnode (NodeSet.union s1 s2) in
           let r = OPSet.union bcset (OPSet.of_list (List.map (uncurry2 combine) crossprod)) in
           if !verbose || !Settings.verbose_knots then
             Printf.printf "\nbccset = %s" (OPSet.to_string r);
           r
          )
      in
      let interferes_before anode =
        if anode=bnode then OPSet.empty else
          (let abset = OPGraph.paths anode bnode opgraph in
           if !verbose || !Settings.verbose_knots then
             Printf.printf "\nabset %s->%s = %s" (string_of_node anode) (string_of_node bnode)
                                                 (OPSet.to_string abset);
           so_butnot_constraint is_lo_opath abset
          )
      in
      let interferes_after anode =
        if cnode=anode then OPSet.empty else 
          (* take notice of the alpha/alpha(t)/alpha(f) stuff *)
          (let caset = 
           if is_control clab labmap then
             let direct b =
                let paths = OPGraph.paths (CEnode (clab,b)) anode opgraph in
                let other = CEnode (clab, not b) in
                OPSet.filter (fun (_,_,nset) -> not (NodeSet.mem other nset)) paths
             in
             OPSet.union (direct true) (direct false)
           else OPGraph.paths cnode anode opgraph 
           in
           if !verbose || !Settings.verbose_knots then 
             Printf.printf "\ncaset %s->%s (%B) = %s" (string_of_node cnode) (string_of_node anode)
                                                      (is_control clab labmap) (OPSet.to_string caset);
           so_butnot_constraint is_lo_opath caset
          )
      in
      let cassign at =
        let alab = at.tripletlab.lablab in
        let anode = Cnode alab in
        if !verbose || !Settings.verbose_knots then
          Printf.printf "\n--checking assign %s" alab;
        let vcheck lpk paths =
          if !verbose || !Settings.verbose_knots && not (OPSet.is_empty paths) then 
            Printf.printf "\n%s %s" 
                          (string_of_loparkind lpk)
                          (OPSet.to_string paths);
          lpk, paths
        in
        let aintf = intf_of_triplet Internal at in
        let screg = !Settings.param_SCreg && Assign.is_reg_assign (Intfdesc.assign aintf) in
        let interferes =
          [vcheck InsideLo (OPSet.filter (fun (_,_,nodeset) -> NodeSet.mem anode nodeset) 
                                            bccset
                              );
           (if screg then 
              InsideLo, OPSet.empty
            else 
              vcheck BeforeLo (interferes_before anode)
           );
           (if screg then
              AfterLo, OPSet.empty
            else
              vcheck AfterLo  (interferes_after anode)
           )
          ]
        in
        (match Option.findfirst (not <.> OPSet.is_empty <.> sndof2) interferes with
         | None                    -> ()
         | Some (direction, opset) ->
             (* we want the internal interference, unweakened for the guarantee *)
             let reportpaths direction opset =
               let singpre =
                 Printf.sprintf "there is %s '%s' path"
                                (match direction with
                                 | InsideLo 
                                 | AfterLo  -> "an"
                                 | BeforeLo -> "a"
                                )
                                (string_of_loparkind direction)
               in
               let plurpre = 
                 Printf.sprintf "there are %s paths" (string_of_loparkind direction) 
               in
               let pathlims =
                 match direction with
                 | InsideLo -> bnode, cnode
                 | BeforeLo -> anode, bnode
                 | AfterLo  -> cnode, anode
               in
               Listutils.prefixed_phrase_of_list 
                 (string_of_path <.> uncurry2 completepath_of_opath pathlims)
                 singpre
                 plurpre
                 (OPSet.elements opset)
             in
             let stringfun () =
               Printf.sprintf "lo-parallel (internal) stability of %s against interference %s of command %s\
                               \n   -- %s"
                              (string_of_formula bassert)
                              (string_of_intfdesc aintf)
                              (string_of_label at.tripletlab.lablab)
                              (reportpaths direction opset)
             in
             if NameSet.is_empty (NameSet.inter (Formula.frees bassert)
                                                (Intfdesc.assigned aintf)
                                 )
             then
               avoided (pos_of_stitch stitch) "Z3 check" stringfun
             else
               (let scq = 
                  Stability.sc_stable_query_intfdesc bassert aintf 
                in
                check_taut (pos_of_stitch stitch) stringfun scq
               )
        )
      in
      List.iter cassign assigns;
        
      (* check constraints from auxiliary assignments *)
      let is_aux_assign_node node =
        match get_cid (label_of_node node) labmap with
        | CidSimplecom ct -> Com.is_aux_assign ct
        | _               -> false
      in
      (match get_cid blab labmap with
       | CidSimplecom ct -> 
           if Com.is_aux_assign ct then
             (let aas = actual_ancestors (order_of_stitch stitch, bnode) in
              if !verbose || !Settings.verbose_knots then 
                Printf.printf "\n actual ancestors %s" (ONSet.to_string aas);
              let check_ancestor (order,node as onode) =
                if !verbose || !Settings.verbose_knots then 
                  Printf.printf "\nchecking actual ancestor %s" (string_of_onode onode);
                let paths = OPGraph.paths node bnode opgraph in
                let order_ok = match order with
                               | Uo -> is_uo_opath
                               | Bo -> is_bo_opath
                               | Lo -> is_lo_opath
                               | _  -> raise (Invalid_argument ("opath_order_ok " ^ string_of_order order))
                in
                let opath_ok (_,_,nodeset as opath) =
                    order_ok opath &&
                    not (NodeSet.exists is_aux_assign_node nodeset) 
                in
                let paths = OPSet.filter opath_ok paths in
                if OPSet.is_empty paths then
                  report (Error ((pos_of_stitch stitch),
                                 Printf.sprintf "stitch %s induces actual ordering %s->%s, and there is no \
                                                 corresponding actual (non-auxiliary) path"
                                                 (string_of_stitch stitch)
                                                 (string_of_onode onode)
                                                 (string_of_node bnode)
                                )
                         )
              in
              List.iter check_ancestor (ONSet.elements aas)
             )
       | _  -> ()
      )

    in
    if !verbose || !Settings.verbose_knots then
      Printf.printf "\n-- looking at knot %s inneropt %s" 
                    (string_of_knot knot)
                    (Option.string_of_option OPSet.to_string inneropt);
    match knot.knotnode with 
    | KnotAlt (k1,k2) -> let inner = KnotMap.find knot knotmap in
                         Knot.fold (cstitch (Some inner)) () k1;
                         check_knot clab rely assigns (Some inner) k2
    | _               -> Knot.fold (cstitch inneropt) () knot
  (* end of check_knot *)
  
  in
  let check_knot_of_triplet rely assigns string_of triplet =
    if !verbose then
      Printf.printf "\nlooking at triplet %s" (string_of_triplet string_of triplet);
    check_knot triplet.tripletlab.lablab rely assigns None (triplet.tripletknot)
  in
  let cbup order_filter constraint_stab constraint_string needed vassigns triplet =
    let check (at,bt) =
      if at=bt then () else
      if !Settings.param_SCloc &&
        (let aves = Assign.loces_of_assign (assign_of_triplet at) in
         let bves = Assign.loces_of_assign (assign_of_triplet bt) in
         match aves, bves with
         | (av,_)::_, (bv,_)::_ -> av=bv
         | _                    -> false
        )
      then ()
      else
        (let alab = at.tripletlab.lablab in
         let blab = bt.tripletlab.lablab in
         let abset = OPGraph.paths (Cnode alab) (Cnode blab) opgraph in
         let opset = so_butnot_constraint order_filter abset in
         if not (OPSet.is_empty opset) then
           let aintf = intf_of_triplet External at in
           let bintf = intf_of_triplet External bt in
           let atassert = assertion_of_knot External at.tripletknot in
           let stringfun () =
             Printf.sprintf "%s-parallel (in-flight) stability of %s against interference %s of command %s\
                             \n   -- there %s"
                            constraint_string
                            (string_of_formula atassert)
                            (string_of_intfdesc bintf)
                            (string_of_label blab)
                            (Listutils.prefixed_phrase_of_list 
                                  (string_of_path <.> 
                                   completepath_of_opath (Cnode alab) (Cnode blab)
                                  )
                                  "is a path"
                                  "are paths"
                                  (OPSet.elements opset)
                            )
           in
           let assigned = Intfdesc.assigned bintf in
           let frees = Formula.frees atassert in
           if not needed || NameSet.is_empty (NameSet.inter assigned frees) then
             avoided at.tripletknot.knotloc "check of" stringfun
           else
             (let boq = constraint_stab aintf.irec bintf.irec in
              check_taut at.tripletknot.knotloc stringfun boq
             )
        )
    in
    if List.mem triplet vassigns then
      List.iter check (List.map (fun vassign -> vassign, triplet) vassigns)
  in
  let check_boparallel = cbup is_bo_opath Stability.bo_stable_query_irecs "bo" in
  let check_uoparallel = cbup is_uo_opath Stability.uo_stable_internal_irecs "uo" in
  
  (* *********************** body of checkproof_thread ***************************** *)
  
  (* filter out our guarantee from the numbered interferences *)
  let extintfs = 
    List.filter (fun (i,_) -> i<>threadnum) nintfs
  in
  let rely = 
    match thread.t_relyopt with
    | None           -> extintfs
    | Some givenrely -> List.map (fun intf -> (-1), intf) givenrely
  in
  match thread.t_body with
  | Threadfinal f ->  
      List.iter (check_external_stability f.fpos f) rely
  | Threadseq []  -> ()
  | Threadseq seq -> 
      (* If we have a given rely, we check it for bo stability. This is somewhat too 
         severe, but never mind: it just introduces incompleteness. Then we make sure that
         the other threads' guarantees are included in the rely.
         
         If we don't have a given rely, we do the cross-product check-bo-stability thing.
       *)
      let cbo ((x, xid as xintf),(y,yid as yintf)) = 
        let stringfun () = 
          Printf.sprintf "inter-thread bo (inflight) stability of %s (from %s) against %s (from %s)" 
                         (string_of_intfdesc xid) (intf_from xintf) 
                         (string_of_intfdesc yid) (intf_from yintf)
        in
        if NameSet.is_empty (NameSet.inter (Intfdesc.assigned yid) 
                                           (Formula.frees xid.irec.i_pre)
                            )
        then
          avoided xid.ipos "Z3 check" stringfun
        else
          (let boq = bo_stable_query_irecs xid.irec yid.irec in
           check_taut xid.ipos stringfun boq
          )
      in
      let pairable (i1,intf1) (i2,intf2) =
        (i1<>i2 || i1<0) &&
        not (!Settings.param_SCloc && actualvar intf1 = actualvar intf2)
      in
      (match thread.t_relyopt with
       | Some givenrely ->
           let icross = List.filter (uncurry2 pairable) (notself_crossprod rely) in
           List.iter cbo icross;
           let cin (_,intf) =
             check_intf_included "given rely" intf givenrely
           in
           List.iter cin extintfs
       | None          ->
           (* check bo-parallelism of extintfs *)
           List.iter cbo (List.filter (uncurry2 pairable) (extintfs >< extintfs))
      );
      
      (* compute assigns, vassigns *)
      let ffassign assigns ct = if is_assign ct then ct::assigns else assigns in
      let assigns = List.fold_left (simplecomfold ffassign) [] seq in
      let vassigns = List.filter is_var_assign assigns in

      (* let's do the work *)
      let check_comtriplet () ct =
        check_knot_of_triplet rely assigns string_of_simplecom ct;
        match ct.tripletof.sc_node with
        | Skip     -> ()
        | Assert f -> 
            let apre = assertion_of_knot External ct.tripletknot in
            let query = _recImplies apre f in
            let stringfun () =
              Printf.sprintf "inheritance of assertion %s \
                              from precondition %s"
                              (string_of_formula f)
                              (string_of_formula apre)
            in
            check_taut ct.tripletpos stringfun query
            
        | Assign a
          when Assign.is_var_assign a ->
            (* uniqueness of write *)
            let loces = Assign.loces_of_assign a in
            (*
               if not !Settings.param_SCloc && List.length loces>1 then
                 report (Error (ct.tripletpos,
                                "simultaneous assignment not allowed with -SCloc false"
                               )
                        );
             *)
            let unique_ve (loc,e) =
              if NameSet.mem (Location.locv loc) !Coherence.coherence_variables then
                (let rhs = 
                   _recSofar Here Now (_recNotEqual (Location._recFloc loc) e) (* fun if it's an array ... *)
                 in
                 let query = _recImplies (assertion_of_knot External ct.tripletknot) rhs in
                 let stringfun () = 
                   Printf.sprintf "uniqueness of write to %s (precondition doesn't imply %s)"
                                  (Location.string_of_loc loc)
                                  (string_of_formula rhs)
                 in
                 check_taut ct.tripletpos stringfun query
                )
              else ()
            in
            List.iter unique_ve loces;
            (* assertion precondition implies interference precondition *)
            (match ct.tripletof.sc_ipreopt with
             | None      -> ()
             | Some ipre ->
                let apre = assertion_of_knot External ct.tripletknot in
                let query = _recImplies apre ipre in
                let stringfun () = 
                  Printf.sprintf "inheritance of interference precondition %s \
                                  from assignment precondition %s" 
                         (string_of_formula ipre)
                         (string_of_formula apre)
                in
                check_taut ct.tripletpos stringfun query
            );
            (* internal bo/uo parallelism *)
            check_boparallel true vassigns ct;
            let cintf = intf_of_triplet Internal ct in
            let cpre = cintf.irec.i_pre in
            let needs_uo = 
              Formula.exists is_recU cpre &&
              not (NameSet.is_empty (NameSet.inter (Intfdesc.assigned cintf) (Formula.frees cpre)))
            in
            check_uoparallel needs_uo vassigns ct;
            (* self-uo stability *)
            let stringfun () = 
              Printf.sprintf "self-uo stability of %s" (Intfdesc.string_of_intfdesc cintf) 
            in
            if not (needs_uo) then
              avoided ct.tripletpos "check of" stringfun
            else
              (let cirec = cintf.irec in
               let query = Stability.uo_stable_internal_irecs cirec cirec in
               check_taut ct.tripletpos stringfun query;
              )
            ;
            (* inclusion in guarantee *)
            check_intf_included "guarantee" (intf_of_triplet External ct) thread.t_guar
      | Assign _ -> ()
    in
    let check_ftriplet () ft =
      check_knot_of_triplet rely assigns string_of_formula ft
    in
    List.iter (Com.tripletfold check_comtriplet check_ftriplet ()) seq;
    match thread.t_postopt with
    | Some knot -> check_knot "" rely assigns None knot
    | None      -> ()
  (* end of checkproof_thread *)
  
let checkproof_prog {p_preopt=preopt; p_givopt=givopt; p_ts=threads; p_postopt=postopt} 
                    labmaps opgraphs knotmaps = 
  push_verbose !verbose_proof (fun () ->
    
    Thread.threadcount := Pervasives.max 2 (List.length threads); 
            (* at least 2, because hatting needs a Here/There distinction *)
    
    proofobs := 0;
    (* extract the guarantees, number them *)
    let guars = List.map (fun t -> t.t_guar) threads in
    let nguars = numbered guars in
    let ngs = List.map (fun (i,gs) -> List.map (fun g -> i,g) gs) nguars in
    let nintfs = List.concat ngs in

    (* extract the coherence variables *)
    let coheres_prepost vset prepostopt =
      match preopt with
      | Some (_,f) -> Modality.get_coherence_vars NameSet.empty vset f
      | _          -> vset
    in
    let vset = NameSet.empty in
    let vset = 
        coheres_prepost (coheres_prepost vset preopt)
                        postopt 
    in
    let vset = 
      match givopt with
      | Some g -> Modality.get_coherence_vars NameSet.empty vset g
      | None   -> vset
    in
    let vset = List.fold_left (Thread.assertion_fold Modality.get_coherence_vars) vset threads in
    Coherence.coherence_variables := vset;
    if not (NameSet.is_empty vset) && not (!Settings.param_SCloc) then
      report (Error (dummy_spos,
                     Printf.sprintf "coherence assertions on %s not allowed with -SCloc false"
                                    (prefixed_phrase_of_list string_of_name
                                                             "variable" "variables"
                                                             (NameSet.elements vset)
                                    )
                    )
             );
    
    (* proof obligation functions *)
    let uncurried_doZ3 (q,v,sfun,a,gs) = AskZ3.doZ3 q v sfun a gs in
    let memo_do_Z3 = Z3Map.memofun z3key_of_z3query uncurried_doZ3 in
    let curried_doZ3 q v sfun a gs = 
      if !Settings.all_valid then Valid(gs,a) else memo_do_Z3 (q,v,sfun,a,gs) 
    in

    let z3q qkind spos stringfun query =
      proofobs := !proofobs+1;
      curried_doZ3 qkind !verbose (fun () -> Printf.sprintf "%s: checking %s"
                                                                 (string_of_sourcepos spos)
                                                                 (stringfun ())
                                  )
                          query (match givopt with None -> [] | Some g -> [g])
    in
  
    let check_taut spos stringfun query = 
     let r = z3q Tautology spos stringfun query in
     report_z3result r spos stringfun
    in
  
    let ask_taut = z3q Tautology in
    
    let ask_sat = z3q Satisfiable in
  
    let avoided spos description stringfun =
      if !verbose || !Settings.z3track<>Settings.Z3trackOff then
        Printf.printf "\n-- %s: avoided %s %s"
                      (string_of_sourcepos spos)
                      description
                      (stringfun ());
      proofobs := !proofobs+1
    in
    
    (* do the threads *)
    List.iter 
      (uncurry2 (* threads *)
        (uncurry2  (* opgraphs *)
          (uncurry2 (* labmaps *)
            (uncurry2 (* numbered knotmaps *)
              (checkproof_thread check_taut ask_taut ask_sat avoided preopt postopt givopt nintfs)))))
      (List.combine 
        (List.combine 
          (List.combine
            (numbered knotmaps)
            labmaps
          )
          opgraphs
        ) 
        threads
      );
    
    (* check inheritance of postcondition *)
    (match postopt with
     | None -> ()
     | Some (poslab,progpost) ->
         (* to avoid cheating, add a pms thread *)
         let pms_tn = !Thread.threadcount in
         Settings.temp_setting Thread.threadcount (!Thread.threadcount+1) (fun () ->
           (* accumulate the postconditions of the threads *)
           let pmsc_process i tpost =
             let number_reg f =
               match f.fnode with
               | Freg r -> Some (rplacFlogc f (pmsc_name i r))
               | _      -> None
             in
             Formula.map number_reg tpost
           in
           let wrap i tpost =
             threaded i (universal Now (pmsc_process i tpost))
           in
           let tpost = function
             | i, {t_body=Threadfinal tpost} -> wrap i tpost
             | i, {t_postopt=Some knot}      -> wrap i (assertion_of_knot External knot)
             | _                             -> _recTrue
           in
           let tposts = conjoin (List.map tpost (numbered threads)) in
           let pms_progpost = threaded pms_tn progpost in
           let query = _recImplies tposts pms_progpost in
           let stringfun () =
             Printf.sprintf "inheritance of program postcondition %s from threads' postcondition %s"
                            (string_of_formula progpost)
                            (string_of_formula tposts)
           in
           Settings.temp_setting AskZ3.in_pms true (fun () -> check_taut progpost.fpos stringfun query)
         )
    )
  )