open Latex
open Program
open Thread
open Com
open Stitch
open Sourcepos

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2016 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)

let dot_of_stitch target ss stitch =
  Printf.sprintf "\n\t%s -> %s [label=\"%s\"]"
                 (latex_of_label (Node.string_of_node stitch.stitchsource))
                 (latex_of_label target)
                 (Order.string_of_order stitch.stitchorder)
  :: ss

let dot_of_knot ss knot target =
  Knot.fold (dot_of_stitch target) ss knot

let dot_of_triplet ss t = 
  let lab = t.tripletlab.lablab in
  let knot = t.tripletknot in
  (* this doesn't preserve Or, And or Alt ... *)
  let ss = (Printf.sprintf "%s[label=\"%s\"]"
                           lab
                           (latex_of_label lab)
           )::ss
  in
  dot_of_knot ss knot lab
  
let dot_of_thread tnum t =
  Printf.printf "\nlabmap = %s" (Name.NameMap.to_string (fun s -> s) !Latex.labmap);
  let body = Thread.tripletfold dot_of_triplet dot_of_triplet [] t in
  let all = match t.t_postopt with 
  | Some knot -> dot_of_knot body knot ("post_" ^ string_of_int tnum)
  | None      -> body
  in
  String.concat "\n" (List.rev all)
  
  
  (* 
             let is_final i = i>List.length comlist in
             let show_com (com,suffix) =
               String.escaped (string_of_simplecom com ^ string_of_comsuffix suffix)
             in
             output_string ch (string_of_assoc (fun i -> "\n\tc"^string_of_int i)
                                               (fun csuf -> "[label=\""^show_com csuf^"\"]")
                                               " " ""
                                               comlist
                              );
             output_string ch ("\n");
             let showcolor skopt j i = (* line j to i *)
               match skopt with
               | Some (P _) -> "color=red,labelfontcolor=red" (* P lines always red *)
               | _          -> (match (if is_root j then None else Some (List.assoc j comlist)), 
                                      (if is_final i then None else Some (List.assoc i comlist)) 
                                with 
                                | Some (_,Exec), Some (_,Prop) -> "style=dashed" (* dashed Exec to Prop *)
                                | _            , Some (_,Prop) 
                                | Some (_,Prop), _             -> "color=red,labelfontcolor=red"    (* red other to Prop, Prop to other *)
                                | _                            -> 
                                    (match skopt with 
                                     | None -> "style=dotted" (* for implicit barrier lines *)
                                     | _    -> ""
                                    )
                               )
             in
             let showlabel = function  
               | Some sk -> "taillabel=\"" ^ string_of_strandkind sk ^ "\""
               | None    -> ""
             in
             let dotnode j = if is_root j then "croot" else 
                             if is_final j then "cfinal" else 
                               "c"^string_of_int j 
             in
             let edgeattr sopt j i = 
               match showcolor sopt j i, showlabel sopt with
               | "", "" -> ""
               | s , "" -> "[" ^ s ^ "]"
               | "", s' -> "[" ^ s' ^ "]"
               | s , s' -> "[" ^ s ^ ", " ^ s' ^ "]"
             in
             let show_dep i jsset =
               if not (IntStrandSet.is_empty jsset) then
                 output_string ch (
                   "\n\t" ^
                   string_of_list (fun (j,sopt) -> dotnode j ^ "->" ^ dotnode i ^ edgeattr sopt j i)
                                  "; "
                                  (IntStrandSet.elements jsset)
                 )
             in
             Array.iteri show_dep (Array.of_list (anclist ancestry));
 
             )
             ;
 *)
 
let dot_of_program filename {p_preopt=preopt; p_ts=ts; p_postopt=postopt} =
  let prenode = match preopt with 
                | Some (poslab, f) ->
                    Printf.sprintf "\n\t{ rank = source; %s[label=\"%s\"]; }"
                                    poslab.lablab
                                    (latex_of_label poslab.lablab)
                | None             -> ""
  
  in
  (* postnode won't work properly without ancestors *)
  let postnode = match postopt with
                 | Some (poslab, f) ->
                     Printf.sprintf "\n\t{ rank = sink; %s[label=\"%s\", fontcolor=mediumpurple1]; }"
                                    poslab.lablab
                                    (latex_of_label poslab.lablab)
                 | None             -> ""
  
  in
  let output = Printf.sprintf "digraph G {\
                               \n\tnode [shape=plaintext];\
                               \n\tedge [arrowsize=0.3,labelfontsize=10,labeldistance=2.0];\
                               \n\
                               %s\
                               %s\
                               %s\n}"
                        prenode
                        (String.concat ";\n" (List.map (Function.uncurry2 dot_of_thread) (Listutils.numbered ts)))
                        postnode
  in
  output


(*     
             output_string ch ("\n\n}\n");
             close_out ch;
             let prefix = Filename.chop_extension name in
             let command = 
               Printf.sprintf "dot -Tpdf %s.dot -o %s.pdf; if [ `uname` == \"Darwin\" ]; then open %s.pdf; else echo thread%d dependencies in %s.pdf; fi" 
                                       prefix     prefix                                         prefix                    tindex           prefix
             in
             ignore (Unix.system command)
            )
 *)