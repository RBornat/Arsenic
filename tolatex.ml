open Program
open Sourcepos
open Latex
open Arg

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception Error of string

let parse filename =
  (try Parseutils.parse_program filename
   with 
   | Parseutils.Error s -> raise (Error s)
   | exn                -> raise exn
  )

let dot = ref false
let multilace = ref false

let tranfile filename = 
  print_newline (print_string ("\nprocessing " ^ filename));
  let tidyup s = 
    print_string s;
    flush stdout;
    flush stderr
  in
  try let prog = parse filename in
      let show s = Printf.printf "\n\n%s\n" s in
      if !dot then
        show (Dotdiagram.dot_of_program filename prog)
      else
      if !multilace then
        (nolace (); show (latex_of_program filename prog);
         laceonly (); show (latex_of_program filename prog);
         embroider (); show (latex_of_program filename prog)
        )
      else
        show (latex_of_program filename prog);
      tidyup ""
  with 
  | Sys_error s                         -> tidyup ("\n\n** FATAL Sys_error \""^s^"\"")
  | Error s 
  | Formula.Error s                     -> tidyup ("\n\n" ^ s)
  | Latex.Error s                       -> tidyup ("\n\n** ERROR " ^ s)
  | exn                                 -> tidyup ("\n\n** Unexpected exception " ^ Printexc.to_string exn)

let progname = "ToLaTeX"
let files = ref []
let usage = "Usage: " ^ progname ^ " [options]* filename filename ..."
let opts = Arg.align [("-name"     , Tuple [Set_string snamesource; String snametarget],
                                                    " define name equivalence");
                      ("-lab"      , Tuple [Set_string labsource; String labtarget],
                                                     " define label equivalence");
                      ("-thread"   , Tuple [Set_int tnamesource; String tnametarget],
                                                     " define thread names");
                      ("-cols"     , Set twocols   , " threads in columns (happens anyway with laceonly) (default no cols)");
                      ("-dot"      , Set dot       , " dot diagram of constraints");
                      ("-noaux"    , Clear aux     , " don't show auxiliaries in laceonly and no lace");
                      ("-nolace"   , Unit nolace   , " no lacing");
                      ("-lace"     , Unit laceonly , " lace only");
                      ("-embroider", Unit embroider, " embroidered lacing (default)");
                      ("-multilace", Set multilace , " all three kinds of lacing")
                     ]
let _ = Arg.parse opts (fun s -> files := s :: !files) usage
let _ = match !files with 
        | [] -> print_string ("\nno file specified") 
        | fs -> Settings.expand_macros := false; 
                List.iter tranfile (List.rev fs)
