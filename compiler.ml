open Program

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

let tranfile filename = 
  print_newline (print_string ("\nprocessing " ^ filename));
  let tidyup s = 
    print_string s;
    flush stdout;
    flush stderr
  in
  try let prog = parse filename in
      Printf.printf "\n\n%s\n" (string_of_program prog);
      tidyup ""
  with 
  | Sys_error s                         -> tidyup ("\n\n** FATAL Sys_error \""^s^"\"")
  | Error s 
  | Formula.Error s                     -> tidyup ("\n\n" ^ s)
  | exn                                 -> tidyup ("\n\n** Unexpected exception " ^ Printexc.to_string exn)

let progname = "Compile"
let files = ref []
let usage = "Usage: " ^ progname ^ " [options]* filename filename ..."
let opts = Arg.align []
let _ = Arg.parse opts (fun s -> files := s :: !files) usage
let _ = match !files with 
        | [] -> print_string ("\nno file specified") 
        | fs -> List.iter tranfile (List.rev fs)