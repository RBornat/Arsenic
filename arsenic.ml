open Tuple
open Program
open Printer
open Settings
open Sourcepos
open Report
open Z3
open Rely

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception Error of string

let parse opts usage filename =
  let ch = open_in filename in
     (try 
       let line = input_line ch in
       if String.sub line 0 2 = "##" then
         (let args = Str.split (Str.regexp "[ \t]+") line in
          Arg.current := 0;
          Arg.parse_argv (Array.of_list (Usage.progname::(List.tl args)))
                         opts 
                         (fun s -> raise (Arg.Bad ("unrecognised in-file argument " ^s)))
                         usage
         )
       with 
       | Invalid_argument _     -> ()
       | Arg.Bad s | Arg.Help s -> (close_in ch; raise (Error s))
       | exn                    -> raise exn
     );
  close_in ch;
  let in_channel = open_in filename in
  let lexbuf = Lexing.from_channel in_channel in
  try
    let result = Parser.program Lexer.make_token lexbuf in
    close_in in_channel; 
    result
  with
  | Parsing.Parse_error ->
      (close_in in_channel;
       let curr = lexbuf.Lexing.lex_curr_p in
       raise (Error ("**Parse error at line "^string_of_int (curr.Lexing.pos_lnum)^ 
                     " character "^string_of_int (curr.Lexing.pos_cnum-curr.Lexing.pos_bol)^
                     " (just before \""^Lexing.lexeme lexbuf^"\")"))
                    )
  | Program.ParseError(loc,s) ->
        (close_in in_channel;
         raise (Error ("\n**SYNTAX ERROR at "^string_of_location loc ^ ": " ^ s))
        )
  | Lexer.LexError(loc,s) -> 
        (close_in in_channel;
         raise (Error ("\n**LEXING ERROR at "^string_of_location loc ^ ": " ^ s))
        )
  | exn -> (close_in in_channel; raise exn)

let checkfile opts usage filename = 
  AskZ3.z3_querycount:=0;
  AskZ3.triv_querycount:=0;
  AskZ3.invalid_querycount:=0;
  AskZ3.unsat_querycount:=0;
  AskZ3.undef_querycount:=0;
  errorcount:=0;
  undecidedcount:=0;
  warningcount:=0;
  let basename = Filename.basename filename in
  Settings.fileprefix := (try Filename.chop_extension basename with _ -> basename);
  print_newline (print_string ("\nprocessing " ^ filename));
  let tidyup s = 
  (*if !keep_log then Z3.close_log (); *)
    print_string s;
  (*Printf.printf "\nz3_querycount=%d, triv_querycount=%d, invalidcount=%d, undecidedcount=%d, warningcount=%d\n" 
                       (!AskZ3.z3_querycount) (!AskZ3.triv_querycount) (!invalidcount) (!undecidedcount) (!warningcount); *)
    flush stdout;
    flush stderr
  in
  try let prog = parse opts usage filename in
      if !verbose then 
        print_newline (print_string(string_of_program prog)); 
      if !keep_log then ignore (Z3.open_log (!Settings.fileprefix ^ ".log"));
      let start = Time.start_timer() in
      let labmaps, opgraphs, knotmaps = Lace.lace_of_prog prog in
      Checkproof.checkproof_prog prog labmaps opgraphs knotmaps;
      let result = if !AskZ3.invalid_querycount  <>0 ||
                      !errorcount                <>0 then "Invalid" else
                   if !undecidedcount            <>0 then "Undecided" else
                   if !warningcount              <>0 then "Valid (modulo warnings)" else
                                                          "Valid"
      in
      Printf.printf "\n\n%s" result;
      (* (match !lace_only, lace with
          | false, Some lace -> 
              Proof.proofcheck_lace lace;
              tidyup "";
              print_newline (print_string (if !invalidcount  <>0 then "Invalid" else
                                           if !undecidedcount<>0 then "Undecided" else
                                           if !warningcount<>0 then "Valid (modulo warnings)" else
                                                                    "Valid"
                                          ))
         | true, _ | _, None ->
             tidyup ""
        );
      *)
     let showvar name vref =
       if !vref=0 then ""
       else
         Printf.sprintf "%s %d"
                        name !vref
     in
     Time.show_interval "total time" (Time.interval start (Time.now()));
     let results = [showvar "proof obligations"     Checkproof.proofobs;
                    showvar "Z3 queries"            AskZ3.z3_querycount;
                    showvar "trivial queries"       AskZ3.triv_querycount;
                    showvar "invalid queries"       AskZ3.invalid_querycount;
                    showvar "unsats"                AskZ3.unsat_querycount;
                    showvar "undefs"                AskZ3.undef_querycount;
                    showvar "errors"                errorcount;
                    showvar "undecided"             undecidedcount;
                    showvar "warnings"              warningcount
                   ]
     in
     Printf.printf "\n%s\n" (String.concat ", " (List.filter (fun s -> String.length s <> 0) results))
  with 
(*
  | Dependency.Error s                  -> tidyup ("\n\n** CRASH: " ^ s)
  | Lace.LabUnifyError(sk,ar1,ar2,s)    -> tidyup ("\n\n** CRASH: " ^ s)
  | Proof.ProofCheckCrash s             -> tidyup ("\n\n** CRASH: " ^ s)
 *)
  | Sys_error s                         -> tidyup ("\n\n** FATAL Sys_error \""^s^"\"")
  | AskZ3.Crash s
  | Checkproof.Crash s
  | Lace.Crash s                        -> tidyup ("\n\n** CRASH: " ^ s)
  | Error s 
  | Formula.Error s                     -> tidyup ("\n\n" ^ s)
  | Lace.Abandon                        -> tidyup ("\n\n** Lace errors: checking abandoned")
  | Z3.Error(_,code)                    -> tidyup ("\n\n** Z3 error: " ^ Z3utils.string_of_Z3error_code code)
  | Invalid_argument s                  -> tidyup ("\n\n** Invalid_argument " ^s)
  | Report.Exit                         -> tidyup ("") 
  | exn                                 -> tidyup ("\n\n** Unexpected exception " ^ Printexc.to_string exn)

let _ = match !Usage.files with 
        | [] -> print_string ("\nno file specified") 
        | fs -> List.iter (checkfile Usage.opts Usage.usage) (List.rev fs)
