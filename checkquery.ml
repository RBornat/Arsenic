open Tuple
open Query
open Printer
open Settings
open Sourcepos
open Report
open Name
open Formula
open Intfdesc
open Stability
open AskZ3
open Z3

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception Error of string

let parse_queries_from_channel in_channel =
  let lexbuf = Lexing.from_channel in_channel in
  try
    let result = temp_setting Settings.allow_tcep true (fun () -> Parser.queries Lexer.make_token lexbuf) in
    result
  with
  | Parsing.Parse_error ->
      (let curr = lexbuf.Lexing.lex_curr_p in
       raise (Error ("**Parse error at line "^string_of_int (curr.Lexing.pos_lnum)^ 
                          " character "^string_of_int (curr.Lexing.pos_cnum-curr.Lexing.pos_bol)^
                          " (just before \""^Lexing.lexeme lexbuf^"\")")))
  | Program.ParseError(spos,s) ->
        raise (Error ("\n**SYNTAX ERROR at "^string_of_sourcepos spos ^ " " ^ s))
  | Lexer.LexError(spos,s) -> 
        raise (Error ("\n**LEXING ERROR at "^string_of_sourcepos spos ^ ": " ^ s))
  
let parse_queries_from_file filename =
  let in_channel = open_in filename in
  try
    let result = parse_queries_from_channel in_channel in
    close_in in_channel;
    result
  with
  | exn -> (close_in in_channel; raise exn)

let check_query prefix query =
  let tidyup s = 
    (* if !keep_log then Z3.close_log (); *)
    print_string s;
    flush stdout;
    flush stderr
  in
  try
    if !keep_log then 
      (let logname = prefix ^ ".log" in
       print_newline (print_string ("opening log file " ^ logname ^ "; " ^ string_of_bool (Z3.open_log logname)))
      );
    Printf.printf "\nQuery is: %s\n" (string_of_query query); 
    let tautZ3 f fs =
      match z3check_query Tautology (fun () -> "") !verbose (List.rev fs) f with
      | Valid     _                  -> 
          print_string ("\nValid\n")
      | Invalid   (assertions, f, m) ->
          if !verbose || !verbose_z3report || !z3track<>Z3trackOff then
            print_string ("\nInvalid with counter-example\n" ^ m ^ "\n")
          else
            Printf.printf "\nInvalid\n"
      | Undecided (assertions, f, m) -> 
          print_string ("\n**Unknown with remark " ^ m ^ "\n")
      | BadQuery (f, s)    -> 
          print_string ("\n**BadQuery " ^ s ^ "\n")
    in
    let show_sat = function
      | Valid     _                  -> "Sat"
      | Invalid   (assertions, f, m) -> "Unsat"
      | Undecided (assertions, f, m) -> "Unknown with remark " ^ m 
      | BadQuery (f, s)              -> "BadQuery " ^ s 
    in
    let satZ3 f fs =
      z3check_query Satisfiable (fun () -> "") !verbose (List.rev fs) f
    in
    let rec show_query fs query =
      match fs with 
      | []    -> explain_string_of_formula query
      | f::fs -> "_assert " ^ string_of_formula f ^ ";\n" ^ show_query fs query
    in
    let rec do_query assertions query =
      match query with 
      | Qassert (f,q)        -> do_query (f::assertions) q
      | Qtaut f              -> tautZ3 f assertions
      | Qsat f               -> Printf.printf "\n%s\n" (show_sat (satZ3 f assertions))
      | Qstableformula (p,i) ->
          let scq = Stability.sc_stable_query_intfdesc p i in
          Printf.printf "\nsc stability\n%s\n" (show_query assertions scq);
          tautZ3 scq assertions;
          let satq, extq = Stability.ext_stable_queries_intfdesc Strongestpost.ExtHat p i in
          Printf.printf "\next stability\n_sat(%s) =>\n%s\n" (string_of_formula satq) (show_query assertions extq);
          (match satZ3 satq assertions with 
           | Invalid _ -> Printf.printf "\nUnsat, therefore Valid\n"
           | r         -> Printf.printf "\n%s\n" (show_sat r); 
                          tautZ3 extq assertions
          );
          let satq, uoq = Stability.uo_stable_queries_intfdesc p i in
          Printf.printf "\nuo stability\n_sat(%s) =>\n%s\n" (string_of_formula satq) (show_query assertions uoq);
          (match satZ3 satq assertions with 
           | Invalid _ -> Printf.printf "\nUnsat, therefore Valid\n"
           | r         -> Printf.printf "\n%s\n" (show_sat r); 
                          tautZ3 uoq assertions
          )
      | Qstableintf (i1,i2)  -> 
          let i1i = Intfdesc.instance NameSet.empty i1 in
          let boq = Stability.bo_stable_query_intfdesc i1i.i_pre i2 in
          Printf.printf "\nbo stability 1 against 2\n%s\n" (show_query assertions boq);
          tautZ3 boq assertions;
          let i2i = Intfdesc.instance NameSet.empty i2 in
          let boq = Stability.bo_stable_query_intfdesc i2i.i_pre i1 in
          Printf.printf "\nbo stability 2 against 1\n%s\n" (show_query assertions boq);
          tautZ3 boq assertions
      | Qspimplies  (p,assign,q) -> 
          let sp = Strongestpost.strongest_post true p assign in
          let spq = _recImplies sp q in
          Printf.printf "\nsp-implies assertion\n%s\n" (show_query assertions spq);
          tautZ3 spq assertions
    in
    let start = Time.start_timer() in
    do_query [] query;
    Time.show_interval "total time" (Time.interval start (Time.now()));
    tidyup "";
  with 
  | Sys_error s                 -> tidyup ("\n\n** FATAL Sys_error \""^s^"\"")
  | Error s | Formula.Error s   -> tidyup ("\n\n" ^ s)
  | AskZ3.Crash s               -> tidyup ("\n\n** CRASH: " ^ s)
  | Z3.Error(_,code)            -> tidyup ("\n\n** Z3 error: " ^ Z3utils.string_of_Z3error_code code)
  | Report.Exit                 -> tidyup ("")
  | Invalid_argument s          -> tidyup ("\n\n** Invalid argument: " ^s)
  | exn                         -> tidyup ("\n\n** Unexpected exception " ^ Printexc.to_string exn)

let checkfile filename = 
  AskZ3.z3_querycount:=0;
  AskZ3.triv_querycount:=0;
  AskZ3.invalid_querycount:=0;
  AskZ3.unsat_querycount:=0;
  AskZ3.undef_querycount:=0;
  errorcount:=0;
  undecidedcount:=0;
  warningcount:=0;
  print_newline (print_string ("\nprocessing " ^ filename));
  let basename = Filename.basename filename in
  let prefix = 
    try Filename.chop_extension basename with _ -> basename
  in
  List.iter (check_query prefix) (parse_queries_from_file filename);
  let showvar name vref =
    if !vref=0 then ""
    else
      Printf.sprintf "%s %d"
                     name !vref
  in
  let results = [showvar "Z3 queries"            AskZ3.z3_querycount;
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

let _ = match !Usage.files with 
        | [] -> List.iter (check_query "stdin") (parse_queries_from_channel stdin)
        | fs -> List.iter checkfile (List.rev fs)
