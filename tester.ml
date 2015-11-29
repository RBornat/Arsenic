open Function
open Listutils
open Tuple

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let unexpected = ref 0
let time = ref ""
let results = ref ""

type flag = FError | FUndecided

let runtest progname files args flags = 
  let args = String.concat " " args in
  let files = String.concat " " files in
  let command = 
    if args<>"" then "./Arsenic " ^ args ^ " " ^ files
                else "./Arsenic " ^ files
  in
  if files="" then (Printf.printf "%s -- no file specified\n" command; exit 1);
  Printf.printf "%s\n" command;
  let channel = Unix.open_process_in command in
  let rec take n xs =
    match n, xs with
      0, _       -> []
    | _, []      -> []
    | _, x :: xs -> x :: take (n-1) xs
  in
  let rec find ws words =
    try ws = take (List.length ws) words || find ws (List.tl words)
    with 
    | Failure "tl" -> false
  in
  let string_of_flag = function
    | FError     -> "error"
    | FUndecided -> "undecided"
  in
  let rec accept flags flag n words =
    match flags with
    | []                    -> Printf.printf "\n**Unexpected %s line %d %s"
                                             (string_of_flag flag)
                                             n
                                             (String.concat " " words);
                               unexpected := !unexpected+1;
                               []
    | (flag',m,ws as e)::es -> if flag=flag' && n=m && find ws words then es
                               else e::accept es flag n words
  in
  let rec checkoutput flags =
    try let s = input_line channel in
        (* Printf.printf "%s\n" s; *)
        let words = Stringutils.words s in
        match words with
        | "**ERROR"::"line"::n::words      -> checkoutput (accept flags FError (int_of_string n) words)
        | "**ERROR:"::words                -> checkoutput (accept flags FError 0 words)
        | "**OH"::"BOTHER"::"line"::n::words -> checkoutput (accept flags FUndecided (int_of_string n) words)
        | "**OH"::"BOTHER"::words            -> checkoutput (accept flags FUndecided 0 words)
        | "total"::"time"::"CPU"::secs::_  -> time:=secs; checkoutput flags
        | "proof"::"obligations"::_        -> results:=s; checkoutput flags
        | "**"::"FATAL"::"Sys_error"::_    
        | "**Parse"::"error"::_            
        | "**"::"BADQUERY"::_              -> Printf.printf "%s\n" s; exit 1
        | _ when Stringutils.starts_with s "**"
                                           -> Printf.printf "%s\n" s; 
                                              unexpected := !unexpected+1;
                                              checkoutput flags
        | _                                -> checkoutput flags
    with End_of_file -> flags
  in
  let unseen = checkoutput flags in
  (match unseen with
   | [] -> ()
   | _  -> Printf.printf "\n**Expected %s" 
             (string_of_list (fun (flag,n,ws) -> Printf.sprintf "%s line %d %s" 
                                                                (string_of_flag flag) 
                                                                n 
                                                                (String.concat " " ws)
                             )
                             "\n**and "
                             unseen
             )
  );
  let status = Unix.close_process_in channel in
  let summary = 
    match !time, !results with
    | "", "" -> ""
    | "", r  -> r
    | t , r  -> String.concat " " [t; "sec"; r]
  in
  match status with
  | Unix.WEXITED   i -> if i<>0 then Printf.printf "\nunexpected exit %d" i 
                        else 
                        if !unexpected=0 && List.length unseen=0 then 
                          Printf.printf "OK %s\n" summary
                        else
                          print_newline();
                        exit i
  | Unix.WSIGNALED i -> Printf.printf "\nkilled by signal %d" i; exit 1
  | Unix.WSTOPPED  i -> Printf.printf "\nstopped by signal %d" i; exit 1
  
let progname = Sys.argv.(0)
let args = List.tl (Array.to_list Sys.argv)

let files, args = List.partition (fun s -> Stringutils.ends_with s ".proof" ||
                                           Stringutils.ends_with s ".unproof" ||
                                           Stringutils.ends_with s ".unparse"
                                 )
                                 args

let rec getflags es args = function
  | "-error" :: n :: word 
    :: rest                     -> (try getflags ((FError, int_of_string n, Stringutils.words word)::es) args rest
                                    with Failure "int_of_string" -> 
                                      Printf.printf "\n-error %s %s ignored -- %s should be integer"
                                                    n word n;
                                      getflags es args rest
                                   )
  | "-undecided" :: n :: word 
                      :: rest   -> (try getflags ((FUndecided, int_of_string n, Stringutils.words word)::es) args rest
                                    with Failure "int_of_string" -> 
                                      Printf.printf "\n-error %s %s ignored -- %s should be integer"
                                                    n word n;
                                      getflags es args rest
                                   )
  | arg                 :: rest -> getflags es (arg::args) rest
  | []                          -> List.rev es, List.rev args

let flags, args = getflags [] [] args

let _ = runtest progname files args flags
