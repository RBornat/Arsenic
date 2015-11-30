open Sourcepos

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
(* ******************* reporting errors, warnings, etc. **************** *)

exception Exit

let errorcount     = ref 0
let undecidedcount = ref 0
let warningcount   = ref 0
let remarkcount    = ref 0

let show_warnings = ref true (* unset by -suppresswarnings switch *)

let ignore_undecided () = undecidedcount := !undecidedcount-1

type report = 
  | Error     of sourcepos * string
  | Undecided of sourcepos * string
  | Warning   of sourcepos * string
  | Remark    of sourcepos * string

let reportbuffer = ref []
let reportbuffer_buffer = ref []
let reports = ref []

let report stuff = 
  if Listutils.null !reportbuffer_buffer then
    (let kind, loc, s, ref, show = 
       (match stuff with 
        | Error     (loc,s) -> "**ERROR"    , loc, s, errorcount    , true
        | Undecided (loc,s) -> "**OH BOTHER", loc, s, undecidedcount, true
        | Warning   (loc,s) -> "**WARNING"  , loc, s, warningcount  , !show_warnings
        | Remark    (loc,s) -> ""           , loc, s, remarkcount   , !show_warnings
       )
     in
     let message = 
         "\n" ^ kind ^
         (if loc=dummyloc then "" else (" " ^ string_of_location loc)) ^ 
         ": " ^ s
     in
     if not (List.mem message !reports) then
       (reports := message::!reports;
        if show then print_newline (print_string message);
        ref := !ref + 1;
        let maxerrors = !Settings.maxerrors in
        if maxerrors>0 && !errorcount + !undecidedcount=maxerrors then
          raise Exit
       )
    )
  else
    reportbuffer := stuff :: !reportbuffer
    
let push_reports () = 
  (reportbuffer_buffer := !reportbuffer :: !reportbuffer_buffer;
   reportbuffer := []
  )

let pop_reports () =
  match !reportbuffer_buffer with
  | []                -> raise (Invalid_argument "pop_reports")
  | buffer :: buffers -> (let reports = !reportbuffer@buffer in
                          reportbuffer := [];
                          reportbuffer_buffer := buffers;
                          List.iter report (List.rev reports)
                         )

let discard_reports () = 
  match !reportbuffer_buffer with
  | []                -> raise (Invalid_argument "discard_reports")
  | buffer :: buffers -> (reportbuffer := buffer;
                          reportbuffer_buffer := buffers
                         )

let mark_reports () = !reportbuffer

let discard_allbutwarnings mark =
  if Listutils.null !reportbuffer_buffer then
    raise (Invalid_argument "discard_allbutwarnings unbuffered")
  else
    (let rec retrieve_warnings reports =
       if reports==mark then [] else
         match reports with
         | []                          -> raise (Invalid_argument "discard_allbutwarnings no mark")
         | (Warning _ as w) :: reports
         | (Remark  _ as w) :: reports -> w :: retrieve_warnings reports
         | _                :: reports -> retrieve_warnings reports
     in
     let warnings = retrieve_warnings !reportbuffer in
     discard_reports ();
     List.iter report (List.rev warnings)
    )

let is_allwarnings mark = 
  if Listutils.null !reportbuffer_buffer then
    raise (Invalid_argument "is_allwarnings unbuffered")
  else
    (let rec check_warnings reports =
       if reports==mark then true else
         match reports with
         | []                   -> raise (Invalid_argument "is_allwarnings no mark")
         | Warning _ :: reports 
         | Remark  _ :: reports -> check_warnings reports
         | _                    -> false
     in
     check_warnings !reportbuffer
    )
