open Listutils
open Option
open Sourcepos
open Formula
open Name
open Com
open Thread

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception ParseError of sourcepos * string (* because I can't put it in Parser, and I have to put it somewhere *)

type outerassert = positionedlabel * formula

type program = {p_preopt    : outerassert option;
                p_givopt    : formula option;
                p_hdrs      : header list;          (* for tolatex *)
                p_ts        : thread list;
                p_postopt   : outerassert option;
               }

let get_outerassert_lab ouaopt =
  match ouaopt with
  | Some ({lablab=lab},_) -> Some lab
  | None                  -> None

let string_of_outerassert (poslab, f) =
    "{ " ^ string_of_label poslab.lablab ^ ": " ^ string_of_formula f ^ " }"

let threadsep = "-----------------------"

let string_of_threadlist = 
  string_of_list string_of_thread ("\n" ^ threadsep ^ "\n")

let string_of_given i =
  "given {" ^ string_of_formula i ^ "}"

let string_of_program {p_preopt=preopt; p_givopt=givopt; p_ts = ts; p_postopt=postopt } = 
  (match preopt, givopt with
   | None, None  -> ""
   | _           -> sofirst string_of_outerassert "\n" preopt ^ 
                    sofirst string_of_given "\n" givopt ^ 
                    threadsep ^ 
                    "\n"
  ) ^ 
  string_of_threadlist ts ^ 
  (match postopt with 
   | None -> ""
   | _    -> "\n" ^ threadsep ^ solast "\n" string_of_outerassert postopt
  )


