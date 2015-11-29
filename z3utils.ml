open Settings
open Tuple
open Program
open Z3
open Printer

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let string_of_Z3error_code = function
  | Z3.OK                -> "OK"
  | Z3.SORT_ERROR        -> "SORT_ERROR"
  | Z3.IOB               -> "IOB"
  | Z3.INVALID_ARG       -> "INVALID_ARG"
  | Z3.PARSER_ERROR      -> "PARSER_ERROR"
  | Z3.NO_PARSER         -> "NO_PARSER"
  | Z3.INVALID_PATTERN   -> "INVALID_PATTERN"
  | Z3.MEMOUT_FAIL       -> "MEMOUT_FAIL"
  | Z3.FILE_ACCESS_ERROR -> "FILE_ACCESS_ERROR"
  | Z3.INTERNAL_FATAL    -> "INTERNAL_FATAL"
  | Z3.INVALID_USAGE     -> "INVALID_USAGE"
  | Z3.DEC_REF_ERROR     -> "DEC_REF_ERROR"
  | Z3.EXCEPTION         -> "EXCEPTION"

type sortinfo = 
  | SimpleSort of sort 
  | TupleSort  of sort * func_decl
  | FuncSort   of sort * func_decl
  | ArraySort  of sort
  | VarSort    of sort

let sort_of_sortinfo = function
  | SimpleSort  s    -> s
  | TupleSort  (s,_) -> s
  | FuncSort   (s,_) -> s
  | ArraySort  s     -> s
  | VarSort    s     -> s

let rec string_of_sortinfo ctx = function 
  | SimpleSort s          -> "SimpleSort " ^ sort_to_string ctx s 
  | TupleSort  (s,fdecl)  -> "TupleSort " ^ bracketed_string_of_pair (sort_to_string ctx) 
                                                                     (func_decl_to_string ctx) 
                                                                     (s,fdecl)
  | FuncSort   (s,fdecl)  -> "FuncSort " ^ bracketed_string_of_pair (sort_to_string ctx) 
                                                                    (func_decl_to_string ctx) 
                                                                    (s,fdecl)
  | ArraySort  s          -> "ArraySort " ^ sort_to_string ctx s
  | VarSort    s          -> "VarSort " ^ sort_to_string ctx s
