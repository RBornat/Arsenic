open Tuple
open Settings

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let progname = Sys.argv.(0)
let files = ref []
let usage = "Usage: " ^ progname ^ " [options]* filename filename ..."
let ignored = ref ""
let opts = Arg.align
               [("-verbose", Arg.Symbol (List.map fstof2 verboseopts, setverbose), 
                   " verbose proofcheck, various arguments, defaults false" );
                ("suppresswarnings", Arg.Clear Report.show_warnings, " suppress warning messages");
                ("-allvalid", Arg.Set all_valid, " accept all proof dependencies");
                ("-laceonly", Arg.Set lace_only, " lace only, no proof");
                ("-maxerrors", Arg.Set_int maxerrors, 
                    " quit after this number of Z3 errors or unknowns");
                ("-spunchanged", Arg.Bool (set_bool sp_unchanged), 
                    Printf.sprintf " conjoin x=(-)x in sp for unchanged x (default %B)" !sp_unchanged);
                ("-noproof", Arg.Set lace_only, " lace only, no proof");
                ("-SCreg", Arg.Bool (set_bool param_SCreg), 
                    Printf.sprintf " register renaming (default %B)" !param_SCreg);
                ("-SCloc", Arg.Bool (set_bool param_SCloc), 
                    Printf.sprintf " SC per location (default %B)" !param_SCloc);
                ("-LocalSpec", Arg.Bool (set_bool param_LocalSpec), 
                    Printf.sprintf " don't speculate propagation (default %B)" !param_LocalSpec);
                ("-allow_bu_coincidence", Arg.Bool (set_bool allow_bu_coincidence), 
                    Printf.sprintf " allow temporal coincidences in _B and _U (default %B)" !allow_bu_coincidence);
                ("-treeformulas", Arg.Bool (set_bool tree_formulas), 
                    Printf.sprintf " print big formulas as trees in error reports (default %B)" !tree_formulas);
                ("-tree_formulas", Arg.Bool (set_bool tree_formulas), 
                    Printf.sprintf " print big formulas as trees in error reports (default %B)" !tree_formulas);
                ("-z3benchmarks", Arg.Bool (set_bool z3benchmarks), 
                    Printf.sprintf " produce .smt2 files for each Z3 query (default %B)" !z3benchmarks);
                ("-z3onecontext", Arg.Set z3onecontext, 
                    " use the same context repeatedly, until a timeout");
                ("-z3timeout", Arg.Set_int z3timeout, 
                    Printf.sprintf " Z3 timeout setting, in milliseconds (default %d)" !z3timeout);
                ("-z3track", Arg.Symbol (List.map fstof2 z3trackopts, setz3track), 
                    " show z3 enquiries even when not verbose");
                ("-z3usenonlinear", Arg.Set z3usenonlinear, 
                    " use the non-linear arithmetic solver");
                ("-z3useqe", Arg.Bool (set_bool z3useqe), 
                    Printf.sprintf " use qe tactic (default %B)" !z3useqe);
                ("-z3log"    , Arg.Set    keep_log   , " open Z3 log");
                ("-z3counters", Arg.Set z3counters   , 
                    Printf.sprintf " show Z3 (counter) models (default %B)" !z3counters);
                ("-error"  , Arg.Tuple [Arg.Set_string ignored; Arg.Set_string ignored],
                             " ignored (flag for Test)")
                
               ]
let _ = Arg.parse opts (fun s -> files := s :: !files) usage

