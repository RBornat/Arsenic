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
                   " verbose proofcheck, defaults false");
                ("suppresswarnings", Arg.Clear Report.show_warnings, " suppress warning messages");
                ("-allvalid", Arg.Set all_valid, " accept all proof dependencies");
                ("-laceonly", Arg.Set lace_only, " lace only, no proof");
                ("-maxerrors", Arg.Set_int maxerrors, 
                    " quit after this number of Z3 errors or unknowns");
                ("-spunchanged", Arg.Bool (set_bool sp_unchanged), 
                    " conjoin x=(-x) in sp for unchanged x (default true)");
                ("-noproof", Arg.Set lace_only, " lace only, no proof");
                ("-sat", Arg.Bool (set_bool param_usesat), " use sat check in stability (default true)");
                ("-SCreg", Arg.Bool (set_bool param_SCreg), " register renaming (default true)");
                ("-SCloc", Arg.Bool (set_bool param_SCloc), " SC per location (default true)");
                ("-LocalSpec", Arg.Bool (set_bool param_LocalSpec), " don't speculate propagation (default true)");
                ("-treeformulas", Arg.Bool (set_bool tree_formulas), 
                    " print big formulas as trees in error reports (default true)");
                ("-tree_formulas", Arg.Bool (set_bool tree_formulas), 
                    " print big formulas as trees in error reports (default true)");
                ("-simpleUBsince", Arg.Bool (set_bool simpleUBsince), 
                    " use simple, but slower, Univ/B-> since translation (default false)");
                ("-z3benchmarks", Arg.Bool (set_bool z3benchmarks), 
                    " produce .smt2 files for each Z3 query (default false)");
                ("-z3onecontext", Arg.Set z3onecontext, 
                    " use the same context repeatedly, until a timeout");
                ("-z3timeout", Arg.Set_int z3timeout, 
                    " Z3 timeout setting, in milliseconds (default 4000)");
                ("-z3track", Arg.Symbol (List.map fstof2 z3trackopts, setz3track), 
                    " show z3 enquiries even when not verbose");
                ("-z3usenonlinear", Arg.Set z3usenonlinear, 
                    " use the non-linear arithmetic solver");
                ("-z3useqe", Arg.Bool (set_bool z3useqe), 
                    " use qe tactic (default true)");
                ("-z3log"    , Arg.Set    keep_log   , " open Z3 log");
                ("-z3counters", Arg.Set z3counters   , " show Z3 (counter) models (default false)");
                ("-error"  , Arg.Tuple [Arg.Set_string ignored; Arg.Set_string ignored],
                             " ignored (flag for Test)")
                
               ]
let _ = Arg.parse opts (fun s -> files := s :: !files) usage

