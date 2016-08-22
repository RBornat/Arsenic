open Function
open Name
open Sourcepos
open Listutils

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
(* don't open anything else: circularity beckons *)

let fileprefix = ref ""

let lace_only = ref false

let set_bool bref b = bref:=b

(* *********************** -verbose ****************************** *)

let verbose = ref false
let verbose_auxiliaries = ref false
let verbose_coherence = ref false
let verbose_dependencies = ref false
let verbose_disjunction = ref false
let verbose_graph = ref false
let verbose_lace = ref false
let verbose_knots = ref false
let verbose_modality = ref false
let verbose_proof = ref false
let verbose_relies = ref false
let verbose_semicolon = ref false
let verbose_selfstability = ref false
let verbose_structuredcommand = ref false
let verbose_timing = ref false
let verbose_z3check = ref false
let verbose_z3report = ref false
let verbose_z3benchmark = ref false

let verboseopts = [("all"              , verbose                  ); 
                   ("auxiliaries"      , verbose_auxiliaries      );
                   ("coherence"        , verbose_coherence        );
                   ("disjunction"      , verbose_disjunction      );
                   ("dependencies"     , verbose_dependencies     );
                   ("graph"            , verbose_graph            );
                   ("lace"             , verbose_lace             ); 
                   ("knots"            , verbose_knots            ); 
                   ("modality"         , verbose_modality         ); 
                   ("proof"            , verbose_proof            ); 
                   ("relies"           , verbose_relies           ); 
                   ("selfstability"    , verbose_selfstability    );
                   ("semicolon"        , verbose_semicolon        ); 
                   ("structuredcommand", verbose_structuredcommand); 
                   ("timing"           , verbose_timing           );
                   ("timings"          , verbose_timing           );
                   ("z3benchmark"      , verbose_z3benchmark      );
                   ("Z3benchmark"      , verbose_z3benchmark      );
                   ("z3check"          , verbose_z3check          );
                   ("Z3check"          , verbose_z3check          ); 
                   ("z3report"         , verbose_z3report         );
                   ("Z3report"         , verbose_z3report         )
                  ] 
let setverbose s = (List.assoc s verboseopts) := true

let temp_setting vref v f =
  let oldv = !vref in
  vref := v;
  try
    let result = f () in
    vref := oldv;
    result
  with exn -> vref:=oldv; raise exn
  
let push_verbose v f = 
  temp_setting verbose (!verbose||v) f
  
(* *********************** -tree_formulas ****************************** *)

let tree_formulas = ref true

(* *********************** -z3 parameters ************************ *)

let z3timeout = ref 4000
let z3benchmarks = ref false
let z3onecontext = ref false
let keep_log = ref false
let z3usenonlinear = ref false
let z3useqe = ref true

type z3tracktype = Z3trackLong | Z3trackShort | Z3trackQueryOnly | Z3trackOff

let z3trackopts = [("long", Z3trackLong); ("short", Z3trackShort); ("query", Z3trackQueryOnly); ("off", Z3trackOff)]

let z3track = ref Z3trackOff
let setz3track s = z3track := z3trackopts <@> s

let z3counters = ref false

(* *********************** stability ************************ *)

let param_SCreg = ref true
let param_SCloc = ref true
let param_LocalSpec = ref true

(* *********************** miscellaneous ************************ *)

let maxerrors = ref 0
let simpleUBsince = ref false
let expand_macros = ref true
let all_valid = ref false
let allow_tcep = ref false
let sp_unchanged = ref true

