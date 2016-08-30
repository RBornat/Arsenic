open Function
open Tuple
open Listutils
open Z3
open Program
open Typecheck
open Printer
open Formula
open Ftype
open Name
open Modality
open Z3utils
open Settings
open Time

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception Crash of string

type z3result = 
  | Valid     of formula list * formula
  | Invalid   of formula list * formula * string 
  | Undecided of formula list * formula * string
  | BadQuery  of formula * string

let shortstring_of_z3result = function 
  | Valid     _ -> "valid"
  | Invalid   _ -> "invalid"
  | Undecided _ -> "unknown"
  | BadQuery  _ -> "bad query"
                                         
let z3_querycount = ref 0
let triv_querycount = ref 0
let invalid_querycount = ref 0
let unsat_querycount = ref 0
let undef_querycount = ref 0

let z3ctx = ref None

(* plagiarised from Josh Berdine's test_mlapi.ml *)
(**
   Prove that the constraints already asserted in the logical
   context implies the given formula.
   Z3 is a satisfiability checker. So, one can prove f by showing
   that (not f) is unsatisfiable.
   The context z3context is not modified by this function.
*)
type z3question = Tautology | Satisfiable

let string_of_z3question = function
  | Tautology   -> "Tautology"
  | Satisfiable -> "Satisfiable"

let z3validate question noisy z3context slv asserts f ast_asserts ast_f =
  z3_querycount := !z3_querycount+1;

  (* save the current state of the solver *)
  solver_push z3context slv;

  try
    List.iter (solver_assert z3context slv) ast_asserts;
    let ast_query = 
      match question with 
      | Tautology   -> mk_not z3context ast_f 
      | Satisfiable -> ast_f
    in
    solver_assert z3context slv ast_query;
    let verbmark res ex = 
       push_verbose !verbose_z3benchmark (fun () ->
         if !verbose || !z3benchmarks then
           (set_ast_print_mode z3context Z3.PRINT_SMTLIB2_COMPLIANT;
            let qid = ex ^ string_of_int !z3_querycount in
            let qstring = 
              benchmark_to_smtlib_string z3context
                                         qid
                                         ""
                                         res
                                         (if !Settings.z3timeout=0 then ""
                                          else ("(set-option :timeout " ^ string_of_int  !Settings.z3timeout ^ ")\n")
                                         )
                                         (Array.of_list ast_asserts)
                                         ast_query
            in
            set_ast_print_mode z3context Z3.PRINT_SMTLIB_FULL; 
            if !verbose then
              print_newline (print_string ("\nz3validate\n" ^ qstring));
            if !z3benchmarks then
              (let prefix = !Settings.fileprefix ^
                            "_t"^(* string_of_int !Thread.tindex ^ *)
                            "_ex" ^ string_of_int !z3_querycount ^
                            "_" in
               let name,ch = Filename.open_temp_file prefix ".smt2" in
               output_string ch qstring;
               close_out ch;
               Printf.printf "\nbenchmark %s in tmp file %s" qid name
              )
           )
         )
    in
    verbmark "unknown" "preexample"; (* in case of a segfault *)
    if !verbose_timing then
      (let _ = now() in ());
    let result = solver_check z3context slv in
    if !verbose_timing then
      Time.show_interval "solver_check" (last_interval());
    verbmark (match result with
              | L_FALSE -> "unsat"
              | L_TRUE  -> "sat"
              | L_UNDEF -> "unknown"
             ) 
             "example";
  
    let get_mstring () = 
                     (* if !verbose then print_newline (print_string "calling solver_get_model\n"); *)
                     let m = solver_get_model z3context slv in
                     (* if !verbose then print_newline (print_string "solver_get_model returned; calling model_to_string\n"); *)
                     let mstring = model_to_string z3context m in
                     if !verbose then 
                       ((* print_newline (print_string "model_to_string returned\n"); *)
                        print_newline (print_string mstring);
                        print_newline ();
                       );
                     mstring
    in
    let result = match result with
                 | Z3.L_FALSE -> (* unsat *)
                     (match question with
                      | Tautology ->
                          if !verbose then print_newline (print_string "negation unsat, therefore valid tautology\n");
                          Valid (asserts, f)
                      | Satisfiable -> 
                          unsat_querycount := !unsat_querycount+1;
                          if !verbose then 
                            print_newline (print_string "unsat, therefore invalid satisfiable\n")
                          else if noisy then 
                            print_newline (print_string ("\n** invalid z3validate Satisfiable (" ^ ast_to_string z3context ast_f ^ ")"));
                          Invalid (asserts, f, "")
                     )
                 | Z3.L_TRUE -> (* sat *)
                     (match question with
                      | Tautology ->
                          invalid_querycount := !invalid_querycount+1;
                          if !verbose then print_newline (print_string "negation sat, therefore invalid tautology\n") 
                          else if noisy then 
                            print_newline (print_string ("\n** invalid z3validate Tautology (" ^ ast_to_string z3context ast_f ^ ")"));
                          let mstring = get_mstring () in
                          if noisy then print_newline (print_string (mstring ^ "\n"));
                          Invalid (asserts, f, mstring)
                      | Satisfiable -> 
                          if !verbose then 
                            Printf.printf "\nsat, therefore valid Satisfiable with example %s\n"
                                          (get_mstring ());
                          Valid (asserts, f)
                     )
                 | Z3.L_UNDEF -> (* unknown *)
                     undef_querycount := !undef_querycount+1;
                     if !verbose then print_newline (print_string ("unknown z3validate " ^ string_of_z3question question ^ "\n"))
                     else if noisy then
                       print_newline (print_string ("\n** undecided z3validate " ^ string_of_z3question question ^ 
                                                    " (" ^ ast_to_string z3context ast_f ^ ")"));
                     try 
                         let mstring = solver_get_reason_unknown z3context slv in
                         if noisy then print_newline (print_string (mstring ^ "\n"));
                         Undecided (asserts, f, mstring)
                      with
                        Z3.Error(_,Z3.INVALID_USAGE) ->
                          Undecided (asserts, f, "-- no reason available (probably because of a timeout)")
    in
    (* restore context *)
    solver_pop z3context slv 1;
    (* if !verbose then
         print_newline (print_string ("\nz3validate popped"));
     *)
    result
  with exn -> solver_pop z3context slv 1; raise exn

let in_pms = ref false (* secret parameter for postcondition check *)

let track_query () = !z3track<>Z3trackOff
let track_tree () = !z3track<>Z3trackOff && !z3track<>Z3trackQueryOnly
let track_embedding () = !z3track=Z3trackLong
let track_result () = !z3track<>Z3trackOff && !z3track<>Z3trackQueryOnly

let activity_chars = Array.of_list ['/'; '-'; '\\'; '|']
let activity_idx = ref 0

let z3check_query question task noisy assertions query =
  push_verbose !verbose_z3check (fun () -> 
    if !verbose || !z3track<>Z3trackOff then
      (let taskstring = task() in
        if taskstring="" then print_string "\nz3check_query "
        else Printf.printf "\nz3check_query %s\n" taskstring
      )
    (* doesn't work else 
      (Printf.printf "\r%c\027[K" (activity_chars.(!activity_idx));
       flush stdout;
       activity_idx := (!activity_idx + 1) mod 4 
      ) *);
    let verbinfo s query assertions = 
      if !verbose then
        print_string (s ^ 
            (if null assertions then explain_string_of_formula query 
             else ("query = " ^ explain_string_of_formula query ^
                   "\nassertions = " ^ 
                   bracketed_lines_of_list 
                     (if !Settings.tree_formulas then indented_string_of_formula true 4 
                      else string_of_formula
                     ) 
                     assertions ^ 
                   "\n"
                  )
            ))
    in
    push_verbose (track_tree ()) (fun () -> verbinfo "" query assertions);
    (* filter out nonsense *)
    let verbtriv result =
      if !verbose || !z3track=Z3trackLong then
        Printf.printf "\n%s (trivially)" (shortstring_of_z3result result);
      triv_querycount := !triv_querycount+1;
      result
    in
    match query.fnode with 
    | LogArith(f, Implies, _) when is_recFalse f -> verbtriv (Valid (assertions, query))
    | LogArith(_, Implies, t) when is_recTrue  t -> verbtriv (Valid (assertions, query))
    | _                                          ->
    (* What's the threadcount appropriate to this query?
    
       If a query has (^) or (~) alone, then two threads.
       If it has (^) and (^^) or ((~) and (~~) together, then three.
       If it has Threaded, then count the threads.
       Otherwise just one thread (it's an SC query, really it is).
     *)
    let count_threads n f =
      match f.fnode with
      | Threaded (i, _)    -> Some (Pervasives.max n (i+1))
      | Fvar(Some h, _, _) -> let i = Modality.tn_of_hat h in
                              Some (Pervasives.max n (i+1))
      | _                  -> None
    in
    let tc = List.fold_left (Formula.fold count_threads) 1 (query::assertions) 
    in
    Settings.temp_setting Thread.threadcount tc (fun () ->
      (try 
           (* a simple way to get Univ(true), B(true) equivalent to true. All I really need
              is the barrier event.
            *)
           let assertions = 
              if List.exists (Formula.exists (is_recU <||> is_recBfr)) (query::assertions)
              then (Modality.ur_event ())::assertions 
              else assertions
           in
           (* and say that hatted stuff is from the past *)
           let assertions = 
              if List.exists (Formula.exists is_hatted) (query::assertions)
              then Modality.hat_hi_asserts@assertions 
              else assertions
           in
           (* add _cv assertions for coherence variables, not(_cv ..) for the others *)
           let cvars =
             List.fold_left (get_coherence_vars NameSet.empty) NameSet.empty (query::assertions)
           in
           let assertions = 
             if !Settings.param_SCloc then
               (let frees = List.fold_left Formula.fof NameSet.empty (query::assertions) in
                (* x&new is a technical construct. We don't need coherence for it ... *)
                let frees = NameSet.filter (fun v -> not (Stringutils.ends_with v "&new")) frees in
                assertions @ coherencevar_assertions frees cvars 
               )
             else assertions
           in
           let query, assertions = simplify query, List.map simplify assertions in
           push_verbose (track_embedding ()) (fun () -> verbinfo "\nsimplified query\n" query assertions);
           let get_varmap cxt bcxt query assertions = 
             let types, binders = 
               completed_typeassign_formula_list cxt bcxt Bool (query::assertions) 
             in 
             types, binders, List.sort Pervasives.compare (* for lexical order *)
                                       (List.filter (is_anyvar <.> fstof2) types) 
           in
           let _, binders, varmap = 
             get_varmap [] [] query assertions 
           in
           let state_params, state_paramtypes = List.split varmap in
         
           (* do the embedding *)
           let embed () =
             let modal_cxt, assertions = 
               Listutils.mapfold (Modality.embed binders) [] assertions 
             in
             let modal_cxt, query = 
               Modality.embed binders modal_cxt query
             in
             let coherencetypes =
               List.fold_left (fun set binding -> match extract_coherencetype binding with
                                                  | Some t -> FtypeSet.add t set
                                                  | None   -> set
                              )
                              FtypeSet.empty
                              modal_cxt
             in
             let axioms = 
               if !in_pms then Coherence.pms_axiom :: Coherence.coherence_axioms
                          else Coherence.coherence_axioms
             in
             let modal_cxt, axioms =
               embed_axiom (FtypeSet.elements coherencetypes) 
                           modal_cxt 
                           (fandw NoHook (conjoin axioms)) 
             in
             let assertions = assertions@axioms in
             modal_cxt, query, assertions
           in
           let modal_cxt, query, assertions =
             Settings.temp_setting Thread.threadnum 0 embed
           in
         
           push_verbose (track_embedding ()) (fun () ->
             verbinfo "\nz3check_query with translated temporal assertions\n" query assertions
           );
           if !verbose then 
             Printf.printf "\nmodal_cxt=[%s]" (string_of_ftypecxt modal_cxt);
          
           let types, binders = 
             completed_typeassign_formula_list (mfilter modal_cxt)
                                               [] 
                                               Bool
                                               (query::assertions)
           in
                  
           (* now, for goodness sake, the variables are distinct. No aliasing. 
              (Didn't think I'd have to tell Z3 that ...)
            *)
           let vars = 
             List.map fstof2
               (List.filter (function (_,VarType _) -> true | _ -> false) types) 
           in
           let vscross = 
             List.filter (fun (x,y) -> (types<@>x)=(types<@>y)) (notself_crossprod vars) 
           in
           if !verbose && not (Listutils.null vscross) then
             Printf.printf "\nvscross = %s" 
                           (bracketed_string_of_list 
                              (bracketed_string_of_pair string_of_name string_of_name) 
                              vscross
                           );
           let assertions = 
             List.map (fun (x,y) -> _recNotEqual (_recFname x) (_recFname y)) vscross
             @
             assertions
           in
    
           (* translate into Z3 asts *)
         
           let fresh_ctx () = 
             let z3context = mk_context (if !Settings.z3timeout=0 then [] 
                                   else [("timeout",string_of_int !Settings.z3timeout)]
                                  )
             in
             let params = Z3.mk_params z3context in
             if not(!z3usenonlinear) then
               Z3.params_set_bool z3context params (Z3.mk_string_symbol z3context "smt.arith.nl") false;
             z3context, params
           in
           let z3context, params = 
             match !z3onecontext with 
             | false -> fresh_ctx ()
             | true  -> (match !z3ctx with
                         | None     -> let z3context, params = fresh_ctx () in
                                       z3ctx := Some (z3context, params);
                                       z3context, params
                         | Some pair -> pair
                        )
           in
           (* set_ast_print_mode z3context Z3.PRINT_SMTLIB2_COMPLIANT; *)
         
           (* sort out the type-to-sort mapping. Tuples make this tricky *)
           (* let sym_of_name = NameMap.vmemofun !verbose "sym_of_name" string_of_name (get_symbol_string z3context) id (mk_string_symbol z3context) in *)
           let sym_of_name = NameMap.memofun id (mk_string_symbol z3context) in
           (* has to be memoised, because otherwise you get lots of different structured sorts *)
           let type2sortinfo memofun t = 
             let r =
               match t with
               | Int          -> SimpleSort (mk_int_sort  z3context)
               | Bool         -> SimpleSort (mk_bool_sort z3context)
               | TupleType ts -> 
                   let ss = List.map (sort_of_sortinfo <.> memofun) ts in
                   let tuple_sort_name = new_name "tuple_sort" in
                   let rec makefields i = function
                     | []    -> []
                     | s::ss -> 
                        sym_of_name (new_name ("field"^string_of_int i)) :: makefields (i+1) ss
                   in
                   let fieldnames = makefields 1 ss in
                   let tsort, tmakef, taccessorfs  = 
                     mk_tuple_sort z3context (mk_string_symbol z3context tuple_sort_name)
                                             (Array.of_list fieldnames)
                                             (Array.of_list ss)
                   in
                   TupleSort (tsort, tmakef)
               | FuncType _   -> 
                   (* we can't do functional programming: unnamed functions don't have a sort. *)
                   raise (Crash ("unnamed " ^ string_of_ftype t ^ " in sortinfo_of_type with typecxt = [\n\t" ^
                                 string_of_ftypecxt types ^ "]\nand binder_tuple_cxt = [\n\t" ^
                                 string_of_binder_ftypecxt binders ^
                                 "]"))
               | FTypeVar _   -> (* it can happen, e.g. in r2=y. Just say Int *)
                                 memofun Int
               | VarType t    -> let sortname = Modality.typed_name Modality.vartype_name t in
                                 let sort = mk_uninterpreted_sort z3context (mk_string_symbol z3context sortname) in
                                 VarSort sort
             in
             if !verbose then
               Printf.printf "\ntype2sortinfo %s -> %s" (string_of_ftype t) (string_of_sortinfo z3context r);
             r
           in
           let sortinfo_of_type = 
             FtypeMap.vmemorec !verbose "sortinfo_of_type" string_of_ftype (string_of_sortinfo z3context) id type2sortinfo
             (* FtypeMap.memorec id type2sortinfo *)
           in
           let state_param_sortinfos = List.map sortinfo_of_type state_paramtypes in
           let history_fdecl = 
             mk_func_decl 
                  z3context 
                  (sym_of_name history_function_name) 
                  (Array.of_list (List.map sort_of_sortinfo state_param_sortinfos)) 
                  (sort_of_sortinfo (sortinfo_of_type Bool))
           in

           let tb_to_sortinfo_cxt = List.map (fun (f,t) -> f, sortinfo_of_type t) binders in 
         
           let add_ast_cxts (name_ast_cxt, name_fdecl_cxt) (n,t) =
             match t with
             | FuncType (ts,t) -> 
                 name_ast_cxt, 
                 (n, 
                  mk_func_decl z3context (sym_of_name n) 
                                   (Array.of_list 
                                      (List.map (sort_of_sortinfo <.> sortinfo_of_type) ts)
                                   )
                                   (sort_of_sortinfo (sortinfo_of_type t))
                 ) :: name_fdecl_cxt
             | _               -> 
                 (n, 
                  mk_const z3context (sym_of_name n) (sort_of_sortinfo (sortinfo_of_type t))
                 ) :: name_ast_cxt,
                 name_fdecl_cxt
           in
           let build_ast_cxts name_ast_cxt name_fdecl_cxt typecxt =
             List.fold_left add_ast_cxts (name_ast_cxt,name_fdecl_cxt) typecxt
           in
         
           (* commented out to avoid compiler moan
           let string_of_ast_cxt = 
             string_of_assoc (fun n -> "\n\t" ^ string_of_name n) (ast_to_string z3context) ":" ";"
           in
            *)
                  
           (* here we go with the translation *)
           let rec ast_of_formula z3context name_ast_cxt name_fdecl_cxt orig_f =
             let ac2 mk_something z3context a b = mk_something z3context [| a; b |] in
             let arithf = function
             | Plus  -> ac2 mk_add
             | Minus -> ac2 mk_sub
             | Times -> ac2 mk_mul
             | Div   ->     mk_div
             | Mod   ->     mk_mod
             in
             let compf = function
             | Less         ->     mk_lt 
             | LessEqual    ->     mk_le 
             | Equal        ->     mk_eq 
             | NotEqual     -> ac2 mk_distinct
             | GreaterEqual ->     mk_ge 
             | Greater      ->     mk_gt
             in
             let logf = function
             | And     -> ac2 mk_and
             | Or      -> ac2 mk_or
             | Implies ->     mk_implies
             | Iff     ->     mk_iff
             in
             let badtbsort f s = 
               raise (Crash ("sort of " ^ string_of_formula f ^ 
                                  " in tb_to_sortinfo_cxt\n" ^ 
                                  string_of_assoc (fun f -> "\n\t" ^ string_of_formula f)
                                                  (string_of_sortinfo z3context) 
                                                  ":" 
                                                  ";\n" 
                                                  tb_to_sortinfo_cxt ^
                                  "\nis " ^ string_of_sortinfo z3context s))
             in
             let notbsort f =
                raise (Crash ("no sort for " ^ string_of_formula f ^ 
                                   " in tb_to_sortinfo_cxt " ^ string_of_assoc string_of_formula (string_of_sortinfo z3context) ":" "; " tb_to_sortinfo_cxt))
             in
             let rec aof f = 
               match f.fnode with 
               | Fint i                      -> embed_numeral z3context (Numeral_large (i, sort_of_sortinfo (sortinfo_of_type Int)))
               | Fbool b                     -> (if b then mk_true else mk_false) z3context 
               | Freg r                      -> name_ast_cxt <@> r
               | Fvar (_,_,v)                -> name_ast_cxt <@> v (* this is the argument of &v<type>, and also could be a bound variable *)
               | Flogc n                     -> name_ast_cxt <@> n
               | Negarith f                  -> mk_unary_minus z3context (aof f) 
               | Not f                       -> mk_not z3context (aof f)
               | Arith    (left, aop, right) -> (arithf aop) z3context (aof left) (aof right)
               | Compare  (left, cop, right) -> (compf  cop) z3context (aof left) (aof right)
               | LogArith (left, lop, right) -> (logf   lop) z3context (aof left) (aof right)
               | Binder          (bk, n, bf) -> 
                   let rec multibind bk ns napps name_ast_cxt f = match f.fnode with
                     | Binder (bk', n, bf)
                       when bk=bk' && not (List.mem n ns) -> 
                         if is_free n bf then
                           (let nsort = (try sort_of_sortinfo (List.assq f tb_to_sortinfo_cxt)
                                         with Not_found -> notbsort f
                                        )
                            in
                            let nast = mk_const z3context (sym_of_name n) nsort in
                            let napp = to_app z3context nast in
                            multibind bk (n::ns) (napp::napps) ((n,nast)::name_ast_cxt) bf
                           )
                         else
                           multibind bk ns napps name_ast_cxt bf
                     | _ -> List.rev napps, name_ast_cxt, f
                   in
                   let napps, name_ast_cxt, bf = multibind bk [] [] name_ast_cxt f in
                   if null napps then aof bf else
                     (match bk with Forall -> mk_forall_const | Exists -> mk_exists_const)
                         z3context
                         0            (* default weight *)
                         (Array.of_list napps)
                         [| |]        (* no patterns *)
                         (ast_of_formula z3context name_ast_cxt name_fdecl_cxt bf)
               | Tuple fs                    -> 
                   (try match List.assq f tb_to_sortinfo_cxt with
                    | TupleSort (_,fdecl) -> let asts = List.map aof fs in
                                             mk_app z3context fdecl (Array.of_list asts)
                    | s                   -> badtbsort f s
                    with Not_found -> 
                      notbsort f
                   )
               | Ite (cf,tf,ef)              -> mk_ite z3context (aof cf) (aof tf) (aof ef)
               | App (n, fs)                 -> 
                   let ndecl = name_fdecl_cxt <@> n in
                   mk_app z3context ndecl (Array.of_list (List.map aof fs))
               | Bfr           _             
               | Univ          _             
               | Fandw         _             
               | Sofar         _
               | Since         _
               | Cohere        _     
               | Threaded      _     
               (* | Latest        _ *)
                                  ->
                   raise (Invalid_argument ("askZ3.ast_of_formula\n" ^ explain_string_of_formula orig_f ^ "\ncontains " ^ string_of_formula f))
             in
             aof orig_f
           in
           let name_ast_cxt, name_fdecl_cxt = 
             build_ast_cxts [] [(history_function_name,history_fdecl)] types
           in
           let aof = ast_of_formula z3context name_ast_cxt name_fdecl_cxt in
           (* try Josh's tactics ... *)
           let slv = 
             if !z3useqe then
                  Z3.mk_solver_from_tactic z3context (Z3.tactic_and_then z3context (Z3.mk_tactic z3context "qe") (Z3.mk_tactic z3context "smt")) 
             else
               mk_solver z3context
           in
           Z3.solver_set_params z3context slv params;
           z3validate question noisy z3context slv assertions query (List.map aof assertions) (aof query)
       with TypeCheckError s -> BadQuery (query,s)
      )
    ) 
  )
  
let doZ3 question noisy stringfun f assertions =
  push_verbose (noisy || !verbose_z3check) (fun () ->
    let r = z3check_query question stringfun noisy assertions f in
    push_verbose (track_result () || !verbose_z3report) (fun () ->
      if !verbose then
        (match r with
         | Valid     _                  -> 
             Printf.printf "\nValid\n"
         | Invalid   (assertions, f, m) ->
             if question=Tautology then
               Printf.printf "\nInvalid with counter-example\n%s\n" m
             else
               Printf.printf "\nInvalid\n"
         | Undecided (assertions, f, m) -> 
             Printf.printf "\n**Unknown with remark %s\n" m 
         | BadQuery (f, s)              -> 
             Printf.printf "\n**BadQuery %s\n" s
        )
    );
    r
  )

let tautZ3 = doZ3 Tautology

let satZ3 = doZ3 Satisfiable
