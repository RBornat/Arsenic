/* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 */

%{
  open Function
  open Tuple
  open Sourcepos
  open Program
  open Query
  open Com
  open Thread
  open Settings
  open Printer
  open Formula
  open Name
  open Location
  open Assign
  open Intfdesc
  open Report
  open Listutils
  open Knot
  open Stitch
  open Order
  open Node
  
  exception ParserCrash of string
  
  let get_sourcepos() =
    Parsing.symbol_start_pos(), Parsing.symbol_end_pos()

  let fadorn   f = Formula.fadorn (get_sourcepos()) f
  
  let tripletadorn pre lab tof = Com.tripletadorn (get_sourcepos()) pre lab tof
  
  let simplecomadorn ipre c = Com.simplecomadorn (get_sourcepos()) ipre c
  
  let structsimplecomadorn c = Com.structsimplecomadorn (get_sourcepos()) c
  
  let intfadorn   i = Intfdesc.intfadorn (get_sourcepos()) i
  
  let stitchadorn o n a = Stitch.stitchadorn (get_sourcepos()) o n a
  
  let knotadorn k = Knot.knotadorn (get_sourcepos()) k  
  
  let bad s = raise (Program.ParseError(get_sourcepos(),s))
  
  let warn s = report (Warning (get_sourcepos(), s))
  
  let pureness_allows ok_auxreg ok_logc =
    let logc_allowed = if ok_logc then ["logical constants"] else [] in
    let reg_allowed = if ok_auxreg then "registers" else "non-auxiliary registers" in
    let allowed = reg_allowed::"numbers"::"booleans"::logc_allowed in
    phrase_of_list id ", " " and " allowed
    
  let check_pureness ok_auxreg ok_logc formula = 
    let ok_r r = ok_auxreg || is_realreg r in
    let rec cp (badfs,set) f = match f.fnode with
      | Flogc n            -> if not (ok_logc) 
                              then Some (badfs,addname n set) 
                              else None
      | Freg  r            -> if not (ok_r r) 
                              then Some (badfs,addname r set)
                              else None
      | Fvar  (None,NoHook,v) -> Some (badfs, addname v set)
      | Fvar       _ 
      | Ite        _
      | Binder     _   
      | Since      _   
      | Bfr        _      
      | Univ       _      
      (* | Latest     _     *) 
      | Cohere     _     
      | Threaded   _       -> Some (f::badfs, set)
      | _                  -> None
    in
    let badfs, badns = Formula.fold cp ([], NameSet.empty) formula in
    if null badfs && NameSet.is_empty badns then formula else
      let logcs, vars, auxregs = NameSet.filter is_logc badns,
                                 NameSet.filter is_anyvar badns,
                                 NameSet.filter is_auxreg badns
      in
      let description = phrase_of_list id ", " " and " 
                          (List.filter (not <.> Stringutils.is_empty)
                             [prefixed_phrase_of_list string_of_formula "subformula" "subformulas" badfs;
                              prefixed_phrase_of_list string_of_name "logical constant" "logical constants"
                                 (NameSet.elements logcs);
                              prefixed_phrase_of_list string_of_name "variable" "variables"
                                 (NameSet.elements vars);
                              prefixed_phrase_of_list string_of_name "auxiliary register" "auxiliary registers"
                                 (NameSet.elements auxregs)])
      in
        raise (Program.ParseError (formula.fpos,
                           "formula " ^ string_of_formula formula ^ 
                           " should be a pure combination of " ^ 
                           pureness_allows (not (NameSet.is_empty auxregs)) ok_logc ^
                           ", but contains " ^ description))

  let check_realpure = check_pureness false
  let check_anypure  = check_pureness true
  
  let find_pmscs =
    Formula.fold (fun ns f -> match f.fnode with 
                              | Flogc n when is_pmsc n -> Some (n::ns)
                              | _                      -> None
                 ) 
                 []
                 
  let check_assertion pmsc_allowed assertion = 
    let badnames = if pmsc_allowed then [] else find_pmscs assertion in 
    if null badnames then assertion else
      bad ("assertion " ^ string_of_formula assertion ^ " contains " ^
           standard_phrase_of_list id 
             [prefixed_phrase_of_list string_of_name 
                                      "pms-register name" 
                                      "pms-register names" 
                                      badnames
             ]
          )
             
  let check_given assertion =
    let fvs = Formula.frees assertion in
    let fvs = NameSet.filter (not <.> is_logc) fvs in
    if NameSet.is_empty fvs then assertion else
      bad(Printf.sprintf "assertion contains non-logical-constant %s"
                         (prefixed_phrase_of_list string_of_name
                                                  "name"
                                                  "names"
                                                  (NameSet.elements fvs)
                         )
         )
  
  let check_varlist ns string_of_result result =
    match List.filter (not <.> is_anyvar) ns with
    | []     -> result
    | unvars -> bad (phrase_of_list string_of_name ", " " and " unvars ^
                     " should be variables in " ^ 
                     string_of_result result)
  
  (* filtering variables *)
  let classify_var n =
        if is_anyreg n || is_anyvar n || is_parsedlogc n || is_pmsc n then _Fname n else
                bad ("Parser crash: " ^ string_of_name n ^ " can't be classified as register, variable or logical constant")

  (* filtering assigns -- parsed as lhs list := formula list, where each lhs is a
     list of Assign.location. All lists are non-empty -- see loclist and formulas entries in parser
   *)
  let classify_assign ok_logc is_com (lefts (*,assignop *), rights) =
    let string_of_lhs = function
      | [a] -> string_of_location a
      | lhs -> "(" ^ string_of_list string_of_location "," lhs ^ ")"
    in
    let assign () = "assignment " ^ 
                    string_of_list string_of_lhs "," lefts ^
                    ":=" (*(string_of_assignop assignop)*) ^
                    string_of_list string_of_formula "," rights
    in
    let bad_interferenceform () = 
      bad (assign() ^ " in interference description: only location[,location]*:=formula[,formula]* assignments are allowed")
    in
    let isreg_lhs lhs = 
      match lhs with 
      | VarLoc r -> Name.is_anyreg r
    in
    let isvar_lhs = Name.is_anyvar <.> locv
    in
    let isloc_actually f =
      match f.fnode with
      | Fvar _                      -> true
      | _                           -> false
    in
    let ispmsc_lhs = Name.is_pmsc <.> locv
    in
    let is_lhs isf = List.for_all isf in
    let is_singleton = function
      | [_] -> true
      | _   -> false
    in
    (* check no repetitions on lhs *)
    if not (nodups (=) (List.concat lefts)) then
      bad ("some of the lhs elements are repeated") 
    ;
    (* first split: registers or vars on lhs? *)
    if List.for_all (List.for_all isreg_lhs) lefts then
      (if not is_com then bad_interferenceform();
       (* second split: all vars on rhs? *)
       match List.partition isloc_actually rights with
       | rights  , [] ->
           (* no pmscs on the right *) (* surely no pmscs anywhere? *)
           let pmscs = List.filter (Formula.exists Formula.is_pmsc) rights in
           if not (Listutils.null pmscs) then
             bad ("assignment reads from " ^ 
                  prefixed_phrase_of_list string_of_formula "fake variable" "fake variables" pmscs
                 )
           ;
           (* we can have multi-singletons on left, singleton on right *)
           let lefts = 
             match List.for_all is_singleton lefts, rights with
             | true , [e] -> [List.concat lefts]
             | _          -> lefts
           in
           (* do lhs and rhs lengths match? *)
           if List.length lefts <> List.length rights then
             bad ("unbalanced assignment: " ^ " lhs has " ^ 
                  string_of_int (List.length lefts) ^ " components; rhs has " ^
                  string_of_int (List.length rights)
                 )
           ;
           (* convert rhs formulas to locs *)
           let loc_rhs e =
             match e.fnode with
             | Fvar (None,NoHook,v) -> VarLoc v
             | Fvar _            -> bad ("temporal variable " ^ string_of_formula e ^ " on rhs of assignment")
             | _                 -> raise (Invalid_argument ("loc_rhs " ^ string_of_formula e))
           in
           let rights = List.map loc_rhs rights in
           let rslocs = List.combine (List.map (List.map locv) lefts) rights in
           let check_single is_first (rs,loc) = 
             (* first lhs can have a realreg in first position *)
             if not is_first && Name.is_realreg (List.hd rs) then 
               bad ("only first left-hand element may name an actual (non-auxiliary) register");
             (* if realreg first, rhs must be real *)
             if Name.is_realreg (List.hd rs) then
               (match loc with
                | VarLoc v -> 
                    if Name.is_auxvar v then
                      bad ("cannot assign value from auxiliary variable " ^ string_of_var v ^
                           " to " ^ prefixed_phrase_of_list string_of_reg "actual register" "actual registers" rs
                          )
               )
           in
           check_single true (List.hd rslocs);
           List.iter (check_single false) (List.tl rslocs);
           (* that's it, I think *)
           (* let b = 
                match assignop, rslocs with
                | LocalAssign     , _       -> false
                | LoadReserve     , [_,loc] -> if is_auxloc loc then bad "auxiliary load_reserved" else true
                | LoadReserve     , _       -> bad ("multi-location load_reserved " ^ string_of_assignop assignop ^
                                                    " register assignment"
                                                   )
                | StoreConditional, _       -> bad ("store-conditional operator " ^ string_of_assignop assignop ^
                                                    " used in register assignment"
                                                   )
              in
            *)
           RsbecomeLocs ((* b, *) rslocs)
       | []  , rights ->
           ((* it had better be a single-register assignment *)
            match lefts, rights (*, assignop *) with
            | [[loc]], [e] (*, LocalAssign *)     -> RbecomesE (locv loc,e)
            (* | [[loc]], [e], StoreConditional -> 
                       bad ("store-conditional operator " ^ string_of_assignop assignop ^
                            " used in register assignment"
                           )
               | _, _, LoadReserve                   ->
                       bad ("load_reserved operator " ^ string_of_assignop assignop ^
                            " used in register assignment with non-store rhs"
                           )
             *)
            | _            ->
                bad ("register:=formula assignment must have one register, one formula")
           )
       | vars, others -> 
           bad ("register-assignment rhs must be all locations or all formulas: " ^
                standard_phrase_of_list string_of_formula vars ^
                ncase_of (fun _ -> "")
                         (fun _ -> " is a location")
                         (fun _ -> " are locations")
                         vars ^
                "; and " ^
                standard_phrase_of_list string_of_formula others ^
                ncase_of (fun _ -> "")
                         (fun _ -> " is a formula.")
                         (fun _ -> " are formulas.")
                         others
               )
      )
    else
    if List.for_all (List.for_all isvar_lhs) lefts then
      ((* and they must all be singletons *)
       let multiples = List.filter (function [a] -> false | _ -> true) lefts in
       if not (Listutils.null multiples) then
         bad ("invalid multi-location left-hand " ^
              prefixed_phrase_of_list string_of_lhs "side" "sides" multiples
             )
       ;
       let lefts = List.concat lefts in
       (* Can't assign to pmsc names *)
       let pmscs, _ = List.partition ispmsc_lhs lefts in
       if not (Listutils.null pmscs) then
         bad ("assignment to " ^ prefixed_phrase_of_list string_of_location "fake variable" "fake variables" pmscs)
       ;
       (* Sort out single assignments *)
       let rights = match lefts with
                    | [l] -> [singleton_or_tuple rights]
                    | _   -> rights
       in
       (* do lhs and rhs lengths match? *)
       if List.length lefts <> List.length rights then
         bad ("unbalanced assignment: " ^ " lhs has " ^ 
              string_of_int (List.length lefts) ^ " components; rhs has " ^
              string_of_int (List.length rights)
             )
       ;
       let loces = List.combine lefts rights in
       let check_single is_first (loc,e) =
         (* first can be real assignment; others must be auxiliary *)
         if not is_first && not (is_auxloc loc) then
           bad ("non-auxiliary location " ^ string_of_location loc ^ " can only be assigned as \
                 first component of multiple assignment");
         (* if the left is real location and the right is a tuple, first tuple element must be real *)
         (match is_auxloc loc, e.fnode with
          | true, Tuple (f::fs) ->
              ignore (check_realpure ok_logc f);
              List.iter (ignore <.> check_anypure ok_logc) fs
          | true, _ ->
              ignore (check_realpure ok_logc e)
          | false, _ ->
              ignore (check_anypure ok_logc e)
         )
       in
       check_single true (List.hd loces);
       List.iter (check_single false) (List.tl loces);
       (* and that seems to be it *)
       (* let b =
            match loces, is_com, assignop with
            | _      , _    , LocalAssign      -> false
            | [loc,e], true , StoreConditional -> if is_auxloc loc then bad "auxiliary store-conditional"
                                                  else true
            | _      , true , StoreConditional -> bad ("store-conditional operator " ^ string_of_assignop assignop ^
                                                       " used in multi-location assignment"
                                                      ) 
            | _      , false, StoreConditional -> bad ("store-conditional operator " ^ string_of_assignop assignop ^
                                                       " used in interference assignment"
                                                      )
            | _      , _    , LoadReserve      -> bad ("load_reserved operator " ^ string_of_assignop assignop ^
                                                       " used in location assignment"
                                                      )
          in
        *)
       LocbecomesEs ((* b, *) loces)
      )
    else
      (let regs, others = List.partition (is_lhs isreg_lhs) lefts in
       let vars, others = List.partition (is_lhs isvar_lhs) others in
       bad ("unclassifiable assignment " ^ assign() ^ ": lhs must be all registers or \
            all locations: this assigns to " ^
            standard_phrase_of_list id
              (List.filter (not <.> Stringutils.is_empty)
                 [prefixed_phrase_of_list string_of_lhs "register" "registers" regs;
                  prefixed_phrase_of_list string_of_lhs "location" "locations" vars;
                  prefixed_phrase_of_list string_of_lhs "non-reg/non-location" "non-regs/non-locs" others
                 ]
              )
           )
      )
       
  let check_intf_assign assign = 
    classify_assign true false assign 
   
  (* let check_conditional_assign assign =
       match classify_assign true true assign with
       | LocbecomesEs (true,_) (*as a*) -> bad "store-conditional not supported. Sorry." (*; a*)
       | _                              -> bad ("conditional assignment must be store-conditional")
   *)
    
  let rec makebinder bindf locnames f = 
    match locnames with
    | [] -> f (* we can't actually parse an empty locname list, so this is just for recursion *)
    | (loc,n)::locnames -> let f = makebinder bindf locnames f in
                           Formula.fadorn (spos_of_sposspos loc f.fpos) (bindf n f)
                           
  let no_hats pl f =
    match pl with 
    | None -> f
    | _    -> bad ("can't apply " ^ string_of_pl pl ^ " to (" ^ string_of_formula f ^ ")")


  let tcep_apply pl wh f =
    let wrong s =
      bad ("can't apply " ^ s ^ " to (" ^ string_of_formula f ^ ")")
    in
    match f.fnode with
    | Fvar  (None,NoHook,v)  -> {f with fnode=Fvar (pl,wh,v)}
    | Since (NoHook,f1,f2)   -> no_hats pl {f with fnode=Since(wh,f1,f2)}
    | Bfr   (NoHook,bf)      -> no_hats pl {f with fnode=Bfr(wh,bf)}
    | Univ  (NoHook,uf)      -> no_hats pl {f with fnode=Univ(wh,uf)}
    | _                      -> (match pl,wh with
                                 | None, NoHook -> f
                                 | _            -> wrong (string_of_pl pl ^ string_of_wh wh)
                                )
      
  let check_knot knot =
    let badknot () = bad (Knot.alt_token ^ "may only appear at top level of a knot") in
    let rec ckn knot =
      match knot.knotnode with
    | SimpleKnot   _  -> ()
    | KnotOr  (k1,k2)
    | KnotAnd (k1,k2) -> List.iter ckn [k1;k2]
    | KnotAlt (k1,k2) -> badknot ()
    in
    match knot.knotnode with
    | SimpleKnot   _  -> knot
    | KnotOr  (k1,k2)
    | KnotAnd (k1,k2)
    | KnotAlt (k1,k2) -> List.iter ckn [k1;k2]; knot

  let classify_prog_headers hs = 
    let asserts = 
      List.fold_left 
        (fun asserts -> function AssertHdr (l,a) -> (l,a)::asserts | _ -> asserts) 
        []
        hs
    in
    let givens = 
      List.fold_left 
        (fun gs -> function GivenHdr g -> g::gs | _ -> gs) 
        []
        hs
    in
    let aopt = match asserts with
               | []  -> None
               | [a] -> Some a
               | _   -> bad ("multiple initial assertions")
    in
    let gopt = match givens with
      | [] -> None
      | _  -> Some (conjoin (List.rev givens))
    in
    aopt, gopt
                
  let classify_thread_headers hs = 
    let guars = 
      List.fold_left 
        (fun guars -> function GuarHdr g -> g::guars | _ -> guars) 
        []
        hs
    in
    match guars with
      | []  -> GuarHdr []::hs, []
      | [g] -> hs, g
      | _   -> bad ("multiple guarantees")
   
  let classify_thread_trailers ts = 
    let relies = 
      List.fold_left 
        (fun relies -> function RelyHdr r -> r::relies | _ -> relies) 
        []
        ts
    in
    match relies with
      | []  -> None
      | _   -> Some (List.concat (List.rev relies))
   
  (* handle macros *)
  let macros = ref (NameMap.empty : (name list * formula) NameMap.t)
  let tmacros = ref (NameMap.empty : (name list * thread) NameMap.t)
  let prog_macros = ref NameMap.empty
  let first_thread = ref true
  
  let prog_start() = 
    macros := NameMap.empty; 
    first_thread := true
    
  let thread_start() =
    if !first_thread then
      prog_macros := !macros
    else
      macros := !prog_macros

  let add_macro name params formula =
    macros := NameMap.add name (params, formula) !macros
  
  let macro_expand name argopt =
    try Some (let params,f = NameMap.find name !macros in
              let args =
                match argopt with
                | None      -> []
                | Some args -> args
              in
              try 
                let assoc = List.combine params args in
                if !Settings.expand_macros then 
                  reloc (get_sourcepos()) (Formula.substitute assoc f)
                else 
                  match argopt with 
                  | None      -> fadorn (Flogc name)
                  | Some args -> reloc (get_sourcepos()) (fadorn (App (name,args)))
              with Invalid_argument _ -> 
                        bad (Printf.sprintf "macro %s expects %s"
                                  name
                                  (let n = List.length params in
                                   if n=1 then "1 argument" else
                                     Printf.sprintf "%d arguments" n
                                  )
                            )
             )
    with Not_found -> None

  let add_tmacro name params thread =
    tmacros := NameMap.add name (params, thread) !tmacros   
    
  let check_t_postopt knot =
    match knot.knotnode with
    | KnotAlt _ -> bad "thread postcondition knot can't be an ordered disjunction"
    | _         -> ()

  type conditionthing =
    | CTAssign of Location.location list list (* * Assign.assignop *) * Formula.formula list
    | CTExpr   of formula
%}

%token LPAR RPAR

%token <string> INT
%token <string> NAME 
%token <string> PMSREG

%token THREADSEP

%token SEMICOLON
%token IF THEN ELSE FI /* ASSUME */
%token WHILE DO OD UNTIL
%token SKIP ASSERT

%token BECOMES LOADRESERVE STORECONDITIONAL

/* arith operators */
%token PLUS MINUS TIMES DIV MOD
/* comparison operators */
%token LESS LESSEQUAL EQUAL NOTEQUAL GREATEREQUAL GREATER
/* logical operators */
%token IMPLIES IFF AND OR NOT EXISTS FORALL
%token HAT DHAT TILDE DTILDE

%left COMMA
/* %nonassoc AT */
%right SINCE
%nonassoc IFF
%right IMPLIES
%left OR
%left AND
%nonassoc LESS LESSEQUAL EQUAL NOTEQUAL GREATEREQUAL GREATER
%left PLUS MINUS
%left TIMES DIV MOD

%token SOFAR OUAT COHERE COHEREVAR FANDW /* SITF */ LATEST
%token BFR UNIV SINCE

%token TRUE FALSE /* TOP TOPRELY BACKSLASH */

%token COMMA DOT
%token LBRACE RBRACE SQBRA SQKET LSBRACE RSBRACE LSSQBRA RSSQBRA
/* %token ANDANGEL ORDEMON */
%token LO BO UO GO
%token ORLOOP

%token COLON BAR EOP QUERY

%token GUARANTEE /* INTERNAL*/  GIVEN MACRO TMACRO RELY

%token Q_ASSERT Q_AGAINST Q_SP Q_SAT

%start program             /* Entry point */
%start justaformula        /* Entry point */
%start queries             /* Entry point */

%type  <Program.program> program
%type  <Formula.formula> justaformula
%type  <Query.query list> queries

%%
program:
  | progstart proghdrs threadsep threads          
                                        { let preopt, givopt = classify_prog_headers $2 in
                                          let ts, postopt = $4 in
                                         { p_preopt = preopt; p_givopt = givopt; p_hdrs = $2;
                                           p_ts = ts; p_postopt = postopt
                                         }
                                        }

progstart:
  |                                     { prog_start() }

threadsep:
  | THREADSEP                           { thread_start() }
  
proghdrs:
  | initassert proghdrs                 { let l,a = $1 in AssertHdr (l,a) :: $2 }
  | given proghdrs                      { GivenHdr $1 :: $2 }
  | macro proghdrs                      { let m,ps,f = $1 in MacroHdr (m,ps,f) :: $2 }
  | tmacro proghdrs                     { let m,ps,t = $1 in TMacroHdr (m,ps,t) :: $2 }
  |                                     { [] }

initassert: 
  | labelled_assert                     {let lab, assertion = $1 in
                                         lab,check_assertion false assertion
                                        }

labelled_assert:  
  | LBRACE loclabel COLON formula RBRACE    
                                        { $2, $4 }

given:
  | GIVEN LBRACE formula RBRACE         { check_given $3 }

macro:
  | MACRO name EQUAL formula            { add_macro $2 [] $4; ($2,[],$4) }
  | MACRO name LPAR namelist RPAR EQUAL formula                 
                                        { add_macro $2 $4 $7; ($2,$4,$7) }
tmacro:
  | TMACRO name EQUAL thread            { add_tmacro $2 [] $4; ($2,[],$4) }
  | TMACRO name LPAR namelist RPAR EQUAL thread                 
                                        { add_tmacro $2 $4 $7; ($2,$4,$7) }
threads:
  | thread threadsep omegaopt EOP       {[$1],$3}
  | thread EOP                          {[$1],None}
  | thread threadsep threads            {match $3 with ts,postopt -> $1::ts,postopt}

omegaopt:
  | labelled_assert                     { let lab, f = $1 in Some (lab,check_assertion true f) }
  |                                     { None }

thread:
    threadhdrs seq t_postopt threadtrlrs 
                                        { let hdrs,guar = classify_thread_headers $1 in
                                          let relyopt = classify_thread_trailers $4 in
                                          {t_pos=get_sourcepos(); 
                                           t_guar=guar; t_body=Threadseq $2; t_postopt=$3; t_relyopt=relyopt;
                                           t_hdrs=hdrs; t_trlrs=$4
                                          } 
                                        }
  | threadhdrs LBRACE formula RBRACE       
                                        { let hdrs,guar = classify_thread_headers $1 in
                                          {t_pos=get_sourcepos(); t_guar=guar; t_hdrs=hdrs; 
                                           t_body=Threadfinal (check_assertion true $3); 
                                           t_postopt=None; t_relyopt=None; t_trlrs=[]
                                          }
                                        }

threadhdrs:
  | macro threadhdrs                    { let m,ps,f = $1 in MacroHdr (m,ps,f) :: $2 }
  | guarantee threadhdrs                { GuarHdr $1 :: $2 }
  |                                     { [] }

threadtrlrs:
  | macro threadtrlrs                   { let m,ps,f = $1 in MacroHdr (m,ps,f) :: $2 }
  | rely threadtrlrs                    { RelyHdr $1 :: $2 }
  |                                     { [] }

guarantee:
  | GUARANTEE SQBRA interferes SQKET      {$3}
  | GUARANTEE SQBRA            SQKET      {[]}

t_postopt:
  | knot                                { check_t_postopt $1; Some $1 }
  |                                     { None }
  
rely:
  | RELY SQBRA interferes SQKET         {$3}
  | RELY SQBRA        SQKET             {[]}
  
seq:
  | com                                 {[$1]}
  | com SEMICOLON seq                   {$1::$3}
  |                                     {[]}

com:
  | comtriplet                          { Com $1}
  | structcom                           { Structcom $1}

comtriplet:
  | preknot ipreopt loclabel COLON scomnode          
                                        { let ok () = tripletadorn $1 $3 (simplecomadorn $2 $5) in
                                          match $2, $5 with
                                          | Some _, Assign a
                                             when Assign.is_var_assign a -> ok()
                                          | None  , _                    -> ok()
                                          | _                            ->
                                              bad (string_of_scomnode $5 ^
                                                   " cannot cause external interference, so \
                                                    cannot have an interference precondition"
                                                  )
                                        }

preknot:
  | knot                                {$1}
  |                                     {knotadorn (SimpleKnot [])}

ipreopt:
  | LSSQBRA formula RSSQBRA             { Some ((* IpreSimple *) (check_assertion false $2)) }
  /* | LSSQBRA QUERY formula RSSQBRA       { Some (IpreRes (check_assertion false $3)) }
     | LSSQBRA formula SEMICOLON QUERY formula RSSQBRA 
                                           { Some (IpreDouble (check_assertion false $2, 
                                                               check_assertion false $5
                                                              )
                                                  ) 
                                           }
     | LSSQBRA QUERY formula SEMICOLON formula RSSQBRA 
                                           { Some (IpreDouble (check_assertion false $5, 
                                                               check_assertion false $3
                                                              )
                                                  ) 
                                           }
   */
  |                                     { None }

knot:
  | LSBRACE stitchlist RSBRACE          { knotadorn  (SimpleKnot $2)                  }
  | knot OR knot                        { check_knot (knotadorn (KnotOr     ($1,$3))) }  /* left-recursive, I hope */
  | knot AND knot                       { check_knot (knotadorn (KnotAnd    ($1,$3))) }  /* left-recursive, I hope */
  | knot ORLOOP knot                    { check_knot (knotadorn (KnotAlt    ($1,$3))) }  
  | LPAR knot RPAR                      { $2 }

stitchlist:
  | stitch                              {[$1]}
  | stitch SEMICOLON stitchlist         {$1::$3}
  |                                     {[]}

stitch:
  /* | order node stitchlocopt stitchspopt COLON formula            
                                        { stitchadorn $1 $2 $3 $4 (check_assertion false $6) }
   */
  | order node COLON formula            
                                        { stitchadorn $1 $2 (check_assertion false $4) }

/* stitchlocopt:
     | QUERY location                      { Some ($2) }
     |                                     { None }
  
   stitchspopt:
     | LBRACE formula RBRACE               { Some (SpostSimple (check_assertion false $2)) }
     | LBRACE QUERY formula RBRACE         { Some (SpostRes (check_assertion false $3)) }
     | LBRACE formula SEMICOLON QUERY formula RBRACE 
                                           { Some (SpostDouble (check_assertion false $2, 
                                                                check_assertion false $5
                                                               )
                                                  ) 
                                           }
     | LBRACE QUERY formula SEMICOLON formula RBRACE 
                                           { Some (SpostDouble (check_assertion false $5, 
                                                                check_assertion false $3
                                                               )
                                                  ) 
                                           }
     |                                     { None }
 */
 
node:
  | label                               { Cnode $1 }
  | label LPAR name RPAR                { CEnode ($1,
                                                  match $3 with
                                                  | "t" -> true
                                                  | "f" -> false
                                                  | _   -> bad (Printf.sprintf "%s should be t or f in %s(%s)"
                                                                        $3 $1 $3
                                                               )
                                                 )
                                        }
                                        
loclabel:
  | label                               { {labspos=get_sourcepos(); lablab=$1} }

label:
  | NAME                                { $1 }
  
order:
  | LO                                  {Lo}
  | BO                                  {Bo}
  | UO                                  {Uo}
  | GO                                  {Go}
  
scomnode:
  | SKIP                                { Skip                                   }
  | ASSERT formula                      { Assert (check_assertion false $2)      }
  | assign                              { let a = classify_assign true true $1 in
                                          (* if Assign.is_storeconditional a then
                                               report (Error (get_sourcepos(),
                                                              "store-conditional as command, not control condition"
                                                             )
                                                      );
                                           *)
                                          Assign a
                                        }
 
 hatting:
   | HAT                                { Hat }
   | DHAT                               { DHat }
   | TILDE                              { Tilde }
   | DTILDE                             { DTilde }
   
/* for some reason this doesn't work if I use place and time or even tcep */
fname:
  | LPAR MINUS RPAR NAME                { if NameMap.mem $4 !macros then
                                            bad ("macro_expand name " ^ string_of_name $4 ^ " follows (-)")
                                          else
                                          if is_anyvar $4 then fadorn (Fvar (None,Hook,$4)) 
                                          else
                                            bad (string_of_name $4 ^
                                                 " should be variable in order to follow (-)"
                                                )
                                        }
  | LPAR hatting RPAR NAME                  { if NameMap.mem $4 !macros then
                                            bad ("macro_expand name " ^ string_of_name $4 ^ " follows (^)")
                                          else
                                          if is_anyvar $4 then fadorn (Fvar (Some $2,NoHook,$4)) else
                                            bad (string_of_name $4 ^
                                                 " should be variable in order to follow (^)"
                                                )
                                        }
  | LPAR MINUS RPAR
    LPAR hatting RPAR
    NAME                                { bad ($7 ^ " can't be both (^) and (-)") }
  | LPAR hatting RPAR
    LPAR MINUS RPAR
    NAME                                { bad ($7 ^ " can't be both (^) and (-)") }
  | NAME                                { match macro_expand $1 None with
                                          | None   -> fadorn (classify_var $1)
                                          | Some f -> f
                                        }
  | PMSREG                              { fadorn (classify_var $1) }

place:
  | LPAR hatting RPAR                   {if !Settings.allow_tcep then Some $2
                                         else bad "hatting not allowed in assertions or formulae"
                                        }
  |                                     {None}
  
time:
  | LPAR MINUS RPAR                     {if !Settings.allow_tcep then Hook
                                         else bad "(-) not allowed in assertions or formulae"
                                        }
  |                                     {NoHook}
  
tcep:
  | LPAR hatting RPAR LPAR MINUS RPAR       {bad (if !Settings.allow_tcep then 
                                                "cannot have both hatting and (-) prefixes"
                                              else 
                                                "hatting and (-) not allowed in assertions or formulae"
                                             )
                                        }
  | LPAR MINUS RPAR LPAR hatting RPAR       {bad (if !Settings.allow_tcep then 
                                                "cannot have both (-) and hatting prefixes"
                                              else 
                                                "(-) and hatting not allowed in assertions or formulae"
                                             )
                                        }
  | LPAR hatting RPAR                       {if !Settings.allow_tcep then Some $2, NoHook
                                         else bad "hatting not allowed in assertions or formulae"
                                        }
  | LPAR MINUS RPAR                     {if !Settings.allow_tcep then None, Hook
                                         else bad "(-) not allowed in assertions or formulae"
                                        }
  |                                     {None, NoHook}
  
assign:
  | lhss BECOMES formulas               {$1 (*,LocalAssign *),$3}
  /* | lhss LOADRESERVE formulas           {bad "load-reserve not supported. Sorry"(*; $1,LoadReserve,$3*)}
     | lhss STORECONDITIONAL formulas      {bad "store-conditional not supported. Sorry"(*; $1,StoreConditional,$3*)}
   */
  
lhss:
  | lhs                                 {[$1]}
  | lhs COMMA lhss                      {$1::$3}
  
lhs:
  | location                            {[$1]}
  | LPAR loclist RPAR                   {$2}

location:
  | name                                {VarLoc $1}

loclist:
  | location                            {[$1]}
  | location COMMA loclist              {$1::$3}
  
formulas:  
  | formula                             {[$1]}
  | formula COMMA formulas              {$1::$3}

formulalist:
  | formulas                            {$1}
  |                                     {[]}
  
structcom:
  | IF condition THEN seq ELSE seq FI   {structsimplecomadorn(If ($2,$4,$6))}
  | IF condition THEN seq FI            {structsimplecomadorn(If ($2,$4,[]))}
  | WHILE condition DO seq OD           {structsimplecomadorn(While ($2,$4))}
  | DO seq UNTIL condition              {structsimplecomadorn(DoUntil ($2,$4))}

condition:
  | preknot ipreopt loclabel COLON conditionthing       
                                        { match $5 with
                                          | CTAssign (locs (*, op *), es) ->
                                              (* let assign = check_conditional_assign (locs, op, es) in *)
                                              let assign = classify_assign true true (locs, es) in
                                              if Assign.is_reg_assign assign && $2!=None then
                                                bad "register assign with interference precondition";
                                              let scomnode = simplecomadorn $2 (Assign assign) in
                                              CAssign (tripletadorn $1 $3 scomnode) 
                                          | CTExpr e ->
                                              if $2=None then 
                                                CExpr (tripletadorn $1 $3 e)
                                              else bad "control expression with an interference precondition"
                                        }

conditionthing:
  | assign                              { let (locs (*, op *), es) = $1 in CTAssign (locs (*, op *), es) }
  | formula                             { CTExpr $1 }
  
primary:
  | INT                                 {fadorn(Fint $1)}
  | TRUE                                {fadorn(Fbool true)}
  | FALSE                               {fadorn(Fbool false)}
  | fname                               {$1} /* may actually be a macro_expand name, so expansion and adornment happens in fname */
  | LPAR formula RPAR                   {$2}
  | MINUS primary                       {fadorn(Negarith($2))} 
  | NOT primary                         {fadorn(Not($2))}
  | tcep SOFAR LPAR formula RPAR        {let pl, wh = $1 in
                                         no_hats pl (fadorn (Sofar (wh, $4)))
                                        }
  | tcep OUAT LPAR formula RPAR         {let pl, wh = $1 in
                                         no_hats pl (fadorn (ouat wh $4).fnode)
                                        }
  | tcep LATEST LPAR latestname RPAR   
                                        { bad "latest not supported (yet, again). Sorry"(*;
                                          let pl, wh = $1 in
                                          fadorn (Latest (pl,wh,$4)) *)
                                        }
/*
  | time USOFAR LPAR formula RPAR      {fadorn (Univ ($1, fadorn (Sofar (NoHook, $4))))}
 */
  
  | COHERE LPAR name COMMA formula COMMA formula RPAR
                                        {if not (is_anyvar $3) then 
                                           bad (string_of_name $3 ^ " should be variable in coherence formula");
                                         fadorn (Cohere ($3, check_anypure true $5, check_anypure true $7))
                                        }
  | COHEREVAR LPAR name RPAR            {if !Settings.allow_tcep then 
                                           fadorn (_App (Formula.coherevar_token) 
                                                        [fadorn (_Fname $3)]
                                                  )
                                         else
                                           bad (Formula.coherevar_token ^ " not allowed in assertions or formulae")
                                        }
/*| SOMEWHERE LPAR formula RPAR         {check_universalisable $3 
                                            (fun s -> Printf.sprintf "cannot apply %s to formula containing %s"
                                                         string_of_SOMEWHERE s); 
                                         fadorn (somewhere $3).fnode
                                        }   
 */
  
  | place LPAR formula RPAR             {tcep_apply $1 NoHook $3}
  | time LPAR formula RPAR              {tcep_apply None $1 $3}
  
/* we're parsing Apps now, but the only use is for macro_expand macros */
  | NAME LPAR formulalist RPAR          { match macro_expand $1 (Some $3) with
                                          | Some f -> f
                                          | None   -> 
                                              bad ("undefined macro " ^ string_of_name $1)
                                        }
  
  | tcep BFR LPAR formula RPAR          {let pl, wh = $1 in
                                         no_hats pl (fadorn (Bfr (wh,$4)))
                                        }
  | time UNIV LPAR formula RPAR        {fadorn (Univ ($1,$4))}
  | time FANDW LPAR formula RPAR       {if !Settings.allow_tcep then fadorn (Fandw ($1,$4))
                                         else bad (Formula.m_Fandw_token ^ " not allowed in assertions or formulas")
                                        }
                                        
  | EXISTS boundnames primary           {makebinder _Exists $2 $3}
  | FORALL boundnames primary           {makebinder _Forall $2 $3}
  
  | IF formula THEN formula ELSE formula FI
                                        {fadorn (Ite ($2,$4,$6))}

latestname:
  | NAME                                { let badname () = bad "name in 'latest' must be simple variable" in
                                          match macro_expand $1 None with
                                          | Some f ->
                                             (match f.fnode with
                                              | Fvar (None, NoHook, v) -> v
                                              | _                   -> badname ()
                                             )
                                         | None   -> 
                                             if is_anyvar $1 then $1
                                             else badname ()
                                        }
compare_op:
  | LESS                                { Less }
  | LESSEQUAL                           { LessEqual }
  | EQUAL                               { Equal }
  | NOTEQUAL                            { NotEqual }
  | GREATEREQUAL                        { GreaterEqual }
  | GREATER                             { Greater }

comparison:
  | formula compare_op formula 
    %prec AND                           { let r = $1,fadorn(Compare($1,$2,$3)) in 
                                          (* Printf.printf "\nrule 1 building %s" 
                                                (bracketed_string_of_pair string_of_formula string_of_formula r); 
                                           *)
                                          r  
                                        }
  | formula compare_op comparison        { let c, right = $3 in
                                          (* Printf.printf "\nrule 2 sees %s" 
                                                (bracketed_string_of_pair string_of_formula string_of_formula $3);
                                           *)
                                          let r =
                                          $1,
                                          fadorn (_And (Formula.fadorn (spos_of_sposspos $1.fpos c.fpos) (Compare($1,$2,c)))
                                                       right
                                                 )
                                          in
                                          (* Printf.printf "\nrule 2 building %s" 
                                                (bracketed_string_of_pair string_of_formula string_of_formula r);
                                           *)
                                          r
                                        }
formula:
  | primary                             {$1}
  
  | formula TIMES formula               {fadorn(Arith($1,Times,$3))}
  | formula DIV formula                 {fadorn(Arith($1,Div,$3))}
  | formula MOD formula                 {fadorn(Arith($1,Mod,$3))}
  | formula PLUS formula                {fadorn(Arith($1,Plus,$3))}
  | formula MINUS formula               {fadorn(Arith($1,Minus,$3))} 

/*
  | formula LESS formula                {fadorn(Compare($1,Less,$3))}
  | formula LESSEQUAL formula           {fadorn(Compare($1,LessEqual,$3))}
  | formula EQUAL formula               {fadorn(Compare($1,Equal,$3))}
  | formula NOTEQUAL formula            {fadorn(Compare($1,NotEqual,$3))}
  | formula GREATEREQUAL formula        {fadorn(Compare($1,GreaterEqual,$3))}
  | formula GREATER formula             {fadorn(Compare($1,Greater,$3))}
 */
 
  | comparison                          { let r = sndof2 $1 in 
                                          (* Printf.printf "\ncomparison built %s" (string_of_formula r); *)
                                          r 
                                        }
  | formula AND formula                 {fadorn(LogArith($1,And,$3))}
  | formula OR formula                  {fadorn(LogArith($1,Or,$3))}
  | formula IFF formula                 {fadorn(LogArith($1,Iff,$3))}
  | formula IMPLIES formula             {fadorn(LogArith($1,Implies,$3))}

  | formula SINCE formula               {fadorn (Since(NoHook,$1,$3))} /* place, time done elsewhere */
  
  | formula COMMA formulas              {fadorn(Tuple($1::$3))}

boundnames:
  | locname                             {[$1]}
  | LPAR locnamelist RPAR               {$2}

name:
  | NAME                                {$1}
  | pmsreg                              {$1}

pmsreg:
  | PMSREG                              {let i,r = pmsc_parts $1 in
                                         if string_of_int (int_of_string i)=i 
                                           then $1
                                           else bad ("pms-register name must start with \
                                                      simple integer: no leading zeroes"
                                                    )
                                        }

/* name plus location */
locname:
  | name                                {get_sourcepos(),$1}
  
locnamelist:
  | locname                             {[$1]}
  | locname COMMA locnamelist           {$1::$3}

namelist:
  | name                                {[$1]}
  | name COMMA namelist                 {$1::$3}
  
interferes:
  | interference                        {[$1]}
  | interference SEMICOLON interferes   {$1::$3}
  |                                     {[]}

interference:
  | idescription                        {let binders, (pre, assign) = $1 in
                                         let assign = check_intf_assign assign in
                                         intfadorn {i_binders  = binders;
                                                    i_pre      = pre;
                                                    i_assign   = assign
                                                   }
                                        }
idescription:
  | ibinders idesc                      {$1,$2}
  
ibinders:
  | SQBRA namelist SQKET DOT            {NameSet.of_list $2}
  |                                     {NameSet.empty}

idesc:
  | formula BAR assign                  {check_assertion false $1, $3}
  
/* *************************************** just a formula *********************************** */

justaformula:
  | formula EOP                         {$1}
  
/* *************************************** queries *********************************** */

query:
  | formula                             {Qtaut $1}
  | Q_SAT formula                        {Qsat $2}
  | Q_ASSERT formula SEMICOLON query     {Qassert ($2,$4)}
  | formula Q_AGAINST interference       {Qstableformula ($1,$3)}
  | interference Q_AGAINST interference  {Qstableintf ($1,$3)}
  | Q_SP LPAR formula SEMICOLON assign RPAR IMPLIES formula
                                        {Qspimplies ($3,classify_assign true true $5, $8)}
                                        
queries:
  | EOP                                 {[]}
  | query EOP                           {[$1]}
  | query SEMICOLON queries             {$1::$3}
    
%%
