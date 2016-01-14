open Function
open Option
open Tuple
open Listutils
open Formula
open Name
open Ftype
open Typecheck

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception Error of string
let starts_with = Stringutils.starts_with

(* bound variables don't get included in global coherence vars. Of course? *)
let get_coherence_vars binders =
  let rec cof binders vset f = 
    match f.fnode with
    | Cohere (v,f1,f2) -> let vset = 
                            if NameSet.mem v binders then vset else addname v vset
                          in
                          Some (List.fold_left (Formula.fold (cof binders)) vset [f1;f2])
    | Binder (bk,n,bf) -> Some (Formula.fold (cof (addname n binders)) vset bf)
    | _                -> None
  in
  Formula.fold (cof binders)

(* we currently have two temporal modalities: B and Univ. They are handled as temporal assertions:
   B(P) means there was a time at which there was a barrier event, since which P held locally; 
   Univ(P) means the same thing but across all threads.
   P since Q means there was a time at which P/\Q and since then P.
   P since Q is exists hi (Q@hi /\ forall hi' (hi<=hi'<=0 => P@hi'))
   B(P) is P since bev
   We don't need to count threads: there is just Here and There, two 'places'. Here is
   the current place; There is at least partly outside it.
   Univ(P) is forall pl (P since bev).
   B(true) and Univ(true) are just true, so we need a bev at the beginning of time, in all timecones.
   Hatting (see stability rules and strongestpost.ml) puts variables, B and Sofar into There.
   Strongest-post substitution affects variables, modalities and 'since', changing Now into Then.
   A variable will never be There and Then; B and Sofar may be.
 *)
 
let valuefn_name = "&v"             (* (vname,place,history index) *)
let latestfn_name = "&latest"       (* (vname,ishatted,history index) *)
let coherencefn_name = "&co"
let coherencevar_name = "&cv"
let vartype_name = "&vtype"

let history_function_name = "&hf"
let history_index_name = "&hi"
let barrier_event_name = "bev&"     (* & on the end cos it's a variable *)
let tid_name = "&tid"

let barrier_event_formula = _recFname barrier_event_name

let rec axstring_of_type t = 
  match t with
  | Bool            -> "Bool"
  | Int             -> "Int"
  | TupleType    ts -> "!Tup" ^ String.concat "" (List.map axstring_of_type ts) ^ "!" 
  | FuncType (ts,t) -> "!Func" ^ String.concat "" (List.map axstring_of_type ts) 
                       ^ axstring_of_type t ^ "!"
  | FTypeVar      _ 
  | VarType       _ -> raise (Invalid_argument ("axstring_of_type " ^ string_of_ftype t))

let typed_name prefix t = 
  let tstring = axstring_of_type t in
  prefix ^ tstring

(* *********************************** simplification ************************************** *)

(* U(since) used to be horrible, and U and B are versions of since. 
   To deal with some of the horrors, we try to simplify them away.
   Now that U does not see through since, sofar and ouat, it all got easier.
 *)

let rec simplify f =
  let pushlogical build mf = 
    (* this was too enthusiastic. Lost proofs. So we don't do it. But we preserve its bones for a while. *)
    None
    (*
       let pushbinop _recOp f1 f2 =
           Some (_recOp (simplify (build f1)) (simplify (build f2)))
       in
       if is_pure mf then Some (simplify mf) else
         (match mf.fnode with
          | LogArith (f1, And    , f2) -> 
              pushbinop _recAnd f1 f2
          | LogArith (f1, Or     , f2) -> 
              if is_pure f1 || is_pure f2 then pushbinop _recOr f1 f2 else None
          | LogArith (f1, Implies, f2) -> 
              if is_pure f1 then pushbinop _recImplies f1 f2 else None
          | Binder (Forall, n, bf)     ->
              Some (_recForall n (simplify (build bf)))
          | _                          -> 
              None
         )
     *)
  in
  let optsimp f = match f.fnode with
    | Univ (wh,uf) -> 
        (match uf.fnode with
         | Univ  (_,uf')     -> Some (simplify (universal wh uf'))
         | Bfr   (_,_,bf)    -> Some (simplify (universal wh bf))
         | Fandw   (_,ef)    -> Some (simplify (universal wh ef))
         | Since (_,_,p,q)   -> 
             Some (simplify (conjoin [universal wh (conjoin [p; ouat Here wh q]); since Here wh p q])) 
         (* | Sofar (_,_,sf)    -> 
             let indivs = individualise sf in
             let history = conjoin (sf :: List.map (sofar Here wh) indivs) in
             Some (simplify (conjoin [universal wh history; sofar Here wh sf])) *)
         | _                 ->
             (* can't see how to do this with Sofar translation above ...
                (match extract_shorthand uf with
                 | Some (_,_,n,ouf) when n=m_ouat_token
                                -> Some (simplify (ouat Here wh ouf))
                 | _            -> 
              *)
                  pushlogical (_recUniv wh) uf 
                  |~~ (fun () ->
                          Some (simplify (since Here wh (simplify (fandw Now uf)) barrier_event_formula))
                       )
            (* ) *)
        )
    | Bfr (pl,wh,bf) -> 
        (* because we prohibit Bfr formulae with coincidences, and we don't construct them
           automatically, we don't need to do what we do with _U(since) and _U(sofar) above.
         *)
        pushlogical (_recBfr pl wh) bf 
        |~~ (fun () ->
                Some (simplify (since pl wh bf barrier_event_formula))
             )
    | Since (pl,wh,f1,f2) ->
        let f1 = simplify f1 in
        let f2 = simplify f2 in
        (match f1.fnode with
         | Since (_,_,sf1,sf2) -> Some (simplify (since pl wh sf1 (conjoin [f1;f2])))
         | Sofar (_,_,sf)      -> Some (simplify (conjoin [sofar pl wh sf; ouat pl wh f2])) 
         | _                   -> None
        )
    | _ -> None
  in
  let r = Formula.map optsimp f in
  (* Printf.printf "\nsimplify %s = %s" (string_of_formula f) (string_of_formula r); *)
  r

and individualise p = (* for inside sofar *)
  let pfrees = NameSet.filter Name.is_anyvar (Formula.frees p) in
  if NameSet.cardinal pfrees<2 then 
    [] (* not even two free variables: we don't need to touch it *)
  else
    List.map (fun v -> bindExists (NameSet.remove v pfrees) p)
             (NameSet.elements pfrees)

let allthreads f =
  conjoin (Array.to_list (Array.init !Thread.threadcount (fun i -> threaded i f)))
  
let ur_event () = 
  let event = ouat Here Now barrier_event_formula in
  allthreads event
  
(* *********************************** embedding ************************************** *)

let addcxt (vtn, t as pair) cxt = if List.mem_assoc vtn cxt then cxt else pair::cxt

(* &x(v,pl,hi) arguments are
     -- variable
     -- thread number      
     -- history index 
     ;
 *)
let embedvariable cxt pl hi v vtype =
  let vtn = typed_name valuefn_name vtype in
  let pair = (vtn, FuncType ([VarType vtype; Int; Int], vtype)) in
  let f = _recApp vtn [_recFname v; pl; hi] in
  addcxt pair cxt, f
  
(* &latest(v,ishatted,hi) arguments are
     -- variable
     -- hatted (only by InflightHat)     
     -- history index 
     ;
 *)
let embedlatest cxt pl hi v vtype =
  let vtn = typed_name latestfn_name vtype in
  let pair = (vtn, FuncType ([VarType vtype; Bool; Int], vtype)) in 
  let f = _recApp vtn [_recFname v; _recFbool (pl=There); hi] in
  addcxt pair cxt, f

(* &co<type>(x,f1,f2) arguments are
     -- variable
     -- f1
     -- f2
 *) 
let embedcoherence cxt v vtype f1 f2 =
  let ctn = typed_name coherencefn_name vtype in
  let pair = (ctn, FuncType ([VarType vtype; vtype; vtype], Bool)) in 
  let f = _recApp ctn [_recFname v; f1; f2] in
  addcxt pair cxt, f

(* for the convenience of askZ3, two convenience functions *)
let is_modalitybinding (v, _) =
  Stringutils.starts_with v valuefn_name ||
  Stringutils.starts_with v latestfn_name ||
  Stringutils.starts_with v coherencefn_name

let extract_coherencetype (v, t) =
  if Stringutils.starts_with v coherencefn_name then
    (match t with
     | FuncType ([VarType vtype; _; _], Bool) -> Some vtype
     | _                                      -> 
         raise 
           (Error 
             (Printf.sprintf "extract_coherencetype %s"
                             (bracketed_string_of_pair string_of_name 
                                                       string_of_ftype
                                                       (v,t)
                             ) 
             )
      )
    )
  else None
  
(* we also need coherence_var (_cv) assertions *)
let coherencevar_assertions frees cvars =
  NameSet.map (fun v -> let app = _recApp Formula.coherevar_token [_recFname v] in
                        if NameSet.mem v cvars then app else negate app
              )
           Function.id
           (NameSet.filter Name.is_anyvar frees)

let cv_coherence v vtype = 
  let ctn = typed_name coherencevar_name vtype in
  (ctn, FuncType ([VarType vtype], Bool)), 
  _recApp ctn [_recFname v]

let embedcoherencevar cxt v vtype =
  let pair, f = cv_coherence v vtype in
  addcxt pair cxt, Some f

type situation = 
  | Amodal 
  | InSince of formula 
  | InBfr of formula 
  | InU of formula
  | InSofar of formula

let embed is_stabq bcxt cxt orig_f = 
  (* is_stabq seems to be redundant with the functional treatment of Latest ... *)
  
  (* I used to be defensive about hatting and hooking (There and Then). Now I'm not. It shouldn't happen that you get There+Then;
     it shouldn't happen that you get There inside There or Then inside Then. But if the first happens I'll ignore it; if the 
     second happens I'll take the outer (which is the same as taking the inner, isn't it? but the code works that way).
   *)

  let rec tsf bounds situation (tn:int) (tidopt:Formula.formula option) (hiopt:Name.name option) (hicurr:Formula.formula) bcxt cxt f = 
    let noisy = !Settings.verbose_modality in
    if noisy then Printf.printf "\ntsf formula is %s" (string_of_formula f);
    let _recFint_of_pl pl =
      match pl with 
      | Here  -> _recFint (string_of_int tn) 
      | There -> _recFint (string_of_int ((tn+1) mod !Thread.threadcount))
      (* | There, false -> _recFint (string_of_int (-1)) (* specially for Latest *) *)
    in
    let formula_of_pl pl = 
      match tidopt with
      | Some tidf -> tidf
      | _         -> _recFint_of_pl pl
    in
    let hi_of_ep wh =
      match wh with Then -> _recFint (string_of_int (-1)) | _ -> hicurr
    in
    let hiformula_of_ep wh =
      either (hi_of_ep wh) (hiopt &~~ (_Some <.> _recFname))
    in
    let bindallthreads tidname bf = 
      let tidf = _recFname tidname in
      let limits =
        _recAnd (_recLessEqual (_recFint "0") tidf)
                (_recLess tidf (_recFint (string_of_int !Thread.threadcount)))
      in
      bindForall (NameSet.singleton tidname) 
                 (_recImplies limits bf)
    in
    let tevw cxt wh ef =
      let tidf = _recFname tid_name in
      let cxt, ef = 
        anyway2 (opttsf bounds (InU ef) tn (Some tidf) hiopt (hiformula_of_ep wh) bcxt) 
                cxt 
                ef 
      in 
      Some (cxt, Some (bindallthreads tid_name ef))
    in
    let temporal_extra bcxt cxt wh p =
      match tidopt with 
      | None -> cxt, _recTrue
      | _    -> anyway2 (opttsf bounds situation tn tidopt hiopt (hiformula_of_ep wh) bcxt) cxt p
    in
    if !Settings.verbose || !Settings.verbose_modality then
      Printf.printf "\nembed f %s" (string_of_formula f); 
    let process_var cxt pl wh v f =
        let tidf = formula_of_pl pl in
        let epf = hiformula_of_ep wh in
        let vtype = if v=barrier_event_name then Bool else bcxt <@@> f in
        embedvariable cxt tidf epf v vtype
    in
    match f.fnode with
    | Fvar (_,_,v) 
       when Stringutils.ends_with v "&new" -> (* x!new isn't really a variable, doesn't have a history *)
        None
    | Fvar (pl,wh,v) ->
        let cxt, vv = process_var cxt pl wh v f in
        Some (cxt, Some vv)
    | Latest (pl,wh,v) -> 
        let epf = hiformula_of_ep wh in
        let vtype = bcxt <@@> f in
        let cxt, f = embedlatest cxt pl epf v vtype in
        Some (cxt, Some f)
    | Flogc s when NameSet.mem s bounds ->
        None
    | Flogc s ->
        (match s with
         | "SCloc"     -> Some (_recFbool !Settings.param_SCloc)
         | "SCreg"     -> Some (_recFbool !Settings.param_SCreg)
         | "LocalSpec" -> Some (_recFbool !Settings.param_LocalSpec)
         | _           -> None
        ) 
        &~~ (fun f -> Some (cxt, Some f))
    | Cohere (v, f1, f2) ->
        let cxt, f1 = anyway2 (opttsf bounds situation tn tidopt hiopt hicurr bcxt) cxt f1 in
        let cxt, f2 = anyway2 (opttsf bounds situation tn tidopt hiopt hicurr bcxt) cxt f2 in
        let cxt, f = embedcoherence cxt v (bcxt <@@> f) f1 f2 in
        Some (cxt, Some f)
    | Since (pl, wh, f1, f2) ->
        (* U does _not_ see through since. So we ignore tidopt, except for extra_f1 *)
        let cxt, extra_f1 = temporal_extra bcxt cxt wh (conjoin [f1; ouat pl wh f2]) in
        let hi = match hiopt with
                 | None    -> history_index_name 
                 | Some hi -> new_name history_index_name 
        in
        let hi_formula = _recFname hi in
        let cxt, f2 = anyway2 (opttsf bounds (InSince f2) tn None (Some hi) hi_formula bcxt) cxt f2 in
        let hi1 = new_name history_index_name in
        let hi1_formula = _recFname hi1 in
        let cxt, f1 = anyway2 (opttsf bounds (InSince f1) tn None (Some hi1) hi1_formula bcxt) cxt f1 in
        let since_assert =
          if !Settings.simpleUBsince then
            ((* This somewhat simpler version -- which doesn't demand a previous state -- is 
                for some reason often 2.5 times slower ... and I honestly can't see why.
              *)
             let cmp_op = match wh with | Now -> _recLessEqual | Then -> _recLess in
             bindExists 
               (NameSet.singleton hi)
               (conjoin 
                  [cmp_op hi_formula hicurr;
                   f2; 
                   bindForall 
                     (NameSet.singleton hi1) 
                     (_recImplies 
                        (conjoin [_recLessEqual hi_formula hi1_formula;
                                  cmp_op hi1_formula hicurr
                                 ]
                        )
                        f1
                     )
                  ]
               )
            )
          else (
            (* treating Sofar like Bfr: think that's right *)
            let cmp_op1, cmp_op2, limit = 
              match situation, wh with 
              | Amodal   , Now 
              | InSince _, Now -> _recLessEqual, _recLessEqual, hicurr 
              | Amodal   , Then 
              | InSince _, Then -> _recLess     , _recLess     , hicurr
              | InBfr _  , Now 
              | InSofar _, Now 
              | InU   _  , Now -> _recLess     , _recLessEqual, hicurr
              | InBfr _  , Then 
              | InSofar _, Then 
              | InU   _  , Then -> _recLess     , _recLess     , (match hicurr.fnode with
                                                                 | Fint "0" -> _recFint "-1"
                                                                 | _        -> _recMinus hicurr (_recFint "1")
                                                                )
            in
            bindExists 
              (NameSet.singleton hi)
              (conjoin 
                 [cmp_op1 hi_formula limit;
                  f2; 
                  bindForall 
                    (NameSet.singleton hi1) 
                    (_recImplies 
                       (conjoin [_recLessEqual hi_formula hi1_formula;
                                 cmp_op2 hi1_formula hicurr
                                ]
                       )
                       f1
                    )
                 ]
              )
          )
        in
        Some (cxt, Some (conjoin [extra_f1; since_assert]))
    | Sofar (pl, wh, sf) ->
        let do_sofar cxt tidopt extra_sf =
          match sf.fnode with
          | Since (Here,Now,{fnode=Fandw(Now,uf)},f2) 
              when f2=barrier_event_formula
                          -> (* Printf.printf "\n** modality.ml got one %s" (string_of_formula f); *)
                             tevw cxt wh (rplacSofar uf Here Now uf)
          | _             ->
              (* same as since, except from the beginning of time *)
              let hi = match hiopt with
                       | None    -> history_index_name 
                       | Some hi -> new_name history_index_name 
              in
              let hi_formula = _recFname hi in
              let cxt, sf = anyway2 (opttsf bounds (InSofar sf) tn tidopt (Some hi) hi_formula bcxt) cxt sf in
              let cmp_op = match wh with | Now -> _recLessEqual | Then -> _recLess in
              let sofar_assertion = 
                bindForall (NameSet.singleton hi) (_recImplies (cmp_op hi_formula hicurr) sf)
              in
              Some (cxt, Some (conjoin [extra_sf; sofar_assertion]))
        in
        (* if it's outside U, or not multivariate, just do it *)
        if tidopt=None ||
           NameSet.cardinal (NameSet.filter Name.is_anyvar (Formula.frees sf)) < 2
        then
          do_sofar cxt tidopt _recTrue
        else
          (* inside U and multivariate *)
          (let cxt, extra_sf = 
             let history = sf :: List.map (sofar Here wh) (individualise sf) in
             let cxt, bcxt = completed_typeassign_formula_list cxt bcxt Bool history in
             temporal_extra bcxt cxt wh (conjoin history) 
           in
           do_sofar cxt None extra_sf
          )
    | Fandw (wh,ef) -> tevw cxt wh ef
    | Binder (fe, v, bf) ->
        let bounds = NameSet.add v bounds in
        let cxt, bf' = anyway2 (opttsf bounds situation tn tidopt hiopt hicurr bcxt)
                               ((v,bcxt<@@>f)::cxt)
                               bf
        in Some (List.remove_assoc v cxt, Some (_recBinder fe v bf'))
    | App (name, [{fnode=Fvar(_,_,v)} as var])
      when name=Formula.coherevar_token ->
        Some (embedcoherencevar cxt v (bcxt <@@> var)) 
    | Threaded (tid, tf) ->
        let cxt, tf' =
          anyway2 (opttsf bounds situation tid tidopt hiopt hicurr bcxt) cxt tf        
        in
        Some (cxt, Some tf')
    | Bfr  _ 
    | Univ _ ->
        raise (Error (Printf.sprintf "Modality.embed: unsimplified %s in %s"
                                     (string_of_formula f)
                                     (string_of_formula orig_f)
                     )
              )
    | _ -> 
        if noisy then Printf.printf " -- ignored";
        None
  and opttsf bounds situation tn tidopt hiopt hicurr bcxt = 
    Formula.optmapfold (tsf bounds situation tn tidopt hiopt hicurr bcxt)
  in
  anyway2 (opttsf NameSet.empty Amodal !Thread.threadnum None None (_recFint "0") bcxt) cxt orig_f

let mfilter = List.filter is_modalitybinding

let embed_axiom types cxt axiom =
  let cfrees = Formula.frees axiom in
  let cvs = List.filter Name.is_anyvar (NameSet.elements cfrees) in
  let handle (modal_cxt, fs) t =
    let vbinders = List.map (fun v -> v,t) cvs in
    let cxt, axbinders = 
      completed_typeassign_formula_list (vbinders @ mfilter cxt) [] Bool [axiom]
    in
    let cxt, axiom = embed false axbinders cxt axiom in
    mfilter cxt, bindForall cfrees axiom::fs
  in
  List.fold_left handle (cxt, []) types 

