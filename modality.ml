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

(* an attempt to define writes(P), the assertion which can be said to be transmitted in 
   interference by B(P) and to other threads by U(P). Idea is to stop assertions claiming
   to transmit coincidences. Inspired by 
        writes(A since B) = writes(A) /\ writes(ouat(B))
 *)

(* I'm not trying too hard to make this efficient. If it works I could memoise it *)

let indivs pfrees _P = (* produce a conjunction of quantified univariate formulae *)
    List.map (fun v -> bindExists (NameSet.remove v pfrees) _P)
             (NameSet.elements pfrees)

let univariate f = NameSet.cardinal (NameSet.filter Name.is_anyvar (Formula.frees f)) < 2

let rec writes _P =
  let bad f = raise (Error (Printf.sprintf "%s: writes(%s) inside %s"
                                                (Sourcepos.string_of_sourcepos _P.fpos)
                                                (string_of_formula f)
                                                (string_of_formula _P)
                           )
                    )
  in
  let getvars f = NameSet.filter Name.is_anyvar (Formula.frees f) in
  let univariate ns = NameSet.cardinal ns < 2 in
  let opt_wrs f =
    match extract_shorthand f with
    | Some (Ouat(NoHook,nf)) ->
        let vs = getvars nf in
        if univariate vs then Some f else
          (match nf.fnode with
           | LogArith (f1,And,f2) ->
               Some (conjoin [ouat NoHook (writes f1); ouat NoHook (writes f2)])
           | _                    -> Some (conjoin (List.map (ouat NoHook) (indivs vs nf)))
          )
    | Some (Ouat _)          -> bad f
    | _                      ->
       match f.fnode with
       | Since (NoHook, af, bf) -> Some (conjoin [writes af; writes (ouat NoHook bf)])
       | Sofar (NoHook, sf)     -> 
           let vs = getvars sf in 
           if univariate vs then Some f
           else
             (match sf.fnode with 
              | LogArith (f1,And,f2) ->
                  Some (conjoin [sofar NoHook (writes f1); sofar NoHook (writes f2)])
              | _                    -> Some sf (* I think it's as simple as that *)
             )
       | Bfr  (NoHook, mf) 
       | Univ (NoHook, mf) -> Some (writes mf)
       (* we don't want these bad forms of temporality *)
       | Since _
       | Sofar _
       | Bfr   _
       | Univ  _ -> bad f
       (* otherwise look at its parts, please *)
       | _       -> if univariate (getvars f) then Some f else None
  in
  Formula.map opt_wrs _P
  
(* we currently have two temporal modalities: B and Univ. They are handled as temporal assertions:
   B(P) means there was a time at which there was a barrier event, since which P held locally; 
   Univ(P) means the same thing but across all threads.
   P since Q means there was a time at which P/\Q and since then P.
   P since Q is exists hi (Q@hi /\ forall hi' (hi<=hi'<=0 => P@hi'))
   B(P) is P since bev
   We don't need to count threads: there is just None and There, two 'places'. None is
   the current place; There is at least partly outside it.
   Univ(P) is forall threads (P since bev).
   B(true) and Univ(true) are just true, so we need a bev at the beginning of time, in all timecones.
   Hatting (see stability rules and strongestpost.ml) puts variables, B and Sofar into There.
   Strongest-post substitution affects variables, modalities and 'since', changing NoHook into Hook.
   A variable will never be There and Hook; B and Sofar may be.
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
   NoHook that U does not see through since, sofar and ouat, it all got easier.
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
    | Univ (hk,uf) -> 
        (match uf.fnode with
         | Univ  (_,uf')     -> Some (simplify (universal hk uf'))
         | Bfr   (_,bf)      -> Some (simplify (universal hk bf))
         | Fandw   (_,ef)    -> Some (simplify (universal hk ef))
         | Since (_,p,q)     -> 
             Some (simplify (conjoin [universal hk (conjoin [p; ouat hk q]); since hk p q])) 
         (* | Sofar (_,sf)    -> 
             let indivs = individualise sf in
             let history = conjoin (sf :: List.map (sofar None hk) indivs) in
             Some (simplify (conjoin [universal hk history; sofar None hk sf])) 
          *)
         |_                   ->
             (* can't see how to do this with Sofar translation above ...
                (match extract_shorthand uf with
                 | Some (_,_,n,ouf) when n=m_ouat_token
                                -> Some (simplify (ouat None hk ouf))
                 | _            -> 
              *)
                  pushlogical (_recUniv hk) uf 
                  |~~ (fun () ->
                          (* this is the 'old' way, which quantifies (fandw) across threads. But then
                             so does the 'new' way below. And at least this one aligns the boundary
                             events, which is a reasonable abstraction. Aligning them properly with
                             the 'new' treatment would be a bit scary. I might attempt it one day.
                           *)
                          Some (simplify (since hk (simplify (fandw NoHook uf)) barrier_event_formula))
                          (* the 'new way
                             Some (fandw hk (simplify (since NoHook uf barrier_event_formula)))
                           *)
                       )
            (* ) *)
        )
    | Bfr (hk,bf) -> 
        (* because we prohibit Bfr formulae with coincidences, and we don't construct them
           automatically, we don't need to do what we do with _U(since) and _U(sofar) above.
         *)
        pushlogical (_recBfr hk) bf 
        |~~ (fun () ->
                Some (simplify (since hk bf barrier_event_formula))
             )
    | Since (hk,f1,f2) ->
        let f1 = simplify f1 in
        let f2 = simplify f2 in
        (match f1.fnode with
         | Since (_,sf1,sf2) -> Some (simplify (since hk sf1 (conjoin [f1;f2])))
         | Sofar (_,sf)      -> Some (simplify (conjoin [sofar hk sf; ouat hk f2])) 
         | _                 -> None
        )
    | _ -> None
  in
  let r = Formula.map optsimp f in
  (* Printf.printf "\nsimplify %s = %s" (string_of_formula f) (string_of_formula r); *)
  r

let allthreads f =
  conjoin (Array.to_list (Array.init !Thread.threadcount (fun i -> threaded i f)))
  
let ur_event () = 
  let event = ouat NoHook barrier_event_formula in
  allthreads event
  
(* *********************************** embedding ************************************** *)

let addcxt (vtn, t as pair) cxt = if List.mem_assoc vtn cxt then cxt else pair::cxt

(* &x(v,ht,hi) arguments are
     -- variable
     -- thread number      
     -- history index 
     ;
 *)
let embedvariable cxt ht hi v vtype =
  let vtn = typed_name valuefn_name vtype in
  let pair = (vtn, FuncType ([VarType vtype; Int; Int], vtype)) in
  let f = _recApp vtn [_recFname v; ht; hi] in
  addcxt pair cxt, f
  
(*
    (* &latest(v,ishatted,hi) arguments are
         -- variable
         -- enhat (only by InflightHat)     
         -- history index 
         ;
     *)
    let embedlatest cxt ht hi v vtype =
      let vtn = typed_name latestfn_name vtype in
      let pair = (vtn, FuncType ([VarType vtype; Bool; Int], vtype)) in 
      let f = _recApp vtn [_recFname v; _recFbool (ht=There); hi] in
      addcxt pair cxt, f
 *)
 
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

let tn_of_hat = function 
  | Hat  | Tilde  -> 1
  | DHat | DTilde -> 2

let embed bcxt cxt orig_f = 
  
  (* I used to be defensive about hatting and hooking (There and Hook). NoHook I'm not. It shouldn't happen that you get There+Hook;
     it shouldn't happen that you get There inside There or Hook inside Hook. But if the first happens I'll ignore it; if the 
     second happens I'll take the outer (which is the same as taking the inner, isn't it? but the code works that way).
   *)

  let rec tsf bounds situation (tn:int) (tidopt:Formula.formula option) (hiopt:Name.name option) (hicurr:Formula.formula) bcxt cxt f = 
    let noisy = !Settings.verbose_modality in
    (* if noisy then Printf.printf "\ntsf formula is %s" (string_of_formula f); *)
    let _recFint_of_pl ht =
      match ht with 
      | None      -> _recFint (string_of_int tn) 
      (* tildes and hats don't occur in the same query *)
      | Some Hat  | Some Tilde  -> _recFint (string_of_int ((tn+1) mod !Thread.threadcount)) (* and should be state -1, really *)
      | Some DHat | Some DTilde -> _recFint (string_of_int ((tn+2) mod !Thread.threadcount)) (* and should be state -1, really *)
      (* | There, false -> _recFint (string_of_int (-1)) (* specially for Latest *) *)
    in
    let formula_of_hat ht = 
      match tidopt with
      | Some tidf -> tidf
      | _         -> _recFint_of_pl ht
    in
    let hi_of_ep hk =
      match hk with Hook -> _recFint (string_of_int (-1)) | _ -> hicurr
    in
    let hiformula_of_ep hk =
      either (hi_of_ep hk) (hiopt &~~ (_Some <.> _recFname))
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
    let tevw cxt hk ef =
      Printf.printf "\ntranslating %s" (string_of_formula (_recFandw hk ef));
      let tidf = _recFname tid_name in
      let cxt, ef = 
        anyway2 (opttsf bounds (InU ef) tn (Some tidf) hiopt (hiformula_of_ep hk) bcxt) 
                cxt 
                ef 
      in 
      Some (cxt, Some (bindallthreads tid_name ef))
    in
    let temporal_extra bcxt cxt hk p =
      match tidopt with 
      | None -> cxt, _recTrue
      | _    -> anyway2 (opttsf bounds situation tn tidopt hiopt (hiformula_of_ep hk) bcxt) cxt p
    in
    if !Settings.verbose || !Settings.verbose_modality then
      Printf.printf "\nembed tidopt=%s f=%s" (string_of_option string_of_formula tidopt) (string_of_formula f); 
    let process_var cxt ht hk v f =
      let tidf, epf = 
      match tn, ht, hk with
      | 0, Some ht, NoHook ->
          _recFint_of_int (tn_of_hat ht),
          _recFint_of_int (-1) (* for now *)
      | _                  ->
          formula_of_hat ht,
          hiformula_of_ep hk
      in
      let vtype = if v=barrier_event_name then Bool else bcxt <@@> f in
      embedvariable cxt tidf epf v vtype
    in
    match f.fnode with
    | Fvar (_,_,v) 
       when Stringutils.ends_with v "&new" -> (* x!new isn't really a variable, doesn't have a history *)
        None
    | Fvar (ht,hk,v) -> (* I don't think we need special treatment of bound variables: they won't be hatted or hooked *)
        let cxt, vv = process_var cxt ht hk v f in
        Some (cxt, Some vv)
    (* | Latest (ht,hk,v) -> 
           let epf = hiformula_of_ep hk in
           let vtype = bcxt <@@> f in
           let cxt, f = embedlatest cxt ht epf v vtype in
           Some (cxt, Some f)
     *)
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
    | Since (hk, f1, f2) ->
        (* U does _not_ see through since. So we ignore tidopt, except for extra_f1 *)
        let cxt, extra_f1 = temporal_extra bcxt cxt hk (conjoin [f1; ouat hk f2]) in
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
             let cmp_op = match hk with | NoHook -> _recLessEqual | Hook -> _recLess in
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
              match situation, hk with 
              | Amodal   , NoHook 
              | InSince _, NoHook -> _recLessEqual, _recLessEqual, hicurr 
              | Amodal   , Hook 
              | InSince _, Hook -> _recLess     , _recLess     , hicurr
              | InBfr _  , NoHook 
              | InSofar _, NoHook 
              | InU   _  , NoHook -> _recLess     , _recLessEqual, hicurr
              | InBfr _  , Hook 
              | InSofar _, Hook 
              | InU   _  , Hook -> _recLess     , _recLess     , (match hicurr.fnode with
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
    | Sofar (hk, sf) ->
        let do_sofar cxt tidopt extra_sf =
          (* same as since, except from the beginning of time *)
          let hi = match hiopt with
                   | None    -> history_index_name 
                   | Some hi -> new_name history_index_name 
          in
          let hi_formula = _recFname hi in
          let cxt, sf = anyway2 (opttsf bounds (InSofar sf) tn tidopt (Some hi) hi_formula bcxt) cxt sf in
          let cmp_op = match hk with | NoHook -> _recLessEqual | Hook -> _recLess in
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
             let history = sf :: List.map (sofar hk) (individualise sf) in
             let cxt, bcxt = completed_typeassign_formula_list cxt bcxt Bool history in
             temporal_extra bcxt cxt hk (conjoin history) 
           in
           do_sofar cxt None extra_sf
          )
    | Fandw (hk,ef) -> tevw cxt hk ef
    | Binder (fe, v, bf) ->
        (* if Name.is_anyvar v then 
             raise (Error (Sourcepos.string_of_sourcepos f.fpos ^ ": cannot embed variable binding " ^ string_of_formula f));
         *)
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
  and individualise _P = 
    let pfrees = NameSet.filter Name.is_anyvar (Formula.frees _P) in
    if NameSet.cardinal pfrees<2 then 
      [] (* not even two free variables: we don't need to touch it *)
    else
      List.map (fun v -> bindExists (NameSet.remove v pfrees) _P)
               (NameSet.elements pfrees)
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
    let cxt, axiom = embed axbinders cxt axiom in
    mfilter cxt, bindForall cfrees axiom::fs
  in
  List.fold_left handle (cxt, []) types 

