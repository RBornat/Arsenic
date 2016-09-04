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

(* an attempt to define enbar(P), the assertion which can be said to be transmitted in 
   interference by B(P) and across threads by U(P). Idea is to stop assertions claiming
   to transmit coincidences. Inspired by 
        enbar(A since B) = enbar(A) /\ enbar(ouat(B))

   I'm not trying too hard to make it efficient. It is used once on each
   _B and _U in Lace; it is used once on each thread postcondition in Checkproof.
   Neither of those seem to need attention.
   
   It can be used repeatedly in enhat, if the relevant setting is applied. I intend
   to memoise enhat to protect that.
 *)

(* in what follows, pos is a boolean: a formula occurs in a positive position.
   Temporal formulas in negative positions -- except perhaps sofar -- are a problem.
 *)
let randombool_name = "boolrand&"     (* & on the end cos it's a variable. And it mustn't start with r ... *)

let enbar binders _P =
  let univariate binders f = 
    NameSet.cardinal 
      (NameSet.filter Name.is_anyvar 
                      (NameSet.diff (Formula.frees f) binders)
      ) < 2
  in
  let bad f = raise (Error (Printf.sprintf "%s: enbar(%s) inside %s"
                                                (Sourcepos.string_of_sourcepos _P.fpos)
                                                (string_of_formula f)
                                                (string_of_formula _P)
                           )
                    )
  in
  let newrand () = _recFname (Name.new_name randombool_name) in
  let treatment pos binders posf f =
    if univariate binders f then Some None else 
    if pos then posf () else 
      _SomeSome (newrand())
  in
  let rec enb_opt pos binders f =
    match f.fnode with
    | Not nf ->
        (optbar (not pos) binders nf &~~ (_SomeSome <.> _recNot))
        |~~ (fun () -> Some None)
    | LogArith (f1, Implies, f2) ->
        (optionpair_either (optbar (not pos) binders) f1 (optbar pos binders) f2
         &~~ (_SomeSome <.> uncurry2 _recImplies)
        )
        |~~ (fun () -> Some None)
    | LogArith (f1, Iff, f2) ->
        (optbar pos binders (conjoin [_recImplies f1 f2; _recImplies f2 f2]) 
         &~~ _SomeSome
        )
        |~~ (fun () -> Some None)
    | Binder (bk, n, bf) ->
        (optbar pos (NameSet.add n binders) bf &~~ (_SomeSome <.> _recBinder bk n)) 
        |~~ (fun () -> Some None)
    (* here come the temporal cases. We know we are not univariate *)
    | Since (NoHook, f1, f2) ->
        treatment pos binders
          (fun _ -> _SomeSome (conjoin [bar pos binders f1; bar pos binders (ouat NoHook f2)]))
          f
    | Bfr   (NoHook, bf) ->
        treatment pos binders
        (fun _ -> (optbar pos binders bf &~~ (_SomeSome <.> _recBfr NoHook))
                  |~~ (fun () -> Some None)
        )
        bf
    | Univ  (NoHook, uf) ->
        treatment pos binders
        (fun _ -> (optbar pos binders uf &~~ (_SomeSome <.> _recUniv NoHook))
                  |~~ (fun () -> Some None)
        )
        uf
    | Sofar (NoHook, sf) ->
        treatment pos binders 
        (fun _ ->
           match Formula.deconjoin sf with
           | Some fs -> _SomeSome (bar pos binders (conjoin (List.map (sofar NoHook) fs)))
           | None    -> _SomeSome (bar pos binders sf)
        )
        sf
    | Ouat  (NoHook, sf) ->
        treatment pos binders 
        (fun _ ->
           match Formula.deconjoin sf with
           | Some fs -> _SomeSome (bar pos binders (conjoin (List.map (ouat NoHook) fs)))
           | None    -> _SomeSome (newrand ())
        )
        sf
    (* no hooking, please *)
    | Since (Hook, _, _) 
    | Bfr   (Hook, _) 
    | Univ  (Hook, _) 
    | Sofar (Hook, _)  
    | Ouat  (Hook, _) -> bad f
    (* otherwise *)
    | _               -> None
  and optbar pos binders f = Formula.optmap (enb_opt pos binders) f
  and bar pos binders = (optbar pos binders ||~ id)
  in
  Formula.map (enb_opt true binders) _P
  
(* ******************************** how it works ******************************** 

   We suppose a number of threads 0..tc and a number of states -infinity..(0 or 1).
   
   In a stability query, with hatting and/or hooking, the initial thread number is 0
   and the thread count is 3, if there is double hatting, or 2 otherwise.
   
   In a query with explicit thread numbering the thread count is the maximum thread number
   and (because of the way we construct the queries) the initial thread number is irrelevant.
   Thread numbers never appear in a stability query.
   
   In queries without hatting, hooking or thread numbering the thread count and thread
   number are each 1.
   
   There's a 'now' function (see nowf) which takes a thread id and delivers either
   0 or 1. In a stability query, with hatting and/or hooking, it is 
        -- nowf tid = if tid=0 then 1 else 0 fi
   That is, there is an extra state in thread 0, the new state instantaneously generated
   by an assignment. hooked_now is 0, the state before the assignment.
   
   In a non-stability query, without hatting or hooking, 
        -- nowf tid = 0
   That is, a sort of array of threads * states. 
   
   In a stability query, or a query without hatting or hooking and without explicit 
   thread numbering, . 
   
   Variable references are embedded as a function from variable name thread number and 
   state number. There is a function for each possible type of variable name (int, bool, 
   tuple of ...)
        -- x     (plain x)         is v_tx(x,tid,nowf tid)
        -- (-)x  (hooked x)        is v_tx(x,tid,0)
        -- (^)x  (hatted x)        is v_tx(x,1,hat_state)
        -- (^^)x (double-hatted x) is v_tx(x,2,dhat_state)
        -- (~)x  (tilde x)         is v_tx(x,1,hat_state)
        -- (~~)x (double-tilde x)  is v_tx(x,2,dhat_state)
   Note that tilde and hat never occur in the same query. hat_state and dhat_state are 
   defined to be some value less than 0 (i.e. they are some time in the past, notionally
   before the pre-interference state). Note that hatted (etc.) occurrences are treated 
   as in another thread.
   
   Sofar(P) is P everywhere, since the beginning of time 
        -- forall t (forall hi (hi<nowf t -> P^hi))@t)
        -- hooked Sofar replaces nowf t by 0, the Sofar state before the assignment.
   Note that Sofar(x=0)=>(^x)=0 (and (^^)x=0 and so on). 
   Hooked Sofar replaces nowf t by 0.
   
   Ouat(P) is at one point in the current thread P -- exists hi (hi<nowf 0 -> P^hi). Note
   that Ouat((^x)=0) is kind of ok.
   Hooked Ouat replaces nowf 0 by 0. 
   
   P since Q means there was a time at which P/\Q and since then P.
        -- exists hi (Q^hi /\ forall hi' (hi<=hi'<=nowf tid => P^hi'))
   Hooked since replaces nowf tid by 0
   
   B(P) means there was a time at which there was a barrier event, since which P held locally
        -- P since bev& 
   bev& is a boolean variable, used only for B and U.
   Hooked B is just hooked since.
   
   U(P) means that P has held in all threads since a barrier event
        -- exists hi (hi<nowf tid /\ bev&^hi /\ forall t (forall hi' (hi<=hi'<nowf t -> P^hi'))@t)
   It doesn't use an embedded since because that nobbles Z3. I don't think it matters that
   it quantifies across threads: all it is asking is that there is a numbering of states
   which makes certain local orderings possible. I don't think it matters that all
   threads are ordered against one 'global' barrier event either.
   
   Note that U(x=0) does not imply (^x)=0: the hat_state could be prior to the bev& state.
   That's intentional: you can't suppose that interference which arrives after a U-creating
   barrier (like a Power sync) started out after that barrier. 
   
   ****************************************************************************** *)
 
let valuefn_name = "&v"             (* (vname,place,history index) *)
let latestfn_name = "&latest"       (* (vname,ishatted,history index) *)
let coherencefn_name = "&co"
let coherencevar_name = "&cv"
let vartype_name = "&vtype"

let history_function_name = "&hf"
let history_index_name = "&hi"
let barrier_event_name = "bev&"     (* & on the end cos it's a variable *)
let tid_name = "&tid"
let hat_hi_name = "&hat"
let dhat_hi_name = "&hathat"

let now_function_name = "&now"

let barrier_event_formula = _recFname barrier_event_name
let hat_hi_formula = _recFname hat_hi_name
let dhat_hi_formula = _recFname dhat_hi_name

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
 *)

let rec simplify f =
  let check_barring uf =
    let uf' = enbar NameSet.empty uf in
    if not (Formula.eq uf uf') then 
      raise (Error (Printf.sprintf "%s: can't embed %s (enbarred as %s)"
                                   (Sourcepos.string_of_sourcepos uf.fpos)
                                   (string_of_formula uf)
                                   (string_of_formula uf')
                   )
            )
  in
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
         | Univ  (_,uf')     -> _SomeSome (simplify (universal hk uf'))
         | Bfr    (_,bf)     -> _SomeSome (simplify (universal hk bf ))
         | Fandw  (_,ef)     -> _SomeSome (simplify (universal hk ef ))
         | Sofar (_, sf)     -> _SomeSome (simplify (sofar hk sf)) 
         | Since (_,p,q)     -> check_barring uf; check_barring p;
                                _SomeSome (simplify (since hk (fandw NoHook p) (conjoin [fandw NoHook uf; barrier_event_formula])))
         |_                  ->
             check_barring uf;
             pushlogical (_recUniv hk) uf 
             |~~ (fun () ->
                     (* this is the 'old' way, which quantifies (fandw) across threads. But then
                        so does the 'new' way below. And at least this one aligns the boundary
                        events, which is a reasonable abstraction. Aligning them properly with
                        the 'new' treatment would be a bit scary. I might attempt it one day.
                      *)
                     Some (Some (simplify (since hk (simplify (fandw NoHook uf)) barrier_event_formula)))
                     (* the 'new way
                        Some (Some (fandw hk (simplify (since NoHook uf barrier_event_formula))))
                      *)
                  )
        )
    | Bfr (hk,bf) -> 
        (* because we prohibit Bfr formulae with coincidences, and we don't construct them
           automatically, we don't need to do what we do with _U(since) and _U(sofar) above.
         *)
        pushlogical (_recBfr hk) bf 
        |~~ (fun () ->
                Some (Some (simplify (since hk bf barrier_event_formula)))
             )
    | Since (hk,f1,f2) ->
        let f1 = simplify f1 in
        let f2 = simplify f2 in
        (match f1.fnode with
         | Since (_,sf1,sf2) -> Some (Some (simplify (since hk sf1 (conjoin [f1;f2]))))
         | Sofar (_,sf)      -> Some (Some (simplify (conjoin [sofar hk sf; ouat hk f2]))) 
         | _                 -> None
        )
    | Sofar (hk,sf) ->
        (match sf.fnode with
         | Univ  (_,uf)  -> _SomeSome (simplify (sofar hk uf))
         | Bfr   (_,bf)  -> _SomeSome (simplify (sofar hk bf))
         | Fandw (_,ef)  -> _SomeSome (simplify (sofar hk ef))
         | Since (_,p,q) -> _SomeSome (simplify (conjoin [sofar hk p; fandw hk (ouat hk q)]))
         | Sofar (_,sf') -> _SomeSome (simplify (sofar hk sf'))
         | _             -> check_barring sf;
                            None
        )
    (* Ouat isn't since and doesn't cross threads, so doesn't get treated here *)
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

(* I think this might be a little redundant ... *)
type situation = 
  | Amodal 
  | InSince of formula 
  | InBfr of formula 
  | InU of formula
  | InSofar of formula
  | InOuat of formula

(* hats and tildes don't occur in same query *)

let tn_of_hat = function 
  | Hat  | Tilde  -> 1
  | DHat | DTilde -> 2

let hi_of_hat = function 
  | Hat  | Tilde  -> hat_hi_formula
  | DHat | DTilde -> dhat_hi_formula

(* hatted stuff comes from a state before now, and before the hooked state *)
let hat_hi_asserts = 
  let zero = _recFint_of_int 0 in
  [ _recLess hat_hi_formula zero; _recLess dhat_hi_formula zero ]

(* note that hooked formulae operate in state 0; unhooked in state 1 (if stabq) or 0. 
   That last is regulated by the now function: if there's a hook around it will go for 1.
 *)
let nowf tid = _recApp now_function_name [tid]
let new_nowf f _ = f
let hooked_now = _recFint_of_int 0

let embed bcxt cxt orig_f = 
  
  (* I used to be defensive about hatting and hooking (There and Hook). NoHook I'm not. It shouldn't happen that you get There+Hook;
     it shouldn't happen that you get There inside There or Hook inside Hook. But if the first happens I'll ignore it; if the 
     second happens I'll take the outer (which is the same as taking the inner, isn't it? but the code works that way).
   *)

  let rec tsf bounds situation (tidf:formula) (hiopt:Name.name option) (nowf:formula->formula) bcxt cxt f = 
    let noisy = !Settings.verbose_modality in
    (* if noisy then Printf.printf "\ntsf formula is %s" (string_of_formula f); *)
    let formula_of_hat ht = 
      match ht with 
      | None      -> tidf
      (* tildes and hats don't occur in the same query *)
      | Some hat  -> _recFint_of_int (tn_of_hat hat)
    in
    let hi_of_ep hk =
      match hk with Hook -> hooked_now | _ -> nowf tidf
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
      (* Printf.printf "\ntranslating %s" (string_of_formula (_recFandw hk ef)); *)
      let tidf' = _recFname tid_name in
      let cxt, ef = 
        anyway2 (opttsf bounds (InU ef) tidf' hiopt (new_nowf (hiformula_of_ep hk)) bcxt) 
                cxt 
                ef 
      in 
      Some (cxt, Some (bindallthreads tid_name ef))
    in
    if !Settings.verbose || !Settings.verbose_modality then
      Printf.printf "\nembed tidf=%s f=%s" (string_of_formula tidf) (string_of_formula f); 
    let process_var cxt ht hk v f =
      let tidf, epf = 
      match ht, hk with
      | Some ht, NoHook ->
          _recFint_of_int (tn_of_hat ht), hi_of_hat ht
      | _               ->
          formula_of_hat ht, hiformula_of_ep hk
      in
      let vtype = if v=barrier_event_name then Bool else bcxt <@@> f in
      embedvariable cxt tidf epf v vtype
    in
    match f.fnode with
    | Fvar (_,_,v) 
       when Stringutils.ends_with v "&new" -> (* x!new isn't really a variable, doesn't have a history *)
        None
    | Fvar (ht,hk,v) -> (* We don't need special treatment of bound variables: they may even be hatted (but not hooked )*)
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
        let cxt, f1 = anyway2 (opttsf bounds situation tidf hiopt nowf bcxt) cxt f1 in
        let cxt, f2 = anyway2 (opttsf bounds situation tidf hiopt nowf bcxt) cxt f2 in
        let cxt, f = embedcoherence cxt v (bcxt <@@> f) f1 f2 in
        Some (cxt, Some f)
    | Since (hk, f1, f2) ->
        let hi = match hiopt with
                 | None    -> history_index_name 
                 | Some hi -> new_name history_index_name 
        in
        let hi_formula = _recFname hi in
        let cxt, f2 = anyway2 (opttsf bounds (InSince f2) tidf (Some hi) (new_nowf hi_formula) bcxt) cxt f2 in
        let hi1 = new_name history_index_name in
        let hi1_formula = _recFname hi1 in
        let cxt, f1 = anyway2 (opttsf bounds (InSince f1) tidf (Some hi1) (new_nowf hi1_formula) bcxt) cxt f1 in
        let since_assert =
          if !Settings.simpleUBsince then
            ((* This somewhat simpler version -- which doesn't demand a previous state -- is 
                for some reason often 2.5 times slower ... and I honestly can't see why.
              *)
             let cmp_op = match hk with | NoHook -> _recLessEqual | Hook -> _recLess in
             bindExists 
               (NameSet.singleton hi)
               (conjoin 
                  [cmp_op hi_formula (nowf tidf);
                   f2; 
                   bindForall 
                     (NameSet.singleton hi1) 
                     (_recImplies 
                        (conjoin [_recLessEqual hi_formula hi1_formula;
                                  cmp_op hi1_formula (nowf tidf)
                                 ]
                        )
                        f1
                     )
                  ]
               )
            )
          else (
            (* treating Sofar like U: think that's right *)
            let cmp_op1, cmp_op2, limit = 
              match situation, hk with 
              | Amodal   , NoHook 
              | InSince _, NoHook -> _recLessEqual, _recLessEqual, nowf tidf 
              | InBfr _  , NoHook 
              | InSofar _, NoHook 
              | InOuat  _, NoHook 
              | InU   _  , NoHook -> _recLess     , _recLessEqual, nowf tidf
              | Amodal   , Hook   -> _recLess     , _recLess     , nowf tidf
              | InBfr _  , Hook 
              | InSofar _, Hook 
              | InOuat  _, Hook 
              | InU     _, Hook   
              | InSince _, Hook   -> raise (Error ("hooked since inside something else " ^ (string_of_formula f)))
                                     (* _recLess     , _recLess     , (match (nowf tidf).fnode with
                                                                       | Fint "0" -> _recFint "-1"
                                                                       | _        -> _recMinus (nowf tidf) (_recFint "1")
                                                                      )
                                      *)
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
                                 cmp_op2 hi1_formula (nowf tidf)
                                ]
                       )
                       f1
                    )
                 ]
              )
          )
        in
        Some (cxt, Some since_assert)
    | Sofar (hk, sf) ->
        (* forall threads forall time sf *)
        let hi = match hiopt with
                 | None    -> history_index_name 
                 | Some hi -> new_name history_index_name 
        in
        let hi_formula = _recFname hi in
        let tid_formula = _recFname tid_name in
        let now = if hk=Hook then hooked_now else nowf tid_formula in 
        let cxt, sf = anyway2 (opttsf bounds (InSofar sf) tid_formula (Some hi) (new_nowf hi_formula) bcxt) cxt sf in
        let since_always = 
          bindForall (NameSet.singleton hi) (_recImplies (_recLessEqual hi_formula now) sf)
        in
        Some (cxt, Some (bindallthreads tid_name since_always))
    | Ouat (hk, sf) ->
        (* exists time (not sf) *)
        let hi = match hiopt with
                 | None    -> history_index_name 
                 | Some hi -> new_name history_index_name 
        in
        let hi_formula = _recFname hi in
        let now = if hk=Hook then hooked_now else nowf tidf in 
        let cxt, sf = anyway2 (opttsf bounds (InSofar sf) tidf (Some hi) (new_nowf hi_formula) bcxt) cxt sf in
        let since_always = 
          bindExists (NameSet.singleton hi) (_recAnd (_recLessEqual hi_formula now) sf)
        in
        Some (cxt, Some since_always)
    | Fandw (hk,ef) -> tevw cxt hk ef
    | Binder (fe, v, bf) ->
        (* if Name.is_anyvar v then 
             raise (Error (Sourcepos.string_of_sourcepos f.fpos ^ ": cannot embed variable binding " ^ string_of_formula f));
         *)
        let bounds = NameSet.add v bounds in
        let cxt, bf' = anyway2 (opttsf bounds situation tidf hiopt nowf bcxt)
                               ((v,bcxt<@@>f)::cxt)
                               bf
        in Some (List.remove_assoc v cxt, Some (_recBinder fe v bf'))
    | App (name, [{fnode=Fvar(_,_,v)} as var])
      when name=Formula.coherevar_token ->
        Some (embedcoherencevar cxt v (bcxt <@@> var)) 
    | Threaded (tid, tf) ->
        let cxt, tf' =
          anyway2 (opttsf bounds situation (_recFint_of_int tid) hiopt nowf bcxt) cxt tf        
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
  and opttsf bounds situation tidf hiopt nowf bcxt = 
    Formula.optmapfold (tsf bounds situation tidf hiopt nowf bcxt)
  in
  anyway2 (opttsf NameSet.empty Amodal (_recFint_of_int !Thread.threadnum) None nowf bcxt) cxt orig_f


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

