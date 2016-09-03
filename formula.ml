(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015-2016 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
open Function
open Option
open Tuple
open Sourcepos
open Name
open Listutils
open MySet

exception Error of string

type formula = {fpos: sourcepos; fnode: formulanode}

 (* type-check for various restrictions -- formula, assertion, aux formula, etc. 
    Don't distinguish regs from auxs in this type. Check on parsing? Yes.
  *)
 (* variables can be hooked or enhat. Modalities can be hooked. So we 
    separate hatting from (what is currently called) hooking. And so that we can
    have a hatting parameter to enhat, we make hatting an option.
  *)
 (* Ouat is now a full citizen: sort of !B using the initial boundary event -- i.e. one 
    time in current thread. Sofar is now  U using the initial bev -- i.e. all threads all time.
  *)
 and formulanode =
  | Fint         of string (* a sequence of decimal digits, by construction I hope *)
  | Fbool        of bool
  | Freg         of reg
  | Fvar         of hatting option * hooking * var
  | Flogc        of logc
  | Negarith     of formula
  | Arith        of formula * arithop * formula
  | Not          of formula
  | LogArith     of formula * boolop * formula
  | Compare      of formula * compareop * formula
  | Ite          of formula * formula * formula (* Ite only in assertions, people! *)
  | Binder       of bkind * name * formula      (* name must not be var -- I don't know how to police this *)
  | Tuple        of formula list
  
  | Since        of hooking * formula * formula    
  | Bfr          of hooking * formula                              
  | Univ         of hooking * formula 
  (* I can't deal with latest at the moment. Too busy simplifying for v1.1. RB 09/08/2016
      | Latest       of hatting * hooking * var                  (* global function; hatting _only_ for InflightHat *)
   *)
  | Sofar        of hooking * formula              
  | Ouat         of hooking * formula              
  
  | Cohere       of var * formula * formula             (* it's a global relation ... but embedding is subtle *)
  
  | Fandw        of hooking * formula (* ONLY for use in modality.ml and askZ3.ml; current use ONLY 
                                         to distribute coherence axioms across all threads.
                                       *)
  | App          of name * formula list (* these are currently provided for the benefit
                                           of askZ3 in the embedding of stuff.
                                           Don't use otherwise without thinking _hard_.
                                         *)
  | Threaded of threadid * formula (* for use when playing inter-thread games. *) 

and hatting = Hat | DHat | Tilde | DTilde

and hooking = 
  | NoHook    (* v    *)
  | Hook      (* (-)v *)

and boolop = And | Or | Implies | Iff 

and compareop = Less | LessEqual | Equal | NotEqual | GreaterEqual | Greater

  (* no Ite, no AndAnd, no OrOr, because they hide an implicit branch.
     Actually we could allow Ite provided we prohibit it in the purity 
     check in the parser. But there's no point having AndAnd or OrOr.
   *)

and bkind = Forall | Exists

and arithop = Plus | Minus | Times | Div | Mod

and threadid = int

(* and threadid = At_int of int | At_name of name *)

exception Substitute of formula

let is_Tildehatting = function
  | Tilde  
  | DTilde -> true
  | _      -> false
  
(* constructor/destructor functions *)

let _Fint      i           = Fint i
let _Fbool     b           = Fbool b
let _Freg      fr          = Freg fr
let _Fvar      pl hk v     = Fvar (pl,hk,v)
let _Flogc     n           = Flogc n

let _Fname     n           = if Name.is_anyreg n then Freg n else 
                             if Name.is_anyvar n then Fvar (None,NoHook,n)
                             else Flogc n

let _Negarith  f           = Negarith f
let _Not       f           = Not f
let _Arith     f1 op f2    = Arith (f1,op,f2)
let _LogArith  f1 op f2    = LogArith (f1,op,f2)
let _And       f1 f2       = LogArith (f1,And,f2)
let _Or        f1 f2       = LogArith (f1,Or,f2)
let _Implies   f1 f2       = LogArith (f1,Implies,f2)
let _Iff       f1 f2       = LogArith (f1,Iff,f2)
let _Compare   f1 op f2    = Compare (f1,op,f2)
let _Equal     f1 f2       = Compare (f1,Equal,f2)
let _NotEqual  f1 f2       = Compare (f1,NotEqual,f2)
let _Binder    bk n f      = Binder (bk,n,f)
let _Forall    n f         = Binder (Forall,n,f)
let _Exists    n f         = Binder (Exists,n,f)
let _Tuple     fs          = Tuple fs
let _Ite       cf tf ef    = Ite (cf,tf,ef)
let _Bfr       hk f        = Bfr (hk,f)
let _U         hk f        = Univ (hk,f)
let _Univ                  = _U
let _Fandw     hk f        = Fandw (hk,f)
let _Since     hk f1 f2    = Since (hk,f1,f2)
let _App       n fs        = App (n,fs)
let _Sofar     hk f        = Sofar (hk,f)
let _Ouat      hk f        = Ouat (hk,f)
let _Cohere    v f1 f2     = Cohere (v,f1,f2)
let _Threaded  tid f       = Threaded (tid,f)

(* let _Latest    pl hk v     = Latest (pl,hk,v) *)

(* let _At_int i = At_int i *)

let var_of_fvar = sndof2

(* end of constructor/destructor functions *)

(* ********************* building formula records ********************** *)

let fadorn sourcepos fnode = {fpos=sourcepos; fnode=fnode}

let _frec = fadorn dummy_spos

let _recFreg  r      = _frec (Freg r)
let _recFvar         = _frec <...> _Fvar
let _recFlogc k      = _frec (Flogc k)

let _recFname n = _frec (_Fname n)

let _recFint  i = _frec (Fint i)
let _recFint_of_int = _recFint <.> string_of_int

let _recFbool b = _frec (Fbool b)

let _recTrue = _recFbool true
let _recFalse = _recFbool false

let _recNot    f = _frec (Not f)
let _recNegative f = _frec (Negarith f)

let _recArith    f1 op f2 = _frec (Arith (f1,op,f2))
let _recLogArith f1 op f2 = _frec (LogArith (f1,op,f2))
let _recCompare  f1 op f2 = _frec (Compare (f1,op,f2))

let _recMinus f1 f2 = _recArith f1 Minus f2

let _recAnd     f1 f2 = _recLogArith f1 And f2
let _recOr      f1 f2 = _recLogArith f1 Or f2
let _recImplies f1 f2 = _recLogArith f1 Implies f2
let _recIff     f1 f2 = _recLogArith f1 Iff f2

let _recEqual        f1 f2 = _recCompare f1 Equal        f2
let _recNotEqual     f1 f2 = _recCompare f1 NotEqual     f2
let _recGreaterEqual f1 f2 = _recCompare f1 GreaterEqual f2
let _recLess         f1 f2 = _recCompare f1 Less         f2
let _recLessEqual    f1 f2 = _recCompare f1 LessEqual    f2

let _recIte = _frec <...> _Ite

let _recBinder bk n f = _frec (_Binder bk n f)

let _recExists = _recBinder Exists
let _recForall = _recBinder Forall

let _recTuple = _frec <.> _Tuple

let _recSince = _frec <...> _Since 

let _recBfr = _frec <..> _Bfr

let _recUniv = _frec <..> _Univ

let _recFandw = _frec <..> _Fandw

let _recApp = _frec <..> _App

let _recSofar = _frec <..> _Sofar
   
let _recOuat = _frec <..> _Ouat
   
let _recCohere = _frec <...> _Cohere

let _recThreaded = _frec <..> _Threaded

(* let _recLatest = _frec <...> _Latest *)

(* ********************* replacing fnodes ********************** *)

let rplac_fnode f fnode = {f with fnode=fnode}

let rplacFreg  f = rplac_fnode f <.> _Freg
let rplacFvar  f = rplac_fnode f <...> _Fvar
let rplacFlogc f = rplac_fnode f <.> _Flogc

let rplacFbool f = rplac_fnode f <.> _Fbool

let rplacTrue f = rplacFbool f true
let rplacFalse f = rplacFbool f false

let rplacNot f = rplac_fnode f <.> _Not
let rplacNegarith f = rplac_fnode f <.> _Negarith

let rplacArith f f1 op f2 = rplac_fnode f (Arith (f1,op,f2))
let rplacLogArith f f1 op f2 = rplac_fnode f (LogArith (f1,op,f2))
let rplacCompare f f1 op f2 = rplac_fnode f (Compare (f1,op,f2))

let rplacAnd f f1 f2 = rplac_fnode f (_And f1 f2)
let rplacOr f f1 f2 = rplac_fnode f (_Or f1 f2)
let rplacImplies f f1 f2 = rplac_fnode f (_Implies f1 f2)
let rplacIff f f1 f2 = rplac_fnode f (_Iff f1 f2)

let rplacEqual f f1 f2 = rplac_fnode f (_Equal f1 f2)

let rplacIte f = rplac_fnode f <...> _Ite

let rplacBinder f bk n f = rplac_fnode f (Binder (bk,n,f))

let rplacExists f = rplacBinder f Exists
let rplacForall f = rplacBinder f Forall

let rplacTuple f = rplac_fnode f <.> _Tuple

let rplacBfr f = rplac_fnode f <..> _Bfr

let rplacUniv f = rplac_fnode f <..> _Univ

let rplacFandw f = rplac_fnode f <..> _Fandw

let rplacSince f = rplac_fnode f <...> _Since

let rplacApp f = rplac_fnode f <..> _App

let rplacSofar f  = rplac_fnode f <..> _Sofar

let rplacOuat f  = rplac_fnode f <..> _Ouat

let rplacThreaded f = rplac_fnode f <..> _Threaded

(* ********************* check for particular shapes *********************** *)

let is_realreg    = function | {fnode=Freg r } -> Name.is_realreg r                 | _ -> false
let is_auxreg     = function | {fnode=Freg r } -> Name.is_auxreg r                 | _ -> false
let is_anyreg     = function | {fnode=Freg r } -> if Name.is_anyreg r then true
                                                   else raise (Error ("Freg " ^ string_of_name r))
                             | _ -> false

let is_realvar    = function | {fnode=Fvar (_,_,v)  } -> Name.is_realvar v | _ -> false
let is_auxvar     = function | {fnode=Fvar (_,_,v)  } -> Name.is_auxvar v  | _ -> false
let is_oldvar     = function | {fnode=Fvar (_,Hook,_)} -> true              | _ -> false

let is_anyvar     = function | {fnode=Fvar _} -> true | _ -> false

(* logc includes pmsc, apparently. See name.ml *)
let is_logc       = function | {fnode=Flogc _} -> true                  | _ -> false
let is_pmsc       = function | {fnode=Flogc n} -> Name.is_pmsc n        | _ -> false

let is_True  = function (Fbool true ) -> true | _ -> false
let is_False = function (Fbool false) -> true | _ -> false

let is_recTrue f  = is_True  f.fnode
let is_recFalse f = is_False f.fnode

let is_Bfr = function Bfr _ -> true | _ -> false
let is_recBfr f = is_Bfr f.fnode

let is_U = function Univ _ -> true | _ -> false
let is_recU f = is_U f.fnode

(* let is_Latest = function Latest _ -> true | _ -> false
   let is_recLatest f = is_Latest f.fnode
 *)

let is_Since = function Since _ -> true | _ -> false
let is_recSince f = is_Since f.fnode

let is_Sofar = function Sofar _ -> true | _ -> false
let is_recSofar f = is_Sofar f.fnode

let is_Ouat = function Ouat _ -> true | _ -> false
let is_recOuat f = is_Ouat f.fnode

let is_Cohere = function Cohere _ -> true | _ -> false
let is_recCohere f = is_Cohere f.fnode

(* ********************* functions for building meaningful formulas ********************* *)

let singleton_or_tuple = function
  | [f] -> f
  | fs  -> _recTuple fs
  
let reg_of_formula f = match f.fnode with
  | Freg r -> r
  | _       -> raise (Invalid_argument "reg_of_formula")

let conjoin fs = 
  if List.exists is_recFalse fs then _recFalse else
  match List.filter (not <.> is_recTrue) fs with
  | []    -> _recTrue
  | f::fs -> List.fold_left _recAnd f fs

let disjoin fs = 
  if List.exists is_recTrue fs then _recTrue else
  match List.filter (not <.> is_recFalse) fs with 
  | []    -> _recFalse
  | f::fs -> List.fold_left _recOr f fs
  
let negate f = match f.fnode with
  | Fbool b -> rplacFbool f (not b)
  | Not   f -> f
  | _       -> rplacNot f f

let before hk f = match f.fnode with
  | Bfr _ -> f
  | _     -> rplacBfr f hk f

let since hk f1 f2 = fadorn (spos_of_sposspos f1.fpos f2.fpos) (Since (hk,f1,f2))

let rec universal hk f = match f.fnode with
  | Fbool true  -> f
  | Fbool false -> f
  | Univ (_,uf) -> universal hk uf
  | _           -> rplacUniv f hk f

let rec fandw hk f = match f.fnode with
  | Fbool true  -> f
  | Fbool false -> f
  | _           -> rplacFandw f hk f

let sofar hk f = match f.fnode with
  | Sofar (hk',_) 
    when hk=hk' -> f
  | Fbool _     -> f
  | _           -> rplacSofar f hk f

let ouat hk f = match f.fnode with
  | Ouat (hk',_) 
    when hk=hk' -> f
  | Fbool _     -> f
  | _           -> rplacOuat f hk f

let threaded atf f = rplacThreaded f atf f 

let formula_of_threadid = _recFint <.> string_of_int

let rec deconjoin f =
  match f.fnode with
  | Not nf                 -> (dedisjoin &~ _Some) nf
  | LogArith (f1, And, f2) ->
      (match deconjoin f1, deconjoin f2 with
       | Some f1s, Some f2s -> Some (f1s@f2s)
       | Some f1s, None     -> Some (f1s@[f2])
       | None    , Some f2s -> Some (f1::f2s)
       | _                  -> Some [f1;f2]
      )
  | _                      -> None
  
and dedisjoin f =
  match f.fnode with
  | Not nf                     -> deconjoin nf
  | LogArith (f1, Implies, f2) -> 
      (let notf1 = _recNot f1 in
       match dedisjoin notf1, dedisjoin f2 with
       | Some f1s, Some f2s -> Some (f1s@f2s)
       | Some f1s, None     -> Some (f1s@[f2])
       | None    , Some f2s -> Some (notf1::f2s)
       | _                  -> Some [notf1;f2]
      )
  | LogArith (f1, Or     , f2) ->
      (match dedisjoin f1, dedisjoin f2 with
       | Some f1s, Some f2s -> Some (f1s@f2s)
       | Some f1s, None     -> Some (f1s@[f2])
       | None    , Some f2s -> Some (f1::f2s)
       | _                  -> Some [f1;f2]
      )
  | _                          -> None
    
 
(* ********************* string_of_formula etc. *********************** *)

let m_Bfr_token     = "_B"
let m_Univ_token    = "_U"
let m_Fandw_token   = "fandw" (* far and wide *)
let m_Sofar_token   = "sofar"  
let m_Ouat_token    = "ouat" (* once upon a time *)
let since_token     = "since"
let m_Latest_token  = "latest"
let cohere_token    = "_c"
let coherevar_token = "_cv"
let m_atthread_token = "@"

let string_of_hatting = function
  | Hat         -> "Hat"
  | DHat        -> "DHat"
  | Tilde       -> "Tilde"
  | DTilde      -> "DTilde"
  
(* let string_of_SOMEWHERE  = "faiaf" (* far away in a forest *)
   let string_of_EVERYWHERE = "Univ"  (* universal -- too important to be twee? *)
 *)

(* we can't extract priorities from the parser. Damn *)

type prioritydir = Left | Right | Assoc | NonAssoc

let string_of_prioritydir = function
  | Left     -> "Left"
  | Right    -> "Right"
  | Assoc    -> "Assoc"
  | NonAssoc -> "NonAssoc"
  
let commaprio               =  NonAssoc, -10

let logprio = function 
  | Implies                 -> Right   , 10
  | Iff                     -> Left    , 20 
  | Or                      -> Assoc   , 40
  | And                     -> Assoc   , 60

let compprio _              =  NonAssoc, 100

let arithprio = function
  | Plus                    -> Assoc   , 200
  | Minus                   -> Left    , 200
  | Times                   -> Assoc   , 210
  | Div | Mod               -> Left    , 210
  

let primaryprio             =  NonAssoc, 1000
let abitlessthanprimaryprio =  NonAssoc, 900

let string_of_prio = bracketed_string_of_pair string_of_prioritydir string_of_int

let mustbracket_left (lassoc,lprio) (supassoc, supprio) =
  lprio<supprio || (lprio=supprio && match supassoc with | Left | Assoc -> false |_ -> true)

let mustbracket_right (supassoc, supprio) (rassoc,rprio) =
  supprio>rprio || (supprio=rprio && match supassoc with | Right | Assoc -> false |_ -> true)

let formulaprio f = 
  match f.fnode with 
  | Fint     _ 
  | Fbool    _ 
  | Freg     _ 
  | Fvar     _ 
  | Flogc    _
  | Negarith _ 
  | Not      _                  -> primaryprio
  | Arith   (left, aop, right)  -> arithprio aop
  | Compare (left, cop, right)  -> compprio cop
  | LogArith(left, lop, right)  -> logprio lop
  | Ite    _                    -> primaryprio
  | Binder _                    -> primaryprio
  | Tuple  _                    -> commaprio
  | Since  _                    -> Left, 5 (* below Implies *)
  | Bfr    _                    -> primaryprio (* because it's printed as an app *)
  | Univ   _                    -> primaryprio (* because it's printed as an app *)
  | Fandw  _                    -> primaryprio (* because it's printed as an app *)
  | App    _                    -> primaryprio
  | Sofar  _                    -> primaryprio (* because it's printed as an app *)
  | Ouat   _                    -> primaryprio (* because it's printed as an app *)
  | Cohere _                    -> primaryprio (* because it's printed as an app *)
  (* | Latest _                    -> primaryprio (* because it's printed as an app *) *)
  | Threaded _                  -> abitlessthanprimaryprio (* bracket everything but primaries *) 
  
let is_primary f = formulaprio f = primaryprio

let string_of_arithop = function
  | Plus    -> "+"
  | Minus   -> "-"
  | Times   -> "*"
  | Div     -> "/"
  | Mod     -> "%"

let string_of_logop = function
  | And     -> "/\\"
  | Or      -> "\\/"
  | Implies -> "=>"
  | Iff     -> "<=>"

let string_of_compareop = function
  | Less            -> "<"
  | LessEqual       -> "<="
  | Equal           -> "="
  | NotEqual        -> "!="
  | GreaterEqual    -> ">="
  | Greater         -> ">"
  
let string_of_bkind = function
  | Forall -> "Forall"
  | Exists -> "Exists"
 
let string_of_infixSince = function
  | true  -> " " ^ since_token ^ " "
  | false -> " (-)" ^ since_token ^ " "

let hook_token = "(-)"

let hat_token = "(^)"
let dhat_token = "(^^)"
let tilde_token = "(~)"
let dtilde_token = "(~~)"

let string_of_hk = function
  | NoHook -> ""
  | Hook -> hook_token
  
let string_of_pl = function
  | None        -> ""
  | Some Hat    -> hat_token
  | Some DHat   -> dhat_token
  | Some Tilde  -> tilde_token
  | Some DTilde -> dtilde_token

let string_of_prefixSofar hk = 
  string_of_hk hk ^ m_Sofar_token
  
let string_of_prefixOuat hk = 
  string_of_hk hk ^ m_Ouat_token
  
let rec string_of_primary f = 
  match f.fnode with
  | Fint   i               -> i
  | Fbool  b               -> string_of_bool b
  | Freg   r               -> string_of_reg r
  | Fvar   (pl,hk,v)       -> string_of_pl pl ^ string_of_hk hk ^ Name.string_of_var v
  | Flogc  n               -> string_of_logc n
  | Negarith f'            -> "-" ^ string_of_primary f'
  | Not    f'              -> "!" ^ string_of_primary f'
  | Ite (cf,tf,ef)         -> Printf.sprintf "if %s then %s else %s fi"
                                             (string_of_formula cf)
                                             (string_of_formula tf)
                                             (string_of_formula ef)
  | Fandw  (hk,f)          -> string_of_hk hk ^ m_Fandw_token ^ bracketed_string_of_formula f
  | Bfr    (hk,f)          -> string_of_hk hk ^ m_Bfr_token ^ bracketed_string_of_formula f
  | Univ   (hk,f)          -> string_of_hk hk ^ m_Univ_token ^ bracketed_string_of_formula f
  | Binder (bk, n, f)      -> let ns, f = multibind bk [n] f in
                              string_of_bkind bk ^ "(" ^ 
                              string_of_list string_of_name "," ns ^ ")" ^ 
                              bracketed_string_of_formula f
  | App (n,fs)             -> string_of_name n ^ "(" ^ string_of_args fs ^ ")"
  | Sofar (hk,f)           -> string_of_prefixSofar hk ^ bracketed_string_of_formula f
  | Ouat  (hk,f)           -> string_of_prefixOuat hk ^ bracketed_string_of_formula f
  | Cohere (v,f1,f2)       -> cohere_token ^ "(" ^ string_of_var v ^ "," ^ string_of_args [f1;f2] ^ ")"
  (* 
    | Latest (hk,v)          -> string_of_hk hk ^ m_Latest_token ^ "(" ^ string_of_var v ^ ")"
   *)
  | _                      -> bracketed_string_of_formula f

and bracketed_string_of_formula f = "(" ^ string_of_formula f ^ ")"

and multibind bk ns f = match f.fnode with
  | Binder (bk', n, bf)
    when bk=bk' && not (List.mem n ns) -> multibind bk (n::ns) bf
  | _                                  -> List.rev ns, f

and string_of_args args = 
  let _, commaprio = commaprio in
  let f arg =
    let _, argprio = formulaprio arg in
    if argprio>commaprio then string_of_formula arg
                         else bracketed_string_of_formula arg
  in
  string_of_list f "," args
  
and string_of_formula f = 
  match f.fnode with
  | Fint         _ 
  | Fbool        _ 
  | Freg         _ 
  | Fvar         _ 
  | Flogc        _ 
  | Negarith     _ 
  | Not          _ 
  | Ite          _
  | Bfr          _              
  | Univ         _              
  | Fandw        _              
  | Binder       _
  | App          _  
  | Sofar        _ 
  | Ouat         _ 
  | Cohere       _            
  (* | Latest       _  *)
                                -> string_of_primary f
  | Arith   (left, aop, right)  -> string_of_binary_formula left right (string_of_arithop   aop) (arithprio aop)
  | Compare (left, cop, right)  -> string_of_binary_formula left right (string_of_compareop cop) (compprio cop)
  | LogArith(left, lop, right)  -> 
      (match compare_shorthand f with
       | Some (_,_,cseq)        -> string_of_cseq cseq
       | None                   -> string_of_binary_formula left right (string_of_logop     lop) (logprio lop)
      ) 
  | Since (NoHook, left, right) -> string_of_binary_formula left right (" " ^ since_token ^ " ") (formulaprio f)
  | Since (hk, left, right)     -> string_of_hk hk ^ 
                                   bracketed_string_of_formula {f with fnode=Since(NoHook,left,right)}
  | Threaded (tid,tf)           -> string_of_binary_formula tf (formula_of_threadid tid) m_atthread_token (formulaprio f)
  | Tuple fs                    -> string_of_args fs

and bracket_left lprio fprio = if mustbracket_left lprio fprio then bracketed_string_of_formula 
                                                               else string_of_formula

and bracket_right fprio rprio = if mustbracket_right fprio rprio then bracketed_string_of_formula
                                                                 else string_of_formula
                                                 
and string_of_binary_formula left right opstr opprio =
  let lprio = formulaprio left in
  let leftf = bracket_left lprio opprio in
  let rprio = formulaprio right in
  let rightf = bracket_right opprio rprio in
  leftf left^opstr^rightf right

and string_of_cseq = function
  | (left,cop,right) :: []   ->
      string_of_binary_formula left right (string_of_compareop cop) (compprio cop)
  | (left,cop,_    ) :: cseq ->
      (* do the first half of string_of_binary_formula. Whahey! *)
      let opprio = compprio cop in
      let lprio = formulaprio left in
      let leftf = bracket_left lprio opprio in
      leftf left ^ string_of_compareop cop ^ string_of_cseq cseq
  | _                        -> 
      raise (Error "string_of_cseq sees []")
  
and compare_shorthand f =
  match f.fnode with
  | Compare  (left,cop,right) -> Some (left,right,[(left,cop,right)])
  | LogArith (left,And,right) ->
      (match compare_shorthand left, compare_shorthand right with
       | Some (left,leftright,lefts), Some (rightleft,right,rights) ->
           (* Printf.printf "\ncompare_shorthand %s %s; computer says %B"
                            (string_of_cseq lefts)
                            (string_of_cseq rights)
                            (leftright=rightleft);
            *)
           (* this test isn't good enough, but we're not ready for stripspos yet, are we? *)
           if leftright=rightleft then Some (left,right,lefts@rights) else None
       | _ -> None
      )
  | _                         -> None

let string_of = string_of_formula

let out c f = output_string c (string_of_formula f)

(* ********************* indented_string_of_formula *********************** *)

let tabsize = 4
let max_width = 120

let indent_string indent = String.make (indent*tabsize) ' '

let tab_width s = (String.length s + (tabsize-1)) / tabsize

let tab_padded s = s ^ String.make (tab_width s * tabsize - String.length s) ' '

type indentation = MustIndent | MustBracket | Level

let mustindent_left (lassoc,lprio) (supassoc, supprio) =
if lprio>supprio then MustIndent else
  if lprio<supprio then MustBracket else
   (match supassoc with 
    | Left | Assoc -> Level
    | _            -> MustIndent
   )

let mustindent_right (supassoc, supprio) (rassoc,rprio) =
if supprio<rprio then MustIndent else
  if supprio>rprio then MustBracket else
   (match supassoc with 
    | Right | Assoc -> Level
    | _             -> MustIndent
   )

(* just_log: boolean. When true just indent the logical operators (not the arith/compares) *)

(* the new version, done properly with lists of lines. Tab sizes have nothing to do with it
   -- or do they?
   Not much attempt to stop repeated String/List concats here.
 *)
let indented_string_of_formula just_log indent f = 
  let prefix_string s line = s ^ line in
  let prefix_strings s = List.map (prefix_string s) in
  let pad_lines padwidth (ss,w) = 
      prefix_strings (String.make padwidth ' ') ss, w+padwidth
  in
  let rec isf_lines max_width f =
    let canthappen s f = raise (Error (s ^ " sees empty list from isf_lines " ^ string_of_formula f)) in
    let rec one_liner f = 
      let ok_width () = String.length (string_of_formula f) <= max_width in
      match f.fnode with
      (* these can't come apart *)
      | Fint         _
      | Fbool        _
      | Freg         _
      | Fvar         _
      | Flogc        _         
      (* | Latest       _    *)
                               -> true
      (* these stay together, unless we want them apart or they are too wide *)
      | Negarith       _ 
      | Arith        _ 
      | Compare      _         -> just_log && ok_width ()
      (* these always come apart *)
      | LogArith     _         -> false
      (* these come apart if their insides come apart *)
      | Not                  f -> one_liner f
      | Bfr              (_,f) -> one_liner f
      | Univ             (_,f) -> one_liner f
      | Fandw            (_,f) -> one_liner f
      (* these come apart if their insides come apart, or if they are too wide *)
      | Binder         (_,_,f) -> one_liner f && ok_width ()
      | Tuple               fs -> List.for_all one_liner fs && ok_width ()
      | Ite         (cf,tf,ef) -> List.for_all one_liner [cf;ef;tf] && ok_width ()
      | App             (n,fs) -> List.for_all one_liner fs && ok_width () 
      | Since        (_,f1,f2) -> one_liner f1 && one_liner f2 && ok_width ()
      | Sofar            (_,f) -> one_liner f && ok_width ()
      | Ouat             (_,f) -> one_liner f && ok_width ()
      | Cohere       (_,f1,f2) -> one_liner f1 && one_liner f2 && ok_width ()
      | Threaded         (_,f) -> one_liner f && ok_width ()
    and padded_prefix opstr = opstr ^ " " 
    and bracket_lines lpar rpar = function
      | []   , _ -> raise (Invalid_argument "isf_lines.bracket_lines []")
      | [s]  , w -> [lpar ^ s ^ rpar], w+2
      | s::ss, w -> (lpar ^ s)::(prefix_strings " " ss) @[rpar], w+String.length lpar
    and prefix_op opstr padded_opstr (ss,w) = 
      let padwidth = String.length padded_opstr in
      if padwidth>tabsize && padwidth+w>max_width then 
        opstr::prefix_strings (String.make tabsize ' ') ss, max (String.length opstr) (w+tabsize)
      else
       (match ss with
        | []    -> raise (Invalid_argument "isf_lines.prefix_op")
        | s::ss -> prefix_string padded_opstr s::prefix_strings (String.make padwidth ' ') ss, w+padwidth
       )
    and isf_prefix opstr bracket f =
      let padded_opstr = padded_prefix opstr in
      let padwidth = String.length padded_opstr in
      let lines = isf_lines (max_width-(min padwidth tabsize)) f in
      let lines = if bracket then bracket_lines "(" ")" lines else lines in
      prefix_op opstr padded_opstr lines
    and concat_blocks blocks =
      let blockss, blockws = List.split blocks in
      let w = List.fold_left max 0 blockws in
      List.concat blockss, w
    and isf_app name args = 
      let mustbracket = match args with [f] -> not (is_primary f) | _ -> true in
      let prefix = padded_prefix name ^ (if mustbracket then "(" else "") in
      let padwidth = String.length prefix in
      let arglines = List.map (isf_arglines (max_width-(min padwidth tabsize))) args in
      let argsw = List.fold_left (fun x -> max x <.> sndof2) 0 arglines in
      let arglines = List.map (fun (ss,_) -> ss, argsw) arglines in
      match arglines with 
      | [] -> [prefix ^ (if mustbracket then ")" else "")], padwidth+1
      | argline::arglines -> 
          let arglines = prefix_op prefix prefix argline ::
                         List.map (prefix_op (String.make (String.length prefix) ' ') 
                                             (String.make (String.length prefix) ' ')
                                  ) 
                                  arglines
          in
          Listutils.interpconcat [","] (List.map fstof2 arglines) @ (if mustbracket then [")"] else []), sndof2 (List.hd arglines)
    and isf_arglines max_width arg =
      let arglines = isf_lines max_width arg in
      let _, argprio = formulaprio arg in
      let _, commaprio = commaprio in
      if argprio>commaprio then arglines else bracket_lines "(" ")" arglines
    and isb left right opstr opprio =
      let padded_opstr = padded_prefix opstr in
      let padwidth = String.length padded_opstr in
      let dosub mustindent sub =
         match mustindent with
        | MustIndent  -> pad_lines padwidth (isf_lines (max_width-padwidth) sub) 
        | MustBracket -> pad_lines padwidth (bracket_lines "(" ")" (isf_lines (max_width-padwidth) sub))
        | Level       -> isf_lines max_width sub
      in
      let lefts, lw = dosub (mustindent_left (formulaprio left) opprio) left in
      let rights, rw = dosub (mustindent_right opprio (formulaprio right)) right in
      lefts @ (match rights with 
               | []    -> canthappen "isb" right
               | r::rs -> try 
                             let blanks = String.sub r 0 padwidth in
                             if String.trim blanks<>"" then raise (Invalid_argument "");
                             (padded_opstr ^ String.sub r padwidth (String.length r - padwidth)) :: rs
                          with
                             Invalid_argument _ -> raise (Error ("isb packing\n\t" ^ String.concat "\n\t" rights))
              ),
      max lw rw
    in
    let do_one ff f = let s = ff f in [s], String.length s in
    if one_liner f then do_one string_of_formula f else
      match f.fnode with
      | Fint  _                     (* these are all one-liners: shouldn't appear here *)
      | Fbool  _ 
      | Freg   _ 
      | Fvar   _ 
      | Flogc  _    
      (* | Latest _  *)
                                    -> raise (Invalid_argument ("indented_string_of_formula.isf_lines " ^ string_of_formula f))
      | Negarith f                  -> isf_prefix "-" (not (is_primary f)) f
      | Not     f'                  -> isf_prefix "!" (not (is_primary f')) f'
      | Arith    (left, aop, right) -> isb left right (string_of_arithop   aop) (arithprio aop)
      | Compare  (left, cop, right) -> isb left right (string_of_compareop cop) (compprio  cop)
      | LogArith (left, lop, right) -> isb left right (string_of_logop     lop) (logprio   lop)
      | Since (NoHook, left, right) -> isb left right (" " ^ since_token ^ " ") (formulaprio f)
      | Since (hk, left, right)     -> isf_app (string_of_hk hk) [{f with fnode=Since(NoHook,left,right)}]
      | Binder (bk, n, f)           -> 
          let ns, f = multibind bk [n] f in
          let prefix = 
            string_of_bkind bk ^ "(" ^  string_of_list string_of_name "," ns ^ ")"
          in
          let bracket = not (is_primary f) in
          let prefix, padded_prefix = 
            if bracket then let s = (padded_prefix prefix) ^ " (" 
                            in s, s
                       else prefix, padded_prefix prefix 
          in
          let ss,w = 
            prefix_op prefix padded_prefix (isf_lines (max_width-tabsize) f) 
          in
          (if bracket then ss@[")"] else ss),w
      | Tuple fs                    -> isf_app "" fs
      | App (n,fs)                  -> isf_app n fs
      | Ite (cf,tf,ef)              -> let itelines prefix f =
                                         prefix_op prefix (padded_prefix prefix) (isf_lines (max_width-tabsize) f) 
                                       in
                                       let ss, w =
                                         concat_blocks [itelines "if" cf; itelines "then" tf; itelines "else" ef]
                                       in
                                       ss@["fi"], w
      | Fandw    (hk,f)             -> isf_app (string_of_hk hk ^ m_Fandw_token) [f]
      | Bfr    (hk,f)               -> isf_app (string_of_hk hk ^ m_Bfr_token) [f]
      | Univ   (hk,f)               -> isf_app (string_of_hk hk ^ m_Univ_token) [f]
      | Sofar    (hk,f)             -> isf_app (string_of_prefixSofar hk) [f]
      | Ouat     (hk,f)             -> isf_app (string_of_prefixOuat hk) [f]
      | Cohere (v,f1,f2)            -> isf_app cohere_token [_recFname v; f1; f2]
      | Threaded (tid,tf)           -> isb tf (formula_of_threadid tid) " @ " (formulaprio f)
  in
  let lines = isf_lines max_width f in
  String.concat "\n" (""::(fstof2 (pad_lines indent lines))@[""])

let explain_string_of_formula f = 
  if !Settings.tree_formulas then indented_string_of_formula true 0 f
                             else string_of_formula f

(* ********************** maps, folds, exists for formulas ********************** *)

(* exists in a formula. optp f delivers Some witness when it knows, None when it doesn't 
   (it can't deliver true or false because it must sometimes deal with binders) *)

let optexists (optp: formula -> 'a option) f = 
  let rec ef f =
    optp f |~~ (fun () -> 
      match f.fnode with
      | Fint     _
      | Fbool    _
      | Freg     _
      | Fvar     _            
      | Flogc    _            -> None
      | Negarith f 
      | Not      f            -> ef f
      | Arith     (f1,_,f2)
      | LogArith  (f1,_,f2)
      | Compare   (f1,_,f2)   -> optfirst ef [f1;f2]
      | Binder    (_,n,f)     -> ef f (* really: catch it in p if you are implementing binders *)
      | Tuple     fs          -> optfirst ef fs
      | Ite       (cf,f1,f2)  -> optfirst ef [cf;f1;f2]
      | Since     (_,f1,f2)   -> optfirst ef [f1;f2]
      | Bfr       (_,f)       -> ef f
      | Univ      (_,f)       -> ef f
      (*  | Latest    _           -> None *)
      | Fandw     (_,f)       -> ef f
      | App       (_,fs)      -> optfirst ef fs (* really: catch it in p if n matters *)
      | Sofar     (_,f)       -> ef f
      | Ouat      (_,f)       -> ef f
      | Cohere    (_,f1,f2)   -> optfirst ef [f1;f2] (* catch v in p if it matters *)
      | Threaded  (_,f)       -> ef f
    )
  in
  ef f

let exists p = 
  bool_of_opt <.> optexists (fun f -> if p f then Some () else None)
  
(* fold (left) in a formula. optp x f delivers Some x' when it knows, None when it doesn't *)

let optfold (optp: 'a -> formula -> 'a option) x =
  let rec ofold x f =
    optp x f |~~ (fun () -> 
      match f.fnode with
        | Fint     _
        | Fbool    _
        | Freg     _
        | Fvar     _            
        | Flogc    _            -> None
        | Negarith  f
        | Not       f           -> ofold x f
        | Arith     (f1,_,f2)
        | LogArith  (f1,_,f2)
        | Compare   (f1,_,f2)   -> optfold ofold x [f1;f2]
        | Binder    (_,n,f)     -> ofold x f (* really!: catch it in optp if you are doing binders *)
        | Tuple     fs          -> optfold ofold x fs
        | Ite       (cf,tf,ef)  -> optfold ofold x [cf;tf;ef]
        | Since     (_,f1,f2)   -> optfold ofold x [f1;f2]
        | Bfr       (_,f)       -> ofold x f
        | Univ      (_,f)       -> ofold x f
        (* | Latest    _           -> None *)
        | Fandw     (_,f)       -> ofold x f
        | App       (n,fs)      -> optfold ofold x fs (* really!: catch the appname in optp if n matters *)
        | Sofar     (_,f)       -> ofold x f
        | Ouat      (_,f)       -> ofold x f
        | Cohere    (_,f1,f2)   -> optfold ofold x [f1;f2] (* catch v in optp if it matters *)
        | Threaded  (_,f)       -> ofold x f
    )
  in
  ofold x 

let fold optp x f = (revargs (optfold optp) f ||~ id) x

(* traversing a formula and modifying it: None if no change, Some f' if it changes.
   Note that the function ff now gives back Some r if it knows the answer (so r is an option)
   or None if it doesn't. Hope this works ...
 *)

let optmap ff f =
  let take1 c x = Some {f with fnode = c x} in
  let take2 c (f1,f2) = Some {f with fnode = c f1 f2} in
  let take3 c (f1,f2,f3) = Some {f with fnode = c f1 f2 f3} in
  let rec trav f =
    match ff f with
    | Some result -> result
    | _           -> match f.fnode with 
                     | Fint     _
                     | Fbool    _
                     | Freg     _
                     | Fvar     _            
                     | Flogc    _            -> None
                     | Negarith f            -> trav f &~~ take1 _Negarith
                     | Not      f            -> trav f &~~ take1 _Not
                     | Arith    (f1,op,f2)   -> trav2 f1 f2 &~~ take2 (revargs _Arith op) 
                     | LogArith (f1,op,f2)   -> trav2 f1 f2 &~~ take2 (revargs _LogArith op)
                     | Compare  (f1,op,f2)   -> trav2 f1 f2 &~~ take2 (revargs _Compare op)
                     | Binder   (bk,n,f)     -> trav f &~~ take1 (_Binder bk n)
                     | Tuple    fs           -> optmap_any trav fs &~~ take1 _Tuple
                     | Ite      (cf,tf,ef)   -> trav3 cf tf ef &~~ take3 _Ite
                     | Since    (hk,f1,f2)   -> trav2 f1 f2 &~~ take2 (_Since hk)
                     | Bfr      (hk,f)       -> trav f &~~ take1 (_Bfr hk)
                     | Univ     (hk,f)       -> trav f &~~ take1 (_Univ hk)
                     (* | Latest   _            -> None *)
                     | Fandw    (hk,f)       -> trav f &~~ take1 (_Fandw hk)
                     | App      (n,fs)       -> optmap_any trav fs &~~ take1 (_App n)
                     | Sofar    (hk,f)       -> trav f &~~ take1 (_Sofar hk)
                     | Ouat     (hk,f)       -> trav f &~~ take1 (_Ouat hk)
                     | Cohere   (v,f1,f2)    -> trav2 f1 f2 &~~ take2 (_Cohere v)
                     | Threaded (i,f)        -> trav f &~~ take1 (_Threaded i) 
    and trav2 f1 f2 = optionpair_either trav f1 trav f2
    and trav3 f1 f2 f3 = optiontriple_either trav f1 trav f2 trav f3
    in
    trav f
    
let filter p f = fold (fun fs f -> if p f then Some (f::fs) else None) [] f

let map ff = optmap ff ||~ id

(* mapfold in a formula. ff x f delivers Some (x, None) if x changes but f doesn't, 
                                         Some (x, Some f) if f changes (and doesn't matter x)
                                         None otherwise.
   optmapfold ff x f delivers x, None or x, Some f' -- use anyway2 to deal with it.
   Deal with it ...
 *)

let optmapfold ff x f =
  let rec ttl x f = 
    let unary f c = 
      let (x,fopt) = ttl x f in 
      x, match fopt with None -> None | Some f -> Some (c f) 
    in
    let binary f1 f2 c =  
      let (x,f1opt) = ttl x f1 in
      let (x,f2opt) = ttl x f2 in
      x, match f1opt, f2opt with
         | None, None -> None
         | _          -> Some (c (either f1 f1opt) (either f2 f2opt))
    in
    let ternary f1 f2 f3 c =  
      let (x,f1opt) = ttl x f1 in
      let (x,f2opt) = ttl x f2 in
      let (x,f3opt) = ttl x f3 in
      x, match f1opt, f2opt, f3opt with
         | None, None, None -> None
         | _                -> Some (c (either f1 f1opt) (either f2 f2opt) (either f3 f3opt))
    in
    let nary fs c = 
      let (x, fopts) = Listutils.mapfold ttl x fs in 
      x, (if not (List.exists (function (Some _) -> true | None -> false) fopts) then None 
          else Some (c (List.map (uncurry2 either) (List.combine fs fopts))))
    in
    match ff x f with
    | Some (result) -> result
    | _             -> match f.fnode with 
                       | Fint      _
                       | Fbool     _
                       | Freg      _
                       | Fvar      _            
                       | Flogc     _          -> x,None
                       | Negarith  f          -> unary f _recNegative
                       | Not       f          -> unary f negate
                       | Arith     (f1,op,f2) -> binary f1 f2 (revargs _recArith op)
                       | LogArith  (f1,op,f2) -> binary f1 f2 (revargs _recLogArith op)
                       | Compare   (f1,op,f2) -> binary f1 f2 (revargs _recCompare op)
                       | Binder    (bk,n,f)   -> unary f (_recBinder bk n)
                       | Tuple     fs         -> nary fs _recTuple
                       | Ite       (cf,tf,ef) -> ternary cf tf ef _recIte
                       | Since     (hk,f1,f2) -> binary f1 f2 (_recSince hk)
                       | Bfr       (hk,f)     -> unary f (_recBfr hk)
                       | Univ      (hk,f)     -> unary f (_recUniv hk)
                       (* | Latest    _          -> x,None *)
                       | Fandw     (hk,f)     -> unary f (_recFandw hk)
                       | App       (n,fs)     -> nary fs (_recApp n)
                       | Sofar     (hk,f)     -> unary f (_recSofar hk)
                       | Ouat      (hk,f)     -> unary f (_recOuat hk)
                       | Cohere    (v,f1,f2)  -> binary f1 f2 (_recCohere v)
                       | Threaded  (tid,f)    -> unary f (_recThreaded tid) 
  in
  ttl x f

let mapfold ff x = anyway2 (optmapfold ff) x

(* ******************************* substitution ********************************* *)

let substitute mapping orig_f =
  let rec sub_opt mapping = 
    let sub mapping f = 
      match f.fnode with
      | Freg   r               -> (try Some (Some (mapping <@> r)) with Not_found -> None)
      | Flogc  n               -> (try Some (Some (mapping <@> n)) with Not_found -> None)
      | Fvar   (None,NoHook,v) -> (try Some (Some (mapping <@> v)) with Not_found -> None)
      | Binder (bk,n,bf)       -> (sub_opt (List.remove_assoc n mapping) bf 
                                   &~~ (_Some <.> (_Some <.> rplacBinder f bk n))
                                  )
                                  |~~ (fun () -> Some None) (* leave it alone *)
      | Cohere (v,f1,f2)       -> 
          (try match mapping <@> v with
               | {fnode=Fvar(None,NoHook,v')} ->
                   Some (Some (_recCohere v' (anyway (sub_opt mapping) f1)
                                             (anyway (sub_opt mapping) f2)
                              )
                        )
               | other ->
                   raise (Substitute f)
           with Not_found -> None
          )
      | _                   -> None
    in
    optmap (sub mapping)
  in
  anyway (sub_opt mapping) orig_f

let rec reloc_opt newloc = function 
  | {fpos=spos} when spos=newloc -> (* keep going *)
      None 
  | f                            -> (* change, and force scan of subformulas *)
      Some (Some (reloc newloc {f with fpos=newloc}))
    
and stripspos_opt f = reloc_opt dummy_spos f

and optreloc newloc = optmap (reloc_opt newloc)

and reloc newloc f = (optreloc newloc ||~ id) f 

let optstripspos = optreloc dummy_spos

let stripspos = reloc dummy_spos

let eq f1 f2 = stripspos f1 = stripspos f2

(* let is_threadsavvy = 
     exists (fun f -> match f.fnode with 
                         (* what's this doing here? | Fadep(hk,_,_) -> not hk *)
                         | Univ _          -> true 
                         | Threaded _   -> true 
                         | _ -> false
               )

   let is_temporal = 
     exists (fun f -> match f.fnode with Sofar _ -> true | Ouat _ -> true | Since _ -> true | _ -> false)

   let is_coloursavvy =
     exists (fun f -> match f.fnode with
             | Red _ -> true
             (* this is probably wrong | Univ   _ -> !Settings.uimpliesprop *)
             | _     -> false
            )
 *)

(* formula free of substitution effects *)
let subst_clean f =
  let rec bad f =
    exists (fun f ->
              match f.fnode with
              | Fvar (None, NoHook, _) -> false
              | Fvar                 _ -> true
              | Bfr       (NoHook, bf) -> bad bf
              | Bfr                  _ -> true
              | Univ      (NoHook, uf) -> bad uf
              | Univ                 _ -> true
              | Fandw     (NoHook, ef) -> bad ef
              | Fandw                _ -> true
              | Since (NoHook, f1, f2) -> bad f1 || bad f2
              | Since                _ -> true
              | _                      -> false
           )
           f
  in
  not (bad f)

let is_hatted f = (* maybe this needs to look inside modalities ... *)
  match f.fnode with
  | Fvar (Some _, _, _) -> true
  | _                   -> false

let is_hooked f =
  match f.fnode with
  | Fvar      (_, Hook, _) 
  | Since     (Hook, _, _)        
  | Bfr       (Hook, _)                  
  | Sofar     (Hook, _)    
  | Ouat      (Hook, _)    
  (* | Latest    (Hook, _) *)
                            -> true
  | _                       -> false

(* *********************** free names ******************************* *)

(* After a good deal of faffing, this has gone back to the obvious. It doesn't notice
   App names: otherwise everything. Especially the v in Cohere and in latest.
 *)
let rec fof frees f =
  let optf frees f = 
    match f.fnode with
    | Freg   r              -> Some (addname r frees)
    | Fvar   (_,_,v)        -> Some (addname v frees)
    | Flogc  n              -> Some (addname n frees)
    | Binder (_,n,f)        -> let bfrees = fof NameSet.empty f in
                               Some (NameSet.union frees (subtractname n bfrees))
    | App    (_,fs)         -> Some (List.fold_left fof frees fs) 
    | Cohere (v,f1,f2)      -> Some (List.fold_left fof (addname v frees) [f1;f2])
    (* | Latest (_,_,v)        -> Some (addname v frees) *)
    | _                     -> None
  in
  (revargs (optfold optf) f ||~ id) frees

let frees = fof NameSet.empty

let freevars = NameSet.filter Name.is_anyvar <.> frees

let is_free n = NameSet.mem n <.> frees
 
let bind bk bset f = 
  let frees = frees f in
  let binders = NameSet.inter frees bset in
  if NameSet.is_empty binders then 
    f 
  else
    List.fold_left (fun f hk -> _recBinder bk hk f) 
                   f 
                   (List.rev (NameSet.elements binders)) (* rev for lexical order *)

let bindForall = bind Forall
let bindExists = bind Exists

(* formula independent of variables *)
let is_pure =
  not <.> NameSet.exists Name.is_anyvar <.> frees 

(* *********************** formula sets ******************************* *)

(* ************** sets of formulas: only safe when stripspos'd; ************
   ************** use addformula not FormulaSet.add;           ************
   ************** use memformula not FormulaSet.mem            ************ *)

module FormulaSet = MySet.Make (struct type t = formula 
                                       let compare = Pervasives.compare 
                                       let to_string = string_of_formula
                                end)

let addformula = FormulaSet.add <.> stripspos
let memformula = FormulaSet.mem <.> stripspos
