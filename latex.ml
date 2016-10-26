open Function
open Tuple
open Option
open Listutils
open Sourcepos
open Name
open Formula
open Node
open Stitch
open Knot
open Location
open Assign
open Com
open Intfdesc
open Thread
open Program

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
(* ************************************************************************************ *
 *                                                                                      *
 *  This is a mess, very ad hoc, and it only just works. Well it sometimes doesn't      *
 *  work -- it puts a semicolon after \scloc, for example, and it puts \ before a       *
 *  command that doesn't have a knot. But it's bearable, and I've wasted too much       *
 *  of my life trying to fix it.                                                        *
 *                                                                                      *
 * ************************************************************************************ *)

exception Error of string

let macros = ref NameSet.empty

let latexnl = "\\\\"
let latexcolon = "::"

let latexarg arg =
  Printf.sprintf "{%s}" arg
  
let latexcommand command optarg args =
  Printf.sprintf "\\%s%s%s"
                 command
                 (match optarg with None -> "" | Some arg -> Printf.sprintf "[%s]" arg)
                 (string_of_list latexarg "" args)

let latexenv is_begin name optarg =
  Printf.sprintf "\\%s%s%s"
    (if is_begin then "begin" else "end")
    (latexarg name)
                 (match optarg with None -> "" | Some arg -> Printf.sprintf "[%s]" arg)

(* ********************** command-line options ************************************* *)

type lacing =
  | NoLace
  | Laced
  | Embroider
  
let twocols = ref false
let lacing = ref Embroider

let nolace () = lacing:=NoLace
let laceonly () = lacing:=Laced
let embroider () = lacing:=Embroider

let use_cols () =
  match !twocols, !lacing with
  | true, Laced
  | true, Embroider -> true
  | _               -> false

let aux = ref true

let show_aux () =
  !aux || !lacing = Embroider

let is_aux_assign_map = ref (Node.NodeMap.empty: bool NodeMap.t)
let init_lab = ref ""

let scan_for_aux_assign seq =
  is_aux_assign_map := Node.NodeMap.empty;
  let do_node n b = 
    is_aux_assign_map := NodeMap.add n b !is_aux_assign_map 
  in
  let rec sfaa com =
    let do_sct sct =
      let lab = sct.tripletlab.lablab in
      do_node (Cnode lab) (Com.is_aux_assign sct)
    in
    let do_condition c =
      match c with
      | CAssign sct -> do_sct sct
      | CExpr   ft  -> let lab = ft.tripletlab.lablab in
                       do_node (CEnode (lab,true)) false;
                       do_node (CEnode (lab,false)) false;
    in
    match com with
    | Com sct      -> do_sct sct
    | Structcom sc ->
       (match sc.structcomnode with
        | If (c,s1,s2)  -> do_condition c; do_seq s1; do_seq s2
        | While (c,s)   -> do_condition c; do_seq s
        | DoUntil (s,c) -> do_seq s; do_condition c 
       )
  and do_seq s = List.iter sfaa s 
  in
  do_node (Cnode !init_lab) false;
  do_seq seq

let rec aux_filter_seq seq =
  (* actually a kind of fold *)
  let afs cs c =
    match c with
    | Com sct      -> if Com.is_aux_assign sct then cs else c::cs
    | Structcom sc ->
       let do_sc scn = Structcom (structcomadorn sc.structcompos scn) in
       (match sc.structcomnode with
        | If (c,s1,s2)  -> do_sc (If (c, aux_filter_seq s1, aux_filter_seq s2))
        | While (c,s)   -> do_sc (While (c, aux_filter_seq s))
        | DoUntil (s,c) -> do_sc (DoUntil (aux_filter_seq s, c))
       )::cs
  in
  if show_aux() then seq else List.rev (List.fold_left afs [] seq)

let aux_filter_knot knot =
  let is_aux_stitch stitch =
    let source = source_of_stitch stitch in
    try not (NodeMap.find source !is_aux_assign_map)
    with Not_found -> raise (Error (string_of_node source ^ " not in aux_assign_map"))
  in
  if show_aux() then knot else Knot.filter is_aux_stitch knot

let twocolopt = Some ("r@" ^ latexarg (latexcommand "intfspace" None []) ^ "l")

let colsep sep indent = sep ^ " " ^ latexnl ^ "\n" ^ indent

let cols optarg string_of sep indent cs =
  String.concat ("\n" ^ indent)
   [latexcommand "cols" optarg [];
    string_of_list string_of (colsep sep indent) cs;
    latexcommand "sloc" None []
   ]
    
let multicol s = 
  if use_cols() then
    latexcommand "multicolumn" None ["2"; "l"; s]
  else s

let snamemap = ref (Name.NameMap.empty : Name.name NameMap.t)
let snamesource = ref ""
let snametarget t =
  let s = !snamesource in
  snamemap := NameMap.add s t !snamemap

let labmap = ref (Name.NameMap.of_assoc [("aa", "init" ); ("zz", "final"); 
                                         ("bb", "beta" ); ("cc", "gamma");
                                         ("dd", "delta")
                                        ]: Name.name NameMap.t
                 )

let labsource = ref ""
let labtarget t =
  let s = !labsource in
  labmap := NameMap.add s t !labmap

module IntMap = MyMap.Make (struct type t = int
                                   let compare = Pervasives.compare
                                   let to_string = string_of_int
                            end
                           )

let tnamemap = ref (IntMap.empty : string IntMap.t)
let tnamesource = ref 0
let tnametarget t =
  let i = !tnamesource in
  tnamemap := IntMap.add i t !tnamemap

(* ******************************** names ************************************* *)

let sname s =
  Printf.sprintf "\\<%s>" s
  
let latex_of_name s =
  try sname (NameMap.find s !snamemap)
  with Not_found -> if String.length s>1 then sname s else s
                    (* if NameSet.mem s !macros then sname s else s *)
  
let latex_sofirst string_of = function 
  | None   -> None
  | Some f -> Some (string_of f)

let latex_solast = latex_sofirst
  
let latex_sofirst_list string_of xs =
  match xs with 
  | [] -> None 
  | xs -> Some (string_of xs)

let latex_solast_list = latex_sofirst_list

let latex_of_label l =
  try sname (NameMap.find l !labmap)
  with Not_found -> sname ("lab" ^ l)

let thread_name i =
  try 
    Printf.sprintf "%s (%d)" (IntMap.find i !tnamemap) i
  with Not_found -> Printf.sprintf "Thread %d" i
  
let vspace k =
  latexcommand "vspace" None [Printf.sprintf "%dpt" k]

(* ******************************** formulas ************************************* *)

let latex_of_arithop = function
  | Plus    -> "+"
  | Minus   -> "-"
  | Times   -> "*"
  | Div     -> "/"
  | Mod     -> "\\%"

let latex_of_logop = function
  | And     -> "@"
  | Or      -> "|"
  | Implies -> "=>"
  | Iff     -> "<=>"

let latex_of_compareop = function
  | Less            -> "<"
  | LessEqual       -> "<="
  | Equal           -> "="
  | NotEqual        -> "!="
  | GreaterEqual    -> ">="
  | Greater         -> ">"
  
let latex_of_bkind = function
  | Forall -> "@*"
  | Exists -> "|*"

let latex_of_bool = sname <.> string_of_bool

let pmsc_colon = ":::"

let latex_of_reg r = 
  if Stringutils.ends_with r "_" then "\\_"
  else sname r

let latex_of_var v =
  latex_of_name v

let latex_of_logc v =
  if Name.is_pmsc v then
    let tnum, r = Name.pmsc_parts v in
    "(" ^ tnum ^ pmsc_colon ^ latex_of_reg r ^ ")"
  else latex_of_name v

let rec formulaprio f =
  let default () = Formula.formulaprio f in
  match f.fnode with
  | Tuple fs -> if not (show_aux()) then formulaprio (List.hd fs) else default()
  | _        -> default()

let rec latex_of_primary f =
  let latex_of_app name args =
    Printf.sprintf "%s(%s)" name args
  in
    match f.fnode with
    | Fint   i             -> i
    | Fbool  b             -> latex_of_bool b
    | Freg   r             -> latex_of_reg r
    | Fvar   (_,_,v)       -> latex_of_var v
    | Flogc  n             -> latex_of_logc n
    | Negarith f'          -> "-" ^ latex_of_primary f'
    | Not    f'            -> "!" ^ latex_of_primary f'
    | Ite (cf,tf,ef)       -> sname "if"     ^ " " ^ latex_of_formula cf
                              ^ " " ^ sname "then" ^ " " ^ latex_of_formula tf
                              ^ " " ^ sname "else" ^ " " ^ latex_of_formula ef
                              ^ " " ^ sname "fi"
    | Bfr (_,_,f)          -> latex_of_app (sname "Bfr")     (latex_of_formula f)
    | Univ   (_,f)         -> latex_of_app (sname "U")       (latex_of_formula f)
    | Fandw    (_,f)         -> latex_of_app (sname "Fandw")     (latex_of_formula f)
    | Sofar (_,f)        -> latex_of_app (sname "sofar")   (latex_of_formula f)
    | Ouat  (_,_,f)        -> latex_of_app (sname "ouat")   (latex_of_formula f)
    | App (n,fs)           -> latex_of_app (latex_of_name n) (latex_of_args fs)
    | Cohere (v,f1,f2)     -> latex_of_app (latex_of_var v ^"_{c}") (latex_of_args [f1;f2])
    (* | Latest _             -> raise (Error "latest not supported. Sorry") (*latex_of_app (sname "latest") (latex_of_var v)*) *)
    | _                    -> bracketed_latex_of_formula f

and bracketed_latex_of_formula f = Printf.sprintf "(%s)" (latex_of_formula f)

and latex_of_args args = 
  let _, commaprio = commaprio in
  let f arg =
    let _, argprio = formulaprio arg in
    if argprio>commaprio then latex_of_formula arg
                         else bracketed_latex_of_formula arg
  in
  string_of_list f "," args
  
and latex_of_formula f = 
  match f.fnode with
  | Fint         _ 
  | Fbool        _ 
  | Freg         _ 
  | Fvar         _ 
  | Flogc        _ 
  | Negarith     _ 
  | Not          _
  | Ite          _
  | Sofar        _ 
  | Ouat         _ 
  | Cohere       _             
  | App          _  
  | Bfr          _              
  | Univ         _              
  | Fandw        _
  (* | Latest       _   *)           
                                -> latex_of_primary f
  | Arith   (left, aop, right)  -> latex_of_binary_formula left right (latex_of_arithop   aop) (arithprio aop)
  | Compare (left, cop, right)  -> latex_of_binary_formula left right (latex_of_compareop cop) (compprio cop)
  | LogArith(left, lop, right)  -> 
      (match compare_shorthand f with
       | Some (_,_,cseq)        -> latex_of_cseq cseq
       | None                   -> latex_of_binary_formula left right (latex_of_logop     lop) (logprio lop)
      )
  | Since   (_, _, left, right)    -> latex_of_binary_formula left right (" " ^ sname "since" ^ " ") (formulaprio f)
  | Binder (bk, n, f)           -> 
      let ns, f = multibind bk [n] f in
      Printf.sprintf "%s%s(%s)"
            (latex_of_bkind bk)
            (match ns with 
             | [n] -> Printf.sprintf " %s " (latex_of_name n)
             | _   -> Printf.sprintf "(%s)" (string_of_list latex_of_name "," ns) 
            )
            (latex_of_formula f)
  | Tuple fs                    -> if not (show_aux()) then latex_of_formula (List.hd fs)
                                   else latex_of_args fs
  | Threaded (i,tf)             -> let lff = bracket_left (formulaprio tf) (formulaprio tf)  in
                                   lff f ^ "@@@@" ^ string_of_int i                                   

and bracket_left lprio fprio = if mustbracket_left lprio fprio then bracketed_latex_of_formula 
                                                               else latex_of_formula

and bracket_right fprio rprio = if mustbracket_right fprio rprio then bracketed_latex_of_formula
                                                                 else latex_of_formula

and latex_of_binary_formula left right opstr opprio =
  let lprio = formulaprio left in
  let leftf = bracket_left lprio opprio in
  let rprio = formulaprio right in
  let rightf = bracket_right opprio rprio in
  leftf left^opstr^rightf right

and latex_of_cseq = function
  | (left,cop,right) :: []   ->
      latex_of_binary_formula left right (latex_of_compareop cop) (compprio cop)
  | (left,cop,_    ) :: cseq ->
      (* do the first half of latex_of_binary_formula. Whahey! *)
      let opprio = compprio cop in
      let lprio = formulaprio left in
      let leftf = bracket_left lprio opprio in
      leftf left ^ latex_of_compareop cop ^ latex_of_cseq cseq
      
  | _                        -> 
      raise (Error "latex_of_cseq sees []")

let latex_of_location = function
  | VarLoc v         -> latex_of_var v
  
(* ******************************** commands ************************************* *)

let latex_of_node = function
  | Cnode  l     -> latex_of_label l
  | CEnode (l,b) -> Printf.sprintf "%s_{%s}"
                        (latex_of_label l)
                        (if b then "t" else "f")

(* I doubt if this is right in complicated circumstances *)
let latex_of_stitch { stitchorder      = order; 
                      stitchsource     = source;
                      (* stitchlocopt     = locopt;
                       *)
                      stitchspopt      = spopt; 
                      stitchembroidery = assertion 
                    } =
 let spstuff =
      match !lacing, spopt with
      | Embroider, Some f -> Printf.sprintf " \\{%s\\}" (latex_of_formula f)
      | _                 -> ""
  (*   | Embroider, Some (SpostSimple f        ) -> Printf.sprintf " \\{%s\\}" (latex_of_formula f)
       | Embroider, Some (SpostRes fres        ) -> Printf.sprintf " \\{ *:%s\\}" (latex_of_formula fres)
       | Embroider, Some (SpostDouble (f, fres)) -> Printf.sprintf " \\{%s; *:%s\\}" (latex_of_formula f) (latex_of_formula fres)
   *)
  in
  let trailer =
    match !lacing with 
    | Embroider -> Printf.sprintf ": %s" (latex_of_formula assertion)
    | _         -> ""
  in
  Printf.sprintf "%s %s%s%s" 
                 (sname (Order.string_of_order order))
                 (latex_of_node source)
                 (* (match locopt with
                     | None     -> ""
                     | Some loc -> Printf.sprintf "*%s" (latex_of_location loc)
                    )
                  *)
                 spstuff
                 trailer

let knotdisjunction = latex_of_logop Or
let knotconjunction = latex_of_logop And
let knotalt         = "|>" 

let latex_of_knot =
  let rec lok knot =
    match knot.knotnode with
    | SimpleKnot stitches -> 
        latexcommand "assertd" None [string_of_list latex_of_stitch ";" stitches]
    | KnotAnd     (k1,k2) -> bok knot k1 ^ " " ^ knotconjunction ^ " " ^ bok knot k2
    | KnotOr      (k1,k2) -> bok knot k1 ^ " " ^ knotdisjunction ^ " " ^ bok knot k2
    | KnotAlt     (k1,k2) -> bok knot k1 ^ " " ^ knotalt         ^ " " ^ bok knot k2
  and bok parent knot =
    match knot.knotnode, parent.knotnode with
    | SimpleKnot _, _          
    | KnotAnd _   , _
    | KnotOr  _   , KnotOr _ -> lok knot
    | _                      -> "(" ^ lok knot ^ ")"
  in
  lok <.> aux_filter_knot

let latex_of_assign a =
  let soa lhs rhs = lhs ^ (string_of_assignop ()) ^ rhs in
  match a with
  | RbecomesE (r,f) -> soa (latex_of_reg r) (latex_of_formula f)
  | LocbecomesEs (loces) ->
      ( (* let op = if b then StoreConditional else LocalAssign in *)
       match loces with
       | [loc,e] ->
           let rhs =
             match show_aux(), e.fnode with
             | false, Tuple (e::_) -> e
             | _                   -> e
           in
           soa (latex_of_location loc) (latex_of_formula rhs)
       | _     ->
           let locs, es = List.split loces in
           let string_of_rhs e =
             match show_aux(), e.fnode with
             | false, Tuple (e::_) -> latex_of_formula e
             | true, Tuple _       -> "(" ^ latex_of_formula e ^ ")"
             | _                   -> latex_of_formula e
           in
           soa (if show_aux() 
                then string_of_list latex_of_location "," locs
                else latex_of_location (List.hd locs)
               ) 
               (if show_aux() 
                then string_of_list string_of_rhs "," es
                else string_of_rhs (List.hd es)
               )
      )
  | RsbecomeLocs (rslocs) -> 
      ( (* let op = if b then LoadReserve else LocalAssign in *)
       match rslocs with
       | [rs,loc] ->
           let lhs =
             match show_aux(), rs with
             | false, r::_ -> [r]
             | _           -> rs
           in
           soa (string_of_list latex_of_reg "," lhs) (latex_of_location loc)
           
       | _      ->
           let rss, locs = List.split rslocs in
           let string_of_lhs rs =
             match rs with
             | [r] -> latex_of_reg r
             | _   -> "(" ^ string_of_list latex_of_reg "," rs ^ ")"
           in
           soa (string_of_list string_of_lhs "," rss) (string_of_list latex_of_location "," locs)
      )

let lot lok sep latex_of_alpha {tripletknot=knot; tripletlab=lab; tripletof=alpha} =
  let header = 
    if !lacing=NoLace then "" else
      Printf.sprintf "%s%s" 
      (match knot.knotnode with
       | SimpleKnot [] -> ""
       | _             -> lok knot
      )  
      sep        
  in
  Printf.sprintf "%s%s%s %s"
      header
      (latex_of_label lab.lablab) 
      latexcolon 
      (latex_of_alpha alpha) 

let latex_of_triplet sep latex_of_alpha = lot latex_of_knot sep latex_of_alpha

let latex_of_simplecom sc = 
  match sc.sc_node with
  | Skip     -> sname "skip"
  | Assert f -> latexcommand "assertcom" None [latex_of_formula f]
  | Assign a -> latex_of_assign a

let rec latex_of_comtriplet trisep ct =
  let ipre, ipre_sep = 
    match use_cols(), !lacing, ct.tripletof.sc_ipreopt with
    | true, Embroider, Some pre           -> 
        latexcommand "ipre" None [latex_of_formula pre], " & \\\\ "
    (* | true, Embroider, Some (IpreSimple pre)           -> 
        latexcommand "ipre" None [latex_of_formula pre], " & \\\\ "
       | true, Embroider, Some (IpreRes preres)           -> 
           latexcommand "ipreres" None [latex_of_formula preres], " & \\\\ "
       | true, Embroider, Some (IpreDouble (pre, preres)) -> 
           latexcommand "ipredouble" None [latex_of_formula pre; latex_of_formula preres],
           " & \\\\ "
     *)
    | _                                                -> "", ""
  in
  lot (fun k -> string_of_pair latex_of_knot id ipre_sep (k, ipre))
      trisep
      latex_of_simplecom 
      ct
  
and latex_of_com trisep indent ct = 
  match ct with
  | Com c         -> latex_of_comtriplet trisep c
  | Structcom sc  -> latex_of_structcom trisep indent sc

and latex_of_structcom trisep indent sc = 
  let sep = " " ^ latexnl ^ "\n" ^ indent in
  let lis s = 
    latexcommand "pindent" None [] ^ latex_of_seq true trisep  (indent ^ "  ") s
  in
  match sc.structcomnode with 
  | If (c,s1,[])        -> String.concat sep 
                            [sname "if" ^ " " ^ latex_of_condition c ^ 
                                       " " ^ sname "then";
                             lis s1;
                             sname "fi"
                            ]
  | If (c,s1,s2)        -> String.concat sep 
                            [sname "if" ^ " " ^ latex_of_condition c ^ 
                                       " " ^ sname "then";
                             lis s1;
                             sname "else";
                             lis s2;
                             sname "fi"
                            ]
  | While (c,s)         -> String.concat sep 
                            [sname "while" ^ " " ^ latex_of_condition c ^ 
                                       " " ^ sname "do";
                             lis s;
                             sname "od"
                            ]
  | DoUntil (s,c)       -> String.concat sep 
                            [sname "do";
                             lis s;
                             sname "until" ^ " " ^ latex_of_condition c 
                            ]

and latex_of_condition c =
  match c with
  | CExpr   ft -> latex_of_triplet " " latex_of_formula ft
  | CAssign ct -> latex_of_triplet " " latex_of_simplecom ct
  
and latex_of_seq withcols trisep indent cs =
  let rec lsq cs =
    (* it appears to be necessary to line things up _locally_ -- i.e. sequences of comtriplets *)
    let rec swt scoms cs =
      match cs with
      | c::cs' when is_simplecom c -> swt (c::scoms) cs'
      | _                          -> List.rev scoms, cs
    in
    match use_cols(), swt [] cs with
    | true, ((_::_::_) as scoms, cs') ->
        ("\\!\\!" ^ cols twocolopt (latex_of_com " & " indent) ";" indent scoms) :: lsq cs'
    | _                               -> 
        (match cs with
         | []      -> []
         | c::cs   -> latex_of_com trisep indent c :: lsq cs
        )
  in
  match lsq cs with
  | _::_::_ as ss -> if withcols then cols None id ";" indent ss
                                 else String.concat (colsep ";" indent) ss
  | [s]           -> s
  | []            -> ""
  

(* ******************************** interference ************************************* *)

let latex_of_binders binders =
  match NameSet.elements binders with 
  | [] -> None
  | ns -> Some (string_of_list string_of_name "," ns)
  
let latex_of_intfdesc c intfdesc = 
  let i = intfdesc.irec in
  latexcommand ("interference" ^ c) 
               (latex_of_binders  i.i_binders)
               [latex_of_formula  i.i_pre;
                latex_of_assign i.i_assign
               ]


(* ******************************** thread ************************************* *)

let filteropt indent rs = 
  let rs = List.filter Option.bool_of_opt rs in
  List.map (fun r -> indent ^ _The r) rs

let latex_of_relyentry (iopt, intfdesc) = 
  (match iopt with 
   | Some i -> string_of_int (-i) ^": "
   | None   -> ""
  ) ^
  latex_of_intfdesc "g" intfdesc 

let latex_of_relypart = function
  | [] -> latexcommand "emptyrely" None []
  | rs -> latexcommand "rely" None [string_of_list latex_of_relyentry ("; " ^ latexnl ^ " ") rs]

let latex_of_macro m ps f = 
  macros := NameSet.add m !macros;
  latexcommand "macro" (match ps with 
                         | [] -> None 
                         | _  -> Some ("(" ^ string_of_list latex_of_name "," ps ^ ")")
                        )
                        [sname m; latex_of_formula f]

type thread_wrapper = 
  | Numbered of int
  | UnNumbered
  | TMacroed
  
let latex_of_thread wrapper {t_hdrs=headers; t_body=body; t_postopt=postopt; t_trlrs=trailers} =
  let latex_of_header = function
    | MacroHdr (m,ps,f)  -> latex_of_macro m ps f
    | GuarHdr   gs       -> 
        (match gs with
         | [] -> latexcommand "emptyguarantee" None [] 
         | _  -> latexcommand "guarantee" None 
                              [string_of_list (latex_of_intfdesc "g") ("; " ^ latexnl ^ " ") gs]
        ) ^ " " ^ vspace 3
    | TMacroHdr _      -> raise (Error ("thread has 'tmacro' header"))
    | GivenHdr  _      -> raise (Error ("thread has 'given' header"))
    | AssertHdr _      -> raise (Error ("thread has initial assert header"))
    | RelyHdr   _      -> raise (Error ("thread has 'rely' header"))
  in
  let embroider s =
    if !lacing<>Embroider then None else Some s
  in
  let headers = List.map (embroider <.> latex_of_header) headers in
  let thr, rht, trisep =
    match !twocols, !lacing with
    | true , Laced
    | true , Embroider   -> "lthr", "rhtl", "\\ "              
    | _    , NoLace      -> "thr" , "rht" , ""                 
    | _                  -> "thr" , "rht" , " " ^ latexnl ^ " \\quad "
  in
  let indent, opener, closer =
    match wrapper with 
    | UnNumbered -> "" , 
                    latexcommand "thr" None [""], 
                    latexcommand "rht" None []
    | Numbered i -> "  ", 
                    latexcommand "thr" None [thread_name i], 
                    latexcommand "rht" None []
    | TMacroed   -> "", "", ""
  in
  let bstring1, bstring2 =
    match body with
    | Threadseq []  -> None, None
    | Threadseq seq -> 
        scan_for_aux_assign seq;
        Some (latex_of_seq false trisep indent (aux_filter_seq seq)),
        (latex_solast latex_of_knot postopt &~~ embroider)
    | Threadfinal f -> Some (latexcommand "assert" None [latex_of_formula f]),
                       None
  in
  let latex_of_trailer = function
    | MacroHdr (m,ps,f)  -> latex_of_macro m ps f
    | RelyHdr   rs       -> 
        (match rs with
         | [] -> latexcommand "emptyrely" None [] 
         | _  -> latexcommand "rely" None 
                              [string_of_list (latex_of_intfdesc "g") ("; " ^ latexnl ^ " ") rs]
        ) ^ " " ^ vspace 3
    | TMacroHdr _      -> raise (Error ("thread has 'tmacro' trailer"))
    | GuarHdr   _      -> raise (Error ("thread has 'guarantee' trailer"))
    | GivenHdr  _      -> raise (Error ("thread has 'given' trailer"))
    | AssertHdr _      -> raise (Error ("thread has assertion trailer"))
  in
  let middle =
     (String.concat (" " ^ vspace 3 ^ " " ^ latexnl ^ "\n") <.> filteropt indent)
       (headers @ (bstring1 :: bstring2
                   :: List.map (embroider <.> latex_of_trailer) trailers
                  )
       )
  in
  match middle with
  | "" -> ""
  | _  -> String.concat "\n" [opener; middle; closer]

let latex_of_numberedthread (n,t) =
  latex_of_thread (Numbered n) t
  
let latex_of_tmacro m ps t = 
  macros := NameSet.add m !macros;
  latexcommand "tmacro" (match ps with 
                         | [] -> None 
                         | _  -> Some ("(" ^ string_of_list latex_of_name "," ps ^ ")")
                        )
                        [sname m; latex_of_thread TMacroed t]

(* ******************************** program ************************************* *)

let latex_of_given f = latexcommand "given" None [latex_of_formula f]

let latex_of_outerassert init (poslab, f) =
  latexcommand "assert" None [latex_of_label poslab.lablab ^ latexcolon ^ latex_of_formula f] ^
  (if init then " " ^ vspace 3 else "")

let latex_of_program filename {p_hdrs=headers; p_ts = ts; p_postopt=postopt } =
  let latex_of_header = function
  | AssertHdr (poslab, f) -> init_lab := poslab.lablab; latex_of_outerassert true (poslab, f)
  | GivenHdr  g           -> latexcommand "given" None [latex_of_formula g]
  | MacroHdr (m,ps,f)     -> latex_of_macro m ps f
  | TMacroHdr (m,ps,t)    -> latex_of_tmacro m ps t
  | GuarHdr   _           -> raise (Error ("program has guarantee header"))
  | RelyHdr   _           -> raise (Error ("program has rely header"))
  in
  macros := NameSet.empty;
  let headers = List.map latex_of_header headers in
  let progmacros = !macros in
  let spacer =
    match postopt with 
    | None   -> "" 
    | Some _ -> " " ^ vspace 3
  in
  let tstring = 
    match ts with
    | []  -> None
    | [t] -> Some (latex_of_thread UnNumbered t ^ spacer)
    | _   -> 
        let tstrings = 
          List.map (fun nt -> macros:=progmacros; latex_of_numberedthread nt) 
                   (numbered ts) 
          in
        match List.filter (not <.> Stringutils.is_empty) tstrings with 
        | []        -> None
        | [tstring] -> Some tstring
        | tstrings  ->
            let bcols = List.map (fun _ -> "l") tstrings in
            Some (String.concat "\n"
                  [latexcommand "BRA" (Some (String.concat "||" bcols)) [];
                   String.concat "\n&\n" tstrings;
                   latexcommand "KET" None []
                  ] ^ spacer
                 )
  in
  "% " ^ filename ^ "\n" ^
  "$$" ^
  cols (Some "c") id "" ""
    (headers @ filteropt ""
              [tstring;
               latex_solast (latex_of_outerassert false) postopt
              ]
    ) ^
  "$$"

