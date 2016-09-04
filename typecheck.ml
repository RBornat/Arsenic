open Function
open Option
open Tuple
open Program
open Printer
open Name
open Formula
open Location
open Assign
open Ftype
open Listutils
open Intfdesc
(* open Intfrel *)

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
exception TypeUnifyError of ftype * ftype
exception TypeCheckError of string

type ftypecxt         = (name    * ftype) list                  (* use assoc *)
type binder_tuple_cxt = (formula * ftype) list                  (* use assq *)

let new_FTypeVar () = FTypeVar (Name.new_unknown_string ())

let rec eval cxt s =
  try Some (evaltype cxt (List.assoc s cxt)) with Not_found -> None

and evaltype cxt t = 
  match t with
  | Bool 
  | Int             -> t
  | TupleType ts    -> TupleType (List.map (evaltype cxt) ts)
  | FuncType (ts,t) -> FuncType (List.map (evaltype cxt) ts, evaltype cxt t)
  | FTypeVar s      -> (try evaltype cxt (cxt <@> s) with Not_found -> t)
  | VarType t       -> VarType (evaltype cxt t)
  
let pickdiff cxt t t1 t2 = 
  let t = evaltype cxt t in
  let t1 = evaltype cxt t1 in
  let t2 = evaltype cxt t2 in
  if t=t1 then t2 else t1
  
let rec unifytype cxt t1 t2 = 
  match evaltype cxt t1, evaltype cxt t2 with
  | FTypeVar s1            , (FTypeVar s2 as t2')  -> if s1=s2 then cxt else (s1,t2')::cxt
  | FTypeVar s1 as t1'     , t2'                   -> if canunifytype s1 cxt t2' then (s1,t2')::cxt 
                                                      else raise (TypeUnifyError (t1',t2'))
  | t1'                   , (FTypeVar s2 as t2')   -> if canunifytype s2 cxt t1' then (s2,t1')::cxt 
                                                      else raise (TypeUnifyError (t1',t2'))
  | (TupleType t1s as t1'), (TupleType t2s as t2') -> 
      unifylists (TypeUnifyError (t1',t2')) cxt t1s t2s 
  | (FuncType (t1s, tr1) as t1'), 
    (FuncType (t2s, tr2) as t2')                   -> 
      let cxt = unifylists (TypeUnifyError (t1',t2')) cxt t1s t2s in
      unifytype cxt tr1 tr2 
  | t1'                   , t2'                    -> if t1'=t2' then cxt 
                                                      else raise (TypeUnifyError (t1',t2'))

and unifypair cxt (t1,t2) = unifytype cxt t1 t2

and unifylists exn cxt t1s t2s = 
  let pairs = try List.combine t1s t2s with Invalid_argument _ -> raise exn in
  List.fold_left unifypair cxt pairs
  
and canunifytype s cxt = function
  | Bool
  | Int             -> true
  | TupleType ts    -> List.for_all (canunifytype s cxt) ts
  | FuncType (ts,t) -> List.for_all (canunifytype s cxt) ts && canunifytype s cxt t
  | FTypeVar s'     -> (match eval cxt s' with
                        | None    -> s<>s'
                        | Some t' -> canunifytype s cxt t'
                       )
  | VarType t       -> canunifytype s cxt t
  
(* when you think you have a complete type context, simplify it with evalcxt. 
   Throws away FTypeVars 
 *)
let evalcxt cxt = 
  let evalpair (s,_) = (s, _The (eval cxt s)) in
  let ec = List.map evalpair cxt in
  List.filter (fun (s,_) -> s.[0]<>'?') ec

let string_of_evalcxt = string_of_ftypecxt <.> evalcxt

let rec assigntype cxt t s =
  match eval cxt s with
  | Some t' -> 
      (try unifytype cxt t t' 
       with TypeUnifyError(t1,t2) -> 
         raise (TypeCheckError (s ^ " seems to be type " ^ string_of_ftype (evaltype cxt t2) ^ 
                                " but in context has to be type " ^ string_of_ftype (evaltype cxt t1)))
      )
  | None    -> (s,t)::cxt

let rec typeassign_formula cxt bcxt t f =
  (* uncurried type_assign_formula *)
  let utaf (cxt,bcxt) (t,f) = typeassign_formula cxt bcxt t f in
  try 
    let unary cxt bcxt tout tin f = 
       let cxt = unifytype cxt t tout in
       try typeassign_formula cxt bcxt tin f 
       with TypeUnifyError (t1,t2) -> 
         raise (TypeCheckError(string_of_formula f ^ 
                    " should be " ^ string_of_ftype (evaltype cxt tin) ^ 
                    " but is actually " ^ string_of_ftype (pickdiff cxt tin t1 t2)))
     in
     let binary cxt bcxt tout tin1 tin2 f1 f2 =
       let cxt, bcxt = unary cxt bcxt tout tin1 f1 in
       unary cxt bcxt tout tin2 f2
     in
     let ternary cxt bcxt tout tin1 tin2 tin3 f1 f2 f3 =
       let cxt, bcxt = binary cxt bcxt tout tin1 tin2 f1 f2 in
       unary cxt bcxt tout tin3 f3
     in
     match f.fnode with
     | Fint              _ -> unifytype cxt t Int, bcxt
     | Fbool             _ -> unifytype cxt t Bool, bcxt
     | Freg              r -> assigntype cxt t (string_of_reg r), bcxt
     | Fvar      (_, _, v) -> (* for translation to Z3, all variable instances are typed in bcxt (see modality.ml) *)
                              assigntype cxt t (string_of_var v), (f,t)::bcxt
     (* | Latest (_, _, v)    -> assigntype cxt t (string_of_var v), (f,t)::bcxt *)
     | Flogc             n -> assigntype cxt t (string_of_logc n), bcxt
     | Negarith          f -> unary  cxt bcxt Int  Int  f 
     | Not               f -> unary  cxt bcxt Bool Bool f
     | Arith     (f1,_,f2) -> binary cxt bcxt Int  Int  Int  f1 f2
     | LogArith  (f1,_,f2) -> binary cxt bcxt Bool Bool Bool f1 f2
     | Compare (f1,cop,f2) -> (match cop with 
                                   | Equal | NotEqual ->
                                       let t = new_FTypeVar () in
                                       binary cxt bcxt Bool t t f1 f2
                                   | _ ->
                                       binary cxt bcxt Bool Int  Int  f1 f2
                                  )
     | Tuple            fs -> 
         let ts = List.map (fun _ -> new_FTypeVar ()) fs in
         let tfs = List.combine ts fs in
         let cxt',bcxt' = 
           List.fold_left utaf 
                          (cxt,(f,t)::bcxt)  (* f indexes the tuple type *)
                          tfs 
         in
         (unifytype cxt' t (TupleType ts), bcxt')
     | Binder   (_, n, f') -> 
         let s = string_of_name n in
         let tv = new_FTypeVar () in
         let cxt, bcxt = 
           unary ((s,tv)::cxt)          (* with a mapping for n *)
                 ((f,tv)::bcxt)         (* f indexes the type of n in bcxt *)
                 Bool Bool f' in
         List.remove_assoc s cxt,       (* remove the outermost one *)
         bcxt 
     | Sofar            (_,f) 
     | Ouat           (_,_,f) -> unary cxt bcxt Bool Bool f
     | Since      (_,_,f1,f2) -> binary cxt bcxt Bool Bool Bool f1 f2
     | Ite         (cf,tf,ef) -> ternary cxt bcxt t Bool t t cf tf ef
     | Cohere (v,f1,f2)       -> let cxt = unifytype cxt t Bool in
                                 let cxt, tv = typeassign_var cxt v in
                                 let cxt, bcxt = typeassign_formula cxt ((f,tv)::bcxt) tv f1 in
                                 typeassign_formula cxt bcxt tv f2
     | App (n,[{fnode=Fvar(_,_,v)} as var])
       when n = Formula.coherevar_token ->
         utaf (cxt,bcxt) (new_FTypeVar(),var) (* we don't type the cv function *)
     | App          (n,fs)  ->
         let ts = List.map (fun _ -> new_FTypeVar ()) fs in
         List.fold_left utaf 
                        (assigntype cxt (FuncType(ts,t)) (string_of_name n), bcxt) 
                        (List.combine ts fs)
     | Bfr      (_,_,bf)    -> unary cxt bcxt Bool Bool bf
     | Univ        (_,f)    -> unary cxt bcxt Bool Bool f
     | Fandw       (_,f)    -> unary cxt bcxt Bool Bool f
     | Threaded(_,f)        -> typeassign_formula cxt bcxt t f
with 
  | TypeCheckError s        -> raise (TypeCheckError (s ^ " (in context " ^ string_of_formula f ^ ")"))
  
and typeassign_var cxt v =
  try cxt, cxt <@> v with Not_found -> let t = new_FTypeVar () in (v,t)::cxt, t
    
let permissible_regtypes = [Bool; Int]

(* let completed_typeassign_formula cxt bcxt t f =
   let cxt, bcxt = typeassign_formula cxt bcxt Bool f in
   let types = evalcxt cxt in
   let binders = List.map (fun (f,t) -> (f, evaltype cxt t)) bcxt in
   (* the Z3 client of this thing gets very confused if there are remaining FTypeVars in
      binders. So we get rid of them. According to the client it is ok if we replace them with
      Int. So we do that.
    *)
   print_string ("\nbinders before processing = " ^ string_of_binder_ftypecxt binders);
   let binders = 
     List.map (fun (f,t) -> f, Ftype.map (function FTypeVar _ -> Some Int | _ -> None) t) binders 
   in
   (* nobody likes registers of complex types *)
   List.iter 
     (fun (n,t) -> 
        if Name.isanyreg n && not (List.mem t permissible_regtypes) then
          raise 
            (TypeCheckError 
               (Printf.sprintf "register %s is type %s in formula %s;\n    -- registers must be %s"
                               (Name.string_of_name n) (string_of_ftype t) (string_of_formula f)
                               (Listutils.phrase_of_list ", " " or " string_of_ftype permissible_regtypes)
               )
            )
     )
     types;
   print_string ("\nbinders after processing = " ^ string_of_binder_ftypecxt binders);
   types, binders *)


let completed_typeassign_formula_list cxt bcxt t fs =
   let cxt, bcxt = 
     List.fold_left (fun (cxt,bcxt) -> typeassign_formula cxt bcxt t) (cxt,bcxt) fs 
   in
   let types = evalcxt cxt in
   let binders = List.map (fun (f,t) -> (f, evaltype cxt t)) bcxt in
   (* the AskZ3 client of this thing gets very confused if there are remaining FTypeVars in
      binders. So we get rid of them. According to the client it is ok if we replace them with
      Int. So we do that.
    *)
   let resolve_typevars cxt =
     List.map (fun (f,t) -> f, Ftype.map (function FTypeVar _ -> Some Int | _ -> None) t) cxt
   in
   (* if !Settings.verbose then
        print_string ("\ncompleted_typeassign_formula_list formulas = \n\t" ^
                      string_of_list string_of_formula "\n\t" fs ^
                      "\ntypes = " ^ string_of_ftypecxt types ^
                      "\nbinders = " ^ string_of_binder_ftypecxt binders ^ 
                      "\ntypes after processing = " ^ string_of_ftypecxt (resolve_typevars types) ^
                      "\nbinders after processing = " ^ string_of_binder_ftypecxt (resolve_typevars binders)); 
    *)
   resolve_typevars types, resolve_typevars binders

let typeassign_loc cxt bcxt = function
  | VarLoc v         -> let cxt, t = typeassign_var cxt v in (cxt, bcxt), t

let typeassign_assign cxt bcxt a =
  let doit cxt bcxt loc fs = 
    let (cxt, bcxt), t = typeassign_loc cxt bcxt loc in
    typeassign_formula cxt bcxt t (singleton_or_tuple fs)
  in
  match a with 
  | RbecomesE (r,e)         -> doit cxt bcxt (VarLoc r) [e] (* cheat *)
  | LocbecomesEs ((* b, *) loces)  -> 
      List.fold_left (fun (cxt,bcxt) (loc,e) -> doit cxt bcxt loc [e])
                     (cxt,bcxt) 
                     loces
  | RsbecomeLocs ((* b, *) rslocs) -> 
      List.fold_left (fun (cxt,bcxt) (rs,loc) -> doit cxt bcxt loc (List.map _recFreg rs))
                     (cxt,bcxt) 
                     rslocs

(* todo later ...
   let rec typeassign_intfformula cxt bcxt r =
     let dolist = List.fold_left (uncurry2 typeassign_intfformula) (cxt,bcxt) in
     match r with
     | IntersectIntf rs                     -> dolist rs 
     | UnionIntf     rs                     -> dolist rs 
     | SingTopIntf  vs                      -> cxt,bcxt
     | SingIntf      i                      -> 
         let cxt,bcxt = typeassign_formula cxt bcxt Bool i.i_pre in
         let cxt,bcxt = typeassign_formula cxt bcxt Bool i.i_after in
         typeassign_assign cxt bcxt (Intfdesc.assign i.i_ves)
     | intfrel                          -> 
         raise (Invalid_argument ("typeassign_intfformula " ^ string_of_intfformula intfrel))

   let typeassign_intfquery rq = 
     let dopair r1 r2 = List.fold_left (uncurry2 typeassign_intfformula) ([],[]) [r1;r2] in
     match rq with
     | EqualIntf    (r1,r2) -> dopair r1 r2  
     | IncludedIntf (r1,r2) -> dopair r1 r2
 *)
