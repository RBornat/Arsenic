open Tuple
open Function
open Option
open Listutils
open Name
open Formula
open Location
open Assign

(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
(* ******************** hatting *************************
   ****************************************************** *)
   
let enhat hatting orig_f =
  let rec opt_hat f =
    match f.fnode with
    | Fvar(None,NoHook,v)     -> _SomeSome (_recFvar (Some hatting) NoHook v)
    | Bfr (None,NoHook,bf)    -> if is_Tildehatting hatting 
                                 then ohat bf &~~ (_SomeSome <.> _recBfr (Some hatting) NoHook)
                                 else _SomeSome (conjoin [f; hat bf]) (* because B(P)=>P *)
    | Univ (NoHook,uf)        -> _SomeSome (conjoin [f; hat uf])      (* because U(P)=>P *) 
    (* | Latest (None,NoHook,v)       -> if hatting=InflightHat 
                                      then _SomeSome (_recLatest There NoHook v)
                                      else Some None (* don't touch it! *)
     *)
    | Sofar (NoHook,sf)       -> _SomeSome (conjoin [f; hat sf])      (* because Sofar(P)=>P *)
    | Ouat  (None,NoHook,sf)  -> ohat sf &~~ (_SomeSome <.> _recOuat (Some hatting) NoHook) (* Ouat is local *)
    | Since (None,NoHook,f1,f2) -> optionpair_either ohat f1 ohat f2
                                 &~~ (_SomeSome <.> uncurry2 (_recSince (Some hatting) NoHook)) 
    (* we hat even inside binders. Oh yes. Because binding a variable doesn't bind thread or epoch *) 
    | Binder (bk,n,bf)
                              -> (ohat bf &~~ (_SomeSome <.> _recBinder bk n))
                                 |~~ (fun () -> Some None)
    | Fvar    _           
    | Bfr     _           
    | Univ    _        
    | Sofar   _
    | Ouat    _
    | Since   _               -> raise (Invalid_argument (Printf.sprintf "Strongestpost.enhat.opt_hat %s in %s %s" 
                                                                         (string_of_formula f)
                                                                         (string_of_hatting hatting)
                                                                         (string_of_formula orig_f)
                                                         )
                                       )
    | _                         -> None
  and ohat f = Formula.optmap opt_hat f
  and hat f = Formula.map opt_hat f
  in
  hat orig_f

(* ******************** strongest-post substitution *************************
        
    Takes an assoc list mapping, from names to formulas. 
    
    Bfr, Univ, Sofar, Ouat: 
    
        If P[mapping]=P then (M P)[mapping] = M P;
    
        (M P)[regmapping] = M (P[regmapping]);
     
        (_B P)[varmapping] = (-)_B(P)/\P[varmapping]; 
        (_U P)[varmapping] = (-)_U(P)/\P[varmapping]; 
        (_S P)[varmapping] = (-)_S(P)/\P[varmapping]; 
        (_O P)[varmapping] = (-)_O(P)\/P[varmapping];  -- or, not and
      
    Since:
      
      If P[mapping]=P and Q[mapping]=Q then (P since Q)[mapping] = P since Q
      
      (P since Q)[regmapping] = P[regmapping] since Q[regmapping]
      
      (P since Q)[varmapping = (-)(P since Q) /\ P[varmapping]
      
   ************************************************************************** *)
 
let optsp_substitute mapping orig_f =
  let isvarmapping mapping f = 
    if List.for_all (Name.is_anyvar <.> fstof2) mapping then true
    else
    if List.for_all (Name.is_anyreg <.> fstof2) mapping then false
    else
      raise (Invalid_argument ("sp_substitute [" ^ 
              string_of_assoc Name.string_of_name string_of_formula ":" "; " mapping ^ 
              "] " ^ string_of_formula orig_f ^ 
              ", which contains " ^ string_of_formula f))
  in
  let rec optsub mapping f = 
    let domodality mm condis mf =
      (subopt mapping 
       &~ (fun mf' -> 
             if isvarmapping mapping f 
             then _SomeSome (condis [mm Hook mf; mf'])
             else _SomeSome (mm NoHook mf')
          )
      ) mf
    in
    match f.fnode with
    | Freg   r                -> (try _SomeSome (mapping <@> r) with Not_found -> None)
    (* Flogc omitted deliberately: you can't assign to a logical constant *)
    (* We only substitute for unhooked variables -- None+NoHook, There+NoHook *)
    | Fvar  (None,NoHook,v)   -> (try _SomeSome (mapping <@> v) with Not_found -> None)
    | Fvar     (_,NoHook,v)   -> None (* Formula.optmap leaves it alone *)
    | Binder (bk,n,bf)        -> (subopt (List.remove_assoc n mapping) &~ (_SomeSome <.> _recBinder bk n)) bf 
                                 |~~ (fun () -> Some None) (* don't touch it! *)
    | Bfr (None,NoHook,bf)    -> domodality (_recBfr None) conjoin bf
    | Bfr (Some _,NoHook,_)   -> Some None
    | Ouat (None,NoHook, sf)  -> domodality (_recOuat None) disjoin sf
    | Ouat (Some _,NoHook,_)  -> Some None
    | Since (None,NoHook,f1,f2) -> (if isvarmapping mapping f 
                                then (* x\xhook affects only f1 *)
                                  subopt mapping f1 
                                  &~~ (fun f1' -> _SomeSome (conjoin [f; f1']))
                                else (* r\rhook affects both *)
                                  optionpair_either (subopt mapping) f1 (subopt mapping) f2
                                  &~~ (fun (f1,f2) -> _SomeSome (_recSince None NoHook f1 f2))
                               )
                               |~~ (fun () -> Some None)
    | Since (Some _,NoHook,_,_) -> Some None
    | Univ (NoHook,uf)        -> domodality _recUniv conjoin uf
    (* | Latest (pl,NoHook,v)       -> if List.mem_assoc v mapping 
                                       then _SomeSome (_recLatest pl Hook v)
                                       else Some None
     *)
    | Sofar (NoHook, sf)      -> domodality _recSofar conjoin sf
    | Fvar      _
    | Bfr       _           
    | Univ      _            
    (* | Latest    _  *)          
    | Sofar     _             
    | Ouat      _             
    | Since     _           -> raise (Invalid_argument (Printf.sprintf "sp_substitute [%s] %s, which contains %s" 
                                                                       (string_of_assoc string_of_name string_of_formula "->" ";" mapping)
                                                                       (string_of_formula orig_f) 
                                                                       (string_of_formula f)
                                                       )
                                     )
    | _                     -> None
  and subopt mapping = Formula.optmap (optsub mapping)
  in
  subopt mapping orig_f
  
let sp_substitute mapping f = 
  (optsp_substitute mapping ||~ id) f

(* strongest_post generates new names, so feels no need to use Exists *)
let strongest_post with_result pre assign = 
  let decorate f = if with_result then f else _recTrue in
  let old_name name =
    if Name.is_anyvar name then _recFvar None Hook name
                           else _recFname (name ^ "!old")
  in
  let sp_multiple is_varsubst mapping locs es = 
    let sub = sp_substitute mapping in
    (* only ns change in an is_varsubst mapping -- matters with modalities *)
    let unchanged =
      if is_varsubst then
       ((* collect modal variables *) 
        let rec vsof vset f =
          let optvs fvs f = 
            match f.fnode with
            | Fvar (None,NoHook,v) -> Some (NameSet.add v fvs)
            | Binder (_,n,f)    -> let bvs = vsof NameSet.empty f in
                                   Some (NameSet.union fvs (NameSet.remove n bvs))
            | _                 -> None
          in
          Formula.fold optvs vset f
        in 
        let mvs f =
          let optmvs fvs f =
            match f.fnode with
            | Bfr    (_,_,bf)   -> Some (vsof fvs bf)
            | Univ     (_,uf)   -> Some (vsof fvs uf)
            | Sofar    (_,sf)   -> Some (vsof fvs sf)
            | Ouat   (_,_,sf)   -> Some (vsof fvs sf)
            | Since (_,_,f1,f2) -> Some (vsof (vsof fvs f1) f2)
            | Binder  (_,n,f)   -> let bvs = vsof NameSet.empty f in
                                   Some (NameSet.union fvs (NameSet.remove n bvs))
            | _                 -> None
          in
          Formula.fold optmvs NameSet.empty f
        in
        let vars = mvs pre in
        let unchanged = NameSet.diff vars (NameSet.of_list (List.map fstof2 mapping)) in
        conjoin (List.map (fun v -> _recEqual (_recFvar None NoHook v)
                                              (_recFvar None Hook v)
                          )
                          (NameSet.elements unchanged)
                )
       )
      else _recTrue
    in
    let effect (loc,e) =
      match loc with
      | VarLoc v         -> _recEqual (_recFname v) (sub e) (* sub e for register assignments *)
    in
    conjoin (sub pre 
             :: (if !Settings.sp_unchanged then unchanged else _recTrue)
             :: List.map (decorate <.> effect) (List.combine locs es)
            )
  in
  match assign with
  | RbecomesE  (r,e)        -> sp_multiple false [r, old_name r] [VarLoc r] [e]
  | LocbecomesEs ((* b, *) loces)  -> let locs, es = List.split loces in
                               sp_multiple true (List.map (function VarLoc v         -> v, old_name v
                                                          )
                                                          locs
                                                )
                                                locs
                                                es
  | RsbecomeLocs ((* b, *) rslocs) -> let rss, locs = List.split rslocs in
                               let rs = List.concat rss in
                               let rs' = List.map old_name rs in
                               let sub = sp_substitute (List.combine rs rs') in
                               conjoin 
                                 (sub pre ::
                                  List.map (fun (rs,loc) -> 
                                              decorate (_recEqual (singleton_or_tuple (List.map _recFreg rs)) 
                                                                  (_recFloc loc)
                                                       )
                                           )
                                           rslocs
                                 )
                          