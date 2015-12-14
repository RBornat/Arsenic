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
 
(* ******************** strongest-post substitution *************************
        
    Takes an assoc list mapping, from names to formulas. 
    
    Bfr, Univ, Sofar: 
    
        If P[mapping]=P then (M P)[mapping] = M P;
    
        (M P)[regmapping] = M (P[regmapping]);
     
        (B P)[varmapping] = (-)B(P)/\P[varmapping]; 
        (U P)[varmapping] = (-)U(P)/\P[varmapping]/\hat(P); 
        (S P)[varmapping] = (-)S(P)/\P[varmapping]; 
      
    Since:
      
      If P[mapping]=P and Q[mapping]=Q then (P since Q)[mapping] = P since Q
      
      (P since Q)[regmapping] = P[regmapping] since Q[regmapping]
      
      (P since Q)[varmapping = (-)(P since Q) /\ P[varmapping]
      
   ************************************************************************** *)

let hatted bfr_too orig_f=
  let rec opt_hat binders f =
    match f.fnode with
    | Fvar(Here,Now,v)          -> if NameSet.mem v binders then None else Some (_recFvar There Now v)
    | Bfr(Here,Now,bf)          -> if bfr_too then Some (_recBfr There Now bf)
                                   else Some f (* don't touch it! *) 
    | Univ (Now,_)              -> Some f (* don't touch it! *)
    | Latest (Here,Now,v,lf)    -> Some (_recLatest There Now v (anyway (ohat binders) lf))
    | Sofar (Here,Now,sf)       -> Some (_recSofar There Now sf)
    | Since (Here,Now,f1,f2)    -> Some (_recSince There Now f1 f2)
    | Binder (bk,n,bf)          -> (ohat (NameSet.add n binders) &~ (_Some <.> _recBinder bk n)) bf 
                                   |~~ (fun () -> Some f) (* sorry, but this is essential: 
                                                             bound variables can't be hatted
                                                           *)
    | Fvar    _           
    | Bfr     _           
    | Univ    _        
    | Latest  _        
    | Since   _                 -> raise (Invalid_argument (Printf.sprintf "Strongestpost.hatted.opt_hat %s in %s" 
                                                                           (string_of_formula f)
                                                                           (string_of_formula orig_f)
                                                           )
                                         )
    | _                         -> None
  and ohat binders = Formula.optmap (opt_hat binders)
  in
  Formula.map (opt_hat NameSet.empty) orig_f

(* in in-flight stability checks, we don't allow latest. I think this is what I mean *)
let rec strip_latest orig_f =
  let doit f = 
    match f.fnode with
    | Latest (Here,Now,v,lf) -> Some (_recEqual (_recFname v) (strip_latest lf))
    | Latest _               -> raise (Invalid_argument (Printf.sprintf "Strongestpost.strip_latest %s in %s"
                                                                        (string_of_formula f)
                                                                        (string_of_formula orig_f)
                                                        )
                                      )
    | _                      -> None
  in
  Formula.map doit orig_f
  
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
    let domodality isU mm mf =
      (subopt mapping 
       &~ (fun mf' -> 
             if isvarmapping mapping f then
               (Some (conjoin [mm Was mf; 
                               mf'; 
                               if isU then anyway (subopt mapping) (hatted true mf) else _recTrue
                              ]
                     )
               )
             else
               Some (mm Now mf')
          )
      ) mf
    in
    match f.fnode with
    | Freg   r                -> (try Some (mapping <@> r) with Not_found -> None)
    (* Flogc omitted deliberately: you can't assign to a logical constant *)
    (* We only substitute for unhooked variables -- Here+Now, There+Now *)
    | Fvar  (Here,Now,v)      -> (try Some (mapping <@> v) with Not_found -> None)
    | Fvar (There,Now,v)      -> None (* Formula.optmap leaves it alone *)
    | Binder (bk,n,bf)        -> (subopt (List.remove_assoc n mapping) &~ (_Some <.> _recBinder bk n)) bf 
                                 |~~ (fun () -> Some f) (* sorry, but this is essential: bf can't be
                                                           substituted with the original mapping
                                                         *)
    | Bfr (Here,Now,bf)       -> domodality false (_recBfr Here) bf
    | Bfr (There,Now,bf)      -> Some f
    | Univ (Now,uf)           -> domodality true _recUniv uf
    | Latest (Here,Now,v,lf)  -> if List.mem_assoc v mapping then 
                                   Some (_recLatest Here Was v (anyway (subopt mapping) lf))
                                 else 
                                   (subopt mapping) lf
                                   &~~ (_Some <.> _recLatest Here Now v)
    | Latest (There,Now,v,lf) -> Some f
    | Sofar (Here,Now, sf)    -> domodality false (_recSofar Here) sf
    | Sofar (There,Now, sf)   -> Some f
    | Since (Here,Now,f1,f2) -> (if isvarmapping mapping f then
                                    optionpair_either (subopt mapping) f1 (subopt mapping) f2
                                    &~~ (fun (f1',_) -> Some (conjoin [_recSince Here Was f1 f2; f1']))
                                  else
                                    optionpair_either (subopt mapping) f1 (subopt mapping) f2
                                    &~~ (fun (f1,f2) -> Some (_recSince Here Now f1 f2))
                                 )
                                 |~~ (fun () -> Some f)
    | Since (There,Now,f1,f2)-> Some f
    | Fvar      _
    | Bfr       _           
    | Univ      _            
    | Latest    _            
    | Sofar     _             
    | Since     _             -> raise (Invalid_argument (Printf.sprintf "sp_substitute [%s] %s, which contains %s" 
                                                                         (string_of_assoc string_of_name string_of_formula "->" ";" mapping)
                                                                         (string_of_formula orig_f) 
                                                                         (string_of_formula f)
                                                         )
                                       )
    | _                       -> None
  and subopt mapping = Formula.optmap (optsub mapping)
  in
  subopt mapping orig_f
  
let sp_substitute mapping f = 
  (optsp_substitute mapping ||~ id) f

(* strongest_post generates new names, so feels no need to use Exists *)
let strongest_post with_result pre assign = 
  let decorate f = if with_result then f else _recTrue in
  let old_name name =
    if Name.is_anyvar name then _recFvar Here Was name
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
            | Fvar (Here,Now,v) -> Some (NameSet.add v fvs)
            | Binder (_,n,f)    -> let bvs = vsof NameSet.empty f in
                                   Some (NameSet.union fvs (NameSet.remove n bvs))
            | _                 -> None
          in
          Formula.fold optvs vset f
        in 
        let mvs f =
          let optmvs fvs f =
            match f.fnode with
            | Bfr      (_,_,bf) -> Some (vsof fvs bf)
            | Univ       (_,uf) -> Some (vsof fvs uf)
            | Sofar    (_,_,sf) -> Some (vsof fvs sf)
            | Since (_,_,f1,f2) -> Some (vsof (vsof fvs f1) f2)
            | Binder (_,n,f)    -> let bvs = vsof NameSet.empty f in
                                   Some (NameSet.union fvs (NameSet.remove n bvs))
            | _                 -> None
          in
          Formula.fold optmvs NameSet.empty f
        in
        let vars = mvs pre in
        let unchanged = NameSet.diff vars (NameSet.of_list (List.map fstof2 mapping)) in
        conjoin (List.map (fun v -> _recEqual (_recFvar Here Now v)
                                              (_recFvar Here Was v)
                          )
                          (NameSet.elements unchanged)
                )
       )
      else _recTrue
    in
    let effect (loc,e) =
      match loc with
      | VarLoc v         -> _recEqual (_recFname v) (sub e) (* sub e for register assignments *)
      | ArrayLoc (v,ixf) -> _recEqual (_recFname v) (_recArrayStore (old_name v) ixf e)
    in
    conjoin (sub pre 
             :: (if !Settings.sp_unchanged then unchanged else _recTrue)
             :: List.map (decorate <.> effect) (List.combine locs es)
            )
  in
  match assign with
  | RbecomesE  (r,e)        -> sp_multiple false [r, old_name r] [VarLoc r] [e]
  | LocbecomesEs (b,loces)  -> let locs, es = List.split loces in
                               sp_multiple true (List.map (function VarLoc v         -> v, old_name v
                                                           |        ArrayLoc (v,ixf) -> v, old_name v 
                                                          )
                                                          locs
                                                )
                                                locs
                                                es
  | RsbecomeLocs (b,rslocs) -> let rss, locs = List.split rslocs in
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
                          