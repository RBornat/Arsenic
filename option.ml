open Function
open Listutils

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let string_of_option string_of = function
  | Some x -> "Some (" ^ string_of x ^ ")"
  | None   -> "None"
  
exception Failed_The

let _The = function Some x -> x | None -> raise Failed_The

let _Some x = Some x;;

let _SomeSome x = Some (Some x);;

let bool_of_opt = function Some _ -> true | None -> false

let (&~~) v g =
  match v with 
    None    -> None
  | Some v' -> g v'

let (|~~) v g =
  match v with
    None -> g ()
  | v    -> v

let (&~) f g x = f x &~~ g

let (|~) f g x =
  match f x with
    None -> g x
  | v    -> v

let (||~) f g x =
  match f x with
  | Some x' -> x'
  | None    -> g x

let anyway f = f ||~ id (* same as either x (f x), and to be preferred in those circumstances *)

let either x = function
  | None    -> x
  | Some x' -> x'

(* this is useful in mapfold. Oh dear *)
let anyway2 f x y =
  match f x y with
  | x, Some y -> x, y
  | x, None   -> x, y
  
let whatever f x = either x (f x)

let optionpair_either f x g y =
  match f x, g y with
  | None  , None   -> None
  | Some x, None   -> Some (x,y)
  | None  , Some y -> Some (x,y) 
  | Some x, Some y -> Some (x,y)

let optiontriple_either f x g y h z =
  match optionpair_either f x g y, h z with
  | None      , None   -> None
  | None      , Some z -> Some (x,y,z) 
  | Some (x,y), None   -> Some (x,y,z)
  | Some (x,y), Some z -> Some (x,y,z)

let optchange f x =
  match f x with
  | x' when x<>x' -> Some x'
  | _             -> None

let rec optfirst optf xs =
  match xs with
  | []    -> None
  | x::xs -> optf x |~~ (fun () -> optfirst optf xs)

let findfirst bf = 
  optfirst (fun x -> if bf x then Some x else None)
  
(* optmap_all f xs gives Some if f succeeds on all x *)

let rec optmap_all f  = function
| []    -> Some []
| x::xs -> f x &~~ (fun x -> (optmap_all f xs &~~ (fun xs -> Some (x::xs))))

(* optmap_any xs gives Some if f succeeds on any x *)

let rec optmap_any f  = function
| []    -> None
| x::xs -> optionpair_either f x (optmap_any f) xs &~~ (_Some <.> uncurry2 cons)

let rec optfold f x = function
| []      -> None
| y :: ys -> (match f x y with
              | Some x -> Some (anyway (revargs (optfold f) ys) x) 
              | None   -> optfold f x ys
             )

let sofirst string_of sep = function 
  | None   -> ""
  | Some f -> string_of f ^ sep

let sofirst_list string_of sep xs =
  sofirst string_of sep (match xs with [] -> None | xs -> Some xs)
  
let solast sep string_of = function 
  | None   -> ""
  | Some f -> sep ^ string_of f

let solast_list sep string_of xs =
  solast sep string_of (match xs with [] -> None | xs -> Some xs)
  