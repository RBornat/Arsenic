open Function
(* mustn't open Tuple ... *)

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let string_of_list string_of sepstr xs = String.concat sepstr (List.map string_of xs)

let bracketed_string_of_list string_of xs = "[" ^ string_of_list string_of ";" xs ^ "]"

let bracketed_lines_of_list string_of xs = 
  "[" ^ string_of_list (fun x -> "\n    " ^ string_of x) ";" xs ^ "]"
  
let string_of_setlist string_of xs = "{" ^ string_of_list string_of ";" xs ^ "}"

let null = function [] -> true | _ -> false

let singleton = function [_] -> true | _ -> false

let cons x xs = x::xs

(* fold_right to keep things in input order. Hang the inefficiency! *)
let (><) xs ys = 
  List.fold_right 
    (fun x pairs -> 
        List.fold_right (fun y pairs -> (x,y)::pairs) ys pairs) 
    xs
    []

let notself_crossprod xs =
  let r = xs><xs in
  List.filter (not <.> uncurry2 (==)) r
  
let numbered xs = Array.to_list (Array.mapi (fun i x -> i,x) (Array.of_list xs))

let rec nodups eq = function
  | []    -> true
  | x::xs -> not (List.exists (eq x) xs) && nodups eq xs

let last xs = List.nth xs (List.length xs - 1)

let mapfold f x ys = 
  let rec mtl zs x = function
    |    [] -> x, List.rev zs
    | y::ys -> let x',z = f x y in
               mtl (z::zs) x' ys
  in
  mtl [] x ys

let lookup x xs = try Some(List.assoc x xs) with _ -> None

let mappedby = List.mem_assoc

let (<@>) xys x = List.assoc x xys
let (<@@>) xys x = List.assq x xys

let memofun newf =
  let table = ref [] in
  let lookup x =
    try (!table)<@>x
    with Not_found ->
      (let y = newf x in
       table := (x,y)::!table;
       y
      )
  in
  lookup

let rec ncombine xss = 
  let bad () =
    let shape = 
      bracketed_string_of_list (bracketed_string_of_list (fun _ -> ".")) xss
    in
    raise (Invalid_argument ("Listutils.ncombine " ^ shape))
  in
  match xss with
  | []           -> []
  | []::xss'     -> if List.exists (not <.> null) xss' then bad()
                    else xss
  | (x::xs)::xss -> 
      let hds,tails = 
        List.fold_left (fun (hds,tails) xs -> match xs with 
                                              | x::xs -> x::hds, xs::tails
                                              | _     -> bad ()
                       )
                       ([x],[xs])
                       xss
      in
      try List.rev hds::ncombine (List.rev tails)
      with Invalid_argument _ -> bad ()
        
let rec interpconcat interp xs =
  match xs with
  | []       -> []
  | [x]      -> x
  | x::xs    -> List.concat [x;interp;interpconcat interp xs]

let rec first f xs =
  match xs with 
  | []    -> raise Not_found
  | x::xs -> try f x with Not_found -> first f xs

(* oh for the Oxford comma ... *)
let phrase_of_list string_of sep1 sep2 =
  (let rec ph = function
   | []      -> ""
   | [x]     -> x
   | [x1;x2] -> x1 ^ sep2 ^ x2
   | x::xs   -> x ^ sep1 ^ ph xs
   in
   ph 
  ) 
  <.> List.filter (not <.> Stringutils.is_empty) 
  <.> List.map string_of 

let standard_phrase_of_list string_of = phrase_of_list string_of ", " " and "

let ncase_of sz ss sp = 
  (function
   | []  -> sz ()
   | [x] -> ss x
   | xs  -> sp xs
  )
  
let prefixed_phrase_of_list string_of singular plural = 
  ncase_of (fun () -> "")
           (fun s  -> singular ^ " " ^ s)
           (fun ss -> plural ^ " " ^ standard_phrase_of_list id ss)
  <.> List.filter (not <.> Stringutils.is_empty)
  <.> List.map string_of

let string_of_assoc fx fy colon semicolon xys = 
  String.concat semicolon (List.map (fun (x,y) -> fx x ^ colon ^ fy y) xys)

let vmemofun verbose str string_of_key string_of_target newf =
  let table = ref [] in
  let lookup x =
    if verbose then
      Printf.printf "\nvmemofun %s %s; assocs [%s]" str (string_of_key x) (string_of_assoc string_of_key string_of_target "->" ";" !table);
    try (!table)<@>x
    with Not_found ->
      (let y = newf x in
       table := (x,y)::!table;
       if verbose then
         Printf.printf " -> %s\nnew assocs [%s]" (string_of_target y) (string_of_assoc string_of_key string_of_target "->" ";" !table);
       y
      )
  in
  lookup

