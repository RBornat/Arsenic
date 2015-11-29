(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let fstof2 (x,_) = x
let sndof2 (_,y) = y

let two_map     f   (a,b) = (f a, f b)
let two_fold    f x (a,b) = List.fold_left f x [a;b]
let two_mapfold f x (a,b) = 
  let x, a = f x a in
  let x, b = f x b in
  x, (a,b)

let fstof3  (x,_,_) = x
let sndof3  (_,y,_) = y
let thrdof3 (_,_,z) = z

let three_map     f   (a,b,c) = (f a, f b, f c)
let three_fold    f x (a,b,c) = List.fold_left f x [a;b;c]
let three_mapfold f x (a,b,c) = 
  let x, a = f x a in
  let x, b = f x b in
  let x, c = f x c in
  x, (a,b,c)

let fstof5  (x,_,_,_,_) = x
let sndof5  (_,y,_,_,_) = y
let thrdof5 (_,_,z,_,_) = z
let frthof5 (_,_,_,a,_) = a
let ffthof5 (_,_,_,_,b) = b

let five_map     f   (a,b,c,d,e) = (f a, f b, f c, f d, f e)
let five_fold    f x (a,b,c,d,e) = List.fold_left f x [a;b;c;d;e]
let five_mapfold f x (a,b,c,d,e) = 
  let x, a = f x a in
  let x, b = f x b in
  let x, c = f x c in
  let x, d = f x d in
  let x, e = f x e in
  x, (a,b,c,d,e)

let string_of_pair fx fy sep (x,y) =
  fx x ^ sep ^ fy y

let bracketed_string_of_pair fx fy (x,y) =
  "(" ^ string_of_pair fx fy "," (x,y) ^ ")"

let string_of_triple fx fy fz sep (x,y,z) =
  fx x ^ sep ^ fy y ^ sep ^ fz z

let bracketed_string_of_triple fx fy fz (x,y,z) =
  "(" ^ string_of_triple fx fy fz "," (x,y,z) ^ ")"

let string_of_quadruple fx fy fz fa sep (x,y,z,a) =
  fx x ^ sep ^ fy y ^ sep ^ fz z ^ sep ^ fa a

let bracketed_string_of_quadruple fx fy fz fa (x,y,z,a) =
  "(" ^ string_of_quadruple fx fy fz fa "," (x,y,z,a) ^ ")"

let string_of_quintuple fx fy fz fa fb sep (x,y,z,a,b) =
  fx x ^ sep ^ fy y ^ sep ^ fz z ^ sep ^ fa a ^ sep ^ fb b

let bracketed_string_of_quintuple fx fy fz fa fb sep (x,y,z,a,b) =
  "(" ^ string_of_quintuple fx fy fz fa fb "," (x,y,z,a,b) ^ ")"
