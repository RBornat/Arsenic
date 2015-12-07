(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let (<.>) f g a = f (g a)
let (<..>) f g a b = f (g a b)
let (<...>) f g a b c = f (g a b c)
let (<....>) f g a b c d = f (g a b c d)

let revargs f b a = f a b

let uncurry2 f (a,b) = f a b

let curry2 f a b = f (a,b)

let uncurry3 f (a,b,c) = f a b c

let curry3 f a b c = f (a,b,c)

let currypair a b = a,b

let id s = s

let ok s = true

let revargs2 f a b = f b a

let isAny fs v = List.exists (fun f -> f v) fs

let isAll fs v = List.for_all (fun f -> f v) fs

let (<&&>) f g x = f x && g x

let (<||>) f g x = f x || g x
