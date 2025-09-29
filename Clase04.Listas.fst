module Clase04.Listas

open FStar.List.Tot

val sum_int : list int -> int
let rec sum_int xs =
  match xs with
 | [] -> 0
 | x::xs' -> x + sum_int xs'

(* Demuestre que sum_int "distribuye" sobre la concatenación de listas. *)
let rec sum_append (l1 l2 : list int)
  : Lemma (sum_int (l1 @ l2) == sum_int l1 + sum_int l2)
  = 
    match l1 with
    | [] -> ()
    | x::xs -> sum_append xs l2

(* Idem para length, definida en la librería de F*. *)
let rec len_append (l1 l2 : list int)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  =
    match l1 with
    | [] -> ()
    | x::xs -> len_append xs l2

let rec snoc (xs : list int) (x : int) : list int =
  match xs with
  | [] -> [x]
  | y::ys -> y :: snoc ys x

(* unit-tests *)
let _ = assert (snoc [1;2;3] 4 == [1;2;3;4])
let _ = assert (snoc [1;2;3] 5 == [1;2;3;5])

let rec rev_int (xs : list int) : list int =
  match xs with
  | [] -> []
  | x::xs' -> snoc (rev_int xs') x

let rec rev_cons (x:int) (xs : list int)
  : Lemma (rev_int(x::xs) == snoc (rev_int xs) x)
=
  match xs with
  | [] -> ()
  | y::ys -> rev_cons x ys

let rec rev_snoc (xs : list int) (x:int)
  : Lemma (rev_int(snoc xs x) == x::(rev_int xs))
=
  match xs with
  | [] -> ()
  | y::ys -> rev_snoc ys x

let rec snoc_append (xs : list int) (ys : list int) (x:int)
  : Lemma ((snoc (xs@ys) x) == xs @ (snoc ys x))
=
  match xs with
  | [] -> ()
  | z::zs -> snoc_append zs ys x

let rec rev_append_int (xs ys : list int)
  : Lemma (rev_int (xs @ ys) == rev_int ys @ rev_int xs)
=
  match xs with
  | [] -> ()
  | z::zs -> 
    rev_append_int zs ys;
    snoc_append (rev_int ys) (rev_int zs) z

let rec rev_rev (xs : list int)
  : Lemma (rev_int (rev_int xs) == xs)
= 
  match xs with
  | [] -> ()
  | y::ys -> 
    rev_rev ys;
    rev_snoc (rev_int ys) y

let rev_injective (xs ys : list int)
  : Lemma (requires rev_int xs == rev_int ys) (ensures xs == ys)
=
  rev_rev xs;
  rev_rev ys
