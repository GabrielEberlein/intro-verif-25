module Clase04.BST

open FStar.Mul
open FStar.List.Tot

let max (x y : int) : int = if x > y then x else y

type bst =
  | L
  | N of bst & int & bst

let rec insert (x: int) (t: bst) : bst =
  match t with
  | L -> N (L, x, L)
  | N (l, y, r) ->
    (* Nota: admite duplicados *)
    if x <= y
    then N (insert x l, y, r)
    else N (l, y, insert x r)

let rec member (x: int) (t: bst) : bool =
  match t with
  | L -> false
  | N (l, y, r) ->
    if x < y then member x l
    else if x > y then member x r
    else true

let rec to_list (t: bst) : list int =
  match t with
  | L -> []
  | N (l, x, r) -> to_list l @ [x] @ to_list r

let rec from_list (l: list int) : bst =
  match l with
  | [] -> L
  | x :: xs -> insert x (from_list xs)

let rec size (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + size l + size r

let rec height (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + max (height l) (height r)

let rec insert_size (x:int) (t:bst) : Lemma (size (insert x t) == 1 + size t) =
  match t with
  | L -> ()
  | N (l, x', r) -> 
    insert_size x l;
    insert_size x r

let rec insert_height (x:int) (t:bst)
: Lemma (height (insert x t) <= 1 + height t)
=
  match t with
  | L -> ()
  | N (l, x', r) -> 
    insert_height x l;
    insert_height x r

let rec insert_mem (x:int) (t:bst) : Lemma (member x (insert x t)) =
  match t with
  | L -> ()
  | N (l, x', r) ->
    if x=x' then ()
    else if x < x' then
      insert_mem x l
    else
      insert_mem x r

(* ¿Puede demostrar también que:
     height t <= height (insert x t)
   ? ¿Cuál es la forma "más fácil" de hacerlo? *)
let rec height_increase (x:int) (t:bst)
: Lemma (height t <= height (insert x t))
= 
  match t with
  | L -> ()
  | N (l, x', r) -> 
    height_increase x l;
    height_increase x r

let rec extract_min (t: bst) : option (int & bst) =
  match t with
  | L -> None
  | N (L, x, r) -> Some (x, r)
  | N (l, x, r) ->
    match extract_min l with
    | None -> None
    | Some (y, l') -> Some (y, N (l', x, r))

let rec extract_min_ok (t:bst) : Lemma (match extract_min t with
                                      | None -> t == L
                                      | Some (x, t') -> size t' == size t-1)
=
  match t with
  | L -> ()
  | N (L, x, r) -> ()
  | N (l, x, r) ->
    extract_min_ok l

let delete_root (t: bst) : Pure bst (requires N? t) (ensures fun _ -> True) =
  let N (l, _, r) = t in
  match extract_min r with
  | None -> l
  | Some (x, r') -> N (l, x, r')

(* Nota: delete no mantiene el invariante de BST. ¿Cómo se podría arreglar? *)

let rec delete (x: int) (t: bst) : bst =
  match t with
  | L -> L
  | N (l, y, r) ->
    if x < y then N (delete x l, y, r)
    else if x > y then N (l, y, delete x r)
    else delete_root t

(* Un poco más difícil. Require un lema auxiliar sobre extract_min:
declárelo y demuéstrelo. Si le parece conveniente, puede modificar
las definiciones de delete, delete_root y extract_min. *)
let rec delete_size (x:int) (t:bst) : Lemma (delete x t == t \/ size (delete x t) == size t - 1) =
  match t with
  | L -> ()
  | N (l, x', r) -> 
    if x < x' then delete_size x l
    else if x > x' then delete_size x r
    else extract_min_ok r

(* Versión más fuerte del lema anterior. *)
let rec delete_size_mem (x:int) (t:bst)
: Lemma (requires member x t)
        (ensures size (delete x t) == size t - 1)
= 
  match t with
  | L -> ()
  | N (l, x', r) -> 
    if x < x' then delete_size_mem x l
    else if x > x' then delete_size_mem x r
    else extract_min_ok r

(* ¿Es cierto que `to_list (insert x t)` es una permutación de `x :: to_list t`?
   ¿Cómo se podría probar? *)
//No es lo mismo, to_list genera la lista inorder, si se inserta un elemento antes este no quedara 
//primero en la lista si no en la posicion que le corresponde

// Necesito este lema para to_list_length
let rec len_append (l1 l2 : list int)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  =
    match l1 with
    | [] -> ()
    | x::xs -> len_append xs l2

let rec to_list_length (t:bst) : Lemma (length (to_list t) == size t) =
  match t with
  | L -> ()
  | N (l, x, r) ->
    to_list_length l;
    len_append (to_list l) [x];
    to_list_length r

(* Contestar en texto (sin intentar formalizar):
    ¿Es cierto que `member x (insert y (insert x t))`? ¿Cómo se puede probar?
    ¿Es cierto que `delete x (insert x t) == t`?
*)
// member x (insert y (insert x t)) es cierto, para probarlo habria que hacer un lema que indique
// que member x (insert y t) == (x=y || member x t) y luego usar insert_mem

// delete x (insert x t) == t no es cierto, ya que podemos llamar las funciones con un bst que no cumpla
// la invariante. Un contraejemplo es,
