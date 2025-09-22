module Clase01

(* Hace que '*' sea la multiplicación de enteros, en vez del constructor de tuplas. *)
open FStar.Mul

let suma (x y : int) : int = x + y

(* Defina una función suma sobre naturales *)
let addnat (x y : nat) : nat = x+y

(* Defina una función suma de 3 argumentos, que use la anterior. *)
let suma3 (x y z : int) : int = x+y+z

(* Defina una función que incremente un número en 1. *)
let incr (x:int) : int = x+1

(* Dé más tipos a la función de incremento. ¿Cómo se comparan
estos tipos? *)
let incr'   (x:nat) : int = x+1
let incr''  (x:nat) : nat = x+1
let incr''' (x:nat) : y:int{y = x+1} = x+1

(* Un tipo refinado es un subtipo del tipo base, se puede
usar sin coerción. El subtipado es también consciente de funciones. *)
let addnat' (x y : nat) : int = x + y

let debilitar1 (f : int -> int) : nat -> int = f
let debilitar2 (f : nat -> nat) : nat -> int = f
let debilitar3 (f : int -> nat) : nat -> int = f

let par   (x:int) : bool = x % 2 = 0
let impar (x:int) : bool = x % 2 = 1

(* Dadas estas definiciones, dé un tipo a incr que diga
que dado un número par, devuelve un número impar. *)
 let incr'''' (x:int{par x}) : (y:int{impar y}) = x+1

(* ¿Por qué falla la siguiente definición? Arreglarla. *)
// El atributo expect_failure causa que F* chequeé que la definición
// subsiguiente falle. Borrarlo para ver el error real.
let muldiv (a:int) (b : nonzero) : (y:int{y = a}) = (a * b) / b

(* Defina una función de valor absoluto *)
let abs (x:int) : nat = if x >= 0 then x else -x

(* Defina una función que calcule el máximo de dos enteros. *)
let max (x y : int) : int = if x > y then x else y

(* Dé tipos más expresivos a max.
   1- Garantizando que el resultado es igual a alguno de los argumentos
   2- Además, garantizando que el resultado es mayor o igual a ambos argumentos. *)
let max' (x y : int) : (z:int{x=z || y=z}) = if x > y then x else y
let max'' (x y : int) : (z:int{(x=z || y=z) && (z>=x && z>=y)}) = if x > y then x else y

(* Defina la función de fibonacci, de enteros a enteros,
o alguna restricción apropiada. *)
val fib : (x:nat) -> (y:int{y>=1}) 
let rec fib x = 
   if x <= 1 then 1 else fib(x-1) + fib(x-2)

(* Defina un tipo 'digito' de naturales de un sólo dígito. *)
 type digito = d:nat{d<10}

(* Defina una función que compute el máximo de tres dígitos, usando
alguna definición anterior. El resultado debe ser de tipo digito.
¿Por qué funciona esto? ¿De cuáles partes anteriores del archivo
depende, exactamente? *)
//TO DO: ver porque funciona con cualquier max
let max_digito (x y z : digito) : digito = max'' (max'' x y) z

(* Defina la función factorial. ¿Puede darle un mejor tipo? *)
val fac : (x:nat) -> (y:nat{y >= 1})
let rec fac x = 
   if x=0 then 1 else x*fac(x-1)

(* Defina una función que sume los números naturales de 0 a `n`. *)
val triang : (n:nat) -> (y:nat{y>=n && (if n<=1 then n=y else y>=n+(n-1))})
let rec triang n = if n=0 then 0 else triang(n-1) + n

(* Intente darle un tipo a fib que diga que el resultado es siempre
mayor o igual al argumento. Si el chequeo falla, dé hipótesis de por qué. *)
val fib' : (x:nat) -> (y:int{y>=1 && y>=x}) 
let rec fib' x = 
   if x <= 1 then 1 else fib'(x-1) + fib'(x-2)

(* Idem para la función factorial. *)
//val fac' : (x:nat) -> (y:nat{y >= 1 && y >= x && (if x<=1 then y=1 else y>=x*(x-1))})
val fac' : (x:nat) -> (y:nat{y >= 1 && y >= x})
let rec fac' x = 
   if x=0 then 1 else x*fac'(x-1)

(* Defina la siguiente función que suma una lista de enteros. *)
val sum_int : list int -> int
let rec sum_int xs = 
   match xs with
   | [] -> 0
   | hd::tl -> hd + (sum_int tl)

(* Defina la siguiente función que revierte una lista de enteros. *)
val append_int : list int -> list int -> list int 
let rec append_int l1 l2 = 
   match l1 with
   | [] -> l2
   | (hd::tl) -> hd::(append_int tl l2)

val rev_int : list int -> list int
let rec rev_int xs = 
   match xs with
   | [] -> []
   | hd::tl -> append_int (rev_int tl) (hd::[])
