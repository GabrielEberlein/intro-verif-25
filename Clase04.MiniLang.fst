module Clase04.MiniLang

type l_ty =
  | Int
  | Bool

type var = nat

(* Pequeño lenguaje de expresiones, indexado por el tipo de su resultado *)
type expr : l_ty -> Type =
  | EInt : int -> expr Int
  | EBool : bool -> expr Bool
  | EAdd : expr Int -> expr Int -> expr Int
  | EEq : expr Int -> expr Int -> expr Bool
  | EIf :
    #ty:_ ->
    expr Bool -> expr ty -> expr ty -> expr ty

(* Traducción de tipos de MiniLang a tipos de F* *)
let lift (ty : l_ty) : Type =
  match ty with
  | Int -> int
  | Bool -> bool
(* El evaluador intrínsecamente-tipado de MiniLang *)
val eval (#ty:l_ty) (e : expr ty) : Tot (lift ty)
let rec eval (#ty:l_ty) (e : expr ty) : Tot (lift ty) (decreases e) =
  match e with
  | EInt i -> i
  | EBool b -> b
  | EAdd m n -> eval m + eval n
  | EEq m n -> eval m = eval n
  | EIf c t e ->
    if eval c then eval t else eval e

(* Optimización sobre expresionse MiniLang: constant folding *)
let rec constant_fold (#ty:l_ty) (e : expr ty) : Tot (expr ty) (decreases e)=
  match e with
  | EAdd (EInt m) (EInt n) -> EInt (m + n)
  | EAdd l r -> EAdd (constant_fold l) (constant_fold r)
  | EEq (EInt m) (EInt n) -> EBool (m=n)
  | EEq l r -> EEq (constant_fold l) (constant_fold r)
  | EIf c l r -> (
    match constant_fold c with
    | EBool true -> constant_fold l
    | EBool false -> constant_fold r
    | _ -> EIf c (constant_fold l) (constant_fold r)
  )
  | _ -> e (* Completar con más casos. *)

(* Correctitud de la optimización de constant folding *)
let rec constant_fold_ok (#ty:l_ty) (e : expr ty)
  : Lemma (ensures eval e == eval (constant_fold e))
          (decreases e)
=
    match e with
    | EAdd l r -> constant_fold_ok l; constant_fold_ok r
    | EEq l r -> constant_fold_ok l; constant_fold_ok r
    | EIf c l r -> constant_fold_ok c; constant_fold_ok l; constant_fold_ok r
    | _ -> ()
