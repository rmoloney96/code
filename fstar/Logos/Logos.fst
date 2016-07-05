
module Logos

open FStar.List
open FStar.Nat
open FStar.String
open FStar.All
(* open FStar.Maybe *)

type atom = string

val === : atom -> atom -> bool

type ty = 
  | Int : ty
  | Str : ty 
  | Sort : atom -> ty 
  | Rel : ty -> ty -> ty 
  | Pi : ty -> ty 
  | TyVar : atom -> nat -> ty

type term = 
  | Var : atom -> term 
  | Funsym : atom -> (list term) -> term
  
type log = 
  | And : log -> log -> log
  | Or : log -> log -> log
  | Lam : log -> log -> log
  | Term : term -> log

type subst = list (term * term)

val fv : s:term -> nat 
let rec fv s ex = match s with
 | Var a -> 

val unify: theta:subst -> s:term -> t:term -> Tot (option term)



(* let rec unify t s = *)
