
module Logos

open FStar.List
open FStar.Nat
open FStar.String 
open FStar.Maybe
 
type ty = | Int : ty
  | Str : ty 
  | Sort : string -> nat : ty 
  | Rel : ty -> ty -> ty 
  | Pi : ty -> ty 
  | TyVar : string -> nat -> ty

type term = | Var : string -> nat -> term 
  | Funsym : string -> (list term) -> term
  
type log = | And : log -> log -> log
  | Or : log -> log -> log
  | Lam : log -> log -> log
  | Term : term -> log

unify : term -> term -> maybe term

