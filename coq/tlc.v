
Require Import String.
Require Import List.

Inductive type : Set := 
| Nat : type 
| Arrow : type -> type -> type. 

(* 
Variable type : Set. 
*) 

Inductive expr : Set := 
| Var : string -> expr 
| Con : string -> list expr -> expr
| Funv : string -> expr
| Lam : type -> expr -> expr
| Cas : expr -> list (pat*expr) -> expr
with pat : Set := 
| Pat : string -> list expr -> pat.

Definition context := list type. 

Fixpoint typecheck (expr)

Fixpoint eval (Expr : := 