
Require Import List. 
Require Import String. 

Definition ident := (string*nat)%type.

Inductive natexp : Set := 
| z : natexp
| s : natexp -> natexp. 

Inductive listexp : Set := 
| n : listexp
| c : natexp -> listexp -> listexp. 

Inductive con : Set := 
| nc : natexp -> con
| lc : listexp -> con.
b

Inductive Expr : Set :=
| bvar : nat -> Expr
| fvar : ident -> Expr
| con : ident -> Expr 
| f : ident -> Expr 
| appl : ident -> list Expr -> Expr 
| lam : list Expr -> Expr 
| explet : ident -> Expr -> Expr 
| expcase : Expr -> list (Patr*Expr) -> Expr 
with Patr : Set :=
| patr : ident -> list Expr -> Patr.

