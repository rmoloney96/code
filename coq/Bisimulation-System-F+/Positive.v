Require Import SystemF. 
Require Import Eval.
Require Import List. 

Section Positive. 

  Variable Delta : nat -> Term.
  Variable Xi : nat -> Ty.  
  Variable Prog : forall n l m, Derivation Xi [n ; l |= F m @ Xi m] -> Derivation Xi [n ; l |= Delta m @ Xi m]. 
  Variable ProgTy : forall m, valid (Xi m) 0.
  
  Notation "t ~> t'" := (Ev Delta t t') (at level 60).  
  Notation "t ~>+ t'" := (Evplus Delta t t') (at level 60).
  Notation "t ~>* t'" := (Evstar Delta t t') (at level 60). 

Inductive Neg : Ty -> Set := 
| npos : Abs 
| nneg : 
with Pos : Ty -> Set := 
| ppos : forall n, Pos (TV n)
| pneg : forall ty, Neg ty -> 
