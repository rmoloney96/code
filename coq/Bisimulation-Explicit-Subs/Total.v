Require Import SystemF.
Require Import List.
Require Import Utils.
Require Import Bisimulation. 
  
Section Total.

  Variable Delta : nat -> Term.
  Variable Xi : nat -> Ty.  
  Variable Prog : forall n l m, Derivation Xi [n ; l |= F m @ Xi m] -> Derivation Xi [n ; l |= Delta m @ Xi m]. 
  Variable ProgTy : forall m, valid (Xi m) 0.

  Inductive Total : Holds -> Set := 
  | total_derivation : forall n l t A, Derivation Xi [n ; l |= t @ A] -> Total [n ; l |= t @ A]


