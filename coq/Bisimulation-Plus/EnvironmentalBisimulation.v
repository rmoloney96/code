Require Import SystemF. 
Require Import Eval.
Require Import List. 
(* Require Import Cycle. *)



Section Bisimulation. 

  Variable Delta : nat -> Term.
  Variable Xi : nat -> Ty.  
  Variable Prog : forall n l m, Derivation Xi [n ; l |= F m @ Xi m] -> Derivation Xi [n ; l |= Delta m @ Xi m]. 
  Variable ProgTy : forall m, valid (Xi m) 0.
  
  Notation "t ~> t'" := (Ev Delta t t') (at level 60).  
  Notation "t ~>+ t'" := (Evplus Delta t t') (at level 60).
  Notation "t ~>* t'" := (Evstar Delta t t') (at level 60). 


Inductive label : Set := 
| lt : Term -> label 
| lty : Ty -> label
| lft : label
| rgt : label 
| fst : label
| snd : label 
| fld : label.

Inductive trans : Term -> label -> Term -> Type := 
| trans_app : forall t1 t2 A B, 
  Derivation Xi [0; nil |= t1 @ Imp A B] ->
  Derivation Xi [0; nil |= t2 @ A] -> 
  trans t1 (lt t2) (App t1 t2)
| trans_tapp : forall t ty A,
  Derivation Xi [0; nil |= t @ All A] ->
  valid ty 0 -> 
  trans t (lty ty) (TApp t ty)
| trans_inl : forall t A B, 
  Derivation Xi [0; nil |= (Inl t B) @ Or A B] -> 
  trans (Inl t B) lft t 
| trans_inr : forall t A B, 
  Derivation Xi [0; nil |= (Inr t A) @ Or A B] -> 
  trans (Inr t A) rgt t 
| trans_fst : forall s t A B, 
  Derivation Xi [0; nil |= (Pair s t) @ And A B] -> 
  trans (Pair s t) fst s 
| trans_snd : forall s t A B, 
  Derivation Xi [0; nil |= (Pair s t) @ And A B] -> 
  trans (Pair s t) snd t
| trans_fold : forall t ty, 
  Derivation Xi [0; nil |= (Fold t ty) @ ty] -> 
  trans (Fold t ty) fld t
(* | trans_gen : forall t ty, 
  Derivation Xi [0; nil | t @ ty] -> 
  *)
| trans_next : forall l t1 t2 t3, t1 ~>* t2 -> trans t2 l t3 -> trans t1 l t3.

CoInductive simulates : Term -> Term -> Type := 
| simulates_base : forall a b, 
  (forall a' l, 
    trans a l a' -> {b' : Term & trans b l b' & simulates a' b'}) -> 
  simulates a b.
