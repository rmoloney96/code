Module Type MONAD.
  Set Implicit Arguments. 
  
  Parameter M : forall (A : Type), Type.
  Parameter bind : forall (A B : Type),
    M A -> (A -> M B) -> M B.
  Parameter ret : forall (A : Type),
    A -> M A.
  
  Infix ">>=" := bind (at level 20, left associativity) : monad_scope.
  Open Scope monad_scope.
  
  Axiom left_unit : forall (A B : Type) (f : A -> M B) (a : A),
    (ret a) >>= f = f a.
  Axiom right_unit : forall (A B : Type) (m : M A),
    m >>= (fun a : A => ret a) = m.
  Axiom bind_assoc : forall (A B C : Type) (m : M A) (f : A -> M B) (g : B -> M C) (x : B),
    (m >>= f) >>= g = m >>= (fun x => (f x) >>= g).

End MONAD.

Module ListMonad <: MONAD. 
  
  Require Import List.
  
  Set Implicit Arguments.
  
  Definition M := list.
  
  Fixpoint bind (A : Type) (B : Type) (l : M A) (f : A -> M B) {struct l} : M B :=
    match l with
      | nil => nil
      | h::t => (f h)++(bind t f)
    end.
  
  Infix ">>=" := bind (at level 20, left associativity) : monad_scope.
  Open Scope monad_scope.
  
  Definition ret (A : Type) := fun a : A => a::nil.
  
  Lemma left_unit : forall (A B : Type) (f : A -> M B) (a : A),
    (ret a) >>= f = f a.
  Proof.
    intros ; simpl ; rewrite app_nil_end ; reflexivity.
  Defined. 
  
  Lemma right_unit : forall (A B : Type) (m : M A),
    m >>= (fun a : A => ret a) = m.
  Proof.
    simple induction m.
    simpl. reflexivity.
    intros. simpl.
    cut (bind l (fun a0 : A => ret a0) = l).
    intros. rewrite H0. reflexivity.
    exact H.
  Defined. 
  
  Lemma bind_assoc : forall (A B C : Type) (m : M A) (f : A -> M B) (g : B -> M C) (x : B),
    (m >>= f) >>= g = m >>= (fun x => (f x) >>= g).
  Proof.
    simple induction m.
    intros. simpl. reflexivity.
    intros. simpl.
    cut (l >>= f >>= g = l >>= (fun x0 : A => f x0 >>= g)).
    intros. rewrite < - H0.
    induction (f a).
    simpl. reflexivity.
    simpl. rewrite IHm0. rewrite app_ass. reflexivity.
    apply H. exact x.
  Defined.

End ListMonad.

(* Example *)
Import ListMonad.
Require Import Peano.
Require Import List.

Fixpoint downfrom (n : nat) {struct n} : (list nat) :=
  match n with
    | 0 => n::nil
    | S m => n::(downfrom m)
  end.
