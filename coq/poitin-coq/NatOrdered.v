Require Import OrderedType.
Require Import Arith.
 
Module NatOrder <: OrderedType.
  Definition t := nat. 

  (* 
  Definition eq (A:Type) := eq A.  
  Definition lt := lt. 
  *) 

  Definition eq_refl : forall x : t, x = x.
  Proof. 
    auto. 
  Defined.
  
  Definition eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    auto.
  Defined.

  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    congruence.
  Defined.

  Require Import Omega.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. 
    intros ; omega.
  Defined.
  
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. 
    intros ; omega.
  Defined. 

  Definition eq := eq (A:=nat).  
  Definition lt := lt. 
  Hint Unfold eq.
  Hint Unfold lt.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof. 
    intros. case (lt_eq_lt_dec x y) ; firstorder.
  Defined.
  
End NatOrder.