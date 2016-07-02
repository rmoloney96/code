
Variable P:Set.


Ltac case_eq H := 
  cut H ; intros ; destruct H.

Require Import Peano_dec.

Lemma test : forall (k k' : nat), eq_nat_dec k k'.
Proof. 
  intros. case_eq (k=k').
  intros. cut P. intros.  


 
