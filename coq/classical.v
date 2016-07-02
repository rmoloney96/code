
Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~P -> P.
Definition excluded_middle := forall P:Prop, P\/~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q)->(~P\/Q).

Lemma peirce_EQ_classic : peirce <-> classic.
Proof.
  split. unfold classic. intros.
  apply (H P False). intros. 
  compute in H0. 
  absurd (~ P). compute. intros. apply H0. assumption.
  assumption. 
  
  unfold peirce. intros. 
  apply H. compute. intros.
  apply H1. apply H0. intros.
  absurd P. assumption. assumption.
Qed.

Lemma classic_EQ_excluded_middle : classic <-> excluded_middle.
Proof.
  split. 
  unfold excluded_middle. intros.
  apply H. compute. intros. 
  absurd (~ P). compute. intros.
  apply H0. right. assumption.
  compute. intros. apply H0. 
  left. assumption.

  unfold classic. unfold excluded_middle.
  intros. case (H P). intros. assumption.
  intros. absurd P. assumption. absurd (~ P). 
  assumption. assumption.
Defined.

Lemma excluded_middle_EQ_de_morgan_and_not :  excluded_middle <-> de_morgan_not_and_not.
Proof.
  split. unfold de_morgan_not_and_not. unfold excluded_middle. 
  intros. compute in H0. 
  case (H P) ; case (H Q). 
  intros. left. assumption.
  intros. left. assumption.
  intros. right. assumption.
  intros.
  case H0. split. assumption.
  assumption.

  unfold excluded_middle. intros.
  apply (H P (~ P)). 
  compute. intros.
  case H0. 
  intros. absurd (~ P).
  assumption.
  assumption.
Defined.


Lemma de_morgan_not_and_not_EQ_implies_to_or : de_morgan_not_and_not <-> implies_to_or.
Proof.
  split. 
  
  unfold implies_to_or. intros.
  apply H. compute. intros. 
  case H1. intros. 
  absurd (~ P). compute. 
  assumption. compute. 
  intros. apply H3. apply H0. assumption.

  unfold de_morgan_not_and_not. unfold implies_to_or. intros.
  cut (forall (P : Prop), ~ ~ P -> P). intros.
  case (H (~ P) (~~Q)). intros. compute.
  intros. apply H0.
  
  split. assumption. assumption. 
  
  intros. left. apply H1. assumption.
  intros. right. apply H1. assumption.
  intros.
  case (H P0 P0).
  intros. assumption. intros.
  absurd (~ P0). assumption. assumption. 
  intros. assumption.
Defined.