
Require Import List.
Parameter A : Set.
Parameter B : Set.
Definition assoc_list := list (A * B)%type.
Parameter eq_dec : forall (x:A) (y:A),{x=y}+{x<>y}.

Lemma assoc : forall (x:A) (l: assoc_list),
  {y | In (x,y) l} + {forall (y:B), ~In (x,y) l}.
Proof. 
  intros ; induction l ; firstorder.
  case (eq_dec x (fst a)).
  intros. left. exists (snd a). rewrite e. 
  cut ((fst a,snd a) = a). intros.  rewrite H. 
  firstorder.
  destruct a ; auto.
  intros. right. intros. unfold not. intros. 
  simpl in H.
  inversion H. unfold not in n. apply n. 
  rewrite H0. auto.
  firstorder.
Defined. 

Extraction  assoc.