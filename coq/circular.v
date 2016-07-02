Require Import List.

CoInductive CoNat : Type := 
| Z : CoNat
| S : CoNat -> CoNat.

CoFixpoint inf : CoNat := S(inf).

Eval compute in inf.

Definition isZero (n:CoNat) :=
  match n with 
    | Z => True
    | S n' => False
  end.

Eval compute in (isZero inf).

Ltac circle := 
  match goal with
    | [ H : ((context[?x]) = ?x) |- _ ] => induction x ; inversion H ; congruence
  end. 



Lemma nocirc : forall (A : Set) (h : A) (t : list A), cons h t  = t -> False.
  intros A h t H'. circle. 
  intros A h t H'. induction t. inversion H'. congruence.
Defined. 

 