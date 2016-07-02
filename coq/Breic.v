

Theorem impl : forall A C, A /\ C -> C.
Proof.
  intros. 
  inversion H. 
  auto.
Defined.

Theorem impl2 : forall F S, F /\ S -> F.
Proof.
  intros.

  inversion H.
    intros.
  inversion H.
  exact H1.
exact H0.
Defined.

Theorem impl3 : forall (A B:Prop), A -> A \/ B.
  intros.
  left.
  exact H.
Defined.

Theorem ggg : forall (A B:Prop), A /\ B -> B /\ A.
Proof.
  intros.  
  split.
  inversion H.
  exact H1.
 
  inversion H.
  exact H0.
Defined.

Theorem 


