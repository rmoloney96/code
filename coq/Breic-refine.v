

Theorem and_is_commutative : forall A B, A /\ B  -> B /\ A.
Proof.
  refine 
  (fun (A B : Prop) (p : A /\ B) => 
      match p with 
       | conj a b => conj b a
      end). 
Qed.


Theorem and_is_comm : forall A B, A /\ B -> B /\ A. 
Proof.
  intros.
  inversion H.
  split.
  exact H1.
  exact H0.
Defined.

Print and_is_comm.