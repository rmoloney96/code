
Theorem and_is_commutative : forall A B, A /\ B -> B /\ A.
Proof.
  refine (fun A B p => match p with 
                         | conj a b => conj b a
                       end).
Defined.

Inductive and (A B:Type) : Type :=
  conj : A -> B -> A /\ B.


