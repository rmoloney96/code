
Fixpoint even (x:nat) : Prop := 
  match x with 
    | 0 => True 
    | S(0) => False 
    | S(S(x')) => even x'
  end.


Fixpoint double (x:nat) : nat := 
  match x with 
    | 0 => 0
    | S x' => S (S (double x'))
  end.

Theorem double_even : forall (x:nat), even(double x).
Proof. 
  intros x. induction x. 
  unfold even. unfold double. auto. 
  unfold even. unfold double. unfold even in IHx. unfold double in IHx.  
  assumption.
Defined.

 
  