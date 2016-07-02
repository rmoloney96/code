Require Import Lang. 
Require Import Soundness.

Definition Bool := Bas 1.

Definition t : [Bool] ⊢ v 0 @ Bool.
Proof.
  auto with derivation.
Defined.

Definition testing1 : MetaGamma [Bool] (v 0) Bool.
Proof.
  unfold MetaGamma.
  intros.
  apply Gamma_Closure. 
  exact t.