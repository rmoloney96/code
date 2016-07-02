
Require Import Ascii.
Require Import Bool.
Require Import Omega. 
Require Import Peano. 

Inductive eq_ascii : ascii -> ascii -> Prop := 
| ascii_eq : forall (a b:ascii), 
  (nat_of_ascii a) = (nat_of_ascii b) -> eq_ascii a b.

Lemma bit_significant_r : forall n m, 2*n+1 <> 2*m+0.
Proof. 
  intros n m. omega.
Defined.

Lemma bit_significant_l : forall n m, 2*n+0 <> 2*m+1.
Proof. 
  intros n m. omega.
Defined.

Lemma bit_reg_l : forall n m, 2*n = 2*m -> n = m.
Proof. 
  intros n m. omega.
Defined.

Lemma plus_reg_r : forall n m p, n + p = m + p -> n = m.
  intros. omega.
Defined.  

Ltac simplify_nat := 
  match goal with 
    | H: 2*?m + ?p = 2*?n + ?p |- _ => eapply plus_reg_r in H ; simplify_nat
    | H: 2*?m = 2*?n |- _ => eapply bit_reg_l in H ; simplify_nat
    | H: 2*?m + 0 = 2*?n + 1 |- _ => eapply bit_significant_l in H ; simplify_nat
    | H: 2*?m + 1 = 2*?n + 0 |- _ => eapply bit_significant_r in H ; simplify_nat
    | H: False |- _ => inversion H
    | H: true <> true |- _ => congruence
    | H: false <> false |- _ => congruence
    | H: true = false |- _ => congruence
    | H: false = true |- _ => congruence
    | H: ?b <> ?b', b : bool, b' : bool |- _ => destruct b ; destruct b' ; simplify_nat
    | _ : _ |- _ => idtac
  end.

Theorem eq_ascii_eq : forall a b, eq_ascii a b -> a = b.
Proof.
  intros a b. 
  destruct a as [b1 b2 b3 b4 b5 b6 b7 b8].
  destruct b as [b1' b2' b3' b4' b5' b6' b7' b8'].
  intros H ; inversion H ; clear H ; subst ; unfold nat_of_ascii in *. 
  (* bit 1 *)
  case (bool_dec b1 b1') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b2 b2') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b3 b3') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b4 b4') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b5 b5') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b6 b6') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b7 b7') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b8 b8') ; intro H' ; subst ; auto.  
  destruct b8 ; destruct b8' ; auto ; congruence.
Qed.


Print eq_ascii_eq. 
