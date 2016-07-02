Require Import Lang.
Require Import List. 
Require Import Arith.
Require Import Context.

Lemma sub_pres : forall r s Ξ Γ A B, 
  (Ξ++A::Γ ⊢ r @ B) -> 
  (Ξ++Γ ⊢ s @ A) -> 
  (Ξ++Γ ⊢ sub r (length Ξ) s @ B).
Proof.
  induction r ; intros s Ξ Γ A B H H0 ; inversion H ; simpl ; subst ; eauto with derivation.
 
  (* v *) 
  intros.
  inversion H. subst.
  simpl. 
  case (le_lt_dec (length Ξ) n) ; intros.
  (* le *)
    case (eq_nat_dec (length Ξ) n) ; intros.
    (* eq *)
      subst.
      rewrite idx_at in H3. inversion H3. rewrite H2 in H0. auto.
    (* neq *)
      destruct n. 
      absurd (length Ξ <= 0) ; eauto with arith.
  (* ge *)
  apply strengthen_gt with (A:=A).
  inversion l. apply n0 in H2. inversion H2. subst.
  apply le_n_S. auto. auto. 
  (* lt *)
  apply strengthen_lt with (A:=A). auto. auto.
 
  (* lam *) 
  intros. simpl. inversion H. subst.
  change (S (length Ξ)) with (length (t::Ξ)).
  apply ImpIntro. 
  change (t::Ξ++Γ) with ((t::Ξ)++Γ).
  apply IHr with (A:=A). auto.
  unfold shift. change 0 with (length (nil (A:=Ty))). 
  simpl.
  change (t :: Ξ ++ Γ) with ([]++t::(Ξ++Γ)).
  apply weaken. auto. 
Defined.

Lemma gamma_reduce : forall r s Ξ Γ A B, 
  (Ξ++A::Γ ⊢ r @ B) -> 
  ([] ⊢ s @ A) -> 
  (Ξ++Γ ⊢ sub r (length Ξ) s @ B).
Proof.
  induction r ; intros s Ξ Γ A B H H0 ; inversion H ; simpl ; subst ; eauto with derivation.
 
  (* v *) 
  intros.
  inversion H. subst.
  simpl. 
  case (le_lt_dec (length Ξ) n) ; intros.
  (* le *)
    case (eq_nat_dec (length Ξ) n) ; intros.
    (* eq *)
      subst.
      rewrite idx_at in H3. inversion H3. rewrite H2 in H0. apply weaken_closed.  auto.
    (* neq *)
      destruct n. 
      absurd (length Ξ <= 0) ; eauto with arith.
  (* ge *)
  apply strengthen_gt with (A:=A).
  inversion l. apply n0 in H2. inversion H2. subst.
  apply le_n_S. auto. auto. 
  (* lt *)
  apply strengthen_lt with (A:=A). auto. auto.
 
  (* lam *) 
  intros. simpl. inversion H. subst.
  change (S (length Ξ)) with (length (t::Ξ)).
  apply ImpIntro. 
  change (t::Ξ++Γ) with ((t::Ξ)++Γ).
  apply IHr with (A:=A). auto.
  unfold shift. change 0 with (length (nil (A:=Ty))). 
  simpl.
  change (t :: Ξ ++ Γ) with ([]++t::(Ξ++Γ)).
  rewrite closed_shift_invariant with (A:=A). auto. auto.
Defined. 

Lemma gamma_reduce_left : forall r s Γ A B, 
  (A::Γ ⊢ r @ B) -> 
  ([] ⊢ s @ A) -> 
  (Γ ⊢ sub r 0 s @ B).
Proof.
  intros. 
  change Γ with ([] ++ Γ).
  apply gamma_reduce with (A:=A). simpl. auto. auto.
Defined.
  
Fixpoint MetaGamma (Γ : Ctx) (t : Term) (A : Ty): Set :=
  match Γ with 
    | nil => [] ⊢ t @ A
    | (B::Γ') => forall (a : Term), [] ⊢ a @ B -> MetaGamma Γ' (sub t 0 a) A
  end.

Lemma Gamma_Closure : forall Γ t A, Γ ⊢ t @ A -> MetaGamma Γ t A.
Proof.
  induction Γ.
  intros. simpl. auto.
  intros. simpl.
  intros. apply IHΓ.
  apply gamma_reduce_left with (A:=a). auto. auto.
Defined. 

Lemma Gamma_Opening : forall Γ t A, MetaGamma  t A -> Γ ⊢ t @ A. 