Require Import Arith.
Require Import List.
Require Import Lang.

Lemma idx_length : forall (s : Set) (A : s) G n, idx n G = Some A -> length G > n.
Proof.
  induction G ; intros ; simpl. 
  destruct n. 
  (* zero *)
  simpl in H.  inversion H.
  simpl in H. inversion H.
  (* succ *)
  intros. simpl. 
  case_eq n. intros. subst. auto with arith.
  intros. apply gt_n_S. apply IHG. subst. simpl in H. auto.
Defined.

Lemma idx_at : forall (S : Set) (Ξ Γ : list S) (A : S), idx (length Ξ) (Ξ++A::Γ) = Some A.
Proof.
  induction Ξ. simpl. intros. auto.
  intros. simpl. apply IHΞ.
Defined.
 
Lemma hole_at_i : forall i j k,
  shiftat j (v i) = (v k) -> (~ j = k).
Proof.
  intros. simpl in *.
  case_eq (le_lt_dec j i).
  intros. rewrite H0 in H. clear H0.
  unfold not. intros. rewrite <- H0 in H. 
  inversion H. 
  apply (le_Sn_n i). rewrite H2. auto.
  intros. rewrite H0 in H. clear H0.
  inversion H. 
  unfold not. intros. rewrite H1 in l. rewrite H0 in l.
  apply (lt_irrefl k). auto.
Defined. 

Lemma idx_shift_le : forall (s : Set) 
  Ξ Γ i (A : s) B,  length Ξ <= i -> 
  idx i (Ξ ++ Γ) = Some B ->
  idx (S i) (Ξ ++ A :: Γ) = Some B.
Proof.
  induction Ξ ; intros. 
  simpl in * ; auto.
  simpl ; destruct i. 
   (* 0 *) simpl in H ; inversion H.  
   (* S i *) apply IHΞ ; eauto with arith.
Defined. 

Lemma idx_shift_lt : forall (s : Set) 
  Ξ Γ i (A : s) B,  i < length Ξ -> 
  idx i (Ξ ++ Γ) = Some B ->
  idx i (Ξ ++ A :: Γ) = Some B.
Proof.
  induction Ξ ; intros. 
  simpl in *. inversion H. 
  simpl ; destruct i. 
   (* 0 *) simpl in * ; auto.
   (* S i *) simpl in *. apply IHΞ ; eauto with arith.
Defined. 

Definition weaken_var_lt : forall Ξ Γ i A B,
  i < length Ξ -> 
  (Ξ ++ Γ ⊢ v i @ B) ->
  (Ξ ++ A :: Γ ⊢ v i @ B).
Proof. 
  intros.
  apply VarIntro. 
  inversion H0. subst. apply idx_shift_lt ; auto.
Defined. 
 
Definition weaken_var_gt : forall Ξ Γ i A B,
  length Ξ < (S i) -> 
  (Ξ ++ Γ ⊢ v i @ B) ->
  (Ξ ++ A :: Γ ⊢ v (S i) @ B).
Proof. 
  intros.
  apply VarIntro.
  inversion H0. subst.
  apply idx_shift_le; auto with arith.  
Defined.

Lemma weaken_var : forall Ξ Γ i A B, 
  (Ξ ++ Γ ⊢ v i @ B) -> 
  (Ξ ++ A :: Γ ⊢ shiftat (length Ξ) (v i) @ B).
Proof. 
  intros.
  simpl.
  case (le_lt_dec (length Ξ) i). intros.
  apply weaken_var_gt; auto with arith.
  intros. 
  apply weaken_var_lt; auto with arith.
Defined.  

Lemma weaken : forall Ξ Γ t A B, 
  (Ξ ++ Γ ⊢ t @ B) -> 
  (Ξ ++ A :: Γ ⊢ shiftat (length Ξ) t @ B).
Proof.
  refine 
    (fix weaken (Ξ Γ : Ctx) (t : Term) (A B : Ty) 
      (d : (Ξ ++ Γ ⊢ t @ B)) {struct t} : (Ξ ++ A :: Γ ⊢ shiftat (length Ξ) t @ B) := 
      (match t as t' 
         return (t = t' -> (Ξ ++ A :: Γ ⊢ shiftat (length Ξ) t @ B))
        with 
         | v i => _ 
         | ƛ ty r => _ 
         | r · s => _
       end) (refl_equal t))  ; intros ; subst.

  (* var *) 
  intros. apply weaken_var. auto.
  (* lam *)
  simpl.
  inversion d. subst.  
  apply ImpIntro.
  change (S (length Ξ)) with (length (ty::Ξ)).
  change (ty :: Ξ ++ A :: Γ) with ((ty :: Ξ) ++ A :: Γ).
  apply weaken. auto.

  (* app *) 
  simpl.
  inversion d. subst.  
  apply ImpElim with (A:=A0).
  apply weaken. auto.
  apply weaken. auto.
Defined.

Require Import Omega.

Lemma shift_invariance : forall t Γ i A, i >= length Γ -> (Γ ⊢ t @ A) -> shiftat i t = t.
Proof. 
  induction t ; intros ; simpl ; auto. 

  (* v *)
  inversion H0. subst. apply idx_length in H3. 
  simpl. case (le_lt_dec i n) ; intros. apply False_rec. omega. auto.
  
  (* lam *) 
  inversion H0 ; subst.
  rewrite IHt with (Γ:=t::Γ) (A:=B). auto. simpl. auto with arith. 
  inversion H0 ; subst.  auto.

  (* app *) 
  inversion H0. subst.
  rewrite IHt1 with (Γ:=Γ) (A:=A0 ⇒ A).
  rewrite IHt2 with (Γ:=Γ) (A:=A0).
  auto. auto. auto. auto. auto.
Defined.

Lemma closed_shift_invariant : forall t A i, ([] ⊢ t @ A) -> shiftat i t = t.
Proof. 
  intros. 
  apply shift_invariance with (Γ:=[]) (A :=A). simpl. auto with arith. auto.
Defined.

Lemma weaken_closed_one : forall Γ t A B, ([] ⊢ t @ A) -> (Γ ⊢ t @ A) -> (B::Γ ⊢ t @ A).
Proof.
  induction Γ ; intros.

  (* [] *)
  apply closed_shift_invariant with (i:=0) in H. 
  rewrite <- H.
  change [B] with ([]++B::[]). 
  apply weaken. simpl. auto.
  intros.
  
  (* a::Γ *)
  apply closed_shift_invariant with (i:=0) in H.
  rewrite <- H.
  change (B::a::Γ) with ([]++B::(a::Γ)). 
  apply weaken. simpl.  auto.
Defined.

Lemma weaken_closed : forall Γ t A, ([] ⊢ t @ A) -> (Γ ⊢ t @ A).
Proof.
  induction Γ. 
  intros. auto. intros. apply weaken_closed_one. auto. apply IHΓ. auto.
Defined.

Lemma idx_sameR : forall (A : Set) i a (Γ Ξ:list A), 
  length Ξ < S i -> 
  idx (S i) (Ξ++a::Γ) = idx i (Ξ++Γ).
Proof.
  refine
    (fix idx_sameR (A : Set) i a (Γ Ξ:list A) (H: length Ξ < S i) {struct Ξ} : idx (S i) (Ξ++(a::Γ)) = idx i (Ξ++Γ) := 
      (match Ξ as Ξ' return (Ξ = Ξ' -> idx (S i) (Ξ++(a::Γ)) = idx i (Ξ++Γ)) with 
         | nil => _
         | cons a g => _
       end) (refl_equal Ξ)).
  intros. subst. simpl. auto.
  intros ; subst. simpl. simpl in H. 
  destruct i.  apply le_S_n in H. apply le_n_O_eq in H.
  inversion H.  
  apply idx_sameR. auto with arith.  
Defined.  

Lemma idx_sameL : forall (s : Set) (Γ Ξ:list s) i A, 
  i < length Ξ -> 
  idx i (Ξ++A::Γ) = idx i (Ξ++Γ).
Proof. 
  induction Ξ ; intros ; simpl in *.
  unfold lt in H. apply le_n_O_eq in H. inversion H.
  destruct i. simpl. auto.   
  simpl. apply IHΞ. eauto with arith.
Defined.     

Lemma strengthen_gt : forall Ξ Γ i A B, 
  length Ξ < S i -> 
  (Ξ ++ A :: Γ ⊢ v (S i) @ B) -> 
  (Ξ ++ Γ ⊢ v i @ B).
Proof.
  intros. 
  inversion H0 ; subst ; auto.
  apply VarIntro. 
  rewrite <- idx_sameR with (a:=A) ; auto.
Defined. 

Lemma strengthen_lt : forall Ξ Γ i A B, 
  i < length Ξ -> 
  (Ξ ++ A :: Γ ⊢ v i @ B) -> 
  (Ξ ++ Γ ⊢ v i @ B).
Proof.
  intros. inversion H0. subst. 
  apply VarIntro.
  rewrite <- idx_sameL with (A:=A) ; auto. 
Defined.
