Require Import SystemF. 
Require Import Eval.
Require Import List. 
(* Require Import Cycle. *)

Ltac typecheck :=
  let Heq := fresh "Heq" in
    match goal with 
      | [ |- Derivation ?Xi (H (ctx ?n ?l) ?t ?ty) ] => 
        cut (typeof Xi n l t = Some ty)  ; [ intro Heq ; apply typeof_has_derivation in Heq; auto | simpl ; auto ]
    end.

Ltac typerefine Hyp := 
  let Heq := fresh "Heq" in 
    match type of Hyp with 
      | Derivation (H ?Xi (ctx ?n ?l) ?t ?ty) => 
        cut (typeof Xi n l t = Some ty) ; [ intros Heq ; simpl in Heq ; inversion Heq ; subst
          | compute ; (match goal with 
                         | [ |- Some ?ty' = Some _ ] => apply (type_unique Xi) with (ty2 := ty') in Hyp; try (rewrite <- Hyp) ; auto
                       end) ; typecheck]
    end.

Ltac typeunique := 
  match goal with 
    | [ H1 : (Derivation ?Xi (H (ctx ?n ?l) ?t ?ty1)) , H2 : (Derivation ?Xi (H (ctx ?n ?l) ?t ?ty2)) |- _ ] => 
      eapply (type_unique Xi n l t ty1 ty2) in H1 ; try (inversion H1) ; subst ; clear H1 
  end.

Ltac type_dec_simpl := 
  match goal with 
    | H : valid ?xty ?n |- context [ valid_dec ?xty ?n ] => case_eq (valid_dec xty n) ; intros ; subst ; simpl ; auto ; 
      try (elimtype False ; congruence) ; type_dec_simpl
    | |- context [ ty_eq_dec ?xty ?xty ] => case_eq (ty_eq_dec xty xty) ; intros ; subst ; simpl ; auto ; 
      try (elimtype False ; congruence) ; type_dec_simpl
    | _ => idtac
  end.

Ltac typecheck_opaque :=
  let Heq := fresh "Heq" in
    match goal with 
      | [ |- Derivation ?Xi (H (ctx ?n ?l) ?t ?ty) ] => 
        cut (typeof Xi n l t = Some ty)  ; [ intro Heq ; apply typeof_has_derivation in Heq; auto | 
          simpl ; type_dec_simpl ; auto ]
    end.

Section Bisimulation. 

  Variable Delta : nat -> Term.
  Variable Xi : nat -> Ty.  
  Variable Prog : forall n l m, Derivation Xi [n ; l |= F m @ Xi m] -> Derivation Xi [n ; l |= Delta m @ Xi m]. 
  Variable ProgTy : forall m, valid (Xi m) 0.
  
  Notation "t ~> t'" := (Ev Delta t t') (at level 60).  
  Notation "t ~>+ t'" := (Evplus Delta t t') (at level 60).
  Notation "t ~>* t'" := (Evstar Delta t t') (at level 60). 


Inductive label : Set := 
| lt : Term -> label 
| lty : Ty -> label.

Inductive trans : Term -> label -> Term -> Type := 
| trans_app : forall t1 t2 A B, 
  Derivation Xi [0; nil |= (Abs A t1) @ Imp A B] ->
  Derivation Xi [0; nil |= t2 @ A] -> 
  trans (Abs A t1) (lt t2) (sub t1 0 t2)
| trans_tapp : forall t ty A,
  Derivation Xi [0; nil |= (Lam t) @ All A] ->
  valid ty 0 -> 
  trans (Lam t) (lty ty) (tysubt t 0 ty)
| trans_next : forall l t1 t2 t3, t1 ~>* t2 -> trans t2 l t3 -> trans t1 l t3.

CoInductive simulates : Term -> Term -> Type := 
| simulates_base : forall a b, 
  (forall a' l, 
    trans a l a' -> {b' : Term & trans b l b' & simulates a' b'}) -> 
  simulates a b.

Notation " a :<: b " := (simulates a b) (at level 90). 

Theorem simulates_refl : forall t, t :<: t.
Proof.
  refine 
    (cofix simulates_refl (t : Term) : t :<: t := _) ;
    eapply simulates_base. 
  intros. exists a'. auto. apply simulates_refl.
Defined.

Theorem simulates_transitive : forall t1 t2 t3, (t1 :<: t2) -> (t2 :<: t3) -> t1 :<: t3.
Proof.
  refine (cofix simulates_transitive (t1 t2 t3 : Term) (H1 : t1 :<: t2) (H2 : t2 :<: t3) : t1 :<: t3 := _) ;
    apply simulates_base. 
  intros a l Htrans.
  inversion H1 ; subst. 
  apply X in Htrans.
  inversion Htrans.
  inversion H2 ; subst.
  apply X1 in H. inversion H. 
  exists x0. auto. 
  apply simulates_transitive with (t2:=x); auto.
Defined. 

Theorem evaleq_sim : forall r s, r ~>* s -> s :<: r.
Proof.
  intros r s Hstar.
  inversion Hstar.
  subst.
  apply simulates_refl. 
  apply simulates_base.
  intros a' l Htrans.
  exists a'. 
  apply trans_next with (t2:=s) ; auto. 
  apply simulates_refl.
Defined.  

Inductive reduces : Term -> Set := 
| reduces_base : 
  forall a, { b : Term & a ~>+ b } -> reduces a.

Inductive evaluates : Term -> Term -> Set := 
| evaluates_base : forall a b, a ~>* b -> notT (reduces b) -> evaluates a b.

Inductive converges : Term -> Set := 
| converges_base : forall a, {b : Term & evaluates a b} -> converges a.

Inductive diverges : Term -> Set := 
| diverges_base : forall a, (forall b, a ~>* b -> reduces b) -> diverges a.  

Lemma not_reduces_implies_value : forall t A, Derivation Xi [0; nil |= t @ A] -> notT (reduces t) -> Value t.
Proof. 
  intros t A HD Hred. unfold not in Hred.
  apply stuck_imp_value with (Delta:=Delta) (Xi:=Xi) (A:=A) ; auto.
  unfold notT ; intros Hex. 
  inversion Hex as [x P]. 
  unfold not in Hred. apply Hred.
  apply reduces_base ; exists x ; auto.
Defined.

Lemma evaluates_imp_value : forall a b A, Derivation Xi [0; nil |= a @ A] -> evaluates a b -> Value b.
Proof.
  intros a b A HD Heval.
  inversion Heval. apply not_reduces_implies_value with (A:=A) in H0. auto.
  apply evstar_preservation with (Xi:=Xi) (n:=0) (l:=nil) (ty:=A) in H ; auto using Prog, ProgTy.
Defined.

Lemma value_imp_not_diverges : forall t A, Derivation Xi [0; nil |= t @ A] -> Value t -> diverges t -> False.
Proof.
  intros t A HD Hv Hdiv.
  inversion Hdiv ; subst.  
  cut (t ~>* t) ; [ intros Hrefl ; apply H in Hrefl| idtac ].
  inversion Hrefl ; subst.
  inversion H0 ; subst.
  eapply evplus_value_stuck. eexact HD. auto. eexact H1.  
  apply Evstar_refl. auto.
Defined.

Lemma diverges_imp_not_converge : forall a, diverges a -> notT (converges a).
Proof. 
  intros a H. 
  (* -> *)
  inversion H. subst. 
  unfold not. intros HC. inversion HC. subst. inversion H1. inversion H2. subst. 
  unfold not in H4. apply H4. apply H0. auto.
Defined.

Lemma converges_imp_not_diverge : forall a, converges a -> notT (diverges a).  
Proof.
  intros.
  inversion H. subst. inversion H0. inversion H1. subst. 
  unfold not. intros Hd. apply H3. inversion Hd. subst. apply H4 in H2. auto.
Defined. 

Lemma diverges_eval : forall t s, t ~>* s -> diverges t -> diverges s.
Proof.
  intros t s Hev Hdiv.
  inversion Hdiv. subst. 
  cut (forall b : Term, s ~>* b -> reduces b).
  intros.
  apply diverges_base ; auto.
  (* next *) 
  intros b Hev'.
  cut (t ~>* b) ; [ intros Htb ; apply H in Htb ; auto | idtac ].
  apply evstar_trans with (s:=s) ; auto.
Defined. 

Lemma diverges_no_trans : forall t s l, diverges t -> trans t l s -> False.
Proof.
  refine (fix diverges_no_trans (t s : Term) l (Hdiv : diverges t) (Htrans : trans t l s) {struct Htrans} : False := _).
  destruct Htrans ; subst.
  (* Abs *) 
  cut (Value (Abs A t1)) ; [intros Hval ; apply value_imp_not_diverges with (t:=(Abs A t1)) (A:=Imp A B) ; auto | idtac ].  
  apply Value_Abs.
  (* Lam *) 
  cut (Value (Lam t)) ; [intros Hval ; apply value_imp_not_diverges with (t:=(Lam t)) (A:=All A) ; auto | idtac ].  
  apply Value_Lam.
  (* Ev *)
  apply diverges_eval with (s:=t2) in Hdiv.
  apply diverges_no_trans with (t:=t2) (l:=l) (s:=t3) ; auto.
  auto.
Defined.

Lemma trans_abs_ty : forall r s l A B, 
  Derivation Xi [0 ; nil |= r @ Imp A B] -> trans r l s -> Derivation Xi [0 ; nil |= s @ B].
Proof.
  induction 2.
  (* Abs *)
  inversion H ; subst. 
  cut (nil = nil ++ (nil (A:=Ty))) ; [ intro Gamma ; rewrite Gamma | simpl ; auto ]. 
  cut (0 = length (nil (A:=Ty))) ; [ intro Length ; rewrite Length | simpl ; auto ]. 
  apply sub_preservation with (xty:=A). intros. apply ProgTy.
  simpl ; auto. simpl ; auto.
  (* Lam *) 
  inversion H. 
  (* Ev *)
  apply IHtrans. apply evstar_preservation with (Delta:=Delta) (t:=t1).
  (* F *) 
  intros. apply Prog. auto. auto. auto.
  (* rest *)
  auto. 
Defined.

Lemma trans_lam_ty : forall r s l A B, l = lty B -> 
  Derivation Xi [0 ; nil |= r @ All A] -> trans r l s -> Derivation Xi [0 ; nil |= s @ tysub A 0 B].
Proof.
  induction 3. 
  (* Abs *) 
  inversion H0. 
  (* Lam *) 
  inversion H ; subst. 
  inversion H0 ; subst.
  apply tysub_derivation_simple ; auto.
  (* Ev *)
  apply IHtrans. auto. 
  apply evstar_preservation with (Delta:=Delta) (Xi:=Xi) (n:=0) (l:=nil) (ty:=All A) in e ; auto.
Defined.

Lemma trans_ty : forall r s l A, 
  Derivation Xi [0; nil |= r @ A ] -> trans r l s -> {B : Ty & Derivation Xi [0 ; nil |= s @ B]}.
Proof. 
  induction 2.
  (* Abs *)
  exists B. 
  apply sub_preservation_basic with (xty:=A0). auto. inversion d. subst. auto. auto.
  (* Lam *) 
  exists (tysub A0 0 ty).
  apply tysub_derivation_simple ; auto. 
  inversion d ; subst ; auto.
  (* Ev *) 
  apply IHtrans. 
  apply evstar_preservation with (Delta:=Delta) (Xi:=Xi) (n:=0) (l:=nil) (ty:=A) in e ; auto.
Defined.

Lemma trans_preservation : forall r s t u l A B, 
  Derivation Xi [0; nil |= r @ A ] -> 
  Derivation Xi [0; nil |= t @ A ] -> 
  trans r l s -> 
  trans t l u -> 
  Derivation Xi [0; nil |= s @ B ] -> 
  Derivation Xi [0; nil |= u @ B ].
Proof.
  refine 
    (fix trans_preservation r s t u l A B 
      (Hr : Derivation Xi [0; nil |= r @ A ])
      (Ht : Derivation Xi [0; nil |= t @ A ])
      (Htransr : trans r l s) 
      {struct Htransr} : trans t l u -> Derivation Xi [0; nil |= s @ B] -> Derivation Xi [0 ; nil |= u @ B] := 
      (match Htransr in (trans r0 l0 s0) 
         return (l = l0 -> r = r0 -> s = s0 -> trans t l u -> Derivation Xi [0; nil |= s @ B] -> Derivation Xi [0 ; nil |= u @ B]) 
         with 
         | trans_app t1 t2 A B Habs Hx => _ 
         | trans_tapp t ty A HLam Hv => _
         | trans_next l t1 t2 t3 Hev Htrans_next => _
       end) (refl_equal l) (refl_equal r) (refl_equal s)).

  (* induction on Abs *) 
  generalize r s t u l A B Hr Ht Htransr.
  refine 
    (fix trans_preservation_abs r s t u l A B 
      (Hr : Derivation Xi [0; nil |= r @ A ])
      (Ht : Derivation Xi [0; nil |= t @ A ])
      (Htransr : trans r l s) 
      (Hleq : l = lt t2) 
      (Hreq : r = Abs A0 t1) 
      (Hseq : s = sub t1 0 t2) 
      (Htranst : trans t l u) 
      (Hs : Derivation Xi [0; nil |= s @ B]) 
      {struct Htranst} : Derivation Xi [0 ; nil |= u @ B] := 
      (match Htranst in (trans t' l' u') 
         return (l = l' -> t = t' -> u = u' -> Derivation Xi [0 ; nil |= u @ B]) 
         with 
         | trans_app t1' t2' A' B' Habs' Hx' => _ 
         | trans_tapp t' ty' A' HLam' Hv' => _
         | trans_next l' t1' t2' t3' Hev' Htrans_next' => _
       end) (refl_equal l) (refl_equal t) (refl_equal u)) ; intros.

  (* Abs - Abs *) 
  clear trans_preservation ; clear trans_preservation_abs.
  inversion Hleq ; subst. 
  cut (Imp A' B' = Imp A0 B0) ; [intros Heq ; inversion Heq ; clear Heq ; subst | auto ].
  apply sub_preservation_basic with (xty:=A0) ; auto.
  cut (B0 = B1) ; [ intros HeqB ; subst ;auto | auto ].
  inversion Habs' ; subst. auto.
  inversion Habs ; subst.
  apply sub_preservation_basic with (t:=t1) (s:=t2) (ty:=B0) in H8 ; auto.
  apply type_unique with (Xi:=Xi) (n:=0) (L:=nil) (t:=sub t1 0 t2) ; auto.
  typeunique ; auto. typeunique ; auto.
  (* Abs - Lam *) 
  elimtype False ; subst ; congruence.
  (* Abs - Ev *)
  apply evstar_preservation with (Xi:=Xi) (n:=0) (l:=nil) (ty:=A1) in Hev' ; auto.
  apply (trans_preservation_abs r0 s0 t2' u0 l0 A1 B1 Hr0 Hev' Htransr0) ; auto.
  rewrite H1 ; rewrite H. auto. rewrite <- H0 ; auto.

  (* Induction on Lam *) 
  generalize r s t u l A B Hr Ht Htransr.
  refine (fix trans_preservation_lam r s t u l A B 
      (Hr : Derivation Xi [0; nil |= r @ A ])
      (Ht : Derivation Xi [0; nil |= t @ A ])
      (Htransr : trans r l s) 
      (Hleq : l = lty ty) 
      (Hreq : r = Lam t0) 
      (Hseq : s = tysubt t0 0 ty) 
      (Htranst : trans t l u) 
      (Hs : Derivation Xi [0; nil |= s @ B]) 
      {struct Htranst} : Derivation Xi [0 ; nil |= u @ B] := 
      (match Htranst in (trans t' l' u') 
         return (l = l' -> t = t' -> u = u' -> Derivation Xi [0 ; nil |= u @ B]) 
         with 
         | trans_app t1' t2' A' B' Habs' Hx' => _ 
         | trans_tapp t' ty' A' HLam' Hv' => _
         | trans_next l' t1' t2' t3' Hev' Htrans_next' => _
       end) (refl_equal l) (refl_equal t) (refl_equal u)) ; intros.

  (* Lam - Abs *) 
  elimtype False ; subst ; congruence.
  (* Lam - Lam *) 
  clear trans_preservation_lam ; clear trans_preservation.
  cut (All A' = All A0) ; [intros Heq ; inversion Heq ; clear Heq ; subst | auto ].
  inversion Ht0 ; subst.
  inversion Hr0 ; subst.
  apply tysub_derivation_simple with (tyx:=ty') in H1 ; auto. 
  apply tysub_derivation_simple with (tyx:=ty') in H2 ; auto.
  cut (B0 = tysub ty0 0 ty') ; [intros Heq ; subst | auto ].
  auto.
  inversion H ; subst. 
  apply type_unique with (ty1:=tysub ty0 0 ty') in Hs ; auto.
  auto. auto. auto. auto.
  apply type_unique with (ty1:=All A0) in Hr0 ; subst ; auto.
  apply type_unique with (ty1:=All A') in Ht0 ; subst ; auto.

  (* Lam - Ev *) 
  apply evstar_preservation with (Xi:=Xi) (n:=0) (l:=nil) (ty:=A1) in Hev'; auto. 
  apply (trans_preservation_lam r0 s0 t2' u0 l' A1 B0 Hr0 Hev'). 
  rewrite <- H. auto. rewrite Hleq in H. auto. auto. auto.  
  rewrite <- H1 in Htrans_next'. auto. auto. rewrite H0 in Ht0. auto.  

  (* induction on Ev *) 
  intros Hleq Hreq Hseq Htranst Hs. 
  apply trans_preservation with (r:=t2) (s:=s) (t:=t) (A:=A) (B:=B) (l:=l) ; auto.
  apply evstar_preservation with (Xi:=Xi) (n:=0) (l:=nil) (ty:=A) in Hev ; auto. 
  rewrite Hreq in Hr. auto.
  rewrite <- Hleq in Htrans_next.
  rewrite <- Hseq in Htrans_next. 
  auto.
Defined. 

Lemma trans_preservation_ex : forall r s t u l A, 
  Derivation Xi [0; nil |= r @ A ] -> 
  Derivation Xi [0; nil |= t @ A ] -> 
  trans r l s -> 
  trans t l u -> { B : Ty & Derivation Xi [0; nil |= s @ B ] & Derivation Xi [0; nil |= u @ B ]}.
Proof.
  intros. 
  assert (Hty := H1) ; auto.
  apply trans_ty with (A:=A) in Hty; auto. 
  inversion Hty.
  exists x ; auto.
  apply trans_preservation with (r:=r) (s:=s) (t:=t) (l:=l) (A:=A) ; auto.
Defined.  

 
Inductive bisimulates : Term -> Term -> Type := 
| bisimulates_base : forall s t, s :<: t -> t :<: s -> bisimulates t s. 

Notation " a :~: b " := (bisimulates a b) (at level 90).

(* This is necessary for contextual equivalence and used in the literature *)
Axiom converges_or_diverges : forall a, converges a + diverges a.

End Bisimulation. 

