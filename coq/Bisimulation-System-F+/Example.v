Require Import SystemF. 
Require Import Eval. 
Require Import Bisimulation. 
Require Import List.

Definition Delta := 
  (fun x => match x with 
              | O => F 0
              | S n => Unit
            end).

Definition Xi := 
  (fun x => match x with 
              | O => Zero
              | S n => One
            end).


Notation "t ~> t'" := (Ev Delta t t') (at level 60).  
Notation "t ~>+ t'" := (Evplus Delta t t') (at level 60).
Notation "t ~>* t'" := (Evstar Delta t t') (at level 60). 

Notation " a :<: b " := (simulates Delta Xi a b) (at level 90). 

Theorem Prog : forall m n l, Derivation Xi [n ; l |= F m @ Xi m] -> Derivation Xi [n ; l |= Delta m @ Xi m].
Proof.
  induction m ; intros n l HF.
  simpl. auto.
  simpl. 
  typecheck.
Defined.

Theorem ProgTy : forall m, valid (Xi m) 0.
Proof.
  induction m ; simpl ; auto. 
Defined.

(* Example *) 
Definition ID1 := (Lam (Abs (TV 0) (V 0))).
Definition ID2 := (Lam (Abs (TV 0) (App (TApp ID1 (TV 0)) (V 0)))).

Lemma ID1_type : Derivation Xi [0 ;nil |= ID1 @ (All (Imp (TV 0) (TV 0)))].
Proof.
  typecheck.
Defined. 

Lemma ID2_type : Derivation Xi [0 ;nil |= ID2 @ (All (Imp (TV 0) (TV 0)))].
Proof.
  typecheck. 
Defined.

Lemma evalsto : forall t ty, (App (TApp ID1 ty) t) ~>* t.
Proof.
  intros t ty.
  apply compute_eval with (bound:=3).
  compute.
  destruct t ; auto. 
  destruct t1 ; auto.
  destruct t ; auto.  
Defined.

Ltac termeq_simp := 
  match goal with 
    | [ H : Abs _ _ = Lam _ |- _ ] => elimtype False ; inversion H 
    | [ H : Lam _ = Abs _ _ |- _ ] => elimtype False ; inversion H 
    | [ H : Lam _ = Lam _ |- _ ] => inversion H ; subst ; clear H ; termeq_simp
    | [ H : Abs _ _ = Abs _ _ |- _ ] => inversion H ; subst ; clear H ; termeq_simp
    | [ H : Abs _ _ = _ |- _ ] => progress (simpl in H) ; termeq_simp || idtac
    | [ H : _ = Abs _ _ |- _ ] => progress (simpl in H) ; termeq_simp || idtac
    | [ H : Lam _ = _ |- _ ] => progress (simpl in H) ; termeq_simp || idtac
    | [ H : _ = Lam _ |- _ ] => progress (simpl in H) ; termeq_simp || idtac
    | _ => idtac
  end.

Ltac elimtrans Htrans := 
  let Htrans' := fresh "Htrans" in
    assert (Htrans' := Htrans) ; generalize_eqs Htrans' ; induction Htrans' ; intros ; subst ; termeq_simp ;
      match goal with 
        | [ 
          HD : Derivation Xi (H (ctx _ _) ?e ?ty),
          H : ?e ~>* ?e',
          IH : trans _ _ _ _ _ -> _ = _ -> sigT2 _ _
          |- sigT2 _ _ ] => 
        apply IH ; auto ; apply sym_eq ; apply Value_refl with (Delta:=Delta) (Xi:=Xi) (A:=ty) ; simpl ; auto using Value_Abs, Value_Lam
        | _ => idtac
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


Require Import Coq.Logic.JMeq.

Theorem simulates_id1_id2 : (ID1 :<: ID2).
Proof.
  unfold ID1 in *. 
  apply simulates_base.
  cut (Derivation Xi [0 ;nil |= (Lam (Abs (TV 0) (V 0))) @ (All (Imp (TV 0) (TV 0)))]) ; [ intros Hid1ty | typecheck ].
  intros a' l Htrans.

  elimtrans Htrans.
  unfold ID2.
  exists (tysubt (Abs (TV 0) (App (TApp ID1 (TV 0)) (V 0))) 0 ty). 
  apply trans_tapp with (A:=Imp (TV 0) (TV 0)) ; auto. typecheck.
  
  apply simulates_base.
  intros a' l Htrans'.
  cut (Derivation Xi [0 ;nil |= Abs ty (V 0) @ (Imp ty ty)]) ; [ intros Hnexty | typecheck_opaque ].

  unfold tysubt in Htrans' ; fold tysubt. 
  elimtrans Htrans'. simpl.
  exists (sub (App (TApp (Lam (Abs (TV 0) (V 0))) ty) (V 0)) 0 t2).
  apply trans_app with (B:=ty) ; auto. 
  typecheck_opaque.

  apply simulates_base.
  intros a' l Htrans''.

  exists a'. simpl.
  apply trans_next with (t2:=t2).
  apply compute_eval with (bound:=3).
  simpl.
  destruct t2 ; auto. destruct t2_1 ; auto. destruct t2 ; auto. auto. 

  apply simulates_refl.
Defined.
  
