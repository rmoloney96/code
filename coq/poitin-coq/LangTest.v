Require Import MyUtils. 
Require Import Atom. 
Require Import List. 
Require Import Metatheory.

(* Infix "==" := eq_atom_dec (at level 90). *)

(* Instead of notation, we can use a type-class with the following file *)
(* However, we should probably stick all decidable equalities into the class *)
(* and get something like MLs eq types. *) 
(* Require Import EqAtomDec. *) 

Inductive pat : Set := 
| Inl : pat
| Inr : pat.

(* preterms *)
Inductive term : Set := 
| bvar : nat -> term
| fvar : atom -> term
| abs : term -> term
| fp : term -> term 
| app : term -> term -> term
| prod : term -> term -> term
| inl : term -> term
| inr : term -> term
| unit : term
| cas : term -> term -> term -> term.
Coercion bvar : nat >-> term.
Coercion fvar : atom >-> term.

Definition term_eq_dec : forall t t' : term, {t = t'} + {t <> t'}.
Proof.
  decide equality. auto with arith. auto using eq_atom_dec.
Defined.

Notation "`case` t `of` { A | B }" := (cas t A B).

(* nat := 1 + nat *)
Definition Zero := inl unit. 
Definition Succ := (fun x => inr x).
(* bool := 1 + 1 *) 
Definition T := inl unit.
Definition F := inr unit.

Definition eqn := 
  fp 
  (abs (abs 
    (`case` 1 `of`  
      { (`case` 1 `of` { T | F })
        | (`case` 1 `of` { F | (app (app 4 1) 0)} )
      }))).

Fixpoint fv (t:term) := 
  match t with
    | bvar n => {}
    | fvar a => singleton a
    | abs t' => fv t'
    | fp t' => fv t'
    | app m n => (fv m) `union` (fv n)
    | prod m n => (fv m) `union` (fv n) 
    | inl l => fv l
    | inr r => fv r
    | unit => {}
    | cas x l r => (fv x) `union` (fv l) `union` (fv r) 
  end.

Fixpoint subst (z : atom) (u : term) (e : term) {struct e} : term :=
  match e with
    | bvar i => bvar i
    | fvar v => if v == z then u else (fvar v)
    | abs e1 => abs (subst z u e1)
    | app e1 e2 => app (subst z u e1) (subst z u e2)
    | prod e1 e2 => prod (subst z u e1) (subst z u e2)
    | inl l => inl (subst z u l) 
    | inr r => inr (subst z u r)
    | cas e e1 e2 => 
      cas (subst z u e) (subst z u e1) (subst z u e2)
    | fp e1 => fp (subst z u e1)
    | unit => unit
  end.
 
Notation "[ z ~> u ] e" := (subst z u e) (at level 68).

Fixpoint open_rec (k : nat) (u : term) (e : term) {struct e} : term :=
  match e with
    | bvar i => if k === i then u else (bvar i)
    | fvar x => fvar x
    | abs e1 => abs (open_rec (S k) u e1)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
    | fp e => fp (open_rec k u e)
    | prod a b => prod (open_rec k u a) (open_rec k u b)
    | inl l => inl (open_rec k u l) 
    | inr r => inr (open_rec k u r)
    | cas e e1 e2 => 
      cas (open_rec k u e)
      (open_rec (S k) u e1) 
      (open_rec (S k) u e2)
    | unit => unit
  end.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

(* opening that just replaces an outermost abstraction *)
Definition open e u := open_rec 0 u e.
 
Definition open_times n e u := 
  match n with 
    | 0 => e
    | S n' => open_rec n' u e
  end.

Inductive lc : term -> Prop := 
| lc_fvar : forall x, lc (fvar x)
| lc_abs : forall L e,
  (forall x:atom, x `notin` L -> lc (open e (fvar x))) ->
  lc (abs e)
| lc_app : forall e1 e2,
  lc e1 ->
  lc e2 ->
  lc (app e1 e2)
| lc_unit : lc unit
| lc_prod : forall e1 e2, lc e1 -> lc e2 -> lc (prod e1 e2)
| lc_inl : forall e, lc e -> lc (inl e)
| lc_inr : forall e, lc e -> lc (inr e)
| lc_cas : forall L e e1 e2, 
  lc e ->
  (forall x:atom, x `notin` L -> lc (open e1 (fvar x))) -> 
  (forall x:atom, x `notin` L -> lc (open e2 (fvar x))) ->
  lc (cas e e1 e2).
Hint Constructors lc.

Lemma open_lc_diff : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof.
  induction e ; intros j v i u Hdiff ; try (f_equal ; intros ; eauto ; congruence). 
  (* bvar *) 
  simpl in *. case (j === n) ; case (i === n) ; intros ; auto with arith ; try congruence. subst. simpl in H. 
  case_eq (n===n). intros. rewrite H0 in H. auto. intros. congruence.
  (* abs *) 
  intros. simpl in *. f_equal. apply (IHe (S j) v (S i) u). omega. inversion H. auto.
  (* fp *)
  intros. simpl in *. f_equal. eapply IHe. eauto. inversion H. eauto.
  (* app *)
  intros ; simpl in * ; f_equal ; [ eapply IHe1 ; eauto ; inversion H ; eauto | eapply IHe2 ; eauto ; inversion H ; eauto].
  (* prod *)
  intros ; simpl in * ; f_equal ; [ eapply IHe1 ; eauto ; inversion H ; eauto | eapply IHe2 ; eauto ; inversion H ; eauto].
  (* inl *)
  intros. simpl in *. f_equal. eapply IHe. eauto. inversion H. eauto.
  (* inr *) 
  intros. simpl in *. f_equal. eapply IHe. eauto. inversion H. eauto.
  (* case *) 
  intros. simpl in *. f_equal ;  
  [ eapply (IHe1 j v i u) ; eauto ; inversion H ; eauto | 
    eapply (IHe2 (S j) v (S i) u)  ; eauto ; inversion H ; eauto | 
      eapply (IHe3 (S j) v (S i) u) ; eauto ; inversion H ; eauto ].
Defined. 


Lemma open_lc : forall k u e, lc e -> e = {k ~> u} e.
Proof.
  intros.  generalize dependent k.
  induction H ; simpl ; try (intros ; f_equal ; intuition).
  (* abs *)
  pick fresh x for L ; intros ;
  apply open_lc_diff with (i := S k) (j := 0) (u := u) (v := (fvar x)) ; auto ;
  unfold open in H0 ; eapply H0 ; auto.
  (* cas right *)
  pick fresh x for L ; intros.
  apply open_lc_diff with (i := S k) (j := 0) (u := u) (v := (fvar x)) ; auto. 
  unfold open in H1 ; apply H1 ; auto.
  (* cas left *)
  pick fresh x for L ; intros.
  apply open_lc_diff with (i := S k) (j := 0) (u := u) (v := (fvar x)) ; auto. 
  unfold open in H3 ; apply H3 ; auto.
Defined. 

Lemma subst_open_rec : forall e1 e2 u x k,
  lc u ->[x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
  induction e1; intros e2 u x k Hlc; try (simpl in *; f_equal; auto ; fail).
  (* bvar *) 
  simpl ; case (k === n) ; intros ; auto.
  (* fvar *) 
  simpl ; case (a == x) ; intros ; eapply open_lc ; auto.
Defined.

Lemma subst_open_var : forall (x y : atom) u e,
  y <> x ->
  lc u ->
  open ([x ~> u] e) y = [x ~> u] (open e y).
Proof.
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec with (e2 := y).
  simpl.
  destruct (y == x).
    Case "y=x".
    destruct Neq. auto.
    Case "y<>x".
    auto.
  auto.
Qed.

Lemma subst_lc : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He ; try (simpl in * ; f_equal ; eauto ; intuition ; fail).
  Case "lc_var".
   simpl.
   destruct (x0 == x).
     auto.
     auto.
  Case "lc_abs".
   simpl.
    apply lc_abs with (L := L `union` singleton x).
    intros x0 Fr.
    rewrite subst_open_var. auto. auto. auto.
  Case "lc_app".
   simpl.
    apply lc_cas with (L := L `union` singleton x). eauto. 
    (* inl *)
    intros x0 Fr. 
    rewrite subst_open_var. auto. auto. auto.
    (* inr *)
    intros x0 Fr. 
    rewrite subst_open_var. auto. auto. auto.
Qed.

(* time to make observables *) 
Inductive value : exp -> Prop :=
  | value_abs : forall e,
      lc (abs e) ->
      value (abs e).

Inductive eval : exp -> exp -> Prop :=
  | eval_beta : forall e1 e2,
      lc (abs e1) ->
      value e2 ->
      eval (app (abs e1) e2) (open e1 e2)
  | eval_app_1 : forall e1 e1' e2,
      lc e2 ->
      eval e1 e1' ->
      eval (app e1 e2) (app e1' e2)
  | eval_app_2 : forall e1 e2 e2',
      value e1 ->
      eval e2 e2' ->
      eval (app e1 e2) (app e1 e2').



