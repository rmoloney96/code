Require Import MyUtils. 
Require Import Atom. 
Require Import List. 
Require Import Metatheory.

(* 

Case (cas) is written such that it only destructures a single sum.
Evaluation of a case statement consists in application of the left or
right branch in a single abstraction to the term inside of inl/inr
constructor.  Applications are of arity one.

Types such as Nat have to be represented as: 

Nat = Z | S Nat  ->   Nat := inl unit OR inr Nat

List is represented as: 

List_A := Nil | Cons A List_A  ->  List_A := inl unit OR inr (prod A List_A)

This is a very inconvenient syntax, but yields very efficient proofs. 

*) 

(* preterms *)
Inductive term : Set := 
| bvar : nat -> term
| fvar : atom -> term
| abs : term -> term
| fp : term -> term 
| app : term -> term -> term
| proj1 : term -> term 
| proj2 : term -> term
| prod : term -> term -> term
| inl : term -> term
| inr : term -> term
| unit : term
| cas : term -> term -> term -> term.
Coercion bvar : nat >-> term.
Coercion fvar : atom >-> term.


(* this is even easier to write than the SML equivalent! *)
Definition term_eq_dec : forall t t' : term, {t = t'} + {t <> t'}.
Proof.
  decide equality. auto with arith. auto using eq_atom_dec.
Defined.

Eval compute in (3 + 5).

Fixpoint fv (t:term) := 
  match t with
    | bvar n => {}
    | fvar a => singleton a
    | abs t' => fv t'
    | fp t' => fv t'
    | app m n => (fv m) `union` (fv n)
    | proj1 t' => fv t'
    | proj2 t' => fv t'
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
    | proj1 t' => proj1 (subst z u t') 
    | proj2 t' => proj2 (subst z u t') 
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

(* replace a bvar with a term *)
Fixpoint open_rec (k : nat) (u : term) (e : term) {struct e} : term :=
  match e with
    | bvar i => if k === i then u else (bvar i)
    | fvar x => fvar x
    | abs e1 => abs (open_rec (S k) u e1)
    | fp e => fp (open_rec (S k) u e)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
    | proj1 t => proj1 (open_rec k u t) 
    | proj2 t => proj2 (open_rec k u t)
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

(* local closure: well formedness wrt lambda abstraction *)
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
| lc_fp : forall L e,
  (forall x:atom, x `notin` L -> lc (open e (fvar x))) ->
  lc (fp e)
| lc_proj1 : forall e, 
  lc e -> 
  lc (proj1 e)
| lc_proj2 : forall e, 
  lc e -> 
  lc (proj2 e)
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
  induction e ; intros j v i u Hdiff ; try ( intros ; simpl in * ; f_equal ; intros ; inversion H ; eauto ; fail). 
  (* bvar *) 
  simpl in *. case (j === n) ; case (i === n) ; intros ; auto with arith ; try congruence. subst. simpl in H. 
  case_eq (n===n). intros. rewrite H0 in H. auto. intros. congruence.
Defined.

Lemma open_lc : forall k u e, lc e -> e = {k ~> u} e.
Proof.
  intros.  generalize dependent k.
  induction H ; simpl ; try (intros ; f_equal ; intuition)
    ; pick fresh x for L ; intros ;
      apply open_lc_diff with (i := S k) (j := 0) (u := u) (v := (fvar x)) ; auto ;
        unfold open in H0 ; eauto ; firstorder.
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

Ltac pick_fresh Y :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
    set (Y := (A `union` B)).

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
  Case "lc_fp".
   simpl.
    apply lc_fp with (L := L `union` singleton x).
    intros x0 Fr.
    rewrite subst_open_var. auto. auto. auto.
  Case "lc_cas".
   simpl.
    apply lc_cas with (L := L `union` singleton x) ; auto.
    (* inl *)
    intros x0 Fr.
    rewrite subst_open_var. auto. auto. auto.
    (* inr *)
    intros x0 Fr.
    rewrite subst_open_var. auto. auto. auto.
Defined.

(* single step operational semantics *)
Inductive eval : term -> term -> Prop :=
| eval_beta : forall e1 e2,
  lc (abs e1) ->
  lc e2 ->
  eval (app (abs e1) e2) (open e1 e2)
| eval_fp : forall e1, 
  lc (fp e1) -> 
  eval (fp e1) (open e1 (fp e1))
| eval_proj1 : forall e1 e2, 
  lc e1 -> 
  lc e2 ->
  eval (proj1 (prod e1 e2)) e1
| eval_proj2 : forall e1 e2, 
  lc e1 -> 
  lc e2 -> 
  eval (proj2 (prod e1 e2)) e2
| eval_cas_1 : forall e e1 e2,
  lc (inl e) -> 
  lc (abs e1) ->
  lc (abs e2) -> 
  eval (cas (inl e) e1 e2) (open e1 e)
| eval_cas_2 : forall e e1 e2,
  lc (inr e) -> 
  lc (abs e1) -> 
  lc (abs e2) ->
  eval (cas (inr e) e1 e2) (open e2 e)
(* experiments / atomic evaluation contexts ala Felleisen *)
| eval_proj1_exp : forall e e', 
  eval e e' -> 
  eval (proj1 e) (proj1 e')
| eval_proj2_exp : forall e e', 
  eval e e' -> 
  eval (proj2 e) (proj2 e')
| eval_app_exp : forall e1 e1' e2,
  lc e2 ->
  eval e1 e1' ->
  eval (app e1 e2) (app e1' e2)  
| eval_cas_exp : forall e e' e1 e2, 
  lc (abs e1) -> 
  lc (abs e2) -> 
  eval e e' ->
  eval (cas e e1 e2) (cas e' e1 e2).

Hint Constructors eval.

Lemma subst_fresh : forall (x : atom) e u,
  x `notin` fv e -> [x ~> u] e = e.
Proof.
  intros x e u H.
  induction e ; try (simpl in * ; f_equal ; auto ; auto).
  Case "fvar".
   simpl.
   destruct (a == x).
    Case "a=x".
      subst. simpl fv in H. decideFSet.
    Case "a<>x".
      auto.
Qed.

Lemma subst_intro : forall (x : atom) u e,
  x `notin` (fv e) ->
  lc u ->
  open e u = [x ~> u](open e x).
Proof.
  intros x u e H J.
  unfold open.
  rewrite subst_open_rec; auto.
  simpl.
  destruct (x == x).
  Case "x = x".
    rewrite subst_fresh; auto.
  Case "x <> x".
    destruct n; auto.
Qed.

Lemma open_abs : forall e u,
  lc (abs e) ->
  lc u ->
  lc (open e u).
Proof with auto using subst_lc.
  intros e u H J.
  inversion H; subst.
  pick fresh y for (L `union` (fv e)).
  rewrite (subst_intro y). eauto using subst_lc. eauto. eauto. 
Qed.
 
Lemma open_fp : forall e u, 
  lc (fp e) -> 
  lc u -> 
  lc (open e u).
Proof with auto using subst_lc.
  intros e u H J.
  inversion H; subst.
  pick fresh y for (L `union` (fv e)).
  rewrite (subst_intro y). eauto using subst_lc. eauto. eauto.
Defined. 

Lemma eval_regular : forall e1 e2,
  eval e1 e2 -> lc e1 /\ lc e2.
Proof.
  intros e1 e2 H ; induction H; intuition ; auto using open_abs, open_fp.
  (* inl *)
  apply lc_cas with (L:= (fv e1)) ; auto ;
    intros ; apply open_abs ; auto. 
  apply open_abs ; auto ; inversion H ; auto.
  (* inr *)
  apply lc_cas with (L:= (fv e2)) ; auto ;
    intros ; apply open_abs ; auto. 
  apply open_abs ; auto ; inversion H ; auto. 
  (* cas context *)
  apply lc_cas with (L:= (fv (cas e e1 e2))) ; auto ;
  intros ; apply open_abs ; auto ; f_equal ; 
    try (apply open_abs ; auto ; inversion H ; auto).
  apply lc_cas with (L:= (fv (cas e e1 e2))) ; auto ;
  intros ; apply open_abs ; auto ; f_equal ; 
    try (apply open_abs ; auto ; inversion H ; auto).
Qed.

(* reduction relation *)
Inductive reduces : term -> Prop := 
| reduces_base : 
  forall a, (exists b, eval a b) -> reduces a.

(* multi-step reduction relation *)
Inductive multistep : term -> term -> Prop := 
| multistep_refl : forall a, multistep a a
| multistep_eval : forall a b, eval a b -> multistep a b.

Inductive evaluates : term -> term -> Prop := 
| evaluates_base : forall a b, multistep a b -> ~(reduces b) -> evaluates a b.

Inductive converges : term -> Prop := 
| converges_base : forall a, (exists b, evaluates a b) -> converges a.

Inductive diverges : term -> Prop := 
| diverges_base : forall a, (forall b, multistep a b -> reduces b) -> diverges a.

Hint Constructors evaluates multistep converges diverges.

Lemma diverges_imp_not_converge : forall a, diverges a -> ~(converges a).
Proof. 
  intros a H. 
  (* -> *)
  inversion H. subst. 
  unfold not. intros HC. inversion HC. subst. inversion H1. inversion H2. subst. 
  unfold not in H4. apply H4. apply H0. auto.
Defined.

Lemma converges_imp_not_diverge : forall a, converges a -> ~(diverges a).  
Proof.
  intros.
  inversion H. subst. inversion H0. inversion H1. subst. 
  unfold not. intros Hd. apply H3. inversion Hd. subst. apply H4 in H2. auto.
Defined. 

(* omega diverges, for fun *) 
Lemma omega_diverges : diverges (fp 0). 
Proof.
  intros. constructor. intros. inversion H. subst.
  (* ->* refl *)
  constructor. exists (open 0 (fp 0)). apply eval_fp.
  apply lc_fp with (L := {}). intros. compute. apply lc_fvar.
  subst. 
  (* ->* eval *)
  constructor. 
  inversion H0. subst. compute in *.
  exists (fp 0). auto. 
Defined.

(* this formulation of diverges is much easier to work with *)
CoInductive diverges' : term -> Prop := 
| diverges'_base : forall x, (exists y, eval x y -> diverges' y) -> diverges' x.

Lemma omega_diverges' : diverges' (fp 0). 
Proof. 
  refine (cofix div : diverges' (fp 0) := _). 
  constructor. exists (open 0 (fp 0)). intros. compute in *. auto.
Defined.

Inductive value : term -> Prop := 
| value_fv : forall a, value (fvar a)
| value_abs : forall t, lc (abs t) -> value (abs t)
| value_unit : value unit
| value_prod : forall t1 t2, lc (prod t1 t2) -> value (prod t1 t2)
| value_inl : forall t, lc (inl t) -> value (inl t)
| value_inr : forall t, lc (inr t) -> value (inr t).

Hint Constructors value.

Lemma value_not_reduces : forall t, value t -> ~ (reduces t).
Proof.
  induction t ; intros Hv ; inversion Hv ; unfold not ; intros Hr ; inversion Hr as [x He] ; 
    subst ; inversion He as [x H] ; inversion H.
Defined.
  
Lemma reduces_not_value : forall t, reduces t -> ~ value t. 
Proof.
  induction t ; intros Hr ; inversion Hr as [x He] ; subst ; unfold not ; intros Hv ; inversion Hv;
    subst ; inversion He as [x H] ; inversion H.
Defined.

Lemma value_or_reduces : forall t, lc t -> reduces t \/ value t. 
Proof. 
  intros. induction t ; try (right ; auto ; fail) ; try (left ; auto ; fail). 
  inversion H. left. constructor. exists (open t (fp t)). auto.
  left. inversion H. apply IHt1 in H2. apply IHt2 in H3. 
  inversion H2. constructor. inversion H4. inversion H5. 
  exists (app x t2). apply eval_app_exp. inversion H ; auto. auto.
  subst. inversion H4. subst. 
Defined.
  

Inductive active : term -> Prop := 
| active_prod : forall t1 t2, lc (prod t1 t2) -> active (prod t1 t2)
| active_inl : forall t, lc (inl t) -> active (inl t)
| active_inr : forall t, lc (inr t) -> active (inr t).

Inductive passive : term -> Prop := 
| passive_unit : passive unit
| passive_abs : forall t, lc (abs t) -> passive (abs t)
| passive_fp : forall t, lc (fp t) -> passive (fp t).

Inductive label : Set := 
| label_fvar : forall (b : atom), label
| label_fst 
| label_snd 
| label_inl 
| label_inr
| label_fp
| label_app : forall (b : term), label.

(* we need an arbitrary divergent term of active type *)
Definition inf := inl (fp (inl 0)).

(* create a transition system for our functional programs *)
Inductive trans : term -> label -> term -> Prop :=
| trans_fvar : forall (x : atom), trans x (label_fvar x) x
| trans_fst : forall t1 t2, lc (prod t1 t2) -> trans (prod t1 t2) label_fst t1
| trans_snd : forall t1 t2, lc (prod t1 t2) -> trans (prod t1 t2) label_snd t2
| trans_inl : forall t, lc (inl t) -> trans (inl t) label_inl t 
| trans_inr : forall t, lc (inr t) -> trans (inr t) label_inr t
(* | trans_fp : forall t, lc (fp t) -> trans (fp t) label_fp  (open t (fp t)) *)
| trans_app : forall t1 t2, lc (abs t1) -> lc t2 -> trans (abs t1) (label_app t2) (app (abs t1) t2)
| trans_next : forall t1 t2 t3 l, eval t1 t2 -> trans t2 l t3 -> trans t1 l t3.

Hint Constructors trans.

Ltac lc_solve := 
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
    match goal with 
      | |- lc (fp _) =>
        eapply lc_fp with (L:=(A `union` B)) ; intros ; compute ; try lc_solve
      | |- lc (abs _) =>
        eapply lc_abs with (L:=(A `union` B)) ; intros ; compute ; try lc_solve
      | |- lc (cas _ _ _) => 
        eapply lc_cas with (L:=(A `union` B)) ; intros ; compute ; try lc_solve
      | |- lc (fvar _) => 
        apply lc_fvar ; try lc_solve
      | |- lc (inl _) => 
        apply lc_inl ; try lc_solve
      | |- lc (inr _) => 
        apply lc_inr ; try lc_solve
      | |- lc unit => 
        apply lc_unit ; try lc_solve
      | |- lc (prod _ _) => 
        apply lc_prod ; try lc_solve
      | |- lc (app _ _) => 
            apply lc_app ; try lc_solve
      | |- lc (proj1 _) => 
        apply lc_proj1 ; try lc_solve 
      | |- lc (proj2 _) => 
        apply lc_proj2 ; try lc_solve
    end.

(* terms remain locally closed by undergoing a transition *)
Lemma trans_regular : forall t1 t2 l, trans t1 l t2 -> lc t1 /\ lc t2.
Proof.
  intros t1 t2 l H. induction H ; subst ; try (split ; auto ; inversion H ; subst ; auto ; fail ).
  (* fp *) 
(*  split. auto. apply open_fp. auto. auto. *)
  (* next *)
  split. intros. auto. inversion IHtrans. auto. 
  apply eval_regular in H ; inversion H ; auto. inversion IHtrans. auto.
Defined. 
Hint Resolve trans_regular.

CoInductive simulates : term -> term -> Prop := 
| simulates_base : forall a b, 
  (forall a' l, 
    trans a l a' -> 
    (exists b', trans b l b' /\ simulates a' b')) -> 
  simulates a b.

CoInductive bisimulates : term -> term -> Prop := 
| bisimulates_base : forall a b, 
  (forall a' l, 
    trans a l a' -> 
    (exists b', trans b l b' /\ bisimulates a' b')) -> 
  (forall b' l, 
    trans b l b' -> 
    (exists a', trans a l a' /\ bisimulates a' b')) -> 
  bisimulates a b.

Lemma bisimulation_impl_simulation_right : forall a b, bisimulates a b -> simulates a b.
Proof.
  refine 
    (cofix bisim (a b : term) (Hb : bisimulates a b) : simulates a b := 
      _).
  inversion Hb. subst. eapply simulates_base. 
  intros. apply H in H1. inversion H1. inversion H2. 
  exists x. split. auto. apply bisim. auto.
Defined.

Lemma bisimulation_impl_simulation_left : forall a b, bisimulates a b -> simulates b a.
Proof.
  refine 
    (cofix bisim (a b : term) (Hb : bisimulates a b) : simulates b a := 
      _).
  inversion Hb. subst. eapply simulates_base. 
  intros. apply H0 in H1. inversion H1. inversion H2. 
  exists x. split. auto. apply bisim. auto.
Defined.

Ltac trans_prove_lc := 
  match goal with 
    | H : trans ?x _ _ |- lc ?x => apply trans_regular in H ; inversion H ; auto
    | H : trans _ _ ?x |- lc ?x => apply trans_regular in H ; inversion H ; auto
  end.

Lemma bisimulation_refl : forall a, lc a -> bisimulates a a.
Proof.
  refine 
    (cofix bisim (a : term) (H: lc a) : bisimulates a a := _) ;
  eapply bisimulates_base.
  
  intros. exists a'. split ; auto. apply bisim ; trans_prove_lc.
  
  intros. exists b'. split ; auto. apply bisim ; trans_prove_lc.
Defined.

Lemma bisimulation_symm : forall a b, lc a -> lc b -> bisimulates a b -> bisimulates b a.
Proof.
  refine 
    (cofix bisim (a b:term) (Ha : lc a) (Hb : lc b) (Hbi : bisimulates a b) : bisimulates b a := 
      _). 
  apply bisimulates_base. 

  (* left *)
  intros.
  inversion Hbi. subst. cut (trans b l a') ; intros ; auto.
  apply H1 in H ; subst. inversion H. inversion H3.  
  exists x. split ; auto. apply bisim ; try trans_prove_lc ; auto.

  (* right *)
  intros.
  inversion Hbi. subst. cut (trans a l b') ; intros ; auto.
  apply H0 in H ; subst. inversion H. inversion H3.  
  exists x. split ; auto. apply bisim ; try trans_prove_lc ; auto.
Defined.

Lemma bisimulation_trans : forall a b c, lc a -> lc b -> lc c -> bisimulates a b -> bisimulates b c -> bisimulates a c.
Proof.
  refine
    (cofix bisim (a b c:term) (Ha : lc a) (Hb : lc b) (Hc : lc c) (Hbi_ab  : bisimulates a b) (Hbi_bc : bisimulates b c) : bisimulates a c := _)
    ; apply bisimulates_base.
  intros.
  inversion Hbi_ab ; inversion Hbi_bc ; subst.
  cut (trans a l a') ; intros ; auto. 
  apply H0 in H2. inversion H2. inversion H3. 
  cut (trans b l x) ; intros ; auto.
  apply H4 in H8. inversion H8. inversion H9. 
  exists x0. split ; auto. eapply bisim with (b:=x) ; try trans_prove_lc ; auto. 
  
  intros.
  inversion Hbi_ab ; inversion Hbi_bc ; subst.
  cut (trans c l b') ; intros ; auto. 
  apply H5 in H2. inversion H2. inversion H3. 
  cut (trans b l x) ; intros ; auto.
  apply H1 in H8. inversion H8. inversion H9. 
  exists x0. split ; auto. eapply bisim with (b:=x) ; try trans_prove_lc ; auto. 
Defined. 

Ltac remove_trans_false := 
  match goal with 
    | H : trans ?a ?l ?b, H0 : trans ?a' ?l' ?b' |- _ => 
      inversion H ; clear H ; inversion H0 ; clear H0 ; subst ; try congruence ; auto
    | H : eval (fvar ?a) ?b |- _ => inversion H ; clear H
    | H : eval (inl ?a) ?b |- _ => inversion H ; clear H
    | H : eval (inr ?a) ?b |- _ => inversion H ; clear H
    | H : eval (prod ?a ?b) ?c |- _ => inversion H ; clear H
  end.

Lemma testing : forall x y, x < y -> x <= y. 
Proof. 
  intros. inversion H ; subst. 
  auto with arith. inversion H0. subst. auto. auto with arith.
Defined.

Lemma lc_abs_z : forall n, lc (abs (bvar n)) -> n = 0. 
Proof.
  intros. destruct n. inversion H ; subst ; reflexivity.
  inversion H. compute in H1. subst.
  pick fresh x for L. apply (H1 x) in Fr. inversion Fr.
Defined. 

Lemma lc_fp_z : forall n, lc (fp (bvar n)) -> n = 0.
Proof.  
  intros. destruct n. inversion H. subst ; reflexivity.
  inversion H. compute in H1. subst.
  pick fresh x for L. apply (H1 x) in Fr. inversion Fr.
Defined.

Lemma eval_imp_bisimulation : forall a b, eval a b -> bisimulates a b.
Proof. 
  refine (cofix bisim (a b : term) (Heval : eval a b) : bisimulates a b := _) ; apply bisimulates_base. 

  intros.
 
  generalize dependent b. generalize dependent a.
  induction a; intros ; inversion Heval ; subst.
  induction a. apply lc_fp_z in H1. subst. compute in *. inversion Heval. subst.
  inversion H. subst. 


  intros. 
  inversion H. subst ; inversion Heval ; subst. subst. 
  inversion Heval. subst. inversion Heval. subst.
  inversion Heval. subst. inversion Heval. subst. 
  exists (app (abs b) t2). split. induction a. inversion H0. inversion Heval.
    apply IHa.
    apply lc_abs_z in H0.
  induction e1. apply lc_abs_z in H2.subst. compute in *. apply trans_app ; auto.
  inversion 
  inversion H2. subst.
Defined.  


Lemma simulation_pair_imp_bisimulation : forall a b, simulates a b -> simulates b a -> bisimulates a b.
Proof.
  refine 
    (cofix bisim (a b : term) (Hsima : simulates a b) (Hsimb : simulates b a) : bisimulates a b := _). 
  dependent inversion Hsima.
  

_).
  intros.
  (* left *)
  inversion Hsima. subst. 
  

  apply H0 in H. inversion H. inversion H1.
  exists x. split ; auto. 
  inversion Hsimb. subst. apply H4 in H2. inversion H2. inversion H5.
  
  
  


Ltac show_trans_exists :=  
  match goal with 
    | Heval : eval ?s ?t, Htrans : trans ?t _ ?a |- _ => 
      exists a ; split ; try (eapply trans_next ; eauto)
  end.

Definition tnil := inl unit.
Definition tcons := (fun a b => (inr (prod a b))).
(* 
letrec map = 
% f . % l . 
  case l of 
    | nil => nil 
    | cons a b => (cons (@ f a) (@ (@ map f) b))
*)
Definition map := fp (abs (abs (cas 0 tnil (tcons (app 2 (proj1 0)) (app (app 3 2) (proj2 0)))))).
(* 
letrec iterate = 
% f . % k . 
  cons k (@ (@ iterate f) (@ f k))
*)
Definition iterate := fp (abs (abs (tcons 0 (app (app 2 1) (app 1 0))))).
        
(* automates local closure proofs for terms *) 
Lemma map_lc : lc map.
Proof.
  unfold map.
  lc_solve. 
Defined. 

Lemma iterate_lc : lc iterate. 
Proof.
  unfold iterate.
  lc_solve.
Defined.

Lemma left_hand_iterate : forall f x, lc f -> lc x -> lc (app (app map f) (app (app iterate f) x)).
Proof.
  intros. lc_solve ; auto using map_lc, iterate_lc.
Defined.

Lemma iterate_proof : forall f x, lc f -> lc x -> bisimulates (app (app map f) (app (app iterate f) x))  
                                                              (app (app iterate f) (app f x)).
Proof.
  refine (cofix bisim (f x : term) (Hlcf : lc f) (Hlcx : lc x) 
    : bisimulates (app (app map f) (app (app iterate f) x)) (app (app iterate f) (app f x)) := _).
  constructor. 
  (* left *) 
  intros. 
  exists (tcons (app f x) (app (app iterate f) (app f x))).
  split. eapply trans_next with (t2:=(tcons (app f x) (app (app iterate f) (app f x)))).
  beta
  cut 
    (eval 
      (fp
        (abs
          (abs (tcons 0%nat (app (app 2%nat 1%nat) (app 1%nat 0%nat)))))) 
      (open 
        (abs
          (abs (tcons 0%nat (app (app 2%nat 1%nat) (app 1%nat 0%nat)))))
        (fp
          (abs
            (abs (tcons 0%nat (app (app 2%nat 1%nat) (app 1%nat 0%nat)))))))) ; intros.
  intros.
  inversion H0. subst. 
        
  
  
Definition.

(* 
Lemma eval_imp_bisimulates : forall a b, eval a b -> bisimulates b a.
  refine (cofix bisim (a b : term) (Heval : eval a b) : bisimulates b a := _).
  apply bisimulates_base. 
  (* easy to show the left half of simulation *)
  intros ; try show_trans_exists ; try (apply bisimulation_refl ; prove_lc).
  (* right half *) 
  intros. 
Defined.
*) 

(* behavioural equivalence relation *) 
CoInductive b_eq : term -> term -> Prop := 
| b_eq_base : 
  forall a b b', 

(* hard to prove... 
Lemma value_is_eval : forall t, value t <-> exists b, evaluates b t.
Proof. 
  intros t ; split.
  (* -> *)
  intros Hv. exists t. apply evaluates_base. apply multistep_refl.
  unfold not. intros Hr. inversion Hv ; subst ; inversion Hr as [x He] ; subst ; 
    inversion He as [x Hes] ;
      inversion Hes.
  (* <- *) 
  intros He. inversion He. inversion H. subst.
  induction t. inversion H0. subst. 
  inversion He. inversion H2. subst. inversion H3. subst.
  inversion H0. subst.
*) 

Fixpoint raise (t : term) := 
  match t with 
    | unit => unit
    | fp t' => fp (raise t')
    | fvar s => fvar s
    | bvar n => bvar (S n)
    | abs t' => abs (raise t') 
    | app m n => app (raise m) (raise n)
    | prod e1 e2 => prod (raise e1) (raise e2) 
    | proj1 e => proj1 (raise e)
    | proj2 e => proj2 (raise e)
    | inl e => inl (raise e)
    | inr e => inr (raise e) 
    | cas e e1 e2 => cas (raise e) (raise e1) (raise e2) 
  end.

(* case distributivity *) 
Fixpoint case_dist (t : term) : term := 
  match t with 
    | cas (cas e e1 e2) f1 f2 => 
      cas e 
      (cas e1 (raise (case_dist f1)) (raise (case_dist f2))) 
      (cas e2 (raise (case_dist f1)) (raise (case_dist f2)))
    | unit => unit
    | fp t' => fp (case_dist t')
    | fvar s => fvar s
    | bvar n => bvar (S n)
    | abs t' => abs (case_dist t') 
    | app m n => app (case_dist m) (case_dist n)
    | prod e1 e2 => prod (case_dist e1) (case_dist e2) 
    | proj1 e => proj1 (case_dist e)
    | proj2 e => proj2 (case_dist e)
    | inl e => inl (case_dist e)
    | inr e => inr (case_dist e) 
    | cas e e1 e2 => cas (case_dist e) (case_dist e1) (case_dist e2) 
  end.      

(* eval_big : big step operational semantics  

------
e => e

e => e' e' -> e''
-----------------
     e => e''

*)


(* eval_coind : big step coinductive operational semantics *)

CoInductive diverges : term -> Prop := 
| diverges_app_1 : forall e e', diverges e -> diverges (app e e')
| diverges_app_2 : forall e1 e2 e2', eval_big e e' -> diverges 
| diverges_cas : forall e e1 e2, diverges e -> diverges (cas e e1 e2)
| diverges 

Notation "`case` t `of` { A | B }" := (cas t A B).

(* nat := 1 + nat *)
Definition Zero := inl unit. 
Definition Succ := (fun x => inr x).
(* bool := 1 + 1 *) 
Definition T := inl unit.
Definition F := inr unit.

(* Nat = 1 + Nat *) 
Definition One := Succ Zero.
Definition Two := Succ One.
Definition Three := Succ Two. 
Definition add := (fp (abs (abs (abs (cas 2 (abs 2) (abs (Succ (app (app 3 0) 2)))))))).

Ltac lc_abs_run := 
  let L := fresh "L" in 
    intros ; compute ; pick fresh x for L.

Ltac prove_lc := 
  match goal with 
    | |- lc (fp ?x) => apply lc_fp
    | |- lc (abs ?x) => lc_abs_run ; intros ; compute
    | |- lc (cas ?x ?y ?z) => apply lc_cas 
    | |- lc (inr ?x) => apply lc_inr
    | |- lc (inl ?x) => apply lc_inl
    | |- lc ?x => auto
  end.

Lemma add_lc : lc add.
Proof.
  unfold add. 
  repeat prove_lc.
Defined.



Lemma eval_add : eval (app (app add One) Two) Three.
Proof. 
  compute.
