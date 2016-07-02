
Require Import List. 

Notation "[]" := nil.
Notation "[ a ]" := (cons a nil).
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..). 
Infix "::" := cons.

Definition type_context := list nat.

Fixpoint type_lower (tc :type_context) : type_context := 
  match tc with 
    | [] => []
    | n::t => match n with 
                | 0 => type_lower t 
                | S n' => n'::(type_lower t)
              end
  end.

(* typing derivations carry their terms with them *) 
Inductive type : type_context -> Type := 
| type_top : type []
| type_var : forall n, type [n]
| type_arrow : forall L M, type L -> type M -> type (L++M)
| type_all : forall L, type L -> type (type_lower L)
| type_fp : forall L, type L -> type (type_lower L).
Implicit Arguments type_arrow [L M]. 
Implicit Arguments type_all [L].
Implicit Arguments type_fp [L].
Coercion type_var : nat >-> type.

Inductive post_type : Type := 
| post_type_top : post_type 
| post_type_var : nat -> post_type
| post_type_arrow : post_type -> post_type -> post_type
| post_type_all : post_type -> post_type
| post_type_fp : post_type -> post_type.

Inductive type_eq : forall C C', type C -> type C' -> Prop := 
| type_eq_top : type_eq [] [] type_top type_top
| type_eq_var : forall n n', n = n' -> type_eq [n] [n'] (type_var n) (type_var n')
| type_eq_arrow : forall L M A B L' M' A' B', 
  type_eq L L' A A' -> 
  type_eq M M' B B' -> 
  type_eq (L++M) (L'++M') (type_arrow A B) (type_arrow A' B')
| type_eq_all : forall L L' A A', 
  type_eq L L' A A' -> 
  type_eq (type_lower L) (type_lower L') (type_all A) (type_all A')
| type_eq_fp : forall L L' A A', 
  type_eq L L' A A' -> 
  type_eq (type_lower L) (type_lower L') (type_fp A) (type_fp A').
Implicit Arguments type_eq [C C']. 
Hint Constructors type_eq.

Definition type_simpl : forall C, type C -> post_type.
Proof.
  induction 1. 
  apply post_type_top.
  apply (post_type_var n).
  apply (post_type_arrow IHtype1 IHtype2).
  apply (post_type_all IHtype).
  apply (post_type_fp IHtype).
Defined.
Implicit Arguments type_simpl [C].
 
Theorem type_eq_impl_simpl_eq : forall C C' (A:type C) (B:type C'), type_eq A B -> (type_simpl A) = (type_simpl B).
Proof.
  intros C C' A B. induction 1.
  (* top *)
  reflexivity.
  (* var *)
  subst. reflexivity.   
  (* arrow *) 
  simpl. rewrite IHtype_eq1. rewrite IHtype_eq2. reflexivity.
  (* all *) 
  simpl. rewrite IHtype_eq. reflexivity.
  (* fp *) 
  simpl. rewrite IHtype_eq. reflexivity.
Defined.
 
Theorem type_eq_impl_context : forall C C' (A:type C) (B:type C'), type_eq A B -> C = C'.
Proof. 
  intros C C' A B. induction 1 ; subst ; auto.
Defined.

Require Import JMeq.
Lemma type_eq_impl_jmeq : forall L M (A :type L) (B:type M),
  type_eq A B -> JMeq A B. 
Proof. 
  intros L M A B ; induction 1. reflexivity. subst ; auto. 
  (* arrow *) 
  cut (type_eq A A'). intros HeqA. apply type_eq_impl_context in HeqA. subst.
  apply JMeq_eq in IHtype_eq1. rewrite IHtype_eq1.
  cut (type_eq B B'). intros HeqB. apply type_eq_impl_context in HeqB. subst.
  apply JMeq_eq in IHtype_eq2. rewrite IHtype_eq2. reflexivity. auto. auto.
  (* all *) 
  cut (type_eq A A'). intros HeqA. apply type_eq_impl_context in HeqA. subst.
  apply JMeq_eq in IHtype_eq. rewrite IHtype_eq. auto. auto.
  (* fp *)
  cut (type_eq A A'). intros HeqA. apply type_eq_impl_context in HeqA. subst.
  apply JMeq_eq in IHtype_eq. rewrite IHtype_eq. auto. auto.
Defined.

Lemma type_eq_refl : forall L (A:type L), type_eq A A.
Proof.
  induction A ; auto.
Defined.

Lemma type_eq_symm : forall L M (A:type L) (B:type M), type_eq A B -> type_eq B A.
Proof.
  induction 1 ; auto.
Defined.

Lemma type_eq_trans : forall L M N (A:type L) (B:type M) (C:type N), type_eq A B -> type_eq B C -> type_eq A C.
Proof. 
  induction 2 ; auto. 
  subst ; auto.
  (* arrow *)
  inversion H. simpl. subst.
  dependent rewrite H3. simpl. 
  assert (L0 = L'). eapply type_eq_impl_context with (A:=A0) (B:=A'). auto. 
  assert (M = M'). eapply type_eq_impl_context with (A:=B) (B:=B'). auto. auto.
  apply type_eq_impl_jmeq in H0_. apply type_eq_impl_jmeq in H0_0. subst. 
  apply JMeq_eq in H0_. subst. apply JMeq_eq in H0_0. subst. auto.
  (* all *) 
  assert (L0 = L'). eapply type_eq_impl_context. eauto. subst.
  apply type_eq_impl_jmeq in H0. apply JMeq_eq in H0. subst ; auto.
  (* fp *) 
  assert (L0 = L'). eapply type_eq_impl_context. eauto. subst.
  apply type_eq_impl_jmeq in H0. apply JMeq_eq in H0. subst ; auto.
Defined.

Require Import Arith. 
Infix "===" := eq_nat_dec (at level 50).
Definition type_eq_dec : forall C C' (A:type C) (B:type C'), {type_eq A B} + {~ type_eq A B}.
Proof.
  refine (fix type_eq_dec (C C' : type_context) (A : type C) (B : type C') {struct A} := _).
  destruct A ; destruct B ; try (right ; unfold not ; intros H ; inversion H ; fail).
  (* top *) 
  left ; auto.
  (* var *) 
  case (n === n0). intros. subst. left. auto.
  intros. right. unfold not ; intros. inversion H. congruence. 
  (* arrow *)
  case (type_eq_dec L L0 A1 B1) ; case (type_eq_dec M M0 A2 B2). 
  intros. left. auto.
  intros. right. unfold not. intros.
  unfold not in n. apply n. 
  inversion H. dependent rewrite <- H7. dependent rewrite <- H12.
  simpl. auto.
  intros. right. unfold not. intros.
  unfold not in n. apply n. 
  inversion H. dependent rewrite <- H6. dependent rewrite <- H11.
  simpl. auto.
  intros. right. unfold not. intros. 
  unfold not in n. apply n.
  inversion H. dependent rewrite <- H7. dependent rewrite <- H12.
  simpl. auto.
  (* all *) 
  case (type_eq_dec L L0 A B). intros. left. auto.
  intros. right. unfold not. intros. unfold not in n. apply n.
  inversion H. subst. dependent rewrite <- H5. dependent rewrite <- H8. simpl. auto.
  (* fp *) 
  case (type_eq_dec L L0 A B). intros. left. auto.
  intros. right. unfold not. intros. unfold not in n. apply n.
  inversion H. subst. dependent rewrite <- H5. dependent rewrite <- H8. simpl. auto.
Defined.

Definition eq_type_dec : forall C (A:type C) (B:type C), {A = B} + {~ A = B}.
Proof.
  intros. 
  case (type_eq_dec C C A B). intros. 
  apply type_eq_impl_jmeq in t. 
  left. apply JMeq_eq. auto.
  intros.
  right. unfold not. intros. apply n. rewrite H. auto.
  apply type_eq_refl.
Defined.

Definition remove_nat (n:nat) (l:list nat) := remove eq_nat_dec n l.
Hint Unfold remove_nat.
Notation "L // k" := (remove_nat k L) (at level 62).

Lemma cons_distr : forall a L k, (a :: L // k) = ([a] // k) ++ L // k.
Proof.
  intros. unfold remove_nat. simpl. 
  case_eq (k===a). intros. rewrite e. simpl. reflexivity.
  intros. simpl. rewrite H. auto.
Defined.

Lemma append_distr : forall L M k, (L // k) ++ (M // k) = (L ++ M // k).
Proof. 
  induction L. simpl. auto.
  intros. 
  rewrite <- app_comm_cons.
  rewrite cons_distr. simpl.
  case_eq (k===a). intros. simpl. apply IHL.
  intros. simpl. rewrite H. simpl. f_equal. apply IHL.
Defined.

Lemma type_lower_open : forall L k, type_lower (L // (S k)) = type_lower L // k.
Proof. 
  intros. induction L. simpl. auto. 
  simpl. destruct a. simpl. auto.
  simpl. case_eq (k===a). 
  intros. simpl. auto.
  intros. simpl. f_equal. auto.
Defined.

Definition type_open_rec (TC:type_context) (k : nat) (u : type []) (T : type TC) : type (TC//k).
Proof. 
  refine 
    (fix type_open_rec (TC:type_context) (k : nat) (u : type []) (T : type TC) {struct T} : type (TC//k) :=
      match T in type M return type (M//k) with
        | type_top => type_top
        | type_var i => 
          match k === i with 
            | left Hl => _ 
            | right Hr => _
          end
        | type_arrow L M T1 T2 => _
        | type_all L T' => _
        | type_fp L T' => _
      end).
  (* var *) 
  subst ; unfold remove_nat ; unfold remove ; 
    case_eq (i===i) ; intros ; auto ; intros ; absurd (i=i) ; auto. 
  unfold remove_nat ; unfold remove ; 
    case_eq (i===k) ; intros ; auto. rewrite e. destruct (k===k). auto.
  rewrite e in Hr. cut (k=k). intros. apply Hr in H0. inversion H0. auto.
    case_eq (k===i) ; intros. auto. 
    apply type_var.
  (* arrow *)
    rewrite <- append_distr.
    eapply type_arrow ; apply type_open_rec ; auto. 
  (* all *)
    rewrite <- type_lower_open.
    eapply type_all. apply type_open_rec. auto. auto.
  (* fp *)
    rewrite <- type_lower_open.
    eapply type_all. apply type_open_rec. auto. auto.
Defined.
Implicit Arguments type_open_rec [TC].

Print type_open_rec.
Print eq_rec.

(* 
Definition lower_roll TC : type (type_lower TC // 0) ->  type (type_lower TC).
Proof.
  intros. rewrite <- lower_zero. auto.
*) 

Definition type_open : type [0] -> type [] -> type [].
Proof.
  intros A u. apply (type_open_rec 0 u A).
Defined.

Inductive typ : Type := 
| typ_base : forall L, type L -> typ.

Definition context := list (nat * typ)%type.

Fixpoint lower (c : context) : context := 
  match c with 
    | [] => [] 
    | (n,T)::t => match n with 
                    | 0 => lower t
                    | S n' => (n',T)::(lower t)
                  end
  end.

Inductive term : forall TC, context -> type TC -> Type := 
| unit : term [] [] type_top 
| var : forall TC (A :type TC) n, term TC [(n,(typ_base TC A))] A
| abs : forall TC1 TC2 A B L, 
  term TC2 L B -> 
  term (TC1++TC2) (lower L) (type_arrow A B)
| fp : forall TC L A, term TC L A -> term TC L A
| app : forall TC1 TC2 L1 L2 A B, 
  term (TC1++TC2) L1 (type_arrow A B) -> 
  term TC1 L2 A -> 
  term TC2 (L1++L2) B
(* type folding/unfolding isomorphism *)
| unroll : forall A L, 
  term (type_lower [0]) L (type_fp A) -> 
  term [] L (type_open A (type_fp A))
| roll : forall A L, 
  term [] L (type_open A (type_fp A)) -> 
  term (type_lower [0]) L (type_fp A)
(* type abstraction and application *)
| abst : forall TC L A, 
  term (type_lower TC) L (type_all A)
| appt : forall L A, 
  term (type_lower [0]) L (type_all A) -> 
  forall (B : type []), 
    term [] L (type_open A B).
Implicit Arguments var [TC].
Implicit Arguments abs [TC1 TC2 L B].
Implicit Arguments fp [TC L A].
Implicit Arguments app [TC1 TC2 L1 L2 A B]. 
Implicit Arguments unroll [A L]. 
Implicit Arguments roll [A L].
Implicit Arguments abst [TC L A].
Implicit Arguments appt [L A].

Notation "'T" := type_top (at level 60).
Infix "-->" := type_arrow (at level 61). 
Notation "'All E" := (type_all E) (at level 62). 
Notation "'Rec E" := (type_fp E) (at level 62). 


Fixpoint type_in (TC : type_context) (A : type TC) (C:context) (k : nat) : Prop := 
  match C with 
    | nil => False
    | ((n,typ_base TC' A')::C') => ((k=n) /\ (type_eq A' A)) \/ (type_in TC A C' k) 
  end. 

Definition type_in_dec (TC:type_context) (A:type TC) (C:context) (k:nat) : {type_in TC A C k} + {~ type_in TC A C k}.
Proof.
  intros TC A ; induction C. 
  right. simpl. auto.
  intros. destruct a. destruct t. simpl. 
  case_eq (k === n) ; case_eq (type_eq_dec L TC t A) ; case_eq (IHC k) ; intros ;  
    try (left; left ; split ; auto ; fail) ; 
      try (left ; right ; auto ; fail). 
  right ; unfold not ; intros Hnew. inversion Hnew. inversion H1. inversion H2. auto. auto.
  right ; unfold not ; intros Hnew. inversion Hnew. inversion H2. congruence. congruence.
  right ; unfold not ; intros Hnew. inversion Hnew. inversion H1. inversion H2. auto. auto.
Defined.

Definition weaken (k:nat) (C:context) : { C' :context | forall (TC:type_context) (A:type TC), ~ type_in TC A C' k}.
Proof.
  refine 
    (fix weaken (k :nat) (C : context) {struct C} : { C' :context | forall (TC:type_context) (A:type TC), ~ type_in TC A C' k} := 
      match C return { C' :context | forall (TC:type_context) (A:type TC), ~ type_in TC A C' k} with
        | nil => exist _ nil _ 
        | ((n,T)::t)=> match k === n with 
                         | left Hl => match weaken k t with 
                                        | exist l P => exist _ l _
                                      end
                         | right Hr => match weaken k t with 
                                         | exist l P => exist _ ((n,T)::l) _
                                       end
                       end
      end). 
  intros. simpl. auto.
  intros. apply P. 
  intros. simpl. case T. intros. unfold not. intros.
  inversion H. inversion H0. congruence. eapply P. eauto.
Defined.   

Fixpoint weaken_weak (k :nat) (C : context) {struct C} : context := 
  match C with 
    | nil => nil 
    | ((n,T)::t)=> match k === n with 
                     | left H => weaken_weak k t
                     | right H => (n,T)::(weaken_weak k t)
                   end
  end.
Notation "L /// k" := (weaken_weak k L) (at level 62).

Lemma lower_open : forall L k, lower (L /// (S k)) = lower L /// k.
Proof.
  induction L. simpl. intros. auto.
  intros. simpl. 
  destruct a. destruct t.
  destruct n. simpl. auto.
  intros.
  intros. 
  case_eq (k === n). intros. simpl. rewrite H. auto.
  intros. simpl. rewrite H. f_equal. auto. 
Defined.

Lemma type_not_in_weaken : forall TC A C k, ~ type_in TC A (C///k) k.
Proof.
  intros TC A. induction C. intros. simpl. auto.
  intros. unfold not. intros. 
  destruct a. simpl in H. case_eq (k===n). intros. rewrite H0 in H. 
  unfold not in IHC. eapply IHC. eauto.
  intros.
  rewrite H0 in H. simpl in H. destruct t. 
  inversion H. inversion H1. congruence. 
  unfold not in IHC. eapply IHC. eauto.
Defined.

Lemma type_in_one_impl_eq : forall TC A B k n, type_in TC B ((n, typ_base TC A) :: []) k -> k = n -> A = B.
Proof.
  intros. apply JMeq_eq. apply type_eq_impl_jmeq. simpl in H. inversion H. inversion H1. auto. inversion H1.
Defined.   
  
Lemma type_in_one_not_impl_eq : forall TC A B k n, type_in TC B ((n, typ_base TC A) :: []) k -> k <> n -> A <> B.
Proof.
  intros. simpl in H. inversion H. inversion H1. unfold not. intros. congruence.
  inversion H1.
Defined. 

Definition open_rec (A B:type []) (L:context) (k : nat) (H : type_in [] B L k) (u : term [] [] B) (T : term [] L A) : term [] (L///k) A.
Proof.
  refine (fix open_rec (A B:type []) (L:context) (k : nat) (H : type_in [] B L k) (u : term [] [] B) (T : term [] L A) : term [] (L///k) A := _). 
  destruct T. 
  (* top*) 
  simpl. apply unit.
  (* var *) 
  case_eq (k === n). intros. 
  apply type_in_one_impl_eq in H. simpl. rewrite H0. rewrite H. auto. auto. intros.
  apply type_in_one_not_impl_eq in H. simpl. rewrite H0. 
  apply var. auto. 
  (* abs *) 
  rewrite <- lower_open. 
  apply abs.  


  intros A B L. k H u T. generalize dependent k.
  
  ; induction T. 
  (* top *) 
  intros ; simpl. try (intros H) ; inversion H.
  (* var *) 
  intros.
  case_eq (type_in_dec TC B ((n,typ_base TC A) :: []) k) ; case_eq (k===n) ; case_eq (type_eq_dec TC TC A B) ; 
  intros ; try (simpl in * ; rewrite H0 in H2 ; rewrite H1 in H2 ; try rewrite H1).
  cut (A = B). intros. rewrite H3. auto. apply JMeq_eq. apply type_eq_impl_jmeq ; auto.
  absurd (type_eq A B). auto. inversion H. inversion H3. auto. inversion H3.
  absurd (k = n). auto. inversion t0. inversion H3. auto. inversion H3.  
  absurd (k = n). auto. inversion t. inversion H3. auto. inversion H3.  
  absurd (k = n /\ type_eq A B \/ False). auto. 
  left. split. auto. auto.
  congruence. apply var.
  (* abs *) 
  congruence.
  intros. rewrite <- lower_open. apply abs. eapply IHT.  
  (* next*) 
  Focus 2. intros. eapply IHT. eauto. eauto.
  (* next *)
  Focus 2. intros. 
  
  
  simpl in *. 
  intros.
  intros. case_eq (k=== n)

  simpl. case_eq (k === n). intros. 
  case_eq (type_in_dec TC B ((n, typ_base TC A) :: []) k).
  intros. simpl in t.
  simpl in H1. rewrite H0 in H1. simpl in H1. 
  case_eq (type_eq_dec TC TC A B). intros. rewrite H2 in H1. 
  cut (A = B). intros. rewrite H3. exact u. 
  apply JMeq_eq. apply type_eq_impl_jmeq. auto. 
  intros. rewrite H2 in H1. simpl in *. inversion H1.
  intros. congruence.
  intros. 
  case_eq (type_in_dec TC B ((n, typ_base TC A) :: []) k).
  intros. simpl in H1. auto. 
  simpl in H1.
inversion t.
  inversion H. 

Defined.

Defined. 
(* replace a bvar with a term *)
Fixpoint open_rec (k : nat) (u : term []) (e : term [k]) {struct e} : term :=
  match e with
    | var i => if k === i then u else (var i)
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
