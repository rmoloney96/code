
(* typing derivations carry their terms with them *) 
Inductive type : nat -> Type := 
| type_top : type 0
| type_var : forall n, type (S n)
| type_abs : forall n, type (S n) -> type n
| type_fix : forall n, type (S n) -> type n
| type_arrow : forall n, type n -> type n -> type n
| type_prod : forall n, type n -> type n -> type n
| type_sum : forall n, type n -> type n -> type n
| type_weak : forall n, type n -> type (S n).
 
Implicit Arguments type_abs [n]. 
Implicit Arguments type_fix [n].
Implicit Arguments type_arrow [n].
Implicit Arguments type_prod [n].
Implicit Arguments type_sum [n].
Implicit Arguments type_weak [n].
Coercion type_var : nat >-> type.
Infix "-->" := type_arrow (at level 55, right associativity).
Infix "**" := type_prod (at level 50).
Infix "-|-" := type_sum (at level 55).
Notation "#/\ E" := (type_abs E) (at level 55). 
Notation "#\ E" := (type_fix E) (at level 55).
Notation "^ E" := (type_weak E) (at level 45).

Require Import Arith. 
Infix "===" := eq_nat_dec (at level 50).

Inductive type_eq : forall n n', type n -> type n' -> Prop := 
| type_eq_top : type_eq 0 0 type_top type_top
| type_eq_var : forall n n', 
  n = n' -> 
  type_eq (S n) (S n') (type_var n) (type_var n')
| type_eq_abs : forall n n' T1 T2, 
  type_eq (S n) (S n') T1 T2 -> 
  type_eq n n' (type_abs T1) (type_abs T2)
| type_eq_fix : forall n n' T1 T2, 
  type_eq (S n) (S n') T1 T2 -> 
  type_eq n n' (type_fix T1) (type_fix T2)
| type_eq_arrow : forall n n' T1 T1' T2 T2', 
  type_eq n n' T1 T1' -> 
  type_eq n n' T2 T2' -> 
  type_eq n n' (type_arrow T1 T2) (type_arrow T1' T2')
| type_eq_prod : forall n n' T1 T1' T2 T2', 
  type_eq n n' T1 T1' -> 
  type_eq n n' T2 T2' -> 
  type_eq n n' (type_prod T1 T2) (type_prod T1' T2')
| type_eq_sum : forall n n' T1 T1' T2 T2', 
  type_eq n n' T1 T1' -> 
  type_eq n n' T2 T2' -> 
  type_eq n n' (type_sum T1 T2) (type_sum T1' T2')
| type_eq_weak : forall n n' T1 T2, 
  type_eq n n' T1 T2 ->
  type_eq (S n) (S n') (type_weak T1) (type_weak T2).
Implicit Arguments type_eq [n n']. 
Hint Constructors type_eq.
 
Theorem type_eq_impl_context : forall n n' (A:type n) (B:type n'), type_eq A B -> n = n'.
Proof. 
  intros n n' A B. induction 1 ; subst ; auto.
Defined.

Require Import JMeq.

Ltac jmeq_solve := 
  match goal with 
    | H : JMeq ?T1 ?T2 |- _ => apply JMeq_eq in H ; subst ; auto ; try jmeq_solve
    | H : ?x = ?x |- _ => idtac
    | H1 : type (S ?n), H2 : type (S ?n0) |- _ => assert (n = n0) ; [ eapply type_eq_impl_context ; eauto | subst ] ; jmeq_solve
    | H1 : type ?n, H2 : type ?n0 |- _ => assert (n = n0) ; [ eapply type_eq_impl_context ; eauto | subst ] ; jmeq_solve
  end.

Lemma type_eq_jmeq : forall n n' (T1 : type n) (T2 : type n'), type_eq T1 T2 -> JMeq T1 T2.
Proof.
  induction 1 ; subst ; auto with arith ; try jmeq_solve. 
Defined.
Implicit Arguments type_eq_jmeq [n n']. 

Lemma type_eq_eq : forall n (T1 T2: type n), type_eq T1 T2 -> T1 = T2.
Proof.
  intros. apply type_eq_jmeq in H. apply JMeq_eq in H. auto.
Defined.
Implicit Arguments type_eq_eq [n]. 
Hint Resolve type_eq_eq. 

Lemma type_eq_refl : forall n (T : type n), type_eq T T.
Proof.
  induction T ; auto.
Defined.  

Ltac type_eq_sync_ns := 
  match goal with 
    | H : type_eq ?P ?Q |- _ => assert (type_eq P Q) ; auto ; apply type_eq_impl_context in H ; subst
  end.

Ltac type_eq_conv := 
  match goal with 
    | H : type_eq ?P ?Q |- _ => apply type_eq_eq in H ; rewrite H in *
  end.

Ltac type_eq_dep := 
  match goal with 
    | H : existT ?P ?n ?T3 = existT ?P ?n ?T1 |- type_eq ?T1 ?T2 => 
      change (match existT P n T1 with 
                | existT pf t => type_eq t T2
              end) ; rewrite <- H
    | H : existT ?P ?n ?T3 = existT ?P ?n ?T2 |- type_eq ?T1 ?T2 => 
      change (match existT P n T2 with 
                | existT pf t => type_eq T1 t
              end) ; rewrite <- H
  end.

Ltac type_eq_dec_case :=     
  intros ; right ; unfold not in *; intro Heq ; 
    (match goal with 
       | H : _ -> False |- False => apply H
     end) ; type_eq_sync_ns ; 
    (match goal with 
       | H : type_eq ?P ?Q |- _ => inversion H ; subst ; clear H
     end) ; type_eq_conv ; repeat progress type_eq_dep ; try (apply type_eq_refl) ; auto.
 
Ltac type_eq_dec_solver := 
  try (intros ; left ; auto ; fail) ; 
    try (intros ; right ; unfold not ; intros Heq ; inversion Heq ; fail). 

Lemma type_eq_dec : forall n n' (T1 : type n) (T2 : type n'), {type_eq T1 T2} + {~ type_eq T1 T2}.
Proof.
  refine (fix type_eq_dec n n' (T1 : type n) (T2 : type n') {struct T1} := _).
  destruct T1 ; destruct T2 ; type_eq_dec_solver.
  (* var *)
  case (n === n0). intros Heq. rewrite Heq. left ; auto. 
  intros. right. unfold not. intros. inversion H. subst. apply type_eq_eq in H. congruence. 
  (* abs *) 
  case (type_eq_dec (S n) (S n0) T1 T2) ; type_eq_dec_solver ; type_eq_dec_case.
  (* fix *) 
  case (type_eq_dec (S n) (S n0) T1 T2) ; type_eq_dec_solver ; type_eq_dec_case.
  (* arrow *) 
  case (type_eq_dec n n0 T1_1 T2_1) ; case (type_eq_dec n n0 T1_2 T2_2) ; type_eq_dec_solver ; type_eq_dec_case.
  (* prod *) 
  case (type_eq_dec n n0 T1_1 T2_1) ; case (type_eq_dec n n0 T1_2 T2_2) ; type_eq_dec_solver ; type_eq_dec_case.
  (* sum *) 
  case (type_eq_dec n n0 T1_1 T2_1) ; case (type_eq_dec n n0 T1_2 T2_2) ; type_eq_dec_solver ; type_eq_dec_case.
  (* weak *) 
  case (type_eq_dec n n0 T1 T2) ; type_eq_dec_solver. intros.
  right. unfold not in *. intros. apply n1. inversion H. subst. repeat progress type_eq_dep. auto.
Defined.
Implicit Arguments type_eq_dec [n n']. 

Lemma eq_type_dec : forall n (T1 T2 : type n), {T1 = T2} + {~ T1 = T2}.
Proof.
  intros ; case (type_eq_dec T1 T2) ; intros ; type_eq_dec_solver. 
  intros. unfold not in *. right. intros Heq. apply n0. rewrite Heq. apply type_eq_refl.
Defined. 

Lemma le_n_O_eq_transparent : forall n, n <= 0 -> 0 = n.
Proof.
  induction n; auto with arith.
Defined.

Definition weaken_type : forall n n', n' <= n -> type n' -> type n.
Proof.
  induction n. intros.
  apply le_n_O_eq_transparent in H. subst. auto.
  intros. case_eq (le_le_S_dec n' n). intros.
  apply type_weak ; apply (IHn n') ; auto.
  intros. cut (n' = (S n)). intros. subst. auto.
  apply le_antisym ; auto.
Defined.

Theorem le_S_n_transparent : forall n m, S n <= S m -> n <= m.
Proof.
  induction m; auto with arith.
Defined.

Lemma le_Sn_n_absurd : forall k, ~ S k <= k.
Proof.
  induction k. unfold not.  intros. inversion H.
  unfold not. intros. apply le_S_n_transparent in H. auto.
Defined. 

Definition open_type_rec : forall (k n l:nat), n <= k -> l = (S k) -> type n -> type l -> type k.
Proof.
  refine 
    (fix open_type_rec (k n l:nat) (H: n <= k) (Hs: l = (S k)) (u:type n) (t : type l) {struct t}: type k := 
      (match t in type m return (m = l -> type k) with
         | type_top => 
           (fun _ => weaken_type k 0 _ type_top)
         | type_var n' => 
           (fun (H0:(S n')=l) => _)
         | type_abs n' T => 
           (fun (H0:n'=l) => type_abs _)
         | type_fix n' T => 
           (fun (H0:n'=l) => type_fix _)
         | type_arrow n' T1 T2 => 
           (fun (H0:n'=l) => type_arrow (open_type_rec k n _ _ _ u T1) (open_type_rec k n _ _ _ u T2))
         | type_prod n' T1 T2 => 
           (fun (H0:n'=l) => type_prod (open_type_rec k n _ _ _ u T1) (open_type_rec k n _ _ _ u T2))
         | type_sum n' T1 T2 => 
           (fun (H0:n'=l) => type_sum (open_type_rec k n _ _ _ u T1) (open_type_rec k n _ _ _ u T2))
         | type_weak n' T => 
           (fun (H0:(S n')=l) => 
             match le_lt_eq_dec n' k _ with 
               | left Hl => (open_type_rec k n _ _ _ u T) 
               | right Hr => _
             end)
       end) (refl_equal l)).
  (* top, we never reach here since the type isn't even correct to descend... *)
  subst. inversion _H.
  (* var *) 
  apply (weaken_type k n H). exact u.
  (* abs *) 
  cut (n <= n'). intros H1. 
  rewrite <- H0 in *. rewrite <- Hs. apply (open_type_rec n' n (S n')). auto. auto. auto. auto. subst. 
  apply le_S. auto.
  (* fix *)
  cut (n <= n'). intros H1. 
  rewrite <- H0 in *. rewrite <- Hs. apply (open_type_rec n' n (S n')). auto. auto. auto. auto. subst. 
  apply le_S. auto.
  (* arrow *)
  auto. subst. auto. auto. subst. auto.
  (* prod *) 
  auto. subst. auto. auto. subst. auto.
  (* sum *) 
  auto. subst. auto. auto. subst. auto.
  (* weak *) 
  subst. inversion H0. auto. unfold lt in Hl. subst. auto. unfold lt in Hl. rewrite H0 in Hl. rewrite Hs in Hl. 
  apply le_Sn_n_absurd in Hl. inversion Hl. subst. auto.
Defined.
Extraction open_type_rec.
Print open_type_rec.

Definition open_type : forall (n:nat), type (S n) -> type n -> type n.
Proof.
  intros. apply (open_type_rec n n (S n)) ; auto.
Defined.
Implicit Arguments open_type [n]. 

Definition id := (#/\ 0).
 
(* sanity checks *) 
Eval compute in open_type (#/\ (#/\ (^(^0 --> 1) --> 2))) id.

Eval compute in open_type (#/\((^0 --> 1) --> ^(^id))) id.

Eval compute in open_type ((0 --> ^(id)) --> ^(id)) id.

Require Import List.
 
Definition typ := type 0.
Definition context := list typ.
 
Inductive term : context -> typ -> Type :=
| unit : term nil type_top
| var : forall G T, term G T 
| abs : forall GR G T1, GR=T1::G -> term G T1
| app : forall G T1 T2, term G (T1-->T2) -> term G T1 -> term G T2
(* type application *)
| apt : forall G T1 T2, term G (#/\ T1) -> term G T2 -> term G (open_type T1 T2)
(* algebraic *) 
| prod : forall G T1 T2, term G T1 -> term G T2 -> term G (T1**T2)
(* Not sure if we want this instead of fst/snd
| splt : forall G T1 T2 T3, term n G (T1**T2) -> term n G (T1 --> (T2 --> T3)) -> term n G T3
*) 
| fst : forall G T1 T2, term G (T1**T2) -> term G T1
| snd : forall G T1 T2, term G (T1**T2) -> term G T2
| inl : forall G T1 T2, term G T1 -> term G (T1 -|- T2)
| inr : forall G T1 T2, term G T2 -> term G (T1 -|- T2)
| cas : forall G T1 T2 T3, term G (T1-|-T2) -> term G (T1 --> T3) -> term G (T2 --> T3) -> term G T3
(* rec types *) 
| unr : forall G T, term G (#\ T) -> term G (open_type T (#\ T))
| rol : forall G T, term G (open_type T (#\ T)) -> term G (#\ T)
(* structural *) 
| weak : forall G T T1, term G T -> term (T1::G) T.
Notation "G |- x ;; T" := (term G x T) (at level 55). 

Definition Suffix (A:Type) (m l : list A) := {l' | l = l'++m}.
Implicit Arguments Suffix [A].

Definition context_eq_dec (n:nat) G G' := list_eq_dec (eq_type_dec n) G G'. 
Implicit Arguments context_eq_dec [n]. 

Definition weaken_context : forall G G' T, Suffix G' G -> term G' T -> term G T.
Proof.
  refine 
    (fix weaken_context (G G' : context) (T:typ) (H:Suffix G' G) (t : term G' T) : term G T := 
      match context_eq_dec G' G with 
        | left Hl => _
        | right Hr => 
          (match G as x return (G = x -> term G T) with 
             | nil => (fun (Heq : G = nil) => _)
             | cons ht Gtail => 
               (fun (Heq : G = cons ht Gtail) =>
                 let H := weaken_context Gtail G' T _ t in 
                   _)
           end) (refl_equal G)
      end). subst. auto.
  intros. subst. inversion H. apply sym_eq in H0. apply app_eq_nil in H0. inversion H0. subst. auto.
  inversion H. rewrite H0 in Heq. 
  destruct x. simpl in H0. congruence. unfold Suffix. 
  inversion Heq. exists x. auto. auto.
  apply (weak Gtail T ht) in H0. subst. auto.
Defined.
  
Definition open_term_rec : forall (k:nat) G G' G'' T T', length G <= k -> Suffix G' G -> G' = (T'::G'') -> term G T' -> term G' T -> term G'' T.
Proof.
  refine 
    (fix open_term_rec (k:nat) (G G' G'' : context) (T T':typ) 
      (Hl: length G <= k) (Hs: Suffix G' G) (H0: G' = (T'::G'')) (u: term G T') (t:term G' T) {struct t} 
      : term G'' T := 
      (match t in term G'0 T0 return (G'0 = G' -> term G'' T) with
         | unit => _
         | var G T => _
         | abs GR G H T => _
         | app G T1 T2 t1 t2 => _
         | apt G T1 T2 t1 t2 => _
         | prod G T1 T2 t1 t2 => _
         | fst G T1 T2 t => _
         | snd G T1 T2 t => _
         | inl G T1 T2 t => _
         | inr G T1 T2 t => _
         | cas G T1 T2 T3 s f g => _
         | unr G T t => _
         | rol G T t => _
         | weak G T T1 t => _
       end) (refl_equal G')).
  (* unit *)
  intros. subst. inversion H. 
  (* var *) 
  intros. subst. eapply (weaken_context G'' G'). unfold Suffix. exists 


Definition open_term_rec : forall (k n l:nat), n <= k -> l = (S k) -> type n -> type l -> type k.

Definition open_type_rec : forall (k n l:nat), n <= k -> l = (S k) -> type n -> type l -> type k.



