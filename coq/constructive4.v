
CoInductive Sierp : Set := 
| T : Sierp
| DS : Sierp -> Sierp.

Definition decomp (x : Sierp) : Sierp := 
  match x with 
    | T => T
    | DS x' => DS x'
  end.

Lemma decomp_eql : forall x, x = decomp x.
  intro x. case x. simpl. auto.
  intros. simpl. auto.
Defined.    

CoInductive CoLe : Sierp -> Sierp -> Prop := 
| cole_base : forall x, CoLe x T 
| cole_next : forall x y, CoLe x y -> 
  CoLe (DS x) (DS y).

Infix "~<=" := CoLe (at level 90). 

Lemma cole_refl : forall x, x ~<= x.
  cofix.
  intro x. rewrite (decomp_eql x). 
  destruct x. simpl. apply cole_base.
  simpl. apply cole_next.
  apply cole_refl.
Defined.  

Ltac decomp_eql_tac :=
  match goal with 
    | [ |- ?x ~<= ?y ] => rewrite (decomp_eql x) ; simpl ;
      rewrite (decomp_eql y) ; 
        simpl ; try (apply cole_refl) ; 
            try (apply cole_next)
  end.
  
(* We take equality to be the relation induced by symetrising. *)
Definition CoEq x y := CoLe x y /\ CoLe y x.

Infix "~=" := CoEq (at level 90). 

Lemma coeq_refl : forall x, x ~= x.
Proof. 
  intros.
  unfold CoEq. split ; decomp_eql_tac.
Defined. 
  
(* Trivial, by definition *)
Lemma cole_antisym : forall x y, CoLe x y /\ CoLe y x -> CoEq x y.
Proof. auto. 
Defined.

Lemma cole_trans : forall x y z, x ~<= y -> y ~<= z -> x ~<= z.
  cofix.
  intros x y z Hxy Hyz.
  destruct x ; destruct y ; destruct z ; inversion Hxy ; inversion Hyz ; subst.
  exact Hxy. 
  exact Hxy. 
  apply cole_base.
  decomp_eql_tac. apply (cole_trans x y z H1 H4).
Defined. 

CoFixpoint bot : Sierp := DS bot.

Lemma bot_least : forall x, bot ~<= x.
Proof.
  cofix.
  intros. destruct x ; decomp_eql_tac ; auto.
  apply cole_base.
Defined.

Lemma top_greatest : forall x, x ~<= T.
Proof.
  apply cole_base.
Defined.

Lemma non_degenerate : ~ (bot ~= T).
Proof.
  unfold not. intros.
  inversion H.
  inversion H1. rewrite (decomp_eql bot) in H4 ; simpl in *. inversion H4.
Defined. 

CoFixpoint join (x : Sierp) (y : Sierp) : Sierp := 
  match x with 
    | T => T
    | DS x' => match y with 
                 | T => T
                 | DS y' => DS (join x' y')
               end
  end.

Lemma join_correct : (forall x y, x ~<= join x y) /\ (forall x y, y ~<= join x y).
Proof.
  split.
  (* left *)
  cofix.
  intros. destruct x ; destruct y ; decomp_eql_tac.
  apply top_greatest.
  apply join_correct.
  (* right *) 
  cofix.
  intros. destruct x ; destruct y ; decomp_eql_tac.
  apply top_greatest.
  apply join_correct.
Defined.

Lemma join_least : forall a x y, (x ~<= a) /\ (y ~<= a) -> (join x y ~<= a).
Proof.
  cofix.
  intros. 
  inversion H.
  destruct x ; destruct y ; destruct a ; decomp_eql_tac.
  inversion H0. inversion H0. inversion H1. (* impossible *)
  apply top_greatest.
  inversion H0. inversion H1. subst.
  apply join_least. split. exact H4. exact H7.
Defined.

CoFixpoint meet (x : Sierp) (y : Sierp) : Sierp := 
  match x,y with 
    | T,T => T
    | DS x', T => DS x'
    | T, DS y' => DS y' 
    | DS x',DS y' => DS (meet x' y')
  end.

Lemma meet_correct : (forall x y, meet x y ~<= x) /\ (forall x y, meet x y ~<= y).
Proof.
  split.
  (* left *)
  cofix.
  intros. destruct x ; destruct y ; decomp_eql_tac.
  apply top_greatest.
  apply meet_correct.
  (* right *)
  cofix.
  intros. destruct x ; destruct y ; decomp_eql_tac.
  apply top_greatest.
  apply meet_correct.
Defined.

Ltac decomp_le_solve := 
  match goal with 
    | [ H : T ~<= DS ?x |- ?y ] => inversion H
    | [ |- ?x ~<= T ] => apply top_greatest
  end.

Lemma meet_greatest : forall a x y, (a ~<= x) /\ (a ~<= y) -> (a ~<= meet x y).
Proof.
  cofix. 
  intros. 
  inversion H.
  destruct x ; destruct y ; destruct a ; decomp_eql_tac ; try decomp_le_solve.
  inversion H1. subst. exact H4.
  inversion H0. subst. exact H4.
  inversion H0. inversion H1. subst. apply meet_greatest. split. exact H4. exact H7. 
Defined.

CoInductive Rierp : Set := 
| F : Rierp
| DR : Rierp -> Rierp.

Definition decompr (x : Rierp) : Rierp := 
  match x with 
    | F => F
    | DR x' => DR x'
  end.

Lemma decompr_eql : forall x, x = decompr x.
  intro x. case x. simpl. auto.
  intros. simpl. auto.
Defined.    

CoInductive CoLeR : Rierp -> Rierp -> Prop := 
| coler_base : forall x, CoLeR F x 
| coler_right : forall x, CoLeR F x -> 
  CoLeR F (DR x)
| coler_next : forall x y, CoLeR x y -> 
  CoLeR (DR x) (DR y).

Infix "~<=r" := CoLeR (at level 90). 

Lemma coler_refl : forall x, x ~<=r x.
  cofix.
  intro x. rewrite (decompr_eql x). 
  destruct x. simpl. apply coler_base.
  simpl. apply coler_next.
  apply coler_refl.
Defined.  

Ltac decompr_eql_tac :=
  match goal with 
    | [ |- ?x ~<=r ?y ] => rewrite (decompr_eql x) ; simpl ;
      rewrite (decompr_eql y) ; 
        simpl ; try (apply coler_refl) 
          ; try (apply coler_right) ; 
            try (apply coler_next)
  end.
  
(* We take equality to be the relation induced by symetrising. *)
Definition CoEqR x y := CoLeR x y /\ CoLeR y x.

Infix "~=r" := CoEqR (at level 90). 

Lemma coeqR_refl : forall x, x ~=r x.
Proof. 
  intros.
  unfold CoEqR. split ; decompr_eql_tac.
Defined. 
  
(* Trivial, by definition *)
Lemma coler_antisym : forall x y, CoLeR x y /\ CoLeR y x -> CoEqR x y.
Proof. auto. 
Defined.

Lemma botr_least : forall x, F ~<=r x.
Proof.
  cofix.
  intros. destruct x. apply coler_base.
  apply coler_right. apply botr_least.
Defined.

Lemma coler_trans : forall x y z, x ~<=r y -> y ~<=r z -> x ~<=r z.
  cofix.
  intros x y z Hxy Hyz.
  destruct x ; destruct y ; destruct z ; inversion Hxy ; inversion Hyz ; subst.
  exact Hxy. exact Hyz.
  decompr_eql_tac. apply botr_least.
  apply coler_base. apply coler_base.
  decompr_eql_tac. apply (coler_trans x y z H1 H4).
Defined. 

CoFixpoint topr : Rierp := DR topr.

Lemma topr_greatest : forall x, x ~<=r topr.
Proof.
  cofix.
  intros. destruct x ; decompr_eql_tac ; auto.
Defined.

Lemma non_degenerate_r : ~ (F ~=r topr).
Proof.
  unfold not. intros.
  inversion H.
  inversion H1. rewrite (decompr_eql topr) in H3 ; simpl in *. inversion H3.
Defined. 

CoFixpoint meetr (x : Rierp) (y : Rierp) : Rierp := 
  match x with 
    | F => F
    | DR x' => match y with 
                 | F => F
                 | DR y' => DR (meetr x' y')
               end
  end.

Lemma meetr_correct : (forall x y, meetr x y ~<=r x) /\ (forall x y, meetr x y ~<=r y).
Proof.
  split.
  (* left *)
  cofix.
  intros. destruct x ; destruct y ; decompr_eql_tac.
  apply botr_least.
  apply meetr_correct.
  (* right *) 
  cofix.
  intros. destruct x ; destruct y ; decompr_eql_tac.
  apply botr_least.
  apply meetr_correct.
Defined.

Lemma meetr_greatest : forall a x y, (a ~<=r x) /\ (a ~<=r y) -> (a ~<=r meetr x y).
Proof.
  cofix.
  intros. 
  inversion H.
  destruct x ; destruct y ; destruct a ; decompr_eql_tac.
  inversion H0. inversion H0. inversion H1. (* impossible *)
  apply botr_least.
  inversion H0. inversion H1. subst.
  apply meetr_greatest. split. exact H4. exact H7.
Defined.

CoFixpoint joinr (x : Rierp) (y : Rierp) : Rierp := 
  match x,y with 
    | F,F => F
    | DR x', F => DR x'
    | F, DR y' => DR y' 
    | DR x',DR y' => DR (joinr x' y')
  end.

Lemma joinr_correct : (forall x y, x ~<=r joinr x y) /\ (forall x y, y ~<=r joinr x y).
Proof.
  split.
  (* left *)
  cofix.
  intros. destruct x ; destruct y ; decompr_eql_tac.
  apply botr_least.
  apply joinr_correct.
  (* right *)
  cofix.
  intros. destruct x ; destruct y ; decompr_eql_tac.
  apply botr_least. 
  apply joinr_correct.
Defined.

Ltac decompr_le_solve := 
  match goal with 
    | [ H : DR ?x ~<=r F |- ?y ] => inversion H
    | [ |- F ~<=r ?x ] => apply botr_least
  end.

Lemma joinr_least : forall a x y, (x ~<=r a) /\ (y ~<=r a) -> (joinr x y ~<=r a).
Proof.
  cofix. 
  intros. 
  inversion H.
  destruct x ; destruct y ; destruct a ; decompr_eql_tac ; try decompr_le_solve.
  inversion H1. subst. exact H4.
  inversion H0. subst. exact H4.
  inversion H0. inversion H1. subst. apply joinr_least. split. exact H4. exact H7. 
Defined.

(* We now have another bounded lattice! *)

(* 
   Making the Galois connection 
*) 

CoFixpoint nots (x : Sierp) : Rierp :=
  match x with 
    | T => F 
    | DS x' => DR (nots x')
  end.

CoFixpoint notr (y : Rierp) : Sierp := 
  match y with 
    | F => T 
    | DR x' => DS (notr x') 
  end.

Lemma fold_notr : F = nots T.
Proof.
  intros. rewrite (decompr_eql (nots T)). simpl. auto.
Defined.

Lemma fold_nots : T = notr F.
Proof.
  intros. rewrite (decomp_eql (notr F)). simpl. auto.
Defined.

Lemma notmore : forall x, DR x ~<=r F -> False.
Proof. 
  intros.
  inversion H.
Defined.

Lemma notless : forall x, T ~<= DS x -> False.
Proof.
  intros. 
  inversion H.
Defined. 

Lemma galois : forall x y, x ~<=r nots y <-> y ~<= notr x.
Proof.
  split.
  (* left *)
  generalize x y. 
  cofix.
  intros.
  destruct x0 ; destruct y0 ; decomp_eql_tac.
  rewrite (decompr_eql (nots (DS y0))) in H. simpl in H. inversion H. 
  apply top_greatest. apply top_greatest.
  rewrite (decompr_eql (nots T)) in H. simpl in H. inversion H. 
  rewrite (decompr_eql (nots (DS y0))) in H. simpl in H. inversion H. subst. 
  apply galois. exact H2. 
  (* right *)
  generalize x y. 
  cofix.
  intros.
  destruct x0 ; destruct y0 ; decompr_eql_tac.
  apply botr_least.
  rewrite (decomp_eql (notr (DR x0))) in H. simpl in H. inversion H. 
  rewrite (decomp_eql (notr (DR x0))) in H. simpl in H. inversion H. subst. 
  apply galois. exact H2. 
Defined.

(* Mixing signatures *) 

CoFixpoint meetrs (x : Rierp) (y : Sierp) : Rierp := 
  match x with 
    | F => F 
    | DR x' => match y with
                 | T => x' 
                 | DS y' => DR (meetrs x y) 
               end
  end.

Fixpoint strip (n:nat) (x : Sierp) {struct n} : Prop := 
  match n with 
    | O => match x with 
             | T => True 
             | DS x' => False
           end
    | S n' => match x with 
                | T => True 
                | DS x' => strip n' x'
              end
  end.

Definition isTrue (x : Sierp) := exists n, strip n x.

Fixpoint stripr (n:nat) (x : Rierp) {struct n} : Prop := 
  match n with 
    | O => match x with 
             | F => False
             | DR x' => True
           end
    | S n' => match x with 
                | F => False
                | DR x' => stripr n' x'
              end
  end.

Definition isFalse (x : Rierp) := exists n, stripr n x.

(* To justify mixed signatures we use truth tables *) 

Lemma meetrs_correct : forall x y, isFalse (meetrs x y) -> isFalse x \/ ~ isTrue y.

(* infinite joins correct *) 
(* 
Require Import Streams.

CoFixpoint exOne (A : Set) (c : Sierp) (s : Stream A) (P : A -> Sierp) : Sierp :=
  match c with 
    | T => T
    | DS(x') => match s with 
                  | Cons x s' => match P x with 
                                   | T => T 
                                   | DS(x'') => DS (exOne A (meet x' x'') s' P)
                                 end
                end
  end.

Definition ex (A : Set) (s : Stream A) (P : A -> Sierp) : Sierp := 
  exOne A bot s P.
Implicit Arguments ex [A].

CoFixpoint from n := Cons n (from (1+n)).
Definition nat := from O.

Lemma test : DS (DS (DS T)) ~<= DS T.
Proof.
  intros. apply cole_next. apply top_greatest. 
Defined. 

Lemma test2 : DR F ~<=r DR (DR F).
Proof.
  intros. apply coler_next. apply botr_least.
Defined. 

*)