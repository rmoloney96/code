
CoInductive S : Set := 
| T : S
| DS : S -> S.

Definition decomp (x : S) : S := 
  match x with 
    |T => T
    | DS x' => DS x'
  end.

Lemma decomp_eql : forall x, x = decomp x.
  intro x. case x. simpl. auto.
  intros. simpl. auto.
Defined.    

CoInductive CoLe : S -> S -> Prop := 
| cole_base : CoLe T T 
| cole_left : forall x y, CoLe x y -> 
  CoLe (DS x) y
| cole_right : forall x y, CoLe x y -> 
  CoLe x (DS y).

Infix "~<=" := CoLe (at level 90). 

Lemma cole_refl : forall x, x ~<= x.
  cofix.
  intro x. rewrite (decomp_eql x). 
  destruct x. simpl. apply cole_base.
  simpl. apply cole_left. apply cole_right. 
  apply cole_refl.
Defined.  

Ltac decomp_eql_tac :=
  match goal with 
    | [ |- ?x ~<= ?y ] => rewrite (decomp_eql x) ;
      rewrite (decomp_eql y) ; 
        simpl ; try (apply cole_refl) 
          ; try (apply cole_right) ; try (apply cole_left)
  end.
  
(* We take equality to be the relation induced by symetrising. *)
Definition CoEq x y := CoLe x y /\ CoLe y x.

(* Trivial, by definition *)
Lemma cole_antisym : forall x y, CoLe x y /\ CoLe y x -> CoEq x y.
Proof. auto. 
Defined.

Lemma cole_sym : forall x y, x ~<= y -> y ~= x.
  cofix. 
  intros x y Hxy. rewrite (decomp_eql x) in *.
  rewrite (decomp_eql y) in *. 
  destruct x ; destruct y. 
  (* T T *) 
  apply coeq_refl.
  simpl in Hxy. inversion Hxy. 
  simpl in Hxy. inversion Hxy.
  simpl in *. apply coeq_next. 
  apply coeq_sym. inversion Hxy as [H1|]; subst. exact H1.
Defined.

Lemma coeq_trans : forall x y z, x ~= y -> y ~= z -> x ~= z.
  cofix.
  intros x y z Hxy Hyz.
  destruct x ; destruct y ; destruct z ; inversion Hxy ; inversion Hyz ; subst.
  apply coeq_base.
  apply coeq_next. eapply coeq_trans. eauto. eauto.
Defined. 

CoFixpoint bot : S := DS bot.







CoInductive CoEq : S -> S -> Prop := 
| coeq_base : CoEq T T
| coeq_next : forall x y, CoEq x y -> 
  CoEq (DS x) (DS y).

Hint Constructors CoEq.
 
Infix "~=" := CoEq (at level 90). 

Lemma coeq_refl : forall x, x ~= x.
  cofix.
  intro x. rewrite (decomp_eql x). 
  destruct x. simpl. apply coeq_base.
  simpl. apply coeq_next. 
  apply coeq_refl.
Defined.  
  
Lemma coeq_sym : forall x y, x ~= y -> y ~= x.
  cofix. 
  intros x y Hxy. rewrite (decomp_eql x) in *.
  rewrite (decomp_eql y) in *. 
  destruct x ; destruct y. 
  (* T T *) 
  apply coeq_refl.
  simpl in Hxy. inversion Hxy. 
  simpl in Hxy. inversion Hxy.
  simpl in *. apply coeq_next. 
  apply coeq_sym. inversion Hxy as [H1|]; subst. exact H1.
Defined.

Lemma coeq_trans : forall x y z, x ~= y -> y ~= z -> x ~= z.
  cofix.
  intros x y z Hxy Hyz.
  destruct x ; destruct y ; destruct z ; inversion Hxy ; inversion Hyz ; subst.
  apply coeq_base.
  apply coeq_next. eapply coeq_trans. eauto. eauto.
Defined. 

CoFixpoint bot : S := DS bot.

CoFixpoint min (x : S) (y : S) : S := 
  match x with 
    | T => T
    | DS x' => match y with 
                 | T => T
                 | DS y' => DS (min x' y')
               end
  end.


Lemma min_commutative : forall x y, min x y ~= min y x.
Proof.
  cofix. intros. destruct x ; destruct y ; decomp_eql_tac.
  apply min_commutative.
Defined.

  
Lemma min_associative : forall x y z, min x (min y z) ~= min (min x y) z.
Proof.
  cofix. intros. destruct x ; destruct y ; destruct z ; decomp_eql_tac. 
  apply min_associative.
Defined.
  
Lemma min_is_join : (forall x,  min x bot ~= x) /\ (forall x, min T x ~= T).
Proof.
  split.
  (* Bottom *)
  cofix.
  destruct x. decomp_eql_tac. decomp_eql_tac. apply min_is_join.
  destruct x. decomp_eql_tac. 
  decomp_eql_tac.
Defined.

(*
Ltac codest := 
  match goal with 
    | [ H : Delay T ] |- 
*)

CoFixpoint max (x : DS) (y : DS) : DS := 
  match x with 
    | N T => y
    | D x' => match y with 
                | N T => N T
                | D y' => D (max x' y')
              end
  end. 

Fixpoint atleast (n : nat) (d : DS) : bool := 
  match d with 
    | N T => true
    | D d' => match n with 
                | O => false
                | S n' => atleast n' d'
              end
  end.

Fixpoint atleastP (n : nat) (d : DS) : Prop := 
  match d with 
    | N T => True
    | D d' => match n with 
                | O => False
                | S n' => atleastP n' d'
              end
  end.

(* some reflective principles *)
Lemma atleastimp : forall n d, atleastP n d -> atleast n d = true.
Proof.
  induction n. destruct d. destruct s. intros. simpl in * ; auto.
  intros. simpl in *. inversion H.
  destruct d. destruct s. intros. simpl in *. auto.
  intros. simpl in *. apply IHn. auto.
Defined.

Lemma impatleast : forall n d, atleast n d = true -> atleastP n d.
Proof.
  induction n. destruct d. destruct s. intros. simpl in * ; auto.
  intros. simpl in *. inversion H.
  destruct d. destruct s. intros. simpl in *. auto.
  intros. simpl in *. apply IHn. auto.
Defined.

Require Import Streams.

Section Streams.
  Variable A : Set. 
  
  Lemma unfold_Stream :
    forall x:(Stream A), x = match x with
                           | Cons a s => Cons a s
                         end. 
  Proof. 
    destruct x ; auto.
  Defined.
End Streams.
Implicit Arguments unfold_Stream [A].

CoFixpoint from (n: nat) : Stream nat := Cons n (from (S n)).
 
Definition naturals := from O. 

(* ex can be used directly in sentences *)
CoFixpoint ex (A : Set) (s : Stream A) (P : A -> bool) : DS :=
  match s with 
    | Cons x s' => match P x with 
                     | true => N T
                     | false => D (ex A s' P)
                   end
  end.
Implicit Arguments ex [A].

(* 'all' must be looked at at the meta level *)
CoFixpoint all (A : Set) (s : Stream A) (P : A -> bool) : DS := 
  match s with 
    | Cons x s' => match P x with 
                     | false => N T 
                     | true => D (all A s' P)
                   end
  end.
Implicit Arguments all [A].

Require Import Compare_dec.

Definition sentence1 := all naturals (fun x => leb O x).

Lemma sentence_holds : sentence1 ~= inf.
Proof.
  unfold sentence1.   
  generalize naturals.
  cofix.
  intros. simpl.
  rewrite (decomp_eql (all s (fun _ : nat => true))).
  rewrite (decomp_eql inf).
  simpl. destruct s. simpl.  
  apply coeq_next. auto.
Defined.

Definition not_inf x := x ~= inf.
Definition not_nt := forall x, x = N T. 

Definition negb := (fun x => match x with
                               | true => false 
                               | false => true
                             end).

Type not_inf.

Lemma test : inf ~= inf.
Proof. 
  intros. apply coeq_refl.
Defined.

(* Double negation translation using only existentials. *)
Lemma sentence2 : not_inf (ex naturals (fun x => negb (leb O x))).
Proof.
  unfold not_inf.
  generalize naturals.
  cofix.
  intros.
  rewrite (decomp_eql (ex s (fun x : nat => negb (leb 0 x)))).
  rewrite (decomp_eql inf).
  destruct s. 
  simpl.
  apply coeq_next. apply sentence2.
Defined.

CoFixpoint f (n : nat) : DS := D (f (S n)).

Lemma f_inf : forall n, f n ~= inf.
Proof. 
  cofix.
  intros. 
  rewrite (decomp_eql (f n)). 
  rewrite (decomp_eql inf).
  simpl.
  apply coeq_next.
  apply f_inf.
Defined.
  
(* 

Principles of positivity 

1) Remove all universal quanification, by replacement with 
   negative statements.

2) Start at the outermost statement, and work in.

3) 


¬ Ex x. ¬ P x

True -> Inf, 


Compositionality of computer programs. 

If we have inductive or structurally recursive programs, they can
always use inductive arguments internally. 

*)   
  


