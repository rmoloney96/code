

CoInductive Delay (A : Set) : Set := 
  | N : A -> Delay A
  | D : Delay A -> Delay A.

Implicit Arguments N [A].
Implicit Arguments D [A].

Inductive Serpinsky : Set := 
  | T : Serpinsky.

Definition DS := Delay Serpinsky.

Definition decomp (x : DS) : DS := 
  match x with 
    | N T => N T
    | D x' => D x'
  end.

Lemma decomp_eql : forall x, x = decomp x.
  intro x. case x. simpl. intros. case s. auto.
  intros. simpl. auto.
Defined.    
 
CoInductive CoEq : DS -> DS -> Prop := 
| coeq_base : CoEq (N T) (N T)
| coeq_next : forall x y, CoEq x y -> 
  CoEq (D x) (D y).

Hint Constructors CoEq.
 
Infix "~=" := CoEq (at level 90). 

Lemma coeq_refl : forall x, x ~= x.
  cofix.
  intro x. rewrite (decomp_eql x). 
  destruct x. simpl. destruct s. apply coeq_base. 
  simpl. apply coeq_next. 
  apply coeq_refl.
Defined.  
  
Lemma coeq_sym : forall x y, x ~= y -> y ~= x.
  cofix. 
  intros x y Hxy. rewrite (decomp_eql x) in *.
  rewrite (decomp_eql y) in *. 
  destruct x ; destruct y. destruct s ; destruct s0.
  simpl in *. exact Hxy. destruct s.
  simpl in Hxy. inversion Hxy. destruct s.
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

Hint Resolve coeq_refl coeq_sym coeq_trans.

CoFixpoint inf : DS := D inf.

CoFixpoint min (x : DS) (y : DS) : DS := 
  match x with 
    | N T => N T
    | D x' => match y with 
                | N T => N T 
                | D y' => D (min x' y')
              end
  end.

Lemma min_commutative : forall x y, min x y ~= min y x.
Proof.
  cofix. intros. destruct x ; destruct y. 
  destruct s ; destruct s0.  apply coeq_refl.
  rewrite (decomp_eql (min (N s) (D y))). 
  rewrite (decomp_eql (min (D y) (N s))).
  simpl. apply coeq_refl.
  rewrite (decomp_eql (min (N s) (D x))). 
  rewrite (decomp_eql (min (D x) (N s))).
  simpl. apply coeq_refl.  
  rewrite (decomp_eql (min (D x) (D y))). 
  rewrite (decomp_eql (min (D y) (D x))).
  simpl. apply coeq_next. apply min_commutative.
Defined.

(* 

Lemma min_associative : forall x y z, min x (min y z) ~= min (min x y) z.
Proof.
  cofix. intros. destruct x ; destruct y ; destruct z. 
  destruct s ; destruct s0 ; destruct s1.  
  rewrite (decomp_eql (min (N T) (min (N T) (N T)))). 
  rewrite (decomp_eql (min (min (N T) (N T)) (N T))). 
  compute. apply coeq_refl.
  rewrite (decomp_eql (min (N T) (min (N T) (N T)))). 
  rewrite (decomp_eql (min (min (N T) (N T)) (N T))). 
  
*) 
  
Lemma min_is_join : (forall x,  min x inf ~= x) /\ (forall x, min (N T) x ~= (N T)).
Proof.
  split.
  (* Bottom *)
  cofix.
  intros. 
  destruct x. destruct s.
  rewrite (decomp_eql (min (N T) inf)). compute. 
  apply coeq_refl.
  rewrite (decomp_eql (min (D x) inf)).
  simpl. apply coeq_next. apply min_is_join.
  (* Top *)
  intros.
  destruct x. destruct s.
  rewrite (decomp_eql (min (N T) (N T))). compute.
  apply coeq_refl.
  rewrite (decomp_eql (min (N T) (D x))). compute.
  apply coeq_refl.
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
  


