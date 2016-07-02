
CoInductive CoNat : Type := 
| Z : CoNat
| S : CoNat -> CoNat.

Definition pred (x : CoNat) : CoNat := 
  match x with 
    | Z => Z 
    | S x' => x'
  end.

Definition decomp (x : CoNat) : CoNat := 
  match x with 
    | Z => Z
    | S x' => S x'
  end.

Lemma decomp_eql : forall x, x = decomp x.
  intro x. case x. simpl. auto.
  intros. simpl. auto.
Defined.    

CoInductive CoEq : CoNat -> CoNat -> Prop := 
| coeq_base : CoEq Z Z
| coeq_next : forall x y, CoEq x y -> 
  CoEq (S x) (S y).

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
  simpl in *. exact Hxy.
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

Hint Resolve coeq_refl coeq_sym coeq_trans.

Require Import Setoid.

Add Relation CoNat CoEq
  reflexivity proved by coeq_refl
  symmetry proved by coeq_sym
  transitivity proved by coeq_trans
as coeq_relation.

CoFixpoint inf : CoNat := S(inf).

CoFixpoint add (x:CoNat) (y:CoNat) : CoNat := 
  match y with 
    | Z => x
    | S y' => S (add x y')
  end.

Infix "+" := add.

Lemma add_x_z : forall x, x + Z ~= x.
  intros. destruct x. 
  (* Z *) 
  rewrite (decomp_eql (Z + Z)) ; simpl ; auto.
  (* x *)
  rewrite (decomp_eql (S x + Z)). simpl. auto.
Defined. 
   
Lemma add_z_x : forall x, Z + x ~= x.
  cofix. 
  intros x. destruct x. 
  (* Z *)
  rewrite (decomp_eql (Z + Z)) ; simpl ; auto.
  (* x *)
  rewrite (decomp_eql (Z + S x)) ; simpl.
  apply coeq_next (* guard *). auto.
Defined. 

Lemma add_x_s : forall x y, x + (S y) = S (x + y).
  intros x y. rewrite (decomp_eql (add x (S y))). simpl. auto.   
Defined. 

Ltac co_unfold elt := 
  match goal with 
    | |- context f [add ?x ?y] => 
      rewrite (decomp_eql (add x y)) ; simpl
  end.

Lemma add_s_x : forall x y, ((S x) + y) ~= (S (x + y)).
  cofix.
  intros x y. 
  destruct x ; destruct y. 
  (* Z, Z *) 
  clear add_s_x. repeat co_unfold add. auto.
  (* Z, y *) 
  co_unfold add. apply coeq_next. (* guard *)
  rewrite (decomp_eql (Z + S y)). simpl. auto. 
  (* x, Z *) 
  co_unfold add. apply coeq_next. (* guard *)
  rewrite (decomp_eql (S x + Z)). simpl. auto. 
  (* x, y *)
  co_unfold add. apply coeq_next. (* guard *)
  rewrite (decomp_eql (S x + S y)). simpl. auto.
Defined.    
  
Definition inf_eq : inf = (S inf).
  apply (decomp_eql inf).
Defined. 

Lemma add_x_inf : forall x, (x+inf) ~= inf.
  cofix.
  intros x. rewrite (decomp_eql inf).
  simpl. rewrite add_x_s.
  apply coeq_next. auto.
Defined. 

Lemma add_inf_x : forall x, (inf+x) ~= inf.
  cofix. 
  intros x. destruct x.
  (* Z *) 
  rewrite add_x_z. reflexivity. 
  (* x *)
  rewrite (decomp_eql inf). simpl. 
  co_unfold add.
  apply coeq_next. (* guard *)
  rewrite <- inf_eq. auto.
Defined.   
