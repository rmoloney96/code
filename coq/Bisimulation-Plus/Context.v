Require Import SystemF. 
Require Import List.
Require Import Eval. 
Require Import Bisimulation.
Require Import Arith. 

Section Contextual. 

  Variable Delta : nat -> Term.
  Variable Xi : nat -> Ty.  
  Variable Prog : forall n l m, Derivation Xi [n ; l |= F m @ Xi m] -> Derivation Xi [n ; l |= Delta m @ Xi m]. 
  Variable ProgTy : forall m, valid (Xi m) 0.
  
  Notation "t ~> t'" := (Ev Delta t t') (at level 60).  
  Notation "t ~>+ t'" := (Evplus Delta t t') (at level 60).
  Notation "t ~>* t'" := (Evstar Delta t t') (at level 60). 

  Notation " a :<: b " := (simulates Delta Xi a b) (at level 90). 

Inductive reduces : Term -> Set := 
| reduces_base : 
  forall a, { b : Term & a ~>+ b } -> reduces a.

Inductive evaluates : Term -> Term -> Set := 
| evaluates_base : forall a b, a ~>* b -> notT (reduces b) -> evaluates a b.

Inductive Context : Set :=. 

Fixpoint insert (c : Context) (t : Term) : Term := 
  match c with 
  end.

Axiom contextual_equivalence : forall C a b A, 
  Derivation Xi [0 ; nil |= a @ A] ->
  Derivation Xi [0 ; nil |= b @ A] -> 
  a :<: b -> 
  (forall t : Term, Derivation Xi [0 ; nil |= t @ A] -> Derivation Xi [0 ; nil |= insert C t @ One]) -> 
  evaluates (insert C a) Unit -> 
  evaluates (insert C b) Unit.


CoInductive codiverges : Term -> Set := 
| codiverges_base : forall a b, a ~>+ b -> codiverges b -> codiverges a.

Axiom converges_or_diverges : forall a, converges Delta a + codiverges a.

(* 

Lemma weaken_one : forall t G n L ty xty,
  Derivation Xi [n; G ++ L |= t @ ty] ->
  Derivation Xi [n; G ++ xty :: L |= shift (length G) t @ ty].
Proof.
  induction t ; intros. 
  (* F *) 
  inversion H. subst. 
  apply FunIntro.
  (* V *) 
  apply shift_var; auto.
  (* App *) 
  inversion H; subst.
  apply ImpElim with (xty:=xty0); fold shift ; auto.
  (* TApp *) 
  inversion H; subst.
  apply AllElim ; fold shift; auto.
  (* Abs *) 
  inversion H; subst.
  apply ImpIntro ; fold shift; auto.
  cut (length G + 1 = length (t :: G)) ; [ intros H0 | rewrite plus_comm ; auto].
  rewrite H0. 
  cut (t :: G ++ xty :: L = (t :: G) ++ xty :: L) ; [intros H1 | auto].
  rewrite H1 ; auto. 
  (* Lam *) 
  inversion H ; subst.
  apply AllIntro ; fold shift ; auto.
  cut (map tyshift (G ++ xty :: L) = map tyshift G ++ (tyshift xty) :: map tyshift L) ; [ intros Heq | auto ].
  cut (length G = length (map tyshift G)) ; [intros Heq2 | auto ]. 
  rewrite Heq. rewrite Heq2. apply IHt.
  cut (map tyshift G ++ map tyshift L = map tyshift (G ++ L)); [ intros Heq3 | auto ].
  rewrite Heq3. auto.
    (* Heq3 *)
    rewrite map_app. auto. 
    (* Heq2 *) 
    rewrite map_length. auto.
    rewrite map_app. simpl. auto.
Defined.   

Fixpoint shiftn (n: nat) (d : nat) (t : Term) : Term := 
  match n with 
    | 0 => t 
    | S n' => shift d (shiftn n' d t)
  end.

Lemma weaken : forall F G t n L ty,
  Derivation Xi [n; G ++ L |= t @ ty] ->
  Derivation Xi [n; G ++ F ++ L |= shiftn (length F) (length G) t @ ty].
Proof.
  induction F. intros. simpl. auto.
  intros. 
  simpl. 
  apply weaken_one. apply IHF. auto.
Defined.

Lemma var_shift : forall n0 n, n < (S n0) -> shift (S n0) (V n) = V n.
Proof. 
  induction n0. 
  intros. simpl. destruct n. auto. 
  elimtype False. 
  firstorder.
  intros.
  unfold shift.
  case_eq (le_lt_dec (S (S n0)) n).
  intros.
  elimtype False. firstorder. 
  intros. auto.
Defined.

Lemma shift_id : forall a G A n m, 
  length G <= n -> 
  Derivation Xi [ m ; G |= a @ A ] -> 
  shift n a = a.
Proof.
  induction a ; intros.
  (* F *) 
  intros ; simpl ; auto.
  (* V *) 
  inversion H0. subst.
  destruct n0. 
    (* Z *) 
    elimtype False. firstorder. 
    (* S n0 *) 
    apply var_shift. 
    firstorder.
  (* App *) 
  simpl. 
  inversion H0 ; subst. 
  rewrite IHa1 with (m:=m) (G:=G) (A:=Imp xty A) ; auto. 
  rewrite IHa2 with (m:=m) (G:=G) (A:=xty) ; auto.
  (* TApp *) 
  simpl.
  inversion H0 ; subst.
  rewrite IHa with (m:=m) (G:=G) (A:=All ty) ; auto. 
  (* Abs *) 
  simpl.
  inversion H0 ; subst.
  rewrite IHa with (m:=m) (G:=t::G) (A:=ty) ; auto. 
  simpl. firstorder.
  (* Lam *) 
  simpl.
  inversion H0 ; subst.
  rewrite IHa with (m:=S m) (G:=map tyshift G) (A:=ty) ; auto.
  rewrite map_length. auto. 
Defined.

Lemma shiftn_id : forall a A m n,
  Derivation Xi [ 0 ; nil |= a @ A ] -> 
  a= shiftn m n a.
Proof.
  induction m ; intros.
  (* Z *)
  simpl. auto.
  (* S m *)
  simpl.
  rewrite shift_id with (G:=nil) (A:=A) (m:=0). 
  apply IHm. auto.
  simpl. firstorder.
  rewrite <- IHm. auto. auto.
Defined. 

Theorem app_nil_r : forall A (l : list A), l = l ++ nil.
Proof. 
  induction l ; firstorder.
Defined. 

Lemma GammaCloseVar : forall G a t A B, 
  Derivation Xi [ 0 ; (cons A G) |= t @ B ] -> 
  Derivation Xi [ 0; nil |= a @ A ] -> 
  Derivation Xi [ 0; G |= (sub t 0 a) @ B].
Proof.
  intros.
  cut (G = nil ++ G). intros. rewrite H1.  
  apply sub_preservation with (xty:=A). 
  auto.
  simpl; auto. 
  simpl; auto.
  cut (G = nil ++ G ++ nil) ; [ intros Heq | idtac].
  cut (a = shiftn (length G) (length (A:=Ty) nil) a) ; [ intros Heq_shift | idtac ].
  intros. rewrite Heq ; rewrite Heq_shift.
  apply weaken. 
  simpl. auto. simpl in *.   
  rewrite <- shiftn_id with (A:=A) (m:=length G) (n:=0). auto. auto.
  apply app_nil_r. simpl. auto.   
Defined.

Lemma app_diverges : forall f x A B, 
  Derivation Xi [0 ; nil |= f @ Imp A B] ->
  Derivation Xi [0 ; nil |= x @ A] -> 
  codiverges f -> 
  codiverges (App f x).
Proof. 
  refine (cofix app_diverges f x A B 
    (Hf : Derivation Xi [0 ; nil |= f @ Imp A B])
    (Hx : Derivation Xi [0 ; nil |= x @ A])
    (Hfdiv : codiverges f) 
    : codiverges (App f x) := _). 
  inversion Hfdiv. subst.
  apply codiverges_base with (b:= (App b x)).
  apply evplus_app with (s:=x) in H. auto. 
  apply app_diverges with (A:=A) (B:=B).
  apply evplus_preservation with (Xi:=Xi) (n:=0) (l:=nil) (ty:=Imp A B) in H ; auto using Prog, ProgTy.
  auto. auto.
Defined.

Axiom contextual_simulation : forall c a b A, 
  Derivation Xi [0 ; nil |= a @ A] ->
  Derivation Xi [0 ; nil |= b @ A] -> 
  a :<: b -> 
  Derivation Xi [0 ; (cons A nil) |= c @ One] -> 
  (sub c 0 b) ~>* Unit -> 
  (sub c 0 a) ~>* Unit.

Notation " a :~: b " := (bisimulates Delta Xi a b) (at level 90).
*)

End Contextual.
