Require Import String. 
Require Import List.

Fixpoint Suffix `A` (l:list A) (l':list A) : Prop := 
  match l' with 
    | nil => False 
    | cons h' t' => l = t' \/ Suffix A l t'
  end.

(* Definition Suffix `A` (l:list A) (l':list A) := Prefix (rev l) (rev l'). *)

Lemma suffix_correct : forall A (l':list A) (l:list A), Suffix l l' -> exists l'':list A, l'' <> nil /\ l''++l=l'.
Proof.
  induction l'. intros. inversion H.
  intros. simpl in H. destruct l. exists (a::l'). split. congruence. rewrite app_nil_end. auto. inversion H. rewrite H0. 
  exists (a::nil). auto. split. congruence.
  firstorder.
  apply IHl' in H0. inversion H0.
  exists (a::x). simpl. split. congruence. inversion H1. subst. auto.
Defined.

Lemma suffix_smaller : forall A (l:list A) (l':list A), Suffix l l' -> length l < length l'.
Proof.
  intros A l l'. generalize dependent l. generalize dependent l'.
  induction l' ; destruct l ; firstorder simpl in * ; subst ; auto with arith.
Defined.

Lemma suffix_one : forall A (l l':list A) (a:A), Suffix (cons a l') l -> Suffix l' l.
Proof.
  intros. induction l. inversion H.
  simpl. inversion H. subst. right. simpl. auto.
  right. apply IHl. auto.
Defined. 

Lemma suffix_not_nil : forall A (l l':list A), Suffix l l' -> l' <> nil.
Proof.
  intros. destruct l'. inversion H. unfold not. intros. inversion H0.
Defined.

Lemma suffix_app : forall A (l x:list A), x <> nil -> Suffix l (x ++ l). 
Proof.
  intros. induction x. congruence.  
  simpl. destruct x. left. simpl. auto.
  simpl. right. simpl in IHx. apply IHx. congruence.
Defined.

Lemma suffix_trans : forall A (l l' l'':list A), Suffix l' l -> Suffix l'' l' -> Suffix l'' l.
Proof.
  intros A l l' l'' H H0. cut (Suffix l' l) ; auto ; intros H1. apply suffix_not_nil in H1. 
  apply suffix_correct in H ; apply suffix_correct in H0.
  destruct H. destruct H0. destruct H ; destruct H0. subst.
  rewrite <- app_ass in *. apply suffix_app. 
  destruct x ; destruct x0 ; try (congruence).
  simpl. firstorder.
Defined.

Lemma Suffix_acc : forall A (l:list A), Acc Suffix l.
Proof. 
  induction l. 
  constructor. intros. inversion H.
  constructor. intros. inversion H. subst. auto.
  eapply Acc_inv. eauto. auto.
Defined. 

Theorem Suffix_wf : forall A, well_founded (Suffix (A:=A)).
Proof.
  intros. exact (Suffix_acc A).
Defined.

Inductive Parse `A` (l:list string) : bool -> Type := 
| empty_parse : A -> {l' : list string | l' = l} -> Parse A (l:list string) false
| productive_parse : A -> {l' : list string | Suffix l' l} -> Parse A (l:list string) true.
Implicit Arguments empty_parse [A].
Implicit Arguments productive_parse [A].  

Definition M := list. 
Definition ret `A` (x:A) := cons x nil.
Definition fail `A` := (nil (A:=A)). 

Definition Parser (A:Type) b := forall (l:list string), M (Parse A l b).

Definition empty `A` : Parser (list A) false.
  intros. unfold Parser. 
  refine 
    (fun toks => ret (empty_parse toks nil _)). exists toks. auto.
Defined.

Ltac dup H H' := 
  let T := type of H in 
    cut T ; try (intros H' ; auto).

Definition alt : forall A b1 b2, Parser A b1 -> Parser A b2 -> Parser A (b1 || b2).
  intros A b1 b2 HP1 HP2. unfold Parser in *. 
  case_eq (orb b1 b2) ; destruct b1 ; destruct b2 ; firstorder; simpl in * ; try (congruence).
Defined.

Extraction alt. 

Print alt. 


