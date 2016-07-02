
Inductive term : Set := 
| true 
| false 
| zero 
| succ (t : term) 
| pred (t : term)
| iszero (t : term)
| ift (t1 : term) (t2 : term) (t3 : term).

Inductive value : term -> Set := 
| true_v : forall (t : term), t = true -> value t
| false_v : forall (t : term), t = false -> value t. 

Require Import List. 

Fixpoint constants (t : term) : list term := 
  match t with 
    | true => true::nil
    | false => false::nil 
    | zero => zero::nil
    | succ t' => constants t'
    | pred t' => constants t' 
    | iszero t' => constants t'
    | ift t1 t2 t3 => (constants t1)++(constants t2)++(constants t3)
  end.

Fixpoint size (t : term) : nat := 
  match t with 
    | true => 1 
    | false => 1
    | zero => 1
    | succ t' => 1+(size t')
    | pred t' => 1+(size t')
    | iszero t' => 1+(size t')
    | ift t1 t2 t3 => 1+(size t1)+(size t2)+(size t3)
  end.

Require Import Compare_dec.

Fixpoint max (nl : list nat) : nat := 
  match nl with 
    | nil => 0 
    | h::nil => h
    | h::t => 
      if (leb (max t) h) then h else (max t)
  end.
  
Fixpoint depth (t : term) : nat := 
  match t with 
    | true => 1 
    | false => 1
    | zero => 1
    | succ t' => 1+(depth t')
    | pred t' => 1+(depth t')
    | iszero t' => 1+(depth t')
    | ift t1 t2 t3 => 1+max((depth t1)::(depth t2)::(depth t3)::nil) 
  end.

Require Import Omega. 

Theorem constants_less_than_size : 
  forall (t : term), length (constants t) <= size t.
Proof. 
  induction t ; simpl in *; try omega.
  (* Last ift case *) 
  rewrite app_length. rewrite app_length. omega.
Qed. 

Inductive R1 : term -> term -> Prop := 
| e_iftrue : forall (t1 t2:term), R1 (ift true t1 t2) t1
| e_iffalse : forall (t1 t2:term), R1 (ift false t1 t2) t2
| e_if : forall (t1 t1' t2 t3:term), 
  R1 t1 t1' -> R1 (ift t1 t2 t3) (ift t1' t2 t3). 

Ltac ics H := inversion H ; clear H ; subst.

(* things that can only evaluate to themselves *)
Ltac inv_constants := 
  match goal with 
    | [ H : R1 true _       |- _ ] => ics H
    | [ H : R1 false _      |- _ ] => ics H
    | [ H : R1 zero  _      |- _ ] => ics H
    | [ H : R1 (succ _) _   |- _ ] => ics H
    | [ H : R1 (pred _) _   |- _ ] => ics H
    | [ H : R1 (iszero _) _ |- _ ] => ics H
    | [ H : R1 _ true       |- _ ] => ics H
    | [ H : R1 _ false      |- _ ] => ics H
    | [ H : R1 _  zero      |- _ ] => ics H
    | [ H : R1 _ (succ _)   |- _ ] => ics H
    | [ H : R1 _ (pred _)   |- _ ] => ics H
    | [ H : R1 _ (iszero _) |- _ ] => ics H
    | [ H : R1 (ift true _ _) _       |- _ ] => ics H
    | [ H : R1 (ift false _ _) _      |- _ ] => ics H
    | [ H : R1 (ift zero _ _)  _      |- _ ] => ics H
    | [ H : R1 (ift (succ _) _ _) _   |- _ ] => ics H
    | [ H : R1 (ift (pred _) _ _) _   |- _ ] => ics H
    | [ H : R1 (ift (iszero _) _ _) _ |- _ ] => ics H
    | [ H : R1 _ (ift true _ _)       |- _ ] => ics H
    | [ H : R1 _ (ift false _ _)      |- _ ] => ics H
    | [ H : R1 _ (ift zero _ _)       |- _ ] => ics H
    | [ H : R1 _ (ift (succ _) _ _)   |- _ ] => ics H
    | [ H : R1 _ (ift (pred _) _ _)   |- _ ] => ics H
    | [ H : R1 _ (ift (iszero _) _ _) |- _ ] => ics H 
    | _ => idtac
  end.
Hint Extern 1 (_ = _) => inv_constants.

Ltac inj H := 
  match goal with 
    | [ H : (_ = _) |- _ ] => injection H ; intros ; subst 
  end.
Hint Extern 1 (_ = _) => inj. 


Ltac H := 
Lemma nocirc : forall (A : Set) (h : A) (t : list A), cons h t  = t -> False.
  intros. induction t ; inversion H ; congruence.
Defined. 

Lemma ift_circle_1 : 
  forall (t t' t'': term), ift t t' t'' = t -> False. 
  induction t; auto; intros; inversion H. 
  rewrite H1 in * |-. rewrite H2 in * |-.  
  firstorder.
Defined. 

Lemma ift_circle_2 : 
  forall (t t' t'': term), ift t t' t'' = t' -> False. 
  induction t'; auto; intros; inversion H. 
  rewrite H1 in * |-. rewrite H2 in * |-.  
  firstorder.
Defined. 

Lemma ift_circle_3 : 
  forall (t t' t'': term), ift t t' t'' = t'' -> False. 
  induction t''; auto; intros; inversion H.    
  rewrite H1 in * |-. rewrite H2 in * |-.  
  firstorder.
Defined. 

Theorem determinacy_of_R1 : 
  forall (t t': term), R1 t t' -> forall (t'' : term), R1 t t'' -> t' = t''.
Proof.
  induction 1 ; auto. intros. 
  inversion H0 ; auto. subst. inversion H0. subst. auto. auto. 
  inversion H0 ; auto. subst. inversion H0. subst. auto.
    inversion H5; subst ;auto.  subst. inversion H0. subst. auto. auto.
     rewrite <- H2 in H0. inversion H0 ; auto. rewrite H10 in H6. 
     rewrite H6. apply ift_circle_3 in H6. inversion H6.
     subst. cut (t1' = t1'0). intros. rewrite H1. auto.
     apply IHR1. auto. 
Defined.

Inductive Normal : term -> Set := 
| normal : forall t t', ~ R1 t t' -> Normal t.

Theorem Normal_implies_value : 
  forall (t : term), Normal t -> value t.
Proof. 
  induction t. intros. 
  apply true_v. auto.
  intros. apply false_v. auto.
  intros.  
auto. 
  inversion H. unfold not in H0.  


Inductive R1s : term -> term -> Set := 
| R1_self : forall t, R1s t t
| R1_once : forall t t', R1 t t' -> R1s t t'
| R1_many : forall t t' t'', R1s t t' -> R1s t' t'' -> R1s t t''.

Theorem 







  



  
  
  