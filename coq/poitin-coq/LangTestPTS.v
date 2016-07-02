Require Import List. 
Notation "[]" := nil.
Notation "[ a ]" := (cons a nil).
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..). 
Infix "::" := cons.

Require Import Arith. 
Infix "===" := eq_nat_dec (at level 50). 

Inductive term : Set := 
| var : nat -> term
| Pi : term -> term -> term
| abs : term -> term -> term
| app : term -> term -> term
| star : term
| box : term.
Coercion var : nat >-> term.

Fixpoint open_rec (k:nat) (t:term) (u:term) : term := 
  match t with 
    | var n => match (k === n) with 
                 | left Hr => u 
                 | right Hr => t
               end
    | Pi A B => Pi (open_rec k A u) (open_rec (S k) B u)
    | abs A B => abs (open_rec k A u) (open_rec (S k) B u)
    | app A B => app (open_rec k A u) (open_rec k B u) 
    | star => star 
    | box => box
  end.
Definition open := open_rec 0.

Inductive beta_eq : term -> term -> Prop := 
| beta_eq_base : forall A B C, beta_eq (app (abs A B) C) (open B C)
| beta_eq_refl : forall A, beta_eq A A
| beta_eq_sym : forall A B, beta_eq A B -> beta_eq B A 
| beta_eq_trans : forall A B C, beta_eq A B -> beta_eq B C -> beta_eq A C. 
Infix "=b=" := beta_eq (at level 50).

Inductive cube : term -> term -> Prop := 
| cube_s_s : cube star star 
| cube_b_b : cube box box 
| cube_s_b : cube box star.
Infix "~>" := cube (at level 50).

Fixpoint reduce (t:term) : term := 
  match t with 
    | var n => var n
    | Pi A B => Pi A B
    | abs A B => abs A B
    | app (abs A B) C => (open B C)
    | app A B => app (reduce A) B
    | star => star 
    | box => box
  end.      

Definition context := list (nat * term).

Reserved Notation "G |- x ;; T" (at level 55).
Inductive turnstile : context -> term -> term -> Set := 
| star_intro : [] |- star ;; box
| var_intro : forall x T G, 
  In (x,T) G -> 
  G |- x ;; T
| app_intro : forall f a A A' B G, 
  G |- f ;; (Pi A B) -> 
    G |- a ;; A' ->
      A =b= A' -> 
      G |- (app f a) ;; (open B a)
| lam_intro : forall x b A B G t, 
  ([(x,A)] ++ G) |- b ;; B -> 
    G |- (Pi A B) ;; t -> 
      G |- (abs A b) ;; (Pi A B)
| pi_intro : forall x A B t s, 
  G |- A ;; s -> 
    ([(x,A)] ++ G) |- B ;; t -> 
      s ~> t -> 
      G |- (Pi A B) ;; t      
  where "G |- x ;; T" := (turnstile G x T).




Definition varin (n:nat) (c:context) : {t | In (n,t) c} + {forall t, ~ In (n,t) c}.
Proof.
  intros. induction c.
  (*nil*)
  right ; intros ; simpl ; auto.
  (*cons*)
  destruct a. simpl. 
  case_eq (n0 === n). 
    (* n0 = n *)
    intros e He. rewrite e in *. 
    left. exists t. auto.
    (* n0 <> n *)
    intros ne Hne.
    case_eq IHc.
      (* In next *)  
      intros e He.  left. inversion e. exists x. auto.
      (* not In next *)
      intros Hni Hnew. right. 
      intros. unfold not. intros. inversion H.
        (* left *) 
        inversion H0. congruence.    
        (* right *) 
        unfold not in * ; eapply Hni. eauto.
Defined.
Infix "@" := varin (at level 55).
