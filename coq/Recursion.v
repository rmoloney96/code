
Require Import Arith. 

Inductive fact_domain : nat -> Prop :=
| fact_domain_zero :
  fact_domain 0
| fact_domain_pos :
  forall n : nat, fact_domain (n-1) -> fact_domain n.

Theorem fact_domain_pos_true : forall n : nat, fact_domain n -> 0 <= n.
Proof. 
  intros n H. case H. auto with arith. 
  intros n' H'. case H'. auto with arith.
  intros n'' H''. auto with arith. 
Defined.

Theorem fact_domain_inv :
  forall n : nat, fact_domain n -> 0 < n -> fact_domain (n-1).
Proof. 
  intros n H Hlt. case H. simpl. apply fact_domain_zero.
  intros n0' H'. auto. 
Defined.
Transparent fact_domain_inv.

Require Import Arith. 

Print fact_domain_inv.
 
Fixpoint fact (n : nat) (h : fact_domain n) {struct h} : nat :=
  match lt_eq_lt_dec n 0 with
    | inleft hle => 
      match hle with 
        | left nlt0 => False_rec nat (lt_n_O n nlt0)
        | right neq0 => 1
      end
    | inright hgt => 
      match h in (fact_domain n) return (fact_domain (n - 1)) with 
        | fact_domain_zero => fact_domain_zero
        | fact_domain_pos _ H' => n * (fact (n-1) H')
      end
  end.


      

(fact_domain_inv n h hgt))
  end.


Definition fact (n: nat) (h : fact_domain n) : nat.
Proof.
  refine 
    (fix f (n : nat) (h : fact_domain n) {struct h} :=  
      match le_gt_dec n 0 with 
        | left _ => 1 
        | right hgt => n * (f (n-1) (fact_domain_inv n h hgt))
      end).
  destruct n. inversion hgt. 
  simpl. cut (n-0 = n). intros. inversion h. simpl in *. rewrite H in *.       
  auto. auto with arith. 
Defined.

Require Import Ascii.
Require Import String. 


Inductive Suffix (s:string) : string -> Prop :=
| suffix_refl : Suffix s s
| suffix_next : forall s' c, Suffix s s' -> Suffix s (String c s').
Hint Constructors Suffix.

Lemma Suffix_empty : forall (s:string), Suffix "" s.
Proof.
  induction s ; auto ; destruct s ; auto. 
Defined.
Hint Resolve Suffix_empty.

Lemma Suffix_both : forall (s' s:string) c c', 
  Suffix (String c s) (String c' s') -> Suffix s s'.
Proof.
  induction s' ;intros ; inversion H ; subst ; auto. inversion H1.
  apply suffix_next. eapply IHs'. eauto.
Defined.

Definition ProperSuffix (s s':string) := exists c, Suffix (String c s) s'.
Hint Unfold ProperSuffix.

Lemma ProperSuffix_irrefl (s :string) : ~ ProperSuffix s s.
Proof.
  induction s. unfold not. intros. inversion H.
  inversion H0.
  unfold not. intros. inversion H.
  eapply Suffix_both in H0. 
  cut (ProperSuffix s s). intros. auto.
  eauto.
Defined.

Lemma ProperSuffix_not_empty (s :string) : ~ProperSuffix s "".
Proof.
  induction s. unfold  not. intros. inversion H. inversion H0.
  unfold not. intros. inversion H. inversion H0.
Defined.    

Lemma ProperSuffix_both : forall (s s':string) c c', 
  ProperSuffix (String c s) (String c' s') -> ProperSuffix s s'.
Proof. 
  destruct s; intros. inversion H ; subst ; auto. 
  apply Suffix_both in H0. unfold ProperSuffix.
  exists c. auto.

  inversion H. apply Suffix_both in H0. 
  unfold ProperSuffix. exists c. auto.
Defined.

Definition SuffixFamily (s:string) := {s' | Suffix s' s}.
