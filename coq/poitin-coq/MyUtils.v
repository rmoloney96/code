Require Import List. 
Require Import Peano_dec.

Fixpoint upto_aux m m' n {struct n} : list nat := 
  match n with 
    | 0 => nil 
    | (S n') => 
      match eq_nat_dec n m' with
        | left _ => nil
        | right _ => m::(upto_aux (S m) m' n')
      end
  end.
      
Definition upto m n := upto_aux m m n. 

Fixpoint downto m n {struct m} : list nat := 
  match eq_nat_dec m n with 
    | left _ => nil
    | right _ => 
      match m with 
        | 0 => nil 
        | (S m') => m::(downto m' n)
      end      
  end. 

Require Import Ascii.

Inductive digit : Set := Zero | One | Two | Three | Four | Five | Six | Seven | Eight | Nine.
Definition base10 := list digit.

Fixpoint base10_inc (xs : base10) := 
  match xs with 
    | nil => cons One nil
    | cons x xs' => 
      match x with 
        | Zero => cons One xs'
        | One => cons Two xs'
        | Two => cons Three xs'
        | Three => cons Four xs'
        | Four => cons Five xs'
        | Five => cons Six xs'
        | Six => cons Seven xs'
        | Seven => cons Eight xs'
        | Eight => cons Nine xs'
        | Nine => cons Zero (base10_inc xs')
      end
  end.

Fixpoint base10_of_nat (n:nat) := 
  match n with 
    | 0 => cons Zero nil
    | S n' => base10_inc (base10_of_nat n')
  end.

Definition nat_of_digit (d:digit) := 
  match d with 
    | Zero => 0
    | One => S(0)
    | Two => S(S(0))
    | Three => S(S(S(0)))
    | Four => S(S(S(S(0))))
    | Five => S(S(S(S(S(0)))))
    | Six => S(S(S(S(S(S(0))))))
    | Seven => S(S(S(S(S(S(S(0)))))))
    | Eight => S(S(S(S(S(S(S(S(0))))))))
    | Nine => S(S(S(S(S(S(S(S(S(0)))))))))
  end.
  
Fixpoint nat_of_base10 (b:base10) := 
  match b with 
    | nil => 0
    | cons d ds => (nat_of_digit d) + (10 * (nat_of_base10 ds))
  end.

Require Import String.
Open Local Scope char_scope.
Definition string_of_digit (d : digit) := 
  match d with 
    | Zero => "0"
    | One => "1"
    | Two => "2"
    | Three => "3"
    | Four => "4"
    | Five => "5"
    | Six => "6"
    | Seven => "7"
    | Eight => "8"
    | Nine => "9"
  end.      

Open Local Scope string_scope.
Fixpoint string_of_base10_aux (ds : base10) := 
  match ds with 
    | nil => ""
    | cons d ds' => String (string_of_digit d) (string_of_base10_aux ds') 
  end.

Definition string_of_base10 (ds : base10) := string_of_base10_aux (rev ds).

Definition string_of_nat (n:nat) := string_of_base10 (base10_of_nat n).

Require Import OptionMonad.
Open Scope char_scope.

Fixpoint base10_of_string_aux (s:string) : option base10 :=
  match s with
    | EmptyString => Some (A:=base10) nil
    | String c s' => 
      match c with 
        | "0" => t <- (base10_of_string_aux s') ;; ret (cons Zero t)
        | "1" => t <- (base10_of_string_aux s') ;; ret (cons One t) 
        | "2" => t <- (base10_of_string_aux s') ;; ret (cons Two t) 
        | "3" => t <- (base10_of_string_aux s') ;; ret (cons Three t) 
        | "4" => t <- (base10_of_string_aux s') ;; ret (cons Four t) 
        | "5" => t <- (base10_of_string_aux s') ;; ret (cons Five t) 
        | "6" => t <- (base10_of_string_aux s') ;; ret (cons Six t) 
        | "7" => t <- (base10_of_string_aux s') ;; ret (cons Seven t) 
        | "8" => t <- (base10_of_string_aux s') ;; ret (cons Eight t) 
        | "9" => t <- (base10_of_string_aux s') ;; ret (cons Nine t) 
        | _ => None (A:=base10)
      end
  end.

Definition base10_of_string (s:string) := l <- (base10_of_string_aux s) ;; ret (rev l).

Definition nat_of_string (s:string) := x <- (base10_of_string s) ;; ret (nat_of_base10 x).

Notation "A || B" := (if A then true else (if B then true else false)).
Notation "A && B" := (if A then (if B then true else false) else false).
Notation "! A" := (if A then false else true) (at level 10).

Definition compose `A B C` (f : B -> C) (g : A -> B) :=
  (fun (x:A) => f (g x)).
Implicit Arguments compose [A B C]. 
Infix "o" := compose (at level 20).

Definition uncurry `A B C` (f : A -> B -> C) (p : A * B) : C.
Proof. 
  firstorder.
Defined.

Fixpoint foldr (A B : Type) (f : A -> B -> B) (zero : B) (l : list A) : B := 
  match l with 
    | nil => zero
    | cons h t => (f h (foldr A B f zero t))
  end.
Implicit Arguments foldr [A B]. 

Fixpoint foldl (A B : Type) (f : A -> B -> B) (zero : B) (l : list A) : B := 
  match l with 
    | nil => zero
    | cons h t => foldl A B f (f h zero) t
  end.
Implicit Arguments foldl [A B]. 

Fixpoint map (A B : Type) (f : A -> B) (l : list A) : list B := 
  match l with 
    | nil => nil 
    | cons h t => cons (f h) (map A B f t)
  end.

Fixpoint assoc (A B :Type) (f : A -> bool) (l : list (A*B)) : option B := 
  match l with 
    | nil => None 
    | cons h t => 
      match h with 
        | (k,v) => 
          if f k 
            then Some v
            else assoc A B f t
      end
  end.
Implicit Arguments assoc [A B]. 

Theorem pair_eq_dec : forall (A B:Type), 
  (forall (a a':A), {a = a'} + {a <> a'}) -> 
  (forall (b b':B), {b = b'} + {b <> b'}) -> 
  (forall (c c':A*B), {c = c'} + {c <> c'}).
Proof.
  decide equality.
Defined.
Implicit Arguments pair_eq_dec [A B].

Fixpoint zip (A B:Type) (l:list A) (l':list B) : option (list (A*B)):= 
  match l, l' with 
    | nil, nil => Some nil
    | cons h t, cons h' t' => 
      match zip A B t t' with
        | None => None 
        | Some a => Some (cons (h,h') a)
      end
    | _,_ => None
  end.

Fixpoint iter (A:Type) (f:A->A) (zero:A) (n:nat) {struct n} : A := 
  match n with 
    | 0 => zero
    | S n' => f (iter A f zero n')
  end.

(* This gives us an `In' predicate that uses decidable equality so is useable for both Type and Set, and not just Prop *)
Definition Member : forall (A : Type) (eq_dec : forall (a b:A), {a = b} + {a <> b}) (a : A) (l : list A), Prop.
  intros A eq_dec.
  refine 
    (fix Member (a : A) (l : list A) {struct l} : Prop :=
      match l with
        | nil => False
        | b :: m => match eq_dec a b with 
                      | left p => True
                      | right p => Member a m
                    end
      end) ; try (right ; clear Member ; auto ; fail).
Defined.
Implicit Arguments Member [A].

Lemma member_imp_in : forall A (x:A) l eq_dec, Member eq_dec x l -> In x l. 
Proof.
  induction l. intros. inversion H. intros. simpl in H. case_eq (eq_dec x a). 
  intros. rewrite e. firstorder.
  intros. rewrite H0 in H. simpl. right. eapply IHl. eauto.  
Defined.

Lemma in_imp_member : forall A (x:A) l eq_dec, In x l -> Member eq_dec x l.
Proof.
  induction l. intros. inversion H. intros. simpl in H. inversion H.
  simpl. case_eq (eq_dec x a). intros. auto. intros. congruence.
  simpl. case_eq (eq_dec x a). intros. auto. intros. 
  apply IHl. auto.
Defined.
 
Require Import List.
Fixpoint Prefix `A` (l:list A) (l':list A) : Prop := 
  match l' with 
    | nil => False 
    | cons h' t' => 
      match l with 
        | nil => True 
        | cons h t => h = h' /\ Prefix A t t'
      end
  end.

Lemma prefix_correct : forall A (a:A) (l:list A) (l':list A), Prefix l l' -> exists l'':list A, l++l''=l'.
Proof.
  induction l. intros. exists l'. auto.
  intros. simpl in H. destruct l'. inversion H.
  inversion H. rewrite H0. apply IHl in H1. inversion H1.
  exists x. rewrite <- H2. auto. 
Defined.   

(* 
Inductive Suffix A (l':list A) : list A -> Prop := 
| suffix_same : forall (a:A) (l:list A), l' = l -> Suffix A l' (cons a l)
| suffix_next : forall (a:A) (l:list A), Suffix A l' l -> Suffix A l' (cons a l).
Implicit Arguments Suffix [A]. 
*)

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

Lemma prefix_smaller : forall A (l:list A) (l':list A), Prefix l l' -> length l < length l'. 
Proof.
  induction l ; destruct l'; firstorder ; simpl ; auto with arith.
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

Lemma suffix_nil : forall A (l:list A) (a:A), Suffix nil (cons a l).
Proof. 
  induction l. simpl. left. auto.
  intros. simpl in *. right. apply IHl. auto.
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

