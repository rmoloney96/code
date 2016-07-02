Require Import OrderedType.
Require Import Ascii.
Require Import Omega. 
Require Import Peano.
Require Import Bool.

Inductive eq_ascii : ascii -> ascii -> Prop := 
| ascii_eq : forall (a b:ascii), 
  (nat_of_ascii a) = (nat_of_ascii b) -> eq_ascii a b.

Hint Constructors eq_ascii.

Lemma bit_significant_r : forall n m, 2*n+1 <> 2*m+0.
Proof. 
  intros n m. omega.
Defined.

Lemma bit_significant_l : forall n m, 2*n+0 <> 2*m+1.
Proof. 
  intros n m. omega.
Defined.

Lemma bit_reg_l : forall n m, 2*n = 2*m -> n = m.
Proof. 
  intros n m. omega.
Defined.

Lemma plus_reg_r : forall n m p, n + p = m + p -> n = m.
  intros. omega.
Defined.  

Ltac simplify_nat := 
  match goal with 
    | H: 2*?m + ?p = 2*?n + ?p |- _ => eapply plus_reg_r in H ; simplify_nat
    | H: 2*?m = 2*?n |- _ => eapply bit_reg_l in H ; simplify_nat
    | H: 2*?m + 0 = 2*?n + 1 |- _ => eapply bit_significant_l in H ; simplify_nat
    | H: 2*?m + 1 = 2*?n + 0 |- _ => eapply bit_significant_r in H ; simplify_nat
    | H: False |- _ => inversion H
    | H: true <> true |- _ => congruence
    | H: false <> false |- _ => congruence
    | H: true = false |- _ => congruence
    | H: false = true |- _ => congruence
    | H: ?b <> ?b', b : bool, b' : bool |- _ => destruct b ; destruct b' ; simplify_nat
    | _ : _ |- _ => idtac
  end.

Theorem eq_ascii_eq : forall a b, eq_ascii a b -> a = b.
Proof.
  intros a b. 
  destruct a as [b1 b2 b3 b4 b5 b6 b7 b8].
  destruct b as [b1' b2' b3' b4' b5' b6' b7' b8'].
  intros H ; inversion H ; clear H ; subst ; unfold nat_of_ascii in *. 
  (* bit 1 *)
  case (bool_dec b1 b1') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b2 b2') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b3 b3') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b4 b4') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b5 b5') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b6 b6') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b7 b7') ; intro H' ; subst ; simplify_nat.
  case (bool_dec b8 b8') ; intro H' ; subst ; auto.  
  destruct b8 ; destruct b8' ; auto ; congruence.
Qed.

Module AsciiOrdered <: OrderedType.
  
  Definition t := ascii. 
 
  Inductive lt_ascii : ascii -> ascii -> Prop := 
  | ascii_lt : forall (a b:ascii), 
    (nat_of_ascii a) < (nat_of_ascii b) -> lt_ascii a b.

  Hint Constructors lt_ascii.

  Definition eq := eq_ascii.
  Definition lt := lt_ascii.

  Hint Unfold eq lt.

  Theorem eq_refl : forall x: t, eq x x.
  Proof. 
    auto.
  Qed.
  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros x y H. inversion H. auto. 
  Qed.
  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z H1 H2. inversion H1 ; inversion H2. subst. apply ascii_eq. 
    rewrite H. auto.
  Qed.

  Require Import Omega.
  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z H1 H2. inversion H1 ; inversion H2. 
    apply ascii_lt. omega.
  Qed.
  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H1. unfold not. intros H2. 
    inversion H1 ; inversion H2. rewrite <- H5 in H. 
    subst. omega.
  Qed.
  
  Lemma lt_eq_lt_dec_imp : forall (a b : ascii) (n m : nat),  
    n = (nat_of_ascii a) -> m = (nat_of_ascii b) -> 
    {n < m} + {n = m} + {m < n} -> 
    {lt a b} + {eq a b} + {lt b a}.
  Proof.
    intros a b n m p1 p2 Hdec. 
    inversion Hdec. inversion H.
    (* lt a b *)
    cut ((nat_of_ascii a) < (nat_of_ascii b)).
    intros Hc. left ; left ; auto. omega.
    (* eq a b *) 
    cut ((nat_of_ascii a) = (nat_of_ascii b)).
    intros Hc. left ; right ; auto. subst ; auto.
    (* lt b a *) 
    cut ((nat_of_ascii b) < (nat_of_ascii a)).
    intros Hc. right ; auto. subst ; auto.   
  Qed.

  Lemma lt_eq_lt_dec (a b : ascii) : {lt a b} + {eq a b} + {lt b a}.
  Proof.
    intros a b. 
    set (an := (nat_of_ascii a)).
    set (bn := (nat_of_ascii b)).
    eapply (lt_eq_lt_dec_imp a b an bn). auto. auto.
    apply lt_eq_lt_dec.
  Qed.

  Theorem compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y. case (lt_eq_lt_dec x y).
    intros. induction s. 
    (* lt x y *) 
    apply LT. auto.
    (* eq x y *) 
    apply EQ. auto.
    (* lt y x *)
    apply GT. 
  Qed.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

End AsciiOrdered.

Require Import String.

Inductive string_eq : string -> string -> Prop := 
| string_eq_base : string_eq EmptyString EmptyString
| string_eq_next : forall (a b: ascii) (s1 s2 : string), 
  AsciiOrdered.eq a b -> string_eq s1 s2 -> string_eq (String a s1) (String b s2).

Hint Constructors string_eq.

Theorem eq_string_eq : forall (s s':string), string_eq s s' -> s = s'.
Proof. 
  intros s ; induction s ; intros s' ; destruct s' ; intro H ; auto ; inversion H ; subst.  
  apply eq_ascii_eq in H3. rewrite H3. cut (s = s') ; intros ; subst ; auto.
Defined.

Hint Resolve eq_string_eq. 
 
Module StringOrder <: OrderedType.

  Definition t := string.

  Inductive string_lt : string -> string -> Prop := 
  | string_lt_smaller : forall (a : ascii) (s : string), 
    string_lt EmptyString (String a s)
  | string_lt_base : forall (a b: ascii) (s1 s2: string), 
    AsciiOrdered.lt a b -> string_lt (String a s1) (String b s2)
  | string_lt_next : forall (a b: ascii) (s1 s2: string), 
    AsciiOrdered.eq a b -> string_lt s1 s2 -> string_lt (String a s1) (String b s2).

  Hint Constructors string_lt.

  Definition eq := string_eq.
  Definition lt := string_lt.

  Hint Unfold eq lt.

  Theorem eq_refl : forall x : t, eq x x.
  Proof.
    intros x. induction x ; auto.
  Qed.
  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    induction 1 ; auto.
  Qed.
  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    induction x. intros y z H H0. 
    (* case 1 *)
    inversion H. subst. inversion H0. subst. auto.
    (* case 2 *)
    intros. destruct z. inversion H0. subst. inversion H.
    (* case 3 *) 
    inversion H0. subst. inversion H. subst. 
    apply string_eq_next. inversion H4. subst. inversion H6. subst. 
    rewrite H1 in H2. auto. eapply IHx. eauto. eauto. 
  Qed.

  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    induction x ; intros y z H H0.
    (* case 1 *)
    destruct y. inversion H. inversion H. 
    subst. inversion H0. subst. auto. auto. 

    (* case 2 *)
    inversion H ; subst ; inversion H0 ; subst.
    (* subcase 1 *)
    apply string_lt_base. apply (AsciiOrdered.lt_trans a b b0) in H4 ; auto. 
    (* subcase 2 *)
    inversion H ; subst. inversion H3. subst. inversion H2. subst. rewrite H1 in H5.
    auto. inversion H3. inversion H7. subst. rewrite H1 in H8. 
    apply string_lt_next. auto. eapply IHx. eauto. auto.
    (* subcase 3 *)
    apply string_lt_base. inversion H3. subst. inversion H6. subst. rewrite <- H1 in H2.
    auto.
    (* subcase 4 *)
    intros. inversion H3. inversion H4. subst. rewrite <- H1 in H8. 
    apply string_lt_next. auto. eapply IHx. eauto. eauto.
  Qed.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. 
    induction x ; destruct y; unfold not ; intros.
    inversion H. inversion H0. inversion H.
    inversion H0. subst. inversion H. subst. inversion H4. inversion H2. omega.
    subst. inversion H0. subst. eapply IHx. eauto. auto.
  Qed.

  Lemma lt_eq_lt_dec : forall a b, {lt a b} + {eq a b} + {lt b a}.
  Proof.
    refine 
      (fix f (a : string) (b : string) {struct a} : {lt a b} + {eq a b} + {lt b a} :=
        match a return {lt a b} + {eq a b} + {lt b a} with 
          | EmptyString => match b return {lt "" b} + {eq "" b} + {lt b ""} with 
                             | EmptyString => _
                             | String cb sb => _ 
                           end
          | String ca sa => match b return {lt (String ca sa) b} + {eq (String ca sa) b} + {lt b (String ca sa)} with 
                              | EmptyString => _ 
                              | String cb sb => 
                                match (AsciiOrdered.lt_eq_lt_dec ca cb) with 
                                  | inleft pl =>
                                    match pl with 
                                      | left pll => _
                                      | right plr => match (f sa sb) with 
                                                       | inleft fpl => 
                                                         match fpl with 
                                                           | left fpll => _ 
                                                           | right fpll => _
                                                         end
                                                       | inright fpr => _
                                                     end
                                    end
                                  | inright pr => _
                                end
                            end
        end) ; clear f ; auto.
  Qed.

  Theorem compare : forall x y : t, Compare lt eq x y.
  Proof. 
    intros x y. case (lt_eq_lt_dec x y).
    intros. induction s. 
    (* lt x y *) 
    apply LT. auto.
    (* eq x y *) 
    apply EQ. auto.
    (* lt y x *)
    apply GT. 
  Defined.

End StringOrder.

