(*  implement these *) 
Require Import Ascii.
Require Import MyUtils.
Require Import Arith.
(* Require Import Coq.Arith.Bool_nat. *)
Open Scope char_scope.

Notation "# C" := (nat_of_ascii C) (at level 5).

Definition tab := ascii_of_nat 9.
Definition linefeed := ascii_of_nat 10.
Definition carriage_return := ascii_of_nat 13.
Definition space := ascii_of_nat 32.

Definition isUpper (c:ascii) :bool := 
  (le_lt_dec #"A" #c) && (le_lt_dec #c #"Z").

Definition isLower (c:ascii) :bool := 
  (le_lt_dec #"a" #c) && (le_lt_dec #c #"z").

Definition isDigit (c:ascii) :bool := 
  (le_lt_dec #"0" #c) && (le_lt_dec #c #"9").

Definition isAlpha (c:ascii) :bool := 
  (isUpper c) || (isLower c).

Definition isAlphaNum (c:ascii) :bool := 
  (isAlpha c) || (isDigit c).

Definition isHexDigit (c:ascii) :bool := 
  (isDigit c) || 
    ((le_lt_dec #"a" #c) && (le_lt_dec #c #"f") 
      || (le_lt_dec #"A" #c) && (le_lt_dec #c #"F")).

Definition isGraph (c:ascii) :bool :=
  (le_lt_dec #"!" #c) && (le_lt_dec #c #"~").

Definition isPrint (c:ascii) :bool := 
  (isGraph c) || (eq_nat_dec #c #" ").

Definition isPunct (c:ascii) :bool := 
  (isGraph c) && (! (isAlphaNum c)).

Definition isCtrl (c:ascii) :bool := 
  ! (isPrint c).

Definition isSpace (c:ascii) :bool := 
  ((le_lt_dec #tab #c) && (le_lt_dec #c #carriage_return)
    || (le_lt_dec #c #" ")).

Definition isNewline (c:ascii) : bool := 
  if (eq_nat_dec #c #carriage_return) then true else false.

Definition toLower (c:ascii) :ascii := 
  if isUpper c
    then (ascii_of_nat (#c + 32))
    else c.

Definition toUpper (c:ascii) :ascii := 
  if isLower c
    then (ascii_of_nat (#c - 32))
    else c.

Lemma lower_imp_alpha : forall (c:ascii), isLower c = true -> isAlpha c = true.
Proof. 
  intros c H; unfold isAlpha ; rewrite H ; destruct isUpper ; auto.
Defined.  

Lemma lower_imp_alphanum : forall (c:ascii), isLower c = true -> isAlphaNum c = true. 
Proof. 
  intros c H; unfold isAlphaNum; apply lower_imp_alpha in H; rewrite H; auto.
Defined.

Lemma upper_imp_alpha : forall (c:ascii), isUpper c = true -> isAlpha c = true.
Proof. 
  intros c H; unfold isAlpha ; rewrite H ; destruct isLower ; auto.
Defined.

Lemma upper_imp_alphanum : forall (c:ascii), isUpper c = true -> isAlphaNum c = true.
Proof.
  intros c H; unfold isAlphaNum; apply upper_imp_alpha in H; rewrite H; auto.
Defined.  
