(** * SfLib: Software Foundations Library *)
(* Version of 4/21/2010 *)

(** Here we collect together several useful definitions and theorems
    from Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not
    already in the Coq standard library.  From now on we can [Import]
    or [Export] this file, instead of cluttering our environment with
    all the examples and false starts in those files. *)

(** * From the Coq standard library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac Case name := Case_aux Case name.
Ltac SCase name := Case_aux SCase name.
Ltac SSCase name := Case_aux SSCase name.
Ltac SSSCase name := Case_aux SSSCase name.
Ltac SSSSCase name := Case_aux SSSSCase name.
Ltac SSSSSCase name := Case_aux SSSSSCase name.
Ltac SSSSSSCase name := Case_aux SSSSSSCase name.
Ltac SSSSSSSCase name := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
(* An exercise in Basics.v *)
Admitted.

(* From Poly.v *)

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).

(** * From Props.v *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** * From Logic.v *)

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof. 
(* An exercise in Logic.v *)
Admitted.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
(* An exercise in Logic.v *)
Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
(* An exercise in Logic.v *)
Admitted.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
(* An exercise in Logic.v *)
Admitted.

Definition relation (X:Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

Inductive refl_step_closure (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | rsc_refl  : forall (x : X),
                 refl_step_closure X R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure X R y z ->
                    refl_step_closure X R x z.
Implicit Arguments refl_step_closure [X]. 

Tactic Notation "rsc_cases" tactic(first) tactic(c) :=
  first;
  [ c "rsc_refl" | c "rsc_step" ].

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y r.
  apply rsc_step with y. apply r. apply rsc_refl.   Qed.

Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  (* FILL IN HERE *) Admitted.


