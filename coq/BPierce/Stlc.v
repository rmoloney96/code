(** * Stlc: The Simply Typed Lambda-Calculus *)
(* Version of 4/26/2010 *)



Require Export Smallstep.
Require Import Relations.

(* ###################################################################### *)
(** * More Automation *)

(** Time to take the gloves off... *)

(* ###################################################################### *)
(** ** The [auto] and [eauto] Tactics *)

(** The [auto] tactic solves goals that are solvable by any combination of 
     - [intros]
     - [apply] (with a local hypothesis, by default)
     - [reflexivity]
       
    The [eauto] tactic works just like [auto], except that it uses
    [eapply] instead of [apply]. *)

(** Using [auto] is always "safe" in the sense that it will never fail
    and will never change the proof state: either it completely solves
    the current goal, or it does nothing.

    Here is a contrived example: *)

Lemma auto_example_1 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof.
 auto.  Qed.

(** By default, [auto] and [eauto] consider just the hypotheses in the
    current context.  But we can also give a list of lemmas and
    constructors to consider in addition to these, by writing [auto
    using ...]. *)

Lemma auto_example_2 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto using conj, or_introl, or_intror.  Qed.

(** There are some constructors and lemmas that are applied very often
    in proofs.  We can tell [auto] to _always_ consider these, instead
    of mentioning them explicitly each time.  This is accomplished by
    writing
[[
      Hint Resolve l.
]]
    at the top level, where [l] is a top-level lemma theorem or a
    constructor of an inductively defined proposition (i.e., anything
    whose type is an implication).  As a shorthand, we can write
[[
      Hint Constructors c.
]]
    to tell Coq to add _all_ of the constructors from the inductive
    definition of [c] to the database used by [auto].

    It is also sometimes necessary to add
[[
      Hint Unfold d.
]]
    where [d] is a defined symbol, so that [auto] knows to expand
    uses of [d] and enable further possibilities for applying
    lemmas that it knows about.  *)

(** Here are some [Hint]s we will find useful.  There is an example of
    the effect of the [and] and [or] hints below. *)
Hint Constructors and.
Hint Constructors or.

Hint Constructors refl_step_closure.
Hint Resolve beq_id_eq beq_id_false_not_eq.

Lemma auto_example_3 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto.  Qed.

(** Warning: Just as with Coq's other automation facilities, it is
    easy to overuse [auto] and [eauto] and wind up with proofs that
    are impossible to understand later! 

    Also, overuse of [eauto] can make proof scripts very slow.  Get in
    the habit of using [auto] most of the time and [eauto] more
    sparingly. *)

(* ###################################################################### *)
(** ** The [Proof with] Tactic *)

(** If you start a proof with [Proof with (tactic)] then writing [...]
     instead of [.] after a tactic in the body of the proof will try
     to solve all generated subgoals with [tactic] (and fail if this
     doesn't work).

     One common use of this facility is "[Proof with auto]" (or
     [eauto]).  We'll see many examples of this later in the file. *)

(* ###################################################################### *)
(** ** The [solve by inversion] Tactic *)

(** Here's another nice automation feature: it often arises that the
    context contains a contradictory assumption and we want to use
    [inversion] on it to solve the goal.  We'd like to be able to say
    to Coq, "find a contradictory assumption and invert it" without
    giving its name explicitly.

    Unfortunately, Coq does not provide a built-in tactic that does
    this.  However, it is not too hard to define one
    ourselves.  (Thanks to Aaron Bohannon for this nice hack.) *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(** Again, the details of how the [Tactic Notation] definition works
    are not important.  All we need to know is that doing [solve by
    inversion] will find a hypothesis that can be inverted to solve
    the goal, if there is one.  The tactics [solve by inversion 2] and
    [solve by inversion 3] are slightly fancier versions which will
    perform two or three inversions in a row, if necessary, to solve
    the goal. *)

(* ###################################################################### *)
(** ** The [try solve] Tactic *)

(** If [t] is a tactic, then [try solve [t]] is a tactic that
      - if [t] solves the goal, behaves just like [t], or
      - if [t] cannot completely solve the goal, does
        nothing.

    More generally, [try solve [t1 | t2 | ...]] will try to solve the
    goal by using [t1], [t2], etc.  If none of them succeeds in
    completely solving the goal, then [try solve [t1 | t2 | ...]] does
    nothing.

    The fact that it does nothing when it doesn't completely succeed
    in solving the goal means that there is no harm in using [try
    solve T] in situations where [T] might actually make no sense.  In
    particular, if we put it after a [;] it will solve as many
    subgoals as it can and leave the rest for us to solve by other
    methods.  It will _not_ leave any of the subgoals in a mangled
    state. *)

(* ###################################################################### *)
(** ** The [normalize] Tactic *)

(** When experimenting when the languages defined in this file, we
    will sometimes want to see what a particular concrete term steps
    to, so we want to solve goals of the form [ t -->* t' ] where
    [t] is a completely concrete term.  These proofs are simple but
    repetitive. Consider for example reducing an arithmetic expression
    using the small-step relation [astep] defined in the previous
    chapter: *)

Definition astep_many st := refl_step_closure (astep st).
Notation " t '/' st '-->a*' t' " := (astep_many st t t')
  (at level 40, st at level 39).

Example astep_example1 : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state -->a* (ANum 15).
Proof.
  apply rsc_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2. 
      apply av_num. 
      apply AS_Mult.
  apply rsc_step with (ANum 15).
    apply AS_Plus.
  apply rsc_refl.
Qed.

(** We repeatedly applied [rsc_step] until we got to a normal form. The proofs that 
    the intermediate steps are possible are simple enough that [auto], with
    appropriate hints, can solve them. *)

Hint Constructors astep aval.
Example astep_example1' : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state -->a* (ANum 15).
Proof.
  eapply rsc_step. auto. simpl.
  eapply rsc_step. auto. simpl.
  apply rsc_refl.
Qed.

(** The following custom Ltac captures this pattern.  In addition,
    before each rsc_step we print out the current goal, so that the
    user can follow how the term is being evaluated. *)

Ltac print_goal := match goal with |- ?x => idtac x end.

Ltac normalize := 
   repeat (print_goal; eapply rsc_step ; [ (eauto 10; fail) | (instantiate; simpl)]);
   apply rsc_refl.

Example astep_example1'' : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state -->a* (ANum 15).
Proof.
  normalize.
  (* At this point in the proof script, the Coq response shows 
     a trace of how the expression evaluated. *)
Qed.

(** Finally, this is also useful as a simple way to calculate what the normal
    form of a term is, by proving a goal with an existential variable in it. *)
Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state -->a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

(* ###################################################################### *)
(** * Typed Arithmetic Expressions
 *)

(** To motivate the discussion of types, let's begin with an extremely
    simple language of arithmetic and boolean expressions -- a
    language just barely complex enough to have the possibility of
    programs "going wrong" because of runtime type errors. *)

(* ###################################################################### *)
(** ** Syntax *)

Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_iszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue tm_true
  | bv_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tm_zero
  | nv_succ : forall t, nvalue t -> nvalue (tm_succ t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.  

(* ###################################################################### *)
(** ** Small-step reduction *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) --> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (tm_if t1 t2 t3) --> (tm_if t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      (tm_succ t1) --> (tm_succ t1')
  | ST_PredZero :
      (tm_pred tm_zero) --> tm_zero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tm_pred (tm_succ t1)) --> t1
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      (tm_pred t1) --> (tm_pred t1')
  | ST_IszeroZero :
      (tm_iszero tm_zero) --> tm_true
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tm_iszero (tm_succ t1)) --> tm_false
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      (tm_iszero t1) --> (tm_iszero t1')

where "t1 '-->' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) tactic(c) :=
  first;
  [ c "ST_IfTrue" | c "ST_IfFalse" | c "ST_If" 
  | c "ST_Succ" | c "ST_PredZero" | c "ST_PredSucc" | c "ST_Pred" 
  | c "ST_IszeroZero" | c "ST_IszeroSucc" | c "ST_Iszero" ].

Hint Constructors step.

(** Notice that the [step] relation doesn't care at all about whether
    expressions make sense or not.  For example, it is easy to see
    that
[[
    tm_succ (tm_if tm_true tm_true tm_true)
]]
    is nonsensical, but the [step] relation will happily reduce it one
    step to
[[
    tm_succ tm_true.
]]
*)

(* ###################################################################### *)
(** ** Normal Forms and Values *)

(** The first interesting thing about the [step] relation is that the
    progress theorem as we stated it before fails!  That is, there are
    terms that are normal forms (they can't take a step) but not
    values -- i.e., we have not included them in our definition of
    possible "results of evaluation."  Such terms are said to be
    stuck. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** Exercise: 2 stars, optional (some_tm_is_stuck) *)
Example some_tm_is_stuck :
  exists t, stuck t.
Proof.
  intros. exists (tm_succ tm_true). 
  unfold stuck. split. unfold normal_form.
  unfold not. intros.
  inversion H. inversion H0. inversion H2.
  unfold not. intros.
  inversion H. inversion H0. inversion H0. subst. inversion H2.
Defined.
(** [] *)

(** Fortunately, things are not _completely_ messed up: values and
    normal forms are not the same in this language, but at least the
    former set is included in the latter (i.e., we did not
    accidentally define things so that some value could still take a
    step). *)

(** **** Exercise: 3 stars, optional (value_is_nf) *)
(** Hint: You will reach a point in this proof where you need to use
    an induction to reason about a term that is known to be a numeric
    value.  This induction can be performed either over the term
    itself or over the evidence that it is a numeric value.  The proof
    goes through in either case, but you will find that one way is
    quite a bit shorter than the other.  For the sake of the exercise,
    try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  partial_function step.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Typing *)

(** Critical observation: although there are stuck terms in this
    language, they are all "nonsensical", mixing booleans and numbers
    in a way that we don't even _want_ to have a meaning.  We can
    easily exclude such ill-typed terms by defining a "typing
    relation" that relates terms to the types (either numeric or
    boolean) of their final results.  *)

Inductive ty : Type := 
  | ty_bool : ty
  | ty_nat : ty.

(** The typing relation *)

(** In informal notation, the typing relation is often written [|- t :
    T], pronounced "[t] has type [T]."
[[[
                            --------------                             (T_True)
                            |- true : Bool

                           ---------------                            (T_False)
                           |- false : Bool

                |- t1 : Bool    |- t2 : T    |- t3 : T
                --------------------------------------                   (T_If)
                     |- if t1 then t2 else t3 : T

                              ----------                               (T_Zero)
                              |- 0 : Nat

                              
                             |- t1 : Nat
                           ----------------                            (T_Succ)
                           |- succ t1 : Not

                             |- t1 : Nat
                           ----------------                            (T_Pred)
                           |- pred t1 : Not

                             |- t1 : Nat
                         -------------------                         (T_IsZero)
                         |- iszero t1 : Bool
]]]
*)

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       has_type tm_true ty_bool
  | T_False : 
       has_type tm_false ty_bool
  | T_If : forall t1 t2 t3 T,
       has_type t1 ty_bool ->
       has_type t2 T ->
       has_type t3 T ->
       has_type (tm_if t1 t2 t3) T
  | T_Zero : 
       has_type tm_zero ty_nat
  | T_Succ : forall t1,
       has_type t1 ty_nat ->
       has_type (tm_succ t1) ty_nat
  | T_Pred : forall t1,
       has_type t1 ty_nat ->
       has_type (tm_pred t1) ty_nat
  | T_Iszero : forall t1,
       has_type t1 ty_nat ->
       has_type (tm_iszero t1) ty_bool.


Tactic Notation "has_type_cases" tactic(first) tactic(c) :=
  first;
  [ c "T_True" | c "T_False" | c "T_If" | c "T_Zero" | c "T_Succ" 
  | c "T_Pred" | c "T_Iszero" ].

Hint Constructors has_type.

(* ###################################################################### *)
(** *** Examples *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not calculate
    the type of the normal form of a term. *)

Example has_type_1 : 
  has_type (tm_if tm_false tm_zero (tm_succ tm_zero)) ty_nat.
Proof.
  apply T_If. 
    apply T_False.
    apply T_Zero.
    apply T_Succ.
      apply T_Zero.  Qed.

Example has_type_not : 
  ~ has_type (tm_if tm_false tm_zero tm_true) ty_bool.
Proof.
  intros Contra. solve by inversion 2.  Qed.

(** **** Exercise: 1 star *)
Example succ_hastype_nat__hastype_nat : forall t,
  has_type (tm_succ t) ty_nat ->
  has_type t ty_nat.  
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values. *)

(** **** Exercise: 2 stars (finish_progress) *)
Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T HT.
  has_type_cases (induction HT) (Case)...
  (* the cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  Case "T_If".
    right. destruct IHHT1.
    SCase "t1 is a value". destruct H.
      SSCase "t1 is a bvalue". destruct H.
        SSSCase "t1 is tm_true". 
          exists t2...
        SSSCase "t1 is tm_false". 
          exists t3...
      SSCase "t1 is an nvalue".
        solve by inversion 2.  (* on H and HT1 *)
    SCase "t1 can take a step".
      destruct H as [t1' H1].
      exists (tm_if t1' t2 t3)...
  (* FILL IN HERE *) Admitted.
(** [] *)

(** This is a bit more interesting than the progress theorem that we
    saw in Smallstep.v, where _all_ normal forms were values.  Here, a
    term can be stuck, but only if it is ill typed. *)

(** **** Exercise: 1 star (step_review) *)
(** Quick review.  Answer _true_ or _false_.  (As usual, no need to
    hand these in.)
      - In this language, every well-typed normal form is a value.

      - Every value is a normal form.

      - The single-step evaluation relation is
        a partial function.

      - The single-step evaluation relation is a TOTAL function.

*)
(** [] *)

(* ###################################################################### *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term.

    This theorem is also sometimes called the _subject reduction_
    property, because it tells us what happens when the "subject" of
    the typing relation is reduced. *)

(** **** Exercise: 2 stars (finish_preservation) *)
Theorem preservation : forall t t' T,
  has_type t T ->
  t --> t' ->
  has_type t' T.
Proof with eauto.
  intros t t' T HT HE.
  generalize dependent t'.
  (has_type_cases (induction HT) (Case)); 
         (* every case needs to introduce a couple of things *)
         intros t' HE; 
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (preservation_alternate_proof) *)
(** Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proof to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  has_type t T ->
  t --> t' ->
  has_type t' T.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we can see that a
    well-typed term can _never_ reach a stuck state.  *)

Definition stepmany := (refl_step_closure step).
Notation "t1 '-->*' t2" := (stepmany t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  has_type t T -> 
  t -->* t' ->
  ~(stuck t').
Proof. 
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.   
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.

(** Indeed, in the present -- extremely simple -- language,
    every well-typed term can be reduced to a normal form: this is the
    normalization property.  In richer languages, this property often
    fails, though there are some interesting languages (such as Coq's
    [Fixpoint] language, and the simply typed lambda-calculus, which
    we'll be looking at next) where all _well-typed_ terms can be
    reduced to normal forms. *)

(* ###################################################################### *)
(** ** Additional exercises *)

(** **** Exercise: 2 stars (subject_expansion) *)
(** Having seen the subject reduction property, it is reasonable
    to wonder whether the opposity property -- subject
    EXPANSION -- also holds.  That is, is it always the case
    that, if [t --> t'] and [has_type t' T], then [has_type t T]?
    If so, prove it.  If not, give a counter-example.

    (* FILL IN HERE *)
[]
*)

(** **** Exercise: 2 stars (variation1) *)
(** Suppose we add the following two new rules to the evaluation
    relation:
[[
      | ST_PredTrue : 
           (tm_pred tm_true) --> (tm_pred tm_false)
      | ST_PredFalse : 
           (tm_pred tm_false) --> (tm_pred tm_true)
]]
   Which of the following properties remain true in the presence
   of these rules?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinacy of [step]

      - Normalization of [step] for well-typed terms

      - Progress

      - Preservation

[]
*)

(** **** Exercise: 2 stars (variation2) *)
(** Suppose, instead, that we add this new rule to the typing relation: 
[[
      | T_IfFunny : forall t2 t3,
           has_type t2 ty_nat ->
           has_type (tm_if tm_true t2 t3) ty_nat
]]
   Which of the following properties remain true in the presence of
   this rule?  (Answer in the same style as above.)
      - Determinacy of [step]

      - Normalization of [step] for well-typed terms

      - Progress

      - Preservation

[]
*)

(** **** Exercise: 2 stars (variation3) *)
(** Suppose, instead, that we add this new rule to the typing relation: 
[[
      | T_SuccBool : forall t,
           has_type t ty_bool ->
           has_type (tm_succ t) ty_bool
]]
   Which of the following properties remain true in the presence of
   this rule?  (Answer in the same style as above.)
      - Determinacy of [step]

      - Normalization of [step] for well-typed terms

      - Progress

      - Preservation

[]
*)

(** **** Exercise: 2 stars (variation4) *)
(** Suppose, instead, that we add this new rule to the [step] relation: 
[[
      | ST_Funny1 : forall t2 t3,
           (tm_if tm_true t2 t3) --> t3
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 2 stars (variation5) *)
(** Suppose instead that we add this rule:
[[
      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (tm_if t1 t2 t3) --> (tm_if t1 t2' t3)
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 2 stars (variation6) *)
(** Suppose instead that we add this rule:
[[
      | ST_Funny3 : 
          (tm_pred tm_false) --> (tm_pred (tm_pred tm_false))
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 2 stars (variation7) *)
(** Suppose instead that we add this rule:
   [[
      | T_Funny4 : 
            has_type tm_zero ty_bool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 2 stars (variation8) *)
(** Suppose instead that we add this rule:
   [[
      | T_Funny5 : 
            has_type (tm_pred tm_zero) ty_bool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 3 stars, optional (more_variations) *)
(** Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
    [] 
*)

(** **** Exercise: 1 star (remove_predzero) *)
(** The evaluation rule [E_PredZero] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of
    zero to be undefined, rather than being defined to be zero.
    Can we achieve this simply by removing the rule from the
    definition of [step]?

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (prog_pres_bigstep) *)
(** Suppose our evaluation relation is defined in the big-step
    style.  What are the appropriate analogs of the progress and
    preservation properties?

(* FILL IN HERE *)
[]
*)

(* ###################################################################### *)
(** * The Simply Typed Lambda-Calculus *)

(** The simply typed lambda-calculus (STLC) can be described as the
    simplest possible functional programming language -- it contains
    anonymous functions, application, variables, and nothing else.

    Since it is essentially a small fragment of Coq's built-in
    functional language, we could informally use the same
    notation for programs.  For example,
[[
          fun x:A => x
]]
    is the identity function at the type [A], and
[[
          fun x:A => fun y:B => x
]]
    is a function that takes an argument of type [A], throws it
    away, and returns the constant-[x] function (of type [B->A]).

    However, this "[fun ... => ...]" notation is a little heavy,
    especially for writing on the blackboard.  So when we discuss
    terms informally, we'll use another common way of writing function
    abstractions in this language: [\x:A.x], where [\] stands for the
    greek letter "lambda".  

    
    To keep things simple, we'll start with the _pure_ simply typed
    lambda-calculus, where base types like [A], [B], etc. are
    completely uninterpreted -- i.e., there are no constants belonging
    to base types and no primitive operations over base types.  At the
    end of the chapter, we'll see how to extend the pure system to
    something closer to a real programming language by adding base
    types like numbers.

    The main new technical issues that we'll have to face in this
    section are dealing with _variable binding_ and _substitution_.

    - We've already seen how to formalize a language with
      variables (Imp).  There, however, the variables were all global.
      In STLC, we need to handle _bound_ variables because of function
      parameters.

    - Moreover, instead of just looking up global variables in
      the store, we'll need to reduce function applications by
      substituting arguments for parameters in function
      bodies.
*)

(* ###################################################################### *)
(** ** Syntax and Operational Semantics *)

Module STLC.

(* ################################### *)
(** *** Types *)

(** The function types of the STLC are just like the function types of
    Coq.  We begin with a collection of base types, which we write
    [A], [B], etc., in informal examples (formally, they are
    designated by the constructor [ty_base] together with an [id]).
    Then, for every pair of types [T1] and [T2], we construct the
    arrow type [T1->T2] (formally, [ty_arrow T1 T2]). *)

Inductive ty : Type := 
  | ty_base  : id -> ty 
  | ty_arrow : ty -> ty -> ty.

(** Some base types for use in examples... *)

Notation A := (ty_base (Id 0)).
Notation B := (ty_base (Id 1)).
Notation C := (ty_base (Id 2)).

(* ################################### *)
(** *** Terms *)

(** The terms of the STLC are just variables, function application,
    and function abstraction.  We use identifiers as variable
    names. *)

Inductive tm : Type :=
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm.

(** One important thing to note here is that an abstraction
    [\x:T.t] (formally, [tm_abs x T t]) is always annotated with the
    type ([T]) of its parameter.  This is in contrast to Coq (and
    other functional languages like ML, Haskell, etc.), where we can
    write either
[[
      fun x : A => t
]]
    or
[[
      fun x => t
]]
    and trust Coq to fill in an appropriate annotation in the latter
    case.
*)

Tactic Notation "tm_cases" tactic(first) tactic(c) :=
  first;
  [ c "tm_var" | c "tm_app" | c "tm_abs" ].

(** Some variables for examples... *)

Notation a := (Id 0).
Notation b := (Id 1).
Notation c := (Id 2).

(** Some identity functions on various types... *)

(**   [id_A = \a:A. a] *)

Notation id_A := 
  (tm_abs a A (tm_var a)).

(**   [id_AarrowA = \a:A->A. a] *)

Notation id_AarrowA := 
  (tm_abs a (ty_arrow A A) (tm_var a)).

(**   [id_AarrowA_arrow_AarrowA = \a:(A->A)->(A->A). a] *)

Notation id_AarrowA_arrow_AarrowA :=
  (tm_abs a (ty_arrow (ty_arrow A A) (ty_arrow A A)) (tm_var a)).

(** A function that takes an [A] and returns a constant function
    of type [B->A]: *)

(**   [k = \a:A. \b:B. a] *)

Notation k := (tm_abs a A (tm_abs b B (tm_var a))).

(** (We make these Notations rather than Definitions to make things
    easier for [auto].) *)

(* ################################### *)
(** *** Values *)

(** When we come to defining the values of the STLC, we have to
    think a little.

    First, an application is clearly _not_ a value: It represents a
    function being invoked on some argument, and the term cannot be
    finished computing till this invocation has actually happened.

    For abstractions, on the other hand, we have a choice:

      - We can say that [\a:A.t] is a value only if [t] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what
        argument it is going to be applied to).

      - Or we can say that [\a:A.t] is always a value, no matter
        whether [t] is one or not -- in other words, we can say
        that reduction stops at abstractions.  

    Coq makes the first choice -- for example,
[[
         Eval simpl in (fun a:bool => plus 3 4)
]]
    yields [fun a:bool => 7].  But most real functional
    programming languages make the second choice -- reduction of
    a function's body only begins when the function is actually
    applied to an argument.  We also make the latter choice here.

    Having decided this, we don't need to worry about whether
    variables are values, since we'll always be reducing programs
    "from the outside in," and that means the [step] relation
    will always be working with closed terms (ones with no free
    variables).  *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tm_abs x T t).

Hint Constructors value.

(* ################################### *)
(** *** Substitution *)

(** Now we come to the most interesting part of the definition:
    the operation of substituting one term for the free
    occurrences of some variable in another term.  This operation
    will be used in a moment to define the operational semantics
    of function application, where we will need to substitute the
    argument term for the function parameter in the function's
    body.
    
    Informally, substitution is often written [[s/x]t],
    pronounced "substitute [s] for [x] in [t]".

    For example:
[[
      [(\b:A.b)/a]a = \b:A.b

      [(\b:A.b)/a]c = c
      
      [(\b:A.b)/a](\c:B. a) = \c:B. \b:A.b

      [(\b:A.b)/a](\c:(A->A)->(A->A). c a) 
        = \c:(A->A)->(A->A). c (\b:A.b)

      [(\b:A.b)/a](\a:B.a) = \a:B.a

      [(\b:(B->B)->(B->B).b)/a](a (\a:B.a)) 
        = (\b:(B->B)->(B->B).b) (\a:B.a)
]]
    Note that, in the last two examples, we do _not_ substitute
    for the [a] in the body of an abstraction whose bound
    variable is named [a].

    Here is the formal definition:*)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tm_var x' => if beq_id x x' then s else t
  | tm_abs x' T t1 => tm_abs x' T (if beq_id x x' then t1 else (subst x s t1)) 
  | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
  end.

(** Technical note: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted in, may
    itself contain free variables.  Since we are only interested in
    defining the [step] relation on closed terms here, we can avoid
    this extra complexity. *)

(* ################################### *)
(** *** Reduction *)

(** The small-step reduction relation for STLC follows the same
    pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side until it becomes a literal function; then we reduce its
    right-hand side (the argument) until it is also a value; and
    finally we substitute the argument for the bound variable in
    the body of the function.  This last rule, written informally
    as
[[
      (\a:T.t12) v2 --> [v2/a]t12
]]
    is traditionally called "beta-reduction".

    Informally: 
[[[
                               value v2
                     ---------------------------                    (ST_AppAbs)
                     (\a:T.t12) v2 --> [v2/a]t12

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                       value v1     t2 --> t2'
                       -----------------------                        (ST_App2)
                           v1 t2 --> v1 t2'
]]]
Formally:
*)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tm_app (tm_abs x T t12) v2) --> (subst x v2 t12)
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         tm_app v1 t2 --> tm_app v1  t2'

where "t1 '-->' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) tactic(c) :=
  first;
  [ c "ST_AppAbs" | c "ST_App1" | c "ST_App2" ].

Notation stepmany := (refl_step_closure step).
Notation "t1 '-->*' t2" := (stepmany t1 t2) (at level 40).

Hint Constructors step.

(* ##################################### *)
(** *** Examples *)

Lemma step_example1 :
  (tm_app id_AarrowA id_A) -->* id_A.
Proof.
  eapply rsc_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply rsc_refl.  Qed.  

Lemma step_example2 :
  (tm_app id_AarrowA (tm_app id_AarrowA id_A)) -->* id_A.
Proof.
  eapply rsc_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply rsc_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply rsc_refl.  Qed. 

(** We can use the [normalize] tactic from above to simplify the
    proof. *)

Lemma step_example2' :
  (tm_app id_AarrowA (tm_app id_AarrowA id_A)) -->* id_A.
Proof.
  normalize.
Qed. 

(** **** Exercise: 2 stars (step_example3) *)  
(** Try to do this one both with and without [normalize]. *)
Lemma step_example3 :
       (tm_app (tm_app id_AarrowA_arrow_AarrowA id_AarrowA) id_A)
  -->* id_A.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Typing *)

(* ################################### *)
(** *** Contexts *)

(** Question: What is the type of the term "[x y]"?

    Answer: It depends on the types of [x] and [y]!  

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place "typing judgment", informally
    written [Gamma |- t : T], where [Gamma] is a "typing context"
    -- a mapping from variables to their types.  *)

Definition partial_map (A:Type) := id -> option A.

Definition context := partial_map ty.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
Qed.

(* ################################### *)
(** *** Typing Relation *)

(** Informally: 
[[[
                             Gamma x = T
                            --------------                              (T_Var)
                            Gamma |- x : T

                      Gamma, x:T11 |- t12 : T12
                     ----------------------------                       (T_Abs)
                     Gamma |- \x:T11.t12 : T11->T12

                        Gamma |- t1 : T11->T12
                          Gamma |- t2 : T11
                        ----------------------                          (T_App)
                         Gamma |- t1 t2 : T12

]]]
The notation [ Gamma, x:T ] means "extend the partial function [Gamma]
to also map [x] to [T]."
*)

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (tm_var x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (extend Gamma x T11) t12 T12 -> 
      has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App : forall T11 T12 Gamma t1 t2,
      has_type Gamma t1 (ty_arrow T11 T12) -> 
      has_type Gamma t2 T11 -> 
      has_type Gamma (tm_app t1 t2) T12.
     
Tactic Notation "typing_cases" tactic(first) tactic(c) :=
  first;
  [ c "T_Var" | c "T_Abs" | c "T_App" ].

Hint Constructors has_type.

(* ################################### *)
(** *** Examples *)

Example typing_example_1 :
  has_type empty (tm_abs a A (tm_var a)) (ty_arrow A A).
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(** Note that since we added the has_type constructors to the
    hints database, auto can actually solve this one immediately.
    *)

Example typing_example_1' :
  has_type empty (tm_abs a A (tm_var a)) (ty_arrow A A).
Proof. auto.  Qed.

Hint Unfold beq_id beq_nat extend.

(** Written informally, the next one is:
[[
     empty |- \a:A. \b:A->A. b (b a)) 
           : A -> (A->A) -> A.
]]
*)

Example typing_example_2 :
  has_type empty
    (tm_abs a A
       (tm_abs b (ty_arrow A A)
          (tm_app (tm_var b) (tm_app (tm_var b) (tm_var a)))))
    (ty_arrow A (ty_arrow (ty_arrow A A) A)).
Proof with auto using extend_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(** **** Exercise: 2 stars, optional *)
(** Prove the same result without using [auto], [eauto], or
    [eapply]. *)

Example typing_example_2_full :
  has_type empty
    (tm_abs a A
       (tm_abs b (ty_arrow A A)
          (tm_app (tm_var b) (tm_app (tm_var b) (tm_var a)))))
    (ty_arrow A (ty_arrow (ty_arrow A A) A)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (typing_example_3) *)
(** Formally prove the following typing derivation holds:
[[
   empty |- (\a:A->B. \b:B-->C. \c:A.
               b (a c)) 
         : T.
]]
*)

Example typing_example_3 :
  exists T, 
    has_type empty
      (tm_abs a (ty_arrow A B)
         (tm_abs b (ty_arrow B C)
            (tm_abs c A
               (tm_app (tm_var b) (tm_app (tm_var a) (tm_var c))))))
      T.

Proof with auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can also show that terms are _not_ typable.  For example, let's
    formally check that there is no typing derivation assigning a type
    to the term [\a:A. \b:B, a b] -- i.e.,
[[
    ~ exists T,
        empty |- (\a:A. \b:B, a b) : T.
]]
*)
Example typing_nonexample_1 :
  ~ exists T,
      has_type empty 
        (tm_abs a A
            (tm_abs b B
               (tm_app (tm_var a) (tm_var b))))
        T.
Proof.
  intros C. destruct C.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  (* rewrite extend_neq in H1. rewrite extend_eq in H1. *)
  inversion H1.  Qed.

(** **** Exercise: 2 stars (typing_nonexample_2) *)
(** Now you prove this one doesn't hold:
[[
   ~ exists T,
       empty |- (\a:A->A, \b:B, a b) : T.
]]
*)

Example typing_nonexample_2 :
  ~ exists T,
      has_type empty
        (tm_abs a (ty_arrow A A)
           (tm_abs b B
              (tm_app (tm_var a) (tm_var b))))
        T.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (typing_nonexample_3) *)
(** Another nonexample:
[[
    ~ (exists S, exists T,
          empty |- (\a:S. a a) : T).
]]
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        has_type empty 
          (tm_abs a S
             (tm_app (tm_var a) (tm_var a)))
          T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (typing_statements) *)

(** Which of the following propositions are provable? 
       - [b:B |- \a:A.a : A->A]

       - [exists T,  empty |- (\b:B->B. \a:B. b a) : T]

       - [exists T,  empty |- (\b:B->B. \a:B. a b) : T]

       - [exists S, a:S |- (\b:B->B. b) a : S]

       - [exists S, exists T,  a:S |- (a a a) : T]

[]
*)

(** **** Exercise: 1 star (more_typing_statements) *)

(** Which of the following propositions are provable?  For the
    ones that are, give witnesses for the existentially bound
    variables.
       - [exists T,  empty |- (\b:B->B->B. \a:B, b a) : T]

       - [exists T,  empty |- (\a:A->B, \b:B-->C, \c:A, b (a c)):T]

       - [exists S, exists U, exists T,  a:S, b:U |- (\c:A. a b c) : T]

       - [exists S, exists T,  a:S |- \b:A. a (a b) : T]

       - [exists S, exists U, exists T,  a:S |- a (\c:U. c a) : T]

[]
*)

(* ###################################################################### *)
(** ** Properties *)

(* ###################################################################### *)
(** *** Free Variables *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tm_var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tm_abs y T11 t12).

Tactic Notation "afi_cases" tactic(first) tactic(c) :=
  first;
  [ c "afi_var" | c "afi_app1" | c "afi_app2" | c "afi_abs" ].

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* ###################################################################### *)
(** *** Substitution *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof.
  intros. generalize dependent Gamma. generalize dependent T. 
  (afi_cases (induction H) Case); intros.
  Case "afi_var". 
    inversion H0; subst. exists T. assumption.
  Case "afi_app1".
    inversion H0; subst. eapply IHappears_free_in. apply H4. 
  Case "afi_app2".
    inversion H0; subst. eapply IHappears_free_in. apply H6.
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    apply not_eq_beq_id_false in H. 
    rewrite extend_neq in H7; assumption.
Qed.

(** **** Exercise: 2 stars *)
Corollary typable_empty__closed : forall t T, 
    has_type empty t T  ->
    closed t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     has_type Gamma' t S.
Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  (typing_cases (induction H) Case); intros.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x0 Hafi.
    (* tricky step... the Gamma' we use to instantiate is 
       [extend ty Gamma x T1] *)
    unfold extend. remember (beq_id x x0) as e. destruct e...
  Case "T_App".
    apply T_App with T11...  Qed.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (extend Gamma x U) t S  ->
     has_type empty v U   ->
     has_type Gamma (subst x v t) S.
Proof with eauto.
  intros Gamma x U v t S Ht Hv.
  generalize dependent Gamma. generalize dependent S. 
  (tm_cases (induction t) Case); intros S Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tm_var".
    rename i into y. remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      apply beq_id_eq in Heqe. subst.
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
      eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tm_abs".
    rename i into y. apply T_Abs.
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      eapply context_invariance...
      apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend.
      destruct (beq_id y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...  Qed.

(* ###################################################################### *)
(** *** Preservation *)

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t --> t'  ->
     has_type empty t' T.
Proof with eauto.
  remember (@empty ty) as Gamma. 
  intros t t' T HT. generalize dependent t'.   
  (typing_cases (induction HT) Case); intros t' HE; subst Gamma.
  Case "T_Var".
    inversion HE. 
  Case "T_Abs".
    inversion HE.  
  Case "T_App".
    (step_cases (inversion HE) SCase); subst...
    (* The ST_App1 and ST_App2 cases are immediate by induction, and
       auto takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...  Qed.

(** **** Exercise: 2 stars (subject_expansion_stlc) *)
(** An exercise earlier in this file asked about the subject
    expansion property for the simple language of arithmetic and
    boolean expressions.  Does this property hold for STLC?  That
    is, is it always the case that, if [t --> t'] and [has_type
    t' T], then [has_type t T]?  If so, prove it.  If not, give a
    counter-example.

(* FILL IN HERE *)
[]
*)

(* ###################################################################### *)
(** *** Progress *)

Theorem progress : forall t T, 
     has_type empty t T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  (typing_cases (induction Ht) Case); subst Gamma...
  Case "T_Var".
    inversion H. 

  Case "T_App".
    right. destruct IHHt1...

    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is a value".
        (* Since t2 is a value and has an arrow type, it must be an abs.
           Sometimes this is proved separately and called a "canonical 
           forms" lemma *)
        inversion H; subst. exists (subst x t2 t)...
      SSCase "t2 steps".
        destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...

    SCase "t1 steps".
      destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
Qed.

(** **** Exercise: 3 stars, optional *)
(** Show that progress can also be proved by induction on terms
    instead of types. *)

Theorem progress' : forall t T,
     has_type empty t T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  (tm_cases (induction t) Case); intros T Ht.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** *** Uniqueness of types *)

(** **** Exercise: 3 stars *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)
(** Formalize this statement and prove it. *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** ** Additional exercises *)

(** **** Exercise: 1 star (progress_preservation_statement) *)
(** Without peeking, write down the progress and preservation
    theorems for the simply typed lambda-calculus. *)
(** [] *)

(** **** Exercise: 2 stars (stlc_variation1) *)
(** Suppose we add the following new rule to the evaluation
    relation of the STLC:
[[
      | T_Strange : forall x t,  
           has_type empty (tm_abs x A t) B
]]
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinacy of [step]

      - Progress

      - Preservation

[]
*)

(** **** Exercise: 2 stars (stlc_variation2) *)
(** Suppose we remove the rule [ST_App1] from the [step]
    relation. Which of the three properties in the previous
    exercise become false in the absence of this rule? For each
    that becomes false, give a counterexample.

[]
*)

End STLC.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Exercise: STLC with Arithmetic *) 

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.

(* ###################################################################### *)
(** ** Syntax and operational semantics *)

(** To types, we add a base type of natural numbers (and remove
    the other base types, for brevity) *)

Inductive ty : Type :=
  | ty_arrow : ty -> ty -> ty
  | ty_nat   : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, and zero-testing... *)

Inductive tm : Type :=
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  | tm_nat  : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) tactic(c) :=
  first;
  [ c "tm_var" | c "tm_app" | c "tm_abs" |
    c "tm_nat" | c "tm_succ" | c "tm_pred" | c "tm_mult" | c "tm_if0" ].

(** **** Exercise: 4 stars (STLCArith) *)
(** Finish formalizing the definition and properties of the STLC extended
    with arithmetic.  Specifically:

    - Copy the whole development of STLC that we went through above (from
      the definition of values through the Progress theorem), and
      paste it into the file at this point.

    - Extend the definitions of the [subst] operation and the [step]
      relation to include appropriate clauses for the arithmetic operators.

    - Extend the proofs of all the properties of the original STLC to deal
      with the new syntactic forms.  Make sure Coq accepts the whole file. *)

(* FILL IN HERE *)
(** [] *)

End STLCArith.

(** Version of 4/26/2010 *)

