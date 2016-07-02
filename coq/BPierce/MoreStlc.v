(** * MoreStlc: More on the Simply Typed Lambda-Calculus *)
(* Version of 4/23/2010 *)


Require Export Stlc.
Require Import Relations.

(* ###################################################################### *)
(** * Typechecking for STLC *)

(** The [has_type] relation defines what it means for a term to belong
    to a type (in some context).  But it doesn't, by itself, tell us
    how to _check_ whether or not a term is well typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- they exactly follow the shape of the term.  This makes it
    straightforward to translate the typing rules into clauses of a
    typechecking _function_ that takes a term and a context and either
    returns the term's type or else signals that the term is not
    typable. *)

Module STLCChecker.
Import STLC.

(* ###################################################################### *)
(** ** Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Fixpoint beq_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | ty_base i, ty_base i' => 
      beq_id i i'
  | ty_arrow T11 T12, ty_arrow T21 T22 => 
      andb (beq_ty T11 T21) (beq_ty T12 T22)
  | _,_ => 
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [beq_ty] and the logical
    proposition that its inputs are equal. *)

Lemma beq_ty_refl : forall T1,
  beq_ty T1 T1 = true.
Proof.
  intros T1. induction T1; simpl.
    symmetry. apply beq_id_refl.
    rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.

Lemma beq_ty__eq : forall T1 T2,
  beq_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  Case "T1=ty_base i".
    symmetry in H0. apply beq_id_eq in H0. subst...
  Case "T1=ty_arrow T1_1 T1_2".
    apply andb_true in H0. destruct H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.

(* ###################################################################### *)
(** ** The Typechecker *)

(** Now here's the typechecker.  It works by walking over the
    structure of the given term, returning either [Some T] or [None].
    Each time we make a recursive call to find out the types of the
    subterms, we need to pattern-match on the results to make sure
    that they are not [None].  Also, in the [tm_app] case, we use
    pattern matching to extract the left- and right-hand sides of the
    function's arrow type (and fail if the type of the function is not
    [ty_arrow T11 T12] for some [T1] and [T2]). *)

Fixpoint type_check (Gamma:context) (t:tm) : option ty :=
  match t with
  | tm_var x => Gamma x
  | tm_abs x T11 t12 => match type_check (extend Gamma x T11) t12 with
                          | Some T12 => Some (ty_arrow T11 T12)
                          | _ => None
                        end
  | tm_app t1 t2 => match type_check Gamma t1, type_check Gamma t2 with
                      | Some (ty_arrow T11 T12),Some T2 =>
                        if beq_ty T11 T2 then Some T12 else None
                      | _,_ => None
                    end
  end.

(* ###################################################################### *)
(** ** Properties *)

(** To verify that this typechecking algorithm is the correct one, we
    show that it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  (tm_cases (induction t) Case); intros Gamma T Htc; inversion Htc.
  Case "tm_var"...
  Case "tm_app".
    remember (type_check Gamma t1) as TO1.
    remember (type_check Gamma t2) as TO2.
    destruct TO1 as [T1|]; try solve by inversion;
    destruct T1 as [|T11 T12]; try solve by inversion.
    destruct TO2 as [T2|]; try solve by inversion.
    remember (beq_ty T11 T2) as b.
    destruct b; try solve by inversion.
    symmetry in Heqb. apply beq_ty__eq in Heqb.
    inversion H0; subst...
  Case "tm_abs".
    rename i into y. rename t into T1.
    remember (extend Gamma y T1) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve by inversion.
    inversion H0; subst...
Qed.    

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  (typing_cases (induction Hty) Case); simpl.
  Case "T_Var"...
  Case "T_Abs". rewrite IHHty...
  Case "T_App".
    rewrite IHHty1. rewrite IHHty2.
    rewrite (beq_ty_refl T11)...
Qed.

End STLCChecker.

(* ###################################################################### *)
(** * Simple Extensions to STLC *)

(** The simply typed lambda-calculus has enough structure to make its
    theoretical properties interesting, but it is not yet much of a
    programming language.  In this chapter, we begin to close the gap
    with more familiar languages by introducing a number of familiar
    features that have straightforward treatments at the level of
    typing. *)

(** *** Numbers and Booleans *)

(** Adding types, constants, and primitive operations for numbers and
    booleans is easy -- just a matter of combining the two halves of
    the Stlc.v chapter. *)

(** *** The [Unit] Type *)

(** Another useful base type, found especially in languages in the ML
    family, is the singleton type [Unit].  In contrast to the
    uninterpreted base types of the simply typed lambda-calculus, this
    type _is_ interpreted, in the simplest possible way: we explicitly
    introduce a single element---the term constant [unit] (with a
    small [u])---and a typing rule making [unit] an element of [Unit].
    We also add [unit] to the set of possible result values of
    computations---indeed, [unit] is the _only_ possible result of
    evaluating an expression of type [Unit].
<<
       t ::=                Terms:
           | ...               (other terms same as before)
           | unit              unit value

       v ::=                Values:
           | ...     
           | unit              unit

       T ::=                Types:
           | ...
           | Unit              Unit type
>>
*)

(** *** [let]-bindings *)

(** When writing a complex expression, it is often useful---both for
    avoiding repetition and for increasing readability---to give names
    to some of its subexpressions.  Most languages provide one or more
    ways of doing this.  In OCaml, for example, we can write [let x=t1
    in t2] to mean ``evaluate the expression [t1] and bind the name
    [x] to the resulting value while evaluating [t2].''

    Our [let]-binder follows ML's in choosing a call-by-value
    evaluation order, where the [let]-bound term must be fully
    evaluated before evaluation of the [let]-body can begin.  The
    typing rule [T_Let] tells us that the type of a [let] can be
    calculated by calculating the type of the [let]-bound term,
    extending the context with a binding with this type, and in this
    enriched context calculating the type of the body, which is then
    the type of the whole [let] expression.

    At this point in the course, it's probably just as easy to simply
    look at the rules defining this new feature as to wade through a
    lot of english text conveying the same information.  Here they
    are:

    Syntax:
<<
       t ::=                Terms:
           | ...               
           | let x=t in t      let-binding
>> 
   Reduction:
[[[
                                 t1 --> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 --> let x=t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x=v1 in t2 --> [v1/x] t2
]]]
   Typing:
[[[
                Gamma |- t1 : T1      Gamma, x:T1 |- t2 : T2
                --------------------------------------------            (T_Let)
                        Gamma |- let x=t1 in t2 : T2
]]]
 *)

(** *** Pairs *)

(** Our functional programming examples have made frequent use of
    _pairs_ of values.  The type of such pairs is called a _product
    type_.

    The formalization of pairs is almost too simple to be worth
    discussing---by this point in the book, it should be about as easy
    to read a set of inference rules (or a formal [Inductive]
    definition) as to wade through a description in English conveying
    the same information.  However, let's look briefly at the various
    parts of the definition to emphasize the common pattern.

    In Coq, the primitive way of extracting the components of a pair
    is _pattern matching_.  An alternative style is to take [fst] and
    [snd] -- the first- and second-projection operators -- as
    primitives.  Just for fun, let's do our products this way.  For
    example, here's how we'd write a function that takes a pair of
    numbers and returns the pair of their sum and product:
<<
       \x:nat*nat. 
          let sum = x.fst + x.snd in
          let prod = x.fst * x.snd in
          (sum,prod)
>>

    Adding pairs to the simply typed lambda-calculus, then, involves
    adding two new forms of term---pairing, written [(t1,t2)], and
    projection, written [t.fst] for the first projection from [t] and
    [t.snd] for the second projection---plus one new type constructor,
    [T1*T2], called the _product_ of [T1] and [T2].  

    Syntax:
<<
       t ::=                Terms:
           | ...               
           | (t,t)             pair
           | t.fst             first projection
           | t.snd             second projection

       v ::=                Values:
           | ...
           | (v,v)             pair value

       T ::=                Types:
           | ...
           | T * T             product type
>>

   For evaluation, we need several new rules specifying how pairs and
   projection behave.  
[[[
                              t1 --> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) --> (t1',t2)

                              t2 --> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) --> (v1,t2')

                              t1 --> t1'
                          ------------------                          (ST_Fst1)
                          t1.fst --> t1'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst --> v1

                              t1 --> t1'
                          ------------------                          (ST_Snd1)
                          t1.snd --> t1'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd --> v2
]]]
    Rules [ST_FstPair] and [ST_SndPair] specify that, when a fully
    evaluated pair meets a first or second projection, the result is
    the appropriate component.  The congruence rules [ST_Fst1] and
    [ST_Snd1] allow reduction to proceed under projections, when the
    term being projected from has not yet been fully evaluated.
    [ST_Pair1] and [ST_Pair2] evaluate the parts of pairs: first the
    left part, and then---when a value appears on the left---the right
    part.  The ordering arising from the use of the metavariables [v]
    and [t] in these rules enforces a left-to-right evaluation
    strategy for pairs.  (Note the implicit convention that
    metavariables like [v] and [v1] can only denote values.)  We've
    also added a clause to the definition of values, above, specifying
    that [(v1,v2)] is a value.  The fact that the components of a pair
    value must themselves be values ensures that a pair passed as an
    argument to a function will be fully evaluated before the function
    body starts executing.  

   The typing rules for pairs and projections are straightforward.
   The rule, [T_Pair], says that [(t1,t2)] has type [T1*T2] if [t1]
   has type [T1] and [t2] has type [T2].  Conversely, the rules
   [T_Fst] and [T_Snd] tell us that, if [t1] has a product type
   [T11*T12] (i.e., if it will evaluate to a pair), then the types of
   the projections from this pair are [T11] and [T12].
[[[
               Gamma |- t1 : T1       Gamma |- t2 : T2
               ---------------------------------------                 (T_Pair)
                       Gamma |- (t1,t2) : T1*T2

                        Gamma |- t1 : T11*1T2
                        ---------------------                           (T_Fst)
                        Gamma |- t1.fst : T11

                        Gamma |- t1 : T11*T12
                        ---------------------                           (T_Snd)
                        Gamma |- t1.snd : T12

]]]
 *)

(** *** Lists *)

(** The typing features we have seen can be classified into _base
    types_ like [Bool], and _type constructors_ like [->] and [*] that
    build new types from old ones.  Another useful type constructor is
    [list].  For every type [T], the type [list T] describes
    finite-length lists whose elements are drawn from [T].

    Below we give the syntax, semantics, and typing rules for lists.
    Except for the fact that explicit type annotations are mandatory
    on [nil] and cannot appear on [cons], these lists are essentially
    identical to those we built in Coq.  We use [case] (a very
    simplified form of Coq's [match]) to destruct lists, to avoid
    dealing with questions like "what is the [head] of the empty
    list?"  So, for example, here is a function that calculates the
    sum of the first two elements of a list of numbers:
<<
       \x:list nat.
          case x of
            nil -> 0
          | a::x' -> case x' of
                       nil -> a
                     | b::x'' -> a+b
>>

    While we say that [cons v1 v2] is a value, we really mean that
    [v2] should also be a list -- we'll have to enforce this in the
    formal definition of value. *)

(**
    Syntax:
<<
       t ::=                Terms:
           | ...
           | nil T
           | cons t t
           | case t of nil -> t | x::x -> t

       v ::=                Values:
           | ...
           | nil T             nil value
           | cons v v          cons value

       T ::=                Types:
           | ...
           | list T            list of Ts
>>
   Reduction:
[[[
                                 t1 --> t1'
                       --------------------------                    (ST_Cons1)
                       cons t1 t2 --> cons t1' t2

                                 t2 --> t2'
                       --------------------------                    (ST_Cons2)
                       cons v1 t2 --> cons v1 t2'

                              t1 --> t1'
               ----------------------------------------              (ST_Case1)
                   (case t1 of nil -> t2 | h::t -> t3)
               --> (case t1' of nil -> t2 | h::t -> t3)

               ---------------------------------------------       (ST_CaseNil)
               (case nil T of nil -> t2 | h::t -> t3) --> t2

            ---------------------------------------------         (ST_CaseCons)
            (case (cons vh vt) of nil -> t2 | h::t -> t3)
                          --> [vh/h,vt/t]t3
]]]
   Typing:
[[[
                          -----------------------                       (T_Nil)
                          Gamma |- nil T : list T

                Gamma |- t1 : T      Gamma |- t2 : list T
                -----------------------------------------              (T_Cons)
                       Gamma |- cons t1 t2: list T

                Gamma |- t1 : list T1        Gamma |- t2 : T
                      Gamma, h:T1, t:list T1 |- t3 : T
              ------------------------------------------------         (T_Case)
              Gamma |- (case t1 of nil -> t2 | h::t -> t3) : T
]]]
 *)


(** *** General Recursion *)

(** Another facility found in most programming languages (including
    Coq) is the ability to define recursive functions.  For example,
    we might like to be able to define the factorial function like
    this:
<<
   fact = \x:nat. 
             if x=0 then 1 else x * (fact (pred x)))    
>> 
   But this would be require quite a bit of work to formalize: we'd
   have to introduce a notion of "function definitions" and carry
   around an "environment" of such definitions in the definition of
   the [step] relation.

   Here is another way that is straightforward to formalize: instead
   of writing recursive definitions where the right-hand side can
   contain the identifier being defined, we can define a _fixed-point
   operator_ that performs the "unfolding" of the recursive definition
   in the right-hand side lazily during reduction.
<<
   fact = 
       fix
         (\f:nat->nat.
            \x:nat. 
               if x=0 then 1 else x * (f (pred x)))    
>> 
   The intuition is that the higher-order function [f] passed to [fix]
   is a _generator_ for the [fact] function: if [f] is applied to a
   function that approximates the desired behavior of [fact] up to
   some number [n] (that is, a function that returns correct results
   on inputs less than or equal to [n]), then it returns a better
   approximation to [fact]---a function that returns correct results
   for inputs up to [n+1].  Applying [fix] to this generator returns
   its fixed point---a function that gives the desired behavior for
   all inputs [n].

   Syntax:
<<
       t ::=                Terms:
           | ...
           | fix t             fixed-point operator
>>
   Reduction:
[[[
                                 t1 --> t1'
                             ------------------                       (ST_Fix1)
                             fix t1 --> fix t1'

                -------------------------------------------         (ST_FixAbs)
                fix (\x:T1.t2) --> [(fix(\x:T1.t2)) / x] t2
]]]
   Typing:
[[[
                            Gamma |- t1 : T1->T1
                            --------------------                        (T_Fix)
                            Gamma |- fix t1 : T1
]]]
 *)

(** **** Exercise: 1 star (halve_fix) *)
(** Translate this recursive definition into one using [fix]:
<<
   halve = 
     \x:nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
(* FILL IN HERE *)
[]
*)

(** **** Exercise: 1 star (fact_steps) *)
(** Write down the sequence of steps that the term [fact 1] goes
    through to reduce to a normal form (assuming the usual reduction
    rules for arithmetic operations).

    (* FILL IN HERE *)
[]
*)

(** The ability to form the fixed point of a function of type [T->T]
    for any [T] has some surprising consequences.  In particular, it
    implies that _every_ type is inhabited by some term.  To see this,
    observe that, for every type [T], we can define a function
    [diverge_T] as follows:
[[
      diverge_T = \x:Unit. fix (\x:Unit.x);
]]
    Whenever [diverge_T] is applied to a [unit] argument, we get a
    non-terminating evaluation sequence in which [ST-AppAbs] is
    applied over and over, always yielding the same term.  That is,
    for every type [T], the term [diverge_T unit] is an _undefined
    element_ of [T]. *)


(* ###################################################################### *)
(** * Formalizing the Extensions *)

(** **** Exercise: 5 stars (STLC_extensions) *)
(** Formalizing the extensions is left to you.  We've provided the
    necessary extensions to the syntax of terms and types, and we've
    included a few examples that you can test your definitions with to
    make sure they are working as expected.  You'll fill in the rest
    of the definitions and extend all the proofs accordingly.  (A good
    strategy is to work on the extensions one at a time, in multiple
    passes, rather than trying to work through the file from start to
    finish in a single pass.) *)

Module STLCExtended.

(* ###################################################################### *)
(** *** Syntax and Operational Semantics *)

Inductive ty : Type :=
  | ty_base  : id -> ty
  | ty_arrow : ty -> ty -> ty
  | ty_unit  : ty
  | ty_pair  : ty -> ty -> ty
  | ty_list  : ty -> ty
  | ty_nat   : ty.

Tactic Notation "ty_cases" tactic(first) tactic(c) :=
  first;
  [ c "ty_base" | c "ty_arrow" | c "ty_unit" |
    c "ty_pair" | c "ty_list" | c "ty_nat" ].

Inductive tm : Type :=
    (* pure STLC *)
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
    (* unit *)
  | tm_unit : tm
    (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
    (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_case : tm -> tm -> id -> id -> tm -> tm 
          (* i.e., [case t1 of | nil -> t2 | x::y -> t3] *)
    (* numbers *)
  | tm_nat : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
    (* let *)
  | tm_let : id -> tm -> tm -> tm 
          (* i.e., [let x = t1 in t2] *)
    (* fix *)
  | tm_fix  : tm -> tm.
(** Note that, for brevity, we've chosen a compressed version of the
    numeric operations, with a single [if0] form combining a zero test
    and a conditional. *)

Tactic Notation "tm_cases" tactic(first) tactic(c) :=
  first;
  [ c "tm_var" | c "tm_app" | c "tm_abs" |
    c "tm_unit" |
    c "tm_pair" | c "tm_fst" | c "tm_snd" |
    c "tm_nil" | c "tm_cons" | c "tm_case" |
    c "tm_nat" | c "tm_succ" | c "tm_pred" | c "tm_mult" | c "tm_if0" |
    c "tm_let" |
    c "tm_fix" ].

(** Some variables, for use in examples... *)

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation l := (Id 3).
Notation A := (ty_base (Id 4)).
Notation B := (ty_base (Id 5)).
Notation k := (Id 6).
Notation i1 := (Id 7).
Notation i2 := (Id 8).

(* ###################################################################### *)
(** *** Substitution *)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tm_var y => if beq_id x y then s else t
  | tm_abs y T t1 =>  tm_abs y T (if beq_id x y then t1 else (subst x s t1))
  | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
  (* FILL IN HERE *)
  | _ => t  (* ... and delete this line *) 
  end.

(* ###################################################################### *)
(** *** Reduction *)

(** Next we define the values of our language. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tm_abs x T11 t12)
  (* FILL IN HERE *)
  .

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (tm_app (tm_abs x T11 t12) v2) --> (subst x v2 t12)
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (tm_app t1 t2) --> (tm_app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (tm_app v1 t2) --> (tm_app v1 t2')
  (* FILL IN HERE *)

where "t1 '-->' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) tactic(c) :=
  first;
  [ c "ST_AppAbs" | c "ST_App1" | c "ST_App2" | 
    (* FILL IN HERE *)
  ].

Notation stepmany := (refl_step_closure step).
Notation "t1 '-->*' t2" := (stepmany t1 t2) (at level 40).

Hint Constructors step.

(* ###################################################################### *)
(** *** Typing *)

(* Standard definitions for contexts *)
Definition context := id -> (option ty).
Definition empty : context := (fun _ => None).
Definition extend (Gamma : context) (x:id) (T : ty) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Typing rules for proper terms *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (tm_var x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (extend Gamma x T11) t12 T12 -> 
      has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      has_type Gamma t1 (ty_arrow T1 T2) -> 
      has_type Gamma t2 T1 -> 
      has_type Gamma (tm_app t1 t2) T2
  (* FILL IN HERE *)
  .

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) tactic(c) :=
  first;
  [ c "T_Var" | c "T_Abs" | c "T_App" 
    (* FILL IN HERE *)
].

(* ###################################################################### *)
(** ** Examples *)

(** **** Exercise: 2 stars (examples) *)
(** Finish the proofs. *)
(* fact := fix
             (\f:nat->nat.
                \a:nat. 
                   if a=0 then 1 else a * (f (pred a))) *)
Definition fact :=
  tm_fix
    (tm_abs f (ty_arrow ty_nat ty_nat)
      (tm_abs a ty_nat
        (tm_if0 
           (tm_var a) 
           (tm_nat 1) 
           (tm_mult 
              (tm_var a) 
              (tm_app (tm_var f) (tm_pred (tm_var a))))))).

(** (Warning: you may be able to typecheck [fact] but still have some
    rules wrong!) *)

(* These hints improve the automation for [has_type]. 

  It says that whenever [auto] arrives at a goal of the form
  [(has_type G (tm_app e1 e1) T)], it should consider [eapply T_App],
  leaving an existential variable for the middle type T1, and similar
  for [case]. That variable will then be filled in during the search
  for type derivations for [e1] and [e2]. 

  We also include a hint to "try harder" when solving equality goals;
  this is useful to automate uses of T_Var (which includes an equality
  as a precondition).
*)

Hint Extern 2 (has_type _ (tm_app _ _) _) => eapply T_App; auto.
(** <<
(* Uncomment this once you've defined the [T_Case] constructor for
   the typing relation: *)
Hint Extern 2 (has_type _ (tm_case _ _ _ _ _) _) => eapply T_Case; auto.
>> *)
Hint Extern 2 (_ = _) => compute; reflexivity.


Example fact_typechecks :
  has_type empty fact (ty_arrow ty_nat ty_nat).
Proof with auto.
(* FILL IN HERE *) Admitted.

Example fact_example: 
  (tm_app fact (tm_nat 4)) -->* (tm_nat 24).
Proof. 
  (* FILL IN HERE *) Admitted.

(* map :=
     \g:nat->nat.
       fix
         (\f:[nat]->[nat].
            \l:[nat]. 
               case l of
               | [] -> []
               | x::l -> (g x)::(f l)) *) 
Definition map :=
  tm_abs g (ty_arrow ty_nat ty_nat)
    (tm_fix
      (tm_abs f (ty_arrow (ty_list ty_nat) (ty_list ty_nat))
        (tm_abs l (ty_list ty_nat)
          (tm_case (tm_var l)
            (tm_nil ty_nat) 
            a l (tm_cons (tm_app (tm_var g) (tm_var a)) 
                         (tm_app (tm_var f) (tm_var l))))))).

Example map_typechecks :
  has_type empty map 
    (ty_arrow (ty_arrow ty_nat ty_nat)
      (ty_arrow (ty_list ty_nat) 
        (ty_list ty_nat))).
Proof with auto.
  (* FILL IN HERE *) Admitted.

Example map_example :
  tm_app (tm_app map (tm_abs a ty_nat (tm_succ (tm_var a))))
         (tm_cons (tm_nat 1) (tm_cons (tm_nat 2) (tm_nil ty_nat)))
  -->* (tm_cons (tm_nat 2) (tm_cons (tm_nat 3) (tm_nil ty_nat))).
Proof with auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Properties of Typing *)

(** The proofs of progress and preservation for this system are
    essentially the same (though of course somewhat longer) as for the
    pure simply typed lambda-calculus. *)

(* ###################################################################### *)
(** *** Progress *)

Theorem progress : forall t T, 
     has_type empty t T ->
     value t \/ exists t', t --> t'. 
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t --> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  (has_type_cases (induction Ht) Case); intros HeqGamma; subst.
  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |- x : T] (since the
       context is empty). *)
    inversion H.
  Case "T_Abs".
    (* If the [T_Abs] rule was the last used, then [t = tm_abs x T11 t12],
       which is a value. *)
    left...
  Case "T_App".
    (* If the last rule applied was T_App, then [t = t1 t2], and we know 
       from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is a value 
       or can take a step. *)
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
      (* If both [t1] and [t2] are values, then we know that 
         [t1 = tm_abs x T11 t12], since abstractions are the only values
         that can have an arrow type.  But 
         [(tm_abs x T11 t12) t2 --> subst x t2 t12] by [ST_AppAbs]. *)
        inversion H; subst; try (solve by inversion).
        exists (subst x t2 t12)...
      SSCase "t2 steps".
        (* If [t1] is a value and [t2 --> t2'], then [t1 t2 --> t1 t2'] 
           by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
    SCase "t1 steps".
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2] by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
  (* FILL IN HERE *)
Qed.


(* ###################################################################### *)
(** *** Context Invariance *)

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
        appears_free_in x (tm_abs y T11 t12)
  (* FILL IN HERE *)
  .

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     has_type Gamma' t S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  (has_type_cases (induction H) Case); 
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. remember (beq_id x y) as e.
    destruct e...
  (* FILL IN HERE *)
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  (has_type_cases (induction Htyp) Case); inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx. 
    apply not_eq_beq_id_false in H2. rewrite H2 in Hctx...
  (* FILL IN HERE *)
Qed.

(* ###################################################################### *)
(** *** Preservation *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (extend Gamma x U) t S  ->
     has_type empty v U   ->
     has_type Gamma (subst x v t) S.
Proof with eauto.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then 
     Gamma |- (subst x v t) S. *)
  intros Gamma x U v t S Htypt Htypv. 
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow directly
     from the IH, with the exception of tm_var and tm_abs.
     The former aren't automatic because we must reason about how the
     variables interact. *)
  (tm_cases (induction t) Case);
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  Case "tm_var".
    simpl. rename i into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |- subst x v y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [subst x v y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      apply beq_id_eq in Heqe. subst.
      unfold extend in H1. rewrite <- beq_id_refl in H1. 
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend in H1. rewrite <- Heqe in H1...
  Case "tm_abs".
    rename i into y. rename t into T11.
    (* If [t = tm_abs y T11 t0], then we know that
         [Gamma,x:U |- tm_abs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       As our IH, we know that forall S Gamma, 
         [Gamma,x:U |- t0 : S -> Gamma |- subst x v t0 S].
    
       We can calculate that 
         subst x v t = tm_abs y T11 (if beq_id x y
                                      then t0 
                                      else subst x v t0)
       And we must show that [Gamma |- subst x v t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_id x y then t0 else subst x v t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    apply T_Abs...
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
      eapply context_invariance...
      apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend.
      destruct (beq_id y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- subst x v t0 : T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...
  (* FILL IN HERE *)
Qed.

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t --> t'  ->
     has_type empty t' T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t --> t'], then [empty |- t' : T]. *)
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]).  We show just the interesting ones. *)
  (has_type_cases (induction HT) Case); 
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t --> t']: [ST_App1], [ST_App2], and 
       [ST_AppAbs]. In the first two cases, the result follows directly from 
       the IH. *)
    inversion HE; subst...
    SCase "ST_AppAbs".
      (* For the third case, suppose 
           [t1 = tm_abs x T11 t12]
         and
           [t2 = v2].  
         We must show that [empty |- subst x v2 t12 : T2]. 
         We know by assumption that
             [empty |- tm_abs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and 
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  (* FILL IN HERE *)
Qed.
(** [] *)

End STLCExtended.
