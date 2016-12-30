Exploring Cardinality in the Modal μ-Calculus 
==============================================

This is an exploration of the meaning of cardinality constraints in
the Modal μ-Calculus when applied to finite transition systems. It
implements an interpreter for Modal μ-formulae.

Monotonicity 
============

In order to show that fixed points are well defined, we need to know
that the functions associated with formulae of a given free variable
in the modal mu calculus are monotonic. That is for a function f on
the the power set of a set U the following hold:

~~~

X ⊆ Y → ⟦ φ ⟧(X) ⊆ ⟦ φ ⟧(Y)

~~~

With this fact we have well defined fixed points such that: 

~~~

⟦ μ X . φ ⟧ ≔ ⋂{ X ⊆ U | ⟦ φ ⟧(X) ⊆ X }

~~~ 

In order to define show montonicity, we also need antitonicity as negation 
will induce an inversion of the principle such that: 

~~~

(∀ X Y → Y ⊆ X → ⟦ φ ⟧(X) ⊆ ⟦ φ ⟧(Y))
 → 
(∀ X Y → X ⊆ Y → ⟦ ¬φ ⟧(X) ⊆ ⟦ ¬φ ⟧(Y))

~~~

In order to show montonicity and antitonicity we can impose a
restriction on the syntax of the formulae known as "positivity". The
positivity restriction states that free variables to be used in fixed
points must be in a "positive" position in the formula. This can be
defined inductively which we find convenient to do simultaneously with
the definition of negatively occuring formulae with a single inductive
relation called "Polarity". 

The Polarity of a term gives a set of all variables (from 𝓥) which occur 
in a positive context and all variables in a negative context for a given term. 

~~~

Polarity : Φ → 𝒫(𝓥) → 𝒫(𝓥) → Set

~~~

Since it is possible to have variables in a mixed polarity (both
positive and negative), posivity for a free variable x can most
usefully be defined as a polarity in which the variable is not in a
negative poliarity for the formaule.

~~~

Positive x φ ≔ Polarity φ 𝓟 𝓝 ∧ x ∉ 𝓝

~~~

Given a positive formulae φ we can ensure monotonicity and thereby
fixed-points.

There is one further complication. We define ⟦\_⟧ as a function in
Agda, however functions must be total for Agda to accept them. This
means we need to know that φ is monotonic in order to show that the
fixed points are well defined and terminating. But the proof of
monotonicity requires the definion of ⟦\_⟧. This leads to a difficult
circularity.

We dispense with this problem by requiring that the interpretation of
fixed points must always decrease or we give up. If the interpretation
is not monotonic the result will be somewhat arbitrary. However if it
is indeed monotonic then the result will have the meaning of the fixed
point. This allows us to *assume* the monotonicity before we prove
it, a proof which has a somewhat coinductive flavour.

