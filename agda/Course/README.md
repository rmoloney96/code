
Semantics of Programming Languages (CS3017)
===========================================

This directory contains Agda proof scripts which accompany the slides for the CS3017 course at Trinity present here: https://www.cs.tcd.ie/matthew.hennessy/splexternal2015/index.php.

Structure
---------

* Topic 1: Operational semantics for simple arithmetic expressions.

The examples given in the slides are contained in the file: ``OperationalSemantics.agda''

* Topic 2: Induction

A limited number of examples from the slides are present in the file: ``Induction.agda''

Some of the consistency proofs are given in ``Consistency.agda''. 

There is a proof that (∀ E → Σ[ n ∈ ℕ ] E ⟶⋆ num n) in ``SmallSteEval.agda''.  It makes use of transfinite induction rather than strong mathematical induction, but the approach is substantially similar. Induction is performed over the size of proofs.

* Topic 3: A (first-order) functional programming language.

There were no slides for this - PCF would be a possible choice for implementation.

* Topic 4: The While programming language

The While programming language and progress proof is in the file: ``While.agda''

* Topic 5: Handling Exceptions

Not completed

* Topic 6: Provably correct implementations

The subject of all files.

* Topic 7: Functions as data

Not completed


