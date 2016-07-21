RDF Triple Store 
================

This is an exploration into the implementation of an RDF triple store
in Agda. The idea is to provide a sufficient library that we can look
at various ontological and logical notions over a triple-store.

Modal Mu-Calculus 
-----------------

As a first exploration we have implemented the modal mu-calculus as a
typing judgement. This turns out to be convenient for use with a
triple store.  It acts both as a specification of a the shape of a
graph, allowing cycles, but also can double as a query language,
associating the set of all subjects which meet any given
specification.

In the file `Mu.agda` one will find an implementation of the modal-mu
calculus over an RDF database seen as a triple store.  The Mu-calculus
literal terminals are defined to be parametric in a datatype theory
which can be implemented independently.  The datatype theory is very
flexible though it must be checkable in an empty context.  An example
data type theory is given in the file `RDF.agda`.

Example
-------

We can use the modal mu-calculus to determine whether or not a given
RDF object meets a mu-calculus specification.  We see below a
specification of a `Polity` which shows that a polity is such that all
of it's "name" properties are strings, that there exists a
"population" which is a natural number and there exists a
"neighbouringPolity" which is, itself, a `Polity`. 

~~~agda

Polity : Shape
Polity = ν "Pol" ((ℓ[ "name" ] Str) ⊗
                  (ℓ⟨ "population" ⟩ Natural) ⊗
                  (α⟨ "neighbouringPolity" ⟩ (v "Pol")))


~~~

We can then check this against a Database (which currently must be
given explicitly as a list), using the `checkφ` function.

~~~agda 
DB : Database
DB = fs-plain (("seshat:Rome" , "neighbouringPolity" , inj₁ "seshat:Rome") ∷ 
              (("seshat:Rome" , "name" , inj₂ (s "Rome")) ∷
              (("seshat:Rome" , "name" , inj₂ (s "That")) ∷
              (("seshat:Rome" , "population" , inj₂ (n 1000)) ∷ 
              (("seshat:AThing" , "thingy", inj₂ (s "Foo")) ∷ [])))))


checkDB : Bool
checkDB with checkφ DB "seshat:Rome" Polity
checkDB | yes p = true
checkDB | no ¬p = false
~~~

