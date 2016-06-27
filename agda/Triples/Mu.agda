open import Utilities.Logic
open import Relation.Binary
open import Relation.Nullary.Decidable

module Mu
  (Atom : Set)
  (X : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqX : DecEq X)
  (eqD : DecEq D)
  (DT : Set)
  (⊢ᵟ_∶_ : D → DT → Set)
  (typeDec : Decidable (⊢ᵟ_∶_))
  where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import FiniteSubset renaming (_∪_ to _∪_fs ; _∩_ to _∩_fs) 
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool
open import Data.List

import Database as DB
module DBmodule = DB Atom X D eqAtom eqX eqD DT ⊢ᵟ_∶_ typeDec
open DBmodule public

Interpretation : Set
Interpretation = Atom → Database

infixl 21 _⊕_
infixl 21 _⊗_
data Shape : Set where
  ⊥ : Shape
  ⊤ : Shape
  α⟨_⟩_ : (a : X) → Shape → Shape
  α[_]_ : (a : X) → Shape → Shape
  ℓ⟨_⟩_ : (a : X) → DT → Shape
  ℓ[_]_ : (a : X) → DT → Shape
  _⊕_ : Shape → Shape → Shape
  _⊗_ : Shape → Shape → Shape
  -- Loops
  ν : Atom → Shape → Shape
  --  μ : Atom → Shape → Shape (redundant?)
  v : Atom → Shape
  -- Negation
  -_ : Shape → Shape



mutual
 
  -- Need a well foundedness proof here over the relation ⊂
  -- but this should be trivial
  {-# TERMINATING #-}
  gfp : Atom → Shape → Interpretation → Database → Database
  gfp x φ i T with ⟦ φ ⟧ i T
  gfp x φ i T | T' with T' ⊂? T
  gfp x φ i T | T' | yes p = gfp x φ (i [ x ≔ T ]) T'
  gfp x φ i T | T' | no ¬p = T
  
  _[_≔_] : Interpretation → Atom → Database → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y

  ⟦_⟧ : Shape → (i : Interpretation) → Database → Database
  ⟦ ⊥ ⟧ i S = ∅
  ⟦ ⊤ ⟧ i S = S
  ⟦ α⟨ a ⟩ φ ⟧ i S = Σs∈ S ⟨s, a ,t⟩∧t∈ (⟦ φ ⟧ i S)
  ⟦ α[ a ] φ ⟧ i S = Πs∈ S ⟨s, a ,t⟩∧t∈ (⟦ φ ⟧ i S)
  ⟦ ℓ⟨ a ⟩ τ ⟧ i S = Σs∈ S ⟨s, a ,l⟩∧⊢l∶ τ
  ⟦ ℓ[ a ] τ ⟧ i S = Πs∈ S ⟨s, a ,l⟩∧⊢l∶ τ
  ⟦ φ ⊕ φ₁ ⟧ i S = (⟦ φ ⟧ i S) ∪ (⟦ φ₁ ⟧ i S) 
  ⟦ φ ⊗ φ₁ ⟧ i S = (⟦ φ ⟧ i S) ∩ (⟦ φ₁ ⟧ i S) 
  ⟦ ν x φ ⟧ i S = gfp x φ i S
  ⟦ v x ⟧ i S = i x 
  ⟦ - φ ⟧ i S = S / ⟦ φ ⟧ i S

  -- Some possible extensions:

  -- Parametric Shapes
  --  Π : Atom → Shape → Shape
  --  _·_ : Shape → Shape → Shape 
  
  -- Finite non-looping recursion
  --  v : Atom → Shape
  --  μ : Atom → Shape → Shape

open import Utilities.ListProperties

_⊢_∶_ : Database → X → Shape → Set
Ξ ⊢ x ∶ φ = x ∈ Data.List.map sub
                   (listOf (⟦ φ ⟧ (λ _ → Ξ) Ξ))


checkφ : ∀ Ξ x φ → Dec ( Ξ ⊢ x ∶ φ )
checkφ Ξ x φ with Data.List.map sub $ listOf (⟦ φ ⟧ (λ _ → Ξ) Ξ)
checkφ Ξ x φ | lst = eq2in eqX x lst
