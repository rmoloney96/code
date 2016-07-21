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
Interpretation = Atom → Subjects

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

open import FinSet

mutual
 
  -- Need a well foundedness proof here over the relation ⊂
  -- but this should be trivial
  {-# TERMINATING #-}
  fp : Atom → Shape → Interpretation → Subjects → Transitions → Subjects
  fp x φ i S 𝓣 with ⟦ φ ⟧ i S 𝓣
  fp x φ i S 𝓣 | S' with S' ⊂? S
  fp x φ i S 𝓣 | S' | yes p = fp x φ (i [ x ≔ S ]) S' 𝓣
  fp x φ i S 𝓣 | S' | no ¬p = S
  
  _[_≔_] : Interpretation → Atom → Subjects → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y

  ⟦_⟧ : Shape → (i : Interpretation) → Subjects → Transitions → Subjects
  ⟦ ⊥ ⟧ i S 𝓣 = ∅
  ⟦ ⊤ ⟧ i S 𝓣 = S
  ⟦ α⟨ a ⟩ φ ⟧ i S 𝓣 = ⟪ s ∈ S ∣ ∃[ t ∈ (⟦ φ ⟧ i S 𝓣) ] ⌊ (s , a , uri t) ∈trans? 𝓣 ⌋ ⟫
  ⟦ α[ a ] φ ⟧ i S 𝓣 = ⟪ s ∈ S ∣ Π[ t ∈ (⟦ φ ⟧ i S 𝓣) ] ⌊ (s , a , uri t) ∈trans? 𝓣 ⌋ ⟫
  ⟦ ℓ⟨ a ⟩ τ ⟧ i S 𝓣 =  ⟪ s ∈ S ∣ ∃[ l ∈ (𝓡ₗ 𝓣) ] (⌊ (s , a , lit l) ∈trans? 𝓣 ⌋ ∧ ⌊ typeDec l τ ⌋) ⟫ 
  ⟦ ℓ[ a ] τ ⟧ i S 𝓣 = ⟪ s ∈ S ∣ Π[ l ∈ 𝓡ₗ 𝓣 ] (⌊ (s , a , lit l) ∈trans? 𝓣 ⌋ ∧ ⌊ typeDec l τ ⌋) ⟫ 
  ⟦ φ ⊕ φ₁ ⟧ i S 𝓣 = (⟦ φ ⟧ i S 𝓣) ∪ (⟦ φ₁ ⟧ i S 𝓣) 
  ⟦ φ ⊗ φ₁ ⟧ i S 𝓣 = (⟦ φ ⟧ i S 𝓣) ∩ (⟦ φ₁ ⟧ i S 𝓣) 
  ⟦ ν x φ ⟧ i S 𝓣 = fp x φ i S 𝓣
  ⟦ v x ⟧ i S 𝓣 = i x 
  ⟦ - φ ⟧ i S 𝓣 = 𝓓 𝓣 ̸ ⟦ φ ⟧ i S 𝓣

  -- Some possible extensions:

  -- Parametric Shapes
  --  Π : Atom → Shape → Shape
  --  _·_ : Shape → Shape → Shape 
  
  -- Finite non-looping recursion
  --  v : Atom → Shape
  --  μ : Atom → Shape → Shape


_⊢_∶_ : Transitions → X → Shape → Set
𝓣 ⊢ x ∶ φ = x ∈ ⟦ φ ⟧ (λ _ → (𝓓 𝓣)) (𝓓 𝓣) 𝓣

checkφ : ∀ 𝓣 x φ → Dec ( 𝓣 ⊢ x ∶ φ )
checkφ 𝓣 x φ = x ∈? ⟦ φ ⟧ (λ _ → (𝓓 𝓣)) (𝓓 𝓣) 𝓣
