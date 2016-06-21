open import Utilities.Logic

module Triples
  (Atom : Set)
  (X : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqX : DecEq X)
  (eqD : DecEq D)
  (DT : Set)
  (⊢ᵟ_∶_ : D → DT → Set)
  where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import FiniteSubset
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool

ObjectTriple = X × X × X
DataTriple = X × X × D

,-inv₁ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} →  ¬ x ≡ y →  ¬ (x , w) ≡ (y , z)
,-inv₁ f refl = f refl

,-inv₂ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} →
  ¬ w ≡ z →  ¬ (x , w) ≡ (y , z)
,-inv₂ f refl = f refl

DecEqPair : {A B : Set} → (eqA : DecEq A) → (eqB : DecEq B) → DecEq (A × B)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) with eqA proj₁ proj₃
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p with eqB proj₂ proj₄
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p₁ | yes p = yes (cong₂ _,_ p₁ p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p | no ¬p = no (,-inv₂ ¬p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | no ¬p = no (,-inv₁ ¬p) 

eqObjectTriple : DecEq ObjectTriple
eqObjectTriple = DecEqPair eqX (DecEqPair eqX eqX)

eqDataTriple : DecEq DataTriple
eqDataTriple = DecEqPair eqX (DecEqPair eqX eqD)

Database = FiniteSubSet ObjectTriple eqObjectTriple false × FiniteSubSet DataTriple eqDataTriple false

_∈_obj : ObjectTriple → Database → Set
o ∈ Γ obj = Σ[ e ∈ Element (proj₁ Γ) ] o ≡ proj₁ e

_∈_dat : DataTriple → Database → Set
o ∈ Γ dat = Σ[ e ∈ Element (proj₂ Γ) ] o ≡ proj₁ e

infix 21 _⊕_
infix 21 _⊗_

data Shape : Set where
  α⟨_⟩_ : (a : X) → Shape → Shape
  α[_]_ : (a : X) → Shape → Shape
  ℓ⟨_⟩_ : (a : X) → DT → Shape
  ℓ[_]_ : (a : X) → DT → Shape
  _⊕_ : Shape → Shape → Shape
  _⊗_ : Shape → Shape → Shape
  -- Loops
  ν : Atom → Shape → Shape
  μ : Atom → Shape → Shape
  -- Negation
  -_ : Shape → Shape

Interpretation : Set
Interpretation = Atom → Database

mutual 
  _[_≔_] : Interpretation → Atom → Shape → Interpretation
  (i [ X ≔ φ ]) Y with eqAtom X Y
  (i [ X₁ ≔ φ ]) Y | yes p = {!!} --⟦ φ ⟧ i
  (i [ X₁ ≔ φ ]) Y | no ¬p = i Y

  ⟦_⟧ : Shape → (i : Interpretation) → (Ξ : Database) → Set
  ⟦ α⟨ a ⟩ φ ⟧ i = ⟦ φ ⟧ i 
  ⟦ α[ a ] φ ⟧ i = ⟦ φ ⟧ i
  ⟦ ℓ⟨ a ⟩ φ ⟧ = {!!}
  ⟦ ℓ[ a ] φ ⟧ = {!!}
  ⟦ φ ⊕ φ₁ ⟧ i Ξ = ⟦ φ ⟧ i Ξ ⊎ ⟦ φ₁ ⟧ i Ξ 
  ⟦ φ ⊗ φ₁ ⟧ i Ξ = ⟦ φ ⟧ i Ξ × ⟦ φ₁ ⟧ i Ξ 
  ⟦ ν X φ ⟧ i Ξ = ⟦ φ ⟧ (i [ X ≔ φ ]) Ξ
  ⟦ μ X φ ⟧ i Ξ = {!!}
  ⟦ - φ ⟧ i Ξ = {!!}

  -- Some possible extensions:

  -- Parametric Shapes
  --  Π : Atom → Shape → Shape
  --  _·_ : Shape → Shape → Shape 
  
  -- Finite non-looping recursion
  --  v : Atom → Shape
  --  μ : Atom → Shape → Shape


{-
open import Data.List

Ctx : Set
Ctx = List (X × Shape)

data _,_⊢_∶_ : Database → Ctx → X → Shape → Set₁ where
 I⊕ₗ : ∀ {Ξ Γ s τ σ} → Ξ , Γ ⊢ s ∶ σ → Ξ , Γ ⊢ s ∶ σ ⊕ τ
 I⊕ᵣ : ∀ {Ξ Γ s τ σ} → Ξ , Γ ⊢ s ∶ τ → Ξ , Γ ⊢ s ∶ σ ⊕ τ
 I⊗ : ∀ {Ξ Γ s τ σ} → Ξ , Γ ⊢ s ∶ σ → Ξ , Γ ⊢ s ∶ τ → Ξ , Γ ⊢ s ∶ σ ⊗ τ
 Iα : ∀ {Ξ Γ s p t σ} → (t , p , s) ∈ Ξ obj → Ξ , Γ ⊢ s ∶ σ → Ξ , Γ ⊢ t ∶ (α⟨ p ⟩ σ)
 Iℓ : ∀ {Ξ Γ d p t σ} → (t , p , d) ∈ Ξ dat → ⊢ᵟ d ∶ σ → Ξ , Γ ⊢ t ∶ (ℓ⟨ p ⟩ σ)
 Iν : ∀ {Ξ Γ t σ} →  Ξ , (t , σ) ∷ Γ ⊢ t ∶ σ → Ξ , Γ ⊢ t ∶ (ν σ)

-}
