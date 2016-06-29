
module FiniteSubsetUtils where

open import FiniteSubset
open import Utilities.ListProperties renaming (_∈_ to _∈L_)
open import Data.List
open import Utilities.Logic
open import Data.Bool
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Nat
open import Finiteness renaming (∣_∣ to ∣_∣listable)

_∈_ : ∀ {C : Set}{eq : DecEq C} {b : Bool} → C → FiniteSubSet C eq b → Set
_∈_ {eq = eq} x S = x ∈L (listOf S)

_∈𝔹_ : ∀ {C : Set}{eq : DecEq C} {b : Bool} → C → FiniteSubSet C eq b → Bool
_∈𝔹_ {eq = eq} x S = ⌊ eq2in eq x (listOf S ) ⌋

_/_ : {C : Set}{eq : DecEq C} {b1 b2 : Bool}
  → FiniteSubSet C eq b1 → FiniteSubSet C eq b2
  → FiniteSubSet C eq b1
_/_ {C} {eq = _==_} {b1} {b2} S T = 
        for s ∈ S as _
        do if not (s ∈𝔹 T)
           then return {b = true} s

_⊆_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
        FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
_⊆_ S T = ∀ s → s ∈ S → s ∈ T 

_⊆L_ : ∀ {C : Set} → List C → List C → Set
_⊆L_ S T = ∀ s → s ∈L S → s ∈L T 

⊆Lx∷S⇒⊆LS : ∀ {C} {x : C} {S T} → ((x ∷ S) ⊆L T) → x ∈L T → S ⊆L T
⊆Lx∷S⇒⊆LS S⊆T x∈LT s x = S⊆T s (there x)

_⊆L?_ : ∀ {C : Set} {eq : DecEq C} → 
       Decidable (_⊆L_ {C})
[] ⊆L? T = yes (λ s → λ ())
_⊆L?_ {eq = eq} (x ∷ S) T with eq2in eq x T
_⊆L?_ {eq = eq} (x ∷ S) T | yes p with _⊆L?_ {eq = eq} S T
(x ∷ S) ⊆L? T | yes p₁ | yes p = yes (λ s x₁ → aux p₁ x₁ p)
  where aux : ∀ {C : Set} {s x : C} {T S} → x ∈L T → s ∈L (x ∷ S) → S ⊆L T → s ∈L T
        aux P here S⊆T = P
        aux P (there Q) S⊆T = S⊆T _ Q
(x ∷ S) ⊆L? T | yes p | no ¬p = no (λ x₁ → ¬p (⊆Lx∷S⇒⊆LS x₁ p))
(x ∷ S) ⊆L? T | no ¬p = no (λ z → ¬p (z x here))

_⊆?_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
       Decidable (_⊆_ {C} {eq} {b1} {b2})
_⊆?_ {eq = eq} S T = _⊆L?_ {eq = eq} (listOf S) (listOf T)

_⊂_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
        FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
S ⊂ T = S ⊆ T × ¬ T ⊆ S 

open import Function

∣_∣ : ∀ {C : Set} {eq : DecEq C} {b1 : Bool} →
      FiniteSubSet C eq b1 → ℕ
∣ S ∣ = length ∘ proj₁ $ lstbl2nodup (fsListable S)


open import Data.Nat

_≺_ : {C : Set}{eq : DecEq C} {b1 b2 : Bool} →
      FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
S ≺ T = ∣ S ∣ <′ ∣ T ∣  

open import Induction.WellFounded
open import Induction.Nat

module WF⊆mod (C : Set) (eq : DecEq C) (b : Bool) where
  open Inverse-image {_<_ = _<′_} (∣_∣ {C} {eq} {b}) renaming (well-founded to well-founded-ii-obj)
  {- The inverse image of a well founded relation is well founded. -}

  wf≺ : Well-founded _≺_
  wf≺ = well-founded-ii-obj <-well-founded

  ⊂⇒<′ : ∀ {S T : FiniteSubSet C eq b} → S ⊂ T → S ≺ T
  ⊂⇒<′ {S} {T} P with listOf S 
  ⊂⇒<′ {S} {T} P | S' = ?

{-
open Subrelation {A = Database} {_<₁_ = (_⊂_)} {_<₂_ =  _≺_} ⊂⇒<′
  renaming (well-founded to well-founded-subrelation)

{- The sub relation of a well-founded relation is well founded -}
wf⊂ : Well-founded _⊂_ 
wf⊂ = well-founded-subrelation wf≺
-}

{-
open Inverse-image {_<_ = _<′_} (∣_∣ {true} {DataTriple} {eqDataTriple}) renaming (well-founded to well-founded-ii-dat)
{- The inverse image of a well founded relation is well founded. -}
wf≺dat : Well-founded _≺dat_
wf≺dat = well-founded-ii-dat <-well-founded
-}
