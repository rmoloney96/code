open import Utils

module Relation
  (C : Set)
  (eqC : DecEq C)
  where

open import Data.List
open import Data.Bool
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Data.Nat
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function
open import FinSet
open import Membership

open import Database C C eqC eqC 

module WFTrans = FinSet.WF⊂mod Transition eqTrans
open WFTrans renaming (_∈?_ to _∈trans?_) 

_∈?_ : (x : C) → (L : List C) → Dec (x ∈ L)
x ∈? S = eq2in eqC x S

-- Right restriction (at property a)
_⟨_⟩▹_ : ∀ (R : Transitions) (a : C) (A : List C)  → Transitions
R ⟨ a ⟩▹ A = ⟪ τ ∈ R ∣ ⌊ eqC (prop τ) a ⌋ ∧ ⌊ (obj τ) ∈? A ⌋ ⟫

σ₁ : ∀ s R → Transitions
σ₁ s R = ⟪ τ ∈ R ∣ ⌊ eqC (sub τ) s ⌋ ⟫

𝓒 : ∀ s R → ℕ
𝓒 s R = ∣ 𝓓 (σ₁ s R) ∣⟨ eqC ⟩
