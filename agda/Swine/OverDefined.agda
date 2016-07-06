open import Utils

module OverDefined
  (Atom : Set)
  (eq : DecEq Atom) where

open import Relation.Nullary

⟨_↔_⟩ : Atom → Atom → Atom → Atom
⟨ x ↔ y ⟩ z with eq x z
⟨ x ↔ y ⟩ z | yes p = y
⟨ x ↔ y ⟩ z | no ¬p with eq y z
⟨ x ↔ y ⟩ z | no ¬p | yes p = x
⟨ x ↔ y ⟩ z | no ¬p₁ | no ¬p = z

open import Data.Nat
open import Data.List
open import Data.Product hiding (map)
open import Data.Fin renaming (zero to fzero ; suc to fsuc) hiding (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

π₁ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → A × B → A 
π₁ = proj₁

π₂ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → A × B → A 
π₂ = proj₁

data Code : Set where
  c : Atom → Code

open import Data.Vec hiding (zip ; map)
open import Data.List.All
open import Function
open import Data.Unit

Arity : ℕ → Set
Arity m = Vec ℕ m

-- Signatures
Signature : Set 
Signature = List (Code × Σ[ m ∈ ℕ ] Arity m)

data _∈_sig : Code → Signature → Set where
  here : ∀ {Γ x} n → (α : Arity n) → x ∈ (x , (n , α)) ∷ Γ sig
  there : ∀ {x y α Γ} → x ∈ Γ sig → x ∈ (y , α) ∷ Γ sig

findArity : ∀ {x Γ} → x ∈ Γ sig → Σ[ m ∈ ℕ ] Arity m
findArity (here n α) = (n , α)
findArity (there p) = findArity p

data abt (Ξ : Signature) : ℕ → Set where
  name : Atom → abt Ξ zero 
  oper : ∀ {n} {α : Arity n} {op : Code} → (j : op ∈ Ξ sig) →
         n ≡ π₁ (findArity j) → α ≡ π₂ (findArity j)
         ((i : Fin (π₁ (findArity j))) → abt Ξ (Data.List.All.lookup i (π₂ (findArity j)))) → 
         abt Ξ zero
