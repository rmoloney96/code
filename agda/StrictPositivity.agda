module Positivity where 

open import Data.Nat
open import Data.Bool 
open import Data.List 
open import Data.Unit using (⊤)
-- open import Relation.Unary using (Decidable)
open import Data.Maybe.Core
open import Relation.Nullary.Core
open import Level using (Level) -- renaming (suc to ^)

Id : (x : Level) (X : Set x) → (X → X)
Id = λ x X x' → x'

Ctx : Set
Ctx = List Bool

data _∈_ : ℕ → Ctx → Set where 
  inzero : ∀ {Δ} → zero ∈ (true ∷ Δ)
  innext : ∀ {n Δ b} → n ∈ Δ → (suc n) ∈ (b ∷ Δ) 

inInversionSuc : ∀ {n Δ b} → (suc n) ∈ (b ∷ Δ) → n ∈ Δ
inInversionSuc (innext {n} {Δ} {b} p) = p 

inctx : ∀ n Δ → Dec (n ∈ Δ)
inctx _       []          = no (λ())
inctx zero    (true ∷ Δ)  = yes inzero
inctx zero    (false ∷ Δ) = no (λ())
inctx (suc n) (b ∷ Δ)     with inctx n Δ
inctx (suc n) (b ∷ Δ)     | (yes p) = yes (innext p)
inctx (suc n) (b ∷ Δ)     | (no p)  = no (λ p' → p (inInversionSuc p')) 

empty : ℕ → Ctx 
empty (suc n) = false ∷ (empty n) 
empty zero     = []

data Ty : Set where
  ∗ : Ty
  ι : ℕ → Ty
  _⇒_ : Ty → Ty → Ty
  _×_ : Ty → Ty → Ty 
  _⊕_ : Ty → Ty → Ty
  μ : Ty → Ty
  Π : Ty → Ty

{-
data _·_⊢_ : Ctx → Ctx → Ty → Set where 
     VarValid : ∀ {n ΔP ΔN} → n ∈ ΔP → ¬(n ∈ ΔN) → ΔP · ΔN ⊢ (ι n) 
     ImpValid : ∀ {ΔP ΔN α β} → 
       ΔN · ΔP ⊢ α → 
       ΔP · ΔN ⊢ β → 
       ΔP · ΔN ⊢ (α ⇒ β)
     AndValid : ∀ {ΔP ΔN α β} → 
       ΔP · ΔN ⊢ α → 
       ΔP · ΔN ⊢ β → 
       ΔP · ΔN ⊢ (α × β)
     OrValid : ∀ {ΔP ΔN α β} → 
       ΔP · ΔN ⊢ α → 
       ΔP · ΔN ⊢ β → 
       ΔP · ΔN ⊢ (α ⊕ β)
     AllValid : ∀ {ΔP ΔN α} → 
       (true ∷ ΔP) · (false ∷ ΔN) ⊢ α → 
       ΔP · ΔN ⊢ Π α

<_> : Ctx → Ctx 
< Δ > = empty (length Δ)

data _⊢⁺_ : Ctx → Ty → Set where 
  OnlyPositive : ∀ {Δ α} → Δ · < Δ > ⊢ α → Δ ⊢⁺ α 

varValidInversion : ∀ {ΔP ΔN n} → ΔP · ΔN ⊢ ι n → n ∈ ΔP
varValidInversion {ΔP} {ΔN} {n} (VarValid p) = p

orValidInversionL : ∀ {ΔP ΔN α β} → ΔP · ΔN ⊢ (α ⊕ β) → (ΔP · ΔN ⊢ α)
orValidInversionL {ΔP} {ΔN} {α} {β} (OrValid p q) = p

orValidInversionR : ∀ {ΔP ΔN α β} → ΔP · ΔN ⊢ (α ⊕ β) → (ΔP · ΔN ⊢ β)
orValidInversionR {ΔP} {ΔN} {α} {β} (OrValid p q) = q

impValidInversionL : ∀ {ΔP ΔN α β} → ΔP · ΔN ⊢ (α ⇒ β) → (ΔN · ΔP ⊢ α)
impValidInversionL {ΔP} {ΔN} {α} {β} (ImpValid p q) = p

impValidInversionR : ∀ {ΔP ΔN α β} → ΔP · ΔN ⊢ (α ⇒ β) → (ΔP · ΔN ⊢ β)
impValidInversionR {ΔP} {ΔN} {α} {β} (ImpValid p q) = q

andValidInversionL : ∀ {ΔP ΔN α β} → ΔP · ΔN ⊢ (α × β) → (ΔP · ΔN ⊢ α)
andValidInversionL {ΔP} {ΔN} {α} {β} (AndValid p q) = p

andValidInversionR : ∀ {ΔP ΔN α β} → ΔP · ΔN ⊢ (α × β) → (ΔP · ΔN ⊢ β)
andValidInversionR {ΔP} {ΔN} {α} {β} (AndValid p q) = q

allValidInversion : ∀ {ΔP ΔN α} → ΔP · ΔN ⊢ Π α → ((true ∷ ΔP) · (false ∷ ΔN) ⊢ α)
allValidInversion {ΔP} {ΔN} {α} (AllValid p) = p

isValid : ∀ ΔP ΔN α → Dec (ΔP · ΔN ⊢ α)
isValid ΔP ΔN (ι n)   with (inctx n ΔP)
isValid ΔP ΔN (ι n)   | yes p = yes (VarValid p) 
isValid ΔP ΔN (ι n)   | no p  = no (λ p' → p (varValidInversion p'))
isValid ΔP ΔN (α ⇒ β) with isValid ΔN ΔP α
isValid ΔP ΔN (α ⇒ β) | yes p with isValid ΔP ΔN β
isValid ΔP ΔN (α ⇒ β) | yes p | yes q = yes (ImpValid p q) 
isValid ΔP ΔN (α ⇒ β) | yes p | no q  = no (λ x → q (impValidInversionR x))
isValid ΔP ΔN (α ⇒ β) | no p  = no (λ x → p (impValidInversionL x))
isValid ΔP ΔN (α × β) with isValid ΔP ΔN α
isValid ΔP ΔN (α × β) | yes p with isValid ΔP ΔN β
isValid ΔP ΔN (α × β) | yes p | yes q = yes (AndValid p q) 
isValid ΔP ΔN (α × β) | yes p | no q  = no (λ x → q (andValidInversionR x))
isValid ΔP ΔN (α × β) | no p  = no (λ x → p (andValidInversionL x))
isValid ΔP ΔN (α ⊕ β) with isValid ΔP ΔN α
isValid ΔP ΔN (α ⊕ β) | yes p with isValid ΔP ΔN β
isValid ΔP ΔN (α ⊕ β) | yes p | yes q = yes (OrValid p q) 
isValid ΔP ΔN (α ⊕ β) | yes p | no q  = no (λ x → q (orValidInversionR x))
isValid ΔP ΔN (α ⊕ β) | no p  = no (λ x → p (orValidInversionL x))
isValid ΔP ΔN (Π α)   with isValid (true ∷ ΔP) (false ∷ ΔN) α
isValid ΔP ΔN (Π α)   | yes p = yes (AllValid p) 
isValid ΔP ΔN (Π α)   | no p  = no (λ x → p (allValidInversion x))
-}