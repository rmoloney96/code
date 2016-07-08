
open import Data.Vec
open import Data.Nat using (ℕ) 
open import Data.Fin

module TypedLambda where 


record LambdaTheory : Set where

  field
    n : ℕ -- number of types
    m : ℕ -- number of constants
    γ : Fin m → Fin n -- map from constants to types
  
  data Ty : Set where 
    𝕋 : Fin n → Ty
    _⇒_ : Ty → Ty → Ty
    _⊗_ : Ty → Ty → Ty

  data Term : Set where 
    ι : ∀ {n} → Fin n → Term 
    ƛ : Ty → Term → Term
    _∘_ : Term → Term → Term
    c : Fin m → Term

  data _⊢_∶_ : ∀ {n} → Vec Ty n → Term → Ty → Set where
    ιIntro : ∀ {n Γ} → {r : Fin n} →
      Γ ⊢ (ι r) ∶ (lookup r Γ)
    cIntro : ∀ {n r} →
      {Γ : Vec Ty n} → 
      Γ ⊢ c r ∶ 𝕋 (γ r)
    λIntro : ∀ {n α β t} → 
      {Γ : Vec Ty n} → 
      (Γ ++ [ β ]) ⊢ t ∶ α → 
      Γ ⊢ ƛ β t ∶ (β ⇒ α) 
    λElim : ∀ {n α β t s} → 
      {Γ : Vec Ty n} → 
      Γ ⊢ t ∶ (α ⇒ β) → 
      Γ ⊢ s ∶ α → 
      Γ ⊢ t ∘ s ∶ β

  -- ↑ : ∀ {m} → Term → ℕ → Term 
  -- ↑ (ι y) d with compare d y
  -- ↑ (ι y) d | p = ?  
  -- ↑ (ƛ α y') d = ƛ α (↑ y' (suc d))
  -- ↑ (y ∘ y') d = ↑ y d ∘ ↑ y' d
  -- ↑ (c y) d = c y 

--  ↑ (ι r) d with compare r d 
--  ↑ (ι r) d | p = 

--  ⟦_:=_⟧ : ℕ → 

𝔹 : Fin 1 
𝔹 = zero
 
true : Fin 2
true = zero 

false : Fin 2
false = suc zero

γ : Fin 2 → Fin 1
γ zero = 𝔹
γ (suc i) = 𝔹 

r = record { n = 1 ; m = 2 ; γ = γ}

open LambdaTheory r

  
λIntro : ∀ {n α β t} → {Γ : Vec Ty n} → (Γ ++ [ β ]) ⊢ t ∶ α → Γ ⊢ ƛ β t ∶ (β ⇒ α) 
