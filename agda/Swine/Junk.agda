
data VecIdx : (n : ℕ) (P : ℕ → Set) → Set where
  []ⁱ : ∀ {P} → VecIdx 0 P 
  _∷ⁱ_ : ∀ {n} {P} → P n → VecIdx n P → VecIdx (suc n) P 

tab : ∀ (α : Arity) → (P : ℕ → Set) → Set 
tab α P = Vec (Σ[ i ∈ ℕ ] P i) (length α)
