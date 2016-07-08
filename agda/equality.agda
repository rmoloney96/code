
open import Level using (succ; zero)

data _≈_ : ∀ {a} → ∀ {A : Set a} → A → A → Set (succ a) where 
  refl : ∀ {x : A}  → x ≈ x