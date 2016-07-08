module Coinductive where 

open import Coinduction

data ℂ : Set where 
  ∅ : ℂ 
  1+ : ∞ ℂ → ℂ

one : ℂ 
one = 1+ (♯ ∅)
two : ℂ 
two = 1+ (♯ one)
three : ℂ 
three = 1+ (♯ two)

inf : ℂ 
inf = 1+ (♯ inf)

inf2 : ℂ 
inf2 = 1+ (♯ (1+ (♯ inf)))

data _≡∞_ : ℂ → ℂ → Set where
  ≡∞-refl : ∀ {n} → n ≡∞ n 
  ≡∞-succ : ∀ {n m} → ∞ ((♭ n) ≡∞ (♭ m)) → (1+ n) ≡∞ (1+ m)

three_theorem : three ≡∞ three 
three_theorem = ≡∞-refl

theorem : inf ≡∞ inf2 
theorem = ≡∞-succ (♯ ≡∞-succ (♯ ≡∞-refl)) 
