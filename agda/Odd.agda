module Odd where 

open import Data.Nat

mutual
  data Even : ℕ → Set where 
    evenZero : Even zero
    evenNext : ∀ {n} → Odd n → Even (suc n) 
  data Odd : ℕ → Set where 
    oddOne : Odd (suc zero) 
    oddNext : ∀ {n} → Even n → Odd (suc n)