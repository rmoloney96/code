module Equality where

open import Level using (suc; zero)

data _≈_ {a} {A : Set a} (x : A) :  A → Set a where 
  refl : x ≈ x
