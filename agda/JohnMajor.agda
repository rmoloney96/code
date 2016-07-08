module JohnMajor where 

open import Data.Nat renaming (_⊔_ to _⊔_Nat)
open import Level using (zero; suc; _⊔_)

data JohnMajorEq {a} {A : Set a} (x : A) : ∀ {b} {B : Set b} → B → Set _ where
  JohnMajorRefl : JohnMajorEq x x

test : JohnMajorEq 1 1
test = {!!}