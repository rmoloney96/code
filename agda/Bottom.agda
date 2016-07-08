module Bottom where 

open import Data.Empty

test : ∀ {A : Set} → ⊥ → A
test ()

b ∨ ¬b