module Flip where 

flip : ∀ {A : Set} {B : A → Set} → (x : A) → (y : B x) → ({} → C x y)
flip 