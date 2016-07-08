
module transitive where 

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data ℕ : Set where 
  z : ℕ 
  s : ℕ → ℕ 

data ⊥ : Set where 

f : ℕ → ℕ 
f z = z
f (s x) = f x


data _≤_ : ℕ → ℕ → Set where 
  zero : ∀ (n : ℕ) → z ≤ n 
  next : ∀ (n m : ℕ) → n ≤ m → s n ≤ s m

isz≤1 : z ≤ s z
isz≤1 = zero (s z)

zle : ∀ n → n ≤ z → n ≡ z
zle .z (zero .z) = refl 

data ⋆ : ∀ {A : Set} (R : A → A → Set) → A → A → Set₂ where 
  base⋆ : ∀ {A : Set} (R : A → A → Set) x y → R x y → ⋆ R x y
  next⋆ : ∀ {A : Set} (R : A → A → Set) x y z → ⋆ R x y → R y z → ⋆ R x z 


-- trans : ∀ {A : Set} (R : A → A → Set) → A → A → Set₂ 
-- trans R x y = R x y , Σ[z ∶ A] trans R x z → R z y