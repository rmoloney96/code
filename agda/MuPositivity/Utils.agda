
module Utils where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Product
open import Data.Vec
open import Data.Nat hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Data.Bool hiding (_≟_)

≡n : ∀ {n} → Vec Set (suc n) → Set
≡n (A ∷ []) = {x y : A} → x ≡ y
≡n (A ∷ (B ∷ w)) = {x y : A} → x ≡ y → (≡n (B ∷ w))

DecEq : ∀ X → Set
DecEq X = Decidable (_≡_ {A = X})

n≤m⇒1+n≤1+m : ∀ n m → n ≤′ m → suc n ≤′ suc m
n≤m⇒1+n≤1+m n .n ≤′-refl = ≤′-refl
n≤m⇒1+n≤1+m n₁ _ (≤′-step p) with n≤m⇒1+n≤1+m n₁ _ p
n≤m⇒1+n≤1+m n₁ _ (≤′-step p) | res = ≤′-step res 

1+n≤1+m⇒n≤m : ∀ n m → suc n ≤′ suc m → n ≤′ m 
1+n≤1+m⇒n≤m n .n ≤′-refl = ≤′-refl
1+n≤1+m⇒n≤m n zero (≤′-step ())
1+n≤1+m⇒n≤m n (suc m) (≤′-step p) = ≤′-step (1+n≤1+m⇒n≤m n m p) 

infix 6 _⇒_
_⇒_ : Bool → Bool → Bool
P ⇒ Q = not P ∨ Q

open import Level 
record DecTotalOrderEq (C : Set) (_≼_ : Rel C Level.zero) : Set where
  field
    tri : Trichotomous _≡_ _≼_
    tran : Transitive _≼_
    _≼?_ : Decidable _≼_

  _≟_ : ∀ x y → Dec (x ≡ y)
  x ≟ y with tri x y
  x ≟ y | tri< a ¬b ¬c = no ¬b
  x ≟ y | tri≈ ¬a b ¬c = yes b
  x ≟ y | tri> ¬a ¬b c = no ¬b 
  
