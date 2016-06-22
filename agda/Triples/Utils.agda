
module Utils where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Product
open import Data.Vec
open import Data.Nat

⇒ : ∀ {n} → Vec Set (suc n) → Set
⇒ (A ∷ []) = A
⇒ (A ∷ (B ∷ w)) = A → (⇒ (B ∷ w))

≡n : ∀ {n} → Vec Set (suc n) → Set
≡n (A ∷ []) = {x y : A} → x ≡ y
≡n (A ∷ (B ∷ w)) = {x y : A} → x ≡ y → (≡n (B ∷ w))

@ 

congₙ : ∀ {n} {v : Vec Set (suc n)} → (f : ⇒ v) → (≡n v) → (f (⇒ 

{-
congₙ : ∀ 

cong₃ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl
-}
