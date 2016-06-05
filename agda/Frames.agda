
module Frames where

open import Data.Bool
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (inspect)


data Formula : ℕ → Set where
  v : Bool → Formula 1
  _∩_[_] : ∀ {n k m} → Formula n → Formula m → k ≡ n + m → Formula k
  _∪_[_] : ∀ {n k m} → Formula n → Formula m → k ≡ n + m → Formula k
  _⊕_[_] : ∀ {n k m} → Formula n → Formula m → k ≡ n + m → Formula k

data AltFormula : ℕ → Set where
  va : Bool → AltFormula 1
  _∪_[_]a : ∀ {n k m} → AltFormula n → AltFormula m → k ≡ n + m → AltFormula k
  _⊕_[_]a : ∀ {n k m} → AltFormula n → AltFormula m → k ≡ n + m → AltFormula k
  
inj : ∀ {n} → AltFormula n → Formula n
inj (va x) = v x
inj (f ∪ f₁ [ p ]a) = inj f ∪ inj f₁ [ p ]
inj (f ⊕ f₁ [ p ]a) = inj f ⊕ inj f₁ [ p ]

∣_∣ : ∀ {n} → Formula n → Bool
∣ v x ∣ = x
∣ x ∩ x₁ [ p ] ∣ = ∣ x ∣ ∧ ∣ x₁ ∣
∣ x ∪ x₁ [ p ] ∣ = ∣ x ∣ ∨ ∣ x₁ ∣
∣ x ⊕ x₁ [ p ] ∣ = if ∣ x ∣ then (not ∣ x₁ ∣) else ∣ x₁ ∣  

∣_∣a : ∀ {n} → AltFormula n → Bool
∣ va x ∣a = x
∣ x ∪ x₁ [ p ]a ∣a = ∣ x ∣a ∨ ∣ x₁ ∣a
∣ x ⊕ x₁ [ p ]a ∣a = if ∣ x ∣a then (not ∣ x₁ ∣a) else ∣ x₁ ∣a  


sumless : ∀ {k o m n n₁} → k ≤ m + n₁ → o ≤ n + n₁ →  k + o  ≤  n + m + n₁
sumless p q = {!p!} 

mutual
  imbed-∩ : ∀ {m n k} → Formula m → Formula n → k ≡ m + n → Σ[ o ∈ ℕ ] o ≤ k × AltFormula o
  imbed-∩ {.1} {n} (v false) g refl = 1 , (s≤s z≤n , va false)
  imbed-∩ (v true) g p = {!!}
  imbed-∩ (f ∩ f₁ [ x ]) g p = {!!}
  imbed-∩ (f ∪ f₁ [ refl ]) g refl with imbed-∩ f g refl | imbed-∩ f₁ g refl
  imbed-∩ {_} {n₁} (f ∪ f₁ [ refl ]) g refl | proj₁ , proj₂ , proj₃ | proj₄ , proj₅ , proj₆ = proj₁ + proj₄ + n₁ , ({!!} , proj₃ ∪ proj₆ [ {!!} ]a)
  imbed-∩ (f ⊕ f₁ [ x ]) g p = {!!}
  
  imbed : ∀ {n} → Formula n → Σ[ m ∈ ℕ ] m ≤ n × AltFormula m
  imbed (v x) = 1 , s≤s z≤n , va x
  imbed (f ∩ f₁ [ p ]) = imbed-∩ f f₁ p
  imbed (f ∪ f₁ [ p ]) = {!!}
  imbed (f ⊕ f₁ [ p ]) = {!!}

{-


mutual
-  imbed-∩ : Formula → Formula → AltFormula
-  imbed-∩ (v false) f₁ = va false
-  imbed-∩ (v true) f₁ =  imbed f₁
-  imbed-∩ (f ∩ f₁) f₂ with imbed-∩ f f₁ | imbed-∩ f f₂
-  imbed-∩ (f ∩ f₁) f₂ | x | y = imbed-∩ (inj x) (inj y)
-  imbed-∩ (f ∪ f₁) f₂ = imbed-∩ f f₂ ∪a imbed-∩ f₁ f₂
-  imbed-∩ (f ⊕ f₁) f₂ = imbed-∩ f f₂ ⊕a imbed-∩ f₁ f₂
-
-  imbed : Formula → AltFormula
-  imbed (v x) = va x
-  imbed (f ∩ f₁) = imbed-∩ f f₁
-  imbed (f ∪ f₁) = imbed f ∪a imbed f₁
-  imbed (f ⊕ f₁) = imbed f ⊕a imbed f₁

-}
