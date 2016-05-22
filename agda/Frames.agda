
module Frames where

open import Data.Bool

data Formula : Set where
  v : Bool → Formula
  _∩_ : Formula → Formula → Formula
  _∪_ : Formula → Formula → Formula
  _⊕_ : Formula → Formula → Formula

data AltFormula : Set where
  va : Bool → AltFormula
  _∪a_ : AltFormula → AltFormula → AltFormula
  _⊕a_ : AltFormula → AltFormula → AltFormula
  

inj : AltFormula → Formula
inj (va x) = v x
inj (f ∪a f₁) = inj f ∪ inj f₁
inj (f ⊕a f₁) = inj f ⊕ inj f₁

∣_∣ : Formula → Bool
∣ v x ∣ = x
∣ x ∩ x₁ ∣ = ∣ x ∣ ∧ ∣ x₁ ∣
∣ x ∪ x₁ ∣ = ∣ x ∣ ∨ ∣ x₁ ∣
∣ x ⊕ x₁ ∣ = if ∣ x ∣ then (not ∣ x₁ ∣) else ∣ x₁ ∣  

∣_∣a : AltFormula → Bool
∣ va x ∣a = x
∣ x ∪a x₁ ∣a = ∣ x ∣a ∨ ∣ x₁ ∣a
∣ x ⊕a x₁ ∣a = if ∣ x ∣a then (not ∣ x₁ ∣a) else ∣ x₁ ∣a  

mutual
  imbed-∩ : Formula → Formula → AltFormula
  imbed-∩ (v false) f₁ = va false
  imbed-∩ (v true) f₁ =  imbed f₁
  imbed-∩ (f ∩ f₁) f₂ with imbed-∩ f f₁ | imbed-∩ f f₂
  imbed-∩ (f ∩ f₁) f₂ | x | y = imbed-∩ (inj x) (inj y)
  imbed-∩ (f ∪ f₁) f₂ = imbed-∩ f f₂ ∪a imbed-∩ f₁ f₂
  imbed-∩ (f ⊕ f₁) f₂ = imbed-∩ f f₂ ⊕a imbed-∩ f₁ f₂

  imbed : Formula → AltFormula
  imbed (v x) = va x
  imbed (f ∩ f₁) = imbed-∩ f f₁
  imbed (f ∪ f₁) = imbed f ∪a imbed f₁
  imbed (f ⊕ f₁) = imbed f ⊕a imbed f₁
