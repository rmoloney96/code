
module CounterExample where

open import Data.Nat
open import Data.Product
open import Data.List
open import Membership
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

open import Monotonic ℕ ℕ ℕ _≟_ _≟_

A = 0
B = 1
C = 2
D = 3
E = 4
F = 5
G = 6
H = 7

{- Counter Example -}
𝓣 : Transitions
𝓣 = (A , B , C) ∷ (A , B , D) ∷ (F , B , G) ∷ []
open ModalTransitionSystem 𝓣

S : Set
S = List ℕ

i : Interpretation
i = (λ _ → [])

φ⟨_⟩ : (a : ℕ) → Φ+
φ⟨ a ⟩ = α⟨ B ⟩⁅ 2 ⁆ (v a)

X₁ : Subjects
X₁ = A ∷ ∅

Y₁ : Subjects
Y₁ = A ∷ D ∷ ∅

X₁⊆Y₁ : X₁ ⊆ Y₁
X₁⊆Y₁ .0 here = here
X₁⊆Y₁ x (there x∈X₁) = there (there x∈X₁)

reflRepl : ∀ a → (a ≟ a) ≡ yes refl
reflRepl a with (a ≟ a)
reflRepl a | yes refl = refl
reflRepl a | no ¬p = refl ↯ ¬p


φNotMonotone : ∀ (a : ℕ) → 
 ----------------------------------------------------------
  Σ[ X ∈ S ] Σ[ Y ∈ S ] X ⊆ Y × ¬ (⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ X ]) ⊆ ⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ Y ]))
φNotMonotone a = X₁ , Y₁ , X₁⊆Y₁ , example a
  where example : ∀ a → ¬ (⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ X₁ ]) ⊆ ⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ Y₁ ]))
        example a p with a ≟ a
        example a₁ p₁ | yes p = {!!}
        example a₁ p | no ¬p = refl ↯ ¬p


X₂ : Subjects
X₂ = G ∷ ∅

Y₂ : Subjects
Y₂ = C ∷ G ∷ ∅

X₂⊆Y₂ : X₂ ⊆ Y₂
X₂⊆Y₂ .6 here = there here
X₂⊆Y₂ x (there x∈X₂) = there (there x∈X₂)

φNotMonotone₂ : ∀ (a : ℕ) → 
 ----------------------------------------------------------
  Σ[ X ∈ S ] Σ[ Y ∈ S ] X ⊆ Y × ¬ (⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ X ]) ⊆ ⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ Y ]))
φNotMonotone₂ a = X₂ , Y₂ , X₂⊆Y₂ , example a
  where example : ∀ a → ¬ (⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ X₂ ]) ⊆ ⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ Y₂ ]))
        example a p with a ≟ a
        example a₁ p₁ | yes p = {!!}
        example a₁ p | no ¬p = refl ↯ ¬p
