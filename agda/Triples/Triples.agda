open import Utilities.Logic

module Triples
  (Atom : Set)
  (X : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqX : DecEq X)
  (eqD : DecEq D)
  where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import FiniteSubset
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool

Triple = X × X × (X ⊎ D)

,-inv1 : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} →  ¬ x ≡ y →  ¬ (x , w) ≡ (y , z)
,-inv1 f refl = f refl

,-inv2 : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} {x y : A} {w z : B} {r s : C} →
  ¬ w ≡ z →  ¬ (x , w , r) ≡ (y , z , s)
,-inv2 f refl = f refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl

,-inv3-inj1 : ∀ {ℓ m} {X : Set ℓ} {D : Set m} {a b c d : X} {p q : X × D} → ¬ proj₁ p ≡ proj₁ q → ¬ (a , b , p) ≡ (c , d , q)
,-inv3-inj1 f refl = f refl

_at_ : ∀ (A : Set) → A → A
A at x = x

third1 : ∀ {a b c d e f : X} → (a , b , (X ⊎ D ∋ inj₁ c)) ≡ (d , e , (X ⊎ D ∋ inj₁ f)) → c ≡ f
third1 refl = refl

third1-2 : ∀ {a b c d e : X} {f : D} → ¬ (a , b , (X ⊎ D ∋ inj₁ c)) ≡ (d , e , (X ⊎ D ∋ inj₂ f))
third1-2 ()

third2-1 : ∀ {a b d e f : X} {c : D} → ¬ (a , b , (X ⊎ D ∋ inj₂ c)) ≡ (d , e , (X ⊎ D ∋ inj₁ f))
third2-1 ()

third2 : ∀ {a b d e : X} {c f : D} → (a , b , (X ⊎ D ∋ inj₂ c)) ≡ (d , e , (X ⊎ D ∋ inj₂ f)) → c ≡ f
third2 refl = refl

EqTriple : DecEq Triple
EqTriple (proj₁ , proj₂) (proj₃ , proj₄) with eqX proj₁ proj₃
EqTriple (proj₁ , proj₂ , proj₄) (proj₃ , proj₅ , proj₆) | yes p with eqX proj₂ proj₅
EqTriple (proj₁ , proj₂ , inj₁ x) (proj₃ , proj₅ , inj₁ x₁) | yes p₁ | yes p with eqX x x₁
EqTriple (proj₁ , proj₂ , inj₁ x) (proj₃ , proj₅ , inj₁ x₁) | yes p₂ | yes p₁ | yes p = yes (cong₂ _,_ p₂ (cong₂ _,_ p₁ (cong inj₁ p)))
EqTriple (proj₁ , proj₂ , inj₁ x) (proj₃ , proj₅ , inj₁ x₁) | yes p₁ | yes p | no ¬p = no (¬p ∘ third1)
EqTriple (proj₁ , proj₂ , inj₁ x) (proj₃ , proj₅ , inj₂ y) | yes p₁ | yes p = no third1-2
EqTriple (proj₁ , proj₂ , inj₂ y) (proj₃ , proj₅ , inj₁ x) | yes p₁ | yes p = no third2-1
EqTriple (proj₁ , proj₂ , inj₂ y) (proj₃ , proj₅ , inj₂ y₁) | yes p₁ | yes p with eqD y y₁
EqTriple (proj₁ , proj₂ , inj₂ y) (proj₃ , proj₅ , inj₂ y₁) | yes p₂ | yes p₁ | yes p = yes (cong₂ _,_ p₂ (cong₂ _,_ p₁ (cong inj₂ p)))
EqTriple (proj₁ , proj₂ , inj₂ y) (proj₃ , proj₅ , inj₂ y₁) | yes p₁ | yes p | no ¬p = no (¬p ∘ third2)
EqTriple (proj₁ , proj₂ , proj₄) (proj₃ , proj₅ , proj₆) | yes p | no ¬p = no (,-inv2 ¬p)
EqTriple (proj₁ , proj₂) (proj₃ , proj₄) | no ¬p = no (,-inv1 ¬p)

--_==_ : DecEq Triple
--x == y = EqTriple x y

Database = FiniteSubSet Triple EqTriple false

infix 21 _⊕_
infix 21 _⊗_

data Shape : Set where
  v : Atom → Shape
  μ : Atom → Shape → Shape
  α⟨_⟩_ : X → Shape → Shape
  ℓ⟨_⟩_ : X → D → Shape
  _⊕_ : Shape → Shape → Shape
  _⊗_ : Shape → Shape → Shape
  
--_∈_ : ∀ t → Γ → {e : Element Γ} → Set
--t ∈ Γ = proj₁ e ≡ t

--test : ∀ x A → x ∈ A
--test x A = {!!}

data _⊢_∶_ : Database → X → Shape → Set₁ where
 I⊕ₗ : ∀ {Γ s τ σ} → Γ ⊢ s ∶ σ → Γ ⊢ s ∶ σ ⊕ τ
 I⊕ᵣ : ∀ {Γ s τ σ} → Γ ⊢ s ∶ τ → Γ ⊢ s ∶ σ ⊕ τ
 I⊗ : ∀ {Γ s τ σ} → Γ ⊢ s ∶ σ → Γ ⊢ s ∶ τ → Γ ⊢ s ∶ σ ⊗ τ
 Ia : ∀ {Γ t p σ} → (e : Element Γ) →   → Γ ⊢ proj₁ e ∶ σ → Γ ⊢ t ∶ (α⟨ p ⟩ σ)
