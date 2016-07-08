open import Utils
open import Data.Product hiding (map) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality 
open import Data.List
open import Data.Empty

module AtomProperties
  (Atom : Set)
  (eq : DecEq Atom)
  (fresh : (xs : List Atom) → Σ[ y ∈ Atom ] y ∉ xs)
  where

open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Nullary
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

eq-yes : ∀ x {y} (p : x ≡ y) → eq x y ≡ yes p
eq-yes x refl with eq x x
eq-yes x refl | yes refl = refl --refl
eq-yes x refl | no ¬p = refl ↯ ¬p

⟨_↔_⟩ₐ : Atom → Atom → Atom → Atom
⟨ x ↔ y ⟩ₐ z with eq x z
⟨ x ↔ y ⟩ₐ z | yes p = y
⟨ x ↔ y ⟩ₐ z | no ¬p with eq y z
⟨ x ↔ y ⟩ₐ z | no ¬p | yes p = x
⟨ x ↔ y ⟩ₐ z | no ¬p₁ | no ¬p = z

lemma↔ₐ : ∀ x y z → 
  x ≡ z ∧ ⟨ x ↔ y ⟩ₐ z ≡ y ∨
  y ≡ z ∧ x ≢ z ∧ ⟨ x ↔ y ⟩ₐ z ≡ x ∨
  y ≢ z ∧ x ≢ z ∧ ⟨ x ↔ y ⟩ₐ z ≡ z
lemma↔ₐ x y z
    with eq x z
... | yes p = inj₁ (p , refl)
... | no ¬p with eq y z
...         | yes p₁ = inj₂ (inj₁ (p₁ , ¬p , refl))
...         | no ¬p₁ = inj₂ (inj₂ (¬p₁ , ¬p , refl)) 

lemma↔ₐ-x≡z : ∀ x y z → x ≡ z → ⟨ x ↔ y ⟩ₐ z ≡ y
lemma↔ₐ-x≡z x y .x refl
  with lemma↔ₐ x y x
...  | inj₁ (refl , p) = p
...  | inj₂ (inj₁ (p , q , r)) = refl ↯ q
...  | inj₂ (inj₂ (p , q , r)) = refl ↯ q

lemma↔ₐ-y≡z : ∀ x y z → y ≡ z → ⟨ x ↔ y ⟩ₐ z ≡ x
lemma↔ₐ-y≡z x y .y refl with lemma↔ₐ x y y 
lemma↔ₐ-y≡z y .y .y refl | inj₁ (refl , q) = q
lemma↔ₐ-y≡z x y .y refl | inj₂ (inj₁ (p , q , r)) = r
lemma↔ₐ-y≡z x y .y refl | inj₂ (inj₂ (p , q , r)) = refl ↯ p

lemma↔ₐ-y≢z∧x≢z : ∀ x y z → x ≢ z → y ≢ z → ⟨ x ↔ y ⟩ₐ z ≡ z
lemma↔ₐ-y≢z∧x≢z x y z p q
  with lemma↔ₐ x y z
lemma↔ₐ-y≢z∧x≢z x y .x p q | inj₁ (refl , r) = refl ↯ p
lemma↔ₐ-y≢z∧x≢z x y .y p q | inj₂ (inj₁ (refl , s , t)) = refl ↯ q
lemma↔ₐ-y≢z∧x≢z x y z p q | inj₂ (inj₂ (r , s , t)) = t

lemma↔ₐ-a≢x∧a≢y∧a≢z⇒a≢⟨x↔y⟩ₐz : ∀ x y z a → a ≢ x → a ≢ y → a ≢ z → a ≢ ⟨ x ↔ y ⟩ₐ z
lemma↔ₐ-a≢x∧a≢y∧a≢z⇒a≢⟨x↔y⟩ₐz x y z a a≢x a≢y a≢z with ⟨ x ↔ y ⟩ₐ z | lemma↔ₐ x y z
lemma↔ₐ-a≢x∧a≢y∧a≢z⇒a≢⟨x↔y⟩ₐz x y .x a a≢x a≢y a≢z | .y | inj₁ (refl , refl) = a≢y
lemma↔ₐ-a≢x∧a≢y∧a≢z⇒a≢⟨x↔y⟩ₐz x y .y a a≢x a≢y a≢z | .x | inj₂ (inj₁ (refl , r , refl)) = a≢x
lemma↔ₐ-a≢x∧a≢y∧a≢z⇒a≢⟨x↔y⟩ₐz x y z a a≢x a≢y a≢z | .z | inj₂ (inj₂ (q , r , refl)) = a≢z 

lemma↔ₐ-invol : ∀ x y z → ⟨ x ↔ y ⟩ₐ (⟨ x ↔ y ⟩ₐ z) ≡ z
lemma↔ₐ-invol x y z with ⟨ x ↔ z ⟩ₐ  (⟨ x ↔ z ⟩ₐ z) | lemma↔ₐ x y (⟨ x ↔ y ⟩ₐ z)
lemma↔ₐ-invol x y z | c | inj₁ (p , q) with ⟨ x ↔ y ⟩ₐ z | lemma↔ₐ x y z
lemma↔ₐ-invol x y .x | c | inj₁ (p , q) | d | inj₁ (refl , r) = trans q (trans (sym r) (sym p))
lemma↔ₐ-invol x y z | c | inj₁ (p , q) | d | inj₂ (inj₁ (r , s , t)) = trans q r
lemma↔ₐ-invol x y z | c | inj₁ (p , q) | d | inj₂ (inj₂ (r , s , t)) = trans p t ↯ s
lemma↔ₐ-invol x y z | c | inj₂ (inj₁ (p , q , r)) with ⟨ x ↔ y ⟩ₐ z | lemma↔ₐ x y z
lemma↔ₐ-invol x y z | c | inj₂ (inj₁ (refl , q , r)) | .y | inj₁ (s , t) = trans r s
lemma↔ₐ-invol x .x .x | c | inj₂ (inj₁ (refl , q , r)) | .x | inj₂ (inj₁ (refl , v , refl)) = r
lemma↔ₐ-invol x y .y | c | inj₂ (inj₁ (refl , q , r)) | .y | inj₂ (inj₂ (u , v , refl)) = refl ↯ u 
lemma↔ₐ-invol x y z | c | inj₂ (inj₂ (p , q , r)) with ⟨ x ↔ y ⟩ₐ z | lemma↔ₐ x y z
lemma↔ₐ-invol x y .x | c | inj₂ (inj₂ (p , q , r)) | .y | inj₁ (refl , refl) = refl ↯ p
lemma↔ₐ-invol x y .y | c | inj₂ (inj₂ (p , q , r)) | .x | inj₂ (inj₁ (refl , v , refl)) = refl ↯ q
lemma↔ₐ-invol x y z | c | inj₂ (inj₂ (p , q , r)) | .z | inj₂ (inj₂ (u , v , refl)) = r

lemma↔ₐ-comm : ∀ x y z → ⟨ x ↔ y ⟩ₐ z ≡ ⟨ y ↔ x ⟩ₐ z
lemma↔ₐ-comm x y z with ⟨ x ↔ y ⟩ₐ z | lemma↔ₐ x y z
lemma↔ₐ-comm x y .x | .y | inj₁ (refl , refl) =  sym (lemma↔ₐ-y≡z y x x refl)
lemma↔ₐ-comm x y .y | .x | inj₂ (inj₁ (refl , p , refl)) = sym (lemma↔ₐ-x≡z y x y refl)
lemma↔ₐ-comm x y z | .z | inj₂ (inj₂ (q , r , refl)) = sym (lemma↔ₐ-y≢z∧x≢z y x z q r)

lemma↔ₐ-cancel : ∀ x y z w → w ≢ y → w ≢ z → ⟨ z ↔ y ⟩ₐ (⟨ x ↔ z ⟩ₐ w) ≡ ⟨ x ↔ y ⟩ₐ w
lemma↔ₐ-cancel x y z w w≢y w≢x
  with eq x w
... | yes p rewrite eq-yes x refl | eq-yes z refl = refl
... | no _ with eq z w 
...        | yes z≡w = sym z≡w ↯ w≢x
...        | no ¬p with eq z w
...                | yes p = p ↯ ¬p
...                | no _ with eq y w
...                       | yes y≡w = sym y≡w ↯ w≢y
...                       | no _ = refl
