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

lemma↔ₐ-id : ∀ x y → ⟨ x ↔ x ⟩ₐ y ≡ y
lemma↔ₐ-id x y with ⟨ x ↔ x ⟩ₐ y | lemma↔ₐ x x y
lemma↔ₐ-id x .x | .x | inj₁ (refl , refl) = refl
lemma↔ₐ-id x .x | .x | inj₂ (inj₁ (refl , p , refl)) = refl
lemma↔ₐ-id x y | .y | inj₂ (inj₂ (p , q , refl)) = refl

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


¬refl : ∀ {A B : Set} {x : B} → x ≢ x → A
¬refl p = refl ↯ p

{- Not proud of this one! -}
lemma↔ₐ-dist : ∀ x y a b w → ⟨ x ↔ y ⟩ₐ (⟨ a ↔ b ⟩ₐ w) ≡ ⟨ ⟨ x ↔ y ⟩ₐ a ↔ ⟨ x ↔ y ⟩ₐ b ⟩ₐ (⟨ x ↔ y ⟩ₐ w)
lemma↔ₐ-dist x y a b w with ⟨ a ↔ b ⟩ₐ w | lemma↔ₐ a b w
lemma↔ₐ-dist x y a b .a | .b | inj₁ (refl , refl)
  with ⟨ x ↔ y ⟩ₐ b | lemma↔ₐ x y b
lemma↔ₐ-dist b y a .b .a | .b | inj₁ (refl , refl) | .y | inj₁ (refl , refl) with ⟨ b ↔ y ⟩ₐ a | lemma↔ₐ b y a
lemma↔ₐ-dist b y a .b .a | .b | inj₁ (refl , refl) | .y | inj₁ (refl , refl) | g | res rewrite eq-yes g refl = refl
lemma↔ₐ-dist x y a b .a | .b | inj₁ (refl , refl) | f | inj₂ (inj₁ x₁) with ⟨ x ↔ y ⟩ₐ a | lemma↔ₐ x y a
lemma↔ₐ-dist x y a b .a | .b | inj₁ (refl , refl) | f | inj₂ (inj₁ x₁) | g | res rewrite eq-yes g refl = refl
lemma↔ₐ-dist x y a b .a | .b | inj₁ (refl , refl) | f | inj₂ (inj₂ y₁) with ⟨ x ↔ y ⟩ₐ a | lemma↔ₐ x y a
lemma↔ₐ-dist x y a b .a | .b | inj₁ (refl , refl) | f | inj₂ (inj₂ y₁) | g | res rewrite eq-yes g refl = refl
lemma↔ₐ-dist x y a b .b | .a | inj₂ (inj₁ (refl , p , refl)) with ⟨ x ↔ y ⟩ₐ a | lemma↔ₐ x y a
lemma↔ₐ-dist x y a b .b | .a | inj₂ (inj₁ (refl , p , refl)) | g | res with ⟨ x ↔ y ⟩ₐ b | lemma↔ₐ x y b
lemma↔ₐ-dist x y a b .b | .a | inj₂ (inj₁ (refl , p , refl)) | g | res | h | res₂ with ⟨ g ↔ h ⟩ₐ h | lemma↔ₐ g h h
lemma↔ₐ-dist x g .x b .b | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | .g | inj₁ x₂ | .g | inj₁ (refl , refl) = refl
lemma↔ₐ-dist x g .x b .b | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | h | inj₁ x₂ | i | inj₂ (inj₁ (refl , proj₁ , proj₂)) = sym proj₂
lemma↔ₐ-dist x g .x b .b | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | .g | inj₁ (p₂ , refl) | .g | inj₂ (inj₂ (q , r , refl)) = refl
lemma↔ₐ-dist x g .x .g .g | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | .x | inj₂ (inj₁ (refl , q , refl)) | i | inj₁ (s , t) = trans s (sym t)
lemma↔ₐ-dist x g .x .g .g | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | .x | inj₂ (inj₁ (refl , q , refl)) | i | inj₂ (inj₁ (r , s , t)) = sym t
lemma↔ₐ-dist x g .x .g .g | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | .x | inj₂ (inj₁ (refl , q , refl)) | .x | inj₂ (inj₂ (r , s , refl)) = refl ↯ r
lemma↔ₐ-dist x g .x .g .g | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | .g | inj₂ (inj₂ (q , r , refl)) | .g | inj₁ (refl , refl) = refl
lemma↔ₐ-dist x g .x h .h | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | .h | inj₂ (inj₂ (q , r , refl)) | i | inj₂ (inj₁ (s , t , u)) = sym u
lemma↔ₐ-dist x g .x h .h | .x | inj₂ (inj₁ (refl , p , refl)) | .g | inj₁ (refl , refl) | .h | inj₂ (inj₂ (q , r , refl)) | .h | inj₂ (inj₂ (s , t , refl)) = refl ↯ s
lemma↔ₐ-dist x₁ y .y .x₁ .x₁ | .y | inj₂ (inj₁ (refl , p , refl)) | .y | inj₂ (inj₁ (refl , x₃)) | .y | inj₁ (refl , refl) | .y | inj₁ (refl , refl) = refl
lemma↔ₐ-dist x₁ y .y b .b | .y | inj₂ (inj₁ (refl , p , refl)) | g | inj₂ (inj₁ (refl , x₃)) | h | inj₁ x₂ | i | inj₂ (inj₁ (q , r , s)) = sym s
lemma↔ₐ-dist x y .y .x .x | .y | inj₂ (inj₁ (refl , p , refl)) | g | inj₂ (inj₁ (refl , x₂)) | .y | inj₁ (refl , refl) | i | inj₂ (inj₂ (q , r)) = refl ↯ q
lemma↔ₐ-dist g y .y b .b | .y | inj₂ (inj₁ (refl , p , refl)) | .g | inj₂ (inj₁ (refl , q , refl)) | .g | inj₂ res₂ | .g | inj₁ (refl , refl) = refl
lemma↔ₐ-dist g y .y b .b | .y | inj₂ (inj₁ (refl , p , refl)) | .g | inj₂ (inj₁ (refl , q , refl)) | h | inj₂ (inj₁ x₁) | .g | inj₂ (inj₁ (refl , r , refl)) = refl
lemma↔ₐ-dist g y .y .y .y | .y | inj₂ (inj₁ (refl , p , refl)) | .g | inj₂ (inj₁ (refl , q , refl)) | h | inj₂ (inj₁ (refl , proj₁ , proj₂)) | i | inj₂ (inj₂ y₁) = refl ↯ p
lemma↔ₐ-dist g y .y b .b | .y | inj₂ (inj₁ (refl , p , refl)) | .g | inj₂ (inj₁ (refl , q , refl)) | h | inj₂ (inj₂ y₁) | .g | inj₂ (inj₁ (refl , r , refl)) = refl
lemma↔ₐ-dist g y .y b .b | .y | inj₂ (inj₁ (refl , p , refl)) | .g | inj₂ (inj₁ (refl , q , refl)) | h | inj₂ (inj₂ y₂) | i | inj₂ (inj₂ (r , s , t)) = refl ↯ r
lemma↔ₐ-dist x₁ y a b .b | .a | inj₂ (inj₁ (refl , p , refl)) | h | inj₂ (inj₂ y₁) | .h | res₂ | .h | inj₁ (refl , refl) = refl
lemma↔ₐ-dist x₁ y a b .b | .a | inj₂ (inj₁ (refl , p , refl)) | g | inj₂ (inj₂ y₁) | h | res₂ | i | inj₂ (inj₁ (q , r , s)) = sym s
lemma↔ₐ-dist x y₁ a b .b | .a | inj₂ (inj₁ (refl , p , refl)) | g | inj₂ (inj₂ y₂) | h | inj₁ x₁ | .h | inj₂ (inj₂ (r , s , refl)) = refl ↯ r
lemma↔ₐ-dist x y₁ g b .b | .g | inj₂ (inj₁ (refl , p , refl)) | .g | inj₂ (inj₂ (proj₄ , proj₃ , refl)) | h | inj₂ res₂ | .h | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl ↯ proj₁
lemma↔ₐ-dist x y₁ a b w | e | inj₂ (inj₂ y) with ⟨ x ↔ y₁ ⟩ₐ e | lemma↔ₐ x y₁ e
lemma↔ₐ-dist x y₁ a b w | e | inj₂ (inj₂ y) | g | res with ⟨ x ↔ y₁ ⟩ₐ b | lemma↔ₐ x y₁ b
lemma↔ₐ-dist x y₁ a b w | e | inj₂ (inj₂ y) | g | res | h | res₂ with ⟨ x ↔ y₁ ⟩ₐ a | lemma↔ₐ x y₁ a
lemma↔ₐ-dist x y₁ a b w | e | inj₂ (inj₂ y) | g | res | h | res₂ | i | res₃ with ⟨ x ↔ y₁ ⟩ₐ w | lemma↔ₐ x y₁ w
lemma↔ₐ-dist x y₁ a b w | e | inj₂ (inj₂ y) | g | res | h | res₂ | i | res₃ | j | res₄ with ⟨ x ↔ y₁ ⟩ₐ w | lemma↔ₐ x y₁ w
lemma↔ₐ-dist x y₁ a b w | e | inj₂ (inj₂ y) | g | res | h | res₂ | i | res₃ | j | res₄ | k | res₅ with ⟨ i ↔ h ⟩ₐ j | lemma↔ₐ i h j
lemma↔ₐ-dist w y₁ a .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .y₁ | inj₁ (refl , refl) | j | res₃ | .j | res₄ | k | res₅ | .y₁ | inj₁ (refl , refl) = refl
lemma↔ₐ-dist w y₁ a .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , r , refl)) | j | inj₁ (s , t) | .j | res₄ | .y₁ | inj₁ (u , refl) | .w | inj₁ (refl , refl) = sym s ↯ q
lemma↔ₐ-dist w .w .w .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₁ (proj₂ , refl) | .w | inj₁ (proj₁ , refl) | .w | inj₁ (refl , refl) = refl
lemma↔ₐ-dist w .w .w .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₂ (inj₁ (refl , proj₃ , refl)) | .w | inj₂ (inj₁ (refl , x)) | .w | inj₁ (proj₁ , refl) | .w | inj₁ (refl , refl) = refl
lemma↔ₐ-dist w y₁ .y₁ .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , r , refl)) | .w | inj₂ (inj₁ (refl , s , refl)) | .w | inj₂ (inj₂ (t , u , v)) | .y₁ | inj₁ (m , refl) | .w | inj₁ (refl , refl) = refl ↯ u
lemma↔ₐ-dist w y₁ .y₁ .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₆ , refl)) | .y₁ | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .y₁ | inj₁ (proj₂ , refl) | .y₁ | inj₁ (proj₁ , refl) | .w | inj₁ (refl , refl) = refl ↯ proj₄
lemma↔ₐ-dist w y₁ .w .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₇ , refl)) | .w | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₁ (proj₂ , proj₃ , refl)) | .y₁ | inj₁ (proj₁ , refl) | .w | inj₁ (refl , refl) = proj₂ ↯ proj₅
lemma↔ₐ-dist w y₁ .w .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₇ , refl)) | .w | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₂ (proj₂ , proj₃ , refl)) | .y₁ | inj₁ (proj₁ , refl) | .w | inj₁ (refl , refl) = proj₁ ↯ proj₃
lemma↔ₐ-dist w .w a .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₄ , refl)) | j | res₃ | .j | res₄ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) | .w | inj₁ (refl , refl) = refl
lemma↔ₐ-dist w y₁ a .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₄ , refl)) | j | res₃ | .j | res₄ | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | .w | inj₁ (refl , refl) = refl ↯ proj₂
lemma↔ₐ-dist w y₁ .w h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .y₁ | inj₁ (refl , refl) | .y₁ | res₄ | k | res₅ | .h | inj₁ (refl , refl) = refl ↯ q
lemma↔ₐ-dist w y₁ .y₁ h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₁ (refl , proj₃ , refl)) | .w | inj₁ (proj₁ , proj₂) | k | res₅ | .h | inj₁ (refl , refl) = proj₂ ↯ proj₃
lemma↔ₐ-dist w y₁ .y₁ h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .w | inj₂ (inj₁ (refl , proj₂ , refl)) | .w | inj₂ (inj₁ (proj₁ , x)) | k | res₅ | .h | inj₁ (refl , refl) = proj₁ ↯ q
lemma↔ₐ-dist w y₁ .y₁ h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , proj₃)) | k | res₅ | .h | inj₁ (refl , refl) = refl ↯ proj₂
lemma↔ₐ-dist w y₁ .y₁ h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .y₁ | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .y₁ | inj₁ (proj₃ , refl) | .y₁ | inj₁ (proj₁ , refl) | .h | inj₁ (refl , refl) = refl ↯ proj₄ 
lemma↔ₐ-dist w y₁ .y₁ h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .y₁ | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .y₁ | inj₁ (proj₁ , refl) | k | inj₂ res₅ | .h | inj₁ (refl , refl) = refl ↯ proj₃
lemma↔ₐ-dist w .w .w h .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .w | inj₂ (inj₁ (refl , proj₁ , refl)) | k | res₅ | .h | inj₁ (refl , refl) = refl ↯ proj₃
lemma↔ₐ-dist w y₁ .w h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | k | res₅ | .h | inj₁ (refl , refl) = refl ↯ proj₂
lemma↔ₐ-dist w y₁ .w b .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | j | res₂ | .y₁ | inj₁ (refl , refl) | .j | res₄ | k | res₅ | .y₁ | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ q
lemma↔ₐ-dist w y₁ .y₁ .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | j | inj₁ (refl , proj₄) | .w | inj₂ (inj₁ (refl , proj₁ , refl)) | .j | res₄ | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ p
lemma↔ₐ-dist w y₁ .y₁ .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₁ (proj₁ , proj₃) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = sym proj₃
lemma↔ₐ-dist w .w .w .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₆ , refl)) | .w | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₂ (inj₁ (refl , proj₃ , proj₄)) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = refl
lemma↔ₐ-dist w y₁ .y₁ .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₂ (inj₁ (refl , proj₁ , refl)) | .w | inj₂ (inj₂ y) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₂
lemma↔ₐ-dist w y₁ .y₁ .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .y₁ | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₁ (refl , proj₄ , refl)) | .y₁ | inj₁ (proj₁ , refl) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₅ 
lemma↔ₐ-dist w y₁ .y₁ j .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .j | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₁ (refl , proj₃ , refl)) | .j | inj₂ (inj₁ (proj₁ , x)) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁
lemma↔ₐ-dist w y₁ .y₁ .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₃ , refl)) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₂
lemma↔ₐ-dist w y₁ i .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .y₁ | inj₁ (refl , refl) | .i | inj₂ (inj₂ (proj₁ , proj₃ , refl)) | .y₁ | res₄ | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ p
lemma↔ₐ-dist w .w i .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₆ , refl)) | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₁ (proj₁ , refl) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₆
lemma↔ₐ-dist w y₁ i .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₇ , refl)) | .i | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₁ (proj₁ , proj₃ , proj₄)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₃
lemma↔ₐ-dist w y₁ i .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₇ , refl)) | .i | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₃ , proj₄)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₄ ↯ proj₃
lemma↔ₐ-dist w y₁ i .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .y₁ | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .y₁ | inj₁ (proj₁ , refl) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₆
lemma↔ₐ-dist w .w i .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₁ (refl , proj₁ , refl)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₁
lemma↔ₐ-dist w y₁ i .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₂ (proj₇ , proj₈ , refl)) | .i | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₃ , refl)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₃ 
lemma↔ₐ-dist w y₁ a b .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | h | res₂ | i | inj₁ (proj₄ , proj₅) | .y₁ | inj₁ (proj₃ , refl) | k | res₅ | .y₁ | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = sym proj₄ ↯ q
lemma↔ₐ-dist w y₁ a b .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | h | res₂ | i | inj₂ res₃ | .y₁ | inj₁ (proj₃ , refl) | k | res₅ | .y₁ | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl
lemma↔ₐ-dist w y₁ a b .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .y₁ | inj₁ (proj₃ , refl) | i | res₃ | j | inj₂ res₄ | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = sym proj₃ ↯ p
lemma↔ₐ-dist w y₁ a .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₆ , refl)) | i | res₃ | j | inj₂ (inj₁ (proj₃ , proj₄ , proj₅)) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl ↯ proj₄
lemma↔ₐ-dist w y₁ a .y₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₆ , refl)) | i | res₃ | j | inj₂ (inj₂ (proj₃ , proj₄ , proj₅)) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl ↯ proj₄
lemma↔ₐ-dist w y₁ a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | i | res₃ | j | inj₂ (inj₁ (proj₃ , proj₄ , proj₅)) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl ↯ proj₄
lemma↔ₐ-dist w y₁ a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .y₁ | inj₁ (refl , refl) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | i | res₃ | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | k | res₅ | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl ↯ proj₄
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₃ , refl)) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) | .w | inj₁ x₁ | k | res₅ | .w | inj₁ (refl , refl) = proj₁ x₁
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₁ (proj₁ , proj₂ , proj₃)) | k | res₅ | .w | inj₁ (refl , refl) = sym proj₃
lemma↔ₐ-dist w .w .w .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₁ (refl , proj₃ , refl)) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₂ y) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) = refl
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) | .w | inj₂ (inj₂ (proj₁ , proj₂ , proj₃)) | k | inj₂ res₅ | .w | inj₁ (refl , refl) = refl ↯ proj₁ 
lemma↔ₐ-dist x w a .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₃ , refl)) | .w | inj₁ (refl , refl) | j | inj₂ (inj₁ (proj₁ , x₁)) | .j | res₄ | k | res₅ | .w | inj₁ (refl , refl) = sym proj₁ ↯ q
lemma↔ₐ-dist w .w j .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₁ (refl , refl) | .j | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .j | res₄ | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) = refl
lemma↔ₐ-dist x w j .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₇ , refl)) | .w | inj₁ (refl , refl) | .j | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .j | inj₁ (proj₃ , proj₄) | .x | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | .w | inj₁ (refl , refl) = proj₃
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₈ , refl)) | .w | inj₁ (refl , refl) | .x | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .x | inj₂ (inj₁ (proj₃ , proj₄ , refl)) | .x | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | .w | inj₁ (refl , refl) = refl ↯ proj₇ 
lemma↔ₐ-dist x w j .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .w | inj₁ (refl , refl) | .j | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .j | inj₂ (inj₂ (proj₃ , y)) | .x | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | .w | inj₁ (refl , refl) = refl ↯ proj₃
lemma↔ₐ-dist x w j .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₁ (refl , refl) | .j | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .j | inj₁ (proj₁ , proj₂) | k | inj₂ (inj₂ y) | .w | inj₁ (refl , refl) = proj₁
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .w | inj₁ (refl , refl) | .x | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .x | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | k | inj₂ (inj₂ y) | .w | inj₁ (refl , refl) = refl ↯ proj₅
lemma↔ₐ-dist x w j .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₁ (refl , refl) | .j | inj₂ (inj₂ (proj₂ , proj₃ , refl)) | .j | inj₂ (inj₂ (proj₁ , y₁)) | k | inj₂ (inj₂ y) | .w | inj₁ (refl , refl) = refl ↯ proj₁
lemma↔ₐ-dist x w a b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₃ , refl)) | h | inj₂ (inj₁ (proj₁ , x₁)) | j | res₃ | .j | res₄ | k | res₅ | .h | inj₁ (refl , refl) = sym proj₁ ↯ p
lemma↔ₐ-dist x w a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₅ , refl)) | .h | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | j | res₃ | .j | res₄ | k | inj₁ (proj₁ , proj₂) | .h | inj₁ (refl , refl) = proj₁ ↯ proj₅
lemma↔ₐ-dist w .w a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₁ (refl , proj₇ , refl)) | .h | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | res₃ | .w | inj₁ (refl , refl) | .w | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = refl ↯ proj₇
lemma↔ₐ-dist x w a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₉ , refl)) | .h | inj₂ (inj₂ (proj₇ , proj₈ , refl)) | .x | inj₁ (proj₅ , proj₆) | .x | inj₂ (inj₁ (proj₃ , proj₄ , refl)) | .x | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = proj₆ ↯ proj₉
lemma↔ₐ-dist x w a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₈ , refl)) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .x | inj₂ (inj₁ (proj₅ , x₁)) | .x | inj₂ (inj₁ (proj₃ , proj₄ , refl)) | .x | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = sym proj₅ ↯ q
lemma↔ₐ-dist x w .x h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₁₀ , refl)) | .h | inj₂ (inj₂ (proj₈ , proj₉ , refl)) | .x | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .x | inj₂ (inj₁ (proj₃ , proj₄ , refl)) | .x | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = refl ↯ proj₆
lemma↔ₐ-dist x w a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₈ , refl)) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | res₃ | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .x | inj₂ (inj₁ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = refl ↯ proj₃
lemma↔ₐ-dist x w a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .h | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₃ | .j | res₄ | k | inj₂ (inj₂ (proj₁ , proj₂ , proj₃)) | .h | inj₁ (refl , refl) = refl ↯ proj₁
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | j | inj₁ (refl , proj₃) | .w | inj₁ (refl , refl) | .j | res₄ | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = sym proj₃ ↯ proj₂
lemma↔ₐ-dist x w .x b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | j | inj₂ (inj₁ (proj₁ , x₁)) | .w | inj₁ (refl , refl) | .j | res₄ | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = sym proj₁ ↯ p
lemma↔ₐ-dist x w .x j .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .j | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₁ (refl , refl) | .j | inj₁ (proj₁ , proj₃) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁ ↯ q
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₇ , refl)) | .x | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₁ (refl , refl) | .x | inj₂ (inj₁ (proj₁ , proj₃ , refl)) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₆
lemma↔ₐ-dist x w .x j .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₅ , refl)) | .j | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .w | inj₁ (refl , refl) | .j | inj₂ (inj₂ (proj₁ , y)) | k | res₅ | .w | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₁
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) | j | inj₁ (proj₃ , proj₄) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = proj₃ ↯ p
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₇ , refl)) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) | .x | inj₂ (inj₁ (proj₅ , proj₆ , refl)) | k | inj₁ (proj₃ , proj₄) | .x | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = proj₃ ↯ proj₆
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) | .x | inj₂ (inj₁ (proj₃ , proj₄ , refl)) | k | inj₂ res₅ | .x | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl
lemma↔ₐ-dist x w .x .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₁ (refl , refl) | .w | inj₁ (refl , refl) | j | inj₂ (inj₂ (proj₃ , y)) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl ↯ proj₃
lemma↔ₐ-dist x w .x b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₅ , refl)) | h | inj₂ res₂ | .w | inj₁ (refl , refl) | j | inj₁ (proj₃ , proj₄) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = proj₃ ↯ q
lemma↔ₐ-dist x w .x b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₅ , refl)) | h | inj₂ res₂ | .w | inj₁ (refl , refl) | j | inj₂ res₄ | k | inj₁ (proj₃ , proj₄) | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = proj₃ ↯ q
lemma↔ₐ-dist x w .x b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | h | inj₂ (inj₁ (proj₃ , x₁)) | .w | inj₁ (refl , refl) | j | inj₂ res₄ | k | inj₂ res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = sym proj₃ ↯ p
lemma↔ₐ-dist x w .x h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₈ , refl)) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | inj₁ (refl , refl) | .x | inj₂ (inj₁ (proj₃ , proj₄ , refl)) | k | inj₂ res₅ | .x | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl
lemma↔ₐ-dist x w .x h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .h | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₁ (refl , refl) | j | inj₂ (inj₂ (proj₃ , y)) | k | inj₂ res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = refl ↯ proj₃
lemma↔ₐ-dist x w a b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₂ , refl)) | h | res₂ | i | inj₂ (inj₁ (proj₁ , x₁)) | j | res₄ | k | res₅ | l | inj₂ res₆ = sym proj₁ ↯ q
lemma↔ₐ-dist w .w i b .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₁ (refl , proj₆ , refl)) | j | res₂ | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .j | res₄ | .w | inj₁ (refl , refl) | .i | inj₂ (inj₁ (refl , proj₁ , refl)) = refl ↯ proj₆
lemma↔ₐ-dist x w i b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₇ , refl)) | h | res₂ | .i | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | j | res₄ | k | inj₁ (proj₃ , proj₄) | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = proj₃ ↯ proj₇
lemma↔ₐ-dist x w i b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | j | res₂ | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .j | inj₁ (proj₁ , proj₃) | k | inj₂ res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁ ↯ proj₆
lemma↔ₐ-dist x w i .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₇ , refl)) | .w | inj₁ (refl , refl) | .i | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₁ (proj₁ , proj₃ , proj₄)) | k | inj₂ res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym proj₄ ↯ p
lemma↔ₐ-dist x w i .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .w | inj₁ (refl , refl) | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (proj₁ , y)) | k | inj₂ res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₁
lemma↔ₐ-dist x w i b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | j | inj₂ (inj₁ (proj₁ , x₁)) | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .j | inj₂ res₄ | k | inj₂ res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym proj₁ ↯ p
lemma↔ₐ-dist x w i .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₇ , refl)) | .x | inj₂ (inj₂ (proj₁ , proj₃ , refl)) | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .x | inj₂ (inj₁ (s , t , refl)) | k | inj₂ res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ proj₃ 
lemma↔ₐ-dist x w i .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₇ , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₆ , refl)) | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (s , t , refl)) | k | inj₂ res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ s
lemma↔ₐ-dist x w i .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₅ , refl)) | .w | inj₁ (refl , refl) | .i | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | j | inj₁ (proj₁ , proj₂) | k | inj₂ res₅ | .j | inj₂ (inj₂ (s , t , refl)) = proj₁ ↯ p
lemma↔ₐ-dist x w i .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₁ (refl , refl) | .i | inj₂ (inj₂ (proj₂ , proj₃ , refl)) | .x | inj₂ (inj₁ (u , v , refl)) | .x | inj₂ (inj₁ (a , b , refl)) | .x | inj₂ (inj₂ (s , t , refl)) = refl
lemma↔ₐ-dist x w i .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | .w | inj₁ (refl , refl) | .i | inj₂ (inj₂ (proj₂ , proj₃ , refl)) | .x | inj₂ (inj₁ (u , v , refl)) | k | inj₂ (inj₂ y) | .x | inj₂ (inj₂ (s , t , refl)) = refl
lemma↔ₐ-dist x w i .x .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .w | inj₁ (refl , refl) | .i | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | inj₂ (inj₂ (proj₁ , proj₂ , proj₃)) | k | inj₂ res₅ | .j | inj₂ (inj₂ (s , t , refl)) = sym proj₃ ↯ s
lemma↔ₐ-dist x w i b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | h | inj₂ res₂ | .i | inj₂ (inj₂ (proj₂ , proj₃ , refl)) | j | inj₁ (e , f) | k | inj₂ res₅ | .j | inj₂ (inj₂ (s , t , refl)) = e ↯ proj₄
lemma↔ₐ-dist x w i b .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₄ , refl)) | h | inj₂ (inj₁ (e , f , g)) | .i | inj₂ (inj₂ (proj₂ , proj₃ , refl)) | j | inj₂ res₄ | k | inj₂ res₅ | .j | inj₂ (inj₂ (s , t , refl)) = sym e ↯ p
lemma↔ₐ-dist x w i h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .h | inj₂ (inj₂ (proj₁ , proj₄ , refl)) | .i | inj₂ (inj₂ (proj₂ , proj₃ , refl)) | j | inj₂ (inj₁ (e , f , g)) | k | inj₂ res₅ | .j | inj₂ (inj₂ (s , t , refl)) = sym g
lemma↔ₐ-dist x w i h .w | .w | inj₂ (inj₂ (p , q , refl)) | .x | inj₂ (inj₁ (refl , proj₆ , refl)) | .h | inj₂ (inj₂ (proj₁ , proj₄ , refl)) | .i | inj₂ (inj₂ (proj₂ , proj₃ , refl)) | j | inj₂ (inj₂ (f , r)) | k | inj₂ res₅ | .j | inj₂ (inj₂ (s , t , refl)) = refl ↯ f
lemma↔ₐ-dist w j a b .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | h | res₂ | .j | res₃ | .j | inj₁ (refl , refl) | k | res₅ | .h | inj₁ (refl , refl) = refl ↯ proj₄
lemma↔ₐ-dist x₁ h a .x₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .h | inj₁ (refl , refl) | j | res₃ | .j | inj₂ (inj₁ (proj₁ , x)) | k | res₅ | .h | inj₁ (refl , refl) = sym proj₁
lemma↔ₐ-dist x₁ h a .x₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .h | inj₁ (refl , refl) | j | res₃ | .j | inj₂ (inj₂ y) | k | inj₁ (proj₁ , proj₂) | .h | inj₁ (refl , refl) = proj₁ ↯ proj₄
lemma↔ₐ-dist x₁ h a .x₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .h | inj₁ (refl , refl) | j | res₃ | .j | inj₂ (inj₂ y) | k | inj₂ (inj₁ (proj₁ , x)) | .h | inj₁ (refl , refl) = sym proj₁
lemma↔ₐ-dist x₁ h .x₁ .x₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .h | inj₁ (refl , refl) | .h | inj₁ (refl , refl) | .h | inj₂ (inj₂ (e , f , g)) | k | inj₂ (inj₂ y) | .h | inj₁ (refl , refl) = g ↯ proj₃
lemma↔ₐ-dist w h .h .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₇ , proj₈ , refl)) | .h | inj₁ (refl , refl) | .w | inj₂ (inj₁ (refl , proj₃ , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = refl ↯ proj₅
lemma↔ₐ-dist x₁ h w .x₁ .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₈ , proj₉ , refl)) | .h | inj₁ (refl , refl) | .w | inj₂ (inj₂ (proj₃ , proj₆ , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = refl ↯ q
lemma↔ₐ-dist h y₁ a .y₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .h | inj₂ (inj₁ (refl , f , refl)) | j | res₃ | .j | inj₂ res₄ | k | inj₁ (proj₁ , proj₂) | .h | inj₁ (refl , refl) = sym proj₁
lemma↔ₐ-dist h y₁ a .y₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .h | inj₂ (inj₁ (refl , f , refl)) | j | res₃ | .j | inj₂ res₄ | k | inj₂ (inj₁ (proj₁ , x)) | .h | inj₁ (refl , refl) = proj₁ ↯ proj₃
lemma↔ₐ-dist h y₁ a .y₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | .h | inj₂ (inj₁ (refl , f , refl)) | j | res₃ | .j | inj₂ (inj₁ (proj₁ , x)) | k | inj₂ (inj₂ y) | .h | inj₁ (refl , refl) = proj₁ ↯ proj₃
lemma↔ₐ-dist h w a .w .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₇ , proj₈ , refl)) | .h | inj₂ (inj₁ (refl , f , refl)) | .w | inj₁ (proj₃ , refl) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = refl ↯ proj₇
lemma↔ₐ-dist h y₁ a .y₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .h | inj₂ (inj₁ (refl , f , refl)) | .w | inj₂ (inj₁ (o , n , m)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = m
lemma↔ₐ-dist h y₁ a .y₁ w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .h | inj₂ (inj₁ (refl , f , refl)) | .w | inj₂ (inj₂ (o , n , m)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | .h | inj₁ (refl , refl) = sym m ↯ q
lemma↔ₐ-dist x₁ y₁ a h w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .h | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | j | res₃ | .j | inj₂ (inj₁ (o , n , m)) | k | res₅ | .h | inj₁ (refl , refl) = o ↯ proj₄
lemma↔ₐ-dist x₁ w a h .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₇ , proj₈ , refl)) | .h | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₁ (proj₃ , refl) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | k | res₅ | .h | inj₁ (refl , refl) = refl ↯ proj₁
lemma↔ₐ-dist x₁ y₁ a h w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₇ , proj₈ , refl)) | .h | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ res₃ | .w | inj₂ (inj₂ (proj₃ , proj₄ , refl)) | k | inj₁ (proj₁ , proj₂) | .h | inj₁ (refl , refl) = proj₁ ↯ proj₈
lemma↔ₐ-dist x₁ y₁ a h w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₈ , proj₉ , refl)) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | inj₂ res₃ | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | k | inj₂ (inj₁ (proj₁ , proj₂ , proj₃)) | .h | inj₁ (refl , refl) = proj₁ ↯ proj₈
lemma↔ₐ-dist x₁ y₁ a h w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₈ , proj₉ , refl)) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | inj₂ (inj₁ (proj₃ , proj₄ , proj₅)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | k | inj₂ (inj₂ y) | .h | inj₁ (refl , refl) = sym proj₅ ↯ proj₉
lemma↔ₐ-dist x₁ y₁ a h w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₈ , proj₉ , refl)) | .h | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | inj₂ (inj₂ (proj₃ , proj₄ , proj₅)) | .w | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | k | inj₂ (inj₂ y) | .h | inj₁ (refl , refl) = sym proj₅ ↯ q
lemma↔ₐ-dist x₁ i .x₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₂ | .i | inj₁ (refl , refl) | .j | res₄ | .i | inj₁ (proj₁ , refl) | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁ ↯ proj₅
lemma↔ₐ-dist x₁ i .x₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₂ | .i | inj₁ (refl , refl) | .j | res₄ | k | inj₂ (inj₁ (proj₁ , x)) | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁ ↯ proj₄
lemma↔ₐ-dist x₁ i .x₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₂ | .i | inj₁ (refl , refl) | .j | inj₁ (proj₁ , proj₃) | k | inj₂ (inj₂ y) | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁ ↯ proj₅
lemma↔ₐ-dist x₁ i .x₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₂ | .i | inj₁ (refl , refl) | .j | inj₂ (inj₁ (proj₁ , x)) | k | inj₂ (inj₂ y) | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁ ↯ proj₄
lemma↔ₐ-dist x₁ i .x₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | inj₁ (proj₄ , proj₅) | .i | inj₁ (refl , refl) | .w | inj₂ (inj₂ (proj₁ , proj₃ , refl)) | k | inj₂ (inj₂ y) | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym proj₅ ↯ proj₆
lemma↔ₐ-dist x₁ i .x₁ .i w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₆ , proj₇ , refl)) | .w | inj₂ (inj₁ (refl , proj₄ , proj₅)) | .i | inj₁ (refl , refl) | .w | inj₂ (inj₂ (proj₁ , proj₃ , refl)) | k | inj₂ (inj₂ y) | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym proj₅ ↯ q
lemma↔ₐ-dist x₁ i .x₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₂ (e , f , g)) | .i | inj₁ (refl , refl) | .w | inj₂ (inj₂ (proj₁ , proj₃ , refl)) | k | inj₂ (inj₂ y) | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym g ↯ p
lemma↔ₐ-dist i y₁ .y₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₂ | .i | inj₂ (inj₁ (refl , f , refl)) | .j | inj₁ (proj₁ , proj₃) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁ ↯ proj₅
lemma↔ₐ-dist i y₁ .y₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₂ | .i | inj₂ (inj₁ (refl , f , refl)) | .j | inj₂ (inj₁ (proj₁ , x)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = proj₁ ↯ q
lemma↔ₐ-dist i w .w .i .w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₁ (refl , refl) | .i | inj₂ (inj₁ (refl , f , refl)) | .w | inj₂ (inj₂ (o , n , refl)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = refl ↯ o
lemma↔ₐ-dist i y₁ .y₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | .w | inj₂ (inj₁ (proj₁ , proj₃ , proj₄)) | .i | inj₂ (inj₁ (refl , f , refl)) | .w | inj₂ (inj₂ (o , n , refl)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym proj₄ ↯ proj₆
lemma↔ₐ-dist i y₁ .y₁ b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (d , e , g)) | .i | inj₂ (inj₁ (refl , f , refl)) | .w | inj₂ (inj₂ (o , n , refl)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym g ↯ p
lemma↔ₐ-dist x₁ y₁ i b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₂ | .i | inj₂ (inj₂ (e , f , refl)) | .j | inj₁ (o , n) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = o ↯ proj₅
lemma↔ₐ-dist x₁ y₁ i b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | j | res₂ | .i | inj₂ (inj₂ (e , f , refl)) | .j | inj₂ (inj₁ (o , n , m)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = o ↯ proj₄
lemma↔ₐ-dist x₁ y₁ i b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₁ (ε , ν) | .i | inj₂ (inj₂ (e , f , refl)) | .w | inj₂ (inj₂ (o , n , refl)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym ν ↯ proj₄
lemma↔ₐ-dist x₁ y₁ i b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₁ (r , s , t)) | .i | inj₂ (inj₂ (e , f , refl)) | .w | inj₂ (inj₂ (o , n , refl)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym t ↯ proj₅
lemma↔ₐ-dist x₁ y₁ i b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | .w | inj₂ (inj₂ (r , s , t)) | .i | inj₂ (inj₂ (e , f , refl)) | .w | inj₂ (inj₂ (o , n , refl)) | k | res₅ | .i | inj₂ (inj₁ (refl , proj₂ , refl)) = sym t ↯ p
lemma↔ₐ-dist x y₁ a b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₅ , proj₆ , refl)) | h | res₂ | i | res₃ | j | inj₁ (proj₃ , proj₄) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = proj₃ ↯ proj₆
lemma↔ₐ-dist x y₁ a b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | h | res₂ | i | res₃ | j | inj₂ (inj₁ (proj₃ , x₁)) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = proj₃ ↯ proj₄
lemma↔ₐ-dist x y₁ a b w | .w | inj₂ (inj₂ (p , q , refl)) | .w | inj₂ (inj₂ (proj₄ , proj₅ , refl)) | h | res₂ | i | res₃ | j | inj₂ (inj₂ (e , f , g)) | k | res₅ | .j | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = sym g

