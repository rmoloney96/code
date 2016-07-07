
module Utils where

open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect)
open import Data.List
open import Data.Empty

DecEq : ∀ X → Set
DecEq X = Decidable (_≡_ {A = X})

infix 5 _∈_
data _∈_ {a} {A : Set a} : A → List A → Set a where
  here  : ∀ {x}   {xs : List A} → x ∈ (x ∷ xs)
  there : ∀ {x y} {xs : List A} (x∈xs : x ∈ xs) → x ∈ (y ∷ xs)

--infix 5 _∉_
_∉_ : ∀ {a} {A : Set a} → A → List A → Set a
x ∉ xs = x ∈ xs → ⊥ 

∈⇒≡ : ∀ {a} {A : Set a} → {x y : A} → y ∈ (x ∷ []) → y ≡ x
∈⇒≡ here = refl
∈⇒≡ (there ())

≡⇒∈ : ∀ {a} {A : Set a} → {x y : A} → y ≡ x → y ∈ (x ∷ [])
≡⇒∈ refl = here

[]-right-identity : ∀ {a} {C : Set a} → (xs : List C) → xs ++ [] ≡ xs
[]-right-identity [] = refl
[]-right-identity (x ∷ xs) rewrite []-right-identity xs = refl

++-assoc : ∀ {a} {C : Set a} → (xs ys zs : List C) → xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs with ++-assoc xs ys zs
++-assoc (x ∷ xs) ys zs | res = cong₂ _∷_ refl res
