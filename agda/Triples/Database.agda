open import Utilities.Logic
open import Relation.Nullary.Decidable
open import Relation.Binary

module Database
  (Atom : Set)
  (X : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqX : DecEq X)
  (eqD : DecEq D)
  (DT : Set)
  (⊢ᵟ_∶_ : D → DT → Set)
  (typeDec : Decidable (⊢ᵟ_∶_))
  where

open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
--open import FiniteSubset renaming (_∪_ to _∪_fs ; _∩_ to _∩_fs) 
open import Data.Sum renaming ( [_,_] to ⟨_,_⟩ )
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool
open import Data.List
open import Induction.WellFounded
open import Induction.Nat
--open import Utilities.ListProperties
open import Data.Empty
--open import FiniteSubsetUtils
open import FinSet

Transition = X × X × (X ⊎ D)

,-inv₁ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} →  ¬ x ≡ y →  ¬ (x , w) ≡ (y , z)
,-inv₁ f refl = f refl

,-inv₂ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} → ¬ w ≡ z →  ¬ (x , w) ≡ (y , z)
,-inv₂ f refl = f refl

inj₁-inv : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {a b : A} → ¬ a ≡ b → ¬ (A ⊎ B ∋ inj₁ a) ≡ inj₁ b
inj₁-inv p refl = p refl

inj₂-inv : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {a b : B} → ¬ a ≡ b → ¬ (A ⊎ B ∋ inj₂ a) ≡ inj₂ b
inj₂-inv p refl = p refl

DecEqPair : {A B : Set} → (eqA : DecEq A) → (eqB : DecEq B) → DecEq (A × B)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) with eqA proj₁ proj₃
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p with eqB proj₂ proj₄
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p₁ | yes p = yes (cong₂ _,_ p₁ p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p | no ¬p = no (,-inv₂ ¬p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | no ¬p = no (,-inv₁ ¬p) 

DecEqSum : {A B : Set} → (eqA : DecEq A) → (eqB : DecEq B) → DecEq (A ⊎ B)
DecEqSum eqA eqB (inj₁ x) (inj₁ x₁) with eqA x x₁
DecEqSum eqA eqB (inj₁ x) (inj₁ x₁) | yes p = yes (cong inj₁ p)
DecEqSum eqA eqB (inj₁ x) (inj₁ x₁) | no ¬p = no (inj₁-inv ¬p)
DecEqSum eqA eqB (inj₁ x) (inj₂ y) = no (λ ())
DecEqSum eqA eqB (inj₂ y) (inj₁ x) = no (λ ())
DecEqSum eqA eqB (inj₂ y) (inj₂ y₁) with eqB y y₁
DecEqSum eqA eqB (inj₂ y) (inj₂ y₁) | yes p = yes (cong inj₂ p)
DecEqSum eqA eqB (inj₂ y) (inj₂ y₁) | no ¬p = no (inj₂-inv ¬p)

eqThird : DecEq (X ⊎ D)
eqThird = DecEqSum eqX eqD

eqTrans : DecEq Transition
eqTrans = DecEqPair eqX (DecEqPair eqX eqThird)

Transitions : Set
Transitions = List Transition

Subjects : Set
Subjects = List X

Objects : Set
Objects = List (X ⊎ D)

Literals : Set
Literals = List D

sub : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → A
sub (o , _ , _) = o

prop : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → B
prop (_ , p , _) = p

obj : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → C
obj (_ , _ , l) = l

uri : X → X ⊎ D
uri = inj₁

lit : D → X ⊎ D
lit = inj₂

∅ : ∀ {ℓ} {C : Set ℓ} → List C
∅ = []

𝓓 : Transitions → Subjects
𝓓 Ξ = Data.List.map sub Ξ

𝓡ₛ : Transitions → Subjects
𝓡ₛ Ξ = foldr (λ x r → ( ⟨ (λ u → [ u ]) , (λ l → []) ⟩ x) ++ r) [] (Data.List.map obj Ξ) 

𝓡ₗ : Transitions → Literals
𝓡ₗ Ξ = foldr (λ x r → ( ⟨ (λ u → []) , (λ l → [ l ]) ⟩ x) ++ r) [] (Data.List.map obj Ξ) 

open import Data.List

any-syntax = any
all-syntax = all

syntax any-syntax (λ x → B) S = ∃[ x ∈ S ] B
syntax all-syntax (λ x → B) S = Π[ x ∈ S ] B

infix 2 any-syntax
infix 2 all-syntax

_⊂_ : (S : List X) → (T : List X) → Set
S ⊂ T = S ⊂⟨ eqX ⟩ T

_⊂?_ : (S : List X) → (T : List X) → Dec (S ⊂ T)
S ⊂? T = S ⊂⟨ eqX ⟩? T

_∈?_ : (x : X) → (L : List X) → Dec (x ∈ L)
x ∈? S = eq2in eqX x S

_∈trans?_ : (x : Transition) → (L : Transitions) → Dec (x ∈ L)
x ∈trans? S = eq2in eqTrans x S

_∪_ : List X → List X → List X
S ∪ T = S ++ T

_∩_ : List X → List X → List X
S ∩ T = ⟪ s ∈ S ∣ ⌊ s ∈? T ⌋ ⟫

_̸_ : List X → List X → List X
S ̸ T = ⟪ s ∈ S ∣ not ⌊ s ∈? T ⌋ ⟫ 
