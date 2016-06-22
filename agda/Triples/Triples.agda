open import Utilities.Logic
open import Relation.Nullary.Decidable
open import Relation.Binary

module Triples
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

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import FiniteSubset renaming (_∪_ to _∪_fs ; _∩_ to _∩_fs) 
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool
open import Data.List
open import Induction.WellFounded

ObjectTriple = X × X × X
DataTriple = X × X × D

,-inv₁ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} →  ¬ x ≡ y →  ¬ (x , w) ≡ (y , z)
,-inv₁ f refl = f refl

,-inv₂ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} →
  ¬ w ≡ z →  ¬ (x , w) ≡ (y , z)
,-inv₂ f refl = f refl

DecEqPair : {A B : Set} → (eqA : DecEq A) → (eqB : DecEq B) → DecEq (A × B)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) with eqA proj₁ proj₃
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p with eqB proj₂ proj₄
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p₁ | yes p = yes (cong₂ _,_ p₁ p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p | no ¬p = no (,-inv₂ ¬p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | no ¬p = no (,-inv₁ ¬p) 

eqObjectTriple : DecEq ObjectTriple
eqObjectTriple = DecEqPair eqX (DecEqPair eqX eqX)

eqDataTriple : DecEq DataTriple
eqDataTriple = DecEqPair eqX (DecEqPair eqX eqD)

Database = FiniteSubSet ObjectTriple eqObjectTriple true × FiniteSubSet DataTriple eqDataTriple true

_∈_obj : ObjectTriple → Database → Set
o ∈ Γ obj = Σ[ e ∈ Element (proj₁ Γ) ] o ≡ proj₁ e

_∈_dat : DataTriple → Database → Set
o ∈ Γ dat = Σ[ e ∈ Element (proj₂ Γ) ] o ≡ proj₁ e

infix 21 _⊕_
infix 21 _⊗_

data Shape : Set where
  α⟨_⟩_ : (a : X) → Shape → Shape
  α[_]_ : (a : X) → Shape → Shape
  ℓ⟨_⟩_ : (a : X) → DT → Shape
  ℓ[_]_ : (a : X) → DT → Shape
  _⊕_ : Shape → Shape → Shape
  _⊗_ : Shape → Shape → Shape
  -- Loops
  ν : Atom → Shape → Shape
  μ : Atom → Shape → Shape
  v : Atom → Shape
  -- Negation
  -_ : Shape → Shape

prop : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → B
prop (_ , p , _) = p

dat : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → C
dat (_ , _ , l) = l

all_∈op_  : X → Database → Database
all p ∈op (objdb , datadb) = (for t ∈ objdb as true
                                 do if ⌊ eqX p (prop t) ⌋ then return {b = true} t  , datadb)

all_∈dp_is_  : X → Database → DT → Database
all p ∈dp (objdb , datadb) is τ = (objdb , for t ∈ datadb as true
                                             do if ⌊ eqX p (prop t) ⌋ ∧ ⌊ typeDec (dat t) τ ⌋ then return {b = true} t)

_∪_ : Database → Database → Database
(proj₁ , proj₂) ∪ (proj₃ , proj₄) = proj₁ ∪ proj₃ fs , proj₂ ∪ proj₄ fs 

_∩_ : Database → Database → Database
(proj₁ , proj₂) ∩ (proj₃ , proj₄) = proj₁ ∩ proj₃ fs , proj₂ ∩ proj₄ fs 

_/_fs : {C : Set}{eq : DecEq C} {b1 b2 : Bool}
  → FiniteSubSet C eq b1 → FiniteSubSet C eq b2
  → FiniteSubSet C eq (b1 ∧ b2) 
_/_fs {C} {eq = _==_} {b1} {b2} U S = for u ∈ U as _ do
                                        for s ∈ S as true do
                                          if not ⌊ u == s ⌋ then return {b = true} u

_/_ : Database → Database → Database
(proj₁ , proj₂) / (proj₃ , proj₄) = (proj₁ / proj₃ fs) , (proj₂ / proj₄ fs)

_≈_ : ∀ {C : Set} {eq : DecEq C} → FiniteSubSet C eq true → FiniteSubSet C eq true → Set
X ≈ Y = (X / Y fs) ≡ mzero × (Y / X fs) ≡ mzero

_⊂_fs : ∀ {C : Set} {eq : DecEq C} → FiniteSubSet C eq true → FiniteSubSet C eq true → Set
S ⊂ T fs = S / T fs ≡ mzero

_⊂_ : Database → Database → Set
(proj₁ , proj₂) ⊂ (proj₃ , proj₄) = (proj₁ ⊂ proj₃ fs) × (proj₂ ⊂ proj₄ fs)

_⊂?_fs : ∀ {C : Set} {eq : DecEq C} → Decidable ((_⊂_fs {C} {eq}))
S ⊂? T fs with S / T fs
S ⊂? T fs | fs-plain [] = yes refl
S ⊂? T fs | fs-plain (x ∷ x₁) = no (λ ())

_⊂?_ : Decidable (_⊂_)
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) with proj₁ ⊂? proj₃ fs | proj₂ ⊂? proj₄ fs
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | yes p | yes p₁ = yes (p , p₁)
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | yes p | no ¬p = no (λ { ( a , b ) → ¬p b})
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | no ¬p | b = no (λ { (a , b) → ¬p a })


Interpretation : Set
Interpretation = Atom → Database

mutual

  -- Need a well foundedness proof here over the relation ⊂ 
  gfp : Atom → Shape → Interpretation → Database → Database → Database
  gfp x φ i T S with ⟦ φ ⟧ i T S
  gfp x φ i T S | T' with T' ⊂? T
  gfp x φ i T S | T' | yes p = ? -- gfp x φ (i [ x ≔ T ]) T' S
  gfp x φ i T S | T' | no ¬p = T
  
  _[_≔_] : Interpretation → Atom → Database → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y

  ⟦_⟧ : Shape → (i : Interpretation) → Database → Database → Database
  ⟦ α⟨ a ⟩ φ ⟧ i Ξ = ⟦ φ ⟧ i (all a ∈op Ξ)
  ⟦ α[ a ] φ ⟧ i Ξ = {!!}
  ⟦ ℓ⟨ a ⟩ τ ⟧ i Ξ _ = all a ∈dp Ξ is τ
  ⟦ ℓ[ a ] x ⟧ i Ξ = {!!}
  ⟦ φ ⊕ φ₁ ⟧ i Ξ S = (⟦ φ ⟧ i Ξ S) ∪ (⟦ φ₁ ⟧ i Ξ S) 
  ⟦ φ ⊗ φ₁ ⟧ i Ξ S = (⟦ φ ⟧ i Ξ S) ∩ (⟦ φ₁ ⟧ i Ξ S) 
  ⟦ ν x φ ⟧ i Ξ S = gfp x φ i S S
  ⟦ μ x φ ⟧ i Ξ = {!!}
  ⟦ v x ⟧ i Ξ S = i x 
  ⟦ - φ ⟧ i Ξ S = S / ⟦ φ ⟧ i Ξ S

  -- Some possible extensions:

  -- Parametric Shapes
  --  Π : Atom → Shape → Shape
  --  _·_ : Shape → Shape → Shape 
  
  -- Finite non-looping recursion
  --  v : Atom → Shape
  --  μ : Atom → Shape → Shape
