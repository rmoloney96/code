--open import Utilities.Logic
open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable

module MuMinus
  (Atom : Set)
  (X : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqX : DecEq X)
  where

open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool hiding (_≟_)
open import Data.List
open import Induction.WellFounded
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import FinSet

import Database as DB
module DBmodule = DB Atom X eqAtom eqX
open DBmodule public

Interpretation : Set
Interpretation = Atom → Subjects

Predicate : Set
Predicate = X → Bool


infixl 21 _⊗_
data Shape : Set where
  v : Atom → Shape
  P : Predicate → Shape
  α[_]_ : (a : X) → Shape → Shape
  _⊗_ : Shape → Shape → Shape
  --_has_ : Shape → ℕ → Shape
  -- Loops
  μ : Atom → Shape → Shape
  -- Negation
  -_ : Shape → Shape


module Positivity where
  module WFAtom = FinSet.WF⊂mod Atom eqAtom
  open WFAtom public
  open import Four

  _∈atom?_ : (x : Atom) → (L : List Atom) → Dec (x ∈ L)
  x ∈atom? S = eq2in eqAtom x S

  _⊸_ : List Atom → Atom → List Atom
  _⊸_ X x = ⟪ y ∈ X ∣ not ⌊ (eqAtom x y) ⌋ ⟫ 

  fvs : Shape → List Atom
  fvs (v x) = [ x ] 
  fvs (P x) = []
  fvs (α[ a ] s) = fvs s
  fvs (s ⊗ s₁) = fvs s ∪ fvs s₁
  fvs (μ x s) = fvs s ⊸ x
  fvs (- s) = fvs s

  polarities : Shape → List Atom × List Atom ⊎ ⊤
  polarities (v x) = inj₁ $ [ x ] , []
  polarities (P x) = inj₁ $ [] , []
  polarities (α[ a ] s) = polarities s
  polarities (s ⊗ s₁) with polarities s | polarities s₁
  polarities (s ⊗ s₁) | inj₁ (p₁ , n₁) | inj₁ (p₂ ,  n₂) = inj₁ $ p₁ ∪ p₂ , n₁ ∪ n₂
  polarities (s ⊗ s₁) | inj₁ x | inj₂ tt = inj₂ tt
  polarities (s ⊗ s₁) | inj₂ tt | res₂ = inj₂ tt 
  polarities (μ x s) with polarities s
  polarities (μ x s) | inj₁ (p , n) with x ∈? n
  polarities (μ x s) | inj₁ (p , n) | yes q = inj₂ tt 
  polarities (μ x s) | inj₁ (p , n) | no ¬q = inj₁ (p ⊸ x , n)
  polarities (μ x s) | inj₂ tt = inj₂ tt
  polarities (- s) with polarities s
  polarities (- s) | inj₁ (p , n) = inj₁ (n , p)
  polarities (- s) | inj₂ y = inj₂ tt

  PositiveClosed : Shape → Set
  PositiveClosed s with polarities s
  PositiveClosed s | inj₁ ([] , []) = ⊤
  PositiveClosed s | inj₁ ([] , x ∷ proj₂) = ⊥
  PositiveClosed s | inj₁ (x ∷ proj₁ , proj₂) = ⊥
  PositiveClosed s | inj₂ y = ⊥

  data Polarity : Shape → List Atom → List Atom → Set where
    Var : ∀ {x} → Polarity (v x) [ x ] []
    Prop : ∀ {p} → Polarity (P p) [] []
    Alpha : ∀ {s a p n} → Polarity s p n → Polarity (α[ a ] s) p n
    And : ∀ {s₁ s₂ p₁ p₂ n₁ n₂} → Polarity s₁ p₁ n₁ → Polarity s₂ p₂ n₂ → Polarity (s₁ ⊗ s₂) (p₁ ∪ p₂) (n₁ ∪ n₂)
    Mu : ∀ {x s p n} → Polarity s p n → x ∉ n → Polarity (μ x s) (p ⊸ x) n
    Not : ∀ {s p n} → Polarity s p n → Polarity (- s) n p
  
  PositiveIn : Atom → Shape → Set
  PositiveIn a s = ∀ {a p n} → a ∉ n → Polarity s p n

module WFX = FinSet.WF⊂mod X eqX
open WFX hiding (NotInUnionLeft ; NotInUnionRight)

mutual

  𝓥 : Predicate → Subjects → Subjects
  𝓥 f S = ⟪ s ∈ S ∣ f s ⟫

  𝓤 : Transitions → Subjects
  𝓤 𝓣 = 𝓓 𝓣 ∪ 𝓡 𝓣 
  
  fpWF : Atom → Shape → Interpretation → (S : Subjects) → Transitions → (Acc _⊂_ S) → Subjects
  fpWF x φ i S 𝓣 a with ⟦ φ ⟧ i S 𝓣
  fpWF x φ i S 𝓣 a | S' with S' ⊂? S
  fpWF x φ i S 𝓣 (acc rs) | S' | yes p = fpWF x φ ((i [ x ≔ S ])) S' 𝓣 (rs S' p)
  fpWF x φ i S 𝓣 a | S' | no ¬p = S

  fp : Atom → Shape → Interpretation → Subjects → Transitions → Subjects
  fp x φ i S 𝓣 = fpWF x φ i S 𝓣 (wf⊂ S)
  
  _[_≔_] : Interpretation → Atom → Subjects → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y

  ⟦_⟧ : Shape → (i : Interpretation) → Subjects → Transitions → Subjects
  ⟦ P p ⟧ i S 𝓣 = 𝓥 p S 
  ⟦ α[ a ] φ ⟧ i S 𝓣 = ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧ i S 𝓣) ⌋ ⟫
  ⟦ φ ⊗ φ₁ ⟧ i S 𝓣 = (⟦ φ ⟧ i S 𝓣) ∩ (⟦ φ₁ ⟧ i S 𝓣)
  ⟦ μ x φ ⟧ i S 𝓣 = fp x φ i S 𝓣
  ⟦ v x ⟧ i S 𝓣 = i x 
  ⟦ - φ ⟧ i S 𝓣 = 𝓤 𝓣 ̸ ⟦ φ ⟧ i S 𝓣

open Positivity

mutual 
  Monotone : ∀ i S 𝓣 X Y {p n} →
    (a : Atom) → (φ : Shape) → a ∉ n → Polarity φ p n → X ⊆ Y →
    ---------------------------------------------------
    ⟦ φ ⟧ (i [ a ≔ X ]) S 𝓣 ⊆ ⟦ φ ⟧ (i [ a ≔ Y ]) S 𝓣
  Monotone i S 𝓣 X Y a (v x) nin pos sub with eqAtom a x
  Monotone i S 𝓣 X Y a (v .a) nin pos sub | yes refl = sub
  Monotone i S 𝓣 X Y a (v x) nin pos sub | no ¬p = λ x₁ z → z
  Monotone i S 𝓣 X Y a (P x) nin pos sub = λ x₁ z → z
  Monotone i S 𝓣 X Y a (α[ a₁ ] s) nin (Alpha pos) sub with Monotone i S 𝓣 X Y a s nin pos sub
  Monotone i S 𝓣 X Y a (α[ a₁ ] s) nin (Alpha pos) sub | res = λ x x₁ → {!!}
  Monotone i S 𝓣 X Y a (s ⊗ s₁) nin (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
    WFX.IntersectionLaw (Monotone i S 𝓣 X Y a s (NotInUnionLeft n₂ nin) pos sub)
                        (Monotone i S 𝓣 X Y a s₁ (NotInUnionRight n₁ nin) pos₁ sub)
  Monotone i S 𝓣 X Y a (μ x s) nin (Mu pos x₁) sub = {!!}
  Monotone i S 𝓣 X Y a (- s) nin (Not pos) sub =
    WFX.NegationLaw (𝓤 𝓣) (Antitone i S 𝓣 X Y a s nin pos sub)
  
  {- A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D -}
  {- A ⊆ B → (S / A) ⊆ (S / B) -}
  
  Antitone : ∀ i S 𝓣 X Y {p n} →
    (a : Atom) → (φ : Shape) → a ∉ p → Polarity φ p n → X ⊆ Y →
    ---------------------------------------------------
    ⟦ φ ⟧ (i [ a ≔ Y ]) S 𝓣 ⊆ ⟦ φ ⟧ (i [ a ≔ X ]) S 𝓣
  Antitone i S 𝓣 X Y a (v x) nip Var sub with eqAtom a x
  Antitone i S 𝓣 X Y x (v .x) nip Var sub | yes refl = ⊥-elim $ nip here
  Antitone i S 𝓣 X Y a (v x) nip Var sub | no ¬p = λ x₁ z → z
  Antitone i S 𝓣 X Y a (P x) nip pos sub = λ x₁ z → z
  Antitone i S 𝓣 X Y a (α[ a₁ ] s) nip pos sub = {!!}
  Antitone i S 𝓣 X Y a (s ⊗ s₁) nip (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
    WFX.IntersectionLaw (Antitone i S 𝓣 X Y a s (NotInUnionLeft p₂ nip) pos sub)
                        (Antitone i S 𝓣 X Y a s₁ (NotInUnionRight p₁ nip) pos₁ sub) 
  Antitone i S 𝓣 X Y a (μ x s) nip pos sub = {!!}
  Antitone i S 𝓣 X Y a (- s) nip (Not pos) sub =
    WFX.NegationLaw (𝓤 𝓣) (Monotone i S 𝓣 X Y a s nip pos sub)
    
--a ⟦ φ ⟧ i S 𝓣  
--Monotonic s f = ?

{-

_⊢_∶_ : Transitions → X → Shape → Set
𝓣 ⊢ x ∶ φ = x ∈ ⟦ φ ⟧ (λ _ → 𝓓 𝓣 ∪ 𝓡 𝓣) (𝓓 𝓣 ∪ 𝓡 𝓣) 𝓣

checkφ : ∀ 𝓣 x φ → Dec ( 𝓣 ⊢ x ∶ φ )
checkφ 𝓣 x φ = x ∈? ⟦ φ ⟧ (λ _ → (𝓓 𝓣 ∪ 𝓡 𝓣)) (𝓓 𝓣 ∪ 𝓡 𝓣) 𝓣

-}
