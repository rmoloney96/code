--open import Utilities.Logic
open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable
open import Level

module Monotonic
  (Atom : Set)
  (C : Set)
  (Atom : Set)
  (eqAtom : DecEq Atom)
  (eqC : DecEq C)
  where

open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool hiding (_≟_)
open import Data.List
open import Induction.WellFounded
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Unit
open import Data.Empty
open import FinSet
open import Membership


import Database as DB
module DBmodule = DB Atom C eqAtom eqC
open DBmodule public

Interpretation : Set
Interpretation = Atom → Subjects

Predicate : Set
Predicate = C → Bool


infixl 21 _⊗_
data Φ : Set where
  v : Atom → Φ
  P : Predicate → Φ
  α[_]_ : (a : C) → Φ → Φ
  _⊗_ : Φ → Φ → Φ
--  _has_ : Φ → ℕ → Φ
  -_ : Φ → Φ


data Φ+ : Set where
  v : Atom → Φ+
  P : Predicate → Φ+
  α[_]_ : (a : C) → Φ+ → Φ+
  _⊗_ : Φ+ → Φ+ → Φ+
  α⟨_⟩⁅_⁆_ : (a : C) → ℕ → Φ+ → Φ+
  -_ : Φ+ → Φ+


module Positivity where
  module WFAtom = FinSet.WF⊂mod Atom eqAtom
  --open WFAtom using (_∪_)

  data Polarity : Φ → List Atom → List Atom → Set where
    Var : ∀ {x} → Polarity (v x) [ x ] []
    Prop : ∀ {p} → Polarity (P p) [] []
    Alpha : ∀ {s a p n} → Polarity s p n → Polarity (α[ a ] s) p n
    And : ∀ {s₁ s₂ p₁ p₂ n₁ n₂} → Polarity s₁ p₁ n₁ → Polarity s₂ p₂ n₂ → Polarity (s₁ ⊗ s₂) (p₁ ∪ p₂) (n₁ ∪ n₂)
    Not : ∀ {s p n} → Polarity s p n → Polarity (- s) n p

  PositiveIn : Atom → Φ → Set
  PositiveIn a s = ∀ {a p n} → Polarity s p n → a ∉ n

  data Polarity+ : Φ+ → List Atom → List Atom → Set where
    Var : ∀ {x} → Polarity+ (v x) [ x ] []
    Prop : ∀ {p} → Polarity+ (P p) [] []
    Alpha : ∀ {s a p n} → Polarity+ s p n → Polarity+ (α[ a ] s) p n
    ExistC : ∀ {s a p n m} → Polarity+ s p n → Polarity+ (α⟨ a ⟩⁅ m ⁆ s) (p ∪ n) (p ∪ n)
    And : ∀ {s₁ s₂ p₁ p₂ n₁ n₂} → Polarity+ s₁ p₁ n₁ → Polarity+ s₂ p₂ n₂ → Polarity+ (s₁ ⊗ s₂) (p₁ ∪ p₂) (n₁ ∪ n₂)
    Not : ∀ {s p n} → Polarity+ s p n → Polarity+ (- s) n p

  PositiveIn+ : Atom → Φ+ → Set
  PositiveIn+ a φ = Σ[ p ∈ List Atom ] Σ[ n ∈ List Atom ] Polarity+ φ p n × a ∉ n

  NegativeIn+ : Atom → Φ+ → Set
  NegativeIn+ a φ = Σ[ p ∈ List Atom ] Σ[ n ∈ List Atom ] Polarity+ φ p n × a ∉ p

  polarity+ : ∀ (φ : Φ+) → Σ[ p ∈ List Atom ] Σ[ n ∈ List Atom ] Polarity+ φ p n
  polarity+ (v x) = x ∷ [] , [] , Var
  polarity+ (P x) = [] , [] , Prop
  polarity+ (α[ a ] φ) with polarity+ φ 
  polarity+ (α[ a ] φ) | (p , n , pφ) = p , n , Alpha pφ
  polarity+ (φ ⊗ φ₁) with polarity+ φ | polarity+ φ₁
  polarity+ (φ ⊗ φ₁) | (p , n , pφ) | (p₁ , n₁ , pφ₁ ) = p ++ p₁ , n ++ n₁ , And pφ pφ₁
  polarity+ (α⟨ a ⟩⁅ x ⁆ φ) with polarity+ φ
  polarity+ (α⟨ a ⟩⁅ x ⁆ φ) | (p , n , pφ) = p ++ n , p ++ n , ExistC pφ
  polarity+ (- φ) with polarity+ φ
  polarity+ (- φ) | (p , n , pφ) = n , p , Not pφ

  PolarityUnique : ∀ {φ p p₁ n n₁} → Polarity+ φ p n → Polarity+ φ p₁ n₁ → n ≈ n₁ × p ≈ p₁
  PolarityUnique Var Var = ((λ x x₁ → x₁) , (λ x x₁ → x₁)) , ((λ x z → z) , (λ x z → z))
  PolarityUnique Prop Prop = ((λ x x₁ → x₁) , (λ x x₁ → x₁)) , ((λ x z → z) , (λ x z → z))
  PolarityUnique (Alpha {φ} pφ) (Alpha {.φ} pφ₁)
    with PolarityUnique pφ pφ₁ 
  PolarityUnique (Alpha {φ} pφ) (Alpha {.φ} pφ₁) | n≈n₁×p≈p₁ = n≈n₁×p≈p₁
  PolarityUnique (ExistC {φ} pφ) (ExistC {.φ} pφ₁) 
    with PolarityUnique pφ pφ₁
  PolarityUnique (ExistC pφ) (ExistC pφ₁) | (n₁⊆n , n⊆n₁) , (p₁⊆p , p⊆p₁)
    = (A⊆B⇒C⊆D⇒A∪C⊆B∪D p₁⊆p n₁⊆n , A⊆B⇒C⊆D⇒A∪C⊆B∪D p⊆p₁ n⊆n₁) ,
      (A⊆B⇒C⊆D⇒A∪C⊆B∪D p₁⊆p n₁⊆n , A⊆B⇒C⊆D⇒A∪C⊆B∪D p⊆p₁ n⊆n₁)
  PolarityUnique (And pφ pφ₁) (And pφ₂ pφ₃)
    with PolarityUnique pφ pφ₂ | PolarityUnique pφ₁ pφ₃
  PolarityUnique (And pφ pφ₁) (And pφ₂ pφ₃)
    | (n₁⊆n , n⊆n₁) , (p₁⊆p , p⊆p₁) | (n₃⊆n₂ , n₂⊆n₃) , (p₃⊆p₂ , p₂⊆p₃)
    = ( A⊆B⇒C⊆D⇒A∪C⊆B∪D n₁⊆n n₃⊆n₂ , A⊆B⇒C⊆D⇒A∪C⊆B∪D n⊆n₁ n₂⊆n₃ ) ,
      ( A⊆B⇒C⊆D⇒A∪C⊆B∪D p₁⊆p p₃⊆p₂ , A⊆B⇒C⊆D⇒A∪C⊆B∪D p⊆p₁ p₂⊆p₃ )
  PolarityUnique (Not pφ) (Not pφ₁) with PolarityUnique pφ pφ₁
  PolarityUnique (Not pφ) (Not pφ₁) | p≈p₁ , n≈n₁ = n≈n₁ , p≈p₁

  isPositiveIn+ : ∀ a φ → Dec (PositiveIn+ a φ)
  isPositiveIn+ a φ  with polarity+ φ 
  isPositiveIn+ a φ | p , n , pφ with eq2in eqAtom a n
  isPositiveIn+ a φ | p , n , pφ | yes q =
    no (λ {(p' , n' , pφ' , ¬q) →
          let (n₁⊆n , n⊆n₁) , (p₁⊆p , p⊆p₁) = PolarityUnique pφ pφ'
          in ¬q (n₁⊆n a q)}) 
  isPositiveIn+ a φ | p , n , pφ | no ¬q = yes (p , n , pφ , ¬q)
  
module ModalTransitionSystem (𝓣 : Transitions) where

  module WFX = FinSet.WF⊂mod C eqC
  open WFX

  _[_≔_] : Interpretation → Atom → Subjects → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y


  𝓢 : Subjects
  𝓢 = 𝓓 𝓣 ∪ 𝓡 𝓣 
  
  𝓥 : Predicate → Subjects
  𝓥 f = ⟪ s ∈ 𝓢 ∣ f s ⟫

  open import Relation C eqC
  
  mutual

    ⟦_⟧ : Φ → (i : Interpretation) → Subjects
    ⟦ P p ⟧ i = 𝓥 p
    ⟦ α[ a ] φ ⟧ i = ⟪ s ∈ 𝓢 ∣ Π[ t ∈ 𝓢 ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧ i) ⌋ ⟫
    ⟦ φ ⊗ φ₁ ⟧ i = (⟦ φ ⟧ i) ∩ (⟦ φ₁ ⟧ i)
    ⟦ v x ⟧ i = i x 
    ⟦ - φ ⟧ i = 𝓢 ̸ ⟦ φ ⟧ i

    ⟦_⟧+ : Φ+ → (i : Interpretation) → Subjects
    ⟦ P p ⟧+ i = 𝓥 p
    ⟦ α[ a ] φ ⟧+ i = ⟪ s ∈ 𝓢 ∣ Π[ t ∈ 𝓢 ] (⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧+ i) ⌋) ⟫
    ⟦ φ ⊗ φ₁ ⟧+ i = (⟦ φ ⟧+ i) ∩ (⟦ φ₁ ⟧+ i)
    ⟦ v x ⟧+ i = i x
    ⟦ α⟨ a ⟩⁅ n ⁆ φ  ⟧+ i = ⟪ s ∈ 𝓢 ∣ ⌊ 𝓒 s (𝓣 ⟨ a ⟩▹ (⟦ φ ⟧+ i)) ≟ℕ n ⌋ ⟫
    ⟦ - φ ⟧+ i = 𝓢 ̸ ⟦ φ ⟧+ i


  open Positivity
  open import MonotonicProperties C eqC
  
  mutual
  
    Monotone : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ) → a ∉ n → Polarity φ p n → X ⊆ Y →
      ---------------------------------------------------
            ⟦ φ ⟧ (i [ a ≔ X ]) ⊆ ⟦ φ ⟧ (i [ a ≔ Y ]) 
    Monotone i X Y a (v x) nin pos sub with eqAtom a x
    Monotone i X Y a (v .a) nin pos sub | yes refl = sub 
    Monotone i X Y a (v x) nin pos sub | no ¬p = λ x₁ z → z
    Monotone i X Y a (P x) nin pos sub = λ x₁ z → z
    Monotone i X Y a (α[ a₁ ] s) nin (Alpha pos) sub =
      α[]-Monotonic {𝓢} {𝓣 = 𝓣} (Monotone i X Y a s nin pos sub)
    Monotone i X Y a (s ⊗ s₁) nin (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      IntersectionLaw (Monotone i X Y a s (NotInUnionLeft n₂ nin) pos sub)
                      (Monotone i X Y a s₁ (NotInUnionRight n₁ nin) pos₁ sub)
    Monotone i X Y a (- s) nin (Not pos) sub =
      NegationLaw 𝓢 (Antitone i X Y a s nin pos sub)
  
    Antitone : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ) → a ∉ p → Polarity φ p n → X ⊆ Y →
      ---------------------------------------------------
      ⟦ φ ⟧ (i [ a ≔ Y ]) ⊆ ⟦ φ ⟧ (i [ a ≔ X ]) 
    Antitone i X Y a (v x) nip Var sub with eqAtom a x
    Antitone i X Y x (v .x) nip Var sub | yes refl = ⊥-elim $ nip here
    Antitone i X Y a (v x) nip Var sub | no ¬p = λ x₁ z → z 
    Antitone i X Y a (P x) nip pos sub = λ x₁ z → z
    Antitone i X Y a (α[ a₁ ] s) nip (Alpha pos) sub =
      α[]-Monotonic {𝓢} {𝓣 = 𝓣} (Antitone i X Y a s nip pos sub)
    Antitone i X Y a (s ⊗ s₁) nip (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      IntersectionLaw (Antitone i X Y a s (NotInUnionLeft p₂ nip) pos sub)
                          (Antitone i X Y a s₁ (NotInUnionRight p₁ nip) pos₁ sub) 
    Antitone i X Y a (- s) nip (Not pos) sub =
      NegationLaw 𝓢 (Monotone i X Y a s nip pos sub)

    Stable+ : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ+) → a ∉ n → a ∉ p → Polarity+ φ p n → ⟦ φ ⟧+ (i [ a ≔ X ]) ≡ ⟦ φ ⟧+ (i [ a ≔ Y ])
    Stable+ i X Y a (v x) nin nip Var with eqAtom a x
    Stable+ i X Y a (v .a) nin nip Var | yes refl = ⊥-elim $ nip here
    Stable+ i X Y a (v x) nin nip Var | no ¬p = refl
    Stable+ i X Y a (P x) nin nip Prop = refl
    Stable+ i X Y a₁ (α[ a ] φ) nin nip (Alpha pol) with Stable+ i X Y a₁ φ nin nip pol
    Stable+ i X Y a₁ (α[ a ] φ) nin nip (Alpha pol) | p rewrite p = refl
    Stable+ i X Y a₁ (α⟨ a ⟩⁅ n ⁆ φ) nin nip (ExistC {_} {_} {p₁} {n₁} pol) with Stable+ i X Y a₁ φ (NotInUnionRight p₁ nip) (NotInUnionLeft n₁ nin) pol
    Stable+ i X Y a₁ (α⟨ a ⟩⁅ n ⁆ φ) nin nip (ExistC {_} {_} {p₁} {n₁} pol) | p rewrite p = refl
    Stable+ i X Y a (φ ⊗ φ₁) nin nip (And {_} {_} {p₁} {p₂} {n₁} {n₂} pol pol₁)
      with Stable+ i X Y a φ (NotInUnionLeft n₂ nin) (NotInUnionLeft p₂ nip ) pol
      | Stable+ i X Y a φ₁ (NotInUnionRight n₁ nin) (NotInUnionRight p₁ nip) pol₁
    Stable+ i X Y a (φ ⊗ φ₁) nin nip (And pol pol₁) | p | q rewrite p | q = refl
    Stable+ i X Y a (- φ) nin nip (Not pol) with Stable+ i X Y a φ nip nin pol
    Stable+ i X Y a (- φ) nin nip (Not pol) | p rewrite p = refl 
    
    Monotone+ : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ+) → a ∉ n → Polarity+ φ p n → X ⊆ Y →
      ---------------------------------------------------
            ⟦ φ ⟧+ (i [ a ≔ X ]) ⊆ ⟦ φ ⟧+ (i [ a ≔ Y ]) 
    Monotone+ i X Y a (v x) nin pos sub with eqAtom a x
    Monotone+ i X Y a (v .a) nin pos sub | yes refl = sub 
    Monotone+ i X Y a (v x) nin pos sub | no ¬p = λ x₁ z → z
    Monotone+ i X Y a (P x) nin pos sub = λ x₁ z → z
    Monotone+ i X Y a (α[ a₁ ] s) nin (Alpha pos) sub =
      α[]-Monotonic {𝓢} {𝓣 = 𝓣} (Monotone+ i X Y a s nin pos sub)
    Monotone+ i X Y a (α⟨ a₁ ⟩⁅ n ⁆ s) nin (ExistC {_} {_} {p₁} {n₁} pos) sub
      with Stable+ i X Y a s (NotInUnionRight p₁ nin) (NotInUnionLeft n₁ nin) pos
    Monotone+ i X Y a (α⟨ a₁ ⟩⁅ n ⁆ s) nin (ExistC {_} {_} {p₁} {n₁} pos) sub | p rewrite p = λ x z → z
    Monotone+ i X Y a (s ⊗ s₁) nin (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      IntersectionLaw (Monotone+ i X Y a s (NotInUnionLeft n₂ nin) pos sub)
                      (Monotone+ i X Y a s₁ (NotInUnionRight n₁ nin) pos₁ sub)
    Monotone+ i X Y a (- s) nin (Not pos) sub =
      NegationLaw 𝓢 (Antitone+ i X Y a s nin pos sub)
  
    Antitone+ : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ+) → a ∉ p → Polarity+ φ p n → X ⊆ Y →
      ---------------------------------------------------
      ⟦ φ ⟧+ (i [ a ≔ Y ]) ⊆ ⟦ φ ⟧+ (i [ a ≔ X ]) 
    Antitone+ i X Y a (v x) nip Var sub with eqAtom a x
    Antitone+ i X Y x (v .x) nip Var sub | yes refl = ⊥-elim $ nip here
    Antitone+ i X Y a (v x) nip Var sub | no ¬p = λ x₁ z → z 
    Antitone+ i X Y a (P x) nip pos sub = λ x₁ z → z
    Antitone+ i X Y a (α[ a₁ ] s) nip (Alpha pos) sub =
      α[]-Monotonic {𝓢} {𝓣 = 𝓣} (Antitone+ i X Y a s nip pos sub)
    Antitone+ i X Y a (α⟨ a₁ ⟩⁅ n ⁆ s) nin (ExistC {_} {_} {p₁} {n₁} pos) sub
      with Stable+ i X Y a s (NotInUnionRight p₁ nin) (NotInUnionLeft n₁ nin) pos
    Antitone+ i X Y a (α⟨ a₁ ⟩⁅ n ⁆ s) nin (ExistC {_} {_} {p₁} {n₁} pos) sub
      | p rewrite p = λ x z → z
    Antitone+ i X Y a (s ⊗ s₁) nip (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      IntersectionLaw (Antitone+ i X Y a s (NotInUnionLeft p₂ nip) pos sub)
                      (Antitone+ i X Y a s₁ (NotInUnionRight p₁ nip) pos₁ sub) 
    Antitone+ i X Y a (- s) nip (Not pos) sub =
      NegationLaw 𝓢 (Monotone+ i X Y a s nip pos sub)


  data νΦ : Set where
    ν : ∀ (a : Atom) (φ : Φ+) → ∀ {_ : T ⌊ isPositiveIn+ a φ ⌋} → νΦ
    νν : ∀ (a : Atom) → νΦ → νΦ

  fixApprox : (Subjects → Subjects) → (S : Subjects) → (Acc _⊂_ S) → Subjects
  fixApprox f X ac with f X
  fixApprox f X ac | S with S ⊂? X
  fixApprox f X (acc rs) | S | yes p = fixApprox f S (rs S p)
  fixApprox f X ac | S | no ¬p = S 
  
  fix : (Subjects → Subjects) → Subjects
  fix f = fixApprox f 𝓢 (wf⊂ 𝓢)

  ⟦_⟧ν : νΦ → Interpretation → Subjects
  ⟦ ν a φ ⟧ν i = fix (λ X → ⟦ φ ⟧+ (i [ a ≔ X ]))
  ⟦ νν a φ ⟧ν i = fix (λ X → ⟦ φ ⟧ν (i [ a ≔ X ]))

  Monotonic : (f : Subjects → Subjects) → Set
  Monotonic f = ∀ {X Y : Subjects} → X ⊆ Y → (f X) ⊆ (f Y)
  
  φ+Monotonic : ∀ {a i} {φ : Φ+} → PositiveIn+ a φ → Monotonic (λ X → ⟦ φ ⟧+ (i [ a ≔ X ])) 
  φ+Monotonic {a} {i} (p , n , pφ , a∉n) {X} {Y} X⊆Y = Monotone+ i X Y a _ a∉n pφ X⊆Y

  InterpBounded : Interpretation → Set
  InterpBounded i = ∀ a → i a ⊆ 𝓢

  BoundedByS : ∀ i φ → InterpBounded i → ⟦ φ ⟧+ i ⊆ 𝓢
  BoundedByS i (v x) iB = iB x
  BoundedByS i (P f) iB = ⟪S∣P⟫⊆S 𝓢 f
  BoundedByS i (α[ a ] φ) iB = ⟪S∣P⟫⊆S 𝓢 _
  BoundedByS i (φ ⊗ φ₁) iB with BoundedByS i φ iB 
  BoundedByS i (φ ⊗ φ₁) iB | φ⊆S = IntersectionLeft φ⊆S
  BoundedByS i (α⟨ a ⟩⁅ x ⁆ φ) iB = ⟪S∣P⟫⊆S 𝓢 _
  BoundedByS i (- φ) iB = ⟪S∣P⟫⊆S 𝓢 _

  _̂_ : (Subjects → Subjects) → ℕ → Subjects → Subjects
  f ̂ ℕ.zero = λ x → x
  f ̂ (ℕ.suc n) = f ∘ (f ̂ n)

  -- f is bounded below S
  _↓_ : (Subjects → Subjects) → Subjects → Set
  f ↓ S = ∀ X → X ⊆ S → f X ⊆ S

  nth-approx-shrinks : ∀ f n → Monotonic f → f ↓ 𝓢 → ((f ̂ (1 + n)) 𝓢) ⊆ ((f ̂ n) 𝓢)
  nth-approx-shrinks f ℕ.zero mf f↓𝓢 = f↓𝓢 𝓢 (λ x z → z)
  nth-approx-shrinks f (ℕ.suc n) mf f↓𝓢 = mf (nth-approx-shrinks f n mf f↓𝓢)


{-
  fDecreases : ∀ f → Monotonic f → ∀ X → (wf : Acc _⊂_ X) → fixApprox f X wf ⊆ X
  fDecreases f mf X wf with f X ⊂? X  
  fDecreases f mf X (acc rs) | yes p with fDecreases f mf (f X) (rs (f X) p)
  fDecreases f mf X (acc rs) | yes p | fX⊆X = λ x x₁ →
    let res = fX⊆X x x₁ in {!!}
  fDecreases f mf X ac | no ¬p = {!let mf !}
  -}
  
--  fixIsGreatest : ∀ f X Y → (g : Y ⊆ 𝓢) → Y ⊆ f X →  

{-
Monotone+ : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ+) → a ∉ n → Polarity+ φ p n → X ⊆ Y →
      ---------------------------------------------------
            ⟦ φ ⟧+ (i [ a ≔ X ]) ⊆ ⟦ φ ⟧+ (i [ a ≔ Y ]) 
    
-}
