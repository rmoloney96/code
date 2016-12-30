open import Utils

module FinSet
  where

open import Data.List
open import Data.Bool
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Nat
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function
open import Data.Unit
open import Data.Sum
open import Membership

open import Induction.WellFounded

ℕ-wf : Well-founded _<′_
ℕ-wf n = acc (aux n)
  where aux : ∀ x y → y <′ x → Acc _<′_ y
        aux .(suc y) y ≤′-refl = ℕ-wf y
        aux .(suc x) y (≤′-step {x} p) = aux x y p 

module WF⊂mod (C : Set) (eq : DecEq C) where

  ∣_∣ : List C → ℕ
  ∣ S ∣ = ∣ S ∣⟨ eq ⟩ 

  open Inverse-image {_<_ = _<′_} (∣_∣) renaming (well-founded to well-founded-ii-obj)
  {- The inverse image of a well founded relation is well founded. -}
 
  _≺_ : List C → List C → Set 
  S ≺ T = S ≺⟨ eq ⟩ T
  
  wf≺ : Well-founded _≺_
  wf≺ = well-founded-ii-obj ℕ-wf

  _⊂_ : List C → List C → Set
  S ⊂ T = S ⊂⟨ eq ⟩ T

  ⊂⇒≺ : ∀ {S T} → S ⊂ T → S ≺ T
  ⊂⇒≺ (proj₁ , proj₂) = proj₂
  
  open Subrelation {_<₁_ = _⊂_} {_<₂_ = _≺_} (⊂⇒≺) renaming (well-founded to well-founded-sub)
  
  wf⊂ : Well-founded _⊂_ 
  wf⊂ = well-founded-sub wf≺

  comprehension-raw : ∀ (S : List C) → (P : C → Bool) → List C
  comprehension-raw [] P = [] 
  comprehension-raw (x ∷ S) P = let l = comprehension-raw S P
                                in if P x then (x ∷ l) else l

  noMore : ∀ {S P x} → x ∈ comprehension-raw S P → x ∈ S
  noMore {[]} incr = incr
  noMore {(x ∷ S)} {P} incr with P x
  noMore {x ∷ S} incr | false = there (noMore incr)
  noMore {x ∷ S} here | true = here
  noMore {x ∷ S} (there incr) | true = there (noMore incr)
  
  comprehension-syntax : ∀ (S : List C) → (P : C → Bool) → List C
  comprehension-syntax S P = proj₁ (dedup eq (comprehension-raw S P))

  syntax comprehension-raw S (λ x → B) = ⟪ x ∈ S ∣ B ⟫

  _⊂?_ : (S : List C) → (T : List C) → Dec (S ⊂ T)
  S ⊂? T = S ⊂⟨ eq ⟩? T

  _∈?_ : (x : C) → (L : List C) → Dec (x ∈ L)
  x ∈? S = eq2in eq x S

  _∪_ : List C → List C → List C
  S ∪ T = ⟪ s ∈ (S ++ T) ∣ true ⟫ 

  _∩_ : List C → List C → List C
  S ∩ T = ⟪ s ∈ S ∣ ⌊ s ∈? T ⌋ ⟫

  _̸_ : List C → List C → List C
  S ̸ T = ⟪ s ∈ S ∣ not ⌊ s ∈? T ⌋ ⟫ 

  InUnionLeft : ∀ {S} S₁ {a} → a ∈ S → a ∈ (S ∪ S₁)
  InUnionLeft {[]} S₁ ()
  InUnionLeft {(a ∷ S)} S₁ here = here
  InUnionLeft {(x ∷ S)} S₁ (there p) = there $ InUnionLeft S₁ p

  InUnionRight : ∀ S {S₁ a} → a ∈ S₁ → a ∈ (S ∪ S₁)
  InUnionRight [] here = here
  InUnionRight [] (there p) = there $ InUnionRight [] p 
  InUnionRight (x ∷ S) p = there $ InUnionRight S p
  
  NotInUnionLeft : ∀ {S : List C} S₁ {a} → a ∉ (S ∪ S₁) → a ∉ S
  NotInUnionLeft {S} S₁ p q = p $ InUnionLeft {S} S₁ q

  NotInUnionRight : ∀ S {S₁ : List C} {a} → a ∉ (S ∪ S₁) → a ∉ S₁
  NotInUnionRight S {S₁} p q = p $ InUnionRight S {S₁} q

  _⟶_ : ∀ (P Q : C → Bool) → Set
  P ⟶ Q = ∀ {s : C} → T (P s) → T (Q s)

  BoolImp : ∀ (P Q : C → Bool) → ∀ (s : C) → T (P s ⇒ Q s) → T (P s) → T (Q s)
  BoolImp P Q s Ps⇒Qs Ps with P s | Q s
  BoolImp P Q s Ps⇒Qs () | false | Qs
  BoolImp P Q s () Ps | true | false
  BoolImp P Q s Ps⇒Qs Ps | true | true = tt

  ImpBool : ∀ (P Q : C → Bool) → ∀ (s : C) → (T (P s) → T (Q s)) → T (P s ⇒ Q s) 
  ImpBool P Q s Ps⇒Qs with P s | Q s 
  ImpBool P Q s Ps⇒Qs | false | Qs = tt
  ImpBool P Q s Ps⇒Qs | true | Qs = Ps⇒Qs tt
  
  ImplicationLawRaw : ∀ (S : List C) → (P Q : C → Bool) → P ⟶ Q → comprehension-raw S P ⊆ comprehension-raw S Q 
  ImplicationLawRaw [] P Q imp x ()
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS with ImpBool P Q x (imp {x})
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS | ix with P x | Q x
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS | ix | false | false = ImplicationLawRaw S P Q imp x₁ inS
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS | ix | false | true = there $ ImplicationLawRaw S P Q imp x₁ inS
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS | () | true | false
  ImplicationLawRaw (x₁ ∷ S) P Q imp .x₁ here | ix | true | true = here
  ImplicationLawRaw (x ∷ S) P Q imp x₁ (there inS) | ix | true | true = there $ ImplicationLawRaw S P Q imp x₁ inS

  ImplicationLaw : ∀ (S : List C) → (P Q : C → Bool) → P ⟶ Q → comprehension-syntax S P ⊆ comprehension-syntax S Q
  ImplicationLaw S P Q imp x inS = dedup-complete eq (comprehension-raw S Q) x (ImplicationLawRaw S P Q imp x (dedup-sound eq (comprehension-raw S P) x inS))

  BothIntersection : ∀ {A B x} → (x ∈ A) → (x ∈ B) → x ∈ (A ∩ B)
  BothIntersection {x ∷ A} {B} here x∈B with x ∈? B
  BothIntersection {x ∷ A} here x∈B | yes p = here
  BothIntersection {x ∷ A} here x∈B | no ¬p = x∈B ↯ ¬p
  BothIntersection {x ∷ A} (there x∈A) x∈B with BothIntersection x∈A x∈B
  BothIntersection {x ∷ A} {B} (there x∈A) x∈B | res with x ∈? B
  BothIntersection {x ∷ A} (there x∈A) x∈B | res | yes p = there res
  BothIntersection {x ∷ A} (there x∈A) x∈B | res | no ¬p = res

  IntersectionBoth : ∀ {A B x} → x ∈ (A ∩ B) → (x ∈ A) × (x ∈ B) 
  IntersectionBoth {[]} ()
  IntersectionBoth {x ∷ A} {B} inboth with x ∈? B
  IntersectionBoth {x ∷ A} here | yes p = here , p
  IntersectionBoth {x ∷ A} (there inboth) | yes p = let x∈A×x∈B = IntersectionBoth {A} inboth
                                                    in there (proj₁ x∈A×x∈B)  , (proj₂ x∈A×x∈B)
  IntersectionBoth {x ∷ A} inboth | no ¬p = let x∈A×x∈B = IntersectionBoth {A} inboth
                                            in there (proj₁ x∈A×x∈B)  , (proj₂ x∈A×x∈B)
  
  --⟪ s ∈ S ∣ ⌊ s ∈? T ⌋ ⟫

  IntersectionLaw : ∀ {A B C D} → A ⊆ B → C ⊆ D → (A ∩ C) ⊆ (B ∩ D)
  IntersectionLaw {A} A⊆B C⊆D x xin =
    let (x∈A , x∈C) = IntersectionBoth {A} xin
    in let x∈B = A⊆B x x∈A
       in let x∈D = C⊆D x x∈C
           in BothIntersection x∈B x∈D 

  LessEmptyIsEmpty : ∀ {A : List C} → A ⊆ [] → A ≡ []
  LessEmptyIsEmpty {[]} p = refl
  LessEmptyIsEmpty {x ∷ A} p with p x here
  LessEmptyIsEmpty {x ∷ A} p | ()

  NegationLaw : ∀ S {A B} → A ⊆ B → (S ̸ B) ⊆ (S ̸ A)
  NegationLaw [] A⊆B x x∈S̸B = x∈S̸B
  NegationLaw (x ∷ S) {A} {B} A⊆B with x ∈? A
  NegationLaw (x ∷ S) {A} {B} A⊆B | yes p with A⊆B x p
  NegationLaw (x ∷ S) {A} {B} A⊆B | yes p | res with x ∈? B
  NegationLaw (x ∷ S) A⊆B | yes p₁ | res | yes p = NegationLaw S A⊆B
  NegationLaw (x ∷ S) A⊆B | yes p | res | no ¬p = res ↯ ¬p
  NegationLaw (x ∷ S) {A} {B} A⊆B | no ¬p with x ∈? B
  NegationLaw (x ∷ S) A⊆B | no ¬p | yes p = λ y y∈S̸B → there $ NegationLaw S A⊆B y y∈S̸B
  NegationLaw (x ∷ S) A⊆B | no ¬p₁ | no ¬p with NegationLaw S A⊆B
  NegationLaw (x ∷ S) A⊆B | no ¬p₁ | no ¬p | res = λ y y∈S̸B → hereOrThere S A⊆B y∈S̸B
    where hereOrThere : ∀ S {A B x y} → A ⊆ B → y ∈ (x ∷ (S ̸ B)) → y ∈ (x ∷ (S ̸ A))
          hereOrThere S A⊆B here = here
          hereOrThere S A⊆B (there y∈S̸B) = there $ NegationLaw S A⊆B _ y∈S̸B

  open import Database C C eq eq

  ImpliesSub : ∀ {A t B s a 𝓣} → A ⊆ B →
      T (⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? A ⌋) → 
      T (⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? B ⌋)
  ImpliesSub {A} {t} A⊆B t∈A with t ∈? A
  ImpliesSub {A} {t} {B} A⊆B t∈A | yes p with t ∈? B
  ImpliesSub A⊆B t∈A | yes p₁ | yes p = t∈A
  ImpliesSub {A} {t} A⊆B t∈A | yes p | no ¬p = ⊥-elim (¬p (A⊆B t p))
  ImpliesSub {A} {t} {B} A⊆B t∈A | no ¬p with t ∈? B
  ImpliesSub {A} {t} {B} {s} {a} {𝓣} A⊆B t∈A | no ¬p | yes p with (s , a , t) ∈trans? 𝓣
  ImpliesSub A⊆B t∈A | no ¬p | yes p₁ | yes p = ⊥-elim t∈A
  ImpliesSub A⊆B t∈A | no ¬p₁ | yes p | no ¬p = tt
  ImpliesSub A⊆B t∈A | no ¬p₁ | no ¬p = t∈A 

  ImpliesAllSub : ∀ {S A B a 𝓣} → A ⊆ B → ∀ {s} → 
     T (Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? A ⌋) → 
     T (Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? B ⌋)
  ImpliesAllSub {[]} A⊆B = λ _ → tt
  ImpliesAllSub {x ∷ S} {A} {B} {a} {𝓣} A⊆B {s} premise with ImpliesSub {A} {x} {B} {s} {a} {𝓣} A⊆B
  ImpliesAllSub {x ∷ S} {A} {B} {a} {𝓣} A⊆B {s} premise | res with ⌊ (s , a , x) ∈trans? 𝓣 ⌋ ⇒ ⌊ x ∈? A ⌋
  ImpliesAllSub {x ∷ S} A⊆B () | res | false
  ImpliesAllSub {x ∷ S} A⊆B premise | res | true with res tt
  ImpliesAllSub {x ∷ S} {A} {B} {a} {𝓣} A⊆B {s} premise | res | true | res₂ with ⌊ (s , a , x) ∈trans? 𝓣 ⌋ ⇒ ⌊ x ∈? B ⌋
  ImpliesAllSub {x ∷ S} A⊆B {s} premise | res | true | () | false
  ImpliesAllSub {x ∷ S} {A} {B} {a} {𝓣} A⊆B {s} premise | res | true | res₂ | true = ImpliesAllSub {S} {A} {B} {a} {𝓣} A⊆B {s} premise

  ComprehensionLaw : ∀ {S A B a} {𝓣 : Transitions} → A ⊆ B →
   ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? A ⌋ ⟫ ⊆
   ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? B ⌋ ⟫
  ComprehensionLaw {S} {A} {B} {a} {𝓣} A⊆B =
     ImplicationLawRaw S (λ s → Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? A ⌋)
                         (λ s → Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? B ⌋)
          (ImpliesAllSub {S} {A} {B} {a} {𝓣} A⊆B) 
  
{- with ImpliesAllSub {x ∷ S} {A} {B} {x} {a} {𝓣} (A⊆B) | Π[ t ∈ (x ∷ S) ] ⌊ (x , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? A ⌋
  ComprehensionLaw {x ∷ S} A⊆B | f | false = λ x₁ x₂ → {!!}
  ComprehensionLaw {x ∷ S} A⊆B | f | true = {!!}  -}
  
-- All subsets are drawn from the bounding set U
--module BoundingSet (C : Set) (eq : DecEq C) (U : List C) where
  
--∀ (S : List C) → (P Q : C → Bool) → P ⟶ Q 
