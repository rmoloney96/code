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

data _∈_  {C : Set} : (x : C) → (L : List C) → Set where
  here : ∀ {x L} → x ∈ (x ∷ L)
  there : ∀ {x y L} → x ∈ L → x ∈ (y ∷ L)

_∉_ : ∀ {C : Set} → C → List C → Set
x ∉ S = x ∈ S → ⊥

eq2in : ∀ {C : Set} → (eq : DecEq C) → (x : C) → (L : List C) → Dec (x ∈ L)
eq2in eq₁ x [] = no (λ ())
eq2in eq₁ x (x₁ ∷ L) with eq2in eq₁ x L
eq2in eq₁ x (x₁ ∷ L) | yes p = yes (there p)
eq2in eq₁ x (x₁ ∷ L) | no ¬p with eq₁ x x₁
eq2in eq₁ x (.x ∷ L) | no ¬p | yes refl = yes here
eq2in eq₁ x (x₁ ∷ L) | no ¬p₁ | no ¬p = no (aux ¬p₁ ¬p)
  where aux : ∀ {C} {x x₁ : C} {L} → x ∉ L → x ≢ x₁ → x ∉ (x₁ ∷ L)
        aux p q here = q refl
        aux p q (there r) = p r

--∈? : ∀ {X} (eq : DecEq X}} (x : X) S → Dec (x ∈ S)
--∈? eq x S = eq2in eq x S

DecIn : ∀ (X : Set) → Set
DecIn X = ∀ (x : X) (L : List X) → Dec (x ∈ L)

data _#_ {C} : C → List C → Set where
  []# : ∀ {x} → x # [] 
  snoc# : ∀ {x y L} → x # L → y ≢ x → x # (y ∷ L)

#? : ∀ {C : Set} (eq : DecEq C) → Decidable (_#_ {C})
#? eq x [] = yes []#
#? eq x₁ (x ∷ L) with #? eq x₁ L 
#? eq x₁ (x ∷ L) | yes p with eq x x₁
#? eq x₁ (.x₁ ∷ L) | yes p₁ | yes refl = no (λ {(snoc# L#x₁ q) → q refl}) 
#? eq x₁ (x ∷ L) | yes p | no ¬p = yes (snoc# p ¬p)
#? eq x₁ (x ∷ L) | no ¬p = no (λ { (snoc# L#x₁ q) → ¬p L#x₁})

∉⇒# : ∀ {C} → (eq : DecEq C) → ∀ xs (x : C) → x ∉ xs → x # xs
∉⇒# eq [] x p = []#
∉⇒# eq (x ∷ xs) x₁ p with eq x₁ x
∉⇒# eq (x ∷ xs) .x p₁ | yes refl = ⊥-elim (p₁ here)
∉⇒# eq (x ∷ xs) x₁ p | no ¬p with ∉⇒# eq xs x₁ (λ z → p (there z))
∉⇒# eq (x ∷ xs) x₁ p | no ¬p | q = snoc# q (¬p ∘ sym)

#-lemma : ∀ {C} → (eq : DecEq C) → ∀ (x y : C) xs → y ∉ xs → y ∈ (x ∷ xs) → x # xs → x ≡ y
#-lemma eq x y xs p q r with ∉⇒# eq xs y p
#-lemma eq y .y xs p here r | res = refl
#-lemma eq x y xs p (there q) r | res = q ↯ p

#-lemma₁ : ∀ {C} → (eq : DecEq C) → ∀ (x y : C) xs → x # xs → (x # (y ∷ xs) → ⊥) → x ≡ y
#-lemma₁ eq x y xs p q with eq x y 
#-lemma₁ eq x .x xs p₁ q | yes refl = refl
#-lemma₁ eq x y xs p q | no ¬p = let h = snoc# p (¬p ∘ sym) in h ↯ q

¬#⇒∈ : ∀ {C} → (eq : DecEq C) → ∀ xs (x : C) → (x # xs → ⊥) → x ∈ xs
¬#⇒∈ eq [] x p = ⊥-elim (p []#)
¬#⇒∈ eq (x ∷ xs) x₁ p with #? eq x₁ xs 
¬#⇒∈ eq (x ∷ xs) x₁ p₁ | yes p with #-lemma₁ eq x₁ x xs p p₁
¬#⇒∈ eq (x ∷ xs) .x p₁ | yes p | refl = here
¬#⇒∈ eq (x ∷ xs) x₁ p | no ¬p with ¬#⇒∈ eq xs x₁ ¬p
¬#⇒∈ eq (x ∷ xs) x₁ p | no ¬p | res = there res

_⊆_ : ∀ {C : Set} (xs ys : List C) → Set
S ⊆ T = ∀ x → x ∈ S → x ∈ T

_⊆⟨_⟩?_ : ∀ {C : Set} (xs : List C) (eq : DecEq C) (ys : List C) → Dec (xs ⊆ ys)
[] ⊆⟨ eq ⟩? T = yes (λ x → λ ())
(x ∷ S) ⊆⟨ eq ⟩? T with S ⊆⟨ eq ⟩? T
(x ∷ S) ⊆⟨ eq ⟩? T | yes p with eq2in eq x T
(x ∷ S) ⊆⟨ eq ⟩? T | yes p₁ | yes p = yes (λ x₁ x₂ → aux p x₂ p₁)
  where aux : ∀ {C : Set} {T S : List C} {x y : C} → x ∈ T → y ∈ (x ∷ S) → S ⊆ T → y ∈ T
        aux P here R = P
        aux P (there Q) R = R _ Q
(x ∷ S) ⊆⟨ eq ⟩? T | yes p | no ¬p = no (λ z → ¬p (z x here))
(x ∷ S) ⊆⟨ eq ⟩? T | no ¬p = no (λ z → ¬p (λ x₁ z₁ → z x₁ (there z₁)))

_≈_ : ∀ {C : Set} (xs ys : List C) → Set
S ≈ T = S ⊆ T × T ⊆ S

data NoDup {C : Set} : List C → Set where
  [] : NoDup []
  _∷_ : ∀ {x L} → x # L → NoDup L → NoDup (x ∷ L)

dedup : ∀ {C : Set} → (eq : DecEq C) → (L : List C) → Σ[ S ∈ List C ] NoDup S
dedup eq [] = [] , []
dedup eq (x ∷ L) with dedup eq L
dedup eq (x ∷ L) | L' , P with #? eq x L'
dedup eq (x ∷ L) | L' , P | yes p = x ∷ L' , p ∷ P
dedup eq (x ∷ L) | L' , P | no ¬p = L' , P

dedup-sound : ∀ {C} → (eq : DecEq C) → ∀ xs y → y ∈ proj₁ (dedup eq xs) → y ∈ xs
dedup-sound eq [] y y∈dedup = y∈dedup
dedup-sound eq (x ∷ xs) y y∈dedup with dedup eq xs | dedup-sound eq xs y
dedup-sound eq (x ∷ xs) y y∈dedup | S , P | Q with #? eq x S
dedup-sound eq (y ∷ xs) .y here | S , P | Q | yes p = here
dedup-sound eq (x ∷ xs) y (there y∈dedup) | S , P | Q | yes p = there (Q y∈dedup)
dedup-sound eq (x ∷ xs) y y∈dedup | S , P | Q | no ¬p = there (Q y∈dedup)

dedup-complete : ∀ {C} → (eq : DecEq C) → ∀ xs y → y ∈ xs → y ∈ proj₁ (dedup eq xs)
dedup-complete eq [] y y∈xs = y∈xs
dedup-complete eq (x ∷ xs) y y∈xs with dedup eq xs | dedup-complete eq xs y 
dedup-complete eq (x ∷ xs) y y∈xs | S , P | Q with #? eq x S
dedup-complete eq (y ∷ xs) .y here | S , P | Q | yes p = here
dedup-complete eq (x ∷ xs) y (there y∈xs) | S , P | Q | yes p = there (Q y∈xs)
dedup-complete eq (y ∷ xs) .y here | S , P | Q | no ¬p = ¬#⇒∈ eq S y ¬p
dedup-complete eq (x ∷ xs) y (there y∈xs) | S , P | Q | no ¬p = Q y∈xs

dedup-≈ : ∀ {C} → ∀ xs (eq : DecEq C) → proj₁ (dedup eq xs) ≈ xs
dedup-≈ xs eq = dedup-sound eq xs , dedup-complete eq xs 

∣_∣⟨_⟩ : {C : Set} → List C → (eq : DecEq C) → ℕ
∣ S ∣⟨ eq ⟩ = length (proj₁ (dedup eq S))

--open import Data.Nat

_≺⟨_⟩_ : {C : Set} → List C → (eq : DecEq C) → List C → Set
S ≺⟨ eq ⟩ T = ∣ S ∣⟨ eq ⟩ <′ ∣ T ∣⟨ eq ⟩

_⊂⟨_⟩_ : {C : Set} → List C → (eq : DecEq C) → List C → Set
S ⊂⟨ eq ⟩ T = S ⊆ T × S ≺⟨ eq ⟩ T

_<?_ : ∀ n m → Dec (n <′ m)
zero <? zero = no (λ ())
zero <? suc m = yes (aux m)
  where aux : ∀ m → zero <′ suc m
        aux zero = ≤′-refl
        aux (suc m₁) = ≤′-step (aux m₁)
suc n <? zero = no (λ ())
suc n <? suc m with n <? m
suc n <? suc m | yes p = yes (n≤m⇒1+n≤1+m _ _ p)
suc n <? suc m | no ¬p = no (λ x → ¬p (1+n≤1+m⇒n≤m (suc n) m x))

_⊂⟨_⟩?_ : {C : Set} → (S : List C) → (eq : DecEq C) → (T : List C) → Dec (S ⊂⟨ eq ⟩ T)
S ⊂⟨ eq ⟩? T with S ⊆⟨ eq ⟩? T | ∣ S ∣⟨ eq ⟩ <? ∣ T ∣⟨ eq ⟩
S ⊂⟨ eq ⟩? T | yes p | yes p₁ = yes (p , p₁)
S ⊂⟨ eq ⟩? T | yes p | no ¬p = no (¬p ∘ proj₂)
S ⊂⟨ eq ⟩? T | no ¬p | res₂ = no (¬p ∘ proj₁)

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
  P ⟶ Q = ∀ {s : C} → T (P s ⇒ Q s)

  BoolImp : ∀ (P Q : C → Bool) → ∀ (s : C) → T (P s ⇒ Q s) → T (P s) → T (Q s)
  BoolImp P Q s Ps⇒Qs Ps with P s | Q s
  BoolImp P Q s Ps⇒Qs () | false | Qs
  BoolImp P Q s () Ps | true | false
  BoolImp P Q s Ps⇒Qs Ps | true | true = tt

  impBool : ∀ (P Q : C → Bool) → ∀ (s : C) → (T (P s) → T (Q s)) → T (P s ⇒ Q s) 
  impBool P Q s Ps⇒Qs with P s | Q s 
  impBool P Q s Ps⇒Qs | false | Qs = tt
  impBool P Q s Ps⇒Qs | true | Qs = Ps⇒Qs tt
  
  ImplicationLawRaw : ∀ (S : List C) → (P Q : C → Bool) → P ⟶ Q → comprehension-raw S P ⊆ comprehension-raw S Q
  ImplicationLawRaw [] P Q imp x ()
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS with imp {x}
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

--  NegationLaw : ∀ {S A B} → A ⊆ S → B ⊆ S → A ⊆ B → (S ̸ A) ⊆ (S ̸ B)
--  NegationLaw {[]} A⊆S B⊆S A⊆B = {!!}
--  NegationLaw {x ∷ S} A⊆S B⊆S A⊆B = {!!}


