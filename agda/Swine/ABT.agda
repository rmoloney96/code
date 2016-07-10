open import Utils
open import Data.Product hiding (map) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality 
open import Data.List
open import Data.Empty

module ABT
  (Atom : Set)
  (eq : DecEq Atom)
  (fresh : (xs : List Atom) → Σ[ y ∈ Atom ] y ∉ xs)
  where

import AtomProperties as AP
module AtomModule = AP Atom eq fresh
open AtomModule public

open import Relation.Nullary
--open import Data.Vec
open import Data.Nat
open import Data.Unit hiding (_≟_)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Relation.Binary
open import Function
open import Data.Sum renaming (_⊎_ to ∨)


Arity : Set
Arity = List ℕ 

data Code : Set where
  c : Atom → Code

infix 22 _·_

data Abt : Set where
  name : Atom → Abt
  oper : (op : Code) → (α : Arity) → (abts : List Abt) → Abt
  _·_ : (x : Atom) → (a : Abt) → Abt

Signature : Set
Signature = List (Code ∧ Arity)

data _∈_sig : Code → Signature → Set where
  here : ∀ {Γ x} → (α : Arity) → x ∈ (x , α) ∷ Γ sig
  there : ∀ {x y α Γ} → x ∈ Γ sig → x ∈ (y , α) ∷ Γ sig

findArity : ∀ {x Γ} → x ∈ Γ sig → Arity
findArity (here α) = α
findArity (there p) = findArity p

valence : Abt → ℕ 
valence (name x) = 0
valence (oper x α x₁) = 0
valence (x · a) = 1 + (valence a)

arity : Abt → Arity
arity (name x) = []
arity (oper x α x₁) = α
arity (x · x₁) = (valence (x · x₁)) ∷ []

open import Data.List.All hiding (map)

data _#_ : Atom → Abt → Set where
  name# : ∀ {x y} → x ≢ y → x # (name y)
  oper# : ∀ {x op α abts} → All (x #_) abts → x # (oper op α abts)
  x·x# : ∀ {x a} →  x # (x · a)
  x·y# : ∀ {x y a} → x ≢ y → x # a → x # (y · a)

inv-x#name : ∀ {x} → ¬ (x # name x)
inv-x#name (name# x₁) = refl ↯ x₁ 

inv-x#oper : ∀ {x op α abts} → x # oper op α abts → All (_#_ x) abts
inv-x#oper (oper# x₁) = x₁

inv-All#₁ : ∀ {x a abts} → All (_#_ x) (a ∷ abts) → x # a
inv-All#₁ (px ∷ p) = px

inv-All#₂ : ∀ {x a abts} → All (_#_ x) (a ∷ abts) → All (x #_) abts
inv-All#₂ (px ∷ p) = p

inv-x#bind : ∀ {x y a} → x ≢ y → x # (y · a) → x # a
inv-x#bind x≢y x·x# = refl ↯ x≢y
inv-x#bind x≢y (x·y# x₁ p) = p

mutual
 _#s?_ : ∀ x → (abts : List Abt) → Dec (All (x #_) abts)
 x #s? [] = yes []
 x #s? (x₁ ∷ abts) with x #? x₁
 x #s? (x₁ ∷ abts) | yes p with x #s? abts
 x #s? (x₁ ∷ abts) | yes p₁ | yes p = yes (p₁ ∷ p)
 x #s? (x₁ ∷ abts) | yes p | no ¬p = no (¬p ∘ inv-All#₂)
 x #s? (x₁ ∷ abts) | no ¬p = no (¬p ∘ inv-All#₁)
 
 _#?_ : Decidable (_#_)
 x #? name x₁ with eq x x₁
 x #? name .x | yes refl = no inv-x#name
 x #? name x₁ | no ¬p = yes (name# ¬p)
 x #? oper op α abts with x #s? abts
 x #? oper op α abts | yes p = yes (oper# p)
 x #? oper op α abts | no ¬p = no (¬p ∘ inv-x#oper)
 x #? (y · a) with eq x y
 x #? (.x · a) | yes refl = yes x·x#
 x #? (y · a) | no ¬p with x #? a
 x #? (y · a) | no ¬p | yes p = yes (x·y# ¬p p)
 x #? (y · a) | no ¬p₁ | no ¬p = no (¬p ∘ (inv-x#bind ¬p₁))

mutual
 ⟨_↔_⟩ₗ : Atom → Atom → List Abt → List Abt
 ⟨ x ↔ y ⟩ₗ [] = []
 ⟨ x ↔ y ⟩ₗ (x₁ ∷ xs) = ⟨ x ↔ y ⟩ x₁ ∷ ⟨ x ↔ y ⟩ₗ xs

 ⟨_↔_⟩ : Atom → Atom → Abt → Abt 
 ⟨ x ↔ y ⟩ (name z) = name (⟨ x ↔ y ⟩ₐ z)
 ⟨ x ↔ y ⟩ (oper op α abts) = oper op α (⟨ x ↔ y ⟩ₗ abts)
 ⟨ x ↔ y ⟩ (z · a) = (⟨ x ↔ y ⟩ₐ z) · ⟨ x ↔ y ⟩ a

_─_ : List Atom → Atom → List Atom
[] ─ x = []
(x ∷ xs) ─ x₁ with eq x x₁
(x ∷ xs) ─ .x | yes refl = xs ─ x
(x ∷ xs) ─ x₁ | no ¬p = x ∷ xs ─ x₁

mutual

 fvs : List Abt → List Atom 
 fvs [] = []
 fvs (x ∷ abts) = fvs abts ++ fv x
 
 fv : Abt → List Atom 
 fv (name x) = x ∷ []
 fv (oper op α abts) = fvs abts
 fv (x · a) = (fv a) ─ x

mutual
 data _≈αs_ : List Abt → List Abt → Set where
   []≈αs : [] ≈αs []
   ∷≈αs : ∀ {x y abts₁ abts₂} →
   
     x ≈α y → abts₁ ≈αs abts₂ →
     ---------------------------
     (x ∷ abts₁) ≈αs (y ∷ abts₂)
   
 data _≈α_ : Abt → Abt → Set where
   name≈α : ∀ {x} → name x ≈α name x
   oper≈α : ∀ {op α abts₁ abts₂} →
   
            abts₁ ≈αs abts₂ →
     ----------------------------------
     oper op α abts₁ ≈α oper op α abts₂

   bindx≈xα : ∀ {x abt₁ abt₂} →

            abt₁ ≈α abt₂ →
         ------------------------
           x · abt₁ ≈α x · abt₂

   bindx≈yα : ∀ {x y abt₁ abt₂} →

         x ≢ y → y # abt₁ → ⟨ x ↔ y ⟩ abt₁ ≈α abt₂ →
         --------------------------------------------
                 x · abt₁ ≈α y · abt₂

--open import Relation.Nullary.Decidable

inv-name : ∀ {x y} → name x ≈α name y → x ≡ y
inv-name name≈α = refl

inv-∷α₁ : ∀ {x y xs ys} → (x ∷ xs) ≈αs (y ∷ ys) → x ≈α y
inv-∷α₁ (∷≈αs x₁ p) = x₁

inv-∷α₂ : ∀ {x y xs ys} → (x ∷ xs) ≈αs (y ∷ ys) → xs ≈αs ys
inv-∷α₂ (∷≈αs x₁ p) = p

inv-∷₁ : ∀ {C : Set} {x y : C} {xs ys} → (_≡_ {_} {List C} (x ∷ xs) (y ∷ ys)) → x ≡ y
inv-∷₁ refl = refl

inv-∷₂ : ∀ {C : Set} {x y : C} {xs ys} → (_≡_ {_} {List C} (x ∷ xs) (y ∷ ys)) → xs ≡ ys
inv-∷₂ refl = refl

inv-oper₁ : ∀ {x y α β abts abts₁} → oper (c x) α abts ≈α oper (c y) β abts₁ → x ≡ y
inv-oper₁ (oper≈α x) = refl

inv-oper₂ : ∀ {x y α β abts abts₁} → oper (c x) α abts ≈α oper (c y) β abts₁ → α ≡ β
inv-oper₂ (oper≈α x) = refl

inv-oper₃ : ∀ {x y α β abts abts₁} → oper (c x) α abts ≈α oper (c y) β abts₁ → abts ≈αs abts₁
inv-oper₃ (oper≈α x) = x

inv-·₁ : ∀ {x y a b} → x ≢ y → (x · a) ≈α (y · b) → ⟨ x ↔ y ⟩ a ≈α b
inv-·₁ np (bindx≈xα q) =  refl ↯ np
inv-·₁ np (bindx≈yα x₁ x₂ q) = q

inv-·₂ : ∀ {x a b} → (x · a) ≈α (x · b) → a ≈α b 
inv-·₂ (bindx≈xα p) = p
inv-·₂ (bindx≈yα x≢x x₂ p) = refl ↯ x≢x

inv-·₃ : ∀ {x y a b} → x ≢ y → (x · a) ≈α (y · b) → y # a
inv-·₃ p (bindx≈xα q) = refl ↯ p
inv-·₃ p (bindx≈yα x₁ x₂ q) = x₂

_≟arity_ : (x : Arity) → (y : Arity) → Dec (x ≡ y)
[] ≟arity [] = yes refl
[] ≟arity (x ∷ y) = no (λ ())
(x ∷ x₁) ≟arity [] = no (λ ())
(x ∷ xs) ≟arity (y ∷ ys) with x ≟ y
(x ∷ xs) ≟arity (y ∷ ys) | yes p with xs ≟arity ys
(x ∷ xs) ≟arity (y ∷ ys) | yes p₁ | yes p = yes (cong₂ _∷_ p₁ p)
(x ∷ xs) ≟arity (y ∷ ys) | yes p | no ¬p = no (¬p ∘ inv-∷₂)
(x ∷ xs) ≟arity (y ∷ ys) | no ¬p = no (¬p ∘ inv-∷₁)

mutual
  _≈αs?_ : Decidable (_≈αs_)
  [] ≈αs? [] = yes []≈αs
  [] ≈αs? (x ∷ ys) = no (λ ())
  (x ∷ xs) ≈αs? [] = no (λ ())
  (x ∷ xs) ≈αs? (x₁ ∷ ys) with x ≈α? x₁
  (x ∷ xs) ≈αs? (x₁ ∷ ys) | yes p with xs ≈αs? ys
  (x ∷ xs) ≈αs? (x₁ ∷ ys) | yes p₁ | yes p = yes (∷≈αs p₁ p)
  (x ∷ xs) ≈αs? (x₁ ∷ ys) | yes p | no ¬p = no (¬p ∘ inv-∷α₂)
  (x ∷ xs) ≈αs? (x₁ ∷ ys) | no ¬p =  no ((¬p ∘ inv-∷α₁))
  
  _≈α?_ : Decidable (_≈α_)
  name x ≈α? name x₁ with eq x x₁
  name x ≈α? name .x | yes refl = yes name≈α
  name x ≈α? name x₁ | no ¬p = no (¬p ∘ inv-name)
  name x ≈α? oper op α abts = no (λ ())
  name x ≈α? (x₁ · y) = no (λ ())
  oper op α abts ≈α? name x = no (λ ())
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ with eq x x₁
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | yes p with α ≟arity α₁
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | yes p₁ | yes p with abts ≈αs? abts₁
  oper (c x) α abts ≈α? oper (c .x) .α abts₁ | yes refl | yes refl | yes p = yes (oper≈α p)
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | yes p₁ | yes p | no ¬p = no (¬p ∘ inv-oper₃)
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | yes p | no ¬p = no (¬p ∘ inv-oper₂)
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | no ¬p = no (¬p ∘ inv-oper₁)
  oper op α abts ≈α? (x · y) = no (λ ())
  (x · a) ≈α? name x₂ = no (λ ())
  (x · a) ≈α? oper op α abts = no (λ ())
  (x · a) ≈α? (y · b) with eq x y
  (x · a) ≈α? (y · b) | yes p with a ≈α? b
  (x · a) ≈α? (.x · b) | yes refl | yes p = yes (bindx≈xα p)
  (x · a) ≈α? (.x · b) | yes refl | no ¬p = no (¬p ∘ inv-·₂)
  (x · a) ≈α? (y · b) | no ¬p with ⟨ x ↔ y ⟩ a ≈α? b 
  (x · a) ≈α? (y · b) | no ¬p | yes p with y #? a
  (x · a) ≈α? (y · b) | no ¬p | yes p₁ | yes p = yes (bindx≈yα ¬p p p₁)
  (x · a) ≈α? (y · b) | no ¬p₁ | yes p | no ¬p = no (¬p ∘ inv-·₃ ¬p₁)
  (x · a) ≈α? (y · b) | no ¬p₁ | no ¬p = no (¬p ∘ inv-·₁ ¬p₁)

{-
Now lives in AtomProperties

⟨x↔y⟩ₐx≈αy : ∀ x y → name (⟨ x ↔ y ⟩ₐ x) ≈α name y
⟨x↔y⟩ₐx≈αy x y with eq x x
⟨x↔y⟩ₐx≈αy x y | yes p = name≈α
⟨x↔y⟩ₐx≈αy x y | no ¬p = refl ↯ ¬p

⟨x↔y⟩ₐz≈αz : ∀ x y z → x ≢ z → y ≢ z → name (⟨ x ↔ y ⟩ₐ z) ≈α name z
⟨x↔y⟩ₐz≈αz x y z x≢z y≢z with eq x z
⟨x↔y⟩ₐz≈αz x y .x x≢z y≢z | yes refl = refl ↯ x≢z
⟨x↔y⟩ₐz≈αz x y z x≢z y≢z | no ¬p with eq y z
⟨x↔y⟩ₐz≈αz x y .y x≢z y≢z | no ¬p | yes refl = refl ↯ y≢z
⟨x↔y⟩ₐz≈αz x y z x≢z y≢z | no ¬p₁ | no ¬p = name≈α
-}

mutual
  ≈αs-refl : ∀ {x} → x ≈αs x
  ≈αs-refl {[]} = []≈αs
  ≈αs-refl {x ∷ x₁} = ∷≈αs ≈α-refl ≈αs-refl
 
  ≈α-refl : ∀ {x} → x ≈α x
  ≈α-refl {name x} = name≈α
  ≈α-refl {oper op α abts} = oper≈α  ≈αs-refl
  ≈α-refl {x · x₁} = bindx≈xα {x} {x₁} ≈α-refl

x·a≈αy·⟨x↔y⟩a : ∀ x y a → x ≢ y → y # a → x · a ≈α y · ⟨ x ↔ y ⟩ a
x·a≈αy·⟨x↔y⟩a x y (name x₁) x≢y (name# x₂) with eq x x₁
x·a≈αy·⟨x↔y⟩a x₁ y (name _) x≢y (name# x₂) | yes p = bindx≈yα x≢y (name# x₂) {!!} -- (lemma↔ₐ-x≡z x₁ y x₁ refl)
x·a≈αy·⟨x↔y⟩a x y (name x₁) x≢y (name# x₂) | no ¬p with eq y x₁
x·a≈αy·⟨x↔y⟩a x x₁ (name .x₁) x≢y (name# x₂) | no ¬p | yes refl = refl ↯ x₂
x·a≈αy·⟨x↔y⟩a x y (name x₁) x≢y (name# x₂) | no ¬p₁ | no ¬p = bindx≈yα x≢y (name# x₂) {!!} -- (lemma↔ₐ-y≢z∧x≢z ?)
x·a≈αy·⟨x↔y⟩a x y (oper op α abts) x≢y y#a = bindx≈yα x≢y y#a (oper≈α ≈αs-refl)
x·a≈αy·⟨x↔y⟩a x y (z · a) x≢y y#a = bindx≈yα x≢y y#a ≈α-refl

{-
⟨x↔y⟩x≈αy : ∀ x y → name (⟨ x ↔ y ⟩ₐ x) ≈α name y
⟨x↔y⟩x≈αy x y with eq x x
⟨x↔y⟩x≈αy x y | yes refl = name≈α
⟨x↔y⟩x≈αy x y | no ¬p = refl ↯ ¬p

⟨x↔y⟩ₐx≡y : ∀ x y → ⟨ x ↔ y ⟩ₐ x ≡ y
⟨x↔y⟩ₐx≡y x y with eq x y
⟨x↔y⟩ₐx≡y x y | yes p with eq x x
⟨x↔y⟩ₐx≡y x y | yes p₁ | yes p = refl
⟨x↔y⟩ₐx≡y x y | yes p | no ¬p = refl ↯ ¬p
⟨x↔y⟩ₐx≡y x y | no ¬p with eq x x
⟨x↔y⟩ₐx≡y x y | no ¬p | yes p = refl
⟨x↔y⟩ₐx≡y x y | no ¬p₁ | no ¬p = refl ↯ ¬p

⟨x↔y⟩z≈αz : ∀ x y z → z ≢ x → z ≢ y → name (⟨ x ↔ y ⟩ₐ z) ≈α name z
⟨x↔y⟩z≈αz x y z z≢x z≢y with eq x z
⟨x↔y⟩z≈αz x y z z≢x z≢y | yes p = sym p ↯ z≢x
⟨x↔y⟩z≈αz x y z z≢x z≢y | no ¬p with eq y z
⟨x↔y⟩z≈αz x y z z≢x z≢y | no ¬p | yes p = sym p ↯ z≢y
⟨x↔y⟩z≈αz x y z z≢x z≢y | no ¬p₁ | no ¬p = name≈α

-}

mutual
  ⟨x↔x⟩ₗabts : ∀ x abts → ⟨ x ↔ x ⟩ₗ abts ≡ abts
  ⟨x↔x⟩ₗabts x [] = refl
  ⟨x↔x⟩ₗabts x (a ∷ abts) rewrite ⟨x↔x⟩a≡a x a | ⟨x↔x⟩ₗabts x abts = refl
  
  ⟨x↔x⟩a≡a : ∀ x a → ⟨ x ↔ x ⟩ a ≡ a
  ⟨x↔x⟩a≡a x (name x₁) with eq x x₁
  ⟨x↔x⟩a≡a x (name .x) | yes refl = refl
  ⟨x↔x⟩a≡a x (name x₁) | no ¬p with eq x x₁
  ⟨x↔x⟩a≡a x (name x₁) | no ¬p | yes p = p ↯ ¬p
  ⟨x↔x⟩a≡a x (name x₁) | no ¬p₁ | no ¬p = refl
  ⟨x↔x⟩a≡a x (oper op α abts) rewrite ⟨x↔x⟩ₗabts x abts = refl
  ⟨x↔x⟩a≡a x (x₁ · a) with eq x x₁
  ⟨x↔x⟩a≡a x (.x · a) | yes refl rewrite ⟨x↔x⟩a≡a x a = refl
  ⟨x↔x⟩a≡a x (x₁ · a) | no ¬p with eq x x₁
  ⟨x↔x⟩a≡a x (.x · a) | no ¬p | yes refl rewrite ⟨x↔x⟩a≡a x a = refl
  ⟨x↔x⟩a≡a x (x₁ · a) | no ¬p₁ | no ¬p rewrite ⟨x↔x⟩a≡a x a = refl

⟨↔⟩ₐ-invol : ∀ x y z → ⟨ x ↔ z ⟩ₐ (⟨ x ↔ z ⟩ₐ y) ≡ y
⟨↔⟩ₐ-invol x y z with eq x y
⟨↔⟩ₐ-invol x y z | yes p with eq x z
⟨↔⟩ₐ-invol x y z | yes p₁ | yes p = trans (sym p) p₁
⟨↔⟩ₐ-invol x y z | yes p | no ¬p with eq z z
⟨↔⟩ₐ-invol x y z | yes p₁ | no ¬p | yes p = p₁
⟨↔⟩ₐ-invol x y z | yes p | no ¬p₁ | no ¬p = refl ↯ ¬p
⟨↔⟩ₐ-invol x y z | no ¬p with eq z y
⟨↔⟩ₐ-invol x y z | no ¬p | yes p with eq x x
⟨↔⟩ₐ-invol x y z | no ¬p | yes p₁ | yes p = p₁
⟨↔⟩ₐ-invol x y z | no ¬p₁ | yes p | no ¬p with eq z x
⟨↔⟩ₐ-invol x .x .x | no ¬p₁ | yes refl | no ¬p | yes refl = refl
⟨↔⟩ₐ-invol x y z | no ¬p₂ | yes p | no ¬p₁ | no ¬p = refl ↯ ¬p₁
⟨↔⟩ₐ-invol x y z | no ¬p₁ | no ¬p with eq x y
⟨↔⟩ₐ-invol x y z | no ¬p₁ | no ¬p | yes p = p ↯ ¬p₁
⟨↔⟩ₐ-invol x y z | no ¬p₂ | no ¬p₁ | no ¬p with eq z y
⟨↔⟩ₐ-invol x y z | no ¬p₂ | no ¬p₁ | no ¬p | yes p = p ↯ ¬p₁
⟨↔⟩ₐ-invol x y z | no ¬p₃ | no ¬p₂ | no ¬p₁ | no ¬p = refl


mutual
  ⟨↔⟩ₗ-invol : ∀ x z abts → ⟨ x ↔ z ⟩ₗ (⟨ x ↔ z ⟩ₗ abts) ≡ abts
  ⟨↔⟩ₗ-invol x z [] = refl
  ⟨↔⟩ₗ-invol x z (a ∷ abts) rewrite ⟨↔⟩-invol x z a | ⟨↔⟩ₗ-invol x z abts = refl
  
  ⟨↔⟩-invol : ∀ x z a → ⟨ x ↔ z ⟩ (⟨ x ↔ z ⟩ a) ≡ a
  ⟨↔⟩-invol x z (name x₁) rewrite ⟨↔⟩ₐ-invol x x₁ z = refl
  ⟨↔⟩-invol x z (oper op α abts) rewrite ⟨↔⟩ₗ-invol x z abts = refl
  ⟨↔⟩-invol x z (x₁ · a)
   rewrite ⟨↔⟩ₐ-invol x z x₁
         | ⟨↔⟩-invol x z a with eq x x₁
  ⟨↔⟩-invol x z (x₁ · a) | yes p with eq x z
  ⟨↔⟩-invol x .x (.x · a) | yes refl | yes refl = refl
  ⟨↔⟩-invol x z (x₁ · a) | yes p | no ¬p with eq z z
  ⟨↔⟩-invol x z (.x · a) | yes refl | no ¬p | yes p₁ = refl
  ⟨↔⟩-invol x z (x₁ · a) | yes p | no ¬p | no ¬p₁ = refl ↯ ¬p₁
  ⟨↔⟩-invol x z (x₁ · a) | no ¬p with eq z x₁
  ⟨↔⟩-invol x z (.z · a) | no ¬p | yes refl rewrite eq-yes x refl = refl
  ⟨↔⟩-invol x z (x₁ · a) | no ¬p | no ¬p₁ with eq x x₁
  ⟨↔⟩-invol x z (x₁ · a) | no ¬p | no ¬p₁ | yes p = p ↯ ¬p
  ⟨↔⟩-invol x z (x₁ · a) | no ¬p₂ | no ¬p₁ | no ¬p with eq z x₁
  ⟨↔⟩-invol x z (x₁ · a) | no ¬p₂ | no ¬p₁ | no ¬p | yes p₃ = p₃ ↯ ¬p₁
  ⟨↔⟩-invol x z (x₁ · a) | no ¬p₂ | no ¬p₁ | no ¬p | no ¬p₃ = refl

mutual
  ⟨↔⟩ₗ-comm : ∀ x y abts → ⟨ x ↔ y ⟩ₗ abts ≡ ⟨ y ↔ x ⟩ₗ abts
  ⟨↔⟩ₗ-comm x y [] = refl
  ⟨↔⟩ₗ-comm x y (x₁ ∷ abts)
    rewrite ⟨↔⟩-comm x y x₁
          | ⟨↔⟩ₗ-comm x y abts = refl
  
  ⟨↔⟩-comm : ∀ x y a → ⟨ x ↔ y ⟩ a ≡ ⟨ y ↔ x ⟩ a
  ⟨↔⟩-comm x y (name x₁) rewrite lemma↔ₐ-comm x y x₁ = refl
  ⟨↔⟩-comm x y (oper op α abts) rewrite ⟨↔⟩ₗ-comm x y abts = refl
  ⟨↔⟩-comm x y (x₁ · a) with ⟨ x ↔ y ⟩ₐ x₁ | lemma↔ₐ x y x₁
  ⟨↔⟩-comm x y (.x · a) | .y | inj₁ (refl , refl) with eq y x
  ⟨↔⟩-comm y .y (.y · a) | .y | inj₁ (refl , refl) | yes refl = refl
  ⟨↔⟩-comm x y (.x · a) | .y | inj₁ (refl , refl) | no ¬p
    rewrite eq-yes x refl
          | ⟨↔⟩-comm x y a = refl
  ⟨↔⟩-comm x y (.y · a) | .x | inj₂ (inj₁ (refl , p , refl))
    rewrite eq-yes y refl
          | ⟨↔⟩-comm x y a = refl
  ⟨↔⟩-comm x y (x₁ · a) | .x₁ | inj₂ (inj₂ (p , q , refl)) with eq y x₁
  ⟨↔⟩-comm x x₁ (.x₁ · a) | .x₁ | inj₂ (inj₂ (p₁ , q , refl)) | yes refl = refl ↯ p₁
  ⟨↔⟩-comm x y (x₁ · a) | .x₁ | inj₂ (inj₂ (p , q , refl)) | no ¬p with eq x x₁
  ⟨↔⟩-comm x₁ y (.x₁ · a) | .x₁ | inj₂ (inj₂ (p₁ , q , refl)) | no ¬p | yes refl = refl ↯ q 
  ⟨↔⟩-comm x y (x₁ · a) | .x₁ | inj₂ (inj₂ (p , q , refl)) | no ¬p₁ | no ¬p
    rewrite ⟨↔⟩-comm x y a = refl
  
mutual
  ⟨↔⟩ₗ-id : ∀ x abts → ⟨ x ↔ x ⟩ₗ abts ≡ abts
  ⟨↔⟩ₗ-id x [] = refl
  ⟨↔⟩ₗ-id x (a ∷ abts) rewrite ⟨↔⟩-id x a | ⟨↔⟩ₗ-id x abts = refl

  ⟨↔⟩-id : ∀ x a → ⟨ x ↔ x ⟩ a ≡ a
  ⟨↔⟩-id x (name x₁) rewrite lemma↔ₐ-id x x₁ = refl
  ⟨↔⟩-id x (oper op α abts) rewrite ⟨↔⟩ₗ-id x abts = refl
  ⟨↔⟩-id x (x₁ · a)
    rewrite lemma↔ₐ-id x x₁
          | ⟨↔⟩-id x a = refl


mutual
  ⟨↔⟩-cancel : ∀ x y z a → z ≢ y → z ≢ x → z # a → y # ⟨ x ↔ z ⟩ a → ⟨ z ↔ y ⟩ (⟨ x ↔ z ⟩ a) ≡ a
  ⟨↔⟩-cancel x y z (name x₁) z≢y z≡x (name# x₂) (name# x₃) with ⟨ x ↔ z ⟩ₐ x₁ | lemma↔ₐ x z x₁
  ⟨↔⟩-cancel x₁ y z (name .x₁) z≢y z≡x (name# x₃) (name# x₄) | .z | inj₁ (refl , refl) rewrite eq-yes z refl = {!!}
  ⟨↔⟩-cancel x y z (name x₁) z≢y z≡x (name# x₂) (name# x₃) | e | inj₂ res = {!!}
  ⟨↔⟩-cancel x y z (oper op α abts) z≢y z≡x z#a z#⟨x↔z⟩a = {!!}
  ⟨↔⟩-cancel x y z (x₁ · a) z≢y z≡x z#a z#⟨x↔z⟩a = {!!}

  -- ? rewrite lemma↔ₐ-cancel x y z x₁ {!!} (x₂ ∘ sym) = {!!} -- rewrite lemma↔ₐ-cancel x y z x₁ = {!!}
mutual

  ⟨x↔y⟩ℓa≈αsb⇒All[y#] : ∀ x y abts abts₁ → x ≢ y → All (y #_) abts → ⟨ x ↔ y ⟩ₗ abts ≈αs abts₁ → All (_#_ x) abts₁
  ⟨x↔y⟩ℓa≈αsb⇒All[y#] x y .[] .[] x≢y [] []≈αs = []
  ⟨x↔y⟩ℓa≈αsb⇒All[y#] x₁ y _ _ x≢y (px ∷ Ally#) (∷≈αs x₂ a≈b) = (⟨x↔y⟩a≈αb⇒x#b x₁ _ _ _ x≢y px x₂) ∷ ⟨x↔y⟩ℓa≈αsb⇒All[y#] x₁ y _ _ x≢y Ally# a≈b
  
  ⟨x↔y⟩a≈αb⇒x#b : ∀ x y a b → x ≢ y → y # a → ⟨ x ↔ y ⟩ a ≈α b → x # b
  ⟨x↔y⟩a≈αb⇒x#b x y _ (name x₁) x≢y (name# {_} {y₂} x₂) a≈b with ⟨ x ↔ y ⟩ₐ y₂ | lemma↔ₐ x y y₂
  ⟨x↔y⟩a≈αb⇒x#b y x₁ .(name y) (name .x₁) x≢y (name# x₃) name≈α | .x₁ | inj₁ (refl , refl) = name# x≢y
  ⟨x↔y⟩a≈αb⇒x#b x y .(name y) (name x₁) x≢y (name# x₃) name≈α | .x₁ | inj₂ (inj₁ (refl , x₂)) = refl ↯ x₃
  ⟨x↔y⟩a≈αb⇒x#b x y₁ .(name y) (name y) x≢y (name# x₂) name≈α | .y | inj₂ (inj₂ (proj₁ , proj₂ , refl)) = name# proj₂
  ⟨x↔y⟩a≈αb⇒x#b x y _ (oper op α abts) x≢y (name# x₁) ()
  ⟨x↔y⟩a≈αb⇒x#b x y _ (x₁ · b) x≢y (name# x₂) ()
  ⟨x↔y⟩a≈αb⇒x#b x y _ (name x₁) x≢y (oper# x₂) ()
  ⟨x↔y⟩a≈αb⇒x#b x y _ (oper op α₁ abts₁) x≢y (oper# x₁) (oper≈α x₂) = oper# (⟨x↔y⟩ℓa≈αsb⇒All[y#] x y _ abts₁ x≢y x₁ x₂) -- oper# {!!}
  ⟨x↔y⟩a≈αb⇒x#b x y _ (x₁ · b) x≢y (oper# x₂) ()
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y x·x# (bindx≈xα a≈b) with eq x y
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y x·x# (bindx≈xα a≈b) | yes p = p ↯ x≢y
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y x·x# (bindx≈xα a≈b) | no ¬p rewrite eq-yes y refl = x·x#
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y x·x# (bindx≈yα x₁ x₂ a≈b) with eq x y
  ⟨x↔y⟩a≈αb⇒x#b y .y _ _ x≢y x·x# (bindx≈yα x₁ x₂ a≈b) | yes refl = refl ↯ x≢y
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·x# {_} {a}) (bindx≈yα {_} {w} x₁ x₂ a≈b) | no ¬p 
     rewrite eq-yes y refl = x·y# x₁ (⟨x↔y⟩a≈αb⇒x#b x w (⟨ x ↔ y ⟩ a) _ x₁ x₂ a≈b)
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {y₁} x₁ y#a) (bindx≈xα a≈b) with eq x y₁
  ⟨x↔y⟩a≈αb⇒x#b x y₁ _ _ x≢y (x·y# x₁ y#a) (bindx≈xα a≈b) | yes refl = x·y# x≢y (⟨x↔y⟩a≈αb⇒x#b x y₁ _ _ x≢y y#a a≈b)
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {y₁} x₁ y#a) (bindx≈xα a≈b) | no ¬p with eq y y₁ 
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# x₁ y#a) (bindx≈xα a≈b) | no ¬p | yes refl = x·x#
  ⟨x↔y⟩a≈αb⇒x#b x y₁ _ _ x≢y (x·y# x₁ y#a) (bindx≈xα a≈b) | no ¬p₁ | no ¬p = x·y# ¬p₁ (⟨x↔y⟩a≈αb⇒x#b x y₁ _ _ x≢y y#a a≈b)
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {y₁} x₁ y#a) (bindx≈yα x₂ x₃ a≈b) with eq x y₁
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {y₁} x₁ y#a) (bindx≈yα {_} {y₂} x₂ x₃ a≈b) | yes p
    rewrite refl = {!!} --  x·y# {!!} (⟨x↔y⟩a≈αb⇒x#b {!!} {!!} {!!} {!!} {!!} {!!} {!!})
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {y₁} x₁ y#a) (bindx≈yα x₂ x₃ a≈b) | no ¬p with eq y₁ y
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# x₁ y#a) (bindx≈yα x₂ x₃ a≈b) | no ¬p | yes refl = refl ↯ x₁
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {y₁} x₁ y#a) (bindx≈yα {_} {y₂} x₂ x₃ a≈b) | no ¬p₁ | no ¬p with eq y y₁
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# x₁ y#a) (bindx≈yα x₂ x₃ a≈b) | no ¬p₁ | no ¬p | yes refl = refl ↯ x₁
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {y₁} x₁ y#a) (bindx≈yα {_} {y₂} x₂ x₃ a≈b) | no ¬p₂ | no ¬p₁ | no ¬p = ?
--    x·y# {!!} (⟨x↔y⟩a≈αb⇒x#b {!!} {!!} {!!} {!!} {!!} {!!} {!a≈b!}) -- x·y# {!!} (⟨x↔y⟩a≈αb⇒x#b {!!} {!!} {!!} {!!} {!!} {!!} {!!})


{-
-}

{-
mutual


  All# : ∀ {x y z abts₁ abts₂} → x ≢ y → ⟨ x ↔ z ⟩ₗ abts₁ ≈αs ⟨ y ↔ z ⟩ₗ abts₂ → All (z #_) abts₁ → All (z #_) abts₂ → All (y #_) abts₁
  All# x≢y abts≈ [] [] = []
  All# x≢y () [] (px ∷ Allz₂)
  All# x≢y () (px ∷ Allz₁) []
  All# x≢y (∷≈αs x₃ abts≈) (px ∷ Allz₁) (px₁ ∷ Allz₂) = one# x≢y x₃ px px₁ ∷ (All# x≢y abts≈ Allz₁ Allz₂)

  one# : ∀ {x y z a b} → x ≢ y → ⟨ x ↔ z ⟩ a ≈α ⟨ y ↔ z ⟩ b → z # a → z # b → y # a
  one# {x} x≢y abt≈ (name# {y = y₁} x₂) (name# x₃) with eq x y₁
  one# x≢y abt≈ (name# x₂) (name# x₃) | yes p = name# (λ x → x≢y (trans p (sym x)))
  one# {x} {y} {z} x≢y abt≈ (name# {_} {y₁} x₂) (name# {_} {y₂} x₃) | no ¬p with eq z y | eq y₂ y₁
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p | yes refl | yes refl = name# x₃
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₁ | yes refl | no ¬p = name# x₂
  one# {x} {y} {z} x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₁ | no ¬p | yes refl with eq z y
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₁ | no ¬p | yes refl | yes p = p ↯ ¬p
  one# {x} {y} {z} x≢y abt≈ (name# {_} {w} x₂) (name# x₃) | no ¬p₂ | no ¬p₁ | yes refl | no ¬p with eq z w
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₂ | no ¬p₁ | yes refl | no ¬p | yes p = p ↯ x₃
  one# {x} {y} {z} x≢y abt≈ (name# {_} {w} x₂) (name# x₃) | no ¬p₃ | no ¬p₂ | yes refl | no ¬p₁ | no ¬p with eq y w
  one# x≢y name≈α (name# x₂) (name# x₃) | no ¬p₃ | no ¬p₂ | yes refl | no ¬p₁ | no ¬p | yes p = name# (refl ↯ x₃)
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₄ | no ¬p₃ | yes refl | no ¬p₂ | no ¬p₁ | no ¬p = name# ¬p
  one# {x} {y} {z} x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₂ | no ¬p | no ¬p₁ with eq z y
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₂ | no ¬p | no ¬p₁ | yes p = p ↯ ¬p
  one# {x} {y} {z} x≢y abt≈ (name# {_} {w} x₂) (name# x₃) | no ¬p₃ | no ¬p₁ | no ¬p₂ | no ¬p with eq z w
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₃ | no ¬p₁ | no ¬p₂ | no ¬p | yes p = p ↯ x₂
  one# {x} {y} {z} x≢y abt≈ (name# x₂) (name# {_} {w₁} x₃) | no ¬p₄ | no ¬p₂ | no ¬p₃ | no ¬p₁ | no ¬p with eq y w₁
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₄ | no ¬p₂ | no ¬p₃ | no ¬p₁ | no ¬p | yes refl = name# ¬p₃
  one# {x} {y} {z} x≢y abt≈ (name# {_} {w} x₂) (name# x₃) | no ¬p₅ | no ¬p₃ | no ¬p₄ | no ¬p₂ | no ¬p₁ | no ¬p with eq z y
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₅ | no ¬p₃ | no ¬p₄ | no ¬p₂ | no ¬p₁ | no ¬p | yes p = p ↯ ¬p₂
  one# {x} {y} {z} x≢y abt≈ (name# x₂) (name# {_} {w} x₃) | no ¬p₆ | no ¬p₄ | no ¬p₅ | no ¬p₃ | no ¬p₂ | no ¬p₁ | no ¬p with eq z w
  one# x≢y abt≈ (name# x₂) (name# x₃) | no ¬p₆ | no ¬p₄ | no ¬p₅ | no ¬p₃ | no ¬p₂ | no ¬p₁ | no ¬p | yes p = p ↯ x₃
  one# x≢y name≈α (name# x₂) (name# x₃) | no ¬p₇ | no ¬p₅ | no ¬p₆ | no ¬p₄ | no ¬p₃ | no ¬p₂ | no ¬p₁ | no ¬p = name# (refl ↯ ¬p₆)
  one# x≢y () (name# x₂) (oper# x₃)
  one# x≢y () (name# x₂) x·x#
  one# x≢y () (name# x₂) (x·y# x₃ z#b)
  one# x≢y () (oper# x₂) (name# x₃)
  one# x≢y (oper≈α x₁) (oper# x₂) (oper# x₃) = oper# (All# x≢y x₁ x₂ x₃)
  one# x≢y () (oper# x₂) x·x# 
  one# x≢y () (oper# x₂) (x·y# x₃ z#b)
  one# x≢y () x·x# (name# x₂)
  one# x≢y () x·x# (oper# x₂)
  one# {x} x≢y abt≈ (x·x# {x₁}) x·x# with eq x₁ x
  one# {x} x≢y abt≈ x·x# x·x# | yes refl with eq x x
  one# {x} {y} x≢y abt≈ x·x# x·x# | yes refl | yes p with eq y x
  one# x≢y abt≈ x·x# x·x# | yes refl | yes p₁ | yes p = sym p ↯ x≢y
  one# {x} x≢y abt≈ x·x# x·x# | yes refl | yes p | no ¬p with eq x x
  one# x≢y (bindx≈xα abt≈) x·x# x·x# | yes refl | yes p₁ | no ¬p | yes p = x·x#
  one# {x} x≢y (bindx≈yα x₁ x₂ abt≈) (x·x# {_} {a}) x·x# | yes refl | yes p₁ | no ¬p | yes p rewrite ⟨x↔x⟩a≡a x a = one# x≢y {!!} {!!} {!!} -- one# x≢y {!abt≈!} {!!} {!!}
  one# {x} x≢y (bindx≈xα abt≈) (x·x# {_} {a}) x·x# | yes refl | yes p | no ¬p₁ | no ¬p rewrite ⟨x↔x⟩a≡a x a = {!!}
  one# {x} x≢y (bindx≈yα y x₁ abt≈) (x·x# {_} {a}) x·x# | yes refl | yes p | no ¬p₁ | no ¬p rewrite ⟨↔⟩-invol x x a = {!!}
  one# x≢y abt≈ x·x# x·x# | yes refl | no ¬p = {!!}
  one# x≢y abt≈ x·x# x·x# | no ¬p = {!!}
  one# x≢y abt≈ x·x# (x·y# x₂ z#b) = {!abt≈!}
  one# x≢y () (x·y# x₂ z#a) (name# x₁)
  one# x≢y () (x·y# x₂ z#a) (oper# x₁)
  one# x≢y abt≈ (x·y# x₂ z#a) x·x# = {!!}
  one# x≢y abt≈ (x·y# x₂ z#a) (x·y# x₁ z#b) = {!!}

-}
{-

  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b : ∀ {x y z} abts abts₁ →
         All (z #_) abts₁ → All (z #_) abts → x ≢ y → ⟨ x ↔ z ⟩ₗ abts ≈αs ⟨ y ↔ z ⟩ₗ abts₁ → ⟨ x ↔ y ⟩ₗ abts ≈αs abts₁
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b [] [] Az#a Az#b x≢y abts≈αs = abts≈αs
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b [] (x₁ ∷ abts₁) Az#a Az#b x≢y ()
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b (x₁ ∷ abts) [] Az#a Az#b x≢y ()
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b (x₁ ∷ abts) (x₂ ∷ abts₁) (px ∷ Az#a) (px₁ ∷ Az#b) x≢y (∷≈αs x₃ abts≈αs) =
    ∷≈αs (inv-·₁ x≢y (⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b x₁ x₂ x≢y px₁ px x₃))
         (⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b abts abts₁ Az#a Az#b x≢y abts≈αs) 

  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b : ∀ {x y z} a b → x ≢ y → z # a → z # b → ⟨ x ↔ z ⟩ a ≈α ⟨ y ↔ z ⟩ b → x · a ≈α y · b
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name x₁) (name x₂) p q r a≈αb with ⟨ x ↔ z ⟩ₐ x₁ | lemma↔ₐ x z x₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name .x) (name x₃) p q r a≈αb | .z | inj₁ (refl , refl) with eq y x₃
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name .x) (name .y) p q r a≈αb | .z | inj₁ (refl , refl) | yes refl = bindx≈yα p (name# (p ∘ sym)) (swapx x y)
      where swapx : ∀ x y → name (⟨ x ↔ y ⟩ₐ x) ≈α name y
            swapx x y rewrite lemma↔ₐ-x≡z x y x refl = name≈α 
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name .x) (name x₃) p q r a≈αb | .z | inj₁ (refl , refl) | no ¬p₁ with eq z x₃
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name .x) (name x₃) p q (name# x₂) a≈αb | .x | inj₁ (refl , refl) | no ¬p₁ | yes p₂ = p₂ ↯ x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name .x) (name .z) p q (name# x₂) name≈α | .z | inj₁ (refl , refl) | no ¬p₁ | no ¬p₂ = refl ↯ x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} (name x₁) (name x₂) p q r a≈αb | s | inj₂ t with eq y x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x) (name y) p₁ (name# x₁) r name≈α | .x | inj₂ (inj₁ (refl , proj₂ , refl)) | yes refl = refl ↯ x₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name y) p₁ q r name≈α | .x₁ | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | yes refl = refl ↯ proj₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name x₁) (name x₂) p q r a≈αb | s | inj₂ t | no ¬p with eq z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₂) (name x) p₁ q (name# x₄) name≈α | y | inj₂ (inj₁ x₃) | no ¬p | yes refl = refl ↯ x₄
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x₂) p₁ q (name# x₃) a≈αb | s | inj₂ (inj₂ y₁) | no ¬p | yes refl = refl ↯ x₃
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name z) (name s) p (name# x) r name≈α | .s | inj₂ (inj₁ (refl , proj₂ , refl)) | no ¬p₁ | no ¬p = refl ↯ x
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name .x₁) p q r name≈α | .x₁ | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | no ¬p₁ | no ¬p = bindx≈yα p (name# ¬p₁) (swap-none _ _ x₁ proj₂ ¬p₁)
      where swap-none : ∀ x y z → x ≢ z → y ≢ z → name (⟨ x ↔ y ⟩ₐ z) ≈α name z
            swap-none x y z p q rewrite lemma↔ₐ-y≢z∧x≢z x y z p q = name≈α
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (oper op α abts) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (x₂ · b) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (name x₁) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (oper .op .α abts₁) p (oper# x₂) (oper# x₃) (oper≈α x₄) = {!!}
  -- bindx≈yα p (oper# (All# p x₄ x₂ x₃)) (oper≈α (⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b abts abts₁ x₃ x₂ p x₄))
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (x₁ · b) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (name x₂) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (oper op α abts) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (x₁ · a) (x₂ · b) p q r a≈αb with ⟨ x ↔ z ⟩ₐ x₁ | lemma↔ₐ x z x₁ | ⟨ y ↔ z ⟩ₐ x₂ | lemma↔ₐ x z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x · a) (.x · b) p q r (bindx≈xα a≈αb) | z | inj₁ (refl , refl) | .z | inj₁ (refl , proj₂) = {!bindx≈xα!} -- bindx≈yα {!!} {!!} {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x · a) (.x · b) p q r (bindx≈yα z≢f f# a≈αb) | z | inj₁ (refl , refl) | f | inj₁ (refl , proj₂) = {!!} -- bindx≈yα {!!} {!!} {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb | z | inj₁ (refl , refl) | f | inj₂ (inj₁ (s , t , u)) with eq x₁ x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (.x₁ · b) p₁ q r a≈αb | z | inj₁ (refl , refl) | f | inj₂ (inj₁ (s , t , u)) | yes refl = refl ↯ t
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb | .x₂ | inj₁ (refl , refl) | f | inj₂ (inj₁ (refl , t , u)) | no ¬p rewrite eq-yes x₂ refl = {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb | z | inj₁ (refl , refl) | f | inj₂ (inj₂ (s , t , u)) with eq x₁ x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (z · a) (.z · b) p₁ q r a≈αb | .z | inj₁ (refl , refl) | f | inj₂ (inj₂ (s , t , refl)) | yes refl = refl ↯ t
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb | z | inj₁ (refl , refl) | f | inj₂ (inj₂ (s , t , u)) | no ¬p with eq z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (.x₁ · b) p q r a≈αb | z | inj₁ (refl , refl) | f | inj₂ (inj₂ (s , t , refl)) | no ¬p | yes p₂ = refl ↯ t
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb | z | inj₁ (refl , refl) | f | inj₂ (inj₂ (s , t , u)) | no ¬p | no ¬p₂ = {!!} 
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (z · a) (x · b) p q r a≈αb | .x | inj₂ (inj₁ (refl , proj₂ , refl)) | f | inj₁ (refl , proj₄) = {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x · b) p q r a≈αb | .x₁ | inj₂ (inj₂ (proj₁ , proj₂ , refl)) | f | inj₁ (refl , proj₄) = {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb | e | inj₂ res | f | inj₂ (inj₁ (proj₁ , x₃)) = {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb | e | inj₂ res | f | inj₂ (inj₂ y₁) = {!!}
-}

 
{- eq x x₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} (x₁ · a) (x₂ · b) p₁ q r a≈αb | yes p with eq y x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (y · b) p₂ q r (bindx≈xα a≈αb) | yes refl | yes refl rewrite lemma↔ₐ-x≡z x₁ y x₁ refl = 
    bindx≈yα p₂ (one# p₂ {!!} q r) {!!} -- bindx≈yα p₂ (one# {!!} {!!} q r) {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (x₁ · a) (x₂ · b) p₂ q r (bindx≈yα x₃ x₄ a≈αb) | yes p₁ | yes p = refl ↯ x₃ 
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p₁ q r a≈αb | yes p | no ¬p = {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (x₁ · a) (x₂ · b) p q r a≈αb | no ¬p with eq z x₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} (x₁ · a) (x₂ · b) p₁ q r a≈αb | no ¬p | yes p with eq y x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {z = z} (x₁ · a) (x₂ · b) p₂ q r (bindx≈xα a≈αb) | no ¬p | yes p₁ | yes p rewrite ⟨x↔x⟩a≡a z a = {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p₂ q r (bindx≈yα x₃ x₄ a≈αb) | no ¬p | yes p₁ | yes p = {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p₁ q r a≈αb | no ¬p₁ | yes p | no ¬p = {!!}
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb | no ¬p₁ | no ¬p = {!!}
-} 

{-

z · ⟨ x₁ ↔ .z ⟩ a) ≈α
z · ⟨ y ↔ .z ⟩ b)
-}

mutual
  ≈αs-sym : ∀ {a b} → a ≈αs b → b ≈αs a
  ≈αs-sym []≈αs = []≈αs
  ≈αs-sym (∷≈αs x₁ p) = ∷≈αs (≈α-sym x₁) (≈αs-sym p)
 
  ≈α-sym : ∀ {a b} → a ≈α b → b ≈α a
  ≈α-sym name≈α = name≈α
  ≈α-sym (oper≈α x) = oper≈α (≈αs-sym x)
  ≈α-sym (bindx≈xα p) = bindx≈xα (≈α-sym p)
  ≈α-sym (bindx≈yα x₁ x₂ p) = bindx≈yα {!!} {!!} (≈α-sym (swapper _ _ _ _ p))
    where swapper : ∀ x y a b → ⟨ x ↔ y ⟩ a ≈α b → a ≈α ⟨ y ↔ x ⟩ b
          swapper x y a b a≈b rewrite ⟨↔⟩-comm x y a = {!!} 
{-
mutual
  ≈αs-trans : ∀ {a b c} → a ≈αs b → b ≈αs c → a ≈αs c
  ≈αs-trans []≈αs []≈αs = []≈αs
  ≈αs-trans (∷≈αs x₂ p) (∷≈αs x₃ q) = ∷≈αs (≈α-trans x₂ x₃) (≈αs-trans p q)
 
  ≈α-trans : ∀ {a b c} → a ≈α b → b ≈α c → a ≈α c
  ≈α-trans name≈α name≈α = name≈α
  ≈α-trans (oper≈α x) (oper≈α x₁) = oper≈α (≈αs-trans x x₁)
  ≈α-trans (bindx≈xα p) (bindx≈xα q) = bindx≈xα (≈α-trans p q)
  ≈α-trans (bindx≈xα p) (bindx≈yα {x} {y} {a} x₁ x₂ q) = bindx≈yα x₁ {!!} {!!} -- rewrite ⟨x↔x⟩a≡a _ (⟨ x ↔ _ ⟩ _) = {!!}
  ≈α-trans (bindx≈yα x₂ x₃ p) (bindx≈xα q) = {!-m!}
  ≈α-trans (bindx≈yα x₂ x₃ p) (bindx≈yα x₄ x₅ q) = {!-m!}

mutual
  #-≈αslemma : ∀ {a b x} → a ≈αs b → All (x #_) a → All (x #_) b
  #-≈αslemma []≈αs q = q
  #-≈αslemma (∷≈αs x₂ p) (px ∷ q) = (#-≈αlemma x₂ px) ∷ #-≈αslemma p q
 
  #-≈αlemma : ∀ {a b x} → a ≈α b → x # a → x # b
  #-≈αlemma name≈α (name# x₂) = name# x₂
  #-≈αlemma (oper≈α x₁) (oper# x₂) = oper# (#-≈αslemma x₁ x₂)
  #-≈αlemma (bindx≈xα p) x·x# = x·x#
  #-≈αlemma (bindx≈xα p) (x·y# x₁ q) = x·y# x₁ (#-≈αlemma p q)
  #-≈αlemma (bindx≈yα x₂ x₃ p) (x·x#) = x·y# x₂ {!!}
  #-≈αlemma (bindx≈yα {x} {y} x₂ x₃ p) (x·y# {z} x₁ q) with eq z y
  #-≈αlemma (bindx≈yα x₂ x₃ p₁) (x·y# x₄ q) | yes refl = x·x# -- refl ↯ x₄
  #-≈αlemma (bindx≈yα x₂ x₃ p) (x·y# x₄ q) | no ¬p = x·y# ¬p (#-≈αlemma {!!} q)
 


{-

ren : ∀ x y a → x ≢ y → y # a → (x · a) ≈α (y · ⟨ x ↔ y ⟩ a)
ren x y (name x₁) p (name# x₂) with eq x x₁
ren x₁ y (name .x₁) p₁ (name# x₂) | yes refl = {!!}
ren x y (name x₁) p (name# x₂) | no ¬p = {!!}
ren x y (oper op α abts) p q = {!!}
ren x y (x₁ · a) p q = {!!}


mutual
 Abts-ind : ∀ (P : Abt → Set) →
   (∀ {x} → P (name x)) →
   (∀ x a → x # a → P a → P (x · a)) → 
   (∀ op α abts → All P abts → P (oper op α abts)) →
    ∀ abts → All P abts
 Abts-ind P Pname Pop Pabs [] = []
 Abts-ind P Pname Pop Pabs (x ∷ abts) =
  (Abt-ind P Pname Pop Pabs x) ∷ (Abts-ind P Pname Pop Pabs abts)
 
 Abt-ind : ∀ (P : Abt → Set) →
   (∀ {x} → P (name x)) →
   (∀ x a → x # a → P a → P (x · a)) → 
   (∀ op α abts → All P abts → P (oper op α abts)) →
    ∀ a → P a
 Abt-ind P Pname Pabs Pop (name x₁) = Pname
 Abt-ind P Pname Pabs Pop (oper op α []) = Pop op α [] []
 Abt-ind P Pname Pabs Pop (oper op α (x ∷ abts)) = {!!}
 Abt-ind P Pname Pabs Pop (x₁ · a) = Pabs x₁ a {!fresh !} {!!}
 
--open import Data.List.All hiding (map)

mutual
 
 WFs : Signature → List Abt → Arity → Set
 WFs Ξ [] [] = ⊤
 WFs Ξ [] (x ∷ α) = ⊥
 WFs Ξ (a ∷ as) [] = ⊥
 WFs Ξ (a ∷ as) (x₁ ∷ α) = (valence a) ≡ x₁ × WF Ξ a × WFs Ξ as α 

 WF : Signature → Abt → Set
 WF Ξ (name x) = ⊤
 WF Ξ (oper op α abts) = ∀ (i : op ∈ Ξ sig) → findArity i ≡ α → WFs Ξ abts α
 WF Ξ (xs · a) = WF Ξ a 

-}
-}
