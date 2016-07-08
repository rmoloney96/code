open import Utils
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality 
open import Data.List
open import Data.Empty

{-

This is an attempt to lift ideas from: "Principles of Alpha-Induction
and Recursion for the Lambda Calculus in Constructive Type Theory"
into ABTs more generally.

The basic idea is that by symmetrising the binding rule, which in
Harper's description has a "left handed" or "right handed approach, we
get a simpler formulation.

-}


module SymABT
  (Atom : Set)
  (eq : DecEq Atom)
  (fresh : (xs : List Atom) → Σ[ y ∈ Atom ] y ∉ xs)
  where

open import Relation.Nullary
--open import Data.Vec
open import Data.Nat
open import Data.Unit hiding (_≟_)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Relation.Binary
open import Function

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
Signature = List (Code × Arity)

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

⟨_↔_⟩ₐ : Atom → Atom → Atom → Atom
⟨ x ↔ y ⟩ₐ z with eq x z
⟨ x ↔ y ⟩ₐ z | yes p = y
⟨ x ↔ y ⟩ₐ z | no ¬p with eq y z
⟨ x ↔ y ⟩ₐ z | no ¬p | yes p = x
⟨ x ↔ y ⟩ₐ z | no ¬p₁ | no ¬p = z

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

x∉xs━x : ∀ xs x → x ∉ (xs ─ x)
x∉xs━x [] x () 
x∉xs━x (x ∷ xs) x₁ q with eq x x₁
x∉xs━x (x ∷ xs) .x q | yes refl = x∉xs━x xs x q
x∉xs━x (x ∷ xs) .x here | no x≢x = refl ↯ x≢x
x∉xs━x (x ∷ xs) x₁ (there q) | no ¬p = x∉xs━x xs x₁ q

y∈xs─x⇒y≢x : ∀ xs x y → y ∈ xs ─ x → y ≢ x
y∈xs─x⇒y≢x [] x y () y≡x
y∈xs─x⇒y≢x (x ∷ xs) x₁ y p y≡x with eq x x₁
y∈xs─x⇒y≢x (x ∷ xs) .x .x p₁ refl | yes refl = x∉xs━x xs x p₁
y∈xs─x⇒y≢x (y ∷ xs) x₁ .y here y≡x | no ¬p = y≡x ↯ ¬p
y∈xs─x⇒y≢x (x ∷ xs) x₁ .x₁ (there p) refl | no ¬p = x∉xs━x xs x₁ p

mutual

 fvs : List Abt → List Atom 
 fvs [] = []
 fvs (x ∷ abts) = fvs abts ++ fv x
 
 fv : Abt → List Atom 
 fv (name x) = x ∷ []
 fv (oper op α abts) = fvs abts
 fv (x · a) = (fv a) ─ x

mutual
 data _⊢_≈αs_ : List Atom → List Abt → List Abt → Set where
   []≈αs : ∀ {Γ} → Γ ⊢ [] ≈αs []
   
   ∷≈αs : ∀ {Γ x y abts₁ abts₂} →
   
     Γ ⊢ x ≈α y → Γ ⊢ abts₁ ≈αs abts₂ →
     ---------------------------
     Γ ⊢ (x ∷ abts₁) ≈αs (y ∷ abts₂)
   
 data _⊢_≈α_ : List Atom → Abt → Abt → Set where
   name≈α : ∀ {x} → name x ≈α name x
   oper≈α : ∀ {op α abts₁ abts₂} →
   
            abts₁ ≈αs abts₂ →
     ----------------------------------
     Γ ⊢ oper op α abts₁ ≈α oper op α abts₂

   bind≈α : ∀ {x y xs abt₁ abt₂} →

    (∀ c → c ∉ (x ∷ y ∷ Γ) → (x ∷ y ∷ Γ) ⊢ ⟨ x ↔ c ⟩ abt₁ ≈α ⟨ y ↔ c ⟩ abt₂) →
     -------------------------------------------------
             x · abt₁ ≈α y · abt₂

{-

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
inv-·₁ {y = y} np (bind≈α x₁) with x₁ y
inv-·₁ {y = y} np (bind≈α x₁) | res = {!!}

inv-·₂ : ∀ {x a b} → (x · a) ≈α (x · b) → a ≈α b 
inv-·₂ q = {!!}

inv-·₃ : ∀ {x y a b} → x ≢ y → (x · a) ≈α (y · b) → y # a
inv-·₃ p q = {!!}

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
  (x · a) ≈α? (y · b) with fresh (fv a ++ fv b)
  (x · a) ≈α? (y · b) | v , p = {!!} 

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

mutual
  ≈αs-refl : ∀ {x} → x ≈αs x
  ≈αs-refl {[]} = []≈αs
  ≈αs-refl {x ∷ x₁} = ∷≈αs ≈α-refl ≈αs-refl
 
  ≈α-refl : ∀ {x} → x ≈α x
  ≈α-refl {name x} = name≈α
  ≈α-refl {oper op α abts} = oper≈α  ≈αs-refl
  ≈α-refl {x · x₁} = {!!} -- bindx≈xα {x} {x₁} ≈α-refl

x·a≈αy·⟨x↔y⟩a : ∀ x y a → x ≢ y → y # a → x · a ≈α y · ⟨ x ↔ y ⟩ a
x·a≈αy·⟨x↔y⟩a x y (name x₁) x≢y (name# x₂) with eq x x₁
x·a≈αy·⟨x↔y⟩a x₁ y (name .x₁) x≢y (name# x₂) | yes refl = {!!} -- bindx≈yα x≢y (name# x₂) (⟨x↔y⟩ₐx≈αy x₁ y)
x·a≈αy·⟨x↔y⟩a x y (name x₁) x≢y (name# x₂) | no ¬p with eq y x₁
x·a≈αy·⟨x↔y⟩a x x₁ (name .x₁) x≢y (name# x₂) | no ¬p | yes refl = refl ↯ x₂
x·a≈αy·⟨x↔y⟩a x y (name x₁) x≢y (name# x₂) | no ¬p₁ | no ¬p = {!!} -- bindx≈yα x≢y (name# x₂) (⟨x↔y⟩ₐz≈αz x y x₁ ¬p₁ x₂)
x·a≈αy·⟨x↔y⟩a x y (oper op α abts) x≢y y#a = {!!} -- bindx≈yα x≢y y#a (oper≈α ≈αs-refl)
x·a≈αy·⟨x↔y⟩a x y (z · a) x≢y y#a = {!!} -- bindx≈yα x≢y y#a ≈α-refl

⟨x↔y⟩x≈αy : ∀ x y → name (⟨ x ↔ y ⟩ₐ x) ≈α name y
⟨x↔y⟩x≈αy x y with eq x x
⟨x↔y⟩x≈αy x y | yes refl = name≈α
⟨x↔y⟩x≈αy x y | no ¬p = refl ↯ ¬p

⟨x↔y⟩z≈αz : ∀ x y z → z ≢ x → z ≢ y → name (⟨ x ↔ y ⟩ₐ z) ≈α name z
⟨x↔y⟩z≈αz x y z z≢x z≢y with eq x z
⟨x↔y⟩z≈αz x y z z≢x z≢y | yes p = sym p ↯ z≢x
⟨x↔y⟩z≈αz x y z z≢x z≢y | no ¬p with eq y z
⟨x↔y⟩z≈αz x y z z≢x z≢y | no ¬p | yes p = sym p ↯ z≢y
⟨x↔y⟩z≈αz x y z z≢x z≢y | no ¬p₁ | no ¬p = name≈α

mutual
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b : ∀ {x y z} abts abts₁ →
         All (z #_) abts₁ → All (z #_) abts → x ≢ y → ⟨ x ↔ z ⟩ₗ abts ≈αs ⟨ y ↔ z ⟩ₗ abts₁ → ⟨ x ↔ y ⟩ₗ abts ≈αs abts₁
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b [] [] Az#a Az#b x≢y abts≈αs = abts≈αs
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b [] (x₁ ∷ abts₁) Az#a Az#b x≢y ()
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b (x₁ ∷ abts) [] Az#a Az#b x≢y ()
  ⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b (x₁ ∷ abts) (x₂ ∷ abts₁) (px ∷ Az#a) (px₁ ∷ Az#b) x≢y (∷≈αs x₃ abts≈αs) =
    ∷≈αs (inv-·₁ x≢y (⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b x₁ x₂ x≢y px₁ px x₃))
         (⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b abts abts₁ Az#a Az#b x≢y abts≈αs) 

  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b : ∀ {x y z} a b → x ≢ y → z # a → z # b → ⟨ x ↔ z ⟩ a ≈α ⟨ y ↔ z ⟩ b → x · a ≈α y · b
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} (name x₁) (name x₂) p q r a≈αb with eq x x₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {_} {y} (name x) (name x₂) p₁ q r a≈αb | yes refl with eq y x₂ 
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x) (name y) p₁ q r a≈αb | yes refl | yes refl = {!!} -- bindx≈yα p₁ (name# (p₁ ∘ sym )) (⟨x↔y⟩x≈αy x y)
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {z = z} (name x) (name x₂) p₁ q r a≈αb | yes refl | no ¬p with eq z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x) (name y) p₁ q r name≈α | yes refl | no ¬p | yes refl = r ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x) (name z) p₁ q r name≈α | yes refl | no ¬p | no ¬p₂ = r ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name x₁) (name x₂) p q r a≈αb | no ¬p with eq z x₁ | eq y x
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {y = y} (name x₁) (name x₂) p₂ q r a≈αb | no ¬p | yes p | yes p₁ with eq y x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name .x₁) p₃ q r name≈α | no ¬p | yes refl | yes refl | yes refl = r ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x₂) p₂ q r a≈αb | no ¬p₁ | yes refl | yes p₁ | no ¬p = q ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x₂) p₁ q r a≈αb | no ¬p₁ | yes refl | no ¬p = q ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} (name x₁) (name x₂) p₁ q r a≈αb | no ¬p₁ | no ¬p | yes refl with eq x x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x) p₁ q r name≈α | no ¬p₁ | no ¬p | yes refl | yes refl = q ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {z = z} (name x₁) (name x₂) p₁ q r a≈αb | no ¬p₂ | no ¬p₁ | yes refl | no ¬p with eq z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x) (name x₂) p₁ q r name≈α | no ¬p₂ | no ¬p₁ | yes refl | no ¬p | yes p = refl ↯ p₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x₂) p₁ q r a≈αb | no ¬p₃ | no ¬p₂ | yes refl | no ¬p₁ | no ¬p = refl ↯ p₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {y = y} (name x₁) (name x₂) p q r a≈αb | no ¬p₂ | no ¬p | no ¬p₁ with eq y x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name y) p₁ q r name≈α | no ¬p₂ | no ¬p | no ¬p₁ | yes refl = q ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {z = z} (name x₁) (name x₂) p q r a≈αb | no ¬p₃ | no ¬p₁ | no ¬p₂ | no ¬p with eq z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name y) (name x₂) p₁ q r name≈α | no ¬p₃ | no ¬p₁ | no ¬p₂ | no ¬p | yes refl = r ↯ inv-x#name 
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} (name x₂) (name .x₂) p q r name≈α | no ¬p₄ | no ¬p₂ | no ¬p₃ | no ¬p₁ | no ¬p = {!!} -- bindx≈yα p (name# ¬p₁) (⟨x↔y⟩z≈αz x y x₂ (¬p₄ ∘ sym) (¬p₁ ∘ sym))
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (oper op α abts) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (x₂ · b) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (name x₁) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (oper .op .α abts₁) p (oper# x₂) (oper# x₃) (oper≈α x₄) = {!!} -- bindx≈yα p (oper# {!!}) (oper≈α (⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b abts abts₁ x₃ x₂ p x₄))
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (x₁ · b) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (name x₂) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (oper op α abts) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb = {!a≈αb!} -- bindx≈yα p {!!} (bindx≈yα {!!} {!!} {!!}) -- bindx≈yα p {!!} (bindx≈yα {!!} {!!} {!!})

{-
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b : ∀ {x y z} a b → x ≢ y → z # a → z # b → ⟨ x ↔ z ⟩ a ≈α ⟨ y ↔ z ⟩ b → x · a ≈α y · b
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} (name x₁) (name x₂) p q r a≈αb with eq x x₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} (name .x) (name x₂) p₁ q r a≈αb | yes refl with eq y x₂ 
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} (name .x) (name .y) p₁ q r a≈αb | yes refl | yes refl = bindx≈yα p₁ (name# (p₁ ∘ sym )) (⟨x↔y⟩x≈αy x y)
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name .x) (name x₂) p₁ q r a≈αb | yes refl | no ¬p with eq z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {.y} (name .x) (name .y) p₁ q r name≈α | yes refl | no ¬p | yes refl = r ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name .x) (name .z) p₁ q r name≈α | yes refl | no ¬p | no ¬p₂ = r ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} {z} (name x₁) (name x₂) p q r a≈αb | no ¬p with eq z x₁ | eq y x
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} (name x₁) (name x₂) p₂ q r a≈αb | no ¬p | yes p | yes p₁ with eq y x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name .x₁) p₃ q r name≈α | no ¬p | yes refl | yes refl | yes refl = r ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x₂) p₂ q r a≈αb | no ¬p₁ | yes refl | yes p₁ | no ¬p = q ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x₂) p₁ q r a≈αb | no ¬p₁ | yes refl | no ¬p = q ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} (name x₁) (name x₂) p₁ q r a≈αb | no ¬p₁ | no ¬p | yes refl with eq x x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x) p₁ q r name≈α | no ¬p₁ | no ¬p | yes refl | yes refl = q ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {z = z} (name x₁) (name x₂) p₁ q r a≈αb | no ¬p₂ | no ¬p₁ | yes refl | no ¬p with eq z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x) (name x₂) p₁ q r name≈α | no ¬p₂ | no ¬p₁ | yes refl | no ¬p | yes p = refl ↯ p₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name x₂) p₁ q r a≈αb | no ¬p₃ | no ¬p₂ | yes refl | no ¬p₁ | no ¬p = refl ↯ p₁
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {y = y} (name x₁) (name x₂) p q r a≈αb | no ¬p₂ | no ¬p | no ¬p₁ with eq y x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (name y) p₁ q r name≈α | no ¬p₂ | no ¬p | no ¬p₁ | yes refl = q ↯ inv-x#name
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {z = z} (name x₁) (name x₂) p q r a≈αb | no ¬p₃ | no ¬p₁ | no ¬p₂ | no ¬p with eq z x₂
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name y) (name x₂) p₁ q r name≈α | no ¬p₃ | no ¬p₁ | no ¬p₂ | no ¬p | yes refl = r ↯ inv-x#name 
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b {x} {y} (name x₂) (name .x₂) p q r name≈α | no ¬p₄ | no ¬p₂ | no ¬p₃ | no ¬p₁ | no ¬p = bindx≈yα p (name# ¬p₁) (⟨x↔y⟩z≈αz x y x₂ (¬p₄ ∘ sym) (¬p₁ ∘ sym))
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (oper op α abts) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (name x₁) (x₂ · b) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (name x₁) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (oper .op .α abts₁) p (oper# x₂) (oper# x₃) (oper≈α x₄) = bindx≈yα {!!} {!!} (oper≈α (⟨x↔z⟩a≈αs⟨y↔z⟩b⇒x·a≈αsy·b abts abts₁ x₃ x₂ p x₄))
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (oper op α abts) (x₁ · b) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (name x₂) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (oper op α abts) p q r ()
  ⟨x↔z⟩a≈α⟨y↔z⟩b⇒x·a≈αy·b (x₁ · a) (x₂ · b) p q r a≈αb = {!r!} -- bindx≈yα p {!!} (bindx≈yα {!!} {!!} {!!})
-}

mutual
  ≈αs-sym : ∀ {a b} → a ≈αs b → b ≈αs a
  ≈αs-sym []≈αs = []≈αs
  ≈αs-sym (∷≈αs x₁ p) = ∷≈αs (≈α-sym x₁) (≈αs-sym p)
 
  ≈α-sym : ∀ {a b} → a ≈α b → b ≈α a
  ≈α-sym name≈α = name≈α
  ≈α-sym (oper≈α x) = oper≈α (≈αs-sym x)
--  ≈α-sym (bindx≈xα p) = bindx≈xα (≈α-sym p)
  ≈α-sym (bind≈α p) = {!!} -- bind≈α (x₁ ∘ sym ) {!-m!} (≈α-sym {!-m!})


mutual
  ≈αs-trans : ∀ {a b c} → a ≈αs b → b ≈αs c → a ≈αs c
  ≈αs-trans []≈αs []≈αs = []≈αs
  ≈αs-trans (∷≈αs x₂ p) (∷≈αs x₃ q) = ∷≈αs (≈α-trans x₂ x₃) (≈αs-trans p q)
 
  ≈α-trans : ∀ {a b c} → a ≈α b → b ≈α c → a ≈α c
  ≈α-trans name≈α name≈α = name≈α
  ≈α-trans (oper≈α x) (oper≈α x₁) = oper≈α (≈αs-trans x x₁)
--  ≈α-trans (bindx≈xα p) (bindx≈xα q) = bindx≈xα (≈α-trans p q)
--  ≈α-trans (bindx≈xα p) (bindx≈yα x₁ x₂ q) = {!!}
--  ≈α-trans (bindx≈yα x₂ x₃ p) (bindx≈xα q) = {!!}
  ≈α-trans (bind≈α p) (bind≈α q) = {!!}

mutual
  #-≈αslemma : ∀ {a b x} → a ≈αs b → All (x #_) a → All (x #_) b
  #-≈αslemma []≈αs q = q
  #-≈αslemma (∷≈αs x₂ p) (px ∷ q) = (#-≈αlemma x₂ px) ∷ #-≈αslemma p q
 
  #-≈αlemma : ∀ {a b x} → a ≈α b → x # a → x # b
  #-≈αlemma name≈α (name# x₂) = name# x₂
  #-≈αlemma (oper≈α x₁) (oper# x₂) = oper# (#-≈αslemma x₁ x₂)
  #-≈αlemma (bind≈α p) (x·y# x₁ q) = {!!} -- x·y# x₁ (#-≈αlemma p q)
  #-≈αlemma (bind≈α p) x·x# = {!!}
  
 


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
