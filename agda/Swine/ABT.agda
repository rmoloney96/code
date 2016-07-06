open import Utils

module ABT
  (Atom : Set)
  (eq : DecEq Atom) where

open import Relation.Nullary
--open import Data.Vec
open import Data.Nat
open import Data.List
open import Data.Product hiding (map)
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

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
   bind≈α : ∀ {x abt₁ abt₂} →

            abt₁ ≈α abt₂ →
         ---------------------
         x · abt₁ ≈α x · abt₂

--open import Relation.Nullary.Decidable
open import Relation.Binary
open import Function

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

inv-·₁ : ∀ {x y a b} → x · a ≈α y · b → x ≡ y
inv-·₁ (bind≈α x) = refl

inv-·₂ : ∀ {x y a b} → x · a ≈α y · b → a ≈α b 
inv-·₂ (bind≈α x) = x

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
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | yes p with α ≟arity α₁  --abts ≈αs? abts₁
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | yes p₁ | yes p with abts ≈αs? abts₁
  oper (c x) α abts ≈α? oper (c .x) .α abts₁ | yes refl | yes refl | yes p = yes (oper≈α p)
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | yes p₁ | yes p | no ¬p = no (¬p ∘ inv-oper₃)
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | yes p | no ¬p = no (¬p ∘ inv-oper₂)
  oper (c x) α abts ≈α? oper (c x₁) α₁ abts₁ | no ¬p = no (¬p ∘ inv-oper₁)
  oper op α abts ≈α? (x · y) = no (λ ())
  (x · x₁) ≈α? name x₂ = no (λ ())
  (x · x₁) ≈α? oper op α abts = no (λ ())
  (x · x₁) ≈α? (x₂ · y) with eq x x₂
  (x · x₁) ≈α? (x₂ · y) | yes p with x₁ ≈α? y
  (x · x₁) ≈α? (.x · y) | yes refl | yes p = yes (bind≈α p)
  (x · x₁) ≈α? (x₂ · y) | yes p | no ¬p = no (¬p ∘ inv-·₂)
  (x · x₁) ≈α? (x₂ · y) | no ¬p = no (¬p ∘ inv-·₁)

mutual
 #-≈αslemma : ∀ {a b x} → a ≈αs b → All (x #_) a → All (x #_) b
 #-≈αslemma []≈αs q = q
 #-≈αslemma (∷≈αs x₂ p) (px ∷ q) = (#-≈αlemma x₂ px) ∷ #-≈αslemma p q
 
 #-≈αlemma : ∀ {a b x} → a ≈α b → x # a → x # b
 #-≈αlemma name≈α x₂ = x₂
 #-≈αlemma (oper≈α x₁) (oper# x₂) = oper# (#-≈αslemma x₁ x₂)
 #-≈αlemma (bind≈α p) x·x# = x·x#
 #-≈αlemma (bind≈α p) (x·y# x₁ x₂) = x·y# x₁ (#-≈αlemma p x₂)

mutual
 ≈αs-refl : ∀ {x} → x ≈αs x
 ≈αs-refl {[]} = []≈αs
 ≈αs-refl {x ∷ x₁} = ∷≈αs ≈α-refl ≈αs-refl
 
 ≈α-refl : ∀ {x} → x ≈α x
 ≈α-refl {name x} = name≈α
 ≈α-refl {oper op α abts} = oper≈α ≈αs-refl
 ≈α-refl {x · x₁} = bind≈α ≈α-refl

mutual
 ≈αs-sym : ∀ {a b} → a ≈αs b → b ≈αs a
 ≈αs-sym []≈αs = []≈αs
 ≈αs-sym (∷≈αs x₁ p) = ∷≈αs (≈α-sym x₁) (≈αs-sym p)
 
 ≈α-sym : ∀ {a b} → a ≈α b → b ≈α a
 ≈α-sym name≈α = name≈α
 ≈α-sym (oper≈α x) = oper≈α (≈αs-sym x)
 ≈α-sym (bind≈α p) = bind≈α (≈α-sym p)


mutual
 ≈αs-trans : ∀ {a b c} → a ≈αs b → b ≈αs c → a ≈αs c
 ≈αs-trans []≈αs []≈αs = []≈αs
 ≈αs-trans (∷≈αs x₂ p) (∷≈αs x₃ q) = ∷≈αs (≈α-trans x₂ x₃) (≈αs-trans p q)
 
 ≈α-trans : ∀ {a b c} → a ≈α b → b ≈α c → a ≈α c
 ≈α-trans name≈α q = q
 ≈α-trans (oper≈α x) (oper≈α x₁) = oper≈α (≈αs-trans x x₁)
 ≈α-trans (bind≈α x₁) (bind≈α x₂) = bind≈α (≈α-trans x₁ x₂) 

--open import Data.List.All hiding (map)
open import Data.Empty

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

