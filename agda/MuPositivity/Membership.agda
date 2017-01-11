module Membership where

open import Utils
open import Data.List
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Data.Nat
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function


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

multiplicity : {C : Set} → (eq : DecEq C) → C → List C → ℕ
multiplicity eq x [] = zero
multiplicity eq x (x₁ ∷ L) with eq x x₁
multiplicity eq x (x₁ ∷ L) | yes p = suc (multiplicity eq x L)
multiplicity eq x (x₁ ∷ L) | no ¬p = multiplicity eq x L

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

{-
open import Data.Sum

x∉[] : ∀ {C : Set} (x : C) → x ∉ [] 
x∉[] x ()

¬x∷T⊆[] : ∀ {C : Set} {y : C} {T} → (y ∷ T) ⊆ [] → ⊥
¬x∷T⊆[] {_} {y} p with p y here
¬x∷T⊆[] {_} {y} p | ()

hereOrThere : ∀ {C : Set} {x y : C} {S} → x ∈ S → y ∈ (x ∷ S) → y ∈ S
hereOrThere x∈S here = x∈S
hereOrThere x∈S (there y∈x∷S) = y∈x∷S

staysIn : ∀ {C : Set} {x y : C} {S T} →
  x ∈ T →  y ∈ (x ∷ S) → S ⊆ T → y ∈ T
staysIn x∈T here S⊆T = x∈T
staysIn x∈T (there y∈x∷S) S⊆T = S⊆T _ y∈x∷S

staysOut : ∀ {C : Set} {x y : C} {S T} →
  x ∈ T → x ∉ S → S ⊆ T → ¬ T ⊆ S → ¬ (T ⊆ (x ∷ S))
staysOut x∈T x∉S S⊆T ¬T⊆S T⊆x∷S = {!!}

_⊂_ : ∀ {C : Set} (xs ys : List C) → Set
_⊂_ {C} S T = S ⊆ T × ¬ (T ⊆ S)


die : ∀ {C : Set} {x y : C} {S T} →
  x ∈ T → x ∉ S → S ⊆ T → ¬ T ⊆ S → (x ∷ S) ⊂ T → ⊥ 
die x∈T x∉S S⊆T ¬T⊆S (x∷S⊆T , ¬T⊆x∷S) = {!!} 

_≲⟨_⟩_ : ∀ {C : Set} → (S : List C) → (eq : DecEq C) → (T : List C) → Dec (S ⊂ T)
[] ≲⟨ eq ⟩ [] = no (λ z → proj₂ z (λ x x₁ → x₁))
[] ≲⟨ eq ⟩ (x ∷ T) = yes ((λ x₁ → λ ()) , (λ x₁ → ¬x∷T⊆[] x₁))
(x ∷ S) ≲⟨ eq ⟩ T with S ≲⟨ eq ⟩ T 
(x ∷ S) ≲⟨ eq ⟩ T | yes (S⊆T , ¬T⊆S ) with eq2in eq x S
(x ∷ S) ≲⟨ eq ⟩ T | yes (S⊆T , ¬T⊆S) | yes p =
  yes ((λ x₁ x₂ → hereOrThere (S⊆T x₁ (hereOrThere p x₂)) here) ,
       (λ x₁ → ¬T⊆S (λ x₂ x₃ → hereOrThere p (x₁ x₂ x₃))))
(x ∷ S) ≲⟨ eq ⟩ T | yes (S⊆T , ¬T⊆S) | no ¬p with eq2in eq x T
(x ∷ S) ≲⟨ eq ⟩ T | yes (S⊆T , ¬T⊆S) | no ¬p | yes p =
  no (λ x₁ → {!!})
(x ∷ S) ≲⟨ eq ⟩ T | yes (S⊆T , ¬T⊆S) | no ¬p₁ | no ¬p = {!!}
(x ∷ S) ≲⟨ eq ⟩ T | no ¬p = {!!}

-}

{-
_⊂_ : ∀ {C : Set} (xs ys : List C) → Set
_⊂_ {C} S T = S ⊆ T × Σ[ R ∈ List C ] R ≢ [] × R ⊆ T × (∀ x → x ∈ T → x ∈ S ⊎ x ∈ R)

_≲⟨_⟩_ : ∀ {C : Set} → (S : List C) → (eq : DecEq C) → (T : List C) → Dec (S ⊂ T)
[] ≲⟨ eq ⟩ [] = no ((λ {(S⊆T , [] , R≢[] , _) → R≢[] refl ;
                       (S⊆T , (x ∷ R) , R≢[] , sub , f) → x∉[] x (sub x here) }))
[] ≲⟨ eq ⟩ (x ∷ T) = yes
                       ((λ x₁ → λ ()) , x ∷ T , (λ ()) , (λ x₁ x₂ → x₂) , (λ x₁ → inj₂))
(x ∷ S) ≲⟨ eq ⟩ T with S ≲⟨ eq ⟩ T
(x ∷ S) ≲⟨ eq ⟩ T | yes (S⊆T , R , R≢[] , R⊆T , part ) with eq2in eq x T
(x ∷ S) ≲⟨ eq ⟩ T | yes (S⊆T , R , R≢[] , R⊆T , part ) | res = {!!}
(x ∷ S) ≲⟨ eq ⟩ T | no ¬p = {!!}
-}
{-
[] ≲⟨ eq ⟩ [] = no (λ {(_ , _ , () , _)})
[] ≲⟨ eq ⟩ (x ∷ T) = yes ((λ x₁ → λ ()) , x , here , (λ ()))
(x ∷ S) ≲⟨ eq ⟩ T with eq2in eq x T
(x ∷ S) ≲⟨ eq ⟩ T | yes p with S ≲⟨ eq ⟩ T
(x ∷ S) ≲⟨ eq ⟩ T | yes p₁ | yes (l , y , y∈T , y∉S) = {!!}
{-
  yes ((λ x x₁ → oneMore x₁ p₁ l) , y , y∈T , {!!})
  where oneMore : ∀ {C : Set} {x y : C} {S T} → x ∈ (y ∷ S) → y ∈ T → S ⊆ T → x ∈ T
        oneMore here y∈T s⊆T = y∈T
        oneMore (there x∈y∷S) y∈T s⊆T = s⊆T _ x∈y∷S
        notOneMore : ∀ {C : Set} {x y : C} {S T} → y ∈ T → y ∉ S → S ⊆ T → y ∉ (y ∷ T)
        notOneMore y∈T₁ y∉S₁ S⊆T here = {!!}
        notOneMore y∈T₁ y∉S₁ S⊆T (there y∈y∷S) = {!!}
        -}
(x ∷ S) ≲⟨ eq ⟩ T | yes p | no ¬p = {!!}
(x ∷ S) ≲⟨ eq ⟩ T | no ¬p = no (λ z → ¬p (proj₁ z x here))
-}
