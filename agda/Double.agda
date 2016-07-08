module Double where 

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Level
open import Relation.Nullary
open import Function 
open import Data.Bool 

left : ∀ {ℓ} → (∀ (A : Set ℓ) → A ⊎ ¬ A) → (∀ (A : Set ℓ) → ¬ ¬ A → A)
left f A p with f A
left f A p | inj₁ x₁ = x₁
left f A p | inj₂ y with p y
left f A p | inj₂ y | () 

right : ∀ {ℓ} → (∀ (A : Set ℓ) → ¬ ¬ A → A) → (∀ (A : Set ℓ) → A ⊎ ¬ A)
right f A = f (A ⊎ (¬ A)) (λ x → x (inj₁ (f A (λ z → x (inj₂ z)))))


{-
_+_ : ∀ {ℓ m n} (A : Set ℓ) (B : Set ℓ) → Set ((suc n) ⊔ m ⊔ ℓ)
_+_ {ℓ} {m} {n} A B = ∀ (C : Set n) → (A → C) → (B → C) → C

[_,_]_ : ∀ {ℓ m n} → {A : Set ℓ} {B : Set m} {C : Set n} → (A → C) → (B → C) → (A + B) → C
[_,_]_ {A} {B} {C} f g x with x C
[_,_]_ {A} {B} {C} f g x | res = {!!}
-}

AC : {A B : Set} {R : A → B → Set} → (∀ (x : A) → Σ[ y ∶ B ] R x y) → Σ[ f ∶ (A → B) ] (∀ (x : A) → R x (f x))
AC {A} {B} {R} p = (proj₁ ∘ p) , proj₂ ∘ p


data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (B a → W A B) → W A B

lem : {A : Set} {B : A → Set} → ((x : A) → B x) → ¬ (W A B)
lem h (sup a f) = lem h (f (h a)) 

invertF : ∀ (F : Bool → Set) → (b : Bool) → F true × F false → F b
invertF F true p = proj₁ p
invertF F false p = proj₂ p 

Wfunct : ∀ (F : Bool → Set) → W Bool F → ¬ (F false × F true)
Wfunct F (sup b x) (proj₁ , proj₂) = lem (λ {true → proj₂; false → proj₁}) (x (invertF F b (proj₂ , proj₁)))

functW : ∀ (F : Bool → Set) → ¬ (F false × F true) → W Bool F 
functW F x = {!!}

Nat : Set 
Nat = W Bool (λ { false → ⊥ ; true → ⊤ })

z : Nat
z = sup false (λ ())

s : Nat → Nat
s n = sup true (λ _ → n)

List : (A : Set) → Set
List A = W Bool (λ { false → ⊥ ; true → A})

nil : {A : Set} → List A 
nil {A} = sup false (λ ())

cons : {A : Set} → (a : A) → List A → List A
cons {A} x xs = sup true (λ (y : A) → {!!})

hd : {A : Set} → List A → A ⊎ ⊤
hd (sup true f) = inj₁ {!!}
hd (sup false f) = {!!} 

https://www.youtube.com/watch?feature=player_embedded&v=BJ70tozVDtE#!
my reaction: 
http://www.youtube.com/watch?v=PXgmRBX6iU4


Okay, so uh, do you have anything to back that up? I mean, look, if you're willing to discount three centuries of Darwinism, that's woo! But how do you know? Hmm?
I don't. But it's what I choose to believe.