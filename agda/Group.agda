

module Group where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.Product
open import Data.Nat hiding (_≟_ ; compare) 
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Data.Nat.DivMod 
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Data.Unit hiding (_≟_)
open import Level


record Group {ℓ : Level} : Set₁ where
  
  infix 21 _⊗_

  field
    S : Set
    _≈_ : Rel S ℓ
    isEq : IsEquivalence _≈_
    _⊗_ : S → S → S
    assoc : ∀ (x y z : S) → x ⊗ (y ⊗ z) ≈ (x ⊗ y) ⊗ z
    e : S
    identity : ∀ (s : S) → (e ⊗ s ≈ s × s ⊗ e ≈ s)
    inverses : ∀ x → Σ[ y ∈ S ] x ⊗ y ≈ e


_≡_%12 : ℕ → ℕ → Set
n ≡ m %12 = True ((n mod 12) ≟ (m mod 12))

refl≡%12 : Reflexive _≡_%12
refl≡%12 {x} with (x mod 12)
refl≡%12 | r with  r ≟ r
refl≡%12 | r | yes p = tt
refl≡%12 | r | no ¬p = ¬p refl

sym≡%12 : ∀ {x y} → x ≡ y %12 → y ≡ x %12
sym≡%12 {x} {y} q with (x mod 12) ≟ (y mod 12)
sym≡%12 {x} {y} tt | yes p with (x mod 12) | (y mod 12)
sym≡%12 tt | yes p | q | r with r ≟ q
sym≡%12 tt | yes refl | q | .q | yes p = tt
sym≡%12 tt | yes refl | q | .q | no ¬p = ¬p refl
sym≡%12 () | no ¬p

ex : StrictTotalOrder _ _ _
ex = (strictTotalOrder 12)



trans≡%12 : ∀ {x y z} → x ≡ y %12 → y ≡ z %12 → x ≡ z %12
trans≡%12 {x} {y} {z} p q with (x mod 12) ≟ (y mod 12) | (y mod 12) ≟ (z mod 12)
trans≡%12 {x} {y} {z} tt tt | yes p | yes p₁ with (x mod 12) | (y mod 12) | (z mod 12)
trans≡%12 {x} {y} {z} tt tt | yes refl | yes refl | t | .t | .t with {!StrictTotalOrder.isStrictTotalOrder.compare (strictTotalOrder 12)!} t t 
trans≡%12 {x} {y} {z} tt tt | yes refl | yes refl | t | .t | .t | res = {!!} 
trans≡%12 p₁ () | yes p | no ¬p
trans≡%12 () tt | no ¬p | yes p
trans≡%12 p () | no ¬p | no ¬p₁

Clock : Group
Clock = record
          { S = ℕ
          ; _≈_ = _≡_%12
          ; isEq = record { refl = λ {x} → refl≡%12 {x}
                          ; sym =  λ {x y} q → sym≡%12 {x} {y} q
                          ; trans = {!!} }
          ; _⊗_ = {!!}
          ; assoc = {!!}
          ; e = {!!}
          ; identity = {!!}
          ; inverses = {!!}
          }

{-

mod+ : ∀ (d : ℕ) → {≢0 : False (d ≟ 0)} → (ℕ → ℕ → ℕ)
mod+ d {≢0} m n = toℕ (_mod_ (m + n) d {≢0})

{- Now to prove the clock is a group. -}

data Clock : Set where
  field
    n : ℕ
  ♯ : Clock → Clock
  -}

{-
assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
assoc zero y z = refl
assoc (succ x) y z with assoc x y z
assoc (succ x) y z | res = cong succ res 

left-id : ∀ (n : ℕ) → (n + zero) ≡ n
left-id zero = refl
left-id (succ n) = cong succ (left-id n)

identity : Σ[ e ∈ ℕ ] ∀ (n : ℕ) → (e + n ≡ n) × (n + e ≡ n)
identity = zero , (λ n → refl , left-id n)
-}

--inverses : Σ[ e ∈ ℕ ] ∀ (n : ℕ) → (n + m ≡ e) 

{-

  
-}



--  S = ℕ mod 12
--  S = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
{-

1 + (4 + 5) = 1 + 9 = 10
(1 + 4) + 5 = 5 + 5 = 10



-}
  
  

