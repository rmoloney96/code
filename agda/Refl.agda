
module Refl where 

--open import Data.Nat
--open import Data.List
open import Relation.Binary.PropositionalEquality as PropEq
     using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Reflection
open import Data.Unit
{-
exampleQuoteGoal : ℕ
exampleQuoteGoal = quoteGoal e in {!!}

example₁ : quoteTerm ((λ x → x) 0) ≡ con (quote ℕ.zero) []
example₁ = refl
-}

data ℕ : Set where 
  zero : ℕ
  succ : ℕ → ℕ


_+_ : ℕ → ℕ → ℕ
zero + y = y
(succ x) + y = succ (x + y)


+-assoc : {x y z : ℕ} → x + (y + z) ≡ (x + y) + z
+-assoc {x} {y} {z} = f x y z 
  where f : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
        f = {!!} 

data Is : {A : Set} → A → Set₁ where 
  is : {A : Set} → (x : A) → Is x

test : Is (quoteTerm _+_)
test = {!!} 

{-# NO_TERMINATION_CHECK #-}
--bollocks : ℕ → ℕ
--bollocks x = bollocks (succ x)

example : Term 
example = deconstruct (quoteTerm _+_)
  where deconstruct : Term → Term
        deconstruct (var x args) = {!!}
        deconstruct (con c args) = {!!}
        deconstruct (def f args) with definition f
        deconstruct (def f args) | function x = {!!}
        deconstruct (def f args) | data-type x = {!x!}
        deconstruct (def f args) | record′ x = {!!}
        deconstruct (def f args) | constructor′ = {!!}
        deconstruct (def f args) | axiom = {!!}
        deconstruct (def f args) | primitive′ = {!!} 
        deconstruct (lam v x) = {!!}
        deconstruct (pi t₁ t₂) = {!!}
        deconstruct (sort x) = {!!}
        deconstruct unknown = {!!}

{-
testrec : Nat → Nat
testrec = f
  where f : Nat → Nat 
        f zero = zero 
        f (succ n) = n

--M< : ℕ 
--M≤ 
  

data Term (s : ℕ) : Set where 
  rec : ℕ → Term s :ℕ → (y : Term)
  lam : ℕ → Term
  app : Term → Term

-}