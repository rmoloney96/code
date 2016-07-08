module Map where 

open import Coinduction
open import Data.Colist
open import Data.Nat
open import Data.Bool

-- map2 : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Colist A → Colist B
-- map2 f [] = []
-- map2 f (x ∷ (♯ [])) = f x ∷ (♯ [])
-- map2 f (x ∷ y ∷ zs) = f x ∷ f y ∷ map2 f zs

-- nats : Colist ℕ 
-- nats = 0 ∷ map suc nats

-- nats2 : Colist ℕ
-- nats2 = 0 ∷ map2 suc nats2      

filter : ∀ {a} {A : Set a} → (A → Bool) → Colist A → Colist A
filter f [] = [] 
filter f (x ∷ xs) with f x
filter f (x ∷ xs) | true = x ∷ (♯ (filter f (♭ xs)))
filter f (x ∷ xs) | false = filter f (♭ xs)

from : ℕ → Colist ℕ
from n = n ∷ (♯ (from (suc n)))

nats : Colist ℕ
nats = from zero

odd : ℕ → Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc  n)) = odd n

test = filter odd nats 

-- map2 : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Colist A → Colist B
-- map2 f [] = []
-- map2 f (x ∷ (♯ [])) = f x ∷ (♯ [])
-- map2 f (x ∷ y ∷ zs) = f x ∷ f y ∷ map2 f zs

-- nats : Colist ℕ 
-- nats = 0 ∷ map suc nats

-- nats2 : Colist ℕ
-- nats2 = 0 ∷ map2 suc nats2      
