
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl)
open import Relation.Nullary

module Order where


data All (P : ℕ → Set) : List ℕ → Set where
  []All : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

countDown : ℕ → List ℕ
countDown zero = [ zero ]
countDown (suc n) = (suc n) ∷ countDown n 

_<?_ : ∀ x y → Dec (x < y)
zero <? zero = no (λ ())
zero <? suc y = yes (s≤s z≤n)
suc x <? zero = no (λ ())
suc x <? suc y with x <? y
suc x <? suc y | yes p = yes (s≤s p)
suc x <? suc y | no ¬p = no (λ {(s≤s p) → ¬p p})

FiveLemma : All (λ x → x < 6) (countDown 5)
FiveLemma = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) ∷
              (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) ∷
               (s≤s (s≤s (s≤s (s≤s z≤n))) ∷
                (s≤s (s≤s (s≤s z≤n)) ∷ (s≤s (s≤s z≤n) ∷ (s≤s z≤n ∷ []All)))))

x≤n⇒x≤1+n : ∀ x n → x ≤ n → x ≤ suc n
x≤n⇒x≤1+n zero n p = z≤n
x≤n⇒x≤1+n (suc x) _ (s≤s p) = s≤s (x≤n⇒x≤1+n x _ p)

[P⇒Q]⇒[AllP⇒AllQ] : ∀ {P Q} L →  (∀ x → P x → Q x) → All P L → All Q L
[P⇒Q]⇒[AllP⇒AllQ] P Q .[] f []All = []All
[P⇒Q]⇒[AllP⇒AllQ] P Q _ f (x₁ ∷ allp) = f _ x₁ ∷ [P⇒Q]⇒[AllP⇒AllQ] P Q _ f allp 

GeneralN : ∀ n → All (λ x → x < suc n) (countDown n)
GeneralN zero = s≤s z≤n ∷ []All
GeneralN (suc n) with GeneralN n  
GeneralN (suc n) | res = (s≤s (s≤s ≤-refl)) ∷ [P⇒Q]⇒[AllP⇒AllQ] (λ z → suc z ≤ suc n) (λ z → suc z ≤ suc (suc n)) (countDown n) (λ x → x≤n⇒x≤1+n (suc x) (suc n)) res 
