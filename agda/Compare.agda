module Compare where 

open import Function 
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary hiding (_⇒_)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl ; trans to ≤-trans)
open import Data.Empty
open import Relation.Unary
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

n≡m⇒n≰sm : ∀ n m → n ≡ m → ¬(suc n ≤ m)
n≡m⇒n≰sm zero    .zero    refl () 
n≡m⇒n≰sm (suc n) .(suc n) refl (s≤s p) = n≡m⇒n≰sm n n refl p

¬s≡s : ∀ {n m} → ¬(suc n ≡ suc m) → ¬(n ≡ m)
¬s≡s {n} {.n} ¬p refl = ¬p refl

≠∨≤⇒< : ∀ {n m} → ¬(n ≡ m) → n ≤ m → n < m
≠∨≤⇒< {zero}  {zero}    ¬p z≤n       with ¬p refl 
≠∨≤⇒< {zero}  {zero}    ¬p z≤n       | () 
≠∨≤⇒< {zero}  {suc m}   ¬p z≤n       = s≤s z≤n
≠∨≤⇒< {suc n} {zero}    ¬p () 
≠∨≤⇒< {suc n} {suc m}   ¬p (s≤s ple) = s≤s (≠∨≤⇒< (¬s≡s ¬p) ple)

¬sn≤n : ∀ n → ¬(1 + n ≤ n)
¬sn≤n .(suc n) (s≤s {.(suc n)} {n} m≤n) = ¬sn≤n n m≤n 

¬ssn≤n : ∀ n → ¬(2 + n ≤ n)
¬ssn≤n .(suc n) (s≤s {.(suc (suc n))} {n} m≤n) = ¬ssn≤n n m≤n

¬s≤s : ∀ {n m} → ¬(suc n ≤ suc m) → ¬(n ≤ m)
¬s≤s {n} {m} ¬p q = ¬p (s≤s q) 

≰∨≠⇒> : ∀ {n m} → ¬(n ≡ m) → ¬(n ≤ m) → n > m
≰∨≠⇒> {zero}  {zero}  ¬p ¬q with ¬p refl 
≰∨≠⇒> {zero}  {zero}  ¬p ¬q | () 
≰∨≠⇒> {suc n} {zero}  ¬p ¬q = s≤s z≤n 
≰∨≠⇒> {zero}  {suc m} ¬p ¬q with ¬q z≤n
≰∨≠⇒> {zero}  {suc m} ¬p ¬q | ()
≰∨≠⇒> {suc n} {suc m} ¬p ¬q = s≤s (≰∨≠⇒> (¬s≡s ¬p) (¬s≤s ¬q))

cmp : Trichotomous _≡_ _<_
cmp n m with n ≟ m 
cmp n m | yes p = tri≈ (n≡m⇒n≰sm n m p) p (n≡m⇒n≰sm m n (sym p)) 
cmp n m | no ¬p with m ≤? n
cmp n m | no ¬p | yes q = tri> (λ x → ⊥-elim (¬sn≤n n (≤-trans x q))) ¬p (≠∨≤⇒< (¬p ∘ sym) q) 
cmp n m | no ¬p | no ¬q with ≰∨≠⇒> (¬p ∘ sym) ¬q 
cmp n m | no ¬p | no ¬q | r = tri< (≰∨≠⇒> (¬p ∘ sym) ¬q) ¬p (λ x → ⊥-elim (¬ssn≤n n (≤-trans (s≤s r) x)))
