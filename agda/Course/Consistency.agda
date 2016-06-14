module Consistency where

open import Data.Nat
open import Data.Product
--open import SmallStepEval
open import OperationalSemantics
open import Relation.Binary.PropositionalEquality

⟶deterministic : ∀ {E E₁ E₂} → E ⟶ E₁ → E ⟶ E₂ → E₁ ≡ E₂
⟶deterministic +⟶ +⟶ = refl
⟶deterministic +⟶ (⊕₁⟶ ())
⟶deterministic +⟶ (⊕₂⟶ ())
⟶deterministic (⊕₁⟶ ()) +⟶
⟶deterministic (⊕₁⟶ p) (⊕₁⟶ q) = cong₂ _⊕_ (⟶deterministic p q) refl
⟶deterministic (⊕₁⟶ ()) (⊕₂⟶ q)
⟶deterministic (⊕₂⟶ ()) +⟶
⟶deterministic (⊕₂⟶ p) (⊕₁⟶ ())
⟶deterministic (⊕₂⟶ p) (⊕₂⟶ q) = cong₂ _⊕_ refl ((⟶deterministic p q))

{- We not only get the same answer, but in the same number of steps. -}
⟶⟨k⟩deterministic : ∀ {E n m k l} → E ⟶ num n ⟨ k ⟩ → E ⟶ num m ⟨ l ⟩ → n ≡ m × k ≡ l 
⟶⟨k⟩deterministic z⟶ z⟶ = refl , refl
⟶⟨k⟩deterministic z⟶ (sn⟶ () q)
⟶⟨k⟩deterministic (sn⟶ () p) z⟶
⟶⟨k⟩deterministic (sn⟶ x p) (sn⟶ x₁ q) with ⟶deterministic x x₁
⟶⟨k⟩deterministic (sn⟶ x p) (sn⟶ x₁ q) | refl with ⟶⟨k⟩deterministic p q
⟶⟨k⟩deterministic (sn⟶ x p) (sn⟶ x₁ q) | refl | refl , refl = refl , refl

⟶⋆deterministic : ∀ {E n m} → E ⟶⋆ num n → E ⟶⋆ num m → n ≡ m
⟶⋆deterministic (k⟶⋆ (n , P)) (k⟶⋆ (m , Q)) with ⟶⟨k⟩deterministic P Q
⟶⋆deterministic (k⟶⋆ (n₁ , P)) (k⟶⋆ (.n₁ , Q)) | refl , refl = refl

⇓deterministic : ∀ {E n m} → (E ⇓ n) → (E ⇓ m) → n ≡ m
⇓deterministic n⇓n n⇓n = refl
⇓deterministic (E⊕E d₁ d₂) (E⊕E d₃ d₄) with ⇓deterministic d₁ d₃ | ⇓deterministic d₂ d₄
⇓deterministic (E⊕E d₁ d₂) (E⊕E d₃ d₄) | refl | refl = refl

{-

The proof that:

E ⇓ n  →  E ⟶⋆ num n

-}

-- Small step reductions are like numbers with extra indices, so we can add them.
add⟶⟨k⟩ : ∀ {E E₁ E₂ k l} → E ⟶ E₁ ⟨ k ⟩ → E₁ ⟶ E₂ ⟨ l ⟩ → E ⟶ E₂ ⟨ k + l ⟩
add⟶⟨k⟩ z⟶ b = b
add⟶⟨k⟩ (sn⟶ a x) b = sn⟶ a (add⟶⟨k⟩ x b)

⊕₁context : ∀ E₁ E₂ n k → E₁ ⟶ num n ⟨ k ⟩ → (E₁ ⊕ E₂) ⟶⋆ (num n ⊕ E₂)
⊕₁context .(num n) E₂ n .0 z⟶ = k⟶⋆ (zero , z⟶)
⊕₁context E₁ E₂ n _ (sn⟶ {_} {E₂'} {_} {m} x p) with ⊕₁context E₂' E₂ n m p
⊕₁context E₁ E₂ n _ (sn⟶ x p) | k⟶⋆ (k , Q) = k⟶⋆ (suc k , sn⟶ (⊕₁⟶ x) Q)

⊕₂context : ∀ E n m k → E ⟶ num m ⟨ k ⟩ → (num n ⊕ E) ⟶⋆ (num (n + m))
⊕₂context .(num m) n m .0 z⟶ = k⟶⋆ (suc zero , sn⟶ +⟶ z⟶)
⊕₂context E n m _ (sn⟶ {_} {E₂'} {_} {l} x p) with ⊕₂context E₂' n m l p
⊕₂context E n m _ (sn⟶ x₁ p) | k⟶⋆ (k , P) = k⟶⋆ (suc k , sn⟶ (⊕₂⟶ x₁) P) 

E⇓n⇒E⟶⋆n : ∀ {E n} → E ⇓ n → E ⟶⋆ num n
E⇓n⇒E⟶⋆n n⇓n = k⟶⋆ (zero , z⟶)
E⇓n⇒E⟶⋆n (E⊕E Bs Bs₁)                      with E⇓n⇒E⟶⋆n Bs | E⇓n⇒E⟶⋆n Bs₁
E⇓n⇒E⟶⋆n (E⊕E {E₁} {E₂} {n₁} {n₂} Bs Bs₁) | k⟶⋆ (k , P)     | res          with ⊕₁context E₁ E₂ n₁ k P
E⇓n⇒E⟶⋆n (E⊕E {E₁} {E₂} {n₁} {n₂} Bs Bs₁) | k⟶⋆ (k , P)     | k⟶⋆ (l , Q) | res with ⊕₂context E₂ n₁ n₂ l Q
E⇓n⇒E⟶⋆n (E⊕E Bs Bs₁)                     | k⟶⋆ (k , P)     | k⟶⋆ (l , Q) | k⟶⋆ (m , O) | k⟶⋆ (r , L) with add⟶⟨k⟩ O L
E⇓n⇒E⟶⋆n (E⊕E Bs Bs₁) | k⟶⋆ (k , P)     | k⟶⋆ (l , Q)     | k⟶⋆ (m , O) | k⟶⋆ (r , L) | ans = k⟶⋆ (m + r , ans)

{-

The proof that:

E ⟶⋆ num n  →  E ⇓ n

-}
E⟶E'⇒E'⇓n⇒E⇓n : ∀ {E E' n} → E ⟶ E' → E' ⇓ n → E ⇓ n
E⟶E'⇒E'⇓n⇒E⇓n +⟶ n⇓n = E⊕E n⇓n n⇓n
E⟶E'⇒E'⇓n⇒E⇓n (⊕₁⟶ p) (E⊕E q q₁) = E⊕E (E⟶E'⇒E'⇓n⇒E⇓n p q) q₁
E⟶E'⇒E'⇓n⇒E⇓n (⊕₂⟶ p) (E⊕E q q₁) = E⊕E q (E⟶E'⇒E'⇓n⇒E⇓n p q₁)

E⟶n⟨k⟩⇒E⇓n : ∀ {E n k} → E ⟶ num n ⟨ k ⟩ → E ⇓ n
E⟶n⟨k⟩⇒E⇓n z⟶ = n⇓n
E⟶n⟨k⟩⇒E⇓n (sn⟶ x P) with E⟶n⟨k⟩⇒E⇓n P
E⟶n⟨k⟩⇒E⇓n (sn⟶ x P) | O = E⟶E'⇒E'⇓n⇒E⇓n x O

E⟶⋆n⇒E⇓n : ∀ {E n} → E ⟶⋆ num n → E ⇓ n
E⟶⋆n⇒E⇓n (k⟶⋆ (_ , P)) = E⟶n⟨k⟩⇒E⇓n P

{-

The proof that:

E ⟶ch⋆ (num n)  →  E ⇓ n

-}
E⟶ch-E'⇒E'⇓n⇒E⇓n : ∀ {E E' n} → E ⟶ch E' → E' ⇓ n → E ⇓ n
E⟶ch-E'⇒E'⇓n⇒E⇓n +⟶ch n⇓n = E⊕E n⇓n n⇓n
E⟶ch-E'⇒E'⇓n⇒E⇓n (⊕₁⟶ch p) (E⊕E x x₁) = E⊕E (E⟶ch-E'⇒E'⇓n⇒E⇓n p x) x₁
E⟶ch-E'⇒E'⇓n⇒E⇓n (⊕₂⟶ch p) (E⊕E x x₁) = E⊕E x (E⟶ch-E'⇒E'⇓n⇒E⇓n p x₁)

E⟶ch-n⟨k⟩⇒E⇓n : ∀ {E n k} → E ⟶ch num n ⟨ k ⟩ → E ⇓ n
E⟶ch-n⟨k⟩⇒E⇓n z⟶ch = n⇓n
E⟶ch-n⟨k⟩⇒E⇓n (sn⟶ch x P) with E⟶ch-n⟨k⟩⇒E⇓n P
E⟶ch-n⟨k⟩⇒E⇓n (sn⟶ch x P) | O = E⟶ch-E'⇒E'⇓n⇒E⇓n x O

E⟶ch⋆⇒E⇓n : ∀ {E n} → E ⟶ch⋆ num n  → E ⇓ n
E⟶ch⋆⇒E⇓n (k⟶ch⋆ (_ , P)) = E⟶ch-n⟨k⟩⇒E⇓n P

{-
We'll use ⇓ to establish determinacy for ⟶ch⋆
-}
⟶ch⋆deterministic : ∀ {E n m} → E ⟶ch⋆ num n → E ⟶ch⋆ num m → n ≡ m
⟶ch⋆deterministic p q = ⇓deterministic (E⟶ch⋆⇒E⇓n p) (E⟶ch⋆⇒E⇓n q)
