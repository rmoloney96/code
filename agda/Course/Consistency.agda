module Consistency where

open import Data.Nat
open import Data.Product
open import SmallStepEval
open import OperationalSemantics

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

E⇓n⇒E⟶⋆n : ∀ {E n} → E ⇓ num n → E ⟶⋆ num n
E⇓n⇒E⟶⋆n n⇓n = k⟶⋆ (zero , z⟶)
E⇓n⇒E⟶⋆n (E⊕E Bs Bs₁)                      with E⇓n⇒E⟶⋆n Bs | E⇓n⇒E⟶⋆n Bs₁
E⇓n⇒E⟶⋆n (E⊕E {E₁} {E₂} {n₁} {n₂} Bs Bs₁) | k⟶⋆ (k , P)     | res          with ⊕₁context E₁ E₂ n₁ k P
E⇓n⇒E⟶⋆n (E⊕E {E₁} {E₂} {n₁} {n₂} Bs Bs₁) | k⟶⋆ (k , P)     | k⟶⋆ (l , Q) | res with ⊕₂context E₂ n₁ n₂ l Q
E⇓n⇒E⟶⋆n (E⊕E Bs Bs₁)                      | k⟶⋆ (k , P)     | k⟶⋆ (l , Q) | k⟶⋆ (m , O) | k⟶⋆ (r , L) with add⟶⟨k⟩ O L
E⇓n⇒E⟶⋆n (E⊕E Bs Bs₁)                      | k⟶⋆ (k , P)     | k⟶⋆ (l , Q) | k⟶⋆ (m , O) | k⟶⋆ (r , L) | ans = k⟶⋆ (m + r , ans)

E⟶n⟨k⟩⇒E⇓n : ∀ {E n k} → E ⟶ num n ⟨ k ⟩ → E ⇓ num n
E⟶n⟨k⟩⇒E⇓n z⟶ = n⇓n
E⟶n⟨k⟩⇒E⇓n (sn⟶ x P) with E⟶n⟨k⟩⇒E⇓n P 
E⟶n⟨k⟩⇒E⇓n {E} (sn⟶ x P) | res = {!Er!}

