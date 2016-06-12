
module OperationalSemantics where

open import Data.Nat

data E : Set where
  num : ℕ → E
  _⊕_ : E → E → E
  _⊗_ : E → E → E

-- Big step operational semantics

infix 10 _⇓_ 
data _⇓_ : E → E → Set where
  n⇓n : ∀ n →

      -------------
      num n ⇓ num n
      
  E⊕E : ∀ E₁ E₂ n₁ n₂ →
  
      E₁ ⇓ num n₁ → E₂ ⇓ num n₂ →
      ---------------------------------
         E₁ ⊕ E₂ ⇓ num (n₁ + n₂)
  
  E⊗E : ∀ E₁ E₂ n₁ n₂ →
  
      E₁ ⇓ num n₁ → E₂ ⇓ num n₂ →
      ---------------------------------
         E₁ ⊗ E₂ ⇓ num (n₁ * n₂)

-- Need for Σ which gives us specifications / existentials.
open import Data.Product

-- Σ[ n ∈ ℕ ] P
-- We can read this as: There exists an n in ℕ such that P
---
-- It is a type of pairs, which has a witness (of type ℕ in this case) and a proof
-- that P holds of that witness.
--
evalBig : ∀ E → Σ[ n ∈ ℕ ] E ⇓ num n
evalBig (num x) = x , n⇓n x
evalBig (e ⊕ e₁) with evalBig e | evalBig e₁
evalBig (e ⊕ e₁) | n , proof_n | m , proof_m = n + m , E⊕E e e₁ n m proof_n proof_m
evalBig (e ⊗ e₁) with evalBig e | evalBig e₁
evalBig (e ⊗ e₁) | n , proof_n | m , proof_m = n * m , E⊗E e e₁ n m proof_n proof_m

example⇓ : num 3 ⊕ (num 2 ⊕ num 1) ⇓ num 6
example⇓ = proj₂ (evalBig (num 3 ⊕ (num 2 ⊕ num 1)))

-- Small step operational semantics
infix 8 _⟶_
data _⟶_ : E → E → Set where
  +⟶ : ∀ n m →
  
          -----------------------------
          num n ⊕ num m ⟶ num (n + m)

  *⟶ : ∀ n m →
  
          -----------------------------
          num n ⊗ num m ⟶ num (n * m)

  ⊕₁⟶ : ∀ E₁ E₁' E₂ →

          E₁ ⟶ E₁' → 
          ---------------------
          E₁ ⊕ E₂ ⟶ E₁' ⊕ E₂

  ⊕₂⟶ : ∀ n E₂ E₂' →

          E₂ ⟶ E₂' →  
          --------------------
          num n ⊕ E₂ ⟶ num n ⊕ E₂'

  ⊗₁⟶ : ∀ E₁ E₁' E₂ →

          E₁ ⟶ E₁' → 
          ---------------------
          E₁ ⊗ E₂ ⟶ E₁' ⊗ E₂

  ⊗₂⟶ : ∀ n E₂ E₂' →

          E₂ ⟶ E₂' → 
          ---------------------
          num n ⊗ E₂ ⟶ num n ⊗ E₂'

example⟶₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ (num 8 ⊕ num 1)
example⟶₁ = ⊕₁⟶ _ _ _ (+⟶ 3 7)
example⟶₂ : (num 10) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ num 9
example⟶₂ = ⊕₂⟶ _ _ _ (+⟶ 8 1)

infix 8 _⟶ch_
data _⟶ch_ : E → E → Set where
  +⟶ch : ∀ n m →
  
          -----------------------------
          num n ⊕ num m ⟶ch num (n + m)

  *⟶ch : ∀ n m →
  
          -----------------------------
          num n ⊗ num m ⟶ch num (n * m)

  ⊕₁⟶ch : ∀ E₁ E₁' E₂ →

          E₁ ⟶ch E₁' → 
          ---------------------
          E₁ ⊕ E₂ ⟶ch E₁' ⊕ E₂

  ⊕₂⟶ch : ∀ E₁ E₂ E₂' →

          E₂ ⟶ch E₂' →  
          --------------------
          E₁ ⊕ E₂ ⟶ch E₁ ⊕ E₂'

  ⊗₁⟶ch : ∀ E₁ E₁' E₂ →

          E₁ ⟶ch E₁' → 
          ---------------------
          E₁ ⊗ E₂ ⟶ch E₁' ⊗ E₂

  ⊗₂⟶ch : ∀ E₁ E₂ E₂' →

          E₂ ⟶ch E₂' → 
          ---------------------
          E₁ ⊗ E₂ ⟶ch E₁ ⊗ E₂'

example⟶ch₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ch num 10 ⊕ (num 8 ⊕ num 1)
example⟶ch₁ = ⊕₁⟶ch _ _ _ (+⟶ch 3 7)
example⟶ch₂ : (num 10) ⊕ (num 8 ⊕ num 1) ⟶ch num 10 ⊕ num 9
example⟶ch₂ = ⊕₂⟶ch _ _ _ (+⟶ch 8 1)

⟶⇒⟶ch : ∀ {E₁ E₂} → (E₁ ⟶ E₂) → (E₁ ⟶ch E₂)
⟶⇒⟶ch (+⟶ n m) = +⟶ch n m
⟶⇒⟶ch (*⟶ n m) = *⟶ch n m
⟶⇒⟶ch (⊕₁⟶ E₁ E₁' E₂ d) = ⊕₁⟶ch E₁ E₁' E₂ (⟶⇒⟶ch d)
⟶⇒⟶ch (⊕₂⟶ n E₂ E₂' d) = ⊕₂⟶ch (num n) E₂ E₂' (⟶⇒⟶ch d)
⟶⇒⟶ch (⊗₁⟶ E₁ E₁' E₂ d) = ⊗₁⟶ch E₁ E₁' E₂ (⟶⇒⟶ch d)
⟶⇒⟶ch (⊗₂⟶ n E₂ E₂' d) = ⊗₂⟶ch (num n) E₂ E₂' (⟶⇒⟶ch d)

{- Not a theorem! -}
⟶ch⇒⟶ : ∀ {E₁ E₂} → (E₁ ⟶ch E₂) → (E₁ ⟶ E₂)
⟶ch⇒⟶ (+⟶ch n m) = +⟶ n m
⟶ch⇒⟶ (*⟶ch n m) = *⟶ n m
⟶ch⇒⟶ (⊕₁⟶ch E₁ E₁' E₂ d) = ⊕₁⟶ E₁ E₁' E₂ (⟶ch⇒⟶ d)
⟶ch⇒⟶ (⊕₂⟶ch E₁ E₂ E₂' d) = {!!} {-  E₂ ⟶ E₂'                  No applicable rule
                                           ———————————————————             
                                           (E₁ ⊕ E₂) ⟶ (E₁ ⊕ E₂')  -}
⟶ch⇒⟶ (⊗₁⟶ch E₁ E₁' E₂ d) = ⊗₁⟶ E₁ E₁' E₂ (⟶ch⇒⟶ d)
⟶ch⇒⟶ (⊗₂⟶ch E₁ E₂ E₂' d) = {!!} {-  E₂ ⟶ E₂'                  No applicable rule
                                           ———————————————————             
                                           (E₁ ⊗ E₂) ⟶ (E₁ ⊗ E₂')  -}

data _⟶_⟨_⟩ : E → E → ℕ → Set where
  z⟶ : ∀ E₁ →
  
                 --------------
                 E₁ ⟶ E₁ ⟨ 0 ⟩
                 
  sn⟶ : ∀ E₁ E₂ E₃ n →

                 E₁ ⟶ E₂ ⟨ n ⟩  →  E₂ ⟶ E₃ →
                 -----------------------------
                 E₁ ⟶ E₃ ⟨ 1 + n ⟩ 


data _⟶⋆_ : E → E → Set where
  k⟶⋆ : ∀ E₁ E₂ →

                 Σ[ k ∈ ℕ ] E₁ ⟶ E₂ ⟨ k ⟩ →
                 --------------------------
                 E₁ ⟶⋆ E₂ 

_FinalAnswerOf_ : ℕ → E → Set
_FinalAnswerOf_ n E = E ⟶⋆ num n

-- We need a notion of equality - we'll use Agda's 
open import Relation.Binary.PropositionalEquality

⇓Consistency : ∀ {E n m} → (E ⇓ n) × (E ⇓ m) → n ≡ m
⇓Consistency (n⇓n n , n⇓n .n) = refl
⇓Consistency (E⊕E E₁ E₂ n₃ n₄ d₁ d₂ , E⊕E .E₁ .E₂ n₁ n₂ d₃ d₄) with ⇓Consistency (d₁ , d₃) | ⇓Consistency (d₂ , d₄)
⇓Consistency (E⊕E E₁ E₂ n₁ n₂ d₁ d₂ , E⊕E .E₁ .E₂ .n₁ .n₂ d₃ d₄) | refl | refl = refl 
⇓Consistency (E⊗E E₁ E₂ n₃ n₄ d₁ d₂ , E⊗E .E₁ .E₂ n₁ n₂ d₃ d₄) with ⇓Consistency (d₁ , d₃) | ⇓Consistency (d₂ , d₄)
⇓Consistency (E⊗E E₁ E₂ n₁ n₂ d₁ d₂ , E⊗E .E₁ .E₂ .n₁ .n₂ d₃ d₄) | refl | refl = refl 
