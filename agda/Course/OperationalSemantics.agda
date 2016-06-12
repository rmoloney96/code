
module Simplified where

open import Data.Nat

data Exp : Set where
  num : ℕ → Exp
  _⊕_ : Exp → Exp → Exp

-- Big step operational semantics

infix 10 _⇓_ 
data _⇓_ : Exp → Exp → Set where
  n⇓n : ∀ {n} →

      -------------
      num n ⇓ num n
      
  E⊕E : ∀ {E₁ E₂ n₁ n₂} →
  
      E₁ ⇓ num n₁ → E₂ ⇓ num n₂ →
      ---------------------------------
         E₁ ⊕ E₂ ⇓ num (n₁ + n₂)
  

-- Need for Σ which gives us specifications / existentials.
open import Data.Product

-- Σ[ n ∈ ℕ ] P
-- We can read this as: There exists an n in ℕ such that P
---
-- It is a type of pairs, which has a witness (of type ℕ in this case) and a proof
-- that P holds of that witness.
--
evalBig : ∀ E → Σ[ n ∈ ℕ ] E ⇓ num n
evalBig (num x) = x , n⇓n
evalBig (e ⊕ e₁) with evalBig e | evalBig e₁
evalBig (e ⊕ e₁) | n , proof_n | m , proof_m = n + m , E⊕E proof_n proof_m

example⇓ : num 3 ⊕ (num 2 ⊕ num 1) ⇓ num 6
example⇓ = proj₂ (evalBig (num 3 ⊕ (num 2 ⊕ num 1)))

-- Small step operational semantics
infix 8 _⟶_
data _⟶_ : Exp → Exp → Set where
  +⟶ : ∀ {n m} →
  
          -----------------------------
          num n ⊕ num m ⟶ num (n + m)

  ⊕₁⟶ : ∀ {E₁ E₁' E₂} →

          E₁ ⟶ E₁' → 
          ---------------------
          E₁ ⊕ E₂ ⟶ E₁' ⊕ E₂

  ⊕₂⟶ : ∀ {n E₂ E₂'} →

          E₂ ⟶ E₂' →  
          --------------------
          num n ⊕ E₂ ⟶ num n ⊕ E₂'

example⟶₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ (num 8 ⊕ num 1)
example⟶₁ = ⊕₁⟶ +⟶ 
example⟶₂ : (num 10) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ num 9
example⟶₂ = ⊕₂⟶ +⟶

infix 8 _⟶ch_
data _⟶ch_ : Exp → Exp → Set where
  +⟶ch : ∀ {n m} →
  
          -----------------------------
          num n ⊕ num m ⟶ch num (n + m)

  ⊕₁⟶ch : ∀ {E₁ E₁' E₂} →

          E₁ ⟶ch E₁' → 
          ---------------------
          E₁ ⊕ E₂ ⟶ch E₁' ⊕ E₂

  ⊕₂⟶ch : ∀ {E₁ E₂ E₂'} →

          E₂ ⟶ch E₂' →  
          --------------------
          E₁ ⊕ E₂ ⟶ch E₁ ⊕ E₂'


example⟶ch₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ch num 10 ⊕ (num 8 ⊕ num 1)
example⟶ch₁ = ⊕₁⟶ch +⟶ch
example⟶ch₂ : (num 10) ⊕ (num 8 ⊕ num 1) ⟶ch num 10 ⊕ num 9
example⟶ch₂ = ⊕₂⟶ch +⟶ch

⟶⇒⟶ch : ∀ {E₁ E₂} → (E₁ ⟶ E₂) → (E₁ ⟶ch E₂)
⟶⇒⟶ch +⟶ = +⟶ch
⟶⇒⟶ch (⊕₁⟶ d) = ⊕₁⟶ch (⟶⇒⟶ch d)
⟶⇒⟶ch (⊕₂⟶ d) = ⊕₂⟶ch (⟶⇒⟶ch d)

{- Not a theorem! -}
⟶ch⇒⟶ : ∀ {E₁ E₂} → (E₁ ⟶ch E₂) → (E₁ ⟶ E₂)
⟶ch⇒⟶ +⟶ch = +⟶
⟶ch⇒⟶ (⊕₁⟶ch d) = ⊕₁⟶ (⟶ch⇒⟶ d)
⟶ch⇒⟶ (⊕₂⟶ch d) = {!!} {-  E₂ ⟶ E₂'                  No applicable rule
                                 ———————————————————             
                                 (E₁ ⊕ E₂) ⟶ (E₁ ⊕ E₂')  -}

-- Bring in Agda's notion of negation (a map to a datatype of no constructors)
open import Data.Empty
open import Relation.Nullary

-- We can prove it is not a theorem by exhibiting a counter-example using the case above.
-- i.e. choose to reduce the second antecedent first.
⟶ch¬⇒⟶ : ¬ (∀ E₁ E₂ → (E₁ ⟶ch E₂) → (E₁ ⟶ E₂))
⟶ch¬⇒⟶ f with f ((num 0 ⊕ num 0) ⊕ (num 0 ⊕ num 0)) ((num 0 ⊕ num 0) ⊕ num 0) (⊕₂⟶ch +⟶ch)
⟶ch¬⇒⟶ f | ()

data _⟶_⟨_⟩ : Exp → Exp → ℕ → Set where
  z⟶ : ∀ {E₁} →
  
                 --------------
                 E₁ ⟶ E₁ ⟨ 0 ⟩
                 
  sn⟶ : ∀ {E₁ E₂ E₃ n} →

                 E₁ ⟶ E₂ ⟨ n ⟩ → E₂ ⟶ E₃ →  
                 -----------------------------
                 E₁ ⟶ E₃ ⟨ 1 + n ⟩ 


data _⟶⋆_ : Exp → Exp → Set where
  k⟶⋆ : ∀ {E₁ E₂} →

                 Σ[ k ∈ ℕ ] E₁ ⟶ E₂ ⟨ k ⟩ →
                 --------------------------
                 E₁ ⟶⋆ E₂ 

-- We need a notion of equality - we'll use Agda's 
open import Relation.Binary.PropositionalEquality

⇓Consistency : ∀ {E n m} → (E ⇓ n) → (E ⇓ m) → n ≡ m
⇓Consistency n⇓n n⇓n = refl
⇓Consistency (E⊕E d₁ d₂) (E⊕E d₃ d₄) with ⇓Consistency d₁ d₃ | ⇓Consistency d₂ d₄
⇓Consistency (E⊕E d₁ d₂) (E⊕E d₃ d₄) | refl | refl = refl 

{-
∣_∣  : ∀ {k E E'} → E ⟶ E' ⟨ k ⟩ → ℕ
∣_∣ {k} e = k

∣_∣⋆  : ∀ {E E'} → E ⟶⋆ E' → ℕ
∣ k⟶⋆ (n , p) ∣⋆ = ∣ p ∣

⟶⋆Diamond : ∀ {E E₁ E₂} → (E ⟶⋆ E₁) → (E ⟶⋆ E₂) → Σ[ E₃ ∈ Exp ] (E₁ ⟶⋆ E₃ × E₂ ⟶⋆ E₃)
⟶⋆Diamond (k⟶⋆ (zero , z⟶)) (k⟶⋆ (n , p)) = _ , k⟶⋆ (n , p) , k⟶⋆ (zero , z⟶)
⟶⋆Diamond (k⟶⋆ (suc n , p)) (k⟶⋆ (zero , z⟶)) = _ , k⟶⋆ (zero , z⟶) , k⟶⋆ (suc n , p)
⟶⋆Diamond (k⟶⋆ (suc n , sn⟶ p x)) (k⟶⋆ (suc m , sn⟶ q x₁)) with ⟶⋆Diamond {!!} {!!} --  (k⟶⋆ (n , p)) (k⟶⋆ (m , q))
⟶⋆Diamond (k⟶⋆ (suc n , sn⟶ p x)) (k⟶⋆ (suc m , sn⟶ q x₁)) | res = {!!}
-}

{-
⟶⋆Consistency : ∀ {E n m} → (E ⟶⋆ num n) × (E ⟶⋆ num m) → n ≡ m
⟶⋆Consistency (k⟶⋆ _ _ (zero , z⟶ _) , k⟶⋆ _ _ (zero , z⟶ _)) = refl
⟶⋆Consistency (k⟶⋆ _ _ (zero , z⟶ _) , k⟶⋆ _ _ (suc n , sn⟶ _ E₂ _ .n () x))
⟶⋆Consistency (k⟶⋆ _ _ (suc k₁ , sn⟶ _ E₂ _ .k₁ () P) , k⟶⋆ _ _ (.0 , z⟶ _))
⟶⋆Consistency (k⟶⋆ E₁ _ (suc k₁ , sn⟶ .E₁ E₂ _ .k₁ x P) , k⟶⋆ .E₁ _ (.(suc n) , sn⟶ .E₁ E₃ _ n x₁ Q)) = {!!}
-}

