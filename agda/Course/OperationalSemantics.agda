
module OperationalSemantics where

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
  
      E₁ ⇓ num n₁  →  E₂ ⇓ num n₂ →
      ----------------------------
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
          --------------------------
          num n ⊕ E₂ ⟶ num n ⊕ E₂'

example⟶₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ (num 8 ⊕ num 1)
example⟶₁ = ⊕₁⟶ +⟶ 
example⟶₂ : (num 10) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ num 9
example⟶₂ = ⊕₂⟶ +⟶

infix 8 _⟶ch_
data _⟶ch_ : Exp → Exp → Set where
  +⟶ch : ∀ {n m} →
  
          -------------------------------
          num n ⊕ num m ⟶ch num (n + m)

  ⊕₁⟶ch : ∀ {E₁ E₁' E₂} →

          E₁ ⟶ch E₁' → 
          ----------------------
          E₁ ⊕ E₂ ⟶ch E₁' ⊕ E₂

  ⊕₂⟶ch : ∀ {E₁ E₂ E₂'} →

          E₂ ⟶ch E₂' →  
          ----------------------
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

        E₁ ⟶ E₂ →  E₂ ⟶ E₃ ⟨ n ⟩ →  
        ----------------------------
             E₁ ⟶ E₃ ⟨ 1 + n ⟩ 


data _⟶⋆_ : Exp → Exp → Set where
  k⟶⋆ : ∀ {E₁ E₂} →

        Σ[ k ∈ ℕ ] E₁ ⟶ E₂ ⟨ k ⟩ →
        --------------------------
               E₁ ⟶⋆ E₂ 

-- Small step reductions are like numbers with extra indices, so we can add them.
add⟶⟨k⟩ : ∀ {E E₁ E₂ k l} → E ⟶ E₁ ⟨ k ⟩ → E₁ ⟶ E₂ ⟨ l ⟩ → E ⟶ E₂ ⟨ k + l ⟩
add⟶⟨k⟩ z⟶ b = b
add⟶⟨k⟩ (sn⟶ a x) b = sn⟶ a (add⟶⟨k⟩ x b)

-- We need a notion of equality - we'll use Agda's 
open import Relation.Binary.PropositionalEquality

⇓Consistency : ∀ {E n m} → (E ⇓ n) → (E ⇓ m) → n ≡ m
⇓Consistency n⇓n n⇓n = refl
⇓Consistency (E⊕E d₁ d₂) (E⊕E d₃ d₄) with ⇓Consistency d₁ d₃ | ⇓Consistency d₂ d₄
⇓Consistency (E⊕E d₁ d₂) (E⊕E d₃ d₄) | refl | refl = refl

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

data Val : Exp → Set where
  numVal : ∀ n → Val (num n)

-- We want sums
open import Data.Sum

⟶progress : ∀ E → Val E ⊎ Σ[ E' ∈ Exp ] E ⟶ E' 
⟶progress (num x) = inj₁ (numVal x)
⟶progress (E ⊕ E₁)              with ⟶progress E
⟶progress (_ ⊕ E₁)              | inj₁ (numVal x) with ⟶progress E₁
⟶progress (.(num n) ⊕ .(num m)) | inj₁ (numVal n) | inj₁ (numVal m) = inj₂ (num (n + m) , +⟶)
⟶progress (.(num n) ⊕ E₁)       | inj₁ (numVal n) | inj₂ (E' , P) = inj₂ ((num n ⊕ E') , ⊕₂⟶ P)
⟶progress (E ⊕ E₁)              | inj₂ (E' , P) = inj₂ ((E' ⊕ E₁) , ⊕₁⟶ P)

∣_∣ : Exp → ℕ
∣ num x ∣ = 1
∣ E ⊕ E₁ ∣ = 1 + ∣ E ∣ + ∣ E₁ ∣

data Acc {A : Set} (_≺_ : A → A → Set) (x : A) : Set where
  acc : (g : (∀ y → y ≺ x → Acc _≺_ y)) → Acc _≺_ x

WellFounded : {A : Set} → (_≺_ : A → A → Set) → Set
WellFounded R = ∀ x → Acc R x

ℕ-wf : WellFounded _<′_
ℕ-wf n = acc (aux n)
  where aux : ∀ x y → y <′ x → Acc _<′_ y
        aux .(suc y) y ≤′-refl = ℕ-wf y
        aux .(suc x) y (≤′-step {x} p) = aux x y p 

_≺_ : Exp → Exp → Set
x ≺ y = ∣ x ∣ <′ ∣ y ∣ 

Acc<⇒Acc≺ : ∀ x → Acc  _<′_ (∣ x ∣) → Acc _≺_ x
Acc<⇒Acc≺ x (acc g) = acc (λ y p → Acc<⇒Acc≺ y (g ∣ y ∣ p))

wf≺ : WellFounded _≺_
wf≺ x = Acc<⇒Acc≺ x (ℕ-wf ∣ x ∣)

open import Data.Nat.Properties

E≺E⊕E₁ : ∀ E E₁ → E ≺ (E ⊕ E₁)
E≺E⊕E₁ E E₁ = m≤′m+n (suc ∣ E ∣) ∣ E₁ ∣

open import Data.Nat.Properties.Simple

E₁≺E⊕E₁ : ∀ E E₁ → E₁ ≺ (E ⊕ E₁)
E₁≺E⊕E₁ E E₁ rewrite +-comm ∣ E ∣ ∣ E₁ ∣ = m≤′m+n (suc ∣ E₁ ∣) ∣ E ∣

evalAux : ∀ E → Acc _≺_ E → Σ[ n ∈ ℕ ] E ⟶⋆ num n
evalAux (num x) _ = x , k⟶⋆ (zero , z⟶)
evalAux (E ⊕ E₁) (acc g) with evalAux E (g E (E≺E⊕E₁ E E₁))
evalAux (E ⊕ E₁) (acc g) | n , P with evalAux E₁ (g  E₁ (E₁≺E⊕E₁ E E₁))
evalAux (E ⊕ E₁) (acc g) | n , P | m , Q = n + m , {!!} 

n≤m⇒n+o≤m+o : ∀ {n m o} → n ≤ m → n + o ≤ m + o
n≤m⇒n+o≤m+o {zero} {m} {o} z≤n = n≤m+n m o
n≤m⇒n+o≤m+o (s≤s p) = s≤s (n≤m⇒n+o≤m+o p)

