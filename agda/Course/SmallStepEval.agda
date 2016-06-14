module SmallStepEval where

open import OperationalSemantics
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Product
open import Induction.WellFounded
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

{-
The size of an expression will be used to find a well founded relation on terms
-}

∣_∣ : Exp → ℕ
∣ num x ∣ = 1
∣ E ⊕ E₁ ∣ = 1 + ∣ E ∣ + ∣ E₁ ∣

ℕ-wf : Well-founded _<′_
ℕ-wf n = acc (aux n)
  where aux : ∀ x y → y <′ x → Acc _<′_ y
        aux .(suc y) y ≤′-refl = ℕ-wf y
        aux .(suc x) y (≤′-step {x} p) = aux x y p 

_≺_ : Exp → Exp → Set
x ≺ y = ∣ x ∣ <′ ∣ y ∣ 

open Inverse-image {_<_ = _<′_} ∣_∣ renaming (well-founded to well-founded-ii)

{- The inverse image of a well founded relation is well founded. -}
wf≺ : Well-founded _≺_
wf≺ = well-founded-ii ℕ-wf

_⟵_ : Exp → Exp → Set
E' ⟵ E = E ⟶ E'

m≤′m'⇒m+n≤′m+n : ∀ m m' n → m ≤′ m' → n + m ≤′ n + m'
m≤′m'⇒m+n≤′m+n m m' zero p = p
m≤′m'⇒m+n≤′m+n m m' (suc n) p with m≤′m'⇒m+n≤′m+n m m' n p
m≤′m'⇒m+n≤′m+n m m' (suc n) p | res = s≤′s res 

E≺E₁⇒E'⊕E₁≺E⊕E₁ : ∀ E E' E₁ → E' ≺ E → (E' ⊕ E₁) ≺ (E ⊕ E₁)
E≺E₁⇒E'⊕E₁≺E⊕E₁ E E' E₁ p with m≤′m'⇒m+n≤′m+n (suc ∣ E' ∣) ∣ E ∣ ∣ E₁ ∣ p
E≺E₁⇒E'⊕E₁≺E⊕E₁ E E' E₁ p | res rewrite +-comm (suc ∣ E' ∣) ∣ E₁ ∣
  = s≤′s (aux (∣ E₁ ∣) (∣ E' ∣) (∣ E ∣) res) 
  where aux : ∀ n m o → n + suc m ≤′ n + o → n + suc m ≤′ o + n
        aux n m o p rewrite +-comm n o = p

⟵⇒<′ : ∀ {E E'} → E ⟵ E' → E ≺ E' 
⟵⇒<′ +⟶ = ≤′-step ≤′-refl
⟵⇒<′ (⊕₁⟶ p) with ⟵⇒<′ p
⟵⇒<′ (⊕₁⟶ {E₁} {E₁'} {E₂} p) | Q = E≺E₁⇒E'⊕E₁≺E⊕E₁ E₁ E₁' E₂ Q
⟵⇒<′ (⊕₂⟶ p) with ⟵⇒<′ p
⟵⇒<′ (⊕₂⟶ {E₁} {E₂} {E₂'} p) | Q = s≤′s (s≤′s Q)

open Subrelation {_<₁_ = _⟵_  } {_<₂_ =  _≺_} ⟵⇒<′
  renaming (well-founded to well-founded-subrelation)

{- The sub relation of a well-founded relation is well founded -}
wf⟵ : Well-founded _⟵_ 
wf⟵ = well-founded-subrelation wf≺

{- Using the well-foundedness, eval is a simple use of the progress lemma + recursion -}
evalWF : ∀ E → (Acc _⟵_ E) → Σ[ n ∈ ℕ ] E ⟶⋆ num n
evalWF E a with ⟶progress E
evalWF .(num n) a | inj₁ (numVal n) = n , k⟶⋆ (zero , z⟶) -- 
evalWF E (acc rs) | inj₂ (E' , P) with evalWF E' (rs E' P)
evalWF E (acc rs) | inj₂ (E' , P) | n , k⟶⋆ (k , Q) = n , k⟶⋆ (suc k , sn⟶ P Q)

{- Now eval is re-expressed with an additional auxilliary relation tracking the wellfoundedness -} 
eval : ∀ E → Σ[ n ∈ ℕ ] E ⟶⋆ num n
eval E = evalWF E (wf⟵ E)

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
