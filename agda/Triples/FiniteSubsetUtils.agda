
module FiniteSubsetUtils where

open import FiniteSubset
open import Utilities.ListProperties renaming (_∈_ to _∈L_)
open import Data.List
open import Utilities.Logic
open import Data.Bool
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Nat
open import Finiteness renaming (∣_∣ to ∣_∣listable)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function

_∈_ : ∀ {C : Set}{eq : DecEq C} {b : Bool} → C → FiniteSubSet C eq b → Set
_∈_ {eq = eq} x S = x ∈L (listOf S)

_∉L_ : ∀ {C : Set} → C → List C → Set
x ∉L S = x ∈L S → ⊥

_∉_ : ∀ {C : Set}{eq : DecEq C} {b : Bool} → C → FiniteSubSet C eq b → Set
_∉_ {eq = eq} x S = x ∈L (listOf S) → ⊥ 

∈L? : ∀ {C : Set} (eq : DecEq C) → (x : C) → (S : List C) → Dec (x ∈L S)
∈L? eq x S = eq2in eq x S

_∈𝔹_ : ∀ {C : Set}{eq : DecEq C} {b : Bool} → C → FiniteSubSet C eq b → Bool
_∈𝔹_ {eq = eq} x S = ⌊ eq2in eq x (listOf S ) ⌋

_/_ : {C : Set}{eq : DecEq C} {b1 b2 : Bool}
  → FiniteSubSet C eq b1 → FiniteSubSet C eq b2
  → FiniteSubSet C eq b1
_/_ {C} {eq = _==_} {b1} {b2} S T = 
        for s ∈ S as _
        do if not (s ∈𝔹 T)
           then return {b = true} s

_⊆_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
        FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
_⊆_ S T = ∀ s → s ∈ S → s ∈ T 

_⊆L_ : ∀ {C : Set} → List C → List C → Set
_⊆L_ S T = ∀ s → s ∈L S → s ∈L T 

⊆Lx∷S⇒⊆LS : ∀ {C} {x : C} {S T} → ((x ∷ S) ⊆L T) → x ∈L T → S ⊆L T
⊆Lx∷S⇒⊆LS S⊆T x∈LT s x = S⊆T s (there x)

_⊆L?_ : ∀ {C : Set} {eq : DecEq C} → 
       Decidable (_⊆L_ {C})
[] ⊆L? T = yes (λ s → λ ())
_⊆L?_ {eq = eq} (x ∷ S) T with eq2in eq x T
_⊆L?_ {eq = eq} (x ∷ S) T | yes p with _⊆L?_ {eq = eq} S T
(x ∷ S) ⊆L? T | yes p₁ | yes p = yes (λ s x₁ → aux p₁ x₁ p)
  where aux : ∀ {C : Set} {s x : C} {T S} → x ∈L T → s ∈L (x ∷ S) → S ⊆L T → s ∈L T
        aux P here S⊆T = P
        aux P (there Q) S⊆T = S⊆T _ Q
(x ∷ S) ⊆L? T | yes p | no ¬p = no (λ x₁ → ¬p (⊆Lx∷S⇒⊆LS x₁ p))
(x ∷ S) ⊆L? T | no ¬p = no (λ z → ¬p (z x here))


_⊆?_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
       Decidable (_⊆_ {C} {eq} {b1} {b2})
_⊆?_ {eq = eq} S T = _⊆L?_ {eq = eq} (listOf S) (listOf T)

_⊂_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
        FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
S ⊂ T = S ⊆ T × ¬ T ⊆ S 

_⊂L_ : ∀ {C : Set} →
        List C → List C → Set
S ⊂L T = S ⊆L T × ¬ T ⊆L S 

_⊂L?_ : ∀ {C : Set}{eq : DecEq C} →
       Decidable (_⊂L_ {C})
_⊂L?_ {eq = eq} S T with _⊆L?_ {eq = eq} S T

_⊂L?_ {eq = eq} S T | yes p with _⊆L?_ {eq = eq} T S
S ⊂L? T | yes p₁ | yes p = no (λ z → proj₂ z p)
S ⊂L? T | yes p | no ¬p = yes (p , ¬p)
S ⊂L? T | no ¬p = no (λ z → ¬p (proj₁ z))

_Σ⊂_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
        FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
_Σ⊂_ {C} S T =  S ⊆ T × Σ[ x ∈ C ] x ∈ T × x ∉ S

_Σ⊂L_ : ∀ {C : Set} →
        List C → List C → Set
_Σ⊂L_ {C} S T = S ⊆L T × Σ[ x ∈ C ] x ∈L T × x ∉L S

Σ⊂⇒⊂ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
     (S : FiniteSubSet C eq b1) → (T : FiniteSubSet C eq b2) →
     (S Σ⊂ T) → S ⊂ T
Σ⊂⇒⊂ S T (proj₁ , proj₂ , proj₃ , proj₄) = proj₁ , (λ x → proj₄ (x proj₂ proj₃))

open import Utilities.ListsAddition -- Utilities.ListAddition

strongRemDup : ∀ {X : Set} → (∈? : DecIn X) → (xs : List X) →
               Σ[ ys ∈ List X ] (∀ x → x ∈L xs → x ∈L ys) ×
                                (∀ x → x ∈L ys → x ∈L xs) × 
                                NoDup ys
strongRemDup ∈? xs = (remDup ∈? xs)
                     , (λ x P → remDupSound ∈? x xs P)
                     , (λ x P → remDupComplete ∈? x xs P)
                     , (λ x → remDupCorrect ∈? xs x)

∣_∣ND : ∀  {X : Set} → ListableNoDup X → ℕ
∣_∣ND nodup = length ∘ proj₁ $ nodup

_∈ND_ : ∀ {C : Set} → C → ListableNoDup C → Set
x ∈ND T = x ∈L (proj₁ T)  -- 

_⊆ND_ : ∀ {C : Set} → (S : ListableNoDup C) → (T : ListableNoDup C) → Set
S ⊆ND T = ∀ x → x ∈ND S → x ∈ND T

_⊂ND_ : ∀ {C : Set} → (S : ListableNoDup C) → (T : ListableNoDup C) → Set
S ⊂ND T = S ⊆ND T × ¬ (T ⊆ND S) 

{-
aux : ∀ {C : Set} (x s : C) (xs ys : List C) → (x ∷ xs) ⊆L (x ∷ ys) → s ∈L xs → s ∈L ys
aux x s xs ys x∷xs⊆Lx∷ys s∈Lxs s≢x with x∷xs⊆Lx∷ys s (there s∈Lxs)        
aux s .s xs₁ ys x∷xs⊆Lx∷ys s∈Lxs s≢x | here = ⊥-elim (s≢x refl)
aux x s xs₁ ys x∷xs⊆Lx∷ys s∈Lxs s≢x | there res = res
-}

-- ∀ {C : Set} (eq : DecEq C) (x : C) (xs ys : List C) → x ∷ xs ⊆L 

notInAndOut : ∀ {C : Set} (x s : C) xs → x ∉L xs → s ∈L xs → s ≢ x
notInAndOut s .s _ x∉ here refl = ⊥-elim (x∉ here) 
notInAndOut s .s _ x∉ (there s∈) refl = ⊥-elim (x∉ (there s∈))

strengthen : ∀ {C : Set} (x : C) (xs ys : List C) → x ∉L xs → (x ∷ xs) ⊆L (x ∷ ys) → (xs ⊆L ys)
strengthen x xs ys P Q y y∈ys with Q y (there y∈ys)
strengthen y xs ys P Q .y y∈ys | here = ⊥-elim $ P y∈ys 
strengthen x xs ys P Q y y∈ys | there res = res

weaken¬⊆ : ∀ {C : Set} (x : C) (xs ys : List C) → x ∉L xs → ¬ (xs ⊆L ys) → ¬ (x ∷ xs) ⊆L (x ∷ ys)
weaken¬⊆ x xs ys x∉xs ¬xs⊆ys x∷⊆Lx∷xs = ¬xs⊆ys (λ s x₁ → aux x s xs ys x∷⊆Lx∷xs x₁ (notInAndOut x s xs x∉xs x₁))
  where aux : ∀ {C : Set} (x s : C) (xs ys : List C) → (x ∷ xs) ⊆L (x ∷ ys) → s ∈L xs → s ≢ x → s ∈L ys
        aux x s xs ys x∷xs⊆Lx∷ys s∈Lxs s≢x with x∷xs⊆Lx∷ys s (there s∈Lxs)        
        aux s .s xs₁ ys x∷xs⊆Lx∷ys s∈Lxs s≢x | here = ⊥-elim (s≢x refl) -- (s≢x refl)
        aux x s xs₁ ys x∷xs⊆Lx∷ys s∈Lxs s≢x | there res = res


inMustBeHere : ∀ {C : Set} {x x₁} {S : List C} → x ∉L S → x ∈L (x₁ ∷ S) → x ≡ x₁
inMustBeHere P here = refl
inMustBeHere P (there Q) = Q ↯ P

open import Data.Sum renaming ([_,_] to ⟨_,_⟩)

_─_⟨_⟩ : ∀ {C : Set} → (S : List C) → (T : List C) → (eq : DecEq C) → Σ[ ys ∈ List C ] ∀ x → (x ∈L S × x ∈L ys × x ∉L T) ⊎ (x ∈L T → x ∉L ys)
[] ─ [] ⟨ eq ⟩ = [] , (λ x → inj₂ (λ x₁ → λ ()))
[] ─ (x ∷ T) ⟨ eq ⟩ = [] , (λ x₁ → inj₂ (λ x₂ → λ ()))
(x ∷ S) ─ T ⟨ eq ⟩ with  S ─ T ⟨ eq ⟩ 
(x ∷ S) ─ T ⟨ eq ⟩ | S' , P with eq2in eq x T
(x ∷ S) ─ T ⟨ eq ⟩ | S' , P | yes p = S' , (λ x₁ → aux x₁ (P x₁))
  where aux : ∀ {C : Set} {x S S' T} → (x₁ : C) → (x₁ ∈L S) × (x₁ ∈L S') × (x₁ ∉L T) ⊎ (x₁ ∈L T → x₁ ∉L S') →
                                                   (x₁ ∈L (x ∷ S)) × (x₁ ∈L S') × (x₁ ∉L T) ⊎ (x₁ ∈L T → x₁ ∉L S')
        aux x₂ (inj₁ x₃) = inj₁ (there (proj₁ x₃) , ((proj₁ (proj₂ x₃)) , (proj₂ (proj₂ x₃))))
        aux x₂ (inj₂ y) = inj₂ y 
(x ∷ S) ─ T ⟨ eq ⟩ | S' , P | no ¬p = x ∷ S' , (λ x₁ → aux x₁ ¬p (P x₁))
  where aux : ∀ {C : Set} {x S S' T} → (x₁ : C) → x ∉L T → (x₁ ∈L S) × (x₁ ∈L S') × (x₁ ∉L T) ⊎ (x₁ ∈L T → x₁ ∉L S') → 
                                                            (x₁ ∈L (x ∷ S)) × (x₁ ∈L (x ∷ S')) × (x₁ ∉L T) ⊎ (x₁ ∈L T → x₁ ∉L (x ∷ S')) 
        aux x₂ P₁ (inj₁ x₃) = inj₁ ((there (proj₁ x₃)) , ((there (proj₁ (proj₂ x₃))) , (proj₂ (proj₂ x₃))))
        aux x₂ P₁ (inj₂ y) = inj₂ (λ x₁ x₃ → let p = y x₁ ;
                                                  q = inMustBeHere p x₃
                                              in P₁ (subst (λ z → z ∈L _) q x₁)) 
--  S ⊂L T → NoDupInd S → S ⊂ T
--open import Data.Sum
data _#_ {C} : List C → C → Set where
  []# : ∀ {x} → [] # x 
  snoc# : ∀ {x y L} → L # x → y ≢ x → (y ∷ L) # x

#? : ∀ {C : Set} (eq : DecEq C) → Decidable (_#_ {C})
#? eq [] x = yes []#
#? eq (x ∷ L) x₁ with #? eq L x₁ 
#? eq (x ∷ L) x₁ | yes p with eq x x₁
#? eq (x₁ ∷ L) .x₁ | yes p₁ | yes refl = no (λ {(snoc# L#x₁ q) → q refl}) 
#? eq (x ∷ L) x₁ | yes p | no ¬p = yes (snoc# p ¬p)
#? eq (x ∷ L) x₁ | no ¬p = no (λ { (snoc# L#x₁ q) → ¬p L#x₁})

data ∣_∣∶=_ {C : Set} : List C → ℕ → Set where
  ∣[]∣ : ∣ [] ∣∶= 0
  ∣x∷L∣+1 : ∀ {x L n} → ∣ L ∣∶= n → L # x → ∣ x ∷ L ∣∶= suc n 
  ∣x∷L∣+0 : ∀ {x L n} → ∣ L ∣∶= n → (L # x → ⊥)  → ∣ x ∷ L ∣∶= n 


∣_∣⟨_⟩ : ∀ {C : Set} → List C → (eq : DecEq C) → ℕ
∣ S ∣⟨ eq ⟩ = length ∘ proj₁ $ strongRemDup (eq2in eq) S

∣∣⟨⟩⇒∣∣∶= : ∀ {C} (S : List C) (eq : DecEq C) n → ∣ S ∣⟨ eq ⟩ ≡ n → ∣ S ∣∶= n 
∣∣⟨⟩⇒∣∣∶= [] eq zero refl = ∣[]∣
∣∣⟨⟩⇒∣∣∶= [] eq (suc n) ()
∣∣⟨⟩⇒∣∣∶= (x ∷ S) eq n x₁ with ∣∣⟨⟩⇒∣∣∶= S eq n
∣∣⟨⟩⇒∣∣∶= (x ∷ S) eq n x₁ | res = {!!}

∣∣∶=⇒∣∣⟨⟩ : ∀ {C} (S : List C) (eq : DecEq C) n → ∣ S ∣∶= n  → ∣ S ∣⟨ eq ⟩ ≡ n 
∣∣∶=⇒∣∣⟨⟩ .[] eq .0 ∣[]∣ = refl
∣∣∶=⇒∣∣⟨⟩ _ eq _ (∣x∷L∣+1 {x'} {L} {n} P x₁) with ∣∣∶=⇒∣∣⟨⟩ L eq n P
∣∣∶=⇒∣∣⟨⟩ _ eq _ (∣x∷L∣+1 {x'} {L} {n} P x₁) | res with eq2in eq x' L
∣∣∶=⇒∣∣⟨⟩ _ eq _ (∣x∷L∣+1 P (snoc# x₁ x₂)) | refl | yes here = refl ↯ x₂
∣∣∶=⇒∣∣⟨⟩ _ eq _ (∣x∷L∣+1 P x₁) | refl | yes (there p) = {!refl!}
∣∣∶=⇒∣∣⟨⟩ _ eq _ (∣x∷L∣+1 P x₁) | res | no ¬p = {!!}
∣∣∶=⇒∣∣⟨⟩ _ eq n (∣x∷L∣+0 P x₁) with NoDupInd
∣∣∶=⇒∣∣⟨⟩ _ eq n (∣x∷L∣+0 P x₁) | res = {!!}
{-
open import Function

∣_∣ : ∀ {C : Set} {eq : DecEq C} {b1 : Bool} →
      FiniteSubSet C eq b1 → ℕ
∣ S ∣ = length ∘ proj₁ $ lstbl2nodup (fsListable S)

open import Data.Nat

_≺_ : {C : Set}{eq : DecEq C} {b1 b2 : Bool} →
      FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
S ≺ T = ∣ S ∣ <′ ∣ T ∣  

open import Induction.WellFounded
open import Induction.Nat

module WF⊆mod (C : Set) (eq : DecEq C) (b : Bool) where
  open Inverse-image {_<_ = _<′_} (∣_∣ {C} {eq} {b}) renaming (well-founded to well-founded-ii-obj)
  {- The inverse image of a well founded relation is well founded. -}

  wf≺ : Well-founded _≺_
  wf≺ = well-founded-ii-obj <-well-founded

  ⊂⇒<′ : ∀ {S T : FiniteSubSet C eq b} → S ⊂ T → S ≺ T
  ⊂⇒<′ {S} {T} P with S ⊆? T
  ⊂⇒<′ {S} {T} P | yes p with T ⊆? S
  ⊂⇒<′ (proj₁ , proj₂) | yes p₁ | yes p = ⊥-elim (proj₂ p)
  ⊂⇒<′ (proj₁ , proj₂) | yes p | no ¬p = {!!}
  ⊂⇒<′ (proj₁ , proj₂) | no ¬p = ⊥-elim (¬p proj₁)

{-
open Subrelation {A = Database} {_<₁_ = (_⊂_)} {_<₂_ =  _≺_} ⊂⇒<′
  renaming (well-founded to well-founded-subrelation)

{- The sub relation of a well-founded relation is well founded -}
wf⊂ : Well-founded _⊂_ 
wf⊂ = well-founded-subrelation wf≺

-}

{-
open Inverse-image {_<_ = _<′_} (∣_∣ {true} {DataTriple} {eqDataTriple}) renaming (well-founded to well-founded-ii-dat)
{- The inverse image of a well founded relation is well founded. -}
wf≺dat : Well-founded _≺dat_
wf≺dat = well-founded-ii-dat <-well-founded
-}

-}
