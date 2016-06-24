open import Utilities.Logic
open import Relation.Nullary.Decidable
open import Relation.Binary

module Database
  (Atom : Set)
  (X : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqX : DecEq X)
  (eqD : DecEq D)
  (DT : Set)
  (⊢ᵟ_∶_ : D → DT → Set)
  (typeDec : Decidable (⊢ᵟ_∶_))
  where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import FiniteSubset renaming (_∪_ to _∪_fs ; _∩_ to _∩_fs) 
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool
open import Data.List
open import Induction.WellFounded
open import Induction.Nat

ObjectTriple = X × X × X
DataTriple = X × X × D

,-inv₁ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} →  ¬ x ≡ y →  ¬ (x , w) ≡ (y , z)
,-inv₁ f refl = f refl

,-inv₂ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} → ¬ w ≡ z →  ¬ (x , w) ≡ (y , z)
,-inv₂ f refl = f refl

DecEqPair : {A B : Set} → (eqA : DecEq A) → (eqB : DecEq B) → DecEq (A × B)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) with eqA proj₁ proj₃
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p with eqB proj₂ proj₄
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p₁ | yes p = yes (cong₂ _,_ p₁ p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p | no ¬p = no (,-inv₂ ¬p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | no ¬p = no (,-inv₁ ¬p) 

eqObjectTriple : DecEq ObjectTriple
eqObjectTriple = DecEqPair eqX (DecEqPair eqX eqX)

eqDataTriple : DecEq DataTriple
eqDataTriple = DecEqPair eqX (DecEqPair eqX eqD)

Database = FiniteSubSet ObjectTriple eqObjectTriple true × FiniteSubSet DataTriple eqDataTriple true

_∈_obj : ObjectTriple → Database → Set
o ∈ Γ obj = Σ[ e ∈ Element (proj₁ Γ) ] o ≡ proj₁ e

_∈_dat : DataTriple → Database → Set
o ∈ Γ dat = Σ[ e ∈ Element (proj₂ Γ) ] o ≡ proj₁ e

sub : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → A
sub (o , _ , _) = o

prop : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → B
prop (_ , p , _) = p

obj : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → C
obj (_ , _ , l) = l

--─ : Database → Set

_∪_ : Database → Database → Database
(proj₁ , proj₂) ∪ (proj₃ , proj₄) = proj₁ ∪ proj₃ fs , proj₂ ∪ proj₄ fs 

_∩_ : Database → Database → Database
(proj₁ , proj₂) ∩ (proj₃ , proj₄) = proj₁ ∩ proj₃ fs , proj₂ ∩ proj₄ fs 

_/_fs : {C : Set}{eq : DecEq C} {b1 b2 : Bool}
  → FiniteSubSet C eq b1 → FiniteSubSet C eq b2
  → FiniteSubSet C eq (b1 ∧ b2) 
_/_fs {C} {eq = _==_} {b1} {b2} U S = for u ∈ U as _ do
                                        for s ∈ S as true do
                                          if not ⌊ u == s ⌋ then return {b = true} u

_/_ : Database → Database → Database
(proj₁ , proj₂) / (proj₃ , proj₄) = (proj₁ / proj₃ fs) , (proj₂ / proj₄ fs)

_≈_ : ∀ {C : Set} {eq : DecEq C} → FiniteSubSet C eq true → FiniteSubSet C eq true → Set
X ≈ Y = (X / Y fs) ≡ mzero × (Y / X fs) ≡ mzero

_⊂_fs : ∀ {C : Set} {eq : DecEq C} → FiniteSubSet C eq true → FiniteSubSet C eq true → Set
S ⊂ T fs = S / T fs ≡ mzero × T / S fs ≢ mzero

_⊆_fs : ∀ {C : Set} {eq : DecEq C} → FiniteSubSet C eq true → FiniteSubSet C eq true → Set
S ⊆ T fs = S / T fs ≡ mzero

_⊂_ : Database → Database → Set
(proj₁ , proj₂) ⊂ (proj₃ , proj₄) = (proj₁ ⊂ proj₃ fs) × proj₂ ⊆ proj₄ fs ⊎ proj₁ ⊆ proj₃ fs × (proj₂ ⊂ proj₄ fs)

open import Data.Empty

EmptyNotFull : ∀ {C} {eq} {x : C} {x₁} → fs-plain {C} {eq} (x ∷ x₁) ≢ fs-plain []
EmptyNotFull () 

_⊂?_fs : ∀ {C : Set} {eq : DecEq C} → Decidable ((_⊂_fs {C} {eq}))
S ⊂? T fs with S / T fs
S ⊂? T fs | fs-plain [] with T / S fs
S ⊂? T fs | fs-plain [] | fs-plain [] = no (λ z → proj₂ z refl)
S ⊂? T fs | fs-plain [] | fs-plain (x ∷ x₁) = yes (refl , (λ ()))
S ⊂? T fs | fs-plain (x ∷ x₁) = no (λ x → EmptyNotFull (proj₁ x))

_⊆?_fs : ∀ {C : Set} {eq : DecEq C} → Decidable ((_⊆_fs {C} {eq}))
S ⊆? T fs with S / T fs
S ⊆? T fs | fs-plain [] = yes refl
S ⊆? T fs | fs-plain (x ∷ x₁) = no (λ ())

_⊂?_ : Decidable (_⊂_)
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) with proj₁ ⊂? proj₃ fs
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | yes p with proj₂ ⊆? proj₄ fs
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | yes p | yes p₁ = yes (inj₁ (p , p₁))
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | yes p | no ¬p = no (λ {(inj₁ (a , b)) → ¬p b ; (inj₂ (a , b , c)) → ¬p b})
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | no ¬p with proj₂ ⊂? proj₄ fs
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | no ¬p | yes p with proj₁ ⊆? proj₃ fs
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | no ¬p | yes p₁ | yes p = yes (inj₂ (p , p₁))
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | no ¬p₁ | yes p | no ¬p = no (λ {(inj₁ (a , b)) → ¬p₁ a ; (inj₂ (a , b)) → ¬p a}) 
(proj₁ , proj₂) ⊂? (proj₃ , proj₄) | no ¬p₁ | no ¬p = no ((λ {(inj₁ (a , b)) → ¬p₁ a ; (inj₂ (a , b)) → ¬p b}) )

-- no (λ {(inj₁ (a , b)) → ¬p a ; (inj₂ (a , b , c)) → ¬p {!!} })

open import Data.List
open import Data.Nat

∣_∣ : ∀ {b} {C} {eq : DecEq C} → FiniteSubSet C eq b → ℕ
∣ x ∣ = length (listOf x)

_≺dat_ : FiniteSubSet DataTriple eqDataTriple true → FiniteSubSet DataTriple eqDataTriple true → Set
x ≺dat y = ∣ x ∣ <′ ∣ y ∣

_≺obj_ : FiniteSubSet ObjectTriple eqObjectTriple true → FiniteSubSet ObjectTriple eqObjectTriple true → Set
x ≺obj y  = ∣ x ∣ <′ ∣ y ∣

open Inverse-image {_<_ = _<′_} (∣_∣ {true} {ObjectTriple} {eqObjectTriple}) renaming (well-founded to well-founded-ii-obj)
{- The inverse image of a well founded relation is well founded. -}
wf≺obj : Well-founded _≺obj_
wf≺obj = well-founded-ii-obj <-well-founded

open Inverse-image {_<_ = _<′_} (∣_∣ {true} {DataTriple} {eqDataTriple}) renaming (well-founded to well-founded-ii-dat)
{- The inverse image of a well founded relation is well founded. -}
wf≺dat : Well-founded _≺dat_
wf≺dat = well-founded-ii-dat <-well-founded

open Lexicographic (_≺obj_) (λ _ → _≺dat_) renaming (well-founded to well-founded-lex ; _<_ to _≺_)
wf≺ : Well-founded _≺_
wf≺ = well-founded-lex wf≺obj wf≺dat

⊂⇒≺ : ∀ d c → d ⊂ c → d ≺ c
⊂⇒≺ d c (inj₁ ((proj₅ , proj₆) , proj₇)) = left {!!}
⊂⇒≺ d c (inj₂ (proj₁ , proj₂ , proj₃)) = {!!}

_∈op_⇒Π_  : X → Database → Database → Database
p ∈op (objdb , datadb) ⇒Π (φdb , _) =
   -- Collect all s =p⇒ t
  ((for t ∈ φdb as true
    do for s ∈ objdb as true
       do if ⌊ eqX (prop s) p ⌋ ∧ ⌊ eqX (obj s) (sub t) ⌋  
          then return {b = true} s)
   /
   -- subtract if s =p⇒ t ∧ (t ⊨ φ) ∧
   --             s =p⇒ t' ∧ (t ⊨ ¬φ) ∧ 
   (for t ∈ φdb as true
    do for ¬t ∈ objdb / φdb fs as true
       do for s ∈ objdb as true
          do if ⌊ eqX (prop s) p ⌋ ∧
                ⌊ eqX (obj s) (sub t) ⌋ ∧
                ⌊ eqX (obj s) (sub ¬t) ⌋
             then return {b = true} s)
   fs
  , datadb)

_∈op_⇒Σ_  : X → Database → Database → Database
p ∈op (objdb , datadb) ⇒Σ (φdb , _) =
  (for t ∈ φdb as true
   do for s ∈ objdb as true
      do if ⌊ eqX p (prop s) ⌋ ∧ 
            ⌊ eqX (obj s) (sub t) ⌋
         then return {b = true} s                                
  , datadb)

_∈dp_Πis_  : X → Database → DT → Database
p ∈dp (objdb , datadb) Πis τ = (objdb ,
                                 (for t ∈ datadb as true
                                  do if ⌊ eqX p (prop t) ⌋ ∧
                                        ⌊ typeDec (obj t) τ ⌋
                                     then return {b = true} t)
                                 /
                                 (for t ∈ datadb as true
                                  do for t' ∈ datadb as true
                                     do if ⌊ eqX p (prop t) ⌋ ∧
                                           ⌊ eqX (sub t) (sub t') ⌋ ∧
                                           ⌊ typeDec (obj t) τ ⌋ ∧
                                           not ⌊ typeDec (obj t') τ ⌋
                                        then return {b = true} t)
                                 fs)

_∈dp_Σis_  : X → Database → DT → Database
p ∈dp (objdb , datadb) Σis τ = (objdb ,
                                 for t ∈ datadb as true
                                 do if ⌊ eqX p (prop t) ⌋ ∧
                                       ⌊ typeDec (obj t) τ ⌋
                                    then return {b = true} t)


