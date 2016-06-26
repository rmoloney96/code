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
open import Utilities.ListProperties

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

ObjectStore = FiniteSubSet ObjectTriple eqObjectTriple true
DataStore = FiniteSubSet DataTriple eqDataTriple true
Database =  ObjectStore × DataStore

_∈obj_ : ObjectTriple → Database → Set
o ∈obj Γ  = ∥ eq2in eqObjectTriple o (listOf (proj₁ Γ)) ∥

_∈dat_ : DataTriple → Database → Set
o ∈dat Γ  = ∥ eq2in eqDataTriple o (listOf (proj₂ Γ)) ∥

_∈subject_ : X → Database → Set
x ∈subject Γ = ∥ eq2in eqX x (Data.List.map proj₁ (listOf (proj₁ Γ))) ∥

_∈object_ : X → Database → Set
x ∈object Γ = ∥ eq2in eqX x (Data.List.map (proj₁ ∘ proj₂) (listOf (proj₁ Γ))) ∥

sub : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → A
sub (o , _ , _) = o

prop : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → B
prop (_ , p , _) = p

obj : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → C
obj (_ , _ , l) = l

--─ : Database → Seta

_∪_ : Database → Database → Database
(proj₁ , proj₂) ∪ (proj₃ , proj₄) = proj₁ ∪ proj₃ fs , proj₂ ∪ proj₄ fs 

_∩sub_ : ∀ {C : Set} {eq : DecEq (X × X × C)} → FiniteSubSet (X × X × C) eq true → FiniteSubSet (X × X × C) eq true → FiniteSubSet (X × X × C) eq true
S ∩sub T = for x ∈ S as true
           do for y ∈ T as true
              do if ⌊ eqX (sub x) (sub y) ⌋
                 then return {b = true} x

_∩_ : Database → Database → Database
(proj₁ , proj₂) ∩ (proj₃ , proj₄) = proj₁ ∩sub proj₃ , proj₂ ∩sub proj₄

_/_fs : {C : Set}{eq : DecEq C} {b1 b2 : Bool}
  → FiniteSubSet C eq b1 → FiniteSubSet C eq b2
  → FiniteSubSet C eq (b1 ∧ b2) 
_/_fs {C} {eq = _==_} {b1} {b2} U S = for u ∈ U as _ do
                                        for s ∈ S as true do
                                          if not ⌊ u == s ⌋ then return {b = true} u

_/sub_ : ∀ {C : Set} {eq : DecEq (X × X × C)} → FiniteSubSet (X × X × C) eq true → FiniteSubSet (X × X × C) eq true → FiniteSubSet (X × X × C) eq true
U /sub S = for u ∈ U as _
           do for s ∈ S as true
              do if not ⌊ eqX (sub u) (sub s) ⌋ then return {b = true} u

_/_ : Database → Database → Database
(proj₁ , proj₂) / (proj₃ , proj₄) = (proj₁ /sub proj₃) , (proj₂ /sub proj₄)

_≈_ : ∀ {C : Set} {eq : DecEq C} → FiniteSubSet C eq true → FiniteSubSet C eq true → Set
X ≈ Y = (X / Y fs) ≡ mzero × (Y / X fs) ≡ mzero

_⊂_fs : ∀ {C : Set} {eq : DecEq C} → FiniteSubSet C eq true → FiniteSubSet C eq true → Set
S ⊂ T fs = S / T fs ≡ mzero × T / S fs ≢ mzero

_⊆_fs : ∀ {C : Set} {eq : DecEq C} → FiniteSubSet C eq true → FiniteSubSet C eq true → Set
S ⊆ T fs = S / T fs ≡ mzero

_⊂_ : Database → Database → Set
(proj₁ , proj₂) ⊂ (proj₃ , proj₄) = (proj₁ ⊂ proj₃ fs) × proj₂ ⊆ proj₄ fs ⊎ proj₁ ⊆ proj₃ fs × (proj₂ ⊂ proj₄ fs)

∅ : Database
∅ = mzero , mzero

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

--correct : ∀ (p : X) → Database → Σ[ db ∈ Database ] Σ[ t ∈ X ] Σ[ s ∈ X ] (s ∈subject db → t ∈object db  → (s , p , t) ∈obj db )
--correct p (odb , ddb) = {!!} , (? , {!!})

Σs∈_⟨s,_,t⟩∧t∈_ : Database → X → Database → Database
Σs∈ (S , _) ⟨s, a ,t⟩∧t∈ (φdb , _) = 
  (for t ∈ φdb as true
   do for s ∈ S as true
      do if ⌊ eqX a (prop s) ⌋ ∧ 
            ⌊ eqX (obj s) (sub t) ⌋
         then return {b = true} s                                
  , mzero)

Πs∈_⟨s,_,t⟩∧t∈_ : Database → X → Database → Database
Πs∈ S ⟨s, a ,t⟩∧t∈ φstates =
  (Σs∈ S ⟨s, a ,t⟩∧t∈ φstates) /
  (Σs∈ S ⟨s, a ,t⟩∧t∈ (S / φstates))

Σs∈_⟨s,_,l⟩∧⊢l∶_ : Database → X → DT → Database
Σs∈ (_ , S) ⟨s, a ,l⟩∧⊢l∶ τ = (mzero ,
                               for t ∈ S as true
                               do if ⌊ eqX a (prop t) ⌋ ∧
                                     ⌊ typeDec (obj t) τ ⌋
                                  then return {b = true} t)


Πs∈_⟨s,_,l⟩∧⊢l∶_ : Database → X → DT → Database
Πs∈ S ⟨s, a ,l⟩∧⊢l∶ τ = 
  (Σs∈ S ⟨s, a ,l⟩∧⊢l∶ τ) / 
  (mzero , for t ∈ proj₂ S as true
           do if ⌊ eqX a (prop t) ⌋ ∧
                 not ⌊ typeDec (obj t) τ ⌋
              then return {b = true} t)
 


