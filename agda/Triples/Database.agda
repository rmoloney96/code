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
open import Data.Sum renaming ( [_,_] to ⟨_,_⟩ )
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool
open import Data.List
open import Induction.WellFounded
open import Induction.Nat
open import Utilities.ListProperties
open import Data.Empty

Triple = X × X × (X ⊎ D)

,-inv₁ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} →  ¬ x ≡ y →  ¬ (x , w) ≡ (y , z)
,-inv₁ f refl = f refl

,-inv₂ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x y : A} {w z : B} → ¬ w ≡ z →  ¬ (x , w) ≡ (y , z)
,-inv₂ f refl = f refl

inj₁-inv : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {a b : A} → ¬ a ≡ b → ¬ (A ⊎ B ∋ inj₁  a) ≡ inj₁ b
inj₁-inv p refl = p refl

inj₂-inv : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {a b : B} → ¬ a ≡ b → ¬ (A ⊎ B ∋ inj₂ a) ≡ inj₂ b
inj₂-inv p refl = p refl

DecEqPair : {A B : Set} → (eqA : DecEq A) → (eqB : DecEq B) → DecEq (A × B)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) with eqA proj₁ proj₃
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p with eqB proj₂ proj₄
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p₁ | yes p = yes (cong₂ _,_ p₁ p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | yes p | no ¬p = no (,-inv₂ ¬p)
DecEqPair eqA eqB (proj₁ , proj₂) (proj₃ , proj₄) | no ¬p = no (,-inv₁ ¬p) 

DecEqSum : {A B : Set} → (eqA : DecEq A) → (eqB : DecEq B) → DecEq (A ⊎ B)
DecEqSum eqA eqB (inj₁ x) (inj₁ x₁) with eqA x x₁
DecEqSum eqA eqB (inj₁ x) (inj₁ x₁) | yes p = yes (cong inj₁ p)
DecEqSum eqA eqB (inj₁ x) (inj₁ x₁) | no ¬p = no (inj₁-inv ¬p)
DecEqSum eqA eqB (inj₁ x) (inj₂ y) = no (λ ())
DecEqSum eqA eqB (inj₂ y) (inj₁ x) = no (λ ())
DecEqSum eqA eqB (inj₂ y) (inj₂ y₁) with eqB y y₁
DecEqSum eqA eqB (inj₂ y) (inj₂ y₁) | yes p = yes (cong inj₂ p)
DecEqSum eqA eqB (inj₂ y) (inj₂ y₁) | no ¬p = no (inj₂-inv ¬p)

eqThird : DecEq (X ⊎ D)
eqThird = DecEqSum eqX eqD

eqTriple : DecEq Triple
eqTriple = DecEqPair eqX (DecEqPair eqX eqThird)

Database : Set
Database = FiniteSubSet Triple eqTriple true

sub : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → A
sub (o , _ , _) = o

prop : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → B
prop (_ , p , _) = p

obj : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A × B × C → C
obj (_ , _ , l) = l

--─ : Database → Seta
∅ : Database
∅ = mzero

_∪_ : Database → Database → Database
S ∪ T = S ∪ T fs 

_∩_ : Database → Database → Database
S ∩ T = for x ∈ S as true
        do for y ∈ T as true
           do if ⌊ eqX (sub x) (sub y) ⌋
              then return {b = true} x

_/_ : Database → Database → Database
S / T = for s ∈ S as _
        do if not ⌊ eq2in eqX (sub s) (Data.List.map sub (listOf T)) ⌋
           then return {b = true} s 

{-
/-subtracts : ∀ X S T → X ∈ listOf (S / T) → X ∈ listOf S × (X ∈ listOf T → ⊥)
/-subtracts X₁ (fs-plain []) (fs-plain []) P = P , (λ ())
/-subtracts X₁ (fs-plain []) (fs-plain (x ∷ x₁)) ()
/-subtracts X₁ (fs-plain (x ∷ x₁)) (fs-plain []) P = {!P!} -- {!P!} , (λ ())
/-subtracts X₁ (fs-plain (x ∷ x₁)) (fs-plain (x₂ ∷ x₃)) P = {!!}
-}

_⊆_ : Database → Database → Set
S ⊆ T = S / T ≡ ∅

_⊂_ : Database → Database → Set
S ⊂ T = S / T ≡ ∅ × T / S ≢ ∅ 

EmptyNotFull : ∀ {C} {eq} {x : C} {x₁} → fs-plain {C} {eq} (x ∷ x₁) ≢ fs-plain []
EmptyNotFull () 

_⊂?_ : Decidable (_⊂_)
S ⊂? T with S / T
S ⊂? T | fs-plain [] with T / S
S ⊂? T | fs-plain [] | fs-plain [] = no (λ z → proj₂ z refl)
S ⊂? T | fs-plain [] | fs-plain (x ∷ x₁) = yes (refl , (λ ()))
S ⊂? T | fs-plain (x ∷ x₁) = no (λ x → EmptyNotFull (proj₁ x)) 

{-
_⊆?_fs : Decidable (_⊆_)
S ⊆? T fs with S / T
S ⊆? T fs | fs-plain [] = yes refl
S ⊆? T fs | fs-plain (x ∷ x₁) = no (λ ())

open import Data.List
open import Data.Nat

∣_∣ : Database → ℕ
∣ x ∣ = length (listOf x)

_≺_ : Database → Database → Set
x ≺ y = ∣ x ∣ <′ ∣ y ∣

open Inverse-image {_<_ = _<′_} (∣_∣) renaming (well-founded to well-founded-ii-obj)
{- The inverse image of a well founded relation is well founded. -}
wf≺ : Well-founded _≺_
wf≺ = well-founded-ii-obj <-well-founded

⊂⇒<′ : ∀ {S T} → S ⊂ T → S ≺ T
⊂⇒<′ {S} {T} (proj₁ , proj₂) with S / T
⊂⇒<′ {S} {T} (proj₁ , proj₂) | fs-plain [] with T / S
⊂⇒<′ (proj₁ , proj₂) | fs-plain [] | fs-plain [] = ⊥-elim (proj₂ proj₁)
⊂⇒<′ (proj₁ , proj₂) | fs-plain [] | fs-plain (x ∷ x₁) = {!yes!}
⊂⇒<′ (() , proj₂) | fs-plain (x ∷ x₁)


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

open Lexicographic (_≺obj_) (λ _ → _≺dat_) renaming (well-founded to well-founded-lex ; _<_ to _≺_)
wf≺ : Well-founded _≺_
wf≺ = well-founded-lex wf≺obj wf≺dat

--correct : ∀ (p : X) → Database → Σ[ db ∈ Database ] Σ[ t ∈ X ] Σ[ s ∈ X ] (s ∈subject db → t ∈object db  → (s , p , t) ∈obj db )
--correct p (odb , ddb) = {!!} , (? , {!!})
-}
-}

Σs∈_⟨s,_,t⟩∧t∈_ : Database → X → Database → Database
Σs∈ S ⟨s, a ,t⟩∧t∈ φdb = 
   for t ∈ φdb as true
   do for s ∈ S as true
      do if ⌊ eqX a (prop s) ⌋ ∧ 
            ⌊ eqThird (obj s) (inj₁ (sub t)) ⌋
         then return {b = true} s                                

Πs∈_⟨s,_,t⟩∧t∈_ : Database → X → Database → Database
Πs∈ S ⟨s, a ,t⟩∧t∈ φstates =
  (Σs∈ S ⟨s, a ,t⟩∧t∈ φstates) /
  (Σs∈ S ⟨s, a ,t⟩∧t∈ (S / φstates))

Σs∈_⟨s,_,l⟩∧⊢l∶_ : Database → X → DT → Database
Σs∈ S ⟨s, a ,l⟩∧⊢l∶ τ = for t ∈ S as true
                        do if ⌊ eqX a (prop t) ⌋ ∧
                              (⟨ (λ anObject → false) , (λ l → ⌊ typeDec l τ ⌋) ⟩ (obj t))
                           then return {b = true} t

Πs∈_⟨s,_,l⟩∧⊢l∶_ : Database → X → DT → Database
Πs∈ S ⟨s, a ,l⟩∧⊢l∶ τ =
  (Σs∈ S ⟨s, a ,l⟩∧⊢l∶ τ) / 
  (for t ∈ S as true
   do if ⌊ eqX a (prop t) ⌋ ∧
         not (⟨ (λ anObject → false) , (λ l → ⌊ typeDec l τ ⌋) ⟩ (obj t))
      then return {b = true} t)
