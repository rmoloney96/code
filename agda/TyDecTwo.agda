module TyDecTwo where 

open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (_∘_)
open import Data.Nat hiding (_*_) 
open import Data.Fin renaming (zero to fzero ; suc to fsuc)
open import Data.Fin.Props renaming (_≟_ to _≟_fin)
open import Data.Vec
--open import Data.Vec.Equality using (≈)
open import Data.Sum
open import Data.Unit renaming (_≟_ to _≟_unit)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary.Core
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PropEq
     using (_≡_; refl; trans; sym; cong)


data Ty : Set where
  ① : Ty
  ι : ℕ → Ty
  η : ℕ → Ty
  μ : Ty → Ty
  Π : Ty → Ty
  _⇒_ : Ty → Ty → Ty
  _⊗_ : Ty → Ty → Ty 
  _⊕_ : Ty → Ty → Ty

DecVec : ℕ → Set (lsuc lzero)
DecVec n = Vec (Σ[ A ∶ Set ] Σ[ _≟_a ∶ Decidable (_≡_ {A = A})] A) n

_≟_decvec : ∀ {n m} (xs : DecVec n) (ys : DecVec m) → Dec (xs ≈ ys)
[] ≟ [] decvec = ? 
[] ≟ [] decvec = ? 

{-

data Test : Set where 
  level : ∀ (op# : ℕ) → 
  values : ∀ 
-} 

data Target : Set (Level.suc Level.zero) where
  target : ∀ (op# : ℕ) → 
    (maxValues# : ℕ) → 
    (maxBranches# : ℕ) → 
    (values : Vec (Vec (Σ[ A ∶ Set ] Σ[ _≟_a ∶ Decidable (_≡_ {A = A})] A) maxValues#) op#) → 
    (op2branches : Vec (Target ⊎ ⊤) maxBranches#) → Target

{-
DecVec : ℕ → Set (lsuc lzero)
DecVec n = Vec (Σ[ A ∶ Set ] Σ[ _≟_a ∶ Decidable (_≡_ {A = A})] A) n
-} 

{-
_#_≟_decvec : ∀ n (v s : DecVec n) → Decidable {A = DecVec n} _≡_
zero    # []        ≟ [] decvec = ?
(suc n) # []        ≟ [] decvec = ?
zero    # (x ∷ xs)  ≟ (y ∷ ys) decvec = ?
(suc n) # (x ∷ xs)  ≟ (y ∷ ys) decvec = ? -} 

{-
_≟_target : ∀ (t s : Target) → Decidable {A = Target} _≡_
(target n1 mv1 mb1 v1 opb1) ≟ (target n2 mv2 mb2 v2 opb2)     target with n1 ≟ n2 
(target .n1 mv1 mb1 v1 opb1) ≟ (target n1 mv2 mb2 v2 opb2)    target | yes p with mv1 ≟ mv2 
(target .n1 .mv1 mb1 v1 opb1) ≟ (target n1 mv1 mb2 v2 opb2)   target | yes p | yes q with mb1 ≟ mb2 
(target .n1 mv1 mb1 v1 opb1) ≟ (target n1 mv2 mb2 v2 opb2)    target | yes p | yes q | yes r = ? 
(target .n1 mv1 mb1 v1 opb1) ≟ (target n1 mv2 mb2 v2 opb2)    target | yes p | yes q | no ¬r = ? 
(target .n1 mv1 mb1 v1 opb1) ≟ (target n1 mv2 mb2 v2 opb2)    target | yes p | no ¬q = ?
(target .n1 mv1 mb1 v1 opb1) ≟ (target n1 mv2 mb2 v2 opb2)    target | no ¬p = ?
-}