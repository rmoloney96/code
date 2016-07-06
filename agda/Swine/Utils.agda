
module Utils where

open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect)

DecEq : ∀ X → Set
DecEq X = Decidable (_≡_ {A = X})
