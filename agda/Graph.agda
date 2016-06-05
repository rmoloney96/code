module Graph where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.Product
open import Data.Bool
open import Data.Nat hiding (_≟_ ; compare) 
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Data.Nat.DivMod 
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Data.Unit hiding (_≟_)
open import Level


record Graph {ℓ : Level} : Set₁ where
  field
    Nodes : Set
    Edges : Nodes × Nodes → Bool
