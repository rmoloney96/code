
module Example where

open import IO
open import Coinduction
open import RDF
open import FiniteSubset hiding (_∩_)
open import Data.Product
open import Data.List
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool.Properties
open import Data.Sum
open import Data.List

Polity : Shape
Polity = ν "Pol" ((ℓ[ "name" ] Str) ⊗
                  (ℓ⟨ "population" ⟩ Natural) ⊗
                  (α⟨ "neighbouringPolity" ⟩ (v "Pol")))

Thing : Shape
Thing = (ℓ⟨ "thingy" ⟩ Str)

DB : Transitions
DB = (("seshat:Rome" , "neighbouringPolity" , inj₁ "seshat:Rome") ∷ 
     (("seshat:Rome" , "name" , inj₂ (s "Rome")) ∷
     (("seshat:Rome" , "name" , inj₂ (s "That")) ∷
     (("seshat:Rome" , "population" , inj₂ (n 1000)) ∷ 
     (("seshat:AThing" , "thingy", inj₂ (s "Foo")) ∷ [])))))


checkDB : Bool
checkDB with checkφ DB "seshat:Rome" Polity
checkDB | yes p = true
checkDB | no ¬p = false

open import Relation.Nullary.Decidable
open import Data.String renaming (_≟_ to eqString) hiding (_++_)

main = run (♯ (putStrLn "Checking to see if Rome is a polity") >>
            ♯ (if checkDB
               then putStrLn "A Polity Exists!"
               else putStrLn "No elements of this formula exist"))
