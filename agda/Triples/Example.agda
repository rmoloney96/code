
module Example where

open import IO
open import Coinduction
open import RDF
open import FiniteSubset
open import Data.Product
open import Data.List
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool.Properties

Polity : Shape
Polity = ν "Pol" ((ℓ[ "name" ] Str) ⊗
                  (ℓ⟨ "population" ⟩ Natural) ⊗
                  (ℓ⟨ "doesn't exist" ⟩ Str) ⊗
                  (α⟨ "neighbouringPolity" ⟩ (v "Pol")))


Thing : Shape
Thing = (ℓ⟨ "thingy" ⟩ Str)

DB : Database
DB = fs-plain (("seshat:Rome" , "neighbouringPolity" , "seshat:Rome") ∷ []) ,
     fs-plain (("seshat:Rome" , "name" , s "Rome") ∷
              (("seshat:Rome" , "name" , s "Test") ∷
              (("seshat:Rome" , "population" , n 1000) ∷ 
              (("seshat:AThing" , "thingy", s "Foo") ∷ []))))

checkDB : Bool
checkDB with checkφ DB "seshat:Rome" Polity
checkDB | yes p = true
checkDB | no ¬p = false

test : Σ[ db ∈ Database ] Σs∈ DB ⟨s, "name" ,l⟩∧⊢l∶ Str ≡ db 
test = ({!!} , {!!}) , {!!}

open import Relation.Nullary.Decidable
open import Data.String renaming (_≟_ to eqString)
--open import Database

test2 : Database 
test2 = (mzero , for t ∈ proj₂ DB as true
                 do if ⌊ eqString "name" (prop t) ⌋ ∧
                    not ⌊ typeDec (obj t) Str ⌋
                    then FiniteSubset.return {b = true} t)
              
main = run (♯ (putStrLn "Checking to see if Rome is a polity") >>
            ♯ (if checkDB
               then putStrLn "A Polity Exists!"
               else putStrLn "No elements of this formula exist"))
