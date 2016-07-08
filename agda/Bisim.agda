
module Bisim where 

open import Data.Colist 
open Data.List 

data Ty : Type where 
  ι : ℕ → Ty 
  _⇒_ : Ty → Ty → Ty

data Term : Type where 
  ν : Term 
  ƛ : Term → Ty → Term 

Ctx : Type
Ctx = List.List 
  

data _⊢_∶_ : Ctx → Term → Ty → Type where 
  

data Context : 


