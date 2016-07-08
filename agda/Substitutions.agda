module Substitutions where 

open import Data.Nat 
open import Data.Nat.Properties using (≰⇒>)
open import Data.Bool hiding (_≟_) 
open import Data.List 
open import Data.Unit using (⊤)
-- open import Relation.Unary using (Decidable)
open import Data.Maybe.Core
open import Relation.Nullary.Core
open import Level using (Level) -- renaming (suc to ^)

Id : (x : Level) (X : Set x) → (X → X)
Id = λ x X x' → x'

Ctx : Set
Ctx = List Bool

data _∈_ : ℕ → Ctx → Set where 
  inzero : ∀ {Δ} → zero ∈ (true ∷ Δ)
  innext : ∀ {n Δ b} → n ∈ Δ → (suc n) ∈ (b ∷ Δ) 

inInversionSuc : ∀ {n Δ b} → (suc n) ∈ (b ∷ Δ) → n ∈ Δ
inInversionSuc (innext {n} {Δ} {b} p) = p 

inctx : ∀ n Δ → Dec (n ∈ Δ)
inctx _       []          = no (λ())
inctx zero    (true ∷ Δ)  = yes inzero
inctx zero    (false ∷ Δ) = no (λ())
inctx (suc n) (b ∷ Δ)     with inctx n Δ
inctx (suc n) (b ∷ Δ)     | (yes p) = yes (innext p)
inctx (suc n) (b ∷ Δ)     | (no p)  = no (λ p' → p (inInversionSuc p')) 

empty : ℕ → Ctx 
empty (suc n) = false ∷ (empty n) 
empty zero     = []

data Ty : Set where 
  ι : ℕ → Ty
  _⇒_ : Ty → Ty → Ty
  Π : Ty → Ty

data _·_⊢_ : Ctx → Ctx → Ty → Set where 
     VarValid : ∀ {n ΔP ΔN} → n ∈ ΔP → ΔP · ΔN ⊢ (ι n)
     ImpValid : ∀ {ΔP ΔN α β} → 
       ΔN · ΔP ⊢ α → 
       ΔP · ΔN ⊢ β → 
       ΔP · ΔN ⊢ (α ⇒ β)
     AllValid : ∀ {ΔP ΔN α} → 
       (true ∷ ΔP) · (false ∷ ΔN) ⊢ α → 
       ΔP · ΔN ⊢ Π α

data _⊢⁺_ : Ctx → Ty → Set where 
  OnlyPositive : ∀ {Δ α} → Δ · (empty (length Δ)) ⊢ α → Δ ⊢⁺ α 

varValidInversion : ∀ {ΔP ΔN n} → ΔP · ΔN ⊢ ι n → n ∈ ΔP
varValidInversion {ΔP} {ΔN} {n} (VarValid p) = p

impValidInversionL : ∀ {ΔP ΔN α β} → ΔP · ΔN ⊢ (α ⇒ β) → (ΔN · ΔP ⊢ α)
impValidInversionL {ΔP} {ΔN} {α} {β} (ImpValid p q) = p

impValidInversionR : ∀ {ΔP ΔN α β} → ΔP · ΔN ⊢ (α ⇒ β) → (ΔP · ΔN ⊢ β)
impValidInversionR {ΔP} {ΔN} {α} {β} (ImpValid p q) = q

allValidInversion : ∀ {ΔP ΔN α} → ΔP · ΔN ⊢ Π α → ((true ∷ ΔP) · (false ∷ ΔN) ⊢ α)
allValidInversion {ΔP} {ΔN} {α} (AllValid p) = p

isValid : ∀ ΔP ΔN α → Dec (ΔP · ΔN ⊢ α)
isValid ΔP ΔN (ι n)   with (inctx n ΔP)
isValid ΔP ΔN (ι n)   | yes p = yes (VarValid p) 
isValid ΔP ΔN (ι n)   | no p  = no (λ p' → p (varValidInversion p'))
isValid ΔP ΔN (α ⇒ β) with isValid ΔN ΔP α
isValid ΔP ΔN (α ⇒ β) | yes p with isValid ΔP ΔN β
isValid ΔP ΔN (α ⇒ β) | yes p | yes q = yes (ImpValid p q) 
isValid ΔP ΔN (α ⇒ β) | yes p | no q  = no (λ x → q (impValidInversionR x))
isValid ΔP ΔN (α ⇒ β) | no p  = no (λ x → p (impValidInversionL x))
isValid ΔP ΔN (Π α)   with isValid (true ∷ ΔP) (false ∷ ΔN) α
isValid ΔP ΔN (Π α)   | yes p = yes (AllValid p) 
isValid ΔP ΔN (Π α)   | no p  = no (λ x → p (allValidInversion x))

data Term : Set where 
 v : ℕ → Term
 ƛ : Ty → Term → Term 
 Λ_ : Term → Term 
 _○_ : Term → Term → Term 
 _●_ : Term → Ty → Term 

tyshiftn : ℕ → ℕ → Ty → Ty
tyshiftn cutoff size (ι n)   with cutoff ≤? n
tyshiftn cutoff size (ι n)   | yes p = ι (size + n)
tyshiftn cutoff size (ι n)   | no p  = ι n
tyshiftn cutoff size (α ⇒ β) = ((tyshiftn cutoff size α) ⇒ (tyshiftn cutoff size β))
tyshiftn cutoff size (Π α)   = Π (tyshiftn (1 + cutoff) size α)

tyshift : ℕ → Ty → Ty
tyshift cutoff = tyshiftn cutoff 1

tysub : Ty → ℕ → Ty → Ty 
tysub (ι m)              n              δ with compare n m
tysub (ι .m)             .m             δ | equal   m   = δ
tysub (ι .m)             .(suc (m + k)) δ | greater m k = ι m
tysub (ι .(suc (m + k))) .m             δ | less    m k = ι (m + k)
tysub (α ⇒ β)            n              δ = (tysub α n δ) ⇒ (tysub β n δ)
tysub (Π α)              n              δ = Π (tysub α (1 + n) (tyshift n δ))

tysubt : Term → ℕ → Ty → Term
tysubt (v m)   n δ = v m
tysubt (Λ t)   n δ = Λ (tysubt t (1 + n) (tyshift 0 δ))
tysubt (ƛ α t) n δ = ƛ (tysub α n δ) (tysubt t n δ)
tysubt (t ○ s) n δ = (tysubt t n δ) ○ (tysubt t n δ)
tysubt (t ● α) n δ = (tysubt t n δ) ● (tysub α n δ)

insert : Bool → ℕ → Ctx → Ctx 
insert b zero    Δ       = b ∷ Δ
insert b (suc n) []      = []
insert b (suc n) (r ∷ Δ) = r ∷ (insert b n Δ)

tyWkLe : ∀ {n m ΔP} → n ≤ m → m ∈ ΔP → suc m ∈ insert false n ΔP 
tyWkLe {zero}  {m} {ΔP}         p        q          = innext q
tyWkLe {suc n} {m} {[]}         p        ()
tyWkLe {suc n} {zero}  {b ∷ ΔP} ()       q 
tyWkLe {suc n} {suc m} {b ∷ ΔP} (s≤s p)  (innext q) = innext (tyWkLe p q)

tyWkGt : ∀ {n m ΔP} → n > m → m ∈ ΔP → m ∈ insert false n ΔP 
tyWkGt {zero}  {m} {ΔP}             ()       q          
tyWkGt {suc n} {m} {[]}             p        ()
tyWkGt {suc n} {zero}  {true ∷ ΔP}  p        q          = inzero
tyWkGt {suc n} {zero}  {false ∷ ΔP} p        () 
tyWkGt {suc n} {suc m} {b ∷ ΔP}     (s≤s p)  (innext q) = innext (tyWkGt p q)

--UpwardInsert : ∀ {n b ΔP} → (b ∷ (insert false n ΔP) ≅ (false (suc n) (b ∷ ΔP))
--UpwardInsert {n} {b} {ΔP} p = ? 

tyshiftnCorrect : ∀ {ΔP ΔN α n} → (ΔP · ΔN ⊢ α) → ((insert false n ΔP) · (insert false n ΔN) ⊢ (tyshiftn n 1 α))
tyshiftnCorrect {ΔP} {ΔN} {ι m}   {n} (VarValid p)   with n ≤? m 
tyshiftnCorrect {ΔP} {ΔN} {ι m}   {n} (VarValid p)   | yes q = VarValid (tyWkLe q p)
tyshiftnCorrect {ΔP} {ΔN} {ι m}   {n} (VarValid p)   | no  q = VarValid (tyWkGt (≰⇒> q) p)
tyshiftnCorrect {ΔP} {ΔN} {α ⇒ β} {n} (ImpValid p q) = ImpValid (tyshiftnCorrect p) (tyshiftnCorrect q)
tyshiftnCorrect {ΔP} {ΔN} {Π α}   {n} (AllValid p)   = AllValid (tyshiftnCorrect p)

