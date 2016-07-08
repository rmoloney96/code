module StrictlyPositive where 

open import Data.Nat
open import Data.Bool 
open import Data.List 
open import Data.Unit using (⊤)
open import Relation.Nullary.Core
open import Data.Sum 

Ctx : Set
Ctx = ℕ

data _∈_ : ℕ → Ctx → Set where 
  bounded : ∀ {n Δ} → suc n ≤ Δ → n ∈ Δ

inInversion : ∀ {n Δ} → n ∈ Δ → suc n ≤ Δ
inInversion (bounded p) = p

inctx : ∀ n Δ → Dec (n ∈ Δ)
inctx n Δ with (suc n) ≤? Δ
inctx n Δ | no p = no (λ x → p (inInversion x))
inctx n Δ | yes q  = yes (bounded q)

data Ty : Set where
  ① : Ty
  ι : ℕ → Ty
  η : ℕ → Ty
  _⇒_ : Ty → Ty → Ty
  _×_ : Ty → Ty → Ty 
  _⊕_ : Ty → Ty → Ty
  μ : Ty → Ty
  Π : Ty → Ty

data _·_⊢_ : Ctx → Ctx → Ty → Set where 
     UnitValid : ∀ {Δ Δ+} → 
       Δ · Δ+ ⊢ ①
     VarValid : ∀ {n Δ Δ+} → 
       (n ∈ Δ) → 
       Δ · Δ+ ⊢ (ι n) 
     FixValid : ∀ {n Δ Δ+} → 
       (n ∈ Δ+) → 
       Δ · Δ+ ⊢ (η n) 
     ImpValid : ∀ {Δ Δ+ α β} → 
       Δ · 0 ⊢ α → 
       Δ · Δ+ ⊢ β → 
       Δ · Δ+ ⊢ (α ⇒ β)
     AndValid : ∀ {Δ Δ+ α β} → 
       Δ · Δ+ ⊢ α → 
       Δ · Δ+ ⊢ β → 
       Δ · Δ+ ⊢ (α × β)
     OrValid : ∀ {Δ Δ+ α β} → 
       Δ · Δ+ ⊢ α → 
       Δ · Δ+ ⊢ β → 
       Δ · Δ+ ⊢ (α ⊕ β)
     MuValid : ∀ {Δ Δ+ α} → 
       Δ · (suc Δ+) ⊢ α → 
       Δ · Δ+ ⊢ μ α
     AllValid : ∀ {Δ Δ+ α} → 
       (suc Δ) · Δ+ ⊢ α → 
       Δ · Δ+ ⊢ Π α

varValidInversion : ∀ {Δ Δ+ n} → Δ · Δ+ ⊢ ι n → n ∈ Δ
varValidInversion {Δ} {Δ+} {n} (VarValid p) = p

fixValidInversion : ∀ {Δ Δ+ n} → Δ · Δ+ ⊢ η n → n ∈ Δ+
fixValidInversion {Δ} {Δ+} {n} (FixValid p) = p

orValidInversionL : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⊕ β) → (Δ · Δ+ ⊢ α)
orValidInversionL {Δ} {Δ+} {α} {β} (OrValid p q) = p

orValidInversionR : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⊕ β) → (Δ · Δ+ ⊢ β)
orValidInversionR {Δ} {Δ+} {α} {β} (OrValid p q) = q

impValidInversionL : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⇒ β) → (Δ · 0 ⊢ α)
impValidInversionL {Δ} {Δ+} {α} {β} (ImpValid p q) = p

impValidInversionR : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⇒ β) → (Δ · Δ+ ⊢ β)
impValidInversionR {Δ} {Δ+} {α} {β} (ImpValid p q) = q

andValidInversionL : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α × β) → (Δ · Δ+ ⊢ α)
andValidInversionL {Δ} {Δ+} {α} {β} (AndValid p q) = p

andValidInversionR : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α × β) → (Δ · Δ+ ⊢ β)
andValidInversionR {Δ} {Δ+} {α} {β} (AndValid p q) = q

allValidInversion : ∀ {Δ Δ+ α} → Δ · Δ+ ⊢ Π α → ((suc Δ) · Δ+ ⊢ α)
allValidInversion {Δ} {Δ+} {α} (AllValid p) = p

muValidInversion : ∀ {Δ Δ+ α} → Δ · Δ+ ⊢ μ α → (Δ · (suc Δ+) ⊢ α)
muValidInversion {Δ} {Δ+} {α} (MuValid p) = p

{-
Goal: Δ · Δ+ ⊢ ι n → .Data.Empty.⊥
————————————————————————————————————————————————————————————
p  : n ∈ Δ → .Data.Empty.⊥
Δ  : ℕ
q  : n ∈ Δ+ → .Data.Empty.⊥
-} 

isValid : ∀ Δ Δ+ α → Dec (Δ · Δ+ ⊢ α)
isValid Δ Δ+ ①       = yes UnitValid
isValid Δ Δ+ (ι n)   with (inctx n Δ)
isValid Δ Δ+ (ι n)   | yes p = yes (VarValid p)
isValid Δ Δ+ (ι n)   | no p  = no (λ { (VarValid q) → p q })
isValid Δ Δ+ (η n)   with (inctx n Δ+)
isValid Δ Δ+ (η n)   | yes p = yes (FixValid p)
isValid Δ Δ+ (η n)   | no p  = no (λ { (FixValid q) → p q })
isValid Δ Δ+ (α ⇒ β) with isValid Δ 0 α
isValid Δ Δ+ (α ⇒ β) | yes p with isValid Δ Δ+ β
isValid Δ Δ+ (α ⇒ β) | yes p | yes q = yes (ImpValid p q) 
isValid Δ Δ+ (α ⇒ β) | yes p | no q  = no (λ x → q (impValidInversionR x))
isValid Δ Δ+ (α ⇒ β) | no p  = no (λ x → p (impValidInversionL x))
isValid Δ Δ+ (α × β) with isValid Δ Δ+ α
isValid Δ Δ+ (α × β) | yes p with isValid Δ Δ+ β
isValid Δ Δ+ (α × β) | yes p | yes q = yes (AndValid p q) 
isValid Δ Δ+ (α × β) | yes p | no q  = no (λ x → q (andValidInversionR x))
isValid Δ Δ+ (α × β) | no p  = no (λ x → p (andValidInversionL x))
isValid Δ Δ+ (α ⊕ β) with isValid Δ Δ+ α
isValid Δ Δ+ (α ⊕ β) | yes p with isValid Δ Δ+ β
isValid Δ Δ+ (α ⊕ β) | yes p | yes q = yes (OrValid p q) 
isValid Δ Δ+ (α ⊕ β) | yes p | no q  = no (λ x → q (orValidInversionR x))
isValid Δ Δ+ (α ⊕ β) | no p  = no (λ x → p (orValidInversionL x))
isValid Δ Δ+ (Π α)   with isValid (suc Δ) Δ+ α
isValid Δ Δ+ (Π α)   | yes p = yes (AllValid p) 
isValid Δ Δ+ (Π α)   | no p  = no (λ x → p (allValidInversion x))
isValid Δ Δ+ (μ α)   with isValid Δ (suc Δ+) α
isValid Δ Δ+ (μ α)   | yes p = yes (MuValid p) 
isValid Δ Δ+ (μ α)   | no p  = no (λ x → p (muValidInversion x))

idTy : Ty
idTy = Π ((ι zero) ⇒ (ι zero))

idValid : 0 · 0 ⊢ idTy 
idValid = AllValid
            (ImpValid (VarValid (bounded (s≤s z≤n)))
             (VarValid (bounded (s≤s z≤n))))

listTy : Ty
listTy = Π (μ (① ⊕ ((ι 0) × (η 0))))

listValid : 0 · 0 ⊢ listTy
listValid = AllValid
              (MuValid
               (OrValid UnitValid
                (AndValid (VarValid (bounded (s≤s z≤n)))
                 (FixValid (bounded (s≤s z≤n))))))


notPos : Ty 
notPos = μ ((ι 0) ⇒ (ι 0))

notPosInvalid : ¬ (0 · 0 ⊢ notPos)
notPosInvalid x with muValidInversion x
notPosInvalid x | p with impValidInversionL p
notPosInvalid x | p | q with varValidInversion q
notPosInvalid x | p | q | bounded ()

dodgy : Ty
dodgy = μ (μ ((ι 1) ⇒ (ι 0)))

dodgyInvalid :  ¬ (0 · 0 ⊢ dodgy)
dodgyInvalid x with muValidInversion x
dodgyInvalid x | p with muValidInversion p 
dodgyInvalid x | p | q with impValidInversionL q
dodgyInvalid x | p | q | r with varValidInversion r 
dodgyInvalid x | p | q | r | bounded ()

isThisDodgy : Ty 
isThisDodgy = Π (μ (μ ((((ι 0) ⇒ (η 1)) ⇒ (η 0)))))

isThisDodgyValid : ¬ (0 · 0 ⊢ isThisDodgy)
isThisDodgyValid x with allValidInversion x
isThisDodgyValid x | p with muValidInversion p
isThisDodgyValid x | p | q with muValidInversion q
isThisDodgyValid x | p | q | r with impValidInversionL r
isThisDodgyValid x | p | q | r | s with impValidInversionR s
isThisDodgyValid x | p | q | r | s | t with fixValidInversion t
isThisDodgyValid x | p | q | r | s | t | bounded ()

