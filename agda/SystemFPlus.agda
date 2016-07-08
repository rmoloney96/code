module SystemFPlus where 

open import Function
open import Data.Fin using (Fin)
open import Data.Nat hiding (_*_) 
open import Data.Bool renaming (_≟_ to _≟_Bool) 
open import Data.List 
open import Data.Unit using (⊤)
open import Relation.Nullary.Core
open import Data.Sum 
open import Data.Product 
--open import Relation.Binary.EqReasoning
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

TyCtx : Set
TyCtx = ℕ

data _∈_ : ℕ → TyCtx → Set where 
  bounded : ∀ {n Δ} → suc n ≤ Δ → n ∈ Δ

inInversion : ∀ {n Δ} → n ∈ Δ → suc n ≤ Δ
inInversion (bounded p) = p

intyctx : ∀ n Δ → Dec (n ∈ Δ)
intyctx n Δ with (suc n) ≤? Δ
intyctx n Δ | no p = no (λ x → p (inInversion x))
intyctx n Δ | yes q  = yes (bounded q)

data Ty : Set where
  ① : Ty                -- unit type
  ι : ℕ → Ty           -- universal abstraction vars
  η : ℕ → Ty           -- μ vars 
  _⇒_ : Ty → Ty → Ty  -- implication
  _⊗_ : Ty → Ty → Ty  -- conjunction
  _⊕_ : Ty → Ty → Ty  -- disjunction
  μ : Ty → Ty          -- inductive types
  Π : Ty → Ty          -- universal quantification

Πshiftn : ℕ → ℕ → Ty → Ty
Πshiftn cutoff size ①   = ① 
Πshiftn cutoff size (ι n)   with cutoff ≤? n
Πshiftn cutoff size (ι n)   | yes p = ι (size + n)
Πshiftn cutoff size (ι n)   | no p  = ι n
Πshiftn cutoff size (η n)   = η n
Πshiftn cutoff size (α ⇒ β) = ((Πshiftn cutoff size α) ⇒ (Πshiftn cutoff size β))
Πshiftn cutoff size (α ⊕ β) = ((Πshiftn cutoff size α) ⊕ (Πshiftn cutoff size β))
Πshiftn cutoff size (α ⊗ β) = ((Πshiftn cutoff size α) ⊗ (Πshiftn cutoff size β))
Πshiftn cutoff size (μ α)   = μ (Πshiftn cutoff size α)
Πshiftn cutoff size (Π α)   = Π (Πshiftn (1 + cutoff) size α)

Πshift : ℕ → Ty → Ty
Πshift cutoff = Πshiftn cutoff 1

Πsub : Ty → ℕ → Ty → Ty 
Πsub ①                 n              δ = ①  
Πsub (ι m)              n              δ with compare n m
Πsub (ι .m)             .m             δ | equal   m   = δ
Πsub (ι .m)             .(suc (m + k)) δ | greater m k = ι m
Πsub (ι .(suc (m + k))) .m             δ | less    m k = ι (m + k)
Πsub (η n)              m              δ = (η n)
Πsub (α ⇒ β)            n              δ = (Πsub α n δ) ⇒ (Πsub β n δ)
Πsub (α ⊕ β)            n              δ = (Πsub α n δ) ⊕ (Πsub β n δ)
Πsub (α ⊗ β)            n              δ = (Πsub α n δ) ⊗ (Πsub β n δ)
Πsub (Π α)              n              δ = Π (Πsub α (1 + n) (Πshift n δ))
Πsub (μ α)              n              δ = μ (Πsub α n δ)

_⟦_⟧Πty : Ty → Ty → Ty
_⟦_⟧Πty α β = Πsub α 0 β

μshiftn : ℕ → ℕ → Ty → Ty
μshiftn cutoff size ①   = ① 
μshiftn cutoff size (η n)   with cutoff ≤? n
μshiftn cutoff size (η n)   | yes p = η (size + n)
μshiftn cutoff size (η n)   | no p  = η n
μshiftn cutoff size (ι n)   = ι n
μshiftn cutoff size (α ⇒ β) = ((μshiftn cutoff size α) ⇒ (μshiftn cutoff size β))
μshiftn cutoff size (α ⊕ β) = ((μshiftn cutoff size α) ⊕ (μshiftn cutoff size β))
μshiftn cutoff size (α ⊗ β) = ((μshiftn cutoff size α) ⊗ (μshiftn cutoff size β))
μshiftn cutoff size (Π α)   = Π (μshiftn cutoff size α)
μshiftn cutoff size (μ α)   = μ (μshiftn (1 + cutoff) size α)

μshift : ℕ → Ty → Ty
μshift cutoff = μshiftn cutoff 1

μsub : Ty → ℕ → Ty → Ty 
μsub ①                 n              δ = ①  
μsub (η m)              n              δ with compare n m
μsub (η .m)             .m             δ | equal   m   = δ
μsub (η .m)             .(suc (m + k)) δ | greater m k = η m
μsub (η .(suc (m + k))) .m             δ | less    m k = η (m + k)
μsub (ι n)              m              δ = (ι n)
μsub (α ⇒ β)            n              δ = (μsub α n δ) ⇒ (μsub β n δ)
μsub (α ⊕ β)            n              δ = (μsub α n δ) ⊕ (μsub β n δ)
μsub (α ⊗ β)            n              δ = (μsub α n δ) ⊗ (μsub β n δ)
μsub (μ α)              n              δ = μ (μsub α (1 + n) (μshift n δ))
μsub (Π α)              n              δ = Π (μsub α n δ)

_⟦_⟧μ : Ty → Ty → Ty
_⟦_⟧μ α β = μsub α 0 β

{-
tyWkLe : ∀ {n m ΔP} → n ≤ m → m ∈ ΔP → suc m ∈ suc ΔP 
tyWkLe {zero}  {m} {ΔP}         p        q          = innext q
tyWkLe {suc n} {m} {[]}         p        ()
tyWkLe {suc n} {zero}  {b ∷ ΔP} ()       q 
tyWkLe {suc n} {suc m} {b ∷ ΔP} (s≤s p)  (innext q) = innext (tyWkLe p q)

tyWkGt : ∀ {n m ΔP} → n > m → m ∈ ΔP → m ∈ Πshiftn ΔP 
tyWkGt {zero}  {m} {ΔP}             ()       q          
tyWkGt {suc n} {m} {[]}             p        ()
tyWkGt {suc n} {zero}  {true ∷ ΔP}  p        q          = inzero
tyWkGt {suc n} {zero}  {false ∷ ΔP} p        () 
tyWkGt {suc n} {suc m} {b ∷ ΔP}     (s≤s p)  (innext q) = innext (tyWkGt p q)


tyshiftnCorrect : ∀ {ΔP ΔN α n} → (ΔP · ΔN ⊢ α) → ((insert false n ΔP) · (insert false n ΔN) ⊢ (tyshiftn n 1 α))
tyshiftnCorrect {ΔP} {ΔN} {ι m}   {n} (VarValid p)   with n ≤? m 
tyshiftnCorrect {ΔP} {ΔN} {ι m}   {n} (VarValid p)   | yes q = VarValid (tyWkLe q p)
tyshiftnCorrect {ΔP} {ΔN} {ι m}   {n} (VarValid p)   | no  q = VarValid (tyWkGt (≰⇒> q) p)
tyshiftnCorrect {ΔP} {ΔN} {α ⇒ β} {n} (ImpValid p q) = ImpValid (tyshiftnCorrect p) (tyshiftnCorrect q)
tyshiftnCorrect {ΔP} {ΔN} {Π α}   {n} (AllValid p)   = AllValid (tyshiftnCorrect p)
-}

invι : ∀ {n m} → (ι n ≡ ι m) → n ≡ m
invι refl = refl 

invη : ∀ {n m} → (η n ≡ η m) → n ≡ m
invη refl = refl 

invμ : ∀ {α β} → (μ α ≡ μ β) → α ≡ β
invμ refl = refl 

invΠ : ∀ {α β} → (Π α ≡ Π β) → α ≡ β
invΠ refl = refl 

inv⇒L : ∀ {α β δ γ} → (α ⇒ β ≡ δ ⇒ γ) → α ≡ δ
inv⇒L {.α} {β} {α} {.β} refl = refl

inv⇒R : ∀ {α β δ γ} → (α ⇒ β ≡ δ ⇒ γ) → β ≡ γ
inv⇒R {.α} {β} {α} {.β} refl = refl

inv⊕L : ∀ {α β δ γ} → (α ⊕ β ≡ δ ⊕ γ) → α ≡ δ
inv⊕L {.α} {β} {α} {.β} refl = refl

inv⊕R : ∀ {α β δ γ} → (α ⊕ β ≡ δ ⊕ γ) → β ≡ γ
inv⊕R {.α} {β} {α} {.β} refl = refl

inv⊗L : ∀ {α β δ γ} → (α ⊗ β ≡ δ ⊗ γ) → α ≡ δ
inv⊗L {.α} {β} {α} {.β} refl = refl

inv⊗R : ∀ {α β δ γ} → (α ⊗ β ≡ δ ⊗ γ) → β ≡ γ
inv⊗R {.α} {β} {α} {.β} refl = refl

_≟_ty : Decidable {A = Ty} _≡_
①       ≟ ① ty      = yes refl
①       ≟ (ι m) ty   = no (λ ())
①       ≟ (η m) ty   = no (λ ())
①       ≟ (δ ⇒ γ) ty = no (λ ())  
①       ≟ (δ ⊕ γ) ty = no (λ ()) 
①       ≟ (δ ⊗ γ) ty = no (λ ()) 
①       ≟ (μ β) ty   = no (λ ()) 
①       ≟ (Π β) ty   = no (λ ()) 
(ι n)   ≟ ① ty       = no (λ ())
(ι n)   ≟ (ι m) ty   with n ≟ m 
(ι .n)  ≟ (ι n) ty   | yes refl = yes refl
(ι n)   ≟ (ι m) ty   | no p  = no (p ∘ invι)
(ι n)   ≟ (η m) ty   = no (λ ())
(ι n)   ≟ (δ ⇒ γ) ty = no (λ ())  
(ι n)   ≟ (δ ⊕ γ) ty = no (λ ()) 
(ι n)   ≟ (δ ⊗ γ) ty = no (λ ()) 
(ι n)   ≟ (μ β) ty   = no (λ ()) 
(ι n)   ≟ (Π β) ty   = no (λ ()) 
(η n)   ≟ ① ty       = no (λ ())
(η n)   ≟ (ι m) ty   = no (λ ())
(η n)   ≟ (η m) ty   with n ≟ m 
(η .n)  ≟ (η n) ty   | yes refl = yes refl
(η n)   ≟ (η m) ty   | no p  = no (p ∘ invη)
(η n)   ≟ (δ ⇒ γ) ty = no (λ ())  
(η n)   ≟ (δ ⊕ γ) ty = no (λ ()) 
(η n)   ≟ (δ ⊗ γ) ty = no (λ ()) 
(η n)   ≟ (μ β) ty   = no (λ ()) 
(η n)   ≟ (Π β) ty   = no (λ ()) 
(μ α)   ≟ ① ty       = no (λ ())
(μ α)   ≟ (ι m) ty   = no (λ ())
(μ α)   ≟ (η m) ty   = no (λ ())
(μ α)   ≟ (δ ⇒ γ) ty = no (λ ())  
(μ α)   ≟ (δ ⊕ γ) ty = no (λ ()) 
(μ α)   ≟ (δ ⊗ γ) ty = no (λ ()) 
(μ α)   ≟ (μ β) ty   with α ≟ β ty 
(μ .β)  ≟ (μ β) ty   | yes refl = yes refl 
(μ α)   ≟ (μ β) ty   | no p  = no (p ∘ invμ)
(μ α)   ≟ (Π β) ty   = no (λ ())
(Π α)   ≟ ① ty       = no (λ ())
(Π α)   ≟ (ι m) ty   = no (λ ()) 
(Π α)   ≟ (η m) ty   = no (λ ())
(Π α)   ≟ (δ ⇒ γ) ty = no (λ ())
(Π α)   ≟ (δ ⊕ γ) ty = no (λ ())
(Π α)   ≟ (δ ⊗ γ) ty = no (λ ()) 
(Π α)   ≟ (Π β) ty   with α ≟ β ty 
(Π .α)  ≟ (Π α) ty   | yes refl = yes refl 
(Π α)   ≟ (Π β) ty   | no p  = no (p ∘ invΠ)
(Π α)   ≟ (μ β) ty   = no (λ ()) 
(α ⇒ β) ≟ ① ty      = no (λ ())
(α ⇒ β) ≟ (ι m) ty   = no (λ ())
(α ⇒ β) ≟ (η m) ty   = no (λ ())
(α ⇒ β) ≟ (δ ⇒ γ) ty   with α ≟ δ ty  
(.α ⇒ β) ≟ (α ⇒ γ) ty  | yes refl with β ≟ γ ty 
(.α ⇒ .β) ≟ (α ⇒ β) ty | yes refl | yes refl = yes refl
(.α ⇒ δ) ≟ (α ⇒ γ) ty  | yes refl | no p = no (p ∘ inv⇒R)
(α ⇒ β) ≟ (δ ⇒ γ) ty   | no p = no (p ∘ inv⇒L)
(α ⇒ β) ≟ (δ ⊕ γ) ty = no (λ ()) 
(α ⇒ β) ≟ (δ ⊗ γ) ty = no (λ ()) 
(α ⇒ β) ≟ (μ δ) ty   = no (λ ()) 
(α ⇒ β) ≟ (Π δ) ty   = no (λ ()) 
(α ⊕ β) ≟ ① ty      = no (λ ())
(α ⊕ β) ≟ (ι m) ty   = no (λ ())
(α ⊕ β) ≟ (η m) ty   = no (λ ())
(α ⊕ β) ≟ (δ ⊕ γ) ty   with α ≟ δ ty  
(.α ⊕ β) ≟ (α ⊕ γ) ty  | yes refl with β ≟ γ ty 
(.α ⊕ .β) ≟ (α ⊕ β) ty | yes refl | yes refl = yes refl
(.α ⊕ δ) ≟ (α ⊕ γ) ty  | yes refl | no p = no (p ∘ inv⊕R)
(α ⊕ β) ≟ (δ ⊕ γ) ty   | no p = no (p ∘ inv⊕L)
(α ⊕ β) ≟ (δ ⇒ γ) ty = no (λ ()) 
(α ⊕ β) ≟ (δ ⊗ γ) ty = no (λ ()) 
(α ⊕ β) ≟ (μ δ) ty   = no (λ ()) 
(α ⊕ β) ≟ (Π δ) ty   = no (λ ()) 
(α ⊗ β) ≟ ① ty      = no (λ ())
(α ⊗ β) ≟ (ι m) ty   = no (λ ())
(α ⊗ β) ≟ (η m) ty   = no (λ ())
(α ⊗ β) ≟ (δ ⊗ γ) ty   with α ≟ δ ty  
(.α ⊗ β) ≟ (α ⊗ γ) ty  | yes refl with β ≟ γ ty 
(.α ⊗ .β) ≟ (α ⊗ β) ty | yes refl | yes refl = yes refl
(.α ⊗ δ) ≟ (α ⊗ γ) ty  | yes refl | no p = no (p ∘ inv⊗R)
(α ⊗ β) ≟ (δ ⊗ γ) ty   | no p = no (p ∘ inv⊗L)
(α ⊗ β) ≟ (δ ⇒ γ) ty = no (λ ()) 
(α ⊗ β) ≟ (δ ⊕ γ) ty = no (λ ()) 
(α ⊗ β) ≟ (μ δ) ty   = no (λ ()) 
(α ⊗ β) ≟ (Π δ) ty   = no (λ ()) 

{-
tyeqdec : ∀ t s → Dec (t ≡ s)
tyeqdec t s = ? 
-}

data _·_⊢_type : TyCtx → TyCtx → Ty → Set where 
     UnitValid : ∀ {Δ Δ+} → 
       Δ · Δ+ ⊢ ① type 
     VarValid : ∀ {n Δ Δ+} → 
       (n ∈ Δ) → 
       Δ · Δ+ ⊢ (ι n) type 
     FixValid : ∀ {n Δ Δ+} → 
       (n ∈ Δ+) → 
       Δ · Δ+ ⊢ (η n) type 
     ImpValid : ∀ {Δ Δ+ α β} → 
       Δ · 0 ⊢ α type → 
       Δ · Δ+ ⊢ β type →
       Δ · Δ+ ⊢ (α ⇒ β) type
     AndValid : ∀ {Δ Δ+ α β} → 
       Δ · Δ+ ⊢ α type → 
       Δ · Δ+ ⊢ β type → 
       Δ · Δ+ ⊢ (α ⊗ β) type
     OrValid : ∀ {Δ Δ+ α β} → 
       Δ · Δ+ ⊢ α type → 
       Δ · Δ+ ⊢ β type → 
       Δ · Δ+ ⊢ (α ⊕ β) type
     MuValid : ∀ {Δ Δ+ α} → 
       Δ · (suc Δ+) ⊢ α type → 
       Δ · Δ+ ⊢ μ α type
     AllValid : ∀ {Δ Δ+ α} → 
       (suc Δ) · Δ+ ⊢ α type → 
       Δ · Δ+ ⊢ Π α type

varValidInversion : ∀ {Δ Δ+ n} → Δ · Δ+ ⊢ ι n type → n ∈ Δ
varValidInversion {Δ} {Δ+} {n} (VarValid p) = p

fixValidInversion : ∀ {Δ Δ+ n} → Δ · Δ+ ⊢ η n type → n ∈ Δ+
fixValidInversion {Δ} {Δ+} {n} (FixValid p) = p

orValidInversionL : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⊕ β) type → (Δ · Δ+ ⊢ α type)
orValidInversionL {Δ} {Δ+} {α} {β} (OrValid p q) = p

orValidInversionR : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⊕ β) type → (Δ · Δ+ ⊢ β type)
orValidInversionR {Δ} {Δ+} {α} {β} (OrValid p q) = q

impValidInversionL : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⇒ β) type → (Δ · 0 ⊢ α type)
impValidInversionL {Δ} {Δ+} {α} {β} (ImpValid p q) = p

impValidInversionR : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⇒ β) type → (Δ · Δ+ ⊢ β type)
impValidInversionR {Δ} {Δ+} {α} {β} (ImpValid p q) = q

andValidInversionL : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⊗ β) type → (Δ · Δ+ ⊢ α type)
andValidInversionL {Δ} {Δ+} {α} {β} (AndValid p q) = p

andValidInversionR : ∀ {Δ Δ+ α β} → Δ · Δ+ ⊢ (α ⊗ β) type → (Δ · Δ+ ⊢ β type)
andValidInversionR {Δ} {Δ+} {α} {β} (AndValid p q) = q

allValidInversion : ∀ {Δ Δ+ α} → Δ · Δ+ ⊢ Π α type → ((suc Δ) · Δ+ ⊢ α type)
allValidInversion {Δ} {Δ+} {α} (AllValid p) = p

muValidInversion : ∀ {Δ Δ+ α} → Δ · Δ+ ⊢ μ α type → (Δ · (suc Δ+) ⊢ α type)
muValidInversion {Δ} {Δ+} {α} (MuValid p) = p

isValid : ∀ Δ Δ+ α → Dec (Δ · Δ+ ⊢ α type)
isValid Δ Δ+ ①       = yes UnitValid
isValid Δ Δ+ (ι n)   with (intyctx n Δ)
isValid Δ Δ+ (ι n)   | yes p = yes (VarValid p)
isValid Δ Δ+ (ι n)   | no p  = no (λ { (VarValid q) → p q })
isValid Δ Δ+ (η n)   with (intyctx n Δ+)
isValid Δ Δ+ (η n)   | yes p = yes (FixValid p)
isValid Δ Δ+ (η n)   | no p  = no (λ { (FixValid q) → p q })
isValid Δ Δ+ (α ⇒ β) with isValid Δ 0 α
isValid Δ Δ+ (α ⇒ β) | yes p with isValid Δ Δ+ β
isValid Δ Δ+ (α ⇒ β) | yes p | yes q = yes (ImpValid p q) 
isValid Δ Δ+ (α ⇒ β) | yes p | no q  = no (q ∘ impValidInversionR)
isValid Δ Δ+ (α ⇒ β) | no p  = no (p ∘ impValidInversionL)
isValid Δ Δ+ (α ⊗ β) with isValid Δ Δ+ α
isValid Δ Δ+ (α ⊗ β) | yes p with isValid Δ Δ+ β
isValid Δ Δ+ (α ⊗ β) | yes p | yes q = yes (AndValid p q) 
isValid Δ Δ+ (α ⊗ β) | yes p | no q  = no (q ∘ andValidInversionR)
isValid Δ Δ+ (α ⊗ β) | no p  = no (p ∘ andValidInversionL)
isValid Δ Δ+ (α ⊕ β) with isValid Δ Δ+ α
isValid Δ Δ+ (α ⊕ β) | yes p with isValid Δ Δ+ β
isValid Δ Δ+ (α ⊕ β) | yes p | yes q = yes (OrValid p q) 
isValid Δ Δ+ (α ⊕ β) | yes p | no q  = no (q ∘ orValidInversionR)
isValid Δ Δ+ (α ⊕ β) | no p  = no (p ∘ orValidInversionL)
isValid Δ Δ+ (Π α)   with isValid (suc Δ) Δ+ α
isValid Δ Δ+ (Π α)   | yes p = yes (AllValid p) 
isValid Δ Δ+ (Π α)   | no p  = no (p ∘ allValidInversion)
isValid Δ Δ+ (μ α)   with isValid Δ (suc Δ+) α
isValid Δ Δ+ (μ α)   | yes p = yes (MuValid p) 
isValid Δ Δ+ (μ α)   | no p  = no (p ∘ muValidInversion)

data Term : Set where 
  u : Term                             -- unit
  v : ℕ → Term                        -- variable 
  ƛ : Ty → Term → Term               -- term abstraction
  Λ : Term → Term                     -- Type abstraction
  ↑ : Term → Ty → Term               -- unfold μ 
  ↓ : Term → Ty → Term               -- fold μ
  _○_ : Term → Term → Term           -- Application
  _●_ : Term → Ty → Term             -- Type application
  _*_ : Term → Term → Term           -- Pair
  lft : Term → Ty → Term             -- left injection
  rgt : Term → Ty → Term             -- right injection
  [_∥_]_ : Term → Term → Term → Term -- case (or elim)
  π₁ : Term → Term                    -- project 1 
  π₂ : Term → Term                    -- project 2

Πsubt : Term → ℕ → Ty → Term
Πsubt u       n δ = u
Πsubt (v m)   n δ = v m
Πsubt (Λ t)   n δ = Λ (Πsubt t (1 + n) (Πshift 0 δ))
Πsubt (ƛ α t) n δ = ƛ (Πsub α n δ) (Πsubt t n δ)
Πsubt (t ○ s) n δ = (Πsubt t n δ) ○ (Πsubt t n δ)
Πsubt (t ● α) n δ = (Πsubt t n δ) ● (Πsub α n δ)
Πsubt (↑ t α) n δ = ↑ (Πsubt t n δ) (Πsub α n δ)
Πsubt (↓ t α) n δ = ↓ (Πsubt t n δ) (Πsub α n δ)
Πsubt (lft t α) n δ = lft (Πsubt t n δ) (Πsub α n δ)
Πsubt (rgt t α) n δ = rgt (Πsubt t n δ) (Πsub α n δ)
Πsubt (t * s) n δ = (Πsubt t n δ) * (Πsubt t n δ)
Πsubt (π₁ t) n δ = π₁ (Πsubt t n δ)
Πsubt (π₂ t) n δ = π₂ (Πsubt t n δ)
Πsubt ([ t ∥ s ] r) n δ = [ (Πsubt t n δ) ∥ (Πsubt s n δ) ] (Πsubt r n δ)

_⟦_⟧Πtt : Term → Ty → Term
_⟦_⟧Πtt t α = Πsubt t 0 α

{- This shouldn't happen, as these types should always be closed. 
μsubt : Term → ℕ → Ty → Term
μsubt u       n δ = u
μsubt (v m)   n δ = v m
μsubt (ƛ α t) n δ = ƛ (μsub α n δ) (μsubt t n δ)
μsubt (t ○ s) n δ = (μsubt t n δ) ○ (μsubt t n δ)
μsubt (t ● α) n δ = (μsubt t n δ) ● (μsub α n δ)
μsubt (↑ t α) n δ = ↑ (μsubt t n δ) (μsub α n δ)
μsubt (↓ t α) n δ = ↓ (μsubt t n δ) (μsub α n δ)
μsubt (lft t α) n δ = lft (μsubt t n δ) (μsub α n δ)
μsubt (rgt t α) n δ = rgt (μsubt t n δ) (μsub α n δ)
μsubt (t * s) n δ = (μsubt t n δ) * (μsubt t n δ)
μsubt (π₁ t) n δ = π₁ (μsubt t n δ)
μsubt (π₂ t) n δ = π₂ (μsubt t n δ)
μsubt ([ t ∥ s ] r) n δ = [ (μsubt t n δ) ∥ (μsubt s n δ) ] (μsubt r n δ)

_⟦_⟧μtt : Term → Ty → Term
_⟦_⟧μtt t α = μsubt t 0 α
-} 

Ctx : Set
Ctx = List Ty

data _·_⊢_ctx : TyCtx → TyCtx → Ctx → Set where 
  ctxEmpty : ∀ {Δ Δ+} → 
    Δ · Δ+ ⊢ [] ctx 
  ctxNext : ∀ {Δ Δ+ Γ α} → 
    Δ · Δ+ ⊢ α type → 
    Δ · Δ+ ⊢ Γ ctx → 
    Δ · Δ+ ⊢ (α ∷ Γ) ctx
  
data ⟦_∶_⟧∈ : ℕ → Ty → Ctx → Set where 
  inctxBase : ∀ {α Γ} → ⟦ zero ∶ α ⟧∈ (α ∷ Γ)
  inctxNext : ∀ {n α β Γ} → ⟦ n ∶ α ⟧∈ Γ → ⟦(suc n) ∶ α ⟧∈ (β ∷ Γ)  

inctxBaseInv : ∀ {α β Γ} → ⟦ zero ∶ α ⟧∈ (β ∷ Γ) → α ≡ β
inctxBaseInv inctxBase = refl

inctxNextInv : ∀ {n α β Γ} →  ⟦(suc n) ∶ α ⟧∈ (β ∷ Γ) → ⟦ n ∶ α ⟧∈ Γ
inctxNextInv (inctxNext p) = p

inctxdec : ∀ n α Γ → Dec (⟦ n ∶ α ⟧∈ Γ)
inctxdec zero    α  []      = no (λ()) 
inctxdec zero    α  (β ∷ Γ) with α ≟ β ty
inctxdec zero    .α (α ∷ Γ) | yes refl = yes inctxBase  
inctxdec zero    α  (β ∷ Γ) | no p = no (p ∘ inctxBaseInv)
inctxdec (suc n) α  []      = no (λ())
inctxdec (suc n) α  (β ∷ Γ) with inctxdec n α Γ
inctxdec (suc n) α  (β ∷ Γ) | yes p = yes (inctxNext p) 
inctxdec (suc n) α  (β ∷ Γ) | no p  = no (p ∘ inctxNextInv)

data _·_·_⊢_∶_ : TyCtx → TyCtx → Ctx → Term → Ty → Set where 
  I① : ∀ {Δ Δ+ Γ} → 
    Δ · Δ+ ⊢ Γ ctx → 
    Δ · Δ+ · Γ ⊢ u ∶ ①
  Iv : ∀ {Δ Δ+ Γ n α} → 
    Δ · Δ+ ⊢ Γ ctx → 
    ⟦ n ∶ α ⟧∈ Γ → 
    Δ · Δ+ · Γ ⊢ (v n) ∶ α
  I⇒ : ∀ {Δ Δ+ Γ t α β} → 
    Δ · Δ+ · (α ∷ Γ) ⊢ t ∶ β → 
    Δ · Δ+ · Γ ⊢ (ƛ α t) ∶ (α ⇒ β)
  E⇒ : ∀ {Δ Δ+ Γ s t α β} → 
    Δ · Δ+ · Γ ⊢ t ∶ (α ⇒ β) → 
    Δ · Δ+ · Γ ⊢ s ∶ α → 
    Δ · Δ+ · Γ ⊢ (t ○ s) ∶ β
  IΠ : ∀ {Δ Δ+ Γ t α} → 
    (suc Δ) · Δ+ · Γ ⊢ t ∶ α → 
    Δ · Δ+ · Γ ⊢ (Λ t) ∶ (Π α)
  EΠ : ∀ {Δ Δ+ Γ t α β} → 
    Δ · Δ+ ⊢ α type → 
    Δ · Δ+ · Γ ⊢ t ● α ∶ β → 
    Δ · Δ+ · Γ ⊢ t ⟦ α ⟧Πtt ∶ β ⟦ α ⟧Πty
  Iμ : ∀ {Δ Δ+ Γ t α} → 
    Δ · Δ+ · Γ ⊢ t ∶ μ α → 
    Δ · Δ+ · Γ ⊢ (↑ t (μ α)) ∶ α ⟦ μ α ⟧μ
  Eμ : ∀ {Δ Δ+ Γ t α} → 
    Δ · Δ+ · Γ ⊢ t ∶ α ⟦ μ α ⟧μ → 
    Δ · Δ+ · Γ ⊢ (↓ t (μ α)) ∶ μ α
  I⊕L : ∀ {Δ Δ+ Γ t α β} →
    Δ · Δ+ · Γ ⊢ t ∶ α → 
    Δ · Δ+ · Γ ⊢ (lft t β) ∶ (α ⊕ β)
  I⊕R : ∀ {Δ Δ+ Γ t α β} →
    Δ · Δ+ · Γ ⊢ t ∶ β → 
    Δ · Δ+ · Γ ⊢ (rgt t α) ∶ (α ⊕ β)
  E⊕ : ∀ {Δ Δ+ Γ s t r α β δ} → 
    Δ · Δ+ · Γ ⊢ t ∶ (α ⇒ δ) → 
    Δ · Δ+ · Γ ⊢ s ∶ (β ⇒ δ) → 
    Δ · Δ+ · Γ ⊢ r ∶ (α ⊕ β) → 
    Δ · Δ+ · Γ ⊢ [ t ∥ s ] r ∶ δ
  I⊗ : ∀ {Δ Δ+ Γ s t α β} → 
    Δ · Δ+ · Γ ⊢ s ∶ α → 
    Δ · Δ+ · Γ ⊢ t ∶ β → 
    Δ · Δ+ · Γ ⊢ s * t ∶ (α ⊗ β)
  E⊗L : ∀ {Δ Δ+ Γ s α β} → 
    Δ · Δ+ · Γ ⊢ s ∶ (α ⊗ β) → 
    Δ · Δ+ · Γ ⊢ π₁ s ∶ α
  E⊗R : ∀ {Δ Δ+ Γ s α β} → 
    Δ · Δ+ · Γ ⊢ s ∶ (α ⊗ β) →
    Δ · Δ+ · Γ ⊢ π₂ s ∶ β
