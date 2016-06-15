
open import Relation.Binary -- .PropositionalEquality
open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary
open import Data.Sum
open import Data.Empty
--open import Function

module While (Atom : Set) (_≟_atom : Decidable (_≡_ {A = Atom})) where

open import Data.Nat
open import Data.Maybe

Locs : Set
Locs = Atom

data Arith : Set where
  L : Locs → Arith
  N : ℕ → Arith
  _⊕_ : Arith → Arith → Arith

data BoolVal : Set where
  tt : BoolVal
  ff : BoolVal

data Bool : Set where
  true : Bool
  false : Bool
  _==_ : (E₁ : Arith) → (E₂ : Arith) → Bool
  _∨_ : Bool → Bool → Bool
  _∧_ : Bool → Bool → Bool
  not : Bool → Bool
  
data Com : Set where
  _≔_ : Locs → Arith → Com
  if_then_else_ : Bool → Com → Com → Com
  _,_ : Com → Com → Com
  skip : Com
  while_do_ : Bool → Com → Com

State : Set
State = Locs → ℕ

{-

Either we have to add errors and a map to Maybe ℕ or we have to return some value
to avoid getting stuck (in the progress theorem below) or we have to draw locations
from a finite set (perhaps Fin n for some value n). 

-}
empty : State
empty _ = 42

_[_↦_] : State → Locs → ℕ → State
(f [ l ↦ n ]) x with l ≟ x atom
(f [ l ↦ n ]) x | yes p = n
(f [ l ↦ n ]) x | no ¬p = f x
  

data ⟨_,_⟩⇓_arith : Arith → State → ℕ → Set where

  B-num : ∀ {n s} → 

        --------------------------
        ⟨ N n , s ⟩⇓ n arith

  B-add : ∀ {E₁ E₂ s n₁ n₂} → 

        ⟨ E₁ , s ⟩⇓ n₁ arith →  ⟨ E₂ , s ⟩⇓ n₂ arith → 
        ------------------------------------------------
            ⟨ E₁ ⊕ E₂ , s ⟩⇓ (n₁ + n₂) arith

  B-loc : ∀ {l s n} → 

             s l ≡ n → 
        -----------------------
        ⟨ (L l) , s ⟩⇓ n arith

data ⟨_,_⟩⇓_bool : Bool → State → BoolVal → Set where

  B-true : ∀ {s} →
  
           -----------------------
           ⟨ true , s ⟩⇓ tt bool


  B-false : ∀ {s} → 
  
           -------------------------
           ⟨ false , s ⟩⇓ ff bool

  B-∧true : ∀ {B₁ B₂ s} → 

           ⟨ B₁ , s ⟩⇓ tt bool → ⟨ B₂ , s ⟩⇓ tt bool → 
           --------<------------------------------------
               ⟨ B₁ ∧ B₂ , s ⟩⇓ tt bool

  B-∧false₁ : ∀ {B₁ B₂ s} → 

             ⟨ B₁ , s ⟩⇓ ff bool →
           --------------------------
           ⟨ B₁ ∧ B₂ , s ⟩⇓ ff bool

  B-∧false₂ : ∀ {B₁ B₂ s} → 

            ⟨ B₂ , s ⟩⇓ ff bool →
           --------------------------
           ⟨ B₁ ∧ B₂ , s ⟩⇓ ff bool

  B-∨true₁ : ∀ {B₁ B₂ s} → 

             ⟨ B₁ , s ⟩⇓ tt bool → 
           --------------------------
           ⟨ B₁ ∨ B₂ , s ⟩⇓ tt bool

  B-∨true₂ : ∀ {B₁ B₂ s} → 

             ⟨ B₂ , s ⟩⇓ tt bool → 
           --------------------------
           ⟨ B₁ ∨ B₂ , s ⟩⇓ tt bool

  B-∨false : ∀ {B₁ B₂ s} → 

           ⟨ B₁ , s ⟩⇓ ff bool → ⟨ B₂ , s ⟩⇓ ff bool →
           -----------------------------------------------
                 ⟨ B₁ ∨ B₂ , s ⟩⇓ ff bool
                 
  B-==-true : ∀ {E₁ E₂ s n} →

        ⟨ E₁ , s ⟩⇓ n arith → ⟨ E₂ , s ⟩⇓ n arith → 
        --------------------------------------------------
                 ⟨ E₁ == E₂ , s ⟩⇓ tt bool 

  B-==-false : ∀ {E₁ E₂ s n m} →

        ⟨ E₁ , s ⟩⇓ n arith → ⟨ E₂ , s ⟩⇓ m arith → n ≢ m → 
        -------------------------------------------------
                 ⟨ E₁ == E₂ , s ⟩⇓ ff bool 

  B-not-true : ∀ {B s} →

          ⟨ B , s ⟩⇓ tt bool → 
        -------------------
        ⟨ not B , s ⟩⇓ ff bool

  B-not-false : ∀ {B s} →

          ⟨ B , s ⟩⇓ ff bool → 
        -------------------
        ⟨ not B , s ⟩⇓ tt bool

data ⟨_,_⟩⇓_com : Com → State → State → Set where

  B-assign : ∀ {E l s n} → 

           ⟨ E , s ⟩⇓ n arith → 
         -----------------------------
         ⟨ l ≔ E , s ⟩⇓ s [ l ↦ n ] com

  B-seq : ∀ {C₁ C₂ s₁ s₂ s₃} →

         ⟨ C₁ , s₁ ⟩⇓ s₂ com → ⟨ C₂ , s₂ ⟩⇓ s₃ com → 
         -----------------------------------------
                ⟨ (C₁ , C₂) , s₁ ⟩⇓ s₃ com
  
  B-if-true : ∀ {B C₁ C₂ s s'} → 

         ⟨ B , s ⟩⇓ tt bool → ⟨ C₁ , s ⟩⇓ s' com → 
         -----------------------------------------
            ⟨ if B then C₁ else C₂ , s ⟩⇓ s' com

  B-if-false : ∀ {B C₁ C₂ s s'} → 

         ⟨ B , s ⟩⇓ ff bool → ⟨ C₂ , s ⟩⇓ s' com → 
         -----------------------------------------
            ⟨ if B then C₁ else C₂ , s ⟩⇓ s' com

  B-while-false : ∀ {B C s} → 

            ⟨ B , s ⟩⇓ ff bool →
          ---------------------------
          ⟨ while B do C , s ⟩⇓ s com

  B-while-true : ∀ {B C s₁ s₂ s₃} → 

         ⟨ B , s₁ ⟩⇓ tt bool →
         ⟨ C , s₁ ⟩⇓ s₂ com → 
         ⟨ while B do C , s₂ ⟩⇓ s₃ com → 
         -----------------------------
         ⟨ while B do C , s₁ ⟩⇓ s₃ com

  B-skip : ∀ {s} →

         -------------------
         ⟨ skip , s ⟩⇓ s com

⇓-deterministic-arith : ∀ {C s n₁ n₂} → ⟨ C , s ⟩⇓ n₁ arith → ⟨ C , s ⟩⇓ n₂ arith → n₁ ≡ n₂
⇓-deterministic-arith B-num B-num = refl
⇓-deterministic-arith (B-add p p₁) (B-add q q₁) with ⇓-deterministic-arith p q | ⇓-deterministic-arith p₁ q₁
⇓-deterministic-arith (B-add p p₁) (B-add q q₁) | P | Q rewrite P | Q = refl
⇓-deterministic-arith (B-loc x) (B-loc x₁) = aux x x₁
  where aux : ∀ {n m o : ℕ} → o ≡ n → o ≡ m → n ≡ m
        aux refl refl = refl

⇓-deterministic-bool : ∀ {B s b₁ b₂} → ⟨ B , s ⟩⇓ b₁ bool → ⟨ B , s ⟩⇓ b₂ bool → b₁ ≡ b₂
⇓-deterministic-bool B-true B-true = refl
⇓-deterministic-bool B-false B-false = refl
⇓-deterministic-bool (B-∧true p p₁) (B-∧true q q₁) = refl
⇓-deterministic-bool (B-∧true p p₁) (B-∧false₁ q) = ⇓-deterministic-bool p q
⇓-deterministic-bool (B-∧true p p₁) (B-∧false₂ q) = ⇓-deterministic-bool p₁ q
⇓-deterministic-bool (B-∧false₁ p) (B-∧true q q₁) = ⇓-deterministic-bool p q
⇓-deterministic-bool (B-∧false₁ p) (B-∧false₁ q) = refl
⇓-deterministic-bool (B-∧false₁ p) (B-∧false₂ q) = refl
⇓-deterministic-bool (B-∧false₂ p) (B-∧true q q₁) = ⇓-deterministic-bool p q₁
⇓-deterministic-bool (B-∧false₂ p) (B-∧false₁ q) = refl
⇓-deterministic-bool (B-∧false₂ p) (B-∧false₂ q) = refl
⇓-deterministic-bool (B-∨true₁ p) (B-∨true₁ q) = refl
⇓-deterministic-bool (B-∨true₁ p) (B-∨true₂ q) = refl
⇓-deterministic-bool (B-∨true₁ p) (B-∨false q q₁) = ⇓-deterministic-bool p q
⇓-deterministic-bool (B-∨true₂ p) (B-∨true₁ q) = refl
⇓-deterministic-bool (B-∨true₂ p) (B-∨true₂ q) = refl
⇓-deterministic-bool (B-∨true₂ p) (B-∨false q q₁) = ⇓-deterministic-bool p q₁
⇓-deterministic-bool (B-∨false p p₁) (B-∨true₁ q) = ⇓-deterministic-bool p q
⇓-deterministic-bool (B-∨false p p₁) (B-∨true₂ q) = ⇓-deterministic-bool p₁ q
⇓-deterministic-bool (B-∨false p p₁) (B-∨false q q₁) = refl
⇓-deterministic-bool (B-==-true x x₁) (B-==-true x₂ x₃) = refl
⇓-deterministic-bool (B-==-false x x₁ p) (B-==-true x₂ x₃) with ⇓-deterministic-arith x₁ x₃
⇓-deterministic-bool (B-==-false x x₁ p) (B-==-true x₂ x₃) | refl with ⇓-deterministic-arith x x₂
⇓-deterministic-bool (B-==-false x x₁ p) (B-==-true x₂ x₃) | refl | refl = ⊥-elim (p refl)
⇓-deterministic-bool (B-==-true x x₁) (B-==-false x₂ x₃ p) with ⇓-deterministic-arith x₁ x₃
⇓-deterministic-bool (B-==-true x x₁) (B-==-false x₂ x₃ p) | refl with ⇓-deterministic-arith x x₂
⇓-deterministic-bool (B-==-true x x₁) (B-==-false x₂ x₃ p) | refl | refl = ⊥-elim (p refl)
⇓-deterministic-bool (B-==-false x x₁ p) (B-==-false x₂ x₃ q) = refl
⇓-deterministic-bool (B-not-true p) (B-not-true q) = refl
⇓-deterministic-bool (B-not-false p) (B-not-false q) = refl 
⇓-deterministic-bool (B-not-true p) (B-not-false q) = ⇓-deterministic-bool q p
⇓-deterministic-bool (B-not-false p) (B-not-true q) = ⇓-deterministic-bool q p 

⇓-deterministic : ∀ {C s s₁ s₂} → ⟨ C , s ⟩⇓ s₂ com → ⟨ C , s ⟩⇓ s₁ com → s₁ ≡ s₂
⇓-deterministic (B-assign x) (B-assign x₁) with ⇓-deterministic-arith x x₁
⇓-deterministic (B-assign x) (B-assign x₁) | refl = refl 
⇓-deterministic (B-seq p p₁) (B-seq q q₁) with ⇓-deterministic p q
⇓-deterministic (B-seq p p₁) (B-seq q q₁) | refl with ⇓-deterministic p₁ q₁
⇓-deterministic (B-seq p p₁) (B-seq q q₁) | refl | refl = refl
⇓-deterministic (B-if-true x p) (B-if-true x₁ q) with ⇓-deterministic p q
⇓-deterministic (B-if-true x p) (B-if-true x₁ q) | refl = refl
⇓-deterministic (B-if-true x p) (B-if-false x₁ q) with ⇓-deterministic-bool x x₁
⇓-deterministic (B-if-true x p) (B-if-false x₁ q) | ()
⇓-deterministic (B-if-false x p) (B-if-true x₁ q) with ⇓-deterministic-bool x x₁
⇓-deterministic (B-if-false x p) (B-if-true x₁ q) | () 
⇓-deterministic (B-if-false x p) (B-if-false x₁ q) = ⇓-deterministic p q
⇓-deterministic (B-while-false x) (B-while-false x₁) = refl
⇓-deterministic (B-while-false x) (B-while-true x₁ q q₁) with ⇓-deterministic-bool x x₁
⇓-deterministic (B-while-false x) (B-while-true x₁ q q₁) | ()
⇓-deterministic (B-while-true x p p₁) (B-while-false x₁) with ⇓-deterministic-bool x x₁
⇓-deterministic (B-while-true x p p₁) (B-while-false x₁) | ()
⇓-deterministic (B-while-true x p p₁) (B-while-true x₁ q q₁) with ⇓-deterministic p q
⇓-deterministic (B-while-true x p p₁) (B-while-true x₁ q q₁) | refl = ⇓-deterministic p₁ q₁
⇓-deterministic B-skip B-skip = refl

open import Data.Product

data ⟨_,_⟩⟶⟨_,_⟩ : Com → State → Com → State → Set where 

  S-assign : ∀ {E s n l} → 

                  ⟨ E , s ⟩⇓ n arith → 
           -----------------------------------
           ⟨ l ≔ E , s ⟩⟶⟨ skip , s [ l ↦ n ] ⟩ 

  S-cond-true : ∀ {B C₁ C₂ s} →

           ⟨ B , s ⟩⇓ tt bool → 
           ----------------------------------------
           ⟨ if B then C₁ else C₂ , s ⟩⟶⟨ C₁ , s ⟩

  S-cond-false : ∀ {B C₁ C₂ s} →

           ⟨ B , s ⟩⇓ ff bool → 
           ----------------------------------------
           ⟨ if B then C₁ else C₂ , s ⟩⟶⟨ C₂ , s ⟩

  S-seq-left : ∀ {C₁ C₁' C₂ s s'} →

                  ⟨ C₁ , s ⟩⟶⟨ C₁' , s' ⟩ → 
           ----------------------------------------
           ⟨ (C₁ , C₂) , s ⟩⟶⟨ (C₁' , C₂) , s' ⟩

  S-seq-right : ∀ {C₂ s} →

           ----------------------------------------
           ⟨ (skip , C₂) , s ⟩⟶⟨  C₂ , s ⟩


  S-whilte-true : ∀ {B C s} →

                     ⟨ B , s ⟩⇓ tt bool →
           ----------------------------------------
           ⟨ while B do C , s ⟩⟶⟨ (C , while B do C) , s ⟩

  S-whilte-false : ∀ {B C s} →

                     ⟨ B , s ⟩⇓ ff bool →
           ----------------------------------------
           ⟨ while B do C , s ⟩⟶⟨ skip , s ⟩


evalArith : ∀ E s → Σ[ n ∈ ℕ ] ⟨ E , s ⟩⇓ n arith
evalArith (L x) s = s x , B-loc refl
evalArith (N x) s = x , B-num
evalArith (E ⊕ E₁) s with evalArith E s | evalArith E₁ s 
evalArith (E ⊕ E₁) s | n , P | m , Q = n + m , B-add P Q

evalBool : ∀ B s → Σ[ b ∈ BoolVal ] ⟨ B , s ⟩⇓ b bool
evalBool true s = tt , B-true
evalBool false s = ff , B-false
evalBool (x == x₁) s with evalArith x s | evalArith x₁ s
evalBool (x == x₁) s | n , P | m , Q with n ≟ m
evalBool (x == x₁) s | n , P | .n , Q | yes refl = tt , B-==-true P Q
evalBool (x == x₁) s | n , P | m , Q | no ¬p = ff , (B-==-false P Q ¬p)
evalBool (B ∨ B₁) s with evalBool B s
evalBool (B ∨ B₁) s | ff , P with evalBool B₁ s
evalBool (B ∨ B₁) s | ff , P | ff , Q = ff , B-∨false P Q
evalBool (B ∨ B₁) s | ff , P | tt , Q = tt , B-∨true₂ Q
evalBool (B ∨ B₁) s | tt , P = tt , B-∨true₁ P
evalBool (B ∧ B₁) s with evalBool B s
evalBool (B ∧ B₁) s | ff , P = ff , B-∧false₁ P
evalBool (B ∧ B₁) s | tt , P with evalBool B₁ s
evalBool (B ∧ B₁) s | tt , P | ff , Q = ff , B-∧false₂ Q
evalBool (B ∧ B₁) s | tt , P | tt , Q = tt , B-∧true P Q
evalBool (not B) s with evalBool B s
evalBool (not B) s | ff , P = tt , B-not-false P
evalBool (not B) s | tt , P = ff , B-not-true P

data Terminal : Com → Set where
  skip-stop : Terminal skip

progress : ∀ C s → Terminal C ⊎ Σ[ C' ∈ Com ] Σ[ s' ∈ State ] ⟨ C , s ⟩⟶⟨ C' , s' ⟩
progress (x ≔ E) s with evalArith E s
progress (x ≔ E) s | n , P = inj₂ (skip , ((s [ x ↦ n ]) , (S-assign P)))
progress (if x then C else C₁) s with evalBool x s
progress (if x then C else C₁) s | tt , P = inj₂ (C , s , S-cond-true P)
progress (if x then C else C₁) s | ff , P = inj₂ (C₁ , s , S-cond-false P)
progress (C , C₁) s  with progress C s
progress (._ , C₁) s | inj₁ skip-stop = inj₂ (C₁ , s , S-seq-right)
progress (C , C₁) s  | inj₂ (C' , s' , P) = inj₂ ((C' , C₁) , s' , S-seq-left P)
progress skip s = inj₁ skip-stop
progress (while x do C) s with evalBool x s
progress (while x do C) s | tt , proj₂ = inj₂ ((C , (while x do C)) , s , S-whilte-true proj₂)
progress (while x do C) s | ff , proj₂ = inj₂ (skip , s , S-whilte-false proj₂)

{-

Partiality due to non-termination is somewhat tricky to model in type theory.

We will use a coinductively defined "Delay" monad.

-}
open import Function
open import Delay

never : ∀ {i A} → ∞Delay A i 
force never = later never

mutual

  seqOne : ∀ {i} C C₁ s → Delay (Σ[ s' ∈ State ] ⟨ C , s ⟩⇓ s' com) i → Delay (Σ[ s'' ∈ State ] ⟨ (C , C₁) , s ⟩⇓ s'' com) i
  seqOne C C₁ s ?P = ?P >>= λ { (s' , P) → seqTwo C C₁ s s' P (evalWhile C₁ s')  } 
  
  seqTwo : ∀ {i} C C₁ s s' → ⟨ C , s ⟩⇓ s' com → Delay (Σ[ s'' ∈ State ] ⟨ C₁ , s' ⟩⇓ s'' com) i → Delay (Σ[ s'' ∈ State ] ⟨ (C , C₁) , s ⟩⇓ s'' com) i
  seqTwo C C₁ s s' P ?Q = ?Q >>= (λ {(s'' , Q) → now (s'' , B-seq P Q)})

{- (evalWhile C s) >>= λ { (s' , Q) →
   (evalWhile (while x do C) s') >>= λ { (s'' , R) →
   now (s'' , (B-while-true P Q R))}} -}
   
  whileOne : ∀ {i} x C s → ⟨ x , s ⟩⇓ tt bool → Delay (Σ[ s' ∈ State ] ⟨ C , s ⟩⇓ s' com) i → Delay (Σ[ s'' ∈ State ] ⟨ while x do C , s ⟩⇓ s'' com) i
  whileOne x C s P ?Q = ?Q >>= λ { (s' , Q) → whileTwo x C s s' P Q (evalWhile (while x do C) s') }

  whileTwo : ∀ {i} x C s s' → ⟨ x , s ⟩⇓ tt bool → ⟨ C , s ⟩⇓ s' com → Delay (Σ[ s'' ∈ State ] ⟨ while x do C , s' ⟩⇓ s'' com) i → Delay (Σ[ s'' ∈ State ] ⟨ while x do C , s ⟩⇓ s'' com) i
  whileTwo x C s s' P Q ?R = {!!}

  evalWhile : ∀ {i} C s → Delay (Σ[ s' ∈ State ] ⟨ C , s ⟩⇓ s' com) i
  evalWhile (x ≔ x₁) s with evalArith x₁ s
  evalWhile (x ≔ x₁) s | n , P = now ((s [ x ↦ n ] ) , B-assign P)
  evalWhile (if x then C else C₁) s with evalBool x s
  evalWhile (if x then C else C₁) s | tt , P = later! (evalWhile C s) >>= λ { (s' , Q) → now (s' , B-if-true P Q)}
  evalWhile (if x then C else C₁) s | ff , P = later! (evalWhile C₁ s) >>= λ { (s' , Q) → now (s' , B-if-false P Q)}
  evalWhile (C , C₁) s = seqOne C C₁ s (evalWhile C s)
  evalWhile skip s = now (s , B-skip)
  evalWhile (while x do C) s with evalBool x s
  evalWhile (while x do C) s | tt , P = whileOne x C s P (evalWhile C s)
  evalWhile (while x do C) s | ff , P = now (s , B-while-false P)
        
⟦_⟧ : ∀ {i} → Com → State → Delay State i
⟦ C ⟧ s = evalWhile C s >>= (now ∘ proj₁)
