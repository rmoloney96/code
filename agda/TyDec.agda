module TyDec where 

open import Function using (_∘_)
open import Data.Nat hiding (_*_) 
open import Data.Fin renaming (zero to fzero ; suc to fsuc)
open import Data.Fin.Props renaming (_≟_ to _≟_fin)
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

data Tree : Set where 
  Nullary : Tree
  NullaryNat : Fin 2 → ℕ → Tree
  Unary : Fin 2 → Tree → Tree
  Binary : Fin 3 → Tree → Tree → Tree

invNullaryNat1 : ∀ {op1 op2 n1 n2} → NullaryNat op1 n1 ≡ NullaryNat op2 n2 → op1 ≡ op2
invNullaryNat1 refl = refl

invNullaryNat2 : ∀ {op1 op2 n1 n2} → NullaryNat op1 n1 ≡ NullaryNat op2 n2 → n1 ≡ n2
invNullaryNat2 refl = refl

invUnary1 : ∀ {op1 op2 t1 t2} → Unary op1 t1 ≡ Unary op2 t2 → op1 ≡ op2
invUnary1 refl = refl

invUnary2 : ∀ {op1 op2 t1 t2} → Unary op1 t1 ≡ Unary op2 t2 → t1 ≡ t2
invUnary2 refl = refl

invBinary1 : ∀ {op1 op2 l1 l2 r1 r2} → Binary op1 l1 r1 ≡ Binary op2 l2 r2 → op1 ≡ op2
invBinary1 refl = refl

invBinary2 : ∀ {op1 op2 l1 l2 r1 r2} → Binary op1 l1 r1 ≡ Binary op2 l2 r2 → l1 ≡ l2
invBinary2 refl = refl

invBinary3 : ∀ {op1 op2 l1 l2 r1 r2} → Binary op1 l1 r1 ≡ Binary op2 l2 r2 → r1 ≡ r2
invBinary3 refl = refl

_≟_tree : Decidable {A = Tree} _≡_
Nullary               ≟ Nullary               tree = yes refl  
Nullary               ≟ (NullaryNat op n)     tree = no (λ())
Nullary               ≟ (Unary op t)          tree = no (λ())
Nullary               ≟ (Binary op l r)       tree = no (λ())
(NullaryNat op n)     ≟ Nullary               tree = no (λ ())
(NullaryNat op1 n1)   ≟ (NullaryNat op2 n2)   tree with op1 ≟ op2 fin
(NullaryNat .op1 n1)  ≟ (NullaryNat op1 n2)   tree | yes refl with n1 ≟ n2
(NullaryNat .op1 .n1) ≟ (NullaryNat op1 n1)   tree | yes refl | yes refl = yes refl
(NullaryNat .op1 n1)  ≟ (NullaryNat op1 n2)   tree | yes refl | no p = no (p ∘ invNullaryNat2)
(NullaryNat op1 n1)   ≟ (NullaryNat op2 n2)   tree | no p  = no (p ∘ invNullaryNat1) 
(NullaryNat op1 n1)   ≟ (Unary op t)          tree = no (λ())
(NullaryNat op1 n1)   ≟ (Binary op l r)       tree = no (λ())
(Unary op1 t1)        ≟ Nullary               tree = no (λ())
(Unary op1 t1)        ≟ (NullaryNat op n)     tree = no (λ())
(Unary op1 t1)        ≟ (Unary op2 t2)        tree with op1 ≟ op2 fin
(Unary .op1 t1)       ≟ (Unary op1 t2)        tree | yes refl with t1 ≟ t2 tree
(Unary .op1 .t1)      ≟ (Unary op1 t1)        tree | yes refl | yes refl = yes refl
(Unary .op1 t1)       ≟ (Unary op1 t2)        tree | yes refl | no p = no (p ∘ invUnary2) 
(Unary op1 t1)        ≟ (Unary op2 t2)        tree | no p = no (p ∘ invUnary1) 
(Unary op1 t1)        ≟ (Binary op2 l r)      tree = no (λ())
(Binary op l r)       ≟ Nullary               tree = no (λ())
(Binary op1 l r)      ≟ (NullaryNat op2 n)    tree = no (λ())
(Binary op1 l r)      ≟ (Unary op2 t)         tree = no (λ())
(Binary op1 l1 r1)    ≟ (Binary op2 l2 r2)    tree with op1 ≟ op2 fin
(Binary .op1 l1 r1)   ≟ (Binary op1 l2 r2)    tree | yes refl with l1 ≟ l2 tree
(Binary .op1 .l1 r1)  ≟ (Binary op1 l1 r2)    tree | yes refl | yes refl with r1 ≟ r2 tree
(Binary .op1 .l1 .r1) ≟ (Binary op1 l1 r1)    tree | yes refl | yes refl | yes refl = yes refl
(Binary .op1 .l1 r1)  ≟ (Binary op1 l1 r2)    tree | yes refl | yes refl | no p = no (p ∘ invBinary3)
(Binary .op1 l1 r1)   ≟ (Binary op1 l2 r2)    tree | yes refl | no p = no (p ∘ invBinary2)
(Binary op1 l1 r1)    ≟ (Binary op2 l2 r2)    tree | no p = no (p ∘ invBinary1)

{- 
Op codes 

Nullary
ι = 0
η = 1

Unary
μ = 0 
Π = 1

Binary
⇒ = 0
⊗ = 1
⊕ = 2
-} 

jni : Tree → Ty 
jni Nullary                              = ① 
jni (NullaryNat fzero n)                 = ι n
jni (NullaryNat (fsuc fzero) n)          = η n
jni (NullaryNat (fsuc (fsuc ())) n)   
jni (Unary fzero t)                      = μ (jni t)
jni (Unary (fsuc fzero) t)               = Π (jni t)
jni (Unary (fsuc (fsuc ())) t)
jni (Binary fzero l r)                   = (jni l) ⇒ (jni r)
jni (Binary (fsuc fzero) l r)            = (jni l) ⊗ (jni r)
jni (Binary (fsuc (fsuc fzero)) l r)     = (jni l) ⊕ (jni r)
jni (Binary (fsuc (fsuc (fsuc ()))) l r) 

injEx : (x : Ty) -> Σ[ t ∶ Tree ] jni t ≡ x
injEx ①                         = Nullary , refl 
injEx (ι n)                     = NullaryNat fzero n , refl
injEx (η n)                     = NullaryNat (fsuc fzero) n , refl
injEx (μ t)                     with injEx t
injEx (μ .(jni tree))           | tree , refl = (Unary fzero tree) , refl
injEx (Π t)                     with injEx t
injEx (Π .(jni tree))           | tree , refl = (Unary (fsuc fzero) tree) , refl
injEx (t ⇒ s)                   with injEx t
injEx (.(jni tr1) ⇒ s)          | tr1 , refl with injEx s
injEx (.(jni tr1) ⇒ .(jni tr2)) | tr1 , refl | tr2 , refl = (Binary fzero tr1 tr2) , refl 
injEx (t ⊗ s)                   with injEx t
injEx (.(jni tr1) ⊗ s)          | tr1 , refl with injEx s
injEx (.(jni tr1) ⊗ .(jni tr2)) | tr1 , refl | tr2 , refl = (Binary (fsuc fzero) tr1 tr2) , refl 
injEx (t ⊕ s)                   with injEx t
injEx (.(jni tr1) ⊕ s)          | tr1 , refl with injEx s
injEx (.(jni tr1) ⊕ .(jni tr2)) | tr1 , refl | tr2 , refl = (Binary (fsuc (fsuc fzero)) tr1 tr2) , refl 

inj : Ty → Tree
inj = proj₁ ∘ injEx -- strip off the existential proof

injeq : ∀ {x y} -> inj x ≡ inj y -> x ≡ y
injeq {x} {y} p = trans (sym (proj₂ (injEx _))) (trans (cong jni p) (proj₂ (injEx _)))

_≟_ty : (x y : Ty) -> Dec (x ≡ y)
x ≟ y ty with (inj x) ≟ (inj y) tree
x ≟ y ty | yes p = yes (injeq p)
x ≟ y ty | no p = no (p ∘ (cong inj))
