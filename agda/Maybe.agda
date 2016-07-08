module Maybe where 

  data Maybe (A : Set) : Set where 
    nothing : Maybe A
    just : A → Maybe A 

  maybe : {A B : Set} → B → (A → B) → Maybe A → B
  maybe z f nothing = z 
  maybe z f (just a) = f a

  return : {A : Set} → A → Maybe A 
  return x = just x 

  infixr 40 _>>=_
  _>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing  >>= _ = nothing
  (just x) >>= f = f x

  data _==_ {A : Set}(x : A) : A → Set where 
    refl : x == x

  first_law : {A B : Set} (a : A) (f : A → Maybe B) → (return a >>= f) == f a
  first_law a f = refl

  second_law : {A B : Set} (m : Maybe A) → (m >>= return) == m 
  second_law nothing  = refl
  second_law (just x) = refl

  third_law : {A B C : Set} (m : Maybe A) 
                 (f : A → Maybe B) (g : B → Maybe C) → 
                   ((m >>= f) >>= g) == (m >>= (λ x → f x >>= g))
  third_law nothing  f g = refl 
  third_law (just a) f g = refl

{-
   1.  "Left identity":  return a >>= f  ≡  f a
   2. "Right identity": m >>= return  ≡  m
   3. "Associativity": (m >>= f) >>= g  ≡  m >>= (\x -> f x >>= g) 
-}