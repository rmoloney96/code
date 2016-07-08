module tutorial where 

data Nat : Set where 
  zero : Nat 
  succ : Nat → Nat

pred : Nat → Nat 
pred zero = zero 
pred (succ x) = x {- by agsy -}

_+_ : Nat → Nat → Nat 
zero + m = m
(succ n) + m = succ (n + m)

_*_ : Nat → Nat → Nat 
zero * m = zero 
(succ n) * m = (n * m) + m

_-_ : Nat → Nat → Nat 
zero - m = zero 
n - zero = n
(succ n) - (succ m) = n - m

data Bool : Set where
  true : Bool 
  false : Bool

if_then_else_ : {C : Set} → Bool → C → C → C
if true then t else s = t
if false then t else s = s

natrec : {C : Set} → C → (Nat → C → C) → Nat → C
natrec p h zero = p 
natrec p h (succ n) = h n (natrec p h n)

plus : Nat → Nat → Nat 
plus x y = natrec y (λ x' r → succ r) x

mult : Nat → Nat → Nat 
mult x y = natrec zero (λ x' r → plus r y) y

zerop : Nat → Bool
zerop x = natrec true (λ _ _ → false) x

predT : Nat → Nat 
predT x = natrec zero (λ n r → n) x

sub : Nat → Nat → Nat 
sub x y = natrec x (λ n r → predT r) y

data List (A : Set) : Set where 
  [] : List A
  _::_ : A → List A → List A

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs 

listrec : {A B : Set} → (A → List A → B → B) → B → List A → B
listrec f b [] = b 
listrec f b (x :: xs) = f x xs (listrec f b xs)

foldr : {A B : Set} → (A → B → B) → B → List A → B 
foldr f b [] = b 
foldr f b (x :: xs) = f x (foldr f b xs)

foldl : {A B : Set} → (A → B → B) → B → List A → B
foldl f b [] = b
foldl f b (x :: xs) = foldl f (f x b) xs

filter : {A : Set} → (A → Bool) → List A → List A
filter f xs = foldr (λ x r → if (f x) then (x :: r) else r) [] xs

data _×_ (A B : Set) : Set where 
  <_,_> : A → B → A × B 

fst : {A B : Set} → A × B → A 
fst < a , b > = a 

snd : {A B : Set} → A × B → B 
snd < a , b > = b

hd : {A : Set} → List A → List A
hd xs = foldr (λ x r → x :: []) [] xs 

tl : {A : Set} → List A → List A 
tl xs = listrec (λ x xs r → xs) [] xs 

_++_ : {A : Set} → List A → List A → List A 
xs ++ ys = foldr (λ x r → x :: r) ys xs 

--hdmap : {A B C : Set} → (A → B → C) → List A → List B → List C 
--hdmap f xs ys = foldr (λ x r → foldr (λ y r → (f x y) :: []) [] (hd ys)) [] (hd xs)

reverse : {A : Set} → List A → List A
reverse xs = foldr (λ x r → r ++ (x :: [])) [] xs 

hdmap : {A C : Set} → (A → C) → List A → List C
hdmap f xs = foldr (λ x r → f x :: []) [] xs

zip : {A B : Set} → List A → List B → List (A × B)
zip xs ys = reverse (fst (listrec (λ x xs r → < (hdmap (λ y →  < x , y >) (snd r)) ++ (fst r), tl (snd r) >) (< [] , ys >) (reverse xs)))


data _∨_ (A B : Set) : Set where 
  inl : A → A ∨ B 
  inr : B → A ∨ B

case : {A B C : Set} → A ∨ B → (A → C) → (B → C) → C 
case (inl x) f g = f x
case (inr x) f g = g x

data True : Set where 
  One : True
 

data Vec (A : Set) : Nat → Set where 
  [] : Vec A zero 
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

one = succ zero
two = succ one
three = succ two
four = succ three 
five = succ four 
six = succ five 
seven = succ six 

_⋈_ : {n m : Nat} → {A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ⋈ v = v
(x :: xs) ⋈ v = x :: (xs ⋈ v)

zipv : {n : Nat} → {A B : Set} → Vec A n → Vec B n → Vec (A × B) n 
zipv [] [] = []
zipv (x :: xs) (y :: ys) = < x , y > :: (zipv xs ys)

head : {n : Nat} → {A : Set} → Vec A (succ n) → A 
head (x :: _) = x

tail : {n : Nat} → {A : Set} → Vec A (succ n) → Vec A n
tail (_ :: xs) = xs

mapv : {n : Nat} → {A B : Set} → (A → B) → Vec A n → Vec B n 
mapv f [] = []
mapv f (x :: xs) = (f x) :: (mapv f xs)

data Fin : Nat → Set where 
  fzero : { n : Nat } → Fin (succ n)
  fsucc : { n : Nat } → Fin n → Fin (succ n)

_!_ : {A : Set} → {n : Nat} → Vec A n → Fin n → A
[] ! ()
(x :: xs) ! fzero = x
(x :: xs) ! (fsucc f) = xs ! f

_!!_ : {A : Set} → {n : Nat} → Vec A (succ n) → Fin (succ n) → A
(x :: xs) !! fzero = x
(x :: (y :: xs)) !! (fsucc f) = (y :: xs) !! f 
(x :: []) !! (fsucc ())

data DBtree (A : Set) : Nat → Set where 
  dlf : A → DBtree A zero
  dnd : {n : Nat} → DBtree A n → DBtree A n → DBtree A (succ n)

data _==_ {A : Set} : A → A → Set where 
  refl : (x : A) → x == x

data UTLC : Nat → Set where 
  v : (n : Nat) → UTLC (succ n)
  wk : {n : Nat} → UTLC n → UTLC (succ n)
  lam : {n : Nat} → UTLC (succ n) → UTLC n 
  app : {n : Nat} → UTLC n → UTLC n → UTLC n

ic : UTLC zero
ic = lam (v zero)

kc : UTLC zero 
kc = lam (lam (v one))

sc : UTLC zero 
sc = lam (lam (lam (app (app (v two) (wk (wk (v zero)))) (wk (app (v one) (wk (v zero)))))))

data Ty : Set where 
  B : Ty 
  N  : Ty 
  _⇒_ : Ty → Ty → Ty 

data TLC : Ty → Set where 
  z : TLC N
  s : TLC (N ⇒ N)
  natr : {c : Ty} → TLC ((N ⇒ (c ⇒ c))) → TLC c → TLC N → TLC c
  t : TLC B 
  f : TLC B
  if : {c : Ty} → TLC B → TLC c → TLC c → TLC c
  v : Nat → (a : Ty) → TLC a
  lamt : {b : Ty} → (a : Ty) → TLC b → TLC (a ⇒ b)
  appt : {a b : Ty} → TLC (a ⇒ b) → TLC a → TLC b
  

term = natr (lamt N (lamt B f)) t z 
--term = (app (app (natr (lamt N (lamt B f))) t) z)

zipvec : {A B : Set} → (n : Nat) → Vec A n → Vec B n → Vec (A × B) n 
zipvec zero [] [] = []
zipvec (succ n) (_::_ .{n} x xs) (_::_ .{n} y  ys) = < x , y > :: (zipvec n xs ys)

data Image {A B : Set} (f : A → B) : B → Set where 
  im : (x : A) → Image f (f x)

inv : {A B : Set} (g : A → B) → (y : B) → Image g y → A 
inv g .(g x) (im x) = x