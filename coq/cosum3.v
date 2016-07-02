CoInductive CoNat : Set := 
| Zero : CoNat
| Succ : CoNat -> CoNat.

CoFixpoint plus (x: CoNat) (y: CoNat) : CoNat := 
  match x with 
    | Zero => y 
    | Succ x' => Succ (plus x' y)
  end.

CoInductive CoList : Set := 
| CoNil : CoList 
| CoCons : CoNat -> CoList -> CoList.

CoFixpoint sumlen (xs : CoList) : CoNat := 
  match xs with
    | CoNil => Zero
    | CoCons x' xs' => Succ (f x' xs')
  end
with f (n : CoNat) (xs : CoList) : CoNat :=
  match n with 
    | Zero => sumlen xs
    | Succ x' => Succ (f x' xs)
  end.

  sumlen [] = Zero 
  sumlen (n:xs) = Succ(f xs)
  f Zero xs = sumlen xs
  f (Succ x) xs = Succ(f x xs)

