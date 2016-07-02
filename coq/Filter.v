
Require Import Streams.

Fixpoint le (x : nat) (y : nat) {struct x} : bool := 
  match x with 
    | O => true
    | S x' => match y with 
                | O => false 
                | S y' => le x' y' 
              end
  end.

Definition pred (x : nat) : nat := 
  match x with 
    | O => O 
    | S x' => x' 
  end.

(* Not admissible 

CoFixpoint f (xs : Stream nat) : Stream nat :=
  match xs with 
    | Cons x xs' => 
      match xs' with 
        | Cons y xs'' => 
          if le x y 
            then Cons x (f (Cons y xs''))
            else f (Cons (pred x) (Cons y xs''))
      end
  end.
      
*)

(* 

**** In hosc: ****

data Nat = Z | S Nat; 
data Stream = Cons Nat Stream;
data Bool = True | False;

prod xs where
 
le = \ x y -> case x of {
               Z -> True;
               S x1 -> (case y of {
                             Z -> False;
		             S y1 -> le x1 y1;  
                       });
              };

pred = \ x -> case x of {
               Z -> Z; 
	       S x1 -> x1;
              };
 
prod = \ xs -> 
     case xs of {
       Cons x xs1 -> 
       case xs1 of {
         Cons y xs2 -> 
	  case le x y of {
	    True -> Cons x (prod (Cons y xs2));
	    False -> prod (Cons (pred x) (Cons y xs2));
          };
       };
     };

**** In poitin: ****

prod xs
with 
where 
le = % x y . case x of 
              | Zero => True 
              | Succ(x') => case y of 
                             | Zero => False 
		             | Succ(y') => le x' y';  
pred = % x . case x of 
               | Zero => Zero 
	       | Succ(x') => x'; 
prod = % xs . 
     case xs of 
       | Cons(x,xs') => 
       case xs' of 
        | Cons(y,xs'') => 
	  case le x y of 
	    | True => Cons(x,(prod (Cons(y,xs''))))
	    | False => prod (Cons(pred x,Cons(y,xs''))); 

*)

(* After Supercompilation

(case xs of 
 | Cons(x,xs') => (case xs' of 
                  | Cons(y,xs'') => (case x of 
                                    | Succ(x') => (case y of 
                                                  | Zero => ((f' x') xs'')
                                                  | Succ(y') => (case ((le x') y') of 
                                                                | False => (((f x') y') xs'')
                                                                | True => Cons(Succ(x'),(prod Cons(Succ(y'),xs'')))))
                                    | Zero => Cons(Zero,(prod Cons(y,xs''))))))

with

datatype nat = Zero | Succ of nat;
datatype 'a list = Nil | Cons of 'a * 'a list;
datatype bool = True | False ;
datatype ('a,'b) pair = Pair of 'a * 'b;

where

f' = (% x'. (% xs''. (case x' of 
                      | Succ(x') => ((f' x') xs'')
                      | Zero => Cons(Zero,(prod Cons(Zero,xs''))))));
f = (% x'. (% y'. (% xs''. (case x' of 
                            | Succ(x') => (case ((le x') y') of 
                                          | False => (((f x') y') xs'')
                                          | True => Cons(Succ(x'),(prod Cons(Succ(y'),xs''))))
                            | Zero => Cons(Zero,(prod Cons(Succ(y'),xs'')))))));
le = (% x. (% y. (case x of 
                      | Zero => True
                      | Succ(x') => (case y of 
                                    | Zero => False
                                    | Succ(y') => ((le x') y')))));
pred = (% x. (case x of 
                 | Zero => Zero
                 | Succ(x') => x'));
prod = (% xs. (case xs of 
                 | Cons(x,xs') => (case xs' of 
                                  | Cons(y,xs'') => (case ((le x) y) of 
                                                    | False => (prod Cons((pred x),Cons(y,xs'')))
                                                    | True => Cons(x,(prod Cons(y,xs'')))))));

*) 

CoFixpoint f (xs : Stream nat) : Stream nat :=
  match xs with 
    | Cons x xs' => 
      match xs' with 
        | Cons y xs'' => 
          match x with 
            | O => Cons O (f (Cons y xs''))
            | S x' => 
              match y with 
                | O => 
                  (fix g (x' : nat) (xs'' : Stream nat) {struct x'} := 
                    match x' with 
                      | O => Cons O (f (Cons O xs''))
                      | S x' => g x' xs''
                    end) x' xs''
                | S y' => 
                  if le x' y' 
                    then Cons (S x') (f (Cons (S y') xs''))
                    else 
                      (fix h (x' : nat) (y' : nat) (xs'' : Stream nat) {struct x'} := 
                        match x' with 
                          | O => Cons O (f (Cons (S y') xs''))
                          | S x' => 
                            if le x' y'
                              then Cons (S x') (f (Cons (S y') xs''))
                              else h x' y' xs''
                        end) x' y' xs''
              end
          end
      end
  end.

(* simplified *) 
CoFixpoint f (xs : Stream nat) : Stream nat :=
  match xs with 
    | Cons x xs' => 
      match xs' with 
        | Cons y xs'' => 
          match x with 
            | O => Cons O (f (Cons y xs''))
            | S x' => 
              match y with 
                | O => Cons O (f (Cons O xs''))
                | S y' => 
                  if le x' y' 
                    then Cons (S x') (f (Cons (S y') xs''))
                    else Cons 
                      ((fix h (x' : nat) (y' : nat) {struct x'} := 
                        match x' with 
                          | O => O 
                          | S x' => 
                            if le x' y'
                              then (S x')
                              else h x' y'
                        end) x' y') (f (Cons (S y') xs''))
              end
          end
      end
  end.
              


