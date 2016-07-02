
Section Sort. 

  Variable A : Set.
  Variable lt : A -> A -> Prop. 
  Variable ge : A -> A -> Prop. 
  Variable dec : forall (a b : A), (lt a b) + (ge b a). 

  Inductive Maybe (A : Set) : Set :=
  | just : A -> Maybe A
  | nothing : Maybe A. 

  Inductive Vector (A : Set) : nat -> Set := 
  | vnil : Vector A 0 
  | vcons : forall n, A -> Vector A n -> Vector A (S n).

  Fixpoint nth {n} a i : Maybe A := 
    match a with 
      | vnil => nothing A
      | vcons A x tl => match i with 
                        | 0 => x 
                        | S i => nth tl i
                      end
    end.

  Definition repl : forall (n i : nat) (a : Vector A n) u, Vector A n := 
    (match a as a0 in Vector _ n' return (n = n') -> Vector A n with 
      | vnil => (fun p => _ )
      | vcons A x tl => (fun p => 
        match i with 
          | 0 => _
          | S i => _
        end)
     end) (refl_equal n).


  Fixpoint exchange a i j : {a' : Array A | a[i] == a[j] /\ a'[j] == a'[i]} :=
    match i with 
      | 0 => 
    match a with 
      | nil => nil 
      | x : 

Fixpoint Stooge_sort A i j := 
  

Stooge-Sort(A,i,j)
  if A[i] > A[j] 
  then exchange A[i] and A[j];
  if i+1 >= j
  then return;
  k = floor(j-i+1)/3);
  Stooge-Sort(A,i,j-k);
  Stooge-Sort(A,i+k,j);
  Stooge-Sort(A,i,j-k)


j+1-3k >= i

