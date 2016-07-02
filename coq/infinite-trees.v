
Inductive Tree 0 : Set :=
| Pair : Tree -> Tree -> Tree
| Next : Tree -> Tree
| Terminal : Tree.

Theorem comp : Tree -> Tree -> Tree. 
Proof.



f : A -> B     x : A     
--------------------
      f x : B



Gamma |- t : A   =>   t |= Theta[A]



map succ x |=_{x |= B} A        map succ nats |= B
---------------------------------------------------
        map succ (map succ nats) |= A



-------------------------------     -----------------
omega |=_{(fold omega) |= D}  D     (fold omega) |= D
-----------------------------------------------------
            omega (fold omega) |= D



