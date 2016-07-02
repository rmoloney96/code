
Inductive vector (A:Set) : nat -> Set := 
| vnil : vector A 0 
| vcons : forall n, A -> vector A n -> vector A (S n).
Implicit Arguments vnil [A].
Implicit Arguments vcons [A n].

Definition vapp : forall `A n m`, vector A n -> vector A m -> vector A (n+m).
Proof.
  induction 1. 
  intros. simpl. auto.
  intros. simpl. eapply vcons. auto. apply IHvector. auto.
Defined.

Definition vapp' : forall `A n m`, vector A n -> vector A m -> vector A (n+m).
  refine 
    (fix vapp' (A:Set) (n m:nat) (v1 : vector A n) (v2 : vector A m) : vector A (n+m) := 
      (match v1 as v0 in (vector _ n0) return (n=n0 -> vector A (n+m)) with
         | vnil => _
         | vcons n' a v1' => _
       end) (refl_equal n)). intros.  subst. simpl. auto.
  intros. rewrite H. simpl. apply vcons. auto. 
  destruct n. inversion H. inversion H. rewrite <- H1. apply vapp' ; auto. rewrite H1. auto.
Defined.

Print vapp'. 

Print vapp.
Print vector_rec.

Notation "[]" := vnil.
Infix "::" := vcons (at level 55). 
Notation "[ x , .. , y ]" := (vcons x .. (vcons y vnil) ..) (at level 35).

Check [1, 2]. 

Eval compute in vapp ([1, 2, 3]) ([4, 5, 6]).
