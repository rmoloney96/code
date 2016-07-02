
Parameter type : Type.
Parameter Bool : type.
Parameter Arrow : type -> type -> type.

Inductive term (V : type -> Type) : type -> Type := 
| Var : forall (tau : type), (V tau) -> (term V) tau
| Tr : (term V) Bool
| Fa : (term V) Bool 
| App : forall (tau1 tau2 : type), (term V) (Arrow tau1 tau2) -> (term V) tau1 -> (term V) tau2
| Abs : forall (tau1 tau2 : type), (V tau1) -> term V tau2 -> term V (Arrow tau1 tau2).

Fixpoint even (n : nat) : Prop := 
  match n with 
    | O => True 
    | S n' => odd n' 
  end
with 
  odd (n : nat) : Prop := 
  match n with 
    | O => False 
    | S n' => even n'
  end.

Eval compute in (even 3).  
Eval compute in (odd 3). 

Fixpoint odd2 (n : nat) : bool := 
  match n with 
    | O => false
    | S n' => 
      (fun (f : nat -> bool) (m : nat) => 
        match m with 
          | O => true 
          | S m => f m
        end) odd2 n'
  end.

Fixpoint even2 (n : nat) : bool := 
  match n with 
    | O => true
    | S n' => 
      (fun (f : nat -> bool) (m : nat) => 
        match m with 
          | O => false
          | S m => f m
        end) even2 n'
  end.

Extraction even2.

Eval compute in (odd2 4). 

CoInductive T : Prop := 
| C : forall (A:Prop), A-> ~A ->T.

(* The type T is equivalent to (EX A | A & ~A), so it is empty *)
Lemma empty : ~T.
  unfold not ; intro H ; case H ; intros ; absurd A ; auto.  
Qed.

(* But there is a circular proof of T resulting from the quantification over T
in the constructor of T. *)
Inductive n : Set := 
| z : n 
| s : n -> n.

Extraction n_typ_ind.

CoFixpoint u : T := (C T u empty).

Parameter (A:Set) (P Q: (A -> Prop)). 
 
Lemma lm3 : (exists x, (forall R: A -> Prop, R x)) -> 2 = 3.
Proof.
  intro H.
