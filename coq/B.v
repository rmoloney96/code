(* Attempt to do examples from the SEwB book *) 

Require Import List.

Section Resources. 
  
  Variable Elt : Set.
  Definition Res := list Elt.
 
  Variable eq_dec : forall (x y : Elt), {x = y} + {x <> y}.
  
  Definition free : 
    forall (x:Elt) (rfree : Res),
      ~ In x rfree -> 
      {rfree' : Res | In x rfree' /\ forall (y:Elt), x <> y -> In y rfree -> In y rfree'}.
  Proof. 
    refine 
      (fun (x : Elt) (rfree: Res) (p : ~In x rfree) => 
	exist _ (x::rfree) _). firstorder.
  Defined.
      
  Fixpoint remove (a : Elt) (r : Res) {struct r} : Res := 
    match r with 
      | nil => nil 
      | h::t => 
	match eq_dec a h with 
	  | left _ => remove a t
	  | right _ =>  h::(remove a t)
	end  
    end.

  Lemma remove_correct : forall (x : Elt) (r : Res), 
    ~ In x (remove x r).
  Proof. 
    simple induction r. firstorder.
    intros. simpl. case (eq_dec x a). firstorder.
    firstorder.
  Defined.

  Hint Resolve remove_correct.

  Ltac case_eq_dec := 
    match goal with 
      | [ _ : _ |- context[eq_dec ?x ?y] ] => 
        case (eq_dec x y) ; firstorder ; try subst ; intros ; try congruence
    end.

  Hint Extern 1 (In _ _) => case_eq_dec.

  Lemma remove_inv_neq : forall (x y : Elt) (r : Res), 
    x <> y -> In y r -> In y (remove x r).
  Proof. 
    simple induction r ; simpl ; eauto. 
  Defined.
 
  Hint Resolve remove_inv_neq.

  Definition alloc : 
    forall (x:Elt) (rfree : Res), 
      In x rfree -> 
      {rfree' : Res | ~In x rfree' /\ forall (y:Elt), x <> y -> In y rfree -> In y rfree'}. 
  Proof. 
    refine 
      (fun (x : Elt) (rfree: Res) (p : In x rfree) => 
	exist _ (remove x rfree) _). firstorder.
  Defined.       

End Resources.

Require Import Coq.Sets.Constructive_sets.

Section Res_Prop.

  Variable Elt : Set.
  Variable eq_dec : forall (x y : Elt), {x = y} + {x <> y}.

  Definition ResSet := Ensemble Elt.

  (* Implicit Arguments In [U]. *)

  Definition freeRes : 
    forall (x:Elt) (rfree : ResSet),
      ~ In Elt rfree x -> sigT  
      (fun (rfree' : ResSet) => 
	In Elt rfree' x /\ forall (y:Elt), x <> y -> In Elt rfree y -> In Elt rfree' y).
  Proof. 
    firstorder. refine (existT _ (Add Elt rfree x) _). firstorder.
  Defined.
  
  Definition allocRes : 
    forall (x:Elt) (rfree : ResSet),
      In Elt rfree x -> sigT  
      (fun (rfree' : ResSet) => 
	~ In Elt rfree' x /\ forall (y:Elt), x <> y -> In Elt rfree y -> In Elt rfree' y).
  Proof. 
    firstorder. refine (existT _ (Subtract Elt rfree x) _). firstorder.
  Defined.
  
End Res_Prop.

Section.

End.