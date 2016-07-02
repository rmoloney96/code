Section program.

  Variable instr: Set -> Type.
  
  CoInductive program : Set -> Type :=
    | Then : forall A B:Set, instr A -> (A -> program B) -> program B
    | Return : forall A:Set, A -> program A.

  Implicit Arguments Then [A B].
  Implicit Arguments Return [A].

  CoFixpoint bind (A:Set) (B:Set) (m : program A) : (A -> program B) -> program B :=
    match m with
      | Return A a   => fun (g : A -> program B) => g a
      | Then C D i f =>
        fun (g : D -> program B) =>
          Then i (fun (c:C) => bind D _ (f c) g)
    end.


izero = \ x . { True | False } x 

not = \ x . { False | True } x 

\y. not (iszero y)

not (izero x) 

{False | True} ({ True | False } x)


  CoFixpoint bind (A : Set) (B:Set) (m : program A) :=
    match m in (program A) return ((A -> program B) -> program B) with
      | Return A0 a   => fun (g : A0 -> program B) => g a 
      | Then C D i f => fun (g : D -> program B) => Then i (fun (c:C) => bind D B (f c) g)          
    end.

End program.

 Definition bind : forall (A:Set) (B:Set) (m : program A), (A -> program B) -> program B.
  Proof. 
    refine
      (cofix bind (A:Set) (B:Set) (m : program A) : ((A -> program B) -> program B) := 
        match m in (program A) return ((A -> program B) -> program B) with
          | Return _ a   => _ (* fun (g : A -> program B) => g a *) 
          | Then C D i f => 
            fun (g : D -> program B) =>
              Then i (fun (c:C) => bind D _ (f c) g)

        end).
    intro g. apply g in a. exact a.
  Defined.

  Print bind.


End program.