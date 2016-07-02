
Inductive Ty : Set 
| Ind : 
| CoInd : .

Inductive Ctx : Set
| empty : Ctx 
| next : forall x : Var, t : Ty -> Ctx -> Ctx.

Inductive Sequent : Set
| turnstile Ctx Term Ty.

Syntax "G |- t : T" := Sequent G t T. 


Inductive Derivation : Seq -> Prop 
| and : Derivation (G |- t : T) -> Derivation (F |- s : S) -> 
  Derivation (G ++ F |- (Pair s t) : T
| rep : Rational 
.