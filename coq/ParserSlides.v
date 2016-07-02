
Inductive NT : nat -> Type := 
| expr : forall n, nat -> NT n
| term : forall n, nat -> NT n. 

Definition Parser (n:nat) tok (nt : NT n) (res:nat) := (res,
Definition Grammar (n:nat) tok (nt : NT n) := (fun nt res => Parser tok nt res).