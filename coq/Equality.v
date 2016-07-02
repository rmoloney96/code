

(* 
Theorem ex_ip_ex : forall (A:Type)(a b:A), a=b -> b=a.
Proof.
  intros. rewrite H. auto.
Defined.
Print ex_ip_ex. 
*)  

Print eq_ind.

Theorem ex_ip_ex : forall (A:Type)(a b:A), a=b -> b=a.
Proof.
  refine 
    (fun (A:Type) (a b:A) (H:a=b) => 
      eq_ind_r (fun a':A => b = a') (refl_equal b) H).
Defined.

Require Import ZArith.
 
Theorem plus_permute2 : forall (n m p:nat), n+m+p = n+p+m.
Proof.
  intros. 
  pattern ((n+m)+p). rewrite <- plus_assoc. 
  pattern (m+p). rewrite plus_comm.
  pattern (n+(p+m)). rewrite plus_assoc.
  reflexivity.
Defined.
