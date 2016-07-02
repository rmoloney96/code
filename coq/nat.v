
Require Import Arith.

Theorem bounded : forall n, exists m, n < m.
Proof.
  refine 
    (fix bounded (n : nat) : exists m, n < m := 
      match n as n0 return exists m, n0 < m  with
        | 0 => ex_intro (fun m : nat => 0 < m) 1 (lt_O_Sn 0)
        | S n1 => match (bounded n1) with 
                    | ex_intro m P =>  ex_intro (fun m0 : nat => S n1 < m0) (S m) (lt_n_S n1 m P)
                  end
      end).
Defined. 


  