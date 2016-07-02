Variable n: nat.

Definition Less (n:nat) : Set := {i | i < n}.
Variable P : Less n -> bool.

Variable f : {i : Less n | P i = true}->nat.

Require Import Omega.
Lemma lm: forall i', S i' < n -> i' < n.
  intros; omega.
Qed.

Fixpoint sum (k:nat) : k < n -> nat :=
  match k return k < n -> nat with
    0 => fun h' : 0 < n =>
      let v0:Less n := exist (fun x => x < n) 0 h' in
        match P v0 as b return P v0 = b -> nat with
          true => fun h': P v0 = true =>       f (exist (fun i : Less n => P i = true) v0 h')
          | false => fun _ => 0
        end (refl_equal (P v0))
    | S k' => fun h: S k' < n =>
      let vk := exist (fun x => x < n) (S k') h in
        let vpred := sum k' (lm k' h) in
          match P vk as b return P vk = b -> nat with
            true => fun h' : P vk = true =>
              f (exist (fun i => P i = true) vk h') + vpred
            | false => fun _ => vpred
          end (refl_equal (P vk))
  end.

Program Fixpoint sum2 (k:nat) : k < n -> nat := 
  match k with 
    | 0 => (fun (H:k<n) => 0)
    | S k' => (fun (H:k<n) => k + (sum2 k' _))
  end.
  
 
      
