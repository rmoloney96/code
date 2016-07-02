
Inductive LengthMeasure : string -> string -> Prop := 
| length_smaller : forall s1 s2, length s1 < length s2 -> LengthMeasure s1 s2. 

Require Import Coq.Arith.Wf_nat.

Check well_founded (ltof string length).

Theorem string_length_well_founded : 
  well_founded (ltof string length).
Proof. 
  eapply well_founded_ltof.
Defined.

Require Import Le.

(* recursion with strong specification *) 
Definition tail_n_strong (n:nat) (s:string) : {s' | length s' <= length s}.
Proof.
  refine 
    (fix f (n:nat) (s:string) {struct n} : {s' : string | length s' <= length s} := 
      match n with 
        | 0 => exist (fun s' : string => length s' <= length s) s (le_n (length s))
        | S n' => match s return {s' : string | length s' <= length s} with 
                    | EmptyString => exist _ "" _
                    | String a b => match (f n' b) return {s' : string | length s' <= length (String a b)}  with 
                                      | exist s'' p => exist _ s'' _
                                    end                                      
                  end
      end) ; simpl ; auto with arith.
Defined.
    
Definition shrink_strong (s:string) : {s' | length s' <= length s}.
Proof.
  refine 
    (fix f (s:string) : {s' | length s' <= length s} := 
      match s return {s' | length s' <= length s} with 
        | EmptyString => exist _ EmptyString _
        | String a b => match (tail_n_strong 3 b) return {s' | length s' <= length (String a b)} with 
                          | exist s'' p => exist _ s'' _
                        end
      end) ; simpl ; auto with arith.
Defined.

Fixpoint tail_n (n:nat) (s:string) :string := 
  match n with 
    | 0 => s
    | S n' => match s with 
                | EmptyString => EmptyString
                | String a b => tail_n n' b
              end
  end.

Require List.

Definition R := ltof string length.
Theorem wf_R : well_founded R.
  apply (well_founded_ltof string length).
Defined.

(* with fixpoint *)
Definition shrink_F (f:string -> List.list string) (s:string) : List.list string := 
  match s with 
    | EmptyString => List.nil
    | String a b => match (tail_n_strong 3 b) with 
                      | exist s'' p => List.cons s (f s'')
                    end
  end.

Fixpoint iter (A:Set) (n:nat) (F:A->A)(g:A){struct n} : A :=
  match n with 
    | 0 => g 
    | S p => F (iter A p F g) 
  end.

Require Import Arith.
Definition shrink_terminates : 
  forall s, R "" s ->
    {sl : List.list string | 
      exists p:nat, (forall k:nat, p < k -> forall (g:string->List.list string), 
        iter (string->List.list string) k shrink_F g s = sl)}.
Proof.
  intros. elim s using (well_founded_induction wf_R). 
  intros x Hrec. unfold R in *. unfold ltof in *. 
  case_eq (lt_eq_lt_dec (length s) (length x)).
  intros. 
  inversion s0. 
Defined.

(*
Definition strong_splitl : forall s f c, {s1 : string & { s2 : string | f c = true -> splitl f (String c s) = (s1,s2) -> length s2 < length s}}.
*)