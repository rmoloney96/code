Require Import Monad.
Require Import String.

Inductive Exception : Type := 
| exception : string -> string -> Exception.

Inductive ExceptionM (A:Type) : Type := 
| exn : Exception -> ExceptionM A
| no_exn : A -> ExceptionM A.

Definition bind_exn (A : Type) (B : Type) (e : ExceptionM A) (f : A -> ExceptionM B) : ExceptionM B :=
  match e with
    | exn t => exn B t
    | no_exn a => (f a)
  end.

Definition unit_exn (A : Type) (a : A) := no_exn A a.

Program Instance Monad ExceptionM := 
  unit := unit_exn ;
  bind := bind_exn.

  Next Obligation. (* bind left unit *)
  Proof. 
    unfold bind_exn ; unfold unit_exn ; destruct x ; auto.
  Qed.

  Next Obligation. (* bind right unit *) 
  Proof. 
    unfold bind_exn ; unfold unit_exn ; destruct x ; auto.
  Qed.

Definition raise (A : Type) (t s:string) : ExceptionM A := exn A (exception t s).
Implicit Arguments raise [A]. 

Definition alt (A: Type) (e1 e2 : ExceptionM A) : ExceptionM A := 
  match e1 with 
    | exn t => match e2 with 
                 | exn t' => exn A t'
                 | no_exn a => no_exn A a 
               end
    | no_exn a => no_exn A a 
  end.
Notation "A |+| B" := (alt _ A B) (at level 55).

Definition handle (A:Type) (s:string) (e: ExceptionM A) (handler : string -> ExceptionM A) : ExceptionM A := 
  match e with 
    | exn t => match t with 
                 | exception name msg => 
                   match string_dec s name with 
                     | left _ => handler msg
                     | right _ => e
                   end
               end
    | _ => e
  end.

Notation "A |:| N , s => B" := (handle _ N A (fun s => B)) (at level 105).


(* Tests * 
 * ----- *)
(*
Check (raise (A:=nat) "test" "problem with zero").

Definition zero_exn := "zero_minus". 
Definition syntax_error := "syntax_error".
Definition P (n:nat) := 
  match n with 
    | 0 => raise zero_exn "problem with zero"
    | S n' => unit n'
  end.

Eval compute in P 0. 

Definition fail_test (n:nat) := 
  m <- (P n) ;; unit (m,"no prob")
  |:| zero_exn, msg => unit (n,msg)
  |:| syntax_error, msg => unit (0,msg).

Eval compute in fail_test 0.
Eval compute in P 1 |+| P 0.

*)