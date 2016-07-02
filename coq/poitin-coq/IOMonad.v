Require Import Monad.
Require Import String.
Require Import Ascii.

Inductive IO (A:Type) : Type := 
| get_char : (ascii -> IO A) -> IO A
| put_char : ascii -> IO A -> IO A
| ret_char : A -> IO A.

Definition getChar : IO ascii := 
  get_char _ (ret_char _).

Definition putChar (c : ascii) : IO True := 
  put_char _ c (ret_char _ I).

Fixpoint bindChar (A B : Type) (i : IO A) (f : A -> IO B) : IO B := 
  match i with 
    | ret_char a => (f a) 
    | get_char g => get_char _ (fun c => (bindChar _ _ (g c) f))
    | put_char c a => put_char _ c (bindChar _ _ a f)
  end. 

Definition echo := bindChar _ _ getChar (fun c => putChar c).

Fixpoint print_str (s:string) : IO True := 
  match s with 
    | EmptyString => ret_char _ I
    | String c s' => bindChar _ _ (putChar c) (fun _ => print_str s')
  end.
  
(* Axiom eta : forall (A B : Type) (f : A -> B), (fun (x : A) => f x) = f. *)
Axiom leibniz : forall (A B: Type) (f g : A -> B), (forall x : A, f x = g x) -> f = g.
Lemma eta : forall (A B : Type) (f : A -> B), (fun (x : A) => f x) = f.
Proof.
  intros. apply leibniz. intros. auto.
Defined.

Lemma bind_char_assoc :
  forall (A B C : Type) f g x, 
    bindChar A C x (fun a : A => bindChar B C (f a) g) = bindChar B C (bindChar A B x f) g.
Proof.
  induction x. 
  (* get_char *)
  unfold bindChar. fold bindChar.  
  cut ((fun c : ascii => bindChar A C (i c) (fun a : A => bindChar B C (f a) g)) =
    (fun c : ascii => bindChar B C (bindChar A B (i c) f) g)). intros HR. rewrite HR. auto.
  apply leibniz. auto.
  (* put_char *)
  unfold bindChar. fold bindChar.
  cut ((bindChar A C x (fun a0 : A => bindChar B C (f a0) g)) = (bindChar B C (bindChar A B x f) g)).
  intro HR. rewrite HR. auto. auto.
  (* ret_char *)
  unfold bindChar. fold bindChar. auto.
Defined.

Print bind_char_assoc.

Program Instance Monad IO := 
  unit A := ret_char A;
  bind A B := bindChar A B.

  Next Obligation. (* bind left unit *)
  Proof.
    induction x. 
    (* get_char *)
    unfold bindChar. fold bindChar. 
    cut ((fun c : ascii => bindChar A A (i c) (ret_char A)) = i).
    intros H0. rewrite H0. auto. apply leibniz. auto.
    (* put_char *)
    unfold bindChar. fold bindChar. rewrite IHx. auto.
    (* ret_char *)
    unfold bindChar. auto.
  Qed.

  Next Obligation. (* bind right unit *) 
  Proof. 
    apply bind_char_assoc.
  Qed.
