
Require Import List.
Parameter A : Set.
Parameter B : Set.
Definition assoc_list := list (A * B)%type.
Parameter eq_dec : forall (x:A) (y:A),{x=y}+{x<>y}.

Definition spec (x:A) (l:list (A*B)) r :=
  match r with
    | Some y => In (x,y) l
    | None => forall y:B, ~In (x,y) l
  end.

Fixpoint assoc (x:A) (l:list (A*B)) {struct l}  : option B :=
  match l with
    | nil => None
    | ((x',y)::t) =>
      match eq_dec x x' with
	| left p => Some y
	| right p => assoc x t
      end
  end.

Lemma assoc' : forall (x:A) (l:list (A*B)), option B.
Proof.
  intros x l.
  induction l.
  apply None. 
  case_eq (eq_dec x (fst a)).
  intros. 
  apply (Some (snd a)).
  intros ; apply IHl.
Defined.

Extraction assoc'.    

(* prints out: 
assoc' = 
fun (x : A) (l : list (A * B)) =>
list_rec (fun _ : list (A * B) => option B) None
  (fun (a : A * B) (_ : list (A * B)) (IHl : option B) =>
   match eq_dec x (fst a) as s return (eq_dec x (fst a) = s -> option B) with
   | left e => fun _ : eq_dec x (fst a) = left (x <> fst a) e => Some (snd a)
   | right n => fun _ : eq_dec x (fst a) = right (x = fst a) n => IHl
   end (eq_refl (eq_dec x (fst a)))) l
     : A -> list (A * B) -> option B

(** val assoc' : a -> (a, b) prod list -> b option **)

let rec assoc' x = function
| Nil -> None
| Cons (y, l0) ->
  (match eq_dec x (fst y) with
   | Left -> Some (snd y)
   | Right -> assoc' x l0)

*)

(* 
And then solve the obligations with:

Solve Obligations using intros; clear H0; subst; try (destruct (assoc x t); compute in *; destruct x0); firstorder; congruence.

*) 