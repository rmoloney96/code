Require Import Ascii. 
Require Import String.
Require Import Bool.

Fixpoint CharIn (c:ascii) (s:string) {struct s} : Prop :=
  match s with
    | EmptyString => False
    | String c' s' => c = c' \/ CharIn c s'
  end.

(* Facts about CharIn *) 
Theorem charin_eq : forall (a:ascii) (s:string), CharIn a (String a s).
Proof.
  simpl in |- *; auto.
Qed.

Theorem charin_cons : forall (a b:ascii) (s:string), CharIn b s -> CharIn b (String a s).
Proof.
  simpl in |- *; auto.
Qed.

Theorem charin_empty : forall (a:ascii), ~ CharIn a EmptyString.
Proof.
  unfold not in |- *; intros a H; inversion_clear H.
Qed.

Definition next (s:string) : string := 
  match s with 
    | EmptyString => EmptyString 
    | String c _ => String c EmptyString 
  end.

Open Scope string_scope.
Definition all_sat (f : ascii -> bool) (s : string) :=
  (s = "" \/ ~s = "" /\ forall c, CharIn c s -> f c = true).

Definition terminates (f : ascii -> bool) (s : string) : Prop := 
  match s with 
    | EmptyString => True 
    | String c s => match bool_dec (f c) true with 
                      | left Htrue => False
                      | right Hfalse => True
                    end
  end.

Hint Unfold all_sat terminates.

Ltac invert := 
  match goal with 
    | H : ?x /\ ?y |- _ => (inversion H ; clear H ; invert)
    | H : ?x \/ ?y |- _ => (inversion H ; clear H ; invert)
    | H :_ |- _ =>  idtac
  end.

Definition splitl : forall (f : ascii -> bool) (s:string), 
  { p : string * string | (fst p) ++ (snd p) = s /\ all_sat f (fst p) /\ terminates f (snd p)}. 
  refine   
    (fix splitl_f (f : ascii -> bool) (s:string) {struct s} : 
      { p : string * string | (fst p) ++ (snd p) = s /\ all_sat f (fst p) /\ terminates f (snd p)}
      := 
      match s 
        return { p : string * string | (fst p) ++ (snd p) = s /\ all_sat f (fst p) /\ terminates f (snd p)}
        with 
        | EmptyString => exist _ (EmptyString, EmptyString) _
        | String c s' => 
          match bool_dec (f c) true 
            return 
            { p : string * string | (fst p) ++ (snd p) = (String c s') /\ all_sat f (fst p) /\ terminates f (snd p)}
            with 
            | left Htrue => 
              match (splitl_f f s') with 
                | exist p H => exist _ (String c (fst p),(snd p)) _                            
              end
            | right Hfalse => exist _ (EmptyString, (String c s')) _
          end
      end). 
  split ; simpl ; auto. inversion H. inversion H1. simpl ; auto.   
  split ; invert ; subst ; simpl ; auto.
  split ; invert ; subst ; simpl ; auto. 
  unfold all_sat in H |- *. inversion H as [Hemp | Hnext].
  right. split. rewrite Hemp ; discriminate. intros c' Hin. simpl in Hin. inversion Hin as [Heq | Hfalse] ; subst ; auto. 
  rewrite Hemp in Hfalse. simpl in Hfalse. inversion Hfalse.
 
  right. split. discriminate. intros c' Hin. simpl in Hin. inversion Hin as [Heq | Hin'] ; subst ; auto.
  inversion Hnext as [Hnemp Hall]. apply Hall. auto.

  split ; simpl ; auto.
  split ; simpl ; auto.
  case_eq (f c) ; intros ; simpl ; auto.  
Defined. 

Lemma length_app : forall s1 s2, length (s1 ++ s2) = length s1 + length s2.
  induction s1. auto. intros. simpl.
  cut (length (s1++s2) = length s1+ length s2). intros. auto. auto.
Defined.  

Lemma app_length : forall s1 s2 s3, s1 ++ s2 = s3 -> length (s1 ++ s2) = length s3.
Proof.
  induction 1. reflexivity.
Defined. 

(* assuming splitl is correct, we can use this to spec other functions *) 
Definition splitl_spec (f : ascii -> bool) (s : string) := 
  match (splitl f s) with 
    | exist p _ => p
  end.

(* reduce the specification for splitl *) 
Definition splitl_r_le : forall (f : ascii -> bool) (s : string), { p : string * string | length (snd p) <= length s}. 
Proof.
  refine 
    (fun (f : ascii -> bool) (s : string) =>
      match (splitl f s) with 
        | exist p H => exist _ p _
      end). inversion H. rewrite <- H0. rewrite length_app. auto with arith.
Defined.

Require Import Omega.
Lemma splitl_one : forall (f: ascii -> bool) (c : ascii) (s:string), 
  f c = true -> {p' : string * string | length (snd p') < length (String c s)}.
Proof.
  refine 
    (fun (f : ascii -> bool) (c:ascii) (s : string) (Hf: f c = true) => 
      match (splitl f (String c s)) with 
        | exist p H => exist _ p _ 
      end).
  inversion H as [Happ [Hsat Hterm]].
  cut (fst p ++ snd p = String c s); auto; intros Happ'. 
  apply app_length in Happ. rewrite length_app in Happ. simpl in Happ.
  destruct (snd p) ; subst ; simpl ; auto with arith.
  simpl in Happ. destruct (fst p). simpl in Happ. 
  simpl in Happ'. inversion Happ'. subst. unfold terminates in Hterm.
  rewrite Hf in Hterm. simpl in Hterm. inversion Hterm.
  simpl in Happ. auto with arith. omega.  
Defined.

