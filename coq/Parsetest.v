
(* We are going to work with just numbers for parsing, and not content carriers *)

Inductive Status : Type := progress | stasis.

Definition status_dec : forall (s s':Status), {s = s'} + {s <> s'}.
Proof. 
  decide equality.
Defined. 

Definition ands s s' := 
  match s with 
    | progress => s'
    | stasis => stasis
  end.

Definition ors s s' := 
  match s with 
    | progress => progress 
    | stasis => s'
  end.

Inductive Parse (n' : nat) : Prop := 
| parse : Parse n'.


(* we can down-convert progress to stasis. *)
Require Import Arith.

Definition Parser (A:Type) (s:Status) := forall n, option (A * {n' : nat | Parse n' n s}).

Definition eat : Parser nat progress. 
Proof. unfold Parser.
  refine 
    (fun (n : nat) => 
      match n return option (nat * { n' : nat | Parse n' n progress}) with 
        | 0 => None
        | S n' => Some (n',(exist _ n' (parse_progress _ _ _)))
      end). auto.
Defined.

Definition alt : forall `A s s'`, Parser A s -> Parser A s' -> Parser A (ands s s').
Proof.
  intros A s s' ph1 ph2. unfold Parser.
  refine 
    (fun n => 
      (match ph1 n return option (A*{n' : nat | Parse n' n (ands s s')}) with 
         | None => match ph2 n return option (A*{n' : nat | Parse n' n (ands s s')}) with
                     | None => None
                     | Some (a,(exist n' Hn)) => Some (a,(exist _ n' _))
                 end
         | Some (a,(exist n' Hn)) => Some (a,(exist _ n' _))
       end)) ; destruct s ; destruct s' ; simpl in * ; auto ; try (apply progress_imp_stasis) ; auto.
Defined.
Infix "|+|" := alt (at level 60). 

Definition seq : forall `A B s s'`, Parser A s -> Parser B s' -> Parser (A*B) (ors s s').
  intros A B s s' ph1 ph2. unfold Parser. 
  refine 
    (fun (n:nat) => 
      match ph1 n return option (A * B * {n' : nat | Parse n' n (ors s s')}) with 
        | None => None 
        | Some (a,(exist n2 Hn2)) =>
          match ph2 n2 return option (A * B *{n' : nat | Parse n' n (ors s s')}) with 
            | None => None
            | Some (b,(exist n3 Hn3)) => Some ((a,b),(exist _ n3 _))
          end
      end) ; destruct s ; destruct s' ; simpl in * ; auto ; inversion Hn3 ; inversion Hn2.
    apply parse_progress. apply (lt_trans n3 n2). auto. auto. 
    apply parse_progress. eapply le_lt_trans. eauto. eauto. 
    apply parse_progress. eapply lt_le_trans. eauto. eauto.
    apply parse_stasis. eapply le_trans. eauto. eauto. 
    (* the fast proof, slow code method 
       try (apply parse_progress ; omega) ; try (apply parse_stasis ; omega). *)
Defined.
Infix "|&|" := seq (at level 55).

Print seq.

Definition appl : forall `A B s`, Parser A s -> forall (f:A -> B), Parser B s.
Proof.
  intros A B s ph f. unfold Parser. 
  refine 
    (fun (n:nat) => 
      match ph n with 
        | None => None 
        | Some (a,(exist n2 Hn2)) => Some (f a,(exist _ n2 Hn2))
      end).
Defined. 
Infix "|>|" := appl (at level 55).       

Eval compute in (eat |&| eat |>| (fun p => match p with (a,b) => (a+b) end)) 3.

Fixpoint ParseR (A:Type) (n1 n2:nat) (a:option (A*{n':nat | Parse n' n1 progress})) (b:option (A*{n'':nat | Parse n'' n2 progress})) : Prop := 
  match b with 
    | None => False 
    | Some (_,exist n'' Hn'') => 
      match a with 
        | None => True
        | Some (_,exist n' Hn') => n' < n''
      end
  end.

Variable A : Type. 
Variable n1 :nat.
Variable n2 :nat. 
Check (ParseR A n1 n2). 
Lemma ParseR_Acc : forall a, Acc (ParseR A n1 n2) a.

Require Import Recdef.
Function triangle (n : nat) {wf lt n} : option (nat*{n':nat | Parse n' n progress}) := 
  ((eat |&| triangle |>| (fun p => match p with (a,b) => (a+b) end)) 
    |+| eat) n.
