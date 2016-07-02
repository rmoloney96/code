
Fixpoint plus (x : nat) (y : nat) {struct x} : nat := 
  match x with 
    | 0 => y 
    | S x' => plus x' (S y)
  end.

Fixpoint equal (x : nat) (y : nat) {struct x} : Prop := 
  match x with 
    | 0 => 
      match y with 
        | 0 => True 
        | S y' => False
      end 
    | S x' =>
      match y with 
        | 0 => False 
        | S y' => equal x' y'
      end
    end. 

(* distilled from conjecture: forall x y, equal (plus x y) (plus y x). *) 
Definition conj (x : nat) (y : nat) : Prop := 
  let f1 := 
    (fix r (x : nat) (y : nat) {struct x} : Prop := 
      match x with 
        | 0 => 
          (let f2 := 
            (fix r (y : nat) : Prop := 
              match y with 
                | 0 => True
                | S y' => r y'
              end) 
            in f2 y)
        | S x' => 
          match y with 
            | 0 => 
              (let f3 := 
                (fix r (x : nat) : Prop := 
                  match x with 
                    | 0 => True 
                    | S x' => r x'
                  end) 
                in f3 x')
            | S y' => r x' y'
          end 
      end) 
    in f1 x y.

Ltac case_eq x := generalize (refl_equal x); pattern x at -1; case x.


Lemma conj_zero : forall x, conj x 0 -> conj (S x) 0.
Proof.
  induction x. auto. simpl. simpl in IHx. intros. apply H.
Defined.  
  

Theorem conj_correct : forall x y, conj x y.
Proof.
  induction x ; induction y. firstorder. firstorder. 
  apply conj_zero. auto. firstorder.
Defined. 

Theorem loop_correct : forall x, (fix r (x:nat) : Prop := match x with | 0 => True | S x' => r x' end) x.
Proof.
  induction x. auto. auto.
Defined.   

Theorem conj_correct2 : forall x y, conj x y.
Proof.
  induction x ; induction y. firstorder. firstorder.
  simpl. cut (  True -> (fix r (x0 : nat) : Prop := match x0 with
                               | 0 => True
                               | S x' => r x'
                               end) x). 
  intros. apply H. auto. intros. clear. induction x. auto. auto. 
  firstorder. 
Defined. 


Theorem conj_correct3 : forall x y, conj x y.
Proof.
  induction x ; induction y. firstorder. firstorder.
  simpl. apply loop_correct. firstorder.  
Defined. 




Theorem plus_Z_x : forall x, equal (plus 0 x) x.
Proof. 
  intros. induction x. firstorder. simpl. simpl in IHx. auto.
Defined.   

Theorem plus_comm : forall x y, equal (plus x y) (plus y x).
  intros. 

Fixpoint plus_l (x : nat) (y : nat) {struct x} : nat := 
  match x with 
    | 0 => y 
    | S x' => plus_l x' (S y)
  end.

Fixpoint plus_r (x : nat) (y : nat) {struct y} : nat := 
  match y with 
    | 0 => x 
    | S y' => plus_r (S x) y'
  end.

Theorem r_equal_l : forall (x : nat) (y : nat), equal (plus_l x y) (plus_r x y).
Proof.
  induction x. induction y. firstorder. 
  Focus 2. intros. simpl. unfold plus_r.  

inversion (plus_r x (S y)). 
  intros. unfold plus_l. unfold plus_r.  

      
