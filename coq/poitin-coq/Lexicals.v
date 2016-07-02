Require Import String.
Require Import MyUtils.
Require Import Keywords.
Require Import List.
Require Import StringSets.
Require Char.

Module Type LEXICAL. 
  
  Record Position : Set := 
    mkPos
    {pos_lnum : nat;
      pos_cnum : nat}.
  
  Inductive Element : Set := 
  | Key : string -> Element 
  | Id : string -> Element
  | Con : string -> Element
  | Num : nat -> Element.

  Definition Token := (Element * Position)%type.
  
  Parameter showToken : Token -> string.
  Parameter scan : string -> list Token.

End LEXICAL.

Module Lexical (Keyword:KEYWORDS) <: LEXICAL.

  Record Position : Set := 
    mkPos
    {pos_lnum : nat;
      pos_cnum : nat}.
  
  Inductive Element : Set := 
  | Key : string -> Element 
  | Id : string -> Element
  | Con : string -> Element
  | Num : nat -> Element.

  Definition Token := (Element * Position)%type.

  Definition showElement (e:Element) : string :=  
    match e with 
      | (Key s) => s
      | (Id s) => s
      | (Con s) => s
      | (Num i) => string_of_nat i
    end. 
  
  Definition showToken (t : Token) : string := 
    match t with 
      | (e,_) => showElement e
    end.

  (* Deleted since it's a Coq standard library function
     
     fun member (x:string, l) = List.exists (fn y => x=y) l;  *) 

  Definition idOrKey a := 
    if StringSet.mem a Keyword.alphas 
      then Key a 
      else Id a.

  Definition conOrKey a := 
    if StringSet.mem a Keyword.alphas
      then Key a  
      else Con a.

  Definition numeric n := 
    match nat_of_string n with 
      | None => Id n
      | Some i => Num i
    end.

  Require Import Bool.
  Require Import Arith.
  Require Import String.
  Open Scope string_scope.
  Definition symbolic : forall (sy ss : string) (len : nat), {t : Element*string*nat | length (snd (fst t)) <= length ss}.
    refine 
      (fix symbolic_f (sy ss : string) (len : nat) {struct ss} :  {t : Element*string*nat | length (snd (fst t)) <= length ss} := 
        match ss 
          return {t : Element*string*nat | length (snd (fst t)) <= length ss}
          with 
          | EmptyString => exist _ (Key sy, EmptyString, len) _
          | String c ss1 => 
            match bool_dec (StringSet.mem sy Keyword.symbols || (! (Char.isPunct c))) true           
              return {t : Element*string*nat | length (snd (fst t)) <= length (String c ss1)}
              with 
              | left H => exist _ (Key sy, (String c ss1), len) _
              | right H => match symbolic_f (sy ++ (String c EmptyString)) ss1 (len+1) 
                             return {t : Element*string*nat | length (snd (fst t)) <= length (String c ss1)}
                             with 
                             | exist e P => exist _ e _                       
                           end
            end
        end) ;simpl in * ; auto with arith.
  Defined.  

  Definition inc_cnum pos inc := mkPos (pos.(pos_lnum)) ((pos.(pos_cnum))+inc).
  
  Definition inc_lnum pos inc := mkPos ((pos.(pos_lnum))+inc) (pos.(pos_cnum)).
  
  Definition reset_cnum pos := mkPos (pos.(pos_lnum)) 0.

  Definition isGraphOrNewline c := Char.isGraph c || Char.isNewline c.

  Open Scope char_scope.
  Require Import Substring.
  Open Scope list_scope.
 
  Ltac eqfalse := unfold not in * ; 
    (match goal with 
      | H : (?x = ?x) -> False |- _ => 
        let id := fresh "Heq" in (cut (x = x) ; [ intros id ; apply H in id ; destruct id | auto ] )
     end).

  Ltac magic_false := 
    match goal with
      | H : False |- _ => destruct H 
    end.

  Ltac magic_rewrite := 
    match goal with 
      | H  : (_ = true) |- _ => rewrite H in *; simpl in * ; try magic_false
    end.
        
  Ltac magic_term := 
    match goal with 
      | H : terminates ?f ?x |- _ => 
              simpl in * ; subst ; 
                simpl in * ; subst ; 
                  simpl in * ; try magic_rewrite
    end.

  Ltac magic_neq := 
    match goal with 
      | H : ?s <> "" |- _ => 
        destruct s ; 
          [ eqfalse 
            | simpl ; rewrite length_app ; auto with arith ]
    end.

  Ltac magic_sat := 
    match goal with 
      | H : all_sat ?f ?x |- _ => 
        let Hemp := fresh "Hemp" in 
          let Hall := fresh "Hall" in 
            inversion H as [Hemp | Hp]; 
              [ clear H ; magic_term 
                | inversion Hp as [Hnemp Hall] ; clear Hp ; 
                  simpl in * ; magic_neq  
              ]
    end.

  Ltac convert_bool := 
    match goal with 
      | H: ?x <> true |- _ => apply not_true_is_false in H ; try convert_bool
    end. 

  Open Scope list_scope.
  Program Fixpoint scanning (ss:string) (toks:list Token) (pos:Position) {measure String.length ss} : list Token := 
    match ss with 
      | EmptyString => rev toks 
      | String c ss1 =>
        if bool_dec (Char.isLower c) true 
        then
          let (p,H) := Substring.splitl (fun x => (Char.isAlphaNum x)) (String c ss1) in
          let pos1 := inc_cnum pos (String.length (fst p)) in
          let tok := (idOrKey (fst p), pos1) in 
            scanning (snd p) (tok::toks) pos1
        else if bool_dec (Char.isUpper c) true
        then (* constructor or keyword *) 
          let (p,H) := Substring.splitl Char.isAlphaNum (String c ss1) in
          let pos1 := inc_cnum pos (String.length (fst p)) in
          let tok := (conOrKey (fst p), pos1) in
            scanning (snd p) (tok::toks) pos1
        else if bool_dec (Char.isDigit c) true
        then (* number *) 
          let (p,H) := Substring.splitl Char.isDigit (String c ss1) in
          let pos1 := inc_cnum pos (String.length (fst p)) in
          let tok := (numeric (fst p), pos1) in 
            scanning (snd p) (tok::toks) pos1 
        else if bool_dec (Char.isPunct c) true
        then (*special symbol*)
	  let (t,H) := symbolic (String c EmptyString) ss1 0 in
          let pos1 := inc_cnum pos (snd t) in
          let tok := ((fst (fst t)),pos1) in
            scanning (snd (fst t)) (tok::toks) pos1
	else if bool_dec (Char.isNewline c) true
	then (* newline *) 
	  scanning ss1 toks (inc_lnum (reset_cnum pos) 1)
        else (*ignore spaces, line breaks, control characters*)
	  let (p,H) := Substring.splitl (fun x => ! (isGraphOrNewline x)) (String c ss1)in
	  let pos1 := inc_cnum pos (String.length (fst p)) in
            scanning (snd p) toks pos1
    end.
  Next Obligation.    
  (* identifier or keyword *)
    apply Char.lower_imp_alphanum in H.
    magic_sat.
  Defined.

  (* constructor or keyword *)
  Next Obligation. 
    apply Char.upper_imp_alphanum in H0. 
    magic_sat.
  Defined. 

  (* number *) 
  Next Obligation.
    magic_sat.
  Defined. 

  (*special symbol*) 
  Next Obligation.
    simpl in * ;auto with arith. 
  Defined.
 
  (*ignore spaces, line breaks, control characters*)
  Next Obligation. 
    cut ((!(isGraphOrNewline c)) = true). intro Hcut.
    magic_sat. convert_bool.
    unfold isGraphOrNewline. 
    unfold Char.isPunct in *. unfold Char.isAlphaNum in *. unfold Char.isAlpha in *. 
    case_eq (Char.isGraph c) ; intros Hg. rewrite Hg in H2. rewrite H1 in H2. rewrite H0 in H2.
    rewrite H in H2. inversion H2. rewrite H3. auto.
  Defined.

  Definition scan a := scanning a nil (mkPos 1 1).

End Lexical.