Require Import Lexicals.
Require Import String.
Require Import List.
Require Import Exceptions.
Require Import MyUtils.
Require Import Monad.
Require Import ZArith.
  
Module Type PARSE.
  
  Parameter position : Set.
  Parameter element : Set.
  Parameter token : Set. 
  Parameter M : Type -> Type. 
  Definition Parse A (l:list token) := (A*{l' : list token | Suffix l' l})%type.
  Definition Parser A := forall l, M (Parse A l). 
  Parameter id : Parser string.
  Parameter num : Parser nat.
  Parameter con : Parser string.
  Parameter str : forall (s:string), Parser string.
  Parameter alt : forall (A:Type), Parser A -> Parser A -> Parser A.
  Parameter must : forall (A:Type), Parser A -> Parser A. 
  Parameter pair : forall (A B:Type), Parser A -> Parser B -> Parser (A * B). 
  Parameter s_pair : forall (A:Type), string -> Parser A -> Parser A.
  Parameter pair_s : forall (A:Type), Parser A -> string -> Parser A. 
  Parameter appl : forall (A B:Type), Parser A -> (A -> B) -> Parser B.  
  Parameter repeat : forall (A:Type), Parser A -> Parser (list A). 
  Parameter wrap : forall (A:Type), Parser A -> Parser (list A). 
  (* 
  Parameter infixes : forall (A:Set), Parser A -> (string -> Z) -> (string -> A -> A -> A) -> Parser A. 
  *)
  Parameter reader : forall (A:Type), Parser A -> string -> M A.
End PARSE.
    
Module Parse (Lex : LEXICAL) <: PARSE. 
  
  Definition position := Lex.Position.
  Definition element := Lex.Element.
  Definition token := Lex.Token.

  Definition M := ExceptionM. 

  Definition SyntaxErr := "SyntaxErr"%string.
  Definition Fail := "Fail"%string. 

  Definition report_position r := 
    ("(line,character): ("++(string_of_nat (Lex.pos_lnum r))++
     ","++(string_of_nat (Lex.pos_cnum r))++")")%string. 

  Definition Parse A (l:list token) := (A*{l' : list token | Suffix l' l})%type.
  Definition Parser (A:Type) := forall l, M (Parse A l).

  (*Phrase consisting of an identifier*)
  Definition id : Parser string. 
    unfold Parser.
    refine 
      (fun l : list token => 
        match l return M (Parse string l) with 
          | nil => raise SyntaxErr "Identifier expected, but at end of input."
          | cons (Lex.Id a,_) toks => ret (a,(exist _ toks _))
          | cons (_,pos) _ => 
            raise SyntaxErr ("Identifier expected at "++(report_position pos))%string
        end). simpl ; auto.
  Defined.

  (*Phrase consisting of an number*)
  (* Definition num (l:list token) : Parse nat l := *) 
  Definition num : Parser nat.
    unfold Parser.
    refine 
      (fun l : list token => 
        match l return M (Parse nat l) with 
          | nil => raise SyntaxErr "Number expected, but at end of input."
          | cons (Lex.Num n,_) toks => ret (n,(exist _ toks _))
          | cons (_,pos) _ => 
            raise SyntaxErr ("Number expected at "++(report_position pos)) 
        end). simpl ; auto.
  Defined.

  (* Phrase consisting of a constructor *)
  Definition con : Parser string.
    unfold Parser.
    refine 
      (fun l : list token => 
        match l return M (Parse string l) with 
          | nil => raise SyntaxErr "Constructor expected, but at end of input."
          | cons (Lex.Con c,_) toks => ret (c,(exist _ toks _))
          | cons (_,pos) _ => 
            raise SyntaxErr ("Constructor expected at "++(report_position pos))
        end). simpl ; auto. 
  Defined.

  (*Phrase consisting of the keyword 'a' *)
  Definition str (a:string) : Parser string.
    unfold Parser. 
    refine 
      (fun (a:string) (l : list token) =>       
        match l return M (Parse string l) with 
          | nil => raise SyntaxErr (a++" expected, but at end of input.")
          | cons (Lex.Key b,pos) toks => 
            if string_dec a b then ret (a,(exist _ toks _))
              else raise SyntaxErr (a++" expected, "++b++" found at "++(report_position pos))
          | cons (_,pos) toks => 
            raise SyntaxErr ("Keyword expected: "++a++" at "++(report_position pos))
        end). simpl ; auto.
  Defined.

  (* parsing disjunction *)
  Definition alt `A` (ph1: Parser A) (ph2: Parser A) : Parser A := 
    (fun toks => 
      ph1 toks 
      |:| SyntaxErr, msg => ph2 toks). 
  Infix "|+|" := alt.
  
  (* fail if we can't parse with ph.  This is like prolog's cut and pretty nasty for the same reasons. *)
  Definition must `A` (ph: Parser A) : Parser A :=
    (fun toks => 
      ph toks 
      |:| SyntaxErr, msg => raise Fail msg). 
  Notation "|!| ph" := (must ph) (at level 0).

  (*One phrase then another*)
  Definition pair `A B` (ph1 : Parser A) (ph2 : Parser B) : Parser (A*B).  
    unfold Parser.
    refine 
      (fun (A B : Type) (ph1 : Parser A) (ph2 : Parser B) (toks : list token) => 
        px <- ph1 toks ;;
        (match px with 
           | (x,(exist toks2 Hx)) => 
             py <- ph2 toks2 ;; 
             (match py with
                | (y,(exist toks3 Hy)) => ret ((x,y),exist _ toks3 _)
              end)
         end)) ; eapply suffix_trans ; eauto.
  Defined. 
  Infix "--" := pair (at level 55).

  (*Application of f to the result of a phrase*)
  Definition appl `A B` (ph : Parser A) (f : A -> B) : Parser B. 
    unfold Parser.
    refine 
      (fun (A B : Type) (ph : Parser A) (f : A -> B) (toks : list token) => 
        px <- ph toks ;; 
        (match px with 
           | (x,(exist toks2 Hx)) => 
             ret (f x,exist _ toks2 _)
         end)) ; auto.
  Defined.
  Infix "|>|" := appl (at level 55).
  
  Definition s_pair `A` (a:string) (ph: Parser A) : Parser A :=     
    (str a) -- |!|ph |>| (fun (x:string*A) => snd x).
  Infix "@--" := s_pair (at level 50).

  Definition pair_s `A` (ph: Parser A) (a:string) : Parser A :=
    |!|ph -- (str a) |>| (fun (x:A*string) => fst x).
  Infix "--@" := pair_s (at level 50).

  Require Import Recdef.
  (* We don't use the ML definition of repeat because it doesn't necessarily make progress *)
  Function repeat_aux (A:Type) (ph : Parser A) (toks : list token) {measure length toks} : M (Parse (list A) toks) :=
    match ph toks with 
      | exn e => exn _ e
      | no_exn (a,exist toks' Htoks') => 
        match repeat_aux A ph toks' with 
          | exn e => ret (nil,exist _ toks' Htoks')
          | no_exn (b,exist toks'' Htoks'') => ret ((cons a b), exist _ toks'' (suffix_trans _ toks toks' toks'' Htoks' Htoks''))
        end
    end. intros. apply suffix_smaller. auto.
  Defined. 

  (* this just gives us implicit A and makes the type more readable. [Function is a bit ugly in that it changes the names of parameters] *) 
  Definition repeat `A` (ph:Parser A) : Parser (list A) := repeat_aux A ph.

  Definition wrap `A` (ph:Parser A) : Parser (list A).
    unfold Parser.
    refine 
      (fun (A:Type) (ph:Parser A) (toks:list token) => 
        (px <- ph toks ;;
          (match px with 
             | (a,exist toks' Htoks') => ret (cons a nil, exist _ toks' Htoks') 
           end))).
  Defined.

  (* 
  fun infixes (ph,prec_of,apply) = 
    let fun over k toks = next k (ph toks)
        and next k (x, (Lex.Key(a),pos)::toks) = 
              if prec_of a < k then (x, (Lex.Key a,pos) :: toks)
              else next k ((over (prec_of a) >> apply a x) toks)
          | next k (x, toks) = (x, toks)
    in  over 0  end;

    *) 

  (*Scan and parse, checking that no tokens remain*)
  Definition reader `A` (ph : Parser A) str : M A := 
    (px <- ph (Lex.scan str) ;; 
      (match px with 
         | (x,exist nil H1) => ret x
         | (_,exist (cons tok _) _) => 
           raise SyntaxErr ("Extra characters in phrase: " ++ (Lex.showToken tok) 
             ++ "..." ++ "near "++(report_position (snd tok)))
       end))
    (* Turn failures back into syntax errors *)
    |:| Fail, msg => raise SyntaxErr msg. 

End Parse.