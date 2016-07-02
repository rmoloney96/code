Require Import Ascii.
Set Implicit Arguments.
Unset Strict Implicit.

Inductive IO (A:Type) : Type := 
| get_char : (ascii -> IO A) -> IO A
| put_char : ascii -> IO A -> IO A
| ret : A -> IO A.

Definition getChar : IO ascii := 
  get_char (ret (A:=ascii)).


  
