Require Import Atom.
Require Import EqDec.

Program Instance EqDec Atom := 
  eq_dec := eq_atom_dec.
