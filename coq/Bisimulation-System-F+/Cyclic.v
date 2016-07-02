Require Import SystemF. 
Require Import List.
Require Import Eval. 

Section Cyclic. 

  Variable Delta : nat -> Term.
  Variable Xi : nat -> Ty.  
  Variable Prog : forall n l m, Derivation Xi [n ; l |= F m @ Xi m] -> Derivation Xi [n ; l |= Delta m @ Xi m]. 
  Variable ProgTy : forall m, valid (Xi m) 0.

(*
  Inductive Ev_delta : Term -> Term -> Set :=
  | ev_f : forall n, Ev (F n) (Delta n)
  | ev_app : forall t t' s, Ev t t' -> Ev (App t s) (App t' s)
  | ev_tapp : forall t t' ty, Ev t t' -> Ev (TApp t ty) (TApp t' ty).


  Notation "t ~>d t'" := (Ev Delta t t') (at level 60).  
*) 

  CoInductive PreProof : Holds -> Set := 
  | DeltaStep' : forall n l t t' ty,
    PreProof [n ; l |= t' @ ty] ->
    t ~> t' -> 
    PreProof [n ; l |= t @ ty]
  | ImpIntro' : forall n l t ty xty,
    valid xty n ->
    PreProof [n ; xty::l |= t @ ty] -> 
    PreProof [n ; l |= (Abs xty t) @ (Imp xty ty)]
  | ImpElim' : forall n l t f ty xty,
    PreProof [n ; l |= t @ xty] ->
    PreProof [n ; l |= f @ (Imp xty ty)] -> 
    PreProof [n ; l |= (App f t) @ ty]
  | AllIntro' : forall n l t ty,
    PreProof [S n ; map tyshift l |= t @ ty] -> 
    PreProof [n ; l |= (Lam t) @ All ty]
  | AllElim' : forall n l t ty xty,
    valid xty n ->
    PreProof [n ; l |= t @ All ty] -> 
    PreProof [n ; l |= TApp t xty @ (tysub ty 0 xty)]
  | VarIntro' : forall n l ty i,
    valid ty n -> i < length l -> nth i l Zero = ty ->
    PreProof [n ; l |= V i @ ty].

(* Parameter ProgCyc : forall n l m, PreProof [n ; l |= F m @ Xi m] -> PreProof [n ; l |= Delta m @ Xi m]. *)

Theorem derivation_imp_preproof : forall n l t ty, Derivation Xi [ n ; l |= t @ ty ] -> PreProof [n ; l |= t @ ty].
Proof.
  refine (cofix derivation_imp_preproof n l t ty (HD : Derivation Xi [ n ; l |= t @ ty ]) : PreProof [n ; l |= t @ ty] := _). 
  inversion HD ; subst.
  (* F *) 
  apply DeltaStep' with (t':= Delta m). 
  apply derivation_imp_preproof.
  apply Prog in HD. auto.  
  apply Evplus_base. apply ev_f.  
  (* Abs *)
  apply ImpIntro' ; auto.  
  (* App *) 
  apply ImpElim' with (xty:=xty) ; auto.
  (* Lam *) 
  apply AllIntro'. 
  apply derivation_imp_preproof ; auto.   
  (* TApp *) 
  apply AllElim' ; auto.
  (* V *)    
  apply VarIntro' ; auto.
Defined.

(* 
Lemma ev_lemma : forall a b c, (a ~> b) -> (App a c ~> App b c) -> (App a c ~>+ d) -> (App b c ~>+ d). 

H2 : t0 ~> t'0
  EvH : App t0 t1 ~> App t'0 t1
  t' : Term
  H1 : PreProof [n; l |=t' @ ty]
  H5 : App t0 t1 ~>+ t'
  ============================
   App t'0 t1 ~>+ t'
*)
  
Theorem ev_preservation_cyc : forall t t' n l ty,  PreProof [n ; l |= t @ ty] ->  t ~> t' -> PreProof [n ; l |= t' @ ty].
Proof.
  refine (cofix ev_preservation_cyc t t' n l ty (D : PreProof [n ; l |= t @ ty]) (EvH : t ~> t') : PreProof [n ; l |= t' @ ty] := _)
    ; case_eq t ; intros; subst. 
  (* F *)  
  inversion D; subst.
  apply ev_inter_evplus with (c:= t'0) in EvH.
  inversion EvH ; subst.
    (* = *) 
    auto.
    (* ~>+ *) 
    apply DeltaStep' with (t':=t'0). auto. auto. auto.
  (* V *)
  inversion EvH.
  (* App *) 
  inversion D ; subst.
    (* Delta *) 
    apply ev_inter_evplus with (b:= t') in H4.
    inversion H4 ; subst.
      (* = *)
      subst. exact H1.
      (* ~> *)
      apply DeltaStep' with (t':=t'0); auto. auto.
    (* App Rule *) 
    inversion EvH ; subst. 
    apply ImpElim' with (xty:=xty). auto. 
    apply ev_preservation_cyc with (ty:=Imp xty ty) (n:=n) (l:=l)  in H3 ; auto. 
    (* Subst Rule *) 
    apply sub_preservation. 
  (* TApp *) 
  inversion EvH ; subst.
  inversion D ; subst. 
  apply AllElim ; auto. 
  apply ev_preservation with (t:=t0) ; auto.
  inversion D ; subst.
  inversion H6 ; subst.
  apply tysub_derivation_simple. auto. auto.
  (* Abs *) 
  inversion EvH. 
  (* Lam *) 
  inversion EvH.
Defined. 
