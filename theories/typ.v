From minilola Require Import lang sem opt.
From Coq Require Import List.
Import ListNotations.

(** * Basic type system for checking consistency of pacing annotations *)

(**
  Typing judgement for expressions
*)
Inductive ExprTypeSyn : TypeEnv -> Expr -> Pacing -> Prop :=
  | TypeVal (G : TypeEnv) (v : value) (t : Pacing) :
    ExprTypeSyn G (EVal v) t

  | TypeBinOp (G : TypeEnv) (f : value -> value -> value) (e1 : Expr) (e2 : Expr) (t : Pacing) :
    ExprTypeSyn G e1 t ->
    ExprTypeSyn G e2 t ->
    ExprTypeSyn G (EBinOp f e1 e2) t

  | TypeDirectOut (G : TypeEnv) (y : OUT) (t : Pacing) (t1 : Pacing) :
    G y = Some t1 ->
    PacingEnt t t1 ->
    ExprTypeSyn G (EVar (Varout y)) t

  | TypeDirectIn (G : TypeEnv) (y : IN) (t : Pacing) :
    PacingEnt t (PVar y) ->
    ExprTypeSyn G (EVar (Varin y)) t

  | TypeHoldOut (G : TypeEnv) (y : OUT) (e : Expr) (t : Pacing) :
    G y <> None ->
    ExprTypeSyn G e t ->
    ExprTypeSyn G (EHold (Varout y) e) t

  | TypeHoldIn (G : TypeEnv) (y : IN) (e : Expr) (t : Pacing) :
    ExprTypeSyn G e t ->
    ExprTypeSyn G (EHold (Varin y) e) t

  | TypePrevOut (G : TypeEnv) (x : OUT) (e : Expr) (t : Pacing) (t1 : Pacing) :
    G x = Some t1 ->
    ExprTypeSyn G e t ->
    PacingEnt t t1 ->
    ExprTypeSyn G (EPrev (Varout x) e) t

  | TypePrevIn (G : TypeEnv) (y : IN) (e : Expr) (t : Pacing) :
    ExprTypeSyn G e t ->
    PacingEnt t (PVar y) ->
    ExprTypeSyn G (EPrev (Varin y) e) t.

(**
  Typing judgement for specifications
*)
Inductive SpecTypeSyn : TypeEnv -> Spec -> Prop :=
  | TypeEmpty (G : TypeEnv) :
    SpecTypeSyn G nil

  | TypeEquation (G : TypeEnv) (x : OUT) (e : Expr) (t : Pacing) s:
    G x = None ->
    ExprTypeSyn G e t ->
    SpecTypeSyn (update G x t) s ->
    SpecTypeSyn G ((x, t, e)::s).

Axiom bat_lvl : IN.
Axiom drain   : OUT.
Axiom dft : value.
Axiom f : value -> value -> value.

Example bat_monitor : Spec := [
    (drain, PVar bat_lvl, EBinOp f (EPrev (Varin bat_lvl) (EVal dft)) (EVar (Varin bat_lvl)))
  ].

Goal 
  SpecTypeSyn (fun _ => None) bat_monitor.
Proof.
  apply TypeEquation; auto.
  - apply TypeBinOp.
    + apply TypePrevIn.
      apply TypeVal.
      easy.
    + apply TypeDirectIn.
      easy.
  - apply TypeEmpty.
Qed.

