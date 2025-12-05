From minilola Require Import lang sem.
From Coq Require Import List Sorting.Permutation.

(** * Extended type system for checking consistency of pacing annotations *)

(**
  Typing rules for expressions,
  extended with a [Self] rule for self-references.
*)
Inductive ExprTypeSyn (G : TypeEnv) (x : OUT) : Expr -> Pacing -> Prop :=
  | TypeVal (v : value) (t : Pacing) :
    ExprTypeSyn G x (EVal v) t

  | TypeBinOp (f : value -> value -> value) (e1 : Expr) (e2 : Expr) (t : Pacing) :
    ExprTypeSyn G x e1 t ->
    ExprTypeSyn G x e2 t ->
    ExprTypeSyn G x (EBinOp f e1 e2) t

  | TypeDirectOut (y : OUT) (t : Pacing) (t1 : Pacing) :
    x <> y ->
    G y = Some t1 ->
    PacingEnt t t1 ->
    ExprTypeSyn G x (EVar (Varout y)) t

  | TypeDirectIn (y : IN) (t : Pacing) :
    PacingEnt t (PVar y) ->
    ExprTypeSyn G x (EVar (Varin y)) t

  | TypeHoldOut (y : OUT) (e : Expr) (t : Pacing) :
    x <> y ->
    G y <> None ->
    ExprTypeSyn G x e t ->
    ExprTypeSyn G x (EHold (Varout y) e) t

  | TypeHoldIn (y : IN) (e : Expr) (t : Pacing) :
    ExprTypeSyn G x e t ->
    ExprTypeSyn G x (EHold (Varin y) e) t

  | TypePrevOut (y : OUT) (e : Expr) (t : Pacing) (t1 : Pacing) :
    x <> y ->
    G y = Some t1 ->
    ExprTypeSyn G x e t ->
    PacingEnt t t1 ->
    ExprTypeSyn G x (EPrev (Varout y) e) t

  | TypePrevIn (y : IN) (e : Expr) (t : Pacing) :
    ExprTypeSyn G x e t ->
    PacingEnt t (PVar y) ->
    ExprTypeSyn G x (EPrev (Varin y) e) t

  | Self (e : Expr) (t : Pacing) :
    G x = None ->
    ExprTypeSyn G x e t ->
    ExprTypeSyn G x (EPrev (Varout x) e) t.


(**
  Typing rules for equations,
  extended with a [Reorder] rule for reoredering equations.
*)
Inductive SpecTypeSyn : TypeEnv -> Spec -> Prop :=
  | Empty (G : TypeEnv) :
    SpecTypeSyn G nil

  | Reorder G s1 s2 :
    Permutation s1 s2 ->
    SpecTypeSyn G s2 ->
    SpecTypeSyn G s1

  | Equation (G : TypeEnv) (x : OUT) (e : Expr) (t : Pacing) s:
    G x = None ->
    ExprTypeSyn G x e t ->
    SpecTypeSyn (update G x t) s ->
    SpecTypeSyn G ((x, t, e)::s).