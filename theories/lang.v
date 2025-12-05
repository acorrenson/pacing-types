From Coq Require Export List.
Export ListNotations.

(** * Formalization of core language to model RTLola programs *)

(** ** Preliminary definitions *)

(** We suppose a type of input variables to be given *)
Axiom IN : Type.

(** We suppose a type of output variables to be given *)
Axiom OUT : Type.

(** Input variables are assumed to have a decidable equality *)
Axiom IN_dec : forall (i1 i2 : IN), { i1 = i2 } + { i1 <> i2 }.

(** Output variables are assumed to have a decidable equality *)
Axiom OUT_dec : forall (o1 o2 : OUT), { o1 = o2 } + { o1 <> o2 }.

(** We suppose a type of values to be given *)
Axiom value : Type.

(** Streams are infinite sequences of optional values *)
Definition stream := nat -> option value.

(** Input maps *)
Definition InMap := IN -> stream.

(** Output maps *)
Definition OutMap := OUT -> stream.

(** ** Syntax of Programs *)

Inductive Var : Type :=
  | Varin (s : IN)
  | Varout (s : OUT).

Inductive Expr : Type :=
  | EVar (x : Var)
  | EVal (v : value)
  | EPrev (x : Var) (e : Expr)
  | EHold (x : Var) (e : Expr)
  | EBinOp (f : value -> value -> value) (e1 : Expr) (e2 : Expr).

Inductive Pacing : Type :=
  | PTop
  | PVar (x : IN)
  | PAnd (t1 : Pacing) (t2 : Pacing)
  | POr (t1 : Pacing) (t2 : Pacing).

(**
  A specification is a list of named stream expression labeled
  with pacing annotations.
*)
Definition Spec :=
  list (OUT * Pacing * Expr).

(** Typing environements *)
Definition TypeEnv := OUT -> option Pacing.

(** Updating arbitrary partial output maps *)
Definition update {A} (map : OUT -> option A) (x : OUT) (a : A) :=
  fun x' => if OUT_dec x x' then Some a else map x'.