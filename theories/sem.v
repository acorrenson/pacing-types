From minilola Require Import lang opt.
From Stdlib Require Import Sorting.Permutation.

(** * Formal semantics of stream equations with pacing annotations *)

(** ** Preliminary definitions *)

(** Synchronous stream access *)
Definition sync (w : stream) (n : nat) : option value :=
  w n.

(** Last defined from time point [n] *)
Fixpoint last (w : stream) (n : nat) : option value :=
  match w n with
  | Some v => Some v
  | None =>
    match n with
    | 0 => None
    | S n => last w n
    end
  end.

(** Last defined value from time point [n], or [v] if none *)
Definition hold (w : stream) n (v : option value) : option value :=
  match last w n with
  | Some v' => Some v'
  | None => v
  end.

(**
  Synchronous access to the previous value at time point [n].
  Fail if there is no value at time [n].
*)
Definition prev (w : stream) n (v : option value) : option value :=
  match w n with
  | None => None
  | Some v' =>
    match n with
    | 0 => v
    | S n =>
      match last w n with
      | Some v' => Some v'
      | None => v
      end
    end
  end.

(** ** Semantics of annotations *)

(** Semantics of pacing annotations *)
Fixpoint PacingSem (r : InMap) (t : Pacing) (n : nat) :=
  match t with
  | PTop => True
  | PVar x => r x n <> None
  | PAnd t1 t2 => PacingSem r t1 n /\ PacingSem r t2 n
  | POr t1 t2 => PacingSem r t1 n \/ PacingSem r t2 n
  end.

Fixpoint PacingSemBool (r : InMap) (t : Pacing) (n : nat) :=
  match t with
  | PTop => true
  | PVar x =>
    match r x n with
    | None => false
    | Some _ => true
    end
  | PAnd t1 t2 => (PacingSemBool r t1 n && PacingSemBool r t2 n)%bool
  | POr t1 t2 => (PacingSemBool r t1 n || PacingSemBool r t2 n)%bool
  end.

Lemma PacingSemBool_true_iff:
  forall r t n, PacingSemBool r t n = true <-> PacingSem r t n.
Proof.
  induction t; intros n; simpl; split; auto.
  - now destruct (r x n).
  - now destruct (r x n).
  - intros [H1 H2]%Bool.andb_true_iff.
    firstorder.
  - intros [H1 H2].
    apply Bool.andb_true_iff.
    firstorder.
  - intros [H1 | H1]%Bool.orb_true_iff; firstorder.
  - intros [H1 | H1]; apply Bool.orb_true_iff; firstorder.
Qed.

(**
  Pacing Entailement.
  Define what it means for a pacing annotation
  to describe "less time points" than another one.
*)
Definition PacingEnt (tmust : Pacing) (tcan : Pacing) : Prop :=
  forall (rin : InMap) (n : nat), PacingSem rin tmust n -> PacingSem rin tcan n.

(** ** Semantics of expressions *)

(** Access an input or output stream in a pair of stream maps *)
Definition get '((rin, rout) : InMap * OutMap) (v : Var) :=
  match v with
  | Varin x => rin x
  | Varout x => rout x
  end.

(** Stream denoted by a stream expression in a given pair of stream maps *)
Fixpoint ExprSem (e : Expr) (r : InMap * OutMap) (n : nat) : option value :=
  match e with
  | EVar x => sync (get r x) n
  | EVal v => Some v
  | EPrev x e => prev (get r x) n (ExprSem e r n)
  | EHold x e => hold (get r x) n (ExprSem e r n)
  | EBinOp f e1 e2 => binop f (ExprSem e1 r n) (ExprSem e2 r n)
  end.


(** ** Semantics of equations *)

(** What it means for an equation to be satisfied at a given time point [n] *)
Definition EqSem_at '((x, t, e) : (OUT * Pacing * Expr)) '((rin, rout) : InMap * OutMap) (n : nat) :=
  (rout x n <= ExprSem e (rin, rout) n) /\
  (PacingSem rin t n <-> rout x n <> None).

(** What it means for an equation to be satisfied at all time points *)
Definition EqSem equ r :=
  forall n, EqSem_at equ r n.

(** What it means for a list of equations to be satisfied *)
Definition Sem (s : Spec) (r : InMap * OutMap) :=
  Forall (fun e => EqSem e r) s.

(** What it means for a list of equations to be satisfied at a given time point [n] *)
Definition Sem_at (s : Spec) (r : InMap * OutMap) (n : nat) :=
  Forall (fun e => EqSem_at e r n) s.

(** ** Useful lemmas *)

(** [prev] is compatible with the "less-defined" relation *)
Lemma prev_less_def:
  forall n w (v1 v2 : option value),
    v1 <= v2 ->
    prev w n v1 <= prev w n v2.
Proof.
  intros * H.
  unfold prev. destruct (w n), n; simpl; auto.
  now destruct (last w n).
Qed.

(** [hold] is compatible with the "less-defined" relation *)
Lemma hold_less_def:
  forall n w (v1 v2 : option value),
    v1 <= v2 ->
    hold w n v1 <= hold w n v2.
Proof.
  intros * H.
  unfold hold. now destruct (last w n).
Qed.

(** The semantics of equations is order-insensitive *)
Lemma Sem_Permut:
  forall (s1 s2 : Spec),
    Permutation s1 s2 ->
    forall rin rout,
    Sem s1 (rin, rout) -> Sem s2 (rin, rout).
Proof.
  intros * Hperm * Hsem.
  apply Forall_forall.
  intros x Hx.
  eapply Forall_forall in Hsem; eauto.
  eapply Permutation_in.
  apply Permutation_sym. eauto.
  apply Hx.
Qed.
