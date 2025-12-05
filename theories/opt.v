From Coq Require Import RelationClasses Morphisms Program.

(** * Useful definitions related to option types *)

(** ** Option types and the "less defined" relation *)

Definition less_def {A} (v1 : option A) (v2 : option A) :=
  match v1, v2 with
  | Some v1, Some v2 => v1 = v2
  | Some v1, None => False
  | None, _ => True
  end.

Infix "<=" := less_def.

(** [less_def] is transitive *)
Instance less_def_trans {A} : Transitive (@less_def A).
  intros [x|] [y|] [z|]; simpl; try easy.
  congruence.
Qed.

(** [less_def] is reflexive *)
Instance less_def_refl {A} : Reflexive (@less_def A).
  now intros [x|].
Qed.

(** Lifting of binary operations to operations on optional values *)
Definition binop {A B C} (f : A -> B -> C) (v1 : option A) (v2 : option B) : option C :=
  match v1, v2 with
  | Some v1, Some v2 => Some (f v1 v2)
  | _, _ => None
  end.

(** [binop] is monotone with respect to [less_def] *)
Lemma binop_less_def {A B C} (f : A -> B -> C):
  forall v1 v2 v1' v2',
    v1 <= v1' ->
    v2 <= v2' ->
    binop f v1 v2 <= binop f v1' v2'.
Proof.
  intros * H1 H2.
  unfold binop.
  destruct v1, v2, v1', v2'; try easy.
  congruence.
Qed.

Instance binop_proper {A B C} (f : A -> B -> C):
  Proper (@less_def A ==> @less_def B ==> @less_def C) (binop f).
Proof.
  intros a1 a2 Ha b1 b2 Hb.
  now apply binop_less_def.
Qed.

Definition is_some {A} (v : option A) :=
  v <> None.

Instance is_some_proper {A}:
  Proper (@less_def A ==> impl) (@is_some A).
Proof.
  intros a1 a2 Ha H.
  now destruct a1, a2.
Qed.

Lemma is_some_iff_le {A}:
  forall (v1 : option A) (v2 : A),
    v1 = Some v2 -> v1 <= Some v2.
Proof.
  now intros * ->.
Qed.

(** ** Partial Maps *)