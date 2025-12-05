From minilola Require Import lang sem typ opt.
From Coq Require Import FunctionalExtensionality Sorting.Permutation.

(** * Soundness proof of the type system *)

(**
  Equations are "consistent" if they have at least one model:
  for every inputs, there must existst at least one output
  satisfying the equations.
  Our goal is to prove that well-typed equations are consistent.
*)
Definition Consistent (s : Spec) : Prop :=
  forall (rin : InMap), exists (rout : OutMap), Sem s (rin, rout).

(** ** Preliminary Definitions *)

(** Partial Maps *)
Definition Pmap := OUT -> option stream.

(** Extending a partial map *)
Definition pextend (p : Pmap) (x : OUT) (w : stream) : Pmap :=
  fun x' => if OUT_dec x x' then Some w else p x'.

(** Extending a total map *)
Definition extend (p : OutMap) (x : OUT) (w : stream) : OutMap :=
  fun x' => if OUT_dec x x' then w else p x'.

(** Merging a partial map and a total map *)
Definition merge (rout1 : Pmap) (rout2 : OutMap) : OutMap :=
  fun x =>
    match rout1 x with
    | Some w => w
    | None => rout2 x
    end.

(** Merging lemma *)
Lemma merge_pextend:
  forall rout1 rout2 x w,
    rout1 x = None ->
    merge (pextend rout1 x w) rout2 = merge rout1 (extend rout2 x w).
Proof.
  intros.
  apply functional_extensionality.
  intros y. unfold update, merge, pextend, extend. 
  destruct (OUT_dec x y); subst.
  - now rewrite H.
  - destruct (rout1 y); auto.
Qed.

(** Empty typing context *)
Definition bot_tenv : TypeEnv :=
  fun _ => None.

(** Empty partial map *)
Definition bot_pmap : Pmap :=
  fun _ => None.

Lemma merge_bot:
  forall rout, merge bot_pmap rout = rout.
Proof.
  easy.
Qed.

(**
  Semantic of expressions under partial output maps
*)
Fixpoint PartialExprSem (e : Expr) (rin : InMap) (rout : Pmap) (n : nat) : option value :=
  match e with
  | EVar (Varin x) => sync (rin x) n
  | EVar (Varout x) =>
    match rout x with
    | None => None
    | Some w => sync w n
    end
  | EVal v => Some v
  | EPrev (Varin x) e => prev (rin x) n (PartialExprSem e rin rout n)
  | EPrev (Varout x) e =>
    match rout x with
    | None => None
    | Some w => prev w n (PartialExprSem e rin rout n)
    end
  | EHold (Varin x) e => hold (rin x) n (PartialExprSem e rin rout n)
  | EHold (Varout x) e =>
    match rout x with
    | None => None
    | Some w => hold w n (PartialExprSem e rin rout n)
    end
  | EBinOp f e1 e2 => binop f (PartialExprSem e1 rin rout n) (PartialExprSem e2 rin rout n)
  end.

(** ** Semantic model of the type system *)

(**
  Interpretation of pacing annotations as sets of streams
*)
Definition PacingRel (t : Pacing) (rin : InMap) (w : stream) : Prop :=
  forall n, PacingSem rin t n <-> w n <> None.

(**
  Comparing the domain of typing environements and partial maps
*)
Definition same_dom (G : TypeEnv) (rout : Pmap) : Prop :=
  (forall x, G x = None -> rout x = None) /\
  (forall x t, G x = Some t -> exists w, rout x = Some w).

(**
  Interpretation of typing environement as sets of partial output maps
*)
Definition EnvRel (G : TypeEnv) (rin : InMap) (rout : Pmap) : Prop :=
  same_dom G rout /\
  forall x t w, G x = Some t -> rout x = Some w -> PacingRel t rin w.


(**
  Interpretation of typing environements as sets of stream expressions
*)
Definition ExprRel (G : TypeEnv) (t : Pacing) (rin : InMap) (e : Expr) : Prop :=
  forall rout, EnvRel G rin rout ->
  forall n, (PacingSem rin t n -> PartialExprSem e rin rout n <> None).

(**
  Interpretation of typing environements as sets of specifications
*)
Definition SpecRel (G : TypeEnv) (rin : InMap) (s : Spec) :=
  forall rout1, EnvRel G rin rout1 ->
  exists rout2, Sem s (rin, merge rout1 rout2).

(** Semantic typing judgement for specifications *)
Definition SpecTypeSem (G : TypeEnv) (s : Spec) :=
  forall rin, SpecRel G rin s.

(** Semantic typing judgement for expressions *)
Definition ExprTypeSem (G : TypeEnv) (e : Expr) (t : Pacing) :=
  forall rin, ExprRel G t rin e.

(**
  Adequacy of the semantic model: semantic typing implies consistency.
*)
Lemma adequacy:
  forall s, SpecTypeSem bot_tenv s -> Consistent s.
Proof.
  intros s Hs rin.
  specialize (Hs rin bot_pmap) as (rout2 & H).
  - easy.
  - exists rout2.
    rewrite merge_bot in H.
    apply H.
Qed.

(** ** Soundness of the Type System for Expressions *)

(** The typing rule for constant values is sound *)
Lemma expr_compat_val:
  forall (G : TypeEnv) (v : value) (t : Pacing),
    ExprTypeSem G (EVal v) t.
Proof.
  easy.
Qed.

(** The typing rule for direct accesses to input variables is sound *)
Lemma expr_compat_var_in:
  forall (G : TypeEnv) (x : IN) (t : Pacing),
    PacingEnt t (PVar x) ->
    ExprTypeSem G (EVar (Varin x)) t.
Proof.
  intros G x t H1 rin rout H2 n H3.
  specialize (H1 rin n H3).
  unfold PartialExprSem. simpl in *.
  unfold sync.
  destruct (rin x n); try easy.
Qed.

(** The typing rule for direct accesses to output variables is sound *)
Lemma expr_compat_var_out:
  forall (G : TypeEnv) (x : OUT) (tcan tmust : Pacing),
    G x = Some tcan ->
    PacingEnt tmust tcan ->
    ExprTypeSem G (EVar (Varout x)) tmust.
Proof.
  intros G x tcan tmust H1 H2 rin rout [[H3_1 H3_2] H3_3] n H4.
  specialize (H2 rin n H4).
  specialize (H3_2 _ _ H1) as (w & Hw).
  specialize (H3_3 x _ w H1 Hw n) as [H3_3 H3_4].
  specialize (H3_3 H2).
  unfold PartialExprSem.
  simpl in *. unfold sync.
  rewrite Hw.
  now destruct (w n).
Qed.

(** The typing rule for binary operators is sound *)
Lemma expr_compat_binop:
  forall (G : TypeEnv) f (e1 e2 : Expr) (t : Pacing),
    ExprTypeSem G e1 t ->
    ExprTypeSem G e2 t ->
    ExprTypeSem G (EBinOp f e1 e2) t.
Proof.
  intros G f e1 e2 t He1 He2 rin rout H1 n H2.
  specialize (He1 rin rout H1 n H2).
  specialize (He2 rin rout H1 n H2).
  simpl.
  now destruct (PartialExprSem e1), (PartialExprSem e2).
Qed.

(* The typing rule for previous accesses to output variables is sound *)
Lemma expr_compat_prev_out:
  forall (G : TypeEnv) (x : OUT) (e : Expr) (tcan tmust : Pacing),
    G x = Some tcan ->
    PacingEnt tmust tcan ->
    ExprTypeSem G e tmust ->
    ExprTypeSem G (EPrev (Varout x) e) tmust.
Proof.
  intros G x e tcan tmust Hx Hent He rin rout H1 n H2.
  specialize (He rin rout H1 n H2).
  destruct H1 as [[_ H1] H1'].
  specialize (H1 x _ Hx) as (w & Hw).
  apply Hent in H2. simpl in *.
  rewrite Hw. unfold prev.
  destruct (w n) eqn:Heq, n.
  - apply He.
  - destruct last; try easy.
  - exfalso. eapply H1'; eauto.
  - exfalso. eapply H1'; eauto.
Qed.

(* The typing rule for previous accesses to input variables is sound *)
Lemma expr_compat_prev_in:
  forall (G : TypeEnv) (x : IN) (e : Expr) (tmust : Pacing),
    PacingEnt tmust (PVar x) ->
    ExprTypeSem G e tmust ->
    ExprTypeSem G (EPrev (Varin x) e) tmust.
Proof.
  intros G x e tmust Hent He rin rout H1 n H2.
  specialize (He rin rout H1 n H2).
  apply Hent in H2. simpl in *.
  unfold prev.
  destruct (rin x n) eqn:Heq, n; try easy.
  destruct last; try easy.
Qed.

(* The typing rule for hold accesses to output variables is sound *)
Lemma expr_compat_hold_out:
  forall (G : TypeEnv) (x : OUT) (e : Expr) (tmust : Pacing),
    G x <> None ->
    ExprTypeSem G e tmust ->
    ExprTypeSem G (EHold (Varout x) e) tmust.
Proof.
  intros G x e tmust Hx He rin rout H1 n H2.
  specialize (He rin rout H1 n H2).
  destruct H1 as [[_ H1] _].
  specialize (H1 x). destruct (G x) as [t|]; try easy.
  specialize (H1 _ eq_refl) as (w & Hw).
  simpl. rewrite Hw.
  unfold hold. now destruct last.
Qed.

(* The typing rule for hold accesses to input variables is sound *)
Lemma expr_compat_hold_in:
  forall (G : TypeEnv) (x : IN) (e : Expr) (tmust : Pacing),
    ExprTypeSem G e tmust ->
    ExprTypeSem G (EHold (Varin x) e) tmust.
Proof.
  intros G x e tmust He rin rout H1 n H2.
  specialize (He rin rout H1 n H2).
  simpl. unfold hold. now destruct last.
Qed.

(**
  The typing rules for expressions are sound with respect to semantic typing
*)
Corollary expr_type_sound:
  forall (G : TypeEnv) (e : Expr) (t : Pacing),
    ExprTypeSyn G e t -> ExprTypeSem G e t.
Proof.
  intros G e t Ht.
  induction Ht.
  - apply expr_compat_val.
  - now apply expr_compat_binop.
  - eapply expr_compat_var_out; eauto.
  - now apply expr_compat_var_in.
  - now apply expr_compat_hold_out.
  - now apply expr_compat_hold_in.
  - eapply expr_compat_prev_out; eauto.
  - now eapply expr_compat_prev_in.
Qed.

(** ** Soundness of the type system for specifications *)

(** The partial semantics is less-defined than the total semantics *)
Lemma PartialExprSem_less_def:
  forall e rin rout1 rout2 n,
    PartialExprSem e rin rout1 n <= ExprSem e (rin, merge rout1 rout2) n.
Proof.
  induction e; intros *.
  - destruct x; simpl.
    + now destruct sync.
    + unfold merge.
      destruct (rout1 s); simpl; auto.
      now destruct sync.
  - reflexivity.
  - destruct x.
    + simpl. now apply prev_less_def.
    + simpl. unfold merge at 1.
      destruct (rout1 s) as [w |]; simpl; auto.
      now apply prev_less_def.
  - destruct x; simpl.
    + now apply hold_less_def.
    + unfold merge at 1.
      destruct (rout1 s) as [w |]; simpl; auto.
      now apply hold_less_def.
  - specialize (IHe1 rin rout1 rout2 n).
    specialize (IHe2 rin rout1 rout2 n).
    simpl. now rewrite IHe1, IHe2.
Qed.

(** Construct a [t]-paced stream out of a [t]-paced expressions *)
Definition witness rin rout e t : stream :=
  fun n =>
    if PacingSemBool rin t n then
      PartialExprSem e rin rout n
    else None.

(**
  Updating a well-paced partial output map with a well-paced stream
  gives a well-paced partial output map.
*)
Lemma EnvRel_update:
  forall G t rin rout x e,
    G x = None ->
    EnvRel G rin rout ->
    ExprRel G t rin e ->
    EnvRel (update G x t) rin (pextend rout x (witness rin rout e t)).
Proof.
  intros G t rin rout x e Hx H1 He.
  specialize (He rout H1).
  split.
  - destruct H1 as [[H1 H2] H3].
    split.
    + intros y Hy.
      unfold update in Hy.
      unfold pextend.
      destruct OUT_dec; subst; try easy.
      now apply H1.
    + intros y ty Hy.
      unfold update in Hy.
      unfold pextend. destruct OUT_dec; subst.
      injection Hy as ->. now eexists _.
      eapply H2; eauto.
  - intros y ty w Hy Heq.
    unfold update in Hy.
    unfold pextend in Heq.
    destruct OUT_dec; subst.
    + injection Hy as ->.
      injection Heq as <-.
      intros n. split.
      * intros Hn. specialize (He n Hn).
        unfold witness.
        apply PacingSemBool_true_iff in Hn.
        rewrite Hn.
        now destruct PartialExprSem.
      * intros Hwit. unfold witness in Hwit.
        destruct (PacingSemBool rin ty n) eqn:Heq; try easy.
        now apply PacingSemBool_true_iff in Heq.
    + destruct H1 as [[_ H2] H3].
      apply (H3 _ _ _ Hy Heq).
Qed.

(** The typing rule for empty lists of equations is sound *)
Lemma spec_compat_nil:
  forall G, SpecTypeSem G nil.
Proof.
  intros G rin rout1 H1.
  exists (fun _ _ => None).
  constructor.
Qed.

(** The typing rule for non-empty lists of equations is sound *)
Lemma spec_compat_cons:
  forall G s x e t,
    G x = None ->
    ExprTypeSem G e t ->
    SpecTypeSem (update G x t) s ->
    SpecTypeSem G ((x, t, e)::s).
Proof.
  intros G s x e t Hx He Hs rin rout1 H1.
  pose proof (He' := He rin rout1 H1).
  specialize (Hs rin (pextend rout1 x (witness rin rout1 e t))) as [rout2 Hrout2].
  - now apply EnvRel_update.
  - assert (Hx' : rout1 x = None).
    now apply H1.
    rewrite merge_pextend in Hrout2; auto.
    eexists. constructor; cycle 1.
    apply Hrout2. intros n. split.
  + unfold merge at 1, extend at 1.
    rewrite Hx'.
    destruct OUT_dec; try easy. clear e0.
    (* specialize (He' n Hn). *)
    unfold witness at 1.
    destruct (PacingSemBool rin t n) eqn:Ht; try easy.
    apply PartialExprSem_less_def.
  + unfold merge, extend. rewrite Hx'.
    destruct OUT_dec as [_|]; try easy.
    unfold witness. split; intros Hn.
    * specialize (He' _ Hn).
      apply PacingSemBool_true_iff in Hn.
      now rewrite Hn.
    * destruct PacingSemBool eqn:Ht; try easy.
      now apply PacingSemBool_true_iff.
Qed.

(** The typing rules for equations are sound with respect to semantic typing *)
Corollary spec_type_sound:
  forall (G : TypeEnv) (s : Spec),
    SpecTypeSyn G s -> SpecTypeSem G s.
Proof.
  induction 1.
  - apply spec_compat_nil.
  - apply expr_type_sound in H0.
    apply spec_compat_cons; auto.
Qed.

(** Well typed specifications are consistent *)
Corollary type_soundness:
  forall s,
    SpecTypeSyn bot_tenv s -> Consistent s.
Proof.
  intros s Hs.
  apply adequacy.
  now apply spec_type_sound.
Qed.