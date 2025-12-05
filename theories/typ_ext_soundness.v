From minilola Require Import lang sem opt typ typ_soundness typ_ext.
From Coq Require Import FunctionalExtensionality Lia Sorting.Permutation.

(** * Soundness Proof of the Pacing Type System *)

(** ** Preliminary Definitions *)

(** Compute the last defined value in a finite stream prefix *)
Fixpoint plast (w : list (option value)) :=
  match w with
  | [] => None
  | Some vx::w => Some vx
  | None::w => plast w
  end.

(**
  Semantic of expressions under partial output maps
  and knowing a prefix [vx] for output stream [x].
*)
Fixpoint PartialExprSem (x : OUT) (vx : list (option value)) (e : Expr) (rin : InMap) (rout : Pmap) (n : nat) : option value :=
  match e with
  | EVar (Varin y) => sync (rin y) n
  | EVar (Varout y) =>
    if OUT_dec x y then None
    else
      match rout y with
      | None => None
      | Some w => sync w n
      end
  | EVal v => Some v
  | EPrev (Varin y) e => prev (rin y) n (PartialExprSem x vx e rin rout n)
  | EPrev (Varout y) e =>
    if OUT_dec x y then
      match plast vx with
      | None => (PartialExprSem x vx e rin rout n)
      | Some vx => Some vx
      end
    else
      match rout y with
      | None => None
      | Some w => prev w n (PartialExprSem x vx e rin rout n)
      end
  | EHold (Varin y) e => hold (rin y) n (PartialExprSem x vx e rin rout n)
  | EHold (Varout y) e =>
    if OUT_dec x y then None
    else
      match rout y with
      | None => None
      | Some w => hold w n (PartialExprSem x vx e rin rout n)
      end
  | EBinOp f e1 e2 => binop f (PartialExprSem x vx e1 rin rout n) (PartialExprSem x vx e2 rin rout n)
  end.

(**
  Interpretation of typing environements as sets of stream expressions
*)
Definition ExprRel (G : TypeEnv) (x : OUT) (t : Pacing) (rin : InMap) (e : Expr) : Prop :=
  forall rout, EnvRel G rin rout ->
  forall n vx,
    PacingSem rin t n ->
    PartialExprSem x vx e rin rout n <> None.

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
Definition ExprTypeSem (G : TypeEnv) (x : OUT) (e : Expr) (t : Pacing) :=
  forall rin, ExprRel G x t rin e.

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

(** ** Soundness of the type system for expressions *)

Lemma expr_compat_val:
  forall (G : TypeEnv) x (v : value) (t : Pacing),
    ExprTypeSem G x (EVal v) t.
Proof.
  easy.
Qed.

Lemma expr_compat_var_in:
  forall (G : TypeEnv) x (y : IN) (t : Pacing),
    PacingEnt t (PVar y) ->
    ExprTypeSem G x (EVar (Varin y)) t.
Proof.
  intros G x y t H1 rin rout H2 n vx H3. simpl.
  now specialize (H1 rin n H3).
Qed.

Lemma expr_compat_var_out:
  forall (G : TypeEnv) (x : OUT) (y : OUT) (tcan tmust : Pacing),
    x <> y ->
    G y = Some tcan ->
    PacingEnt tmust tcan ->
    ExprTypeSem G x (EVar (Varout y)) tmust.
Proof.
  intros G x y tcan tmust Hneq H1 H2 rin rout [[H3_1 H3_2] H3_3] n vx H4; simpl.
  destruct (OUT_dec x y) as [Heq | Hne]; try easy.
  specialize (H2 rin n H4).
  specialize (H3_2 _ _ H1) as (w' & Hw').
  specialize (H3_3 y _ w' H1 Hw' n) as [H3_3 _].
  specialize (H3_3 H2).
  unfold sync, merge.
  now rewrite Hw'.
Qed.

Lemma expr_compat_add:
  forall (G : TypeEnv) x f (e1 e2 : Expr) (t : Pacing),
    ExprTypeSem G x e1 t ->
    ExprTypeSem G x e2 t ->
    ExprTypeSem G x (EBinOp f e1 e2) t.
Proof.
  intros G x f e1 e2 t He1 He2 rin rout H1 n vx H2.
  specialize (He1 rin rout H1 n vx H2).
  specialize (He2 rin rout H1 n vx H2).
  simpl.
  destruct (PartialExprSem _ _ e1); try easy.
  destruct (PartialExprSem _ _ e2); try easy.
Qed.

Lemma expr_compat_prev_out:
  forall (G : TypeEnv) (x : OUT) (y : OUT) (e : Expr) (tcan tmust : Pacing),
    x <> y ->
    G y = Some tcan ->
    PacingEnt tmust tcan ->
    ExprTypeSem G x e tmust ->
    ExprTypeSem G x (EPrev (Varout y) e) tmust.
Proof.
  intros G x y e tcan tmust Hne Hy Hent He rin rout H1 n vx H2.
  specialize (He rin rout H1 n vx H2).
  destruct H1 as [[_ H1] H1'].
  specialize (H1 y _ Hy) as (w' & Hw').
  apply Hent in H2. simpl in *.
  destruct OUT_dec as [Heq | Hneq]; try easy.
  rewrite Hw'.
  unfold prev.
  destruct (w' n) eqn:Heq, n.
  - try easy.
  - destruct last; try easy.
  - exfalso. eapply H1'; eauto.
  - exfalso. eapply H1'; eauto.
Qed.

Lemma expr_compat_prev_self:
  forall (G : TypeEnv) (x : OUT) (e : Expr) (t : Pacing),
    G x = None ->
    ExprTypeSem G x e t ->
    ExprTypeSem G x (EPrev (Varout x) e) t.
Proof.
  intros G x e t Hx He rin rout H1 n vx H2.
  specialize (He rin rout H1 n vx H2).
  destruct H1 as [[H1_1 H1_2] H1_3].
  simpl. destruct OUT_dec; try easy.
  destruct (plast vx); try easy.
Qed.

Lemma expr_compat_prev_in:
  forall (G : TypeEnv) (x : OUT) (y : IN) (e : Expr) (tmust : Pacing),
    PacingEnt tmust (PVar y) ->
    ExprTypeSem G x e tmust ->
    ExprTypeSem G x (EPrev (Varin y) e) tmust.
Proof.
  intros G x y e tmust Hent He rin rout H1 n vx H2.
  specialize (He rin rout H1 n vx H2).
  apply Hent in H2. simpl in *.
  unfold prev.
  destruct (rin y n) eqn:Heq, n; try easy.
  destruct last; try easy.
Qed.

Lemma expr_compat_hold_out:
  forall (G : TypeEnv) (x : OUT) (y : OUT) (e : Expr) (tmust : Pacing),
    x <> y ->
    G y <> None ->
    ExprTypeSem G x e tmust ->
    ExprTypeSem G x (EHold (Varout y) e) tmust.
Proof.
  intros G x y e tmust Hne Hy He rin rout H1 n vx H2.
  specialize (He rin rout H1 n vx H2).
  destruct H1 as [[_ H1] _].
  specialize (H1 y). destruct (G y) as [t|]; try easy.
  specialize (H1 _ eq_refl) as (w' & Hw').
  simpl. destruct (OUT_dec); try easy.
  rewrite Hw'.
  unfold hold. now destruct last.
Qed.

Lemma expr_compat_hold_in:
  forall (G : TypeEnv) (x : OUT) (y : IN) (e : Expr) (tmust : Pacing),
    ExprTypeSem G x e tmust ->
    ExprTypeSem G x (EHold (Varin y) e) tmust.
Proof.
  intros G x y e tmust He rin rout H1 n vx H2.
  specialize (He rin rout H1 n vx H2).
  simpl. unfold hold. now destruct last.
Qed.

(**
  The typing rules for expressions are sound with respect to semantic typing
*)
Corollary expr_type_sound:
  forall (G : TypeEnv) (x : OUT) (e : Expr) (t : Pacing),
    ExprTypeSyn G x e t -> ExprTypeSem G x e t.
Proof.
  intros G x e t Ht.
  induction Ht.
  - apply expr_compat_val.
  - now apply expr_compat_add.
  - eapply expr_compat_var_out; eauto.
  - now apply expr_compat_var_in.
  - now apply expr_compat_hold_out.
  - now apply expr_compat_hold_in.
  - eapply expr_compat_prev_out; eauto.
  - now eapply expr_compat_prev_in.
  - now eapply expr_compat_prev_self.
Qed.

(** ** Soundness of the Type System for Specifications *)

Fixpoint witness_aux (rin : InMap) (rout : Pmap) (e : Expr) (x : OUT) (t : Pacing) (n : nat) : option value * list (option value) :=
  if PacingSemBool rin t n then
    match n with
    | 0 => (PartialExprSem x [] e rin rout 0, [])
    | S n =>
      let (vx, px) := witness_aux rin rout e x t n in
      (PartialExprSem x (vx::px) e rin rout (S n), vx::px)
    end
  else
    match n with
    | 0 => (None, [])
    | S n =>
      let (vx, px) := witness_aux rin rout e x t n in
      (None, vx::px)
    end.

Definition witness rin rout e x t n : option value := fst (witness_aux rin rout e x t n).

Lemma witness_aux_length:
  forall rin rout e x t n,
    length (snd (witness_aux rin rout e x t n)) = n.
Proof.
  induction n as [ | n IH ]; simpl.
  - destruct PacingSemBool; try easy.
  - destruct witness_aux as [v w]; simpl in *.
    destruct PacingSemBool; simpl; congruence.
Qed.

Lemma EnvRel_update:
  forall G t rin rout x e,
    G x = None ->
    EnvRel G rin rout ->
    ExprRel G x t rin e ->
    EnvRel (update G x t) rin (pextend rout x (witness rin rout e x t)).
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
      intros n.
      induction n as [|n IH].
      * split; intros Hn.
      ** unfold witness, witness_aux.
        apply PacingSemBool_true_iff in Hn.
        rewrite Hn.
        apply He.
        now apply PacingSemBool_true_iff.
      ** unfold witness, witness_aux in Hn.
        apply PacingSemBool_true_iff.
        now destruct PacingSemBool.
      * split; intros Hn.
      ** unfold witness. simpl.
        apply PacingSemBool_true_iff in Hn.
        rewrite Hn. destruct witness_aux. simpl.
        apply He.
        now apply PacingSemBool_true_iff.
      ** unfold witness in Hn. simpl in Hn.
        apply PacingSemBool_true_iff.
        destruct PacingSemBool; auto.
        now destruct witness_aux.
    + eapply H1; eauto.
Qed.

Lemma spec_compat_nil:
  forall G, SpecTypeSem G nil.
Proof.
  intros G rin rout1 H1.
  exists (fun _ _ => None).
  constructor.
Qed.

Lemma plast_helper_1:
  forall vx,
    exists n, plast vx = nth n vx None.
Proof.
  induction vx as [ | [x|] vx [n IH] ]; simpl.
  - now exists 0.
  - now exists 0.
  - now exists (S n).
Qed.

Fixpoint is_prefix (vx : list (option value)) (w : stream) : Prop :=
  match vx with
  | [] => True
  | v::vx => is_prefix vx w /\ v = w (length vx)
  end.

Lemma is_prefix_helper_1:
  forall v vx w,
    is_prefix (v::vx) w ->
    plast (v::vx) <= last w (length vx).
Proof.
  intros v vx w [H1 ->].
  induction vx as [ | v vx IH ]; simpl in *; auto.
  - reflexivity.
  - destruct (w (S _)); try easy.
    destruct H1 as [H1 ->].
    now apply IH.
Qed.

Lemma is_prefix_helper_2:
  forall px w,
    is_prefix (None::px) w ->
    plast px = None ->
    last w (length px) = None.
Proof.
  intros * H1 H2. simpl in *.
  destruct H1 as [H1 H1'].
  induction px; simpl in *; try easy.
  - now rewrite <- H1'.
  - destruct H1 as [H1 ->].
    rewrite <- H1'.
    apply IHpx; auto.
    destruct (w (length px)); try easy.
    destruct (w (length px)); try easy.
Qed.

Lemma PartialExprSem_less_def:
  forall rin rout rout' x px,
    rout x = None ->
    is_prefix px (rout' x) ->
    rout' x (length px) <> None ->
    forall e,
      PartialExprSem x px e rin rout (length px) <=
      ExprSem e (rin, merge rout rout') (length px).
Proof.
  intros * H1 H2 H3 e. induction e as [ [y|y] | | [y|y] | [y|y] | ]; simpl; auto; try easy.
  - destruct OUT_dec as [Heq | Hne]; try easy.
    unfold merge. now destruct (rout y).
  - now apply prev_less_def.
  - destruct OUT_dec as [-> | Hne]; try easy.
    + unfold merge at 1. rewrite H1.
      destruct px as [ | [vx|] px ].
      * unfold prev. now destruct rout'.
      * apply is_prefix_helper_1 in H2.
        unfold prev. simpl in *.
        destruct rout'; try easy.
        now destruct last.
      * pose proof (H4 := H2).
        apply is_prefix_helper_1 in H4. simpl in H4 |-*.
        destruct plast eqn:Hlast. unfold prev.
        destruct rout'; try easy.
        destruct last; try easy.
        unfold prev. destruct rout'; try easy.
        eapply is_prefix_helper_2 in Hlast; eauto.
        now rewrite Hlast.
    + unfold merge at 1.
      destruct (rout y); try easy.
      now apply prev_less_def.
  - now apply hold_less_def.
  - destruct OUT_dec as [-> | Hne]; try easy.
    destruct (rout y) as [w|] eqn:Hw; try easy.
    unfold merge at 1. rewrite Hw.
    now apply hold_less_def.
  - now rewrite IHe1, IHe2.
Qed.

Lemma is_prefix_witness:
  forall rin rout e x t n,
    is_prefix (snd (witness_aux rin rout e x t n)) (witness rin rout e x t).
Proof.
  induction n; simpl.
  - now destruct PacingSemBool.
  - destruct PacingSemBool.
    destruct witness_aux eqn:Heq; simpl in *. split; auto.
    unfold witness.
    pose proof (Hl := witness_aux_length rin rout e x t n).
    rewrite Heq in Hl. simpl in Hl. rewrite Hl.
    now rewrite Heq.
    pose proof (Hl := witness_aux_length rin rout e x t n).
    destruct witness_aux eqn:Heq; simpl in *. split; auto.
    unfold witness. now rewrite Hl, Heq.
Qed.

Lemma witness_is_some:
  forall rin rout e x t,
    (forall n vx, PacingSem rin t n -> PartialExprSem x vx e rin rout n <> None) ->
    forall n,
      (PacingSemBool rin t n = true -> witness rin rout e x t n <> None) /\
      (PacingSemBool rin t n = false -> witness rin rout e x t n = None).
Proof.
  intros * H1 n.
  induction n as [ | n [IH1 IH2] ]; split; intros Hn.
  - unfold witness, witness_aux.
    rewrite Hn. simpl. apply H1.
    now apply PacingSemBool_true_iff.
  - unfold witness, witness_aux.
    now rewrite Hn.
  - unfold witness. simpl.
    rewrite Hn.
    destruct witness_aux. simpl.
    apply H1.
    now apply PacingSemBool_true_iff.
  - unfold witness. simpl.
    rewrite Hn.
    now destruct witness_aux.
Qed.

Lemma EqSem_iff:
  forall x t e rin rout,
    (forall n, PacingSem rin t n -> rout x n <= ExprSem e (rin, rout) n) ->
    (forall n, PacingSem rin t n <-> rout x n <> None) ->
    EqSem (x, t, e) (rin, rout).
Proof.
  intros * H1 H2 n.
  specialize (H1 n).
  specialize (H2 n).
  destruct (PacingSemBool rin t n) eqn:Ht.
  - apply PacingSemBool_true_iff in Ht.
    split.
    + now apply H1.
    + apply H2.
  - pose proof H2 as [H3 H4].
    split.
    + destruct (rout x n); try easy.
      apply H1.
      now apply H4.
    + apply H2.
Qed.

Lemma witness_partial_sem:
  forall rin rout e x t,
    (forall n p, PacingSem rin t n -> PartialExprSem x p e rin rout n <> None) ->
    forall n vn p,
    witness_aux rin rout e x t n = (vn, p) ->
    if PacingSemBool rin t n then
      vn <> None /\
      vn <= PartialExprSem x p e rin rout n
    else
      vn = None.
Proof.
  intros * H n vn p Hwit.
  destruct n; simpl in Hwit.
  - destruct PacingSemBool eqn:Ht; [split|].
  + injection Hwit as <- <-.
    apply H.
    now apply PacingSemBool_true_iff.
  + now injection Hwit as <- <-.
  + now injection Hwit as <- <-.
  - destruct PacingSemBool eqn:Ht; [split|].
  + destruct witness_aux as [o l].
    injection Hwit as <- <-.
    apply H.
    now apply PacingSemBool_true_iff.
  + destruct witness_aux as [o l].
    injection Hwit as <- <-. simpl.
    reflexivity.
  + destruct witness_aux as [o l].
    now injection Hwit as <- <-.
Qed.

Lemma spec_compat_cons:
  forall G s x e t,
    G x = None ->
    ExprTypeSem G x e t ->
    SpecTypeSem (update G x t) s ->
    SpecTypeSem G ((x, t, e)::s).
Proof.
  intros G s x e t Hx He Hs rin rout1 H1.
  pose proof (He' := He rin rout1 H1).
  specialize (Hs rin (pextend rout1 x (witness rin rout1 e x t))) as [rout2 Hrout2].
  - now apply EnvRel_update.
  - assert (Hx' : rout1 x = None).
    now apply H1.
    rewrite merge_pextend in Hrout2; auto.
    eexists. constructor; cycle 1.
    apply Hrout2. apply EqSem_iff.
  + intros n Ht.
    unfold merge at 1, extend at 1.
    rewrite Hx'. destruct OUT_dec; try easy. clear e0.
    pose proof (Hn := witness_aux_length rin rout1 e x t n).
    rewrite <- Hn. etransitivity; cycle 1.
    * apply PartialExprSem_less_def; eauto.
      unfold extend. destruct OUT_dec as [_|]; try easy.
      apply is_prefix_witness.
      unfold extend. destruct OUT_dec as [_|]; try easy.
      rewrite witness_aux_length.
      eapply witness_is_some in He' as [He1 He2].
      apply He1.
      now apply PacingSemBool_true_iff.
    * rewrite witness_aux_length.
      pose proof (witness_partial_sem _ _ _ _ _ He' n).
      unfold witness.
      destruct witness_aux as [o l]. simpl in *.
      specialize (H _ _ eq_refl).
      apply PacingSemBool_true_iff in Ht.
      rewrite Ht in H.
      destruct H as [_ H].
      now rewrite H.
  + intros n.
    pose proof (witness_partial_sem _ _ _ _ _ He' n).
    split; intros Hn.
    * unfold merge. rewrite Hx'.
      unfold extend. destruct OUT_dec; try easy.
      unfold witness.
      destruct witness_aux eqn:Hwit.
      specialize (H _ _ eq_refl); simpl.
      apply PacingSemBool_true_iff in Hn.
      now rewrite Hn in H.
    * unfold merge in Hn.
      rewrite Hx' in Hn.
      unfold extend in Hn.
      destruct OUT_dec; try easy.
      unfold witness in Hn.
      destruct witness_aux eqn:Hwit; simpl in *.
      specialize (H _ _ eq_refl).
      destruct PacingSemBool eqn:Ht.
      now apply PacingSemBool_true_iff.
      now rewrite H in Hn.
Qed.

Lemma spec_compat_reorder:
  forall G (s1 s2 : Spec),
    Permutation s1 s2 ->
    SpecTypeSem G s1 ->
    SpecTypeSem G s2.
Proof.
  intros G s1 s2 Hperm Htype rin rout1 HG.
  specialize (Htype rin rout1 HG) as [rout2 Hsem].
  exists rout2.
  eapply Sem_Permut; eauto.
Qed.

Corollary spec_type_sound:
  forall (G : TypeEnv) (s : Spec),
    SpecTypeSyn G s -> SpecTypeSem G s.
Proof.
  induction 1.
  - apply spec_compat_nil.
  - eapply spec_compat_reorder.
    apply Permutation_sym; eauto.
    auto.
  - apply expr_type_sound in H0.
    apply spec_compat_cons; auto.
Qed.

Lemma type_soundness:
  forall s,
    SpecTypeSyn bot_tenv s -> Consistent s.
Proof.
  intros s Hs.
  apply adequacy.
  now apply spec_type_sound.
Qed.