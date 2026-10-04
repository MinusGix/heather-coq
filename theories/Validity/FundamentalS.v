(** * The fundamental theorem with global substitutions, layer P

    Every P-derivation is valid at related global substitutions, at the P
    and the M instance ([⊩^{≥P}_P]), together with its context (and, for
    terms, its type).  Each case is one of the rule lemmas of [RulesS], a
    PER/conversion lemma of [ValidS], or a context lemma.  Well-formed
    global contexts are semantic ([GValid]), which gives the validity of
    the global variables' bindings. *)
From DeLaM.Validity Require Export Delta.

#[local] Existing Instance LR_P.

Section FundamentalS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation GValid := (GValid EP EM).

(** ** The judgments' semantics *)

Section Sem.
Context {E : GenericEq}.
Definition SemCtx (G : gctx) (Γ : ctx) : Prop :=
  GValid G /\ @VCtxS EP EM EP LR_P G Γ /\ @VCtxS EP EM EM LR_P G Γ.
Definition SemTy (G : gctx) (Γ : ctx) (T T' : ty) (l : lvl) : Prop :=
  SemCtx G Γ /\ @VTyS EP EM EP LR_P G Γ T T' l /\ @VTyS EP EM EM LR_P G Γ T T' l.
Definition SemTm (G : gctx) (Γ : ctx) (t t' : tm) (T : ty) (l : lvl) : Prop :=
  SemCtx G Γ /\ @VTyS EP EM EP LR_P G Γ T T l /\ @VTyS EP EM EM LR_P G Γ T T l /\
  @VTmS EP EM EP LR_P G Γ t t' T l /\ @VTmS EP EM EM LR_P G Γ t t' T l.
Definition SemCtxEq (G : gctx) (Γ Γ' : ctx) : Prop :=
  @VCtxEqS EP LR_P EP EM G Γ Γ' /\ @VCtxEqS EM LR_P EP EM G Γ Γ'.
End Sem.

(** ** Global variables *)

Lemma FS_tygvar {G Γ U Δ i' l d d'} : SemCtx G Γ -> in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' lD ->
  [ G ; Γ ⊢[ lD ] ] -> lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n B k, in_ctx Δ n B k -> SemTm G Γ (llk d n) (llk d' n) B[d] k) ->
  SemTy G Γ (tyGvar U d) (tyGvar U d') l.
Proof using ELM ELP.
  intros HS Hin Hi HΓ Ht Nd Ht' Nd' Hv. pose proof HS as (HG & _ & _).
  pose proof (in_gctx_DWf (ctx_glob _ _ _ HΓ) Hin) as HΔ; cbn in HΔ.
  destruct (HG _ _ Hin) as [VP VM].
  split; [exact HS | split].
  - exact (VS_tygvar EP EM (fun _ _ _ _ _ _ _ _ H => proj1 H) Hin (lle_trans _ _ _ Hi ge_lle_D) (lle_D_notM Hi) HΓ HΔ VP Ht Nd Ht' Nd'
             (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hv n B k h)))))).
  - exact (VS_tygvar EP EM (fun _ _ _ _ _ _ _ _ H => proj2 H) Hin (lle_trans _ _ _ Hi ge_lle_D) (lle_D_notM Hi) HΓ HΔ VM Ht Nd Ht' Nd'
             (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hv n B k h)))))).
Qed.

Lemma FS_gvar {G Γ u Δ i' A l d d'} : SemCtx G Γ -> in_gctx (gΨ G) u (gdTm Δ i' A l) -> lle i' lD ->
  [ G ; Γ ⊢[ lD ] ] -> lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n B k, in_ctx Δ n B k -> SemTm G Γ (llk d n) (llk d' n) B[d] k) ->
  (forall n B k, in_ctx Δ n B k -> SemTm G Γ (llk d n) (llk d n) B[d] k) ->
  SemTm G Γ (gvar u d) (gvar u d') A[d] l.
Proof using ELM ELP.
  intros HS Hin Hi HΓ Ht Nd Ht' Nd' Hv Hvv. pose proof HS as (HG & _ & _).
  pose proof (in_gctx_DWf (ctx_glob _ _ _ HΓ) Hin) as HT; cbn in HT.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HT) as HΔ.
  destruct (HG _ _ Hin) as (VP & VM & VAP & VAM).
  split; [exact HS | split; [| split; [| split]]].
  - exact (VTyS_inst EP EM HΓ HΔ VP Ht Nd Ht Nd
             (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hvv n B k h))))) VAP).
  - exact (VTyS_inst EP EM HΓ HΔ VM Ht Nd Ht Nd
             (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hvv n B k h))))) VAM).
  - exact (VS_gvar EP EM (fun _ _ _ _ _ _ _ _ H => proj1 H) Hin (lle_trans _ _ _ Hi ge_lle_D) HΓ HT VP VAP Ht Nd Ht' Nd'
             (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hv n B k h)))))
             (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hvv n B k h)))))).
  - exact (VS_gvar EP EM (fun _ _ _ _ _ _ _ _ H => proj2 H) Hin (lle_trans _ _ _ Hi ge_lle_D) HΓ HT VM VAM Ht Nd Ht' Nd'
             (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hv n B k h)))))
             (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hvv n B k h)))))).
Qed.

(** ** Defined globals (M9): δ, then the PER laws *)

Lemma FS_delta {G Γ u Δ T l t0 t d} : SemCtx G Γ -> in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t ->
  [ G ; Γ ⊢[ lD ] ] -> lsub_tail d Δ Γ -> dnfl d ->
  (forall n B k, in_ctx Δ n B k -> [ G ; Γ ⊢[ lD ] llk d n : B[d] @ k ]) ->
  (forall n B k, in_ctx Δ n B k -> SemTm G Γ (llk d n) (llk d n) B[d] k) ->
  [ G ; Δ ⊢[ lD ] t : T @ l ] -> SemTm G Δ t t T l ->
  SemTm G Γ (gdef u t d) t[d] T[d] l.
Proof using ELM ELP.
  intros HS Hin Hl HΓ Ht Nd He Hvv Hb Sb. pose proof HS as (HG & _ & _).
  pose proof (in_gctx_DWf (ctx_glob _ _ _ HΓ) Hin) as HT; cbn in HT.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HT) as HΔ.
  destruct (HG _ _ Hin) as (VP & VM & VAP & VAM).
  destruct Sb as (_ & _ & _ & VbP & VbM).
  assert (Hty : [ G ; Γ ⊢[ lD ] gdef u t d : T[d] @ l ])
    by (eapply wf_gdef; eauto; unfold lle; cbn; lia).
  split; [exact HS | split; [| split; [| split]]].
  - exact (VTyS_inst EP EM HΓ HΔ VP Ht Nd Ht Nd
             (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hvv n B k h))))) VAP).
  - exact (VTyS_inst EP EM HΓ HΔ VM Ht Nd Ht Nd
             (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hvv n B k h))))) VAM).
  - refine (VS_delta EP EM Hin (lift_tm Hty ge_lle_D) _).
    exact (VTmS_inst EP EM HΓ HΔ VP Ht Nd Ht Nd
             (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hvv n B k h)))))
             (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hvv n B k h))))) VAP VbP).
  - refine (VS_delta EP EM Hin (lift_tm Hty ge_lle_D) _).
    exact (VTmS_inst EP EM HΓ HΔ VM Ht Nd Ht Nd
             (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hvv n B k h)))))
             (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hvv n B k h))))) VAM VbM).
Qed.

Lemma FS_gdef {G Γ u Δ T l t0 t d} : SemCtx G Γ -> in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t ->
  [ G ; Γ ⊢[ lD ] ] -> lsub_tail d Δ Γ -> dnfl d ->
  (forall n B k, in_ctx Δ n B k -> [ G ; Γ ⊢[ lD ] llk d n : B[d] @ k ]) ->
  (forall n B k, in_ctx Δ n B k -> SemTm G Γ (llk d n) (llk d n) B[d] k) ->
  [ G ; Δ ⊢[ lD ] t : T @ l ] -> SemTm G Δ t t T l ->
  SemTm G Γ (gdef u t d) (gdef u t d) T[d] l.
Proof using ELM ELP.
  intros HS Hin Hl HΓ Ht Nd He Hvv Hb Sb. pose proof HS as (HG & VCP & VCM).
  destruct (FS_delta HS Hin Hl HΓ Ht Nd He Hvv Hb Sb) as (_ & VTP & VTM & XP & XM).
  split; [exact HS | split; [exact VTP | split; [exact VTM | split]]].
  - exact (VTmS_trans EP EM XP (VTmS_sym EP EM HG VCP VTP XP)).
  - exact (VTmS_trans EP EM XM (VTmS_sym EP EM HG VCM VTM XM)).
Qed.

Lemma FS_gdef_eq {G Γ u Δ T l t0 t t' d d'} : SemCtx G Γ -> in_gctx (gΨ G) u (gdDef Δ T l t0) ->
  tm_leq t0 t -> tm_leq t0 t' ->
  [ G ; Γ ⊢[ lD ] ] -> lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n B k, in_ctx Δ n B k -> [ G ; Γ ⊢[ lD ] llk d n : B[d] @ k ]) ->
  (forall n B k, in_ctx Δ n B k -> [ G ; Γ ⊢[ lD ] llk d' n : B[d'] @ k ]) ->
  (forall n B k, in_ctx Δ n B k -> SemTm G Γ (llk d n) (llk d n) B[d] k) ->
  (forall n B k, in_ctx Δ n B k -> SemTm G Γ (llk d' n) (llk d' n) B[d'] k) ->
  (forall n B k, in_ctx Δ n B k -> SemTm G Γ (llk d n) (llk d' n) B[d] k) ->
  [ G ; Δ ⊢[ lD ] t ≅ t' : T @ l ] -> SemTm G Δ t t' T l ->
  SemTm G Γ (gdef u t d) (gdef u t' d') T[d] l.
Proof using ELM ELP.
  intros HS Hin Hl Hl' HΓ Ht Nd Ht' Nd' He He' Hvv Hvv' Hv Hbb Sb. pose proof HS as (HG & VCP & VCM).
  pose proof (in_gctx_DWf (ctx_glob _ _ _ HΓ) Hin) as HT; cbn in HT.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HT) as HΔ.
  destruct (HG _ _ Hin) as (VP & VM & VAP & VAM).
  destruct Sb as (SΔ & VTbP & VTbM & VbP & VbM). pose proof SΔ as (_ & VΔP & VΔM).
  (* each body related to itself *)
  assert (Sl : SemTm G Δ t t T l).
  { refine (conj SΔ (conj VTbP (conj VTbM (conj _ _))));
      [exact (VTmS_trans EP EM VbP (VTmS_sym EP EM HG VΔP VTbP VbP))
      | exact (VTmS_trans EP EM VbM (VTmS_sym EP EM HG VΔM VTbM VbM))]. }
  assert (Sr : SemTm G Δ t' t' T l).
  { refine (conj SΔ (conj VTbP (conj VTbM (conj _ _))));
      [exact (VTmS_trans EP EM (VTmS_sym EP EM HG VΔP VTbP VbP) VbP)
      | exact (VTmS_trans EP EM (VTmS_sym EP EM HG VΔM VTbM VbM) VbM)]. }
  destruct (FS_delta HS Hin Hl HΓ Ht Nd He Hvv (eqtm_wf_l eq_refl Hbb) Sl) as (_ & VTP & VTM & XP & XM).
  destruct (FS_delta HS Hin Hl' HΓ Ht' Nd' He' Hvv' (eqtm_wf_r eq_refl Hbb) Sr) as (_ & VTP' & VTM' & YP & YM).
  split; [exact HS | split; [exact VTP | split; [exact VTM | split]]].
  - refine (VTmS_trans EP EM XP (VTmS_trans EP EM _ (VTmS_conv EP EM (VTmS_sym EP EM HG VCP VTP' YP) _))).
    + exact (VTmS_inst EP EM HΓ HΔ VP Ht Nd Ht' Nd'
               (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hv n B k h)))))
               (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hvv n B k h))))) VAP VbP).
    + exact (VTyS_inst EP EM HΓ HΔ VP Ht Nd Ht' Nd'
               (fun n B k h => proj1 (proj2 (proj2 (proj2 (Hv n B k h))))) VAP).
  - refine (VTmS_trans EP EM XM (VTmS_trans EP EM _ (VTmS_conv EP EM (VTmS_sym EP EM HG VCM VTM' YM) _))).
    + exact (VTmS_inst EP EM HΓ HΔ VM Ht Nd Ht' Nd'
               (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hv n B k h)))))
               (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hvv n B k h))))) VAM VbM).
    + exact (VTyS_inst EP EM HΓ HΔ VM Ht Nd Ht' Nd'
               (fun n B k h => proj2 (proj2 (proj2 (proj2 (Hv n B k h))))) VAM).
Qed.

(** ** Case tactic

    Every goal is closed by a named lemma applied with [simple eapply] (a
    plain [eapply] unfolds the validity definitions while searching for the
    arity, which is costly on large substituted terms). The rules come
    before the generic sym/trans/conv lemmas: those apply to any goal and
    fail slowly, while a rule fails at once on the wrong former. *)

Ltac f_lwf :=
  first [ eassumption | exact I | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption
        | progress cbn [lwf]; first [split; f_lwf | f_lwf] ].
Ltac f_side0 :=
  first [ eassumption | typeclasses eauto | apply lequiv_refl; f_lwf | apply lequiv_sym; eassumption | f_lwf
        | exact ge_lle_D | reflexivity ].
(** A type related to another is related to itself (the Σ congruences
    need the family's reflexive validity, M8). *)
Ltac f_side :=
  first [ f_side0 | solve [simple eapply VTyS_trans; [eassumption | simple eapply VTyS_sym; f_side0]]
        | solve [simple eapply VTmS_trans; [eassumption | simple eapply VTmS_sym; f_side0]] ].

(** Presupposed typings of left-hand sides and types. *)
Ltac f_types :=
  repeat match goal with
  | H : wf_tm ?G lD ?Γ ?t ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G lD Γ T l |- _ => fail
      | _ => pose proof (wf_tm_ty (i := lD) eq_refl H)
      end
  | H : eq_ty ?G lD ?Γ ?T ?T' ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G lD Γ T l |- _ => fail
      | _ => pose proof (eqty_wf_l (i := lD) eq_refl H)
      end
  | H : eq_tm ?G lD ?Γ ?t ?t' ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_tm G lD Γ t T l |- _ => fail
      | _ => pose proof (eqtm_wf_l (i := lD) eq_refl H)
      end
  end.

Ltac f_ctx :=
  first [ eassumption | apply VCtxS_nil
        | solve [simple eapply VCtxS_var;
                 first [exact (fun _ _ _ _ _ H => proj1 H) | exact (fun _ _ _ _ _ H => proj2 H) | f_side]]
        | solve [simple eapply VCtxS_tl; f_side]
        | solve [simple eapply VCtxS_ext; f_side] ].

Ltac f_rules := vs_rules f_side.

Ltac f_ty :=
  first
  [ eassumption
  | f_rules
  | solve [simple eapply VTyS_sym; f_side] | solve [simple eapply VTyS_trans; f_side]
  | solve [simple eapply VTyS_lconv; f_side]
  | solve [simple eapply VTyS_trans; [eassumption | simple eapply VTyS_sym; f_side]]
  | solve [simple eapply VTyS_trans; [simple eapply VTyS_sym; f_side | eassumption]]
  | solve [simple eapply VTyS_lookup; f_side]
  | solve [simple eapply VTyS_single; f_side]
  | solve [simple eapply VTyS_Jmot; f_side]
  | solve [simple eapply VTyS_single; [eassumption | f_rules]]
  | solve [simple eapply VTyS_single; [f_side | f_rules]]
  | solve [simple eapply VTyS_single;
           [ first [eassumption | simple eapply VTyS_trans; [eassumption | simple eapply VTyS_sym; f_side]]
           | first [eassumption | simple eapply VTmS_trans; [eassumption | simple eapply VTmS_sym; f_side]]]] ].

Ltac f_tm :=
  first
  [ eassumption
  | f_rules
  | solve [simple eapply VTmS_sym; f_side] | solve [simple eapply VTmS_trans; f_side]
  | solve [simple eapply VTmS_conv; f_side] | solve [simple eapply VTmS_lconv; f_side] ].

Ltac f_goal :=
  lazymatch goal with
  | |- GValid (mkG _ nil) => apply GValid_nil
  | |- GValid (mkG _ (_ :: _)) => apply GValid_ext; [assumption | cbn [DValid]; repeat split; assumption]
  | |- GValid _ => eassumption
  | |- @VCtxS _ _ _ _ _ _ => f_ctx
  | |- @VCtxEqS _ _ _ _ _ _ _ =>
      first [ apply VCtxEqS_nil
            | solve [simple eapply VCtxEqS_var;
                     first [exact (fun _ _ _ _ _ H => proj1 H) | exact (fun _ _ _ _ _ H => proj2 H) | f_side]]
            | solve [simple eapply VCtxEqS_ext; f_side] ]
  | |- @VTyS _ _ _ _ _ _ _ _ _ => f_ty
  | |- @VTmS _ _ _ _ _ _ _ _ _ _ => f_tm
  end.

(** ** The theorem *)

(** The validity judgments stay folded while the cases unify against the
    hypotheses: a failed [eassumption] otherwise retries with both sides
    unfolded (19 s → 6 s over the 775 goals). *)
Local Opaque VTyS VTmS VCtxS VCtxEqS.

Theorem fundamentalS :
  (forall G, [ ⊢ G ] -> GValid G) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> i = lD -> SemCtx G Γ) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> i = lD -> SemTy G Γ T T l) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> i = lD -> SemTm G Γ t t T l) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> i = lD -> SemTy G Γ T T' l) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> i = lD ->
     SemTm G Γ t t' T l) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> i = lD -> SemCtxEq G Γ Γ').
Proof using ELM ELP.
  apply typing_mut; intros; try exact I;
    try match goal with H : lM = lD |- _ => discriminate H end;
    ft_prep;
    repeat match goal with
      | IH : forall n A k, in_ctx _ n A k -> ?x = ?x -> _ |- _ =>
          pose proof (fun n A k h => IH n A k h eq_refl); clear IH
      end;
    try solve [ first [simple eapply FS_tygvar | simple eapply FS_gvar]; eassumption ];
    try solve [ first [simple eapply FS_gdef | simple eapply FS_gdef_eq | simple eapply FS_delta]; eassumption ];
    unfold SemTy, SemTm, SemCtxEq in *; unfold SemCtx in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    f_types;
    repeat split.
  all: f_goal.
Qed.

(** ** Layers below P (C, V): lift the derivation to P *)

Corollary fundamentalS_le :
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> lle i lD -> SemCtx G Γ) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> lle i lD -> SemTy G Γ T T l) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> lle i lD -> SemTm G Γ t t T l) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> lle i lD -> SemTy G Γ T T' l) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> lle i lD -> SemTm G Γ t t' T l).
Proof using ELM ELP.
  destruct fundamentalS as (_ & Hc & Hty & Htm & Heqty & Heqtm & _).
  split; [| split; [| split; [| split]]].
  - intros G i Γ Hd Hi. exact (Hc _ _ _ (lift_ctx Hd Hi) eq_refl).
  - intros G i Γ T l Hd Hi. exact (Hty _ _ _ _ _ (lift_ty Hd Hi) eq_refl).
  - intros G i Γ t T l Hd Hi. exact (Htm _ _ _ _ _ _ (lift_tm Hd Hi) eq_refl).
  - intros G i Γ T T' l Hd Hi. exact (Heqty _ _ _ _ _ _ (lift_eqty Hd Hi) eq_refl).
  - intros G i Γ t t' T l Hd Hi. exact (Heqtm _ _ _ _ _ _ _ (lift_eqtm Hd Hi) eq_refl).
Qed.

End FundamentalS.
