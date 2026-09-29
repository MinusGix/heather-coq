(** * Validity of δ (M9: bodied globals, M9_DESIGN.md)

    A defined global [gdef u t d] weak-head reduces to its body's instance
    [t[d]] at the computing layers.  So its validity is anti-reduction
    along that step, from the validity of the instance; the instance's
    validity comes from the body's (N1), instantiated at the related local
    substitutions.  Under related global substitutions a definition goes
    to the same definition on both sides (GObjRel). *)
From DeLaM.Validity Require Export GvarS.
From DeLaM.Typing Require Import Inversion.

#[local] Existing Instance LR_P.

(** ** Locally, and under global weakenings *)

Section DeltaG.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Lemma tmred_delta {G Γ x b e0 A l} : [ G ; Γ ⊢g gdef x b e0 : A @ l ] ->
  [ G ; Γ ⊢g gdef x b e0 ⤳* b[e0] : A @ l ].
Proof.
  intros H. split; [exact H | econstructor; [constructor | constructor] |].
  destruct (inv_gdef ge_typeof H) as (Δ & T0 & l0 & t0 & (HΓ & Hin & Hl & Hi & Ht & Hn & He & Hb) & Hk & HT).
  eapply eqtm_conv; [| rewrite ge_typeof; exact HT].
  destruct Hk as [-> | Hk]; [| eapply eqtm_lconv; [| exact Hk]];
    (eapply eqtm_delta; [exact ge_compt | exact HΓ | exact Hin | exact Hl | exact Ht | exact Hn | exact He | exact Hb]).
Qed.

(** The occurrence under a global weakening and a local substitution. *)
Lemma gdef_inst {G G' γ Γ Θ x b e0 e A l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢g gdef x b e0 : A @ l ] -> [ G' ; Θ ⊢[ ge_layer ] e : Γ⟦γ⟧ ] ->
  [ G' ; Θ ⊢g (gdef x b e0)⟦γ⟧[e] ⤳* (b[e0])⟦γ⟧[e] : A⟦γ⟧[e] @ l ].
Proof.
  intros Hγ HG Ht He.
  pose proof (wf_tm_subst_g (gwa_tm Hγ HG Ht) He) as X.
  rewrite gwa_gdef in X |- *. rewrite gwa_subst, subst_comp.
  exact (tmred_delta X).
Qed.

Lemma VTmG_delta_l {G Γ x b e0 w' A l} : [ G ; Γ ⊢g gdef x b e0 : A @ l ] ->
  VTmG G Γ b[e0] w' A l -> VTmG G Γ (gdef x b e0) w' A l.
Proof.
  intros Ht X G' γ Hγ Θ e e' He.
  pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG.
  eapply LRtm_red_l; [exact (X _ _ Hγ _ _ _ He) |].
  exact (gdef_inst Hγ HG Ht (SubRel_wf_l _ _ _ _ _ He)).
Qed.

Lemma VTmG_delta {G Γ x x' b b' e0 e0' A l} :
  [ G ; Γ ⊢g gdef x b e0 : A @ l ] -> [ G ; Γ ⊢g gdef x' b' e0' : A @ l ] ->
  VTmG G Γ b[e0] b'[e0'] A l -> VTmG G Γ (gdef x b e0) (gdef x' b' e0') A l.
Proof.
  intros Ht Ht' X G' γ Hγ Θ e e' He.
  pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG.
  eapply LRtm_red; [exact (X _ _ Hγ _ _ _ He) | exact (gdef_inst Hγ HG Ht (SubRel_wf_l _ _ _ _ _ He)) |].
  (* the right side, at the right substitution *)
  exact (gdef_inst Hγ HG Ht' (SubRel_wf_r He)).
Qed.

End DeltaG.

(** ** With global substitutions *)

Section DeltaS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxS := (@VCtxS EP EM E LP).
Local Notation VTyS := (@VTyS EP EM E LP).
Local Notation VTmS := (@VTmS EP EM E LP).

(** Related substitutions send a definition to the same definition. *)
Lemma gdef_gsubst {G' G σ σ' u Δ T l t0} : GSubRel G' G σ σ' -> in_gctx (gΨ G) u (gdDef Δ T l t0) ->
  exists x, σ u = GId x /\ σ' u = GId x.
Proof.
  intros Hσ Hin. pose proof (gsr_rel _ _ _ _ _ _ Hσ _ _ Hin) as R. cbn in R.
  destruct (σ u) as [x | | |], (σ' u) as [x' | | |]; cbn in R; try contradiction. subst x'. eauto.
Qed.

(** A term's validity at related local substitutions. *)
Lemma VTmS_inst {i0 G Γ Δ t t' A d d' l} : [ G ; Γ ⊢[ i0 ] ] -> [ G ; Δ ⊢[ lD ] ] -> VCtxS G Δ ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n B k, in_ctx Δ n B k -> VTmS G Γ (llk d n) (llk d' n) B[d] k) ->
  (forall n B k, in_ctx Δ n B k -> VTmS G Γ (llk d n) (llk d n) B[d] k) ->
  VTyS G Δ A A l -> VTmS G Δ t t' A l -> VTmS G Γ t[d] t'[d'] A[d] l.
Proof.
  intros HΓ HΔ VΔ Ht Nd Ht' Nd' Hv Hvv VA Vt G' σ σ' Hσ. rewrite !gsubst_subst, gsubst_subst_ty.
  exact (VTmG_inst (Vt _ _ _ Hσ) (VA _ _ _ (GSubRel_refl_l _ _ Hσ))
           (VSubKS EP EM HΓ HΔ VΔ Ht Nd Ht' Nd' Hv _ _ _ Hσ)
           (VSubKS EP EM HΓ HΔ VΔ Ht Nd Ht Nd Hvv _ _ _ (GSubRel_refl_l _ _ Hσ))).
Qed.

(** δ: the occurrence against its body's instance. *)
Lemma VS_delta {G Γ u Δ T l t0 t d A} : in_gctx (gΨ G) u (gdDef Δ T l t0) ->
  [ G ; Γ ⊢g gdef u t d : A @ l ] -> VTmS G Γ t[d] t[d] A l -> VTmS G Γ (gdef u t d) t[d] A l.
Proof.
  intros Hin Ht V G' σ σ' Hσ. destruct (gdef_gsubst Hσ Hin) as (x & E1 & _).
  pose proof (V _ _ _ Hσ) as X. pose proof (gs_tm EP EM Hσ Ht) as Y.
  cbn [gsubst GSubst_tm gsubst_tm] in Y |- *. rewrite E1 in Y |- *. cbn [pdef] in Y |- *.
  rewrite gsubst_subst in X. exact (VTmG_delta_l Y X).
Qed.

End DeltaS.
