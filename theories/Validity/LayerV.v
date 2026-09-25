(** * Layering Restriction for validity

    On MLTT contexts and types, related substitutions, related types and
    terms, and validity (under global weakenings) do not depend on the
    relation's parameters. *)
From DeLaM.Validity Require Export Def.
From DeLaM.LogRel Require Export Layering.

Section LayerV.
Context `{E : GenericEq} (LP1 LP2 : LRParams).

Lemma LRty_layer {l G Γ T T'} : mltt_ty T -> mltt_ty T' ->
  (@LRty E LP1 l G Γ T T' <-> @LRty E LP2 l G Γ T T').
Proof.
  intros Hm Hm'; split; intros [R HR]; exists R; [apply (LogRel_layer LP1 LP2) | apply (LogRel_layer LP1 LP2)];
    assumption.
Qed.

Lemma LRtm_layer {l G Γ T T' t t'} : mltt_ty T -> mltt_ty T' ->
  (@LRtm E LP1 l G Γ T T' t t' <-> @LRtm E LP2 l G Γ T T' t t').
Proof.
  intros Hm Hm'; split; intros (R & HR & Ht); exists R; split; try exact Ht;
    [apply (LR_stage_layer LP1 LP2) | apply (LR_stage_layer LP1 LP2)]; assumption.
Qed.

Lemma SubRel_layer {G Γ Δ d d'} : mltt_ctx Γ ->
  (@SubRel E LP1 G Γ Δ d d' <-> @SubRel E LP2 G Γ Δ d d').
Proof.
  revert d d'; induction Γ as [| g | Γ IH A k]; intros d d' Hm; cbn; try reflexivity.
  destruct Hm as [HmΓ HmA]. rewrite (IH _ _ HmΓ), (LRtm_layer (mltt_subst _ _ HmA) (mltt_subst _ _ HmA)).
  reflexivity.
Qed.

Lemma VTy_layer {G Γ T T' l} : mltt_ctx Γ -> mltt_ty T -> mltt_ty T' ->
  (@VTy E LP1 G Γ T T' l <-> @VTy E LP2 G Γ T T' l).
Proof.
  intros HΓ Hm Hm'; unfold VTy; split; intros H Δ d d' Hd.
  - apply (LRty_layer (mltt_subst _ _ Hm) (mltt_subst _ _ Hm')), H, (SubRel_layer HΓ), Hd.
  - apply (LRty_layer (mltt_subst _ _ Hm) (mltt_subst _ _ Hm')), H, (SubRel_layer HΓ), Hd.
Qed.

Lemma VTm_layer {G Γ t t' T l} : mltt_ctx Γ -> mltt_ty T ->
  (@VTm E LP1 G Γ t t' T l <-> @VTm E LP2 G Γ t t' T l).
Proof.
  intros HΓ Hm; unfold VTm; split; intros H Δ d d' Hd.
  - apply (LRtm_layer (mltt_subst _ _ Hm) (mltt_subst _ _ Hm)), H, (SubRel_layer HΓ), Hd.
  - apply (LRtm_layer (mltt_subst _ _ Hm) (mltt_subst _ _ Hm)), H, (SubRel_layer HΓ), Hd.
Qed.

Lemma VTyG_layer {G Γ T T' l} : mltt_ctx Γ -> mltt_ty T -> mltt_ty T' ->
  (@VTyG E LP1 G Γ T T' l <-> @VTyG E LP2 G Γ T T' l).
Proof.
  intros HΓ Hm Hm'; unfold VTyG; split; intros H G' γ Hγ;
    apply (VTy_layer (mltt_ctx_gwa _ _ HΓ) (mltt_gwa _ _ Hm) (mltt_gwa _ _ Hm')), H, Hγ.
Qed.

Lemma VTmG_layer {G Γ t t' T l} : mltt_ctx Γ -> mltt_ty T ->
  (@VTmG E LP1 G Γ t t' T l <-> @VTmG E LP2 G Γ t t' T l).
Proof.
  intros HΓ Hm; unfold VTmG; split; intros H G' γ Hγ;
    apply (VTm_layer (mltt_ctx_gwa _ _ HΓ) (mltt_gwa _ _ Hm)), H, Hγ.
Qed.

End LayerV.
