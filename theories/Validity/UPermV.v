(** * Validity along level permutations (M3_DESIGN.md E14)

    Related substitutions and the relation's validity forms are stable
    under level permutations ([LR_perm]); worlds of the permuted global
    context are pulled back along the inverse. This gives the parameters
    of the [□] cases at M ([vpM]) along permutations, hence [LR_perm] and
    [LR_uwk] for the relation at M. *)
From DeLaM.Validity Require Export Payload.
From DeLaM.LogRel Require Export UPermLR.

Section UPermV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VPP : VPPerm lr_vp}.

Lemma LRtm_perm {π πi l G Γ T T' t t'} : uperm π πi (gL G) -> LRtm l G Γ T T' t t' ->
  LRtm (lvsubst l (pφ π)) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof.
  unfold LRtm, LRrel. intros Hp (R & H & Ht). rewrite lmeasure_perm.
  destruct (LR_perm _ _ _ _ _ _ _ H _ _ Hp) as (R' & H' & Ek). exists R'. split; [exact H' |].
  destruct (LR_rel_dnf H _ _ Ht) as [N N']. exact (proj1 (Ek _ _ N N') Ht).
Qed.
Lemma LRty_perm {π πi l G Γ T T'} : uperm π πi (gL G) -> LRty l G Γ T T' ->
  LRty (lvsubst l (pφ π)) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ.
Proof.
  unfold LRty, LogRel. intros Hp (R & H). rewrite lmeasure_perm.
  destruct (LR_perm _ _ _ _ _ _ _ H _ _ Hp) as (R' & H' & _). exists R'. exact H'.
Qed.

Lemma SubRel_perm {π πi G} (Hp : uperm π πi (gL G)) Γ : forall Δ d d', SubRel G Γ Δ d d' ->
  SubRel (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ d[pφ π]ᵤ d'[pφ π]ᵤ.
Proof.
  induction Γ as [| g | Γ IH A l]; intros Δ d d'.
  1-2: cbn [SubRel usubst USubst_ctx ucsubst]; intros (HΔ & N1 & N2 & T1 & T2);
    refine (conj (pg_ctx Hp HΔ) (conj _ (conj _ (conj (lsub_tail_usubst _ _ _ _ T1) (lsub_tail_usubst _ _ _ _ T2)))));
    intros n; cbn [usubst USubst_lsub]; rewrite llk_ulsubst; apply dnf_us_tm.
  - cbn [SubRel usubst USubst_ctx ucsubst]. intros [Ht Hh]. split.
    + refine (SubRel_ext _ _ _ _ _ _ _ _ _ (IH _ _ _ Ht));
        intros n; cbn [usubst USubst_lsub]; rewrite !llk_ldrop, !llk_ulsubst, llk_ldrop; reflexivity.
    + pose proof (LRtm_perm Hp Hh) as X. rewrite !usubst_subst_ty in X.
      rewrite (subst_ext_ty A[pφ π]ᵤ (ldrop 1 d)[pφ π]ᵤ (ldrop 1 d[pφ π]ᵤ)),
        (subst_ext_ty A[pφ π]ᵤ (ldrop 1 d')[pφ π]ᵤ (ldrop 1 d'[pφ π]ᵤ)) in X
        by (intros n; cbn [usubst USubst_lsub]; rewrite !llk_ldrop, !llk_ulsubst, llk_ldrop; reflexivity).
      cbn [usubst USubst_lsub USubst_tm] in X |- *. rewrite !llk_ulsubst. exact X.
Qed.

(** ** Worlds of the permuted context, pulled back *)

Lemma gwk_pull {π πi G G'' γ} : uperm π πi (gL G) -> [ ⊢ G ] -> gwk_ok γ G'' (Gp π G) ->
  gwk_ok γ (Gp πi G'') G.
Proof.
  intros Hp HG Hγ. split; [exact (proj1 Hγ) |].
  pose proof (gwk_wf_usubst _ _ _ (pφ πi) (proj2 Hγ)) as X.
  unfold Gp, G_us, gctx_usubst in X |- *; cbn [gΨ] in X |- *.
  now rewrite (rt_gdecls (proj1 Hp) _ (wfg_dnf _ HG)) in X.
Qed.

Lemma VTy_pull {π πi G G'' γ Γ T T' l} : uperm π πi (gL G) -> gwk_ok γ G'' (Gp π G) -> dnfctx Γ ->
  VTy (Gp πi G'') Γ⟦γ⟧ T⟦γ⟧ T'⟦γ⟧ l ->
  VTy G'' Γ[pφ π]ᵤ⟦γ⟧ T[pφ π]ᵤ⟦γ⟧ T'[pφ π]ᵤ⟦γ⟧ (lvsubst l (pφ π)).
Proof.
  intros Hp Hγ NΓ HV Δ d d' HS.
  pose proof (ctx_glob _ _ _ (SubRel_ctx HS)) as HG''.
  pose proof (uperm_grow _ _ _ _ (proj1 Hγ) (uperm_inv _ _ _ Hp)) as Hpi''.
  pose proof (uperm_grow _ _ _ _ (proj1 Hγ) Hp) as Hp''.
  destruct (SubRel_dnf _ _ _ _ _ HS) as [Nd Nd']. pose proof (wf_ctx_dnf (SubRel_ctx HS)) as NΔ.
  pose proof (SubRel_perm (G := G'') Hpi'' _ _ _ _ HS) as HS1.
  rewrite usubst_gwa_ctx, (rt_ctx (proj1 Hp) _ NΓ) in HS1.
  pose proof (LRty_perm (G := Gp πi G'') Hp'' (HV _ _ _ HS1)) as Y.
  rewrite (Gp_rt Hpi'' HG''), (rt_ctx (proj1 (proj2 Hp)) _ NΔ) in Y.
  rewrite !usubst_subst_ty, !usubst_gwa_ty in Y.
  rewrite (subst_ext_ty _ d[pφ πi]ᵤ[pφ π]ᵤ d), (subst_ext_ty _ d'[pφ πi]ᵤ[pφ π]ᵤ d') in Y
    by (intros n; cbn [usubst USubst_lsub]; rewrite !llk_ulsubst; exact (rt_tm (proj1 (proj2 Hp)) _ (Nd n)) ||
        exact (rt_tm (proj1 (proj2 Hp)) _ (Nd' n))).
  exact Y.
Qed.

Lemma VTm_pull {π πi G G'' γ Γ t t' T l} : uperm π πi (gL G) -> gwk_ok γ G'' (Gp π G) -> dnfctx Γ ->
  VTm (Gp πi G'') Γ⟦γ⟧ t⟦γ⟧ t'⟦γ⟧ T⟦γ⟧ l ->
  VTm G'' Γ[pφ π]ᵤ⟦γ⟧ t[pφ π]ᵤ⟦γ⟧ t'[pφ π]ᵤ⟦γ⟧ T[pφ π]ᵤ⟦γ⟧ (lvsubst l (pφ π)).
Proof.
  intros Hp Hγ NΓ HV Δ d d' HS.
  pose proof (ctx_glob _ _ _ (SubRel_ctx HS)) as HG''.
  pose proof (uperm_grow _ _ _ _ (proj1 Hγ) (uperm_inv _ _ _ Hp)) as Hpi''.
  pose proof (uperm_grow _ _ _ _ (proj1 Hγ) Hp) as Hp''.
  destruct (SubRel_dnf _ _ _ _ _ HS) as [Nd Nd']. pose proof (wf_ctx_dnf (SubRel_ctx HS)) as NΔ.
  pose proof (SubRel_perm (G := G'') Hpi'' _ _ _ _ HS) as HS1.
  rewrite usubst_gwa_ctx, (rt_ctx (proj1 Hp) _ NΓ) in HS1.
  pose proof (LRtm_perm (G := Gp πi G'') Hp'' (HV _ _ _ HS1)) as Y.
  rewrite (Gp_rt Hpi'' HG''), (rt_ctx (proj1 (proj2 Hp)) _ NΔ) in Y.
  rewrite !usubst_subst_ty, !usubst_subst, !usubst_gwa_ty, !usubst_gwa_tm in Y.
  rewrite (subst_ext_ty _ d[pφ πi]ᵤ[pφ π]ᵤ d), (subst_ext_ty _ d'[pφ πi]ᵤ[pφ π]ᵤ d'),
    (subst_ext _ d[pφ πi]ᵤ[pφ π]ᵤ d), (subst_ext _ d'[pφ πi]ᵤ[pφ π]ᵤ d') in Y
    by (intros n; cbn [usubst USubst_lsub]; rewrite !llk_ulsubst; exact (rt_tm (proj1 (proj2 Hp)) _ (Nd n)) ||
        exact (rt_tm (proj1 (proj2 Hp)) _ (Nd' n))).
  exact Y.
Qed.

Lemma VTyG_perm {π πi G Γ T T' l} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> VTyG G Γ T T' l ->
  VTyG (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)).
Proof. intros Hp HG NΓ HV G'' γ Hγ. exact (VTy_pull Hp Hγ NΓ (HV _ _ (gwk_pull Hp HG Hγ))). Qed.
Lemma VTmG_perm {π πi G Γ t t' T l} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> VTmG G Γ t t' T l ->
  VTmG (Gp π G) Γ[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ T[pφ π]ᵤ (lvsubst l (pφ π)).
Proof. intros Hp HG NΓ HV G'' γ Hγ. exact (VTm_pull Hp Hγ NΓ (HV _ _ (gwk_pull Hp HG Hγ))). Qed.

Lemma CtxRel_pull {π πi G G'' γ} : uperm π πi (gL G) -> gwk_ok γ G'' (Gp π G) ->
  forall Γ Γ', dnfctx Γ -> dnfctx Γ' -> CtxRel (Gp πi G'') Γ⟦γ⟧ Γ'⟦γ⟧ ->
  CtxRel G'' Γ[pφ π]ᵤ⟦γ⟧ Γ'[pφ π]ᵤ⟦γ⟧.
Proof.
  intros Hp Hγ. pose proof (uperm_grow _ _ _ _ (proj1 Hγ) Hp) as Hp''.
  induction Γ as [| g | Γ IH A l]; intros [| g' | Γ' A' l'] NΓ NΓ'; cbn [usubst USubst_ctx ucsubst];
    rewrite ?gwa_cext, ?gwa_cnil, ?gwa_cvar; cbn [CtxRel]; try tauto.
  cbn in NΓ, NΓ'. intros (HΓ & Hl & HA & HA'). refine (conj (IH Γ' ltac:(tauto) ltac:(tauto) HΓ) (conj _ (conj _ _))).
  - exact (lequiv_lvsubst _ _ _ _ _ (uperm_usub_ok Hp'') Hl).
  - exact (VTy_pull (Γ := Γ) Hp Hγ ltac:(tauto) HA).
  - exact (VTy_pull (Γ := Γ') Hp Hγ ltac:(tauto) HA').
Qed.

Lemma CtxRelG_perm {π πi G Γ Γ'} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> dnfctx Γ' ->
  CtxRelG G Γ Γ' -> CtxRelG (Gp π G) Γ[pφ π]ᵤ Γ'[pφ π]ᵤ.
Proof.
  intros Hp HG NΓ NΓ' H G'' γ Hγ.
  exact (CtxRel_pull Hp Hγ _ _ NΓ NΓ' (H _ _ (gwk_pull Hp HG Hγ))).
Qed.

End UPermV.
