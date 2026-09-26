(** * Validity of the meta-functions at layer M (M5_DESIGN.md G5)

    The instance of a [CΠ] (or [Λg]) at a world [ρ] and related contexts
    [Δ0 ≈ Δ0'] is its body under the related global substitutions
    extended by [Δ0/g] and [Δ0'/g] ([gcons]); likewise for [TΠ] at
    related types of layer P. The body's validity at the extended
    substitutions relates it. The whnf equations and the bodies' typings
    come from the "growth" instance: the substitutions pushed under the
    binder, sending it to itself ([gsub_up_id]). *)
From DeLaM.Validity Require Export UPiV LetboxS.

(** ** Syntax: the instances of a substituted body *)

Lemma gup_single_ty (T : ty) σ o : gdnf σ -> T⦃gup σ⦄⦃gsingle o⦄ = T⦃gcons σ o⦄.
Proof.
  intros Hσ. apply gsubst_gsubst_ty. intros [|n]; cbn [gcons gup]; [reflexivity|].
  symmetry; apply gosubst_shift_single, Hσ.
Qed.

Lemma body_reduct_ty (T : ty) σ e o : gdnf σ -> LK dnftm e ->
  (T⦃gup σ⦄[gwk e])⦃gsingle o⦄ = T⦃gcons σ o⦄[e].
Proof.
  intros Hσ He. rewrite gsubst_subst_ty, gup_single_ty by exact Hσ. apply subst_ext_ty. intros n.
  rewrite llk_glsubst. unfold gwk. rewrite llk_glren.
  change (gsubst_tm (gren_tm (llk e n) S) (gsingle o)) with ((llk e n)⟪S⟫⦃gsingle o⦄).
  rewrite (gsubst_gren_tm _ _ _ (fun j => GId j)) by reflexivity.
  apply gsubst_id; [exact (He n) | reflexivity].
Qed.

Lemma gwa_up'_shift_tm (t : tm) γ : t⟪S⟫⟦gwk_up' γ⟧ = t⟦γ⟧⟪S⟫.
Proof.
  destruct γ as [|γ0|γ0]; cbn [gwk_up' gwa]; [reflexivity | ..].
  - exact (gren_shift_up_tm t (gwk_fn (gwk_step γ0))).
  - exact (gren_shift_up_tm t (gwk_fn (gwk_up γ0))).
Qed.

Lemma gsub_wk_gup σ γ n : gsub_wk (gup σ) (gwk_up' γ) n = gup (gsub_wk σ γ) n.
Proof.
  destruct γ as [|γ0|γ0]; [reflexivity | ..]; cbn [gwk_up' gsub_wk]; destruct n as [|n]; cbn [gup];
    try reflexivity.
  all: rewrite !(goren_goren _ _ _ (fun i => S (gwk_fn _ i))) by (intros; reflexivity); reflexivity.
Qed.

Lemma gdnf_gsub_wk σ γ : gdnf σ -> gdnf (gsub_wk σ γ).
Proof. intros H n. destruct γ; cbn [gsub_wk]; [apply H | apply dnfo_goren ..]. Qed.

Section KwBody.
Context `{E : GenericEq}.

Lemma lk_dnf_kwsub {G Γ} (ρ : kwk G Γ) e : LK dnftm e -> LK dnftm (kwsub ρ e).
Proof. intros He n. rewrite llk_kwsub. unfold ktm. apply ren_dnf, dnf_gwa, He. Qed.

Lemma kbody_body (T : ty) σ e {G Γ} (ρ : kwk G Γ) :
  kbody ρ (T⦃gup σ⦄[gwk e]) = T⦃gup (gsub_wk σ (kw_γ ρ))⦄[gwk (kwsub ρ e)].
Proof.
  unfold kbody, kwsub. rewrite gwa_subst_ty, gwa_gsubst_ty, subst_ren_lren_ty.
  transitivity (T⦃gup (gsub_wk σ (kw_γ ρ))⦄[lren (gwk e)⟦gwk_up' (kw_γ ρ)⟧ (kw_r ρ)]).
  - f_equal. apply (proj1 gsubst_ext_all). intros n; apply gsub_wk_gup.
  - apply subst_ext_ty. intros n. rewrite llk_lren, llk_gwa. unfold gwk. rewrite !llk_glren, llk_lren, llk_gwa.
    change (gren_tm ?x ?y) with x⟪y⟫. rewrite gwa_up'_shift_tm, gren_ren. reflexivity.
Qed.

Lemma kbodyt_body (t : tm) σ e {G Γ} (ρ : kwk G Γ) :
  kbodyt ρ (t⦃gup σ⦄[gwk e]) = t⦃gup (gsub_wk σ (kw_γ ρ))⦄[gwk (kwsub ρ e)].
Proof.
  unfold kbodyt, kwsub. rewrite gwa_subst, gwa_gsubst_tm, subst_ren_lren.
  transitivity (t⦃gup (gsub_wk σ (kw_γ ρ))⦄[lren (gwk e)⟦gwk_up' (kw_γ ρ)⟧ (kw_r ρ)]).
  - f_equal. apply (proj1 (proj2 gsubst_ext_all)). intros n; apply gsub_wk_gup.
  - apply subst_ext. intros n. rewrite llk_lren, llk_gwa. unfold gwk. rewrite !llk_glren, llk_lren, llk_gwa.
    change (gren_tm ?x ?y) with x⟪y⟫. rewrite gwa_up'_shift_tm, gren_ren. reflexivity.
Qed.

(** The instance at [o]: the body under the world's substitutions,
    extended by [o]. *)
Lemma kbody_inst (T : ty) σ e {G Γ} (ρ : kwk G Γ) o : gdnf σ -> LK dnftm e ->
  (kbody ρ (T⦃gup σ⦄[gwk e]))⦃gsingle o⦄ = T⦃gcons (gsub_wk σ (kw_γ ρ)) o⦄[kwsub ρ e].
Proof.
  intros Hσ He. rewrite kbody_body.
  apply body_reduct_ty; [apply gdnf_gsub_wk, Hσ | apply lk_dnf_kwsub, He].
Qed.
Lemma kbodyt_inst (t : tm) σ e {G Γ} (ρ : kwk G Γ) o : gdnf σ -> LK dnftm e ->
  (kbodyt ρ (t⦃gup σ⦄[gwk e]))⦃gsingle o⦄ = t⦃gcons (gsub_wk σ (kw_γ ρ)) o⦄[kwsub ρ e].
Proof.
  intros Hσ He. rewrite kbodyt_body.
  apply letbox_reduct; [apply gdnf_gsub_wk, Hσ | apply lk_dnf_kwsub, He].
Qed.

(** The world one global binding up. *)
Definition kw_gstep {G Θ} D (HG : [ ⊢ gext G D ]) (HΘ : [ G ; Θ ⊢g ]) : kwk G Θ :=
  mkKwk (gext G D) Θ⟦gwk_step gwk_id⟧ (gwk_step gwk_id) wk_id (gwk_ok_step G D) (wkwf_id _)
    (gwa_ctx (gwk_ok_step G D) HG HΘ).

Lemma ktm_gstep {G Θ D HG HΘ} (t : tm) : ktm (@kw_gstep G Θ D HG HΘ) t = t⟪S⟫.
Proof. unfold ktm; cbn [kw_gstep kw_γ kw_r gwa]. rewrite ren_id_tm; [reflexivity | apply dnftm_nftm, gren_dnf_all]. Qed.
Lemma kbody_gstep {G Θ D HG HΘ} (T : ty) : kbody (@kw_gstep G Θ D HG HΘ) T = T⟪gupr S⟫.
Proof. unfold kbody; cbn [kw_gstep kw_γ kw_r gwk_up' gwa]. rewrite ren_id_ty; [reflexivity | apply dnfty_nfty, gren_dnf_all]. Qed.

(** The η body at a world. *)
Lemma kbodyt_ceta {G Γ} (ρ : kwk G Γ) (u : tm) :
  kbodyt ρ (capp u⟪S⟫ (cvar 0)) = capp (ktm ρ u)⟪S⟫ (cvar 0).
Proof.
  transitivity (capp u⟪S⟫⟦gwk_up' (kw_γ ρ)⟧⟨kw_r ρ⟩ (cvar 0)); [unfold kbodyt; destruct (kw_γ ρ); reflexivity |].
  unfold ktm. rewrite gwa_up'_shift_tm, <- gren_ren. reflexivity.
Qed.

Lemma kbodyt_teta {G Γ} (ρ : kwk G Γ) (u : tm) :
  kbodyt ρ (tapp u⟪S⟫ (tyGvar 0 (lshift 0))) = tapp (ktm ρ u)⟪S⟫ (tyGvar 0 (lshift 0)).
Proof.
  transitivity (tapp u⟪S⟫⟦gwk_up' (kw_γ ρ)⟧⟨kw_r ρ⟩ (tyGvar 0 (lshift 0))); [unfold kbodyt; destruct (kw_γ ρ); reflexivity |].
  unfold ktm. rewrite gwa_up'_shift_tm, <- gren_ren. reflexivity.
Qed.

End KwBody.

Lemma eta_body_c l (t : tm) σ d : (clam l (capp t⟪S⟫ (cvar 0)))⦃σ⦄[d] = clam l (capp t⦃σ⦄[d]⟪S⟫ (cvar 0)).
Proof.
  transitivity (clam l (capp t⟪S⟫⦃gup σ⦄[gwk d] (cvar 0))); [reflexivity |].
  rewrite gshift_up_tm, shift_gwk_subst. reflexivity.
Qed.

Lemma ceta_inst (x : tm) Δ0 : dnftm x -> (capp x⟪S⟫ (cvar 0))⦃gsingle (GCtx Δ0)⦄ = capp x Δ0.
Proof.
  intros Hx. change (capp x⟪S⟫⦃gsingle (GCtx Δ0)⦄ Δ0 = capp x Δ0). f_equal.
  rewrite (gsubst_gren_tm _ _ _ (fun j => GId j)) by reflexivity.
  apply gsubst_id; [exact Hx | reflexivity].
Qed.

Lemma eta_body_t l l' (t : tm) σ d :
  (tlam l l' (tapp t⟪S⟫ (tyGvar 0 (lshift 0))))⦃σ⦄[d] = tlam l l' (tapp t⦃σ⦄[d]⟪S⟫ (tyGvar 0 (lshift 0))).
Proof.
  transitivity (tlam l l' (tapp t⟪S⟫⦃gup σ⦄[gwk d] (tyGvar 0 (lshift 0)))); [reflexivity |].
  rewrite gshift_up_tm, shift_gwk_subst. reflexivity.
Qed.

Lemma teta_inst (x : tm) A0 : dnftm x -> nfty A0 ->
  (tapp x⟪S⟫ (tyGvar 0 (lshift 0)))⦃gsingle (GTy A0)⦄ = tapp x A0.
Proof.
  intros Hx HA. change (tapp x⟪S⟫⦃gsingle (GTy A0)⦄ A0[lshift 0] = tapp x A0).
  rewrite (nf_id_ty _ HA). f_equal.
  rewrite (gsubst_gren_tm _ _ _ (fun j => GId j)) by reflexivity.
  apply gsubst_id; [exact Hx | reflexivity].
Qed.

Section CEtaRed.
Context `{E : GenericEq}.

(** The weakened function at the bound variable, reduced. *)
Lemma tmred_ceta_app {G Γ l T t w} : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ G ; Γ ⊢[ lM ] t ⤳* w : tyCPi l T @ l ] ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] capp t⟪S⟫ (cvar 0) ⤳* capp w⟪S⟫ (cvar 0) : T @ l ].
Proof.
  intros Hl HT H.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT)) as HG1.
  assert (HG2 : [ ⊢ gext (gext G gdCtx) gdCtx ]) by (apply wfg_ctx, HG1).
  pose proof (gwa_tmred (gwk_ok_step G gdCtx) HG1 H) as X. cbn [gwa] in X.
  change (tmred (gext G gdCtx) lM Γ⟪S⟫ t⟪S⟫ w⟪S⟫ (tyCPi l T⟪gupr S⟫) l) in X.
  pose proof (gwk_ty (gwk_ok_up_step (G := G) (D := gdCtx) gdCtx) HG2 HT) as XB.
  change (wf_ty (gext (gext G gdCtx) gdCtx) lM (Γ⟪S⟫⟪gupr S⟫) T⟪gupr S⟫ l) in XB.
  rewrite gcren_shift_up in XB.
  pose proof (eta_c_ty HT) as Eη.
  pose proof (tmred_capp_M (G := gext G gdCtx) (Γ := Γ⟪S⟫) (Δ := cvar 0) Hl XB
                (wfc_var _ _ 0 HG1 eq_refl) (ltac:(rewrite Eη; exact HT)) X) as Y.
  rewrite Eη in Y. exact Y.
Qed.

Lemma tmred_teta_app {G Γ Δ l l' T t w} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
  [ G ; Γ ⊢[ lM ] t ⤳* w : tyTPi Δ l l' T @ l' ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] tapp t⟪S⟫ (tyGvar 0 (lshift 0)) ⤳* tapp w⟪S⟫ (tyGvar 0 (lshift 0)) : T @ l' ].
Proof.
  intros HΔ Hl Hl' HT H.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT)) as HG1.
  pose proof (gwk_ctx (gwk_ok_step G (gdTy Δ lD l)) HG1 HΔ) as HΔ1.
  change [ gext G (gdTy Δ lD l) ; Δ⟪S⟫ ⊢[ lD ] ] in HΔ1.
  assert (HG2 : [ ⊢ gext (gext G (gdTy Δ lD l)) (gdTy Δ⟪S⟫ lD l) ])
    by (apply wfg_ty; [exact HG1 | exact HΔ1 | right; reflexivity | exact Hl]).
  pose proof (gwa_tmred (gwk_ok_step G (gdTy Δ lD l)) HG1 H) as X. cbn [gwa] in X.
  change (tmred (gext G (gdTy Δ lD l)) lM Γ⟪S⟫ t⟪S⟫ w⟪S⟫ (tyTPi Δ⟪S⟫ l l' T⟪gupr S⟫) l') in X.
  pose proof (gwk_ty (gwk_ok_up_step (G := G) (D := gdTy Δ lD l) (gdTy Δ lD l)) HG2 HT) as XB.
  change (wf_ty (gext (gext G (gdTy Δ lD l)) (gdTy Δ⟪S⟫ lD l)) lM (Γ⟪S⟫⟪gupr S⟫) T⟪gupr S⟫ l') in XB.
  rewrite gcren_shift_up in XB.
  assert (HU : [ gext G (gdTy Δ lD l) ; Δ⟪S⟫ ⊢[ lD ] tyGvar 0 (lshift 0) @ l ]).
  { eapply wf_gv with (Δ := Δ⟪S⟫) (i' := lD);
      [discriminate | exact HΔ1 | exact (ing_here (gΨ G) (gdTy Δ lD l)) | apply lle_refl | reflexivity]. }
  pose proof (eta_t_ty HT) as Eη.
  pose proof (tmred_tapp_M (G := gext G (gdTy Δ lD l)) (Γ := Γ⟪S⟫) (Δ := Δ⟪S⟫) HΔ1 Hl Hl' XB HU
                (ltac:(rewrite Eη; exact HT)) X) as Y.
  rewrite Eη in Y. exact Y.
Qed.

End CEtaRed.

(** On well-typed syntax, [⇑σ] is [σ] pushed under the binding with its
    identity instance. *)
Lemma gsubst_up_id_ty {G Γ T l} i D σ : [ gext G D ; Γ ⊢[ i ] T @ l ] ->
  T⦃gup σ⦄ = T⦃gsub_up_id D σ⦄.
Proof.
  intros H. exact (proj1 (proj2 (proj2 equiv_gsubst)) _ _ _ _ _ H _ _
                     (gsub_equiv_up_id G D σ) (dnfo_gsub_up_id D σ)).
Qed.

Section MetaV.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsMV : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtmM := (@LRtm EM LRM).
Local Notation VCtxSP := (@VCtxS EP EM EP LR_P).
Local Notation VCtxSPM := (@VCtxS EP EM EM LR_P).

Let HM := @gm_layer_M EP EM EMl.

(** ** Related substitutions under the binder *)

(** Extended by related contexts. *)
Lemma GSubRel_cons_c {G G' σ σ' Δ0 Δ0'} :
  GSubRel G' G σ σ' -> vp_ctx (vpM EP EM) G' Δ0 Δ0' ->
  GSubRel G' (gext G gdCtx) (gcons σ (GCtx Δ0)) (gcons σ' (GCtx Δ0')).
Proof.
  intros Hw (HD & HP & HPM).
  apply (GSubRel_cons2 EP EM Hw); cbn [gdecl_gsubst gobj_wf dnfo GObjRel].
  - exact (wf_ctx_dnf (eqctx_wf_l (i := lD) eq_refl HD)).
  - exact (wf_ctx_dnf (eqctx_wf_r (i := lD) eq_refl HD)).
  - exact (eqctx_wf_l (i := lD) eq_refl HD).
  - exact (eqctx_wf_r (i := lD) eq_refl HD).
  - exact (conj HP HPM).
  - exact (conj (CtxRelG_trans HP (CtxRelG_sym HP)) (CtxRelG_trans HPM (CtxRelG_sym HPM))).
  - exact (conj (CtxRelG_trans (CtxRelG_sym HP) HP) (CtxRelG_trans (CtxRelG_sym HPM) HPM)).
Qed.

(** At a world, extended by related contexts. *)
Lemma GSubRel_ext_c {G G' σ σ' Δ} (ρ : @kwk EM G' Δ) {Δ0 Δ0'} :
  GSubRel G' G σ σ' -> vp_ctx (vpM EP EM) (kw_G ρ) Δ0 Δ0' ->
  GSubRel (kw_G ρ) (gext G gdCtx) (gcons (gsub_wk σ (kw_γ ρ)) (GCtx Δ0)) (gcons (gsub_wk σ' (kw_γ ρ)) (GCtx Δ0')).
Proof.
  intros Hσ h. exact (GSubRel_cons_c (GSubRel_wk EP EM Hσ (kw_gok ρ) (kw_glob ρ)) h).
Qed.

(** The local substitutions at the world, under the extension. *)
Lemma SubRel_ext {G' Γ σ Δ d d'} (ρ : @kwk EM G' Δ) o : SubRelM G' Γ⦃σ⦄ Δ d d' ->
  SubRelM (kw_G ρ) (Γ⟪S⟫)⦃gcons (gsub_wk σ (kw_γ ρ)) o⦄ (kw_Δ ρ) (kwsub ρ d) (kwsub ρ d').
Proof. intros H. rewrite gcons_shift_ctx, <- gwa_gsubst_ctx. exact (SubRel_kw _ _ _ ρ _ _ H). Qed.

(** Pushed under the binder, to itself. *)
Lemma GSubRel_up_c {G G' σ σ'} : GSubRel G' G σ σ' ->
  GSubRel (gext G' gdCtx) (gext G gdCtx) (gsub_up_id gdCtx σ) (gsub_up_id gdCtx σ').
Proof.
  intros Hσ. pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  apply (GSubRel_up_id EP EM (D := gdCtx) Hσ); cbn [gdecl_gsubst gdecl_ren id_obj gobj_wf GObjRel];
    try reflexivity.
  apply wfg_ctx, HG'.
Qed.

Section Bodies.
Variables (G : gctx) (Γ : ctx) (G' : gctx) (σ σ' : gsub) (Δ : ctx) (d d' : lsub).
Hypothesis (Hσ : GSubRel G' G σ σ') (Hd : SubRelM G' Γ⦃σ⦄ Δ d d').

Lemma mv_G' : [ ⊢ G' ]. Proof. exact (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)). Qed.
Lemma mv_L : gL G <= gL G'. Proof. exact (gsr_L _ _ _ _ _ _ Hσ). Qed.
Lemma mv_Δ : [ G' ; Δ ⊢[ lM ] ].
Proof. pose proof (SubRel_ctx Hd) as X. rewrite HM in X. exact X. Qed.
Lemma mv_Nσ : gdnf σ. Proof. exact (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)). Qed.
Lemma mv_Nσ' : gdnf σ'. Proof. exact (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)). Qed.
Lemma mv_Nd : LK dnftm d. Proof. exact (proj1 (SubRel_dnf _ _ _ _ _ Hd)). Qed.
Lemma mv_Nd' : LK dnftm d'. Proof. exact (proj2 (SubRel_dnf _ _ _ _ _ Hd)). Qed.

(** A body valid under a context binding, at the growth instance. *)
Lemma VTy_grow_c {T T' l} : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T' @ l ] ->
  VTySM (gext G gdCtx) Γ⟪S⟫ T T' l ->
  LRtyM l (gext G' gdCtx) Δ⟪S⟫ T⦃gup σ⦄[gwk d] T'⦃gup σ'⦄[gwk d'].
Proof.
  intros HT HT' VT.
  pose proof (VT _ _ _ (GSubRel_up_c Hσ) _ gwk_id (gwk_ok_id _)) as X; cbn [gwa] in X.
  rewrite <- (gsubst_up_id_ty _ _ σ HT), <- (gsubst_up_id_ty _ _ σ' HT') in X.
  unfold gsub_up_id in X. rewrite gcons_shift_ctx, <- gwa_gsubst_ctx in X.
  exact (X _ _ _ (SubRel_gwa Hd (gwk_ok_step G' gdCtx) (wfg_ctx _ _ mv_G'))).
Qed.
Lemma VTm_grow_c {t t' T l} : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t' : T @ l ] ->
  VTmSM (gext G gdCtx) Γ⟪S⟫ t t' T l ->
  LRtmM l (gext G' gdCtx) Δ⟪S⟫ T⦃gup σ⦄[gwk d] T⦃gup σ⦄[gwk d'] t⦃gup σ⦄[gwk d] t'⦃gup σ'⦄[gwk d'].
Proof.
  intros Ht Ht' Vt.
  pose proof (Vt _ _ _ (GSubRel_up_c Hσ) _ gwk_id (gwk_ok_id _)) as X; cbn [gwa] in X.
  rewrite <- (gsubst_up_id_tm _ _ σ Ht), <- (gsubst_up_id_tm _ _ σ' Ht'),
    <- (gsubst_up_id_ty _ _ σ (proj1 (proj2 (proj2 (proj2 presupposition))) _ _ _ _ _ _ Ht eq_refl)) in X.
  unfold gsub_up_id in X. rewrite gcons_shift_ctx, <- gwa_gsubst_ctx in X.
  exact (X _ _ _ (SubRel_gwa Hd (gwk_ok_step G' gdCtx) (wfg_ctx _ _ mv_G'))).
Qed.

(** At a world and related contexts. *)
Lemma VTy_inst_c {T T' l} (VT : VTySM (gext G gdCtx) Γ⟪S⟫ T T' l) (ρ : @kwk EM G' Δ) {Δ0 Δ0'}
  (h : vp_ctx (vpM EP EM) (kw_G ρ) Δ0 Δ0') :
  LRtyM l (kw_G ρ) (kw_Δ ρ) (kbody ρ T⦃gup σ⦄[gwk d])⦃gsingle (GCtx Δ0)⦄
    (kbody ρ T'⦃gup σ'⦄[gwk d'])⦃gsingle (GCtx Δ0')⦄.
Proof.
  rewrite !kbody_inst by first [exact mv_Nσ | exact mv_Nσ' | exact mv_Nd | exact mv_Nd'].
  pose proof (VT _ _ _ (GSubRel_ext_c ρ Hσ h) _ gwk_id (gwk_ok_id _)) as X; cbn [gwa] in X.
  exact (X _ _ _ (SubRel_ext ρ _ Hd)).
Qed.
Lemma VTm_inst_c {t t' T l} (Vt : VTmSM (gext G gdCtx) Γ⟪S⟫ t t' T l) (ρ : @kwk EM G' Δ) {Δ0 Δ0'}
  (h : vp_ctx (vpM EP EM) (kw_G ρ) Δ0 Δ0') :
  LRtmM l (kw_G ρ) (kw_Δ ρ) (kbody ρ T⦃gup σ⦄[gwk d])⦃gsingle (GCtx Δ0)⦄
    (kbody ρ T⦃gup σ⦄[gwk d'])⦃gsingle (GCtx Δ0)⦄
    (kbodyt ρ t⦃gup σ⦄[gwk d])⦃gsingle (GCtx Δ0)⦄ (kbodyt ρ t'⦃gup σ'⦄[gwk d'])⦃gsingle (GCtx Δ0')⦄.
Proof.
  rewrite !kbody_inst, !kbodyt_inst by first [exact mv_Nσ | exact mv_Nσ' | exact mv_Nd | exact mv_Nd'].
  pose proof (Vt _ _ _ (GSubRel_ext_c ρ Hσ h) _ gwk_id (gwk_ok_id _)) as X; cbn [gwa] in X.
  exact (X _ _ _ (SubRel_ext ρ _ Hd)).
Qed.

End Bodies.

(** ** [CΠ] formation and congruence *)

(** The instances' canonical relation. *)
Definition canonC (G' : gctx) (Δ : ctx) (A A' : ty) (k : lvl) : @CInstRel EM LRM G' Δ :=
  fun ρ Δ0 Δ0' _ => @LRrel EM LRM (lmeasure k) (kw_G ρ) (kw_Δ ρ)
    (kbody ρ A)⦃gsingle (GCtx Δ0)⦄ (kbody ρ A')⦃gsingle (GCtx Δ0')⦄ k.

Section CPi.
Variables (G : gctx) (Γ : ctx) (l l' : lvl) (T T' : ty).
Hypothesis (Hl : lequiv (gL G) l l') (HT : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ])
  (HT' : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T' @ l ])
  (VT : VTySM (gext G gdCtx) Γ⟪S⟫ T T' l).

Lemma cpi_LR {G' σ σ' Δ d d'} (Hσ : GSubRel G' G σ σ') (Hd : SubRelM G' Γ⦃σ⦄ Δ d d') :
  @LR EM LRM (lmeasure l) (@LRbelow EM LRM (lmeasure l)) G' Δ (tyCPi l T⦃gup σ⦄[gwk d]) (tyCPi l' T'⦃gup σ'⦄[gwk d']) l
    (@CPiRel EM LRM G' Δ l l' T⦃gup σ⦄[gwk d] T'⦃gup σ'⦄[gwk d']
       (canonC G' Δ T⦃gup σ⦄[gwk d] T'⦃gup σ'⦄[gwk d'] l)).
Proof.
  destruct (VTy_grow_c _ _ _ _ _ _ _ _ Hσ Hd HT HT' VT) as [R0 H0].
  destruct (escape_ty _ _ _ _ _ _ _ _ H0) as (HX & HX' & EXX).
  rewrite HM in HX, HX'.
  pose proof (SubRel_ctx Hd) as HΔ. rewrite HM in HΔ.
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as EL.
  assert (Hl1 : lequiv (gL G') l l') by exact (lequiv_weaken _ _ _ _ EL Hl).
  pose proof (lequiv_wf_l _ _ _ Hl1) as Wl.
  eapply (@LRcpi EM LRM (lmeasure l) (@LRbelow EM LRM (lmeasure l)) G' Δ _ _ l l l' _ _
           (canonC G' Δ T⦃gup σ⦄[gwk d] T'⦃gup σ'⦄[gwk d'] l)).
  - reflexivity.
  - exact (lequiv_refl _ _ Wl).
  - exact (lequiv_sym _ _ _ Hl1).
  - exact Wl.
  - apply tyred_refl. rewrite HM. apply wft_cpi; [exact HΔ | exact Wl | exact HX].
  - apply tyred_refl. rewrite HM. eapply wft_lconv; [| exact Hl1].
    apply wft_cpi; [exact HΔ | exact (lequiv_wf_r _ _ _ Hl1) |].
    eapply wft_lconv; [exact HX' | apply lequiv_sym, Hl1].
  - rewrite HM. exact HX.
  - rewrite HM. exact HX'.
  - apply geq_ty_cpi; [exact HΔ | exact Hl1 | exact HX | exact EXX].
  - intros ρ Δ0 Δ0' h.
    destruct (VTy_inst_c _ _ _ _ _ _ _ _ Hσ Hd VT ρ h) as [R HR].
    exact (LR_canon _ _ _ _ _ _ _ HR).
  - apply releq_refl.
Qed.

Lemma VS_cpi : VTySM G Γ (tyCPi l T) (tyCPi l' T') l.
Proof.
  apply (VTyS_intro_loc EP EM). intros G' σ σ' Hσ Δ d d' Hd.
  eexists. exact (cpi_LR Hσ Hd).
Qed.

End CPi.

(** ** [Λg]: its whnf equation is extensionality, from the bodies at the
    growth instance; its instances are the bodies at [Δ0/g], anti-reduced
    by β. *)

Section CLam.
Variables (G : gctx) (Γ : ctx) (l l' : lvl) (T : ty) (t t' : tm).
Hypothesis (Hl : lequiv (gL G) l l') (HT : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ])
  (Ht : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ]) (Ht' : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t' : T @ l ])
  (VT : VTySM (gext G gdCtx) Γ⟪S⟫ T T l) (Vt : VTmSM (gext G gdCtx) Γ⟪S⟫ t t' T l).

Lemma VS_clam : VTmSM G Γ (clam l t) (clam l' t') (tyCPi l T) l.
Proof.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Δ d d' Hd.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσσ.
  set (A := T⦃gup σ⦄[gwk d]). set (Ar := T⦃gup σ⦄[gwk d']).
  set (b := t⦃gup σ⦄[gwk d]). set (b' := t'⦃gup σ'⦄[gwk d']).
  destruct (VTy_grow_c _ _ _ _ _ _ _ _ Hσσ Hd HT HT VT) as [R0 H0].
  destruct (escape_ty _ _ _ _ _ _ _ _ H0) as (HA & HAr & HAAr).
  destruct (VTm_grow_c _ _ _ _ _ _ _ _ Hσ Hd Ht Ht' Vt) as (Rb & HRb & Hbb).
  destruct (escape_tm _ _ _ _ _ _ _ _ HRb _ _ Hbb) as (Hb & Hb' & Ebb).
  pose proof (geq_ty_sound HAAr) as DAAr.
  rewrite HM in HA, HAr, Hb, Hb', DAAr. fold A Ar b b' in HA, HAr, Hb, Hb', DAAr, Ebb.
  pose proof (SubRel_ctx Hd) as HΔ. rewrite HM in HΔ.
  assert (Hl1 : lequiv (gL G') l l') by exact (lequiv_weaken _ _ _ _ (gsr_L _ _ _ _ _ _ Hσ) Hl).
  pose proof (lequiv_wf_l _ _ _ Hl1) as Wl. pose proof (lequiv_wf_r _ _ _ Hl1) as Wl'.
  assert (DU : [ G' ; Δ ⊢[ lM ] tyCPi l A ≅ tyCPi l Ar @ l ])
    by (apply eqty_cpi; [exact HΔ | exact (lequiv_refl _ _ Wl) | exact HA | exact DAAr]).
  assert (Hw : [ G' ; Δ ⊢[ lM ] clam l b : tyCPi l A @ l ])
    by (apply wf_clam; [exact HΔ | exact Wl | exact HA | exact Hb]).
  assert (Hw'A : [ G' ; Δ ⊢[ lM ] clam l' b' : tyCPi l A @ l ])
    by (eapply pre_clam_r; [exact HΔ | exact Hl1 | exact HA | exact Hb']).
  assert (Hw'Ar : [ G' ; Δ ⊢[ lM ] clam l' b' : tyCPi l Ar @ l ])
    by (eapply wf_conv; [exact Hw'A | apply eqty_sym, DU]).
  assert (HAl : [ gext G' gdCtx ; Δ⟪S⟫ ⊢[ lM ] A @ l' ])
    by (eapply wft_lconv; [exact HA | apply lequiv_sym, Hl1]).
  assert (Hb'l : [ gext G' gdCtx ; Δ⟪S⟫ ⊢[ lM ] b' : A @ l' ])
    by (eapply wf_lconv; [exact Hb' | apply lequiv_sym, Hl1]).
  assert (Hb'r : [ gext G' gdCtx ; Δ⟪S⟫ ⊢[ lM ] b' : Ar @ l' ])
    by (eapply wf_conv; [exact Hb'l | apply eqty_sym; eapply eqty_lconv; [exact DAAr | apply lequiv_sym, Hl1]]).
  assert (HArl : [ gext G' gdCtx ; Δ⟪S⟫ ⊢[ lM ] Ar @ l' ])
    by (eapply wft_lconv; [exact HAr | apply lequiv_sym, Hl1]).
  pose proof (cpi_LR G Γ l l T T (lequiv_refl _ _ (lequiv_wf_l _ _ _ Hl)) HT HT VT Hσσ Hd) as HLR.
  (* extensionality: both sides, at the bound variable, β-reduce to the bodies *)
  assert (E1 : [ G' ; Δ ⊢ clam l b ≈ clam l' b' : tyCPi l A @ l ]).
  { apply geq_tm_cext; [exact Wl | exact HA | exact Hw | exact Hw'A |].
    eapply geq_tm_exp; [| | exact Ebb]; rewrite HM.
    - exact (tmred_ceta_body HΔ Wl HA Hb).
    - eapply tmred_lconv; [exact (tmred_ceta_body HΔ Wl' HAl Hb'l) | exact Hl1]. }
  eexists; split; [exact HLR |].
  exists (clam l b), (clam l' b').
  refine (conj _ (conj _ (conj (whnf_clam _ _) (conj (whnf_clam _ _) (conj E1 (conj _ _)))))).
  - rewrite HM. apply tmred_refl, Hw.
  - rewrite HM. apply tmred_refl, Hw'Ar.
  - eapply geq_tm_conv; [exact E1 |]. rewrite HM. exact DU.
  - intros ρ Δ0 Δ0' h. unfold canonC.
    pose proof (VTm_inst_c _ _ _ _ _ _ _ _ Hσ Hd Vt ρ h) as Y.
    pose proof (VTy_inst_c _ _ _ _ _ _ _ _ Hσσ Hd VT ρ h) as Z0.
    destruct (LRtm_irrel_r Y Z0) as (R' & HR' & Hrel).
    exists R'. split; [exact HR' |].
    pose proof (kw_ctx ρ) as HΔρ. rewrite HM in HΔρ.
    assert (HGc : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) gdCtx) ])
      by (rewrite gdecl_gwa_ctx; apply wfg_ctx, kw_glob).
    pose proof (eqctx_wf_l (i := lD) eq_refl (proj1 h)) as HΔ0.
    pose proof (eqctx_wf_r (i := lD) eq_refl (proj1 h)) as HΔ0'.
    pose proof (kw_body_ty ρ HGc (ltac:(rewrite HM; exact HA))) as HAρ.
    pose proof (kw_body_tm ρ HGc (ltac:(rewrite HM; exact Hb))) as Hbρ.
    pose proof (kw_body_ty ρ HGc (ltac:(rewrite HM; exact HArl))) as HArρ.
    pose proof (kw_body_tm ρ HGc (ltac:(rewrite HM; exact Hb'r))) as Hb'ρ.
    rewrite gdecl_gwa_ctx, HM in HAρ, Hbρ, HArρ, Hb'ρ.
    pose proof (kw_lequiv ρ Hl1) as Hlρ.
    eapply (LR_red_tm _ _ _ _ _ _ _ _ HR' _ _ _ _ Hrel); rewrite HM, ktm_clam.
    + exact (tmred_cbeta_M HΔρ (lequiv_wf_l _ _ _ Hlρ) HAρ Hbρ HΔ0).
    + eapply tmred_lconv; [exact (tmred_cbeta_M HΔρ (lequiv_wf_r _ _ _ Hlρ) HArρ Hb'ρ HΔ0') | exact Hlρ].
Qed.

End CLam.

(** ** Application to a context: the function's relation at the identity
    world, its instance at the related contexts, anti-reduced *)

Section CApp.
Variables (G : gctx) (Γ : ctx) (l : lvl) (T : ty) (t t' : tm) (Δ1 Δ1' : ctx).
Hypothesis (HΔ1 : [ G ; Δ1 ⊢[ lD ] ]) (HΔ1' : [ G ; Δ1' ⊢[ lD ] ])
  (VEqP : @VCtxEqS EP LR_P EP EM G Δ1 Δ1') (VEqM : @VCtxEqS EM LR_P EP EM G Δ1 Δ1')
  (Vt : VTmSM G Γ t t' (tyCPi l T) l).

Lemma VS_capp : VTmSM G Γ (capp t Δ1) (capp t' Δ1') T⦃gsingle (GCtx Δ1)⦄ l.
Proof.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ d d' Hd.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσσ. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  destruct (SubRel_dnf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (Vt _ _ _ Hσ G' gwk_id (gwk_ok_id G') Θ d d' Hd) as X. cbn [gwa] in X.
  destruct X as (R & HLR & Hrel).
  set (A := T⦃gup σ⦄[gwk d]) in *. set (Ar := T⦃gup σ⦄[gwk d']) in *.
  change ((tyCPi l T)⦃σ⦄[d]) with (tyCPi l A) in HLR.
  change ((tyCPi l T)⦃σ⦄[d']) with (tyCPi l Ar) in HLR.
  destruct (escape_ty _ _ _ _ _ _ _ _ HLR) as (HCA & HCAr & _).
  destruct (LR_inv_cpi HLR (tyred_refl _ _ HCA))
    as (m2 & U1' & instR & _ & _ & _ & Wl & HT' & HA & _ & _ & HI & HR).
  assert (E : tyCPi m2 U1' = tyCPi l Ar)
    by (eapply tyred_whnf_det; [exact HT' | apply tyred_refl, HCAr | constructor | constructor]).
  injection E as -> ->.
  apply HR in Hrel. destruct Hrel as (w & w' & Hw & Hw' & Nw & Nw' & Ew & Ew' & K).
  (* the related contexts *)
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ1' compt_D) as HD'.
  pose proof (gs_ctx EP EM Hσ HΔ1' compt_D) as HDl.
  pose proof (CtxRelG_escape_P EP EM (VEqP _ _ _ Hσ) HD HD') as [_ HDD].
  pose proof (CtxRelG_escape_P EP EM (VEqP _ _ _ Hσσ) HD HDl) as [_ HDDl].
  assert (h : vp_ctx (@lr_vp LRM) G' Δ1⦃σ⦄ Δ1'⦃σ'⦄)
    by exact (conj HDD (conj (VEqP _ _ _ Hσ) (VEqM _ _ _ Hσ))).
  assert (hσσ : vp_ctx (@lr_vp LRM) G' Δ1⦃σ⦄ Δ1'⦃σ⦄)
    by exact (conj HDDl (conj (VEqP _ _ _ Hσσ) (VEqM _ _ _ Hσσ))).
  pose proof (vpl_ctx_trans hσσ (vpl_ctx_sym hσσ)) as hl.
  (* the instances at the identity world *)
  pose proof (SubRel_ctx Hd) as HΘg.
  set (ρ0 := kw_loc wk_id (wkwf_id Θ) HΘg).
  pose proof (K ρ0 _ _ h) as Kk. pose proof (HI ρ0 _ _ h) as HIk. pose proof (HI ρ0 _ _ hl) as HIr.
  rewrite HM in HA, HCAr, Hw, Hw'.
  assert (HAr : [ gext G' gdCtx ; Θ⟪S⟫ ⊢[ lM ] Ar @ l ]).
  { destruct (LR_inv_cpi HLR (tyred_refl _ _ HCA)) as (? & ? & ? & _ & _ & _ & _ & HT2 & _ & X & _).
    assert (E : tyCPi x x0 = tyCPi l Ar)
      by (eapply tyred_whnf_det; [exact HT2 | apply tyred_refl; rewrite HM; exact HCAr | constructor | constructor]).
    injection E as -> ->. rewrite HM in X. exact X. }
  assert (NA : nfty A) by exact (wf_ty_nf HA).
  assert (NAr : nfty Ar) by exact (wf_ty_nf HAr).
  assert (NW : nftm w) by exact (wf_tm_nf (eqtm_wf_r (i := lM) eq_refl (tmred_eq _ _ _ _ _ _ _ Hw))).
  assert (NW' : nftm w') by exact (wf_tm_nf (eqtm_wf_r (i := lM) eq_refl (tmred_eq _ _ _ _ _ _ _ Hw'))).
  unfold ρ0, kty, ktm, kbody, kw_loc in Kk, HIk, HIr;
    cbn [kw_G kw_Δ kw_γ kw_r gwk_up' gwa wk_ren] in Kk, HIk, HIr.
  rewrite !ren_id_ty in HIk, HIr by first [exact NA | exact NAr].
  rewrite !ren_id_tm in Kk by first [exact NW | exact NW'].
  destruct (escape_ty _ _ _ _ _ _ _ _ HIk) as (HIA & HIA' & _). rewrite HM in HIA, HIA'.
  assert (Hr1 : [ G' ; Θ ⊢g capp t⦃σ⦄[d] Δ1⦃σ⦄ ⤳* capp w Δ1⦃σ⦄ : A⦃gsingle (GCtx Δ1⦃σ⦄)⦄ @ l ])
    by (rewrite HM; exact (tmred_capp_M Wl HA HD HIA Hw)).
  assert (Hr2 : [ G' ; Θ ⊢g capp t'⦃σ'⦄[d'] Δ1'⦃σ'⦄ ⤳* capp w' Δ1'⦃σ'⦄ : Ar⦃gsingle (GCtx Δ1'⦃σ'⦄)⦄ @ l ])
    by (rewrite HM; exact (tmred_capp_M Wl HAr HD' HIA' Hw')).
  pose proof (LR_red_tm _ _ _ _ _ _ _ _ HIk _ _ _ _ Kk Hr1 Hr2) as Z.
  rewrite (gs_gsingle_ty T _ σ Nσ). cbn [gosubst]. rewrite !gsingle_subst_ty by assumption.
  change ((capp t Δ1)⦃σ⦄[d]) with (capp t⦃σ⦄[d] Δ1⦃σ⦄).
  change ((capp t' Δ1')⦃σ'⦄[d']) with (capp t'⦃σ'⦄[d'] Δ1'⦃σ'⦄).
  eapply LRtm_irrel_r; [exists (instR ρ0 _ _ h); split; [exact HIk | exact Z] | eexists; exact HIr].
Qed.

End CApp.

(** ** β: the application of [Λg] reduces to the body's instance *)

Lemma VS_cbeta {G Γ l T t Δ1} : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> [ G ; Δ1 ⊢[ lD ] ] ->
  VCtxSP G Δ1 -> VCtxSPM G Δ1 -> VTmSM (gext G gdCtx) Γ⟪S⟫ t t T l ->
  VTmSM G Γ (capp (clam l t) Δ1) t⦃gsingle (GCtx Δ1)⦄ T⦃gsingle (GCtx Δ1)⦄ l.
Proof.
  intros Hl HT Ht HΔ1 VΔP VΔM Vt.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ1 compt_D) as HDr.
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hσ) HD HDr) as [_ HDDr].
  assert (Hσx : GSubRel G' (gext G gdCtx) (gcons σ (GCtx Δ1⦃σ⦄)) (gcons σ' (GCtx Δ1⦃σ'⦄)))
    by exact (GSubRel_cons_c Hσ (conj HDDr (conj (VΔP _ _ _ Hσ) (VΔM _ _ _ Hσ)))).
  pose proof (Vt _ _ _ Hσx G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  rewrite gcons_shift_ctx in Y. specialize (Y _ _ _ He).
  (* the body and its type, at the growth instance *)
  destruct (VTm_grow_c _ _ _ _ _ _ _ _ Hσ He Ht Ht Vt) as (Rb & HRb & Hbb).
  destruct (escape_ty _ _ _ _ _ _ _ _ HRb) as (HA & _ & _).
  destruct (escape_tm _ _ _ _ _ _ _ _ HRb _ _ Hbb) as (Hb & _ & _).
  rewrite HM in HA, Hb.
  pose proof (SubRel_ctx He) as HΘ. rewrite HM in HΘ.
  assert (Hl1 : lwf (gL G') l) by exact (lwf_weaken _ _ _ (gsr_L _ _ _ _ _ _ Hσ) Hl).
  (* the goal *)
  rewrite (gs_gsingle_ty T _ σ Nσ), (gs_gsingle _ _ _ Nσ'), gup_single_ty, (gup_single_tm _ _ _ Nσ')
    by exact Nσ.
  cbn [gosubst].
  eapply LRtm_red_l; [exact Y |]. rewrite HM, <- letbox_reduct, <- body_reduct_ty by assumption.
  exact (tmred_cbeta_M HΘ Hl1 HA Hb HD).
Qed.

(** ** η: [Λg. t⟪↑⟫ g] and [t] are related as [t] is to itself. The whnf
    equation is extensionality, from [t]'s instance at the bound variable
    in the world one binding up. *)

Section CEta.
Variables (G : gctx) (Γ : ctx) (l : lvl) (T : ty) (t : tm).
Hypothesis (Vt : VTmSM G Γ t t (tyCPi l T) l).

Lemma VS_ceta : VTmSM G Γ (clam l (capp t⟪S⟫ (cvar 0))) t (tyCPi l T) l.
Proof.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ d d' Hd.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  destruct (SubRel_dnf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (Vt _ _ _ Hσ G' gwk_id (gwk_ok_id G') Θ d d' Hd) as X. cbn [gwa] in X.
  destruct X as (R & HLR & Hrel). pose proof HLR as HLR0.
  destruct (escape_tm _ _ _ _ _ _ _ _ HLR _ _ Hrel) as (Hu & _ & _).
  set (A := T⦃gup σ⦄[gwk d]) in *. set (Ar := T⦃gup σ⦄[gwk d']) in *.
  change ((tyCPi l T)⦃σ⦄[d]) with (tyCPi l A) in HLR, Hu.
  change ((tyCPi l T)⦃σ⦄[d']) with (tyCPi l Ar) in HLR.
  destruct (escape_ty _ _ _ _ _ _ _ _ HLR) as (HCA & HCAr & HAA).
  destruct (LR_inv_cpi HLR (tyred_refl _ _ HCA))
    as (m2 & U1' & instR & _ & _ & _ & Wl & HT' & HA & HAr & _ & HI & HR).
  assert (E : tyCPi m2 U1' = tyCPi l Ar)
    by (eapply tyred_whnf_det; [exact HT' | apply tyred_refl, HCAr | constructor | constructor]).
  injection E as -> ->.
  apply HR in Hrel. destruct Hrel as (w & w' & Hw & Hw' & Nw & Nw' & Ew & Ew' & K).
  exists R. split; [exact HLR0 |].
  rewrite eta_body_c. set (uσ := t⦃σ⦄[d]) in *.
  pose proof (geq_ty_sound HAA) as DU.
  rewrite HM in HA, HAr, Hu, Hw, Hw', DU.
  pose proof (SubRel_ctx Hd) as HΘg. pose proof HΘg as HΘ. rewrite HM in HΘ.
  pose proof (ctx_glob _ _ _ HΘ) as HG'.
  assert (Hw1 : [ G' ; Θ ⊢[ lM ] clam l (capp uσ⟪S⟫ (cvar 0)) : tyCPi l A @ l ])
    by exact (pre_ceta_l Wl HA Hu).
  assert (Hw'r : [ G' ; Θ ⊢[ lM ] w' : tyCPi l Ar @ l ])
    by exact (eqtm_wf_r (i := lM) eq_refl (tmred_eq _ _ _ _ _ _ _ Hw')).
  assert (Hw'l : [ G' ; Θ ⊢[ lM ] w' : tyCPi l A @ l ]) by (eapply wf_conv; [exact Hw'r | exact DU]).
  (* the whnf equation: [w]'s and [w']'s instances at the bound variable *)
  assert (HG1 : [ ⊢ gext G' gdCtx ]) by (apply wfg_ctx, HG').
  set (ρS := kw_gstep gdCtx HG1 HΘg).
  assert (hS : vp_ctx (@lr_vp LRM) (kw_G ρS) (cvar 0) (cvar 0))
    by exact (conj (eqc_var _ _ 0 HG1 eq_refl) (conj CtxRelG_var CtxRelG_var)).
  destruct (escape_tm _ _ _ _ _ _ _ _ (HI ρS _ _ hS) _ _ (K ρS _ _ hS)) as (_ & _ & Eb).
  unfold ρS in Eb. rewrite !ktm_gstep, kbody_gstep, (eta_c_ty HA) in Eb.
  cbn [kw_gstep kw_G kw_Δ gwa] in Eb. change (Θ⟪gwk_step gwk_id⟫) with Θ⟪S⟫ in Eb.
  assert (E1 : [ G' ; Θ ⊢ clam l (capp uσ⟪S⟫ (cvar 0)) ≈ w' : tyCPi l A @ l ]).
  { apply geq_tm_cext; [exact Wl | exact HA | exact Hw1 | exact Hw'l |].
    eapply geq_tm_exp; [| | exact Eb]; rewrite HM.
    - eapply tmred_trans; [exact (tmred_ceta_body HΘ Wl HA (wf_ceta_body Wl HA Hu)) |].
      exact (tmred_ceta_app Wl HA Hw).
    - apply tmred_refl, (wf_ceta_body Wl HA Hw'l). }
  apply HR. exists (clam l (capp uσ⟪S⟫ (cvar 0))), w'.
  refine (conj _ (conj _ (conj (whnf_clam _ _) (conj Nw' (conj E1 (conj _ _)))))).
  - rewrite HM. apply tmred_refl, Hw1.
  - rewrite HM. exact Hw'.
  - eapply geq_tm_conv; [exact E1 |]. rewrite HM. exact DU.
  - (* the instances: β, then the application of [w] *)
    intros ρ Δ0 Δ0' h. pose proof (K ρ Δ0 Δ0' h) as Kρ. pose proof (HI ρ Δ0 Δ0' h) as HIρ.
    destruct (escape_ty _ _ _ _ _ _ _ _ HIρ) as (HIA & HIAr & _). rewrite HM in HIA, HIAr.
    pose proof (kw_ctx ρ) as HΔρ. rewrite HM in HΔρ.
    assert (HGc : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) gdCtx) ])
      by (rewrite gdecl_gwa_ctx; apply wfg_ctx, kw_glob).
    pose proof (eqctx_wf_l (i := lD) eq_refl (proj1 h)) as HΔ0.
    pose proof (eqctx_wf_r (i := lD) eq_refl (proj1 h)) as HΔ0'.
    pose proof (kw_lwf ρ Wl) as Wlρ.
    pose proof (kw_body_ty ρ HGc (ltac:(rewrite HM; exact HA))) as HAρ.
    pose proof (kw_body_ty ρ HGc (ltac:(rewrite HM; exact HAr))) as HArρ.
    pose proof (kw_body_tm ρ HGc (ltac:(rewrite HM; exact (wf_ceta_body Wl HA Hu)))) as Hbρ.
    rewrite gdecl_gwa_ctx, HM in HAρ, HArρ, Hbρ. rewrite kbodyt_ceta in Hbρ.
    pose proof (kw_tmred ρ (ltac:(rewrite HM; exact Hw))) as Hwρ.
    pose proof (kw_tm ρ (ltac:(rewrite HM; exact Hw'r))) as Hw'ρ.
    rewrite HM, kty_tyCPi in Hwρ, Hw'ρ.
    assert (Nu : dnftm (ktm ρ uσ)) by (unfold ktm; apply ren_dnf, dnf_gwa, (wf_tm_dnf Hu)).
    eapply (LR_red_tm _ _ _ _ _ _ _ _ HIρ _ _ _ _ Kρ); rewrite HM.
    + rewrite ktm_clam, kbodyt_ceta.
      eapply tmred_trans; [pose proof (tmred_cbeta_M HΔρ Wlρ HAρ Hbρ HΔ0) as Z;
                           rewrite (ceta_inst _ _ Nu) in Z; exact Z |].
      exact (tmred_capp_M Wlρ HAρ HΔ0 HIA Hwρ).
    + apply tmred_refl. exact (wf_capp _ _ _ _ _ _ Wlρ HArρ HΔ0' Hw'ρ HIAr).
Qed.

End CEta.

(** ** Type bindings of layer P *)

Section TBind.
Variables (G : gctx) (Δ1 : ctx) (l1 : lvl).
Hypothesis (HΔ1 : [ G ; Δ1 ⊢[ lD ] ]) (VΔP : VCtxSP G Δ1) (VΔM : VCtxSPM G Δ1).

Local Notation D := (gdTy Δ1 lD l1).

Lemma lle_D_C_false : ~ lle lD lC.
Proof. unfold lle; cbn; lia. Qed.

(** Extended by related types. *)
Lemma GSubRel_cons_t {G' σ σ' A A'} :
  GSubRel G' G σ σ' -> vp_ty (vpM EP EM) G' Δ1⦃σ⦄ A A' l1 ->
  GSubRel G' (gext G D) (gcons σ (GTy A)) (gcons σ' (GTy A')).
Proof.
  intros Hw (HA & HP & HPM).
  pose proof (GSubRel_refl_r EP EM Hw) as Hwr.
  pose proof (gs_ctx EP EM Hw HΔ1 compt_D) as HD. pose proof (gs_ctx EP EM Hwr HΔ1 compt_D) as HDr.
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hw) HD HDr) as [_ HDDr].
  apply (GSubRel_cons2 EP EM Hw); cbn [gdecl_gsubst gobj_wf dnfo GObjRel].
  - exact (proj1 (eqty_dnf HA)).
  - exact (proj2 (eqty_dnf HA)).
  - exact (eqty_wf_l (i := lD) eq_refl HA).
  - exact (ctxconv_ty (i := lD) HDDr eq_refl (eqty_wf_r (i := lD) eq_refl HA)).
  - exact (conj (fun Hc => False_ind _ (lle_D_C_false Hc)) (conj HP HPM)).
  - exact (conj (fun Hc => False_ind _ (lle_D_C_false Hc))
             (conj (VTyG_trans HP (VTyG_sym HP)) (VTyG_trans HPM (VTyG_sym HPM)))).
  - exact (conj (fun Hc => False_ind _ (lle_D_C_false Hc))
             (conj (VTyG_transport (VΔP _ _ _ Hw) (VTyG_trans (VTyG_sym HP) HP))
                   (VTyG_transport (VΔM _ _ _ Hw) (VTyG_trans (VTyG_sym HPM) HPM)))).
Qed.

(** At a world, extended by related types. *)
Lemma GSubRel_ext_t {G' σ σ' Δ} (ρ : @kwk EM G' Δ) {A A'} :
  GSubRel G' G σ σ' -> vp_ty (vpM EP EM) (kw_G ρ) Δ1⦃σ⦄⟦kw_γ ρ⟧ A A' l1 ->
  GSubRel (kw_G ρ) (gext G D) (gcons (gsub_wk σ (kw_γ ρ)) (GTy A)) (gcons (gsub_wk σ' (kw_γ ρ)) (GTy A')).
Proof.
  intros Hσ h. rewrite gwa_gsubst_ctx in h.
  exact (GSubRel_cons_t (GSubRel_wk EP EM Hσ (kw_gok ρ) (kw_glob ρ)) h).
Qed.

Lemma wf_ty_gvar_id_D {G0 U Δ Y l} : in_gctx (gΨ G0) U (gdTy Δ lD l) -> [ G0 ⊢[ lD ] Δ ≅ Y ] ->
  [ G0 ; Y ⊢[ lD ] tyGvar U (lshift 0) @ l ].
Proof.
  intros Hin Hc. destruct (eqctx_id_at Hc (i := lD) eq_refl) as [Hw Hn Ht Hv].
  eapply wft_gvar; [discriminate | exact Hw | exact Hin | apply lle_refl | exact Ht | exact I | exact Hv].
Qed.

(** The bound variable, related to itself. *)
Lemma vp_ty_gvar0 {G' σ σ'} : GSubRel G' G σ σ' -> lwf (gL G') l1 ->
  vp_ty (vpM EP EM) (gext G' (gdTy Δ1⦃σ⦄ lD l1)) Δ1⦃σ⦄⟪S⟫ (tyGvar 0 (lshift 0)) (tyGvar 0 (lshift 0)) l1.
Proof.
  intros Hσ Hl1'. pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD.
  pose proof (wf_gext_ty (i := lD) HG' HD (or_intror eq_refl) Hl1') as HG1.
  pose proof (gwk_ok_step G' (gdTy Δ1⦃σ⦄ lD l1)) as Hγ1.
  pose proof (gwk_ctx Hγ1 HG1 HD) as HDs.
  pose proof (CtxRelG_trans (VΔP _ _ _ Hσ) (CtxRelG_sym (VΔP _ _ _ Hσ))) as XP.
  pose proof (CtxRelG_trans (VΔM _ _ _ Hσ) (CtxRelG_sym (VΔM _ _ _ Hσ))) as XM.
  assert (Hin0 : in_gctx (gΨ (gext G' (gdTy Δ1⦃σ⦄ lD l1))) 0 (gdTy Δ1⦃σ⦄⟪S⟫ lD l1))
    by exact (ing_here _ (gdTy Δ1⦃σ⦄ lD l1)).
  refine (conj (eqty_refl _ _ _ _ _ (wf_ty_gvar_id_D Hin0 (eqc_refl _ _ _ HDs))) (conj _ _)).
  - exact (VTyG_gvar_ne (E := EP) (LP := LR_P) (δ := lshift 0) (δ' := lshift 0) Hin0 ge_lle_D I I
             (VSubK_id HDs (CtxRelG_gwk XP Hγ1))).
  - exact (VTyG_gvar_ne (E := EM) (LP := LR_P) (δ := lshift 0) (δ' := lshift 0) Hin0 ge_lle_D I I
             (VSubK_id HDs (CtxRelG_gwk XM Hγ1))).
Qed.

(** Pushed under the binder, to [U^id]. *)
Lemma GSubRel_up_t {G' σ σ'} : GSubRel G' G σ σ' -> lwf (gL G) l1 ->
  GSubRel (gext G' (gdTy Δ1⦃σ⦄ lD l1)) (gext G D) (gsub_up_id D σ) (gsub_up_id D σ').
Proof.
  intros Hσ Hl1. pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ1 compt_D) as HDr.
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hσ) HD HDr) as [_ HDDr].
  assert (Hl1' : lwf (gL G') l1) by exact (lwf_weaken _ _ _ (gsr_L _ _ _ _ _ _ Hσ) Hl1).
  pose proof (wf_gext_ty (i := lD) HG' HD (or_intror eq_refl) Hl1') as HG1.
  pose proof (gwk_ok_step G' (gdTy Δ1⦃σ⦄ lD l1)) as Hγ1.
  pose proof (gwk_ctx Hγ1 HG1 HD) as HDs.
  pose proof (CtxRelG_trans (VΔP _ _ _ Hσ) (CtxRelG_sym (VΔP _ _ _ Hσ))) as XP.
  pose proof (CtxRelG_trans (VΔM _ _ _ Hσ) (CtxRelG_sym (VΔM _ _ _ Hσ))) as XM.
  assert (Hin0 : in_gctx (gΨ (gext G' (gdTy Δ1⦃σ⦄ lD l1))) 0 (gdTy Δ1⦃σ⦄⟪S⟫ lD l1))
    by exact (ing_here _ (gdTy Δ1⦃σ⦄ lD l1)).
  pose proof (VTyG_gvar_ne (E := EP) (LP := LR_P) (δ := lshift 0) (δ' := lshift 0) Hin0 ge_lle_D I I
                (VSubK_id HDs (CtxRelG_gwk XP Hγ1))) as UP.
  pose proof (VTyG_gvar_ne (E := EM) (LP := LR_P) (δ := lshift 0) (δ' := lshift 0) Hin0 ge_lle_D I I
                (VSubK_id HDs (CtxRelG_gwk XM Hγ1))) as UM.
  apply (GSubRel_up_id EP EM (D := D) Hσ); cbn [gdecl_gsubst gdecl_ren id_obj gobj_wf GObjRel].
  - exact HG1.
  - exact (wf_ty_gvar_id_D Hin0 (eqc_refl _ _ _ HDs)).
  - exact (wf_ty_gvar_id_D Hin0 (gwk_eqctx Hγ1 HG1 HDDr)).
  - exact (conj (fun Hc => False_ind _ (lle_D_C_false Hc)) (conj UP UM)).
  - exact (conj (fun Hc => False_ind _ (lle_D_C_false Hc))
             (conj (VTyG_transport (CtxRelG_gwk (VΔP _ _ _ Hσ) Hγ1) UP)
                   (VTyG_transport (CtxRelG_gwk (VΔM _ _ _ Hσ) Hγ1) UM))).
Qed.

Section BodiesT.
Variables (Γ : ctx) (G' : gctx) (σ σ' : gsub) (Δ : ctx) (d d' : lsub).
Hypothesis (Hσ : GSubRel G' G σ σ') (Hd : SubRelM G' Γ⦃σ⦄ Δ d d') (Hl1 : lwf (gL G) l1).

Lemma VTy_grow_t {T T' l} : [ gext G D ; Γ⟪S⟫ ⊢[ lM ] T @ l ] -> [ gext G D ; Γ⟪S⟫ ⊢[ lM ] T' @ l ] ->
  VTySM (gext G D) Γ⟪S⟫ T T' l ->
  LRtyM l (gext G' (gdTy Δ1⦃σ⦄ lD l1)) Δ⟪S⟫ T⦃gup σ⦄[gwk d] T'⦃gup σ'⦄[gwk d'].
Proof.
  intros HT HT' VT. pose proof (GSubRel_up_t Hσ Hl1) as Hu.
  pose proof (VT _ _ _ Hu _ gwk_id (gwk_ok_id _)) as X; cbn [gwa] in X.
  rewrite <- (gsubst_up_id_ty _ _ σ HT), <- (gsubst_up_id_ty _ _ σ' HT') in X.
  unfold gsub_up_id in X. rewrite gcons_shift_ctx, <- gwa_gsubst_ctx in X.
  exact (X _ _ _ (SubRel_gwa Hd (gwk_ok_step G' _) (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hu)))).
Qed.
Lemma VTm_grow_t {t t' T l} : [ gext G D ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> [ gext G D ; Γ⟪S⟫ ⊢[ lM ] t' : T @ l ] ->
  VTmSM (gext G D) Γ⟪S⟫ t t' T l ->
  LRtmM l (gext G' (gdTy Δ1⦃σ⦄ lD l1)) Δ⟪S⟫ T⦃gup σ⦄[gwk d] T⦃gup σ⦄[gwk d'] t⦃gup σ⦄[gwk d] t'⦃gup σ'⦄[gwk d'].
Proof.
  intros Ht Ht' Vt. pose proof (GSubRel_up_t Hσ Hl1) as Hu.
  pose proof (Vt _ _ _ Hu _ gwk_id (gwk_ok_id _)) as X; cbn [gwa] in X.
  rewrite <- (gsubst_up_id_tm _ _ σ Ht), <- (gsubst_up_id_tm _ _ σ' Ht'),
    <- (gsubst_up_id_ty _ _ σ (proj1 (proj2 (proj2 (proj2 presupposition))) _ _ _ _ _ _ Ht eq_refl)) in X.
  unfold gsub_up_id in X. rewrite gcons_shift_ctx, <- gwa_gsubst_ctx in X.
  exact (X _ _ _ (SubRel_gwa Hd (gwk_ok_step G' _) (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hu)))).
Qed.

Lemma VTy_inst_t {T T' l} (VT : VTySM (gext G D) Γ⟪S⟫ T T' l) (ρ : @kwk EM G' Δ) {A A'}
  (h : vp_ty (vpM EP EM) (kw_G ρ) Δ1⦃σ⦄⟦kw_γ ρ⟧ A A' l1) :
  LRtyM l (kw_G ρ) (kw_Δ ρ) (kbody ρ T⦃gup σ⦄[gwk d])⦃gsingle (GTy A)⦄
    (kbody ρ T'⦃gup σ'⦄[gwk d'])⦃gsingle (GTy A')⦄.
Proof.
  rewrite !kbody_inst by first [exact (mv_Nσ _ _ _ _ Hσ) | exact (mv_Nσ' _ _ _ _ Hσ)
                                | exact (proj1 (SubRel_dnf _ _ _ _ _ Hd)) | exact (proj2 (SubRel_dnf _ _ _ _ _ Hd))].
  pose proof (VT _ _ _ (GSubRel_ext_t ρ Hσ h) _ gwk_id (gwk_ok_id _)) as X; cbn [gwa] in X.
  exact (X _ _ _ (SubRel_ext ρ _ Hd)).
Qed.
Lemma VTm_inst_t {t t' T l} (Vt : VTmSM (gext G D) Γ⟪S⟫ t t' T l) (ρ : @kwk EM G' Δ) {A A'}
  (h : vp_ty (vpM EP EM) (kw_G ρ) Δ1⦃σ⦄⟦kw_γ ρ⟧ A A' l1) :
  LRtmM l (kw_G ρ) (kw_Δ ρ) (kbody ρ T⦃gup σ⦄[gwk d])⦃gsingle (GTy A)⦄
    (kbody ρ T⦃gup σ⦄[gwk d'])⦃gsingle (GTy A)⦄
    (kbodyt ρ t⦃gup σ⦄[gwk d])⦃gsingle (GTy A)⦄ (kbodyt ρ t'⦃gup σ'⦄[gwk d'])⦃gsingle (GTy A')⦄.
Proof.
  rewrite !kbody_inst, !kbodyt_inst by first [exact (mv_Nσ _ _ _ _ Hσ) | exact (mv_Nσ' _ _ _ _ Hσ)
                                | exact (proj1 (SubRel_dnf _ _ _ _ _ Hd)) | exact (proj2 (SubRel_dnf _ _ _ _ _ Hd))].
  pose proof (Vt _ _ _ (GSubRel_ext_t ρ Hσ h) _ gwk_id (gwk_ok_id _)) as X; cbn [gwa] in X.
  exact (X _ _ _ (SubRel_ext ρ _ Hd)).
Qed.

End BodiesT.
End TBind.

(** ** [TΠ] formation and congruence *)

Definition canonT (G' : gctx) (Δ : ctx) (Θ : ctx) (m : lvl) (A A' : ty) (k : lvl) : @TInstRel EM LRM G' Δ Θ m :=
  fun ρ B B' _ => @LRrel EM LRM (lmeasure k) (kw_G ρ) (kw_Δ ρ)
    (kbody ρ A)⦃gsingle (GTy B)⦄ (kbody ρ A')⦃gsingle (GTy B')⦄ k.

(** The right-hand local substitutions, at the right-hand context. *)
Lemma SubRel_r_at {G Γ G' σ σ' Δ d d'} : VCtxSM G Γ -> GSubRel G' G σ σ' -> SubRelM G' Γ⦃σ⦄ Δ d d' ->
  SubRelM G' Γ⦃σ'⦄ Δ d' d'.
Proof.
  intros VΓ Hσ Hd. pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  exact (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) (SubRel_refl_r Hd)).
Qed.

Section TPi.
Variables (G : gctx) (Γ Δ1 Δ1' : ctx) (l1 l2 l3 l4 : lvl) (T T' : ty).
Hypothesis (H13 : lequiv (gL G) l1 l3) (H24 : lequiv (gL G) l2 l4)
  (HΔ1 : [ G ; Δ1 ⊢[ lD ] ]) (HΔ1' : [ G ; Δ1' ⊢[ lD ] ])
  (VΓ : VCtxSM G Γ) (VΔP : VCtxSP G Δ1) (VΔM : VCtxSPM G Δ1) (VΔP' : VCtxSP G Δ1') (VΔM' : VCtxSPM G Δ1')
  (VEqP : @VCtxEqS EP LR_P EP EM G Δ1 Δ1') (VEqM : @VCtxEqS EM LR_P EP EM G Δ1 Δ1')
  (HT : [ gext G (gdTy Δ1 lD l1) ; Γ⟪S⟫ ⊢[ lM ] T @ l2 ])
  (HT' : [ gext G (gdTy Δ1 lD l1) ; Γ⟪S⟫ ⊢[ lM ] T' @ l2 ])
  (HTr : [ gext G (gdTy Δ1' lD l3) ; Γ⟪S⟫ ⊢[ lM ] T' @ l4 ])
  (VT : VTySM (gext G (gdTy Δ1 lD l1)) Γ⟪S⟫ T T' l2)
  (VTr : VTySM (gext G (gdTy Δ1' lD l3)) Γ⟪S⟫ T' T' l4).

Lemma tpi_LR {G' σ σ' Δ d d'} (Hσ : GSubRel G' G σ σ') (Hd : SubRelM G' Γ⦃σ⦄ Δ d d') :
  @LR EM LRM (lmeasure l2) (@LRbelow EM LRM (lmeasure l2)) G' Δ
    (tyTPi Δ1⦃σ⦄ l1 l2 T⦃gup σ⦄[gwk d]) (tyTPi Δ1'⦃σ'⦄ l3 l4 T'⦃gup σ'⦄[gwk d']) l2
    (@TPiRel EM LRM G' Δ Δ1⦃σ⦄ Δ1'⦃σ'⦄ l1 l2 l3 l4 T⦃gup σ⦄[gwk d] T'⦃gup σ'⦄[gwk d']
       (canonT G' Δ Δ1⦃σ⦄ l1 T⦃gup σ⦄[gwk d] T'⦃gup σ'⦄[gwk d'] l2)).
Proof.
  pose proof (lequiv_wf_l _ _ _ H13) as Hw1. pose proof (lequiv_wf_l _ _ _ H24) as Hw2.
  pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (SubRel_r_at VΓ Hσ Hd) as Hdr.
  destruct (VTy_grow_t G Δ1 l1 HΔ1 VΔP VΔM Γ G' σ σ' Δ d d' Hσ Hd Hw1 HT HT' VT) as [R0 H0].
  destruct (escape_ty _ _ _ _ _ _ _ _ H0) as (HX & HX'l & EXX).
  destruct (VTy_grow_t G Δ1' l3 HΔ1' VΔP' VΔM' Γ G' σ' σ' Δ d' d' Hσr Hdr (lequiv_wf_r _ _ _ H13) HTr HTr VTr)
    as [R1 H1].
  destruct (escape_ty _ _ _ _ _ _ _ _ H1) as (HX' & _ & _).
  rewrite HM in HX, HX'l, HX'.
  pose proof (SubRel_ctx Hd) as HΔ. rewrite HM in HΔ.
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as EL.
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ1' compt_D) as HD'.
  pose proof (CtxRelG_escape_P EP EM (VEqP _ _ _ Hσ) HD HD') as [HgDD HDD].
  assert (H13' : lequiv (gL G') l1 l3) by exact (lequiv_weaken _ _ _ _ EL H13).
  assert (H24' : lequiv (gL G') l2 l4) by exact (lequiv_weaken _ _ _ _ EL H24).
  pose proof (lequiv_wf_l _ _ _ H13') as Wl1. pose proof (lequiv_wf_l _ _ _ H24') as Wl2.
  eapply (@LRtpi EM LRM (lmeasure l2) (@LRbelow EM LRM (lmeasure l2)) G' Δ _ _ l2 Δ1⦃σ⦄ Δ1'⦃σ'⦄
            l1 l2 l3 l4 _ _ (canonT G' Δ Δ1⦃σ⦄ l1 T⦃gup σ⦄[gwk d] T'⦃gup σ'⦄[gwk d'] l2)).
  - reflexivity.
  - exact (lequiv_refl _ _ Wl2).
  - exact (lequiv_sym _ _ _ H13').
  - exact (lequiv_sym _ _ _ H24').
  - exact Wl1.
  - exact Wl2.
  - apply tyred_refl. rewrite HM. apply wft_tpi; [exact HΔ | exact HD | exact Wl1 | exact Wl2 | exact HX].
  - apply tyred_refl. rewrite HM. eapply wft_lconv; [| exact H24'].
    apply wft_tpi; [exact HΔ | exact HD' | exact (lequiv_wf_r _ _ _ H13') | exact (lequiv_wf_r _ _ _ H24') | exact HX'].
  - exact (conj HDD (conj (VEqP _ _ _ Hσ) (VEqM _ _ _ Hσ))).
  - rewrite HM. exact HX.
  - rewrite HM. exact HX'.
  - apply geq_ty_tpi; [exact HΔ | exact HD | exact HgDD | exact H13' | exact H24' | exact HX | exact EXX | exact HX'].
  - intros ρ A A' h.
    destruct (VTy_inst_t G Δ1 l1 HΔ1 VΔP VΔM Γ G' σ σ' Δ d d' Hσ Hd VT ρ h) as [R HR].
    exact (LR_canon _ _ _ _ _ _ _ HR).
  - apply releq_refl.
Qed.

Lemma VS_tpi : VTySM G Γ (tyTPi Δ1 l1 l2 T) (tyTPi Δ1' l3 l4 T') l2.
Proof.
  apply (VTyS_intro_loc EP EM). intros G' σ σ' Hσ Δ d d' Hd.
  eexists. exact (tpi_LR Hσ Hd).
Qed.

End TPi.

(** ** [Λ(U : Δ)]: as [Λg]; the right-hand body is typed at its own binder
    level ([l3]) *)

Section TLam.
Variables (G : gctx) (Γ Δ1 : ctx) (l1 l2 l3 l4 : lvl) (T : ty) (t t' : tm).
Hypothesis (H13 : lequiv (gL G) l1 l3) (H24 : lequiv (gL G) l2 l4)
  (HΔ1 : [ G ; Δ1 ⊢[ lD ] ]) (VΓ : VCtxSM G Γ) (VΔP : VCtxSP G Δ1) (VΔM : VCtxSPM G Δ1)
  (HT : [ gext G (gdTy Δ1 lD l1) ; Γ⟪S⟫ ⊢[ lM ] T @ l2 ])
  (Ht : [ gext G (gdTy Δ1 lD l1) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l2 ])
  (Ht' : [ gext G (gdTy Δ1 lD l1) ; Γ⟪S⟫ ⊢[ lM ] t' : T @ l2 ])
  (Ht3 : [ gext G (gdTy Δ1 lD l3) ; Γ⟪S⟫ ⊢[ lM ] t' : T @ l4 ])
  (VT : VTySM (gext G (gdTy Δ1 lD l1)) Γ⟪S⟫ T T l2)
  (Vt : VTmSM (gext G (gdTy Δ1 lD l1)) Γ⟪S⟫ t t' T l2)
  (Vt3 : VTmSM (gext G (gdTy Δ1 lD l3)) Γ⟪S⟫ t' t' T l4).

Lemma VS_tlam : VTmSM G Γ (tlam l1 l2 t) (tlam l3 l4 t') (tyTPi Δ1 l1 l2 T) l2.
Proof.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ d d' Hd.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσσ.
  pose proof (lequiv_wf_l _ _ _ H13) as W1. pose proof (lequiv_wf_r _ _ _ H13) as W3.
  pose proof (lequiv_wf_l _ _ _ H24) as W2.
  set (A := T⦃gup σ⦄[gwk d]). set (Ar := T⦃gup σ⦄[gwk d']).
  set (b := t⦃gup σ⦄[gwk d]). set (b' := t'⦃gup σ'⦄[gwk d']).
  destruct (VTy_grow_t G Δ1 l1 HΔ1 VΔP VΔM Γ G' σ σ Θ d d' Hσσ Hd W1 HT HT VT) as [R0 H0].
  destruct (escape_ty _ _ _ _ _ _ _ _ H0) as (HA & HAr & HAAr).
  destruct (VTm_grow_t G Δ1 l1 HΔ1 VΔP VΔM Γ G' σ σ' Θ d d' Hσ Hd W1 Ht Ht' Vt) as (Rb & HRb & Hbb).
  destruct (escape_tm _ _ _ _ _ _ _ _ HRb _ _ Hbb) as (Hb & Hb' & Ebb).
  (* the right-hand body at its binder level, at both types *)
  destruct (VTm_grow_t G Δ1 l3 HΔ1 VΔP VΔM Γ G' σ σ' Θ d d' Hσ Hd W3 Ht3 Ht3 Vt3) as (R3 & HR3 & H33).
  destruct (escape_ty _ _ _ _ _ _ _ _ HR3) as (HA3 & _ & _).
  destruct (escape_tm _ _ _ _ _ _ _ _ HR3 _ _ H33) as (_ & Hb'3 & _).
  destruct (VTm_grow_t G Δ1 l3 HΔ1 VΔP VΔM Γ G' σ σ' Θ d' d' Hσ (SubRel_refl_r Hd) W3 Ht3 Ht3 Vt3)
    as (R4 & HR4 & H44).
  destruct (escape_ty _ _ _ _ _ _ _ _ HR4) as (HAr3 & _ & _).
  destruct (escape_tm _ _ _ _ _ _ _ _ HR4 _ _ H44) as (_ & Hb'r3 & _).
  pose proof (geq_ty_sound HAAr) as DAAr.
  rewrite HM in HA, HAr, Hb, Hb', HA3, Hb'3, HAr3, Hb'r3, DAAr.
  fold A Ar b b' in HA, HAr, Hb, Hb', HA3, Hb'3, HAr3, Hb'r3, DAAr, Ebb.
  pose proof (SubRel_ctx Hd) as HΘ. rewrite HM in HΘ.
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD.
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as EL.
  assert (H13' : lequiv (gL G') l1 l3) by exact (lequiv_weaken _ _ _ _ EL H13).
  assert (H24' : lequiv (gL G') l2 l4) by exact (lequiv_weaken _ _ _ _ EL H24).
  pose proof (lequiv_wf_l _ _ _ H13') as Wl1. pose proof (lequiv_wf_l _ _ _ H24') as Wl2.
  pose proof (lequiv_wf_r _ _ _ H24') as Wl4.
  assert (DU : [ G' ; Θ ⊢[ lM ] tyTPi Δ1⦃σ⦄ l1 l2 A ≅ tyTPi Δ1⦃σ⦄ l1 l2 Ar @ l2 ])
    by (apply eqty_tpi; [exact HΘ | exact HD | exact HD | apply eqc_refl, HD | exact (lequiv_refl _ _ Wl1)
                        | exact (lequiv_refl _ _ Wl2) | exact HA | exact DAAr | exact HAr]).
  assert (Hw : [ G' ; Θ ⊢[ lM ] tlam l1 l2 b : tyTPi Δ1⦃σ⦄ l1 l2 A @ l2 ])
    by (apply wf_tlam; [exact HΘ | exact HD | exact Wl1 | exact Wl2 | exact HA | exact Hb]).
  assert (Hw'A : [ G' ; Θ ⊢[ lM ] tlam l3 l4 b' : tyTPi Δ1⦃σ⦄ l1 l2 A @ l2 ])
    by exact (pre_tlam_r HΘ HD H13' H24' HA HA3 Hb'3).
  assert (Hw'Ar : [ G' ; Θ ⊢[ lM ] tlam l3 l4 b' : tyTPi Δ1⦃σ⦄ l1 l2 Ar @ l2 ])
    by (eapply wf_conv; [exact Hw'A | apply eqty_sym, DU]).
  pose proof (tpi_LR G Γ Δ1 Δ1 l1 l2 l1 l2 T T (lequiv_refl _ _ W1) (lequiv_refl _ _ W2) HΔ1 HΔ1
                VΓ VΔP VΔM VΔP VΔM VΔP VΔM HT HT HT VT VT Hσσ Hd) as HLR.
  (* extensionality *)
  assert (E1 : [ G' ; Θ ⊢ tlam l1 l2 b ≈ tlam l3 l4 b' : tyTPi Δ1⦃σ⦄ l1 l2 A @ l2 ]).
  { apply geq_tm_text; [exact HD | exact Wl1 | exact Wl2 | exact HA | exact Hw | exact Hw'A |].
    eapply geq_tm_exp; [| | exact Ebb]; rewrite HM.
    - exact (tmred_teta_body HΘ HD Wl1 Wl2 HA Hb).
    - eapply tmred_lconv; [exact (tmred_teta_body_lv HΘ HD H13' Wl4 HA3 Hb'3) | exact H24']. }
  eexists; split; [exact HLR |].
  exists (tlam l1 l2 b), (tlam l3 l4 b').
  refine (conj _ (conj _ (conj (whnf_tlam _ _ _) (conj (whnf_tlam _ _ _) (conj E1 (conj _ _)))))).
  - rewrite HM. apply tmred_refl, Hw.
  - rewrite HM. apply tmred_refl, Hw'Ar.
  - eapply geq_tm_conv; [exact E1 |]. rewrite HM. exact DU.
  - intros ρ A0 A0' h. unfold canonT.
    pose proof (VTm_inst_t G Δ1 l1 HΔ1 VΔP VΔM Γ G' σ σ' Θ d d' Hσ Hd Vt ρ h) as Y.
    pose proof (VTy_inst_t G Δ1 l1 HΔ1 VΔP VΔM Γ G' σ σ Θ d d' Hσσ Hd VT ρ h) as Z0.
    destruct (LRtm_irrel_r Y Z0) as (R' & HR' & Hrel).
    exists R'. split; [exact HR' |].
    pose proof (kw_ctx ρ) as HΔρ. rewrite HM in HΔρ.
    pose proof (gwa_ctx (kw_gok ρ) (kw_glob ρ) HD) as HDρ.
    pose proof (eqty_wf_l (i := lD) eq_refl (proj1 h)) as HA0.
    pose proof (eqty_wf_r (i := lD) eq_refl (proj1 h)) as HA0'.
    pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HA)) as HG1.
    pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HA3)) as HG3.
    assert (HGc1 : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) (gdTy Δ1⦃σ⦄ lD l1)) ])
      by (rewrite gdecl_gwa_ty; exact (kw_glob_ty ρ HG1)).
    assert (HGc3 : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) (gdTy Δ1⦃σ⦄ lD l3)) ])
      by (rewrite gdecl_gwa_ty; exact (kw_glob_ty ρ HG3)).
    pose proof (kw_body_ty ρ HGc1 (ltac:(rewrite HM; exact HA))) as HAρ.
    pose proof (kw_body_tm ρ HGc1 (ltac:(rewrite HM; exact Hb))) as Hbρ.
    pose proof (kw_body_ty ρ HGc3 (ltac:(rewrite HM; exact HAr3))) as HArρ.
    pose proof (kw_body_tm ρ HGc3 (ltac:(rewrite HM; exact Hb'r3))) as Hb'ρ.
    rewrite gdecl_gwa_ty, HM in HAρ, Hbρ, HArρ, Hb'ρ.
    pose proof (kw_lequiv ρ H13') as H13ρ. pose proof (kw_lequiv ρ H24') as H24ρ.
    eapply (LR_red_tm _ _ _ _ _ _ _ _ HR' _ _ _ _ Hrel); rewrite HM, ktm_tlam.
    + exact (tmred_tbeta_M HΔρ HDρ (lequiv_wf_l _ _ _ H13ρ) (lequiv_wf_l _ _ _ H24ρ) HAρ Hbρ HA0).
    + eapply tmred_lconv; [| exact H24ρ].
      apply (tmred_tbeta_M HΔρ HDρ (lequiv_wf_r _ _ _ H13ρ) (lequiv_wf_r _ _ _ H24ρ) HArρ Hb'ρ).
      eapply wft_lconv; [exact HA0' | apply lequiv_sym, H13ρ].
Qed.

End TLam.

(** ** Application to a type *)

Section TApp.
Variables (G : gctx) (Γ Δ1 : ctx) (l l' : lvl) (T : ty) (t t' : tm) (A A' : ty).
Hypothesis (HΔ1 : [ G ; Δ1 ⊢[ lD ] ]) (HA : [ G ; Δ1 ⊢[ lD ] A @ l ]) (HA' : [ G ; Δ1 ⊢[ lD ] A' @ l ])
  (VΔP : VCtxSP G Δ1)
  (VAP : @VTyS EP EM EP LR_P G Δ1 A A' l) (VAM : @VTyS EP EM EM LR_P G Δ1 A A' l)
  (Vt : VTmSM G Γ t t' (tyTPi Δ1 l l' T) l').

(** The arguments, related at the substitutions. *)
Lemma tapp_arg {G' σ σ'} : GSubRel G' G σ σ' -> vp_ty (@lr_vp LRM) G' Δ1⦃σ⦄ A⦃σ⦄ A'⦃σ'⦄ l.
Proof.
  intros Hσ. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ1 compt_D) as HDr.
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hσ) HD HDr) as [_ HDDr].
  pose proof (ctxconv_ty (i := lD) (eqctx_sym_D HDDr) eq_refl (gs_ty EP EM Hσr HA')) as HA'σ.
  destruct (VTyG_escape_P EP EM (CtxRelG_trans (VΔP _ _ _ Hσ) (CtxRelG_sym (VΔP _ _ _ Hσ))) HD
              (gs_ty EP EM Hσ HA) HA'σ (VAP _ _ _ Hσ)) as [_ HAA].
  exact (conj HAA (conj (VAP _ _ _ Hσ) (VAM _ _ _ Hσ))).
Qed.

Lemma VS_tapp : VTmSM G Γ (tapp t A) (tapp t' A') T⦃gsingle (GTy A)⦄ l'.
Proof.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ d d' Hd.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσσ. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  destruct (SubRel_dnf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (Vt _ _ _ Hσ G' gwk_id (gwk_ok_id G') Θ d d' Hd) as X. cbn [gwa] in X.
  destruct X as (R & HLR & Hrel).
  set (B := T⦃gup σ⦄[gwk d]) in *. set (Br := T⦃gup σ⦄[gwk d']) in *.
  change ((tyTPi Δ1 l l' T)⦃σ⦄[d]) with (tyTPi Δ1⦃σ⦄ l l' B) in HLR.
  change ((tyTPi Δ1 l l' T)⦃σ⦄[d']) with (tyTPi Δ1⦃σ⦄ l l' Br) in HLR.
  destruct (escape_ty _ _ _ _ _ _ _ _ HLR) as (HCB & HCBr & _).
  destruct (LR_inv_tpi HLR (tyred_refl _ _ HCB))
    as (Θ' & m3 & m4 & U1' & instR & _ & _ & _ & _ & Wl & Wl' & HT' & _ & HB & HBr & _ & HI & HR).
  assert (E : tyTPi Θ' m3 m4 U1' = tyTPi Δ1⦃σ⦄ l l' Br)
    by (eapply tyred_whnf_det; [exact HT' | apply tyred_refl, HCBr | constructor | constructor]).
  injection E as -> -> -> ->.
  apply HR in Hrel. destruct Hrel as (w & w' & Hw & Hw' & Nw & Nw' & Ew & Ew' & K).
  (* the related arguments *)
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ1 compt_D) as HDr.
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hσ) HD HDr) as [_ HDDr].
  pose proof (gs_ty EP EM Hσ HA) as HAσ.
  pose proof (ctxconv_ty (i := lD) (eqctx_sym_D HDDr) eq_refl (gs_ty EP EM Hσr HA')) as HA'σ.
  pose proof (tapp_arg Hσ) as h.
  pose proof (tapp_arg Hσσ) as hσσ.
  pose proof (vpl_ty_trans hσσ (vpl_ty_sym hσσ)) as hl.
  (* the instances at the identity world *)
  pose proof (SubRel_ctx Hd) as HΘg.
  set (ρ0 := kw_loc wk_id (wkwf_id Θ) HΘg).
  pose proof (K ρ0 _ _ h) as Kk. pose proof (HI ρ0 _ _ h) as HIk. pose proof (HI ρ0 _ _ hl) as HIr.
  rewrite HM in HB, HBr, Hw, Hw'.
  assert (NB : nfty B) by exact (wf_ty_nf HB).
  assert (NBr : nfty Br) by exact (wf_ty_nf HBr).
  assert (NW : nftm w) by exact (wf_tm_nf (eqtm_wf_r (i := lM) eq_refl (tmred_eq _ _ _ _ _ _ _ Hw))).
  assert (NW' : nftm w') by exact (wf_tm_nf (eqtm_wf_r (i := lM) eq_refl (tmred_eq _ _ _ _ _ _ _ Hw'))).
  unfold ρ0, kty, ktm, kbody, kw_loc in Kk, HIk, HIr;
    cbn [kw_G kw_Δ kw_γ kw_r gwk_up' gwa wk_ren] in Kk, HIk, HIr.
  rewrite !ren_id_ty in HIk, HIr by first [exact NB | exact NBr].
  rewrite !ren_id_tm in Kk by first [exact NW | exact NW'].
  destruct (escape_ty _ _ _ _ _ _ _ _ HIk) as (HIB & HIB' & _). rewrite HM in HIB, HIB'.
  assert (Hr1 : [ G' ; Θ ⊢g tapp t⦃σ⦄[d] A⦃σ⦄ ⤳* tapp w A⦃σ⦄ : B⦃gsingle (GTy A⦃σ⦄)⦄ @ l' ])
    by (rewrite HM; exact (tmred_tapp_M HD Wl Wl' HB HAσ HIB Hw)).
  assert (Hr2 : [ G' ; Θ ⊢g tapp t'⦃σ'⦄[d'] A'⦃σ'⦄ ⤳* tapp w' A'⦃σ'⦄ : Br⦃gsingle (GTy A'⦃σ'⦄)⦄ @ l' ])
    by (rewrite HM; exact (tmred_tapp_M HD Wl Wl' HBr HA'σ HIB' Hw')).
  pose proof (LR_red_tm _ _ _ _ _ _ _ _ HIk _ _ _ _ Kk Hr1 Hr2) as Z.
  rewrite (gs_gsingle_ty T _ σ Nσ). cbn [gosubst]. rewrite !gsingle_subst_ty by assumption.
  change ((tapp t A)⦃σ⦄[d]) with (tapp t⦃σ⦄[d] A⦃σ⦄).
  change ((tapp t' A')⦃σ'⦄[d']) with (tapp t'⦃σ'⦄[d'] A'⦃σ'⦄).
  eapply LRtm_irrel_r; [exists (instR ρ0 _ _ h); split; [exact HIk | exact Z] | eexists; exact HIr].
Qed.

End TApp.

(** ** β at a type *)

Lemma VS_tbeta {G Γ Δ1 l l' T t A} : lwf (gL G) l -> lwf (gL G) l' -> [ G ; Δ1 ⊢[ lD ] ] ->
  [ gext G (gdTy Δ1 lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> [ gext G (gdTy Δ1 lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] ->
  [ G ; Δ1 ⊢[ lD ] A @ l ] ->
  VCtxSP G Δ1 -> VCtxSPM G Δ1 -> @VTyS EP EM EP LR_P G Δ1 A A l -> @VTyS EP EM EM LR_P G Δ1 A A l ->
  VTmSM (gext G (gdTy Δ1 lD l)) Γ⟪S⟫ t t T l' ->
  VTmSM G Γ (tapp (tlam l l' t) A) t⦃gsingle (GTy A)⦄ T⦃gsingle (GTy A)⦄ l'.
Proof.
  intros Hl Hl' HΔ1 HT Ht HA VΔP VΔM VAP VAM Vt.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (GSubRel_cons_t G Δ1 l HΔ1 VΔP VΔM Hσ (tapp_arg G Δ1 l A A HΔ1 HA HA VΔP VAP VAM Hσ)) as Hσx.
  pose proof (Vt _ _ _ Hσx G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  rewrite gcons_shift_ctx in Y. specialize (Y _ _ _ He).
  destruct (VTm_grow_t G Δ1 l HΔ1 VΔP VΔM Γ G' σ σ' Θ e e' Hσ He Hl Ht Ht Vt) as (Rb & HRb & Hbb).
  destruct (escape_ty _ _ _ _ _ _ _ _ HRb) as (HB & _ & _).
  destruct (escape_tm _ _ _ _ _ _ _ _ HRb _ _ Hbb) as (Hb & _ & _).
  rewrite HM in HB, Hb.
  pose proof (SubRel_ctx He) as HΘ. rewrite HM in HΘ.
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD.
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as EL.
  assert (Hl1 : lwf (gL G') l) by exact (lwf_weaken _ _ _ EL Hl).
  assert (Hl1' : lwf (gL G') l') by exact (lwf_weaken _ _ _ EL Hl').
  rewrite (gs_gsingle_ty T _ σ Nσ), (gs_gsingle _ _ _ Nσ'), gup_single_ty, (gup_single_tm _ _ _ Nσ')
    by exact Nσ.
  cbn [gosubst].
  eapply LRtm_red_l; [exact Y |]. rewrite HM, <- letbox_reduct, <- body_reduct_ty by assumption.
  exact (tmred_tbeta_M HΘ HD Hl1 Hl1' HB Hb (gs_ty EP EM Hσ HA)).
Qed.

(** ** η at a type: from [t]'s instance at the bound variable, in the
    world one binding up *)

Section TEta.
Variables (G : gctx) (Γ Δ1 : ctx) (l l' : lvl) (T : ty) (t : tm).
Hypothesis (HΔ1 : [ G ; Δ1 ⊢[ lD ] ]) (VΔP : VCtxSP G Δ1) (VΔM : VCtxSPM G Δ1)
  (Vt : VTmSM G Γ t t (tyTPi Δ1 l l' T) l').

Lemma VS_teta : VTmSM G Γ (tlam l l' (tapp t⟪S⟫ (tyGvar 0 (lshift 0)))) t (tyTPi Δ1 l l' T) l'.
Proof.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ d d' Hd.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  destruct (SubRel_dnf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (Vt _ _ _ Hσ G' gwk_id (gwk_ok_id G') Θ d d' Hd) as X. cbn [gwa] in X.
  destruct X as (R & HLR & Hrel). pose proof HLR as HLR0.
  destruct (escape_tm _ _ _ _ _ _ _ _ HLR _ _ Hrel) as (Hu & _ & _).
  set (A := T⦃gup σ⦄[gwk d]) in *. set (Ar := T⦃gup σ⦄[gwk d']) in *.
  change ((tyTPi Δ1 l l' T)⦃σ⦄[d]) with (tyTPi Δ1⦃σ⦄ l l' A) in HLR, Hu.
  change ((tyTPi Δ1 l l' T)⦃σ⦄[d']) with (tyTPi Δ1⦃σ⦄ l l' Ar) in HLR.
  destruct (escape_ty _ _ _ _ _ _ _ _ HLR) as (HCA & HCAr & HAA).
  destruct (LR_inv_tpi HLR (tyred_refl _ _ HCA))
    as (Θ' & m3 & m4 & U1' & instR & _ & _ & _ & _ & Wl & Wl' & HT' & _ & HA & HAr & _ & HI & HR).
  assert (E : tyTPi Θ' m3 m4 U1' = tyTPi Δ1⦃σ⦄ l l' Ar)
    by (eapply tyred_whnf_det; [exact HT' | apply tyred_refl, HCAr | constructor | constructor]).
  injection E as -> -> -> ->.
  apply HR in Hrel. destruct Hrel as (w & w' & Hw & Hw' & Nw & Nw' & Ew & Ew' & K).
  exists R. split; [exact HLR0 |].
  rewrite eta_body_t. set (uσ := t⦃σ⦄[d]) in *.
  pose proof (geq_ty_sound HAA) as DU.
  rewrite HM in HA, HAr, Hu, Hw, Hw', DU.
  pose proof (SubRel_ctx Hd) as HΘg. pose proof HΘg as HΘ. rewrite HM in HΘ.
  pose proof (ctx_glob _ _ _ HΘ) as HG'.
  pose proof (gs_ctx EP EM Hσ HΔ1 compt_D) as HD.
  assert (Hw1 : [ G' ; Θ ⊢[ lM ] tlam l l' (tapp uσ⟪S⟫ (tyGvar 0 (lshift 0))) : tyTPi Δ1⦃σ⦄ l l' A @ l' ])
    by exact (pre_teta_l HD Wl Wl' HA Hu).
  assert (Hw'r : [ G' ; Θ ⊢[ lM ] w' : tyTPi Δ1⦃σ⦄ l l' Ar @ l' ])
    by exact (eqtm_wf_r (i := lM) eq_refl (tmred_eq _ _ _ _ _ _ _ Hw')).
  assert (Hw'l : [ G' ; Θ ⊢[ lM ] w' : tyTPi Δ1⦃σ⦄ l l' A @ l' ]) by (eapply wf_conv; [exact Hw'r | exact DU]).
  (* the whnf equation: the instances at the bound variable *)
  assert (HG1 : [ ⊢ gext G' (gdTy Δ1⦃σ⦄ lD l) ])
    by (apply wfg_ty; [exact HG' | exact HD | right; reflexivity | exact Wl]).
  set (ρS := kw_gstep (gdTy Δ1⦃σ⦄ lD l) HG1 HΘg).
  pose proof (vp_ty_gvar0 G Δ1 l HΔ1 VΔP VΔM Hσ Wl) as hS.
  destruct (escape_tm _ _ _ _ _ _ _ _ (HI ρS _ _ hS) _ _ (K ρS _ _ hS)) as (_ & _ & Eb).
  unfold ρS in Eb. rewrite !ktm_gstep, kbody_gstep, (eta_t_ty HA) in Eb.
  cbn [kw_gstep kw_G kw_Δ gwa] in Eb. change (Θ⟪gwk_step gwk_id⟫) with Θ⟪S⟫ in Eb.
  assert (E1 : [ G' ; Θ ⊢ tlam l l' (tapp uσ⟪S⟫ (tyGvar 0 (lshift 0))) ≈ w' : tyTPi Δ1⦃σ⦄ l l' A @ l' ]).
  { apply geq_tm_text; [exact HD | exact Wl | exact Wl' | exact HA | exact Hw1 | exact Hw'l |].
    eapply geq_tm_exp; [| | exact Eb]; rewrite HM.
    - eapply tmred_trans; [exact (tmred_teta_body HΘ HD Wl Wl' HA (wf_teta_body HD Wl Wl' HA Hu)) |].
      exact (tmred_teta_app HD Wl Wl' HA Hw).
    - apply tmred_refl, (wf_teta_body HD Wl Wl' HA Hw'l). }
  apply HR. exists (tlam l l' (tapp uσ⟪S⟫ (tyGvar 0 (lshift 0)))), w'.
  refine (conj _ (conj _ (conj (whnf_tlam _ _ _) (conj Nw' (conj E1 (conj _ _)))))).
  - rewrite HM. apply tmred_refl, Hw1.
  - rewrite HM. exact Hw'.
  - eapply geq_tm_conv; [exact E1 |]. rewrite HM. exact DU.
  - intros ρ A0 A0' h. pose proof (K ρ A0 A0' h) as Kρ. pose proof (HI ρ A0 A0' h) as HIρ.
    destruct (escape_ty _ _ _ _ _ _ _ _ HIρ) as (HIA & HIAr & _). rewrite HM in HIA, HIAr.
    pose proof (kw_ctx ρ) as HΔρ. rewrite HM in HΔρ.
    pose proof (gwa_ctx (kw_gok ρ) (kw_glob ρ) HD) as HDρ.
    assert (HGc : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) (gdTy Δ1⦃σ⦄ lD l)) ])
      by (rewrite gdecl_gwa_ty; exact (kw_glob_ty ρ HG1)).
    pose proof (eqty_wf_l (i := lD) eq_refl (proj1 h)) as HA0.
    pose proof (eqty_wf_r (i := lD) eq_refl (proj1 h)) as HA0'.
    pose proof (kw_lwf ρ Wl) as Wlρ. pose proof (kw_lwf ρ Wl') as Wl'ρ.
    pose proof (kw_body_ty ρ HGc (ltac:(rewrite HM; exact HA))) as HAρ.
    pose proof (kw_body_ty ρ HGc (ltac:(rewrite HM; exact HAr))) as HArρ.
    pose proof (kw_body_tm ρ HGc (ltac:(rewrite HM; exact (wf_teta_body HD Wl Wl' HA Hu)))) as Hbρ.
    rewrite gdecl_gwa_ty, HM in HAρ, HArρ, Hbρ. rewrite kbodyt_teta in Hbρ.
    pose proof (kw_tmred ρ (ltac:(rewrite HM; exact Hw))) as Hwρ.
    pose proof (kw_tm ρ (ltac:(rewrite HM; exact Hw'r))) as Hw'ρ.
    rewrite HM, kty_tyTPi in Hwρ, Hw'ρ.
    assert (Nu : dnftm (ktm ρ uσ)) by (unfold ktm; apply ren_dnf, dnf_gwa, (wf_tm_dnf Hu)).
    eapply (LR_red_tm _ _ _ _ _ _ _ _ HIρ _ _ _ _ Kρ); rewrite HM.
    + rewrite ktm_tlam, kbodyt_teta.
      eapply tmred_trans; [pose proof (tmred_tbeta_M HΔρ HDρ Wlρ Wl'ρ HAρ Hbρ HA0) as Z;
                           rewrite (teta_inst _ _ Nu (wf_ty_nf HA0)) in Z; exact Z |].
      exact (tmred_tapp_M HDρ Wlρ Wl'ρ HAρ HA0 HIA Hwρ).
    + apply tmred_refl. exact (wf_tapp _ _ _ _ _ _ _ _ Hw'ρ HDρ Wlρ Wl'ρ HArρ HA0' HIAr).
Qed.

End TEta.

End MetaV.
