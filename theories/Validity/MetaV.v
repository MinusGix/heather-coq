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

End KwBody.

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

(** At a world, extended by related contexts. *)
Lemma GSubRel_ext_c {G G' σ σ' Δ} (ρ : @kwk EM G' Δ) {Δ0 Δ0'} :
  GSubRel G' G σ σ' -> vp_ctx (vpM EP EM) (kw_G ρ) Δ0 Δ0' ->
  GSubRel (kw_G ρ) (gext G gdCtx) (gcons (gsub_wk σ (kw_γ ρ)) (GCtx Δ0)) (gcons (gsub_wk σ' (kw_γ ρ)) (GCtx Δ0')).
Proof.
  intros Hσ (HD & HP & HPM).
  pose proof (GSubRel_wk EP EM Hσ (kw_gok ρ) (kw_glob ρ)) as Hw.
  apply (GSubRel_cons2 EP EM Hw); cbn [gdecl_gsubst gobj_wf dnfo GObjRel].
  - exact (wf_ctx_dnf (eqctx_wf_l (i := lD) eq_refl HD)).
  - exact (wf_ctx_dnf (eqctx_wf_r (i := lD) eq_refl HD)).
  - exact (eqctx_wf_l (i := lD) eq_refl HD).
  - exact (eqctx_wf_r (i := lD) eq_refl HD).
  - exact (conj HP HPM).
  - exact (conj (CtxRelG_trans HP (CtxRelG_sym HP)) (CtxRelG_trans HPM (CtxRelG_sym HPM))).
  - exact (conj (CtxRelG_trans (CtxRelG_sym HP) HP) (CtxRelG_trans (CtxRelG_sym HPM) HPM)).
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

(** ** Type bindings of layer P *)

Section TBind.
Variables (G : gctx) (Δ1 : ctx) (l1 : lvl).
Hypothesis (HΔ1 : [ G ; Δ1 ⊢[ lD ] ]) (VΔP : VCtxSP G Δ1) (VΔM : VCtxSPM G Δ1).

Local Notation D := (gdTy Δ1 lD l1).

Lemma lle_D_C_false : ~ lle lD lC.
Proof. unfold lle; cbn; lia. Qed.

(** At a world, extended by related types. *)
Lemma GSubRel_ext_t {G' σ σ' Δ} (ρ : @kwk EM G' Δ) {A A'} :
  GSubRel G' G σ σ' -> vp_ty (vpM EP EM) (kw_G ρ) Δ1⦃σ⦄⟦kw_γ ρ⟧ A A' l1 ->
  GSubRel (kw_G ρ) (gext G D) (gcons (gsub_wk σ (kw_γ ρ)) (GTy A)) (gcons (gsub_wk σ' (kw_γ ρ)) (GTy A')).
Proof.
  intros Hσ (HA & HP & HPM). rewrite gwa_gsubst_ctx in HA, HP, HPM.
  pose proof (GSubRel_wk EP EM Hσ (kw_gok ρ) (kw_glob ρ)) as Hw.
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

Lemma wf_ty_gvar_id_D {G0 U Δ Y l} : in_gctx (gΨ G0) U (gdTy Δ lD l) -> [ G0 ⊢[ lD ] Δ ≅ Y ] ->
  [ G0 ; Y ⊢[ lD ] tyGvar U (lshift 0) @ l ].
Proof.
  intros Hin Hc. destruct (eqctx_id_at Hc (i := lD) eq_refl) as [Hw Hn Ht Hv].
  eapply wft_gvar; [discriminate | exact Hw | exact Hin | apply lle_refl | exact Ht | exact I | exact Hv].
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

End MetaV.
