(** * Reducibility of every judgment at M (M2_DESIGN.md, 5g)

    The fundamental theorem at M, at the identity global substitution
    ([ReducibleP]): at a well-formed level, the finite relation; at ω, the
    relation at ω (M4_DESIGN.md F3). *)
From DeLaM.Validity Require Export ReducibleP FundamentalM.

(** ** Validity at ω, at the identity substitutions *)
Section AtOmega.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.
Context {E : GenericEq} {EL : GenericEqLaws} {LP : LRParams} {VL : VPLaws lr_vp}.

Lemma VTySω_red {G Γ T T' l} : [ G ; Γ ⊢g T @ l ] -> [ G ; Γ ⊢g T' @ l ] ->
  @VCtxS EP EM E LP G Γ -> @VTySω EP EM E LP G Γ T T' -> LRtyω G Γ T T'.
Proof.
  intros HT HT' VΓ VT. pose proof (ctx_of_ty HT) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (VΓ _ _ _ (GSubRel_gid EP EM HG) _ _ (gwk_ok_id G)) as X.
  pose proof (VT _ _ _ (GSubRel_gid EP EM HG) _ _ (gwk_ok_id G)) as Y. cbn [gwa] in X, Y.
  rewrite !gsubst_id_ctx in X, Y by first [exact (wf_ctx_dnf HΓ) | reflexivity].
  rewrite !gsubst_id_ty in Y by first [exact (wf_ty_dnf HT) | exact (wf_ty_dnf HT') | reflexivity].
  pose proof (Y _ _ _ (SubRel_id_rel _ _ X HΓ)) as Z.
  now rewrite (subst_id_ty T _ (wf_ty_nf HT) lshift0_id), (subst_id_ty T' _ (wf_ty_nf HT') lshift0_id) in Z.
Qed.

Lemma VTmSω_red {G Γ t t' T l} : [ G ; Γ ⊢g t : T @ l ] -> [ G ; Γ ⊢g t' : T @ l ] ->
  @VCtxS EP EM E LP G Γ -> @VTmSω EP EM E LP G Γ t t' T -> LRtmω G Γ T T t t'.
Proof.
  intros Ht Ht' VΓ Vt. pose proof (ctx_of_tm Ht) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (wf_tm_ty ge_typeof Ht) as HT.
  pose proof (VΓ _ _ _ (GSubRel_gid EP EM HG) _ _ (gwk_ok_id G)) as X.
  pose proof (Vt _ _ _ (GSubRel_gid EP EM HG) _ _ (gwk_ok_id G)) as Y. cbn [gwa] in X, Y.
  rewrite !gsubst_id_ctx in X, Y by first [exact (wf_ctx_dnf HΓ) | reflexivity].
  rewrite !gsubst_id_ty, !gsubst_id in Y
    by first [exact (wf_ty_dnf HT) | exact (wf_tm_dnf Ht) | exact (wf_tm_dnf Ht') | reflexivity].
  pose proof (Y _ _ _ (SubRel_id_rel _ _ X HΓ)) as Z.
  now rewrite (subst_id_ty T _ (wf_ty_nf HT) lshift0_id), (subst_id t _ (wf_tm_nf Ht) lshift0_id),
    (subst_id t' _ (wf_tm_nf Ht') lshift0_id) in Z.
Qed.

End AtOmega.

Section ReducibleM.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsRM : VPLaws (@lr_vp LRM) := vpM_laws EP EM.

(** ** At M *)

Lemma reducibleM_eqty {G Γ T T' l} : [ G ; Γ ⊢[ lM ] T ≅ T' @ l ] -> lwf (gL G) l -> @LRty EM LRM l G Γ T T'.
Proof.
  intros H Hl. destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (fundamentalM EP EM))))) _ _ _ _ _ _ H eq_refl) Hl)
    as ((_ & VΓ) & VT).
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  rewrite <- (@gm_layer_M EP EM EMl) in HT, HT'.
  exact (VTyS_red EP EM HT HT' VΓ VT).
Qed.

Lemma reducibleM_eqtm {G Γ t t' T l} : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ] -> lwf (gL G) l ->
  @LRtm EM LRM l G Γ T T t t'.
Proof.
  intros H Hl.
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalM EP EM)))))) _ _ _ _ _ _ _ H eq_refl) Hl)
    as ((_ & VΓ) & _ & Vt).
  pose proof (eqtm_wf_l (i := lM) eq_refl H) as Ht. pose proof (eqtm_wf_r (i := lM) eq_refl H) as Ht'.
  rewrite <- (@gm_layer_M EP EM EMl) in Ht, Ht'.
  exact (VTmS_red EP EM Ht Ht' VΓ Vt).
Qed.

(** ** At ω *)

Lemma reducibleM_eqty_ω {G Γ T T'} : [ G ; Γ ⊢[ lM ] T ≅ T' @ lomega ] -> @LRtyω EM LRM G Γ T T'.
Proof.
  intros H.
  destruct (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (fundamentalM EP EM))))) _ _ _ _ _ _ H eq_refl) eq_refl)
    as ((_ & VΓ) & VT).
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  rewrite <- (@gm_layer_M EP EM EMl) in HT, HT'.
  exact (VTySω_red EP EM HT HT' VΓ VT).
Qed.

Lemma reducibleM_eqtm_ω {G Γ t t' T} : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ lomega ] -> @LRtmω EM LRM G Γ T T t t'.
Proof.
  intros H.
  destruct (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalM EP EM)))))) _ _ _ _ _ _ _ H eq_refl)
    eq_refl) as ((_ & VΓ) & _ & Vt).
  pose proof (eqtm_wf_l (i := lM) eq_refl H) as Ht. pose proof (eqtm_wf_r (i := lM) eq_refl H) as Ht'.
  rewrite <- (@gm_layer_M EP EM EMl) in Ht, Ht'.
  exact (VTmSω_red EP EM Ht Ht' VΓ Vt).
Qed.

End ReducibleM.
