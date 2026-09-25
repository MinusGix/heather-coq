(** * Validity of contextual types and [box] at layer M (07b)

    The [j = M] relation ([LR_M]) at the M instance.  A contextual type
    [□_Δ] is related by the modal case of the relation, whose context
    component ([vpM]) is the relatedness of [Δ⦃σ⦄] and [Δ'⦃σ'⦄] at P; its
    declarative part comes by escape at the P instance.  A [box] of static
    code is related to itself: related substitutions send static code to
    the same code ([static_gsubst]), and its payload is the code's
    validity at P ([⊩^{≥P}_P]). *)
From DeLaM.Validity Require Export GvarS.

#[local] Existing Instance LR_P.

(** ** Escape of validity at the identity substitution *)

Section Escape.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma lshift0_id n : llk (lshift 0) n = var n.
Proof. cbn; f_equal; lia. Qed.

Lemma VTy_escape {G Δ Δ' T T' l} : CtxRel G Δ Δ' -> [ G ; Δ ⊢g ] -> nfty T -> nfty T' ->
  VTy G Δ T T' l -> [ G ; Δ ⊢ T ≈ T' @ l ].
Proof.
  intros HR HΔ NT NT' H. destruct (H _ _ _ (SubRel_id_rel _ _ HR HΔ)) as [R HRT].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRT) as (_ & _ & X).
  now rewrite (subst_id_ty _ _ NT lshift0_id), (subst_id_ty _ _ NT' lshift0_id) in X.
Qed.

End Escape.

Section ModalS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_laws : VPLaws (@lr_vp LRM) := vpM_laws EP EM.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxEqSP := (@VCtxEqS EP LR_P EP EM).
Local Notation VCtxEqSM := (@VCtxEqS EM LR_P EP EM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).

(** Related contexts at P escape to the P instance, hence to declarative
    equality at P. *)
Lemma CtxRelG_escape_P {G D D'} : @CtxRelG EP LR_P G D D' -> [ G ; D ⊢[ lD ] ] -> [ G ; D' ⊢[ lD ] ] ->
  @geq_ctx EP G D D' /\ [ G ⊢[ lD ] D ≅ D' ].
Proof.
  intros HR HD HD'. pose proof (HR _ _ (gwk_ok_id G)) as X; cbn [gwa] in X.
  rewrite <- (@gm_layer_P EP EM EMl) in HD, HD'.
  pose proof (CtxRel_escape (E := EP) _ _ X HD HD') as Y.
  split; [exact Y|]. rewrite <- (@gm_layer_P EP EM EMl). exact (geq_ctx_sound Y).
Qed.

(** ** Contextual types in the relation *)

Lemma LR_ctyp {G Θ D D' k k'} : [ G ; Θ ⊢[ lM ] ] -> [ G ; D ⊢[ lD ] ] -> [ G ; D' ⊢[ lD ] ] ->
  lwf (gL G) k -> lequiv (gL G) k k' -> vp_ctx (vpM EP EM) G D D' ->
  @LogRel EM LRM lzero G Θ (tyCTyp D k) (tyCTyp D' k') lzero (@CTypRel EM LRM G Θ D D' k k').
Proof.
  intros HΘ HD HD' Hk Hkk HV.
  pose proof HV as (_ & HP & _). destruct (CtxRelG_escape_P HP HD HD') as [Hg _].
  apply LRmod; [reflexivity|].
  eapply MRctyp; [apply lequiv_refl; exact I | exact Hkk | | | exact HV | | intros ? ?; reflexivity].
  - apply tyred_refl. rewrite (@gm_layer_M EP EM EMl). apply wft_CTyp; assumption.
  - apply tyred_refl. rewrite (@gm_layer_M EP EM EMl). apply wft_CTyp; [assumption | assumption |].
    exact (lequiv_wf_r _ _ _ Hkk).
  - exact (geq_ty_CTyp HΘ Hg Hkk).
Qed.

(** A type related at P, in a context related to itself, escapes to the
    P instance. *)
Lemma VTyG_escape_P {G D D' A A' k} : @CtxRelG EP LR_P G D D' -> [ G ; D ⊢[ lD ] ] ->
  [ G ; D ⊢[ lD ] A @ k ] -> [ G ; D ⊢[ lD ] A' @ k ] -> @VTyG EP LR_P G D A A' k ->
  @geq_ty EP G D A A' k /\ [ G ; D ⊢[ lD ] A ≅ A' @ k ].
Proof.
  intros HR HD HA HA' H. pose proof (HR _ _ (gwk_ok_id G)) as X; cbn [gwa] in X.
  pose proof (CtxRel_trans _ _ _ _ X (CtxRel_sym _ _ _ X)) as XX.
  rewrite <- (@gm_layer_P EP EM EMl) in HD.
  pose proof (VTy_escape (E := EP) XX HD (wf_ty_nf HA) (wf_ty_nf HA') (VTyG_loc H)) as Y.
  split; [exact Y|]. rewrite <- (@gm_layer_P EP EM EMl). exact (geq_ty_sound Y).
Qed.

Lemma LR_ctrm {G Θ D D' A A' k k'} : [ G ; Θ ⊢[ lM ] ] -> [ G ; D ⊢[ lD ] ] -> [ G ; D' ⊢[ lD ] ] ->
  [ G ; D ⊢[ lD ] A @ k ] -> [ G ; D' ⊢[ lD ] A' @ k' ] ->
  lwf (gL G) k -> lequiv (gL G) k k' -> vp_ctx (vpM EP EM) G D D' ->
  vp_ty (vpM EP EM) G D A A' k -> vp_ty (vpM EP EM) G D' A' A k' ->
  @LogRel EM LRM lzero G Θ (tyCTrm D A k) (tyCTrm D' A' k') lzero (@CTrmRel EM LRM G Θ D D' A A' k k').
Proof.
  intros HΘ HD HD' HA HA' Hk Hkk HV HVA HVA'.
  pose proof HV as (HDD & HP & _). destruct (CtxRelG_escape_P HP HD HD') as [Hg _].
  pose proof HVA as (HAA & HAP & _).
  assert (HA'D : [ G ; D ⊢[ lD ] A' @ k ]) by exact (eqty_wf_r (i := lD) eq_refl HAA).
  destruct (VTyG_escape_P HP HD HA HA'D HAP) as [HgA _].
  apply LRmod; [reflexivity|].
  eapply MRctrm; [apply lequiv_refl; exact I | exact Hkk | | | exact HV | exact HVA | exact HVA' | |
                  intros ? ?; reflexivity].
  - apply tyred_refl. rewrite (@gm_layer_M EP EM EMl). apply wft_CTrm; assumption.
  - apply tyred_refl. rewrite (@gm_layer_M EP EM EMl). apply wft_CTrm; [assumption | assumption | assumption |].
    exact (lequiv_wf_r _ _ _ Hkk).
  - exact (geq_ty_CTrm HΘ Hg HA HgA Hkk).
Qed.

(** ** Formation *)

Lemma VS_CTyp {G Γ Δ Δ' l l'} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
  lwf (gL G) l -> lequiv (gL G) l l' -> VCtxEqSP G Δ Δ' -> VCtxEqSM G Δ Δ' ->
  VTySM G Γ (tyCTyp Δ l) (tyCTyp Δ' l') lzero.
Proof.
  intros HΓ HΔ HΔ' Hl Hll VP VM G' σ σ' Hσ G'' γ Hγ Θ e e' He.
  rewrite !gs_tyCTyp, !gwa_tyCTyp. cbn [subst Subst_ty subst_ty].
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  pose proof (ctx_glob _ _ _ HΘ) as HG''.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM Hσ HΔ compt_D)) as HD.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM (GSubRel_refl_r EP EM Hσ) HΔ' compt_D)) as HD'.
  assert (EL : gL G'' = gL G) by (rewrite (proj1 Hγ); exact (gsr_L _ _ _ _ _ _ Hσ)).
  eexists. apply LR_ctyp; [exact HΘ | exact HD | exact HD' | now rewrite EL | now rewrite EL |].
  pose proof (CtxRelG_gwk (VP _ _ _ Hσ) Hγ) as XP. pose proof (CtxRelG_gwk (VM _ _ _ Hσ) Hγ) as XM.
  refine (conj _ (conj XP XM)). exact (proj2 (CtxRelG_escape_P XP HD HD')).
Qed.

Lemma VS_CTrm {G Γ Δ Δ' A A' l l'} : GValid EP EM G -> [ G ; Γ ⊢[ lM ] ] ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Δ' ⊢[ lD ] A' @ l' ] ->
  lwf (gL G) l -> lequiv (gL G) l l' ->
  @VCtxS EP EM EP LR_P G Δ -> @VCtxS EP EM EM LR_P G Δ -> VCtxEqSP G Δ Δ' -> VCtxEqSM G Δ Δ' ->
  @VTyS EP EM EP LR_P G Δ A A' l -> @VTyS EP EM EM LR_P G Δ A A' l ->
  VTySM G Γ (tyCTrm Δ A l) (tyCTrm Δ' A' l') lzero.
Proof.
  intros HG HΓ HΔ HΔ' HA HA' Hl Hll VΔP VΔM VP VM VAP VAM G' σ σ' Hσ G'' γ Hγ Θ e e' He.
  rewrite !gs_tyCTrm, !gwa_tyCTrm. cbn [subst Subst_ty subst_ty].
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  pose proof (ctx_glob _ _ _ HΘ) as HG''.
  pose proof (GSubRel_refl_r EP EM Hσ) as Hσr. pose proof (GSubRel_sym EP EM HG Hσ) as Hσs.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM Hσ HΔ compt_D)) as HD.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM Hσr HΔ' compt_D)) as HD'.
  pose proof (gwa_ty Hγ HG'' (gs_ty EP EM Hσ HA)) as HA1.
  pose proof (gwa_ty Hγ HG'' (gs_ty EP EM Hσr HA')) as HA1'.
  assert (EL : gL G'' = gL G) by (rewrite (proj1 Hγ); exact (gsr_L _ _ _ _ _ _ Hσ)).
  assert (Hll' : lequiv (gL G'') l' l) by (rewrite EL; exact (lequiv_sym _ _ _ Hll)).
  (* the context *)
  pose proof (CtxRelG_gwk (VP _ _ _ Hσ) Hγ) as XP. pose proof (CtxRelG_gwk (VM _ _ _ Hσ) Hγ) as XM.
  (* the type, left to right *)
  pose proof (VTyG_gwk (VAP _ _ _ Hσ) Hγ) as YP. pose proof (VTyG_gwk (VAM _ _ _ Hσ) Hγ) as YM.
  (* the type, right to left, over the right-hand context *)
  pose proof (VTyG_lconv (VTyG_gwk (VTyG_transport (VP _ _ _ Hσr) (VTyS_sym EP EM HG VΔP VAP _ _ _ Hσs))
                Hγ) Hll') as ZP.
  pose proof (VTyG_lconv (VTyG_gwk (VTyG_transport (VM _ _ _ Hσr) (VTyS_sym EP EM HG VΔM VAM _ _ _ Hσs))
                Hγ) Hll') as ZM.
  pose proof (CtxRelG_gwk (VP _ _ _ Hσr) Hγ) as XP'.
  pose proof (CtxRelG_escape_P XP HD HD') as [_ HDD].
  assert (HA1'D : [ G'' ; (Δ⦃σ⦄)⟦γ⟧ ⊢[ lD ] (A'⦃σ'⦄)⟦γ⟧ @ l ]).
  { eapply wft_lconv; [exact (ctxconv_ty (i := lD) (eqctx_sym_D HDD) eq_refl HA1') | now rewrite EL]. }
  eexists. apply LR_ctrm; try assumption; try (now rewrite EL).
  - exact (conj HDD (conj XP XM)).
  - refine (conj _ (conj YP YM)).
    exact (proj2 (VTyG_escape_P XP HD HA1 HA1'D YP)).
  - refine (conj _ (conj ZP ZM)).
    pose proof (CtxRelG_trans (CtxRelG_sym XP') XP') as XP''.
    assert (HA1D' : [ G'' ; (Δ'⦃σ'⦄)⟦γ⟧ ⊢[ lD ] (A⦃σ⦄)⟦γ⟧ @ l' ]).
    { eapply wft_lconv; [exact (ctxconv_ty (i := lD) HDD eq_refl HA1) | exact Hll']. }
    exact (proj2 (VTyG_escape_P (CtxRelG_trans (CtxRelG_sym XP) XP) HD' HA1' HA1D' ZP)).
Qed.

(** ** [box] *)

Lemma gwa_boxT (T : ty) γ : (boxT T)⟦γ⟧ = boxT T⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_boxt (t : tm) γ : (boxt t)⟦γ⟧ = boxt t⟦γ⟧.
Proof. now destruct γ. Qed.

(** Related contexts are related to themselves, on the left. *)
Lemma vp_ctx_refl_l {G D D'} : [ G ; D ⊢[ lD ] ] -> @CtxRelG EP LR_P G D D' -> @CtxRelG EM LR_P G D D' ->
  vp_ctx (vpM EP EM) G D D.
Proof.
  intros HD XP XM. refine (conj _ (conj (CtxRelG_trans XP (CtxRelG_sym XP)) (CtxRelG_trans XM (CtxRelG_sym XM)))).
  now apply eqc_refl.
Qed.

Lemma LRtm_boxT {G Θ D T T' l} : [ G ; Θ ⊢[ lM ] ] -> [ G ; D ⊢[ lD ] ] ->
  [ G ; D ⊢[ lC ] T @ l ] -> [ G ; D ⊢[ lC ] T' @ l ] -> ty_leq T T' ->
  lwf (gL G) l -> vp_ctx (vpM EP EM) G D D -> @VTyG EP LR_P G D T T' l -> @VTyG EM LR_P G D T T' l ->
  @LRtm EM LRM lzero G Θ (tyCTyp D l) (tyCTyp D l) (boxT T) (boxT T').
Proof.
  intros HΘ HD HT HT' E Hl HV VP VM. exists (@CTypRel EM LRM G Θ D D l l); split.
  - exact (LR_ctyp HΘ HD HD Hl (lequiv_refl _ _ Hl) HV).
  - assert (Hw : [ G ; Θ ⊢g boxT T : tyCTyp D l @ lzero ])
      by (rewrite (@gm_layer_M EP EM EMl); apply wf_boxT; assumption).
    assert (Hw' : [ G ; Θ ⊢g boxT T' : tyCTyp D l @ lzero ])
      by (rewrite (@gm_layer_M EP EM EMl); apply wf_boxT; assumption).
    pose proof (static_code_ty (i := lC) ltac:(unfold lle; cbn; lia) HT HT' E) as HTT.
    pose proof (@geq_tm_boxT EP EM EMl _ _ _ _ _ _ HΘ Hl HD HT HT' HTT E) as Hg.
    assert (Hn : @CTypNf EM LRM G Θ D l (boxT T) (boxT T'))
      by (apply ctyn_box; exact (conj E (conj HT (conj HT' (conj VP VM))))).
    exists (boxT T), (boxT T'). exact (conj (tmred_refl _ _ _ Hw) (conj (tmred_refl _ _ _ Hw') (conj Hg (conj Hg (conj Hn Hn))))).
Qed.

(** Related substitutions send code to level-equivalent code, which the
    right-hand context types. *)
Lemma box_code_rel {G G' G'' Δ T T' l σ σ' γ} : GSubRel G' G σ σ' -> gwk_ok γ G'' G' -> [ ⊢ G'' ] ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Δ ⊢[ lC ] T' @ l ] -> ty_leq T T' ->
  @VCtxS EP EM EP LR_P G Δ ->
  [ G'' ; (Δ⦃σ⦄)⟦γ⟧ ⊢[ lC ] (T'⦃σ'⦄)⟦γ⟧ @ l ] /\ ty_leq (T⦃σ⦄)⟦γ⟧ (T'⦃σ'⦄)⟦γ⟧.
Proof.
  intros Hσ Hγ HG'' HΔ HT HT' E VΔP.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM Hσ HΔ compt_D)) as HD.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM (GSubRel_refl_r EP EM Hσ) HΔ compt_D)) as HD'.
  pose proof (CtxRelG_gwk (VΔP _ _ _ Hσ) Hγ) as XP.
  destruct (CtxRelG_escape_P XP HD HD') as [_ HDD].
  split.
  - exact (ctxconv_ty (i := lC) (eqctx_sym_D HDD) eq_refl (gwa_ty Hγ HG'' (gs_ty EP EM (GSubRel_refl_r EP EM Hσ) HT'))).
  - apply ty_leq_gwa, (ty_leq_trans _ (T⦃σ'⦄)).
    + exact ((proj1 (proj2 (proj2 static_gsubst))) _ _ _ _ _ HT (lle_refl _) _ _ (GSubRel_agree EP EM Hσ)).
    + apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl | exact E].
Qed.

Lemma VS_boxT {G Γ Δ T T' l} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Δ ⊢[ lC ] T' @ l ] -> ty_leq T T' ->
  @VCtxS EP EM EP LR_P G Δ -> @VCtxS EP EM EM LR_P G Δ ->
  @VTyS EP EM EP LR_P G Δ T T' l -> @VTyS EP EM EM LR_P G Δ T T' l ->
  VTmSM G Γ (boxT T) (boxT T') (tyCTyp Δ l) lzero.
Proof.
  intros HΓ Hl HΔ HT HT' E VΔP VΔM VTP VTM G' σ σ' Hσ.
  rewrite !gs_boxT, !gs_tyCTyp.
  intros G'' γ Hγ Θ e e' He. rewrite !gwa_boxT, !gwa_tyCTyp. cbn [subst Subst_ty Subst_tm subst_ty subst_tm].
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  pose proof (ctx_glob _ _ _ HΘ) as HG''.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM Hσ HΔ compt_D)) as HD.
  assert (EL : gL G'' = gL G) by (rewrite (proj1 Hγ); exact (gsr_L _ _ _ _ _ _ Hσ)).
  destruct (box_code_rel Hσ Hγ HG'' HΔ HT HT' E VΔP) as [HT1' E1].
  apply LRtm_boxT; [exact HΘ | exact HD | exact (gwa_ty Hγ HG'' (gs_ty EP EM Hσ HT)) | exact HT1' | exact E1
                   | now rewrite EL
                   | exact (vp_ctx_refl_l HD (CtxRelG_gwk (VΔP _ _ _ Hσ) Hγ) (CtxRelG_gwk (VΔM _ _ _ Hσ) Hγ))
                   | exact (VTyG_gwk (VTP _ _ _ Hσ) Hγ) | exact (VTyG_gwk (VTM _ _ _ Hσ) Hγ)].
Qed.

Lemma LRtm_boxt {G Θ D A t t' l} : [ G ; Θ ⊢[ lM ] ] -> [ G ; D ⊢[ lD ] ] -> [ G ; D ⊢[ lD ] A @ l ] ->
  [ G ; D ⊢[ lC ] t : A @ l ] -> [ G ; D ⊢[ lC ] t' : A @ l ] -> tm_leq t t' ->
  lwf (gL G) l -> vp_ctx (vpM EP EM) G D D ->
  @VTyG EP LR_P G D A A l -> @VTyG EM LR_P G D A A l ->
  @VTmG EP LR_P G D t t' A l -> @VTmG EM LR_P G D t t' A l ->
  @LRtm EM LRM lzero G Θ (tyCTrm D A l) (tyCTrm D A l) (boxt t) (boxt t').
Proof.
  intros HΘ HD HA Ht Ht' E Hl HV VAP VAM VP VM.
  assert (HVA : vp_ty (vpM EP EM) G D A A l) by exact (conj (eqty_refl _ _ _ _ _ HA) (conj VAP VAM)).
  exists (@CTrmRel EM LRM G Θ D D A A l l); split.
  - exact (LR_ctrm HΘ HD HD HA HA Hl (lequiv_refl _ _ Hl) HV HVA HVA).
  - assert (Hw : [ G ; Θ ⊢g boxt t : tyCTrm D A l @ lzero ])
      by (rewrite (@gm_layer_M EP EM EMl); apply wf_boxt; assumption).
    assert (Hw' : [ G ; Θ ⊢g boxt t' : tyCTrm D A l @ lzero ])
      by (rewrite (@gm_layer_M EP EM EMl); apply wf_boxt; assumption).
    pose proof (static_code_tm (i := lC) ltac:(unfold lle; cbn; lia) Ht Ht' E) as Htt.
    pose proof (@geq_tm_boxt EP EM EMl _ _ _ _ _ _ _ HΘ Hl HD HA Ht Ht' Htt E) as Hg.
    assert (Hn : @CTrmNf EM LRM G Θ D A l (boxt t) (boxt t'))
      by (apply ctrn_box; exact (conj E (conj Ht (conj Ht' (conj VP VM))))).
    exists (boxt t), (boxt t'). exact (conj (tmred_refl _ _ _ Hw) (conj (tmred_refl _ _ _ Hw') (conj Hg (conj Hg (conj Hn Hn))))).
Qed.

Lemma box_code_rel_tm {G G' G'' Δ A t t' l σ σ' γ} : GSubRel G' G σ σ' -> gwk_ok γ G'' G' -> [ ⊢ G'' ] ->
  [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Δ ⊢[ lC ] t : A @ l ] -> [ G ; Δ ⊢[ lC ] t' : A @ l ] -> tm_leq t t' ->
  @VCtxS EP EM EP LR_P G Δ -> @VTyS EP EM EP LR_P G Δ A A l ->
  [ G'' ; (Δ⦃σ⦄)⟦γ⟧ ⊢[ lC ] (t'⦃σ'⦄)⟦γ⟧ : (A⦃σ⦄)⟦γ⟧ @ l ] /\ tm_leq (t⦃σ⦄)⟦γ⟧ (t'⦃σ'⦄)⟦γ⟧.
Proof.
  intros Hσ Hγ HG'' HA Ht Ht' E VΔP VAP.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HA) as HΔ.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM Hσ HΔ compt_D)) as HD.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM (GSubRel_refl_r EP EM Hσ) HΔ compt_D)) as HD'.
  pose proof (CtxRelG_gwk (VΔP _ _ _ Hσ) Hγ) as XP.
  destruct (CtxRelG_escape_P XP HD HD') as [_ HDD].
  pose proof (gwa_ty Hγ HG'' (gs_ty EP EM Hσ HA)) as HA1.
  pose proof (gwa_ty Hγ HG'' (gs_ty EP EM (GSubRel_refl_r EP EM Hσ) HA)) as HA1'.
  (* the type, left and right *)
  pose proof (VTyG_gwk (VAP _ _ _ Hσ) Hγ) as YP.
  destruct (VTyG_escape_P XP HD HA1 (ctxconv_ty (i := lD) (eqctx_sym_D HDD) eq_refl HA1') YP) as [_ HAA].
  split.
  - eapply wf_conv; [exact (ctxconv_tm (i := lC) (eqctx_sym_D HDD) eq_refl
                              (gwa_tm Hγ HG'' (gs_tm EP EM (GSubRel_refl_r EP EM Hσ) Ht'))) |].
    exact HAA.
  - apply tm_leq_gwa, (tm_leq_trans _ (t⦃σ'⦄)).
    + exact ((proj1 (proj2 (proj2 (proj2 static_gsubst)))) _ _ _ _ _ _ Ht (lle_refl _) _ _ (GSubRel_agree EP EM Hσ)).
    + apply (proj1 (proj2 leq_gsubst_all)); [intros; apply gobj_leq_refl | exact E].
Qed.

Lemma VS_boxt {G Γ Δ A t t' l} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Δ ⊢[ lC ] t : A @ l ] -> [ G ; Δ ⊢[ lC ] t' : A @ l ] -> tm_leq t t' ->
  @VCtxS EP EM EP LR_P G Δ -> @VCtxS EP EM EM LR_P G Δ ->
  @VTyS EP EM EP LR_P G Δ A A l -> @VTyS EP EM EM LR_P G Δ A A l ->
  @VTmS EP EM EP LR_P G Δ t t' A l -> @VTmS EP EM EM LR_P G Δ t t' A l ->
  VTmSM G Γ (boxt t) (boxt t') (tyCTrm Δ A l) lzero.
Proof.
  intros HΓ Hl HΔ HA Ht Ht' E VΔP VΔM VAP VAM VtP VtM G' σ σ' Hσ.
  rewrite !gs_boxt, !gs_tyCTrm.
  intros G'' γ Hγ Θ e e' He. rewrite !gwa_boxt, !gwa_tyCTrm. cbn [subst Subst_ty Subst_tm subst_ty subst_tm].
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  pose proof (ctx_glob _ _ _ HΘ) as HG''.
  pose proof (gwa_ctx Hγ HG'' (gs_ctx EP EM Hσ HΔ compt_D)) as HD.
  assert (EL : gL G'' = gL G) by (rewrite (proj1 Hγ); exact (gsr_L _ _ _ _ _ _ Hσ)).
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσl.
  destruct (box_code_rel_tm Hσ Hγ HG'' HA Ht Ht' E VΔP VAP) as [Ht1' E1].
  apply LRtm_boxt; [exact HΘ | exact HD | exact (gwa_ty Hγ HG'' (gs_ty EP EM Hσ HA))
                   | exact (gwa_tm Hγ HG'' (gs_tm EP EM Hσ Ht)) | exact Ht1' | exact E1 | now rewrite EL
                   | exact (vp_ctx_refl_l HD (CtxRelG_gwk (VΔP _ _ _ Hσ) Hγ) (CtxRelG_gwk (VΔM _ _ _ Hσ) Hγ))
                   | exact (VTyG_gwk (VAP _ _ _ Hσl) Hγ) | exact (VTyG_gwk (VAM _ _ _ Hσl) Hγ)
                   | exact (VTmG_gwk (VtP _ _ _ Hσ) Hγ) | exact (VTmG_gwk (VtM _ _ _ Hσ) Hγ)].
Qed.

End ModalS.
