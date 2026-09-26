(** * Decidable type checking: checking (M7_DESIGN.md C1, J3.5)

    One step of the induction on size: checking a term against a
    well-formed type. A synthesizing term: its type is unique
    ([type_uniq]), so checking is its synthesis plus conversion (M6). An
    abstraction or a [box]: the expected type is normalized; its head must
    be the construct's former (head discrimination refutes otherwise),
    whose components give the body's type. A typing of the construct at
    the expected type is inverted and moved onto those components by
    injectivity. *)
From DeLaM.Validity Require Export TCSynth.

Section Step.
Context (n : nat) (IH : IHsz n).

Let ihT T : sz_ty T < n -> nlr_ty T -> TYD T := proj1 IH T.
Let ihC t : sz_tm t < n -> nlr_tm t -> CKD t := proj1 (proj2 IH) t.

Ltac szl := cbn [sz_ty sz_tm sz_ctx sz_l] in *; lia.

Lemma ck_synth t : sz_tm t <= n -> nlr_tm t -> synth t -> CKD t.
Proof.
  intros Hsz Hn Hs G i Γ T k HT.
  pose proof (ctx_of_wf_ty (typeof_idem i) HT) as HΓ.
  destruct (sy_step n IH t Hsz Hn Hs G i Γ HΓ) as [(T' & k' & Ht') | N]; [| right; intros H; exact (N _ _ H)].
  destruct (lvl_eq_dec (gL G) k k') as [Q | Q];
    [| right; intros H; exact (Q (proj1 (type_uniq t Hn Hs _ _ _ _ _ _ _ H Ht')))].
  pose proof (wft_lvl Q (wf_tm_ty_any Ht')) as HT'.
  destruct (decl_eqty_dec_any HT HT') as [E | N].
  - left; exact (wf_conv _ _ _ _ _ _ _ (wf_lvl Q Ht') E).
  - right; intros H; exact (N (proj2 (type_uniq t Hn Hs _ _ _ _ _ _ _ H Ht'))).
Qed.

Lemma ck_lam l l' A b : sz_tm (lam l l' A b) <= n -> nlr_tm (lam l l' A b) -> CKD (lam l l' A b).
Proof.
  intros Hsz [HnA Hnb] G i Γ T k HT.
  pose proof (ctx_of_wf_ty (typeof_idem i) HT) as HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hv]; [right; intros H; eapply typed_V; [| exact H]; cbn; tauto |].
  pose proof (compt_typeof i) as Hc. pose proof (typeof_idem i) as Hi.
  destruct (whnf_normalization_ty_c Hc HT) as (W & _ & Hw & EW).
  destruct (pi_view W) as [(m & m' & A1 & B1 & ->) | Nh];
    [| right; intros H; destruct (inva_lam H) as (B & _ & _ & E); apply Nh;
       exact (head_of_eq Hc Hw (whnf_tyPi _ _ _ _) EW E)].
  pose proof (eqty_wf_r Hi EW) as HW. destruct (inv_ty_pi HW) as ((_ & Hm & Hm' & HA1 & HB1) & Hk).
  assert (Inv : [ G ; Γ ⊢[ i ] lam l l' A b : T @ k ] ->
    lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\ lequiv (gL G) l m /\ lequiv (gL G) l' m' /\
    [ G ; Γ ⊢[ typeof i ] A ≅ A1 @ l ] /\ lvl_eq (gL G) k (lmax l l') /\
    [ G ; Γ ,, A @ l ⊢[ i ] b : B1 @ l' ]).
  { intros H. destruct (inva_lam H) as (B & (_ & Hl & Hl' & HA & Hb) & Hk0 & E0).
    destruct (pi_inj_c Hc (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E0)) as (Q1 & Q2 & EA & EB).
    pose proof (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EA) Q1) as EA'.
    assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
    pose proof (stab_eqty Hi EA (lequiv_sym _ _ _ Q1) HΓA EB) as EB'.
    refine (conj Hl (conj Hl' (conj HA (conj Q1 (conj Q2 (conj EA' (conj Hk0 _))))))).
    exact (wf_conv _ _ _ _ _ _ _ Hb (eqty_lconv _ _ _ _ _ _ _ EB' Q2)). }
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros H; apply N, (Inv H)].
  destruct (ihT A ltac:(szl) HnA G i Γ l HΓ) as [HA | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lequiv_dec (gL G) l m) as [Q1 | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lequiv_dec (gL G) l' m') as [Q2 | N]; [| right; intros H; apply N, (Inv H)].
  destruct (decl_eqty_dec_any (lift_to_typeof_ty HA) (wft_lconv _ _ _ _ _ _ HA1 Q1)) as [EA | N];
    [| right; intros H; apply N, (Inv H)].
  destruct (lvl_eq_dec (gL G) k (lmax l l')) as [Q | N]; [| right; intros H; apply N, (Inv H)].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  pose proof (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EA) (lequiv_sym _ _ _ Q1)) as EA1.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EA1 (lequiv_sym _ _ _ Q1) HΓA HB1) Q2) as HB1'.
  destruct (ihC b ltac:(szl) Hnb G i _ _ _ HB1') as [Hb | N]; [| right; intros H; apply N, (Inv H)].
  left. refine (wf_conv _ _ _ _ _ _ _ (wf_lvl Q (wf_lam _ _ _ _ _ _ _ _ Hv Hl Hl' HA Hb)) _).
  eapply eqty_trans; [exact EW |]. apply (eqty_lvl Hk).
  exact (eqty_pi _ _ _ _ _ _ _ _ _ _ _ (typeof_notV i) (lequiv_sym _ _ _ Q1) (lequiv_sym _ _ _ Q2) HA1 EA1
           (eqty_refl _ _ _ _ _ HB1)).
Qed.

Lemma ck_boxT A0 : sz_tm (boxT A0) <= n -> nlr_tm (boxT A0) -> CKD (boxT A0).
Proof.
  intros Hsz Hn G i Γ T k HT. pose proof (ctx_of_wf_ty (typeof_idem i) HT) as HΓ.
  destruct (layer_eq_dec i lM) as [-> | NM]; [| right; intros H; exact (NM (typed_m_only H I))].
  destruct (whnf_normalization_ty_c compt_M HT) as (W & _ & Hw & EW).
  destruct (ctyp_view W) as [(Δ0 & l0 & ->) | Nh];
    [| right; intros H; destruct (inv_boxT eq_refl H) as (Δ & l & _ & _ & E); apply Nh;
       exact (head_of_eq compt_M Hw (whnf_tyCTyp _ _) EW E)].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW. destruct (inv_ty_CTyp HW) as ((_ & _ & HΔ0 & Hl0) & Hk).
  destruct (ihT A0 ltac:(szl) Hn G lC Δ0 l0 HΔ0) as [HA | N].
  - left. exact (wf_conv _ _ _ _ _ _ _ (wf_lvl Hk (wf_boxT _ _ _ _ _ HΓ Hl0 HΔ0 HA)) EW).
  - right; intros H. destruct (inv_boxT eq_refl H) as (Δ & l & (_ & _ & Hl & HΔ & HA) & _ & E).
    destruct (ctyp_inj (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E)) as (Q & EΔ).
    apply N. exact (wft_lconv _ _ _ _ _ _ (ctxconv_ty (eqctx_sym_D EΔ) (i := lC) eq_refl HA) Q).
Qed.

Lemma ck_boxt a : sz_tm (boxt a) <= n -> nlr_tm (boxt a) -> CKD (boxt a).
Proof.
  intros Hsz Hn G i Γ T k HT. pose proof (ctx_of_wf_ty (typeof_idem i) HT) as HΓ.
  destruct (layer_eq_dec i lM) as [-> | NM]; [| right; intros H; exact (NM (typed_m_only H I))].
  destruct (whnf_normalization_ty_c compt_M HT) as (W & _ & Hw & EW).
  destruct (ctrm_view W) as [(Δ0 & A0 & l0 & ->) | Nh];
    [| right; intros H; destruct (inv_boxt eq_refl H) as (Δ & A & l & _ & _ & E); apply Nh;
       exact (head_of_eq compt_M Hw (whnf_tyCTrm _ _ _) EW E)].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW. destruct (inv_ty_CTrm HW) as ((_ & _ & HΔ0 & HA0 & Hl0) & Hk).
  destruct (ihC a ltac:(szl) Hn G lC Δ0 A0 l0 HA0) as [Ha | N].
  - left. exact (wf_conv _ _ _ _ _ _ _ (wf_lvl Hk (wf_boxt _ _ _ _ _ _ HΓ Hl0 HΔ0 HA0 Ha)) EW).
  - right; intros H. destruct (inv_boxt eq_refl H) as (Δ & A & l & (_ & _ & Hl & HΔ & HA & Ha) & _ & E).
    destruct (ctrm_inj (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E)) as (Q & EΔ & EA).
    apply N. pose proof (ctxconv_tm (eqctx_sym_D EΔ) (i := lC) eq_refl Ha) as Ha'.
    exact (wf_conv _ _ _ _ _ _ _ (wf_lconv _ _ _ _ _ _ _ Ha' Q) EA).
Qed.

Lemma ck_ulam m l b : sz_tm (ulam m l b) <= n -> nlr_tm (ulam m l b) -> CKD (ulam m l b).
Proof.
  intros Hsz Hn G i Γ T k HT. pose proof (ctx_of_wf_ty (typeof_idem i) HT) as HΓ.
  destruct (layer_eq_dec i lM) as [-> | NM]; [| right; intros H; exact (NM (typed_m_only H I))].
  destruct (whnf_normalization_ty_c compt_M HT) as (W & _ & Hw & EW).
  destruct (upi_view W) as [(m0 & l0 & T0 & ->) | Nh];
    [| right; intros H; destruct (inv_ulam eq_refl H) as (T1 & _ & _ & E); apply Nh;
       exact (head_of_eq compt_M Hw (whnf_tyUPi _ _ _) EW E)].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW. destruct (inv_ty_upi HW) as ((_ & _ & Hm0 & Hl0 & HT0) & Hk).
  assert (Inv : [ G ; Γ ⊢[ lM ] ulam m l b : T @ k ] -> m = m0 /\ lwf (m + gL G) l /\
    lequiv (m + gL G) l l0 /\ [ gctx_uwk m G ; Γ⟨ush m⟩ᵤ ⊢[ lM ] b : T0 @ l ]).
  { intros H. destruct (inv_ulam eq_refl H) as (T1 & (_ & _ & Hm & Hl & HT1 & Hb1) & _ & E0).
    destruct (upi_inj (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E0)) as (<- & Q & ET).
    refine (conj eq_refl (conj Hl (conj (lequiv_sym _ _ _ Q) _))).
    exact (wf_conv _ _ _ _ _ _ _ Hb1 (eqty_lconv _ _ _ _ _ _ _ ET (lequiv_sym _ _ _ Q))). }
  destruct (Nat.eq_dec m m0) as [<- | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lwf_Dec (m + gL G) l) as [Hl | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lequiv_dec (m + gL G) l l0) as [Q | N]; [| right; intros H; apply N, (Inv H)].
  pose proof (wft_lconv _ _ _ _ _ _ HT0 Q) as HT0'.
  destruct (ihC b ltac:(szl) Hn _ lM _ _ _ HT0') as [Hb | N]; [| right; intros H; apply N, (Inv H)].
  left. refine (wf_conv _ _ _ _ _ _ _ (wf_lvl Hk (wf_ulam _ _ _ _ _ _ HΓ Hm0 Hl HT0' Hb)) _).
  eapply eqty_trans; [exact EW |]. apply (eqty_lvl Hk).
  exact (eqty_upi _ _ _ _ _ _ _ HΓ Hm0 (lequiv_sym _ _ _ Q) HT0 (eqty_refl _ _ _ _ _ HT0)).
Qed.

Lemma ck_clam l b : sz_tm (clam l b) <= n -> nlr_tm (clam l b) -> CKD (clam l b).
Proof.
  intros Hsz Hn G i Γ T k HT. pose proof (ctx_of_wf_ty (typeof_idem i) HT) as HΓ.
  destruct (layer_eq_dec i lM) as [-> | NM]; [| right; intros H; exact (NM (typed_m_only H I))].
  destruct (whnf_normalization_ty_c compt_M HT) as (W & _ & Hw & EW).
  destruct (cpi_view W) as [(l0 & T0 & ->) | Nh];
    [| right; intros H; destruct (inv_clam eq_refl H) as (T1 & _ & _ & E); apply Nh;
       exact (head_of_eq compt_M Hw (whnf_tyCPi _ _) EW E)].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW. destruct (inv_ty_cpi HW) as ((_ & _ & Hl0 & HT0) & Hk).
  assert (Inv : [ G ; Γ ⊢[ lM ] clam l b : T @ k ] -> lwf (gL G) l /\ lequiv (gL G) l l0 /\
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] b : T0 @ l ]).
  { intros H. destruct (inv_clam eq_refl H) as (T1 & (_ & _ & Hl & HT1 & Hb1) & _ & E0).
    destruct (cpi_inj (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E0)) as (Q & ET).
    refine (conj Hl (conj (lequiv_sym _ _ _ Q) _)).
    exact (wf_conv _ _ _ _ _ _ _ Hb1 (eqty_lconv _ _ _ _ _ _ _ ET (lequiv_sym _ _ _ Q))). }
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lequiv_dec (gL G) l l0) as [Q | N]; [| right; intros H; apply N, (Inv H)].
  pose proof (wft_lconv _ _ _ _ _ _ HT0 Q) as HT0'.
  destruct (ihC b ltac:(szl) Hn _ lM _ _ _ HT0') as [Hb | N]; [| right; intros H; apply N, (Inv H)].
  left. refine (wf_conv _ _ _ _ _ _ _ (wf_lvl (lvl_eq_trans Hk (or_intror (lequiv_sym _ _ _ Q)))
                                         (wf_clam _ _ _ _ _ HΓ Hl HT0' Hb)) _).
  eapply eqty_trans; [exact EW |]. apply (eqty_lvl Hk).
  exact (eqty_cpi _ _ _ _ _ _ HΓ (lequiv_sym _ _ _ Q) HT0 (eqty_refl _ _ _ _ _ HT0)).
Qed.

Lemma ck_tlam l l' b : sz_tm (tlam l l' b) <= n -> nlr_tm (tlam l l' b) -> CKD (tlam l l' b).
Proof.
  intros Hsz Hn G i Γ T k HT. pose proof (ctx_of_wf_ty (typeof_idem i) HT) as HΓ.
  destruct (layer_eq_dec i lM) as [-> | NM]; [| right; intros H; exact (NM (typed_m_only H I))].
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (whnf_normalization_ty_c compt_M HT) as (W & _ & Hw & EW).
  destruct (tpi_view W) as [(Δ0 & l0 & l0' & T0 & ->) | Nh];
    [| right; intros H; destruct (inv_tlam eq_refl H) as (Δ & T1 & _ & _ & E); apply Nh;
       exact (head_of_eq compt_M Hw (whnf_tyTPi _ _ _ _) EW E)].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW.
  destruct (inv_ty_tpi HW) as ((_ & _ & HΔ0 & Hl0 & Hl0' & HT0) & Hk).
  (* the binder's declaration at another level *)
  assert (HE : forall l1, lwf (gL G) l1 -> lequiv (gL G) l0 l1 ->
    GEq (gext G (gdTy Δ0 lD l0)) (gext G (gdTy Δ0 lD l1))).
  { intros l1 Hl1 Q. apply GEq_ext; [exact (GEq_refl _ HG) | exact (wfg_ty' HΔ0 (or_intror eq_refl) Hl0) |
                                    exact (wfg_ty' HΔ0 (or_intror eq_refl) Hl1) |].
    exact (conj eq_refl (conj (or_intror eq_refl) (conj Q (eqc_refl _ _ _ HΔ0)))). }
  assert (Inv : [ G ; Γ ⊢[ lM ] tlam l l' b : T @ k ] -> lwf (gL G) l /\ lwf (gL G) l' /\
    lequiv (gL G) l l0 /\ lequiv (gL G) l' l0' /\ [ gext G (gdTy Δ0 lD l) ; Γ⟪S⟫ ⊢[ lM ] b : T0 @ l' ]).
  { intros H. destruct (inv_tlam eq_refl H) as (Δ & T1 & (_ & _ & HΔ & Hl & Hl' & HT1 & Hb1) & _ & E0).
    destruct (tpi_inj (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E0)) as (Q1 & Q2 & EΔ & ET).
    refine (conj Hl (conj Hl' (conj (lequiv_sym _ _ _ Q1) (conj (lequiv_sym _ _ _ Q2) _)))).
    assert (HE2 : GEq (gext G (gdTy Δ lD l)) (gext G (gdTy Δ0 lD l))).
    { apply GEq_ext; [exact (GEq_refl _ HG) | exact (wfg_ty' HΔ (or_intror eq_refl) Hl) |
                      exact (wfg_ty' HΔ0 (or_intror eq_refl) Hl) |].
      exact (conj eq_refl (conj (or_intror eq_refl) (conj (lequiv_refl _ _ Hl) (eqctx_sym_D EΔ)))). }
    pose proof (gconv_tm HE2 eq_refl Hb1) as Hb2.
    pose proof (gconv_eqty (HE l Hl Q1) eq_refl ET) as ET2.
    exact (wf_conv _ _ _ _ _ _ _ Hb2 (eqty_lconv _ _ _ _ _ _ _ ET2 (lequiv_sym _ _ _ Q2))). }
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lequiv_dec (gL G) l l0) as [Q1 | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lequiv_dec (gL G) l' l0') as [Q2 | N]; [| right; intros H; apply N, (Inv H)].
  pose proof (wft_lconv _ _ _ _ _ _ (gconv_ty (HE l Hl (lequiv_sym _ _ _ Q1)) HT0) Q2) as HT0'.
  destruct (ihC b ltac:(szl) Hn _ lM _ _ _ HT0') as [Hb | N]; [| right; intros H; apply N, (Inv H)].
  left. refine (wf_conv _ _ _ _ _ _ _ (wf_lvl (lvl_eq_trans Hk (or_intror (lequiv_sym _ _ _ Q2)))
                                         (wf_tlam _ _ _ _ _ _ _ HΓ HΔ0 Hl Hl' HT0' Hb)) _).
  eapply eqty_trans; [exact EW |]. apply (eqty_lvl Hk).
  exact (eqty_tpi _ _ _ _ _ _ _ _ _ _ HΓ HΔ0 HΔ0 (eqc_refl _ _ _ HΔ0) (lequiv_sym _ _ _ Q1) (lequiv_sym _ _ _ Q2)
           HT0 (eqty_refl _ _ _ _ _ HT0) HT0').
Qed.

(** ** The step *)

Lemma ck_step t : sz_tm t <= n -> nlr_tm t -> CKD t.
Proof.
  intros Hsz Hn. destruct (synth_dec t) as [Hs | Hs]; [exact (ck_synth t Hsz Hn Hs) |].
  destruct t; cbn in Hs; try (exfalso; exact (Hs I));
    first [ apply ck_lam | apply ck_boxT | apply ck_boxt | apply ck_ulam | apply ck_clam | apply ck_tlam ];
    assumption.
Qed.

End Step.
