(** * The payload of static code at layer M (M2_DESIGN.md, 5d)

    [⊩^{≥P}_P] (07a:21–60) quantifies over weakenings, [k ≥ P] and related
    local substitutions only.  It is therefore [VTyG]/[VTmG]/[CtxRelG] of
    the [j = P] relation at an instance of layer P and at one of layer M.
    The payload of [box c] and [box c'] adds the typing of both at layer
    C; boxed code is compared up to level equivalence (the Static Code
    Lemma, 05:1055; M3_DESIGN.md E11).  The declarative equalities at P
    make the payload convertible along related contexts and types. *)
From DeLaM.Typing Require Export CtxConv.
From DeLaM.Validity Require Export Consequences.

#[local] Existing Instance LR_P.

Section Payload.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation VTyGP := (@VTyG EP LR_P).
Local Notation VTyGM := (@VTyG EM LR_P).
Local Notation VTmGP := (@VTmG EP LR_P).
Local Notation VTmGM := (@VTmG EM LR_P).
Local Notation CtxRelGP := (@CtxRelG EP LR_P).
Local Notation CtxRelGM := (@CtxRelG EM LR_P).

Definition vpM : VParam := {|
  vp_ctx := fun G Δ Δ' => [ G ⊢[ lD ] Δ ≅ Δ' ] /\ CtxRelGP G Δ Δ' /\ CtxRelGM G Δ Δ' ;
  vp_ty := fun G Δ T T' l =>
    [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] /\ VTyGP G Δ T T' l /\ VTyGM G Δ T T' l ;
  vp_tyc := fun G Δ T T' l =>
    ty_leq T T' /\ [ G ; Δ ⊢[ lC ] T @ l ] /\ [ G ; Δ ⊢[ lC ] T' @ l ] /\
    VTyGP G Δ T T' l /\ VTyGM G Δ T T' l ;
  vp_tmc := fun G Δ A t t' l =>
    tm_leq t t' /\ [ G ; Δ ⊢[ lC ] t : A @ l ] /\ [ G ; Δ ⊢[ lC ] t' : A @ l ] /\
    VTmGP G Δ t t' A l /\ VTmGM G Δ t t' A l |}.

Local Ltac vp_split := repeat match goal with |- _ /\ _ => split end.

#[export] Instance vpM_laws : VPLaws vpM.
Proof.
  constructor; cbn.
  (* symmetry and transitivity *)
  - intros * (H & HP & HM).
    vp_split; [exact (eqctx_sym_D H) | exact (CtxRelG_sym HP) | exact (CtxRelG_sym HM)].
  - intros * (H & HP & HM) (H' & HP' & HM').
    vp_split; [exact (eqctx_trans_D H H') | exact (CtxRelG_trans HP HP') | exact (CtxRelG_trans HM HM')].
  - intros * (H & HP & HM).
    vp_split; [exact (eqty_sym _ _ _ _ _ _ H) | exact (VTyG_sym HP) | exact (VTyG_sym HM)].
  - intros * (H & HP & HM) (H' & HP' & HM').
    vp_split; [exact (eqty_trans _ _ _ _ _ _ _ H H') | exact (VTyG_trans HP HP') | exact (VTyG_trans HM HM')].
  - intros * (E & H & H' & HP & HM).
    vp_split; [exact (ty_leq_sym _ _ E) | exact H' | exact H | exact (VTyG_sym HP) | exact (VTyG_sym HM)].
  - intros * (E & H & _ & HP & HM) (E' & _ & H' & HP' & HM').
    vp_split; [exact (ty_leq_trans _ _ _ E E') | exact H | exact H' | exact (VTyG_trans HP HP')
              | exact (VTyG_trans HM HM')].
  - intros * (E & H & H' & HP & HM).
    vp_split; [exact (tm_leq_sym _ _ E) | exact H' | exact H | exact (VTmG_sym HP) | exact (VTmG_sym HM)].
  - intros * (E & H & _ & HP & HM) (E' & _ & H' & HP' & HM').
    vp_split; [exact (tm_leq_trans _ _ _ E E') | exact H | exact H' | exact (VTmG_trans HP HP')
              | exact (VTmG_trans HM HM')].
  (* conversion along related contexts *)
  - intros * (Hc & HcP & HcM) (H & HP & HM).
    vp_split; [exact (ctxconv_eqty (i := lD) Hc eq_refl H) | exact (VTyG_transport HcP HP)
              | exact (VTyG_transport HcM HM)].
  - intros * (Hc & HcP & HcM) (E & H & H' & HP & HM).
    vp_split; [exact E | exact (ctxconv_ty (i := lC) Hc eq_refl H) | exact (ctxconv_ty (i := lC) Hc eq_refl H')
              | exact (VTyG_transport HcP HP) | exact (VTyG_transport HcM HM)].
  - intros * (Hc & HcP & HcM) (E & H & H' & HP & HM).
    vp_split; [exact E | exact (ctxconv_tm (i := lC) Hc eq_refl H) | exact (ctxconv_tm (i := lC) Hc eq_refl H')
              | exact (VTmG_transport HcP HP) | exact (VTmG_transport HcM HM)].
  (* conversion along related types *)
  - intros * (HA & HAP & HAM) (E & H & H' & HP & HM).
    pose proof (eqty_sym _ _ _ _ _ _ HA) as HA'.
    vp_split; [exact E | eapply wf_conv; [exact H | exact HA'] | eapply wf_conv; [exact H' | exact HA']
              | exact (VTmG_conv HP (VTyG_sym HAP)) | exact (VTmG_conv HM (VTyG_sym HAM))].
  (* level conversion *)
  - intros * Hl (H & HP & HM). pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    vp_split; [eapply eqty_lconv; eassumption | exact (VTyG_lconv HP Hl') | exact (VTyG_lconv HM Hl')].
  - intros * Hl (E & H & H' & HP & HM). pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    vp_split; [exact E | eapply wft_lconv; eassumption | eapply wft_lconv; eassumption
              | exact (VTyG_lconv HP Hl') | exact (VTyG_lconv HM Hl')].
  - intros * Hl (E & H & H' & HP & HM). pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    vp_split; [exact E | eapply wf_lconv; eassumption | eapply wf_lconv; eassumption
              | exact (VTmG_lconv HP Hl') | exact (VTmG_lconv HM Hl')].
  (* level equivalence of syntax *)
  - intros * (H & HP & HM) (H' & HP' & HM') Ex.
    vp_split; [exact (leq_eqctx_D _ _ (eqctx_wf_l (i := lD) eq_refl H) (eqctx_wf_l (i := lD) eq_refl H') Ex)
              | exact (CtxRelG_leq HP HP' Ex) | exact (CtxRelG_leq HM HM' Ex)].
  - intros * (H & HP & HM) (H' & HP' & HM') Ex.
    vp_split; [exact (leq_eqty compt_D (eqty_wf_l (i := lD) eq_refl H) (eqty_wf_l (i := lD) eq_refl H') Ex)
              | exact (VTyG_leq HP HP' Ex) | exact (VTyG_leq HM HM' Ex)].
  - intros * (E & H & _ & HP & HM) (E' & H' & _ & HP' & HM') Ex.
    vp_split; [exact Ex | exact H | exact H' | exact (VTyG_leq HP HP' Ex) | exact (VTyG_leq HM HM' Ex)].
  - intros * (E & H & _ & HP & HM) (E' & H' & _ & HP' & HM') Ex.
    vp_split; [exact Ex | exact H | exact H' | exact (VTmG_leq HP HP' Ex) | exact (VTmG_leq HM HM' Ex)].
  (* global weakening *)
  - intros * Hγ HG' (H & HP & HM).
    vp_split; [exact (gwa_eqctx Hγ HG' H) | exact (CtxRelG_gwk HP Hγ) | exact (CtxRelG_gwk HM Hγ)].
  - intros * Hγ HG' (H & HP & HM).
    vp_split; [exact (gwa_eqty Hγ HG' H) | exact (VTyG_gwk HP Hγ) | exact (VTyG_gwk HM Hγ)].
  - intros * Hγ HG' (E & H & H' & HP & HM).
    vp_split; [exact (ty_leq_gwa _ _ _ E) | exact (gwa_ty Hγ HG' H) | exact (gwa_ty Hγ HG' H')
              | exact (VTyG_gwk HP Hγ) | exact (VTyG_gwk HM Hγ)].
  - intros * Hγ HG' (E & H & H' & HP & HM).
    vp_split; [exact (tm_leq_gwa _ _ _ E) | exact (gwa_tm Hγ HG' H) | exact (gwa_tm Hγ HG' H')
              | exact (VTmG_gwk HP Hγ) | exact (VTmG_gwk HM Hγ)].
Qed.

(** The parameters of the [j = M] relation. *)
Definition LR_M : LRParams := {| lr_j := jM ; lr_vp := vpM |}.

End Payload.

(** The meta-functions' neutral applications at payload-related arguments
    (M5_DESIGN.md G3): the payload's P-validity escapes at the identity
    world to the generic equivalence at P. *)
Section PayloadNe.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EGM : GenericEqM EP EM}.

#[export] Instance VPNe_M : @VPNe EM (LR_M EP EM).
Proof.
  pose proof (@gm_layer_M EP EM EGM) as EM'. pose proof (@gm_layer_P EP EM EGM) as EP'.
  constructor; cbn [lr_j lr_vp LR_M vpM vp_ctx vp_ty].
  - intros G Γ l T ν ν' Δ Δ' _ Hl HT (HΔ & HP & _) HE Hν.
    rewrite EM' in HT, HE.
    apply gne_tm_capp; [exact Hl | exact HT | exact (eqctx_wf_l (i := lD) eq_refl HΔ) | | exact HE | exact Hν].
    apply (CtxRel_escape (E := EP) (LP := LR_P)); [exact (HP _ _ (gwk_ok_id G)) | rewrite EP' ..].
    + exact (eqctx_wf_l (i := lD) eq_refl HΔ).
    + exact (eqctx_wf_r (i := lD) eq_refl HΔ).
  - intros G Γ Δ l l' T ν ν' A A' _ Hl Hl' HT (_ & HPc & _) (HA & HPA & _) HE Hν.
    rewrite EM' in HT, HE.
    pose proof (eqty_wf_l (i := lD) eq_refl HA) as HAw.
    pose proof (ctx_of_wf_ty (i := lD) eq_refl HAw) as HΔw.
    apply (gne_tm_tapp (Δ := Δ) (l := l)); [exact HΔw | exact Hl | exact Hl' | exact HT | exact HAw | | exact HE | exact Hν].
    (* the generic equivalence at P, from validity at the identity *)
    assert (Hc : @CtxRel EP LR_P G Δ Δ) by exact (HPc _ _ (gwk_ok_id G)).
    assert (HΔg : [ G ; Δ ⊢[ @ge_layer EP ] ]) by (rewrite EP'; exact HΔw).
    destruct (HPA _ _ (gwk_ok_id G) _ _ _ (SubRel_id_rel _ _ Hc HΔg)) as [R HR].
    destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & X). cbn [gwa] in X.
    assert (Hid : forall n, llk (lshift 0) n = var n) by (intros n; cbn; f_equal; lia).
    rewrite (subst_id_ty _ _ (wf_ty_nf HAw) Hid),
      (subst_id_ty _ _ (wf_ty_nf (eqty_wf_r (i := lD) eq_refl HA)) Hid) in X.
    exact X.
Qed.

End PayloadNe.
