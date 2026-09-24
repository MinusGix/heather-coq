(** * The payload of static code at layer M (M2_DESIGN.md, 5d)

    [⊩^{≥P}_P] (07a:21–60) quantifies over weakenings, [k ≥ P] and related
    local substitutions only.  It is therefore [VTyG]/[VTmG]/[CtxRelG] of
    the [j = P] relation at an instance of layer P and at one of layer M.
    The payload of [box c] adds the typing of [c] at layer C; the
    declarative equalities at P make the payload convertible along
    related contexts and types. *)
From DeLaM.Typing Require Export CtxConv.
From DeLaM.Validity Require Export DeclConsequences.

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
    [ G ; Δ ⊢[ lC ] T @ l ] /\ [ G ; Δ ⊢[ lC ] T' @ l ] /\ [ G ; Δ ⊢[ lC ] T ≅ T' @ l ] /\
    VTyGP G Δ T T' l /\ VTyGM G Δ T T' l ;
  vp_tmc := fun G Δ A t t' l =>
    [ G ; Δ ⊢[ lC ] t : A @ l ] /\ [ G ; Δ ⊢[ lC ] t' : A @ l ] /\ [ G ; Δ ⊢[ lC ] t ≅ t' : A @ l ] /\
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
  - intros * (H1 & H2 & H & HP & HM).
    vp_split; [exact H2 | exact H1 | exact (eqty_sym _ _ _ _ _ _ H) | exact (VTyG_sym HP)
              | exact (VTyG_sym HM)].
  - intros * (H1 & H2 & H & HP & HM) (H1' & H2' & H' & HP' & HM').
    vp_split; [exact H1 | exact H2' | exact (eqty_trans _ _ _ _ _ _ _ H H')
              | exact (VTyG_trans HP HP') | exact (VTyG_trans HM HM')].
  - intros * (H1 & H2 & H & HP & HM).
    vp_split; [exact H2 | exact H1 | exact (eqtm_sym _ _ _ _ _ _ _ H) | exact (VTmG_sym HP)
              | exact (VTmG_sym HM)].
  - intros * (H1 & H2 & H & HP & HM) (H1' & H2' & H' & HP' & HM').
    vp_split; [exact H1 | exact H2' | exact (eqtm_trans _ _ _ _ _ _ _ _ H H')
              | exact (VTmG_trans HP HP') | exact (VTmG_trans HM HM')].
  (* conversion along related contexts *)
  - intros * (Hc & HcP & HcM) (H & HP & HM).
    vp_split; [exact (ctxconv_eqty (i := lD) Hc eq_refl H) | exact (VTyG_transport HcP HP)
              | exact (VTyG_transport HcM HM)].
  - intros * (Hc & HcP & HcM) (H1 & H2 & H & HP & HM).
    vp_split; [exact (ctxconv_ty (i := lC) Hc eq_refl H1) | exact (ctxconv_ty (i := lC) Hc eq_refl H2)
              | exact (ctxconv_eqty (i := lC) Hc eq_refl H) | exact (VTyG_transport HcP HP)
              | exact (VTyG_transport HcM HM)].
  - intros * (Hc & HcP & HcM) (H1 & H2 & H & HP & HM).
    vp_split; [exact (ctxconv_tm (i := lC) Hc eq_refl H1) | exact (ctxconv_tm (i := lC) Hc eq_refl H2)
              | exact (ctxconv_eqtm (i := lC) Hc eq_refl H) | exact (VTmG_transport HcP HP)
              | exact (VTmG_transport HcM HM)].
  (* conversion along related types *)
  - intros * (HA & HAP & HAM) (H1 & H2 & H & HP & HM).
    pose proof (eqty_sym _ _ _ _ _ _ HA) as HA'.
    vp_split; [eapply wf_conv; [exact H1 | exact HA'] | eapply wf_conv; [exact H2 | exact HA']
              | eapply eqtm_conv; [exact H | exact HA']
              | exact (VTmG_conv HP (VTyG_sym HAP)) | exact (VTmG_conv HM (VTyG_sym HAM))].
  (* level conversion *)
  - intros * Hl (H & HP & HM). pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    vp_split; [eapply eqty_lconv; eassumption | exact (VTyG_lconv HP Hl') | exact (VTyG_lconv HM Hl')].
  - intros * Hl (H1 & H2 & H & HP & HM). pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    vp_split; [eapply wft_lconv; eassumption | eapply wft_lconv; eassumption
              | eapply eqty_lconv; eassumption | exact (VTyG_lconv HP Hl') | exact (VTyG_lconv HM Hl')].
  - intros * Hl (H1 & H2 & H & HP & HM). pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    vp_split; [eapply wf_lconv; eassumption | eapply wf_lconv; eassumption
              | eapply eqtm_lconv; eassumption | exact (VTmG_lconv HP Hl') | exact (VTmG_lconv HM Hl')].
  (* global weakening *)
  - intros * Hγ HG' (H & HP & HM).
    vp_split; [exact (gwa_eqctx Hγ HG' H) | exact (CtxRelG_gwk HP Hγ) | exact (CtxRelG_gwk HM Hγ)].
  - intros * Hγ HG' (H & HP & HM).
    vp_split; [exact (gwa_eqty Hγ HG' H) | exact (VTyG_gwk HP Hγ) | exact (VTyG_gwk HM Hγ)].
  - intros * Hγ HG' (H1 & H2 & H & HP & HM).
    vp_split; [exact (gwa_ty Hγ HG' H1) | exact (gwa_ty Hγ HG' H2) | exact (gwa_eqty Hγ HG' H)
              | exact (VTyG_gwk HP Hγ) | exact (VTyG_gwk HM Hγ)].
  - intros * Hγ HG' (H1 & H2 & H & HP & HM).
    vp_split; [exact (gwa_tm Hγ HG' H1) | exact (gwa_tm Hγ HG' H2) | exact (gwa_eqtm Hγ HG' H)
              | exact (VTmG_gwk HP Hγ) | exact (VTmG_gwk HM Hγ)].
Qed.

(** The parameters of the [j = M] relation. *)
Definition LR_M : LRParams := {| lr_j := jM ; lr_vp := vpM |}.

End Payload.
