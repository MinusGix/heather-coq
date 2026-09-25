(** * The fundamental theorem with global substitutions, layer M

    Every M-derivation is valid at related global substitutions, for the
    [j = M] relation ([LR_M]) at the M instance.  Premises at layers C
    and P are valid by the fundamental theorem at P ([fundamentalS_le]),
    which gives the static code's payload and the contexts of [□].  The
    global variables' images are MLTT types and terms, related at
    [⊩^{≥P}_P], which the Layering Restriction carries to [LR_M]. *)
From DeLaM.Validity Require Export FundamentalS LetboxS.

Section FundamentalM.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsF : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation GValid := (GValid EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).

(** ** The judgments' semantics at M *)

Definition SemCtxM (G : gctx) (Γ : ctx) : Prop := GValid G /\ VCtxSM G Γ.
Definition SemTyM (G : gctx) (Γ : ctx) (T T' : ty) (l : lvl) : Prop := SemCtxM G Γ /\ VTySM G Γ T T' l.
Definition SemTmM (G : gctx) (Γ : ctx) (t t' : tm) (T : ty) (l : lvl) : Prop :=
  SemCtxM G Γ /\ VTySM G Γ T T l /\ VTmSM G Γ t t' T l.

(** ** From [⊩^{≥P}_P] at the M instance to [LR_M], on MLTT syntax *)

Lemma VCtxS_toM {G Δ} : [ G ; Δ ⊢[ lD ] ] -> @VCtxS EP EM EM LR_P G Δ -> VCtxSM G Δ.
Proof.
  intros HΔ H G' σ σ' Hσ.
  apply (proj1 (CtxRelG_layer LR_P LRM (mltt_wf_ctx (gs_ctx EP EM Hσ HΔ) ltac:(discriminate))
                  (mltt_wf_ctx (gs_ctx EP EM (GSubRel_refl_r EP EM Hσ) HΔ) ltac:(discriminate)))).
  exact (H _ _ _ Hσ).
Qed.

Lemma VTyS_toM {G Δ A A' l} : [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Δ ⊢[ lD ] A' @ l ] ->
  @VTyS EP EM EM LR_P G Δ A A' l -> VTySM G Δ A A' l.
Proof.
  intros HA HA' H G' σ σ' Hσ.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HA) as HΔ.
  apply (proj1 (VTyG_layer LR_P LRM (mltt_wf_ctx (gs_ctx EP EM Hσ HΔ) ltac:(discriminate))
                  (mltt_wf_ty (gs_ty EP EM Hσ HA) ltac:(discriminate))
                  (mltt_wf_ty (gs_ty EP EM (GSubRel_refl_r EP EM Hσ) HA') ltac:(discriminate)))).
  exact (H _ _ _ Hσ).
Qed.

Lemma lle_M i : lle i lM.
Proof. unfold lle; destruct i; cbn; lia. Qed.

Lemma lle_ge_M i : lle i (@ge_layer EM).
Proof. rewrite (@gm_layer_M EP EM EMl). apply lle_M. Qed.

(** ** Global variables *)

Lemma FM_tygvar {G Γ U Δ i' l d d'} : SemCtxM G Γ -> in_gctx (gΨ G) U (gdTy Δ i' l) ->
  [ G ; Γ ⊢[ lM ] ] -> lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n B k, in_ctx Δ n B k -> SemTmM G Γ (llk d n) (llk d' n) B[d] k) ->
  SemTyM G Γ (tyGvar U d) (tyGvar U d') l.
Proof.
  intros HS Hin HΓ Ht Nd Ht' Nd' Hv. pose proof HS as (HG & _).
  pose proof (ctx_glob _ _ _ HΓ) as HGw.
  pose proof (in_gctx_DWf HGw Hin) as HΔ; cbn in HΔ.
  pose proof (in_gctx_DLayer HGw Hin) as Hi'; cbn in Hi'.
  destruct (HG _ _ Hin) as [_ VM].
  split; [exact HS |].
  refine (VS_tygvar EP EM (E := EM) (LP := LRM)
            (fun G' Δ0 T T' l0 Hm HmT HmT' H => proj1 (VTyG_layer LR_P LRM Hm HmT HmT') (proj2 H))
            Hin (lle_ge_M _) _ HΓ HΔ (VCtxS_toM HΔ VM) Ht Nd Ht' Nd'
            (fun n B k h => proj2 (proj2 (Hv n B k h)))).
  destruct Hi' as [-> | ->]; discriminate.
Qed.

Lemma FM_gvar {G Γ u Δ i' A l d d'} : SemCtxM G Γ -> in_gctx (gΨ G) u (gdTm Δ i' A l) ->
  [ G ; Γ ⊢[ lM ] ] -> lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n B k, in_ctx Δ n B k -> SemTmM G Γ (llk d n) (llk d' n) B[d] k) ->
  (forall n B k, in_ctx Δ n B k -> SemTmM G Γ (llk d n) (llk d n) B[d] k) ->
  SemTmM G Γ (gvar u d) (gvar u d') A[d] l.
Proof.
  intros HS Hin HΓ Ht Nd Ht' Nd' Hv Hvv. pose proof HS as (HG & _).
  pose proof (ctx_glob _ _ _ HΓ) as HGw.
  pose proof (in_gctx_DWf HGw Hin) as HA; cbn in HA.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HA) as HΔ.
  destruct (HG _ _ Hin) as (_ & VM & _ & VAM).
  pose proof (VTyS_toM HA HA VAM) as VA.
  split; [exact HS | split].
  - exact (VTyS_inst EP EM HΓ HΔ (VCtxS_toM HΔ VM) Ht Nd Ht Nd
             (fun n B k h => proj2 (proj2 (Hvv n B k h))) VA).
  - exact (VS_gvar EP EM (E := EM) (LP := LRM)
             (fun G' Δ0 t t' A0 l0 Hm HmA H => proj1 (VTmG_layer LR_P LRM Hm HmA) (proj2 H))
             Hin (lle_ge_M _) HΓ HA (VCtxS_toM HΔ VM) VA Ht Nd Ht' Nd'
             (fun n B k h => proj2 (proj2 (Hv n B k h))) (fun n B k h => proj2 (proj2 (Hvv n B k h)))).
Qed.

(** ** Contextual types and [box] *)

Local Notation SemCtxP := (SemCtx EP EM).
Local Notation SemTyP := (SemTy EP EM).
Local Notation SemTmP := (SemTm EP EM).
Local Notation SemCtxEqP := (SemCtxEq EP EM).

Lemma VTmSM_refl_l {G Γ t t' T l} : GValid G -> VCtxSM G Γ -> VTySM G Γ T T l -> VTmSM G Γ t t' T l ->
  VTmSM G Γ t t T l.
Proof. intros HG HΓ HT H. exact (VTmS_trans EP EM H (VTmS_sym EP EM HG HΓ HT H)). Qed.

Lemma VTySM_refl_l {G Γ T T' l} : GValid G -> VCtxSM G Γ -> VTySM G Γ T T' l -> VTySM G Γ T T l.
Proof. intros HG HΓ H. exact (VTyS_trans EP EM H (VTyS_sym EP EM HG HΓ H)). Qed.

Lemma FM_CTyp {G Γ Δ l} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l ->
  SemCtxP G Δ -> SemTyM G Γ (tyCTyp Δ l) (tyCTyp Δ l) lzero.
Proof.
  intros HS HΓ HΔ Hl (_ & VP & VM). split; [exact HS |].
  exact (VS_CTyp EP EM HΓ HΔ HΔ Hl (lequiv_refl _ _ Hl) VP VM).
Qed.

Lemma FM_CTyp_eq {G Γ Δ Δ' l l'} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  lequiv (gL G) l l' -> SemCtxEqP G Δ Δ' -> SemTyM G Γ (tyCTyp Δ l) (tyCTyp Δ' l') lzero.
Proof.
  intros HS HΓ HΔΔ' Hl [VP VM]. split; [exact HS |].
  exact (VS_CTyp EP EM HΓ (eqctx_wf_l (i := lD) eq_refl HΔΔ') (eqctx_wf_r (i := lD) eq_refl HΔΔ')
           (lequiv_wf_l _ _ _ Hl) Hl VP VM).
Qed.

Lemma FM_CTrm {G Γ Δ T l} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] ->
  lwf (gL G) l -> SemTyP G Δ T T l -> SemTyM G Γ (tyCTrm Δ T l) (tyCTrm Δ T l) lzero.
Proof.
  intros HS HΓ HT Hl ((HG & VP & VM) & VTP & VTM). split; [exact HS |].
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HT) as HΔ.
  exact (VS_CTrm EP EM HG HΓ HΔ HΔ HT HT Hl (lequiv_refl _ _ Hl) VP VM VP VM VTP VTM).
Qed.

Lemma FM_CTrm_eq {G Γ Δ Δ' T T' l l'} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] -> lequiv (gL G) l l' ->
  SemCtxEqP G Δ Δ' -> SemTyP G Δ T T' l -> SemTyM G Γ (tyCTrm Δ T l) (tyCTrm Δ' T' l') lzero.
Proof.
  intros HS HΓ HΔΔ' HTT Hl [VEP VEM] ((HG & VP & VM) & VTP & VTM). split; [exact HS |].
  pose proof (eqty_wf_r (i := lD) eq_refl HTT) as HT'.
  assert (HT'2 : [ G ; Δ' ⊢[ lD ] T' @ l' ])
    by (eapply wft_lconv; [exact (ctxconv_ty (i := lD) HΔΔ' eq_refl HT') | exact (lequiv_sym _ _ _ Hl)]).
  exact (VS_CTrm EP EM HG HΓ (eqctx_wf_l (i := lD) eq_refl HΔΔ') (eqctx_wf_r (i := lD) eq_refl HΔΔ')
           (eqty_wf_l (i := lD) eq_refl HTT) HT'2 (lequiv_wf_l _ _ _ Hl) Hl VP VM VEP VEM VTP VTM).
Qed.

Lemma FM_boxT {G Γ Δ T l} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lC ] T @ l ] -> SemTyP G Δ T T l ->
  SemTmM G Γ (boxT T) (boxT T) (tyCTyp Δ l) lzero.
Proof.
  intros HS HΓ Hl HΔ HT ((HG & VP & VM) & VTP & VTM). split; [exact HS | split].
  - exact (VS_CTyp EP EM HΓ HΔ HΔ Hl (lequiv_refl _ _ Hl) VP VM).
  - exact (VS_boxT EP EM HΓ Hl HΔ HT VP VM VTP VTM).
Qed.

Lemma FM_boxt {G Γ Δ T t l} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] -> SemTmP G Δ t t T l ->
  SemTmM G Γ (boxt t) (boxt t) (tyCTrm Δ T l) lzero.
Proof.
  intros HS HΓ Hl HΔ HT Ht ((HG & VP & VM) & VTP & VTM & VtP & VtM). split; [exact HS | split].
  - exact (VS_CTrm EP EM HG HΓ HΔ HΔ HT HT Hl (lequiv_refl _ _ Hl) VP VM VP VM VTP VTM).
  - exact (VS_boxt EP EM HΓ Hl HΔ HT Ht VP VM VTP VTM VtP VtM).
Qed.

End FundamentalM.
