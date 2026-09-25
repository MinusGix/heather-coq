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
  apply (proj1 (CtxRelG_layer LR_P LRM (mltt_wf_ctx (gs_ctx EP EM Hσ HΔ compt_D) ltac:(discriminate))
                  (mltt_wf_ctx (gs_ctx EP EM (GSubRel_refl_r EP EM Hσ) HΔ compt_D) ltac:(discriminate)))).
  exact (H _ _ _ Hσ).
Qed.

Lemma VTyS_toM {G Δ A A' l} : [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Δ ⊢[ lD ] A' @ l ] ->
  @VTyS EP EM EM LR_P G Δ A A' l -> VTySM G Δ A A' l.
Proof.
  intros HA HA' H G' σ σ' Hσ.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HA) as HΔ.
  apply (proj1 (VTyG_layer LR_P LRM (mltt_wf_ctx (gs_ctx EP EM Hσ HΔ compt_D) ltac:(discriminate))
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

(** The same, with the entries' induction hypotheses at a universe
    substitution [φ] (the global variable's context is [Δ[φ]]). *)
Lemma entries_us {Δ d d' φ} {P : tm -> tm -> ty -> lvl -> Prop} :
  (forall n B k, in_ctx Δ n B k -> P (usubst_tm (llk d n) φ) (usubst_tm (llk d' n) φ) (usubst_ty B[d] φ) (lvsubst k φ)) ->
  forall n B k, in_ctx (ucsubst Δ φ) n B k -> P (llk (ulsubst d φ) n) (llk (ulsubst d' φ) n) B[ulsubst d φ] k.
Proof.
  intros H n B k Hin. destruct (in_ctx_usubst_inv _ _ _ _ _ Hin) as (B0 & k0 & HB0 & -> & ->).
  rewrite !llk_ulsubst, <- usubst_subst_ty'. exact (H _ _ _ HB0).
Qed.

Lemma FM_tygvar_us {G Γ U Δ i' l d d' φ} : SemCtxM G Γ -> in_gctx (gΨ G) U (gdTy (ucsubst Δ φ) i' l) ->
  [ G ; Γ ⊢[ lM ] ] -> lsub_tail (ulsubst d φ) (ucsubst Δ φ) Γ -> dnfl (ulsubst d φ) ->
  lsub_tail (ulsubst d' φ) (ucsubst Δ φ) Γ -> dnfl (ulsubst d' φ) ->
  (forall n B k, in_ctx Δ n B k ->
     SemTmM G Γ (usubst_tm (llk d n) φ) (usubst_tm (llk d' n) φ) (usubst_ty B[d] φ) (lvsubst k φ)) ->
  SemTyM G Γ (tyGvar U (ulsubst d φ)) (tyGvar U (ulsubst d' φ)) l.
Proof.
  intros HS Hin HΓ Ht Nd Ht' Nd' Hv. eapply FM_tygvar; try eassumption.
  exact (entries_us (P := fun a b B k => SemTmM G Γ a b B k) Hv).
Qed.

Lemma FM_gvar_us {G Γ u Δ i' A l d d' φ} : SemCtxM G Γ -> in_gctx (gΨ G) u (gdTm (ucsubst Δ φ) i' A l) ->
  [ G ; Γ ⊢[ lM ] ] -> lsub_tail (ulsubst d φ) (ucsubst Δ φ) Γ -> dnfl (ulsubst d φ) ->
  lsub_tail (ulsubst d' φ) (ucsubst Δ φ) Γ -> dnfl (ulsubst d' φ) ->
  (forall n B k, in_ctx Δ n B k ->
     SemTmM G Γ (usubst_tm (llk d n) φ) (usubst_tm (llk d' n) φ) (usubst_ty B[d] φ) (lvsubst k φ)) ->
  (forall n B k, in_ctx Δ n B k ->
     SemTmM G Γ (usubst_tm (llk d n) φ) (usubst_tm (llk d n) φ) (usubst_ty B[d] φ) (lvsubst k φ)) ->
  SemTmM G Γ (gvar u (ulsubst d φ)) (gvar u (ulsubst d' φ)) A[ulsubst d φ] l.
Proof.
  intros HS Hin HΓ Ht Nd Ht' Nd' Hv Hvv. eapply FM_gvar; try eassumption.
  - exact (entries_us (P := fun a b B k => SemTmM G Γ a b B k) Hv).
  - exact (entries_us (P := fun a b B k => SemTmM G Γ a b B k) Hvv).
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
  - exact (VS_boxT EP EM HΓ Hl HΔ HT HT (ty_leq_refl _) VP VM VTP VTM).
Qed.

(** The congruence: code up to level equivalence (E11). *)
Lemma FM_boxT_eq {G Γ Δ T T' l} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Δ ⊢[ lC ] T' @ l ] -> ty_leq T T' -> SemTyP G Δ T T' l ->
  SemTmM G Γ (boxT T) (boxT T') (tyCTyp Δ l) lzero.
Proof.
  intros HS HΓ Hl HΔ HT HT' E ((HG & VP & VM) & VTP & VTM). split; [exact HS | split].
  - exact (VS_CTyp EP EM HΓ HΔ HΔ Hl (lequiv_refl _ _ Hl) VP VM).
  - exact (VS_boxT EP EM HΓ Hl HΔ HT HT' E VP VM VTP VTM).
Qed.

Lemma FM_boxt {G Γ Δ T t l} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] -> SemTmP G Δ t t T l ->
  SemTmM G Γ (boxt t) (boxt t) (tyCTrm Δ T l) lzero.
Proof.
  intros HS HΓ Hl HΔ HT Ht ((HG & VP & VM) & VTP & VTM & VtP & VtM). split; [exact HS | split].
  - exact (VS_CTrm EP EM HG HΓ HΔ HΔ HT HT Hl (lequiv_refl _ _ Hl) VP VM VP VM VTP VTM).
  - exact (VS_boxt EP EM HΓ Hl HΔ HT Ht Ht (tm_leq_refl _) VP VM VTP VTM VtP VtM).
Qed.

Lemma FM_boxt_eq {G Γ Δ T t t' l} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] -> [ G ; Δ ⊢[ lC ] t' : T @ l ] -> tm_leq t t' ->
  SemTmP G Δ t t' T l ->
  SemTmM G Γ (boxt t) (boxt t') (tyCTrm Δ T l) lzero.
Proof.
  intros HS HΓ Hl HΔ HT Ht Ht' E ((HG & VP & VM) & VTP & VTM & VtP & VtM). split; [exact HS | split].
  - exact (VS_CTrm EP EM HG HΓ HΔ HΔ HT HT Hl (lequiv_refl _ _ Hl) VP VM VP VM VTP VTM).
  - exact (VS_boxt EP EM HΓ Hl HΔ HT Ht Ht' E VP VM VTP VTM VtP VtM).
Qed.

(** ** [letbox] *)

Local Notation MbT M := (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]).
Local Notation Mbt M := (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]).

Lemma FM_letboxT_cong {G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 t t0} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M @ l1 ] -> [ G ; Γ ,, tyCTyp Δ' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
  [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t1 ≅ t2 : MbT M @ l1 ] ->
  [ gext G (gdTy Δ' lC l4) ; Γ⟪S⟫ ⊢[ lM ] t2 : MbT M' @ l3 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTyp Δ l2 @ lzero ] ->
  SemCtxP G Δ -> SemCtxEqP G Δ Δ' -> SemTyM G (Γ ,, tyCTyp Δ l2 @ lzero) M M' l1 ->
  SemTmM (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (MbT M) l1 ->
  SemTmM (gext G (gdTy Δ' lC l4)) Γ⟪S⟫ t2 t2 (MbT M') l3 ->
  SemTmM G Γ t t0 (tyCTyp Δ l2) lzero ->
  SemTmM G Γ (letboxT l1 l2 Δ M t1 t) (letboxT l3 l4 Δ' M' t2 t0) M[lsingle t] l1.
Proof.
  intros Hl13 Hl24 HΔ HΔ' HΔΔ' HM HM' Hb Hb' Htt (_ & VΔP & VΔM) [VEP VEM] (_ & VM) (_ & _ & Vb)
    (_ & _ & Vb') ((HG & VΓ) & VT & Vt).
  pose proof (eqtm_wf_l (i := lM) eq_refl Hb) as Ht1. pose proof (eqtm_wf_r (i := lM) eq_refl Hb) as Ht2.
  pose proof (eqtm_wf_l (i := lM) eq_refl Htt) as Ht. pose proof (eqtm_wf_r (i := lM) eq_refl Htt) as Ht0.
  pose proof (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)) as HΓ.
  pose proof (VTySM_refl_l HG (VCtxS_ext EP EM HG VΓ (VS_CTyp EP EM HΓ HΔ HΔ (lequiv_wf_l _ _ _ Hl24)
                (lequiv_refl _ _ (lequiv_wf_l _ _ _ Hl24)) VΔP VΔM) I) VM) as VMM.
  split; [exact (conj HG VΓ) | split].
  - exact (VTyS_single EP EM VMM (VTmSM_refl_l HG VΓ VT Vt)).
  - exact (VS_letboxT EP EM HG Hl13 Hl24 (lequiv_wf_l _ _ _ Hl13) (lequiv_wf_l _ _ _ Hl24) HΔ HΔ' HΔΔ'
             HM HM' Ht1 Ht2 Hb' Ht Ht0 VΓ VΔP VΔM VEP VEM VM Vb Vb' Vt).
Qed.

Lemma FM_letboxT {G Γ l' l Δ M t' t} : lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] ->
  [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : MbT M @ l' ] -> [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
  SemCtxP G Δ -> SemTyM G (Γ ,, tyCTyp Δ l @ lzero) M M l' ->
  SemTmM (gext G (gdTy Δ lC l)) Γ⟪S⟫ t' t' (MbT M) l' -> SemTmM G Γ t t (tyCTyp Δ l) lzero ->
  SemTmM G Γ (letboxT l' l Δ M t' t) (letboxT l' l Δ M t' t) M[lsingle t] l'.
Proof.
  intros Hl' Hl HΔ HM Ht' Ht SΔ SM Sb St. pose proof SΔ as (_ & VP & VM).
  apply FM_letboxT_cong; try assumption; try (apply lequiv_refl; assumption).
  - now apply eqc_refl.
  - now apply eqtm_refl.
  - now apply eqtm_refl.
  - exact (conj VP VM).
Qed.

Lemma FM_letboxT_beta {G Γ l' l Δ M t' T} : lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] ->
  [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : MbT M @ l' ] ->
  SemTyP G Δ T T l -> SemTyM G (Γ ,, tyCTyp Δ l @ lzero) M M l' ->
  SemTmM (gext G (gdTy Δ lC l)) Γ⟪S⟫ t' t' (MbT M) l' ->
  SemTmM G Γ (letboxT l' l Δ M t' (boxT T)) t'⦃gsingle (GTy T)⦄ M[lsingle (boxT T)] l'.
Proof.
  intros Hl' Hl HΔ HT HM Ht' ((HG & VP & VM') & VTP & VTM) ((_ & VΓ) & VM) (_ & _ & Vb).
  pose proof (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)) as HΓ.
  split; [exact (conj HG (VCtxS_tl EP EM VΓ)) | split].
  - exact (VTyS_single EP EM VM (VS_boxT EP EM HΓ Hl HΔ HT HT (ty_leq_refl _) VP VM' VTP VTM)).
  - exact (VS_letboxT_beta EP EM HG Hl' Hl HΔ HT HM Ht' VP VM' VTP VTM Vb).
Qed.

Lemma FM_letboxt_cong {G Γ l1 l2 l3 l4 Δ Δ' A A' M M' t1 t2 t t0} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢[ lD ] A @ l2 ] -> [ G ; Δ' ⊢[ lD ] A' @ l4 ] ->
  [ G ; Δ ⊢[ lD ] A ≅ A' @ l2 ] ->
  [ G ; Γ ,, tyCTrm Δ A l2 @ lzero ⊢[ lM ] M @ l1 ] -> [ G ; Γ ,, tyCTrm Δ' A' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
  [ gext G (gdTm Δ lC A l2) ; Γ⟪S⟫ ⊢[ lM ] t1 ≅ t2 : Mbt M @ l1 ] ->
  [ gext G (gdTm Δ' lC A' l4) ; Γ⟪S⟫ ⊢[ lM ] t2 : Mbt M' @ l3 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTrm Δ A l2 @ lzero ] ->
  SemCtxEqP G Δ Δ' -> SemTyP G Δ A A' l2 -> SemTyM G (Γ ,, tyCTrm Δ A l2 @ lzero) M M' l1 ->
  SemTmM (gext G (gdTm Δ lC A l2)) Γ⟪S⟫ t1 t2 (Mbt M) l1 ->
  SemTmM (gext G (gdTm Δ' lC A' l4)) Γ⟪S⟫ t2 t2 (Mbt M') l3 ->
  SemTmM G Γ t t0 (tyCTrm Δ A l2) lzero ->
  SemTmM G Γ (letboxt l1 l2 Δ A M t1 t) (letboxt l3 l4 Δ' A' M' t2 t0) M[lsingle t] l1.
Proof.
  intros Hl13 Hl24 HΔ HΔ' HΔΔ' HA HA' HAA' HM HM' Hb Hb' Htt [VEP VEM] ((_ & VΔP & VΔM) & VAP & VAM)
    (_ & VM) (_ & _ & Vb) (_ & _ & Vb') ((HG & VΓ) & VT & Vt).
  pose proof (eqtm_wf_l (i := lM) eq_refl Hb) as Ht1. pose proof (eqtm_wf_r (i := lM) eq_refl Hb) as Ht2.
  pose proof (eqtm_wf_l (i := lM) eq_refl Htt) as Ht. pose proof (eqtm_wf_r (i := lM) eq_refl Htt) as Ht0.
  pose proof (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)) as HΓ.
  pose proof (VTyS_trans EP EM VAP (VTyS_sym EP EM HG VΔP VAP)) as VAAP.
  pose proof (VTyS_trans EP EM VAM (VTyS_sym EP EM HG VΔM VAM)) as VAAM.
  pose proof (VTySM_refl_l HG (VCtxS_ext EP EM HG VΓ (VS_CTrm EP EM HG HΓ HΔ HΔ HA HA (lequiv_wf_l _ _ _ Hl24)
                (lequiv_refl _ _ (lequiv_wf_l _ _ _ Hl24)) VΔP VΔM VΔP VΔM VAAP VAAM) I) VM) as VMM.
  split; [exact (conj HG VΓ) | split].
  - exact (VTyS_single EP EM VMM (VTmSM_refl_l HG VΓ VT Vt)).
  - exact (VS_letboxt EP EM HG Hl13 Hl24 (lequiv_wf_l _ _ _ Hl13) (lequiv_wf_l _ _ _ Hl24) HΔ HΔ' HΔΔ'
             HA HA' HAA' HM HM' Ht1 Ht2 Hb' Ht Ht0 VΓ VΔP VΔM VEP VEM VAP VAM VM Vb Vb' Vt).
Qed.

Lemma FM_letboxt {G Γ l' l Δ A M t' t} : lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Γ ,, tyCTrm Δ A l @ lzero ⊢[ lM ] M @ l' ] ->
  [ gext G (gdTm Δ lC A l) ; Γ⟪S⟫ ⊢[ lM ] t' : Mbt M @ l' ] -> [ G ; Γ ⊢[ lM ] t : tyCTrm Δ A l @ lzero ] ->
  SemTyP G Δ A A l -> SemTyM G (Γ ,, tyCTrm Δ A l @ lzero) M M l' ->
  SemTmM (gext G (gdTm Δ lC A l)) Γ⟪S⟫ t' t' (Mbt M) l' -> SemTmM G Γ t t (tyCTrm Δ A l) lzero ->
  SemTmM G Γ (letboxt l' l Δ A M t' t) (letboxt l' l Δ A M t' t) M[lsingle t] l'.
Proof.
  intros Hl' Hl HΔ HA HM Ht' Ht SA SM Sb St. pose proof SA as ((_ & VP & VM) & _).
  apply FM_letboxt_cong; try assumption; try (apply lequiv_refl; assumption).
  - now apply eqc_refl.
  - now apply eqty_refl.
  - now apply eqtm_refl.
  - now apply eqtm_refl.
  - exact (conj VP VM).
Qed.

Lemma FM_letboxt_beta {G Γ l' l Δ A M t' c} : lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lC ] c : A @ l ] -> [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Γ ,, tyCTrm Δ A l @ lzero ⊢[ lM ] M @ l' ] ->
  [ gext G (gdTm Δ lC A l) ; Γ⟪S⟫ ⊢[ lM ] t' : Mbt M @ l' ] ->
  SemTmP G Δ c c A l -> SemTyM G (Γ ,, tyCTrm Δ A l @ lzero) M M l' ->
  SemTmM (gext G (gdTm Δ lC A l)) Γ⟪S⟫ t' t' (Mbt M) l' ->
  SemTmM G Γ (letboxt l' l Δ A M t' (boxt c)) t'⦃gsingle (GTm c)⦄ M[lsingle (boxt c)] l'.
Proof.
  intros Hl' Hl HΔ Hc HA HM Ht' ((HG & VP & VM') & VAP & VAM & VcP & VcM) ((_ & VΓ) & VM) (_ & _ & Vb).
  pose proof (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)) as HΓ.
  split; [exact (conj HG (VCtxS_tl EP EM VΓ)) | split].
  - exact (VTyS_single EP EM VM (VS_boxt EP EM HΓ Hl HΔ HA Hc Hc (tm_leq_refl _) VP VM' VAP VAM VcP VcM)).
  - exact (VS_letboxt_beta EP EM HG Hl' Hl HΔ HA Hc HM Ht' VP VM' VAP VAM VcP VcM Vb).
Qed.

End FundamentalM.

(** ** The theorem *)

Section FundamentalMThm.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.
Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsT' : VPLaws (@lr_vp LRM) := vpM_laws EP EM.

Ltac m_lwf :=
  first [ eassumption | exact I | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption
        | progress cbn [lwf]; first [split; m_lwf | m_lwf] ].
Ltac m_side :=
  first [ eassumption | typeclasses eauto | apply lequiv_refl; m_lwf | apply lequiv_sym; eassumption | m_lwf
        | apply (lle_ge_M EP EM) | reflexivity | apply eqc_refl; eassumption ].

Ltac m_types :=
  repeat match goal with
  | H : wf_tm ?G lM ?Γ ?t ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G lM Γ T l |- _ => fail
      | _ => pose proof (wf_tm_ty (i := lM) eq_refl H)
      end
  | H : eq_ty ?G lM ?Γ ?T ?T' ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G lM Γ T l |- _ => fail
      | _ => pose proof (eqty_wf_l (i := lM) eq_refl H)
      end
  | H : eq_tm ?G lM ?Γ ?t ?t' ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_tm G lM Γ t T l |- _ => fail
      | _ => pose proof (eqtm_wf_l (i := lM) eq_refl H)
      end
  end.

(** Premises at C and P: the fundamental theorem at P. *)
Ltac m_P :=
  repeat match goal with
  | H : wf_glob ?G |- _ =>
      lazymatch goal with _ : GValid EP EM G |- _ => fail | _ =>
        pose proof (proj1 (fundamentalS EP EM) _ H) end
  | H : wf_ctx ?G lD ?Δ |- _ =>
      lazymatch goal with _ : SemCtx EP EM G Δ |- _ => fail | _ =>
        pose proof (proj1 (proj2 (fundamentalS EP EM)) _ _ _ H eq_refl) end
  | H : wf_ty ?G ?i ?Δ ?T ?l |- _ =>
      lazymatch i with lM => fail | _ => idtac end;
      lazymatch goal with _ : SemTy EP EM G Δ T T l |- _ => fail | _ =>
        pose proof (proj1 (proj2 (fundamentalS_le EP EM)) _ _ _ _ _ H ltac:(unfold lle; cbn; lia)) end
  | H : wf_tm ?G ?i ?Δ ?t ?T ?l |- _ =>
      lazymatch i with lM => fail | _ => idtac end;
      lazymatch goal with _ : SemTm EP EM G Δ t t T l |- _ => fail | _ =>
        pose proof (proj1 (proj2 (proj2 (fundamentalS_le EP EM))) _ _ _ _ _ _ H ltac:(unfold lle; cbn; lia)) end
  | H : eq_ty ?G ?i ?Δ ?T ?T' ?l |- _ =>
      lazymatch i with lM => fail | _ => idtac end;
      lazymatch goal with _ : SemTy EP EM G Δ T T' l |- _ => fail | _ =>
        pose proof (proj1 (proj2 (proj2 (proj2 (fundamentalS_le EP EM)))) _ _ _ _ _ _ H
                      ltac:(unfold lle; cbn; lia)) end
  | H : eq_tm ?G ?i ?Δ ?t ?t' ?T ?l |- _ =>
      lazymatch i with lM => fail | _ => idtac end;
      lazymatch goal with _ : SemTm EP EM G Δ t t' T l |- _ => fail | _ =>
        pose proof (proj2 (proj2 (proj2 (proj2 (fundamentalS_le EP EM)))) _ _ _ _ _ _ _ H
                      ltac:(unfold lle; cbn; lia)) end
  | H : eq_ctx ?G lD ?Δ ?Δ' |- _ =>
      lazymatch goal with _ : SemCtxEq EP EM G Δ Δ' |- _ => fail | _ =>
        pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalS EP EM)))))) _ _ _ _ H eq_refl) end
  end.

Ltac m_ctx :=
  first [ eassumption | apply VCtxS_nil
        | solve [simple eapply VCtxS_var;
                 first [ exact (fun _ _ _ HΔ HΔ' H => proj1 (CtxRelG_layer LR_P LRM
                                  (mltt_wf_ctx HΔ ltac:(discriminate)) (mltt_wf_ctx HΔ' ltac:(discriminate)))
                                  (proj2 H))
                       | m_side ]]
        | solve [simple eapply VCtxS_tl; m_side]
        | solve [simple eapply VCtxS_ext; m_side] ].

Ltac m_rules :=
  first
  [ solve [simple eapply VS_var; m_side]
  | solve [simple eapply VS_nat; m_side] | solve [simple eapply VS_zero; m_side] | solve [simple eapply VS_code_nat; m_side]
  | solve [simple eapply VS_El_nat; m_side]
  | solve [simple eapply VS_succ; m_side]
  | solve [simple eapply VS_U; m_side] | solve [simple eapply VS_El; m_side]
  | solve [simple eapply VS_code_U; m_side] | solve [simple eapply VS_El_U; m_side]
  | solve [simple eapply VS_pi; m_side] | solve [simple eapply VS_app; m_side]
  | solve [simple eapply VS_lam; m_side] | solve [simple eapply VS_natrec; m_side]
  | solve [simple eapply VS_code_pi; m_side]
  | solve [simple eapply VS_beta; m_side] | solve [simple eapply VS_eta; m_side]
  | solve [simple eapply VS_natrec_zero; m_side] | solve [simple eapply VS_natrec_succ; m_side]
  | solve [simple eapply VS_El_pi; m_side] ].

Ltac m_ty :=
  first
  [ eassumption
  | solve [simple eapply VTyS_sym; m_side] | solve [simple eapply VTyS_trans; m_side]
  | solve [simple eapply VTyS_lconv; m_side]
  | solve [simple eapply VTyS_trans; [eassumption | simple eapply VTyS_sym; m_side]]
  | solve [simple eapply VTyS_trans; [simple eapply VTyS_sym; m_side | eassumption]]
  | solve [simple eapply VTyS_lookup; m_side]
  | solve [simple eapply VTyS_leq; m_side]
  | solve [simple eapply VTyS_single; m_side]
  | m_rules
  | solve [simple eapply VTyS_single; [eassumption | m_rules]]
  | solve [simple eapply VTyS_single;
           [ first [eassumption | simple eapply VTyS_trans; [eassumption | simple eapply VTyS_sym; m_side]]
           | first [eassumption | simple eapply VTmS_trans; [eassumption | simple eapply VTmS_sym; m_side]]]] ].

Ltac m_tm :=
  first
  [ eassumption
  | solve [simple eapply VTmS_sym; m_side] | solve [simple eapply VTmS_trans; m_side]
  | solve [simple eapply VTmS_conv; m_side] | solve [simple eapply VTmS_lconv; m_side]
  | solve [simple eapply VTmS_leq; m_side]
  | m_rules ].

Ltac m_goal :=
  lazymatch goal with
  | |- GValid _ _ _ => eassumption
  | |- @VCtxS _ _ _ _ _ _ => m_ctx
  | |- @VTyS _ _ _ _ _ _ _ _ _ => m_ty
  | |- @VTmS _ _ _ _ _ _ _ _ _ _ => m_tm
  end.

(** ** Moving a case to its instance at a universe substitution [φ]

    The theorem quantifies over [φ : L' ⇒ gL G] (M3_DESIGN.md E6): every
    case is the case at the instance [J[φ]], its typing premises moved
    along [φ] by the universe substitution lemma. *)
Ltac us_move :=
  match goal with Hφ : usub_ok ?φ ?L' (gL ?G) |- _ =>
  repeat match goal with
  | H : wf_glob ?G0 |- _ => lazymatch G0 with G_us _ _ _ => fail | _ => idtac end;
      pose proof (proj1 usubstitution _ H _ _ Hφ); clear H
  | H : wf_ctx ?G0 _ _ |- _ => lazymatch G0 with G_us _ _ _ => fail | _ => idtac end;
      pose proof (proj1 (proj2 usubstitution) _ _ _ H _ _ Hφ); clear H
  | H : wf_ty ?G0 _ _ _ _ |- _ => lazymatch G0 with G_us _ _ _ => fail | _ => idtac end;
      pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ H _ _ Hφ); clear H
  | H : wf_tm ?G0 _ _ _ _ _ |- _ => lazymatch G0 with G_us _ _ _ => fail | _ => idtac end;
      pose proof (proj1 (proj2 (proj2 (proj2 usubstitution))) _ _ _ _ _ _ H _ _ Hφ); clear H
  | H : eq_ty ?G0 _ _ _ _ _ |- _ => lazymatch G0 with G_us _ _ _ => fail | _ => idtac end;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ H _ _ Hφ); clear H
  | H : eq_tm ?G0 _ _ _ _ _ _ |- _ => lazymatch G0 with G_us _ _ _ => fail | _ => idtac end;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ _ _ _ H _ _ Hφ);
      clear H
  | H : eq_ctx ?G0 _ _ _ |- _ => lazymatch G0 with G_us _ _ _ => fail | _ => idtac end;
      pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ H _ _ Hφ); clear H
  | H : in_gctx (gΨ G) _ _ |- _ => pose proof (in_gctx_usubst _ _ _ φ H); clear H
  | H : gctx_var G _ |- _ => pose proof (gctx_var_usubst _ _ L' φ H); clear H
  | H : lwf (gL G) _ |- _ => pose proof (lwf_lvsubst _ _ _ _ Hφ H); clear H
  | H : lequiv (gL G) _ _ |- _ => pose proof (lequiv_lvsubst _ _ _ _ _ Hφ H); clear H
  | H : lsub_tail ?d _ _ |- _ => lazymatch d with ulsubst _ _ => fail | _ => idtac end;
      pose proof (lsub_tail_usubst _ _ _ φ H); clear H
  | H : dnfl ?d |- _ => lazymatch d with ulsubst _ _ => fail | _ => idtac end;
      pose proof (dnfl_usubst d φ); clear H
  | H : in_ctx ?Γ0 _ _ _ |- _ => lazymatch Γ0 with ucsubst _ _ => fail | _ => idtac end;
      pose proof (in_ctx_usubst _ _ _ _ φ H); clear H
  | H : ty_leq ?T _ |- _ => lazymatch T with usubst_ty _ _ => fail | _ => idtac end;
      pose proof (proj1 leq_usubst_all _ _ φ φ (fun _ => leqv_refl _) H); clear H
  | H : tm_leq ?t _ |- _ => lazymatch t with usubst_tm _ _ => fail | _ => idtac end;
      pose proof (proj1 (proj2 leq_usubst_all) _ _ φ φ (fun _ => leqv_refl _) H); clear H
  end end.

(** The global variables' entries: their induction hypotheses at [φ]. *)
Ltac us_entries_sem :=
  repeat match goal with
  | IH : forall n A k, in_ctx ?Δ n A k -> forall L' φ, usub_ok φ L' (gL ?G) -> _,
    Hφ : usub_ok ?φ ?L' (gL ?G) |- _ =>
      pose proof (fun n A k h => IH n A k h L' φ Hφ); clear IH
  end.

Lemma usubst_ren_mix (t : tm) r φ : usubst_tm t⟨r⟩ φ = (usubst_tm t φ)⟨r⟩.
Proof. exact (proj1 (proj2 usubst_ren_all) t r φ). Qed.
Lemma usubst_ren_ty_mix (T : ty) r φ : usubst_ty T⟨r⟩ φ = (usubst_ty T φ)⟨r⟩.
Proof. exact (proj1 usubst_ren_all T r φ). Qed.

Theorem fundamentalM_us :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> i = lM -> forall L' φ, usub_ok φ L' (gL G) ->
     SemCtxM EP EM (G_us G L' φ) (ucsubst Γ φ)) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> i = lM -> forall L' φ, usub_ok φ L' (gL G) ->
     SemTyM EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T φ) (lvsubst l φ)) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> i = lM -> forall L' φ, usub_ok φ L' (gL G) ->
     SemTmM EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t φ) (usubst_ty T φ)
       (lvsubst l φ)) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> i = lM -> forall L' φ, usub_ok φ L' (gL G) ->
     SemTyM EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ) (lvsubst l φ)) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> i = lM -> forall L' φ, usub_ok φ L' (gL G) ->
     SemTmM EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ)
       (lvsubst l φ)) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    try match goal with H : ?x = lM |- _ => lazymatch x with lM => fail | _ => discriminate H end end;
    ft_prep;
    repeat match goal with
      | IH : forall n A k, in_ctx _ n A k -> ?x = ?x -> _ |- _ =>
          pose proof (fun n A k h => IH n A k h eq_refl); clear IH
      end;
    us_spec; us_entries_sem; us_move; us_rewrite_all; rewrite ?usubst_ren_mix, ?usubst_ren_ty_mix.
  all: try solve [ first [simple eapply (FM_tygvar_us EP EM) | simple eapply (FM_gvar_us EP EM)]; eassumption ].
  all: m_P.
  all: try solve [ first [ simple eapply (FM_CTyp EP EM) | simple eapply (FM_CTyp_eq EP EM)
                         | simple eapply (FM_CTrm EP EM) | simple eapply (FM_CTrm_eq EP EM)
                         | simple eapply (FM_boxT EP EM) | simple eapply (FM_boxt EP EM)
                         | simple eapply (FM_boxT_eq EP EM) | simple eapply (FM_boxt_eq EP EM)
                         | simple eapply (FM_letboxT EP EM) | simple eapply (FM_letboxT_cong EP EM)
                         | simple eapply (FM_letboxT_beta EP EM)
                         | simple eapply (FM_letboxt EP EM) | simple eapply (FM_letboxt_cong EP EM)
                         | simple eapply (FM_letboxt_beta EP EM) ]; eassumption ].
  all: unfold SemTyM, SemTmM, SemCtxM in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; m_types; repeat split.
  all: try m_goal.
  all: match goal with |- ?g => lazymatch g with context [elimT] => idtac "REC-T" | context [elimt] => idtac "REC-t" | _ => idtac "OTHER" g end end.
Abort.

End FundamentalMThm.
