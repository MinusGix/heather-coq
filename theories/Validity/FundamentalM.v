(** * The fundamental theorem with global substitutions, layer M

    Every M-derivation is valid at related global substitutions, for the
    [j = M] relation ([LR_M]) at the M instance.  Premises at layers C
    and P are valid by the fundamental theorem at P ([fundamentalS_le]),
    which gives the static code's payload and the contexts of [□].  The
    global variables' images are MLTT types and terms, related at
    [⊩^{≥P}_P], which the Layering Restriction carries to [LR_M]. *)
From DeLaM.Validity Require Export FundamentalS LetboxS RecFT UPiV MetaV.
From DeLaM.Typing Require Import StaticCodeEq.

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

(** At ω (M4_DESIGN.md F3): the relation at ω. *)
Local Notation VTySωM := (@VTySω EP EM EM LRM).
Local Notation VTmSωM := (@VTmSω EP EM EM LRM).
Definition SemTyMω (G : gctx) (Γ : ctx) (T T' : ty) : Prop := SemCtxM G Γ /\ VTySωM G Γ T T'.
Definition SemTmMω (G : gctx) (Γ : ctx) (t t' : tm) (T : ty) : Prop :=
  SemCtxM G Γ /\ VTySωM G Γ T T /\ VTmSωM G Γ t t' T.

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

(** The congruence: equal code is [≡ₗ]-related (Static Code, M7 A3; E11). *)
Lemma FM_boxT_eq {G Γ Δ T T' l} : SemCtxM G Γ -> [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Δ ⊢[ lC ] T' @ l ] -> [ G ; Δ ⊢[ lC ] T ≅ T' @ l ] -> SemTyP G Δ T T' l ->
  SemTmM G Γ (boxT T) (boxT T') (tyCTyp Δ l) lzero.
Proof.
  intros HS HΓ Hl HΔ HT HT' ET ((HG & VP & VM) & VTP & VTM). split; [exact HS | split].
  - exact (VS_CTyp EP EM HΓ HΔ HΔ Hl (lequiv_refl _ _ Hl) VP VM).
  - exact (VS_boxT EP EM HΓ Hl HΔ HT HT' (static_code_eqty (lle_refl lC) ET) VP VM VTP VTM).
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
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] -> [ G ; Δ ⊢[ lC ] t' : T @ l ] ->
  [ G ; Δ ⊢[ lC ] t ≅ t' : T @ l ] -> SemTmP G Δ t t' T l ->
  SemTmM G Γ (boxt t) (boxt t') (tyCTrm Δ T l) lzero.
Proof.
  intros HS HΓ Hl HΔ HT Ht Ht' Et ((HG & VP & VM) & VTP & VTM & VtP & VtM). split; [exact HS | split].
  - exact (VS_CTrm EP EM HG HΓ HΔ HΔ HT HT Hl (lequiv_refl _ _ Hl) VP VM VP VM VTP VTM).
  - exact (VS_boxt EP EM HΓ Hl HΔ HT Ht Ht' (static_code_eqtm (lle_refl lC) Et) VP VM VTP VTM VtP VtM).
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


(** ** The recursors on code (M3_DESIGN.md E13)

    The induction hypotheses as the theorem provides them: the motives'
    and branches' at every universe substitution, the rest at [φ]. *)

Lemma SemCtxEqP_refl {G Δ} : SemCtxP G Δ -> SemCtxEqP G Δ Δ.
Proof. intros (_ & VP & VM). exact (conj VP VM). Qed.

Section Rec.
Variables (G : gctx) (Γ : ctx) (L' : nat) (φ : nat -> lvl) (l1 l2 l1' l2' : lvl)
  (MT MT' Mt Mt' : ty) (bs bs' : nat -> tm).
Hypothesis (Hφ : usub_ok φ L' (gL G))
  (HMT : [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ])
  (HMT' : [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ])
  (Hl1 : lequiv L' (lvsubst l1 φ) (lvsubst l1' φ))
  (IMT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G)) ->
     SemTyM (G_us (recGT G) L'' ψ) (ucsubst (recΓT Γ) ψ) (usubst_ty MT ψ) (usubst_ty MT' ψ)
       (lvsubst (lvren l1 (ush 1)) ψ))
  (IMTl : forall L'' ψ, usub_ok ψ L'' (gL (recGT G)) ->
     SemTyM (G_us (recGT G) L'' ψ) (ucsubst (recΓT Γ) ψ) (usubst_ty MT ψ) (usubst_ty MT ψ)
       (lvsubst (lvren l1 (ush 1)) ψ))
  (IMTr : forall L'' ψ, usub_ok ψ L'' (gL (recGT G)) ->
     SemTyM (G_us (recGT G) L'' ψ) (ucsubst (recΓT Γ) ψ) (usubst_ty MT' ψ) (usubst_ty MT' ψ)
       (lvsubst (lvren l1' (ush 1)) ψ))
  (HMt : [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ])
  (HMt' : [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ])
  (Hl2 : lequiv L' (lvsubst l2 φ) (lvsubst l2' φ))
  (IMt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G)) ->
     SemTyM (G_us (recGt G) L'' ψ) (ucsubst (recΓt Γ) ψ) (usubst_ty Mt ψ) (usubst_ty Mt' ψ)
       (lvsubst (lvren l2 (ush 1)) ψ))
  (IMtl : forall L'' ψ, usub_ok ψ L'' (gL (recGt G)) ->
     SemTyM (G_us (recGt G) L'' ψ) (ucsubst (recΓt Γ) ψ) (usubst_ty Mt ψ) (usubst_ty Mt ψ)
       (lvsubst (lvren l2 (ush 1)) ψ))
  (IMtr : forall L'' ψ, usub_ok ψ L'' (gL (recGt G)) ->
     SemTyM (G_us (recGt G) L'' ψ) (ucsubst (recΓt Γ) ψ) (usubst_ty Mt' ψ) (usubst_ty Mt' ψ)
       (lvsubst (lvren l2' (ush 1)) ψ))
  (Hbs : forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                               bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ])
  (Hbs' : forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                               bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ])
  (IBr : forall k, k < nbr -> lM = lM -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G)) ->
     SemTmM (G_us (brG k G) L'' ψ) (ucsubst (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2) ψ)
       (usubst_tm (bs k) ψ) (usubst_tm (bs' k) ψ)
       (usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) ψ) (lvsubst (brLv k l1 l2) ψ))
  (IBr' : forall k, k < nbr -> lM = lM -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G)) ->
     SemTmM (G_us (brG k G) L'' ψ) (ucsubst (brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2') ψ)
       (usubst_tm (bs' k) ψ) (usubst_tm (bs' k) ψ)
       (usubst_ty (brRes k (wrapMT MT') (wrapMt Mt')) ψ) (lvsubst (brLv k l1' l2') ψ))
  (IΓbr : forall k, k < nbr -> lM = lM -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G)) ->
     SemCtxM (G_us (brG k G) L'' ψ) (ucsubst (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2) ψ))
  (GV : GValid (G_us G L' φ)) (VΓ : VCtxSM (G_us G L' φ) (ucsubst Γ φ)).

Local Notation Gφ := (G_us G L' φ).
Local Notation Γφ := (ucsubst Γ φ).

Lemma FM_elimT {k k' D D' s s' T0 T0' k0 k0'} :
  lwf L' k -> lequiv L' k k' -> [ Gφ ; D ⊢[ lD ] ] -> [ Gφ ⊢[ lD ] D ≅ D' ] ->
  SemCtxP Gφ D -> SemCtxEqP Gφ D D' ->
  VTmSM Gφ Γφ s s' (tyCTyp D k) lzero ->
  [ Gφ ; Γφ ⊢[ lM ] elimT (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm (mkrb MT Mt bs) φ) k D s : T0 @ k0 ] ->
  [ Gφ ; Γφ ⊢[ lM ] elimT (lvsubst l1' φ) (lvsubst l2' φ) (usubst_tm (mkrb MT' Mt' bs') φ) k' D' s' : T0' @ k0' ] ->
  VTmSM Gφ Γφ (elimT (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm (mkrb MT Mt bs) φ) k D s)
    (elimT (lvsubst l1' φ) (lvsubst l2' φ) (usubst_tm (mkrb MT' Mt' bs') φ) k' D' s')
    (motT (wrapMT (usubst_ty MT (uup φ))) k D s) (lvsubst l1 φ).
Proof.
  intros Hk Hkk HD HDD (_ & VDP & VDM) [VEqP VEqM] Vs Hw Hw'.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hw) as HΓ0. pose proof (ctx_glob _ _ _ HΓ0) as HG0.
  exact (VS_elimT EP EM G Γ L' φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' Hφ HMT HMT' Hl1
           (fun L'' ψ H => proj2 (IMT L'' ψ H)) (fun L'' ψ H => proj2 (IMTl L'' ψ H))
           (fun L'' ψ H => proj2 (IMTr L'' ψ H)) HMt HMt' Hl2
           (fun L'' ψ H => proj2 (IMt L'' ψ H)) (fun L'' ψ H => proj2 (IMtl L'' ψ H))
           (fun L'' ψ H => proj2 (IMtr L'' ψ H)) Hbs Hbs'
           (fun k Hk L'' ψ H => proj2 (proj2 (IBr k Hk eq_refl L'' ψ H)))
           (fun k Hk L'' ψ H => proj2 (proj2 (IBr' k Hk eq_refl L'' ψ H))) VΓ HG0 HΓ0
           (fun L'' ψ H => proj2 (proj1 (IMTl L'' ψ H))) (fun L'' ψ H => proj2 (proj1 (IMtl L'' ψ H)))
           (fun k Hk L'' ψ H => proj2 (IΓbr k Hk eq_refl L'' ψ H))
           Hk Hkk HD HDD VDP VDM VEqP VEqM Vs Hw Hw').
Qed.

Lemma FM_elimt {k k' D D' U U' s s' T0 T0' k0 k0'} :
  lwf L' k -> lequiv L' k k' -> [ Gφ ; D ⊢[ lD ] ] -> [ Gφ ⊢[ lD ] D ≅ D' ] ->
  [ Gφ ; D ⊢[ lD ] U @ k ] -> [ Gφ ; D' ⊢[ lD ] U' @ k' ] ->
  SemCtxP Gφ D -> SemCtxEqP Gφ D D' -> SemTyP Gφ D U U' k ->
  VTmSM Gφ Γφ s s' (tyCTrm D U k) lzero ->
  [ Gφ ; Γφ ⊢[ lM ] elimt (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm (mkrb MT Mt bs) φ) k D U s : T0 @ k0 ] ->
  [ Gφ ; Γφ ⊢[ lM ] elimt (lvsubst l1' φ) (lvsubst l2' φ) (usubst_tm (mkrb MT' Mt' bs') φ) k' D' U' s' : T0' @ k0' ] ->
  VTmSM Gφ Γφ (elimt (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm (mkrb MT Mt bs) φ) k D U s)
    (elimt (lvsubst l1' φ) (lvsubst l2' φ) (usubst_tm (mkrb MT' Mt' bs') φ) k' D' U' s')
    (mott (wrapMt (usubst_ty Mt (uup φ))) k D U s) (lvsubst l2 φ).
Proof.
  intros Hk Hkk HD HDD HU HU' (_ & VDP & VDM) [VEqP VEqM] (_ & VUP & VUM) Vs Hw Hw'.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hw) as HΓ0. pose proof (ctx_glob _ _ _ HΓ0) as HG0.
  exact (VS_elimt EP EM G Γ L' φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' Hφ HMT HMT' Hl1
           (fun L'' ψ H => proj2 (IMT L'' ψ H)) (fun L'' ψ H => proj2 (IMTl L'' ψ H))
           (fun L'' ψ H => proj2 (IMTr L'' ψ H)) HMt HMt' Hl2
           (fun L'' ψ H => proj2 (IMt L'' ψ H)) (fun L'' ψ H => proj2 (IMtl L'' ψ H))
           (fun L'' ψ H => proj2 (IMtr L'' ψ H)) Hbs Hbs'
           (fun k Hk L'' ψ H => proj2 (proj2 (IBr k Hk eq_refl L'' ψ H)))
           (fun k Hk L'' ψ H => proj2 (proj2 (IBr' k Hk eq_refl L'' ψ H))) VΓ HG0 HΓ0
           (fun L'' ψ H => proj2 (proj1 (IMTl L'' ψ H))) (fun L'' ψ H => proj2 (proj1 (IMtl L'' ψ H)))
           (fun k Hk L'' ψ H => proj2 (IΓbr k Hk eq_refl L'' ψ H))
           Hk Hkk HD HDD HU HU' VDP VDM VEqP VEqM VUP VUM Vs Hw Hw').
Qed.

End Rec.

(** ** At ω: the PER, conversion and level-equivalence rules *)

Lemma FMω_ty_sym {G Γ T T'} : SemTyMω G Γ T T' -> SemTyMω G Γ T' T.
Proof. intros ((HG & HΓ) & V). exact (conj (conj HG HΓ) (VTySω_sym EP EM HG HΓ V)). Qed.
Lemma FMω_ty_trans {G Γ T1 T2 T3} : SemTyMω G Γ T1 T2 -> SemTyMω G Γ T2 T3 -> SemTyMω G Γ T1 T3.
Proof. intros (HS & V1) (_ & V2). exact (conj HS (VTySω_trans EP EM V1 V2)). Qed.
Lemma FMω_tm_sym {G Γ t t' T} : SemTmMω G Γ t t' T -> SemTmMω G Γ t' t T.
Proof. intros ((HG & HΓ) & VT & V). exact (conj (conj HG HΓ) (conj VT (VTmSω_sym EP EM HG HΓ VT V))). Qed.
Lemma FMω_tm_trans {G Γ t1 t2 t3 T} : SemTmMω G Γ t1 t2 T -> SemTmMω G Γ t2 t3 T -> SemTmMω G Γ t1 t3 T.
Proof. intros (HS & VT & V1) (_ & _ & V2). exact (conj HS (conj VT (VTmSω_trans EP EM V1 V2))). Qed.
Lemma FMω_conv {G Γ t t' T T'} : SemTmMω G Γ t t' T' -> SemTyMω G Γ T T' -> SemTmMω G Γ t t' T.
Proof.
  intros (HS & _ & V) ((HG & HΓ) & VT). split; [exact (conj HG HΓ) | split].
  - exact (VTySω_trans EP EM VT (VTySω_sym EP EM HG HΓ VT)).
  - exact (VTmSω_conv EP EM V VT).
Qed.
Lemma FMω_ty_leq {G Γ T T'} : SemTyMω G Γ T T -> SemTyMω G Γ T' T' -> ty_leq T T' -> SemTyMω G Γ T T'.
Proof. intros ((HG & HΓ) & V) (_ & V') E. exact (conj (conj HG HΓ) (VTySω_leq EP EM HΓ V V' E)). Qed.
Lemma FMω_tm_leq {G Γ t t' T} : SemTmMω G Γ t t T -> SemTmMω G Γ t' t' T -> tm_leq t t' -> SemTmMω G Γ t t' T.
Proof.
  intros ((HG & HΓ) & VT & V) (_ & _ & V') E. exact (conj (conj HG HΓ) (conj VT (VTmSω_leq EP EM HΓ VT V V' E))).
Qed.

(** ** Universe polymorphism (UPiV): the induction hypotheses as the
    theorem provides them, the bodies' at every universe substitution *)

Section UPiFM.
Variables (G : gctx) (Γ : ctx) (L' : nat) (φ : nat -> lvl) (n : nat).
Hypothesis (Hφ : usub_ok φ L' (gL G)) (HS : SemCtxM (G_us G L' φ) (ucsubst Γ φ))
  (HΓ : [ G_us G L' φ ; ucsubst Γ φ ⊢[ lM ] ]) (Hn : 0 < n).

Let HG := ctx_glob _ _ _ HΓ.

Lemma FM_upi {l l' T T'} : lequiv (n + gL G) l l' ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTyM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_ty T ψ) (usubst_ty T' ψ) (lvsubst l ψ)) ->
  SemTyMω (G_us G L' φ) (ucsubst Γ φ) (tyUPi n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ)))
    (tyUPi n (lvsubst l' (uupn n φ)) (usubst_ty T' (uupn n φ))).
Proof.
  intros Hl IH. split; [exact HS |].
  exact (VS_upi EP EM G Γ L' φ n Hφ HG HΓ Hn l l' T T' Hl (fun L'' ψ H => proj2 (IH L'' ψ H))).
Qed.

Lemma FM_ulam {l l' T T' t t'} : lequiv (n + gL G) l l' ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTyM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_ty T ψ) (usubst_ty T ψ) (lvsubst l ψ)) ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTyM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_ty T ψ) (usubst_ty T' ψ) (lvsubst l ψ)) ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTmM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_tm t ψ) (usubst_tm t' ψ) (usubst_ty T ψ) (lvsubst l ψ)) ->
  SemTmMω (G_us G L' φ) (ucsubst Γ φ) (ulam n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ)) (usubst_tm t (uupn n φ)))
    (ulam n (lvsubst l' (uupn n φ)) (usubst_ty T' (uupn n φ)) (usubst_tm t' (uupn n φ)))
    (tyUPi n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ))).
Proof.
  intros Hl IT ITT It. split; [exact HS | split].
  - exact (VS_upi EP EM G Γ L' φ n Hφ HG HΓ Hn l l T T (lequiv_refl _ _ (lequiv_wf_l _ _ _ Hl))
             (fun L'' ψ H => proj2 (IT L'' ψ H))).
  - exact (VS_ulam EP EM G Γ L' φ n Hφ HG HΓ Hn l l' T T' t t' Hl (fun L'' ψ H => proj2 (IT L'' ψ H))
             (fun L'' ψ H => proj2 (ITT L'' ψ H)) (fun L'' ψ H => proj2 (proj2 (It L'' ψ H)))).
Qed.

(** The body's type at an instance: its validity at [uext ks φ]. *)
Lemma FM_inst_ty {l T ks} : length ks = n -> Forall (lwf L') ks ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTyM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_ty T ψ) (usubst_ty T ψ) (lvsubst l ψ)) ->
  VTySM (G_us G L' φ) (ucsubst Γ φ) T[uupn n φ]ᵤ[uext ks lvar]ᵤ T[uupn n φ]ᵤ[uext ks lvar]ᵤ
    (lvsubst (lvsubst l (uupn n φ)) (uext ks lvar)).
Proof.
  intros Hks Wks IT. rewrite (uupn_uext_ty n ks φ T Hks), (uupn_uext_l n ks φ l Hks).
  assert (Hψ : usub_ok (uext ks φ) L' (gL (gctx_uwk n G)))
    by (cbn [gL gctx_uwk]; rewrite <- Hks; apply usub_ok_uext; assumption).
  pose proof (proj2 (IT _ _ Hψ)) as X. rewrite (G_us_uwk_uext_φ n _ _ ks φ Hks), (ctx_uwk_uext_φ n _ ks φ Hks) in X.
  exact X.
Qed.

Lemma FM_uapp {l T t t' ls ls'} : lwf (n + gL G) l -> length ls = n -> Forall2 (lequiv (gL G)) ls ls' ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTyM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_ty T ψ) (usubst_ty T ψ) (lvsubst l ψ)) ->
  SemTmMω (G_us G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ)
    (tyUPi n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ))) ->
  SemTmM (G_us G L' φ) (ucsubst Γ φ) (uapp (usubst_tm t φ) (map (fun l => lvsubst l φ) ls))
    (uapp (usubst_tm t' φ) (map (fun l => lvsubst l φ) ls')) (usubst_ty T[uext ls lvar]ᵤ φ)
    (lvsubst (lvsubst l (uext ls lvar)) φ).
Proof.
  intros Hl Hlen Hls IT (_ & _ & Vt).
  pose proof (lequivs_usubst _ _ _ _ _ Hφ Hls) as Hks.
  assert (Hlen' : length (map (fun l => lvsubst l φ) ls) = n) by (rewrite length_map; exact Hlen).
  change (usubst_ty T[uext ls lvar]ᵤ φ) with (T[uext ls lvar]ᵤ[φ]ᵤ).
  rewrite (usubst_ubeta_ty n ls φ T Hlen), (usubst_ubeta_lvl n ls φ l Hlen).
  split; [exact HS | split].
  - exact (FM_inst_ty Hlen' (lequivs_lwf_l _ _ _ Hks) IT).
  - exact (VS_uapp EP EM G Γ L' φ n Hφ HG HΓ l T _ _ _ _ (fun L'' ψ H => proj2 (IT L'' ψ H)) Vt Hlen' Hks).
Qed.

Lemma FM_ubeta {l T t ls} : length ls = n -> Forall (lwf (gL G)) ls ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTyM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_ty T ψ) (usubst_ty T ψ) (lvsubst l ψ)) ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTmM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_tm t ψ) (usubst_tm t ψ) (usubst_ty T ψ) (lvsubst l ψ)) ->
  [ G_us G L' φ ; ucsubst Γ φ ⊢[ lM ] usubst_tm (uapp (ulam n l T t) ls) φ : usubst_ty T[uext ls lvar]ᵤ φ
      @ lvsubst (lvsubst l (uext ls lvar)) φ ] ->
  [ G_us G L' φ ; ucsubst Γ φ ⊢[ lM ] usubst_tm (uapp (ulam n l T t) ls) φ ≅ usubst_tm t[uext ls lvar]ᵤ φ
      : usubst_ty T[uext ls lvar]ᵤ φ @ lvsubst (lvsubst l (uext ls lvar)) φ ] ->
  SemTmM (G_us G L' φ) (ucsubst Γ φ) (uapp (ulam n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ)) (usubst_tm t (uupn n φ)))
      (map (fun l => lvsubst l φ) ls)) (usubst_tm t[uext ls lvar]ᵤ φ) (usubst_ty T[uext ls lvar]ᵤ φ)
    (lvsubst (lvsubst l (uext ls lvar)) φ).
Proof.
  intros Hlen Wls IT It Hw Heq.
  set (ks := map (fun l => lvsubst l φ) ls).
  assert (Hks : length ks = n) by (unfold ks; rewrite length_map; exact Hlen).
  assert (Wks : Forall (lwf L') ks) by exact (lwfs_usubst _ _ _ _ Hφ Wls).
  change (usubst_ty T[uext ls lvar]ᵤ φ) with (T[uext ls lvar]ᵤ[φ]ᵤ) in *.
  change (usubst_tm t[uext ls lvar]ᵤ φ) with (t[uext ls lvar]ᵤ[φ]ᵤ) in *.
  rewrite (usubst_ubeta_ty n ls φ T Hlen), (usubst_ubeta_lvl n ls φ l Hlen), (usubst_ubeta n ls φ t Hlen) in *.
  fold ks in Hw, Heq |- *.
  split; [exact HS | split].
  - exact (FM_inst_ty Hks Wks IT).
  - apply (VS_red EP EM Hw Heq).
    + intros σ e Nσ Ne. exact (red_ubeta_inst n _ _ _ ks σ e Hks Nσ Ne).
    + rewrite (uupn_uext_tm n ks φ t Hks), (uupn_uext_ty n ks φ T Hks), (uupn_uext_l n ks φ l Hks).
      assert (Hψ : usub_ok (uext ks φ) L' (gL (gctx_uwk n G)))
        by (cbn [gL gctx_uwk]; rewrite <- Hks; apply usub_ok_uext; assumption).
      pose proof (proj2 (proj2 (It _ _ Hψ))) as X.
      rewrite (G_us_uwk_uext_φ n _ _ ks φ Hks), (ctx_uwk_uext_φ n _ ks φ Hks) in X. exact X.
Qed.

(** η: the function's validity at [φ] and at [φ] followed by [n] fresh levels. *)
Lemma G_us_uwk_comp G0 L0 ψ0 : G_us G0 (n + L0) (fun i => lvren (ψ0 i) (ush n)) = gctx_uwk n (G_us G0 L0 ψ0).
Proof.
  unfold G_us, gctx_usubst, gctx_uwk; cbn [gL gΨ]. f_equal. rewrite map_map. apply map_ext. intros D.
  destruct D; cbn [gdecl_usubst gdecl_uren]; f_equal;
    first [ reflexivity
          | symmetry; apply lvsubst_lvren; reflexivity
          | symmetry; apply (proj1 (proj2 (proj2 usubst_uren_all))); reflexivity
          | symmetry; apply (proj1 usubst_uren_all); reflexivity ].
Qed.

Lemma FM_ueta {l T t} : lwf (n + gL G) l ->
  (forall L'' ψ, usub_ok ψ L'' (gL (gctx_uwk n G)) ->
     SemTyM (G_us (gctx_uwk n G) L'' ψ) (ucsubst Γ⟨ush n⟩ᵤ ψ) (usubst_ty T ψ) (usubst_ty T ψ) (lvsubst l ψ)) ->
  (forall L'' ψ, usub_ok ψ L'' (gL G) ->
     SemTmMω (G_us G L'' ψ) (ucsubst Γ ψ) (usubst_tm t ψ) (usubst_tm t ψ) (usubst_ty (tyUPi n l T) ψ)) ->
  SemTmMω (G_us G L' φ) (ucsubst Γ φ) (ulam n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ)) (uapp (usubst_tm t φ)⟨ush n⟩ᵤ (ubvars n)))
    (usubst_tm t φ) (tyUPi n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ))).
Proof.
  intros Hl IT It. pose proof (It _ _ Hφ) as (_ & VT & Vt).
  assert (Hψ : usub_ok (fun i => lvren (φ i) (ush n)) (n + L') (gL G))
    by (intros i Hi; apply (lwf_lvren _ _ _ _ (uren_ok_ush n L')), Hφ, Hi).
  pose proof (It _ _ Hψ) as (_ & _ & Vw).
  rewrite G_us_uwk_comp in Vw.
  rewrite <- (proj1 (proj2 (proj2 usubst_uren_all)) Γ φ (ush n) _ (fun _ => eq_refl)) in Vw.
  rewrite <- (proj1 (proj2 usubst_uren_all) t φ (ush n) _ (fun _ => eq_refl)) in Vw.
  rewrite <- (proj1 usubst_uren_all (tyUPi n l T) φ (ush n) _ (fun _ => eq_refl)) in Vw.
  split; [exact HS | split].
  - exact VT.
  - exact (VS_ueta EP EM G Γ L' φ n Hφ HG HΓ Hn l T _ (fun L'' ψ H => proj2 (IT L'' ψ H)) Vt Vw).
Qed.

End UPiFM.

(** ** The meta-functions (M5_DESIGN.md G5) *)

Local Notation extC G := (gext G gdCtx).
Local Notation extT G Δ l := (gext G (gdTy Δ lD l)).

Lemma FM_cpi_eq {G Γ l l' T T'} : SemCtxM G Γ -> lequiv (gL G) l l' -> [ extC G ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ extC G ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] -> SemTyM (extC G) Γ⟪S⟫ T T' l ->
  SemTyM G Γ (tyCPi l T) (tyCPi l' T') l.
Proof.
  intros HS Hl HT HTT (_ & VT). split; [exact HS |].
  exact (VS_cpi EP EM G Γ l l' T T' Hl HT (eqty_wf_r (i := lM) eq_refl HTT) VT).
Qed.

Lemma FM_cpi {G Γ l T} : SemCtxM G Γ -> lwf (gL G) l -> [ extC G ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  SemTyM (extC G) Γ⟪S⟫ T T l -> SemTyM G Γ (tyCPi l T) (tyCPi l T) l.
Proof. intros HS Hl HT ST. exact (FM_cpi_eq HS (lequiv_refl _ _ Hl) HT (eqty_refl _ _ _ _ _ HT) ST). Qed.

Lemma FM_tpi_eq {G Γ Δ Δ' l1 l2 l3 l4 T T'} : SemCtxM G Γ -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ extT G Δ l1 ; Γ⟪S⟫ ⊢[ lM ] T @ l2 ] ->
  [ extT G Δ l1 ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ] -> [ extT G Δ' l3 ; Γ⟪S⟫ ⊢[ lM ] T' @ l4 ] ->
  SemCtxP G Δ -> SemCtxP G Δ' -> SemCtxEqP G Δ Δ' ->
  SemTyM (extT G Δ l1) Γ⟪S⟫ T T' l2 -> SemTyM (extT G Δ' l3) Γ⟪S⟫ T' T' l4 ->
  SemTyM G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ' l3 l4 T') l2.
Proof.
  intros HS HΔ HΔ' H13 H24 HT HTT HT' (_ & VP & VM) (_ & VP' & VM') [VEP VEM] (_ & VT) (_ & VT').
  split; [exact HS |].
  exact (VS_tpi EP EM G Γ Δ Δ' l1 l2 l3 l4 T T' H13 H24 HΔ HΔ' (proj2 HS) VP VM VP' VM' VEP VEM
           HT (eqty_wf_r (i := lM) eq_refl HTT) HT' VT VT').
Qed.

Lemma FM_tpi {G Γ Δ l l' T} : SemCtxM G Γ -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ extT G Δ l ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> SemCtxP G Δ -> SemTyM (extT G Δ l) Γ⟪S⟫ T T l' ->
  SemTyM G Γ (tyTPi Δ l l' T) (tyTPi Δ l l' T) l'.
Proof.
  intros HS HΔ Hl Hl' HT SΔ ST. pose proof SΔ as (_ & VP & VM).
  exact (FM_tpi_eq HS HΔ HΔ (lequiv_refl _ _ Hl) (lequiv_refl _ _ Hl') HT (eqty_refl _ _ _ _ _ HT) HT
           SΔ SΔ (conj VP VM) ST ST).
Qed.

Lemma FM_clam_eq {G Γ l l' T T' t t'} : SemCtxM G Γ -> lequiv (gL G) l l' -> [ extC G ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ extC G ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] -> [ extC G ; Γ⟪S⟫ ⊢[ lM ] t ≅ t' : T @ l ] ->
  SemTyM (extC G) Γ⟪S⟫ T T' l -> SemTmM (extC G) Γ⟪S⟫ t t' T l ->
  SemTmM G Γ (clam l T t) (clam l' T' t') (tyCPi l T) l.
Proof.
  intros HS Hl HT HTT Htt (_ & VTT) (_ & VT & Vt). split; [exact HS | split].
  - exact (VS_cpi EP EM G Γ l l T T (lequiv_refl _ _ (lequiv_wf_l _ _ _ Hl)) HT HT VT).
  - exact (VS_clam EP EM G Γ l l' T T' t t' Hl HT (eqty_wf_r (i := lM) eq_refl HTT) (eqtm_wf_l (i := lM) eq_refl Htt)
             (eqtm_wf_r (i := lM) eq_refl Htt) VT VTT Vt).
Qed.

Lemma FM_clam {G Γ l T t} : SemCtxM G Γ -> lwf (gL G) l -> [ extC G ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ extC G ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> SemTmM (extC G) Γ⟪S⟫ t t T l ->
  SemTmM G Γ (clam l T t) (clam l T t) (tyCPi l T) l.
Proof.
  intros HS Hl HT Ht St.
  exact (FM_clam_eq HS (lequiv_refl _ _ Hl) HT (eqty_refl _ _ _ _ _ HT) (eqtm_refl _ _ _ _ _ _ Ht)
           (conj (proj1 St) (proj1 (proj2 St))) St).
Qed.

Lemma FM_capp_eq {G Γ l T t t' Δ Δ'} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> SemCtxEqP G Δ Δ' ->
  SemTmM G Γ t t' (tyCPi l T) l -> SemTyM G Γ T⦃gsingle (GCtx Δ)⦄ T⦃gsingle (GCtx Δ')⦄ l ->
  SemTmM G Γ (capp t Δ) (capp t' Δ') T⦃gsingle (GCtx Δ)⦄ l.
Proof.
  intros HΔ HΔ' [VEP VEM] ((HG & VΓ) & _ & Vt) (_ & VI). split; [exact (conj HG VΓ) | split].
  - exact (VTySM_refl_l HG VΓ VI).
  - exact (VS_capp EP EM G Γ l T t t' Δ Δ' HΔ HΔ' VEP VEM Vt).
Qed.

Lemma FM_capp {G Γ l T t Δ} : [ G ; Δ ⊢[ lD ] ] -> SemCtxP G Δ -> SemTmM G Γ t t (tyCPi l T) l ->
  SemTyM G Γ T⦃gsingle (GCtx Δ)⦄ T⦃gsingle (GCtx Δ)⦄ l ->
  SemTmM G Γ (capp t Δ) (capp t Δ) T⦃gsingle (GCtx Δ)⦄ l.
Proof. intros HΔ (_ & VP & VM). exact (FM_capp_eq HΔ HΔ (conj VP VM)). Qed.

Lemma FM_tlam_eq {G Γ Δ Δ' l1 l2 l3 l4 T T' t t'} : SemCtxM G Γ -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ extT G Δ l1 ; Γ⟪S⟫ ⊢[ lM ] T @ l2 ] ->
  [ extT G Δ l1 ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ] ->
  [ extT G Δ l1 ; Γ⟪S⟫ ⊢[ lM ] t ≅ t' : T @ l2 ] -> [ extT G Δ' l3 ; Γ⟪S⟫ ⊢[ lM ] t' : T' @ l4 ] ->
  SemCtxP G Δ -> SemCtxP G Δ' -> SemCtxEqP G Δ Δ' ->
  SemTyM (extT G Δ l1) Γ⟪S⟫ T T' l2 ->
  SemTmM (extT G Δ l1) Γ⟪S⟫ t t' T l2 -> SemTmM (extT G Δ' l3) Γ⟪S⟫ t' t' T' l4 ->
  SemTmM G Γ (tlam Δ l1 l2 T t) (tlam Δ' l3 l4 T' t') (tyTPi Δ l1 l2 T) l2.
Proof.
  intros HS HΔ HΔ' H13 H24 HT HTT Htt Ht3 (_ & VP & VM) (_ & VP' & VM') [VEP _] (_ & VTT)
    (_ & VT & Vt) (_ & _ & Vt3).
  split; [exact HS | split].
  - exact (VS_tpi EP EM G Γ Δ Δ l1 l2 l1 l2 T T (lequiv_refl _ _ (lequiv_wf_l _ _ _ H13))
             (lequiv_refl _ _ (lequiv_wf_l _ _ _ H24)) HΔ HΔ (proj2 HS) VP VM VP VM VP VM HT HT HT VT VT).
  - exact (VS_tlam EP EM G Γ Δ Δ' l1 l2 l3 l4 T T' t t' H13 H24 HΔ HΔ' (proj2 HS) VP VM VP' VM' VEP HT
             (eqty_wf_r (i := lM) eq_refl HTT) (eqtm_wf_l (i := lM) eq_refl Htt) (eqtm_wf_r (i := lM) eq_refl Htt)
             Ht3 VT VTT Vt Vt3).
Qed.

Lemma FM_tlam {G Γ Δ l l' T t} : SemCtxM G Γ -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ extT G Δ l ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> [ extT G Δ l ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] ->
  SemCtxP G Δ -> SemTmM (extT G Δ l) Γ⟪S⟫ t t T l' ->
  SemTmM G Γ (tlam Δ l l' T t) (tlam Δ l l' T t) (tyTPi Δ l l' T) l'.
Proof.
  intros HS HΔ Hl Hl' HT Ht SΔ St. pose proof SΔ as (_ & VP & VM).
  exact (FM_tlam_eq HS HΔ HΔ (lequiv_refl _ _ Hl) (lequiv_refl _ _ Hl') HT (eqty_refl _ _ _ _ _ HT)
           (eqtm_refl _ _ _ _ _ _ Ht) Ht SΔ SΔ (conj VP VM) (conj (proj1 St) (proj1 (proj2 St))) St St).
Qed.

Lemma FM_tapp_eq {G Γ Δ l l' T t t' A A'} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] A ≅ A' @ l ] ->
  SemCtxP G Δ -> SemTyP G Δ A A' l -> SemTmM G Γ t t' (tyTPi Δ l l' T) l' ->
  SemTyM G Γ T⦃gsingle (GTy A)⦄ T⦃gsingle (GTy A')⦄ l' ->
  SemTmM G Γ (tapp t A) (tapp t' A') T⦃gsingle (GTy A)⦄ l'.
Proof.
  intros HΔ HAA (_ & VP & _) (_ & VTP & VTM) ((HG & VΓ) & _ & Vt) (_ & VI).
  split; [exact (conj HG VΓ) | split].
  - exact (VTySM_refl_l HG VΓ VI).
  - exact (VS_tapp EP EM G Γ Δ l l' T t t' A A' HΔ (eqty_wf_l (i := lD) eq_refl HAA)
             (eqty_wf_r (i := lD) eq_refl HAA) VP VTP VTM Vt).
Qed.

Lemma FM_tapp {G Γ Δ l l' T t A} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] A @ l ] ->
  SemCtxP G Δ -> SemTyP G Δ A A l -> SemTmM G Γ t t (tyTPi Δ l l' T) l' ->
  SemTyM G Γ T⦃gsingle (GTy A)⦄ T⦃gsingle (GTy A)⦄ l' ->
  SemTmM G Γ (tapp t A) (tapp t A) T⦃gsingle (GTy A)⦄ l'.
Proof. intros HΔ HA. exact (FM_tapp_eq HΔ (eqty_refl _ _ _ _ _ HA)). Qed.

Lemma FM_cbeta {G Γ l T t Δ} : SemCtxM G Γ -> lwf (gL G) l -> [ extC G ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ extC G ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> [ G ; Δ ⊢[ lD ] ] -> SemCtxP G Δ ->
  SemTmM (extC G) Γ⟪S⟫ t t T l ->
  SemTmM G Γ (capp (clam l T t) Δ) t⦃gsingle (GCtx Δ)⦄ T⦃gsingle (GCtx Δ)⦄ l.
Proof.
  intros HS Hl HT Ht HΔ (_ & VP & VM) (_ & VT & Vt). split; [exact HS | split].
  - exact (VTyS_inst_c EP EM HΔ VP VM VT).
  - exact (VS_cbeta EP EM Hl HT Ht HΔ VP VM Vt).
Qed.

Lemma FM_tbeta {G Γ Δ l l' T t A} : SemCtxM G Γ -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ extT G Δ l ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> [ extT G Δ l ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] ->
  [ G ; Δ ⊢[ lD ] A @ l ] -> SemCtxP G Δ -> SemTyP G Δ A A l -> SemTmM (extT G Δ l) Γ⟪S⟫ t t T l' ->
  SemTmM G Γ (tapp (tlam Δ l l' T t) A) t⦃gsingle (GTy A)⦄ T⦃gsingle (GTy A)⦄ l'.
Proof.
  intros HS HΔ Hl Hl' HT Ht HA (_ & VP & VM) (_ & VTP & VTM) (_ & VT & Vt). split; [exact HS | split].
  - exact (VTyS_inst_t EP EM HΔ HA VP VM VTP VTM VT).
  - exact (VS_tbeta EP EM Hl Hl' HΔ HT Ht HA VP VM VTP VTM Vt).
Qed.

Lemma FM_ceta {G Γ l T t} : SemTmM G Γ t t (tyCPi l T) l ->
  SemTmM G Γ (clam l T (capp t⟪S⟫ (cvar 0))) t (tyCPi l T) l.
Proof. intros (HS & VT & Vt). exact (conj HS (conj VT (VS_ceta EP EM G Γ l T t Vt))). Qed.

Lemma FM_teta {G Γ Δ l l' T t} : [ G ; Δ ⊢[ lD ] ] -> SemCtxP G Δ -> SemTmM G Γ t t (tyTPi Δ l l' T) l' ->
  SemTmM G Γ (tlam Δ l l' T (tapp t⟪S⟫ (tyGvar 0 (lshift 0)))) t (tyTPi Δ l l' T) l'.
Proof.
  intros HΔ (_ & VP & VM) (HS & VT & Vt).
  exact (conj HS (conj VT (VS_teta EP EM G Γ Δ l l' T t HΔ VP VM Vt))).
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
Ltac m_side0 :=
  first [ eassumption | typeclasses eauto | apply lequiv_refl; m_lwf | apply lequiv_sym; eassumption | m_lwf
        | apply (lle_ge_M EP EM) | reflexivity | apply eqc_refl; eassumption ].
(** Reflexive validity from a related pair (the Σ congruences, M8). *)
Ltac m_side :=
  first [ m_side0 | solve [simple eapply VTyS_trans; [eassumption | simple eapply VTyS_sym; m_side0]]
        | solve [simple eapply VTmS_trans; [eassumption | simple eapply VTmS_sym; m_side0]] ].

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

Ltac m_rules := vs_rules m_side.

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
  | solve [simple eapply VTyS_single; [m_side | m_rules]]
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

Ltac m_rec_side :=
  first [ eassumption | apply lequiv_refl; eassumption | apply eqc_refl; eassumption
        | apply (SemCtxEqP_refl EP EM); eassumption | eapply lequiv_wf_l; eassumption
        | (* the branches' typings, from their congruence *)
          let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
          match goal with H : forall k, k < nbr -> eq_tm _ lM _ _ _ _ _ |- _ =>
            exact (eqtm_wf_l (i := lM) eq_refl (H k Hk)) end ].

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

(** The motives' induction hypotheses are also kept at every [ψ] (the
    recursion lemmas instantiate them at the code's levels); [keep] hides
    the copies from [us_spec]. *)
Definition keep (P : Prop) : Prop := P.
Ltac us_keep :=
  repeat match goal with
  | IH : forall L' φ, usub_ok φ L' (gL (recGT ?G)) -> _ |- _ =>
      let T := type of IH in
      lazymatch goal with _ : keep T |- _ => fail | _ => let X := fresh "K" in pose proof IH as X; change (keep T) in X end
  | IH : forall L' φ, usub_ok φ L' (gL (recGt ?G)) -> _ |- _ =>
      let T := type of IH in
      lazymatch goal with _ : keep T |- _ => fail | _ => let X := fresh "K" in pose proof IH as X; change (keep T) in X end
  (* the [UΠ] rules use the body at every level substitution (M4) *)
  | IH : forall L' φ, usub_ok φ L' (gL (gctx_uwk _ ?G)) -> _ |- _ =>
      let T := type of IH in
      lazymatch goal with _ : keep T |- _ => fail | _ => let X := fresh "K" in pose proof IH as X; change (keep T) in X end
  (* η uses the function at [φ] followed by fresh levels (M4) *)
  | IH : forall L' φ, usub_ok φ L' (gL ?G) -> SemTmMω _ _ _ _ _ _ _ |- _ =>
      let T := type of IH in
      lazymatch goal with _ : keep T |- _ => fail | _ => let X := fresh "K" in pose proof IH as X; change (keep T) in X end
  end.

(** ** The two halves of a judgment's semantics (M4_DESIGN.md F3): at a
    well-formed level, the finite relation; at ω, the relation at ω. *)

Lemma brLv_lwf k G l1 l2 : lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL (brG k G)) (brLv k l1 l2).
Proof.
  intros H1 H2. unfold brLv, brG, gctx_uwk; cbn [gL].
  destruct (br_isT k); (eapply lwf_lvren; [apply uren_ok_ush | assumption]).
Qed.

Ltac w_lwf :=
  cbn [lwf]; repeat split;
  first [ assumption | exact I | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption
        | eapply lwf_lvren; [apply uren_ok_ush | first [assumption | eapply lequiv_wf_l; eassumption
                                                      | eapply lequiv_wf_r; eassumption]] ].

(** Each induction hypothesis: its half at the premise's level. *)
Ltac w_spec :=
  repeat match goal with
  | IH : (lwf ?L ?k -> ?A) /\ (?k = lomega -> ?B) |- _ =>
      first [ let X := fresh "IH" in pose proof (proj1 IH ltac:(w_lwf)) as X; clear IH
            | let X := fresh "IH" in pose proof (proj2 IH eq_refl) as X; clear IH
            | match goal with Hk : k = lomega |- _ =>
                let X := fresh "IH" in pose proof (proj2 IH Hk) as X; clear IH end ]
  (* the entries of a global variable's substitution: its context's levels *)
  | IH : forall n A k, in_ctx ?Δ n A k -> (lwf ?L k -> _) /\ _,
    Hin : in_gctx (gΨ ?G) _ _, Hc : wf_ctx ?G _ _ |- _ =>
      let HD := fresh "HD" in
      pose proof (gctx_decl_ok _ _ _ (ctx_glob _ _ _ Hc) Hin) as HD; cbn [decl_ok] in HD;
      let HΔ := fresh "HΔ" in
      destruct HD as [HΔ _];
      let X := fresh "IH" in pose proof (fun n A k h => proj1 (IH n A k h) (in_ctx_lwf HΔ h)) as X; clear IH
  (* the recursors' branches *)
  | IH : forall k, k < nbr -> ?x = ?x -> (lwf (gL (brG k ?G)) (brLv k ?l1 ?l2) -> _) /\ _ |- _ =>
      let W1 := fresh "W" in let W2 := fresh "W" in
      assert (W1 : lwf (gL G) l1) by w_lwf; assert (W2 : lwf (gL G) l2) by w_lwf;
      let X := fresh "IH" in pose proof (fun k Hk e => proj1 (IH k Hk e) (brLv_lwf k G l1 l2 W1 W2)) as X;
      clear IH W1 W2
  end.

(** At ω, a rule concluding at a well-formed level is impossible. *)
Ltac w_absurd_rec :=
  match goal with
  | H : wf_tm _ _ _ (elimT _ _ _ _ _ _) _ ?k, Hlev : ?k = lomega |- _ =>
      let X := fresh in pose proof (elimT_lvl_wf H) as X; rewrite Hlev in X; exact X
  | H : wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ ?k, Hlev : ?k = lomega |- _ =>
      let X := fresh in pose proof (elimt_lvl_wf H) as X; rewrite Hlev in X; exact X
  end.

Ltac w_absurd :=
  first [ match goal with Hlev : lwf _ lomega |- _ => cbn [lwf] in Hlev; exact Hlev end
        | w_absurd_rec
        | idtac ] ;
  match goal with Hlev : ?k = lomega |- _ =>
    first [ discriminate Hlev
          | subst; repeat match goal with H : lequiv _ _ _ |- _ => destruct H as (? & ? & ?) end;
            cbn [lwf] in *; tauto
          | subst; match goal with Hc : wf_ctx _ _ ?Γ, Hi : in_ctx ?Γ _ _ lomega |- _ =>
              exact (in_ctx_lwf Hc Hi) end
          | subst; match goal with Hin : in_gctx (gΨ ?G) _ ?D, Hc : wf_ctx ?G _ _ |- _ =>
              let HD := fresh "HD" in pose proof (gctx_decl_ok _ _ _ (ctx_glob _ _ _ Hc) Hin) as HD;
              cbn [decl_ok lwf] in HD; tauto end
          | refine (ilv_not_omega _ _ _ _ _ _ _ Hlev);
            first [eassumption | reflexivity | eapply lequivs_lwf_l; eassumption] ]
  end.

(** The [UΠ] β rule's judgments, before they are moved along [φ]. *)
Ltac upi_judg :=
  try lazymatch goal with
  | |- SemTmM _ _ (G_us ?G _ _) (ucsubst ?Γ _) (usubst_tm (uapp (ulam ?n ?l ?B ?t) ?ls) _) _ (usubst_ty ?T0 _) (lvsubst ?k _) =>
      assert (wf_tm G lM Γ (uapp (ulam n l B t) ls) T0 k)
        by (eapply pre_ubeta_l; first [eassumption | reflexivity]);
      assert (eq_tm G lM Γ (uapp (ulam n l B t) ls) t[uext ls lvar]ᵤ T0 k)
        by (apply eqtm_ubeta; first [assumption | reflexivity])
  end.

Ltac w_side := first [ eassumption | reflexivity | apply lequiv_refl; eassumption
                     | apply lequivs_refl; eassumption ].

(** [$] has no context premise: the context comes from the function. *)
Ltac w_ctx :=
  try match goal with
  | IH : SemTmMω _ _ ?G ?Γ _ _ _ |- _ =>
      lazymatch goal with _ : SemCtxM _ _ G Γ |- _ => fail | _ => pose proof (proj1 IH) end
  end;
  try match goal with
  | H : [ ?G ; ?Γ ⊢[ lM ] _ : _ @ _ ] |- _ =>
      lazymatch goal with _ : [ G ; Γ ⊢[ lM ] ] |- _ => fail | _ =>
        pose proof (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H) end
  | H : [ ?G ; ?Γ ⊢[ lM ] _ ≅ _ : _ @ _ ] |- _ =>
      lazymatch goal with _ : [ G ; Γ ⊢[ lM ] ] |- _ => fail | _ =>
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ctx_extract))))) _ _ _ _ _ _ _ H) end
  end.

(** At ω and for [$] and its β: the semantic rules (UPiV). *)
Ltac w_dispatch :=
  try unfold keep in *;
  first
  [ eassumption
  | solve [eapply FMω_ty_sym; eassumption] | solve [eapply FMω_ty_trans; eassumption]
  | solve [eapply FMω_tm_sym; eassumption] | solve [eapply FMω_tm_trans; eassumption]
  | solve [eapply FMω_conv; eassumption] | solve [eapply FMω_ty_leq; eassumption]
  | solve [eapply FMω_tm_leq; eassumption]
  | solve [eapply FM_upi; w_side] | solve [eapply FM_ulam; w_side]
  | solve [rewrite uren_ush_usubst_tm, ubvars_uupn; w_ctx; eapply FM_ueta; w_side]
  | solve [w_ctx; eapply FM_uapp; w_side]
  | solve [eapply FM_ubeta; w_side] ].

(** The recursors' judgments themselves, moved along [φ] with their
    premises: the validity lemmas read the bundles' typings off them. *)
Ltac rec_judg :=
  try lazymatch goal with
  | |- context [SemTmM _ _ (G_us ?G _ _) (ucsubst ?Γ _) (usubst_tm ?t _) (usubst_tm ?t' _) (usubst_ty ?T _) (lvsubst ?k _)] =>
      lazymatch t with
      | elimT _ _ _ _ _ _ =>
          first [ assert (wf_tm G lM Γ t T k) by (apply wf_elimT; assumption)
                | assert (eq_tm G lM Γ t t' T k) by (eapply eqtm_elimT; eassumption) ]
      | elimt _ _ _ _ _ _ _ =>
          first [ assert (wf_tm G lM Γ t T k) by (apply wf_elimt; assumption)
                | assert (eq_tm G lM Γ t t' T k) by (eapply eqtm_elimt; eassumption) ]
      end
  end.

Lemma usubst_ren_mix (t : tm) r φ : usubst_tm t⟨r⟩ φ = (usubst_tm t φ)⟨r⟩.
Proof. exact (proj1 (proj2 usubst_ren_all) t r φ). Qed.
Lemma usubst_ren_ty_mix (T : ty) r φ : usubst_ty T⟨r⟩ φ = (usubst_ty T φ)⟨r⟩.
Proof. exact (proj1 usubst_ren_all T r φ). Qed.

Theorem fundamentalM_us :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> i = lM -> forall L' φ, usub_ok φ L' (gL G) ->
     SemCtxM EP EM (G_us G L' φ) (ucsubst Γ φ)) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> i = lM ->
     (lwf (gL G) l -> forall L' φ, usub_ok φ L' (gL G) ->
        SemTyM EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T φ) (lvsubst l φ)) /\
     (l = lomega -> forall L' φ, usub_ok φ L' (gL G) ->
        SemTyMω EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T φ))) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> i = lM ->
     (lwf (gL G) l -> forall L' φ, usub_ok φ L' (gL G) ->
        SemTmM EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t φ) (usubst_ty T φ)
          (lvsubst l φ)) /\
     (l = lomega -> forall L' φ, usub_ok φ L' (gL G) ->
        SemTmMω EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t φ) (usubst_ty T φ))) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> i = lM ->
     (lwf (gL G) l -> forall L' φ, usub_ok φ L' (gL G) ->
        SemTyM EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ) (lvsubst l φ)) /\
     (l = lomega -> forall L' φ, usub_ok φ L' (gL G) ->
        SemTyMω EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ))) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> i = lM ->
     (lwf (gL G) l -> forall L' φ, usub_ok φ L' (gL G) ->
        SemTmM EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ)
          (lvsubst l φ)) /\
     (l = lomega -> forall L' φ, usub_ok φ L' (gL G) ->
        SemTmMω EP EM (G_us G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ))) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    try match goal with H : ?x = lM |- _ => lazymatch x with lM => fail | _ => discriminate H end end;
    ft_prep;
    repeat match goal with
      | IH : forall n A k, in_ctx _ n A k -> ?x = ?x -> _ |- _ =>
          pose proof (fun n A k h => IH n A k h eq_refl); clear IH
      end;
    lazymatch goal with |- (lwf _ _ -> _) /\ (_ = lomega -> _) => split; intros Hlev | _ => idtac end;
    w_spec; try solve [exfalso; w_absurd]; try intros ?L' ?φ ?Hφ;
    rec_judg; upi_judg; us_keep; us_spec; us_entries_sem; us_move; us_rewrite_all;
    rewrite ?usubst_ren_mix, ?usubst_ren_ty_mix.
  all: try solve [w_dispatch].
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
  (* the meta-functions (M5) *)
  all: try solve [ first
    [ solve [simple eapply (FM_cpi EP EM); eassumption] | solve [simple eapply (FM_cpi_eq EP EM); eassumption]
    | solve [simple eapply (FM_tpi EP EM); eassumption] | solve [simple eapply (FM_tpi_eq EP EM); eassumption]
    | solve [simple eapply (FM_clam EP EM); eassumption] | solve [simple eapply (FM_clam_eq EP EM); eassumption]
    | solve [simple eapply (FM_capp EP EM); eassumption] | solve [simple eapply (FM_capp_eq EP EM); eassumption]
    | solve [simple eapply (FM_tlam EP EM); eassumption] | solve [simple eapply (FM_tlam_eq EP EM); eassumption]
    | solve [simple eapply (FM_tapp EP EM); eassumption] | solve [simple eapply (FM_tapp_eq EP EM); eassumption]
    | solve [simple eapply (FM_cbeta EP EM); eassumption] | solve [simple eapply (FM_tbeta EP EM); eassumption]
    | solve [rewrite ?usubst_gren_tm'; simple eapply (FM_ceta EP EM); eassumption]
    | solve [rewrite ?usubst_gren_tm'; simple eapply (FM_teta EP EM); eassumption] ] ].
  all: unfold SemTyM, SemTmM, SemCtxM in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; m_types; repeat split.
  all: try m_goal.
  (* the recursors on code *)
  all: try match goal with
           | H : eq_tm _ lM _ (elimT _ _ _ _ _ _) _ _ _ |- _ => pose proof (eqtm_wf_r (i := lM) eq_refl H)
           | H : eq_tm _ lM _ (elimt _ _ _ _ _ _ _) _ _ _ |- _ => pose proof (eqtm_wf_r (i := lM) eq_refl H)
           end.
  all: first
    [ solve [simple eapply (VS_elimT_beta EP EM);
             [eassumption | apply redT_usubst; eassumption | eassumption | eassumption]]
    | solve [simple eapply (VS_elimt_beta EP EM);
             [eassumption | apply redt_usubst; eassumption | eassumption | eassumption]]
    | solve [simple eapply (FM_elimT EP EM); m_rec_side]
    | solve [simple eapply (FM_elimt EP EM); m_rec_side] ].
Qed.

(** ** At the identity universe substitution *)

Lemma G_us_id G : [ ⊢ G ] -> G_us G (gL G) lvar = G.
Proof.
  intros HG. pose proof (wfg_dnf _ HG) as N. clear HG. destruct G as [L Ψ]. unfold G_us, gctx_usubst; cbn [gL gΨ] in *. f_equal.
  induction N as [|D Ψ HD _ IH]; cbn; [reflexivity|]. f_equal; [|exact IH].
  destruct D; cbn in HD |- *; f_equal; rewrite ?lvsubst_id by reflexivity; try reflexivity;
    first [apply usubst_id_ctx | apply usubst_id_ty]; try reflexivity; tauto.
Qed.

Ltac us_id H :=
  let HG := fresh "HG" in
  first [ pose proof (ctx_glob _ _ _ H) as HG
        | pose proof (ctx_glob _ _ _ (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H)) as HG
        | pose proof (ctx_glob _ _ _ (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H)) as HG
        | pose proof (ctx_glob _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 ctx_extract)))) _ _ _ _ _ _ H)) as HG
        | pose proof (ctx_glob _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ctx_extract))))) _ _ _ _ _ _ _ H))
            as HG ];
  rewrite (G_us_id _ HG);
  rewrite ?usubst_id_ctx, ?usubst_id_ty, ?usubst_id, ?lvsubst_id by first [reflexivity | dnf_of H].

(** At a well-formed level, the finite relation; at ω, the relation at ω
    (M4_DESIGN.md F3). *)
Theorem fundamentalM :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> i = lM -> SemCtxM EP EM G Γ) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> i = lM ->
     (lwf (gL G) l -> SemTyM EP EM G Γ T T l) /\ (l = lomega -> SemTyMω EP EM G Γ T T)) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> i = lM ->
     (lwf (gL G) l -> SemTmM EP EM G Γ t t T l) /\ (l = lomega -> SemTmMω EP EM G Γ t t T)) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> i = lM ->
     (lwf (gL G) l -> SemTyM EP EM G Γ T T' l) /\ (l = lomega -> SemTyMω EP EM G Γ T T')) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> i = lM ->
     (lwf (gL G) l -> SemTmM EP EM G Γ t t' T l) /\ (l = lomega -> SemTmMω EP EM G Γ t t' T)) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  destruct fundamentalM_us as (_ & Fc & Fty & Ftm & Feqty & Feqtm & _).
  refine (conj (fun _ _ => I) (conj _ (conj _ (conj _ (conj _ (conj _ (fun _ _ _ _ _ => I))))))).
  { intros G i Γ H Ei. pose proof (Fc _ _ _ H Ei (gL G) lvar (usub_ok_id _)) as X. subst i. revert X. us_id H. auto. }
  all: intros G i Γ; intros until 1; rename H into Hj; intros Ei;
    match goal with
    | F : forall G i Γ, _ |- _ =>
        first [ pose proof (F _ _ _ _ _ _ _ Hj Ei) as [X1 X2]
              | pose proof (F _ _ _ _ _ _ Hj Ei) as [X1 X2]
              | pose proof (F _ _ _ _ _ Hj Ei) as [X1 X2] ]
    end;
    subst i; split; intros Hl;
    [ specialize (X1 Hl (gL G) lvar (usub_ok_id _)); revert X1
    | specialize (X2 Hl (gL G) lvar (usub_ok_id _)); revert X2 ];
    us_id Hj; auto.
Qed.

End FundamentalMThm.
