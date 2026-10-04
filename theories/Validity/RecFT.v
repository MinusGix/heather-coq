(** * Validity of the recursors on code at layer M (M3_DESIGN.md E13)

    A related scrutinee reduces to [box]es of [≡ₗ]-related code or to
    related neutrals. On [box], the recursion lemmas relate the
    recursions; on neutrals, the neutral recursion lemmas. Either way the
    recursors anti-reduce to them. The recursion lemmas work at a target
    with exactly the source's level count, so the source is re-levelled
    to the target's first. *)
From DeLaM.Validity Require Export RecS.

(** ** Syntax: the bundle's components from a recursor's typing *)

Lemma mkrb_inj_bs {MT Mt bs MT' Mt' bs'} : mkrb MT Mt bs = mkrb MT' Mt' bs' -> forall k, k < nbr -> bs k = bs' k.
Proof. intros H; exact (proj2 (proj2 (mkrb_inj H))). Qed.

Lemma RBwf_ext {G Γ l1 l2 MT Mt bs bs'} : (forall k, k < nbr -> bs k = bs' k) ->
  RBwf G Γ l1 l2 MT Mt bs -> RBwf G Γ l1 l2 MT Mt bs'.
Proof.
  intros E (H1 & H2 & H3 & H4 & H5 & H6). repeat split; try assumption.
  intros k Hk; rewrite <- (E k Hk); exact (H6 k Hk).
Qed.

Lemma elimT_RBwf {G Γ l1 l2 MT Mt bs l Δ t T k} :
  [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : T @ k ] -> RBwf G Γ l1 l2 MT Mt bs.
Proof.
  intros H. destruct (elimT_prem H) as (MT0 & Mt0 & bs0 & E & Hrb).
  destruct (mkrb_inj_MT E) as [-> ->]. exact (RBwf_ext (fun k Hk => eq_sym (mkrb_inj_bs E k Hk)) Hrb).
Qed.
Lemma elimt_RBwf {G Γ l1 l2 MT Mt bs l Δ T0 t T k} :
  [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T0 t : T @ k ] -> RBwf G Γ l1 l2 MT Mt bs.
Proof.
  intros H. destruct (elimt_prem H) as (MT0 & Mt0 & bs0 & E & Hrb).
  destruct (mkrb_inj_MT E) as [-> ->]. exact (RBwf_ext (fun k Hk => eq_sym (mkrb_inj_bs E k Hk)) Hrb).
Qed.

(** ** Re-levelling the source *)

Section Relevel.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.
Local Notation LRM := (LR_M EP EM).
Local Notation GSubRel := (GSubRel EP EM).

Lemma gsub_wf_relevel {G' L Ψ σ} L2 : [ G' ⊢ σ : mkG L Ψ ] -> [ G' ⊢ σ : mkG L2 Ψ ].
Proof. intros [H1 H2 H3]; split; assumption. Qed.

Lemma GSubRel_relevel {G' L Ψ σ σ'} L2 : GSubRel G' (mkG L Ψ) σ σ' -> L2 <= gL G' ->
  GSubRel G' (mkG L2 Ψ) σ σ'.
Proof.
  intros [HL Hl Hr Hrel Hl0 Hr0] H2.
  constructor; [cbn; exact H2 | exact (gsub_wf_relevel L2 Hl) | exact (gsub_wf_relevel L2 Hr)
               | exact Hrel | exact Hl0 | exact Hr0].
Qed.

Lemma VCtxS_relevel {E : GenericEq} {LP : LRParams} {L Ψ Γ} L2 : L <= L2 ->
  @VCtxS EP EM E LP (mkG L Ψ) Γ -> @VCtxS EP EM E LP (mkG L2 Ψ) Γ.
Proof. intros HL V G' σ σ' Hσ. apply V, (GSubRel_relevel L Hσ). pose proof (gsr_L _ _ _ _ _ _ Hσ); cbn in *; lia. Qed.

End Relevel.

(** ** The motive instances under global and local substitutions *)

Lemma motT_gs_s M k D s σ e : gdnf σ -> LK dnftm e ->
  ((motT (wrapMT M) k D s)⦃σ⦄)[e] = motT (wrapMT (M⦃gup (guwk σ)⦄[llift (gwk (uwk e))])) k D⦃σ⦄ (s⦃σ⦄)[e].
Proof.
  intros Hσ He. rewrite motT_gsubst by first [hd_tac | exact Hσ].
  rewrite motT_subst by first [hd_tac | exact He]. reflexivity.
Qed.

Lemma mott_gs_s M k D U s σ e : gdnf σ -> LK dnftm e ->
  ((mott (wrapMt M) k D U s)⦃σ⦄)[e] =
  mott (wrapMt (M⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))])) k D⦃σ⦄ U⦃σ⦄ (s⦃σ⦄)[e].
Proof.
  intros Hσ He. rewrite mott_gsubst by first [hd_tac | exact Hσ].
  rewrite mott_subst by first [hd_tac | exact He]. reflexivity.
Qed.

(** ** The recursors *)

Section ElimT.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsFT : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation VCtxSP := (@VCtxS EP EM EP LR_P).
Local Notation VCtxSPM := (@VCtxS EP EM EM LR_P).
Local Notation VCtxEqSP := (@VCtxEqS EP LR_P EP EM).
Local Notation VCtxEqSM := (@VCtxEqS EM LR_P EP EM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtmM := (@LRtm EM LRM).

Variables (G0 : gctx) (Γ0 : ctx) (L' : nat) (φ : nat -> lvl) (l1 l2 l1' l2' : lvl)
  (MT MT' Mt Mt' : ty) (bs bs' : nat -> tm).
Hypothesis (Hφ : usub_ok φ L' (gL G0))
  (HMT : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT @ lvren l1 (ush 1) ])
  (HMT' : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT' @ lvren l1' (ush 1) ])
  (Hl1 : lequiv L' (lvsubst l1 φ) (lvsubst l1' φ))
  (VMT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT ψ) (usubst_ty MT' ψ)
       (lvsubst (lvren l1 (ush 1)) ψ))
  (VMTl : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT ψ) (usubst_ty MT ψ)
       (lvsubst (lvren l1 (ush 1)) ψ))
  (VMTr : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT' ψ) (usubst_ty MT' ψ)
       (lvsubst (lvren l1' (ush 1)) ψ))
  (HMt : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt @ lvren l2 (ush 1) ])
  (HMt' : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt' @ lvren l2' (ush 1) ])
  (Hl2 : lequiv L' (lvsubst l2 φ) (lvsubst l2' φ))
  (VMt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt ψ) (usubst_ty Mt' ψ)
       (lvsubst (lvren l2 (ush 1)) ψ))
  (VMtl : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt ψ) (usubst_ty Mt ψ)
       (lvsubst (lvren l2 (ush 1)) ψ))
  (VMtr : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt' ψ) (usubst_ty Mt' ψ)
       (lvsubst (lvren l2' (ush 1)) ψ))
  (Hbs : forall k, k < nbr -> [ brG k G0 ; brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                               bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ])
  (Hbs' : forall k, k < nbr -> [ brG k G0 ; brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                               bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ])
  (VBr : forall k, k < nbr -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VTmSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) ψ)
       (usubst_tm (bs k) ψ) (usubst_tm (bs' k) ψ)
       (usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) ψ) (lvsubst (brLv k l1 l2) ψ))
  (VBr' : forall k, k < nbr -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VTmSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2') ψ)
       (usubst_tm (bs' k) ψ) (usubst_tm (bs' k) ψ)
       (usubst_ty (brRes k (wrapMT MT') (wrapMt Mt')) ψ) (lvsubst (brLv k l1' l2') ψ))
  (VΓ : VCtxSM (G_us G0 L' φ) (ucsubst Γ0 φ))
  (HG0 : [ ⊢ G_us G0 L' φ ]) (HΓ0 : [ G_us G0 L' φ ; ucsubst Γ0 φ ⊢[ lM ] ])
  (VΓT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) -> VCtxSM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ))
  (VΓt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) -> VCtxSM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ))
  (VΓbr : forall k, k < nbr -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VCtxSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) ψ)).

Local Notation Gφ := (G_us G0 L' φ).
Local Notation Γφ := (ucsubst Γ0 φ).
Local Notation rbL := (usubst_tm (mkrb MT Mt bs) φ).
Local Notation rbR := (usubst_tm (mkrb MT' Mt' bs') φ).

(** The source re-levelled to a target [G'']: the recursion lemmas'
    hypotheses there. *)
Section At.
Variables (G'' : gctx) (σ σ' : gsub) (Θ : ctx) (e e' : lsub).
Hypothesis (Hσ : GSubRel G'' Gφ σ σ') (He : SubRelM G'' Γφ⦃σ⦄ Θ e e').

Lemma at_L : L' <= gL G''. Proof. exact (gsr_L _ _ _ _ _ _ Hσ). Qed.
Lemma at_σ : GSubRel G'' (G_us G0 (gL G'') φ) σ σ'.
Proof. exact (GSubRel_relevel EP EM (gL G'') Hσ (le_n _)). Qed.
Lemma at_φ : usub_ok φ (gL G'') (gL G0).
Proof. intros n Hn; exact (lwf_weaken _ _ _ at_L (Hφ n Hn)). Qed.
Lemma at_l1 : lequiv (gL G'') (lvsubst l1 φ) (lvsubst l1' φ). Proof. exact (lequiv_weaken _ _ _ _ at_L Hl1). Qed.
Lemma at_l2 : lequiv (gL G'') (lvsubst l2 φ) (lvsubst l2' φ). Proof. exact (lequiv_weaken _ _ _ _ at_L Hl2). Qed.
Lemma at_Γ : VCtxSM (G_us G0 (gL G'') φ) Γφ. Proof. exact (VCtxS_relevel EP EM (gL G'') at_L VΓ). Qed.
Lemma at_G : [ ⊢ G_us G0 (gL G'') φ ]. Proof. exact (wfg_grow _ _ _ at_L HG0). Qed.
Lemma at_Γwf : [ G_us G0 (gL G'') φ ; Γφ ⊢[ lM ] ].
Proof.
  pose proof (gwa_ctx (γ := gwk_id) (G' := G_us G0 (gL G'') φ) (G := Gφ) (conj at_L (gwkwf_id _)) at_G HΓ0) as X.
  exact X.
Qed.

End At.

Lemma VS_elimT {k k' D D' s s' T0 T0' k0 k0'} :
  lwf L' k -> lequiv L' k k' -> [ Gφ ; D ⊢[ lD ] ] -> [ Gφ ⊢[ lD ] D ≅ D' ] ->
  VCtxSP Gφ D -> VCtxSPM Gφ D -> VCtxEqSP Gφ D D' -> VCtxEqSM Gφ D D' ->
  VTmSM Gφ Γφ s s' (tyCTyp D k) lzero ->
  [ Gφ ; Γφ ⊢[ lM ] elimT (lvsubst l1 φ) (lvsubst l2 φ) rbL k D s : T0 @ k0 ] ->
  [ Gφ ; Γφ ⊢[ lM ] elimT (lvsubst l1' φ) (lvsubst l2' φ) rbR k' D' s' : T0' @ k0' ] ->
  VTmSM Gφ Γφ (elimT (lvsubst l1 φ) (lvsubst l2 φ) rbL k D s) (elimT (lvsubst l1' φ) (lvsubst l2' φ) rbR k' D' s')
    (motT (wrapMT (usubst_ty MT (uup φ))) k D s) (lvsubst l1 φ).
Proof.
  intros Hk Hkk HD HDD VDP VDM VEqP VEqM Vs Hw Hw'.
  apply (VTmS_intro_loc EP EM). intros G'' σ σ' Hσ Θ e e' He.
  pose proof (at_L _ _ _ Hσ) as HL.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσl. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  pose proof (SubRel_refl_r He) as He'.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (eqctx_wf_r (i := lD) eq_refl HDD) as HD'.
  pose proof (gs_ctx EP EM Hσ HD compt_D) as HDs. pose proof (gs_ctx EP EM Hσr HD' compt_D) as HD's.
  pose proof (gs_ctx EP EM Hσr HD compt_D) as HDr.
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G'')) as XΓ; cbn [gwa] in XΓ.
  pose proof (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) He') as He'r.
  pose proof (CtxRelG_escape_P EP EM (VEqP _ _ _ Hσ) HDs HD's) as [HgDD' HDD'].
  assert (Hk2 : lwf (gL G'') k) by exact (lwf_weaken _ _ _ HL Hk).
  assert (Hkk2 : lequiv (gL G'') k k') by exact (lequiv_weaken _ _ _ _ HL Hkk).
  assert (Hk'2 : lwf (gL G'') k') by exact (lequiv_wf_r _ _ _ Hkk2).
  (* the recursors' bundles, well-formed at the target *)
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (SubRel_wf_l _ _ _ _ _ He'r) as Hew'. rewrite (@gm_layer_M EP EM EMl) in Hew'.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσr Hw') Hew') as X'.
  rewrite gs_elimT, subst_elimT, mkrb_usubst, mkrb_gsubst, mkrb_subst in X, X'.
  pose proof (elimT_RBwf X) as HrbL. pose proof (elimT_RBwf X') as HrbR. clear X X'.
  rewrite gs_elimT, subst_elimT, gs_elimT, subst_elimT, mkrb_usubst, mkrb_usubst, mkrb_gsubst, mkrb_gsubst,
    mkrb_subst, mkrb_subst, motT_gs_s, motT_gs_s by assumption.
  (* the recursion lemmas and the motives, at the re-levelled source *)
  pose proof (at_σ _ _ _ Hσ) as Hσ2. pose proof (at_σ _ _ _ Hσl) as Hσl2.
  pose proof (at_φ _ _ _ Hσ) as Hφ2. pose proof (at_l1 _ _ _ Hσ) as Hl1'. pose proof (at_l2 _ _ _ Hσ) as Hl2'.
  pose proof (at_Γ _ _ _ Hσ) as VΓ2. pose proof (at_G _ _ _ Hσ) as HG2. pose proof (at_Γwf _ _ _ Hσ) as HΓ2.
  assert (Hwl1 : lwf (gL G'') (lvsubst l1 φ)) by exact (proj1 HrbL).
  pose proof (@rec_T EP EM _ _ _ G0 Γ0 (gL G'') φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' Hφ2 HMT HMT' Hl1' VMT VMTl VMTr
                HMt HMt' Hl2' VMt VMtl VMtr Hbs Hbs' VBr VBr' VΓ2 G'' σ σ' Θ e e' Hσ2 He HrbL HrbR eq_refl
                HG2 HΓ2 VΓT VΓt VΓbr) as RT.
  pose proof (@rec_T_ne EP EM _ _ _ G0 Γ0 (gL G'') φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' Hφ2 HMT HMT' Hl1' VMT VMTr
                Hl2' VMt VBr VΓ2 G'' σ σ' Θ e e' Hσ2 He HrbL HrbR eq_refl HG2 HΓ2 VΓT VΓt VΓbr) as RTne.
  pose proof (@MotRel_T EP EM _ _ G0 Γ0 (gL G'') φ MT MT l1 l1 HMT HMT (lequiv_refl _ _ Hwl1) Hφ2 VMTl VMTl VΓ2
                G'' σ σ Θ e e Hσl2 (SubRel_refl_l He) eq_refl) as MRl.
  pose proof (@MotRel_T EP EM _ _ G0 Γ0 (gL G'') φ MT MT' l1 l1' HMT HMT' Hl1' Hφ2 VMT VMTr VΓ2
                G'' σ σ' Θ e' e' Hσ2 He' eq_refl) as MRr.
  (* the scrutinee: related at [□D⦃σ⦄] *)
  assert (Vss : forall d d', SubRelM G'' Γφ⦃σ⦄ Θ d d' ->
            LRtmM lzero G'' Θ (tyCTyp D⦃σ⦄ k) (tyCTyp D⦃σ⦄ k) (s⦃σ⦄)[d] (s'⦃σ'⦄)[d']).
  { intros d d' Hd. pose proof (Vs _ _ _ Hσ _ _ (gwk_ok_id G'') _ _ _ Hd) as Y; cbn [gwa] in Y.
    rewrite gs_tyCTyp in Y. exact Y. }
  pose proof (vp_ctx_refl_l EP EM HDs (VDP _ _ _ Hσ) (VDM _ _ _ Hσ)) as VD.
  pose proof (LR_ctyp EP EM HΘ HDs HDs Hk2 (lequiv_refl _ _ Hk2) VD) as HLc.
  destruct (Vss _ _ He) as (R & HR & Hr).
  pose proof (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ HR HLc _ _) Hr) as (w & w' & Hsw & Hs'w & Hg & Hg' & Hn & Hn').
  assert (HLww : LRtmM lzero G'' Θ (tyCTyp D⦃σ⦄ k) (tyCTyp D⦃σ⦄ k) w w').
  { exists (@CTypRel EM LRM G'' Θ D⦃σ⦄ D⦃σ⦄ k k); split; [exact HLc|].
    exists w, w'. refine (conj _ (conj _ (conj Hg (conj Hg' (conj Hn Hn'))))); apply tmred_refl.
    - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hsw)).
    - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  assert (HLsw' : LRtmM lzero G'' Θ (tyCTyp D⦃σ⦄ k) (tyCTyp D⦃σ⦄ k) (s⦃σ⦄)[e] w').
  { eapply LRtm_red; [exact HLww | exact Hsw |]. apply tmred_refl.
    exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  pose proof (LRtm_trans HLsw' (LRtm_sym HLww)) as HLsw.
  pose proof (LRtm_trans (LRtm_sym HLww) HLww) as Hw'w'.
  assert (Hs'w' : LRtmM lzero G'' Θ (tyCTyp D⦃σ⦄ k) (tyCTyp D⦃σ⦄ k) (s'⦃σ'⦄)[e'] w').
  { eapply LRtm_red; [exact Hw'w' | exact Hs'w |]. apply tmred_refl.
    exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  rewrite (@gm_layer_M EP EM EMl) in Hsw, Hs'w.
  (* the right-hand contextual type *)
  assert (VDD' : vp_ctx (vpM EP EM) G'' D⦃σ⦄ D'⦃σ'⦄) by exact (conj HDD' (conj (VEqP _ _ _ Hσ) (VEqM _ _ _ Hσ))).
  assert (XT : LRtyM lzero G'' Θ (tyCTyp D⦃σ⦄ k) (tyCTyp D'⦃σ'⦄ k'))
    by exact (ex_intro _ _ (LR_ctyp EP EM HΘ HDs HD's Hk2 Hkk2 VDD')).
  assert (toR : forall a a', LRtmM lzero G'' Θ (tyCTyp D⦃σ⦄ k) (tyCTyp D⦃σ⦄ k) a a' ->
                 LRtmM lzero G'' Θ (tyCTyp D'⦃σ'⦄ k') (tyCTyp D'⦃σ'⦄ k') a' a')
    by (intros a a' Ha; exact (LRtm_conv_l (LRtm_conv_r (LRtm_trans (LRtm_sym Ha) Ha) XT) (LRty_sym XT))).
  (* the motives at the scrutinees and their whnfs *)
  pose proof (MRl _ _ _ _ _ _ Hk2 (lequiv_refl _ _ Hk2) HDs (eqc_refl _ _ _ HDs) HLsw (LRtm_trans HLww (LRtm_sym HLww)))
    as VMat_l.
  pose proof (MRr _ _ _ _ _ _ Hk2 Hkk2 HDs HDD' (LRtm_trans (Vss _ _ He') Hs'w') (toR _ _ HLww)) as VMat_r.
  pose proof (MRr _ _ _ _ _ _ Hk2 Hkk2 HDs HDD' (Vss _ _ He') (toR _ _ (Vss _ _ He'))) as VMat_s.
  destruct VMat_s as [RC HRC]. destruct (escape_ty _ _ _ _ _ _ _ _ HRC) as (_ & _ & HgC).
  pose proof (geq_ty_sound HgC) as HC. rewrite (@gm_layer_M EP EM EMl) in HC.
  assert (HCC : [ G'' ; Θ ⊢[ lM ] tyCTyp D⦃σ⦄ k ≅ tyCTyp D'⦃σ'⦄ k' @ lzero ])
    by (apply eqty_CTyp; [exact HΘ | exact HDD' | exact Hkk2]).
  pose proof (tmred_conv _ _ _ _ _ eq_refl Hs'w HCC) as Hs'w4.
  (* the recursions at the whnfs: the recursion lemmas, or neutrals *)
  assert (Z : LRtmM (lvsubst l1 φ) G'' Θ
    (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄)[llift (gwk (uwk e))]) k D⦃σ⦄ w)
    (motT (wrapMT ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄)[llift (gwk (uwk e'))]) k' D'⦃σ'⦄ w')
    (elimT (lvsubst l1 φ) (lvsubst l2 φ)
       (mkrb ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄)[llift (gwk (uwk e))]
          ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄)[llift (gwk (gwk (uwk e)))]
          (fun k0 => ((usubst_tm (bs k0) (uupn (br_nu k0) φ))⦃gbsub k0 σ⦄)[lliftn (br_nl k0) (bsub k0 e)]))
       k D⦃σ⦄ w)
    (elimT (lvsubst l1' φ) (lvsubst l2' φ)
       (mkrb ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄)[llift (gwk (uwk e'))]
          ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄)[llift (gwk (gwk (uwk e')))]
          (fun k0 => ((usubst_tm (bs' k0) (uupn (br_nu k0) φ))⦃gbsub k0 σ'⦄)[lliftn (br_nl k0) (bsub k0 e')]))
       k' D'⦃σ'⦄ w')).
  { destruct Hn as [T1 T1' HV | ν ν' Hνν].
    - destruct HV as (HE & HT1 & HT1c & _ & _).
      exact (RT _ _ _ _ _ _ _ HT1 HDD' (lequiv_refl _ _ Hk2) Hkk2 HE (wf_ty_lwf HT1c)).
    - exact (RTne _ _ _ _ _ _ HDs HDD' Hk2 Hkk2 HgDD' (VEqP _ _ _ Hσ) (VEqM _ _ _ Hσ) Hνν). }
  (* anti-reduction to the goal's types *)
  eapply LRtm_red; [exact (LRtm_conv_r (LRtm_conv_l Z VMat_l) (LRty_sym VMat_r)) | |];
    rewrite (@gm_layer_M EP EM EMl).
  - exact (tmred_elimT_cong HrbL Hk2 HDs Hsw).
  - eapply (tmred_conv _ _ _ _ _ eq_refl);
      [exact (tmred_lconv _ _ _ _ _ (tmred_elimT_cong HrbR Hk'2 HD's Hs'w4) Hl1') |].
    exact (eqty_sym _ _ _ _ _ _ HC).
Qed.

Lemma VS_elimt {k k' D D' U U' s s' T0 T0' k0 k0'} :
  lwf L' k -> lequiv L' k k' -> [ Gφ ; D ⊢[ lD ] ] -> [ Gφ ⊢[ lD ] D ≅ D' ] ->
  [ Gφ ; D ⊢[ lD ] U @ k ] -> [ Gφ ; D' ⊢[ lD ] U' @ k' ] ->
  VCtxSP Gφ D -> VCtxSPM Gφ D -> VCtxEqSP Gφ D D' -> VCtxEqSM Gφ D D' ->
  @VTyS EP EM EP LR_P Gφ D U U' k -> @VTyS EP EM EM LR_P Gφ D U U' k ->
  VTmSM Gφ Γφ s s' (tyCTrm D U k) lzero ->
  [ Gφ ; Γφ ⊢[ lM ] elimt (lvsubst l1 φ) (lvsubst l2 φ) rbL k D U s : T0 @ k0 ] ->
  [ Gφ ; Γφ ⊢[ lM ] elimt (lvsubst l1' φ) (lvsubst l2' φ) rbR k' D' U' s' : T0' @ k0' ] ->
  VTmSM Gφ Γφ (elimt (lvsubst l1 φ) (lvsubst l2 φ) rbL k D U s) (elimt (lvsubst l1' φ) (lvsubst l2' φ) rbR k' D' U' s')
    (mott (wrapMt (usubst_ty Mt (uup φ))) k D U s) (lvsubst l2 φ).
Proof.
  intros Hk Hkk HD HDD HU HU' VDP VDM VEqP VEqM VUP VUM Vs Hw Hw'.
  apply (VTmS_intro_loc EP EM). intros G'' σ σ' Hσ Θ e e' He.
  pose proof (at_L _ _ _ Hσ) as HL.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσl. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  pose proof (SubRel_refl_r He) as He'.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (eqctx_wf_r (i := lD) eq_refl HDD) as HD'.
  pose proof (gs_ctx EP EM Hσ HD compt_D) as HDs. pose proof (gs_ctx EP EM Hσr HD' compt_D) as HD's.
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G'')) as XΓ; cbn [gwa] in XΓ.
  pose proof (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) He') as He'r.
  pose proof (CtxRelG_escape_P EP EM (VEqP _ _ _ Hσ) HDs HD's) as [HgDD' HDD'].
  assert (Hk2 : lwf (gL G'') k) by exact (lwf_weaken _ _ _ HL Hk).
  assert (Hkk2 : lequiv (gL G'') k k') by exact (lequiv_weaken _ _ _ _ HL Hkk).
  assert (Hk'2 : lwf (gL G'') k') by exact (lequiv_wf_r _ _ _ Hkk2).
  (* the index types *)
  pose proof (gs_ty EP EM Hσ HU) as HUs. pose proof (gs_ty EP EM Hσr HU') as HU's.
  assert (HU'sL : [ G'' ; D⦃σ⦄ ⊢[ lD ] U'⦃σ'⦄ @ k ])
    by exact (wft_lconv _ _ _ _ _ _ (ctxconv_ty (eqctx_sym_D HDD') (i := lD) eq_refl HU's) Hkk2).
  destruct (VTyG_escape_P EP EM (VDP _ _ _ Hσl) HDs HUs HU'sL (VUP _ _ _ Hσ)) as [_ HUU].
  assert (VDD' : vp_ctx (vpM EP EM) G'' D⦃σ⦄ D'⦃σ'⦄) by exact (conj HDD' (conj (VEqP _ _ _ Hσ) (VEqM _ _ _ Hσ))).
  assert (VUU : vp_ty (vpM EP EM) G'' D⦃σ⦄ U⦃σ⦄ U'⦃σ'⦄ k) by exact (conj HUU (conj (VUP _ _ _ Hσ) (VUM _ _ _ Hσ))).
  pose proof (vpl_ty_lconv Hkk2 (vpl_ty_ctx VDD' (vpl_ty_sym VUU))) as VR.
  pose proof (vpl_ty_trans VUU (vpl_ty_sym VUU)) as VA.
  (* the recursors' bundles, well-formed at the target *)
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (SubRel_wf_l _ _ _ _ _ He'r) as Hew'. rewrite (@gm_layer_M EP EM EMl) in Hew'.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσr Hw') Hew') as X'.
  rewrite gs_elimt, subst_elimt, mkrb_usubst, mkrb_gsubst, mkrb_subst in X, X'.
  pose proof (elimt_RBwf X) as HrbL. pose proof (elimt_RBwf X') as HrbR. clear X X'.
  rewrite gs_elimt, subst_elimt, gs_elimt, subst_elimt, mkrb_usubst, mkrb_usubst, mkrb_gsubst, mkrb_gsubst,
    mkrb_subst, mkrb_subst, mott_gs_s, mott_gs_s by assumption.
  (* the recursion lemmas and the motives, at the re-levelled source *)
  pose proof (at_σ _ _ _ Hσ) as Hσ2. pose proof (at_σ _ _ _ Hσl) as Hσl2.
  pose proof (at_φ _ _ _ Hσ) as Hφ2. pose proof (at_l1 _ _ _ Hσ) as Hl1'. pose proof (at_l2 _ _ _ Hσ) as Hl2'.
  pose proof (at_Γ _ _ _ Hσ) as VΓ2. pose proof (at_G _ _ _ Hσ) as HG2. pose proof (at_Γwf _ _ _ Hσ) as HΓ2.
  assert (Hwl2 : lwf (gL G'') (lvsubst l2 φ)) by exact (proj1 (proj2 HrbL)).
  pose proof (@rec_t EP EM _ _ _ G0 Γ0 (gL G'') φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' Hφ2 HMT HMT' Hl1' VMT VMTl VMTr
                HMt HMt' Hl2' VMt VMtl VMtr Hbs Hbs' VBr VBr' VΓ2 G'' σ σ' Θ e e' Hσ2 He HrbL HrbR eq_refl
                HG2 HΓ2 VΓT VΓt VΓbr) as Rt.
  pose proof (@rec_t_ne EP EM _ _ _ G0 Γ0 (gL G'') φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' Hφ2 Hl1' VMT
                HMt HMt' Hl2' VMt VMtr VBr VΓ2 G'' σ σ' Θ e e' Hσ2 He HrbL HrbR eq_refl HG2 HΓ2 VΓT VΓt VΓbr) as Rtne.
  pose proof (@MotRel_t EP EM _ _ G0 Γ0 (gL G'') φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ2 VMtl VMtl VΓ2
                G'' σ σ Θ e e Hσl2 (SubRel_refl_l He) eq_refl) as MRl.
  pose proof (@MotRel_t EP EM _ _ G0 Γ0 (gL G'') φ Mt Mt' l2 l2' HMt HMt' Hl2' Hφ2 VMt VMtr VΓ2
                G'' σ σ' Θ e' e' Hσ2 He' eq_refl) as MRr.
  (* the scrutinee: related at [□(D⦃σ⦄ ⊢ U⦃σ⦄)] *)
  assert (Vss : forall d d', SubRelM G'' Γφ⦃σ⦄ Θ d d' ->
            LRtmM lzero G'' Θ (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (s⦃σ⦄)[d] (s'⦃σ'⦄)[d']).
  { intros d d' Hd. pose proof (Vs _ _ _ Hσ _ _ (gwk_ok_id G'') _ _ _ Hd) as Y; cbn [gwa] in Y.
    rewrite gs_tyCTrm in Y. exact Y. }
  pose proof (vp_ctx_refl_l EP EM HDs (VDP _ _ _ Hσ) (VDM _ _ _ Hσ)) as VD.
  pose proof (LR_ctrm EP EM HΘ HDs HDs HUs HUs Hk2 (lequiv_refl _ _ Hk2) VD VA VA) as HLc.
  destruct (Vss _ _ He) as (R & HR & Hr).
  pose proof (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ HR HLc _ _) Hr) as (w & w' & Hsw & Hs'w & Hg & Hg' & Hn & Hn').
  assert (HLww : LRtmM lzero G'' Θ (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (tyCTrm D⦃σ⦄ U⦃σ⦄ k) w w').
  { exists (@CTrmRel EM LRM G'' Θ D⦃σ⦄ D⦃σ⦄ U⦃σ⦄ U⦃σ⦄ k k); split; [exact HLc|].
    exists w, w'. refine (conj _ (conj _ (conj Hg (conj Hg' (conj Hn Hn'))))); apply tmred_refl.
    - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hsw)).
    - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  assert (HLsw' : LRtmM lzero G'' Θ (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (s⦃σ⦄)[e] w').
  { eapply LRtm_red; [exact HLww | exact Hsw |]. apply tmred_refl.
    exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  pose proof (LRtm_trans HLsw' (LRtm_sym HLww)) as HLsw.
  pose proof (LRtm_trans (LRtm_sym HLww) HLww) as Hw'w'.
  assert (Hs'w' : LRtmM lzero G'' Θ (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (s'⦃σ'⦄)[e'] w').
  { eapply LRtm_red; [exact Hw'w' | exact Hs'w |]. apply tmred_refl.
    exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  rewrite (@gm_layer_M EP EM EMl) in Hsw, Hs'w.
  (* the right-hand contextual type *)
  assert (XT : LRtyM lzero G'' Θ (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (tyCTrm D'⦃σ'⦄ U'⦃σ'⦄ k'))
    by exact (ex_intro _ _ (LR_ctrm EP EM HΘ HDs HD's HUs HU's Hk2 Hkk2 VDD' VUU VR)).
  assert (toR : forall a a', LRtmM lzero G'' Θ (tyCTrm D⦃σ⦄ U⦃σ⦄ k) (tyCTrm D⦃σ⦄ U⦃σ⦄ k) a a' ->
                 LRtmM lzero G'' Θ (tyCTrm D'⦃σ'⦄ U'⦃σ'⦄ k') (tyCTrm D'⦃σ'⦄ U'⦃σ'⦄ k') a' a')
    by (intros a a' Ha; exact (LRtm_conv_l (LRtm_conv_r (LRtm_trans (LRtm_sym Ha) Ha) XT) (LRty_sym XT))).
  (* the motives at the scrutinees and their whnfs *)
  pose proof (MRl _ _ _ _ _ _ _ _ Hk2 (lequiv_refl _ _ Hk2) HDs (eqc_refl _ _ _ HDs) (eqty_refl _ _ _ _ _ HUs) HUs
                HLsw (LRtm_trans HLww (LRtm_sym HLww))) as VMat_l.
  pose proof (MRr _ _ _ _ _ _ _ _ Hk2 Hkk2 HDs HDD' HUU HU's (LRtm_trans (Vss _ _ He') Hs'w') (toR _ _ HLww))
    as VMat_r.
  pose proof (MRr _ _ _ _ _ _ _ _ Hk2 Hkk2 HDs HDD' HUU HU's (Vss _ _ He') (toR _ _ (Vss _ _ He'))) as VMat_s.
  destruct VMat_s as [RC HRC]. destruct (escape_ty _ _ _ _ _ _ _ _ HRC) as (_ & _ & HgC).
  pose proof (geq_ty_sound HgC) as HC. rewrite (@gm_layer_M EP EM EMl) in HC.
  assert (HCC : [ G'' ; Θ ⊢[ lM ] tyCTrm D⦃σ⦄ U⦃σ⦄ k ≅ tyCTrm D'⦃σ'⦄ U'⦃σ'⦄ k' @ lzero ])
    by (apply eqty_CTrm; [exact HΘ | exact HDs | exact HDD' | exact HUs | exact HUU | exact Hkk2]).
  pose proof (tmred_conv _ _ _ _ _ eq_refl Hs'w HCC) as Hs'w4.
  (* the recursions at the whnfs: the recursion lemmas, or neutrals *)
  assert (Z : LRtmM (lvsubst l2 φ) G'' Θ
    (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄)[llift (gwk (gwk (uwk e)))]) k D⦃σ⦄ U⦃σ⦄ w)
    (mott (wrapMt ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄)[llift (gwk (gwk (uwk e')))]) k' D'⦃σ'⦄ U'⦃σ'⦄ w')
    (elimt (lvsubst l1 φ) (lvsubst l2 φ)
       (mkrb ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄)[llift (gwk (uwk e))]
          ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄)[llift (gwk (gwk (uwk e)))]
          (fun k0 => ((usubst_tm (bs k0) (uupn (br_nu k0) φ))⦃gbsub k0 σ⦄)[lliftn (br_nl k0) (bsub k0 e)]))
       k D⦃σ⦄ U⦃σ⦄ w)
    (elimt (lvsubst l1' φ) (lvsubst l2' φ)
       (mkrb ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄)[llift (gwk (uwk e'))]
          ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄)[llift (gwk (gwk (uwk e')))]
          (fun k0 => ((usubst_tm (bs' k0) (uupn (br_nu k0) φ))⦃gbsub k0 σ'⦄)[lliftn (br_nl k0) (bsub k0 e')]))
       k' D'⦃σ'⦄ U'⦃σ'⦄ w')).
  { destruct Hn as [t1 t1' HV | ν ν' Hνν].
    - destruct HV as (HE & Ht1 & Ht1c & _ & _).
      exact (Rt _ _ _ _ _ _ _ _ _ _ Ht1 HDD' (lequiv_refl _ _ Hk2) Hkk2 (eqty_refl _ _ _ _ _ HUs) HUU HE
               (wf_tm_lwf Ht1c)).
    - exact (Rtne _ _ _ _ _ _ _ _ HDs HDD' Hk2 Hkk2 HgDD' (VEqP _ _ _ Hσ) (VEqM _ _ _ Hσ) HUs HUU
               (VUP _ _ _ Hσ) (VUM _ _ _ Hσ) Hνν). }
  (* anti-reduction to the goal's types *)
  eapply LRtm_red; [exact (LRtm_conv_r (LRtm_conv_l Z VMat_l) (LRty_sym VMat_r)) | |];
    rewrite (@gm_layer_M EP EM EMl).
  - exact (tmred_elimt_cong HrbL Hk2 HDs HUs Hsw).
  - eapply (tmred_conv _ _ _ _ _ eq_refl);
      [exact (tmred_lconv _ _ _ _ _ (tmred_elimt_cong HrbR Hk'2 HD's HU's Hs'w4) Hl2') |].
    exact (eqty_sym _ _ _ _ _ _ HC).
Qed.

End ElimT.

(** ** β: the reduct is typed (a premise of the rule), hence valid; the
    recursor anti-reduces to it *)

Section Beta.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).

Lemma VS_elimT_beta {G Γ l1 l2 rb l Δ c T k r} :
  [ G ; Γ ⊢[ lM ] elimT l1 l2 rb l Δ (boxT c) : T @ k ] -> redT l1 l2 rb l Δ c = Some r ->
  [ G ; Γ ⊢[ lM ] r : T @ k ] -> VTmSM G Γ r r T k ->
  VTmSM G Γ (elimT l1 l2 rb l Δ (boxT c)) r T k.
Proof.
  intros Hw Hred Hr Vr. destruct (elimT_prem Hw) as (MT & Mt & bs & -> & _).
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hr) Hew) as Xr.
  pose proof (Vr _ _ _ Hσ _ _ (gwk_ok_id G') _ _ _ He) as Y; cbn [gwa] in Y.
  eapply LRtm_red_l; [exact Y |]. rewrite (@gm_layer_M EP EM EMl).
  pose proof (redT_gsubst _ _ _ _ _ _ _ _ _ σ Nσ Hred) as Hred1. rewrite mkrb_gsubst in Hred1.
  pose proof (redT_subst _ _ _ _ _ _ _ _ _ e De Hred1) as Hred2.
  rewrite gs_elimT, subst_elimT, mkrb_gsubst in X |- *. cbn [gsubst GSubst_tm gsubst_tm subst Subst_tm subst_tm] in X |- *.
  split; [exact X | econstructor; [apply red_elimT_beta; exact Hred2 | constructor] |].
  apply eqtm_elimT_beta; assumption.
Qed.

Lemma VS_elimt_beta {G Γ l1 l2 rb l Δ U c T k r} :
  [ G ; Γ ⊢[ lM ] elimt l1 l2 rb l Δ U (boxt c) : T @ k ] -> redt l1 l2 rb l Δ U c = Some r ->
  [ G ; Γ ⊢[ lM ] r : T @ k ] -> VTmSM G Γ r r T k ->
  VTmSM G Γ (elimt l1 l2 rb l Δ U (boxt c)) r T k.
Proof.
  intros Hw Hred Hr Vr. destruct (elimt_prem Hw) as (MT & Mt & bs & -> & _).
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hr) Hew) as Xr.
  pose proof (Vr _ _ _ Hσ _ _ (gwk_ok_id G') _ _ _ He) as Y; cbn [gwa] in Y.
  eapply LRtm_red_l; [exact Y |]. rewrite (@gm_layer_M EP EM EMl).
  pose proof (redt_gsubst _ _ _ _ _ _ _ _ _ _ σ Nσ Hred) as Hred1. rewrite mkrb_gsubst in Hred1.
  pose proof (redt_subst _ _ _ _ _ _ _ _ _ _ e De Hred1) as Hred2.
  rewrite gs_elimt, subst_elimt, mkrb_gsubst in X |- *. cbn [gsubst GSubst_tm gsubst_tm subst Subst_tm subst_tm] in X |- *.
  split; [exact X | econstructor; [apply red_elimt_beta; exact Hred2 | constructor] |].
  apply eqtm_elimt_beta; assumption.
Qed.

End Beta.
