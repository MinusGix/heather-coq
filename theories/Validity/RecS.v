(** * The recursion lemmas on code (M3_DESIGN.md E13)

    The FT case of a recursor, unfolded: related global substitutions
    [σ ≈ σ'] into [G[φ]], related local ones [e ≈ e'] into [Γ[φ]⦃σ⦄],
    and the recursors moved there. This file relates the moved motives'
    instances (from the motives' validity at every [ψ]), the reducts (from
    the branches' validity at [ψ = levels ++ φ], [σ] extended by the
    code's pieces, [e] by the recursive calls), and proves the recursion
    lemmas by induction on the code's C-typing. *)
From DeLaM.Typing Require Export RecPeel.
From DeLaM.Validity Require Export RecObj LetboxS.

(** ** Pointwise equal substitutions *)

Lemma gdecl_gsubst_ext D σ τ : (forall i, σ i = τ i) -> gdecl_gsubst D σ = gdecl_gsubst D τ.
Proof.
  intros H; destruct D; cbn [gdecl_gsubst]; f_equal.
  all: first [ reflexivity | exact (proj1 (proj2 (proj2 gsubst_ext_all)) _ _ _ H)
             | exact (proj1 gsubst_ext_all _ _ _ H) ].
Qed.

Lemma gsub_wf_ext {G' G σ τ} : (forall i, σ i = τ i) -> [ G' ⊢ σ : G ] -> [ G' ⊢ τ : G ].
Proof.
  intros H [Hg Hn Hv]. constructor; [exact Hg | intros i; rewrite <- H; apply Hn |].
  intros n D Hin. rewrite <- H, <- (gdecl_gsubst_ext D σ τ H). exact (Hv _ _ Hin).
Qed.

Lemma gext_s_one o σ i : gext_s (o :: nil) σ i = gcons σ o i.
Proof. unfold gext_s; destruct i; cbn; [reflexivity | f_equal; lia]. Qed.

Section RecS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsRec : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation GObjRel := (GObjRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtmM := (@LRtm EM LRM).

Lemma GRel0_ext {G' G σ σ' τ τ'} : (forall i, σ i = τ i) -> (forall i, σ' i = τ' i) ->
  GRel0 EP EM G' G σ σ' -> GRel0 EP EM G' G τ τ'.
Proof.
  intros H H' R n D Hin. rewrite <- H, <- H', <- (gdecl_gsubst_ext D σ τ H). exact (R _ _ Hin).
Qed.

Lemma GSubRel_ext {G' G σ σ' τ τ'} : (forall i, σ i = τ i) -> (forall i, σ' i = τ' i) ->
  GSubRel G' G σ σ' -> GSubRel G' G τ τ'.
Proof.
  intros H H' [HL Hl Hr R Rl Rr]. constructor; [exact HL | exact (gsub_wf_ext H Hl) | exact (gsub_wf_ext H' Hr)
    | exact (GRel0_ext H H' R) | exact (GRel0_ext H H Rl) | exact (GRel0_ext H' H' Rr)].
Qed.

(** Extension by a context, one on each side, related at P. *)
Lemma GSubRel_ctx1 {G' G σ σ' Δ Δ'} : GSubRel G' G σ σ' -> [ G' ; Δ ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ ≅ Δ' ] ->
  GSubRel G' (gext G gdCtx) (gext_s (GCtx Δ :: nil) σ) (gext_s (GCtx Δ' :: nil) σ').
Proof.
  intros Hσ HΔ HΔΔ. pose proof (eqctx_wf_r (i := lD) eq_refl HΔΔ) as HΔ'.
  refine (GSubRel_ext (fun i => eq_sym (gext_s_one _ _ i)) (fun i => eq_sym (gext_s_one _ _ i)) _).
  apply (GSubRel_cons2 EP EM Hσ); cbn [gdecl_gsubst dnfo gobj_wf].
  - exact (wf_ctx_dnf HΔ).
  - exact (wf_ctx_dnf HΔ').
  - exact HΔ.
  - exact HΔ'.
  - exact (GObjRel_ctx EP EM HΔΔ).
  - exact (GObjRel_ctx EP EM (eqc_refl _ _ _ HΔ)).
  - exact (GObjRel_ctx EP EM (eqc_refl _ _ _ HΔ')).
Qed.

(** Extension by a context and a P-type over it. *)
Lemma GSubRel_ctx_ty {G' G σ σ' Δ Δ' U U' k} : GSubRel G' G σ σ' -> [ G' ; Δ ⊢[ lD ] ] ->
  [ G' ⊢[ lD ] Δ ≅ Δ' ] -> [ G' ; Δ ⊢[ lD ] U ≅ U' @ k ] -> [ G' ; Δ' ⊢[ lD ] U' @ k ] ->
  GSubRel G' (gext (gext G gdCtx) (gdTy (cvar 0) lD k))
    (gext_s (GCtx Δ :: GTy U :: nil) σ) (gext_s (GCtx Δ' :: GTy U' :: nil) σ').
Proof.
  intros Hσ HΔ HΔΔ HU HU'. pose proof (eqctx_wf_r (i := lD) eq_refl HΔΔ) as HΔ'.
  pose proof (eqty_wf_l (i := lD) eq_refl HU) as HUl.
  refine (GSubRel_ext (fun i => eq_sym (gext_s_app (GCtx Δ :: nil) (GTy U) σ i))
                      (fun i => eq_sym (gext_s_app (GCtx Δ' :: nil) (GTy U') σ' i)) _).
  pose proof (GSubRel_ctx1 Hσ HΔ HΔΔ) as H1.
  assert (Ep : forall o τ, gdecl_gsubst (gdTy (cvar 0) lD k) (gext_s (o :: nil) τ) = gdTy (pctx o) lD k)
    by (intros; reflexivity).
  refine (GSubRel_cons2 EP EM H1 _ _ _ _ _ _ _); rewrite ?Ep; cbn [pctx dnfo gobj_wf].
  - exact (wf_ty_dnf HUl).
  - exact (wf_ty_dnf HU').
  - exact HUl.
  - exact HU'.
  - apply (GObjRel_ty EP EM); [intros Hle; unfold lle in Hle; cbn in Hle; lia | exact HU].
  - apply (GObjRel_ty EP EM); [intros; apply ty_leq_refl | exact (eqty_refl _ _ _ _ _ HUl)].
  - apply (GObjRel_ty EP EM); [intros; apply ty_leq_refl | exact (eqty_refl _ _ _ _ _ HU')].
Qed.

(** ** The motives' instances are related *)

Section Mot.
Variables (G0 : gctx) (Γ0 : ctx) (L' : nat) (φ : nat -> lvl) (MT MT' : ty) (l1 l1' : lvl).
Hypothesis (HMT : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT @ lvren l1 (ush 1) ])
           (HMT' : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT' @ lvren l1' (ush 1) ])
           (Hl1 : lequiv L' (lvsubst l1 φ) (lvsubst l1' φ))
           (Hφ : usub_ok φ L' (gL G0))
           (VMT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
              VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT ψ) (usubst_ty MT' ψ)
                (lvsubst (lvren l1 (ush 1)) ψ))
           (VMT' : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
              VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT' ψ) (usubst_ty MT' ψ)
                (lvsubst (lvren l1' (ush 1)) ψ))
           (VΓ : VCtxSM (G_us G0 L' φ) (ucsubst Γ0 φ)).
Variables (G' : gctx) (σ σ' : gsub) (Θ : ctx) (e e' : lsub).
Hypothesis (Hσ : GSubRel G' (G_us G0 L' φ) σ σ')
           (He : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e e').

Lemma MotRel_T {kL kR ΔL ΔR a a'} :
  lwf L' kL -> lequiv L' kL kR -> [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  LRtmM lzero G' Θ (tyCTyp ΔL kL) (tyCTyp ΔL kL) a a' ->
  LRtmM lzero G' Θ (tyCTyp ΔR kR) (tyCTyp ΔR kR) a' a' ->
  LRtyM (lvsubst l1 φ) G' Θ
    (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))])) kL ΔL a)
    (motT (wrapMT ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄[llift (gwk (uwk e'))])) kR ΔR a').
Proof.
  intros HkL Hk HΔL HΔ Ha Ha'.
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as EL; cbn in EL.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  pose proof (proj1 (LRtm_escape Ha)) as Hat. pose proof (proj1 (LRtm_escape Ha')) as Hat'.
  rewrite (motT_inst MT φ σ e kL ΔL a), (motT_inst MT' φ σ' e' kR ΔR a')
    by first [exact (wf_ty_dnf HMT) | exact (wf_ty_dnf HMT') | assumption | exact (wf_ctx_dnf HΔL)
             | exact (wf_ctx_dnf HΔR) | exact (wf_tm_dnf Hat) | exact (wf_tm_dnf Hat')].
  (* left against right, at the left level *)
  assert (HψL : usub_ok (uext (kL :: nil) φ) L' (gL (recGT G0)))
    by (apply (usub_ok_uext (kL :: nil) φ L' (gL G0)); [repeat constructor; exact HkL | exact Hφ]).
  pose proof (VMT _ _ HψL) as X. rewrite G_us_recGT_uext in X.
  pose proof (X _ _ _ (GSubRel_ctx1 Hσ HΔL HΔ) G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  rewrite recΓT_inst' in Y.
  assert (Ha0 : LRtmM lzero G' Θ (tyCTyp ΔL kL)[e] (tyCTyp ΔL kL)[e'] a a') by exact Ha.
  pose proof (Y _ _ _ (SubRel_cons He Ha0)) as Z.
  change (lvsubst (lvren l1 (ush 1)) (uext (kL :: nil) φ)) with
    (lvsubst (lvren l1 (ush (length (kL :: nil)))) (uext (kL :: nil) φ)) in Z.
  rewrite lvren_ush_uext in Z.
  (* the right side at its own level *)
  assert (HψR : usub_ok (uext (kR :: nil) φ) L' (gL (recGT G0))).
  { apply (usub_ok_uext (kR :: nil) φ L' (gL G0)); [repeat constructor | exact Hφ].
    exact (lequiv_wf_r _ _ _ Hk). }
  pose proof (VMT' _ _ HψR) as X'. rewrite G_us_recGT_uext in X'.
  pose proof (X' _ _ _ (GSubRel_ctx1 (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) G' gwk_id
                (gwk_ok_id G')) as Y'; cbn [gwa] in Y'.
  rewrite recΓT_inst' in Y'.
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  pose proof (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) (SubRel_refl_r He)) as He'.
  assert (Ha1 : LRtmM lzero G' Θ (tyCTyp ΔR kR)[e'] (tyCTyp ΔR kR)[e'] a' a') by exact Ha'.
  pose proof (Y' _ _ _ (SubRel_cons He' Ha1)) as Z'.
  change (lvsubst (lvren l1' (ush 1)) (uext (kR :: nil) φ)) with
    (lvsubst (lvren l1' (ush (length (kR :: nil)))) (uext (kR :: nil) φ)) in Z'.
  rewrite lvren_ush_uext in Z'.
  refine (LRty_leq Z (LRty_lconv Z' _) _).
  - rewrite EL; exact Hl1.
  - apply (proj1 leq_subst_all); [apply lsub_leq_refl|].
    apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl|].
    apply (proj1 leq_usubst_all); [| apply ty_leq_refl].
    intros [|i]; unfold uext; cbn; [exact (lequiv_leqv _ _ _ Hk) | apply leqv_refl].
Qed.

End Mot.

Section Mott.
Variables (G0 : gctx) (Γ0 : ctx) (L' : nat) (φ : nat -> lvl) (Mt Mt' : ty) (l2 l2' : lvl).
Hypothesis (HMt : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt @ lvren l2 (ush 1) ])
           (HMt' : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt' @ lvren l2' (ush 1) ])
           (Hl2 : lequiv L' (lvsubst l2 φ) (lvsubst l2' φ))
           (Hφ : usub_ok φ L' (gL G0))
           (VMt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
              VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt ψ) (usubst_ty Mt' ψ)
                (lvsubst (lvren l2 (ush 1)) ψ))
           (VMt' : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
              VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt' ψ) (usubst_ty Mt' ψ)
                (lvsubst (lvren l2' (ush 1)) ψ))
           (VΓ : VCtxSM (G_us G0 L' φ) (ucsubst Γ0 φ)).
Variables (G' : gctx) (σ σ' : gsub) (Θ : ctx) (e e' : lsub).
Hypothesis (Hσ : GSubRel G' (G_us G0 L' φ) σ σ')
           (He : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e e').

Lemma MotRel_t {kL kR ΔL ΔR UL UR a a'} :
  lwf L' kL -> lequiv L' kL kR -> [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  [ G' ; ΔL ⊢[ lD ] UL ≅ UR @ kL ] -> [ G' ; ΔR ⊢[ lD ] UR @ kR ] ->
  LRtmM lzero G' Θ (tyCTrm ΔL UL kL) (tyCTrm ΔL UL kL) a a' ->
  LRtmM lzero G' Θ (tyCTrm ΔR UR kR) (tyCTrm ΔR UR kR) a' a' ->
  LRtyM (lvsubst l2 φ) G' Θ
    (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))])) kL ΔL UL a)
    (mott (wrapMt ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄[llift (gwk (gwk (uwk e')))])) kR ΔR UR a').
Proof.
  intros HkL Hk HΔL HΔ HU HUR Ha Ha'.
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as EL; cbn in EL.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  pose proof (eqty_wf_l (i := lD) eq_refl HU) as HUL.
  pose proof (proj1 (LRtm_escape Ha)) as Hat. pose proof (proj1 (LRtm_escape Ha')) as Hat'.
  rewrite (mott_inst Mt φ σ e kL ΔL UL a), (mott_inst Mt' φ σ' e' kR ΔR UR a')
    by first [exact (wf_ty_dnf HMt) | exact (wf_ty_dnf HMt') | assumption | exact (wf_ctx_dnf HΔL)
             | exact (wf_ctx_dnf HΔR) | exact (wf_ty_dnf HUL) | exact (wf_ty_dnf HUR)
             | exact (wf_tm_dnf Hat) | exact (wf_tm_dnf Hat')].
  assert (HkR : lequiv (gL G') kR kL) by (rewrite EL; apply lequiv_sym, Hk).
  assert (HUR' : [ G' ; ΔR ⊢[ lD ] UR @ kL ]) by (eapply wft_lconv; [exact HUR | rewrite EL; exact Hk]).
  (* left against right, at the left level *)
  assert (HψL : usub_ok (uext (kL :: nil) φ) L' (gL (recGt G0)))
    by (apply (usub_ok_uext (kL :: nil) φ L' (gL G0)); [repeat constructor; exact HkL | exact Hφ]).
  pose proof (VMt _ _ HψL) as X. rewrite G_us_recGt_uext in X.
  pose proof (X _ _ _ (GSubRel_ctx_ty Hσ HΔL HΔ HU HUR') G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  rewrite recΓt_inst' in Y by exact (wf_ty_nf HUL).
  assert (Ha0 : LRtmM lzero G' Θ (tyCTrm ΔL UL kL)[e] (tyCTrm ΔL UL kL)[e'] a a') by exact Ha.
  pose proof (Y _ _ _ (SubRel_cons He Ha0)) as Z.
  change (lvsubst (lvren l2 (ush 1)) (uext (kL :: nil) φ)) with
    (lvsubst (lvren l2 (ush (length (kL :: nil)))) (uext (kL :: nil) φ)) in Z.
  rewrite lvren_ush_uext in Z.
  (* the right side at its own level *)
  assert (HψR : usub_ok (uext (kR :: nil) φ) L' (gL (recGt G0))).
  { apply (usub_ok_uext (kR :: nil) φ L' (gL G0)); [repeat constructor | exact Hφ].
    exact (lequiv_wf_r _ _ _ Hk). }
  pose proof (VMt' _ _ HψR) as X'. rewrite G_us_recGt_uext in X'.
  pose proof (X' _ _ _ (GSubRel_ctx_ty (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
                          (eqty_refl _ _ _ _ _ HUR) HUR) G' gwk_id (gwk_ok_id G')) as Y'; cbn [gwa] in Y'.
  rewrite recΓt_inst' in Y' by exact (wf_ty_nf HUR).
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  pose proof (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) (SubRel_refl_r He)) as He'.
  assert (Ha1 : LRtmM lzero G' Θ (tyCTrm ΔR UR kR)[e'] (tyCTrm ΔR UR kR)[e'] a' a') by exact Ha'.
  pose proof (Y' _ _ _ (SubRel_cons He' Ha1)) as Z'.
  change (lvsubst (lvren l2' (ush 1)) (uext (kR :: nil) φ)) with
    (lvsubst (lvren l2' (ush (length (kR :: nil)))) (uext (kR :: nil) φ)) in Z'.
  rewrite lvren_ush_uext in Z'.
  refine (LRty_leq Z (LRty_lconv Z' _) _).
  - rewrite EL; exact Hl2.
  - apply (proj1 leq_subst_all); [apply lsub_leq_refl|].
    apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl|].
    apply (proj1 leq_usubst_all); [| apply ty_leq_refl].
    intros [|i]; unfold uext; cbn; [exact (lequiv_leqv _ _ _ Hk) | apply leqv_refl].
Qed.

End Mott.

End RecS.
