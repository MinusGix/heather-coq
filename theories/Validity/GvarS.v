(** * Validity of global variables ([U^δ], [u^δ])

    Under related global substitutions a global variable goes either to
    the same global variable (a neutral, related by the generic laws for
    global variables) or to objects related by [⊩^{≥P}_P] in the
    substituted binding context, which are instantiated at the related
    local substitutions ([VSub]). *)
From DeLaM.Validity Require Export RulesS LayerV.

#[local] Existing Instance LR_P.

(** ** Locally, and under global weakenings *)

Section GvarG.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma SubRel_geq G : forall Δ Θ e e', SubRel G Δ Θ e e' -> forall n A k, in_ctx Δ n A k ->
  [ G ; Θ ⊢ llk e n ≈ llk e' n : A[e] @ k ].
Proof.
  induction Δ as [| g | Δ IH B kB]; intros Θ e e' H n A k Hin; inversion Hin; subst;
    cbn [SubRel] in H; destruct H as [Ht Hh]; rewrite shift_subst_ty.
  - exact (LRtm_geq Hh).
  - match goal with Hm : in_ctx Δ _ _ _ |- _ => pose proof (IH _ _ _ Ht _ _ _ Hm) as X end.
    now rewrite !llk_ldrop in X.
Qed.

Lemma SubRel_geq_lsub {G Δ Θ e e'} : SubRel G Δ Θ e e' -> dnfl e -> dnfl e' -> geq_lsub G Θ e e' Δ.
Proof.
  intros H N N'. destruct (SubRel_tail _ _ _ _ _ H) as [T T'].
  pose proof (SubRel_wf_l _ _ _ _ _ H) as [_ _ _ W]. pose proof (SubRel_wf_r H) as [_ _ _ W'].
  constructor; auto; [exact (SubRel_ctx H) | exact (SubRel_geq _ _ _ _ _ H)].
Qed.

(** Related local substitutions under every global weakening. *)
Definition VSubK (G : gctx) (Γ : ctx) (δ δ' : lsub) (Δ : ctx) : Prop :=
  forall G' γ, gwk_ok γ G' G -> VSub G' Γ⟦γ⟧ δ⟦γ⟧ δ'⟦γ⟧ Δ⟦γ⟧.

Lemma subst_comp_ty (T : ty) d e : T[d][e] = T[d[e]].
Proof. apply subst_subst_ty; intros n; now rewrite llk_lcomp. Qed.
Lemma subst_comp (t : tm) d e : t[d][e] = t[d[e]].
Proof. apply subst_subst; intros n; now rewrite llk_lcomp. Qed.

Lemma VTyG_inst {G Γ Δ T T' δ δ' l} : VTyG G Δ T T' l -> VSubK G Γ δ δ' Δ ->
  VTyG G Γ T[δ] T'[δ'] l.
Proof.
  intros H Hδ G' γ Hγ Θ e e' He. rewrite !gwa_subst_ty, !subst_comp_ty.
  exact (H _ _ Hγ _ _ _ (Hδ _ _ Hγ _ _ _ He)).
Qed.

Lemma VTmG_inst {G Γ Δ A t t' δ δ' l} : VTmG G Δ t t' A l -> VTyG G Δ A A l ->
  VSubK G Γ δ δ' Δ -> VSubK G Γ δ δ Δ -> VTmG G Γ t[δ] t'[δ'] A[δ] l.
Proof.
  intros H HA Hδ Hδδ G' γ Hγ Θ e e' He. rewrite !gwa_subst_ty, !gwa_subst, !subst_comp_ty, !subst_comp.
  pose proof (H _ _ Hγ _ _ _ (Hδ _ _ Hγ _ _ _ He)) as X.
  eapply LRtm_irrel_r; [exact X|]. exact (HA _ _ Hγ _ _ _ (Hδδ _ _ Hγ _ _ _ He)).
Qed.

Lemma subst_tyGvar U d e : (tyGvar U d)[e] = tyGvar U d[e].
Proof. reflexivity. Qed.
Lemma subst_gvar u d e : (gvar u d)[e] = gvar u d[e].
Proof. reflexivity. Qed.

(** A global variable sent to a global variable: a neutral. *)
Lemma VTyG_gvar_ne {G Γ x Δ i' l δ δ'} : in_gctx (gΨ G) x (gdTy Δ i' l) -> lle i' ge_layer ->
  dnfl δ -> dnfl δ' -> VSubK G Γ δ δ' Δ -> VTyG G Γ (tyGvar x δ) (tyGvar x δ') l.
Proof.
  intros Hin Hi N N' Hδ G' γ Hγ Θ e e' He. rewrite !gwa_tyGvar, !subst_tyGvar.
  pose proof (Hδ _ _ Hγ _ _ _ He) as X. destruct (SubRel_dnf _ _ _ _ _ He) as [Ne Ne'].
  pose proof (SubRel_geq_lsub X (dnfl_lcomp _ _ (dnfl_gwa _ _ N) Ne) (dnfl_lcomp _ _ (dnfl_gwa _ _ N') Ne'))
    as HL.
  pose proof (gne_ty_gvar (in_gctx_gwa Hγ Hin) Hi HL) as Hne.
  pose proof (geq_ty_sound (gne_ty_geq Hne)) as Heq.
  eexists. eapply LRne; [apply tyred_refl, (eqty_wf_l ge_typeof Heq) | apply tyred_refl, (eqty_wf_r ge_typeof Heq)
                        | exact Hne | apply releq_refl].
Qed.

Lemma VTmG_gvar_ne {G Γ x Δ i' A l δ δ'} : in_gctx (gΨ G) x (gdTm Δ i' A l) -> lle i' ge_layer ->
  dnfl δ -> dnfl δ' -> VSubK G Γ δ δ' Δ -> VSubK G Γ δ δ Δ -> VTyG G Δ A A l ->
  VTmG G Γ (gvar x δ) (gvar x δ') A[δ] l.
Proof.
  intros Hin Hi N N' Hδ Hδδ HA G' γ Hγ Θ e e' He.
  rewrite !gwa_gvar, !gwa_subst_ty, !subst_comp_ty, !subst_gvar.
  pose proof (Hδ _ _ Hγ _ _ _ He) as X. destruct (SubRel_dnf _ _ _ _ _ He) as [Ne Ne'].
  pose proof (SubRel_geq_lsub X (dnfl_lcomp _ _ (dnfl_gwa _ _ N) Ne) (dnfl_lcomp _ _ (dnfl_gwa _ _ N') Ne'))
    as HL.
  pose proof (gne_tm_gvar (in_gctx_gwa Hγ Hin) Hi HL) as Hne.
  destruct (HA _ _ Hγ _ _ _ (Hδδ _ _ Hγ _ _ _ He)) as [R HR].
  exists R; split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR); [exact Hne|].
  eapply gne_tm_conv; [exact Hne|]. apply geq_ty_sound, (escape_ty _ _ _ _ _ _ _ _ HR).
Qed.

End GvarG.

(** A binding's context (and type) is well-formed in the global context. *)
Definition DWf (G : gctx) (D : gdecl) : Prop :=
  match D with
  | gdCtx => True
  | gdTy Δ _ _ => [ G ; Δ ⊢[ lD ] ]
  | gdTm Δ _ T l => [ G ; Δ ⊢[ lD ] T @ l ]
  end.

Lemma gwk_ok_wk1 L D Ψ : gwk_ok (gwk_step gwk_id) (mkG L (D :: Ψ)) (mkG L Ψ).
Proof. split; [reflexivity | constructor; constructor]. Qed.

Lemma in_gctx_DWf {G n D} : [ ⊢ G ] -> in_gctx (gΨ G) n D -> DWf G D.
Proof.
  intros HG; revert n D. induction HG as [L | L Ψ HG IH | L Ψ Δ i l HG IH HΔ Hi Hl | L Ψ Δ i T l HG IH HT Hi Hl];
    intros n D Hin; cbn in Hin; inversion Hin; subst; try exact I.
  all: cbn [DWf gdecl_ren];
    try match goal with Hm : in_gctx ?Ψ _ ?D0 |- _ => is_var Ψ;
          pose proof (IH _ _ Hm) as X; destruct D0; cbn in X |- *; try exact I end.
  all: first [ refine (gwk_ctx (gwk_ok_wk1 _ _ _) _ _) | refine (gwk_ty (gwk_ok_wk1 _ _ _) _ _) ];
    first [eassumption | econstructor; eassumption].
Qed.

(** The layers of the bindings. *)
Definition DLayer (D : gdecl) : Prop :=
  match D with
  | gdCtx => True
  | gdTy _ i _ => i = lC \/ i = lD
  | gdTm _ i _ _ => i = lV \/ i = lC
  end.

Lemma DLayer_ren D ξ : DLayer (gdecl_ren D ξ) = DLayer D.
Proof. now destruct D. Qed.

Lemma in_gctx_DLayer {G n D} : [ ⊢ G ] -> in_gctx (gΨ G) n D -> DLayer D.
Proof.
  intros HG; revert n D. induction HG as [L | L Ψ HG IH | L Ψ Δ i l HG IH HΔ Hi Hl | L Ψ Δ i T l HG IH HT Hi Hl];
    intros n D Hin; cbn in Hin; inversion Hin; subst; rewrite ?DLayer_ren; cbn; auto;
    match goal with Hm : in_gctx ?Ψ _ _ |- _ => is_var Ψ; exact (IH _ _ Hm) end.
Qed.

(** The tail condition only depends on the contexts' shapes (and both
    contexts expand by the same image of their tail, E9). *)
Lemma lsub_tail_gsubst_r {d Δ Γ σ σ'} : lsub_tail d Δ Γ -> lsub_tail d⦃σ'⦄ Δ⦃σ⦄ Γ⦃σ⦄.
Proof.
  intros [Ht Hl]; split.
  - rewrite (ctx_tail_gsubst' Δ), (ctx_tail_gsubst' Γ); now rewrite Ht.
  - intros n; rewrite !clen_gsubst'. assert (E : tlen σ Δ = tlen σ Γ) by (unfold tlen; now rewrite Ht).
    rewrite E, <- !Nat.add_assoc. cbn [gsubst GSubst_lsub]. rewrite llk_glsubst, Hl; reflexivity.
Qed.

Lemma lle_D_notM {i} : lle i lD -> i <> lM.
Proof. intros Hi ->; discriminate (lle_M _ Hi). Qed.

(** ** With global substitutions *)

Section GvarS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxS := (@VCtxS EP EM E LP).
Local Notation VTyS := (@VTyS EP EM E LP).
Local Notation VTmS := (@VTmS EP EM E LP).

Lemma dnfl_gs {G' G σ σ' d} : GSubRel G' G σ σ' -> dnfl d -> dnfl d⦃σ⦄ /\ dnfl d⦃σ'⦄.
Proof.
  intros Hσ N. split; apply (proj2 (proj2 (proj2 gsubst_dnf_all))); auto;
    [exact (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) | exact (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ))].
Qed.

Lemma VSubKS {i0 G Γ Δ d d'} : [ G ; Γ ⊢[ i0 ] ] -> [ G ; Δ ⊢[ lD ] ] -> VCtxS G Δ ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> VTmS G Γ (llk d n) (llk d' n) A[d] k) ->
  forall G' σ σ', GSubRel G' G σ σ' -> VSubK G' Γ⦃σ⦄ d⦃σ⦄ d'⦃σ'⦄ Δ⦃σ⦄.
Proof.
  intros HΓ HΔ VΔ Ht Nd Ht' Nd' Hv G' σ σ' Hσ G'' γ Hγ.
  destruct (dnfl_gs (d := d) Hσ Nd) as [Nd1 _]. destruct (dnfl_gs (d := d') Hσ Nd') as [_ Nd2].
  apply VSub_intro.
  - exact (VΔ _ _ _ (GSubRel_refl_l _ _ Hσ) _ _ Hγ).
  - apply lsub_tail_gwa, lsub_tail_gsubst'; assumption.
  - apply lsub_tail_gwa, lsub_tail_gsubst_r; assumption.
  - intros n; apply dnfl_llk, dnfl_gwa, Nd1.
  - intros n; apply dnfl_llk, dnfl_gwa, Nd2.
  - intros n A' k Hin. destruct (in_ctx_gwa_inv _ _ _ _ _ Hin) as (A0 & Hin0 & ->).
    destruct (in_ctx_gsubst_inv' _ _ _ _ _ Hin0) as [(A & HinA & ->) | (g & m & T1 & Hg & -> & Hm & ->)].
    + pose proof (Hv _ _ _ HinA _ _ _ Hσ _ _ Hγ) as X.
      rewrite gsubst_subst_ty, gwa_subst_ty in X. rewrite !llk_gwa, !llk_glsubst. exact X.
    + (* an entry of the image of [Δ]'s context variable: a variable of [Γ⦃σ⦄] *)
      rewrite !llk_gwa, (gs_tail_var d Δ Γ σ m Ht), (gs_tail_var d' Δ Γ σ' m Ht').
      rewrite <- gwa_subst_ty, (tail_entry_ty d Δ Γ σ T1 Ht (in_ctx_nf _ _ _ _ Hm)), !gwa_var.
      apply V_var, in_ctx_gwa, (in_ctx_gsubst_tail Γ g); [| exact Hm].
      rewrite <- (proj1 Ht); exact Hg.
Qed.

Lemma VTyS_inst {i0 G Γ Δ A d d' l} : [ G ; Γ ⊢[ i0 ] ] -> [ G ; Δ ⊢[ lD ] ] -> VCtxS G Δ ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n B k, in_ctx Δ n B k -> VTmS G Γ (llk d n) (llk d' n) B[d] k) ->
  VTyS G Δ A A l -> VTyS G Γ A[d] A[d'] l.
Proof.
  intros HΓ HΔ VΔ Ht Nd Ht' Nd' Hv HA G' σ σ' Hσ. rewrite !gsubst_subst_ty.
  exact (VTyG_inst (HA _ _ _ Hσ) (VSubKS HΓ HΔ VΔ Ht Nd Ht' Nd' Hv _ _ _ Hσ)).
Qed.

(** A global variable is valid when its local substitution is.  [proj]
    projects the images' relatedness at [⊩^{≥P}_P] (both instances) to
    the instance at hand; the images are MLTT types and terms, as they
    are formed below layer M (Layering Restriction). *)

Lemma VS_tygvar {i0 G Γ U Δ i' l d d'}
  (proj : forall G' Δ T T' l, mltt_ctx Δ -> mltt_ty T -> mltt_ty T' ->
            @VTyG EP LR_P G' Δ T T' l /\ @VTyG EM LR_P G' Δ T T' l -> @VTyG E LP G' Δ T T' l) :
  in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' ge_layer -> i' <> lM -> [ G ; Γ ⊢[ i0 ] ] -> [ G ; Δ ⊢[ lD ] ] ->
  VCtxS G Δ ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> VTmS G Γ (llk d n) (llk d' n) A[d] k) ->
  VTyS G Γ (tyGvar U d) (tyGvar U d') l.
Proof.
  intros Hin Hi HiM HΓ HΔ VΔ Ht Nd Ht' Nd' Hv G' σ σ' Hσ.
  pose proof (VSubKS HΓ HΔ VΔ Ht Nd Ht' Nd' Hv _ _ _ Hσ) as K.
  destruct (dnfl_gs (d := d) Hσ Nd) as [Nd1 _]. destruct (dnfl_gs (d := d') Hσ Nd') as [_ Nd2].
  pose proof (gsr_rel _ _ _ _ _ _ Hσ _ _ Hin) as R.
  pose proof (gsw_var _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ) _ _ Hin) as W.
  pose proof (gsw_var _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ) _ _ Hin) as W'.
  pose proof (mltt_wf_ctx (gs_ctx EP EM Hσ HΔ compt_D) ltac:(discriminate)) as MΔ.
  cbn [gsubst GSubst_ty gsubst_ty]. fold (d⦃σ⦄) (d'⦃σ'⦄).
  cbn in R, W, W'. destruct (σ U) as [x | | T | ], (σ' U) as [x' | | T' | ]; cbn in R, W, W' |- *;
    try contradiction.
  - subst x'. destruct W as (i'' & Hi'' & Hin'').
    exact (VTyG_gvar_ne Hin'' (lle_trans _ _ _ Hi'' Hi) Nd1 Nd2 K).
  - exact (VTyG_inst (proj _ _ _ _ _ MΔ (mltt_wf_ty W HiM) (mltt_wf_ty W' HiM) (proj2 R)) K).
Qed.

Lemma VS_gvar {i0 G Γ u Δ i' A l d d'}
  (proj : forall G' Δ t t' A l, mltt_ctx Δ -> mltt_ty A ->
            @VTmG EP LR_P G' Δ t t' A l /\ @VTmG EM LR_P G' Δ t t' A l -> @VTmG E LP G' Δ t t' A l) :
  in_gctx (gΨ G) u (gdTm Δ i' A l) -> lle i' ge_layer -> [ G ; Γ ⊢[ i0 ] ] -> [ G ; Δ ⊢[ lD ] A @ l ] ->
  VCtxS G Δ ->
  VTyS G Δ A A l ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n B k, in_ctx Δ n B k -> VTmS G Γ (llk d n) (llk d' n) B[d] k) ->
  (forall n B k, in_ctx Δ n B k -> VTmS G Γ (llk d n) (llk d n) B[d] k) ->
  VTmS G Γ (gvar u d) (gvar u d') A[d] l.
Proof.
  intros Hin Hi HΓ HA VΔ VA Ht Nd Ht' Nd' Hv Hvv G' σ σ' Hσ.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HA) as HΔ.
  pose proof (mltt_wf_ctx (gs_ctx EP EM Hσ HΔ compt_D) ltac:(discriminate)) as MΔ.
  pose proof (mltt_wf_ty (gs_ty EP EM Hσ HA) ltac:(discriminate)) as MA.
  pose proof (VSubKS HΓ HΔ VΔ Ht Nd Ht' Nd' Hv _ _ _ Hσ) as K.
  pose proof (VSubKS HΓ HΔ VΔ Ht Nd Ht Nd Hvv _ _ _ (GSubRel_refl_l _ _ Hσ)) as Kd.
  pose proof (VA _ _ _ (GSubRel_refl_l _ _ Hσ)) as VA'.
  destruct (dnfl_gs (d := d) Hσ Nd) as [Nd1 _]. destruct (dnfl_gs (d := d') Hσ Nd') as [_ Nd2].
  pose proof (gsr_rel _ _ _ _ _ _ Hσ _ _ Hin) as R.
  pose proof (gsw_var _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ) _ _ Hin) as W.
  rewrite gsubst_subst_ty. cbn [gsubst GSubst_tm gsubst_tm]. fold (d⦃σ⦄) (d'⦃σ'⦄).
  cbn in R, W. destruct (σ u) as [x | | | t], (σ' u) as [x' | | | t']; cbn in R, W |- *; try contradiction.
  - subst x'. destruct W as (i'' & Hi'' & Hin'').
    exact (VTmG_gvar_ne Hin'' (lle_trans _ _ _ Hi'' Hi) Nd1 Nd2 K Kd VA').
  - exact (VTmG_inst (proj _ _ _ _ _ _ MΔ MA (proj2 R)) VA' K Kd).
Qed.

End GvarS.
