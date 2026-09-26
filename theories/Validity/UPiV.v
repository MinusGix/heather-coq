(** * Validity of universe polymorphism at layer M (M4_DESIGN.md F5)

    The instance of a [UΠ] (or [Λ]) at levels [ls] in a world [ρ] is its
    body at the universe substitution [uext ls φ], under the world's
    global and local substitutions: the body's validity there (the
    fundamental theorem's induction hypothesis at every [ψ]) relates it,
    once the source global context is re-levelled to the world. The right
    side's levels [ls'] are equivalent to [ls]: it is switched by level
    invariance (M3_DESIGN.md E6'). The whnf equations come from escape at
    the extended scope (the body at [uupn n φ], under [guwkn n σ] and
    [uwkn n d]). *)
From DeLaM.Validity Require Export OmegaV RecFT.

(** ** Syntax: instances of a body under the substitutions *)

Lemma usub_ok_grow {φ L1 L2 L} : usub_ok φ L1 L -> L1 <= L2 -> usub_ok φ L2 L.
Proof. intros H HL i Hi. exact (lwf_weaken _ _ _ HL (H i Hi)). Qed.

Lemma uupn_uext_lvl n ls φ i : length ls = n -> lvsubst (uupn n φ i) (uext ls lvar) = uext ls φ i.
Proof.
  intros Hn. destruct (Nat.ltb_spec i n) as [Hi | Hi].
  - rewrite uupn_lt by exact Hi. cbn [lvsubst]. unfold uext. rewrite Hn.
    destruct (Nat.ltb_spec i n); [reflexivity | lia].
  - replace i with (n + (i - n)) by lia. rewrite uupn_ush.
    rewrite (lvren_lvsubst _ _ _ lvar) by (intros m; symmetry; apply uext_ush_lvar, Hn).
    rewrite lvsubst_id by reflexivity. subst n. symmetry; apply uext_ush.
Qed.

Lemma uupn_uext_ty n ls φ (T : ty) : length ls = n -> T[uupn n φ]ᵤ[uext ls lvar]ᵤ = T[uext ls φ]ᵤ.
Proof. intros Hn. apply usubst_usubst_ty. intros i; symmetry; apply uupn_uext_lvl, Hn. Qed.
Lemma uupn_uext_tm n ls φ (t : tm) : length ls = n -> t[uupn n φ]ᵤ[uext ls lvar]ᵤ = t[uext ls φ]ᵤ.
Proof. intros Hn. apply usubst_usubst. intros i; symmetry; apply uupn_uext_lvl, Hn. Qed.
Lemma uupn_uext_l n ls φ l : length ls = n -> lvsubst (lvsubst l (uupn n φ)) (uext ls lvar) = lvsubst l (uext ls φ).
Proof. intros Hn. apply lvsubst_lvsubst. intros i; symmetry; apply uupn_uext_lvl, Hn. Qed.

Section KwU.
Context `{E : GenericEq}.

Lemma kty_usubst {G Γ} (ρ : kwk G Γ) (T : ty) ψ : kty ρ T[ψ]ᵤ = (kty ρ T)[ψ]ᵤ.
Proof. unfold kty. rewrite <- usubst_gwa_ty, <- usubst_ren_ty. reflexivity. Qed.
Lemma ktm_usubst {G Γ} (ρ : kwk G Γ) (t : tm) ψ : ktm ρ t[ψ]ᵤ = (ktm ρ t)[ψ]ᵤ.
Proof. unfold ktm. rewrite <- usubst_gwa_tm, <- usubst_ren. reflexivity. Qed.

(** The instance at [ls] of a body substituted under the binder. *)
Lemma upi_inst_ty n ls φ (T : ty) σ d {G Γ} (ρ : kwk G Γ) : length ls = n -> gdnf σ -> LK dnftm d ->
  (kty ρ T[uupn n φ]ᵤ⦃guwkn n σ⦄[uwkn n d])[uext ls lvar]ᵤ = T[uext ls φ]ᵤ⦃gsub_wk σ (kw_γ ρ)⦄[kwsub ρ d].
Proof.
  intros Hn Hσ Hd. rewrite <- kty_usubst, <- (subst_uinst_ty n ls _ d Hn Hd),
    <- (gsubst_uinst_ty n ls _ σ Hn Hσ), (uupn_uext_ty n ls φ T Hn), kty_subst, gwa_gsubst_ty.
  reflexivity.
Qed.
Lemma upi_inst_tm n ls φ (t : tm) σ d {G Γ} (ρ : kwk G Γ) : length ls = n -> gdnf σ -> LK dnftm d ->
  (ktm ρ t[uupn n φ]ᵤ⦃guwkn n σ⦄[uwkn n d])[uext ls lvar]ᵤ = t[uext ls φ]ᵤ⦃gsub_wk σ (kw_γ ρ)⦄[kwsub ρ d].
Proof.
  intros Hn Hσ Hd. rewrite <- ktm_usubst, <- (subst_uinst_tm n ls _ d Hn Hd),
    <- (gsubst_uinst_tm n ls _ σ Hn Hσ), (uupn_uext_tm n ls φ t Hn).
  unfold ktm, kwsub. rewrite gwa_subst, subst_ren_lren, gwa_gsubst_tm. reflexivity.
Qed.

End KwU.

(** The body's scope at [uext ls φ]: the source's, re-levelled. *)
Lemma G_us_uwk_uext_φ n G L'' ls φ : length ls = n -> G_us (gctx_uwk n G) L'' (uext ls φ) = G_us G L'' φ.
Proof.
  intros <-. unfold G_us, gctx_usubst, gctx_uwk; cbn [gL gΨ]. f_equal. apply map_uren_uext.
Qed.
Lemma ctx_uwk_uext_φ n (Γ : ctx) ls φ : length ls = n -> ucsubst Γ⟨ush n⟩ᵤ (uext ls φ) = ucsubst Γ φ.
Proof. intros <-. apply (proj1 (proj2 (proj2 uren_usubst_all))). intros; symmetry; apply uext_ush. Qed.

(** Instance levels at equivalent level lists, over [φ]. *)
Lemma lequiv_ilvφ {L L' n l l' ls ls' φ} : usub_ok φ L' L -> lequiv (n + L) l l' -> length ls = n ->
  Forall2 (lequiv L') ls ls' -> lequiv L' (lvsubst l (uext ls φ)) (lvsubst l' (uext ls' φ)).
Proof.
  intros Hφ Hl Hn Hls. subst n.
  pose proof (usub_ok_uext _ _ _ _ (lequivs_lwf_l _ _ _ Hls) Hφ) as H1.
  eapply lequiv_trans; [exact (lequiv_lvsubst _ _ _ _ _ H1 Hl) |].
  apply leqv_lequiv.
  - exact (lwf_lvsubst _ _ _ _ H1 (lequiv_wf_r _ _ _ Hl)).
  - rewrite (Forall2_length Hls) in Hl.
    exact (lwf_lvsubst _ _ _ _ (usub_ok_uext _ _ _ _ (lequivs_lwf_r _ _ _ Hls) Hφ) (lequiv_wf_r _ _ _ Hl)).
  - apply leqv_lvsubst; [apply leqv_refl | apply leqv_uext, (lequivs_leqv _ _ _ Hls)].
Qed.

Section UPi.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsU : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
#[local] Instance LR_M_permU : VPPerm (@lr_vp LRM) := vpM_perm EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation VTySωM := (@VTySω EP EM EM LRM).
Local Notation VTmSωM := (@VTmSω EP EM EM LRM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtyωM := (@LRtyω EM LRM).
Local Notation LRωM := (@LRω EM LRM).

Variables (G0 : gctx) (Γ0 : ctx) (L' : nat) (φ : nat -> lvl) (n : nat).
Hypothesis (Hφ : usub_ok φ L' (gL G0)) (HG0 : [ ⊢ G_us G0 L' φ ])
  (HΓ0 : [ G_us G0 L' φ ; ucsubst Γ0 φ ⊢[ lM ] ]) (Hn : 0 < n).

Local Notation Gφ := (G_us G0 L' φ).
Local Notation Γφ := (ucsubst Γ0 φ).
Local Notation Gu := (gctx_uwk n G0).
Local Notation Γu := (Γ0⟨ush n⟩ᵤ).

(** Facts at a target of a related global substitution. *)
Section At.
Variables (G' : gctx) (σ σ' : gsub) (Δ : ctx) (d d' : lsub).
Hypothesis (Hσ : GSubRel G' Gφ σ σ') (Hd : SubRelM G' Γφ⦃σ⦄ Δ d d').

Lemma u_L : L' <= gL G'. Proof. exact (gsr_L _ _ _ _ _ _ Hσ). Qed.
Lemma u_G : [ ⊢ G' ]. Proof. exact (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)). Qed.
Lemma u_φn : usub_ok (uupn n φ) (n + gL G') (n + gL G0).
Proof. apply usub_ok_uupn, (usub_ok_grow Hφ u_L). Qed.
Lemma u_Γσ : [ G' ; Γφ⦃σ⦄ ⊢[ lM ] ]. Proof. exact (gs_ctx EP EM Hσ HΓ0 compt_M). Qed.
Lemma u_Δ : [ G' ; Δ ⊢[ lM ] ].
Proof. pose proof (SubRel_ctx Hd) as X. rewrite (@gm_layer_M EP EM EMl) in X. exact X. Qed.

(** The related substitutions under the binder. *)
Lemma u_σn : GSubRel (gctx_uwk n G') (gctx_uwk n Gφ) (guwkn n σ) (guwkn n σ').
Proof. exact (GSubRel_uwkn EP EM HG0 Hσ). Qed.
Lemma u_dn : SubRelM (gctx_uwk n G') (Γφ⟨ush n⟩ᵤ)⦃guwkn n σ⦄ Δ⟨ush n⟩ᵤ (uwkn n d) (uwkn n d').
Proof.
  rewrite (uren_ush_gsubst_ctx n _ _ (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ))).
  exact (SubRel_uwkn u_G (wf_ctx_lwf u_Γσ) Hd).
Qed.

(** The world's substitutions, with the source re-levelled to the world. *)
Lemma u_σρ (ρ : kwk G' Δ) :
  GSubRel (kw_G ρ) (G_us G0 (gL (kw_G ρ)) φ) (gsub_wk σ (kw_γ ρ)) (gsub_wk σ' (kw_γ ρ)).
Proof.
  exact (GSubRel_relevel EP EM (gL (kw_G ρ)) (GSubRel_wk EP EM Hσ (kw_gok ρ) (kw_glob ρ)) (le_n _)).
Qed.
Lemma u_dρ (ρ : kwk G' Δ) : SubRelM (kw_G ρ) Γφ⦃gsub_wk σ (kw_γ ρ)⦄ (kw_Δ ρ) (kwsub ρ d) (kwsub ρ d').
Proof. rewrite <- gwa_gsubst_ctx. exact (SubRel_kw _ _ _ ρ _ _ Hd). Qed.
Lemma u_ψ (ρ : kwk G' Δ) ls : length ls = n -> Forall (lwf (gL (kw_G ρ))) ls ->
  usub_ok (uext ls φ) (gL (kw_G ρ)) (n + gL G0).
Proof.
  intros <- Hls. apply usub_ok_uext; [exact Hls |].
  apply (usub_ok_grow Hφ). pose proof u_L. pose proof (kw_gL ρ). lia.
Qed.

End At.

(** ** [UΠ] formation and congruence *)

(** The body of a [UΠ] or [Λ] under [φ], [σ] and [d]. *)
Definition Aσ (X : ty) (σ0 : gsub) (d0 : lsub) : ty := X[uupn n φ]ᵤ⦃guwkn n σ0⦄[uwkn n d0].
Definition bσ (x : tm) (σ0 : gsub) (d0 : lsub) : tm := x[uupn n φ]ᵤ⦃guwkn n σ0⦄[uwkn n d0].

(** The instances' canonical relation. *)
Definition canonI (G' : gctx) (Δ : ctx) (A A' : ty) (k : lvl) : @UInstRel EM G' Δ :=
  fun ρ ls ls' => @LRrel EM LRM (lmeasure (lvsubst k (uext ls lvar))) (kw_G ρ) (kw_Δ ρ)
    (usubst_ty (kty ρ A) (uext ls lvar)) (usubst_ty (kty ρ A') (uext ls' lvar)) (lvsubst k (uext ls lvar)).

Section Form.
Variables (l l' : lvl) (T T' : ty).
Hypothesis (Hl : lequiv (n + gL G0) l l')
  (VT : forall L'' ψ, usub_ok ψ L'' (n + gL G0) ->
     VTySM (G_us Gu L'' ψ) (ucsubst Γu ψ) T[ψ]ᵤ T'[ψ]ᵤ (lvsubst l ψ)).

Section At2.
Variables (G' : gctx) (σ σ' : gsub) (Δ : ctx) (d d' : lsub).
Hypothesis (Hσ : GSubRel G' Gφ σ σ') (Hd : SubRelM G' Γφ⦃σ⦄ Δ d d').

(** The bodies at the extended scope. *)
Lemma upi_esc : LRtyM (lvsubst l (uupn n φ)) (gctx_uwk n G') Δ⟨ush n⟩ᵤ (Aσ T σ d) (Aσ T' σ' d').
Proof.
  pose proof (VT (n + L') (uupn n φ) (usub_ok_uupn _ _ _ _ Hφ)) as X.
  unfold G_us in X. rewrite gctx_uwk_usubst, ucren_ush_usubst in X.
  exact (VTyG_loc (X _ _ _ (u_σn _ _ _ Hσ)) _ _ _ (u_dn _ _ _ _ _ _ Hσ Hd)).
Qed.

(** The instances: the bodies at [uext ls φ] in the world. *)
Lemma upi_inst (ρ : @kwk EM G' Δ) ls ls' : length ls = n -> Forall2 (lequiv (gL (kw_G ρ))) ls ls' ->
  @LogRel EM LRM (lvsubst (lvsubst l (uupn n φ)) (uext ls lvar)) (kw_G ρ) (kw_Δ ρ)
    (kty ρ (Aσ T σ d))[uext ls lvar]ᵤ (kty ρ (Aσ T' σ' d'))[uext ls' lvar]ᵤ
    (lvsubst (lvsubst l (uupn n φ)) (uext ls lvar))
    (canonI G' Δ (Aσ T σ d) (Aσ T' σ' d') (lvsubst l (uupn n φ)) ρ ls ls').
Proof.
  intros Hlen Hls.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (lequivs_lwf_l _ _ _ Hls) as Wls. pose proof (lequivs_lwf_r _ _ _ Hls) as Wls'.
  assert (Hlen' : length ls' = n) by (rewrite <- (Forall2_length Hls); exact Hlen).
  pose proof (u_ψ _ _ _ _ Hσ ρ ls Hlen Wls) as Hψ.
  pose proof (u_ψ _ _ _ _ Hσ ρ ls' Hlen' Wls') as Hψ'.
  pose proof (VT _ _ Hψ) as X. rewrite (G_us_uwk_uext_φ n _ _ ls φ Hlen), (ctx_uwk_uext_φ n _ ls φ Hlen) in X.
  pose proof (VTyG_loc (X _ _ _ (u_σρ _ _ _ _ Hσ ρ)) _ _ _ (u_dρ _ _ _ _ _ Hd ρ)) as Y.
  pose proof (VT _ _ Hψ') as X'. rewrite (G_us_uwk_uext_φ n _ _ ls' φ Hlen'), (ctx_uwk_uext_φ n _ ls' φ Hlen') in X'.
  pose proof (VTyG_loc (X' _ _ _ (u_σρ _ _ _ _ Hσ ρ)) _ _ _ (u_dρ _ _ _ _ _ Hd ρ)) as Y2.
  pose proof (LRty_trans (LRty_sym Y2) Y2) as Y'.
  assert (El : lequiv (gL (kw_G ρ)) (lvsubst l (uext ls φ)) (lvsubst l (uext ls' φ)))
    by exact (lequiv_ilvφ (usub_ok_grow Hφ (Nat.le_trans _ _ _ (u_L _ _ _ Hσ) (kw_gL ρ)))
                (lequiv_refl _ _ (lequiv_wf_l _ _ _ Hl)) Hlen Hls).
  assert (Ex : ty_leq T'[uext ls φ]ᵤ⦃gsub_wk σ' (kw_γ ρ)⦄[kwsub ρ d'] T'[uext ls' φ]ᵤ⦃gsub_wk σ' (kw_γ ρ)⦄[kwsub ρ d']).
  { apply subst_leq_ty. apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl |].
    apply (proj1 leq_usubst_all); [apply leqv_uext, (lequivs_leqv _ _ _ Hls) | apply ty_leq_refl]. }
  pose proof (LRty_leq Y (LRty_lconv Y' El) Ex) as Z.
  destruct Z as [R HR]. unfold Aσ.
  rewrite <- (upi_inst_ty n ls φ T σ d ρ Hlen Nσ Nd), <- (upi_inst_ty n ls' φ T' σ' d' ρ Hlen' Nσ' Nd'),
    <- (uupn_uext_l n ls φ l Hlen) in HR.
  exact (LR_canon _ _ _ _ _ _ _ HR).
Qed.

Lemma upi_LR :
  LRωM G' Δ (tyUPi n (lvsubst l (uupn n φ)) (Aσ T σ d)) (tyUPi n (lvsubst l' (uupn n φ)) (Aσ T' σ' d'))
    (@UPiRel EM G' Δ n (lvsubst l (uupn n φ)) (lvsubst l' (uupn n φ)) (Aσ T σ d) (Aσ T' σ' d')
       (canonI G' Δ (Aσ T σ d) (Aσ T' σ' d') (lvsubst l (uupn n φ)))).
Proof.
  destruct upi_esc as [R0 H0]. destruct (escape_ty _ _ _ _ _ _ _ _ H0) as (HA & HA' & HAA).
  rewrite (@gm_layer_M EP EM EMl) in HA, HA'.
  pose proof (u_φn _ _ _ Hσ) as Hφn.
  assert (Hll : lequiv (n + gL G') (lvsubst l (uupn n φ)) (lvsubst l' (uupn n φ)))
    by exact (lequiv_lvsubst _ _ _ _ _ Hφn Hl).
  pose proof (u_Δ _ _ _ _ _ Hd) as HΔ.
  apply (@LRupi EM LRM G' Δ _ _ _ n (lvsubst l (uupn n φ)) (lvsubst l' (uupn n φ)) (Aσ T σ d) (Aσ T' σ' d')
           (canonI G' Δ (Aσ T σ d) (Aσ T' σ' d') (lvsubst l (uupn n φ)))).
  - exact Hn.
  - exact Hll.
  - apply tyred_refl. rewrite (@gm_layer_M EP EM EMl).
    apply wft_upi; [exact HΔ | exact Hn | exact (lequiv_wf_l _ _ _ Hll) | exact HA].
  - apply tyred_refl. rewrite (@gm_layer_M EP EM EMl).
    apply wft_upi; [exact HΔ | exact Hn | exact (lequiv_wf_r _ _ _ Hll) |].
    eapply wft_lconv; [exact HA' | apply lequiv_sym, Hll].
  - apply geq_ty_upi; [exact HΔ | exact Hn | exact Hll | exact HA | exact HAA].
  - intros ρ ls ls' Hlen Hls. exact (upi_inst ρ ls ls' Hlen Hls).
  - apply releq_refl.
Qed.

End At2.

Lemma VS_upi : VTySωM Gφ Γφ (tyUPi n (lvsubst l (uupn n φ)) T[uupn n φ]ᵤ)
                            (tyUPi n (lvsubst l' (uupn n φ)) T'[uupn n φ]ᵤ).
Proof.
  apply VTySω_intro_loc. intros G' σ σ' Hσ Δ d d' Hd.
  eexists. exact (upi_LR _ _ _ _ _ _ Hσ Hd).
Qed.

End Form.

End UPi.
