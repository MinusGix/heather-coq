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

(** ** Typed reductions of [$] (layer M) *)

Lemma tmred_ubeta_M {G Γ n l B b ls} : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lwf (n + gL G) l ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] B @ l ] -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] b : B @ l ] ->
  length ls = n -> Forall (lwf (gL G)) ls ->
  [ G ; Γ ⊢[ lM ] uapp (ulam n l b) ls ⤳* b[uext ls lvar]ᵤ : B[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros HΓ Hn Hl HB Hb Hlen Hls. constructor.
  - eapply pre_ubeta_l; eassumption.
  - econstructor; [apply red_ubeta; exact Hlen | constructor].
  - apply eqtm_ubeta; assumption.
Qed.

Lemma tmred_uapp_M {G Γ n l B t w ls} : lwf (n + gL G) l -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] B @ l ] ->
  length ls = n -> Forall (lwf (gL G)) ls ->
  [ G ; Γ ⊢[ lM ] t ⤳* w : tyUPi n l B @ lomega ] ->
  [ G ; Γ ⊢[ lM ] uapp t ls ⤳* uapp w ls : B[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros Hl HB Hlen Hls [Ht Hr He]. constructor.
  - eapply wf_uapp; eassumption.
  - apply reds_uapp, Hr.
  - eapply eqtm_uapp; [eassumption .. | apply lequivs_refl, Hls | exact He].
Qed.

(** η's body: [Λ ℓ⃗. b], weakened and applied to the bound variables, is [b]. *)
Lemma tmred_ueta_M {G Γ n l B b} : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lwf (n + gL G) l ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] B @ l ] -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] b : B @ l ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] uapp (ulam n l b)⟨ush n⟩ᵤ (ubvars n) ⤳* b : B @ l ].
Proof.
  intros HΓ Hn Hl HB Hb.
  assert (Hl2 : lwf (n + gL (gctx_uwk n G)) (lvren l (uuprn n (ush n))))
    by exact (lwf_lvren _ _ _ _ (uwk_under_ok n (gL G)) Hl).
  pose proof (tmred_ubeta_M (uwk_ctx n HΓ) Hn Hl2 (uwk_under_ty n HB) (uwk_under_tm n Hb)
                (ubvars_length n) (lwfs_ubvars n _)) as X.
  rewrite (ueta_tm n b (wf_tm_dnf Hb)), (ueta_ty n B (wf_ty_dnf HB)), ueta_lvl in X. exact X.
Qed.

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

Lemma ktm_ulam {G Γ} (ρ : kwk G Γ) n l b : ktm ρ (ulam n l b) = ulam n l (ktm ρ b).
Proof. unfold ktm; destruct (kw_γ ρ); reflexivity. Qed.

(** A world under [n] fresh levels: the same weakenings. *)
Lemma kw_uwk_gok n {G Γ} (ρ : kwk G Γ) : gwk_ok (kw_γ ρ) (gctx_uwk n (kw_G ρ)) (gctx_uwk n G).
Proof. destruct (kw_gok ρ) as [HL Hw]. split; [cbn; lia | apply gwk_wf_uren, Hw]. Qed.
Lemma kw_uwk_wf n {G Γ} (ρ : kwk G Γ) : kw_r ρ : (kw_Δ ρ)⟨ush n⟩ᵤ ≤ (Γ⟨ush n⟩ᵤ)⟦kw_γ ρ⟧.
Proof.
  pose proof (wk_wf_usubst _ _ _ (fun j => lvar (ush n j)) (kw_wf ρ)) as X.
  rewrite usubst_gwa_ctx in X. cbn [usubst USubst_ctx] in X. rewrite <- !uren_ush_ctx in X. exact X.
Qed.
Lemma kw_uwk_ctx n {G Γ} (ρ : kwk G Γ) : [ gctx_uwk n (kw_G ρ) ; (kw_Δ ρ)⟨ush n⟩ᵤ ⊢g ].
Proof. exact (uwk_ctx n (kw_ctx ρ)). Qed.
Definition kw_uwk n {G Γ} (ρ : kwk G Γ) : kwk (gctx_uwk n G) Γ⟨ush n⟩ᵤ :=
  mkKwk (gctx_uwk n (kw_G ρ)) (kw_Δ ρ)⟨ush n⟩ᵤ (kw_γ ρ) (kw_r ρ) (kw_uwk_gok n ρ) (kw_uwk_wf n ρ)
    (kw_uwk_ctx n ρ).

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
Local Notation LRtmM := (@LRtm EM LRM).
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

(** ** [Λ] and its congruence *)

Section Lam.
Variables (l l' : lvl) (T : ty) (t t' : tm).
Hypothesis (Hl : lequiv (n + gL G0) l l')
  (VT : forall L'' ψ, usub_ok ψ L'' (n + gL G0) ->
     VTySM (G_us Gu L'' ψ) (ucsubst Γu ψ) T[ψ]ᵤ T[ψ]ᵤ (lvsubst l ψ))
  (Vt : forall L'' ψ, usub_ok ψ L'' (n + gL G0) ->
     VTmSM (G_us Gu L'' ψ) (ucsubst Γu ψ) t[ψ]ᵤ t'[ψ]ᵤ T[ψ]ᵤ (lvsubst l ψ)).

Lemma VS_ulam : VTmSωM Gφ Γφ (ulam n (lvsubst l (uupn n φ)) t[uupn n φ]ᵤ)
  (ulam n (lvsubst l' (uupn n φ)) t'[uupn n φ]ᵤ) (tyUPi n (lvsubst l (uupn n φ)) T[uupn n φ]ᵤ).
Proof.
  pose proof (lequiv_refl _ _ (lequiv_wf_l _ _ _ Hl)) as Hll0.
  apply VTmSω_intro_loc. intros G' σ σ' Hσ Δ d d' Hd.
  pose proof (GSubRel_refl_l _ _ Hσ) as Hσσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ Hd) as [Nd Nd'].
  set (lφ := lvsubst l (uupn n φ)). set (lφ' := lvsubst l' (uupn n φ)).
  set (A := Aσ T σ d). set (Ar := Aσ T σ d'). set (b := bσ t σ d). set (b' := bσ t' σ' d').
  pose proof (u_φn _ _ _ Hσ) as Hφn.
  assert (Hll : lequiv (n + gL G') lφ lφ') by exact (lequiv_lvsubst _ _ _ _ _ Hφn Hl).
  pose proof (lequiv_wf_l _ _ _ Hll) as Wlφ.
  pose proof (u_Δ _ _ _ _ _ Hd) as HΔ.
  (* the types and the bodies at the extended scope *)
  destruct (upi_esc l T T VT G' σ σ Δ d d' Hσσ Hd) as [R0 H0].
  destruct (escape_ty _ _ _ _ _ _ _ _ H0) as (HA & HAr & HAAr).
  rewrite (@gm_layer_M EP EM EMl) in HA, HAr.
  assert (Hbody : LRtmM lφ (gctx_uwk n G') Δ⟨ush n⟩ᵤ A Ar b b').
  { pose proof (Vt (n + L') (uupn n φ) (usub_ok_uupn _ _ _ _ Hφ)) as X.
    unfold G_us in X. rewrite gctx_uwk_usubst, ucren_ush_usubst in X.
    exact (VTmG_loc (X _ _ _ (u_σn _ _ _ Hσ)) _ _ _ (u_dn _ _ _ _ _ _ Hσ Hd)). }
  destruct Hbody as (Rb & HRb & Hbb).
  destruct (escape_tm _ _ _ _ _ _ _ _ HRb _ _ Hbb) as (Hb & Hb' & Ebb).
  rewrite (@gm_layer_M EP EM EMl) in Hb, Hb'.
  pose proof (geq_ty_sound HAAr) as DAAr. rewrite (@gm_layer_M EP EM EMl) in DAAr.
  assert (DU : [ G' ; Δ ⊢[ lM ] tyUPi n lφ A ≅ tyUPi n lφ Ar @ lomega ])
    by (apply eqty_upi; [exact HΔ | exact Hn | exact (lequiv_refl _ _ Wlφ) | exact HA | exact DAAr]).
  assert (Hw : [ G' ; Δ ⊢[ lM ] ulam n lφ b : tyUPi n lφ A @ lomega ])
    by (apply wf_ulam; [exact HΔ | exact Hn | exact Wlφ | exact HA | exact Hb]).
  assert (Hw'A : [ G' ; Δ ⊢[ lM ] ulam n lφ' b' : tyUPi n lφ A @ lomega ])
    by (eapply pre_ulam_r; [exact HΔ | exact Hn | exact Hll | exact HA | exact Hb']).
  assert (Hw'Ar : [ G' ; Δ ⊢[ lM ] ulam n lφ' b' : tyUPi n lφ Ar @ lomega ])
    by (eapply wf_conv; [exact Hw'A | apply eqty_sym, DU]).
  (* the relation of the [UΠ]s, at the canonical instances *)
  pose proof (upi_LR l l T T Hll0 VT G' σ σ Δ d d' Hσσ Hd) as HLR.
  (* extensionality: both sides β-reduce to their bodies at the bound variables *)
  assert (E1 : [ G' ; Δ ⊢ ulam n lφ b ≈ ulam n lφ' b' : tyUPi n lφ A @ lomega ]).
  { apply geq_tm_uext; [exact Hn | exact Wlφ | exact HA | exact Hw | exact Hw'A |].
    eapply geq_tm_exp; [| | exact Ebb]; rewrite (@gm_layer_M EP EM EMl).
    - exact (tmred_ueta_M HΔ Hn Wlφ HA Hb).
    - eapply tmred_lconv; [| exact Hll].
      eapply tmred_ueta_M; [exact HΔ | exact Hn | exact (lequiv_wf_r _ _ _ Hll) | |].
      + eapply wft_lconv; [exact HA | apply lequiv_sym, Hll].
      + eapply wf_lconv; [exact Hb' | apply lequiv_sym, Hll]. }
  eexists; split; [exact HLR |].
  exists (ulam n lφ b), (ulam n lφ' b').
  refine (conj _ (conj _ (conj (whnf_ulam _ _ _) (conj (whnf_ulam _ _ _) (conj E1 (conj _ _)))))).
  - rewrite (@gm_layer_M EP EM EMl). apply tmred_refl, Hw.
  - rewrite (@gm_layer_M EP EM EMl). apply tmred_refl, Hw'Ar.
  - eapply geq_tm_conv; [exact E1 |]. rewrite (@gm_layer_M EP EM EMl). exact DU.
  - (* the instances: the bodies at [uext ls φ], anti-reduced *)
    intros ρ ls ls' Hlen Hls.
    pose proof (lequivs_lwf_l _ _ _ Hls) as Wls. pose proof (lequivs_lwf_r _ _ _ Hls) as Wls'.
    assert (Hlen' : length ls' = n) by (rewrite <- (Forall2_length Hls); exact Hlen).
    pose proof (u_ψ _ _ _ _ Hσ ρ ls Hlen Wls) as Hψ.
    pose proof (u_ψ _ _ _ _ Hσ ρ ls' Hlen' Wls') as Hψ'.
    pose proof (Vt _ _ Hψ) as X. rewrite (G_us_uwk_uext_φ n _ _ ls φ Hlen), (ctx_uwk_uext_φ n _ ls φ Hlen) in X.
    pose proof (VTmG_loc (X _ _ _ (u_σρ _ _ _ _ Hσ ρ)) _ _ _ (u_dρ _ _ _ _ _ Hd ρ)) as Y.
    pose proof (Vt _ _ Hψ') as X'. rewrite (G_us_uwk_uext_φ n _ _ ls' φ Hlen'), (ctx_uwk_uext_φ n _ ls' φ Hlen') in X'.
    pose proof (VTmG_loc (X' _ _ _ (u_σρ _ _ _ _ Hσ ρ)) _ _ _ (u_dρ _ _ _ _ _ Hd ρ)) as Y2.
    pose proof (LRtm_trans (LRtm_sym Y2) Y2) as Y'.
    (* the types' instances, from the relation of the [UΠ]s *)
    pose proof (upi_inst l l T T Hll0 VT G' σ σ Δ d d' Hσσ Hd ρ ls ls' Hlen Hls) as HI.
    assert (Z0 : LRtyM (lvsubst lφ (uext ls lvar)) (kw_G ρ) (kw_Δ ρ) (kty ρ A)[uext ls lvar]ᵤ (kty ρ Ar)[uext ls' lvar]ᵤ)
      by (eexists; exact HI).
    unfold A, Ar, Aσ, lφ in Z0.
    rewrite (upi_inst_ty n ls φ T σ d ρ Hlen Nσ Nd), (upi_inst_ty n ls' φ T σ d' ρ Hlen' Nσ Nd'),
      (uupn_uext_l n ls φ l Hlen) in Z0.
    assert (El : lequiv (gL (kw_G ρ)) (lvsubst l (uext ls φ)) (lvsubst l (uext ls' φ)))
      by exact (lequiv_ilvφ (usub_ok_grow Hφ (Nat.le_trans _ _ _ (u_L _ _ _ Hσ) (kw_gL ρ)))
                  (lequiv_refl _ _ (lequiv_wf_l _ _ _ Hl)) Hlen Hls).
    assert (Ex : tm_leq t'[uext ls φ]ᵤ⦃gsub_wk σ' (kw_γ ρ)⦄[kwsub ρ d'] t'[uext ls' φ]ᵤ⦃gsub_wk σ' (kw_γ ρ)⦄[kwsub ρ d']).
    { apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl |].
      apply (proj1 (proj2 leq_gsubst_all)); [intros; apply gobj_leq_refl |].
      apply (proj1 (proj2 leq_usubst_all)); [apply leqv_uext, (lequivs_leqv _ _ _ Hls) | apply tm_leq_refl]. }
    pose proof (LRtm_leq (LRtm_irrel_r Y Z0) (LRtm_lconv Y' El) Ex) as Z.
    rewrite <- (upi_inst_ty n ls φ T σ d ρ Hlen Nσ Nd), <- (upi_inst_ty n ls' φ T σ d' ρ Hlen' Nσ Nd'),
      <- (upi_inst_tm n ls φ t σ d ρ Hlen Nσ Nd), <- (upi_inst_tm n ls' φ t' σ' d' ρ Hlen' Nσ' Nd'),
      <- (uupn_uext_l n ls φ l Hlen) in Z.
    destruct Z as (R' & HR' & Hrel).
    exists R'. split; [exact HR' |].
    fold lφ in HR', Hrel |- *.
    (* the applications reduce to the instances *)
    pose proof (kw_ctx ρ) as HΔρ. rewrite (@gm_layer_M EP EM EMl) in HΔρ.
    assert (Wlρ : lwf (n + gL (kw_G ρ)) lφ) by (eapply lwf_weaken; [| exact Wlφ]; pose proof (kw_gL ρ); lia).
    assert (Wlρ' : lwf (n + gL (kw_G ρ)) lφ') by (eapply lwf_weaken; [| exact (lequiv_wf_r _ _ _ Hll)]; pose proof (kw_gL ρ); lia).
    pose proof (kw_ty (kw_uwk n ρ) (ltac:(rewrite (@gm_layer_M EP EM EMl); exact HA))) as HAρ.
    pose proof (kw_tm (kw_uwk n ρ) (ltac:(rewrite (@gm_layer_M EP EM EMl); exact Hb))) as Hbρ.
    assert (Hb'r : [ gctx_uwk n G' ; Δ⟨ush n⟩ᵤ ⊢[ lM ] b' : Ar @ lφ' ]).
    { eapply wf_lconv; [| apply lequiv_sym, Hll]. eapply wf_conv; [exact Hb' | apply eqty_sym, DAAr]. }
    assert (HArl : [ gctx_uwk n G' ; Δ⟨ush n⟩ᵤ ⊢[ lM ] Ar @ lφ' ])
      by (eapply wft_lconv; [exact HAr | apply lequiv_sym, Hll]).
    pose proof (kw_ty (kw_uwk n ρ) (ltac:(rewrite (@gm_layer_M EP EM EMl); exact HArl))) as HArρ.
    pose proof (kw_tm (kw_uwk n ρ) (ltac:(rewrite (@gm_layer_M EP EM EMl); exact Hb'r))) as Hb'ρ.
    rewrite (@gm_layer_M EP EM EMl) in HAρ, Hbρ, HArρ, Hb'ρ.
    eapply (LR_red_tm _ _ _ _ _ _ _ _ HR' _ _ _ _ Hrel); rewrite (@gm_layer_M EP EM EMl), ktm_ulam.
    + exact (tmred_ubeta_M HΔρ Hn Wlρ HAρ Hbρ Hlen Wls).
    + eapply tmred_lconv; [exact (tmred_ubeta_M HΔρ Hn Wlρ' HArρ Hb'ρ Hlen' Wls') |].
      exact (lequiv_ilv (kw_gL ρ) Hll Hlen Hls).
Qed.

End Lam.

(** ** [$] and its congruence: the function's relation at the identity
    world, anti-reduced *)

Lemma tyred_upi_inv {G Γ i m l0 A m2 l2 A2 k} :
  [ G ; Γ ⊢[ i ] tyUPi m l0 A ⤳* tyUPi m2 l2 A2 @ k ] -> m2 = m /\ l2 = l0 /\ A2 = A.
Proof.
  intros H. pose proof (tyred_red _ _ _ _ _ _ H) as Hr.
  inversion Hr as [| y z Hy Hz]; subst.
  - auto.
  - exfalso. exact (whnf_ty_no_red _ _ (whnf_tyUPi _ _ _) Hy).
Qed.

Section App.
Variables (l : lvl) (T : ty) (u u' : tm) (ks ks' : list lvl).
Hypothesis (VT : forall L'' ψ, usub_ok ψ L'' (n + gL G0) ->
     VTySM (G_us Gu L'' ψ) (ucsubst Γu ψ) T[ψ]ᵤ T[ψ]ᵤ (lvsubst l ψ))
  (Vu : VTmSωM Gφ Γφ u u' (tyUPi n (lvsubst l (uupn n φ)) T[uupn n φ]ᵤ))
  (Hks : length ks = n) (Hkk : Forall2 (lequiv L') ks ks').

Lemma VS_uapp : VTmSM Gφ Γφ (uapp u ks) (uapp u' ks') T[uupn n φ]ᵤ[uext ks lvar]ᵤ
  (lvsubst (lvsubst l (uupn n φ)) (uext ks lvar)).
Proof.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Δ d d' Hd.
  pose proof (GSubRel_refl_l _ _ Hσ) as Hσσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  destruct (SubRel_dnf _ _ _ _ _ Hd) as [Nd Nd'].
  set (lφ := lvsubst l (uupn n φ)).
  pose proof (Vu _ _ _ Hσ G' gwk_id (gwk_ok_id G') Δ d d' Hd) as X. cbn [gwa] in X.
  destruct X as (R & HLR & Hrel).
  destruct HLR as [n2 l0 l0' A0 A0' iR Hn2 Hl02 HT HT' HTT HI HR].
  destruct (tyred_upi_inv HT) as (-> & -> & ->). destruct (tyred_upi_inv HT') as (_ & -> & ->).
  apply HR in Hrel. destruct Hrel as (w & w' & Hw & Hw' & Nw & Nw' & Ew & Ew' & K).
  (* the bodies' types, at the extended scope *)
  destruct (upi_esc l T T VT G' σ σ Δ d d' Hσσ Hd) as [R0 H0].
  destruct (escape_ty _ _ _ _ _ _ _ _ H0) as (HA & HAr & _).
  rewrite (@gm_layer_M EP EM EMl) in HA, HAr.
  assert (Wlφ : lwf (n + gL G') lφ).
  { pose proof (lequiv_wf_l _ _ _ Hl02) as W. exact W. }
  pose proof (SubRel_ctx Hd) as HΔg.
  assert (Hks' : length ks' = n) by (rewrite <- (Forall2_length Hkk); exact Hks).
  assert (Hkk' : Forall2 (lequiv (gL G')) ks ks')
    by exact (lequivs_weaken _ _ _ _ (u_L _ _ _ Hσ) Hkk).
  pose proof (lequivs_lwf_l _ _ _ Hkk') as Wks. pose proof (lequivs_lwf_r _ _ _ Hkk') as Wks'.
  set (ρ0 := kw_loc wk_id (wkwf_id Δ) HΔg).
  pose proof (K ρ0 ks ks' Hks Hkk') as Kk.
  pose proof (HI ρ0 ks ks' Hks Hkk') as HIk.
  pose proof (HI ρ0 ks ks Hks (lequivs_refl _ _ Wks)) as HIr.
  assert (NA : nfty (Aσ T σ d)) by exact (wf_ty_nf HA).
  assert (NAr : nfty (Aσ T σ d')) by exact (wf_ty_nf HAr).
  assert (NW : nftm w)
    by (eapply wf_tm_nf, eqtm_wf_r; [apply ge_typeof | apply tmred_eq; eassumption]).
  assert (NW' : nftm w')
    by (eapply wf_tm_nf, eqtm_wf_r; [apply ge_typeof | apply tmred_eq; eassumption]).
  unfold ρ0, kty, ktm, kw_loc in Kk, HIk, HIr; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in Kk, HIk, HIr.
  rewrite !ren_id_ty in HIk, HIr by first [exact NA | exact NAr].
  rewrite !ren_id_tm in Kk by first [exact NW | exact NW'].
  (* the applications reduce to the whnfs' *)
  assert (Hr1 : [ G' ; Δ ⊢g uapp u⦃σ⦄[d] ks ⤳* uapp w ks : (Aσ T σ d)[uext ks lvar]ᵤ @ lvsubst lφ (uext ks lvar) ]).
  { rewrite (@gm_layer_M EP EM EMl) in Hw |- *. exact (tmred_uapp_M Wlφ HA Hks Wks Hw). }
  assert (Hr2 : [ G' ; Δ ⊢g uapp u'⦃σ'⦄[d'] ks' ⤳* uapp w' ks' : (Aσ T σ d')[uext ks' lvar]ᵤ @ lvsubst lφ (uext ks lvar) ]).
  { rewrite (@gm_layer_M EP EM EMl) in Hw' |- *. eapply tmred_lconv; [exact (tmred_uapp_M Wlφ HAr Hks' Wks' Hw') |].
    exact (lequiv_ilv (kw_gL ρ0) (lequiv_refl _ _ Wlφ) Hks Hkk'). }
  pose proof (LR_red_tm _ _ _ _ _ _ _ _ HIk _ _ _ _ Kk Hr1 Hr2) as Z.
  unfold Aσ in *.
  rewrite (gsubst_uinst_ty n ks _ σ Hks Nσ), (subst_uinst_ty n ks _ d Hks Nd),
    (subst_uinst_ty n ks _ d' Hks Nd').
  change ((uapp u ks)⦃σ⦄[d]) with (uapp u⦃σ⦄[d] ks). change ((uapp u' ks')⦃σ'⦄[d']) with (uapp u'⦃σ'⦄[d'] ks').
  eapply LRtm_irrel_r; [exists (iR ρ0 ks ks'); split; [exact HIk | exact Z] | eexists; exact HIr].
Qed.

End App.

(** ** β: the application of [Λ] reduces to the body's instance *)

Lemma red_ubeta_inst n0 l0 b ks σ e : length ks = n0 -> gdnf σ -> LK dnftm e ->
  red (uapp (ulam n0 l0 b) ks)⦃σ⦄[e] b[uext ks lvar]ᵤ⦃σ⦄[e].
Proof.
  intros Hn0 Hσ He. rewrite (gsubst_uinst_tm n0 ks b σ Hn0 Hσ), (subst_uinst_tm n0 ks _ e Hn0 He).
  exact (red_ubeta _ _ _ _ Hn0).
Qed.

Lemma VS_red {G Γ lhs rhs T k} : [ G ; Γ ⊢[ lM ] lhs : T @ k ] -> [ G ; Γ ⊢[ lM ] lhs ≅ rhs : T @ k ] ->
  (forall σ e, gdnf σ -> LK dnftm e -> red lhs⦃σ⦄[e] rhs⦃σ⦄[e]) -> VTmSM G Γ rhs rhs T k ->
  VTmSM G Γ lhs rhs T k.
Proof.
  intros Hw Heq Hred Vr.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  pose proof (Vr _ _ _ Hσ _ _ (gwk_ok_id G') _ _ _ He) as Y; cbn [gwa] in Y.
  eapply LRtm_red_l; [exact Y |]. rewrite (@gm_layer_M EP EM EMl).
  split; [exact X | econstructor; [apply Hred; assumption | constructor] |].
  exact (eqtm_subst (i := lM) eq_refl (gs_eqtm EP EM Hσ Heq) Hew).
Qed.

End UPi.
