(** * Validity of λ-abstraction *)
From DeLaM.Validity Require Export App.

Section Lam.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma subst_lift_ren_single_tm (b : tm) d (ρ : rsub) a :
  b[llift d]⟨rlift ρ⟩[lsingle a] = b[lcons (lren d ρ) a].
Proof.
  rewrite subst_ren_lren, (subst_subst _ _ _ (lcons (lren d ρ) a)); [reflexivity|].
  intros [|n]; rewrite llk_lren, llk_llift; cbn; [reflexivity|].
  change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift_lift, shift_single by apply ren_nf.
  now rewrite llk_lren.
Qed.

Lemma ktml_subst_single {G Δ} (ρ : kwk G Δ) (b : tm) d a :
  (ktml ρ b[llift d])[lsingle a] = b⟦kw_γ ρ⟧[lcons (kwsub ρ d) a].
Proof.
  unfold ktml. rewrite gwa_subst.
  rewrite (subst_ext _ (llift d)⟦kw_γ ρ⟧ (llift d⟦kw_γ ρ⟧)).
  - apply subst_lift_ren_single_tm.
  - intros [|n]; rewrite llk_gwa, !llk_llift; [now rewrite gwa_var|].
    change (ren_tm ?x ?r) with x⟨r⟩. now rewrite gwa_ren, llk_gwa.
Qed.

Section LamV.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B : ty} {t t' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (Ht : [ G ; Γ ,, A @ l ⊢g t : B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B l')
  (Vt : VTmG G (Γ ,, A @ l) t t' B l').

Lemma V_lam : VTm G Γ (lam l l' A t) (lam l3 l4 A' t') (tyPi l l' A B) (lmax l l').
Proof.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (LR_pi_here Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB
                (VTyG_refl_l VA) VB _ _ _ Hd) as HP.
  pose proof (VTyG_loc VA) as VAl. pose proof (VTyG_loc VB) as VBl.
  pose proof (VTy_refl_l VAl) as VAA.
  eapply LRtm_of; [exact HP|]. push_subst.
  (* escapes *)
  destruct (VAl _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd' & HAA).
  destruct (VAA _ _ _ Hd) as [RA0 HRA0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA0) as (_ & HAd' & HAdd').
  destruct (VAl _ _ _ (SubRel_refl_r Hd)) as [RA2 HRA2].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (_ & _ & HAA'2).
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Hwd. pose proof (SubRel_wf_r Hd) as Hwd'.
  assert (HΔA : [ G ; Δ ,, A[d] @ l ⊢g ]) by now apply ext_wf_g.
  assert (HΔA' : [ G ; Δ ,, A[d'] @ l ⊢g ]) by now apply ext_wf_g.
  assert (Hld : lsub_wf G ge_layer (Δ ,, A[d] @ l) (llift d) (Γ ,, A @ l))
    by now apply (lsub_wf_lift _ _ ge_typeof).
  assert (Hld' : lsub_wf G ge_layer (Δ ,, A[d'] @ l) (llift d') (Γ ,, A @ l))
    by now apply (lsub_wf_lift _ _ ge_typeof).
  pose proof (wf_ty_subst ge_typeof HB Hld) as HBd.
  pose proof (wf_ty_subst ge_typeof HB Hld') as HBd'.
  pose proof (wf_tm_subst ge_typeof Ht Hld) as Htd.
  (* the right body, by escape at the right substitution *)
  assert (Hlift' : SubRel G (Γ ,, A @ l) (Δ ,, A[d'] @ l) (llift d') (llift d'))
    by (apply SubRel_lift; [exact (SubRel_refl_r Hd) | exact VAA | exact HAd' | exact Hwl]).
  pose proof (proj2 (LRtm_escape (VTmG_loc Vt _ _ _ Hlift'))) as Ht'd'.
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact VAA | exact HAd | exact Hwl]).
  assert (Hliftd : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
    by (apply SubRel_lift; [exact (SubRel_refl_l Hd) | exact VAA | exact HAd | exact Hwl]).
  destruct (VBl _ _ _ Hlift) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (_ & _ & HBdd').
  destruct (VBl _ _ _ Hliftd) as [RB0 HRB0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB0) as (_ & _ & HBdd).
  (* the right λ at its own annotation *)
  assert (HAA's : [ G ; Δ ⊢g A[d'] ≅ A'[d'] @ l ]) by now apply geq_ty_sound.
  assert (HA'3 : [ G ; Δ ⊢g A'[d'] @ l3 ]) by (eapply lconv_ty; [exact HA'd' | now apply lequiv_sym]).
  assert (HΔA'3 : [ G ; Δ ,, A'[d'] @ l3 ⊢g ]) by (apply ext_wf_g; eauto using lequiv_wf_l).
  assert (Ht'3 : [ G ; Δ ,, A'[d'] @ l3 ⊢g t'[llift d'] : B[llift d'] @ l4 ]).
  { eapply (wf_lconv _ _ _ _ _ _ l'); [|exact H4].
    exact (stab_tm ge_typeof HAA's (lequiv_sym _ _ _ H3) HΔA'3 Ht'd'). }
  assert (HB3 : [ G ; Δ ,, A'[d'] @ l3 ⊢g B[llift d'] @ l4 ]).
  { eapply (lconv_ty (l := l')); [|now apply lequiv_sym].
    exact (stab_ty ge_typeof HAA's (lequiv_sym _ _ _ H3) HΔA'3 HBd'). }
  assert (HF : [ G ; Δ ⊢g lam l l' A[d] t[llift d] : tyPi l l' A[d] B[llift d] @ lmax l l' ])
    by (apply wf_lam; auto using ge_notV).
  assert (HPiEq' : [ G ; Δ ⊢g tyPi l l' A[d'] B[llift d'] ≅ tyPi l3 l4 A'[d'] B[llift d'] @ lmax l l' ])
    by (apply eqty_pi; auto using ge_notV, lequiv_sym, eqty_refl).
  assert (HF' : [ G ; Δ ⊢g lam l3 l4 A'[d'] t'[llift d'] : tyPi l l' A[d'] B[llift d'] @ lmax l l' ]).
  { eapply wf_conv; [|rewrite ge_typeof; exact HPiEq'].
    eapply (wf_lconv _ _ _ _ _ _ (lmax l3 l4)); [|apply lequiv_max; now apply lequiv_sym].
    apply wf_lam; eauto using ge_notV, lequiv_wf_l. }
  destruct (escape_ty _ _ _ _ _ _ _ _ HP) as (_ & _ & HPi). rewrite !subst_tyPi in HPi.
  pose proof (geq_ty_sound HPi) as HPiEq.
  (* the Kripke clause: β on both sides *)
  assert (Hw3 : lwf (gL G) l3) by exact (lequiv_wf_l _ _ _ H3).
  assert (K : forall (ρ : kwk G Δ) a a' (ha : @piDom E LP G l l' A A Δ d d' ρ a a')
            la lb la' lb' A1 B1 A1' B1',
            lequiv (gL G) la l -> lequiv (gL G) lb l' ->
            lequiv (gL G) la' l -> lequiv (gL G) lb' l' ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A[d] ≈ A1 @ l ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ A[d] @ l ⊢ ktyl ρ B[llift d] ≈ B1 @ l' ] ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A[d'] ≈ A1' @ l ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ A[d'] @ l ⊢ ktyl ρ B[llift d'] ≈ B1' @ l' ] ->
            @piCod E LP G l l' A A B B Δ d d' ρ a a' ha
              (app (ktm ρ (lam l l' A[d] t[llift d])) la lb A1 B1 a)
              (app (ktm ρ (lam l3 l4 A'[d'] t'[llift d'])) la' lb' A1' B1' a')).
  { intros ρ a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    unfold piDom in ha. unfold piCod. rewrite !ktm_lam.
    assert (Ha0 : LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A[d']) a a')
      by (apply (LRtm_stage (n := lmeasure (lmax l l'))); [rewrite lmeasure_max; lia | exact ha]).
    destruct (LRtm_escape Ha0) as [Haρ Ha'ρ].
    assert (Ha1 := Ha0). rewrite !kty_subst in Ha1.
    pose proof (Vt _ _ (kw_gok ρ)) as Vtρ. rewrite gwa_cext in Vtρ.
    pose proof (Vtρ _ _ _ (SubRel_cons (SubRel_kw _ _ _ ρ _ _ Hd) Ha1)) as X.
    rewrite <- !ktyl_subst_single, <- !ktml_subst_single in X.
    apply (LRtm_stage (n := lmeasure (lmax l l'))) in X; [|rewrite lmeasure_max; lia].
    destruct X as (R & HR & HX). exists R; split; [exact HR|].
    pose proof (kw_ty_l ρ HAd Hwl HBd) as HBdρ. pose proof (kw_tm_l ρ HAd Hwl Htd) as Htdρ.
    pose proof (kw_ty_l ρ HA'3 Hw3 HB3) as HB3ρ. pose proof (kw_tm_l ρ HA'3 Hw3 Ht'3) as Ht'3ρ.
    pose proof (kw_eqty ρ (geq_ty_sound HAA)) as HAAρ. pose proof (kw_eqty ρ HAA's) as HAA'sρ.
    pose proof (kw_ext ρ HA'3 Hw3) as HΔ'A'3. pose proof (kw_ty ρ HAd) as HAdρ. pose proof (kw_ty ρ HA'3) as HA'3ρ.
    pose proof (kw_lequiv ρ H3) as H3ρ. pose proof (kw_lequiv ρ H4) as H4ρ.
    pose proof (kw_lwf ρ Hwl) as Hwlρ. pose proof (kw_lwf ρ Hwl') as Hwl'ρ.
    apply (kw_lequiv ρ) in Hla, Hlb, Hla', Hlb'.
    eapply LR_red_tm; [exact HR | exact HX | |].
    - apply tmred_beta; auto using geq_ty_sound.
    - eapply (tmred_lconv _ _ _ _ l4); [|now apply lequiv_sym].
      apply tmred_beta; eauto using lequiv_wf_l.
      all: first
        [ solve [eapply lequiv_trans; [eassumption | now apply lequiv_sym]]
        | solve [eapply (wf_lconv _ _ _ _ _ _ l); [|exact H3ρ];
                 eapply wf_conv; [exact Ha'ρ | rewrite ge_typeof; apply eqty_sym; exact HAAρ]]
        | solve [eapply (eqty_lconv _ _ _ _ _ _ l); [|exact H3ρ];
                 eapply eqty_trans; [apply eqty_sym, HAA'sρ | now apply geq_ty_sound]]
        | solve [eapply (eqty_lconv _ _ _ _ _ _ l'); [|exact H4ρ];
                 eapply (stab_eqty ge_typeof HAA'sρ (lequiv_sym _ _ _ H3ρ) HΔ'A'3);
                 now apply geq_ty_sound] ]. }
  (* the generic equality of the two λs, by extensionality *)
  assert (Hw1 : wk1 : (Δ ,, A[d] @ l) ≤ Δ) by (constructor; constructor).
  assert (Hr1 : wkr ↑ (Δ ,, A[d] @ l) Δ) by exact (wkr_shift1 _ _ _).
  assert (ha0 : LRrel (lmeasure (lmax l l')) G (Δ ,, A[d] @ l) A[d]⟨wk1⟩ A[d']⟨wk1⟩ l (var 0) (var 0)).
  { apply (LRtm_stage (l := l)); [rewrite lmeasure_max; lia|].
    change (wk_ren wk1) with ↑. apply var0_LRtm; [|exact HΔA].
    pose proof (VAA _ _ _ (SubRel_wk _ _ _ _ _ _ _ Hw1 HΔA Hd)) as HV.
    now rewrite <- !subst_ren_lren_ty in HV. }
  assert (RAd : [ G ; Δ ⊢ A[d] ≈ A[d] @ l ])
    by (eapply geq_ty_trans; [exact HAdd' | apply geq_ty_sym, HAdd']).
  assert (HΔAA : [ G ; Δ ,, A[d] @ l ,, A[d]⟨↑⟩ @ l ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔA HAd) | exact Hwl]).
  assert (HΔAA' : [ G ; Δ ,, A[d] @ l ,, A[d']⟨↑⟩ @ l ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔA HAd') | exact Hwl]).
  pose proof (K (kw_loc wk1 Hw1 HΔA) (var 0) (var 0) ha0 l l' l l'
                A[d]⟨↑⟩ B[llift d]⟨rlift ↑⟩ A[d]⟨↑⟩ B[llift d]⟨rlift ↑⟩
                (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl')
                (geq_ty_wk Hr1 HΔA RAd)
                (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔAA HBdd)
                (geq_ty_wk Hr1 HΔA (geq_ty_sym HAdd'))) as K0.
  assert (GEQ1 : [ G ; Δ ⊢ lam l l' A[d] t[llift d] ≈ lam l3 l4 A'[d'] t'[llift d']
                     : tyPi l l' A[d] B[llift d] @ lmax l l' ]).
  { apply geq_tm_funext; [exact Hwl | exact Hwl' | exact HAd | exact HBd | exact HF
                         | eapply wf_conv; [exact HF' | rewrite ge_typeof; exact HPiEq] |].
    unshelve epose proof (K0 _) as K1.
    - eapply geq_ty_ctxconv; [| apply lequiv_refl, Hwl | exact HΔAA' |].
      + apply geq_ty_sound. exact (geq_ty_wk Hr1 HΔA HAdd').
      + apply geq_ty_sym. exact (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔAA HBdd').
    - unfold piCod, ktyl, ktm, kty, kw_loc in K1; cbn [kw_G kw_Δ kw_γ kw_r gwa] in K1.
      change (wk_ren wk1) with ↑ in K1.
      destruct K1 as (R1 & HR1 & HK1).
      destruct (escape_tm _ _ _ _ _ _ _ _ HR1 _ _ HK1) as (_ & _ & Hg).
      now rewrite liftshift_single_var_ty in Hg by exact (wf_ty_nf HBd). }
  exists (lam l l' A[d] t[llift d]), (lam l3 l4 A'[d'] t'[llift d']).
  refine (conj (tmred_refl _ _ _ HF) (conj (tmred_refl _ _ _ HF') (conj (whnf_lam _ _ _ _)
            (conj (whnf_lam _ _ _ _) (conj GEQ1 (conj _ K)))))).
  eapply geq_tm_conv; [exact GEQ1 | exact HPiEq].
Qed.

End LamV.

End Lam.
