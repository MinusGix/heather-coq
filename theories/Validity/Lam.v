(** * Validity of λ-abstraction *)
From DeLaM.Validity Require Export App.

Section Lam.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

Lemma subst_lift_ren_single_tm (b : tm) d (ρ : rsub) a :
  b[llift d]⟨rlift ρ⟩[lsingle a] = b[lcons (lren d ρ) a].
Proof.
  rewrite subst_ren_lren, (subst_subst _ _ _ (lcons (lren d ρ) a)); [reflexivity|].
  intros [|n]; rewrite llk_lren, llk_llift; cbn; [reflexivity|].
  change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift_lift, shift_single by apply ren_nf.
  now rewrite llk_lren.
Qed.

Lemma wf_tm_wkr {G Γ Δ r t T l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g t : T @ l ] -> [ G ; Δ ⊢g t⟨r⟩ : T⟨r⟩ @ l ].
Proof. intros; eapply weakening_r; eauto using ge_typeof. Qed.
Lemma eqty_wkr {G Γ Δ r T T' l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T ≅ T' @ l ] -> [ G ; Δ ⊢g T⟨r⟩ ≅ T'⟨r⟩ @ l ].
Proof. intros; eapply weakening_r; eauto using ge_typeof. Qed.

Section LamV.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B : ty} {t t' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (Ht : [ G ; Γ ,, A @ l ⊢g t : B @ l' ]) (Ht' : [ G ; Γ ,, A @ l ⊢g t' : B @ l' ])
  (VA : VTy G Γ A A' l) (VB : VTy G (Γ ,, A @ l) B B l')
  (Vt : VTm G (Γ ,, A @ l) t t' B l').

Lemma V_lam : VTm G Γ (lam l l' A t) (lam l3 l4 A' t') (tyPi l l' A B) (lmax l l').
Proof.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (VTy_refl_l VA) as VAA.
  pose proof (LR_pi_here Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB HB VAA VB
                _ _ _ Hd) as HP.
  eapply LRtm_of; [exact HP|]. push_subst.
  (* escapes *)
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd' & HAA).
  destruct (VAA _ _ _ Hd) as [RA0 HRA0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA0) as (_ & HAd' & HAdd').
  destruct (VA _ _ _ (SubRel_refl_r Hd)) as [RA2 HRA2].
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
  pose proof (wf_tm_subst ge_typeof Ht' Hld') as Ht'd'.
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact VAA | exact HAd | exact Hwl]).
  assert (Hliftd : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
    by (apply SubRel_lift; [exact (SubRel_refl_l Hd) | exact VAA | exact HAd | exact Hwl]).
  destruct (VB _ _ _ Hlift) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (_ & _ & HBdd').
  destruct (VB _ _ _ Hliftd) as [RB0 HRB0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB0) as (_ & _ & HBdd).
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
  assert (K : forall Δ' (ρ : wk) (Hρ : ρ : Δ' ≤ Δ) (HΔ' : [ G ; Δ' ⊢g ]) a a'
            (ha : @piDom E G l l' A A Δ d d' Δ' ρ Hρ HΔ' a a') la lb la' lb' A1 B1 A1' B1',
            lequiv (gL G) la l -> lequiv (gL G) lb l' ->
            lequiv (gL G) la' l -> lequiv (gL G) lb' l' ->
            [ G ; Δ' ⊢ A[d]⟨ρ⟩ ≈ A1 @ l ] -> [ G ; Δ' ,, A[d]⟨ρ⟩ @ l ⊢ B[llift d]⟨rlift ρ⟩ ≈ B1 @ l' ] ->
            [ G ; Δ' ⊢ A[d']⟨ρ⟩ ≈ A1' @ l ] -> [ G ; Δ' ,, A[d']⟨ρ⟩ @ l ⊢ B[llift d']⟨rlift ρ⟩ ≈ B1' @ l' ] ->
            @piCod E G l l' A A B B Δ d d' Δ' ρ Hρ HΔ' a a' ha
              (app (lam l l' A[d] t[llift d])⟨ρ⟩ la lb A1 B1 a)
              (app (lam l3 l4 A'[d'] t'[llift d'])⟨ρ⟩ la' lb' A1' B1' a')).
  { intros Δ' ρ Hρ HΔ' a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    unfold piDom in ha. unfold piCod. push_ren.
    assert (Ha0 : LRtm l G Δ' A[d]⟨ρ⟩ A[d']⟨ρ⟩ a a')
      by (apply (LRtm_stage (n := lmeasure (lmax l l'))); [rewrite lmeasure_max; lia | exact ha]).
    destruct (LRtm_escape Ha0) as [Haρ Ha'ρ].
    assert (Ha1 := Ha0). rewrite !subst_ren_lren_ty in Ha1.
    pose proof (Vt _ _ _ (SubRel_cons (SubRel_wk _ _ _ _ _ _ _ Hρ HΔ' Hd) Ha1)) as X.
    rewrite <- !subst_lift_ren_single, <- !subst_lift_ren_single_tm in X.
    apply (LRtm_stage (n := lmeasure (lmax l l'))) in X; [|rewrite lmeasure_max; lia].
    destruct X as (R & HR & HX). exists R; split; [exact HR|].
    pose proof (wk_wf_wkr _ _ _ Hρ) as Hr.
    assert (HAdρ : [ G ; Δ' ⊢g A[d]⟨ρ⟩ @ l ]) by exact (wf_ty_wk Hρ HΔ' HAd).
    assert (HA'3ρ : [ G ; Δ' ⊢g A'[d']⟨ρ⟩ @ l3 ]) by exact (wf_ty_wk Hρ HΔ' HA'3).
    assert (HΔ'A : [ G ; Δ' ,, A[d]⟨ρ⟩ @ l ⊢g ]) by now apply ext_wf_g.
    assert (HΔ'A'3 : [ G ; Δ' ,, A'[d']⟨ρ⟩ @ l3 ⊢g ]) by (apply ext_wf_g; eauto using lequiv_wf_l).
    eapply LR_red_tm; [exact HR | exact HX | |].
    - apply tmred_beta; auto.
      + exact (wf_ty_wkr (wkr_lift Hρ) HΔ'A HBd).
      + exact (wf_tm_wkr (wkr_lift Hρ) HΔ'A Htd).
      + now apply geq_ty_sound.
      + now apply geq_ty_sound.
    - eapply (tmred_lconv _ _ _ _ l4); [|now apply lequiv_sym].
      apply tmred_beta; eauto using lequiv_wf_l.
      + eapply lequiv_trans; [exact Hla' | now apply lequiv_sym].
      + eapply lequiv_trans; [exact Hlb' | now apply lequiv_sym].
      + exact (wf_ty_wkr (wkr_lift Hρ) HΔ'A'3 HB3).
      + exact (wf_tm_wkr (wkr_lift Hρ) HΔ'A'3 Ht'3).
      + eapply (wf_lconv _ _ _ _ _ _ l); [|exact H3].
        eapply wf_conv; [exact Ha'ρ | rewrite ge_typeof].
        apply eqty_sym. exact (eqty_wkr Hr HΔ' (geq_ty_sound HAA)).
      + eapply (eqty_lconv _ _ _ _ _ _ l); [|exact H3].
        eapply eqty_trans; [apply eqty_sym, (eqty_wkr Hr HΔ' HAA's) | now apply geq_ty_sound].
      + eapply (eqty_lconv _ _ _ _ _ _ l'); [|exact H4].
        eapply (stab_eqty ge_typeof (eqty_wkr Hr HΔ' HAA's) (lequiv_sym _ _ _ H3) HΔ'A'3).
        now apply geq_ty_sound. }
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
  pose proof (K _ wk1 Hw1 HΔA (var 0) (var 0) ha0 l l' l l'
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
    - unfold piCod in K1. change (wk_ren wk1) with ↑ in K1.
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
