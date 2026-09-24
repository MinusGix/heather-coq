(** * Validity of Π types *)
From DeLaM.Validity Require Export Basic.

Section Pi.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Syntax *)

Lemma subst_lift_ren_single (B : ty) d (ρ : rsub) a :
  B[llift d]⟨rlift ρ⟩[lsingle a] = B[lcons (lren d ρ) a].
Proof.
  rewrite subst_ren_lren_ty, (subst_subst_ty _ _ _ (lcons (lren d ρ) a)); [reflexivity|].
  intros [|n]; rewrite llk_lren, llk_llift; cbn; [reflexivity|].
  change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift_lift, shift_single by apply ren_nf.
  now rewrite llk_lren.
Qed.

Lemma ktyl_subst_single {G Δ} (ρ : kwk G Δ) (B : ty) d a :
  (ktyl ρ B[llift d])[lsingle a] = B⟦kw_γ ρ⟧[lcons (kwsub ρ d) a].
Proof.
  unfold ktyl. rewrite gwa_subst_ty.
  rewrite (subst_ext_ty _ (llift d)⟦kw_γ ρ⟧ (llift d⟦kw_γ ρ⟧)).
  - apply subst_lift_ren_single.
  - intros [|n]; rewrite llk_gwa, !llk_llift; [now rewrite gwa_var|].
    change (ren_tm ?x ?r) with x⟨r⟩. now rewrite gwa_ren, llk_gwa.
Qed.

(** ** Stages *)

Lemma LogRel_up {l k G Γ T T' R} :
  lmeasure l <= k -> LogRel l G Γ T T' l R -> LR k (LRbelow k) G Γ T T' l R.
Proof. intros Hk H. now apply (LogRel_stage k) in H. Qed.

(** ** Π types *)

Section PiTy.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' : ty}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HA : [ G ; Γ ⊢g A @ l ]) (HA' : [ G ; Γ ⊢g A' @ l ])
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ]) (HB' : [ G ; Γ ,, A' @ l ⊢g B' @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l').

Let N := lmeasure (lmax l l').

Definition piDom Δ d d' : DomRel G Δ :=
  fun ρ => LRrel N (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']) l.
Definition piCod Δ d d' : CodRel G Δ (piDom Δ d d') :=
  fun ρ a a' _ => LRrel N (kw_G ρ) (kw_Δ ρ) (ktyl ρ B[llift d])[lsingle a]
                    (ktyl ρ B'[llift d'])[lsingle a'] l'.

Lemma N_l : lmeasure l <= N.
Proof. unfold N; rewrite lmeasure_max; lia. Qed.
Lemma N_l' : lmeasure l' <= N.
Proof. unfold N; rewrite lmeasure_max; lia. Qed.

Lemma LR_pi_here Δ d d' : SubRel G Γ Δ d d' ->
  LogRel (lmax l l') G Δ (tyPi l l' A B)[d] (tyPi l3 l4 A' B')[d'] (lmax l l')
    (PiRel G Δ l l' l3 l4 A[d] B[llift d] A'[d'] B'[llift d'] (piDom Δ d d') (piCod Δ d d')).
Proof.
  intros Hd. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Hwd. pose proof (SubRel_wf_r Hd) as Hwd'.
  destruct (VTyG_loc VA _ _ _ Hd) as [RA HRA].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd & HAA).
  assert (HΔA : [ G ; Δ ,, A[d] @ l ⊢g ]) by now apply ext_wf_g.
  assert (HΔA' : [ G ; Δ ,, A'[d'] @ l ⊢g ]) by now apply ext_wf_g.
  assert (HBd : [ G ; Δ ,, A[d] @ l ⊢g B[llift d] @ l' ])
    by (eapply (wf_ty_subst ge_typeof HB); now apply (lsub_wf_lift _ _ ge_typeof)).
  assert (HB'd : [ G ; Δ ,, A'[d'] @ l ⊢g B'[llift d'] @ l' ])
    by (eapply (wf_ty_subst ge_typeof HB'); now apply (lsub_wf_lift _ _ ge_typeof)).
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact (VTy_refl_l (VTyG_loc VA)) | exact HAd | exact Hwl]).
  destruct (VTyG_loc VB _ _ _ Hlift) as [RB HRB].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (_ & _ & HBB).
  assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l l')) by now apply lequiv_max.
  push_subst.
  eapply (LRpi N (LRbelow N) G Δ _ _ (lmax l l') l l' l3 l4 A[d] B[llift d] A'[d'] B'[llift d']
            (piDom Δ d d') (piCod Δ d d')).
  - apply lequiv_refl; cbn; auto.
  - exact H3.
  - exact H4.
  - exact Hwl.
  - exact Hwl'.
  - apply tyred_refl, wft_pi; auto using ge_notV.
  - apply tyred_refl. eapply wft_lconv; [|apply lequiv_sym, Hm].
    apply wft_pi; [exact ge_notV | eauto using lequiv_wf_l | eauto using lequiv_wf_l | |].
    + eapply lconv_ty; [exact HA'd | now apply lequiv_sym].
    + eapply (lconv_ty (l := l')); [|now apply lequiv_sym].
      eapply ctx_lvl_ty; [exact HA'd | now apply lequiv_sym | exact HB'd].
  - exact HAd.
  - exact HA'd.
  - exact HBd.
  - exact HB'd.
  - exact HAA.
  - exact HBB.
  - intros ρ. unfold piDom.
    destruct (VTyG_kw ρ VA Hd) as [R HR].
    exact (LR_canon _ _ _ _ _ _ _ (LogRel_up N_l HR)).
  - intros ρ a a' ha. unfold piCod.
    pose proof (SubRel_kw _ _ _ ρ _ _ Hd) as Hdρ.
    assert (Ha : LRtm l (kw_G ρ) (kw_Δ ρ) A⟦kw_γ ρ⟧[kwsub ρ d] A⟦kw_γ ρ⟧[kwsub ρ d'] a a').
    { unfold piDom in ha. apply (LRtm_stage N_l) in ha. rewrite !kty_subst in ha.
      eapply LRtm_irrel_r; [exact ha|].
      exact (VTy_refl_l (VA _ _ (kw_gok ρ)) _ _ _ Hdρ). }
    pose proof (VB _ _ (kw_gok ρ)) as VBρ. rewrite gwa_cext in VBρ.
    pose proof (VBρ _ _ _ (SubRel_cons Hdρ Ha)) as [R HR].
    rewrite <- !ktyl_subst_single in HR.
    exact (LR_canon _ _ _ _ _ _ _ (LogRel_up N_l' HR)).
  - apply releq_refl.
Qed.

Lemma V_pi : VTy G Γ (tyPi l l' A B) (tyPi l3 l4 A' B') (lmax l l').
Proof. intros Δ d d' Hd. eexists. exact (LR_pi_here _ _ _ Hd). Qed.

End PiTy.

End Pi.
