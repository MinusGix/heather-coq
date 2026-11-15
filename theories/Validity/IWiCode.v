(** * Validity of the code of [IWi] (M19_DESIGN.md, M19c)

    As [IWf]'s code (IWfCode.v): the code is related at [U] to itself
    through the decoded type's relation ([LR_IWi_at]), each side reducing
    to its decoding, whose premises the code's own typing gives by
    inversion. The domains' code [d] decodes under [El s, Fin n]. *)
From DeLaM.Validity Require Export IWi.
From DeLaM.Typing Require Import Inversion.

Section IWiCode.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Lemma tyred_El_iwi {G Δ la L l lp li x s n d o c m} : lequiv (gL G) la L -> lequiv (gL G) (iwiL l lp li) L ->
  [ G ; Δ ⊢g tmIWi l lp li x s n d o c m : tyU L @ lsuc L ] ->
  [ G ; Δ ⊢g tyEl la (tmIWi l lp li x s n d o c m) ⤳* tyIWi l lp li (tyEl li x) (tyEl l s) n (tyEl lp d) o c m @ L ].
Proof.
  intros Hla Hk Hc.
  pose proof (conv_U' Hc (lequiv_sym _ _ _ Hk)) as Hc0.
  destruct (inv_code_iwi ge_typeof Hc0) as ((_ & Wl & Wlp & Wli & Hx & Hs & Hn & Hd & Ho & Hc1 & Hm) & _ & _).
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl (iwiL l lp li) (tmIWi l lp li x s n d o c m))).
  - apply eqty_El; [exact ge_notV | solve [apply lequiv_sym; assumption] | apply eqtm_refl, Hc].
  - apply (eqty_lconv _ _ _ _ _ L (iwiL l lp li)); [|solve [apply lequiv_sym; assumption]].
    apply eqty_sym, eqty_El_iwi; [exact ge_compt | exact Wl | exact Wlp | exact Wli | exact Hx | exact Hs
                                 | exact Hn | exact Hd | exact Ho | exact Hc1 | exact Hm].
Qed.

Lemma V_code_iwi {G Γ l lp li l' lp' li' x x' s s' n n' d d' o o' c c' m m'} :
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li ->
  lequiv (gL G) l l' -> lequiv (gL G) lp lp' -> lequiv (gL G) li li' ->
  VTmG G Γ x x' (tyU li) (lsuc li) -> VTmG G Γ s s' (tyU l) (lsuc l) ->
  VTmG G (Γ ,, tyEl l s @ l) n n' tyNat lzero ->
  VTmG G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero) d d' (tyU lp) (lsuc lp) ->
  VTmG G (Γ ,, tyEl l s @ l) o o' (tyEl li x⟨↑⟩) li ->
  VTmG G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero ,, tyEl lp d @ lp) c c' (tyEl li x⟨↑⟩⟨↑⟩⟨↑⟩) li ->
  VTm G Γ m m' (tyEl li x) li ->
  VTm G Γ (tmIWi l lp li x s n d o c m) (tmIWi l' lp' li' x' s' n' d' o' c' m')
    (tyU (iwiL l lp li)) (lsuc (iwiL l lp li)).
Proof.
  intros Hwl Hwlp Hwli Hl Hlp Hli Vx Vs Vn Vd Vo Vc Vm Δ e e' He.
  assert (Hwm : lwf (gL G) (iwiL l lp li)) by (cbn; repeat split; assumption).
  pose proof (V_ElG Hwli Hli Vx) as VX. pose proof (V_ElG Hwl Hl Vs) as VA.
  pose proof (V_ElG Hwlp Hlp Vd) as VD.
  pose proof (LR_IWi_at Hwl Hwlp Hwli (lequiv_sym _ _ _ Hl) (lequiv_sym _ _ _ Hlp) (lequiv_sym _ _ _ Hli)
                VX VA Vn VD Vo Vc _ _ _ _ _ He (Vm _ _ _ He)) as HR.
  pose proof (VTmG_loc Vx _ _ _ He) as Xx. pose proof (VTmG_loc Vs _ _ _ He) as Xs.
  rewrite !subst_tyU in Xx, Xs.
  destruct (VTyG_loc VA _ _ _ He) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & _ & _).
  assert (Hlift : SubRel G (Γ ,, tyEl l s @ l) (Δ ,, (tyEl l s)[e] @ l) (llift e) (llift e'))
    by exact (SubRel_lift He (VTy_refl_l (VTyG_loc VA)) HAd Hwl).
  pose proof (VTmG_loc Vn _ _ _ Hlift) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HNd _].
  pose proof (VTmG_loc Vo _ _ _ Hlift) as XO. rewrite !subst_tyEl, !shift_llift in XO.
  assert (HFd : [ G ; Δ ,, (tyEl l s)[e] @ l ⊢g (tyFin n)[llift e] @ lzero ])
    by (rewrite subst_tyFin; apply wft_fin; [exact ge_notV | exact HNd]).
  assert (Hlift2 : SubRel G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero)
                     (Δ ,, (tyEl l s)[e] @ l ,, (tyFin n)[llift e] @ lzero)
                     (llift (llift e)) (llift (llift e')))
    by exact (SubRel_lift Hlift (V_fin (VTmG_loc (VTmG_refl_l Vn))) HFd I).
  pose proof (VTmG_loc Vd _ _ _ Hlift2) as XD. rewrite !subst_tyU in XD.
  destruct (VTyG_loc VD _ _ _ Hlift2) as [RD HRD]. destruct (escape_ty _ _ _ _ _ _ _ _ HRD) as (HDd & _ & _).
  assert (Hlift3 : SubRel G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero ,, tyEl lp d @ lp)
                     (Δ ,, (tyEl l s)[e] @ l ,, (tyFin n)[llift e] @ lzero ,, (tyEl lp d)[llift (llift e)] @ lp)
                     (llift (llift (llift e))) (llift (llift (llift e'))))
    by exact (SubRel_lift Hlift2 (VTy_refl_l (VTyG_loc VD)) HDd Hwlp).
  pose proof (VTmG_loc Vc _ _ _ Hlift3) as XC. rewrite !subst_tyEl, !shift_llift in XC.
  pose proof (Vm _ _ _ He) as Xm. rewrite !subst_tyEl in Xm.
  assert (Hgeq : [ G ; Δ ⊢ tmIWi l lp li x[e] s[e] n[llift e] d[llift (llift e)] o[llift e]
                     c[llift (llift (llift e))] m[e]
                   ≈ tmIWi l' lp' li' x'[e'] s'[e'] n'[llift e'] d'[llift (llift e')] o'[llift e']
                     c'[llift (llift (llift e'))] m'[e']
                   : tyU (iwiL l lp li) @ lsuc (iwiL l lp li) ])
    by (apply geq_tm_code_iwi;
        [ exact Hl | exact Hlp | exact Hli | exact (proj1 (LRtm_escape Xx)) | exact (LRtm_geq Xx)
        | exact (proj1 (LRtm_escape Xs)) | exact (LRtm_geq Xs) | exact HNd | exact (LRtm_geq XN)
        | exact (proj1 (LRtm_escape XD)) | exact (LRtm_geq XD)
        | exact (LRtm_geq XO) | exact (LRtm_geq XC) | exact (LRtm_geq Xm) ]).
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U Hwm).
  exists (tmIWi l lp li x[e] s[e] n[llift e] d[llift (llift e)] o[llift e] c[llift (llift (llift e))] m[e]),
    (tmIWi l' lp' li' x'[e'] s'[e'] n'[llift e'] d'[llift (llift e')] o'[llift e'] c'[llift (llift (llift e'))] m'[e']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmIWi _ _ _ _ _ _ _ _ _ _) (conj (whnf_tmIWi _ _ _ _ _ _ _ _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  eexists. eapply LR_red_ty; [rewrite <- ?subst_tyEl in HR; exact HR | |]; push_subst.
  - apply tyred_El_iwi; [exact Hla | now apply lequiv_refl | exact (eqtm_wf_l ge_typeof Hgeq')].
  - apply tyred_El_iwi; [exact Hlb | apply lequiv_sym, lequiv_max; [apply lequiv_max |]; assumption
                        | exact (eqtm_wf_r ge_typeof Hgeq')].
Qed.

Lemma V_El_iwi {G Γ l lp li x s n d o c m} : lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li ->
  VTmG G Γ x x (tyU li) (lsuc li) -> VTmG G Γ s s (tyU l) (lsuc l) ->
  VTmG G (Γ ,, tyEl l s @ l) n n tyNat lzero ->
  VTmG G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero) d d (tyU lp) (lsuc lp) ->
  VTmG G (Γ ,, tyEl l s @ l) o o (tyEl li x⟨↑⟩) li ->
  VTmG G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero ,, tyEl lp d @ lp) c c (tyEl li x⟨↑⟩⟨↑⟩⟨↑⟩) li ->
  VTm G Γ m m (tyEl li x) li ->
  VTy G Γ (tyIWi l lp li (tyEl li x) (tyEl l s) n (tyEl lp d) o c m)
    (tyEl (iwiL l lp li) (tmIWi l lp li x s n d o c m)) (iwiL l lp li).
Proof.
  intros Hwl Hwlp Hwli Vx Vs Vn Vd Vo Vc Vm Δ e e' He.
  pose proof (V_ElG Hwli (lequiv_refl _ _ Hwli) Vx) as VX.
  pose proof (V_ElG Hwl (lequiv_refl _ _ Hwl) Vs) as VA.
  pose proof (V_ElG Hwlp (lequiv_refl _ _ Hwlp) Vd) as VD.
  pose proof (LR_IWi_at Hwl Hwlp Hwli (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwlp) (lequiv_refl _ _ Hwli)
                VX VA Vn VD Vo Vc _ _ _ _ _ He (Vm _ _ _ He)) as HR.
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HP & _ & _).
  pose proof (V_code_iwi Hwl Hwlp Hwli (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwlp) (lequiv_refl _ _ Hwli)
                Vx Vs Vn Vd Vo Vc Vm _ _ _ (SubRel_refl_r He)) as Xc.
  rewrite !subst_tyU in Xc.
  eexists. rewrite !subst_tyIWi. eapply LR_red_ty; [exact HR | apply tyred_refl, HP |]. push_subst.
  rewrite ?subst_tmIWi in Xc.
  apply tyred_El_iwi; [apply lequiv_refl; cbn; repeat split; assumption
                      | apply lequiv_refl; cbn; repeat split; assumption
                      | exact (proj1 (LRtm_escape Xc))].
Qed.

End IWiCode.
