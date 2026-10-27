(** * Validity of the codes of [DVec] and [IWf] (M17_DESIGN.md, M17c)

    As [Wf]'s and [∥·∥]'s codes: a code is related at [U] to itself
    through the decoded type's relation ([V_dvec], [LR_IWf_here]), each
    side reducing to its decoding. The decodings' reductions take the
    code's own typing and read the premises off it by inversion. *)
From DeLaM.Validity Require Export IWf.
From DeLaM.Typing Require Import Inversion.

Section IWfCode.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** [DVec] *)

Lemma tyred_El_dvec {G Δ la l k n f} : lequiv (gL G) la l -> lequiv (gL G) k l ->
  [ G ; Δ ⊢g tmDVec k n f : tyU l @ lsuc l ] ->
  [ G ; Δ ⊢g tyEl la (tmDVec k n f) ⤳* tyDVec k n (tyEl k f) @ l ].
Proof.
  intros Hla Hk Hc.
  pose proof (conv_U' Hc (lequiv_sym _ _ _ Hk)) as Hc0.
  destruct (inv_code_dvec ge_typeof Hc0) as ((_ & Wk & Hn & Hf) & _ & _).
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl k (tmDVec k n f))).
  - apply eqty_El; [exact ge_notV | solve [apply lequiv_sym; assumption] | apply eqtm_refl, Hc].
  - apply (eqty_lconv _ _ _ _ _ l k); [|solve [apply lequiv_sym; assumption]].
    apply eqty_sym, eqty_El_dvec; [exact ge_compt | exact Wk | exact Hn | exact Hf].
Qed.

Lemma V_code_dvec {G Γ l l' n n' f f'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ n n' tyNat lzero -> VTmG G (Γ ,, tyFin n @ lzero) f f' (tyU l) (lsuc l) ->
  VTm G Γ (tmDVec l n f) (tmDVec l' n' f') (tyU l) (lsuc l).
Proof.
  intros Hw Hl Vn Vf Δ d d' Hd.
  pose proof (V_ElG Hw Hl Vf) as VF.
  destruct (V_dvec Hw Hl Vn VF _ _ _ Hd) as [R HR].
  pose proof (V_fin (VTm_trans Vn (VTm_sym Vn))) as VFin.
  destruct (VFin _ _ _ Hd) as [RF HRF]. destruct (escape_ty _ _ _ _ _ _ _ _ HRF) as (HFd & _ & _).
  assert (Hlift : SubRel G (Γ ,, tyFin n @ lzero) (Δ ,, (tyFin n)[d] @ lzero) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact (VTy_refl_l VFin) | exact HFd | exact I]).
  pose proof (Vn _ _ _ Hd) as Xn. rewrite !subst_tyNat in Xn.
  pose proof (VTmG_loc Vf _ _ _ Hlift) as Xf. rewrite !subst_tyU in Xf.
  pose proof (geq_tm_code_dvec Hl (proj1 (LRtm_escape Xn)) (LRtm_geq Xn) (LRtm_geq Xf)) as Hgeq.
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U Hw).
  exists (tmDVec l n[d] f[llift d]), (tmDVec l' n'[d'] f'[llift d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmDVec _ _ _) (conj (whnf_tmDVec _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists R. eapply LR_red_ty; [exact HR | |]; push_subst.
  - apply tyred_El_dvec; [exact Hla | now apply lequiv_refl | exact (eqtm_wf_l ge_typeof Hgeq')].
  - apply tyred_El_dvec; [exact Hlb | solve [apply lequiv_sym; assumption] | exact (eqtm_wf_r ge_typeof Hgeq')].
Qed.

Lemma V_El_dvec {G Γ l n f} : lwf (gL G) l ->
  VTm G Γ n n tyNat lzero -> VTmG G (Γ ,, tyFin n @ lzero) f f (tyU l) (lsuc l) ->
  VTy G Γ (tyDVec l n (tyEl l f)) (tyEl l (tmDVec l n f)) l.
Proof.
  intros Hw Vn Vf Δ d d' Hd.
  pose proof (V_ElG Hw (lequiv_refl _ _ Hw) Vf) as VF.
  destruct (V_dvec Hw (lequiv_refl _ _ Hw) Vn VF _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HP & _ & _).
  pose proof (V_code_dvec Hw (lequiv_refl _ _ Hw) Vn Vf _ _ _ (SubRel_refl_r Hd)) as Xc.
  rewrite !subst_tyU in Xc.
  exists R. eapply LR_red_ty; [exact HR | apply tyred_refl, HP |]. push_subst.
  rewrite ?subst_tmDVec, ?subst_tmIWf in Xc.
  apply tyred_El_dvec; [now apply lequiv_refl | now apply lequiv_refl | exact (proj1 (LRtm_escape Xc))].
Qed.

(** ** [IWf] *)

Lemma tyred_El_iwf {G Δ la L l li x s n o c m} : lequiv (gL G) la L -> lequiv (gL G) (lmax l li) L ->
  [ G ; Δ ⊢g tmIWf l li x s n o c m : tyU L @ lsuc L ] ->
  [ G ; Δ ⊢g tyEl la (tmIWf l li x s n o c m) ⤳* tyIWf l li (tyEl li x) (tyEl l s) n o c m @ L ].
Proof.
  intros Hla Hk Hc.
  pose proof (conv_U' Hc (lequiv_sym _ _ _ Hk)) as Hc0.
  destruct (inv_code_iwf ge_typeof Hc0) as ((_ & Wl & Wli & Hx & Hs & Hn & Ho & Hc1 & Hm) & _ & _).
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl (lmax l li) (tmIWf l li x s n o c m))).
  - apply eqty_El; [exact ge_notV | solve [apply lequiv_sym; assumption] | apply eqtm_refl, Hc].
  - apply (eqty_lconv _ _ _ _ _ L (lmax l li)); [|solve [apply lequiv_sym; assumption]].
    apply eqty_sym, eqty_El_iwf; [exact ge_compt | exact Wl | exact Wli | exact Hx | exact Hs
                                 | exact Hn | exact Ho | exact Hc1 | exact Hm].
Qed.

Lemma V_code_iwf {G Γ l li l' li' x x' s s' n n' o o' c c' m m'} :
  lwf (gL G) l -> lwf (gL G) li -> lequiv (gL G) l l' -> lequiv (gL G) li li' ->
  VTmG G Γ x x' (tyU li) (lsuc li) -> VTmG G Γ s s' (tyU l) (lsuc l) ->
  VTmG G (Γ ,, tyEl l s @ l) n n' tyNat lzero ->
  VTmG G (Γ ,, tyEl l s @ l) o o' (tyEl li x⟨↑⟩) li ->
  VTmG G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero) c c' (tyEl li x⟨↑⟩⟨↑⟩) li ->
  VTm G Γ m m' (tyEl li x) li ->
  VTm G Γ (tmIWf l li x s n o c m) (tmIWf l' li' x' s' n' o' c' m')
    (tyU (lmax l li)) (lsuc (lmax l li)).
Proof.
  intros Hwl Hwli Hl Hli Vx Vs Vn Vo Vc Vm Δ d d' Hd.
  assert (Hwm : lwf (gL G) (lmax l li)) by (cbn; split; assumption).
  pose proof (V_ElG Hwli Hli Vx) as VX. pose proof (V_ElG Hwl Hl Vs) as VA.
  pose proof (LR_IWf_here Hwl Hwli (lequiv_sym _ _ _ Hl) (lequiv_sym _ _ _ Hli) VX VA Vn Vo Vc Vm _ _ _ Hd)
    as HR.
  pose proof (VTmG_loc Vx _ _ _ Hd) as Xx. pose proof (VTmG_loc Vs _ _ _ Hd) as Xs.
  rewrite !subst_tyU in Xx, Xs.
  destruct (VTyG_loc VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & _ & _).
  assert (Hlift : SubRel G (Γ ,, tyEl l s @ l) (Δ ,, (tyEl l s)[d] @ l) (llift d) (llift d'))
    by exact (SubRel_lift Hd (VTy_refl_l (VTyG_loc VA)) HAd Hwl).
  pose proof (VTmG_loc Vn _ _ _ Hlift) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HNd _].
  pose proof (VTmG_loc Vo _ _ _ Hlift) as XO. rewrite !subst_tyEl, !shift_llift in XO.
  assert (HFd : [ G ; Δ ,, (tyEl l s)[d] @ l ⊢g (tyFin n)[llift d] @ lzero ])
    by (rewrite subst_tyFin; apply wft_fin; [exact ge_notV | exact HNd]).
  assert (Hlift2 : SubRel G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero)
                     (Δ ,, (tyEl l s)[d] @ l ,, (tyFin n)[llift d] @ lzero)
                     (llift (llift d)) (llift (llift d')))
    by exact (SubRel_lift Hlift (V_fin (VTmG_loc (VTmG_refl_l Vn))) HFd I).
  pose proof (VTmG_loc Vc _ _ _ Hlift2) as XC. rewrite !subst_tyEl, !shift_llift in XC.
  pose proof (Vm _ _ _ Hd) as Xm. rewrite !subst_tyEl in Xm.
  assert (Hgeq : [ G ; Δ ⊢ tmIWf l li x[d] s[d] n[llift d] o[llift d] c[llift (llift d)] m[d]
                   ≈ tmIWf l' li' x'[d'] s'[d'] n'[llift d'] o'[llift d'] c'[llift (llift d')] m'[d']
                   : tyU (lmax l li) @ lsuc (lmax l li) ])
    by (apply geq_tm_code_iwf;
        [ exact Hl | exact Hli | exact (proj1 (LRtm_escape Xx)) | exact (LRtm_geq Xx)
        | exact (proj1 (LRtm_escape Xs)) | exact (LRtm_geq Xs) | exact HNd | exact (LRtm_geq XN)
        | exact (LRtm_geq XO) | exact (LRtm_geq XC) | exact (LRtm_geq Xm) ]).
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U Hwm).
  exists (tmIWf l li x[d] s[d] n[llift d] o[llift d] c[llift (llift d)] m[d]),
    (tmIWf l' li' x'[d'] s'[d'] n'[llift d'] o'[llift d'] c'[llift (llift d')] m'[d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmIWf _ _ _ _ _ _ _ _) (conj (whnf_tmIWf _ _ _ _ _ _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  eexists. eapply LR_red_ty; [exact HR | |]; push_subst.
  - apply tyred_El_iwf; [exact Hla | now apply lequiv_refl | exact (eqtm_wf_l ge_typeof Hgeq')].
  - apply tyred_El_iwf; [exact Hlb | apply lequiv_sym, lequiv_max; assumption
                        | exact (eqtm_wf_r ge_typeof Hgeq')].
Qed.

Lemma V_El_iwf {G Γ l li x s n o c m} : lwf (gL G) l -> lwf (gL G) li ->
  VTmG G Γ x x (tyU li) (lsuc li) -> VTmG G Γ s s (tyU l) (lsuc l) ->
  VTmG G (Γ ,, tyEl l s @ l) n n tyNat lzero ->
  VTmG G (Γ ,, tyEl l s @ l) o o (tyEl li x⟨↑⟩) li ->
  VTmG G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero) c c (tyEl li x⟨↑⟩⟨↑⟩) li ->
  VTm G Γ m m (tyEl li x) li ->
  VTy G Γ (tyIWf l li (tyEl li x) (tyEl l s) n o c m) (tyEl (lmax l li) (tmIWf l li x s n o c m)) (lmax l li).
Proof.
  intros Hwl Hwli Vx Vs Vn Vo Vc Vm Δ d d' Hd.
  pose proof (V_ElG Hwli (lequiv_refl _ _ Hwli) Vx) as VX.
  pose proof (V_ElG Hwl (lequiv_refl _ _ Hwl) Vs) as VA.
  pose proof (LR_IWf_here Hwl Hwli (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwli) VX VA Vn Vo Vc Vm _ _ _ Hd)
    as HR.
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HP & _ & _).
  pose proof (V_code_iwf Hwl Hwli (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwli) Vx Vs Vn Vo Vc Vm
                _ _ _ (SubRel_refl_r Hd)) as Xc.
  rewrite !subst_tyU in Xc.
  eexists. eapply LR_red_ty; [exact HR | apply tyred_refl, HP |]. push_subst.
  rewrite ?subst_tmDVec, ?subst_tmIWf in Xc.
  apply tyred_El_iwf; [apply lequiv_refl; cbn; split; assumption | apply lequiv_refl; cbn; split; assumption
                      | exact (proj1 (LRtm_escape Xc))].
Qed.

End IWfCode.
