(** * Validity of indexed families with infinitary children (M19_DESIGN.md, M19b)

    Formation of [IWi] and [sup_ii], after [IWf]'s (M17b) and [M]'s
    (M18b). The index type's, the shapes' and the domains' relations live
    at the stage of the [IWi] type's level [iwiL l lp li] ([iwiIdx],
    [iwiDom], [iwiPd]), canonical there; the domains' relation carries
    the positions' [PosRel] as a conjunct, so that it is empty off related
    positions ([LRiwi]'s premise). *)
From DeLaM.Validity Require Export IWf M.
From DeLaM.Validity Require Import App MCorec.
From DeLaM.LogRel Require Import IWfAux IWiAux.
From DeLaM.Typing Require Import Inversion PresupIWi.

Section IWiV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Formation *)

Section IWiTy.
Context {G : gctx} {Γ : ctx} {l lp li k kp ki : lvl} {X X' A A' D D' : ty} {N N' Ot Ot' C C' : tm}
  (Hwl : lwf (gL G) l) (Hwlp : lwf (gL G) lp) (Hwli : lwf (gL G) li)
  (Hk : lequiv (gL G) k l) (Hkp : lequiv (gL G) kp lp) (Hki : lequiv (gL G) ki li)
  (VX : VTyG G Γ X X' li) (VA : VTyG G Γ A A' l)
  (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (VD : VTyG G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp)
  (VO : VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li)
  (VC : VTmG G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li).

Let K := lmeasure (iwiL l lp li).
Lemma K_l : lmeasure l <= K.
Proof using . unfold K; rewrite !lmeasure_max; lia. Qed.
Lemma K_lp : lmeasure lp <= K.
Proof using . unfold K; rewrite !lmeasure_max; lia. Qed.
Lemma K_li : lmeasure li <= K.
Proof using . unfold K; rewrite !lmeasure_max; lia. Qed.

(** The index type's, the shapes' and the domains' relations, in every
    world. *)
Definition iwiIdx Δ d d' : DomRel G Δ :=
  fun ρ => LRrel K (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X'[d']) li.
Definition iwiDom Δ d d' : DomRel G Δ :=
  fun ρ => LRrel K (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']) l.
Definition iwiPd Δ d d' : IPosDomRel G Δ :=
  fun ρ a a' p p' y y' =>
    PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'] p p' /\
    LRrel K (kw_G ρ) (kw_Δ ρ) (ktyll ρ D[llift (llift d)])[lsingle2 a p]
      (ktyll ρ D'[llift (llift d')])[lsingle2 a' p'] lp y y'.

Section At.
Context {Δ : ctx} {d d' : lsub} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ).

Let Hdρ := SubRel_kw _ _ _ ρ _ _ Hd.
Let Nd := proj1 (SubRel_nf _ _ _ _ _ Hd).
Let Nd' := proj2 (SubRel_nf _ _ _ _ _ Hd).

Lemma VA_kw : VTy (kw_G ρ) Γ⟦kw_γ ρ⟧ A⟦kw_γ ρ⟧ A'⟦kw_γ ρ⟧ l.
Proof using VA. exact (VA _ _ (kw_gok ρ)). Qed.
Lemma VNt_kw : VTm (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, A⟦kw_γ ρ⟧ @ l) N⟦kw_γ ρ⟧ N'⟦kw_γ ρ⟧ tyNat lzero.
Proof using VNt. pose proof (VNt _ _ (kw_gok ρ)) as Y. now rewrite gwa_cext, gwa_tyNat in Y. Qed.
Lemma VD_kw : VTy (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, A⟦kw_γ ρ⟧ @ l ,, tyFin N⟦kw_γ ρ⟧ @ lzero) D⟦kw_γ ρ⟧ D'⟦kw_γ ρ⟧ lp.
Proof using VD. pose proof (VD _ _ (kw_gok ρ)) as Y. now rewrite !gwa_cext, gwa_tyFin in Y. Qed.
Lemma VC_kw : VTm (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, A⟦kw_γ ρ⟧ @ l ,, tyFin N⟦kw_γ ρ⟧ @ lzero ,, D⟦kw_γ ρ⟧ @ lp)
  C⟦kw_γ ρ⟧ C'⟦kw_γ ρ⟧ X⟦kw_γ ρ⟧⟨↑⟩⟨↑⟩⟨↑⟩ li.
Proof using VC. pose proof (VC _ _ (kw_gok ρ)) as Y. now rewrite !gwa_cext, gwa_tyFin, !gwa_ren_ty in Y. Qed.

Lemma iwiIdx_iff x x' :
  iwiIdx Δ d d' ρ x x' <-> LRtm li (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X[d']) x x'.
Proof using EL VL VN VX Hd.
  exact (LRrel_iff K_li (VTyG_kw ρ VX Hd) (VTyG_kw ρ (VTyG_refl_l VX) Hd)).
Qed.

Lemma iwiDom_iff a a' :
  iwiDom Δ d d' ρ a a' <-> LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A[d']) a a'.
Proof using EL VL VN VA Hd.
  exact (LRrel_iff K_l (VTyG_kw ρ VA Hd) (VTyG_kw ρ (VTyG_refl_l VA) Hd)).
Qed.

Lemma iwiDom_sub a a' : iwiDom Δ d d' ρ a a' ->
  SubRel (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, A⟦kw_γ ρ⟧ @ l) (kw_Δ ρ) (lcons (kwsub ρ d) a) (lcons (kwsub ρ d') a').
Proof using EL VL VN VA Hd.
  intros ha. apply SubRel_cons; [exact Hdρ|]. apply iwiDom_iff in ha. now rewrite !kty_subst in ha.
Qed.

Lemma iwi_arity a a' : iwiDom Δ d d' ρ a a' ->
  NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'].
Proof using EL VL VN VA VNt Hd.
  intros ha. pose proof (VNt_kw _ _ _ (iwiDom_sub a a' ha)) as Y.
  rewrite <- !ktml_subst_single, subst_tyNat in Y. exact (proj1 LRtm_nat Y).
Qed.

Lemma iwi_ot a a' : iwiDom Δ d d' ρ a a' ->
  iwiIdx Δ d d' ρ (ktml ρ Ot[llift d])[lsingle a] (ktml ρ Ot'[llift d'])[lsingle a'].
Proof using EL VL VN VA VO VX Hd.
  intros ha. pose proof (VO _ _ (kw_gok ρ)) as VOρ. rewrite gwa_cext in VOρ.
  pose proof (VOρ _ _ _ (iwiDom_sub a a' ha)) as Y.
  rewrite <- !ktml_subst_single, gwa_ren_ty, !shift_cons_ty, <- !kty_subst in Y.
  exact (proj2 (iwiIdx_iff _ _) Y).
Qed.

(** Related positions, as related terms of [Fin] at the substitution. *)
Lemma iwiPos_sub a a' p p' : iwiDom Δ d d' ρ a a' ->
  PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'] p p' ->
  SubRel (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, A⟦kw_γ ρ⟧ @ l ,, tyFin N⟦kw_γ ρ⟧ @ lzero) (kw_Δ ρ)
    (lcons (lcons (kwsub ρ d) a) p) (lcons (lcons (kwsub ρ d') a') p').
Proof using EL VL VN VA VNt Hd.
  intros ha Hp. pose proof (iwiDom_sub a a' ha) as Hs.
  pose proof (PosRel_LRtm Hp (iwi_arity a a' ha)) as Xp. rewrite !ktml_subst_single in Xp.
  pose proof (VTmG_refl_l VNt _ _ (kw_gok ρ)) as VNρ. rewrite gwa_cext, gwa_tyNat in VNρ.
  pose proof (VNρ _ _ _ Hs) as YN. rewrite !subst_tyNat in YN.
  apply (proj1 LRtm_nat) in YN.
  pose proof (LR_fin_nat (ctx_of_tm (proj1 (NatRel_escape YN))) YN) as HF.
  apply SubRel_cons; [exact Hs|]. rewrite !subst_tyFin. eapply LRtm_irrel_r; [exact Xp | exact HF].
Qed.

Lemma iwiPd_iff a a' p p' y y' : iwiDom Δ d d' ρ a a' ->
  PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'] p p' ->
  (iwiPd Δ d d' ρ a a' p p' y y' <->
   LRtm lp (kw_G ρ) (kw_Δ ρ) (ktyll ρ D[llift (llift d)])[lsingle2 a p]
     (ktyll ρ D[llift (llift d')])[lsingle2 a' p'] y y').
Proof using EL VL VN VA VNt VD Hd.
  intros ha Hp. pose proof (iwiPos_sub a a' p p' ha Hp) as Hs.
  unfold iwiPd. rewrite !(ktyll_subst_single2 ρ d Nd), !(ktyll_subst_single2 ρ d' Nd').
  split; [intros [_ H]; exact (proj1 (LRrel_iff K_lp (VD_kw _ _ _ Hs) (VTy_refl_l VD_kw _ _ _ Hs)) H)|].
  intros H. exact (conj Hp (proj2 (LRrel_iff K_lp (VD_kw _ _ _ Hs) (VTy_refl_l VD_kw _ _ _ Hs)) H)).
Qed.

Lemma iwiPd_sub a a' p p' y y' : iwiDom Δ d d' ρ a a' -> iwiPd Δ d d' ρ a a' p p' y y' ->
  SubRel (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, A⟦kw_γ ρ⟧ @ l ,, tyFin N⟦kw_γ ρ⟧ @ lzero ,, D⟦kw_γ ρ⟧ @ lp) (kw_Δ ρ)
    (lcons (lcons (lcons (kwsub ρ d) a) p) y) (lcons (lcons (lcons (kwsub ρ d') a') p') y').
Proof using EL VL VN VA VNt VD Hd.
  intros ha hy. pose proof (proj1 hy) as Hp.
  apply SubRel_cons; [exact (iwiPos_sub a a' p p' ha Hp)|].
  apply (iwiPd_iff a a' p p' y y' ha Hp) in hy.
  now rewrite (ktyll_subst_single2 ρ d Nd), (ktyll_subst_single2 ρ d' Nd') in hy.
Qed.

(** Canonical at the stage of [IWi]'s level. *)
Lemma iwiIdx_canon : LR K (LRbelow K) (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X'[d']) li (iwiIdx Δ d d' ρ).
Proof using EL VL VN VX Hd.
  destruct (VTyG_kw ρ VX Hd) as [R HR]. exact (LR_canon _ _ _ _ _ _ _ (LogRel_up K_li HR)).
Qed.

Lemma iwiDom_canon : LR K (LRbelow K) (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']) l (iwiDom Δ d d' ρ).
Proof using EL VL VN VA Hd.
  destruct (VTyG_kw ρ VA Hd) as [R HR]. exact (LR_canon _ _ _ _ _ _ _ (LogRel_up K_l HR)).
Qed.

Lemma iwiPd_canon a a' : iwiDom Δ d d' ρ a a' -> forall p p',
  PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'] p p' ->
  LR K (LRbelow K) (kw_G ρ) (kw_Δ ρ) (ktyll ρ D[llift (llift d)])[lsingle2 a p]
    (ktyll ρ D'[llift (llift d')])[lsingle2 a' p'] lp (iwiPd Δ d d' ρ a a' p p').
Proof using EL VL VN VA VNt VD Hd.
  intros ha p p' Hp. pose proof (iwiPos_sub a a' p p' ha Hp) as Hs.
  destruct (VD_kw _ _ _ Hs) as [R HR].
  rewrite <- (ktyll_subst_single2 ρ d Nd), <- (ktyll_subst_single2 ρ d' Nd') in HR.
  pose proof (LR_canon _ _ _ _ _ _ _ (LogRel_up K_lp HR)) as Y.
  eapply LR_releq; [exact Y|]. intros y y'. unfold iwiPd. split; [intros H; exact (conj Hp H) | intros [_ H]; exact H].
Qed.

(** The child index at related arguments. *)
Lemma iwi_ch a a' p p' y y' : iwiDom Δ d d' ρ a a' -> iwiPd Δ d d' ρ a a' p p' y y' ->
  iwiIdx Δ d d' ρ (ktmlll ρ C[llift (llift (llift d))])[lsingle3 a p y]
    (ktmlll ρ C'[llift (llift (llift d'))])[lsingle3 a' p' y'].
Proof using EL VL VN VX VA VNt VD VC Hd.
  intros ha hy. pose proof (VC_kw _ _ _ (iwiPd_sub a a' p p' y y' ha hy)) as Y.
  rewrite !shift_cons_ty', <- !kty_subst in Y.
  rewrite <- (ktmlll_subst_single3 ρ d Nd), <- (ktmlll_subst_single3 ρ d' Nd') in Y.
  exact (proj2 (iwiIdx_iff _ _) Y).
Qed.

(** The child index at related shapes and positions, generically equal
    under the domain's binder. *)
Lemma iwi_gC a a' : iwiDom Δ d d' ρ a a' -> forall p p',
  PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'] p p' ->
  [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ D[llift (llift d)])[lsingle2 a p] @ lp
      ⊢ (ktmlll ρ C[llift (llift (llift d))])[llift (lsingle2 a p)]
        ≈ (ktmlll ρ C'[llift (llift (llift d'))])[llift (lsingle2 a' p')] : (kty ρ X[d])⟨↑⟩ @ li ].
Proof using EL VL VN VX VA VNt VD VC Hd Hwlp.
  intros ha p p' Hp. pose proof (iwiPos_sub a a' p p' ha Hp) as Hs.
  destruct (VD_kw _ _ _ Hs) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HDd & _ & _).
  pose proof (SubRel_lift Hs (VTy_refl_l VD_kw) HDd (kw_lwf ρ Hwlp)) as Hs2.
  pose proof (LRtm_geq (VC_kw _ _ _ Hs2)) as EC.
  rewrite !shift_llift_ty, !shift_cons_ty', <- kty_subst in EC.
  rewrite (ktyll_subst_single2 ρ d Nd), (ktmlll_subst_lift_single2 ρ d Nd), (ktmlll_subst_lift_single2 ρ d' Nd').
  exact EC.
Qed.

End At.

(** Kripke monotonicity of the domains' relation. *)
Lemma iwi_pdmon {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' p p' y y' :
  iwiPd Δ d d' ρ a a' p p' y y' ->
  iwiPd Δ d d' (kw_comp ρ ρ') (ktm ρ' a) (ktm ρ' a') (ktm ρ' p) (ktm ρ' p') (ktm ρ' y) (ktm ρ' y').
Proof using EL VL.
  intros [Hp (R & HR & Hy)]. split.
  - pose proof (PosRel_kw ρ' Hp) as Y. now rewrite !ktm_single, <- !ktml_comp in Y.
  - destruct (LR_kwk _ _ _ _ _ _ _ HR ρ') as (R' & HR' & ER).
    exists R'. rewrite !kty_lsingle2, <- !ktyll_comp in HR'. exact (conj HR' (ER _ _ Hy)).
Qed.

(** The former at a related index, at a related substitution. *)
Lemma LR_IWi_at Δ d d' mm mm' : SubRel G Γ Δ d d' -> LRtm li G Δ X[d] X[d'] mm mm' ->
  LogRel (iwiL l lp li) G Δ
    (tyIWi l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))] mm)
    (tyIWi k kp ki X'[d'] A'[d'] N'[llift d'] D'[llift (llift d')] Ot'[llift d'] C'[llift (llift (llift d'))] mm')
    (iwiL l lp li)
    (IWiRel G Δ l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))]
       (iwiIdx Δ d d') (iwiDom Δ d d') (iwiPd Δ d d') mm).
Proof using EL VL VN VX VA VNt VD VO VC Hwl Hwlp Hwli Hk Hkp Hki.
  intros Hd Xm. pose proof (SubRel_ctx Hd) as HΔ.
  destruct (VTyG_loc VX _ _ _ Hd) as [RX HRX]. destruct (escape_ty _ _ _ _ _ _ _ _ HRX) as (HXd & HX'd & EX).
  destruct (VTyG_loc VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd & EA).
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by exact (SubRel_lift Hd (VTy_refl_l (VTyG_loc VA)) HAd Hwl).
  pose proof (VTmG_loc VNt _ _ _ Hlift) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HNd HN'd]. pose proof (LRtm_geq XN) as EN.
  pose proof (VTmG_loc VO _ _ _ Hlift) as XO. rewrite !shift_llift_ty in XO.
  destruct (LRtm_escape XO) as [HOd HO'd]. pose proof (LRtm_geq XO) as EO.
  assert (HFd : [ G ; Δ ,, A[d] @ l ⊢g (tyFin N)[llift d] @ lzero ])
    by (rewrite subst_tyFin; apply wft_fin; [exact ge_notV | exact HNd]).
  assert (Hlift2 : SubRel G (Γ ,, A @ l ,, tyFin N @ lzero) (Δ ,, A[d] @ l ,, (tyFin N)[llift d] @ lzero)
                     (llift (llift d)) (llift (llift d')))
    by exact (SubRel_lift Hlift (V_fin (VTmG_loc (VTmG_refl_l VNt))) HFd I).
  destruct (VTyG_loc VD _ _ _ Hlift2) as [RD HRD]. destruct (escape_ty _ _ _ _ _ _ _ _ HRD) as (HDd & HD'd & ED).
  rewrite subst_tyFin in HDd, ED.
  assert (Hlift3 : SubRel G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp)
                     (Δ ,, A[d] @ l ,, tyFin N[llift d] @ lzero ,, D[llift (llift d)] @ lp)
                     (llift (llift (llift d))) (llift (llift (llift d')))).
  { pose proof (SubRel_lift Hlift2 (VTy_refl_l (VTyG_loc VD))) as Z. rewrite subst_tyFin in Z.
    exact (Z HDd Hwlp). }
  pose proof (VTmG_loc VC _ _ _ Hlift3) as XC. rewrite !shift_llift_ty in XC.
  destruct (LRtm_escape XC) as [HCd HC'd]. pose proof (LRtm_geq XC) as EC.
  destruct (LRtm_escape Xm) as [Hmd Hm'd]. pose proof (LRtm_geq Xm) as Em.
  assert (HE : IWiEq (G := G) (i := ge_layer) Δ l lp li k kp ki X[d] X'[d'] A[d] A'[d'] N[llift d] N'[llift d']
                 D[llift (llift d)] D'[llift (llift d')] Ot[llift d] Ot'[llift d']
                 C[llift (llift (llift d))] C'[llift (llift (llift d'))]).
  { apply IWiEq_intro; auto using geq_ty_sound, geq_tm_sound, lequiv_sym. }
  assert (HE0 : IWiEq (G := G) (i := ge_layer) Δ l lp li l lp li X[d] X'[d'] A[d] A'[d'] N[llift d] N'[llift d']
                 D[llift (llift d)] D'[llift (llift d')] Ot[llift d] Ot'[llift d']
                 C[llift (llift (llift d))] C'[llift (llift (llift d'))]).
  { apply IWiEq_intro; auto using geq_ty_sound, geq_tm_sound, lequiv_refl. }
  destruct (IWiEq_sig_r ge_typeof ge_notV HE0) as (_ & _ & _ & HX'r & HA'r & HN'r & HD'r & HO'r & HC'r).
  pose proof (proj1 (proj2 (proj2 (proj2 HE)))) as HS.
  eapply LRiwi with (l1 := l) (lp1 := lp) (li1 := li)
    (idxR := iwiIdx Δ d d') (domR := iwiDom Δ d d') (pdR := iwiPd Δ d d').
  - apply lequiv_refl, lwf_max; [apply lwf_max|]; assumption.
  - exact Hk.
  - exact Hkp.
  - exact Hki.
  - exact Hwl.
  - exact Hwlp.
  - exact Hwli.
  - apply tyred_refl, (IWi_ty_wf ge_typeof ge_notV HS Hmd).
  - apply tyred_refl, (pre_iwi_r ge_typeof ge_notV HE Hm'd).
  - exact HXd.
  - exact HX'r.
  - exact HAd.
  - exact HA'r.
  - exact HNd.
  - exact HN'r.
  - exact HDd.
  - exact HD'r.
  - exact HOd.
  - exact HO'r.
  - exact HCd.
  - exact HC'r.
  - exact Hmd.
  - eapply wf_conv; [exact Hm'd | rewrite ge_typeof; apply eqty_sym, geq_ty_sound, EX].
  - exact EX.
  - exact EA.
  - exact EN.
  - exact ED.
  - exact EO.
  - exact EC.
  - exact Em.
  - exact (iwiIdx_canon Hd).
  - intros ρ x y H. exact (proj1 (LR_tm_per _ _ _ _ _ _ _ (iwiIdx_canon Hd ρ)) _ _ H).
  - intros ρ x y z H1 H2. exact (proj2 (LR_tm_per _ _ _ _ _ _ _ (iwiIdx_canon Hd ρ)) _ _ _ H1 H2).
  - exact (iwiDom_canon Hd).
  - intros ρ a a' ha. exact (iwi_arity Hd ρ a a' ha).
  - intros ρ a a' ha. exact (iwi_ot Hd ρ a a' ha).
  - intros ρ a a' ha p p' Hp. exact (iwiPd_canon Hd ρ a a' ha p p' Hp).
  - intros ρ a a' p p' y y' hy. exact (proj1 hy).
  - intros ρ ρ' a a' p p' y y' hy. exact (iwi_pdmon Hd ρ ρ' a a' p p' y y' hy).
  - intros ρ a a' ha p p' y y' hy. exact (iwi_ch Hd ρ a a' p p' y y' ha hy).
  - intros ρ a a' ha p p' Hp. exact (iwi_gC Hd ρ a a' ha p p' Hp).
  - intros ρ. exact (proj2 (iwiIdx_iff Hd ρ _ _) (LRtm_kw ρ Xm)).
  - apply releq_refl.
Qed.

Lemma V_iwi_at {m m'} (Vm : VTm G Γ m m' X li) :
  VTy G Γ (tyIWi l lp li X A N D Ot C m) (tyIWi k kp ki X' A' N' D' Ot' C' m') (iwiL l lp li).
Proof using EL VL VN VX VA VNt VD VO VC Hwl Hwlp Hwli Hk Hkp Hki.
  intros Δ d d' Hd. eexists. rewrite !subst_tyIWi. exact (LR_IWi_at Δ d d' _ _ Hd (Vm _ _ _ Hd)).
Qed.

End IWiTy.

(** ** Syntax *)

Lemma llift_single_single_tm (t a p : tm) : nftm a -> t[llift (lsingle a)][lsingle p] = t[lsingle2 a p].
Proof using . intros Ha. revert Ha. generalize a p. intros x q Nx. meq. Qed.

(** A field's codomain at an argument. *)
Lemma iwiCod_single l lp li (X A : ty) (N : tm) (D : ty) (Ot C c0 y : tm) :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C ->
  (tyIWi l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩ c0)[lsingle y] =
  tyIWi l lp li X A N D Ot C c0[lsingle y].
Proof using . intros. push_subst. f_equal. all: teq_core. Qed.

(** ** Applications of terms related at [Π]

    The whnfs of terms related at a [Π], and their applications (at any
    annotations equivalent to the left type's) to related arguments,
    related at the codomain. *)
Lemma LRtm_pi_K {L G Γ l1 l2 A B T2 f f'} :
  LRtm L G Γ (tyPi l1 l2 A B) T2 f f' ->
  exists w w', [ G ; Γ ⊢g f ⤳* w : tyPi l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢g f' ⤳* w' : tyPi l1 l2 A B @ lmax l1 l2 ] /\ whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tyPi l1 l2 A B @ lmax l1 l2 ] /\ lequiv (gL G) L (lmax l1 l2) /\
    lwf (gL G) l1 /\ lwf (gL G) l2 /\ [ G ; Γ ⊢g A @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢g B @ l2 ] /\
    forall a a' T1, LRtm l1 G Γ A T1 a a' ->
    forall la lb la' lb' A1 B1 A1' B1',
      lequiv (gL G) la l1 -> lequiv (gL G) lb l2 -> lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
      [ G ; Γ ⊢ A ≈ A1 @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ B ≈ B1 @ l2 ] ->
      [ G ; Γ ⊢ A ≈ A1' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ B ≈ B1' @ l2 ] ->
      exists T', LRtm l2 G Γ B[lsingle a] T' (app w la lb A1 B1 a) (app w' la' lb' A1' B1' a').
Proof using EL VL VN.
  intros (R & HR & Hf).
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HT & _ & _).
  destruct (LR_inv_pi HR (tyred_refl _ _ HT))
    as (m3 & m4 & C' & D' & domR & codR & PF & HdomR & HcodR & Heq).
  destruct PF as [Hlv H3 H4 Hw1 Hw2 _ _ HA HA2 HB HB2 HAA HBB].
  pose proof (proj1 (Heq f f') Hf) as HP.
  pose proof (ctx_of_ty HA) as HΓ.
  pose proof (wf_ty_nf HA) as NA. pose proof (wf_ty_nf HA2) as NA2.
  pose proof (wf_ty_nf HB) as NB. pose proof (wf_ty_nf HB2) as NB2.
  destruct HP as (w & w' & Hw & Hw' & Nw & Nw' & Ew & _ & HK).
  assert (EPi : [ G ; Γ ⊢g tyPi m3 m4 C' D' ≅ tyPi l1 l2 A B @ lmax l1 l2 ])
    by (apply eqty_sym, geq_ty_sound, geq_ty_pi; auto using lequiv_sym).
  exists w, w'. refine (conj Hw (conj _ (conj Nw (conj Nw' (conj Ew (conj Hlv (conj Hw1 (conj Hw2 (conj HA (conj HB _)))))))))).
  { eapply tmred_conv; [apply ge_typeof | exact Hw' | exact EPi]. }
  intros a a' T1 Ha la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
  set (ρ0 := kw_loc wk_id (wkwf_id Γ) HΓ) in *.
  pose proof (HdomR ρ0) as HD. change (kw_G ρ0) with G in HD; change (kw_Δ ρ0) with Γ in HD.
  unfold ρ0 in HD; rewrite (kw_loc_id_ty (HΔ := HΓ) _ NA), (kw_loc_id_ty (HΔ := HΓ) _ NA2) in HD.
  assert (ha : domR ρ0 a a').
  { apply (LRrel_canon _ _ _ _ _ _ _ HD). apply (proj1 (LRtm_stage (lmeasure_le_l Hlv))).
    eapply LRtm_irrel_r; [exact Ha|]. eexists. exact (proj2 (LogRel_stage _ _ _ _ _ _ _ (lmeasure_le_l Hlv)) HD). }
  assert (HA1c : [ G ; Γ ⊢ C' ≈ A1' @ l1 ]) by exact (geq_ty_trans (geq_ty_sym HAA) HA1').
  assert (HB1c : [ G ; Γ ,, C' @ l1 ⊢ D' ≈ B1' @ l2 ]).
  { eapply geq_ty_ctxconv; [exact (geq_ty_sound HAA) | now apply lequiv_refl | exact (ctx_of_ty HB2) |].
    exact (geq_ty_trans (geq_ty_sym HBB) HB1'). }
  pose proof (HK ρ0 a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2') as K.
  unfold kty, ktm, ktyl, ρ0, kw_loc in K; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk] in K.
  rewrite (ren_id_tm w), (ren_id_tm w') in K
    by (eapply wf_tm_nf, eqtm_wf_r; [apply ge_typeof | apply tmred_eq; eassumption]).
  rewrite (ren_id_ty A), (ren_id_ty C'), (ren_lift_id_ty B), (ren_lift_id_ty D') in K by assumption.
  pose proof (K HA1 HB1 HA1c HB1c) as c.
  pose proof (HcodR ρ0 _ _ ha) as HC. change (kw_G ρ0) with G in HC; change (kw_Δ ρ0) with Γ in HC.
  unfold ρ0 in HC; rewrite (kw_loc_id_tyl (HΔ := HΓ) _ NB), (kw_loc_id_tyl (HΔ := HΓ) _ NB2) in HC.
  exists D'[lsingle a']. apply (LRtm_stage (lmeasure_le_r Hlv)). eexists. exact (conj HC c).
Qed.

(** [IWiRel] is closed under anti-reduction. *)
Lemma IWiRel_red {G Δ l lp li X A N D Ot C ix dm pd m t t' u u'} :
  IWiRel G Δ l lp li X A N D Ot C ix dm pd m u u' ->
  [ G ; Δ ⊢g t ⤳* u : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Δ ⊢g t' ⤳* u' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  IWiRel G Δ l lp li X A N D Ot C ix dm pd m t t'.
Proof using .
  intros H Ht Ht'. destruct (IWiRel_inv H) as (w & w' & Hw & Hw' & Ew & Nw).
  econstructor; [exact (tmred_trans _ _ _ _ _ Ht Hw) | exact (tmred_trans _ _ _ _ _ Ht' Hw')
                | exact Ew | exact Nw].
Qed.

(** ** Canonical relations

    The relation of any derivation at an [IWi] type is [IWiRel] at
    canonical index and shape relations ([KDom]) and at a domains'
    relation canonical where the relation reads it: at related shapes,
    against a right position related along some right arity [N0]. *)
Lemma LR_iwi_rel {G Δ l lp li X A N D Ot C c T' R N0} {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ} :
  LogRel (iwiL l lp li) G Δ (tyIWi l lp li X A N D Ot C c) T' (iwiL l lp li) R ->
  KDom G Δ (lmeasure (iwiL l lp li)) li X ix -> KDom G Δ (lmeasure (iwiL l lp li)) l A dm ->
  (forall (ρ : kwk G Δ) a a', dm ρ a a' ->
     NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a']) ->
  (forall (ρ : kwk G Δ) a a', dm ρ a a' -> forall p p',
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a'] p p' ->
     exists D1, LR (lmeasure (iwiL l lp li)) (LRbelow (lmeasure (iwiL l lp li))) (kw_G ρ) (kw_Δ ρ)
       (ktyll ρ D)[lsingle2 a p] D1 lp (pd ρ a a' p p')) ->
  (forall (ρ : kwk G Δ) a a' p p' y y', pd ρ a a' p p' y y' ->
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a'] p p') ->
  releq R (IWiRel G Δ l lp li X A N D Ot C ix dm pd c).
Proof using EL VL.
  intros H HX HA Har Hpd HpdE. destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HW & _ & _).
  destruct (LR_inv_iwi H (tyred_refl _ _ HW))
    as (k2 & kp2 & ki2 & X' & A' & N' & D' & Ot' & C' & m' & idxR & domR & pdR
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & idxAd & _ & _ & domAd & arAd & _ & pdAd & pdE & _ & _ & _ & _ & HR).
  assert (Hi : forall ρ, releq (idxR ρ) (ix ρ))
    by (intros ρ; destruct (HX ρ) as [X1 Y]; exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (idxAd ρ) Y)).
  assert (Hd : forall ρ, releq (domR ρ) (dm ρ))
    by (intros ρ; destruct (HA ρ) as [A1 Y]; exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (domAd ρ) Y)).
  intros t t'. etransitivity; [apply HR|]. apply IWiRel_releq.
  - exact Hi.
  - exact Hd.
  - intros ρ a a' p y y' ha (p' & Hy).
    pose proof (pdE _ _ _ _ _ _ _ Hy) as Hp.
    pose proof (proj1 (Hd ρ a a') ha) as ha'.
    destruct (PosRel_retarget Hp _ (Har ρ a a' ha')) as (p2 & Hp2).
    destruct (Hpd ρ a a' ha' p p2 Hp2) as [D1 Y].
    exists p2. exact (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ (pdAd ρ a a' ha p p' Hp) Y y y') Hy).
  - intros ρ a a' p y y' ha (p' & Hy).
    pose proof (HpdE _ _ _ _ _ _ _ Hy) as Hp.
    pose proof (proj1 (Hd ρ a a') ha) as ha'.
    destruct (PosRel_retarget Hp _ (arAd ρ a a' ha)) as (p2 & Hp2).
    destruct (Hpd ρ a a' ha' p p' Hp) as [D1 Y].
    exists p2. exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ (pdAd ρ a a' ha p p2 Hp2) Y y y') Hy).
Qed.

(** ** The children's spine *)

Section WSpine.
Context {G : gctx} {Δ : ctx} {l lp li : lvl} {X A D : ty} {N Ot C N0 : tm}
  {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ}
  (HΔ : [ G ; Δ ⊢g ]) (Hwl : lwf (gL G) l) (Hwlp : lwf (gL G) lp) (Hwli : lwf (gL G) li)
  (NX : nfty X) (NA : nfty A) (NN : nftm N) (ND : nfty D) (NO : nftm Ot) (NC : nftm C)
  (HX : KDom G Δ (lmeasure (iwiL l lp li)) li X ix) (HA : KDom G Δ (lmeasure (iwiL l lp li)) l A dm)
  (Har : forall (ρ : kwk G Δ) a a', dm ρ a a' ->
     NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a'])
  (Hpd : forall (ρ : kwk G Δ) a a', dm ρ a a' -> forall p p',
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a'] p p' ->
     exists D1, LR (lmeasure (iwiL l lp li)) (LRbelow (lmeasure (iwiL l lp li))) (kw_G ρ) (kw_Δ ρ)
       (ktyll ρ D)[lsingle2 a p] D1 lp (pd ρ a a' p p'))
  (HpdE : forall (ρ : kwk G Δ) a a' p p' y y', pd ρ a a' p p' y y' ->
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a'] p p').

Let L := iwiL l lp li.

(** Relation to spine, at the spine's own world: the argument relation
    [yR] relates arguments at the domain family. *)
Lemma DVecWSp_of_LR : forall k k', NatRel G Δ k k' -> forall d c (yR : tm -> tm -> tm -> Prop),
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ L ] ->
  (forall p y y', yR p y y' -> exists T1, LRtm lp G Δ d[lsingle p] T1 y y') ->
  forall T' R, LogRel L G Δ (tyDVec L k (iwiFamT l lp li X A N D Ot C d c)) T' L R ->
  forall cs cs', R cs cs' -> DVecWSp G Δ l lp li X A N D Ot C ix dm pd yR d c k cs cs'.
Proof using EL HA HX HΔ Har Hpd HpdE Hwl Hwli Hwlp NA NC ND NN NO NX VL VN.
  assert (HwL : lwf (gL G) L) by (unfold L; apply lwf_max; [apply lwf_max|]; assumption).
  apply (NatRel_mut G Δ
    (fun k k' _ => forall d c (yR : tm -> tm -> tm -> Prop),
       [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ L ] ->
       (forall p y y', yR p y y' -> exists T1, LRtm lp G Δ d[lsingle p] T1 y y') ->
       forall T' R, LogRel L G Δ (tyDVec L k (iwiFamT l lp li X A N D Ot C d c)) T' L R ->
       forall cs cs', R cs cs' -> DVecWSp G Δ l lp li X A N D Ot C ix dm pd yR d c k cs cs')
    (fun w w' _ => forall k, [ G ; Δ ⊢g k ⤳* w : tyNat @ lzero ] -> forall d c (yR : tm -> tm -> tm -> Prop),
       [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ L ] ->
       (forall p y y', yR p y y' -> exists T1, LRtm lp G Δ d[lsingle p] T1 y y') ->
       forall T' R, LogRel L G Δ (tyDVec L k (iwiFamT l lp li X A N D Ot C d c)) T' L R ->
       forall cs cs', R cs cs' -> DVecWSp G Δ l lp li X A N D Ot C ix dm pd yR d c k cs cs')).
  - intros t t' w w' Ht _ _ _ IH. exact (IH t Ht).
  - intros k Hk d c yR HF HY T' R H cs cs' Hcs.
    pose proof (fin_stab_ty (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF0.
    assert (Hred : [ G ; Δ ⊢g tyDVec L k (iwiFamT l lp li X A N D Ot C d c) ⤳* tyUnit L @ L ])
      by (eapply tyred_trans; [exact (tyred_dvec HwL HF Hk) | exact (tyred_dvec_zero HwL HF0)]).
    destruct (LR_inv_unit H Hred) as (l2 & _ & _ & _ & _ & HR).
    eapply wsp_zero; [exact Hk | exact (proj1 (HR _ _) Hcs)].
  - intros m m' Hmm IH k Hk d c yR HF HY T' R H cs cs' Hcs.
    destruct (NatRel_escape Hmm) as (Hm & _ & _). pose proof (wf_tm_nf Hm) as Nm.
    destruct (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf HF)) as [Nd Nc].
    assert (Nq : nftm (posHd m)) by (unfold posHd; cbn; repeat split; auto).
    pose proof (fin_stab_ty (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF1.
    set (F := iwiFamT l lp li X A N D Ot C d c) in *.
    assert (Hred : [ G ; Δ ⊢g tyDVec L k F ⤳* tySig L L (dvecHd m F) (dvecTl L m F) @ L ])
      by (eapply tyred_trans; [exact (tyred_dvec HwL HF Hk) | exact (tyred_dvec_succ HwL HF1 Hm)]).
    destruct (LR_inv_sig H Hred) as (m3 & m4 & C' & D' & dS & cS & P & domAd & codAd & HR).
    destruct P as [_ Hm3 Hm4 _ _ _ _ HC0 HC' HV HD' HWC HVD].
    apply HR in Hcs. destruct Hcs as (w & w' & Hr & Hr' & Nw & Nw' & Ew & _ & K).
    pose proof (wf_tm_nf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hr))) as Nw0.
    pose proof (wf_tm_nf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hr'))) as Nw0'.
    assert (EΣ : [ G ; Δ ⊢g tySig m3 m4 C' D' ≅ tySig L L (dvecHd m F) (dvecTl L m F) @ lmax L L ])
      by (apply eqty_sym, geq_ty_sound, geq_ty_sig; auto using lequiv_sym).
    pose proof (K (kid HΔ)) as Kι.
    rewrite (kty_kid HΔ _ (wf_ty_nf HC0)) in Kι.
    rewrite (ktyl_kid HΔ _ (wf_ty_nf HV)) in Kι.
    rewrite (kty_kid HΔ _ (wf_ty_nf HC')) in Kι.
    rewrite (ktyl_kid HΔ _ (wf_ty_nf HD')) in Kι.
    rewrite (ktm_kid HΔ _ Nw0), (ktm_kid HΔ _ Nw0') in Kι.
    assert (HΔC' : [ G ; Δ ,, C' @ L ⊢g ]) by exact (ext_wf_g HC' HwL).
    assert (Kι' : forall la lb A1 B1 la' lb' A1' B1',
              lequiv (gL G) la L -> lequiv (gL G) lb L -> lequiv (gL G) la' L -> lequiv (gL G) lb' L ->
              [ G ; Δ ⊢ dvecHd m F ≈ A1 @ L ] ->
              [ G ; Δ ,, dvecHd m F @ L ⊢ dvecTl L m F ≈ B1 @ L ] ->
              [ G ; Δ ⊢ dvecHd m F ≈ A1' @ L ] ->
              [ G ; Δ ,, dvecHd m F @ L ⊢ dvecTl L m F ≈ B1' @ L ] ->
              exists h : dS (kid HΔ) (tmFst la lb A1 B1 w) (tmFst la' lb' A1' B1' w'),
                cS (kid HΔ) _ _ h (tmSnd la lb A1 B1 w) (tmSnd la' lb' A1' B1' w')).
    { intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      apply (Kι la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1).
      - exact (geq_ty_trans (geq_ty_sym HWC) HA1').
      - eapply geq_ty_ctxconv; [exact (geq_ty_sound HWC) | now apply lequiv_refl | exact HΔC' |].
        exact (geq_ty_trans (geq_ty_sym HVD) HB1'). }
    pose proof (domAd (kid HΔ)) as DOM.
    rewrite (kty_kid HΔ _ (wf_ty_nf HC0)), (kty_kid HΔ C') in DOM by exact (wf_ty_nf HC').
    assert (EF : dvecHd m F = tyPi lp L d[lsingle (posHd m)]
                   (tyIWi l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩
                      c[llift (lsingle (posHd m))]))
      by (unfold F; rewrite iwiFamT_single by assumption; reflexivity).
    (* the head, as a term related at the field's Π *)
    assert (Xh : forall la lb A1 B1 la' lb' A1' B1',
              lequiv (gL G) la L -> lequiv (gL G) lb L -> lequiv (gL G) la' L -> lequiv (gL G) lb' L ->
              [ G ; Δ ⊢ dvecHd m F ≈ A1 @ L ] ->
              [ G ; Δ ,, dvecHd m F @ L ⊢ dvecTl L m F ≈ B1 @ L ] ->
              [ G ; Δ ⊢ dvecHd m F ≈ A1' @ L ] ->
              [ G ; Δ ,, dvecHd m F @ L ⊢ dvecTl L m F ≈ B1' @ L ] ->
              LRtm L G Δ (dvecHd m F) C' (tmFst la lb A1 B1 w) (tmFst la' lb' A1' B1' w')).
    { intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      destruct (Kι' la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1') as [h _].
      exact (LRtm_of DOM h). }
    eapply wsp_succ; [exact Hk | exact Hr | eapply tmred_conv; [apply ge_typeof | exact Hr' | exact EΣ]
                     | exact Nw | exact Nw' | exact Ew | | |].
    + (* the head, a function *)
      intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      pose proof (Xh la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1') as Y.
      rewrite EF in Y. destruct (LRtm_pi_K Y) as (w0 & w0' & Hr0 & Hr0' & N0w & N0w' & E0 & Hlv & _).
      exists w0, w0'. fold F. rewrite EF.
      refine (conj _ (conj _ (conj N0w (conj N0w' _)))).
      * eapply tmred_lconv; [exact Hr0 | exact Hlv].
      * eapply tmred_lconv; [exact Hr0' | exact Hlv].
      * eapply geq_tm_lconv; [exact E0 | exact Hlv].
    + (* the head's applications *)
      intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1' y y' Hy
        la2 lb2 A3 B3 la2' lb2' A3' B3' H3 H4 H3' H4' HA3 HB3 HA3' HB3'.
      pose proof (Xh la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1') as Y.
      rewrite EF in Y.
      destruct (LRtm_pi_K Y) as (w0 & w0' & Hr0 & Hr0' & _ & _ & _ & Hlv & Hwp & HwL' & HA0 & HB0 & K0).
      destruct (HY _ _ _ Hy) as (T1 & Xy).
      destruct (LRtm_escape Xy) as [Hyt Hyt']. pose proof (LRtm_geq Xy) as Eyy.
      rewrite iwiFamCodT_single in HB3, HB3' by assumption.
      destruct (K0 y y' T1 Xy la2 lb2 la2' lb2' A3 B3 A3' B3' H3 H4 H3' H4' HA3 HB3 HA3' HB3') as (T2 & Xapp).
      rewrite iwiCod_single, llift_single_single_tm in Xapp by assumption.
      destruct Xapp as (R0 & HR0 & Happ).
      pose proof (proj1 (LR_iwi_rel HR0 HX HA Har Hpd HpdE _ _) Happ) as Z.
      pose proof (tmred_app_annot Hwp HwL' H3 H4 HA0 HB0 Hyt (geq_ty_sound HA3) (geq_ty_sound HB3) Hr0) as Ra.
      pose proof (tmred_app_annot Hwp HwL' H3' H4' HA0 HB0 Hyt' (geq_ty_sound HA3') (geq_ty_sound HB3') Hr0') as Ra'.
      rewrite iwiCod_single, llift_single_single_tm in Ra, Ra' by assumption.
      eapply IWiRel_red; [exact Z | exact Ra |].
      eapply tmred_conv; [apply ge_typeof | exact Ra' |].
      pose proof (wf_ty_func ge_typeof HB0 (lsub_eq_single ge_typeof Hyt' Hyt (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Eyy))))
        as EB.
      rewrite !iwiCod_single, !llift_single_single_tm in EB by assumption. exact EB.
    + (* the tail *)
      intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      destruct (Kι' la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1') as [h Hc].
      pose proof (dvecMv_wf ge_typeof ge_notV ge_compt Hm HF1) as HFmv.
      assert (HDV : [ G ; Δ ⊢g tyDVec L m (dvecMv m F) @ L ])
        by (apply wft_dvec; [exact (compt_notV _ ge_compt) | exact HwL | exact Hm | exact HFmv]).
      pose proof (codAd (kid HΔ) _ _ h) as COD.
      rewrite dvec_cod_single, (kty_kid HΔ) in COD by exact (wf_ty_nf HDV).
      rewrite (ktyl_kid HΔ D') in COD by exact (wf_ty_nf HD').
      unfold F in COD. rewrite iwiFamT_mv in COD.
      refine (IH (posMvT m d) (posMv2 m c) (fun p => yR (posTl m p)) _ _ _ _ _ _ _ Hc).
      * rewrite <- iwiFamT_mv. exact HFmv.
      * intros p y y' Hy. rewrite posMvT_single by exact Nm. exact (HY _ _ _ Hy).
      * exact COD.
  - intros ν ν' Hνν k Hk d c yR HF HY T' R H cs cs' Hcs.
    pose proof (gne_tm_whne_l Hνν) as Nν.
    assert (Hred : [ G ; Δ ⊢g tyDVec L k (iwiFamT l lp li X A N D Ot C d c)
                     ⤳* tyDVec L ν (iwiFamT l lp li X A N D Ot C d c) @ L ])
      by exact (tyred_dvec HwL HF Hk).
    destruct (LR_inv_ne H Hred (whne_tyDVec _ _ _ Nν)) as (V' & _ & HVV & HR).
    eapply wsp_ne; [exact Hk | exact (gne_tm_refl_l Hνν) |].
    eapply NeRel_conv2; [| | exact (proj1 (HR _ _) Hcs)].
    + apply eqty_refl. exact (eqty_wf_l ge_typeof (geq_ty_sound (gne_ty_geq HVV))).
    + apply eqty_sym, geq_ty_sound, gne_ty_geq, HVV.
Qed.

End WSpine.

(** ** [sup_ii] *)

Section SupiiV.
Context {G : gctx} {Γ : ctx} {l lp li k kp ki : lvl} {X X' A A' D D' : ty} {N N' Ot Ot' C C' a a' cs cs' : tm}
  (Hwl : lwf (gL G) l) (Hwlp : lwf (gL G) lp) (Hwli : lwf (gL G) li)
  (Hk : lequiv (gL G) k l) (Hkp : lequiv (gL G) kp lp) (Hki : lequiv (gL G) ki li)
  (VX : VTyG G Γ X X' li) (VA : VTyG G Γ A A' l)
  (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (VD : VTyG G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp)
  (VO : VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li)
  (VC : VTmG G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li)
  (Va : VTm G Γ a a' A l)
  (Vcs : VTm G Γ cs cs' (tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a)) (iwiL l lp li)).

(** The constructor's index. *)
Lemma V_supii_idx : VTm G Γ Ot[lsingle a] Ot[lsingle a] X li.
Proof using EL VL VO Va.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTm_trans Va (VTm_sym Va)) as Vaa.
  pose proof (VTmG_loc (VTmG_refl_l VO) _ _ _ (SubRel_cons Hd (Vaa _ _ _ Hd))) as Y.
  rewrite !shift_cons_ty in Y. rewrite !single_subst, !lift_single_tm by assumption. exact Y.
Qed.

Lemma V_supii_idx2 : VTm G Γ Ot[lsingle a] Ot'[lsingle a'] X li.
Proof using EL VO Va.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTmG_loc VO _ _ _ (SubRel_cons Hd (Va _ _ _ Hd))) as Y.
  rewrite !shift_cons_ty in Y. rewrite !single_subst, !lift_single_tm by assumption. exact Y.
Qed.

Lemma V_supii_ty : VTy G Γ (tyIWi l lp li X A N D Ot C Ot[lsingle a])
  (tyIWi k kp ki X' A' N' D' Ot' C' Ot'[lsingle a']) (iwiL l lp li).
Proof using EL Hk Hkp Hki Hwl Hwli Hwlp VA VC VD VL VN VNt VO VX Va.
  exact (V_iwi_at Hwl Hwlp Hwli Hk Hkp Hki VX VA VNt VD VO VC V_supii_idx2).
Qed.

Lemma V_supii : VTm G Γ (tmSupii l lp li X A N D Ot C a cs) (tmSupii k kp ki X' A' N' D' Ot' C' a' cs')
  (tyIWi l lp li X A N D Ot C Ot[lsingle a]) (iwiL l lp li).
Proof using EL Hk Hkp Hki Hwl Hwli Hwlp VA VC VD VL VN VNt VO VX Va Vcs.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd']. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (VTyG_refl_l VX) as VXX. pose proof (VTyG_refl_l VA) as VAA.
  pose proof (VTmG_refl_l VNt) as VNN. pose proof (VTyG_refl_l VD) as VDD.
  pose proof (VTmG_refl_l VO) as VOO. pose proof (VTmG_refl_l VC) as VCC.
  pose proof (lequiv_refl _ _ Hwl) as Rl. pose proof (lequiv_refl _ _ Hwlp) as Rlp.
  pose proof (lequiv_refl _ _ Hwli) as Rli.
  pose proof (LR_IWi_at Hwl Hwlp Hwli Rl Rlp Rli VXX VAA VNN VDD VOO VCC _ _ _ _ _ Hd (V_supii_idx _ _ _ Hd)) as HW.
  eapply LRtm_of; [exact HW|]. rewrite !subst_supii.
  (* escapes *)
  destruct (VTyG_loc VX _ _ _ Hd) as [RX HRX]. destruct (escape_ty _ _ _ _ _ _ _ _ HRX) as (HXd & HX'd & EX).
  destruct (VTyG_loc VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd & EA).
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by exact (SubRel_lift Hd (VTy_refl_l (VTyG_loc VA)) HAd Hwl).
  pose proof (VTmG_loc VNt _ _ _ Hlift) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HNd HN'd]. pose proof (LRtm_geq XN) as EN.
  pose proof (VTmG_loc VO _ _ _ Hlift) as XO. rewrite !shift_llift_ty in XO.
  destruct (LRtm_escape XO) as [HOd HO'd]. pose proof (LRtm_geq XO) as EO.
  assert (HFd : [ G ; Δ ,, A[d] @ l ⊢g (tyFin N)[llift d] @ lzero ])
    by (rewrite subst_tyFin; apply wft_fin; [exact ge_notV | exact HNd]).
  assert (Hlift2 : SubRel G (Γ ,, A @ l ,, tyFin N @ lzero) (Δ ,, A[d] @ l ,, (tyFin N)[llift d] @ lzero)
                     (llift (llift d)) (llift (llift d')))
    by exact (SubRel_lift Hlift (V_fin (VTmG_loc (VTmG_refl_l VNt))) HFd I).
  destruct (VTyG_loc VD _ _ _ Hlift2) as [RD HRD]. destruct (escape_ty _ _ _ _ _ _ _ _ HRD) as (HDd & HD'd & ED).
  rewrite subst_tyFin in HDd, ED.
  assert (Hlift3 : SubRel G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp)
                     (Δ ,, A[d] @ l ,, tyFin N[llift d] @ lzero ,, D[llift (llift d)] @ lp)
                     (llift (llift (llift d))) (llift (llift (llift d')))).
  { pose proof (SubRel_lift Hlift2 (VTy_refl_l (VTyG_loc VD))) as Z. rewrite subst_tyFin in Z.
    exact (Z HDd Hwlp). }
  pose proof (VTmG_loc VC _ _ _ Hlift3) as XC. rewrite !shift_llift_ty in XC.
  destruct (LRtm_escape XC) as [HCd HC'd]. pose proof (LRtm_geq XC) as EC.
  pose proof (Va _ _ _ Hd) as Xa. pose proof (LRtm_geq Xa) as Ea.
  pose proof (Vcs _ _ _ Hd) as Xcs.
  rewrite !subst_tyDVec, !single_subst, !subst_iwiFam in Xcs by assumption.
  pose proof (LRtm_geq Xcs) as Ecs.
  pose proof (geq_tm_supii (lequiv_sym _ _ _ Hk) (lequiv_sym _ _ _ Hkp) (lequiv_sym _ _ _ Hki)
                HXd (geq_ty_sound EX) HAd (geq_ty_sound EA) HNd (geq_tm_sound EN) HDd (geq_ty_sound ED)
                HOd (geq_tm_sound EO) HCd (geq_tm_sound EC) Ea Ecs) as Dsup.
  pose proof (geq_tm_sound Dsup) as Dsup'.
  rewrite single_subst by assumption.
  eapply iwirel; [exact (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dsup'))
                 | exact (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Dsup')) | exact Dsup |].
  (* the related shapes, in every world *)
  assert (hdom : forall ρ : kwk G Δ, iwiDom (l := l) (lp := lp) (li := li) (A := A) (A' := A) Δ d d' ρ
                   (ktm ρ a[d]) (ktm ρ a'[d'])).
  { intros ρ. unfold iwiDom. apply (LRtm_stage K_l). exact (LRtm_kw ρ Xa). }
  apply iwinf_sup.
  - exact (IWiEq_intro Rl Rlp Rli (geq_ty_sound (geq_ty_refl_l EX)) (geq_ty_sound (geq_ty_refl_l EA))
             (geq_tm_sound (geq_tm_refl_l EN)) (geq_ty_sound (geq_ty_refl_l ED)) (geq_tm_sound (geq_tm_refl_l EO))
             (geq_tm_sound (geq_tm_refl_l EC)) Hwl Hwlp Hwli HXd HAd HNd HDd HOd HCd HXd HAd HNd HDd HOd HCd).
  - apply IWiEq_intro; auto using geq_ty_sound, geq_tm_sound, lequiv_sym.
  - exact hdom.
  - intros ρ. rewrite ktm_single.
    pose proof (iwi_ot VXX VAA VOO Hd ρ _ _ (hdom ρ)) as Y.
    destruct (LR_tm_per _ _ _ _ _ _ _ (iwiIdx_canon (l := l) (lp := lp) VXX Hd ρ)) as [Sy Tr].
    exact (Tr _ _ _ Y (Sy _ _ Y)).
  - intros ρ. destruct (LRtm_kw ρ Xcs) as (R & HR & Hc).
    rewrite kty_tyDVec, ktm_single, iwiFam_T, ktyl_iwiFamT, ktyl_llift_single, ktmll_llift2_single in HR.
    destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HT & _ & _).
    destruct (inv_ty_dvec HT) as ((_ & _ & _ & HFam) & _).
    pose proof (kw_lwf ρ Hwl) as Hwlρ. pose proof (kw_lwf ρ Hwlp) as Hwlpρ. pose proof (kw_lwf ρ Hwli) as Hwliρ.
    assert (Na : nftm (ktm ρ a[d])) by (unfold ktm; apply ren_nf).
    refine (DVecWSp_of_LR (N0 := ktml ρ N[llift d']) (kw_ctx ρ) Hwlρ Hwlpρ Hwliρ _ _ _ _ _ _
              (KDom_comp ρ (fun ρ0 => ex_intro _ _ (iwiIdx_canon (l := l) (lp := lp) VXX Hd ρ0)))
              (KDom_comp ρ (fun ρ0 => ex_intro _ _ (iwiDom_canon (lp := lp) (li := li) VAA Hd ρ0)))
              _ _ _ _ _ (iwi_arity VAA VNN Hd ρ _ _ (hdom ρ)) _ _ _ HFam _ _ _ HR _ _ Hc).
    all: try first [unfold kty; apply ren_nf_ty | unfold ktml; apply ren_nf | unfold ktyll; apply ren_nf_ty
                   | unfold ktmlll; apply ren_nf].
    + intros ρ' a0 a0' h. pose proof (iwi_arity VAA VNN Hd (kw_comp ρ ρ') a0 a0' h) as Y.
      now rewrite !ktml_comp in Y.
    + intros ρ' a0 a0' h p p' Hp. rewrite <- !ktml_comp in Hp.
      pose proof (iwiPd_canon VAA VNN VDD Hd (kw_comp ρ ρ') a0 a0' h p p' Hp) as Y.
      rewrite !ktyll_comp in Y. eexists. exact Y.
    + intros ρ' a0 a0' p p' y y' [Hp _]. now rewrite !ktml_comp in Hp.
    + intros p y y' (p' & Hp & Hy). apply (LRtm_stage K_lp) in Hy.
      rewrite llift_single_single_ty by exact Na. eexists. exact Hy.
Qed.

End SupiiV.

End IWiV.
