(** * Validity of indexed finitary well-founded trees (M17_DESIGN.md, M17b)

    Formation of [IWf] and [sup_i], after [Wf]'s (M15a). The index type's
    and the shapes' relations live at the stage of the [IWf] type's level
    [lmax l li], not at [li] and [l] ([iwfIdx], [iwfDom]); [KDom] makes
    them canonical there, so that any derivation at an [IWf] type has the
    relation [IWfRel] at them ([LR_iwf_rel]). The children's spine
    [DVecISp] comes from the relation at [DVec(k; i. IWf(c))] by induction
    on the length's [NatRel] ([DVecISp_of_LR], for [sup_i]'s validity),
    the head at the head's index [c[inl ⟨⟩]] and the tail at the moved
    family [posMv]. Related positions are related at [Fin] ([PosRel_LRtm]),
    which the child index premise needs. *)
From DeLaM.Validity Require Export Wf DVec.
From DeLaM.LogRel Require Import IWfAux.
From DeLaM.Typing Require Import Inversion.

Lemma subst_lift2_ren_single2 (c : tm) d (r : rsub) a p :
  c[llift (llift d)]⟨rlift (rlift r)⟩[lsingle2 a p] = c[lcons (lcons (lren d r) a) p].
Proof.
  rewrite subst_ren_lren, (subst_subst _ _ _ (lcons (lcons (lren d r) a) p)); [reflexivity|].
  intros [|[|n]]; rewrite llk_lren, !llk_llift; cbn; try reflexivity.
  change (ren_tm ?x ?y) with x⟨y⟩. change (ren_tm ?x ?y) with x⟨y⟩.
  rewrite !shift_lift, shift2_single2 by apply ren_nf. now rewrite llk_lren.
Qed.

Section S.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.
Lemma ktmll_subst_single2 {G Δ} (ρ : kwk G Δ) (c : tm) d a p :
  (ktmll ρ c[llift (llift d)])[lsingle2 a p] = c⟦kw_γ ρ⟧[lcons (lcons (kwsub ρ d) a) p].
Proof using .
  unfold ktmll. rewrite gwa_subst.
  rewrite (subst_ext _ (llift (llift d))⟦kw_γ ρ⟧ (llift (llift d⟦kw_γ ρ⟧))).
  - apply subst_lift2_ren_single2.
  - intros [|[|n]]; rewrite llk_gwa, !llk_llift; [now rewrite gwa_var| |].
    + cbn. now rewrite gwa_var.
    + cbn. change (ren_tm ?x ?r) with x⟨r⟩. change (ren_tm ?x ?r) with x⟨r⟩.
      now rewrite !gwa_ren, llk_gwa.
Qed.

Lemma shift_cons_ty (T : ty) d a : T⟨↑⟩[lcons d a] = T[d].
Proof using . apply ren_subst_ty; intros n; now rewrite rlk_shift1. Qed.

Lemma lift2shift_lift (C : tm) r : C⟨rlift (rlift ↑)⟩⟨rlift (rlift (rlift r))⟩ = C⟨rlift (rlift r)⟩⟨rlift (rlift ↑)⟩.
Proof using .
  rewrite !ren_ren_comp. apply ren_ext_tm; intros [|[|n]]; rlk_simpl; auto;
    destruct n; rlk_simpl; auto; lia.
Qed.

(** The children's family in a world. *)
Lemma ktyl_iwfFamT {G Δ} (ρ : kwk G Δ) l li X A N Ot C c :
  ktyl ρ (iwfFamT l li X A N Ot C c) =
  iwfFamT l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktml ρ c).
Proof using .
  unfold iwfFamT, ktyl, kty, ktml, ktmll. rewrite gwa_tyIWf, !gwa_ren_ty, !gwa_ren. cbn.
  now rewrite shift_lift_ty, shift_lift_ty, liftshift_lift, liftshift_lift, lift2shift_lift.
Qed.

(** Related positions are related at [Fin]. *)
Lemma PosRel_LRtm {G Δ k k' p p'} : PosRel G Δ k k' p p' -> NatRel G Δ k k' ->
  LRtm lzero G Δ (tyFin k) (tyFin k') p p'.
Proof using EL VL VN.
  induction 1 as [k k' m m' Hk Hk' Hmm | k k' m m' p p' Hk Hk' _ IH | k k' p p' Ek Hp]; intros Hkk.
  - destruct (NatRel_escape Hmm) as (Hm & _ & _).
    pose proof (LRtm_fin_inl (LR_fin_nat (ctx_of_tm Hm) Hmm)) as X.
    exact (LRtm_red_ty X (tyred_fin Hk) (tyred_fin Hk')).
  - destruct (NatRel_inv_succ Hkk Hk) as (m2 & Hk2 & Hm2).
    assert (Es : succ m2 = succ m') by (eapply tmred_whnf_det; [exact Hk2 | exact Hk' | constructor ..]).
    injection Es as ->.
    exact (LRtm_red_ty (LRtm_fin_inr (IH Hm2)) (tyred_fin Hk) (tyred_fin Hk')).
  - destruct (LR_fin_nat (ctx_of_tm (gne_tm_typed_l Hp)) Hkk) as [R HR].
    exists R. split; [exact HR|].
    apply (LR_neutral _ _ _ _ _ _ _ HR); [exact Hp |].
    eapply gne_tm_conv; [exact Hp | apply eqty_fin; [exact ge_notV | exact Ek]].
Qed.

(** ** Formation *)

Section IWfTy.
Context {G : gctx} {Γ : ctx} {l li l' li' : lvl} {X X' A A' : ty} {N N' Ot Ot' C C' m m' : tm}
  (Hwl : lwf (gL G) l) (Hwli : lwf (gL G) li) (Hl' : lequiv (gL G) l' l) (Hli' : lequiv (gL G) li' li)
  (VX : VTyG G Γ X X' li) (VA : VTyG G Γ A A' l)
  (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (VO : VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li)
  (VC : VTmG G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li)
  (Vm : VTm G Γ m m' X li).

Let K := lmeasure (lmax l li).
Lemma K_l : lmeasure l <= K.
Proof using li. unfold K; rewrite lmeasure_max; lia. Qed.
Lemma K_li : lmeasure li <= K.
Proof using l. unfold K; rewrite lmeasure_max; lia. Qed.

(** The index type's and the shapes' relations, in every world. *)
Definition iwfIdx Δ d d' : DomRel G Δ :=
  fun ρ => LRrel K (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X'[d']) li.
Definition iwfDom Δ d d' : DomRel G Δ :=
  fun ρ => LRrel K (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']) l.

Lemma iwfIdx_canon {Δ d d'} : SubRel G Γ Δ d d' ->
  forall ρ : kwk G Δ, LR K (LRbelow K) (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X'[d']) li (iwfIdx Δ d d' ρ).
Proof using EL VL VX.
  intros Hd ρ. destruct (VTyG_kw ρ VX Hd) as [R HR].
  exact (LR_canon _ _ _ _ _ _ _ (LogRel_up K_li HR)).
Qed.
Lemma iwfDom_canon {Δ d d'} : SubRel G Γ Δ d d' ->
  forall ρ : kwk G Δ, LR K (LRbelow K) (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']) l (iwfDom Δ d d' ρ).
Proof using EL VA VL.
  intros Hd ρ. destruct (VTyG_kw ρ VA Hd) as [R HR].
  exact (LR_canon _ _ _ _ _ _ _ (LogRel_up K_l HR)).
Qed.

(** A term related at the left index type, related by the index relation. *)
Lemma iwfIdx_of {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) x x' :
  LRtm li (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X[d']) x x' -> iwfIdx Δ d d' ρ x x'.
Proof using EL VL VX.
  intros Hx. unfold iwfIdx. apply (LRtm_stage K_li).
  eapply LRtm_irrel_r; [exact Hx | exact (VTyG_kw ρ VX Hd)].
Qed.

(** Related shapes in a world, at the left shape type. *)
Lemma iwfDom_at {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) a a' : iwfDom Δ d d' ρ a a' ->
  LRtm l (kw_G ρ) (kw_Δ ρ) A⟦kw_γ ρ⟧[kwsub ρ d] A⟦kw_γ ρ⟧[kwsub ρ d'] a a'.
Proof using EL VA VL.
  intros ha. pose proof (SubRel_kw _ _ _ ρ _ _ Hd) as Hdρ.
  unfold iwfDom in ha. apply (LRtm_stage K_l) in ha. rewrite !kty_subst in ha.
  eapply LRtm_irrel_r; [exact ha|]. exact (VTy_refl_l (VA _ _ (kw_gok ρ)) _ _ _ Hdρ).
Qed.

Lemma iwf_arity {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) a a' : iwfDom Δ d d' ρ a a' ->
  NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'].
Proof using EL VA VL VNt.
  intros ha. pose proof (iwfDom_at Hd ρ a a' ha) as Ha. pose proof (SubRel_kw _ _ _ ρ _ _ Hd) as Hdρ.
  pose proof (VNt _ _ (kw_gok ρ)) as VNρ. rewrite gwa_cext in VNρ.
  pose proof (VNρ _ _ _ (SubRel_cons Hdρ Ha)) as Y.
  rewrite <- !ktml_subst_single, gwa_tyNat, subst_tyNat in Y.
  exact (proj1 LRtm_nat Y).
Qed.

Lemma iwf_ot {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) a a' : iwfDom Δ d d' ρ a a' ->
  iwfIdx Δ d d' ρ (ktml ρ Ot[llift d])[lsingle a] (ktml ρ Ot'[llift d'])[lsingle a'].
Proof using EL VA VL VO VX.
  intros ha. pose proof (iwfDom_at Hd ρ a a' ha) as Ha. pose proof (SubRel_kw _ _ _ ρ _ _ Hd) as Hdρ.
  pose proof (VO _ _ (kw_gok ρ)) as VOρ. rewrite gwa_cext in VOρ.
  pose proof (VOρ _ _ _ (SubRel_cons Hdρ Ha)) as Y.
  rewrite <- !ktml_subst_single, gwa_ren_ty, !shift_cons_ty, <- !kty_subst in Y.
  exact (iwfIdx_of Hd ρ _ _ Y).
Qed.

Lemma iwf_ch {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) a a' : iwfDom Δ d d' ρ a a' ->
  forall p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'] p p' ->
  iwfIdx Δ d d' ρ (ktmll ρ C[llift (llift d)])[lsingle2 a p] (ktmll ρ C'[llift (llift d')])[lsingle2 a' p'].
Proof using EL VA VC VL VN VNt VX.
  intros ha p p' Hp. pose proof (iwfDom_at Hd ρ a a' ha) as Ha. pose proof (SubRel_kw _ _ _ ρ _ _ Hd) as Hdρ.
  pose proof (PosRel_LRtm Hp (iwf_arity Hd ρ a a' ha)) as Xp. rewrite !ktml_subst_single in Xp.
  pose proof (VTmG_refl_l VNt _ _ (kw_gok ρ)) as VNρ. rewrite gwa_cext in VNρ.
  pose proof (VNρ _ _ _ (SubRel_cons Hdρ Ha)) as YN. rewrite gwa_tyNat, !subst_tyNat in YN.
  apply (proj1 LRtm_nat) in YN.
  pose proof (LR_fin_nat (ctx_of_tm (proj1 (NatRel_escape YN))) YN) as HF.
  assert (Xp' : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin N⟦kw_γ ρ⟧)[lcons (kwsub ρ d) a] (tyFin N⟦kw_γ ρ⟧)[lcons (kwsub ρ d') a'] p p').
  { rewrite !subst_tyFin. eapply LRtm_irrel_r; [exact Xp | exact HF]. }
  pose proof (VC _ _ (kw_gok ρ)) as VCρ. rewrite !gwa_cext, gwa_tyFin in VCρ.
  pose proof (VCρ _ _ _ (SubRel_cons (SubRel_cons Hdρ Ha) Xp')) as Y.
  rewrite <- !ktmll_subst_single2, !gwa_ren_ty, !shift_cons_ty, <- !kty_subst in Y.
  exact (iwfIdx_of Hd ρ _ _ Y).
Qed.

(** The formers at related indices, at a related substitution. *)
Lemma LR_IWf_at Δ d d' mm mm' : SubRel G Γ Δ d d' -> LRtm li G Δ X[d] X[d'] mm mm' ->
  LogRel (lmax l li) G Δ (tyIWf l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] mm)
    (tyIWf l' li' X'[d'] A'[d'] N'[llift d'] Ot'[llift d'] C'[llift (llift d')] mm') (lmax l li)
    (IWfRel G Δ l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] (iwfIdx Δ d d') (iwfDom Δ d d') mm).
Proof using EL Hl' Hli' Hwl Hwli VA VC VL VN VNt VO VX.
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
  pose proof (VTmG_loc VC _ _ _ Hlift2) as XC. rewrite subst_tyFin, !shift_llift_ty in XC.
  destruct (LRtm_escape XC) as [HCd HC'd]. pose proof (LRtm_geq XC) as EC.
  destruct (LRtm_escape Xm) as [Hmd Hm'd]. pose proof (LRtm_geq Xm) as Em.
  assert (HE : IWfEq (G := G) (i := ge_layer) Δ l li l' li' X[d] X'[d'] A[d] A'[d'] N[llift d] N'[llift d']
                 Ot[llift d] Ot'[llift d'] C[llift (llift d)] C'[llift (llift d')]).
  { apply IWfEq_intro; auto using geq_ty_sound, geq_tm_sound, lequiv_sym. }
  assert (HE0 : IWfEq (G := G) (i := ge_layer) Δ l li l li X[d] X'[d'] A[d] A'[d'] N[llift d] N'[llift d']
                 Ot[llift d] Ot'[llift d'] C[llift (llift d)] C'[llift (llift d')]).
  { apply IWfEq_intro; auto using geq_ty_sound, geq_tm_sound, lequiv_refl. }
  destruct (IWfEq_sig_r ge_typeof ge_notV HE0) as (_ & _ & HX'r & HA'r & HN'r & HO'r & HC'r).
  pose proof (proj1 (proj2 (proj2 HE))) as HS.
  eapply LRiwf with (l1 := l) (li1 := li) (idxR := iwfIdx Δ d d') (domR := iwfDom Δ d d').
  - apply lequiv_refl, lwf_max; assumption.
  - exact Hl'.
  - exact Hli'.
  - exact Hwl.
  - exact Hwli.
  - apply tyred_refl, (IWf_ty_wf ge_typeof ge_notV HS Hmd).
  - apply tyred_refl, (pre_iwf_r ge_typeof ge_notV HE Hm'd).
  - exact HXd.
  - exact HX'r.
  - exact HAd.
  - exact HA'r.
  - exact HNd.
  - exact HN'r.
  - exact HOd.
  - exact HO'r.
  - exact HCd.
  - exact HC'r.
  - exact Hmd.
  - eapply wf_conv; [exact Hm'd | rewrite ge_typeof; apply eqty_sym, geq_ty_sound, EX].
  - exact EX.
  - exact EA.
  - exact EN.
  - exact EO.
  - exact EC.
  - exact Em.
  - exact (iwfIdx_canon Hd).
  - intros ρ x y H. exact (proj1 (LR_tm_per _ _ _ _ _ _ _ (iwfIdx_canon Hd ρ)) _ _ H).
  - intros ρ x y z H1 H2. exact (proj2 (LR_tm_per _ _ _ _ _ _ _ (iwfIdx_canon Hd ρ)) _ _ _ H1 H2).
  - exact (iwfDom_canon Hd).
  - intros ρ a a' ha. exact (iwf_arity Hd ρ a a' ha).
  - intros ρ a a' ha. exact (iwf_ot Hd ρ a a' ha).
  - intros ρ a a' ha p p' Hp. exact (iwf_ch Hd ρ a a' ha p p' Hp).
  - intros ρ. exact (iwfIdx_of Hd ρ _ _ (LRtm_kw ρ Xm)).
  - apply releq_refl.
Qed.

Lemma LR_IWf_here Δ d d' : SubRel G Γ Δ d d' ->
  LogRel (lmax l li) G Δ (tyIWf l li X A N Ot C m)[d] (tyIWf l' li' X' A' N' Ot' C' m')[d'] (lmax l li)
    (IWfRel G Δ l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] (iwfIdx Δ d d') (iwfDom Δ d d') m[d]).
Proof using EL Hl' Hli' Hwl Hwli VA VC VL VN VNt VO VX Vm. intros Hd. rewrite !subst_tyIWf. exact (LR_IWf_at Δ d d' _ _ Hd (Vm _ _ _ Hd)). Qed.

Lemma V_iwf : VTy G Γ (tyIWf l li X A N Ot C m) (tyIWf l' li' X' A' N' Ot' C' m') (lmax l li).
Proof using EL Hl' Hli' Hwl Hwli VA VC VL VN VNt VO VX Vm. intros Δ d d' Hd. eexists. exact (LR_IWf_here _ _ _ Hd). Qed.

End IWfTy.

(** ** Canonical index and shape relations

    As [WfDom], at the stage of the [IWf] type's level: the relations of
    derivations at the left index and shape types in every world. *)
Definition KDom G Δ n l A (d : DomRel G Δ) :=
  forall ρ : kwk G Δ, exists A1, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A) A1 l (d ρ).

Lemma KDom_comp {G Δ n l A} {d : DomRel G Δ} (ρ : kwk G Δ) : KDom G Δ n l A d ->
  KDom (kw_G ρ) (kw_Δ ρ) n l (kty ρ A) (fun ρ' => d (kw_comp ρ ρ')).
Proof using . intros H ρ'. destruct (H (kw_comp ρ ρ')) as [A1 Y]. rewrite kty_comp in Y. eauto. Qed.

Lemma KDom_releq {G Δ n l A} {d1 d2 : DomRel G Δ} : KDom G Δ n l A d1 -> KDom G Δ n l A d2 ->
  forall ρ, releq (d1 ρ) (d2 ρ).
Proof using EL VL.
  intros H1 H2 ρ. destruct (H1 ρ) as [A1 Y1]. destruct (H2 ρ) as [A2 Y2].
  exact (LR_irrel _ _ _ _ _ _ _ _ _ _ Y1 Y2).
Qed.

Lemma LR_iwf_rel {G Δ l li X A N Ot C c T' R} {ix dm : DomRel G Δ} :
  LogRel (lmax l li) G Δ (tyIWf l li X A N Ot C c) T' (lmax l li) R ->
  KDom G Δ (lmeasure (lmax l li)) li X ix -> KDom G Δ (lmeasure (lmax l li)) l A dm ->
  releq R (IWfRel G Δ l li X A N Ot C ix dm c).
Proof using EL VL.
  intros H HX HA. destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HW & _ & _).
  destruct (LR_inv_iwf H (tyred_refl _ _ HW))
    as (k2 & ki2 & X' & A' & N' & Ot' & C' & m' & idxR & domR
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & idxAd & _ & _ & domAd & _ & _ & _ & _ & HR).
  intros t t'. etransitivity; [apply HR|]. apply IWfRel_releq; intros ρ.
  - destruct (HX ρ) as [X1 Y]. exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (idxAd ρ) Y).
  - destruct (HA ρ) as [A1 Y]. exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (domAd ρ) Y).
Qed.

(** ** The children's spine *)

Section ISpine.
Context {G : gctx} {Δ : ctx} {l li : lvl} {X A : ty} {N Ot C : tm} {ix dm : DomRel G Δ}
  (HΔ : [ G ; Δ ⊢g ]) (HwL : lwf (gL G) (lmax l li))
  (NX : nfty X) (NA : nfty A) (NN : nftm N) (NO : nftm Ot) (NC : nftm C)
  (HX : KDom G Δ (lmeasure (lmax l li)) li X ix) (HA : KDom G Δ (lmeasure (lmax l li)) l A dm).

Let L := lmax l li.

Lemma fin_stab_ty {k w T L'} : [ G ; Δ ⊢g k ≅ w : tyNat @ lzero ] ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g T @ L' ] -> [ G ; Δ ,, tyFin w @ lzero ⊢g T @ L' ].
Proof using . intros Ek HT. exact (eqty_wf_l ge_typeof (fin_stab_eqty Ek (eqty_refl _ _ _ _ _ HT))). Qed.

(** Relation to spine, at the spine's own world. *)
Lemma DVecISp_of_LR : forall k k', NatRel G Δ k k' -> forall c,
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ L ] ->
  forall T' R, LogRel L G Δ (tyDVec L k (iwfFamT l li X A N Ot C c)) T' L R ->
  forall cs cs', R cs cs' -> DVecISp G Δ l li X A N Ot C ix dm c k cs cs'.
Proof using EL HA HX HwL HΔ NA NC NN NO NX VL.
  apply (NatRel_mut G Δ
    (fun k k' _ => forall c, [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ L ] ->
       forall T' R, LogRel L G Δ (tyDVec L k (iwfFamT l li X A N Ot C c)) T' L R ->
       forall cs cs', R cs cs' -> DVecISp G Δ l li X A N Ot C ix dm c k cs cs')
    (fun w w' _ => forall k, [ G ; Δ ⊢g k ⤳* w : tyNat @ lzero ] -> forall c,
       [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ L ] ->
       forall T' R, LogRel L G Δ (tyDVec L k (iwfFamT l li X A N Ot C c)) T' L R ->
       forall cs cs', R cs cs' -> DVecISp G Δ l li X A N Ot C ix dm c k cs cs')).
  - intros t t' w w' Ht _ _ _ IH. exact (IH t Ht).
  - intros k Hk c HF T' R H cs cs' Hcs.
    pose proof (fin_stab_ty (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF0.
    assert (Hred : [ G ; Δ ⊢g tyDVec L k (iwfFamT l li X A N Ot C c) ⤳* tyUnit L @ L ])
      by (eapply tyred_trans; [exact (tyred_dvec HwL HF Hk) | exact (tyred_dvec_zero HwL HF0)]).
    destruct (LR_inv_unit H Hred) as (l2 & _ & _ & _ & _ & HR).
    eapply visp_zero; [exact Hk | exact (proj1 (HR _ _) Hcs)].
  - intros m m' Hmm IH k Hk c HF T' R H cs cs' Hcs.
    destruct (NatRel_escape Hmm) as (Hm & _ & _). pose proof (wf_tm_nf Hm) as Nm.
    pose proof (fin_stab_ty (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF1.
    set (F := iwfFamT l li X A N Ot C c) in *.
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
    unfold F in DOM. rewrite iwfFamT_single in DOM by assumption.
    pose proof (LR_iwf_rel DOM HX HA) as RD.
    eapply visp_succ; [exact Hk | exact Hr | eapply tmred_conv; [apply ge_typeof | exact Hr' | exact EΣ]
                      | exact Nw | exact Nw' | exact Ew | |].
    + intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      destruct (Kι' la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1') as [h _].
      exact (proj1 (RD _ _) h).
    + intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      destruct (Kι' la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1') as [h Hc].
      pose proof (dvecMv_wf ge_typeof ge_notV ge_compt Hm HF1) as HFmv.
      assert (HDV : [ G ; Δ ⊢g tyDVec L m (dvecMv m F) @ L ])
        by (apply wft_dvec; [exact (compt_notV _ ge_compt) | exact HwL | exact Hm | exact HFmv]).
      pose proof (codAd (kid HΔ) _ _ h) as COD.
      rewrite dvec_cod_single, (kty_kid HΔ) in COD by exact (wf_ty_nf HDV).
      rewrite (ktyl_kid HΔ D') in COD by exact (wf_ty_nf HD').
      unfold F in COD. rewrite iwfFamT_mv in COD.
      refine (IH (posMv m c) _ _ _ COD _ _ Hc).
      rewrite <- iwfFamT_mv. exact HFmv.
  - intros ν ν' Hνν k Hk c HF T' R H cs cs' Hcs.
    pose proof (gne_tm_whne_l Hνν) as Nν.
    assert (Hred : [ G ; Δ ⊢g tyDVec L k (iwfFamT l li X A N Ot C c)
                     ⤳* tyDVec L ν (iwfFamT l li X A N Ot C c) @ L ])
      by exact (tyred_dvec HwL HF Hk).
    destruct (LR_inv_ne H Hred (whne_tyDVec _ _ _ Nν)) as (V' & _ & HVV & HR).
    eapply visp_ne; [exact Hk | exact (gne_tm_refl_l Hνν) |].
    eapply NeRel_conv2; [| | exact (proj1 (HR _ _) Hcs)].
    + apply eqty_refl. exact (eqty_wf_l ge_typeof (geq_ty_sound (gne_ty_geq HVV))).
    + apply eqty_sym, geq_ty_sound, gne_ty_geq, HVV.
Qed.

End ISpine.
(** ** [sup_i] *)

Lemma iwfFam_T l li X A N Ot C a : iwfFam l li X A N Ot C a = iwfFamT l li X A N Ot C C[llift (lsingle a)].
Proof using . reflexivity. Qed.

Section SupiV.
Context {G : gctx} {Γ : ctx} {l li l' li' : lvl} {X X' A A' : ty} {N N' Ot Ot' C C' a a' cs cs' : tm}
  (Hwl : lwf (gL G) l) (Hwli : lwf (gL G) li) (Hl' : lequiv (gL G) l' l) (Hli' : lequiv (gL G) li' li)
  (VX : VTyG G Γ X X' li) (VA : VTyG G Γ A A' l)
  (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (VO : VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li)
  (VC : VTmG G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li)
  (Va : VTm G Γ a a' A l)
  (Vcs : VTm G Γ cs cs' (tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a)) (lmax l li)).

(** The constructor's index. *)
Lemma V_supi_idx : VTm G Γ Ot[lsingle a] Ot[lsingle a] X li.
Proof using EL VL VO Va.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTm_trans Va (VTm_sym Va)) as Vaa.
  pose proof (VTmG_loc (VTmG_refl_l VO) _ _ _ (SubRel_cons Hd (Vaa _ _ _ Hd))) as Y.
  rewrite !shift_cons_ty in Y. rewrite !single_subst, !lift_single_tm by assumption. exact Y.
Qed.

(** The constructor's index on both sides, and its type. *)
Lemma V_supi_idx2 : VTm G Γ Ot[lsingle a] Ot'[lsingle a'] X li.
Proof using EL VO Va.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTmG_loc VO _ _ _ (SubRel_cons Hd (Va _ _ _ Hd))) as Y.
  rewrite !shift_cons_ty in Y. rewrite !single_subst, !lift_single_tm by assumption. exact Y.
Qed.

Lemma V_supi_ty : VTy G Γ (tyIWf l li X A N Ot C Ot[lsingle a]) (tyIWf l' li' X' A' N' Ot' C' Ot'[lsingle a'])
  (lmax l li).
Proof using EL Hl' Hli' Hwl Hwli VA VC VL VN VNt VO VX Va. exact (V_iwf Hwl Hwli Hl' Hli' VX VA VNt VO VC V_supi_idx2). Qed.

Lemma V_supi : VTm G Γ (tmSupi l li X A N Ot C a cs) (tmSupi l' li' X' A' N' Ot' C' a' cs')
  (tyIWf l li X A N Ot C Ot[lsingle a]) (lmax l li).
Proof using EL Hl' Hli' Hwl Hwli VA VC VL VN VNt VO VX Va Vcs.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd']. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (VTyG_refl_l VX) as VXX. pose proof (VTyG_refl_l VA) as VAA.
  pose proof (VTmG_refl_l VNt) as VNN. pose proof (VTmG_refl_l VO) as VOO. pose proof (VTmG_refl_l VC) as VCC.
  pose proof (LR_IWf_here Hwl Hwli (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwli) VXX VAA VNN VOO VCC V_supi_idx
                _ _ _ Hd) as HW.
  eapply LRtm_of; [exact HW|]. rewrite !subst_supi.
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
  pose proof (VTmG_loc VC _ _ _ Hlift2) as XC. rewrite subst_tyFin, !shift_llift_ty in XC.
  destruct (LRtm_escape XC) as [HCd HC'd]. pose proof (LRtm_geq XC) as EC.
  pose proof (Va _ _ _ Hd) as Xa. pose proof (LRtm_geq Xa) as Ea.
  pose proof (Vcs _ _ _ Hd) as Xcs.
  rewrite !subst_tyDVec, !single_subst, !subst_iwfFam in Xcs by assumption.
  pose proof (LRtm_geq Xcs) as Ecs.
  pose proof (geq_tm_supi (lequiv_sym _ _ _ Hl') (lequiv_sym _ _ _ Hli') HXd (geq_ty_sound EX) HAd (geq_ty_sound EA)
                HNd (geq_tm_sound EN) HOd (geq_tm_sound EO) HCd (geq_tm_sound EC) Ea Ecs) as Dsup.
  pose proof (geq_tm_sound Dsup) as Dsup'.
  rewrite single_subst by assumption.
  eapply iwfrel; [exact (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dsup'))
                 | exact (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Dsup')) | exact Dsup |].
  (* the related shapes, in every world *)
  assert (hdom : forall ρ : kwk G Δ, iwfDom (l := l) (li := li) (A := A) (A' := A) Δ d d' ρ (ktm ρ a[d]) (ktm ρ a'[d'])).
  { intros ρ. unfold iwfDom. apply (LRtm_stage K_l). exact (LRtm_kw ρ Xa). }
  apply iwfnf_sup.
  - exact (IWfEq_intro (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwli) (geq_ty_sound (geq_ty_refl_l EX))
             (geq_ty_sound (geq_ty_refl_l EA)) (geq_tm_sound (geq_tm_refl_l EN)) (geq_tm_sound (geq_tm_refl_l EO))
             (geq_tm_sound (geq_tm_refl_l EC)) Hwl Hwli HXd HAd HNd HOd HCd HXd HAd HNd HOd HCd).
  - apply IWfEq_intro; auto using geq_ty_sound, geq_tm_sound, lequiv_sym.
  - exact hdom.
  - intros ρ. rewrite ktm_single.
    pose proof (iwf_ot VXX VAA VOO Hd ρ _ _ (hdom ρ)) as Y.
    destruct (LR_tm_per _ _ _ _ _ _ _ (iwfIdx_canon (l := l) VXX Hd ρ)) as [Sy Tr].
    exact (Tr _ _ _ Y (Sy _ _ Y)).
  - intros ρ. destruct (LRtm_kw ρ Xcs) as (R & HR & Hc).
    rewrite kty_tyDVec, ktm_single, iwfFam_T, ktyl_iwfFamT, <- ktmll_llift_single in HR.
    destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HT & _ & _).
    destruct (inv_ty_dvec HT) as ((_ & _ & _ & HFam) & _).
    refine (DVecISp_of_LR (kw_ctx ρ) (kw_lwf ρ (lwf_max Hwl Hwli)) _ _ _ _ _
              (KDom_comp ρ (fun ρ0 => ex_intro _ _ (iwfIdx_canon (l := l) VXX Hd ρ0)))
              (KDom_comp ρ (fun ρ0 => ex_intro _ _ (iwfDom_canon (li := li) VAA Hd ρ0)))
              _ _ (iwf_arity (li := li) VAA VNN Hd ρ _ _ (hdom ρ)) _ HFam _ _ HR _ _ Hc).
    all: first [unfold kty; apply ren_nf_ty | unfold ktml; apply ren_nf | unfold ktmll; apply ren_nf].
Qed.

End SupiV.
End S.
