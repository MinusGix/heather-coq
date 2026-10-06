(** * Validity of finitary well-founded trees (M15_DESIGN.md, M15a)

    Formation of [Wf] and [sup_f]. The term relation at [Wf] is [WfRel]: a
    term reduces to a [sup_f] whose shapes are related and whose children are
    related by the spine [VecSp] in every weakening, or to a neutral. The
    spine is the relation at [Vec(Wf; k)] spelled out; two bridges relate it
    to the relation of any type derivation at that [Vec] type, by induction
    on the length's [NatRel]: relation to spine ([VecSp_of_LR], for
    [sup_f]'s validity) and spine to relation ([LR_of_VecSp], for
    [elim_Wf]'s step argument). The second needs the spine in every
    weakening, as [sup_f]'s premise provides it: the relation at a
    successor is [Σ]'s, whose projections are Kripke. *)
From DeLaM.Validity Require Export GLift.

Section Wf.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Formation *)

Section WfTy.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {A A' : ty} {N N' : tm}
  (Hwl : lwf (gL G) l) (Hl' : lequiv (gL G) l' l)
  (HN : [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ])
  (VA : VTyG G Γ A A' l) (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero).

(** The shapes' relation: the relation at the shape type, in every world. *)
Definition wfDom Δ d d' : DomRel G Δ :=
  fun ρ => LRrel (lmeasure l) (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']) l.

(** The arity at related shapes, in every world. *)
Lemma wf_arity {Δ d d'} (ρ : kwk G Δ) a a' : SubRel G Γ Δ d d' ->
  LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']) a a' ->
  NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N[llift d])[lsingle a] (ktml ρ N'[llift d'])[lsingle a'].
Proof.
  intros Hd ha. pose proof (SubRel_kw _ _ _ ρ _ _ Hd) as Hdρ.
  assert (Ha : LRtm l (kw_G ρ) (kw_Δ ρ) A⟦kw_γ ρ⟧[kwsub ρ d] A⟦kw_γ ρ⟧[kwsub ρ d'] a a').
  { rewrite !kty_subst in ha. eapply LRtm_irrel_r; [exact ha|].
    exact (VTy_refl_l (VA _ _ (kw_gok ρ)) _ _ _ Hdρ). }
  pose proof (VNt _ _ (kw_gok ρ)) as VNρ. rewrite gwa_cext in VNρ.
  pose proof (VNρ _ _ _ (SubRel_cons Hdρ Ha)) as X.
  rewrite <- !ktml_subst_single, gwa_tyNat, subst_tyNat in X.
  exact (proj1 LRtm_nat X).
Qed.

Lemma wfDom_canon {Δ d d'} : SubRel G Γ Δ d d' ->
  forall ρ : kwk G Δ, LogRel l (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']) l (wfDom Δ d d' ρ).
Proof.
  intros Hd ρ. unfold wfDom. destruct (VTyG_kw ρ VA Hd) as [R HR].
  exact (LR_canon _ _ _ _ _ _ _ HR).
Qed.

Lemma LR_Wf_here Δ d d' : SubRel G Γ Δ d d' ->
  LogRel l G Δ (tyWf l A N)[d] (tyWf l' A' N')[d'] l (WfRel G Δ l A[d] N[llift d] (wfDom Δ d d')).
Proof.
  intros Hd. pose proof (SubRel_ctx Hd) as HΔ.
  destruct (VTyG_loc VA _ _ _ Hd) as [RA HRA].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd & HAA).
  assert (HΔA' : [ G ; Δ ,, A'[d'] @ l ⊢g ]) by now apply ext_wf_g.
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact (VTy_refl_l (VTyG_loc VA)) | exact HAd | exact Hwl]).
  pose proof (VTmG_loc VNt _ _ _ Hlift) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HNd HN'd0].
  assert (HN'd : [ G ; Δ ,, A'[d'] @ l ⊢g N'[llift d'] : tyNat @ lzero ])
    by exact (stab_tm ge_typeof (geq_ty_sound HAA) (lequiv_refl _ _ Hwl) HΔA' HN'd0).
  pose proof (lequiv_wf_l _ _ _ Hl') as Hwl'.
  rewrite !subst_tyWf.
  eapply LRwf with (l1 := l) (l2 := l') (domR := wfDom Δ d d').
  - now apply lequiv_refl.
  - exact Hl'.
  - exact Hwl.
  - apply tyred_refl, wft_wf; auto using ge_compt.
  - eapply tyred_lconv; [apply tyred_refl, wft_wf; auto using ge_compt | exact (lequiv_sym _ _ _ Hl')].
    + exact (lconv_ty HA'd (lequiv_sym _ _ _ Hl')).
    + exact (ctx_lvl_tm HA'd (lequiv_sym _ _ _ Hl') HN'd).
  - exact HAd.
  - exact HA'd.
  - exact HNd.
  - exact HN'd.
  - exact HAA.
  - exact (LRtm_geq XN).
  - exact (wfDom_canon Hd).
  - intros ρ a a' ha. exact (wf_arity ρ a a' Hd ha).
  - apply releq_refl.
Qed.

Lemma V_wf : VTy G Γ (tyWf l A N) (tyWf l' A' N') l.
Proof. intros Δ d d' Hd. eexists. exact (LR_Wf_here _ _ _ Hd). Qed.

End WfTy.

(** ** The identity world *)

Section KId.
Context {G : gctx} {Δ : ctx} (HΔ : [ G ; Δ ⊢g ]).

Definition kid : kwk G Δ := kw_loc wk_id (wkwf_id Δ) HΔ.

Lemma kty_kid (T : ty) : nfty T -> kty kid T = T.
Proof. intros NT. unfold kty, kid, kw_loc; cbn [kw_γ kw_r gwa wk_ren]. now rewrite ren_id_ty. Qed.
Lemma ktm_kid (t : tm) : nftm t -> ktm kid t = t.
Proof. intros Nt. unfold ktm, kid, kw_loc; cbn [kw_γ kw_r gwa wk_ren]. now rewrite ren_id_tm. Qed.
Lemma ktyl_kid (T : ty) : nfty T -> ktyl kid T = T.
Proof.
  intros NT. unfold ktyl, kid, kw_loc; cbn [kw_γ kw_r gwa wk_ren].
  rewrite <- (ren_id_ty T NT) at 2. apply ren_ext_ty. intros n. rewrite rlk_rlift. destruct n; cbn; lia.
Qed.

End KId.

(** ** Canonical shape relations

    The spine's lemmas need the shapes' relation to be the relation of a
    derivation at the left shape type in every world, as [LRwf]'s premise
    makes it; then any two such relations agree, and so do the relations
    of any two derivations at a [Wf] type. *)
Definition WfDom G Δ l A (domR : DomRel G Δ) :=
  forall ρ : kwk G Δ, exists A1, LogRel l (kw_G ρ) (kw_Δ ρ) (kty ρ A) A1 l (domR ρ).

Lemma WfDom_comp {G Δ l A} {domR : DomRel G Δ} (ρ : kwk G Δ) : WfDom G Δ l A domR ->
  WfDom (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (fun ρ' => domR (kw_comp ρ ρ')).
Proof. intros H ρ'. destruct (H (kw_comp ρ ρ')) as [A1 X]. rewrite kty_comp in X. eauto. Qed.

Lemma WfDom_releq {G Δ l A} {d1 d2 : DomRel G Δ} : WfDom G Δ l A d1 -> WfDom G Δ l A d2 ->
  forall ρ, releq (d1 ρ) (d2 ρ).
Proof.
  intros H1 H2 ρ. destruct (H1 ρ) as [A1 X1]. destruct (H2 ρ) as [A2 X2].
  exact (LR_irrel _ _ _ _ _ _ _ _ _ _ X1 X2).
Qed.

Lemma WfDom_assoc {G Δ l A} {d : DomRel G Δ} (HD : WfDom G Δ l A d) (ρ : kwk G Δ)
  (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) ρ'' :
  releq (d (kw_comp (kw_comp ρ ρ') ρ'')) (d (kw_comp ρ (kw_comp ρ' ρ''))).
Proof.
  revert ρ''. apply (WfDom_releq (l := l) (A := kty ρ' (kty ρ A))); [|exact (WfDom_comp ρ' (WfDom_comp ρ HD))].
  intros ρ0. destruct (HD (kw_comp (kw_comp ρ ρ') ρ0)) as [A2 X2]. rewrite !kty_comp in X2. eauto.
Qed.

Lemma WfDom_of {G Δ l A A'} {domR : DomRel G Δ} :
  (forall ρ : kwk G Δ, LogRel l (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A') l (domR ρ)) -> WfDom G Δ l A domR.
Proof. intros H ρ. eauto. Qed.

Lemma LR_wf_rel {G Δ l A N T' R} {domR : DomRel G Δ} :
  LogRel l G Δ (tyWf l A N) T' l R -> WfDom G Δ l A domR -> releq R (WfRel G Δ l A N domR).
Proof.
  intros H HD. destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HW & _ & _).
  destruct (LR_inv_wf H (tyred_refl _ _ HW))
    as (m2 & C' & M' & domR' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & domAd & _ & HR).
  intros t t'. etransitivity; [apply HR|]. apply WfRel_releq.
  intros ρ. destruct (HD ρ) as [A1 X]. exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (domAd ρ) X).
Qed.

(** ** The spine and the relation at [Vec(Wf; k)] *)

Section Spine.
Context {G : gctx} {Δ : ctx} {l : lvl} {A : ty} {N : tm} {domR : DomRel G Δ}
  (Hwl : lwf (gL G) l) (HWf : [ G ; Δ ⊢g tyWf l A N @ l ]) (HD : WfDom G Δ l A domR).

(** Relation to spine, at the spine's own world. *)
Lemma VecSp_of_LR : forall k k', NatRel G Δ k k' ->
  forall T' R, LogRel l G Δ (tyVec l (tyWf l A N) k) T' l R ->
  forall cs cs', R cs cs' -> VecSp G Δ l A N domR k cs cs'.
Proof.
  pose proof (ctx_of_ty HWf) as HΔ. pose proof (wf_ty_nf HWf) as NW.
  apply (NatRel_mut G Δ
    (fun k k' _ => forall T' R, LogRel l G Δ (tyVec l (tyWf l A N) k) T' l R ->
       forall cs cs', R cs cs' -> VecSp G Δ l A N domR k cs cs')
    (fun w w' _ => forall k, [ G ; Δ ⊢g k ⤳* w : tyNat @ lzero ] ->
       forall T' R, LogRel l G Δ (tyVec l (tyWf l A N) k) T' l R ->
       forall cs cs', R cs cs' -> VecSp G Δ l A N domR k cs cs')).
  - intros t t' w w' Ht _ _ _ IH. exact (IH t Ht).
  - intros k Hk T' R H cs cs' Hcs.
    assert (Hred : [ G ; Δ ⊢g tyVec l (tyWf l A N) k ⤳* tyUnit l @ l ])
      by (eapply tyred_trans; [exact (tyred_vec Hwl HWf Hk) | exact (tyred_vec_zero Hwl HWf)]).
    destruct (LR_inv_unit H Hred) as (l2 & _ & _ & _ & _ & HR).
    eapply vsp_zero; [exact Hk | exact (proj1 (HR _ _) Hcs)].
  - intros m m' Hmm IH k Hk T' R H cs cs' Hcs.
    destruct (NatRel_escape Hmm) as (Hm & _ & _). pose proof (wf_tm_nf Hm) as Nm.
    assert (Hred : [ G ; Δ ⊢g tyVec l (tyWf l A N) k
                     ⤳* tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ l ])
      by (eapply tyred_trans; [exact (tyred_vec Hwl HWf Hk) | exact (tyred_vec_succ Hwl HWf Hm)]).
    destruct (LR_inv_sig H Hred) as (m3 & m4 & C' & D' & dS & cS & P & domAd & codAd & HR).
    destruct P as [_ Hm3 Hm4 _ _ _ _ _ HC' HV HD' HWC HVD].
    apply HR in Hcs. destruct Hcs as (w & w' & Hr & Hr' & Nw & Nw' & Ew & _ & K).
    pose proof (wf_tm_nf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hr))) as Nw0.
    pose proof (wf_tm_nf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hr'))) as Nw0'.
    assert (EΣ : [ G ; Δ ⊢g tySig m3 m4 C' D' ≅ tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ lmax l l ])
      by (apply eqty_sym, geq_ty_sound, geq_ty_sig; auto using lequiv_sym).
    pose proof (K (kid HΔ)) as Kι.
    rewrite (kty_kid HΔ _ NW) in Kι.
    rewrite (ktyl_kid HΔ _ (wf_ty_nf HV)) in Kι.
    rewrite (kty_kid HΔ _ (wf_ty_nf HC')) in Kι.
    rewrite (ktyl_kid HΔ _ (wf_ty_nf HD')) in Kι.
    rewrite (ktm_kid HΔ _ Nw0), (ktm_kid HΔ _ Nw0') in Kι.
    assert (HΔC' : [ G ; Δ ,, C' @ l ⊢g ]) by exact (ext_wf_g HC' Hwl).
    assert (Kι' : forall la lb A1 B1 la' lb' A1' B1',
              lequiv (gL G) la l -> lequiv (gL G) lb l -> lequiv (gL G) la' l -> lequiv (gL G) lb' l ->
              [ G ; Δ ⊢ tyWf l A N ≈ A1 @ l ] ->
              [ G ; Δ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1 @ l ] ->
              [ G ; Δ ⊢ tyWf l A N ≈ A1' @ l ] ->
              [ G ; Δ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1' @ l ] ->
              exists h : dS (kid HΔ) (tmFst la lb A1 B1 w) (tmFst la' lb' A1' B1' w'),
                cS (kid HΔ) _ _ h (tmSnd la lb A1 B1 w) (tmSnd la' lb' A1' B1' w')).
    { intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      apply (Kι la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1).
      - exact (geq_ty_trans (geq_ty_sym HWC) HA1').
      - eapply geq_ty_ctxconv; [exact (geq_ty_sound HWC) | now apply lequiv_refl | exact HΔC' |].
        exact (geq_ty_trans (geq_ty_sym HVD) HB1'). }
    pose proof (domAd (kid HΔ)) as DOM. rewrite (kty_kid HΔ), (kty_kid HΔ C') in DOM by first [exact NW | exact (wf_ty_nf HC')].
    pose proof (LR_wf_rel DOM HD) as RD.
    eapply vsp_succ; [exact Hk | exact Hr | eapply tmred_conv; [apply ge_typeof | exact Hr' | exact EΣ]
                     | exact Nw | exact Nw' | exact Ew | |].
    + intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      destruct (Kι' la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1') as [h _].
      exact (proj1 (RD _ _) h).
    + intros la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      destruct (Kι' la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1') as [h Hc].
      pose proof (codAd (kid HΔ) _ _ h) as COD.
      rewrite vec_cod_single, (kty_kid HΔ), (ktm_kid HΔ) in COD by assumption.
      rewrite (ktyl_kid HΔ D') in COD by exact (wf_ty_nf HD').
      exact (IH _ _ COD _ _ Hc).
  - intros ν ν' Hνν k Hk T' R H cs cs' Hcs.
    pose proof (gne_tm_whne_l Hνν) as Nν.
    assert (Hred : [ G ; Δ ⊢g tyVec l (tyWf l A N) k ⤳* tyVec l (tyWf l A N) ν @ l ])
      by exact (tyred_vec Hwl HWf Hk).
    destruct (LR_inv_ne H Hred (whne_tyVec _ _ _ Nν)) as (V' & _ & HVV & HR).
    eapply vsp_ne; [exact Hk | exact (gne_tm_refl_l Hνν) |].
    eapply NeRel_conv2; [| | exact (proj1 (HR _ _) Hcs)].
    + apply eqty_refl. exact (eqty_wf_l ge_typeof (geq_ty_sound (gne_ty_geq HVV))).
    + apply eqty_sym, geq_ty_sound, gne_ty_geq, HVV.
Qed.

End Spine.

(** ** The spine in every world, and the relation at [Vec(Wf; k)] *)

Lemma ktyl_vecsh {G Γ} (ρ : kwk G Γ) l (T : ty) (m : tm) :
  ktyl ρ (tyVec l T⟨↑⟩ m⟨↑⟩) = tyVec l (kty ρ T)⟨↑⟩ (ktm ρ m)⟨↑⟩.
Proof.
  transitivity (tyVec l (ktyl ρ T⟨↑⟩) (ktml ρ m⟨↑⟩)).
  { unfold ktyl, ktml. now rewrite gwa_tyVec, ren_tyVec. }
  now rewrite ktyl_shift, ktml_shift.
Qed.

(** A spine at a successor, at given whnfs of its tuples. *)
Lemma VecSp_succ_at {G Γ l A N d k m cs cs' w w' T T' l0 l0'} : VecSp G Γ l A N d k cs cs' ->
  [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  [ G ; Γ ⊢g cs ⤳* w : T @ l0 ] -> whnf w -> [ G ; Γ ⊢g cs' ⤳* w' : T' @ l0' ] -> whnf w' ->
    (forall la lb A1 B1 la' lb' A1' B1',
       lequiv (gL G) la l -> lequiv (gL G) lb l -> lequiv (gL G) la' l -> lequiv (gL G) lb' l ->
       [ G ; Γ ⊢ tyWf l A N ≈ A1 @ l ] ->
       [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1 @ l ] ->
       [ G ; Γ ⊢ tyWf l A N ≈ A1' @ l ] ->
       [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1' @ l ] ->
       WfRel G Γ l A N d (tmFst la lb A1 B1 w) (tmFst la' lb' A1' B1' w')) /\
    (forall la lb A1 B1 la' lb' A1' B1',
       lequiv (gL G) la l -> lequiv (gL G) lb l -> lequiv (gL G) la' l -> lequiv (gL G) lb' l ->
       [ G ; Γ ⊢ tyWf l A N ≈ A1 @ l ] ->
       [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1 @ l ] ->
       [ G ; Γ ⊢ tyWf l A N ≈ A1' @ l ] ->
       [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1' @ l ] ->
       VecSp G Γ l A N d m (tmSnd la lb A1 B1 w) (tmSnd la' lb' A1' B1' w')).
Proof.
  intros H Hk Hr Nw Hr' Nw'.
  destruct (VecSp_succ_inv H Hk) as (w0 & w0' & Hr0 & Hr0' & Nw0 & Nw0' & _ & Hf & Hs).
  assert (w0 = w) as -> by (eapply tmred_whnf_det; [exact Hr0 | exact Hr | exact Nw0 | exact Nw]).
  assert (w0' = w') as -> by (eapply tmred_whnf_det; [exact Hr0' | exact Hr' | exact Nw0' | exact Nw']).
  exact (conj Hf Hs).
Qed.

(** The spine at its own world and in every weakening, as [sup_f]'s premise
    provides it. *)
Definition KSp G Δ l A N (d : DomRel G Δ) k cs cs' :=
  VecSp G Δ l A N d k cs cs' /\
  forall ρ : kwk G Δ, VecSp (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => d (kw_comp ρ ρ'))
                       (ktm ρ k) (ktm ρ cs) (ktm ρ cs').

(** Spine to relation, at a length [k], in a world. *)
Definition VecQ G Δ l A N (d : DomRel G Δ) k :=
  forall T' R, LogRel l G Δ (tyVec l (tyWf l A N) k) T' l R ->
  forall cs cs', KSp G Δ l A N d k cs cs' -> R cs cs'.

Lemma VecQ_zero {G Δ l A N} {d : DomRel G Δ} {k} : lwf (gL G) l -> [ G ; Δ ⊢g tyWf l A N @ l ] ->
  [ G ; Δ ⊢g k ⤳* zero : tyNat @ lzero ] -> VecQ G Δ l A N d k.
Proof.
  intros Hwl HWf Hk T' R H cs cs' [Hown _].
  assert (Hred : [ G ; Δ ⊢g tyVec l (tyWf l A N) k ⤳* tyUnit l @ l ])
    by (eapply tyred_trans; [exact (tyred_vec Hwl HWf Hk) | exact (tyred_vec_zero Hwl HWf)]).
  destruct (LR_inv_unit H Hred) as (l2 & _ & _ & _ & _ & HR).
  exact (proj2 (HR _ _) (VecSp_zero_inv Hown Hk)).
Qed.

Lemma VecQ_ne {G Δ l A N} {d : DomRel G Δ} {k ν} : lwf (gL G) l -> [ G ; Δ ⊢g tyWf l A N @ l ] ->
  [ G ; Δ ⊢g k ⤳* ν : tyNat @ lzero ] -> whne ν -> VecQ G Δ l A N d k.
Proof.
  intros Hwl HWf Hk Nν T' R H cs cs' [Hown _].
  destruct (LR_inv_ne H (tyred_vec Hwl HWf Hk) (whne_tyVec _ _ _ Nν)) as (V' & _ & HVV & HR).
  apply (proj2 (HR _ _)).
  eapply NeRel_conv2; [| | exact (VecSp_ne_inv Hown Hk Nν)].
  - apply eqty_refl. exact (eqty_wf_l ge_typeof (geq_ty_sound (gne_ty_geq HVV))).
  - apply geq_ty_sound, gne_ty_geq, HVV.
Qed.

Lemma VecQ_succ {G Δ l A N} {d : DomRel G Δ} {k m} : lwf (gL G) l -> [ G ; Δ ⊢g tyWf l A N @ l ] ->
  WfDom G Δ l A d -> [ G ; Δ ⊢g m : tyNat @ lzero ] -> [ G ; Δ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  (forall ρ : kwk G Δ, VecQ (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => d (kw_comp ρ ρ')) (ktm ρ m)) ->
  VecQ G Δ l A N d k.
Proof.
  intros Hwl HWf HD Hm Hk IH T' R H cs cs' [Hown HK].
  pose proof (ctx_of_ty HWf) as HΔ.
  assert (Hred : [ G ; Δ ⊢g tyVec l (tyWf l A N) k
                   ⤳* tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ l ])
    by (eapply tyred_trans; [exact (tyred_vec Hwl HWf Hk) | exact (tyred_vec_succ Hwl HWf Hm)]).
  destruct (LR_inv_sig H Hred) as (m3 & m4 & C' & D' & dS & cS & P & domAd & codAd & HR).
  destruct P as [_ Hm3 Hm4 _ _ _ _ _ HC' HV HD' HWC HVD].
  apply HR.
  destruct (VecSp_succ_inv Hown Hk) as (w & w' & Hr & Hr' & Nw & Nw' & Ew & _ & _).
  assert (EΣ : [ G ; Δ ⊢g tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) ≅ tySig m3 m4 C' D' @ lmax l l ])
    by (apply geq_ty_sound, geq_ty_sig; auto using lequiv_sym).
  exists w, w'. refine (conj Hr (conj _ (conj Nw (conj Nw' (conj Ew (conj _ _)))))).
  - eapply tmred_conv; [apply ge_typeof | exact Hr' | exact EΣ].
  - exact (geq_tm_conv Ew EΣ).
  - intros ρ la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
    pose proof (kw_lwf ρ Hwl) as Hwlρ.
    (* the annotations, at the spine's types in the world *)
    pose proof (kw_geq_ty ρ HWC) as KC. pose proof (kw_geq_ty_l ρ HWf Hwl HVD) as KD.
    pose proof (kw_ty ρ HC') as HC'ρ.
    assert (HA1'x : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ (tyWf l A N) ≈ A1' @ l ]) by exact (geq_ty_trans KC HA1').
    assert (HB1'x : [ kw_G ρ ; kw_Δ ρ ,, kty ρ (tyWf l A N) @ l
                      ⊢ ktyl ρ (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) ≈ B1' @ l ]).
    { eapply geq_ty_trans; [exact KD|].
      eapply geq_ty_ctxconv; [apply eqty_sym, geq_ty_sound, KC | now apply lequiv_refl
                             | apply ext_wf_g; [exact (kw_ty ρ HWf) | exact Hwlρ] | exact HB1']. }
    rewrite (ktyl_vecsh ρ) in HB1, HB1'x. rewrite !kty_tyWf in HA1, HB1, HA1'x, HB1'x.
    (* the spine in the world, at the weakened whnfs *)
    pose proof (kw_tmred ρ Hk) as Hkρ. rewrite ktm_succ, kty_tyNat in Hkρ.
    pose proof (kw_tmred ρ Hr) as Hrρ. pose proof (kw_tmred ρ Hr') as Hrρ'.
    destruct (VecSp_succ_at (HK ρ) Hkρ Hrρ (whnf_kw ρ _ Nw) Hrρ' (whnf_kw ρ _ Nw')) as [Hf Hs].
    (* the first projections, in [Σ]'s domain relation *)
    pose proof (domAd ρ) as DOM. rewrite kty_tyWf in DOM.
    pose proof (LR_wf_rel DOM (WfDom_comp ρ HD)) as RD.
    pose proof (kw_lequiv ρ H1) as J1. pose proof (kw_lequiv ρ H2) as J2.
    pose proof (kw_lequiv ρ H1') as J1'. pose proof (kw_lequiv ρ H2') as J2'.
    pose proof (Hf la lb A1 B1 la' lb' A1' B1' J1 J2 J1' J2' HA1 HB1 HA1'x HB1'x) as F.
    exists (proj2 (RD _ _) F).
    (* the second projections, in [Σ]'s codomain relation, by the induction hypothesis *)
    pose proof (codAd ρ _ _ (proj2 (RD _ _) F)) as COD.
    rewrite vec_cod_single, kty_tyWf in COD.
    apply (IH ρ _ _ COD). split.
    + exact (Hs la lb A1 B1 la' lb' A1' B1' J1 J2 J1' J2' HA1 HB1 HA1'x HB1'x).
    + intros ρ'. rewrite !ktm_snd.
      pose proof (HK (kw_comp ρ ρ')) as Y.
      rewrite kty_comp, ktml_comp, !ktm_comp in Y.
      pose proof (kw_tmred ρ' Hkρ) as Hkρ'. rewrite ktm_succ, kty_tyNat in Hkρ'.
      pose proof (kw_tmred ρ' Hrρ) as Hrρ2. pose proof (kw_tmred ρ' Hrρ') as Hrρ2'.
      destruct (VecSp_succ_at Y Hkρ' Hrρ2 (whnf_kw ρ' _ (whnf_kw ρ _ Nw)) Hrρ2' (whnf_kw ρ' _ (whnf_kw ρ _ Nw')))
        as [_ Hs'].
      pose proof (kw_lequiv ρ' J1) as K1. pose proof (kw_lequiv ρ' J2) as K2.
      pose proof (kw_lequiv ρ' J1') as K1'. pose proof (kw_lequiv ρ' J2') as K2'.
      pose proof (kw_ty ρ HWf) as HWfρ. rewrite kty_tyWf in HWfρ.
      pose proof (kw_geq_ty ρ' HA1) as KA1. pose proof (kw_geq_ty_l ρ' HWfρ Hwlρ HB1) as KB1.
      pose proof (kw_geq_ty ρ' HA1'x) as KA1'. pose proof (kw_geq_ty_l ρ' HWfρ Hwlρ HB1'x) as KB1'.
      rewrite (ktyl_vecsh ρ') in KB1, KB1'. rewrite !kty_tyWf in KA1, KB1, KA1', KB1'.
      pose proof (Hs' la lb _ _ la' lb' _ _ K1 K2 K1' K2' KA1 KB1 KA1' KB1') as Z.
      eapply (proj2 (proj2 WfRel_dir_all)); [exact Z|].
      intros ρ''. exact (WfDom_assoc HD ρ ρ' ρ'').
Qed.

Section SpineK.
Context {G : gctx} {Δ : ctx} {l : lvl} {A : ty} {N : tm} {domR : DomRel G Δ}
  (Hwl : lwf (gL G) l) (HWf : [ G ; Δ ⊢g tyWf l A N @ l ]) (HD : WfDom G Δ l A domR).

(** Spine to relation: by induction on the length's [NatRel], in every
    world at once (a successor's [Σ] relates its projections in every
    weakening). *)
Lemma LR_of_VecSp_all : forall k k', NatRel G Δ k k' ->
  forall ρ : kwk G Δ, VecQ (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => domR (kw_comp ρ ρ')) (ktm ρ k).
Proof.
  apply (NatRel_mut G Δ
    (fun k k' _ => forall ρ : kwk G Δ,
       VecQ (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => domR (kw_comp ρ ρ')) (ktm ρ k))
    (fun w w' _ => forall k, [ G ; Δ ⊢g k ⤳* w : tyNat @ lzero ] -> forall ρ : kwk G Δ,
       VecQ (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => domR (kw_comp ρ ρ')) (ktm ρ k))).
  - intros t t' w w' Ht _ _ _ IH. exact (IH t Ht).
  - intros k Hk ρ. pose proof (kw_tmred ρ Hk) as Hkρ. rewrite ktm_zero, kty_tyNat in Hkρ.
    pose proof (kw_ty ρ HWf) as HWfρ. rewrite kty_tyWf in HWfρ.
    exact (VecQ_zero (kw_lwf ρ Hwl) HWfρ Hkρ).
  - intros m m' Hmm IH k Hk ρ. pose proof (kw_tmred ρ Hk) as Hkρ. rewrite ktm_succ, kty_tyNat in Hkρ.
    pose proof (kw_ty ρ HWf) as HWfρ. rewrite kty_tyWf in HWfρ.
    destruct (NatRel_escape Hmm) as (Hm & _ & _). pose proof (kw_tm ρ Hm) as Hmρ. rewrite kty_tyNat in Hmρ.
    apply (VecQ_succ (kw_lwf ρ Hwl) HWfρ (WfDom_comp ρ HD) Hmρ Hkρ).
    intros ρ' T' R H cs cs' HK.
    pose proof (IH (kw_comp ρ ρ')) as X. rewrite kty_comp, ktml_comp, ktm_comp in X.
    apply (X T' R H). destruct HK as [Hown HK]. split.
    + eapply (proj2 (proj2 WfRel_dir_all)); [exact Hown|].
      intros ρ0. apply releq_sym', (WfDom_assoc HD ρ ρ' ρ0).
    + intros ρ''. eapply (proj2 (proj2 WfRel_dir_all)); [exact (HK ρ'')|].
      intros ρ0. apply releq_sym', (WfDom_assoc HD ρ ρ' (kw_comp ρ'' ρ0)).
  - intros ν ν' Hνν k Hk ρ. pose proof (kw_tmred ρ Hk) as Hkρ. rewrite kty_tyNat in Hkρ.
    pose proof (kw_ty ρ HWf) as HWfρ. rewrite kty_tyWf in HWfρ.
    exact (VecQ_ne (kw_lwf ρ Hwl) HWfρ Hkρ (gne_tm_whne_l (kw_gne_tm ρ Hνν))).
Qed.

End SpineK.

(** ** [sup_f] *)

Lemma VTmG_refl_l {G Γ t t' T l} : VTmG G Γ t t' T l -> VTmG G Γ t t T l.
Proof. intros H. exact (VTmG_trans H (VTmG_sym H)). Qed.

Section SupfV.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {A A' : ty} {N N' a a' cs cs' : tm}
  (Hwl : lwf (gL G) l) (Hl' : lequiv (gL G) l' l)
  (HN : [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ])
  (VA : VTyG G Γ A A' l) (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (Va : VTm G Γ a a' A l) (Vcs : VTm G Γ cs cs' (tyVec l (tyWf l A N) N[lsingle a]) l).

Lemma V_supf : VTm G Γ (tmSupf l A N a cs) (tmSupf l' A' N' a' cs') (tyWf l A N) l.
Proof.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTyG_refl_l VA) as VAA. pose proof (VTmG_refl_l VNt) as VNN.
  pose proof (LR_Wf_here Hwl (lequiv_refl _ _ Hwl) VAA VNN _ _ _ Hd) as HW.
  eapply LRtm_of; [exact HW|]. rewrite !subst_supf.
  (* escapes *)
  destruct (VTyG_loc VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & _ & EA).
  assert (EAA : [ G ; Δ ⊢ A[d] ≈ A[d] @ l ]) by exact (geq_ty_trans EA (geq_ty_sym EA)).
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by exact (SubRel_lift Hd (VTy_refl_l (VTyG_loc VA)) HAd Hwl).
  pose proof (VTmG_loc VNt _ _ _ Hlift) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HNd _]. pose proof (LRtm_geq XN) as EN.
  pose proof (geq_tm_refl_l EN) as ENN.
  pose proof (Va _ _ _ Hd) as Xa. pose proof (LRtm_geq Xa) as Ea.
  pose proof (Vcs _ _ _ Hd) as Xcs. rewrite !subst_tyVec, !subst_tyWf, !single_subst in Xcs by assumption.
  pose proof (LRtm_geq Xcs) as Ecs.
  pose proof (geq_tm_supf (lequiv_sym _ _ _ Hl') HAd EA HNd EN Ea Ecs) as Dsup.
  pose proof (geq_tm_sound Dsup) as Dsup'.
  assert (HWd : [ G ; Δ ⊢g tyWf l A[d] N[llift d] @ l ]) by (apply wft_wf; auto using ge_compt).
  apply (wfrel _ _ _ _ _ _ _ _ (tmSupf l A[d] N[llift d] a[d] cs[d]) (tmSupf l' A'[d'] N'[llift d'] a'[d'] cs'[d'])).
  - exact (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dsup')).
  - exact (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Dsup')).
  - exact Dsup.
  - apply wfnf_sup.
    + now apply lequiv_refl.
    + exact Hl'.
    + exact EAA.
    + exact EA.
    + exact ENN.
    + exact EN.
    + intros ρ. exact (LRtm_kw ρ Xa).
    + intros ρ. pose proof (kw_lwf ρ Hwl) as Hwlρ.
      pose proof (kw_ty ρ HWd) as HWρ. rewrite kty_tyWf in HWρ.
      pose proof (WfDom_comp ρ (WfDom_of (wfDom_canon VAA Hd))) as HDρ.
      assert (Xaa : LRtm l G Δ A[d] A[d'] a[d] a[d]).
      { eapply LRtm_irrel_r; [exact (LRtm_trans Xa (LRtm_sym Xa))|].
        exact (VTyG_loc VAA _ _ _ Hd). }
      pose proof (wf_arity VAA VNN ρ _ _ Hd (LRtm_kw ρ Xaa)) as Hk.
      destruct (LRtm_kw ρ Xcs) as (R & HR & Hc).
      rewrite kty_tyVec, kty_tyWf, ktm_single in HR.
      exact (VecSp_of_LR Hwlρ HWρ HDρ _ _ Hk _ _ HR _ _ Hc).
Qed.

End SupfV.

End Wf.
