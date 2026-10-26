(** * The children's spine to the relation at their [DVec] (M17_DESIGN.md, M17b)

    The converse of [DVecISp_of_LR], for [elim_IWf]'s validity: a [sup_i]'s
    spine, in every world, is related at the children's [DVec] type, so
    that the step's [cs] entry of the substitution is related. As
    [LR_of_VecSp_all] (M15a), by induction on the length's [NatRel] in
    every world at once, generalized over the family of child indices
    [c] (which moves to [posMv m c] at the tail). *)
From DeLaM.Validity Require Export IWf.
From DeLaM.LogRel Require Import IWfAux.

Section S.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Section KwSyntax.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma ktyl_dvecMv_eq n F : ktyl ρ (dvecMv n F) = dvecMv (ktm ρ n) (ktyl ρ F).
Proof.
  unfold dvecMv, ktyl, ktm. rewrite gwa_subst_ty, gwa_lsingle, lsingle_ren_ty, gwa_ren_ty.
  rewrite liftshift_lift_ty. f_equal. f_equal.
  unfold gwa; destruct (kw_γ ρ); cbn; f_equal; f_equal;
    change (ren_tm ?x ?r) with x⟨r⟩; rewrite ?shift_lift; try reflexivity.
  all: change (gren_tm ?x ?y) with x⟪y⟫; rewrite gren_ren, shift_lift; reflexivity.
Qed.

Lemma ktyl_dvecTl L n F : ktyl ρ (dvecTl L n F) = dvecTl L (ktm ρ n) (ktyl ρ F).
Proof. rewrite !dvecTl_eq, ktyl_shift', kty_tyDVec, ktyl_dvecMv_eq. reflexivity. Qed.

End KwSyntax.

Lemma ktml_kid' {G Δ} (HΔ : [ G ; Δ ⊢g ]) (t : tm) : nftm t -> ktml (kid HΔ) t = t.
Proof.
  intros Nt. unfold ktml, kid, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk].
  rewrite <- (ren_id_tm t Nt) at 2. apply ren_ext_tm. intros n. rewrite rlk_rlift. destruct n; cbn; lia.
Qed.

Lemma ktmll_kid {G Δ} (HΔ : [ G ; Δ ⊢g ]) (t : tm) : nftm t -> ktmll (kid HΔ) t = t.
Proof.
  intros Nt. unfold ktmll, kid, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk].
  rewrite <- (ren_id_tm t Nt) at 2. apply ren_ext_tm. intros n. rewrite !rlk_rlift.
  destruct n as [|[|n]]; cbn; rewrite ?rlk_rlift; cbn; lia.
Qed.

Lemma fin_stab_ty' {G Δ k w T L'} : [ G ; Δ ⊢g k ≅ w : tyNat @ lzero ] ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g T @ L' ] -> [ G ; Δ ,, tyFin w @ lzero ⊢g T @ L' ].
Proof. intros Ek HT. exact (eqty_wf_l ge_typeof (fin_stab_eqty Ek (eqty_refl _ _ _ _ _ HT))). Qed.

(** The spine at its own world and in every weakening, as [sup_i]'s premise
    provides it. *)
Definition IKSp G Δ l li X A N Ot C (ix dm : DomRel G Δ) c k cs cs' :=
  DVecISp G Δ l li X A N Ot C ix dm c k cs cs' /\
  forall ρ : kwk G Δ,
    DVecISp (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
      (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (ktml ρ c) (ktm ρ k) (ktm ρ cs) (ktm ρ cs').

(** Spine to relation, at a family [c] and a length [k], in a world. *)
Definition IVecQ G Δ l li X A N Ot C (ix dm : DomRel G Δ) c k :=
  forall T' R, LogRel (lmax l li) G Δ (tyDVec (lmax l li) k (iwfFamT l li X A N Ot C c)) T' (lmax l li) R ->
  forall cs cs', IKSp G Δ l li X A N Ot C ix dm c k cs cs' -> R cs cs'.

Lemma IVecQ_zero {G Δ l li X A N Ot C} {ix dm : DomRel G Δ} {c k} : lwf (gL G) (lmax l li) ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ lmax l li ] ->
  [ G ; Δ ⊢g k ⤳* zero : tyNat @ lzero ] -> IVecQ G Δ l li X A N Ot C ix dm c k.
Proof.
  intros HwL HF Hk T' R H cs cs' [Hown _].
  pose proof (fin_stab_ty' (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF0.
  assert (Hred : [ G ; Δ ⊢g tyDVec (lmax l li) k (iwfFamT l li X A N Ot C c) ⤳* tyUnit (lmax l li) @ lmax l li ])
    by (eapply tyred_trans; [exact (tyred_dvec HwL HF Hk) | exact (tyred_dvec_zero HwL HF0)]).
  destruct (LR_inv_unit H Hred) as (l2 & _ & _ & _ & _ & HR).
  exact (proj2 (HR _ _) (DVecISp_zero_inv Hown Hk)).
Qed.

Lemma IVecQ_ne {G Δ l li X A N Ot C} {ix dm : DomRel G Δ} {c k ν} : lwf (gL G) (lmax l li) ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ lmax l li ] ->
  [ G ; Δ ⊢g k ⤳* ν : tyNat @ lzero ] -> whne ν -> IVecQ G Δ l li X A N Ot C ix dm c k.
Proof.
  intros HwL HF Hk Nν T' R H cs cs' [Hown _].
  destruct (LR_inv_ne H (tyred_dvec HwL HF Hk) (whne_tyDVec _ _ _ Nν)) as (V' & _ & HVV & HR).
  apply (proj2 (HR _ _)).
  eapply NeRel_conv2; [| | exact (DVecISp_ne_inv Hown Hk Nν)].
  - apply eqty_refl. exact (eqty_wf_l ge_typeof (geq_ty_sound (gne_ty_geq HVV))).
  - apply geq_ty_sound, gne_ty_geq, HVV.
Qed.

(** A spine at a successor, at given whnfs of its tuples. *)
Lemma DVecISp_succ_at {G Γ l li X A N Ot C ix dm c k m cs cs' w w' T T' l0 l0'} :
  DVecISp G Γ l li X A N Ot C ix dm c k cs cs' ->
  [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  [ G ; Γ ⊢g cs ⤳* w : T @ l0 ] -> whnf w -> [ G ; Γ ⊢g cs' ⤳* w' : T' @ l0' ] -> whnf w' ->
    (forall la lb A2 B2 la' lb' A2' B2',
       lequiv (gL G) la (lmax l li) -> lequiv (gL G) lb (lmax l li) ->
       lequiv (gL G) la' (lmax l li) -> lequiv (gL G) lb' (lmax l li) ->
       [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ A2 @ lmax l li ] ->
       [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
           ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ B2 @ lmax l li ] ->
       [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ A2' @ lmax l li ] ->
       [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
           ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ B2' @ lmax l li ] ->
       IWfRel G Γ l li X A N Ot C ix dm c[lsingle (posHd m)]
         (tmFst la lb A2 B2 w) (tmFst la' lb' A2' B2' w')) /\
    (forall la lb A2 B2 la' lb' A2' B2',
       lequiv (gL G) la (lmax l li) -> lequiv (gL G) lb (lmax l li) ->
       lequiv (gL G) la' (lmax l li) -> lequiv (gL G) lb' (lmax l li) ->
       [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ A2 @ lmax l li ] ->
       [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
           ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ B2 @ lmax l li ] ->
       [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ A2' @ lmax l li ] ->
       [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
           ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ B2' @ lmax l li ] ->
       DVecISp G Γ l li X A N Ot C ix dm (posMv m c) m (tmSnd la lb A2 B2 w) (tmSnd la' lb' A2' B2' w')).
Proof.
  intros H Hk Hr Nw Hr' Nw'.
  destruct (DVecISp_succ_inv H Hk) as (w0 & w0' & Hr0 & Hr0' & Nw0 & Nw0' & _ & Hf & Hs).
  assert (w0 = w) as -> by (eapply tmred_whnf_det; [exact Hr0 | exact Hr | exact Nw0 | exact Nw]).
  assert (w0' = w') as -> by (eapply tmred_whnf_det; [exact Hr0' | exact Hr' | exact Nw0' | exact Nw']).
  exact (conj Hf Hs).
Qed.

Lemma IVecQ_succ {G Δ l li X A N Ot C} {ix dm : DomRel G Δ} {c k m} : lwf (gL G) (lmax l li) ->
  nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ lmax l li ] ->
  KDom G Δ (lmeasure (lmax l li)) li X ix -> KDom G Δ (lmeasure (lmax l li)) l A dm ->
  [ G ; Δ ⊢g m : tyNat @ lzero ] -> [ G ; Δ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  (forall ρ : kwk G Δ,
     IVecQ (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
       (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (ktml ρ (posMv m c)) (ktm ρ m)) ->
  IVecQ G Δ l li X A N Ot C ix dm c k.
Proof.
  intros HwL NX NA NN NO NC HF HX HA Hm Hk IH T' R H cs cs' [Hown HK].
  set (L := lmax l li) in *.
  pose proof (fin_stab_ty' (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF1.
  set (F := iwfFamT l li X A N Ot C c) in *.
  assert (Hred : [ G ; Δ ⊢g tyDVec L k F ⤳* tySig L L (dvecHd m F) (dvecTl L m F) @ L ])
    by (eapply tyred_trans; [exact (tyred_dvec HwL HF Hk) | exact (tyred_dvec_succ HwL HF1 Hm)]).
  destruct (LR_inv_sig H Hred) as (m3 & m4 & C' & D' & dS & cS & P & domAd & codAd & HR).
  destruct P as [_ Hm3 Hm4 _ _ _ _ HC0 HC' HV HD' HWC HVD].
  apply HR.
  destruct (DVecISp_succ_inv Hown Hk) as (w & w' & Hr & Hr' & Nw & Nw' & Ew & _ & _).
  assert (EΣ : [ G ; Δ ⊢g tySig L L (dvecHd m F) (dvecTl L m F) ≅ tySig m3 m4 C' D' @ lmax L L ])
    by (apply geq_ty_sound, geq_ty_sig; auto using lequiv_sym).
  exists w, w'. refine (conj Hr (conj _ (conj Nw (conj Nw' (conj Ew (conj _ _)))))).
  - eapply tmred_conv; [apply ge_typeof | exact Hr' | exact EΣ].
  - exact (geq_tm_conv Ew EΣ).
  - intros ρ la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
    pose proof (kw_lwf ρ HwL) as HwLρ.
    (* the annotations, at the spine's types in the world *)
    pose proof (kw_geq_ty ρ HWC) as KC. pose proof (kw_geq_ty_l ρ HC0 HwL HVD) as KD.
    pose proof (kw_ty ρ HC0) as HC0ρ.
    assert (HA1'x : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ (dvecHd m F) ≈ A1' @ L ]) by exact (geq_ty_trans KC HA1').
    assert (HB1'x : [ kw_G ρ ; kw_Δ ρ ,, kty ρ (dvecHd m F) @ L ⊢ ktyl ρ (dvecTl L m F) ≈ B1' @ L ]).
    { eapply geq_ty_trans; [exact KD|].
      eapply geq_ty_ctxconv; [apply eqty_sym, geq_ty_sound, KC | now apply lequiv_refl
                             | apply ext_wf_g; [exact HC0ρ | exact HwLρ] | exact HB1']. }
    rewrite (ktyl_dvecTl ρ) in HB1, HB1'x. rewrite (kty_dvecHd ρ) in HA1, HB1, HA1'x, HB1'x, HC0ρ.
    unfold F in HA1, HB1, HA1'x, HB1'x, HC0ρ. rewrite (ktyl_iwfFamT ρ) in HA1, HB1, HA1'x, HB1'x, HC0ρ.
    (* the spine in the world, at the weakened whnfs *)
    pose proof (kw_tmred ρ Hk) as Hkρ. rewrite ktm_succ, kty_tyNat in Hkρ.
    pose proof (kw_tmred ρ Hr) as Hrρ. pose proof (kw_tmred ρ Hr') as Hrρ'.
    destruct (DVecISp_succ_at (HK ρ) Hkρ Hrρ (whnf_kw ρ _ Nw) Hrρ' (whnf_kw ρ _ Nw')) as [Hf Hs].
    (* the first projections, in [Σ]'s domain relation *)
    pose proof (domAd ρ) as DOM. rewrite (kty_dvecHd ρ) in DOM. unfold F in DOM.
    rewrite (ktyl_iwfFamT ρ), iwfFamT_single in DOM by (unfold kty, ktml, ktmll; first [apply ren_nf_ty | apply ren_nf]).
    pose proof (LR_iwf_rel DOM (KDom_comp ρ HX) (KDom_comp ρ HA)) as RD.
    pose proof (kw_lequiv ρ H1) as J1. pose proof (kw_lequiv ρ H2) as J2.
    pose proof (kw_lequiv ρ H1') as J1'. pose proof (kw_lequiv ρ H2') as J2'.
    pose proof (Hf la lb A1 B1 la' lb' A1' B1' J1 J2 J1' J2' HA1 HB1 HA1'x HB1'x) as Fst.
    exists (proj2 (RD _ _) Fst).
    (* the second projections, in [Σ]'s codomain relation, by the induction hypothesis *)
    pose proof (codAd ρ _ _ (proj2 (RD _ _) Fst)) as COD.
    rewrite (dvec_cod_single ρ), (kty_tyDVec ρ), (ktyl_dvecMv_eq ρ) in COD. unfold F in COD.
    rewrite (ktyl_iwfFamT ρ), iwfFamT_mv in COD.
    pose proof (IH ρ) as IHρ. unfold IVecQ in IHρ. rewrite (ktml_posMv ρ) in IHρ.
    apply (IHρ _ _ COD). split.
    + exact (Hs la lb A1 B1 la' lb' A1' B1' J1 J2 J1' J2' HA1 HB1 HA1'x HB1'x).
    + intros ρ'. rewrite !ktm_snd, !(ktml_posMv ρ').
      pose proof (HK (kw_comp ρ ρ')) as Y.
      rewrite kty_comp, kty_comp, ktml_comp, ktml_comp, ktmll_comp, ktml_comp, !ktm_comp in Y.
      pose proof (kw_tmred ρ' Hkρ) as Hkρ'. rewrite ktm_succ, kty_tyNat in Hkρ'.
      pose proof (kw_tmred ρ' Hrρ) as Hrρ2. pose proof (kw_tmred ρ' Hrρ') as Hrρ2'.
      destruct (DVecISp_succ_at Y Hkρ' Hrρ2 (whnf_kw ρ' _ (whnf_kw ρ _ Nw)) Hrρ2' (whnf_kw ρ' _ (whnf_kw ρ _ Nw')))
        as [_ Hs'].
      pose proof (kw_lequiv ρ' J1) as K1. pose proof (kw_lequiv ρ' J2) as K2.
      pose proof (kw_lequiv ρ' J1') as K1'. pose proof (kw_lequiv ρ' J2') as K2'.
      pose proof (kw_geq_ty ρ' HA1) as KA1. pose proof (kw_geq_ty_l ρ' HC0ρ HwLρ HB1) as KB1.
      pose proof (kw_geq_ty ρ' HA1'x) as KA1'. pose proof (kw_geq_ty_l ρ' HC0ρ HwLρ HB1'x) as KB1'.
      rewrite (ktyl_dvecTl ρ') in KB1, KB1'. rewrite (kty_dvecHd ρ') in KA1, KB1, KA1', KB1'.
      rewrite (ktyl_iwfFamT ρ') in KA1, KB1, KA1', KB1'.
      pose proof (Hs' la lb _ _ la' lb' _ _ K1 K2 K1' K2' KA1 KB1 KA1' KB1') as Z.
      eapply (proj2 (proj2 IWfRel_dir_all)); [exact Z| |].
      * intros ρ''. exact (KDom_assoc HX ρ ρ' ρ'').
      * intros ρ''. exact (KDom_assoc HA ρ ρ' ρ'').
Qed.

Section SpineK.
Context {G : gctx} {Δ : ctx} {l li : lvl} {X A : ty} {N Ot C : tm} {ix dm : DomRel G Δ}
  (HwL : lwf (gL G) (lmax l li))
  (NX : nfty X) (NA : nfty A) (NN : nftm N) (NO : nftm Ot) (NC : nftm C)
  (HX : KDom G Δ (lmeasure (lmax l li)) li X ix) (HA : KDom G Δ (lmeasure (lmax l li)) l A dm).

(** Spine to relation: by induction on the length's [NatRel], in every
    world at once, over every family of child indices. *)
Lemma LR_of_DVecISp_all : forall k k', NatRel G Δ k k' -> forall c,
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ lmax l li ] ->
  forall ρ : kwk G Δ,
    IVecQ (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
      (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (ktml ρ c) (ktm ρ k).
Proof.
  assert (Nρ : forall ρ : kwk G Δ, nfty (kty ρ X) /\ nfty (kty ρ A) /\ nftm (ktml ρ N) /\ nftm (ktml ρ Ot)
                                    /\ nftm (ktmll ρ C))
    by (intros ρ; unfold kty, ktml, ktmll; repeat split; first [apply ren_nf_ty | apply ren_nf]).
  assert (HFρ : forall k c (ρ : kwk G Δ), [ G ; Δ ⊢g k : tyNat @ lzero ] ->
            [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ lmax l li ] ->
            [ kw_G ρ ; kw_Δ ρ ,, tyFin (ktm ρ k) @ lzero
              ⊢g iwfFamT l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktml ρ c) @ lmax l li ]).
  { intros k c ρ Hk HF. assert (HFin : [ G ; Δ ⊢g tyFin k @ lzero ]) by (apply wft_fin; [exact ge_notV | exact Hk]).
    pose proof (kw_ty_l ρ HFin I HF) as Y.
    rewrite kty_tyFin, ktyl_iwfFamT in Y. exact Y. }
  apply (NatRel_mut G Δ
    (fun k k' _ => forall c, [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ lmax l li ] ->
       forall ρ : kwk G Δ,
       IVecQ (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
         (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (ktml ρ c) (ktm ρ k))
    (fun w w' _ => forall k, [ G ; Δ ⊢g k ⤳* w : tyNat @ lzero ] -> forall c,
       [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ lmax l li ] ->
       forall ρ : kwk G Δ,
       IVecQ (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
         (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (ktml ρ c) (ktm ρ k))).
  - intros t t' w w' Ht _ _ _ IH. exact (IH t Ht).
  - intros k Hk c HF ρ. pose proof (kw_tmred ρ Hk) as Hkρ. rewrite ktm_zero, kty_tyNat in Hkρ.
    exact (IVecQ_zero (kw_lwf ρ HwL) (HFρ _ _ ρ (tmred_wf _ _ _ _ _ _ _ Hk) HF) Hkρ).
  - intros m m' Hmm IH k Hk c HF ρ. pose proof (kw_tmred ρ Hk) as Hkρ. rewrite ktm_succ, kty_tyNat in Hkρ.
    destruct (NatRel_escape Hmm) as (Hm & _ & _). pose proof (kw_tm ρ Hm) as Hmρ. rewrite kty_tyNat in Hmρ.
    pose proof (fin_stab_ty' (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF1.
    pose proof (dvecMv_wf ge_typeof ge_notV ge_compt Hm HF1) as HFmv. rewrite iwfFamT_mv in HFmv.
    destruct (Nρ ρ) as (NXρ & NAρ & NNρ & NOρ & NCρ).
    apply (IVecQ_succ (kw_lwf ρ HwL) NXρ NAρ NNρ NOρ NCρ (HFρ _ _ ρ (tmred_wf _ _ _ _ _ _ _ Hk) HF)
             (KDom_comp ρ HX) (KDom_comp ρ HA) Hmρ Hkρ).
    intros ρ' T' R H cs cs' HK.
    pose proof (IH (posMv m c) HFmv (kw_comp ρ ρ')) as Y.
    rewrite kty_comp, kty_comp, ktml_comp, ktml_comp, ktmll_comp, ktml_comp, ktm_comp in Y.
    rewrite <- (ktml_posMv ρ) in H, HK.
    apply (Y T' R H). destruct HK as [Hown HK]. split.
    + eapply (proj2 (proj2 IWfRel_dir_all)); [exact Hown| |].
      * intros ρ0. apply releq_sym', (KDom_assoc HX ρ ρ' ρ0).
      * intros ρ0. apply releq_sym', (KDom_assoc HA ρ ρ' ρ0).
    + intros ρ''. eapply (proj2 (proj2 IWfRel_dir_all)); [exact (HK ρ'')| |].
      * intros ρ0. apply releq_sym', (KDom_assoc HX ρ ρ' (kw_comp ρ'' ρ0)).
      * intros ρ0. apply releq_sym', (KDom_assoc HA ρ ρ' (kw_comp ρ'' ρ0)).
  - intros ν ν' Hνν k Hk c HF ρ. pose proof (kw_tmred ρ Hk) as Hkρ. rewrite kty_tyNat in Hkρ.
    exact (IVecQ_ne (kw_lwf ρ HwL) (HFρ _ _ ρ (tmred_wf _ _ _ _ _ _ _ Hk) HF) Hkρ
             (gne_tm_whne_l (kw_gne_tm ρ Hνν))).
Qed.

(** Spine to relation at the spine's own world, from the spine in every
    world. *)
Lemma LR_of_DVecISp_own {c k k' cs cs'} (HΔ : [ G ; Δ ⊢g ]) : NatRel G Δ k k' -> nftm c ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c @ lmax l li ] ->
  nftm cs -> nftm cs' ->
  (forall ρ : kwk G Δ,
     DVecISp (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
       (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (ktml ρ c) (ktm ρ k) (ktm ρ cs) (ktm ρ cs')) ->
  forall T' R, LogRel (lmax l li) G Δ (tyDVec (lmax l li) k (iwfFamT l li X A N Ot C c)) T' (lmax l li) R ->
  R cs cs'.
Proof.
  intros Hkk Nc HF Ncs Ncs' Hsp T' R H.
  destruct (NatRel_escape Hkk) as (Hk & _ & _). pose proof (wf_tm_nf Hk) as Nk.
  pose proof (LR_of_DVecISp_all _ _ Hkk c HF (kid HΔ)) as Y. unfold IVecQ in Y.
  rewrite (kty_kid HΔ _ NX), (kty_kid HΔ _ NA), (ktml_kid' HΔ _ NN), (ktml_kid' HΔ _ NO), (ktmll_kid HΔ _ NC),
    (ktml_kid' HΔ _ Nc), (ktm_kid HΔ _ Nk) in Y.
  apply (Y T' R H cs cs'). split.
  - pose proof (Hsp (kid HΔ)) as Z.
    rewrite (kty_kid HΔ _ NX), (kty_kid HΔ _ NA), (ktml_kid' HΔ _ NN), (ktml_kid' HΔ _ NO), (ktmll_kid HΔ _ NC),
      (ktml_kid' HΔ _ Nc), (ktm_kid HΔ _ Nk), (ktm_kid HΔ _ Ncs), (ktm_kid HΔ _ Ncs') in Z.
    exact Z.
  - intros ρ. pose proof (Hsp (kw_comp (kid HΔ) ρ)) as Z.
    rewrite kty_comp, kty_comp, ktml_comp, ktml_comp, ktmll_comp, ktml_comp, !ktm_comp in Z.
    rewrite (kty_kid HΔ _ NX), (kty_kid HΔ _ NA), (ktml_kid' HΔ _ NN), (ktml_kid' HΔ _ NO), (ktmll_kid HΔ _ NC),
      (ktml_kid' HΔ _ Nc), (ktm_kid HΔ _ Nk), (ktm_kid HΔ _ Ncs), (ktm_kid HΔ _ Ncs') in Z.
    eapply (proj2 (proj2 IWfRel_dir_all)); [exact Z| |].
    + intros ρ0. exact (KDom_assoc HX (kid HΔ) ρ ρ0).
    + intros ρ0. exact (KDom_assoc HA (kid HΔ) ρ ρ0).
Qed.

End SpineK.
End S.
