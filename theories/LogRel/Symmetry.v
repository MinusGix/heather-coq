(** * Symmetry (ch. 7)

    [LR T T' R] gives [LR T' T (flip R)].  By strong induction on the stage
    (the universe case uses symmetry one stage down) and induction on the
    derivation.  The symmetric Π derivation uses the flipped domain and
    codomain relations, which saturation makes available without choice. *)
From DeLaM.LogRel Require Export Irrelevance.

Definition flipR (R : tm -> tm -> Prop) : tm -> tm -> Prop := fun t t' => R t' t.

Section Symmetry.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Declarative and generic helpers *)

Lemma lconv_ty {G Γ T l l'} : [ G ; Γ ⊢g T @ l ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢g T @ l' ].
Proof. intros; eapply wft_lconv; eauto using lequiv_sym. Qed.

(** Changing the level annotation of the last context entry. *)
Lemma ctx_lvl_ty {G Γ A la la' T l} :
  [ G ; Γ ⊢g A @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A @ la ⊢g T @ l ] -> [ G ; Γ ,, A @ la' ⊢g T @ l ].
Proof.
  intros HA Hl HT. eapply (stab_ty ge_typeof (eqty_refl _ _ _ _ _ HA) Hl); [|exact HT].
  apply ext_wf_g; [now apply (lconv_ty HA) | eauto using lequiv_wf_r].
Qed.

Lemma ctx_lvl_geq {G Γ A la la' T T' l} :
  [ G ; Γ ⊢g A @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A @ la ⊢ T ≈ T' @ l ] -> [ G ; Γ ,, A @ la' ⊢ T ≈ T' @ l ].
Proof.
  intros HA Hl HT. eapply geq_ty_ctxconv; [apply eqty_refl, HA | exact Hl | | exact HT].
  apply ext_wf_g; [now apply (lconv_ty HA) | eauto using lequiv_wf_r].
Qed.

Lemma tmred_U_conv {G Γ t w l1 l2} :
  [ G ; Γ ⊢g t ⤳* w : tyU l1 @ lsuc l1 ] -> lequiv (gL G) l1 l2 ->
  [ G ; Γ ⊢g t ⤳* w : tyU l2 @ lsuc l2 ].
Proof.
  intros Ht Hl. eapply tmred_lconv; [|apply lequiv_suc, lequiv_sym, Hl].
  eapply tmred_conv; [apply ge_typeof | exact Ht |].
  apply eqty_U; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, Ht | exact Hl].
Qed.

Lemma geq_U_conv {G Γ w w' l1 l2} :
  [ G ; Γ ⊢g ] -> [ G ; Γ ⊢ w ≈ w' : tyU l1 @ lsuc l1 ] -> lequiv (gL G) l1 l2 ->
  [ G ; Γ ⊢ w ≈ w' : tyU l2 @ lsuc l2 ].
Proof.
  intros HΓ Hw Hl. eapply geq_tm_lconv; [|apply lequiv_suc, lequiv_sym, Hl].
  eapply geq_tm_conv; [exact Hw |].
  apply eqty_U; [exact ge_notV | now rewrite ge_typeof | exact Hl].
Qed.

(** ** Natural numbers and neutrals *)

Lemma NatRel_sym G Γ : forall t t', NatRel G Γ t t' -> NatRel G Γ t' t.
Proof.
  apply (NatRel_mut G Γ (fun t t' _ => NatRel G Γ t' t) (fun t t' _ => NatNf G Γ t' t)).
  - intros t t' w w' Hw Hw' Heq _ IH. econstructor; eauto using geq_tm_sym.
  - constructor.
  - intros; now constructor.
  - intros; constructor; now apply gne_tm_sym.
Qed.

Lemma NatRel_flip G Γ : releq (flipR (NatRel G Γ)) (NatRel G Γ).
Proof. intros t t'; split; apply NatRel_sym. Qed.

Lemma NeRel_flip G Γ V V' l : releq (flipR (NeRel G Γ V V' l)) (NeRel G Γ V' V l).
Proof.
  intros t t'; unfold flipR, NeRel; split; intros (ν & ν' & H1 & H2 & H3 & H4);
    exists ν', ν; eauto 6 using gne_tm_sym.
Qed.

(** ** Π *)

Definition flipD {G Γ} (domR : DomRel G Γ) : DomRel G Γ :=
  fun ρ => flipR (domR ρ).
Definition flipC {G Γ} {domR : DomRel G Γ} (codR : CodRel G Γ domR) : CodRel G Γ (flipD domR) :=
  fun ρ a a' ha => flipR (codR ρ a' a ha).

Section PiFlip.
Context {G : gctx} {Γ : ctx} {l1 l2 l3 l4 : lvl} {A B A' B' : ty}
  {domR : DomRel G Γ} {codR : CodRel G Γ domR}
  (H13 : lequiv (gL G) l3 l1) (H24 : lequiv (gL G) l4 l2)
  (HA : [ G ; Γ ⊢g A @ l1 ]) (HA' : [ G ; Γ ⊢g A' @ l1 ]).

Lemma PiRel_flip t t' :
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR t' t ->
  PiRel G Γ l3 l4 l1 l2 A' B' A B (flipD domR) (flipC codR) t t'.
Proof.
  intros (w1 & w2 & Hw1 & Hw2 & Hnf1 & Hnf2 & Heq1 & Heq2 & HK).
  assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
  exists w2, w1.
  refine (conj _ (conj _ (conj Hnf2 (conj Hnf1 (conj _ (conj _ _)))))).
  - eapply tmred_lconv; [exact Hw2 | exact Hm].
  - eapply tmred_lconv; [exact Hw1 | exact Hm].
  - eapply geq_tm_lconv; [apply geq_tm_sym, Heq2 | exact Hm].
  - eapply geq_tm_lconv; [apply geq_tm_sym, Heq1 | exact Hm].
  - intros ρ a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    unfold flipC, flipR.
    pose proof (kw_ty ρ HA) as HAr. pose proof (kw_ty ρ HA') as HA'r.
    pose proof (kw_lequiv ρ H13) as H13'. pose proof (kw_lequiv ρ H24) as H24'.
    apply (HK ρ a' a ha la' lb' la lb A1' B1' A1 B1).
    + eapply lequiv_trans; eassumption.
    + eapply lequiv_trans; eassumption.
    + eapply lequiv_trans; eassumption.
    + eapply lequiv_trans; eassumption.
    + eapply geq_ty_lconv; [exact HA1' | apply lequiv_sym, H13'].
    + eapply geq_ty_lconv; [|apply lequiv_sym, H24'].
      eapply ctx_lvl_geq; [eapply lconv_ty; [exact HAr | apply lequiv_sym, H13'] | exact H13' | exact HB1'].
    + eapply geq_ty_lconv; [exact HA1 | apply lequiv_sym, H13'].
    + eapply geq_ty_lconv; [|apply lequiv_sym, H24'].
      eapply ctx_lvl_geq; [eapply lconv_ty; [exact HA'r | apply lequiv_sym, H13'] | exact H13' | exact HB1].
Qed.

Lemma SigRel_flip t t' :
  SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR t' t ->
  SigRel G Γ l3 l4 l1 l2 A' B' A B (flipD domR) (flipC codR) t t'.
Proof.
  intros (w1 & w2 & Hw1 & Hw2 & Hnf1 & Hnf2 & Heq1 & Heq2 & HK).
  assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
  exists w2, w1.
  refine (conj _ (conj _ (conj Hnf2 (conj Hnf1 (conj _ (conj _ _)))))).
  - eapply tmred_lconv; [exact Hw2 | exact Hm].
  - eapply tmred_lconv; [exact Hw1 | exact Hm].
  - eapply geq_tm_lconv; [apply geq_tm_sym, Heq2 | exact Hm].
  - eapply geq_tm_lconv; [apply geq_tm_sym, Heq1 | exact Hm].
  - intros ρ la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    unfold flipD, flipC, flipR.
    pose proof (kw_ty ρ HA) as HAr. pose proof (kw_ty ρ HA') as HA'r.
    pose proof (kw_lequiv ρ H13) as H13'. pose proof (kw_lequiv ρ H24) as H24'.
    refine (HK ρ la' lb' la lb A1' B1' A1 B1 _ _ _ _ _ _ _ _).
    + eapply lequiv_trans; eassumption.
    + eapply lequiv_trans; eassumption.
    + eapply lequiv_trans; eassumption.
    + eapply lequiv_trans; eassumption.
    + eapply geq_ty_lconv; [exact HA1' | apply lequiv_sym, H13'].
    + eapply geq_ty_lconv; [|apply lequiv_sym, H24'].
      eapply ctx_lvl_geq; [eapply lconv_ty; [exact HAr | apply lequiv_sym, H13'] | exact H13' | exact HB1'].
    + eapply geq_ty_lconv; [exact HA1 | apply lequiv_sym, H13'].
    + eapply geq_ty_lconv; [|apply lequiv_sym, H24'].
      eapply ctx_lvl_geq; [eapply lconv_ty; [exact HA'r | apply lequiv_sym, H13'] | exact H13' | exact HB1].
Qed.

End PiFlip.

(** ** Meta-functions

    The flipped instance at [h] is the original one at a proof derived
    from [h]; going back needs the instances to be irrelevant in the
    proof, which [LR_irrel] gives. *)

Definition flipCI {G Γ} (instR : CInstRel G Γ) : CInstRel G Γ :=
  fun ρ Δ Δ' h => flipR (instR ρ Δ' Δ (vpl_ctx_sym h)).

Lemma CPiRel_flip {G Γ l1 l2 T1 T1'} {instR : CInstRel G Γ} :
  lequiv (gL G) l2 l1 ->
  (forall ρ Δ Δ' h h', releq (instR ρ Δ Δ' h) (instR ρ Δ Δ' h')) ->
  releq (flipR (CPiRel G Γ l1 l2 T1 T1' instR)) (CPiRel G Γ l2 l1 T1' T1 (flipCI instR)).
Proof.
  intros Hl Hsame t t'; unfold flipR; split.
  - intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK). exists w', w.
    refine (conj _ (conj _ (conj Hnf' (conj Hnf (conj _ (conj _ _)))))).
    + eapply tmred_lconv; [exact Hw' | exact Hl].
    + eapply tmred_lconv; [exact Hw | exact Hl].
    + eapply geq_tm_lconv; [apply geq_tm_sym, Heq' | exact Hl].
    + eapply geq_tm_lconv; [apply geq_tm_sym, Heq | exact Hl].
    + intros ρ Δ Δ' h. unfold flipCI, flipR. exact (HK ρ Δ' Δ (vpl_ctx_sym h)).
  - intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK). exists w', w.
    pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    refine (conj _ (conj _ (conj Hnf' (conj Hnf (conj _ (conj _ _)))))).
    + eapply tmred_lconv; [exact Hw' | exact Hl'].
    + eapply tmred_lconv; [exact Hw | exact Hl'].
    + eapply geq_tm_lconv; [apply geq_tm_sym, Heq' | exact Hl'].
    + eapply geq_tm_lconv; [apply geq_tm_sym, Heq | exact Hl'].
    + intros ρ Δ Δ' h. apply (Hsame ρ Δ Δ' (vpl_ctx_sym (vpl_ctx_sym h)) h).
      exact (HK ρ Δ' Δ (vpl_ctx_sym h)).
Qed.

(** The argument of the flipped [TΠ], moved to the left domain. *)
Definition tflip_arg {G Γ Δ1 Δ1' l1 l3} (HΔ : vp_ctx lr_vp G Δ1 Δ1') (H13 : lequiv (gL G) l3 l1)
    (ρ : kwk G Γ) {A A'} (h : vp_ty lr_vp (kw_G ρ) Δ1'⟦kw_γ ρ⟧ A A' l3) :
    vp_ty lr_vp (kw_G ρ) Δ1⟦kw_γ ρ⟧ A' A l1 :=
  vpl_ty_lconv (kw_lequiv ρ H13)
    (vpl_ty_ctx (vpl_ctx_sym (vpl_ctx_gwk (kw_gok ρ) (kw_glob ρ) HΔ)) (vpl_ty_sym h)).

Definition flipTI {G Γ Δ1 Δ1' l1 l3} (HΔ : vp_ctx lr_vp G Δ1 Δ1') (H13 : lequiv (gL G) l3 l1)
    (instR : TInstRel G Γ Δ1 l1) : TInstRel G Γ Δ1' l3 :=
  fun ρ A A' h => flipR (instR ρ A' A (tflip_arg HΔ H13 ρ h)).

Lemma TPiRel_flip {G Γ Δ1 Δ1' l1 l2 l3 l4 T1 T1'} {instR : TInstRel G Γ Δ1 l1}
  (HΔ : vp_ctx lr_vp G Δ1 Δ1') (H13 : lequiv (gL G) l3 l1) :
  lequiv (gL G) l4 l2 ->
  (forall ρ A A' h h', releq (instR ρ A A' h) (instR ρ A A' h')) ->
  releq (flipR (TPiRel G Γ Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR))
        (TPiRel G Γ Δ1' Δ1 l3 l4 l1 l2 T1' T1 (flipTI HΔ H13 instR)).
Proof.
  intros Hl Hsame t t'; unfold flipR; split.
  - intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK). exists w', w.
    refine (conj _ (conj _ (conj Hnf' (conj Hnf (conj _ (conj _ _)))))).
    + eapply tmred_lconv; [exact Hw' | exact Hl].
    + eapply tmred_lconv; [exact Hw | exact Hl].
    + eapply geq_tm_lconv; [apply geq_tm_sym, Heq' | exact Hl].
    + eapply geq_tm_lconv; [apply geq_tm_sym, Heq | exact Hl].
    + intros ρ A A' h. unfold flipTI, flipR. exact (HK ρ A' A _).
  - intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK). exists w', w.
    pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    refine (conj _ (conj _ (conj Hnf' (conj Hnf (conj _ (conj _ _)))))).
    + eapply tmred_lconv; [exact Hw' | exact Hl'].
    + eapply tmred_lconv; [exact Hw | exact Hl'].
    + eapply geq_tm_lconv; [apply geq_tm_sym, Heq' | exact Hl'].
    + eapply geq_tm_lconv; [apply geq_tm_sym, Heq | exact Hl'].
    + intros ρ A A' h.
      (* the argument back at [Δ1'], at level [l3] *)
      pose proof (vpl_ty_lconv (lequiv_sym _ _ _ (kw_lequiv ρ H13))
                    (vpl_ty_ctx (vpl_ctx_gwk (kw_gok ρ) (kw_glob ρ) HΔ) (vpl_ty_sym h))) as h'.
      apply (Hsame ρ A A' (tflip_arg HΔ H13 ρ h') h).
      exact (HK ρ A' A h').
Qed.

(** ** The universe *)

Definition Psym n := forall G Γ T T' l R,
  LR n (LRbelow n) G Γ T T' l R -> LR n (LRbelow n) G Γ T' T l (flipR R).

Lemma URel_flip n G Γ l1 l2 t t' :
  Psym (lmeasure l1) -> lmeasure l1 < n -> lequiv (gL G) l1 l2 ->
  URel (LRbelow n) G Γ l1 t t' -> URel (LRbelow n) G Γ l2 t' t.
Proof.
  intros Hsym Hn Hl (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & HK).
  assert (Hm : lmeasure l2 = lmeasure l1) by (symmetry; eapply lequiv_measure; eauto).
  exists w', w. refine (conj _ (conj _ (conj Hnf' (conj Hnf (conj _ _))))).
  - exact (tmred_U_conv Hw' Hl).
  - exact (tmred_U_conv Hw Hl).
  - eapply geq_U_conv; [eapply ctx_of_tm, Hw | apply geq_tm_sym, Heq | exact Hl].
  - intros la lb Hla Hlb.
    destruct (HK lb la) as [R0 H0]; [eapply lequiv_trans; [eassumption | apply lequiv_sym, Hl].. |].
    rewrite LRbelow_spec in H0 by exact Hn.
    exists (flipR R0). rewrite LRbelow_spec by lia. unfold LogRel in *. rewrite Hm.
    eapply LR_lconv; [exact (Hsym _ _ _ _ _ _ H0) | now apply lequiv_sym].
Qed.

(** ** Symmetry *)

Lemma LR_sym_step n : (forall m, m < n -> Psym m) -> Psym n.
Proof.
  intros IHn G Γ T T' l R H.
  induction H as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR].
  - eapply LRnat; eauto.
    intros t t'; unfold flipR; rewrite (HR t' t); apply NatRel_flip.
  - assert (Hm : lmeasure l2 = lmeasure l1) by (eapply lequiv_measure; eauto).
    eapply (LRU n (LRbelow n) G Γ T' T l l2 l1).
    + eapply lequiv_trans; [exact Hl | apply lequiv_suc, lequiv_sym, Hl2].
    + now apply lequiv_sym.
    + lia.
    + exact HT'.
    + exact HT.
    + intros t t'; unfold flipR; rewrite (HR t' t); split.
      * apply URel_flip; auto using lequiv_sym; try apply IHn; lia.
      * apply URel_flip; auto; try apply IHn; lia.
  - eapply LRne; eauto using gne_ty_sym.
    intros t t'; unfold flipR; rewrite (HR t' t); apply NeRel_flip.
  - assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HΓ : [ G ; Γ ⊢g ]) by exact (ctx_of_ty HA).
    assert (HA3 : [ G ; Γ ⊢g A @ l3 ]) by (eapply lconv_ty; [exact HA | now apply lequiv_sym]).
    assert (HA'3 : [ G ; Γ ⊢g A' @ l3 ]) by (eapply lconv_ty; [exact HA' | now apply lequiv_sym]).
    eapply (LRpi n (LRbelow n) G Γ T' T l l3 l4 l1 l2 A' B' A B (flipD domR) (flipC codR)); [split|..].
    + eapply lequiv_trans; [exact Hl | apply lequiv_sym, Hm].
    + now apply lequiv_sym.
    + now apply lequiv_sym.
    + eauto using lequiv_wf_l.
    + eauto using lequiv_wf_l.
    + exact HT'.
    + exact HT.
    + exact HA'3.
    + exact HA3.
    + eapply (lconv_ty (l := l2)); [|now apply lequiv_sym]. eapply ctx_lvl_ty; [exact HA' | now apply lequiv_sym | exact HB'].
    + eapply (lconv_ty (l := l2)); [|now apply lequiv_sym]. eapply ctx_lvl_ty; [exact HA | now apply lequiv_sym | exact HB].
    + eapply geq_ty_lconv; [apply geq_ty_sym, HAA | exact Hl3].
    + eapply geq_ty_lconv; [|exact Hl4].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, HAA | now apply lequiv_sym | | apply geq_ty_sym, HBB].
      apply ext_wf_g; [exact HA'3 | eauto using lequiv_wf_l].
    + intros ρ. eapply LR_lconv; [exact (IHdom ρ) | exact (kw_lequiv ρ Hl3)].
    + intros ρ a a' ha. eapply LR_lconv; [exact (IHcod ρ a' a ha) | exact (kw_lequiv ρ Hl4)].
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split.
      * apply PiRel_flip; auto.
      * intros H. apply (PiRel_flip (A := A') (A' := A) (domR := flipD domR) (codR := flipC codR));
          auto using lequiv_sym.
  - apply LRmod; [exact Hj | exact (ModRel_sym HM)].
  - (* CΠ *)
    assert (Hsame : forall ρ Δ Δ' h h', releq (instR ρ Δ Δ' h) (instR ρ Δ Δ' h'))
      by (intros; exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (instAd ρ Δ Δ' h) (instAd ρ Δ Δ' h'))).
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'.
    eapply (LRcpi n (LRbelow n) G Γ T' T l l2 l1 T1' T1 (flipCI instR)).
    + exact Hj.
    + exact (lequiv_trans _ _ _ _ Hl Hl2').
    + exact Hl2'.
    + exact (lequiv_wf_l _ _ _ Hl2).
    + exact HT'.
    + exact HT.
    + exact (lconv_ty HT1' Hl2').
    + exact (lconv_ty HT1 Hl2').
    + eapply geq_ty_lconv; [apply geq_ty_sym, Hgeq | exact Hl2].
    + intros ρ Δ Δ' h. unfold flipCI.
      eapply LR_lconv; [exact (IHinst ρ Δ' Δ (vpl_ctx_sym h)) | exact (kw_lequiv ρ Hl2)].
    + exact (releq_trans _ _ _ (fun t t' => HR t' t) (CPiRel_flip Hl2 Hsame)).
  - (* TΠ *)
    assert (Hsame : forall ρ A A' h h', releq (instR ρ A A' h) (instR ρ A A' h'))
      by (intros; exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (instAd ρ A A' h) (instAd ρ A A' h'))).
    eapply (LRtpi n (LRbelow n) G Γ T' T l Δ1' Δ1 l3 l4 l1 l2 T1' T1 (flipTI HΔ Hl3 instR)).
    + exact Hj.
    + exact (lequiv_trans _ _ _ _ Hl (lequiv_sym _ _ _ Hl4)).
    + exact (lequiv_sym _ _ _ Hl3).
    + exact (lequiv_sym _ _ _ Hl4).
    + exact (lequiv_wf_l _ _ _ Hl3).
    + exact (lequiv_wf_l _ _ _ Hl4).
    + exact HT'.
    + exact HT.
    + exact (vpl_ctx_sym HΔ).
    + exact HT1'.
    + exact HT1.
    + eapply geq_ty_lconv; [apply geq_ty_sym, Hgeq | exact Hl4].
    + intros ρ A A' h. unfold flipTI.
      eapply LR_lconv; [exact (IHinst ρ A' A _) | exact (kw_lequiv ρ Hl4)].
    + exact (releq_trans _ _ _ (fun t t' => HR t' t) (TPiRel_flip HΔ Hl3 Hl4 Hsame)).
  - assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HΓ : [ G ; Γ ⊢g ]) by exact (ctx_of_ty HA).
    assert (HA3 : [ G ; Γ ⊢g A @ l3 ]) by (eapply lconv_ty; [exact HA | now apply lequiv_sym]).
    assert (HA'3 : [ G ; Γ ⊢g A' @ l3 ]) by (eapply lconv_ty; [exact HA' | now apply lequiv_sym]).
    eapply (LRsig n (LRbelow n) G Γ T' T l l3 l4 l1 l2 A' B' A B (flipD domR) (flipC codR)); [split|..].
    + eapply lequiv_trans; [exact Hl | apply lequiv_sym, Hm].
    + now apply lequiv_sym.
    + now apply lequiv_sym.
    + eauto using lequiv_wf_l.
    + eauto using lequiv_wf_l.
    + exact HT'.
    + exact HT.
    + exact HA'3.
    + exact HA3.
    + eapply (lconv_ty (l := l2)); [|now apply lequiv_sym]. eapply ctx_lvl_ty; [exact HA' | now apply lequiv_sym | exact HB'].
    + eapply (lconv_ty (l := l2)); [|now apply lequiv_sym]. eapply ctx_lvl_ty; [exact HA | now apply lequiv_sym | exact HB].
    + eapply geq_ty_lconv; [apply geq_ty_sym, HAA | exact Hl3].
    + eapply geq_ty_lconv; [|exact Hl4].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, HAA | now apply lequiv_sym | | apply geq_ty_sym, HBB].
      apply ext_wf_g; [exact HA'3 | eauto using lequiv_wf_l].
    + intros ρ. eapply LR_lconv; [exact (IHdom ρ) | exact (kw_lequiv ρ Hl3)].
    + intros ρ a a' ha. eapply LR_lconv; [exact (IHcod ρ a' a ha) | exact (kw_lequiv ρ Hl4)].
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split.
      * apply SigRel_flip; auto.
      * intros H. apply (SigRel_flip (A := A') (A' := A) (domR := flipD domR) (codR := flipC codR));
          auto using lequiv_sym.
Qed.

Theorem LR_sym n : Psym n.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_sym_step, IHn.
Qed.

Corollary LogRel_sym l G Γ T T' l' R :
  LogRel l G Γ T T' l' R -> LogRel l G Γ T' T l' (flipR R).
Proof. apply LR_sym. Qed.

End Symmetry.
