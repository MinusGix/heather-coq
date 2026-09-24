(** * Transitivity (ch. 7, Reflexivity and Transitivity)

    [LR T1 T2 R12] and [LR T2 T3 R23] give [LR T1 T3 R12] (saturation lets
    the composite keep the left relation), and [R12 ∘ R23 ⊆ R12].  By strong
    induction on the stage and induction on the first derivation.  The Π
    case follows the paper: the codomain is composed through [B2[a/x]],
    which needs [a] related to itself (the induction hypothesis on the
    domain composed with its own symmetric) and left irrelevance. *)
From DeLaM.LogRel Require Export Symmetry.

Section Transitivity.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Left irrelevance *)

Lemma LR_irrel_left n G Γ T T' T'' l R R' :
  LR n (LRbelow n) G Γ T' T l R -> LR n (LRbelow n) G Γ T'' T l R' -> releq R R'.
Proof.
  intros H1 H2. apply LR_sym in H1, H2.
  pose proof (LR_irrel _ _ _ _ _ _ _ _ _ _ H1 H2) as H.
  intros t t'; exact (H t' t).
Qed.

(** ** Generic helpers *)

Lemma geq_ty_refl_r {G Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Γ ⊢ T' ≈ T' @ l ].
Proof. intros H; eapply geq_ty_trans; [apply geq_ty_sym, H | exact H]. Qed.

Lemma geq_tm_conv_l {G Γ t t' T T' l l'} :
  [ G ; Γ ⊢ t ≈ t' : T' @ l' ] -> [ G ; Γ ⊢g T' ≅ T @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof. intros; eapply geq_tm_conv; [eapply geq_tm_lconv|]; eauto. Qed.

(** ** Natural numbers and neutrals *)

Lemma NatNf_whnf_l {G Γ w w'} : NatNf G Γ w w' -> whnf w.
Proof. destruct 1; eauto using gne_tm_whne_l with whnf. Qed.
Lemma NatNf_whnf_r {G Γ w w'} : NatNf G Γ w w' -> whnf w'.
Proof. destruct 1; eauto using gne_tm_whne_r with whnf. Qed.

Lemma NatRel_trans G Γ :
  (forall t1 t2, NatRel G Γ t1 t2 -> forall t3, NatRel G Γ t2 t3 -> NatRel G Γ t1 t3).
Proof.
  apply (NatRel_mut G Γ (fun t1 t2 _ => forall t3, NatRel G Γ t2 t3 -> NatRel G Γ t1 t3)
                        (fun t1 t2 _ => forall t3, NatNf G Γ t2 t3 -> NatNf G Γ t1 t3)).
  - intros t1 t2 w1 w2 Hw1 Hw2 Heq Hnf IH t3 H3.
    inversion H3 as [t2' t3' w2' w3 Hw2' Hw3 Heq' Hnf']; subst.
    assert (w2' = w2) as ->
      by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | exact (NatNf_whnf_l Hnf')
                                 | exact (NatNf_whnf_r Hnf)]).
    econstructor; [exact Hw1 | exact Hw3 | eapply geq_tm_trans; eauto | now apply IH].
  - intros t3 H; inversion H; subst; [constructor|].
    match goal with H : [ _ ; _ ⊢ zero ~ _ : _ @ _ ] |- _ => apply gne_tm_whne_l in H; inversion H end.
  - intros t t' Ht IH t3 H; inversion H; subst.
    + constructor; eauto.
    + match goal with H : [ _ ; _ ⊢ succ _ ~ _ : _ @ _ ] |- _ =>
        apply gne_tm_whne_l in H; inversion H end.
  - intros ν ν' Hν t3 H; inversion H; subst.
    + apply gne_tm_whne_r in Hν; inversion Hν.
    + apply gne_tm_whne_r in Hν; inversion Hν.
    + constructor; eapply gne_tm_trans; eauto.
Qed.

Lemma NeRel_trans {G Γ V1 V2 V3 l t1 t2 t3} :
  [ G ; Γ ⊢g V1 ≅ V2 @ l ] -> [ G ; Γ ⊢g V2 ≅ V3 @ l ] ->
  NeRel G Γ V1 V2 l t1 t2 -> NeRel G Γ V2 V3 l t2 t3 -> NeRel G Γ V1 V2 l t1 t3.
Proof.
  intros H12 H23 (ν1 & ν2 & Hν1 & Hν2 & Hn1 & Hn2) (μ2 & μ3 & Hμ2 & Hμ3 & Hm2 & Hm3).
  assert (μ2 = ν2) as ->.
  { eapply tmred_whnf_det; [exact Hμ2 | exact Hν2 | |]; constructor;
      eauto using gne_tm_whne_l, gne_tm_whne_r. }
  exists ν1, μ3. refine (conj Hν1 (conj _ (conj _ _))).
  - eapply tmred_conv; [apply ge_typeof | exact Hμ3 | now apply eqty_sym].
  - eapply gne_tm_trans; [exact Hn1 | eapply gne_tm_conv; [exact Hm2 | now apply eqty_sym]].
  - eapply gne_tm_trans; [exact Hn2 | exact Hm2].
Qed.

(** ** The statement *)

Definition Ptrans n := forall G Γ T1 T2 l R12,
  LR n (LRbelow n) G Γ T1 T2 l R12 -> forall T3 R23,
  LR n (LRbelow n) G Γ T2 T3 l R23 ->
  LR n (LRbelow n) G Γ T1 T3 l R12 /\
  (forall t1 t2 t3, R12 t1 t2 -> R23 t2 t3 -> R12 t1 t3).

(** ** The universe *)

Lemma URel_trans n G Γ l1 l2 t1 t2 t3 :
  Ptrans (lmeasure l1) -> lmeasure l1 < n -> lequiv (gL G) l2 l1 ->
  URel (LRbelow n) G Γ l1 t1 t2 -> URel (LRbelow n) G Γ l2 t2 t3 -> URel (LRbelow n) G Γ l1 t1 t3.
Proof.
  intros Htr Hn Hl (w1 & w2 & Hw1 & Hw2 & Hnf1 & Hnf2 & Heq1 & HK1)
    (w2' & w3 & Hw2' & Hw3 & Hnf2' & Hnf3 & Heq2 & HK2).
  assert (w2' = w2) as -> by (eapply tmred_whnf_det; eauto).
  assert (Hm : lmeasure l2 = lmeasure l1) by (eapply lequiv_measure; eauto).
  exists w1, w3. refine (conj Hw1 (conj (tmred_U_conv Hw3 Hl) (conj Hnf1 (conj Hnf3 (conj _ _))))).
  - eapply geq_tm_trans; [exact Heq1|].
    eapply geq_U_conv; [eapply ctx_of_tm, Hw1 | exact Heq2 | exact Hl].
  - intros la lb Hla Hlb.
    destruct (HK1 la la Hla Hla) as [R1 H1].
    destruct (HK2 la lb) as [R2 H2]; [eapply lequiv_trans; [eassumption | apply lequiv_sym, Hl]..|].
    rewrite LRbelow_spec in H1 by exact Hn. rewrite LRbelow_spec in H2 by lia.
    unfold LogRel in *. rewrite Hm in H2.
    exists R1. rewrite LRbelow_spec by exact Hn.
    exact (proj1 (Htr _ _ _ _ _ _ H1 _ _ (LR_lconv _ _ _ _ _ _ _ _ _ H2 (lequiv_sym _ _ _ Hl)))).
Qed.

(** ** Transitivity *)

Lemma LR_trans_step n : (forall m, m < n -> Ptrans m) -> Ptrans n.
Proof.
  intros IHn G Γ T1 T2 l R12 H.
  induction H as [G Γ T1 T2 l R Hl HT1 HT2 HR
                 | G Γ T1 T2 l l1 l2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l V1 V2 R HT1 HT2 HV HR
                 | G Γ T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 R Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2
                     HA1 HA2 HB1 HB2 HA12 HB12 domAd1 IHdom codAd1 IHcod HR];
    intros T3 R23 H2.
  - (* Nat *)
    destruct (LR_inv_nat H2 HT2) as (_ & HT3 & HR2).
    split; [eapply LRnat; eauto|].
    intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
    eapply NatRel_trans; eauto.
  - (* U *)
    destruct (LR_inv_U H2 HT2) as (l3 & _ & Hl3 & _ & HT3 & HR2).
    assert (Hm : lmeasure l2 = lmeasure l1) by (eapply lequiv_measure; eauto).
    split; [eapply (LRU n (LRbelow n) G Γ T1 T3 l l1 l3); eauto using lequiv_trans|].
    intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
    eapply URel_trans; eauto; try apply IHn; lia.
  - (* neutral *)
    destruct (LR_inv_ne H2 HT2 (gne_ty_whne_r HV)) as (V3 & HT3 & HV23 & HR2).
    assert (E12 : [ G ; Γ ⊢g V1 ≅ V2 @ l ]) by now apply geq_ty_sound, gne_ty_geq.
    assert (E23 : [ G ; Γ ⊢g V2 ≅ V3 @ l ]) by now apply geq_ty_sound, gne_ty_geq.
    split.
    + eapply LRne; eauto using gne_ty_trans.
      eapply releq_trans; [exact HR|]. intros t t'; split; apply NeRel_conv; eauto using eqty_sym.
    + intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
      eapply NeRel_trans; eauto.
  - (* Π *)
    destruct (LR_inv_pi H2 HT2) as (k3 & k4 & A3 & B3 & domR2 & codR2 & Hk & Hk3 & Hk4 & _ & _ &
      HT3 & HA2' & HA3 & HB2' & HB3 & HA23 & HB23 & domAd2 & codAd2 & HR2).
    assert (HΓ : [ G ; Γ ⊢g ]) by exact (ctx_of_ty HA1).
    assert (Hl13 : lequiv (gL G) l1 l3) by now apply lequiv_sym.
    assert (Hl24 : lequiv (gL G) l2 l4) by now apply lequiv_sym.
    (* the composite domain and its relation to the second *)
    assert (Hdom3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A1) (kty ρ A3) l1 (domR1 ρ))
      by (intros ρ; exact (proj1 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd2 ρ) (kw_lequiv ρ Hl13))))).
    assert (Hrefl : forall ρ a a', domR1 ρ a a' -> domR1 ρ a a).
    { intros ρ a a' ha.
      exact (proj2 (IHdom ρ _ _ (LR_sym _ _ _ _ _ _ _ (domAd1 ρ))) a a' a ha ha). }
    assert (H12 : forall ρ a a', domR1 ρ a a' -> domR2 ρ a a').
    { intros ρ a a' ha.
      exact (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ (Hdom3 ρ)
                      (LR_lconv _ _ _ _ _ _ _ _ _ (domAd2 ρ) (kw_lequiv ρ Hl13)) a a') ha). }
    assert (Hcodirr : forall ρ a a1 a2 (h1 : domR1 ρ a a1) (h2 : domR1 ρ a a2),
               releq (codR1 ρ a a1 h1) (codR1 ρ a a2 h2))
      by (intros; eapply LR_irrel; [apply codAd1 | apply codAd1]).
    (* generic and declarative facts about the composite *)
    assert (HA3' : [ G ; Γ ⊢g A3 @ l1 ]) by exact (lconv_ty HA3 Hl3).
    assert (HA13 : [ G ; Γ ⊢ A1 ≈ A3 @ l1 ])
      by (eapply geq_ty_trans; [exact HA12 | eapply geq_ty_lconv; [exact HA23 | exact Hl13]]).
    assert (HB23' : [ G ; Γ ,, A1 @ l1 ⊢ B2 ≈ B3 @ l2 ]).
    { eapply geq_ty_ctxconv; [| exact Hl3 | apply ext_wf_g; [exact HA1 | exact Hw1] |].
      - eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA12 | exact Hl3].
      - eapply geq_ty_lconv; [exact HB23 | exact Hl24]. }
    assert (HB13 : [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B3 @ l2 ]) by (eapply geq_ty_trans; eassumption).
    assert (HP12 : [ G ; Γ ⊢ tyPi l1 l2 A1 B1 ≈ tyPi l3 l4 A2 B2 @ lmax l1 l2 ])
      by (apply geq_ty_pi; auto).
    assert (HP23 : [ G ; Γ ⊢ tyPi l3 l4 A2 B2 ≈ tyPi k3 k4 A3 B3 @ lmax l1 l2 ]).
    { eapply geq_ty_lconv; [apply geq_ty_pi; auto using lequiv_sym | now apply lequiv_max]. }
    assert (HR12 : releq R (PiRel G Γ l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1)).
    { assert (Hd : forall ρ, releq (domR1 ρ) (domR1 ρ)) by (intros; apply releq_refl).
      assert (Hc : forall ρ a a' (ha ha' : domR1 ρ a a'), releq (codR1 ρ a a' ha) (codR1 ρ a a' ha'))
        by (intros; apply Hcodirr).
      pose proof (geq_ty_sound HP23) as HP.
      eapply releq_trans; [exact HR|]. intros t t'; split.
      - exact (PiRel_dir Hw1 HA1 HA2 HA3' HA12 HA13 HB12 HB13 HP Hd Hc t t').
      - exact (PiRel_dir Hw1 HA1 HA3' HA2 HA13 HA12 HB13 HB12 (eqty_sym _ _ _ _ _ _ HP) Hd Hc t t'). }
    split.
    + eapply (LRpi n (LRbelow n) G Γ T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1).
      all: try eassumption.
      * eapply lequiv_trans; eassumption.
      * eapply lequiv_trans; eassumption.
      * eapply (lconv_ty (l := l4)); [|exact Hl4]. eapply ctx_lvl_ty; [exact HA3 | exact Hl3 | exact HB3].
      * intros ρ a a' ha.
        pose proof (Hrefl ρ a a' ha) as haa.
        pose proof (H12 ρ a a' ha) as h2.
        eapply LR_releq; [|apply Hcodirr with (h1 := haa)].
        exact (proj1 (IHcod ρ a a haa _ _
                        (LR_lconv _ _ _ _ _ _ _ _ _ (codAd2 ρ a a' h2) (kw_lequiv ρ Hl24)))).
    + (* terms *)
      intros t1 t2 t3 H12' H23'. apply HR. apply HR in H12'. apply HR2 in H23'.
      destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
      destruct H23' as (w2' & w3 & Hw2r' & Hw3r & Hnf2' & Hnf3 & Heq2 & Heq2' & HK2).
      assert (w2' = w2) as -> by (eapply tmred_whnf_det; eauto).
      assert (Hm34 : lequiv (gL G) (lmax l1 l2) (lmax l3 l4)) by now apply lequiv_max.
      exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
      * eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Hm34] |].
        apply eqty_sym, geq_ty_sound, HP23.
      * eapply geq_tm_trans; [exact Heq1|].
        eapply geq_tm_conv_l; [exact Heq2 | apply eqty_sym, geq_ty_sound, HP12 | exact Hm34].
      * eapply geq_tm_trans; [exact Heq1' | eapply geq_tm_lconv; [exact Heq2 | exact Hm34]].
      * intros ρ a a' ha la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5.
        pose proof (Hrefl ρ a a' ha) as haa.
        pose proof (H12 ρ a a' ha) as h2.
        pose proof (kw_lequiv ρ Hl13) as Hl13'. pose proof (kw_lequiv ρ Hl24) as Hl24'.
        pose proof (kw_lequiv ρ Hl3) as Hl3'. pose proof (kw_lequiv ρ Hl4) as Hl4'.
        pose proof (kw_lwf ρ Hw1) as Hw1'.
        assert (Hw3 : lwf (gL G) l3) by exact (lequiv_wf_l _ _ _ Hl3).
        assert (HA1r : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A1 @ l1 ]) by exact (kw_ty ρ HA1).
        assert (HA2r : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A2 @ l1 ]) by exact (kw_ty ρ HA2).
        assert (HA2_3 : [ G ; Γ ⊢g A2 @ l3 ]) by exact (lconv_ty HA2 Hl13).
        assert (HA3r3 : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A3 @ l3 ]) by exact (kw_ty ρ HA3).
        assert (HΔ2 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l1 ⊢g ]) by exact (kw_ext ρ HA2 Hw1).
        assert (HΔ3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A3 @ l3 ⊢g ]) by exact (kw_ext ρ HA3 Hw3).
        assert (E12 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A1 ≈ kty ρ A2 @ l1 ]) by exact (kw_geq_ty ρ HA12).
        assert (E23 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A2 ≈ kty ρ A3 @ l3 ]) by exact (kw_geq_ty ρ HA23).
        (* reflexive annotations on the middle application *)
        assert (RA2 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A2 ≈ kty ρ A2 @ l1 ]) by exact (geq_ty_refl_r E12).
        assert (RB2 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l1 ⊢ ktyl ρ B2 ≈ ktyl ρ B2 @ l2 ]).
        { apply (geq_ty_refl_r (T := ktyl ρ B1)).
          eapply geq_ty_ctxconv; [apply geq_ty_sound, E12 | now apply lequiv_refl | exact HΔ2 |].
          exact (kw_geq_ty_l ρ HA1 Hw1 HB12). }
        pose proof (HK1 ρ a a haa la lb l1 l2 A4 B4 (kty ρ A2) (ktyl ρ B2) Hla Hlb
                      (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) HA4 HB4 RA2 RB2) as X1.
        assert (X2 : codR2 ρ a a' h2 (app (ktm ρ w2) l1 l2 (kty ρ A2) (ktyl ρ B2) a)
                       (app (ktm ρ w3) la' lb' A5 B5 a')).
        { apply HK2.
          - exact Hl13.
          - exact Hl24.
          - eapply lequiv_trans; [exact Hla' | exact Hl13].
          - eapply lequiv_trans; [exact Hlb' | exact Hl24].
          - eapply geq_ty_lconv; [exact RA2 | exact Hl3'].
          - eapply geq_ty_lconv; [|exact Hl4']. eapply ctx_lvl_geq; [exact HA2r | exact Hl13' | exact RB2].
          - eapply geq_ty_trans; [apply geq_ty_sym, E23 | eapply geq_ty_lconv; [exact HA5 | exact Hl3']].
          - (* [B3 ≈ B5] under [A3]: through [B2] under [A2] *)
            assert (F : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l3 ⊢ ktyl ρ B3 ≈ B5 @ l4 ]).
            { eapply (geq_ty_trans (T' := ktyl ρ B2)).
              - apply geq_ty_sym. exact (kw_geq_ty_l ρ HA2_3 Hw3 HB23).
              - eapply geq_ty_lconv; [|exact Hl4'].
                eapply ctx_lvl_geq; [exact HA2r | exact Hl13' | exact HB5]. }
            eapply geq_ty_ctxconv; [apply geq_ty_sound, E23 | apply lequiv_refl, (kw_lwf ρ Hw3)
                                   | exact HΔ3 | exact F]. }
        pose proof (proj2 (IHcod ρ a a haa _ _
                             (LR_lconv _ _ _ _ _ _ _ _ _ (codAd2 ρ a a' h2) Hl24')) _ _ _ X1 X2) as X3.
        exact (proj1 (Hcodirr ρ a a a' haa ha _ _) X3).
Qed.

Theorem LR_trans n : Ptrans n.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_trans_step, IHn.
Qed.

(** ** Consequences: reflexivity *)

Corollary LR_refl_l n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> LR n (LRbelow n) G Γ T T l R.
Proof. intros H. exact (proj1 (LR_trans n _ _ _ _ _ _ H _ _ (LR_sym _ _ _ _ _ _ _ H))). Qed.

Corollary LR_refl_r n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> LR n (LRbelow n) G Γ T' T' l (flipR R).
Proof. intros H. exact (LR_refl_l _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ H)). Qed.

(** Related terms are related to themselves. *)
Corollary LR_tm_refl_l n G Γ T T' l R t t' :
  LR n (LRbelow n) G Γ T T' l R -> R t t' -> R t t.
Proof.
  intros H Ht. exact (proj2 (LR_trans n _ _ _ _ _ _ H _ _ (LR_sym _ _ _ _ _ _ _ H)) t t' t Ht Ht).
Qed.

End Transitivity.
