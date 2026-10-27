(** * Transitivity (ch. 7, Reflexivity and Transitivity)

    [LR T1 T2 R12] and [LR T2 T3 R23] give [LR T1 T3 R12] (saturation lets
    the composite keep the left relation), and [R12 ∘ R23 ⊆ R12].  By strong
    induction on the stage and induction on the first derivation.  The Π
    case follows the paper: the codomain is composed through [B2[a/x]],
    which needs [a] related to itself (the induction hypothesis on the
    domain composed with its own symmetric) and left irrelevance. *)
From DeLaM.LogRel Require Export Symmetry.
From DeLaM.LogRel Require Import IWfAux MAux.

Section Transitivity.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Left irrelevance *)

Lemma LR_irrel_left n G Γ T T' T'' l R R' :
  LR n (LRbelow n) G Γ T' T l R -> LR n (LRbelow n) G Γ T'' T l R' -> releq R R'.
Proof using EL VL.
  intros H1 H2. apply LR_sym in H1, H2.
  pose proof (LR_irrel _ _ _ _ _ _ _ _ _ _ H1 H2) as H.
  intros t t'; exact (H t' t).
Qed.

(** ** Generic helpers *)

Lemma geq_ty_refl_r {G Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Γ ⊢ T' ≈ T' @ l ].
Proof using EL. intros H; eapply geq_ty_trans; [apply geq_ty_sym, H | exact H]. Qed.

Lemma geq_tm_conv_l {G Γ t t' T T' l l'} :
  [ G ; Γ ⊢ t ≈ t' : T' @ l' ] -> [ G ; Γ ⊢g T' ≅ T @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof using EL. intros; eapply geq_tm_conv; [eapply geq_tm_lconv|]; eauto. Qed.

(** ** Natural numbers and neutrals *)

Lemma NatRel_trans G Γ :
  (forall t1 t2, NatRel G Γ t1 t2 -> forall t3, NatRel G Γ t2 t3 -> NatRel G Γ t1 t3).
Proof using EL.
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
Proof using EL.
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
Proof using EL.
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

(** ** The shared type-level data of a binder former, composed *)

Lemma poly_trans {F G Γ T1 T2 T3 l l1 l2 l3 l4 k3 k4 A1 B1 A2 B2 A3 B3} :
  PolyFacts G Γ F T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 ->
  PolyFacts G Γ F T2 T3 l l3 l4 k3 k4 A2 B2 A3 B3 ->
  PolyFacts G Γ F T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3.
Proof using EL.
  intros [Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HA1 HA2 HB1 HB2 HA12 HB12]
         [_ Hk3 Hk4 _ _ _ HT3 _ HA3 _ HB3 HA23 HB23].
  assert (Hl13 : lequiv (gL G) l1 l3) by solve [apply lequiv_sym; assumption].
  assert (Hl24 : lequiv (gL G) l2 l4) by solve [apply lequiv_sym; assumption].
  assert (HA13 : [ G ; Γ ⊢ A1 ≈ A3 @ l1 ])
    by (eapply geq_ty_trans; [exact HA12 | eapply geq_ty_lconv; [exact HA23 | exact Hl13]]).
  assert (HB23' : [ G ; Γ ,, A1 @ l1 ⊢ B2 ≈ B3 @ l2 ]).
  { eapply geq_ty_ctxconv; [| exact Hl3 | apply ext_wf_g; [exact HA1 | exact Hw1] |].
    - eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA12 | exact Hl3].
    - eapply geq_ty_lconv; [exact HB23 | exact Hl24]. }
  split; try eassumption.
  - eapply lequiv_trans; eassumption.
  - eapply lequiv_trans; eassumption.
  - exact (lconv_ty HA3 Hl3).
  - eapply (lconv_ty (l := l4)); [|exact Hl4]. eapply ctx_lvl_ty; [exact HA3 | exact Hl3 | exact HB3].
  - eapply geq_ty_trans; eassumption.
Qed.

(** ** Π's and Σ's term relations, composed, given the composition of
    their domain and codomain relations (M18b: [M]'s observations) *)

Section BinTrans.
Context {G : gctx} {Γ : ctx} {l1 l2 l3 l4 k3 k4 : lvl} {A1 B1 A2 B2 A3 B3 : ty}
  {domR1 : DomRel G Γ} {codR1 : CodRel G Γ domR1} {domR2 : DomRel G Γ} {codR2 : CodRel G Γ domR2}
  (Hl3 : lequiv (gL G) l3 l1) (Hl4 : lequiv (gL G) l4 l2)
  (Hk3 : lequiv (gL G) k3 l3) (Hk4 : lequiv (gL G) k4 l4)
  (Hw1 : lwf (gL G) l1) (Hw2 : lwf (gL G) l2)
  (HA1 : [ G ; Γ ⊢g A1 @ l1 ]) (HA2 : [ G ; Γ ⊢g A2 @ l1 ]) (HA3 : [ G ; Γ ⊢g A3 @ l3 ])
  (HA12 : [ G ; Γ ⊢ A1 ≈ A2 @ l1 ]) (HB12 : [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B2 @ l2 ])
  (HA23 : [ G ; Γ ⊢ A2 ≈ A3 @ l3 ]) (HB23 : [ G ; Γ ,, A2 @ l3 ⊢ B2 ≈ B3 @ l4 ]).

(* the facts both formers' proofs share, at a world *)
Local Ltac bin_world ρ :=
  pose proof (lequiv_sym _ _ _ Hl3) as Hl13; pose proof (lequiv_sym _ _ _ Hl4) as Hl24;
  pose proof (kw_lequiv ρ Hl13) as Hl13'; pose proof (kw_lequiv ρ Hl24) as Hl24';
  pose proof (kw_lequiv ρ Hl3) as Hl3'; pose proof (kw_lequiv ρ Hl4) as Hl4';
  pose proof (kw_lwf ρ Hw1) as Hw1';
  assert (Hw3 : lwf (gL G) l3) by exact (lequiv_wf_l _ _ _ Hl3);
  assert (HA2r : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A2 @ l1 ]) by exact (kw_ty ρ HA2);
  assert (HA2_3 : [ G ; Γ ⊢g A2 @ l3 ]) by exact (lconv_ty HA2 Hl13);
  assert (HΔ2 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l1 ⊢g ]) by exact (kw_ext ρ HA2 Hw1);
  assert (HΔ3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A3 @ l3 ⊢g ]) by exact (kw_ext ρ HA3 Hw3);
  assert (E12 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A1 ≈ kty ρ A2 @ l1 ]) by exact (kw_geq_ty ρ HA12);
  assert (E23 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A2 ≈ kty ρ A3 @ l3 ]) by exact (kw_geq_ty ρ HA23);
  assert (RA2 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A2 ≈ kty ρ A2 @ l1 ]) by exact (geq_ty_refl_r E12);
  assert (RB2 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l1 ⊢ ktyl ρ B2 ≈ ktyl ρ B2 @ l2 ])
    by (apply (geq_ty_refl_r (T := ktyl ρ B1));
        eapply geq_ty_ctxconv; [apply geq_ty_sound, E12 | now apply lequiv_refl | exact HΔ2 |];
        exact (kw_geq_ty_l ρ HA1 Hw1 HB12)).

Lemma bin_geq_23 F (HF : forall l1 l2 l3 l4 A A' B B', lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ F l1 l2 A B ≈ F l3 l4 A' B' @ lmax l1 l2 ]) :
  [ G ; Γ ⊢ F l1 l2 A1 B1 ≈ F l3 l4 A2 B2 @ lmax l1 l2 ] /\
  [ G ; Γ ⊢ F l3 l4 A2 B2 ≈ F k3 k4 A3 B3 @ lmax l1 l2 ].
Proof using EL HA1 HA12 HB12 Hl3 Hl4 Hk3 Hk4 HA2 HA23 HB23.
  pose proof (lequiv_sym _ _ _ Hl3) as Hl13. pose proof (lequiv_sym _ _ _ Hl4) as Hl24.
  split; [now apply HF|].
  eapply geq_ty_lconv; [apply HF; [apply lequiv_sym, Hk3 | apply lequiv_sym, Hk4 | exact (lconv_ty HA2 Hl13) | exact HA23 | exact HB23]
                       | now apply lequiv_max].
Qed.

Lemma SigRel_trans
  (Hdomc : forall ρ a b c, domR1 ρ a b -> domR2 ρ b c -> domR1 ρ a c)
  (Hcodc : forall ρ a b c (h1 : domR1 ρ a b) (h2 : domR2 ρ b c) (h : domR1 ρ a c) u v w,
     codR1 ρ a b h1 u v -> codR2 ρ b c h2 v w -> codR1 ρ a c h u w) t1 t2 t3 :
  SigRel G Γ l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 t1 t2 ->
  SigRel G Γ l3 l4 k3 k4 A2 B2 A3 B3 domR2 codR2 t2 t3 ->
  SigRel G Γ l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 t1 t3.
Proof using EL HA1 HA12 HA2 HA23 HA3 HB12 HB23 Hk3 Hk4 Hl3 Hl4 Hw1 Hw2.
  intros H12' H23'.
  destruct (bin_geq_23 tySig (@geq_ty_sig _ _ G Γ)) as [HP12 HP23].
  destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
  destruct H23' as (w2' & w3 & Hw2r' & Hw3r & Hnf2' & Hnf3 & Heq2 & Heq2' & HK2).
  assert (w2' = w2) as -> by (eapply tmred_whnf_det; eauto).
  assert (Hm34 : lequiv (gL G) (lmax l1 l2) (lmax l3 l4)) by (apply lequiv_max; apply lequiv_sym; assumption).
  exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
  - eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Hm34] |].
    apply eqty_sym, geq_ty_sound, HP23.
  - eapply geq_tm_trans; [exact Heq1|].
    eapply geq_tm_conv_l; [exact Heq2 | apply eqty_sym, geq_ty_sound, HP12 | exact Hm34].
  - eapply geq_tm_trans; [exact Heq1' | eapply geq_tm_lconv; [exact Heq2 | exact Hm34]].
  - intros ρ la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5.
    bin_world ρ.
    destruct (HK1 ρ la lb l1 l2 A4 B4 (kty ρ A2) (ktyl ρ B2) Hla Hlb
                (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) HA4 HB4 RA2 RB2) as [h1 C1].
    assert (X2 : exists h2 : domR2 ρ (tmFst l1 l2 (kty ρ A2) (ktyl ρ B2) (ktm ρ w2))
                                    (tmFst la' lb' A5 B5 (ktm ρ w3)),
               codR2 ρ _ _ h2 (tmSnd l1 l2 (kty ρ A2) (ktyl ρ B2) (ktm ρ w2))
                              (tmSnd la' lb' A5 B5 (ktm ρ w3))).
    { apply HK2.
          - exact Hl13.
          - exact Hl24.
          - eapply lequiv_trans; [exact Hla' | exact Hl13].
          - eapply lequiv_trans; [exact Hlb' | exact Hl24].
          - eapply geq_ty_lconv; [exact RA2 | exact Hl3'].
          - eapply geq_ty_lconv; [|exact Hl4']. eapply ctx_lvl_geq; [exact HA2r | exact Hl13' | exact RB2].
          - eapply geq_ty_trans; [apply geq_ty_sym, E23 | eapply geq_ty_lconv; [exact HA5 | exact Hl3']].
          - assert (F : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l3 ⊢ ktyl ρ B3 ≈ B5 @ l4 ]).
            { eapply (geq_ty_trans (T' := ktyl ρ B2)).
              - apply geq_ty_sym. exact (kw_geq_ty_l ρ HA2_3 Hw3 HB23).
              - eapply geq_ty_lconv; [|exact Hl4'].
                eapply ctx_lvl_geq; [exact HA2r | exact Hl13' | exact HB5]. }
            eapply geq_ty_ctxconv; [apply geq_ty_sound, E23 | apply lequiv_refl, (kw_lwf ρ Hw3)
                                   | exact HΔ3 | exact F].
    }
    destruct X2 as [h2 C2].
    pose proof (Hdomc ρ _ _ _ h1 h2) as h. exists h.
    exact (Hcodc ρ _ _ _ h1 h2 h _ _ _ C1 C2).
Qed.

Lemma PiRel_trans
  (Hrefl : forall ρ a a', domR1 ρ a a' -> domR1 ρ a a)
  (H12 : forall ρ a a', domR1 ρ a a' -> domR2 ρ a a')
  (Hcodc : forall ρ a a' (haa : domR1 ρ a a) (h2 : domR2 ρ a a') (ha : domR1 ρ a a') u v w,
     codR1 ρ a a haa u v -> codR2 ρ a a' h2 v w -> codR1 ρ a a' ha u w) t1 t2 t3 :
  PiRel G Γ l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 t1 t2 ->
  PiRel G Γ l3 l4 k3 k4 A2 B2 A3 B3 domR2 codR2 t2 t3 ->
  PiRel G Γ l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 t1 t3.
Proof using EL HA1 HA12 HA2 HA23 HA3 HB12 HB23 Hk3 Hk4 Hl3 Hl4 Hw1 Hw2.
  intros H12' H23'.
  destruct (bin_geq_23 tyPi (@geq_ty_pi _ _ G Γ)) as [HP12 HP23].
  destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
  destruct H23' as (w2' & w3 & Hw2r' & Hw3r & Hnf2' & Hnf3 & Heq2 & Heq2' & HK2).
  assert (w2' = w2) as -> by (eapply tmred_whnf_det; eauto).
  assert (Hm34 : lequiv (gL G) (lmax l1 l2) (lmax l3 l4)) by (apply lequiv_max; apply lequiv_sym; assumption).
  exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
  - eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Hm34] |].
    apply eqty_sym, geq_ty_sound, HP23.
  - eapply geq_tm_trans; [exact Heq1|].
    eapply geq_tm_conv_l; [exact Heq2 | apply eqty_sym, geq_ty_sound, HP12 | exact Hm34].
  - eapply geq_tm_trans; [exact Heq1' | eapply geq_tm_lconv; [exact Heq2 | exact Hm34]].
  - intros ρ a a' ha la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5.
    pose proof (Hrefl ρ a a' ha) as haa.
    pose proof (H12 ρ a a' ha) as h2.
    bin_world ρ.
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
          - assert (F : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l3 ⊢ ktyl ρ B3 ≈ B5 @ l4 ]).
            { eapply (geq_ty_trans (T' := ktyl ρ B2)).
              - apply geq_ty_sym. exact (kw_geq_ty_l ρ HA2_3 Hw3 HB23).
              - eapply geq_ty_lconv; [|exact Hl4'].
                eapply ctx_lvl_geq; [exact HA2r | exact Hl13' | exact HB5]. }
            eapply geq_ty_ctxconv; [apply geq_ty_sound, E23 | apply lequiv_refl, (kw_lwf ρ Hw3)
                                   | exact HΔ3 | exact F].
    }
    exact (Hcodc ρ a a' haa h2 ha _ _ _ X1 X2).
Qed.

End BinTrans.

(** ** [M]'s relation, composed (M18b)

    By induction on the depth, as its flip ([MRn_flip]): the generic
    clauses compose, [out]'s observations by [SigRel_trans] and, in its
    codomain, [PiRel_trans], whose codomain is the induction hypothesis on
    the children. The composite keeps the first pair's signatures and
    indices; its codomain is moved from the middle shape and position to
    the third's by [PiRel_dir] and [MRn_dir], which is where the
    relations' irrelevance in their right arguments is used. *)
Section MTrans.

(** The shapes' and positions' relations depend on their right index and
    shape only up to the index's relation ([LR_irrel]'s consequence). *)
Definition MShIrr {G Γ} (idxR : DomRel G Γ) (shR : MShRel G Γ) : Prop :=
  forall ρ x y y', idxR ρ x y -> idxR ρ x y' -> releq (shR ρ x y) (shR ρ x y').

Definition MPosIrr {G Γ} (idxR : DomRel G Γ) (shR : MShRel G Γ) (posR : MPosRel G Γ) : Prop :=
  forall ρ x y y' a b b', idxR ρ x y -> idxR ρ x y' -> shR ρ x y a b -> shR ρ x y' a b' ->
    releq (posR ρ x y a b) (posR ρ x y' a b').

(** The hypotheses of a composition: the two sides, their indices, and
    what the relations' own transitivity, irrelevance and reflexivity
    give (the induction hypotheses at [LRm]'s premises). *)
Definition MTransHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    (I1 I2 : DomRel G Γ) (S1 S2 : MShRel G Γ) (P1 P2 : MPosRel G Γ) (m m' m'' : tm) : Prop :=
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' I1 S1 P1 /\
  MSide G Γ r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' I2 S2 P2 /\
  nftm m /\ nftm m' /\ nftm m'' /\
  (forall ρ, I1 ρ (ktm ρ m) (ktm ρ m')) /\ (forall ρ, I2 ρ (ktm ρ m') (ktm ρ m'')) /\
  (forall ρ x y z a b c, I1 ρ x y -> I2 ρ y z -> S1 ρ x y a b -> S2 ρ y z b c -> S1 ρ x y a c) /\
  MShIrr I1 S1 /\ MPosIrr I1 S1 P1 /\
  (forall ρ x y a b p q, I1 ρ x y -> S1 ρ x y a b -> P1 ρ x y a b p q -> P1 ρ x y a b p p) /\
  (forall ρ x y z a b c p q, I1 ρ x y -> I2 ρ y z -> S1 ρ x y a b -> S2 ρ y z b c ->
     P1 ρ x y a b p q -> P2 ρ y z b c p q).

(** [MR_irrel] at one depth. *)
Lemma MRn_irrel n {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    idxR idxR' shR shR' posR posR' m m' m''} :
  MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' idxR idxR' shR shR' posR posR' m m' m'' ->
  releq (MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m')
        (MRn n G Γ l1 l2 li X A B C s1 s2 si X'' A'' B'' C'' shR' posR' m m'').
Proof using EL.
  intros H t t'; split; intros Ht.
  - eapply MRn_dir; [exact H | exact Ht].
  - eapply MRn_dir; [exact (MIrrHyps_swap H) | exact Ht].
Qed.

(** One side against itself at another right index. *)
Lemma MIrrHyps_self {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m' m''} :
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR ->
  MShIrr idxR shR -> MPosIrr idxR shR posR -> nftm m -> nftm m' -> nftm m'' ->
  (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) -> (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m'')) ->
  MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' r1 r2 ri X' A' B' C'
    idxR idxR shR shR posR posR m m' m''.
Proof using.
  intros HM Si Pi N N' N'' I I'.
  refine (conj HM (conj HM (conj Si (conj _ (conj N (conj N' (conj N'' (conj I I')))))))).
  intros ρ x x' x'' a a' h h' ha. exact (Pi ρ x x' x'' a a' a' h h' ha (proj1 (Si ρ x x' x'' h h' a a') ha)).
Qed.

Lemma MShIrr_kw {G Γ idxR shR} (ρ : kwk G Γ) :
  MShIrr idxR shR -> MShIrr (fun ρ' => idxR (kw_comp ρ ρ')) (fun ρ' => shR (kw_comp ρ ρ')).
Proof using. intros H ρ'. exact (H (kw_comp ρ ρ')). Qed.

Lemma MPosIrr_kw {G Γ idxR shR posR} (ρ : kwk G Γ) :
  MPosIrr idxR shR posR ->
  MPosIrr (fun ρ' => idxR (kw_comp ρ ρ')) (fun ρ' => shR (kw_comp ρ ρ')) (fun ρ' => posR (kw_comp ρ ρ')).
Proof using. intros H ρ'. exact (H (kw_comp ρ ρ')). Qed.

(** The hypotheses at a child: the first pair's at the middle position
    on both sides, the second pair's at the middle and the third. *)
Lemma MTransHyps_child {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    I1 I2 S1 S2 P1 P2 m m' m''} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a b c p p' :
  MTransHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' I1 I2 S1 S2 P1 P2 m m' m'' ->
  S1 ρ (ktm ρ m) (ktm ρ m') a b -> S2 ρ (ktm ρ m') (ktm ρ m'') b c ->
  P1 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' b) p p ->
  P2 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m') (ktm (kw_comp ρ ρ') m'') (ktm ρ' b) (ktm ρ' c) p p' ->
  MTransHyps (kw_G ρ') (kw_Δ ρ')
    l1 l2 li (kty (kw_comp ρ ρ') X) (ktyl (kw_comp ρ ρ') A) (ktyll (kw_comp ρ ρ') B) (ktmlll (kw_comp ρ ρ') C)
    r1 r2 ri (kty (kw_comp ρ ρ') X') (ktyl (kw_comp ρ ρ') A') (ktyll (kw_comp ρ ρ') B') (ktmlll (kw_comp ρ ρ') C')
    s1 s2 si (kty (kw_comp ρ ρ') X'') (ktyl (kw_comp ρ ρ') A'') (ktyll (kw_comp ρ ρ') B'')
      (ktmlll (kw_comp ρ ρ') C'')
    (fun ρ'' => I1 (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => I2 (kw_comp (kw_comp ρ ρ') ρ''))
    (fun ρ'' => S1 (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => S2 (kw_comp (kw_comp ρ ρ') ρ''))
    (fun ρ'' => P1 (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => P2 (kw_comp (kw_comp ρ ρ') ρ''))
    (ktmlll (kw_comp ρ ρ') C)[lsingle3 (ktm (kw_comp ρ ρ') m) (ktm ρ' a) p]
    (ktmlll (kw_comp ρ ρ') C')[lsingle3 (ktm (kw_comp ρ ρ') m') (ktm ρ' b) p]
    (ktmlll (kw_comp ρ ρ') C'')[lsingle3 (ktm (kw_comp ρ ρ') m'') (ktm ρ' c) p'].
Proof using EL.
  intros (HM1 & HM2 & Nm & Nm' & Nm'' & I1m & I2m & Sc & Si & Pi & Pr & P12) h1 h2 hp1 hp2.
  destruct (MSide_child ρ ρ' a b p p HM1 Nm Nm' I1m h1 hp1) as (N1 & N2 & J1).
  destruct (MSide_child ρ ρ' b c p p' HM2 Nm' Nm'' I2m h2 hp2) as (_ & N3 & J2).
  refine (conj (MSide_kw (kw_comp ρ ρ') HM1) (conj (MSide_kw (kw_comp ρ ρ') HM2) (conj N1 (conj N2 (conj N3 (conj J1 (conj J2 _))))))).
  refine (conj _ (conj (MShIrr_kw (kw_comp ρ ρ') Si) (conj (MPosIrr_kw (kw_comp ρ ρ') Pi) (conj _ _)))).
  - intros ρ''. exact (Sc _).
  - intros ρ''. exact (Pr _).
  - intros ρ''. exact (P12 _).
Qed.

(** One composition at a depth. *)
Definition MTransAt n := forall G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    I1 I2 S1 S2 P1 P2 m m' m'',
  MTransHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' I1 I2 S1 S2 P1 P2 m m' m'' ->
  forall t1 t2 t3,
    MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' t1 t2 ->
    MRn n G Γ r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' S2 P2 m' m'' t2 t3 ->
    MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' t1 t3.

Lemma MPi_trans n (IH : MTransAt n) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    I1 I2 S1 S2 P1 P2 m m' m''}
    (H : MTransHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
           I1 I2 S1 S2 P1 P2 m m' m'')
    (ρ : kwk G Γ) a b c (h1 : S1 ρ (ktm ρ m) (ktm ρ m') a b) (h2 : S2 ρ (ktm ρ m') (ktm ρ m'') b c)
    (h : S1 ρ (ktm ρ m) (ktm ρ m') a c) u v w :
  MKidRel n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' ρ a b u v ->
  MKidRel n G Γ r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' S2 P2 m' m'' ρ b c v w ->
  MKidRel n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' ρ a c u w.
Proof using EL.
  pose proof H as (HM1 & HM2 & Nm & Nm' & Nm'' & I1m & I2m & Sc & Si & Pi & Pr & P12).
  pose proof (ms_geq HM1) as HG1. pose proof (ms_geq HM2) as HG2.
  pose proof HG1 as (Hr1 & Hr2 & Hri & (W1 & W2 & Wi & _) & _).
  pose proof HG2 as (Hs1 & Hs2 & Hsi & _).
  pose proof (lequiv_wf_r _ _ _ Hr2) as Wr2.
  assert (Hm : lequiv (gL G) (mlvl l1 l2 li) (mlvl r1 r2 ri)) by (apply lequiv_mlvl; assumption).
  assert (Hm' : lequiv (gL G) (mlvl r1 r2 ri) (mlvl s1 s2 si)) by (apply lequiv_mlvl; assumption).
  assert (Wm : lwf (gL G) (mlvl l1 l2 li)) by (split; [split|]; assumption).
  unfold MKidRel. rewrite !kw_B_single, !kw_mKid. rewrite !mKid_single by kw_nf.
  intros Y1 Y2.
  (* the families at the three shapes *)
  pose proof (ms_gBa HM1 ρ _ _ a b (I1m ρ) h1) as GB1.
  pose proof (ms_gBa HM2 ρ _ _ b c (I2m ρ) h2) as GB2.
  pose proof (ms_gBa HM1 ρ _ _ a c (I1m ρ) h) as GB1'.
  pose proof (geq_ty_sound GB1) as DB1. pose proof (geq_ty_sound GB2) as DB2.
  pose proof (geq_ty_sound GB1') as DB1'.
  pose proof (eqty_wf_l ge_typeof DB1) as HB.
  pose proof (eqty_wf_r ge_typeof DB1) as HBb. pose proof (eqty_wf_r ge_typeof DB1') as HBc.
  pose proof (eqty_wf_l ge_typeof DB2) as HBb'. pose proof (eqty_wf_r ge_typeof DB2) as HBc'.
  pose proof (ext_wf_g HB (kw_lwf ρ W2)) as HΔB.
  pose proof (ext_wf_g HBb' (kw_lwf ρ Wr2)) as HΔB'.
  pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG1) HΔB) (ms_gCa HM1 ρ _ _ a b (I1m ρ) h1)) as K1.
  pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG2) HΔB') (ms_gCa HM2 ρ _ _ b c (I2m ρ) h2)) as K2.
  pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG1) HΔB) (ms_gCa HM1 ρ _ _ a c (I1m ρ) h)) as K1'.
  (* the shapes in the positions' worlds *)
  assert (Sab : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
             S1 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' b)).
  { intros ρ'. rewrite !(ktm_comp ρ ρ'). exact (ms_shmon HM1 ρ ρ' _ _ _ _ (I1m ρ) h1). }
  assert (Sac : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
             S1 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' c)).
  { intros ρ'. rewrite !(ktm_comp ρ ρ'). exact (ms_shmon HM1 ρ ρ' _ _ _ _ (I1m ρ) h). }
  assert (Sbc : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
             S2 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m') (ktm (kw_comp ρ ρ') m'') (ktm ρ' b) (ktm ρ' c)).
  { intros ρ'. rewrite !(ktm_comp ρ ρ'). exact (ms_shmon HM2 ρ ρ' _ _ _ _ (I2m ρ) h2). }
  (* compose at the middle shape [b] *)
  refine (PiRel_dir (kw_lwf ρ W2) HB HBb HBc GB1 GB1' K1 K1' _ _ _ u w
            (PiRel_trans (kw_lequiv ρ (lequiv_sym _ _ _ Hr2)) (kw_lequiv ρ (lequiv_sym _ _ _ Hm))
               (kw_lequiv ρ (lequiv_sym _ _ _ Hs2)) (kw_lequiv ρ (lequiv_sym _ _ _ Hm'))
               (kw_lwf ρ W2) (kw_lwf ρ Wm) HB (lconv_ty HBb' (kw_lequiv ρ (lequiv_sym _ _ _ Hr2))) HBc'
               GB1 K1 GB2 K2 _ _ _ u v w Y1 Y2)).
  - eapply (eqty_trans _ _ _ _ (tyPi l2 (mlvl l1 l2 li) (ktyll ρ B)[lsingle2 (ktm ρ m) a]
        (tyM l1 l2 li (kty ρ X)⟨↑⟩ (ktyl ρ A)⟨rlift ↑⟩ (ktyll ρ B)⟨rlift (rlift ↑)⟩
           (ktmlll ρ C)⟨rlift (rlift (rlift ↑))⟩ (ktmlll ρ C)[llift (lsingle2 (ktm ρ m) a)])));
      [apply eqty_sym|]; apply geq_ty_sound, geq_ty_pi;
      first [ exact HB | exact GB1 | exact GB1' | exact K1 | exact K1'
            | apply kw_lequiv; assumption | apply lequiv_mlvl; apply kw_lequiv; assumption ].
  - intros ρ'. exact (Pi _ _ _ _ _ _ _ (I1m _) (I1m _) (Sab ρ') (Sac ρ')).
  - (* the children at the middle shape and the third's, by irrelevance *)
    intros ρ' p p' hp hp'.
    destruct (MSide_child ρ ρ' a b p p' HM1 Nm Nm' I1m h1 hp) as (N1 & N2 & J1).
    destruct (MSide_child ρ ρ' a c p p' HM1 Nm Nm' I1m h hp') as (_ & N3 & J3).
    exact (MRn_irrel n (MIrrHyps_self (MSide_kw (kw_comp ρ ρ') HM1) (MShIrr_kw _ Si) (MPosIrr_kw _ Pi)
                         N1 N2 N3 J1 J3)).
  - intros ρ' p p' hp. exact (Pr _ _ _ _ _ _ _ (I1m _) (Sab ρ') hp).
  - intros ρ' p p' hp. exact (P12 _ _ _ _ _ _ _ _ _ (I1m _) (I2m _) (Sab ρ') (Sbc ρ') hp).
  - (* the children: the induction hypothesis, moved to the right position *)
    intros ρ' p p' hpp h2' hp x y z Z1 Z2.
    pose proof (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (MTransHyps_child ρ ρ' a b c p p' H h1 h2 hpp h2') x y z Z1 Z2) as Z.
    destruct (MSide_child ρ ρ' a b p p HM1 Nm Nm' I1m h1 hpp) as (N1 & N2 & J1).
    destruct (MSide_child ρ ρ' a b p p' HM1 Nm Nm' I1m h1 hp) as (_ & N3 & J3).
    exact (proj1 (MRn_irrel n (MIrrHyps_self (MSide_kw (kw_comp ρ ρ') HM1) (MShIrr_kw _ Si) (MPosIrr_kw _ Pi)
                                N1 N2 N3 J1 J3) x z) Z).
Qed.

(** The hypotheses in a world. *)
Lemma MTransHyps_kw {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    I1 I2 S1 S2 P1 P2 m m' m''} (ρ : kwk G Γ) :
  MTransHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' I1 I2 S1 S2 P1 P2 m m' m'' ->
  MTransHyps (kw_G ρ) (kw_Δ ρ) l1 l2 li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C)
    r1 r2 ri (kty ρ X') (ktyl ρ A') (ktyll ρ B') (ktmlll ρ C') s1 s2 si (kty ρ X'') (ktyl ρ A'') (ktyll ρ B'') (ktmlll ρ C'')
    (fun ρ' => I1 (kw_comp ρ ρ')) (fun ρ' => I2 (kw_comp ρ ρ')) (fun ρ' => S1 (kw_comp ρ ρ'))
    (fun ρ' => S2 (kw_comp ρ ρ')) (fun ρ' => P1 (kw_comp ρ ρ')) (fun ρ' => P2 (kw_comp ρ ρ'))
    (ktm ρ m) (ktm ρ m') (ktm ρ m'').
Proof using EL.
  intros (HM1 & HM2 & _ & _ & _ & I1m & I2m & Sc & Si & Pi & Pr & P12).
  refine (conj (MSide_kw ρ HM1) (conj (MSide_kw ρ HM2) (conj _ (conj _ (conj _
            (conj (MIdx_kw ρ I1m) (conj (MIdx_kw ρ I2m) _))))))).
  1-3: kw_nf.
  refine (conj _ (conj (MShIrr_kw ρ Si) (conj (MPosIrr_kw ρ Pi) (conj _ _)))).
  - intros ρ'. exact (Sc _).
  - intros ρ'. exact (Pr _).
  - intros ρ'. exact (P12 _).
Qed.

(** The observations, given the children's. *)
Lemma MObs_trans n (IH : MTransAt n) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    I1 I2 S1 S2 P1 P2 m m' m''} :
  MTransHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' I1 I2 S1 S2 P1 P2 m m' m'' ->
  forall t1 t2 t3,
    MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' t1 t2 ->
    MObs (MRn n) G Γ r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' S2 P2 m' m'' t2 t3 ->
    MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' t1 t3.
Proof using EL.
  intros H t1 t2 t3 H12 H23.
  pose proof H as (HM1 & HM2 & Nm & Nm' & Nm'' & I1m & I2m & Sc & _).
  pose proof (ms_geq HM1) as HG1; pose proof (ms_geq HM2) as HG2.
  destruct (MSide_root HM1 Nm Nm' I1m) as (Em1 & EA1 & EB1 & EC1).
  destruct (MSide_root HM2 Nm' Nm'' I2m) as (Em2 & EA2 & EB2 & EC2).
  pose proof HG1 as (Hr1 & Hr2 & Hri & (W1 & W2 & Wi & _) & _).
  pose proof HG2 as (Hs1 & Hs2 & Hsi & _ & HXX2 & _).
  assert (Hm : lequiv (gL G) (mlvl l1 l2 li) (mlvl r1 r2 ri)) by (apply lequiv_mlvl; assumption).
  intros k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann'.
  (* the middle annotations, at the third signature *)
  assert (Ann'' : MAnn G Γ s1 s2 si X'' A'' B'' C'' m'' k1' k2' ki' X1' A1' B1' C1' j1').
  { refine (MAnn_conv (MEq_sym ge_typeof ge_notV (MEq_of_MGeq HG2)) _ Ann').
    eapply eqtm_lconv; [| exact (lequiv_sym _ _ _ Hsi)].
    eapply eqtm_conv; [| rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ (geq_ty_sound HXX2))].
    apply eqtm_sym, geq_tm_sound, Em2. }
  specialize (H12 k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann').
  specialize (H23 k1' k2' ki' X1' A1' B1' C1' j1' k1' k2' ki' X1' A1' B1' C1' j1' Ann' Ann'').
  pose proof (geq_ty_sound EA1) as DA1. pose proof (geq_ty_sound EA2) as DA2.
  assert (Wm : lwf (gL G) (mlvl l1 l2 li)) by (split; [split|]; assumption).
  refine (SigRel_trans (lequiv_sym _ _ _ Hr1) (lequiv_sym _ _ _ Hm) (lequiv_sym _ _ _ Hs1)
            (lequiv_sym _ _ _ (lequiv_mlvl Hs1 Hs2 Hsi)) W1 Wm (eqty_wf_l ge_typeof DA1)
            (eqty_wf_r ge_typeof DA1) (eqty_wf_r ge_typeof DA2) EA1 (M_outB_geq HG1 EB1 EC1)
            EA2 (M_outB_geq HG2 EB2 EC2) _ _ _ _ _ H12 H23).
  - intros ρ a b c h1 h2. exact (Sc ρ _ _ _ a b c (I1m ρ) (I2m ρ) h1 h2).
  - intros ρ a b c h1 h2 h u v w Y1 Y2. exact (MPi_trans n IH H ρ a b c h1 h2 h u v w Y1 Y2).
Qed.

Lemma MRn_trans n : MTransAt n.
Proof using EL.
  induction n as [|n IH]; intros G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    I1 I2 S1 S2 P1 P2 m m' m'' H t1 t2 t3 H12 H23.
  all: pose proof H as (HM1 & HM2 & Nm & Nm' & Nm'' & I1m & I2m & Sc & _).
  all: pose proof (ms_geq HM1) as HG1; pose proof (ms_geq HM2) as HG2.
  all: destruct (MSide_root HM1 Nm Nm' I1m) as (Em1 & EA1 & EB1 & EC1).
  all: destruct (MSide_root HM2 Nm' Nm'' I2m) as (Em2 & EA2 & EB2 & EC2).
  all: pose proof HG1 as (Hr1 & Hr2 & Hri & (W1 & W2 & Wi & _) & _).
  all: pose proof HG2 as (Hs1 & Hs2 & Hsi & _ & HXX2 & _).
  all: assert (Hm : lequiv (gL G) (mlvl l1 l2 li) (mlvl r1 r2 ri)) by (apply lequiv_mlvl; assumption).
  all: destruct H12 as [(w1 & w2 & R1 & R2 & Wh1 & Wh2 & E1 & E1') H12].
  all: destruct H23 as [(w2' & w3 & R2' & R3 & Wh2' & Wh3 & E2 & E2') H23].
  all: assert (w2' = w2) as -> by (eapply tmred_whnf_det; eauto).
  all: split;
    [ exists w1, w3; refine (conj R1 (conj _ (conj Wh1 (conj Wh3 (conj _ _)))));
      [ eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact R3 | exact Hm] |];
        eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, (MGeq_M HG2 Em2) | exact Hm]
      | eapply geq_tm_trans; [exact E1 |];
        eapply geq_tm_conv_l; [exact E2 | apply eqty_sym, geq_ty_sound, (MGeq_M HG1 Em1) | exact Hm]
      | eapply geq_tm_trans; [exact E1' | eapply geq_tm_lconv; [exact E2 | exact Hm]] ] |].
  1: exact Logic.I.
  intros ρ. exact (MObs_trans n IH (MTransHyps_kw ρ H) _ _ _ (H12 ρ) (H23 ρ)).
Qed.

End MTrans.

(** ** The identity type, composed (M11a) *)

Lemma IdNf_whnf_l {G Γ l A a b RA w w'} : IdNf G Γ l A a b RA w w' -> whnf w.
Proof using EL. intros [| ν ν' Hν]; [apply whnf_refl | apply whnf_ne; exact (gne_tm_whne_l Hν)]. Qed.
Lemma IdNf_whnf_r {G Γ l A a b RA w w'} : IdNf G Γ l A a b RA w w' -> whnf w'.
Proof using EL. intros [| ν ν' Hν]; [apply whnf_refl | apply whnf_ne; exact (gne_tm_whne_r Hν)]. Qed.

(** The second step's carrier relation is the first one flipped (both have
    the middle carrier on the left), so its facts come back by the PER. *)
Lemma IdRel_trans {G Γ l1 l2 A1 A2 a1 a2 b1 b2 RA RA2 t1 t2 t3} :
  lequiv (gL G) l2 l1 ->
  [ G ; Γ ⊢ A1 ≈ A2 @ l1 ] -> [ G ; Γ ⊢ a1 ≈ a2 : A1 @ l1 ] -> [ G ; Γ ⊢ b1 ≈ b2 : A1 @ l1 ] ->
  [ G ; Γ ⊢g A1 @ l1 ] -> RA a1 a2 -> RA b1 b2 ->
  (forall x y, RA x y -> RA y x) -> (forall x y z, RA x y -> RA y z -> RA x z) ->
  releq (flipR RA) RA2 ->
  IdRel G Γ l1 A1 a1 b1 RA t1 t2 -> IdRel G Γ l2 A2 a2 b2 RA2 t2 t3 -> IdRel G Γ l1 A1 a1 b1 RA t1 t3.
Proof using EL.
  intros Hl2 HA12 Ha12 Hb12 HA1 Hra Hrb Hs Ht Hfl (w1 & w2 & Hw1 & Hw2 & Heq12 & Hn12)
    (u2 & w3 & Hu2 & Hw3 & Heq23 & Hn23).
  assert (HV : [ G ; Γ ⊢g tyId l2 A2 a2 b2 ≅ tyId l1 A1 a1 b1 @ l2 ]).
  { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_id; auto using lequiv_sym | exact Hl2]. }
  assert (F : forall u v, [ G ; Γ ⊢g u ⤳* v : tyId l2 A2 a2 b2 @ l2 ] ->
                [ G ; Γ ⊢g u ⤳* v : tyId l1 A1 a1 b1 @ l1 ]).
  { intros u v H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hl2)].
    eapply tmred_conv; [apply ge_typeof | exact H | exact HV]. }
  assert (Ew2 : w2 = u2)
    by (eapply tmred_whnf_det; [exact Hw2 | exact Hu2 | exact (IdNf_whnf_r Hn12) | exact (IdNf_whnf_l Hn23)]).
  subst u2.
  assert (Heq23' : [ G ; Γ ⊢ w2 ≈ w3 : tyId l1 A1 a1 b1 @ l1 ]).
  { eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq23 | exact HV] | exact (lequiv_sym _ _ _ Hl2)]. }
  exists w1, w3. refine (conj Hw1 (conj (F _ _ Hw3) (conj (geq_tm_trans Heq12 Heq23') _))).
  assert (C : forall C, [ G ; Γ ⊢ A2 ≈ C @ l2 ] -> [ G ; Γ ⊢ A1 ≈ C @ l1 ]).
  { intros C HC. eapply geq_ty_trans; [exact HA12 | eapply geq_ty_lconv; [exact HC | exact (lequiv_sym _ _ _ Hl2)]]. }
  assert (B : forall e1 e2 x, RA e1 e2 -> RA2 e2 x -> RA e1 x).
  { intros e1 e2 x H1 H2. apply Hfl in H2. unfold flipR in H2. exact (Ht _ _ _ H1 (Hs _ _ H2)). }
  destruct Hn12 as [k1 k2 C1 C2 c1 c2 Hk1 Hk2 HC1 HC2 H1 H2 H3 H4 | ν1 ν2 Hν12].
  - inversion Hn23 as [k2' k3 C2' C3 c2' c3 Hk2' Hk3 HC2' HC3 G1 G2 G3 G4 | ν2' ν3 Hν23]; subst.
    + apply idnf_refl; eauto using lequiv_trans.
    + exfalso. pose proof (gne_tm_whne_l Hν23) as Hwh. inversion Hwh.
  - inversion Hn23 as [k2' k3 C2' C3 c2' c3 Hk2' Hk3 HC2' HC3 G1 G2 G3 G4 | ν2' ν3 Hν23]; subst.
    + exfalso. pose proof (gne_tm_whne_r Hν12) as Hwh. inversion Hwh.
    + apply idnf_ne. eapply gne_tm_trans; [exact Hν12 |].
      eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν23 | exact HV] | exact (lequiv_sym _ _ _ Hl2)].
Qed.

(** ** Binary sums, composed (M12b) *)

Lemma SumNf_whnf_l {G Γ l l' A B RA RB w w'} : SumNf G Γ l l' A B RA RB w w' -> whnf w.
Proof using EL. intros [| | ν ν' Hν]; [apply whnf_inl | apply whnf_inr | apply whnf_ne; exact (gne_tm_whne_l Hν)]. Qed.
Lemma SumNf_whnf_r {G Γ l l' A B RA RB w w'} : SumNf G Γ l l' A B RA RB w w' -> whnf w'.
Proof using EL. intros [| | ν ν' Hν]; [apply whnf_inl | apply whnf_inr | apply whnf_ne; exact (gne_tm_whne_r Hν)]. Qed.

(** The payloads compose by the summands' own transitivity, given as the
    composites [RA ∘ RA2 ⊆ RA] and [RB ∘ RB2 ⊆ RB]. *)
Lemma SumRel_trans {G Γ l1 l2 l3 l4 A1 A2 B1 B2 RA RB RA2 RB2 t1 t2 t3} :
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
  [ G ; Γ ⊢ A1 ≈ A2 @ l1 ] -> [ G ; Γ ⊢ B1 ≈ B2 @ l2 ] ->
  (forall x y z, RA x y -> RA2 y z -> RA x z) -> (forall x y z, RB x y -> RB2 y z -> RB x z) ->
  SumRel G Γ l1 l2 A1 B1 RA RB t1 t2 -> SumRel G Γ l3 l4 A2 B2 RA2 RB2 t2 t3 ->
  SumRel G Γ l1 l2 A1 B1 RA RB t1 t3.
Proof using EL.
  intros Hl3 Hl4 HA12 HB12 CRA CRB (w1 & w2 & Hw1 & Hw2 & Heq12 & Hn12)
    (u2 & w3 & Hu2 & Hw3 & Heq23 & Hn23).
  assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
  assert (HV : [ G ; Γ ⊢g tySum l3 l4 A2 B2 ≅ tySum l1 l2 A1 B1 @ lmax l3 l4 ]).
  { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_sum; auto using lequiv_sym | exact Hm]. }
  assert (F : forall u v, [ G ; Γ ⊢g u ⤳* v : tySum l3 l4 A2 B2 @ lmax l3 l4 ] ->
                [ G ; Γ ⊢g u ⤳* v : tySum l1 l2 A1 B1 @ lmax l1 l2 ]).
  { intros u v H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hm)].
    eapply tmred_conv; [apply ge_typeof | exact H | exact HV]. }
  assert (Ew2 : w2 = u2)
    by (eapply tmred_whnf_det; [exact Hw2 | exact Hu2 | exact (SumNf_whnf_r Hn12) | exact (SumNf_whnf_l Hn23)]).
  subst u2.
  assert (Heq23' : [ G ; Γ ⊢ w2 ≈ w3 : tySum l1 l2 A1 B1 @ lmax l1 l2 ]).
  { eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq23 | exact HV] | exact (lequiv_sym _ _ _ Hm)]. }
  exists w1, w3. refine (conj Hw1 (conj (F _ _ Hw3) (conj (geq_tm_trans Heq12 Heq23') _))).
  assert (CA : forall C, [ G ; Γ ⊢ A2 ≈ C @ l3 ] -> [ G ; Γ ⊢ A1 ≈ C @ l1 ]).
  { intros C HC. eapply geq_ty_trans; [exact HA12 | eapply geq_ty_lconv; [exact HC | exact (lequiv_sym _ _ _ Hl3)]]. }
  assert (CB : forall D, [ G ; Γ ⊢ B2 ≈ D @ l4 ] -> [ G ; Γ ⊢ B1 ≈ D @ l2 ]).
  { intros D HD. eapply geq_ty_trans; [exact HB12 | eapply geq_ty_lconv; [exact HD | exact (lequiv_sym _ _ _ Hl4)]]. }
  destruct Hn12 as [k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha
                   | k1 k2 k1' k2' C D C' D' b b' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Hb | ν1 ν2 Hν12];
    inversion Hn23 as [j1 j2 j1' j2' P Q P' Q' c c' Hj1 Hj2 Hj1' Hj2' HE HE' HF HF' Hc
                      | j1 j2 j1' j2' P Q P' Q' c c' Hj1 Hj2 Hj1' Hj2' HE HE' HF HF' Hc | ν2' ν3 Hν23];
    subst.
  all: first
    [ exfalso; match goal with H : [ _ ; _ ⊢ _ ~ _ : _ @ _ ] |- _ =>
        solve [pose proof (gne_tm_whne_l H) as Hwh; inversion Hwh
              | pose proof (gne_tm_whne_r H) as Hwh; inversion Hwh] end
    | solve [apply sumnf_inl; eauto using lequiv_trans]
    | solve [apply sumnf_inr; eauto using lequiv_trans]
    | apply sumnf_ne; eapply gne_tm_trans; [exact Hν12 |];
      eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν23 | exact HV] | exact (lequiv_sym _ _ _ Hm)] ].
Qed.

(** ** Well-founded trees, composed (M13a) *)

Lemma WNf_whnf_l {G Γ l1 l2 A B d c w w'} : WNf G Γ l1 l2 A B d c w w' -> whnf w.
Proof using EL. destruct 1; [apply whnf_sup | apply whnf_ne; exact (gne_tm_whne_l H)]. Qed.
Lemma WNf_whnf_r {G Γ l1 l2 A B d c w w'} : WNf G Γ l1 l2 A B d c w w' -> whnf w'.
Proof using EL. destruct 1; [apply whnf_sup | apply whnf_ne; exact (gne_tm_whne_r H)]. Qed.

(** Inversion at a [sup] and at a neutral on the left. *)
Lemma WNf_sup_inv {G Γ l1 l2 A B} {d : DomRel G Γ} {c : CodRel G Γ d} {k1 k2 C D a f w} :
  WNf G Γ l1 l2 A B d c (tmSup k1 k2 C D a f) w ->
  exists k1' k2' C' D' a' f', w = tmSup k1' k2' C' D' a' f' /\
    lequiv (gL G) k1 l1 /\ lequiv (gL G) k2 l2 /\ lequiv (gL G) k1' l1 /\ lequiv (gL G) k2' l2 /\
    [ G ; Γ ⊢ A ≈ C @ l1 ] /\ [ G ; Γ ⊢ A ≈ C' @ l1 ] /\
    [ G ; Γ ,, A @ l1 ⊢ B ≈ D @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢ B ≈ D' @ l2 ] /\
    (forall ρ : kwk G Γ, d ρ (ktm ρ a) (ktm ρ a')) /\
    (forall ρ : kwk G Γ, WhRel (kw_G ρ) (kw_Δ ρ)
       (tyPi l2 (lmax l1 l2) (ktyl ρ B)[lsingle (ktm ρ a)] (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩)
       (lmax l2 (lmax l1 l2)) (ktm ρ f) (ktm ρ f')) /\
    (forall (ρ : kwk G Γ) (ha : d ρ (ktm ρ a) (ktm ρ a')) b b', c ρ (ktm ρ a) (ktm ρ a') ha b b' ->
       forall la lb A1 B1 la' lb' A1' B1',
       lequiv (gL G) la l2 -> lequiv (gL G) lb (lmax l1 l2) ->
       lequiv (gL G) la' l2 -> lequiv (gL G) lb' (lmax l1 l2) ->
       [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle (ktm ρ a)] ≈ A1 @ l2 ] ->
       [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B)[lsingle (ktm ρ a)] @ l2
           ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ B1 @ lmax l1 l2 ] ->
       [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle (ktm ρ a)] ≈ A1' @ l2 ] ->
       [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B)[lsingle (ktm ρ a)] @ l2
           ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ B1' @ lmax l1 l2 ] ->
       WRel (kw_G ρ) (kw_Δ ρ) l1 l2 (kty ρ A) (ktyl ρ B)
         (fun ρ' => d (kw_comp ρ ρ')) (fun ρ' x x' h => c (kw_comp ρ ρ') x x' h)
         (app (ktm ρ f) la lb A1 B1 b) (app (ktm ρ f') la' lb' A1' B1' b')).
Proof using EL.
  intros H. remember (tmSup k1 k2 C D a f) as s eqn:Es. destruct H.
  - injection Es as -> -> -> -> -> ->. do 6 eexists; split; [reflexivity|]. eauto 20.
  - subst. exfalso. pose proof (gne_tm_whne_l H) as Hw. inversion Hw.
Qed.

(** [WhRel] composes, the middle whnfs being equal. *)
Lemma WhRel_trans {G Γ T l t1 t2 t3} : WhRel G Γ T l t1 t2 -> WhRel G Γ T l t2 t3 -> WhRel G Γ T l t1 t3.
Proof using EL.
  intros (w1 & w2 & H1 & H2 & N1 & N2 & E12) (w2' & w3 & H2' & H3 & N2' & N3 & E23).
  assert (w2' = w2) as -> by (eapply tmred_whnf_det; [exact H2' | exact H2 | exact N2' | exact N2]).
  exists w1, w3. exact (conj H1 (conj H3 (conj N1 (conj N3 (geq_tm_trans E12 E23))))).
Qed.

Lemma WNf_ne_inv {G Γ l1 l2 A B} {d : DomRel G Γ} {c : CodRel G Γ d} {ν w} :
  whne ν -> WNf G Γ l1 l2 A B d c ν w -> [ G ; Γ ⊢ ν ~ w : tyW l1 l2 A B @ lmax l1 l2 ].
Proof using . intros Hν H. destruct H; [inversion Hν | exact H]. Qed.

(** Composition: the shapes compose by [Td]; at the children, the middle
    tree's children are taken at the left position, which is related to
    itself ([Rc]) and, by the right one, to the third ([Mc]). *)
Lemma WRel_trans :
  forall G Γ l1 l2 A1 B1 (d1 : DomRel G Γ) (c1 : CodRel G Γ d1) t1 t2,
  WRel G Γ l1 l2 A1 B1 d1 c1 t1 t2 ->
  forall l3 l4 A2 B2 (d2 : DomRel G Γ) (c2 : CodRel G Γ d2) t3,
  WRel G Γ l3 l4 A2 B2 d2 c2 t2 t3 ->
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
  [ G ; Γ ⊢g A1 @ l1 ] -> [ G ; Γ ⊢ A1 ≈ A2 @ l1 ] -> [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B2 @ l2 ] ->
  (forall (ρ : kwk G Γ) x y (h : d1 ρ x y),
      [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle x] ≈ (ktyl ρ B2)[lsingle y] @ l2 ]) ->
  (forall ρ x y z, d1 ρ x y -> d2 ρ y z -> d1 ρ x z) ->
  (forall ρ x y z (h : d1 ρ x y) (h' : d1 ρ x z) u v, c1 ρ x z h' u v -> c1 ρ x y h u u) ->
  (forall ρ x y z (h12 : d1 ρ x y) (h13 : d1 ρ x z) (h23 : d2 ρ y z) u w,
      c1 ρ x z h13 u w -> c2 ρ y z h23 u w) ->
  WRel G Γ l1 l2 A1 B1 d1 c1 t1 t3.
Proof using EL.
  apply (WRel_mut
    (fun G Γ l1 l2 A1 B1 d1 c1 t1 t2 _ =>
      forall l3 l4 A2 B2 (d2 : DomRel G Γ) (c2 : CodRel G Γ d2) t3,
      WRel G Γ l3 l4 A2 B2 d2 c2 t2 t3 ->
      lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
      [ G ; Γ ⊢g A1 @ l1 ] -> [ G ; Γ ⊢ A1 ≈ A2 @ l1 ] -> [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B2 @ l2 ] ->
      (forall (ρ : kwk G Γ) x y (h : d1 ρ x y),
          [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle x] ≈ (ktyl ρ B2)[lsingle y] @ l2 ]) ->
      (forall ρ x y z, d1 ρ x y -> d2 ρ y z -> d1 ρ x z) ->
      (forall ρ x y z (h : d1 ρ x y) (h' : d1 ρ x z) u v, c1 ρ x z h' u v -> c1 ρ x y h u u) ->
      (forall ρ x y z (h12 : d1 ρ x y) (h13 : d1 ρ x z) (h23 : d2 ρ y z) u w,
          c1 ρ x z h13 u w -> c2 ρ y z h23 u w) ->
      WRel G Γ l1 l2 A1 B1 d1 c1 t1 t3)
    (fun G Γ l1 l2 A1 B1 d1 c1 w1 w2 _ =>
      forall l3 l4 A2 B2 (d2 : DomRel G Γ) (c2 : CodRel G Γ d2) w3,
      WNf G Γ l3 l4 A2 B2 d2 c2 w2 w3 ->
      lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
      [ G ; Γ ⊢g A1 @ l1 ] -> [ G ; Γ ⊢ A1 ≈ A2 @ l1 ] -> [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B2 @ l2 ] ->
      (forall (ρ : kwk G Γ) x y (h : d1 ρ x y),
          [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle x] ≈ (ktyl ρ B2)[lsingle y] @ l2 ]) ->
      (forall ρ x y z, d1 ρ x y -> d2 ρ y z -> d1 ρ x z) ->
      (forall ρ x y z (h : d1 ρ x y) (h' : d1 ρ x z) u v, c1 ρ x z h' u v -> c1 ρ x y h u u) ->
      (forall ρ x y z (h12 : d1 ρ x y) (h13 : d1 ρ x z) (h23 : d2 ρ y z) u w,
          c1 ρ x z h13 u w -> c2 ρ y z h23 u w) ->
      WNf G Γ l1 l2 A1 B1 d1 c1 w1 w3)).
  - intros G Γ l1 l2 A1 B1 d1 c1 t1 t2 w1 w2 Hw1 Hw2 Heq Hn IH l3 l4 A2 B2 d2 c2 t3 H2 Hl3 Hl4 HA1 HA12 HB12 HC Td Rc Mc.
    destruct (WRel_inv H2) as (w2' & w3 & Hw2' & Hw3 & Heq2 & Hn2).
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HV : [ G ; Γ ⊢g tyW l3 l4 A2 B2 ≅ tyW l1 l2 A1 B1 @ lmax l3 l4 ]).
    { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_W; auto using lequiv_sym | exact Hm]. }
    assert (Ew : w2' = w2)
      by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | exact (WNf_whnf_l Hn2) | exact (WNf_whnf_r Hn)]).
    subst w2'.
    econstructor; [exact Hw1 | | |].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw3 | exact HV] | apply lequiv_sym, Hm].
    + eapply geq_tm_trans; [exact Heq|].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq2 | exact HV] | apply lequiv_sym, Hm].
    + exact (IH l3 l4 A2 B2 d2 c2 w3 Hn2 Hl3 Hl4 HA1 HA12 HB12 HC Td Rc Mc).
  - intros G Γ l1 l2 A1 B1 d1 c1 k1 k2 k1' k2' C D C' D' a a' f f' Hk1 Hk2 Hk1' Hk2' HC0 HC0' HD HD' Ha Hwf Hf IH
      l3 l4 A2 B2 d2 c2 w3 H2 Hl3 Hl4 HA1 HA12 HB12 HC Td Rc Mc.
    destruct (WNf_sup_inv H2) as (k1'' & k2'' & C'' & D'' & a'' & f'' & -> & Hj1 & Hj2 & Hj1' & Hj2'
                                  & HE & HE' & HF & HF' & Ha2 & Hwf2 & Hf2).
    pose proof (lequiv_wf_l _ _ _ Hl3) as W3. pose proof (lequiv_wf_l _ _ _ Hl4) as W4.
    pose proof (lequiv_wf_r _ _ _ Hl3) as W1. pose proof (lequiv_wf_r _ _ _ Hl4) as W2.
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    apply wnf_sup; eauto using lequiv_trans.
    + eapply geq_ty_trans; [exact HA12 | eapply geq_ty_lconv; [exact HE' | apply lequiv_sym, Hl3]].
    + (* [B2 ≈ D''] under [A2], moved under [A1] *)
      eapply geq_ty_trans; [exact HB12|].
      eapply geq_ty_ctxconv; [| exact Hl3 | apply ext_wf_g; [exact HA1 | exact W1] |].
      * eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA12 | exact Hl3].
      * eapply geq_ty_lconv; [exact HF' | apply lequiv_sym, Hl4].
    + (* the children's functions compose, the middle ones' type converted *)
      intros ρ. eapply WhRel_trans; [exact (Hwf ρ) |].
      pose proof (W_fty_eq (kw_lequiv ρ (lequiv_sym _ _ _ Hl3)) (kw_lequiv ρ (lequiv_sym _ _ _ Hl4)) (kw_ty ρ HA1)
                    (kw_geq_ty ρ HA12) (kw_geq_ty_l ρ HA1 W1 HB12) (HC ρ _ _ (Ha ρ))) as EP.
      assert (Qm : lequiv (gL (kw_G ρ)) (lmax l4 (lmax l3 l4)) (lmax l2 (lmax l1 l2)))
        by (apply lequiv_max; [|apply lequiv_max]; apply (kw_lequiv ρ); assumption).
      eapply WhRel_conv; [exact (Hwf2 ρ) | eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, EP | exact Qm] |].
      apply lequiv_sym, Qm.
    + intros ρ h13 b b'' Hbb la lb A1x B1x la'' lb'' A1x'' B1x'' H1 H2' H3 H4 HA1x HB1x HA1x'' HB1x''.
      pose proof (Ha ρ) as h12. pose proof (Ha2 ρ) as h23.
      pose proof (Rc ρ _ _ _ h12 h13 b b'' Hbb) as Hbb12.
      pose proof (Mc ρ _ _ _ h12 h13 h23 b b'' Hbb) as Hbb23.
      pose proof (kw_lwf ρ W1) as V1. pose proof (kw_lwf ρ W2) as V2.
      pose proof (kw_lequiv ρ Hl3) as Q3. pose proof (kw_lequiv ρ Hl4) as Q4.
      assert (Qm : lequiv (gL (kw_G ρ)) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
      pose proof (HC ρ _ _ h12) as EC. pose proof (geq_ty_sound EC) as EC'.
      pose proof (eqty_wf_l ge_typeof EC') as HB1a. pose proof (eqty_wf_r ge_typeof EC') as HB2a.
      assert (RC : [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle (ktm ρ a)] ≈ (ktyl ρ B1)[lsingle (ktm ρ a)] @ l2 ])
        by (eapply geq_ty_trans; [exact EC | apply geq_ty_sym, EC]).
      assert (EW : [ kw_G ρ ; kw_Δ ρ ⊢ tyW l1 l2 (kty ρ A1) (ktyl ρ B1) ≈ tyW l3 l4 (kty ρ A2) (ktyl ρ B2) @ lmax l1 l2 ]).
      { pose proof (kw_geq_ty ρ (geq_ty_W (lequiv_sym _ _ _ Hl3) (lequiv_sym _ _ _ Hl4) HA1 HA12 HB12)) as X.
        now rewrite !kty_tyW in X. }
      assert (HΔ1 : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B1)[lsingle (ktm ρ a)] @ l2 ⊢g ])
        by (apply ext_wf_g; [exact HB1a | exact V2]).
      assert (HΔ2 : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B2)[lsingle (ktm ρ a')] @ l4 ⊢g ])
        by (apply ext_wf_g; [eapply lconv_ty; [exact HB2a | solve [apply lequiv_sym; assumption]] | exact (kw_lwf ρ W4)]).
      assert (EW1 : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B1)[lsingle (ktm ρ a)] @ l2
                      ⊢ (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ ≈ (tyW l3 l4 (kty ρ A2) (ktyl ρ B2))⟨↑⟩ @ lmax l1 l2 ])
        by exact (geq_ty_wk (wkr_shift1 _ _ _) HΔ1 EW).
      assert (RW : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B1)[lsingle (ktm ρ a)] @ l2
                     ⊢ (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ ≈ (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ @ lmax l1 l2 ])
        by (eapply geq_ty_trans; [exact EW1 | apply geq_ty_sym, EW1]).
      (* a type of the left positions' context, moved to the middle positions' *)
      assert (MB : forall X, [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B1)[lsingle (ktm ρ a)] @ l2
                               ⊢ (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ ≈ X @ lmax l1 l2 ] ->
                     [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B2)[lsingle (ktm ρ a')] @ l4
                               ⊢ (tyW l3 l4 (kty ρ A2) (ktyl ρ B2))⟨↑⟩ ≈ X @ lmax l3 l4 ]).
      { intros X HX. eapply geq_ty_lconv; [|exact Qm].
        eapply geq_ty_ctxconv; [| apply lequiv_sym, Q4 | exact HΔ2 |].
        - exact EC'.
        - eapply geq_ty_trans; [apply geq_ty_sym, EW1 | exact HX]. }
      assert (MA : forall X, [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle (ktm ρ a)] ≈ X @ l2 ] ->
                     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B2)[lsingle (ktm ρ a')] ≈ X @ l4 ]).
      { intros X HX. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, EC | exact HX] | exact Q4]. }
      assert (Rl2 : lequiv (gL G) l2 l2) by (apply lequiv_refl; exact W2).
      assert (RL : lequiv (gL G) (lmax l1 l2) (lmax l1 l2)) by (apply lequiv_refl; cbn; split; assumption).
      (* the first trees' children, the middle one at the left position *)
      pose proof (Hf ρ h12 b b Hbb12 la lb A1x B1x l2 (lmax l1 l2) ((ktyl ρ B1)[lsingle (ktm ρ a)])
                    (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ H1 H2' Rl2 RL HA1x HB1x RC RW) as X1.
      (* the second trees' children *)
      pose proof (Hf2 ρ h23 b b'' Hbb23 l2 (lmax l1 l2) ((ktyl ρ B1)[lsingle (ktm ρ a)])
                    (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ la'' lb'' A1x'' B1x''
                    (lequiv_sym _ _ _ Hl4) (lequiv_sym _ _ _ Hm)
                    (lequiv_trans _ _ _ _ H3 (lequiv_sym _ _ _ Hl4)) (lequiv_trans _ _ _ _ H4 (lequiv_sym _ _ _ Hm))
                    (MA _ RC) (MB _ RW) (MA _ HA1x'') (MB _ HB1x'')) as X2.
      refine (IH ρ h12 b b Hbb12 la lb A1x B1x l2 (lmax l1 l2) ((ktyl ρ B1)[lsingle (ktm ρ a)])
                (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ H1 H2' Rl2 RL HA1x HB1x RC RW
                l3 l4 (kty ρ A2) (ktyl ρ B2) _ _ _ X2 Q3 Q4 (kw_ty ρ HA1) (kw_geq_ty ρ HA12)
                (kw_geq_ty_l ρ HA1 W1 HB12) _ _ _ _).
      * intros ρ' x y h. rewrite <- !ktyl_comp. exact (HC (kw_comp ρ ρ') x y h).
      * intros ρ' x y z. exact (Td (kw_comp ρ ρ') x y z).
      * intros ρ' x y z h h'. exact (Rc (kw_comp ρ ρ') x y z h h').
      * intros ρ' x y z h12' h13' h23'. exact (Mc (kw_comp ρ ρ') x y z h12' h13' h23').
  - intros G Γ l1 l2 A1 B1 d1 c1 ν ν' Hν l3 l4 A2 B2 d2 c2 w3 H2 Hl3 Hl4 HA1 HA12 HB12 HC Td Rc Mc.
    pose proof (WNf_ne_inv (gne_tm_whne_r Hν) H2) as Hν2.
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HV : [ G ; Γ ⊢g tyW l3 l4 A2 B2 ≅ tyW l1 l2 A1 B1 @ lmax l3 l4 ]).
    { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_W; auto using lequiv_sym | exact Hm]. }
    apply wnf_ne. eapply gne_tm_trans; [exact Hν |].
    eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν2 | exact HV] | apply lequiv_sym, Hm].
Qed.

(** ** Finitary trees, composed (M15a)

    As [W]: the second derivation is inverted at the middle tree's shape.
    A spine composes along a middle length [NatRel]-related to the left
    one; at a [sup] that is the arity at the related positions ([HC]). The
    middle children are taken at the left canonical annotations, which the
    second derivation accepts after moving them along [geq_vec_nat]. *)
Section WfTrans.

Definition WfTransHyps G Γ l1 A1 N1 (d1 : DomRel G Γ) l2 A2 N2 (d2 : DomRel G Γ) :=
  WfFlipHyps G Γ l1 A1 N1 d1 l2 A2 N2 /\ (forall ρ x y z, d1 ρ x y -> d2 ρ y z -> d1 ρ x z).

Lemma WfTransHyps_kw {G Γ l1 A1 N1 d1 l2 A2 N2 d2} (ρ : kwk G Γ) :
  WfTransHyps G Γ l1 A1 N1 d1 l2 A2 N2 d2 ->
  WfTransHyps (kw_G ρ) (kw_Δ ρ) l1 (kty ρ A1) (ktml ρ N1) (fun ρ' => d1 (kw_comp ρ ρ'))
    l2 (kty ρ A2) (ktml ρ N2) (fun ρ' => d2 (kw_comp ρ ρ')).
Proof using EL.
  intros [Hy Td]. split; [exact (WfFlipHyps_kw ρ Hy)|].
  intros ρ' x y z. exact (Td (kw_comp ρ ρ') x y z).
Qed.

Lemma WfNf_whnf_l {G Γ l A N d w w'} : WfNf G Γ l A N d w w' -> whnf w.
Proof using EL. destruct 1; [apply whnf_supf | apply whnf_ne; exact (gne_tm_whne_l H)]. Qed.
Lemma WfNf_whnf_r {G Γ l A N d w w'} : WfNf G Γ l A N d w w' -> whnf w'.
Proof using EL. destruct 1; [apply whnf_supf | apply whnf_ne; exact (gne_tm_whne_r H)]. Qed.

Lemma WfNf_sup_inv {G Γ l A N} {d : DomRel G Γ} {k C M a cs w} :
  WfNf G Γ l A N d (tmSupf k C M a cs) w ->
  exists k' C' M' a' cs', w = tmSupf k' C' M' a' cs' /\
    lequiv (gL G) k l /\ lequiv (gL G) k' l /\
    [ G ; Γ ⊢ A ≈ C @ l ] /\ [ G ; Γ ⊢ A ≈ C' @ l ] /\
    [ G ; Γ ,, A @ l ⊢ N ≈ M : tyNat @ lzero ] /\ [ G ; Γ ,, A @ l ⊢ N ≈ M' : tyNat @ lzero ] /\
    (forall ρ : kwk G Γ, d ρ (ktm ρ a) (ktm ρ a')) /\
    (forall ρ : kwk G Γ,
       VecSp (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => d (kw_comp ρ ρ'))
         (ktml ρ N)[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')).
Proof using EL.
  intros H. remember (tmSupf k C M a cs) as s eqn:Es. destruct H.
  - injection Es as -> -> -> -> ->. do 5 eexists; split; [reflexivity|]. eauto 20.
  - subst. exfalso. pose proof (gne_tm_whne_l H) as Hw. inversion Hw.
Qed.

Lemma WfNf_ne_inv {G Γ l A N} {d : DomRel G Γ} {ν w} :
  whne ν -> WfNf G Γ l A N d ν w -> [ G ; Γ ⊢ ν ~ w : tyWf l A N @ l ].
Proof using . intros Hν H. destruct H; [inversion Hν | exact H]. Qed.

(** A spine at a length of a known shape. *)
Lemma VecSp_zero_inv {G Γ l A N d k cs cs'} : VecSp G Γ l A N d k cs cs' ->
  [ G ; Γ ⊢g k ⤳* zero : tyNat @ lzero ] -> UnitRel G Γ l cs cs'.
Proof using EL.
  destruct 1 as [|? ? ? ? ? ? ? m ? ? ? ? Hk|? ? ? ? ? ? ? ν ? ? Hk Hν]; intros Hz; [assumption| |].
  - assert (X : succ m = zero) by (eapply tmred_whnf_det; [exact Hk | exact Hz | constructor | constructor]).
    discriminate X.
  - assert (X : ν = zero)
      by (eapply tmred_whnf_det; [exact Hk | exact Hz | constructor; exact (gne_tm_whne_l Hν) | constructor]).
    subst ν. pose proof (gne_tm_whne_l Hν) as Y. inversion Y.
Qed.

Lemma VecSp_succ_inv {G Γ l A N d k m cs cs'} : VecSp G Γ l A N d k cs cs' ->
  [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  exists w w',
    [ G ; Γ ⊢g cs ⤳* w : tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ lmax l l ] /\
    [ G ; Γ ⊢g cs' ⤳* w' : tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ lmax l l ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ lmax l l ] /\
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
Proof using EL.
  destruct 1 as [? ? ? ? ? ? ? ? ? Hk|? ? ? ? ? ? ? m0 ? ? w w' Hk Hcs Hcs' Hn Hn' Heq Hf Hs
                |? ? ? ? ? ? ? ν ? ? Hk Hν]; intros Hsk.
  - assert (X : zero = succ m) by (eapply tmred_whnf_det; [exact Hk | exact Hsk | constructor | constructor]).
    discriminate X.
  - assert (X : succ m0 = succ m) by (eapply tmred_whnf_det; [exact Hk | exact Hsk | constructor | constructor]).
    injection X as ->. exists w, w'. eauto 10.
  - assert (X : ν = succ m)
      by (eapply tmred_whnf_det; [exact Hk | exact Hsk | constructor; exact (gne_tm_whne_l Hν) | constructor]).
    subst ν. pose proof (gne_tm_whne_l Hν) as Y. inversion Y.
Qed.

Lemma VecSp_ne_inv {G Γ l A N d k ν cs cs'} : VecSp G Γ l A N d k cs cs' ->
  [ G ; Γ ⊢g k ⤳* ν : tyNat @ lzero ] -> whne ν ->
  NeRel G Γ (tyVec l (tyWf l A N) ν) (tyVec l (tyWf l A N) ν) l cs cs'.
Proof using EL.
  destruct 1 as [? ? ? ? ? ? ? ? ? Hk|? ? ? ? ? ? ? m0 ? ? ? ? Hk|? ? ? ? ? ? ? ν0 ? ? Hk Hν0 Hne];
    intros Hνk Hν.
  - assert (X : zero = ν) by (eapply tmred_whnf_det; [exact Hk | exact Hνk | constructor | now constructor]).
    subst ν. inversion Hν.
  - assert (X : succ m0 = ν) by (eapply tmred_whnf_det; [exact Hk | exact Hνk | constructor | now constructor]).
    subst ν. inversion Hν.
  - assert (X : ν0 = ν)
      by (eapply tmred_whnf_det; [exact Hk | exact Hνk | constructor; exact (gne_tm_whne_l Hν0) | now constructor]).
    now subst ν0.
Qed.

Lemma WfRel_trans_all :
  (forall G Γ l1 A1 N1 d1 t1 t2, WfRel G Γ l1 A1 N1 d1 t1 t2 ->
     forall l2 A2 N2 d2 t3, WfTransHyps G Γ l1 A1 N1 d1 l2 A2 N2 d2 ->
     WfRel G Γ l2 A2 N2 d2 t2 t3 -> WfRel G Γ l1 A1 N1 d1 t1 t3) /\
  (forall G Γ l1 A1 N1 d1 t1 t2, WfNf G Γ l1 A1 N1 d1 t1 t2 ->
     forall l2 A2 N2 d2 t3, WfTransHyps G Γ l1 A1 N1 d1 l2 A2 N2 d2 ->
     WfNf G Γ l2 A2 N2 d2 t2 t3 -> WfNf G Γ l1 A1 N1 d1 t1 t3) /\
  (forall G Γ l1 A1 N1 d1 k1 cs1 cs2, VecSp G Γ l1 A1 N1 d1 k1 cs1 cs2 ->
     forall l2 A2 N2 d2 k2 cs3, WfTransHyps G Γ l1 A1 N1 d1 l2 A2 N2 d2 ->
     NatRel G Γ k1 k2 -> VecSp G Γ l2 A2 N2 d2 k2 cs2 cs3 -> VecSp G Γ l1 A1 N1 d1 k1 cs1 cs3).
Proof using EL.
  apply WfRel_comb.
  - intros G Γ l1 A1 N1 d1 t1 t2 w1 w2 Hw1 Hw2 Heq Hn IH l2 A2 N2 d2 t3 Hy H2.
    destruct (WfFlip_data (proj1 Hy)) as (W1 & W2 & HWf1 & HWf2 & EWg & EW).
    pose proof (proj1 (proj1 Hy)) as Hl.
    destruct (WfRel_inv H2) as (w2' & w3 & Hw2' & Hw3 & Heq2 & Hn2).
    assert (HV : [ G ; Γ ⊢g tyWf l2 A2 N2 ≅ tyWf l1 A1 N1 @ l2 ]) by (eapply eqty_lconv; [apply eqty_sym, EW | exact Hl]).
    assert (Ew : w2' = w2)
      by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | exact (WfNf_whnf_l Hn2) | exact (WfNf_whnf_r Hn)]).
    subst w2'.
    econstructor; [exact Hw1 | | |].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw3 | exact HV] | apply lequiv_sym, Hl].
    + eapply geq_tm_trans; [exact Heq|].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq2 | exact HV] | apply lequiv_sym, Hl].
    + exact (IH l2 A2 N2 d2 w3 Hy Hn2).
  - intros G Γ l1 A1 N1 d1 k k' C C' M M' a a' cs cs' Hk Hk' HAC HAC' HNM HNM' Ha Hcs IH l2 A2 N2 d2 t3 Hy H2.
    destruct (WfNf_sup_inv H2) as (k'' & C'' & M'' & a'' & cs'' & -> & _ & Hj'' & _ & HE'' & _ & HF'' & Ha2 & Hcs2).
    destruct Hy as [Hy0 Td]. pose proof Hy0 as (Hl & HA1 & HA12 & HN12 & HC).
    pose proof (lequiv_wf_r _ _ _ Hl) as W1.
    apply wfnf_sup.
    + exact Hk.
    + exact (lequiv_trans _ _ _ _ Hj'' Hl).
    + exact HAC.
    + eapply geq_ty_trans; [exact HA12 | eapply geq_ty_lconv; [exact HE'' | apply lequiv_sym, Hl]].
    + exact HNM.
    + eapply geq_tm_trans; [exact HN12|].
      eapply geq_tm_ctxconv; [| exact Hl | apply ext_wf_g; [exact HA1 | exact W1] | exact HF''].
      eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA12 | exact Hl].
    + intros ρ. exact (Td ρ _ _ _ (Ha ρ) (Ha2 ρ)).
    + intros ρ. exact (IH ρ l2 (kty ρ A2) (ktml ρ N2) _ _ _ (WfTransHyps_kw ρ (conj Hy0 Td)) (HC ρ _ _ (Ha ρ)) (Hcs2 ρ)).
  - intros G Γ l1 A1 N1 d1 ν ν' Hν l2 A2 N2 d2 t3 Hy H2.
    destruct (WfFlip_data (proj1 Hy)) as (W1 & W2 & HWf1 & HWf2 & EWg & EW).
    pose proof (proj1 (proj1 Hy)) as Hl.
    pose proof (WfNf_ne_inv (gne_tm_whne_r Hν) H2) as Hν2.
    assert (HV : [ G ; Γ ⊢g tyWf l2 A2 N2 ≅ tyWf l1 A1 N1 @ l2 ]) by (eapply eqty_lconv; [apply eqty_sym, EW | exact Hl]).
    apply wfnf_ne. eapply gne_tm_trans; [exact Hν |].
    eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν2 | exact HV] | apply lequiv_sym, Hl].
  - intros G Γ l1 A1 N1 d1 k1 cs1 cs2 Hk Hu l2 A2 N2 d2 k2 cs3 Hy Hkk H2.
    pose proof (VecSp_zero_inv H2 (NatRel_inv_zero Hkk Hk)) as Hu2.
    apply vsp_zero; [exact Hk|].
    eapply UnitRel_trans; [exact Hu | apply (UnitRel_lconv (proj1 (proj1 Hy))), Hu2].
  - intros G Γ l1 A1 N1 d1 k1 m1 cs1 cs2 w1 w2 Hk Hcs1 Hcs2 Hwh1 Hwh2 Heq Hfst IHfst Hsnd IHsnd
      l2 A2 N2 d2 k2 cs3 Hy Hkk H2.
    destruct (WfFlip_data (proj1 Hy)) as (W1 & W2 & HWf1 & HWf2 & EWg & EW).
    pose proof (proj1 (proj1 Hy)) as Hl.
    destruct (NatRel_inv_succ Hkk Hk) as (m2 & Hk2 & Hmm).
    destruct (VecSp_succ_inv H2 Hk2) as (w2' & w3 & Hcs2' & Hcs3 & Hwh2' & Hwh3 & Heq2 & Hfst2 & Hsnd2).
    assert (Ew : w2' = w2) by (eapply tmred_whnf_det; [exact Hcs2' | exact Hcs2 | exact Hwh2' | exact Hwh2]).
    subst w2'.
    pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
    pose proof (sigvec_eq (lequiv_sym _ _ _ Hl) W1 HWf1 EW Em) as ES.
    assert (Hml : lequiv (gL G) (lmax l2 l2) (lmax l1 l1)) by now apply lequiv_max.
    assert (HV : [ G ; Γ ⊢g tySig l2 l2 (tyWf l2 A2 N2) (tyVec l2 (tyWf l2 A2 N2)⟨↑⟩ m2⟨↑⟩)
                   ≅ tySig l1 l1 (tyWf l1 A1 N1) (tyVec l1 (tyWf l1 A1 N1)⟨↑⟩ m1⟨↑⟩) @ lmax l2 l2 ])
      by (eapply eqty_lconv; [apply eqty_sym, ES | exact Hml]).
    assert (HΓ1 : [ G ; Γ ,, tyWf l1 A1 N1 @ l1 ⊢g ]) by now apply ext_wf_g.
    assert (HΓ2 : [ G ; Γ ,, tyWf l2 A2 N2 @ l2 ⊢g ]) by now apply ext_wf_g.
    assert (VV : [ G ; Γ ,, tyWf l1 A1 N1 @ l1 ⊢ tyVec l1 (tyWf l1 A1 N1)⟨↑⟩ m1⟨↑⟩
                                              ≈ tyVec l2 (tyWf l2 A2 N2)⟨↑⟩ m2⟨↑⟩ @ l1 ])
      by exact (geq_ty_wk (wkr_shift1 _ _ _) HΓ1 (geq_vec_nat m1 m2 Hmm l1 l2 _ _ (lequiv_sym _ _ _ Hl) HWf1 EWg)).
    assert (RA : [ G ; Γ ⊢ tyWf l1 A1 N1 ≈ tyWf l1 A1 N1 @ l1 ]) by (eapply geq_ty_trans; [exact EWg | apply geq_ty_sym, EWg]).
    assert (RB : [ G ; Γ ,, tyWf l1 A1 N1 @ l1 ⊢ tyVec l1 (tyWf l1 A1 N1)⟨↑⟩ m1⟨↑⟩ ≈ tyVec l1 (tyWf l1 A1 N1)⟨↑⟩ m1⟨↑⟩ @ l1 ])
      by (eapply geq_ty_trans; [exact VV | apply geq_ty_sym, VV]).
    assert (MA : forall X, [ G ; Γ ⊢ tyWf l1 A1 N1 ≈ X @ l1 ] -> [ G ; Γ ⊢ tyWf l2 A2 N2 ≈ X @ l2 ]).
    { intros X HX. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, EWg | exact HX] | exact Hl]. }
    assert (MB : forall X, [ G ; Γ ,, tyWf l1 A1 N1 @ l1 ⊢ tyVec l1 (tyWf l1 A1 N1)⟨↑⟩ m1⟨↑⟩ ≈ X @ l1 ] ->
                   [ G ; Γ ,, tyWf l2 A2 N2 @ l2 ⊢ tyVec l2 (tyWf l2 A2 N2)⟨↑⟩ m2⟨↑⟩ ≈ X @ l2 ]).
    { intros X HX. eapply geq_ty_lconv; [|exact Hl].
      eapply geq_ty_ctxconv; [exact EW | apply lequiv_sym, Hl | exact HΓ2 |].
      eapply geq_ty_trans; [apply geq_ty_sym, VV | exact HX]. }
    assert (R1 : lequiv (gL G) l1 l1) by now apply lequiv_refl.
    pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    apply (vsp_succ G Γ l1 A1 N1 d1 k1 m1 cs1 cs3 w1 w3).
    + exact Hk.
    + exact Hcs1.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs3 | exact HV] | apply lequiv_sym, Hml].
    + exact Hwh1.
    + exact Hwh3.
    + eapply geq_tm_trans; [exact Heq|].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq2 | exact HV] | apply lequiv_sym, Hml].
    + intros la lb A1x B1x la'' lb'' A1x'' B1x'' H1 H2' H3 H4 HA1x HB1x HA1x'' HB1x''.
      pose proof (Hfst2 l1 l1 _ _ la'' lb'' A1x'' B1x'' Hl' Hl' (lequiv_trans _ _ _ _ H3 Hl')
                    (lequiv_trans _ _ _ _ H4 Hl') (MA _ RA) (MB _ RB) (MA _ HA1x'') (MB _ HB1x'')) as X2.
      exact (IHfst la lb A1x B1x l1 l1 _ _ H1 H2' R1 R1 HA1x HB1x RA RB l2 A2 N2 d2 _ Hy X2).
    + intros la lb A1x B1x la'' lb'' A1x'' B1x'' H1 H2' H3 H4 HA1x HB1x HA1x'' HB1x''.
      pose proof (Hsnd2 l1 l1 _ _ la'' lb'' A1x'' B1x'' Hl' Hl' (lequiv_trans _ _ _ _ H3 Hl')
                    (lequiv_trans _ _ _ _ H4 Hl') (MA _ RA) (MB _ RB) (MA _ HA1x'') (MB _ HB1x'')) as X2.
      exact (IHsnd la lb A1x B1x l1 l1 _ _ H1 H2' R1 R1 HA1x HB1x RA RB l2 A2 N2 d2 _ _ Hy Hmm X2).
  - intros G Γ l1 A1 N1 d1 k1 ν1 cs1 cs2 Hk Hν1 Hne l2 A2 N2 d2 k2 cs3 Hy Hkk H2.
    destruct (WfFlip_data (proj1 Hy)) as (W1 & W2 & HWf1 & HWf2 & EWg & EW).
    pose proof (proj1 (proj1 Hy)) as Hl.
    destruct (NatRel_inv_ne Hkk Hk (gne_tm_whne_l Hν1)) as (ν2 & Hk2 & Hνν).
    pose proof (VecSp_ne_inv H2 Hk2 (gne_tm_whne_r Hνν)) as Hne2.
    apply (vsp_ne G Γ l1 A1 N1 d1 k1 ν1 cs1 cs3); [exact Hk | exact Hν1 |].
    pose proof (geq_ty_sound (gne_ty_geq (gne_ty_vec (lequiv_sym _ _ _ Hl) HWf1 EWg Hνν))) as EV.
    assert (EV' : [ G ; Γ ⊢g tyVec l2 (tyWf l2 A2 N2) ν2 ≅ tyVec l1 (tyWf l1 A1 N1) ν1 @ l2 ])
      by (eapply eqty_lconv; [apply eqty_sym, EV | exact Hl]).
    pose proof (NeRel_conv2 EV' EV' Hne2) as Hne2'.
    apply (NeRel_lconv _ _ _ _ _ _ (lequiv_sym _ _ _ Hl)) in Hne2'.
    pose proof (eqty_wf_l ge_typeof EV) as HV1.
    eapply NeRel_trans; [apply eqty_refl, HV1 | apply eqty_refl, HV1 | exact Hne | exact Hne2'].
Qed.

End WfTrans.

(** ** Indexed trees, composed (M17b)

    As [Wf]'s: the second derivation is inverted at the middle tree's
    shape, a spine composes along a middle length and family related to
    the left ones, and the middle children are taken at the left
    canonical annotations. The output index is the left tree's own, so
    no index premise is composed. *)
Section IWfTrans.

Definition IWfTransHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 (ix1 dm1 : DomRel G Γ) l2 li2 X2 A2 N2 Ot2 C2
    (dm2 : DomRel G Γ) :=
  IWfFlipHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l2 li2 X2 A2 N2 Ot2 C2 /\
  (forall ρ x y z, dm1 ρ x y -> dm2 ρ y z -> dm1 ρ x z).

Lemma IWfTransHyps_kw {G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l2 li2 X2 A2 N2 Ot2 C2 dm2} (ρ : kwk G Γ) :
  IWfTransHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l2 li2 X2 A2 N2 Ot2 C2 dm2 ->
  IWfTransHyps (kw_G ρ) (kw_Δ ρ) l1 li1 (kty ρ X1) (kty ρ A1) (ktml ρ N1) (ktml ρ Ot1) (ktmll ρ C1)
    (fun ρ' => ix1 (kw_comp ρ ρ')) (fun ρ' => dm1 (kw_comp ρ ρ'))
    l2 li2 (kty ρ X2) (kty ρ A2) (ktml ρ N2) (ktml ρ Ot2) (ktmll ρ C2) (fun ρ' => dm2 (kw_comp ρ ρ')).
Proof using EL.
  intros [Hy Td]. split; [exact (IWfFlipHyps_kw ρ Hy)|].
  intros ρ' x y z. exact (Td (kw_comp ρ ρ') x y z).
Qed.

(** A position pair split along a length related to the left one. *)
Lemma PosRel_split {G Γ k1 k3 p p'} : PosRel G Γ k1 k3 p p' -> forall k2, NatRel G Γ k1 k2 ->
  exists p'', PosRel G Γ k1 k2 p p'' /\ PosRel G Γ k2 k3 p'' p'.
Proof using EL.
  induction 1 as [k1 k3 m1 m3 Hk1 Hk3 Hm | k1 k3 m1 m3 p p' Hk1 Hk3 Hp IH | k1 k3 p p' Ek Hp]; intros k2 Hk12.
  - destruct (NatRel_inv_succ Hk12 Hk1) as (m2 & Hk2 & Hm12).
    exists (posHd m2). split; apply pos_hd; auto.
    exact (NatRel_trans _ _ _ _ (NatRel_sym _ _ _ _ Hm12) _ Hm).
  - destruct (NatRel_inv_succ Hk12 Hk1) as (m2 & Hk2 & Hm12).
    destruct (IH m2 Hm12) as (p'' & Hp1 & Hp2).
    exists (posTl m2 p''). split; eapply pos_tl; eauto.
  - pose proof (geq_tm_sound (NatRel_geq Hk12)) as E12.
    exists p'. split; apply pos_ne.
    + exact E12.
    + exact Hp.
    + eapply eqtm_trans; [apply eqtm_sym, E12 | exact Ek].
    + eapply gne_tm_conv; [eapply gne_tm_trans; [apply gne_tm_sym, Hp | exact Hp] |].
      apply eqty_fin; [exact ge_notV | exact E12].
Qed.

Lemma IWfNf_whnf_l {G Γ l li X A N Ot C ix dm m w w'} : IWfNf G Γ l li X A N Ot C ix dm m w w' -> whnf w.
Proof using EL. destruct 1; [apply whnf_supi | apply whnf_ne; exact (gne_tm_whne_l H)]. Qed.
Lemma IWfNf_whnf_r {G Γ l li X A N Ot C ix dm m w w'} : IWfNf G Γ l li X A N Ot C ix dm m w w' -> whnf w'.
Proof using EL. destruct 1; [apply whnf_supi | apply whnf_ne; exact (gne_tm_whne_r H)]. Qed.

Lemma IWfNf_sup_inv {G Γ l li X A N Ot C} {ix dm : DomRel G Γ} {m k ki X1 A1 N1 O1 C1 a cs w} :
  IWfNf G Γ l li X A N Ot C ix dm m (tmSupi k ki X1 A1 N1 O1 C1 a cs) w ->
  exists k' ki' X1' A1' N1' O1' C1' a' cs', w = tmSupi k' ki' X1' A1' N1' O1' C1' a' cs' /\
    IWfEq (G := G) (i := ge_layer) Γ l li k ki X X1 A A1 N N1 Ot O1 C C1 /\
    IWfEq (G := G) (i := ge_layer) Γ l li k' ki' X X1' A A1' N N1' Ot O1' C C1' /\
    (forall ρ : kwk G Γ, dm ρ (ktm ρ a) (ktm ρ a')) /\
    (forall ρ : kwk G Γ, ix ρ (ktml ρ Ot)[lsingle (ktm ρ a)] (ktm ρ m)) /\
    (forall ρ : kwk G Γ,
       DVecISp (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
         (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ'))
         (ktmll ρ C)[llift (lsingle (ktm ρ a))] (ktml ρ N)[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')).
Proof using EL.
  intros H. remember (tmSupi k ki X1 A1 N1 O1 C1 a cs) as s eqn:Es. destruct H.
  - injection Es as -> -> -> -> -> -> -> -> ->. do 9 eexists; split; [reflexivity|]. eauto 20.
  - subst. exfalso. pose proof (gne_tm_whne_l H) as Hw. inversion Hw.
Qed.

Lemma IWfNf_ne_inv {G Γ l li X A N Ot C} {ix dm : DomRel G Γ} {m ν w} :
  whne ν -> IWfNf G Γ l li X A N Ot C ix dm m ν w -> [ G ; Γ ⊢ ν ~ w : tyIWf l li X A N Ot C m @ lmax l li ].
Proof using . intros Hν H. destruct H; [inversion Hν | exact H]. Qed.

(** A spine at a length of a known shape. *)
Lemma DVecISp_zero_inv {G Γ l li X A N Ot C ix dm c k cs cs'} : DVecISp G Γ l li X A N Ot C ix dm c k cs cs' ->
  [ G ; Γ ⊢g k ⤳* zero : tyNat @ lzero ] -> UnitRel G Γ (lmax l li) cs cs'.
Proof using EL.
  destruct 1 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hk|? ? ? ? ? ? ? ? ? ? ? ? ? m ? ? ? ? Hk
                |? ? ? ? ? ? ? ? ? ? ? ? ? ν ? ? Hk Hν]; intros Hz; [assumption| |].
  - assert (Y : succ m = zero) by (eapply tmred_whnf_det; [exact Hk | exact Hz | constructor | constructor]).
    discriminate Y.
  - assert (Y : ν = zero)
      by (eapply tmred_whnf_det; [exact Hk | exact Hz | constructor; exact (gne_tm_whne_l Hν) | constructor]).
    subst ν. pose proof (gne_tm_whne_l Hν) as Z. inversion Z.
Qed.

Lemma DVecISp_succ_inv {G Γ l li X A N Ot C ix dm c k m cs cs'} :
  DVecISp G Γ l li X A N Ot C ix dm c k cs cs' ->
  [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  exists w w',
    [ G ; Γ ⊢g cs ⤳* w : tySig (lmax l li) (lmax l li) (dvecHd m (iwfFamT l li X A N Ot C c))
                            (dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c)) @ lmax (lmax l li) (lmax l li) ] /\
    [ G ; Γ ⊢g cs' ⤳* w' : tySig (lmax l li) (lmax l li) (dvecHd m (iwfFamT l li X A N Ot C c))
                            (dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c)) @ lmax (lmax l li) (lmax l li) ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tySig (lmax l li) (lmax l li) (dvecHd m (iwfFamT l li X A N Ot C c))
                         (dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c)) @ lmax (lmax l li) (lmax l li) ] /\
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
Proof using EL.
  destruct 1 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hk|? ? ? ? ? ? ? ? ? ? ? ? ? m0 ? ? w w' Hk Hcs Hcs' Hn Hn' Heq Hf Hs
                |? ? ? ? ? ? ? ? ? ? ? ? ? ν ? ? Hk Hν]; intros Hsk.
  - assert (Y : zero = succ m) by (eapply tmred_whnf_det; [exact Hk | exact Hsk | constructor | constructor]).
    discriminate Y.
  - assert (Y : succ m0 = succ m) by (eapply tmred_whnf_det; [exact Hk | exact Hsk | constructor | constructor]).
    injection Y as ->. exists w, w'. eauto 10.
  - assert (Y : ν = succ m)
      by (eapply tmred_whnf_det; [exact Hk | exact Hsk | constructor; exact (gne_tm_whne_l Hν) | constructor]).
    subst ν. pose proof (gne_tm_whne_l Hν) as Z. inversion Z.
Qed.

Lemma DVecISp_ne_inv {G Γ l li X A N Ot C ix dm c k ν cs cs'} : DVecISp G Γ l li X A N Ot C ix dm c k cs cs' ->
  [ G ; Γ ⊢g k ⤳* ν : tyNat @ lzero ] -> whne ν ->
  NeRel G Γ (tyDVec (lmax l li) ν (iwfFamT l li X A N Ot C c)) (tyDVec (lmax l li) ν (iwfFamT l li X A N Ot C c))
    (lmax l li) cs cs'.
Proof using EL.
  destruct 1 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hk|? ? ? ? ? ? ? ? ? ? ? ? ? m0 ? ? ? ? Hk
                |? ? ? ? ? ? ? ? ? ? ? ? ? ν0 ? ? Hk Hν0 Hne]; intros Hνk Hν.
  - assert (Y : zero = ν) by (eapply tmred_whnf_det; [exact Hk | exact Hνk | constructor | now constructor]).
    subst ν. inversion Hν.
  - assert (Y : succ m0 = ν) by (eapply tmred_whnf_det; [exact Hk | exact Hνk | constructor | now constructor]).
    subst ν. inversion Hν.
  - assert (Y : ν0 = ν)
      by (eapply tmred_whnf_det; [exact Hk | exact Hνk | constructor; exact (gne_tm_whne_l Hν0) | now constructor]).
    now subst ν0.
Qed.

Lemma IWfRel_trans_all :
  (forall G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2, IWfRel G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2 ->
     forall l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 m2 t3,
     IWfTransHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l2 li2 X2 A2 N2 Ot2 C2 dm2 ->
     [ G ; Γ ⊢g tyIWf l1 li1 X1 A1 N1 Ot1 C1 m1 ≅ tyIWf l2 li2 X2 A2 N2 Ot2 C2 m2 @ lmax l1 li1 ] ->
     IWfRel G Γ l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 m2 t2 t3 -> IWfRel G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t3) /\
  (forall G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2, IWfNf G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2 ->
     forall l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 m2 t3,
     IWfTransHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l2 li2 X2 A2 N2 Ot2 C2 dm2 ->
     [ G ; Γ ⊢g tyIWf l1 li1 X1 A1 N1 Ot1 C1 m1 ≅ tyIWf l2 li2 X2 A2 N2 Ot2 C2 m2 @ lmax l1 li1 ] ->
     IWfNf G Γ l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 m2 t2 t3 -> IWfNf G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t3) /\
  (forall G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 cs1 cs2,
     DVecISp G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 cs1 cs2 ->
     forall l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 c2 k2 cs3,
     IWfTransHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l2 li2 X2 A2 N2 Ot2 C2 dm2 ->
     NatRel G Γ k1 k2 ->
     [ G ; Γ ,, tyFin k1 @ lzero ⊢g iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1 ≅ iwfFamT l2 li2 X2 A2 N2 Ot2 C2 c2
         @ lmax l1 li1 ] ->
     (forall (ρ : kwk G Γ) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k1) (ktm ρ k2) p p' ->
        ix1 ρ (ktml ρ c1)[lsingle p] (ktml ρ c2)[lsingle p']) ->
     DVecISp G Γ l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 c2 k2 cs2 cs3 ->
     DVecISp G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 cs1 cs3).
Proof using EL.
  apply IWfRel_comb.
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2 w1 w2 Hw1 Hw2 Heq Hn IH
      l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 m2 t3 Hy ET H2.
    pose proof (IWfFlip_lv (proj1 Hy)) as Hml.
    destruct (IWfRel_inv H2) as (w2' & w3 & Hw2' & Hw3 & Heq2 & Hn2).
    assert (HV : [ G ; Γ ⊢g tyIWf l2 li2 X2 A2 N2 Ot2 C2 m2 ≅ tyIWf l1 li1 X1 A1 N1 Ot1 C1 m1 @ lmax l2 li2 ])
      by (eapply eqty_lconv; [apply eqty_sym, ET | exact Hml]).
    assert (Ew : w2' = w2)
      by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | exact (IWfNf_whnf_l Hn2) | exact (IWfNf_whnf_r Hn)]).
    subst w2'.
    econstructor; [exact Hw1 | | |].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw3 | exact HV] | apply lequiv_sym, Hml].
    + eapply geq_tm_trans; [exact Heq|].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq2 | exact HV] | apply lequiv_sym, Hml].
    + exact (IH l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 m2 w3 Hy ET Hn2).
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 k ki k' ki' Xa Aa Na Oa Ca Xb Ab Nb Ob Cb a a' cs cs'
      E1 E2 Hd Ho Hcs IH l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 m2 t3 Hy ET H2.
    destruct (IWfNf_sup_inv H2) as (k'' & ki'' & Xc & Ac & Nc & Oc & Cc & a'' & cs'' & -> & _ & E3 & Hd2 & _ & Hcs2).
    destruct Hy as [Hy0 Td]. pose proof Hy0 as (HE & _ & _ & Hesc & Har & _ & Hch & _).
    apply iwfnf_sup.
    + exact E1.
    + exact (IWfEq_trans ge_typeof ge_notV HE E3).
    + intros ρ. exact (Td ρ _ _ _ (Hd ρ) (Hd2 ρ)).
    + exact Ho.
    + intros ρ. destruct (Hesc ρ _ _ (Hd ρ)) as (Ha & Ha' & Haa).
      refine (IH ρ l2 li2 (kty ρ X2) (kty ρ A2) (ktml ρ N2) (ktml ρ Ot2) (ktmll ρ C2)
               (fun ρ' => ix2 (kw_comp ρ ρ')) (fun ρ' => dm2 (kw_comp ρ ρ'))
               (ktmll ρ C2)[llift (lsingle (ktm ρ a'))] (ktml ρ N2)[lsingle (ktm ρ a')] (ktm ρ cs'')
               (IWfTransHyps_kw ρ (conj Hy0 Td)) (Har ρ _ _ (Hd ρ))
               (IWf_fam_eq ge_typeof ge_notV (IWfEq_kw ρ HE) Ha Ha' Haa) _ (Hcs2 ρ)).
      intros ρ' p p' Hp. rewrite !ktml_comp_child. rewrite !ktm_comp_single in Hp.
      exact (Hch _ _ _ (Hd (kw_comp ρ ρ')) p p' Hp).
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 ν ν' Hν l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 m2 t3 Hy ET H2.
    pose proof (IWfFlip_lv (proj1 Hy)) as Hml.
    pose proof (IWfNf_ne_inv (gne_tm_whne_r Hν) H2) as Hν2.
    assert (HV : [ G ; Γ ⊢g tyIWf l2 li2 X2 A2 N2 Ot2 C2 m2 ≅ tyIWf l1 li1 X1 A1 N1 Ot1 C1 m1 @ lmax l2 li2 ])
      by (eapply eqty_lconv; [apply eqty_sym, ET | exact Hml]).
    apply iwfnf_ne. eapply gne_tm_trans; [exact Hν |].
    eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν2 | exact HV] | apply lequiv_sym, Hml].
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 cs1 cs2 Hk Hu l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 c2 k2 cs3
      Hy Hkk _ _ H2.
    pose proof (DVecISp_zero_inv H2 (NatRel_inv_zero Hkk Hk)) as Hu2.
    apply visp_zero; [exact Hk|].
    eapply UnitRel_trans; [exact Hu | apply (UnitRel_lconv (IWfFlip_lv (proj1 Hy))), Hu2].
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 m1 cs1 cs2 w1 w2 Hk Hcs1 Hcs2 Hwh1 Hwh2 Heq
      Hfst IHfst Hsnd IHsnd l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 c2 k2 cs3 Hy Hkk HF HP H2.
    pose proof (proj1 Hy) as Hy0. pose proof Hy0 as (HE & _).
    pose proof HE as (Hll & Hlli & (Wl & Wli & HX & HA & HN & HO & HC) & _ & _ & _ & _ & _
                      & HX' & HA' & HN' & HO' & HC').
    pose proof (IWfFlip_lv Hy0) as Hml. pose proof (lequiv_sym _ _ _ Hml) as Hml'.
    assert (HL : lwf (gL G) (lmax l1 li1)) by (split; assumption).
    assert (HL2 : lwf (gL G) (lmax l2 li2)) by exact (lequiv_wf_l _ _ _ Hml).
    assert (Hml2 : lequiv (gL G) (lmax (lmax l2 li2) (lmax l2 li2)) (lmax (lmax l1 li1) (lmax l1 li1)))
      by now apply lequiv_max.
    destruct (NatRel_inv_succ Hkk Hk) as (m2 & Hk2 & Hmm).
    destruct (DVecISp_succ_inv H2 Hk2) as (w2' & w3 & Hcs2' & Hcs3 & Hwh2' & Hwh3 & Heq2 & Hfst2 & Hsnd2).
    assert (Ew : w2' = w2) by (eapply tmred_whnf_det; [exact Hcs2' | exact Hcs2 | exact Hwh2' | exact Hwh2]).
    subst w2'.
    pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
    pose proof (eqtm_wf_l ge_typeof Em) as Hm1. pose proof (eqtm_wf_r ge_typeof Em) as Hm2.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hk) as Ek.
    assert (HF1 : [ G ; Γ ,, tyFin (succ m1) @ lzero ⊢g iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1
                    ≅ iwfFamT l2 li2 X2 A2 N2 Ot2 C2 c2 @ lmax l1 li1 ]).
    { refine (stab_eqty ge_typeof _ (lequiv_refl (gL G) lzero I) _ HF).
      - apply eqty_fin; [exact ge_notV | exact Ek].
      - apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV |].
        exact (eqtm_wf_r ge_typeof Ek). }
    pose proof (eqty_wf_l ge_typeof HF1) as HF1w.
    pose proof (dvecHd_eqty ge_typeof ge_notV ge_compt Hm1 Hm2 Em HF1w HF1) as EH.
    assert (ETf : [ G ; Γ ⊢g tyIWf l1 li1 X1 A1 N1 Ot1 C1 c1[lsingle (posHd m1)]
                    ≅ tyIWf l2 li2 X2 A2 N2 Ot2 C2 c2[lsingle (posHd m2)] @ lmax l1 li1 ]).
    { pose proof EH as Y. rewrite !iwfFamT_single in Y by eauto using wf_ty_nf, wf_tm_nf. exact Y. }
    assert (ETs : [ G ; Γ ,, tyFin m1 @ lzero ⊢g iwfFamT l1 li1 X1 A1 N1 Ot1 C1 (posMv m1 c1)
                    ≅ iwfFamT l2 li2 X2 A2 N2 Ot2 C2 (posMv m2 c2) @ lmax l1 li1 ]).
    { rewrite <- !iwfFamT_mv. exact (dvecMv_eqty ge_typeof ge_notV ge_compt Hm1 Hm2 Em HF1w HF1). }
    set (F1 := iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1) in *. set (F2 := iwfFamT l2 li2 X2 A2 N2 Ot2 C2 c2) in *.
    pose proof (dvec_sig_eqty ge_typeof ge_notV ge_compt Hml' HL Hm1 Hm2 Em HF1w HF1) as ES.
    assert (HV : [ G ; Γ ⊢g tySig (lmax l2 li2) (lmax l2 li2) (dvecHd m2 F2) (dvecTl (lmax l2 li2) m2 F2)
                   ≅ tySig (lmax l1 li1) (lmax l1 li1) (dvecHd m1 F1) (dvecTl (lmax l1 li1) m1 F1)
                   @ lmax (lmax l2 li2) (lmax l2 li2) ])
      by (eapply eqty_lconv; [apply eqty_sym, ES | exact Hml2]).
    assert (HH : [ G ; Γ ⊢g dvecHd m1 F1 @ lmax l1 li1 ])
      by exact (wf_ty_single ge_typeof HF1w (fin_inl_wf ge_typeof ge_notV ge_compt Hm1)).
    assert (HH2 : [ G ; Γ ⊢g dvecHd m2 F2 @ lmax l2 li2 ])
      by (eapply wft_lconv; [exact (eqty_wf_r ge_typeof EH) | exact Hml]).
    assert (HΓ1 : [ G ; Γ ,, dvecHd m1 F1 @ lmax l1 li1 ⊢g ]) by (apply ext_wf_g; [exact HH | exact HL]).
    assert (HΓ2 : [ G ; Γ ,, dvecHd m2 F2 @ lmax l2 li2 ⊢g ]) by (apply ext_wf_g; [exact HH2 | exact HL2]).
    pose proof Hy0 as (_ & _ & _ & _ & _ & _ & _ & HGy & Hiey).
    destruct (iwf_succ_geq HE HGy Hk Hk2 Hmm HF (fun ρ p p' Hp => Hiey ρ _ _ (HP ρ p p' Hp))) as [GH GT].
    assert (RA : [ G ; Γ ⊢ dvecHd m1 F1 ≈ dvecHd m1 F1 @ lmax l1 li1 ])
      by exact (geq_ty_trans GH (geq_ty_sym GH)).
    assert (RB : [ G ; Γ ,, dvecHd m1 F1 @ lmax l1 li1 ⊢ dvecTl (lmax l1 li1) m1 F1
                   ≈ dvecTl (lmax l1 li1) m1 F1 @ lmax l1 li1 ])
      by exact (geq_ty_trans (GT _ _ HΓ1) (geq_ty_sym (GT _ _ HΓ1))).
    assert (MA : forall Y, [ G ; Γ ⊢ dvecHd m1 F1 ≈ Y @ lmax l1 li1 ] -> [ G ; Γ ⊢ dvecHd m2 F2 ≈ Y @ lmax l2 li2 ]).
    { intros Y HY. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, GH | exact HY] | exact Hml]. }
    assert (MB : forall Y, [ G ; Γ ,, dvecHd m1 F1 @ lmax l1 li1 ⊢ dvecTl (lmax l1 li1) m1 F1 ≈ Y @ lmax l1 li1 ] ->
                  [ G ; Γ ,, dvecHd m2 F2 @ lmax l2 li2 ⊢ dvecTl (lmax l2 li2) m2 F2 ≈ Y @ lmax l2 li2 ]).
    { intros Y HY. eapply geq_ty_lconv; [| exact Hml].
      eapply geq_ty_trans; [apply geq_ty_sym, (GT _ _ HΓ2) |].
      exact (geq_ty_ctxconv EH Hml' HΓ2 HY). }
    assert (R1 : lequiv (gL G) (lmax l1 li1) (lmax l1 li1)) by now apply lequiv_refl.
    apply (visp_succ G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 m1 cs1 cs3 w1 w3).
    + exact Hk.
    + exact Hcs1.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs3 | exact HV] | apply lequiv_sym, Hml2].
    + exact Hwh1.
    + exact Hwh3.
    + eapply geq_tm_trans; [exact Heq|].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq2 | exact HV] | apply lequiv_sym, Hml2].
    + intros la lb Ax Bx la'' lb'' Ax'' Bx'' H1 H2' H3 H4 HAx HBx HAx'' HBx''.
      pose proof (Hfst2 (lmax l1 li1) (lmax l1 li1) _ _ la'' lb'' Ax'' Bx'' Hml' Hml'
                    (lequiv_trans _ _ _ _ H3 Hml') (lequiv_trans _ _ _ _ H4 Hml')
                    (MA _ RA) (MB _ RB) (MA _ HAx'') (MB _ HBx'')) as Y2.
      exact (IHfst la lb Ax Bx (lmax l1 li1) (lmax l1 li1) _ _ H1 H2' R1 R1 HAx HBx RA RB
               l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 _ _ Hy ETf Y2).
    + intros la lb Ax Bx la'' lb'' Ax'' Bx'' H1 H2' H3 H4 HAx HBx HAx'' HBx''.
      pose proof (Hsnd2 (lmax l1 li1) (lmax l1 li1) _ _ la'' lb'' Ax'' Bx'' Hml' Hml'
                    (lequiv_trans _ _ _ _ H3 Hml') (lequiv_trans _ _ _ _ H4 Hml')
                    (MA _ RA) (MB _ RB) (MA _ HAx'') (MB _ HBx'')) as Y2.
      refine (IHsnd la lb Ax Bx (lmax l1 li1) (lmax l1 li1) _ _ H1 H2' R1 R1 HAx HBx RA RB
               l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 _ _ _ Hy Hmm ETs _ Y2).
      intros ρ p p' Hp. rewrite !ktml_posMv_single by eauto using wf_tm_nf. apply HP.
      apply pos_tl; [exact (kw_tmred_succ Hk ρ) | exact (kw_tmred_succ Hk2 ρ) | exact Hp].
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 ν1 cs1 cs2 Hk Hν1 Hne
      l2 li2 X2 A2 N2 Ot2 C2 ix2 dm2 c2 k2 cs3 Hy Hkk HF _ H2.
    pose proof (IWfFlip_lv (proj1 Hy)) as Hml. pose proof (lequiv_sym _ _ _ Hml) as Hml'.
    destruct (NatRel_inv_ne Hkk Hk (gne_tm_whne_l Hν1)) as (ν2 & Hk2 & Hνν).
    pose proof (DVecISp_ne_inv H2 Hk2 (gne_tm_whne_r Hνν)) as Hne2.
    apply (visp_ne G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 ν1 cs1 cs3); [exact Hk | exact Hν1 |].
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Eν.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hk) as Ek.
    assert (HFν : [ G ; Γ ,, tyFin ν1 @ lzero ⊢g iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1
                    ≅ iwfFamT l2 li2 X2 A2 N2 Ot2 C2 c2 @ lmax l1 li1 ]).
    { refine (stab_eqty ge_typeof _ (lequiv_refl (gL G) lzero I) _ HF).
      - apply eqty_fin; [exact ge_notV | exact Ek].
      - apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV |].
        exact (eqtm_wf_r ge_typeof Ek). }
    assert (EV : [ G ; Γ ⊢g tyDVec (lmax l1 li1) ν1 (iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1)
                    ≅ tyDVec (lmax l2 li2) ν2 (iwfFamT l2 li2 X2 A2 N2 Ot2 C2 c2) @ lmax l1 li1 ]).
    { apply eqty_dvec; [exact (compt_notV _ ge_compt) | exact Hml' | exact (eqtm_wf_l ge_typeof Eν) | exact Eν
                       | exact (eqty_wf_l ge_typeof HFν) | exact HFν]. }
    assert (EV' : [ G ; Γ ⊢g tyDVec (lmax l2 li2) ν2 (iwfFamT l2 li2 X2 A2 N2 Ot2 C2 c2)
                     ≅ tyDVec (lmax l1 li1) ν1 (iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1) @ lmax l2 li2 ])
      by (eapply eqty_lconv; [apply eqty_sym, EV | exact Hml]).
    pose proof (NeRel_conv2 EV' EV' Hne2) as Hne2'.
    apply (NeRel_lconv _ _ _ _ _ _ (lequiv_sym _ _ _ Hml)) in Hne2'.
    pose proof (eqty_wf_l ge_typeof EV) as HV1.
    eapply NeRel_trans; [apply eqty_refl, HV1 | apply eqty_refl, HV1 | exact Hne | exact Hne2'].
Qed.

End IWfTrans.

(** ** Transitivity *)

Lemma LR_trans_step n : (forall m, m < n -> Ptrans m) -> Ptrans n.
Proof using EL VL.
  intros IHn G Γ T1 T2 l R12 H.
  induction H as [G Γ T1 T2 l R Hl HT1 HT2 HR
                 | G Γ T1 T2 l l1 l2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l V1 V2 R HT1 HT2 HV HR
                 | G Γ T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 R P1 domAd1 IHdom codAd1 IHcod HR
                 | G Γ T1 T2 l R Hj HM
                 | G Γ T1 T2 l l1 l2 U1 U2 instR R Hj Hl Hl2 Hw1 HT1 HT2 HU1 HU2 Hgeq instAd IHinst HR
                 | G Γ T1 T2 l Δ1 Δ2 l1 l2 l3 l4 U1 U2 instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HΔ HU1 HU2
                     Hgeq instAd IHinst HR
                 | G Γ T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 R P1 domAd1 IHdom codAd1 IHcod HR
                 | G Γ T1 T2 l l1 l2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l l1 l2 A1 A2 a1 a2 b1 b2 R Hl Hl2 Hn HT1 HT2 HA1 HA12 Ha12 Hb12 HR
                 | G Γ T1 T2 l l1 l2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l l1 l2 A1 A2 a1 a2 b1 b2 RA R Hl Hl2 Hn HT1 HT2 HA1 HA12 Ha12 Hb12
                     HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T1 T2 l l1 l2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 R P1 domAd1 IHdom codAd1 IHcod HR
                 | G Γ T1 T2 l l1 l2 A1 A2 N1 N2 domR1 R Hl Hl2 Hw HT1 HT2 HA1 HA2 HN1t HN2t HAA HNN
                     domAd1 IHdom arAd1 HR
                 | G Γ T1 T2 l l1 l2 A1 A2 RQ R Hl Hl2 Hw HT1 HT2 HA1 HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T1 T2 l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                     HT1 HT2 HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                     widxAd IHwidx Hwisym Hwistr wdomAd IHwdom warAd wotAd wchAd wixAd HR
                 | G Γ T1 T2 l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                     Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT1 HT2 HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                     HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
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
    destruct (LR_inv_pi H2 (pf_red' P1)) as (k3 & k4 & A3 & B3 & domR2 & codR2 &
      P2 & domAd2 & codAd2 & HR2).
    pose proof (poly_trans P1 P2) as P13.
    destruct P1 as [Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HA1 HA2 HB1 HB2 HA12 HB12].
    destruct P2 as [Hk Hk3 Hk4 _ _ _ HT3 HA2' HA3 HB2' HB3 HA23 HB23].
    assert (HΓ : [ G ; Γ ⊢g ]) by exact (ctx_of_ty HA1).
    assert (Hl13 : lequiv (gL G) l1 l3) by solve [apply lequiv_sym; assumption].
    assert (Hl24 : lequiv (gL G) l2 l4) by solve [apply lequiv_sym; assumption].
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
    pose proof (pf_A' P13) as HA3'. pose proof (pf_AA P13) as HA13. pose proof (pf_BB P13) as HB13.
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
    + eapply (LRpi n (LRbelow n) G Γ T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1); [exact P13|..].
      all: try eassumption.
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
  - (* contextual types *)
    assert (HM2 : ModRel G Γ T2 T3 l R23)
      by (destruct (ModRel_red_r HM) as [(Δ & k & HT2) | (Δ & A & k & HT2)];
          [exact (proj2 (LR_inv_CTyp H2 HT2)) | exact (proj2 (LR_inv_CTrm H2 HT2))]).
    destruct (ModRel_trans HM HM2) as [H13 Htr].
    split; [now apply LRmod | exact Htr].
  - (* CΠ: the second instance at [(Δ', Δ')] *)
    destruct (LR_inv_cpi H2 HT2) as (m2 & U3 & instR2 & _ & _ & Hm2 & _ & HT3 & _ & HU3 & Hgeq2 &
      instAd2 & HR2).
    pose proof (lequiv_trans _ _ _ _ Hm2 Hl2) as Hm21.
    assert (Hdiag : forall (ρ : kwk G Γ) Δ Δ', vp_ctx lr_vp (kw_G ρ) Δ Δ' -> vp_ctx lr_vp (kw_G ρ) Δ' Δ')
      by (intros ρ Δ Δ' h; exact (vpl_ctx_trans (vpl_ctx_sym h) h)).
    assert (Hgeq13 : [ G ; Γ ⊢ tyCPi l1 U1 ≈ tyCPi m2 U3 @ l1 ])
      by (eapply geq_ty_trans; [exact Hgeq | eapply geq_ty_lconv; [exact Hgeq2 | solve [apply lequiv_sym; assumption]]]).
    assert (HR13 : releq R (CPiRel G Γ l1 m2 U1 U3 instR)).
    { assert (HP : [ G ; Γ ⊢g tyCPi l2 U2 ≅ tyCPi m2 U3 @ l1 ])
        by (eapply eqty_lconv; [apply geq_ty_sound, Hgeq2 | solve [apply lequiv_sym; assumption]]).
      eapply releq_trans; [exact HR|]. intros t t'; split.
      - apply (CPiRel_dir HP); intros; apply releq_refl.
      - apply (CPiRel_dir (eqty_sym _ _ _ _ _ _ HP)); intros; apply releq_refl. }
    split.
    + eapply (LRcpi n (LRbelow n) G Γ T1 T3 l l1 m2 U1 U3 instR).
      * exact Hj.
      * exact Hl.
      * exact Hm21.
      * exact Hw1.
      * exact HT1.
      * eapply tyred_lconv; [exact HT3 | apply lequiv_refl; exact (lequiv_wf_l _ _ _ Hl)].
      * exact HU1.
      * exact (lconv_ty HU3 Hl2).
      * exact Hgeq13.
      * intros ρ Δ Δ' h.
        exact (proj1 (IHinst ρ Δ Δ' h _ _
                        (LR_lconv _ _ _ _ _ _ _ _ _ (instAd2 ρ Δ' Δ' (Hdiag ρ Δ Δ' h))
                           (kw_lequiv ρ (lequiv_sym _ _ _ Hl2))))).
      * exact HR13.
    + intros t1 t2 t3 H12' H23'. apply HR. apply HR in H12'. apply HR2 in H23'.
      destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
      destruct H23' as (w2' & w3 & Hw2r' & Hw3r & Hnf2' & Hnf3 & Heq2 & Heq2' & HK2).
      assert (w2' = w2) as -> by (eapply tmred_whnf_det; eauto).
      pose proof (geq_ty_sound Hgeq) as E12. pose proof (geq_ty_sound Hgeq2) as E23.
      exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
      * eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact (lequiv_sym _ _ _ Hl2)] |].
        eapply eqty_lconv; [apply eqty_sym, E23 | exact (lequiv_sym _ _ _ Hl2)].
      * eapply geq_tm_trans; [exact Heq1|].
        eapply geq_tm_conv_l; [exact Heq2 | apply eqty_sym, E12 | exact (lequiv_sym _ _ _ Hl2)].
      * eapply geq_tm_trans; [exact Heq1' | eapply geq_tm_lconv; [exact Heq2 | exact (lequiv_sym _ _ _ Hl2)]].
      * intros ρ Δ Δ' h.
        exact (proj2 (IHinst ρ Δ Δ' h _ _
                        (LR_lconv _ _ _ _ _ _ _ _ _ (instAd2 ρ Δ' Δ' (Hdiag ρ Δ Δ' h))
                           (kw_lequiv ρ (lequiv_sym _ _ _ Hl2))))
                 _ _ _ (HK1 ρ Δ Δ' h) (HK2 ρ Δ' Δ' (Hdiag ρ Δ Δ' h))).
  - (* TΠ: the second instance at [(A', A')], moved to its domain *)
    destruct (LR_inv_tpi H2 HT2) as (Δ3 & m3 & m4 & U3 & instR2 & _ & _ & Hm3 & Hm4 & _ & _ & HT3 & HΔ23 &
      _ & HU3 & Hgeq2 & instAd2 & HR2).
    assert (Hdiag : forall (ρ : kwk G Γ) A A', vp_ty lr_vp (kw_G ρ) Δ1⟦kw_γ ρ⟧ A A' l1 ->
                      vp_ty lr_vp (kw_G ρ) Δ2⟦kw_γ ρ⟧ A' A' l3)
      by (intros ρ A A' h;
          exact (vpl_ty_lconv (lequiv_sym _ _ _ (kw_lequiv ρ Hl3))
                   (vpl_ty_ctx (vpl_ctx_gwk (kw_gok ρ) (kw_glob ρ) HΔ)
                      (vpl_ty_trans (vpl_ty_sym h) h)))).
    assert (Hgeq13 : [ G ; Γ ⊢ tyTPi Δ1 l1 l2 U1 ≈ tyTPi Δ3 m3 m4 U3 @ l2 ])
      by (eapply geq_ty_trans; [exact Hgeq | eapply geq_ty_lconv; [exact Hgeq2 | solve [apply lequiv_sym; assumption]]]).
    assert (HR13 : releq R (TPiRel G Γ Δ1 Δ3 l1 l2 m3 m4 U1 U3 instR)).
    { assert (HP : [ G ; Γ ⊢g tyTPi Δ2 l3 l4 U2 ≅ tyTPi Δ3 m3 m4 U3 @ l2 ])
        by (eapply eqty_lconv; [apply geq_ty_sound, Hgeq2 | solve [apply lequiv_sym; assumption]]).
      eapply releq_trans; [exact HR|]. intros t t'; split.
      - apply (TPiRel_dir HP); intros; apply releq_refl.
      - apply (TPiRel_dir (eqty_sym _ _ _ _ _ _ HP)); intros; apply releq_refl. }
    split.
    + eapply (LRtpi n (LRbelow n) G Γ T1 T3 l Δ1 Δ3 l1 l2 m3 m4 U1 U3 instR).
      * exact Hj.
      * exact Hl.
      * exact (lequiv_trans _ _ _ _ Hm3 Hl3).
      * exact (lequiv_trans _ _ _ _ Hm4 Hl4).
      * exact Hw1.
      * exact Hw2.
      * exact HT1.
      * eapply tyred_lconv; [exact HT3 | apply lequiv_refl; exact (lequiv_wf_l _ _ _ Hl)].
      * exact (vpl_ctx_trans HΔ HΔ23).
      * exact HU1.
      * exact HU3.
      * exact Hgeq13.
      * intros ρ A A' h.
        exact (proj1 (IHinst ρ A A' h _ _
                        (LR_lconv _ _ _ _ _ _ _ _ _ (instAd2 ρ A' A' (Hdiag ρ A A' h))
                           (kw_lequiv ρ (lequiv_sym _ _ _ Hl4))))).
      * exact HR13.
    + intros t1 t2 t3 H12' H23'. apply HR. apply HR in H12'. apply HR2 in H23'.
      destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
      destruct H23' as (w2' & w3 & Hw2r' & Hw3r & Hnf2' & Hnf3 & Heq2 & Heq2' & HK2).
      assert (w2' = w2) as -> by (eapply tmred_whnf_det; eauto).
      pose proof (geq_ty_sound Hgeq) as E12. pose proof (geq_ty_sound Hgeq2) as E23.
      exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
      * eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact (lequiv_sym _ _ _ Hl4)] |].
        eapply eqty_lconv; [apply eqty_sym, E23 | exact (lequiv_sym _ _ _ Hl4)].
      * eapply geq_tm_trans; [exact Heq1|].
        eapply geq_tm_conv_l; [exact Heq2 | apply eqty_sym, E12 | exact (lequiv_sym _ _ _ Hl4)].
      * eapply geq_tm_trans; [exact Heq1' | eapply geq_tm_lconv; [exact Heq2 | exact (lequiv_sym _ _ _ Hl4)]].
      * intros ρ A A' h.
        exact (proj2 (IHinst ρ A A' h _ _
                        (LR_lconv _ _ _ _ _ _ _ _ _ (instAd2 ρ A' A' (Hdiag ρ A A' h))
                           (kw_lequiv ρ (lequiv_sym _ _ _ Hl4))))
                 _ _ _ (HK1 ρ A A' h) (HK2 ρ A' A' (Hdiag ρ A A' h))).
  - (* Σ *)
    destruct (LR_inv_sig H2 (pf_red' P1)) as (k3 & k4 & A3 & B3 & domR2 & codR2 &
      P2 & domAd2 & codAd2 & HR2).
    pose proof (poly_trans P1 P2) as P13.
    destruct P1 as [Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HA1 HA2 HB1 HB2 HA12 HB12].
    destruct P2 as [Hk Hk3 Hk4 _ _ _ HT3 HA2' HA3 HB2' HB3 HA23 HB23].
    assert (HΓ : [ G ; Γ ⊢g ]) by exact (ctx_of_ty HA1).
    assert (Hl13 : lequiv (gL G) l1 l3) by solve [apply lequiv_sym; assumption].
    assert (Hl24 : lequiv (gL G) l2 l4) by solve [apply lequiv_sym; assumption].
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
    pose proof (pf_A' P13) as HA3'. pose proof (pf_AA P13) as HA13. pose proof (pf_BB P13) as HB13.
    assert (HP12 : [ G ; Γ ⊢ tySig l1 l2 A1 B1 ≈ tySig l3 l4 A2 B2 @ lmax l1 l2 ])
      by (apply geq_ty_sig; auto).
    assert (HP23 : [ G ; Γ ⊢ tySig l3 l4 A2 B2 ≈ tySig k3 k4 A3 B3 @ lmax l1 l2 ]).
    { eapply geq_ty_lconv; [apply geq_ty_sig; auto using lequiv_sym | now apply lequiv_max]. }
    assert (HR12 : releq R (SigRel G Γ l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1)).
    { assert (Hd : forall ρ, releq (domR1 ρ) (domR1 ρ)) by (intros; apply releq_refl).
      assert (Hc : forall ρ a a' (ha ha' : domR1 ρ a a'), releq (codR1 ρ a a' ha) (codR1 ρ a a' ha'))
        by (intros; apply Hcodirr).
      pose proof (geq_ty_sound HP23) as HP.
      eapply releq_trans; [exact HR|]. intros t t'; split.
      - exact (SigRel_dir Hw1 HA1 HA2 HA3' HA12 HA13 HB12 HB13 HP Hd Hc t t').
      - exact (SigRel_dir Hw1 HA1 HA3' HA2 HA13 HA12 HB13 HB12 (eqty_sym _ _ _ _ _ _ HP) Hd Hc t t'). }
    split.
    + eapply (LRsig n (LRbelow n) G Γ T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1); [exact P13|..].
      all: try eassumption.
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
      * intros ρ la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5.
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
        destruct (HK1 ρ la lb l1 l2 A4 B4 (kty ρ A2) (ktyl ρ B2) Hla Hlb
                    (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) HA4 HB4 RA2 RB2) as [h1 C1].
        assert (X2 : exists h2 : domR2 ρ (tmFst l1 l2 (kty ρ A2) (ktyl ρ B2) (ktm ρ w2))
                                        (tmFst la' lb' A5 B5 (ktm ρ w3)),
                   codR2 ρ _ _ h2 (tmSnd l1 l2 (kty ρ A2) (ktyl ρ B2) (ktm ρ w2))
                                  (tmSnd la' lb' A5 B5 (ktm ρ w3))).
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
        destruct X2 as [h2 C2].
        pose proof (proj2 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd2 ρ) Hl13')) _ _ _ h1 h2) as h.
        exists h.
        pose proof (proj2 (IHcod ρ _ _ h1 _ _
                             (LR_lconv _ _ _ _ _ _ _ _ _ (codAd2 ρ _ _ h2) Hl24')) _ _ _ C1 C2) as X3.
        exact (proj1 (Hcodirr ρ _ _ _ h1 h _ _) X3).
  - (* Unit *)
    destruct (LR_inv_unit H2 HT2) as (l3 & _ & Hl3 & _ & HT3 & HR2).
    split; [eapply (LRunit n (LRbelow n) G Γ T1 T3 l l1 l3); eauto using lequiv_trans|].
    intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
    apply (UnitRel_lconv Hl2) in H23. exact (UnitRel_trans H12 H23).
  - (* sEq *)
    destruct (LR_inv_seq H2 HT2) as (l3 & A3 & a3 & b3 & _ & Hl3 & _ & HT3 & _ & HA23 & Ha23 & Hb23 & HR2).
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'.
    assert (E12 : [ G ; Γ ⊢g A2 ≅ A1 @ l1 ]) by (apply eqty_sym, geq_ty_sound, HA12).
    split.
    + eapply (LRseq n (LRbelow n) G Γ T1 T3 l l1 l3 A1 A3 a1 a3 b1 b3); eauto using lequiv_trans.
      * eapply geq_ty_trans; [exact HA12 | eapply geq_ty_lconv; [exact HA23 | exact Hl2']].
      * eapply geq_tm_trans; [exact Ha12 | eapply geq_tm_conv; [eapply geq_tm_lconv; [exact Ha23 | exact Hl2'] | exact E12]].
      * eapply geq_tm_trans; [exact Hb12 | eapply geq_tm_conv; [eapply geq_tm_lconv; [exact Hb23 | exact Hl2'] | exact E12]].
    + assert (HV : [ G ; Γ ⊢g tySEq l2 A2 a2 b2 ≅ tySEq l1 A1 a1 b1 @ l2 ]).
      { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_seq; eassumption | exact Hl2]. }
      intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
      apply (SEqRel_conv HV Hl2) in H23. exact (SEqRel_trans H12 H23).
  - (* sEmpty *)
    destruct (LR_inv_sempty H2 HT2) as (l3 & _ & Hl3 & _ & HT3 & HR2).
    split; [eapply (LRsempty n (LRbelow n) G Γ T1 T3 l l1 l3); eauto using lequiv_trans|].
    intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
    apply (SEmptyRel_lconv Hl2) in H23. exact (SEmptyRel_trans H12 H23).
  - (* Id *)
    destruct (LR_inv_id H2 HT2) as (l3 & A3 & a3 & b3 & RA2 & _ & Hl3 & _ & HT3 & HA2 & HA23 & Ha23 & Hb23
                                    & HRA2 & Hra2 & Hrb2 & Hps2 & Hpt2 & HR2).
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'.
    pose proof (LR_lconv _ _ _ _ _ _ _ _ _ HRA2 Hl2') as HRA2'.
    destruct (IHRA _ _ HRA2') as [HRA13 Hc].
    assert (Hfl : releq (flipR RA) RA2)
      by exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ HRA) HRA2').
    assert (E12 : [ G ; Γ ⊢g A2 ≅ A1 @ l1 ]) by (apply eqty_sym, geq_ty_sound, HA12).
    split.
    + eapply (LRid n (LRbelow n) G Γ T1 T3 l l1 l3 A1 A3 a1 a3 b1 b3 RA); eauto using lequiv_trans.
      * eapply geq_ty_trans; [exact HA12 | eapply geq_ty_lconv; [exact HA23 | exact Hl2']].
      * eapply geq_tm_trans; [exact Ha12 | eapply geq_tm_conv; [eapply geq_tm_lconv; [exact Ha23 | exact Hl2'] | exact E12]].
      * eapply geq_tm_trans; [exact Hb12 | eapply geq_tm_conv; [eapply geq_tm_lconv; [exact Hb23 | exact Hl2'] | exact E12]].
    + intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
      exact (IdRel_trans Hl2 HA12 Ha12 Hb12 HA1 Hra Hrb Hps Hpt Hfl H12 H23).
  - (* Empty *)
    destruct (LR_inv_empty H2 HT2) as (l3 & _ & Hl3 & _ & HT3 & HR2).
    split; [eapply (LRempty n (LRbelow n) G Γ T1 T3 l l1 l3); eauto using lequiv_trans|].
    intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
    apply (EmptyRel_lconv Hl2) in H23. exact (EmptyRel_trans H12 H23).
  - (* +: the summands compose by their induction hypotheses *)
    destruct (LR_inv_sum H2 HT2) as (u5 & u6 & UA3 & UB3 & RA2 & RB2 & _ & Hu5 & Hu6 & _ & _ & HT3
                                    & _ & HUA23 & _ & HUB23 & HRA2 & HRB2 & _ & _ & _ & _ & HR2).
    pose proof (lequiv_sym _ _ _ Hl3) as Hl3'. pose proof (lequiv_sym _ _ _ Hl4) as Hl4'.
    destruct (IHRA _ _ (LR_lconv _ _ _ _ _ _ _ _ _ HRA2 Hl3')) as [HRA13 CRA].
    destruct (IHRB _ _ (LR_lconv _ _ _ _ _ _ _ _ _ HRB2 Hl4')) as [HRB13 CRB].
    split.
    + eapply (LRsum n (LRbelow n) G Γ T1 T3 l u1 u2 u5 u6 UA UA3 UB UB3 RA RB); eauto using lequiv_trans.
      * eapply geq_ty_trans; [exact HUAA | eapply geq_ty_lconv; [exact HUA23 | exact Hl3']].
      * eapply geq_ty_trans; [exact HUBB | eapply geq_ty_lconv; [exact HUB23 | exact Hl4']].
    + intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
      exact (SumRel_trans Hl3 Hl4 HUAA HUBB CRA CRB H12 H23).
  - (* W: the type-level data as Π's; the terms by [WRel_trans] *)
    destruct (LR_inv_W H2 (pf_red' P1)) as (k3 & k4 & A3 & B3 & domR2 & codR2 &
      P2 & domAd2 & codAd2 & HR2).
    pose proof (poly_trans P1 P2) as P13.
    destruct P1 as [Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HA1 HA2 HB1 HB2 HA12 HB12].
    destruct P2 as [Hk Hk3 Hk4 _ _ _ HT3 HA2' HA3 HB2' HB3 HA23 HB23].
    assert (Hl13 : lequiv (gL G) l1 l3) by solve [apply lequiv_sym; assumption].
    assert (Hl24 : lequiv (gL G) l2 l4) by solve [apply lequiv_sym; assumption].
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
    split.
    + eapply (LRw n (LRbelow n) G Γ T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1); [exact P13|..].
      all: try eassumption.
      intros ρ a a' ha.
      pose proof (Hrefl ρ a a' ha) as haa.
      pose proof (H12 ρ a a' ha) as h2.
      eapply LR_releq; [|apply Hcodirr with (h1 := haa)].
      exact (proj1 (IHcod ρ a a haa _ _
                      (LR_lconv _ _ _ _ _ _ _ _ _ (codAd2 ρ a a' h2) (kw_lequiv ρ Hl24)))).
    + intros t1 t2 t3 H12' H23'. apply HR. apply HR in H12'. apply HR2 in H23'.
      refine (WRel_trans _ _ _ _ _ _ _ _ _ _ H12' _ _ _ _ _ _ _ H23' Hl3 Hl4 HA1 HA12 HB12 _ _ _ _).
      * intros ρ x y h. exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (codAd1 ρ x y h)))).
      * intros ρ x y z h1 h2.
        exact (proj2 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd2 ρ) (kw_lequiv ρ Hl13))) x y z h1 h2).
      * intros ρ x y z h h' u v Huv.
        pose proof (proj2 (IHcod ρ x z h' _ _ (LR_sym _ _ _ _ _ _ _ (codAd1 ρ x z h'))) u v u Huv Huv) as X.
        exact (proj1 (Hcodirr ρ x z y h' h u u) X).
      * intros ρ x y z h12 h13 h23 u w Huw.
        pose proof (proj1 (Hcodirr ρ x z y h13 h12 u w) Huw) as X.
        pose proof (LR_lconv _ _ _ _ _ _ _ _ _ (codAd2 ρ y z h23) (kw_lequiv ρ Hl24)) as C2.
        pose proof (proj1 (IHcod ρ x y h12 _ _ C2)) as C13.
        exact (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ C13 C2 u w) X).
  - (* Wf: the type-level data compose; the terms by [WfRel_trans_all] *)
    destruct (LR_inv_wf H2 HT2) as (l3 & A3 & N3 & domR2 & _ & Hl3 & _ & _ & HT3 & _ & HA3 & _ & HN3t
                                    & HA23 & HNN23 & domAd2 & arAd2 & HR2).
    pose proof (lequiv_sym _ _ _ Hl2) as Hl12.
    assert (Hdom2 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A2) (kty ρ A3) l1 (domR2 ρ))
      by (intros ρ; exact (LR_lconv _ _ _ _ _ _ _ _ _ (domAd2 ρ) (kw_lequiv ρ Hl12))).
    assert (Hdom3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A1) (kty ρ A3) l1 (domR1 ρ))
      by (intros ρ; exact (proj1 (IHdom ρ _ _ (Hdom2 ρ)))).
    assert (Hrefl : forall ρ a a', domR1 ρ a a' -> domR1 ρ a a).
    { intros ρ a a' ha.
      exact (proj2 (IHdom ρ _ _ (LR_sym _ _ _ _ _ _ _ (domAd1 ρ))) a a' a ha ha). }
    assert (H12 : forall ρ a a', domR1 ρ a a' -> domR2 ρ a a')
      by (intros ρ a a' ha; exact (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ (Hdom3 ρ) (Hdom2 ρ) a a') ha)).
    assert (Td : forall ρ x y z, domR1 ρ x y -> domR2 ρ y z -> domR1 ρ x z)
      by (intros ρ; exact (proj2 (IHdom ρ _ _ (Hdom2 ρ)))).
    split.
    + eapply (LRwf n (LRbelow n) G Γ T1 T3 l l1 l3 A1 A3 N1 N3 domR1 R).
      * exact Hl.
      * exact (lequiv_trans _ _ _ _ Hl3 Hl2).
      * exact Hw.
      * exact HT1.
      * exact HT3.
      * exact HA1.
      * exact (lconv_ty HA3 Hl2).
      * exact HN1t.
      * exact (ctx_lvl_tm HA3 Hl2 HN3t).
      * eapply geq_ty_trans; [exact HAA | eapply geq_ty_lconv; [exact HA23 | exact Hl12]].
      * eapply geq_tm_trans; [exact HNN|].
        eapply geq_tm_ctxconv; [| exact Hl2 | apply ext_wf_g; [exact HA1 | exact Hw] | exact HNN23].
        eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HAA | exact Hl2].
      * exact Hdom3.
      * intros ρ a a' ha. eapply NatRel_trans; [exact (arAd1 ρ a a (Hrefl ρ a a' ha)) | exact (arAd2 ρ a a' (H12 ρ a a' ha))].
      * exact HR.
    + intros t1 t2 t3 H12' H23'. apply HR. apply HR in H12'. apply HR2 in H23'.
      exact (proj1 WfRel_trans_all _ _ _ _ _ _ _ _ H12' l2 A2 N2 domR2 t3
               (conj (conj Hl2 (conj HA1 (conj HAA (conj HNN arAd1)))) Td) H23').
  - (* ∥·∥: the carriers compose; the terms are each good alone *)
    destruct (LR_inv_sq H2 HT2) as (l3 & A3 & RQ2 & _ & Hl3 & _ & _ & HT3 & HA2 & HA23 & HRQ2 & _ & _ & HR2).
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'.
    pose proof (LR_lconv _ _ _ _ _ _ _ _ _ HRQ2 Hl2') as HRQ2'.
    destruct (IHRQ _ _ HRQ2') as [HRQ13 _].
    assert (Hfl : releq (flipR RQ) RQ2)
      by exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ HRQ) HRQ2').
    split.
    + eapply (LRsq n (LRbelow n) G Γ T1 T3 l l1 l3 A1 A3 RQ); eauto using lequiv_trans.
      eapply geq_ty_trans; [exact HAA | eapply geq_ty_lconv; [exact HA23 | exact Hl2']].
    + intros t1 t2 t3 H12 H23. apply HR. apply HR in H12. apply HR2 in H23.
      apply (SqRel_conv (RA' := RQ) Hl2 HA2 (geq_ty_lconv (geq_ty_sym HAA) Hl2)) in H23.
      * exact (SqRel_trans H12 H23).
      * intros a; split; intros X; [exact (proj2 (Hfl a a) X) | exact (proj1 (Hfl a a) X)].
  - (* IWf: the type-level data compose; the terms by [IWfRel_trans_all] *)
    destruct (LR_inv_iwf H2 HT2) as (k3 & ki3 & X3 & A3 & N3 & O3 & C3 & m3 & idxR2 & domR2 & _ & Hk3 & Hki3
                                     & _ & _ & _ & HT3 & _ & HX3 & _ & HA3 & _ & HN3 & _ & HO3 & _ & HC3 & _ & Hm3
                                     & HXX23 & HAA23 & HNN23 & HOO23 & HCC23 & Hmm23
                                     & idxAd2 & _ & _ & domAd2 & arAd2 & otAd2 & chAd2 & ixAd2 & HR2).
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'. pose proof (lequiv_sym _ _ _ Hwli2) as Hli2'.
    pose proof (geq_ty_sound HwXX) as EX. pose proof (geq_ty_sound HwAA) as EA.
    pose proof (geq_tm_sound HwNN) as EN. pose proof (geq_tm_sound HwOO) as EO.
    pose proof (geq_tm_sound HwCC) as EC. pose proof (geq_tm_sound Hwmm) as Em.
    assert (HE : IWfEq (G := G) (i := ge_layer) Γ wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC').
    { apply IWfEq_intro; [exact Hl2' | exact Hli2' | exact EX | exact EA | exact EN | exact EO | exact EC
        | exact Hw | exact Hwwi | exact HwX | exact HwA | exact HwN | exact HwO | exact HwC
        | exact HwX' | exact HwA' | exact (eqtm_wf_r ge_typeof EN) | exact (eqtm_wf_r ge_typeof EO)
        | exact (eqtm_wf_r ge_typeof EC)]. }
    (* the index and shape relations compose *)
    assert (Hidx2 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ wX') (kty ρ X3) wli1 (idxR2 ρ))
      by (intros ρ; exact (LR_lconv _ _ _ _ _ _ _ _ _ (idxAd2 ρ) (kw_lequiv ρ Hli2'))).
    assert (Hidx3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ wX) (kty ρ X3) wli1 (widxR ρ))
      by (intros ρ; exact (proj1 (IHwidx ρ _ _ (Hidx2 ρ)))).
    assert (Ti : forall ρ x y z, widxR ρ x y -> idxR2 ρ y z -> widxR ρ x z)
      by (intros ρ; exact (proj2 (IHwidx ρ _ _ (Hidx2 ρ)))).
    assert (Hdom2 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ wA') (kty ρ A3) wl1 (domR2 ρ))
      by (intros ρ; exact (LR_lconv _ _ _ _ _ _ _ _ _ (domAd2 ρ) (kw_lequiv ρ Hl2'))).
    assert (Hdom3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ wA) (kty ρ A3) wl1 (wdomR ρ))
      by (intros ρ; exact (proj1 (IHwdom ρ _ _ (Hdom2 ρ)))).
    assert (Hrefl : forall ρ a a', wdomR ρ a a' -> wdomR ρ a a).
    { intros ρ a a' ha.
      exact (proj2 (IHwdom ρ _ _ (LR_sym _ _ _ _ _ _ _ (wdomAd ρ))) a a' a ha ha). }
    assert (H12 : forall ρ a a', wdomR ρ a a' -> domR2 ρ a a')
      by (intros ρ a a' ha; exact (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ (Hdom3 ρ) (Hdom2 ρ) a a') ha)).
    assert (Td : forall ρ x y z, wdomR ρ x y -> domR2 ρ y z -> wdomR ρ x z)
      by (intros ρ; exact (proj2 (IHwdom ρ _ _ (Hdom2 ρ)))).
    (* contexts and conversions *)
    assert (HΓA : [ G ; Γ ,, wA @ wl1 ⊢g ]) by exact (ext_wf_g HwA Hw).
    assert (HΓAN : [ G ; Γ ,, wA @ wl1 ,, tyFin wN @ lzero ⊢g ])
      by (apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact HwN] | exact I]).
    assert (HA31 : [ G ; Γ ⊢g A3 @ wl1 ]) by exact (lconv_ty HA3 Hl2).
    assert (HN31 : [ G ; Γ ,, A3 @ wl1 ⊢g N3 : tyNat @ lzero ]) by exact (ctx_lvl_tm HA3 Hl2 HN3).
    assert (HΓAN3 : [ G ; Γ ,, A3 @ wl1 ,, tyFin N3 @ lzero ⊢g ])
      by (apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact HN31] | exact I]).
    assert (EA' : [ G ; Γ ⊢g wA' ≅ wA @ wl2 ]) by (eapply eqty_lconv; [apply eqty_sym, EA | exact Hl2]).
    assert (EX1 : [ G ; Γ ,, wA @ wl1 ⊢g wX'⟨↑⟩ ≅ wX⟨↑⟩ @ wli2 ])
      by exact (wk1_eqty G ge_layer ge_typeof _ _ _ _ _ _ HΓA (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EX) Hwli2)).
    assert (EX2 : [ G ; Γ ,, wA @ wl1 ,, tyFin wN @ lzero ⊢g wX'⟨↑⟩⟨↑⟩ ≅ wX⟨↑⟩⟨↑⟩ @ wli2 ])
      by exact (wk1_eqty G ge_layer ge_typeof _ _ _ _ _ _ HΓAN EX1).
    split.
    + eapply (LRiwf n (LRbelow n) G Γ T1 T3 l wl1 wli1 k3 ki3 wX X3 wA A3 wN N3 wO O3 wC C3 wm m3 widxR wdomR R).
      * exact Hl.
      * exact (lequiv_trans _ _ _ _ Hk3 Hl2).
      * exact (lequiv_trans _ _ _ _ Hki3 Hwli2).
      * exact Hw.
      * exact Hwwi.
      * exact HT1.
      * exact HT3.
      * exact HwX.
      * exact (lconv_ty HX3 Hwli2).
      * exact HwA.
      * exact HA31.
      * exact HwN.
      * exact HN31.
      * exact HwO.
      * eapply wf_lconv; [exact (ctx_lvl_tm HA3 Hl2 HO3) | exact Hli2'].
      * exact HwC.
      * eapply wf_lconv; [| exact Hli2'].
        exact (mv_tm ge_typeof (stab2_lsub ge_typeof (eqty_refl _ _ _ _ _ HA3) Hl2 HΓAN3) HC3).
      * exact Hwm.
      * eapply wf_lconv; [exact Hm3 | exact Hli2'].
      * eapply geq_ty_trans; [exact HwXX | eapply geq_ty_lconv; [exact HXX23 | exact Hli2']].
      * eapply geq_ty_trans; [exact HwAA | eapply geq_ty_lconv; [exact HAA23 | exact Hl2']].
      * eapply geq_tm_trans; [exact HwNN|].
        eapply geq_tm_ctxconv; [exact EA' | exact Hl2 | exact HΓA | exact HNN23].
      * eapply geq_tm_trans; [exact HwOO|].
        eapply geq_tm_lconv; [| exact Hli2']. eapply geq_tm_conv; [| exact EX1].
        eapply geq_tm_ctxconv; [exact EA' | exact Hl2 | exact HΓA | exact HOO23].
      * eapply geq_tm_trans; [exact HwCC|].
        eapply geq_tm_lconv; [| exact Hli2']. eapply geq_tm_conv; [| exact EX2].
        eapply geq_tm_ctxconv; [| exact (lequiv_refl (gL G) lzero I) | exact HΓAN |].
        { apply eqty_fin; [exact ge_notV | apply eqtm_sym, EN]. }
        eapply geq_tm_ctxconv2; [exact EA' | exact Hl2 | | exact HCC23].
        apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact (eqtm_wf_r ge_typeof EN)] | exact I].
      * eapply geq_tm_trans; [exact Hwmm|].
        eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Hmm23 | exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EX) Hwli2)]
                             | exact Hli2'].
      * exact Hidx3.
      * exact Hwisym.
      * exact Hwistr.
      * exact Hdom3.
      * intros ρ a a' ha.
        eapply NatRel_trans; [exact (warAd ρ a a (Hrefl ρ a a' ha)) | exact (arAd2 ρ a a' (H12 ρ a a' ha))].
      * intros ρ a a' ha. exact (Ti ρ _ _ _ (wotAd ρ a a (Hrefl ρ a a' ha)) (otAd2 ρ a a' (H12 ρ a a' ha))).
      * intros ρ a a' ha p p' Hp.
        destruct (PosRel_split Hp _ (warAd ρ a a (Hrefl ρ a a' ha))) as (p'' & Hp1 & Hp2).
        exact (Ti ρ _ _ _ (wchAd ρ a a (Hrefl ρ a a' ha) p p'' Hp1) (chAd2 ρ a a' (H12 ρ a a' ha) p'' p' Hp2)).
      * intros ρ. exact (Ti ρ _ _ _ (wixAd ρ) (ixAd2 ρ)).
      * exact HR.
    + assert (Hy : IWfFlipHyps G Γ wl1 wli1 wX wA wN wO wC widxR wdomR wl2 wli2 wX' wA' wN' wO' wC').
      { refine (conj HE (conj Hwisym (conj Hwistr (conj _ (conj warAd (conj wotAd (conj wchAd
                  (conj (conj HwXX (conj HwAA (conj HwNN (conj HwOO HwCC)))) _)))))))).
        - intros ρ a a' h.
          destruct (escape_tm _ _ _ _ _ _ _ _ (wdomAd ρ) a a' h) as (Ha & Ha' & Haa).
          exact (conj Ha (conj Ha' (geq_tm_sound Haa))).
        - intros ρ x y h. exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (widxAd ρ) x y h))). }
      intros t1 t2 t3 H12' H23'. apply HR. apply HR in H12'. apply HR2 in H23'.
      exact (proj1 IWfRel_trans_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12' _ _ _ _ _ _ _ idxR2 domR2 _ _
               (conj Hy Td) (IWf_ty_eq ge_typeof ge_notV HE Em) H23').
  - (* M: the relations compose at the middle index, shape and position
       (their reflexivity from the induction hypotheses and symmetry); the
       terms by [MRn_trans] *)
    destruct (LR_inv_M H2 HT2) as (s1 & s2 & si & X3 & A3 & B3 & C3 & m3 & idxR2 & shR2 & posR2 & _
                                   & Hs1 & Hs2 & Hsi & Wr1 & Wr2 & Wri & _ & HT3 & HX2 & HX3 & HA2 & HA3
                                   & HB2 & HB3 & HC2 & HC3 & _ & Hm3 & HXX23 & HAA23 & HBB23 & HCC23 & Hmm23
                                   & idxAd2 & shAd2 & posAd2 & chAd2 & gB2 & gC2 & gCa2 & imon2 & shmon2
                                   & posmon2 & ixAd2 & HR2).
    pose proof (MSide_of_LR Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HmX HmA HmB HmC HmXX HmAA HmBB HmCC
                  midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon) as HM1.
    pose proof (MSide_of_LR Hs1 Hs2 Hsi Wr1 Wr2 Wri HX2 HA2 HB2 HC2 HXX23 HAA23 HBB23 HCC23
                  idxAd2 shAd2 posAd2 chAd2 gB2 gC2 gCa2 imon2 shmon2 posmon2) as HM2.
    pose proof (MSide_flip HM1) as HM1f.
    pose proof (lequiv_sym _ _ _ Hmr1) as Hmr1'. pose proof (lequiv_sym _ _ _ Hmr2) as Hmr2'.
    pose proof (lequiv_sym _ _ _ Hmri) as Hmri'.
    pose proof (wf_tm_nf Hmm) as Nm. pose proof (wf_tm_nf Hmm') as Nm'. pose proof (wf_tm_nf Hm3) as Nm3.
    (* the index *)
    assert (Hi2 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ mX') (kty ρ X3) mli (idxR2 ρ))
      by (intros ρ; exact (LR_lconv _ _ _ _ _ _ _ _ _ (idxAd2 ρ) (kw_lequiv ρ Hmri'))).
    assert (Hi3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ mX) (kty ρ X3) mli (midxR ρ))
      by (intros ρ; exact (proj1 (IHmidx ρ _ _ (Hi2 ρ)))).
    assert (Ti : forall ρ x y z, midxR ρ x y -> idxR2 ρ y z -> midxR ρ x z)
      by (intros ρ; exact (proj2 (IHmidx ρ _ _ (Hi2 ρ)))).
    assert (Hirefl : forall ρ x x', midxR ρ x x' -> midxR ρ x x)
      by (intros ρ x x' h; exact (proj2 (IHmidx ρ _ _ (LR_sym _ _ _ _ _ _ _ (midxAd ρ))) x x' x h h)).
    assert (Hi12 : forall ρ x x', midxR ρ x x' -> idxR2 ρ x x')
      by (intros ρ x x' h; exact (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ (Hi3 ρ) (Hi2 ρ) x x') h)).
    assert (Ix3 : forall ρ, midxR ρ (ktm ρ mm) (ktm ρ m3)) by (intros ρ; exact (Ti ρ _ _ _ (mixAd ρ) (ixAd2 ρ))).
    (* the shapes *)
    assert (Sh2 : forall ρ y z, idxR2 ρ y z ->
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ mA')[lsingle y] (ktyl ρ A3)[lsingle z] ml1 (shR2 ρ y z))
      by (intros ρ y z h; exact (LR_lconv _ _ _ _ _ _ _ _ _ (shAd2 ρ y z h) (kw_lequiv ρ Hmr1'))).
    assert (Shirr : MShIrr midxR mshR)
      by (intros ρ x y y' h h'; eapply LR_irrel; [exact (mshAd ρ x y h) | exact (mshAd ρ x y' h')]).
    assert (Sc : forall ρ x y z a b c, midxR ρ x y -> idxR2 ρ y z -> mshR ρ x y a b -> shR2 ρ y z b c ->
                   mshR ρ x y a c)
      by (intros ρ x y z a b c h h2; exact (proj2 (IHmsh ρ x y h _ _ (Sh2 ρ y z h2)) a b c)).
    assert (Shrefl : forall ρ x x' a a', midxR ρ x x' -> mshR ρ x x' a a' -> mshR ρ x x' a a)
      by (intros ρ x x' a a' h ha;
          exact (proj2 (IHmsh ρ x x' h _ _ (LR_sym _ _ _ _ _ _ _ (mshAd ρ x x' h))) a a' a ha ha)).
    assert (Sh3 : forall ρ x x', midxR ρ x x' ->
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ mA)[lsingle x] (ktyl ρ A3)[lsingle x'] ml1 (mshR ρ x x')).
    { intros ρ x x' h. pose proof (Hirefl ρ x x' h) as hxx.
      eapply LR_releq; [exact (proj1 (IHmsh ρ x x hxx _ _ (Sh2 ρ x x' (Hi12 ρ x x' h)))) | exact (Shirr ρ x x x' hxx h)]. }
    assert (Sh12 : forall ρ x x' a a', midxR ρ x x' -> mshR ρ x x' a a' -> shR2 ρ x x' a a')
      by (intros ρ x x' a a' h ha;
          exact (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ (Sh3 ρ x x' h) (Sh2 ρ x x' (Hi12 ρ x x' h)) a a') ha)).
    assert (Hsh : forall ρ x x' a a', midxR ρ x x' -> mshR ρ x x' a a' -> mshR ρ x x a a)
      by (intros ρ x x' a a' h ha; exact (proj1 (Shirr ρ x x' x h (Hirefl ρ x x' h) a a) (Shrefl ρ x x' a a' h ha))).
    (* the positions *)
    assert (Pos2 : forall ρ y z b c, idxR2 ρ y z -> shR2 ρ y z b c ->
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyll ρ mB')[lsingle2 y b] (ktyll ρ B3)[lsingle2 z c] ml2
                 (posR2 ρ y z b c))
      by (intros ρ y z b c h hb; exact (LR_lconv _ _ _ _ _ _ _ _ _ (posAd2 ρ y z b c h hb) (kw_lequiv ρ Hmr2'))).
    assert (Pirr : MPosIrr midxR mshR mposR)
      by (intros ρ x y y' a b b' h h' ha ha'; eapply LR_irrel; [exact (mposAd ρ x y a b h ha) | exact (mposAd ρ x y' a b' h' ha')]).
    assert (Prefl : forall ρ x y a b p q, midxR ρ x y -> mshR ρ x y a b -> mposR ρ x y a b p q -> mposR ρ x y a b p p)
      by (intros ρ x y a b p q h ha hp;
          exact (proj2 (IHmpos ρ x y a b h ha _ _ (LR_sym _ _ _ _ _ _ _ (mposAd ρ x y a b h ha))) p q p hp hp)).
    assert (P12 : forall ρ x y z a b c p q, midxR ρ x y -> idxR2 ρ y z -> mshR ρ x y a b -> shR2 ρ y z b c ->
                    mposR ρ x y a b p q -> posR2 ρ y z b c p q).
    { intros ρ x y z a b c p q h h2 ha ha2 hp. pose proof (Pos2 ρ y z b c h2 ha2) as L2.
      exact (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ (proj1 (IHmpos ρ x y a b h ha _ _ L2)) L2 p q) hp). }
    assert (Pos3 : forall ρ x x' a a', midxR ρ x x' -> mshR ρ x x' a a' ->
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyll ρ mB)[lsingle2 x a] (ktyll ρ B3)[lsingle2 x' a'] ml2
                 (mposR ρ x x' a a')).
    { intros ρ x x' a a' h ha. pose proof (Hirefl ρ x x' h) as hxx. pose proof (Hsh ρ x x' a a' h ha) as haa.
      eapply LR_releq; [exact (proj1 (IHmpos ρ x x a a hxx haa _ _
                                        (Pos2 ρ x x' a a' (Hi12 ρ x x' h) (Sh12 ρ x x' a a' h ha))))
                       | exact (Pirr ρ x x x' a a a' hxx h haa ha)]. }
    (* the child index *)
    assert (Ch3 : forall ρ x x' a a' p p', midxR ρ x x' -> mshR ρ x x' a a' -> mposR ρ x x' a a' p p' ->
               midxR ρ (ktmlll ρ mC)[lsingle3 x a p] (ktmlll ρ C3)[lsingle3 x' a' p']).
    { intros ρ x x' a a' p p' h ha hp. pose proof (Hirefl ρ x x' h) as hxx. pose proof (Hsh ρ x x' a a' h ha) as haa.
      pose proof (proj1 (Pirr ρ x x' x a a' a h hxx ha haa p p) (Prefl ρ x x' a a' p p' h ha hp)) as hpp.
      pose proof (proj1 (Pirr ρ x x' x a a' a h hxx ha haa p p') hp) as hpp'.
      exact (Ti ρ _ _ _ (mchAd ρ x x a a p p hxx haa hpp)
               (chAd2 ρ x x' a a' p p' (Hi12 ρ x x' h) (Sh12 ρ x x' a a' h ha)
                  (P12 ρ x x x' a a a' p p' hxx (Hi12 ρ x x' h) haa (Sh12 ρ x x' a a' h ha) hpp'))). }
    (* the families, generically: the second's moved to the first's contexts *)
    assert (EXρ : forall ρ : kwk G Γ, [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ mX' ≅ kty ρ mX @ mli ])
      by (intros ρ; exact (kw_eqty ρ (eqty_sym _ _ _ _ _ _ (geq_ty_sound HmXX)))).
    assert (gB3 : forall ρ x x', midxR ρ x x' ->
               [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ mA)[lsingle x] @ ml1
                   ⊢ (ktyll ρ mB)[llift (lsingle x)] ≈ (ktyll ρ B3)[llift (lsingle x')] @ ml2 ]).
    { intros ρ x x' h. pose proof (Hirefl ρ x x' h) as hxx.
      pose proof (geq_ty_sound (ms_gA HM1 ρ x x hxx)) as EA.
      eapply geq_ty_trans; [exact (mgB ρ x x hxx) |].
      eapply geq_ty_lconv; [| exact (kw_lequiv ρ Hmr2')].
      eapply geq_ty_ctxconv; [exact (geq_ty_sound (ms_gA HM1f ρ x x hxx)) | exact (kw_lequiv ρ Hmr1)
                             | exact (ext_wf_g (eqty_wf_l ge_typeof EA) (kw_lwf ρ Hmw1)) | exact (gB2 ρ x x' (Hi12 ρ x x' h))]. }
    assert (gC3 : forall ρ x x', midxR ρ x x' ->
               [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ mA)[lsingle x] @ ml1 ,, (ktyll ρ mB)[llift (lsingle x)] @ ml2
                   ⊢ (ktmlll ρ mC)[llift (llift (lsingle x))] ≈ (ktmlll ρ C3)[llift (llift (lsingle x'))]
                   : (kty ρ mX)⟨↑⟩⟨↑⟩ @ mli ]).
    { intros ρ x x' h. pose proof (Hirefl ρ x x' h) as hxx.
      pose proof (ctx2_conv ge_typeof (geq_ty_sound (ms_gA HM1f ρ x x hxx)) (kw_lequiv ρ Hmr1)
                    (geq_ty_sound (ms_gB HM1f ρ x x hxx)) (kw_lequiv ρ Hmr2)) as Q.
      pose proof (mgC ρ x x hxx) as GC1.
      pose proof (ctx_of_eqtm ge_typeof (geq_tm_sound GC1)) as HΓ2. pose proof (ctx_pre HΓ2) as HΓ1.
      pose proof (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ2 (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ1 (EXρ ρ))) as EX2.
      eapply geq_tm_trans; [exact GC1 |].
      eapply geq_tm_conv; [| exact EX2]. eapply geq_tm_lconv; [| exact (kw_lequiv ρ Hmri')].
      exact (geq_tm_ctxeq Q (gC2 ρ x x' (Hi12 ρ x x' h))). }
    assert (gCa3 : forall ρ x x' a a', midxR ρ x x' -> mshR ρ x x' a a' ->
               [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ mB)[lsingle2 x a] @ ml2
                   ⊢ (ktmlll ρ mC)[llift (lsingle2 x a)] ≈ (ktmlll ρ C3)[llift (lsingle2 x' a')] : (kty ρ mX)⟨↑⟩ @ mli ]).
    { intros ρ x x' a a' h ha. pose proof (Hirefl ρ x x' h) as hxx. pose proof (Hsh ρ x x' a a' h ha) as haa.
      pose proof (mgCa ρ x x a a hxx haa) as GC1.
      pose proof (ctx_of_eqtm ge_typeof (geq_tm_sound GC1)) as HΓ1.
      pose proof (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ1 (EXρ ρ)) as EX1.
      eapply geq_tm_trans; [exact GC1 |].
      eapply geq_tm_conv; [| exact EX1]. eapply geq_tm_lconv; [| exact (kw_lequiv ρ Hmri')].
      eapply geq_tm_ctxconv; [exact (geq_ty_sound (ms_gBa HM1f ρ x x a a hxx haa)) | exact (kw_lequiv ρ Hmr2)
                             | exact HΓ1 | exact (gCa2 ρ x x' a a' (Hi12 ρ x x' h) (Sh12 ρ x x' a a' h ha))]. }
    (* the composite signature *)
    pose proof (MGeq_trans (ms_geq HM1) (ms_geq HM2)) as (_ & _ & _ & _ & GX & GA & GB & GC).
    pose proof (MSig_lconv ge_typeof ge_notV (conj Wr1 (conj Wr2 (conj Wri (conj HX3 (conj HA3 (conj HB3 HC3))))))
                  Hmr1 Hmr2 Hmri) as (_ & _ & _ & H3X & H3A & H3B & H3C).
    assert (Hs1' : lequiv (gL G) s1 ml1) by exact (lequiv_trans _ _ _ _ Hs1 Hmr1).
    assert (Hs2' : lequiv (gL G) s2 ml2) by exact (lequiv_trans _ _ _ _ Hs2 Hmr2).
    assert (Hsi' : lequiv (gL G) si mli) by exact (lequiv_trans _ _ _ _ Hsi Hmri).
    pose proof (MSide_of_LR Hs1' Hs2' Hsi' Hmw1 Hmw2 Hmwi HmX HmA HmB HmC GX GA GB GC
                  Hi3 Sh3 Pos3 Ch3 gB3 gC3 gCa3 mimon mshmon mposmon) as HM3.
    assert (HI : MIrrHyps G Γ ml1 ml2 mli mX mA mB mC mr1 mr2 mri mX' mA' mB' mC' s1 s2 si X3 A3 B3 C3
                   midxR midxR mshR mshR mposR mposR mm mm' m3).
    { refine (conj HM1 (conj HM3 (conj Shirr (conj _ (conj Nm (conj Nm' (conj Nm3 (conj mixAd Ix3)))))))).
      intros ρ x x' x'' a a' h h' ha. exact (Pirr ρ x x' x'' a a' a' h h' ha (proj1 (Shirr ρ x x' x'' h h' a a') ha)). }
    split.
    + eapply (LRm n (LRbelow n) G Γ T1 T3 l ml1 ml2 mli s1 s2 si mX X3 mA A3 mB B3 mC C3 mm m3 midxR mshR mposR R).
      * exact Hl.
      * exact Hs1'.
      * exact Hs2'.
      * exact Hsi'.
      * exact Hmw1.
      * exact Hmw2.
      * exact Hmwi.
      * exact HT1.
      * exact HT3.
      * exact HmX.
      * exact H3X.
      * exact HmA.
      * exact H3A.
      * exact HmB.
      * exact H3B.
      * exact HmC.
      * exact H3C.
      * exact Hmm.
      * eapply wf_lconv; [exact Hm3 | exact Hmri'].
      * exact GX.
      * exact GA.
      * exact GB.
      * exact GC.
      * eapply geq_tm_trans; [exact Hmmm|].
        eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Hmm23 | exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (geq_ty_sound HmXX)) Hmri)]
                             | exact Hmri'].
      * exact Hi3.
      * exact Sh3.
      * exact Pos3.
      * exact Ch3.
      * exact gB3.
      * exact gC3.
      * exact gCa3.
      * exact mimon.
      * exact mshmon.
      * exact mposmon.
      * exact Ix3.
      * eapply releq_trans; [exact HR | exact (MR_irrel HI)].
    + assert (HT : MTransHyps G Γ ml1 ml2 mli mX mA mB mC mr1 mr2 mri mX' mA' mB' mC' s1 s2 si X3 A3 B3 C3
                     midxR idxR2 mshR shR2 mposR posR2 mm mm' m3)
        by exact (conj HM1 (conj HM2 (conj Nm (conj Nm' (conj Nm3 (conj mixAd (conj ixAd2
                    (conj Sc (conj Shirr (conj Pirr (conj Prefl P12))))))))))).
      intros t1 t2 t3 Y1 Y2. apply HR. apply HR in Y1. apply HR2 in Y2. intros k.
      exact (MRn_trans k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HT t1 t2 t3 (Y1 k) (Y2 k)).
Qed.

Theorem LR_trans n : Ptrans n.
Proof using EL VL.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_trans_step, IHn.
Qed.

(** ** Consequences: reflexivity *)

Corollary LR_refl_l n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> LR n (LRbelow n) G Γ T T l R.
Proof using EL VL. intros H. exact (proj1 (LR_trans n _ _ _ _ _ _ H _ _ (LR_sym _ _ _ _ _ _ _ H))). Qed.

Corollary LR_refl_r n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> LR n (LRbelow n) G Γ T' T' l (flipR R).
Proof using EL VL. intros H. exact (LR_refl_l _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ H)). Qed.

(** Related terms are related to themselves. *)
Corollary LR_tm_refl_l n G Γ T T' l R t t' :
  LR n (LRbelow n) G Γ T T' l R -> R t t' -> R t t.
Proof using EL VL.
  intros H Ht. exact (proj2 (LR_trans n _ _ _ _ _ _ H _ _ (LR_sym _ _ _ _ _ _ _ H)) t t' t Ht Ht).
Qed.

(** The term relation is a PER (M11a: the carriers of [Id] need it). *)
Corollary LR_tm_per n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R ->
  (forall x y, R x y -> R y x) /\ (forall x y z, R x y -> R y z -> R x z).
Proof using EL VL.
  intros H.
  pose proof (LR_sym _ _ _ _ _ _ _ H) as Hs.
  pose proof (proj2 (LR_trans n _ _ _ _ _ _ H _ _ Hs)) as C.
  assert (Sy : forall x y, R x y -> R y x).
  { intros x y Hxy.
    assert (Hyy : R y y).
    { exact (LR_tm_refl_l _ _ _ _ _ _ _ y x Hs Hxy). }
    exact (C y y x Hyy Hxy). }
  split; [exact Sy|]. intros x y z Hxy Hyz. exact (C x y z Hxy (Sy _ _ Hyz)).
Qed.

End Transitivity.
