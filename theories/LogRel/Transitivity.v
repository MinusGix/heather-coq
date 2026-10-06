(** * Transitivity (ch. 7, Reflexivity and Transitivity)

    [LR T1 T2 R12] and [LR T2 T3 R23] give [LR T1 T3 R12] (saturation lets
    the composite keep the left relation), and [R12 ∘ R23 ⊆ R12].  By strong
    induction on the stage and induction on the first derivation.  The Π
    case follows the paper: the codomain is composed through [B2[a/x]],
    which needs [a] related to itself (the induction hypothesis on the
    domain composed with its own symmetric) and left irrelevance. *)
From DeLaM.LogRel Require Export Symmetry.

Section Transitivity.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

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

(** ** The shared type-level data of a binder former, composed *)

Lemma poly_trans {F G Γ T1 T2 T3 l l1 l2 l3 l4 k3 k4 A1 B1 A2 B2 A3 B3} :
  PolyFacts G Γ F T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 ->
  PolyFacts G Γ F T2 T3 l l3 l4 k3 k4 A2 B2 A3 B3 ->
  PolyFacts G Γ F T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3.
Proof.
  intros [Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HA1 HA2 HB1 HB2 HA12 HB12]
         [_ Hk3 Hk4 _ _ _ HT3 _ HA3 _ HB3 HA23 HB23].
  assert (Hl13 : lequiv (gL G) l1 l3) by now apply lequiv_sym.
  assert (Hl24 : lequiv (gL G) l2 l4) by now apply lequiv_sym.
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

(** ** The identity type, composed (M11a) *)

Lemma IdNf_whnf_l {G Γ l A a b RA w w'} : IdNf G Γ l A a b RA w w' -> whnf w.
Proof. intros [| ν ν' Hν]; [apply whnf_refl | apply whnf_ne; exact (gne_tm_whne_l Hν)]. Qed.
Lemma IdNf_whnf_r {G Γ l A a b RA w w'} : IdNf G Γ l A a b RA w w' -> whnf w'.
Proof. intros [| ν ν' Hν]; [apply whnf_refl | apply whnf_ne; exact (gne_tm_whne_r Hν)]. Qed.

(** The second step's carrier relation is the first one flipped (both have
    the middle carrier on the left), so its facts come back by the PER. *)
Lemma IdRel_trans {G Γ l1 l2 A1 A2 a1 a2 b1 b2 RA RA2 t1 t2 t3} :
  lequiv (gL G) l2 l1 ->
  [ G ; Γ ⊢ A1 ≈ A2 @ l1 ] -> [ G ; Γ ⊢ a1 ≈ a2 : A1 @ l1 ] -> [ G ; Γ ⊢ b1 ≈ b2 : A1 @ l1 ] ->
  [ G ; Γ ⊢g A1 @ l1 ] -> RA a1 a2 -> RA b1 b2 ->
  (forall x y, RA x y -> RA y x) -> (forall x y z, RA x y -> RA y z -> RA x z) ->
  releq (flipR RA) RA2 ->
  IdRel G Γ l1 A1 a1 b1 RA t1 t2 -> IdRel G Γ l2 A2 a2 b2 RA2 t2 t3 -> IdRel G Γ l1 A1 a1 b1 RA t1 t3.
Proof.
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
Proof. intros [| | ν ν' Hν]; [apply whnf_inl | apply whnf_inr | apply whnf_ne; exact (gne_tm_whne_l Hν)]. Qed.
Lemma SumNf_whnf_r {G Γ l l' A B RA RB w w'} : SumNf G Γ l l' A B RA RB w w' -> whnf w'.
Proof. intros [| | ν ν' Hν]; [apply whnf_inl | apply whnf_inr | apply whnf_ne; exact (gne_tm_whne_r Hν)]. Qed.

(** The payloads compose by the summands' own transitivity, given as the
    composites [RA ∘ RA2 ⊆ RA] and [RB ∘ RB2 ⊆ RB]. *)
Lemma SumRel_trans {G Γ l1 l2 l3 l4 A1 A2 B1 B2 RA RB RA2 RB2 t1 t2 t3} :
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
  [ G ; Γ ⊢ A1 ≈ A2 @ l1 ] -> [ G ; Γ ⊢ B1 ≈ B2 @ l2 ] ->
  (forall x y z, RA x y -> RA2 y z -> RA x z) -> (forall x y z, RB x y -> RB2 y z -> RB x z) ->
  SumRel G Γ l1 l2 A1 B1 RA RB t1 t2 -> SumRel G Γ l3 l4 A2 B2 RA2 RB2 t2 t3 ->
  SumRel G Γ l1 l2 A1 B1 RA RB t1 t3.
Proof.
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
Proof. destruct 1; [apply whnf_sup | apply whnf_ne; exact (gne_tm_whne_l H)]. Qed.
Lemma WNf_whnf_r {G Γ l1 l2 A B d c w w'} : WNf G Γ l1 l2 A B d c w w' -> whnf w'.
Proof. destruct 1; [apply whnf_sup | apply whnf_ne; exact (gne_tm_whne_r H)]. Qed.

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
Proof.
  intros H. remember (tmSup k1 k2 C D a f) as s eqn:Es. destruct H.
  - injection Es as -> -> -> -> -> ->. do 6 eexists; split; [reflexivity|]. eauto 20.
  - subst. exfalso. pose proof (gne_tm_whne_l H) as Hw. inversion Hw.
Qed.

(** [WhRel] composes, the middle whnfs being equal. *)
Lemma WhRel_trans {G Γ T l t1 t2 t3} : WhRel G Γ T l t1 t2 -> WhRel G Γ T l t2 t3 -> WhRel G Γ T l t1 t3.
Proof.
  intros (w1 & w2 & H1 & H2 & N1 & N2 & E12) (w2' & w3 & H2' & H3 & N2' & N3 & E23).
  assert (w2' = w2) as -> by (eapply tmred_whnf_det; [exact H2' | exact H2 | exact N2' | exact N2]).
  exists w1, w3. exact (conj H1 (conj H3 (conj N1 (conj N3 (geq_tm_trans E12 E23))))).
Qed.

Lemma WNf_ne_inv {G Γ l1 l2 A B} {d : DomRel G Γ} {c : CodRel G Γ d} {ν w} :
  whne ν -> WNf G Γ l1 l2 A B d c ν w -> [ G ; Γ ⊢ ν ~ w : tyW l1 l2 A B @ lmax l1 l2 ].
Proof. intros Hν H. destruct H; [inversion Hν | exact H]. Qed.

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
Proof.
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
        by (apply ext_wf_g; [eapply lconv_ty; [exact HB2a | now apply lequiv_sym] | exact (kw_lwf ρ W4)]).
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

(** ** Transitivity *)

Lemma LR_trans_step n : (forall m, m < n -> Ptrans m) -> Ptrans n.
Proof.
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
                 | G Γ T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 R P1 domAd1 IHdom codAd1 IHcod HR];
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
      by (eapply geq_ty_trans; [exact Hgeq | eapply geq_ty_lconv; [exact Hgeq2 | now apply lequiv_sym]]).
    assert (HR13 : releq R (CPiRel G Γ l1 m2 U1 U3 instR)).
    { assert (HP : [ G ; Γ ⊢g tyCPi l2 U2 ≅ tyCPi m2 U3 @ l1 ])
        by (eapply eqty_lconv; [apply geq_ty_sound, Hgeq2 | now apply lequiv_sym]).
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
      by (eapply geq_ty_trans; [exact Hgeq | eapply geq_ty_lconv; [exact Hgeq2 | now apply lequiv_sym]]).
    assert (HR13 : releq R (TPiRel G Γ Δ1 Δ3 l1 l2 m3 m4 U1 U3 instR)).
    { assert (HP : [ G ; Γ ⊢g tyTPi Δ2 l3 l4 U2 ≅ tyTPi Δ3 m3 m4 U3 @ l2 ])
        by (eapply eqty_lconv; [apply geq_ty_sound, Hgeq2 | now apply lequiv_sym]).
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
    assert (Hl13 : lequiv (gL G) l1 l3) by now apply lequiv_sym.
    assert (Hl24 : lequiv (gL G) l2 l4) by now apply lequiv_sym.
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

(** The term relation is a PER (M11a: the carriers of [Id] need it). *)
Corollary LR_tm_per n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R ->
  (forall x y, R x y -> R y x) /\ (forall x y z, R x y -> R y z -> R x z).
Proof.
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
