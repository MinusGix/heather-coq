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

(** ** The shared type-level data of a binder former, flipped *)

Lemma poly_flip {F G Γ T T' l l1 l2 l3 l4 A B A' B'} :
  PolyFacts G Γ F T T' l l1 l2 l3 l4 A B A' B' -> PolyFacts G Γ F T' T l l3 l4 l1 l2 A' B' A B.
Proof.
  intros [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
  assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
  assert (HA3 : [ G ; Γ ⊢g A @ l3 ]) by (eapply lconv_ty; [exact HA | now apply lequiv_sym]).
  assert (HA'3 : [ G ; Γ ⊢g A' @ l3 ]) by (eapply lconv_ty; [exact HA' | now apply lequiv_sym]).
  split.
  - eapply lequiv_trans; [exact Hl | apply lequiv_sym, Hm].
  - now apply lequiv_sym.
  - now apply lequiv_sym.
  - eauto using lequiv_wf_l.
  - eauto using lequiv_wf_l.
  - exact HT'.
  - exact HT.
  - exact HA'3.
  - exact HA3.
  - eapply (lconv_ty (l := l2)); [|now apply lequiv_sym]. eapply ctx_lvl_ty; [exact HA' | now apply lequiv_sym | exact HB'].
  - eapply (lconv_ty (l := l2)); [|now apply lequiv_sym]. eapply ctx_lvl_ty; [exact HA | now apply lequiv_sym | exact HB].
  - eapply geq_ty_lconv; [apply geq_ty_sym, HAA | exact Hl3].
  - eapply geq_ty_lconv; [|exact Hl4].
    eapply geq_ty_ctxconv; [apply geq_ty_sound, HAA | now apply lequiv_sym | | apply geq_ty_sym, HBB].
    apply ext_wf_g; [exact HA'3 | eauto using lequiv_wf_l].
Qed.

(** ** The identity type, flipped (M11a): the carrier's relation is a PER *)

Lemma IdRel_flip {G Γ l1 l2 A A' a a' b b' RA t t'} :
  lequiv (gL G) l2 l1 ->
  [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢ a ≈ a' : A @ l1 ] -> [ G ; Γ ⊢ b ≈ b' : A @ l1 ] ->
  [ G ; Γ ⊢g A @ l1 ] -> RA a a' -> RA b b' ->
  (forall x y, RA x y -> RA y x) -> (forall x y z, RA x y -> RA y z -> RA x z) ->
  IdRel G Γ l1 A a b RA t' t -> IdRel G Γ l2 A' a' b' (flipR RA) t t'.
Proof.
  intros Hl2 HAA Haa Hbb HA Hra Hrb Hs Ht (w' & w & Hw' & Hw & Heq & Hn).
  assert (HV : [ G ; Γ ⊢g tyId l1 A a b ≅ tyId l2 A' a' b' @ l1 ])
    by (apply geq_ty_sound, geq_ty_id; auto using lequiv_sym).
  assert (F : forall u v, [ G ; Γ ⊢g u ⤳* v : tyId l1 A a b @ l1 ] ->
                [ G ; Γ ⊢g u ⤳* v : tyId l2 A' a' b' @ l2 ]).
  { intros u v H. eapply tmred_lconv; [| exact Hl2].
    eapply tmred_conv; [apply ge_typeof | exact H | exact HV]. }
  exists w, w'. refine (conj (F _ _ Hw) (conj (F _ _ Hw') (conj _ _))).
  - eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact HV] | exact Hl2].
  - assert (CA : forall C, [ G ; Γ ⊢ A ≈ C @ l1 ] -> [ G ; Γ ⊢ A' ≈ C @ l2 ]).
    { intros C HC. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HC] | exact Hl2]. }
    assert (CR : forall e e' x, RA e e' -> RA e x -> flipR RA e' x).
    { intros e e' x He Hx. unfold flipR. eapply Ht; [apply Hs, Hx | exact He]. }
    destruct Hn as [k1 k2 C1 C2 c1 c2 Hk1 Hk2 HC1 HC2 H1 H2 H3 H4 | ν' ν Hν].
    + apply idnf_refl; eauto using lequiv_trans, lequiv_sym.
    + apply idnf_ne. eapply gne_tm_lconv; [eapply gne_tm_conv; [apply gne_tm_sym, Hν | exact HV] | exact Hl2].
Qed.

(** ** Binary sums, flipped (M12b): each injection's payload flips *)

Lemma SumRel_flip {G Γ l1 l2 l3 l4 A A' B B' RA RB t t'} :
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
  [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢ B ≈ B' @ l2 ] ->
  SumRel G Γ l1 l2 A B RA RB t' t -> SumRel G Γ l3 l4 A' B' (flipR RA) (flipR RB) t t'.
Proof.
  intros Hl3 Hl4 HAA HBB (w' & w & Hw' & Hw & Heq & Hn).
  assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
  assert (HV : [ G ; Γ ⊢g tySum l1 l2 A B ≅ tySum l3 l4 A' B' @ lmax l1 l2 ])
    by (apply geq_ty_sound, geq_ty_sum; auto using lequiv_sym).
  assert (F : forall u v, [ G ; Γ ⊢g u ⤳* v : tySum l1 l2 A B @ lmax l1 l2 ] ->
                [ G ; Γ ⊢g u ⤳* v : tySum l3 l4 A' B' @ lmax l3 l4 ]).
  { intros u v H. eapply tmred_lconv; [| exact Hm].
    eapply tmred_conv; [apply ge_typeof | exact H | exact HV]. }
  exists w, w'. refine (conj (F _ _ Hw) (conj (F _ _ Hw') (conj _ _))).
  - eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact HV] | exact Hm].
  - assert (CA : forall C, [ G ; Γ ⊢ A ≈ C @ l1 ] -> [ G ; Γ ⊢ A' ≈ C @ l3 ]).
    { intros C HC. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HC] | exact Hl3]. }
    assert (CB : forall D, [ G ; Γ ⊢ B ≈ D @ l2 ] -> [ G ; Γ ⊢ B' ≈ D @ l4 ]).
    { intros D HD. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, HBB | exact HD] | exact Hl4]. }
    destruct Hn as [k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha
                   | k1 k2 k1' k2' C D C' D' b b' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Hb | ν' ν Hν].
    + apply sumnf_inl; [..| exact Ha]; eauto using lequiv_trans, lequiv_sym.
    + apply sumnf_inr; [..| exact Hb]; eauto using lequiv_trans, lequiv_sym.
    + apply sumnf_ne. eapply gne_tm_lconv; [eapply gne_tm_conv; [apply gne_tm_sym, Hν | exact HV] | exact Hm].
Qed.

(** ** Well-founded trees, flipped (M13a)

    By induction on the relation: at a [sup], the children's relation at
    each weakening flips by the hypothesis, with the data weakened; the
    annotations move along the components' equalities, and the positions'
    ones along the codomain's escape, [HC]. *)
Lemma WRel_flip :
  forall G Γ l1 l2 A B (d : DomRel G Γ) (c : CodRel G Γ d) u v, WRel G Γ l1 l2 A B d c u v ->
  forall l3 l4 A' B', lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢g A' @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    (forall (ρ : kwk G Γ) x y (h : d ρ x y),
        [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle x] ≈ (ktyl ρ B')[lsingle y] @ l2 ]) ->
    WRel G Γ l3 l4 A' B' (flipD d) (flipC c) v u.
Proof.
  apply (WRel_mut
    (fun G Γ l1 l2 A B d c u v _ => forall l3 l4 A' B', lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
       [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢g A' @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
       [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
       (forall (ρ : kwk G Γ) x y (h : d ρ x y),
           [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle x] ≈ (ktyl ρ B')[lsingle y] @ l2 ]) ->
       WRel G Γ l3 l4 A' B' (flipD d) (flipC c) v u)
    (fun G Γ l1 l2 A B d c u v _ => forall l3 l4 A' B', lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
       [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢g A' @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
       [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
       (forall (ρ : kwk G Γ) x y (h : d ρ x y),
           [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle x] ≈ (ktyl ρ B')[lsingle y] @ l2 ]) ->
       WNf G Γ l3 l4 A' B' (flipD d) (flipC c) v u)).
  - intros * Hw Hw' Heq _ IH l3 l4 A' B' Hl3 Hl4 HA HA' HAA HBB HC.
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HV : [ G ; Γ ⊢g tyW l1 l2 A B ≅ tyW l3 l4 A' B' @ lmax l1 l2 ])
      by (apply geq_ty_sound, geq_ty_W; auto using lequiv_sym).
    econstructor.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw' | exact HV] | exact Hm].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw | exact HV] | exact Hm].
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact HV] | exact Hm].
    + exact (IH l3 l4 A' B' Hl3 Hl4 HA HA' HAA HBB HC).
  - intros * Hk1 Hk2 Hk1' Hk2' HC0 HC0' HD HD' Ha Hwf Hf IH l3 l4 A' B' Hl3 Hl4 HA HA' HAA HBB HC.
    pose proof (lequiv_wf_l _ _ _ Hl3) as W3. pose proof (lequiv_wf_l _ _ _ Hl4) as W4.
    pose proof (lequiv_wf_r _ _ _ Hl3) as W1. pose proof (lequiv_wf_r _ _ _ Hl4) as W2.
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HA'3 : [ G ; Γ ⊢g A' @ l3 ]) by (eapply lconv_ty; [exact HA' | now apply lequiv_sym]).
    assert (CA : forall X, [ G ; Γ ⊢ A ≈ X @ l1 ] -> [ G ; Γ ⊢ A' ≈ X @ l3 ]).
    { intros X HX. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HX] | exact Hl3]. }
    assert (CB : forall X, [ G ; Γ ,, A @ l1 ⊢ B ≈ X @ l2 ] -> [ G ; Γ ,, A' @ l3 ⊢ B' ≈ X @ l4 ]).
    { intros X HX. eapply geq_ty_lconv; [|exact Hl4].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, HAA | now apply lequiv_sym | apply ext_wf_g; [exact HA'3 | exact W3] |].
      eapply geq_ty_trans; [apply geq_ty_sym, HBB | exact HX]. }
    apply wnf_sup; eauto using lequiv_trans, lequiv_sym.
    { (* the children's functions, flipped along their type's equality *)
      intros ρ. apply WhRel_sym.
      pose proof (W_fty_eq (kw_lequiv ρ (lequiv_sym _ _ _ Hl3)) (kw_lequiv ρ (lequiv_sym _ _ _ Hl4)) (kw_ty ρ HA)
                    (kw_geq_ty ρ HAA) (kw_geq_ty_l ρ HA W1 HBB) (HC ρ _ _ (Ha ρ))) as EP.
      eapply WhRel_conv; [exact (Hwf ρ) | exact (geq_ty_sound EP) |].
      apply lequiv_max; [|apply lequiv_max]; apply (kw_lequiv ρ); assumption. }
    intros ρ ha b' b Hbb la' lb' A1' B1' la lb A1 B1 H1 H2 H3 H4 HA1' HB1' HA1 HB1.
    unfold flipD, flipC, flipR in ha, Hbb.
    pose proof (kw_lwf ρ W1) as V1. pose proof (kw_lwf ρ W2) as V2.
    pose proof (kw_lequiv ρ Hl3) as Q3. pose proof (kw_lequiv ρ Hl4) as Q4.
    assert (Qm : lequiv (gL (kw_G ρ)) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    pose proof (HC ρ _ _ ha) as EC.
    pose proof (geq_ty_sound EC) as EC'.
    pose proof (eqty_wf_l ge_typeof EC') as HBa. pose proof (eqty_wf_r ge_typeof EC') as HB'a.
    assert (EW : [ kw_G ρ ; kw_Δ ρ ⊢ tyW l1 l2 (kty ρ A) (ktyl ρ B) ≈ tyW l3 l4 (kty ρ A') (ktyl ρ B') @ lmax l1 l2 ]).
    { pose proof (kw_geq_ty ρ (geq_ty_W (lequiv_sym _ _ _ Hl3) (lequiv_sym _ _ _ Hl4) HA HAA HBB)) as X.
      now rewrite !kty_tyW in X. }
    (* the annotations, moved to the left positions *)
    assert (MA : forall X, [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B')[lsingle (ktm ρ a')] ≈ X @ l4 ] ->
                   [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle (ktm ρ a)] ≈ X @ l2 ]).
    { intros X HX. eapply geq_ty_trans; [exact EC | eapply geq_ty_lconv; [exact HX | now apply lequiv_sym]]. }
    assert (MB : forall X, [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B')[lsingle (ktm ρ a')] @ l4
                             ⊢ (tyW l3 l4 (kty ρ A') (ktyl ρ B'))⟨↑⟩ ≈ X @ lmax l3 l4 ] ->
                   [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B)[lsingle (ktm ρ a)] @ l2
                             ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ X @ lmax l1 l2 ]).
    { intros X HX.
      assert (HΔ' : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B')[lsingle (ktm ρ a')] @ l4 ⊢g ])
        by (apply ext_wf_g; [eapply lconv_ty; [exact HB'a | now apply lequiv_sym] | exact (kw_lwf ρ W4)]).
      assert (Y : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B')[lsingle (ktm ρ a')] @ l4
                    ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ X @ lmax l1 l2 ]).
      { eapply geq_ty_trans; [exact (geq_ty_wk (wkr_shift1 _ _ _) HΔ' EW)
                             | eapply geq_ty_lconv; [exact HX | now apply lequiv_sym]]. }
      eapply geq_ty_ctxconv; [| exact Q4 | apply ext_wf_g; [exact HBa | exact V2] | exact Y].
      eapply eqty_lconv; [apply eqty_sym, EC' | exact Q4]. }
    exact (IH ρ ha b b' Hbb la lb A1 B1 la' lb' A1' B1'
             (lequiv_trans _ _ _ _ H3 Hl4) (lequiv_trans _ _ _ _ H4 Hm)
             (lequiv_trans _ _ _ _ H1 Hl4) (lequiv_trans _ _ _ _ H2 Hm)
             (MA _ HA1) (MB _ HB1) (MA _ HA1') (MB _ HB1')
             l3 l4 (kty ρ A') (ktyl ρ B') Q3 Q4 (kw_ty ρ HA) (kw_ty ρ HA') (kw_geq_ty ρ HAA)
             (kw_geq_ty_l ρ HA (lequiv_wf_r _ _ _ Hl3) HBB)
             (fun ρ' x y h => ltac:(rewrite <- !ktyl_comp; exact (HC (kw_comp ρ ρ') x y h)))).
  - intros * Hν l3 l4 A' B' Hl3 Hl4 HA HA' HAA HBB HC.
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HV : [ G ; Γ ⊢g tyW l1 l2 A B ≅ tyW l3 l4 A' B' @ lmax l1 l2 ])
      by (apply geq_ty_sound, geq_ty_W; auto using lequiv_sym).
    apply wnf_ne. eapply gne_tm_lconv; [eapply gne_tm_conv; [apply gne_tm_sym, Hν | exact HV] | exact Hm].
Qed.

(** ** Symmetry *)

Lemma LR_sym_step n : (forall m, m < n -> Psym m) -> Psym n.
Proof.
  intros IHn G Γ T T' l R H.
  induction H as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd IHdom codAd IHcod HR].
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
  - pose proof (poly_flip P) as P'.
    destruct P as [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
    eapply (LRpi n (LRbelow n) G Γ T' T l l3 l4 l1 l2 A' B' A B (flipD domR) (flipC codR)).
    + exact P'.
    + intros ρ. eapply LR_lconv; [exact (IHdom ρ) | exact (kw_lequiv ρ Hl3)].
    + intros ρ a a' ha. eapply LR_lconv; [exact (IHcod ρ a' a ha) | exact (kw_lequiv ρ Hl4)].
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split.
      * apply PiRel_flip; auto.
      * intros H. open_poly. apply (PiRel_flip (A := A') (A' := A) (domR := flipD domR) (codR := flipC codR));
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
  - pose proof (poly_flip P) as P'.
    destruct P as [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
    eapply (LRsig n (LRbelow n) G Γ T' T l l3 l4 l1 l2 A' B' A B (flipD domR) (flipC codR)).
    + exact P'.
    + intros ρ. eapply LR_lconv; [exact (IHdom ρ) | exact (kw_lequiv ρ Hl3)].
    + intros ρ a a' ha. eapply LR_lconv; [exact (IHcod ρ a' a ha) | exact (kw_lequiv ρ Hl4)].
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split.
      * apply SigRel_flip; auto.
      * intros H. open_poly. apply (SigRel_flip (A := A') (A' := A) (domR := flipD domR) (codR := flipC codR));
          auto using lequiv_sym.
  - eapply (LRunit n (LRbelow n) G Γ T' T l l2 l1).
    + exact (lequiv_trans _ _ _ _ Hl (lequiv_sym _ _ _ Hl2)).
    + exact (lequiv_sym _ _ _ Hl2).
    + exact (lequiv_wf_l _ _ _ Hl2).
    + exact HT'.
    + exact HT.
    + intros t t'; unfold flipR; rewrite (HR t' t), (UnitRel_lconv (lequiv_sym _ _ _ Hl2) t' t).
      split; apply UnitRel_sym.
  - (* sEq *)
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'.
    pose proof (geq_ty_sound HSAA) as EA.
    assert (HV : [ G ; Γ ⊢g tySEq s1 SA sa sb ≅ tySEq s2 SA' sa' sb' @ s1 ])
      by (apply geq_ty_sound, geq_ty_seq; assumption).
    eapply (LRseq n (LRbelow n) G Γ T' T l s2 s1 SA' SA sa' sa sb' sb).
    + exact (lequiv_trans _ _ _ _ Hl Hl2').
    + exact Hl2'.
    + exact (lequiv_wf_l _ _ _ Hl2).
    + exact HT'.
    + exact HT.
    + exact (lconv_ty (eqty_wf_r ge_typeof EA) Hl2').
    + eapply geq_ty_lconv; [apply geq_ty_sym, HSAA | exact Hl2].
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Hsaa | exact EA] | exact Hl2].
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Hsbb | exact EA] | exact Hl2].
    + intros t t'; unfold flipR; rewrite (HR t' t), <- (SEqRel_conv HV Hl2' t t').
      split; apply SEqRel_sym.
  - (* sEmpty *)
    eapply (LRsempty n (LRbelow n) G Γ T' T l s2 s1).
    + exact (lequiv_trans _ _ _ _ Hl (lequiv_sym _ _ _ Hl2)).
    + exact (lequiv_sym _ _ _ Hl2).
    + exact (lequiv_wf_l _ _ _ Hl2).
    + exact HT'.
    + exact HT.
    + intros t t'; unfold flipR; rewrite (HR t' t), (SEmptyRel_lconv (lequiv_sym _ _ _ Hl2) t' t).
      split; apply SEmptyRel_sym.
  - (* Id *)
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'.
    pose proof (geq_ty_sound HIAA) as EA.
    assert (HIA' : [ G ; Γ ⊢g IA' @ s1 ]) by exact (eqty_wf_r ge_typeof EA).
    assert (HAA' : [ G ; Γ ⊢ IA' ≈ IA @ s2 ]) by (eapply geq_ty_lconv; [apply geq_ty_sym, HIAA | exact Hl2]).
    assert (Haa' : [ G ; Γ ⊢ ia' ≈ ia : IA' @ s2 ])
      by (eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Hiaa | exact EA] | exact Hl2]).
    assert (Hbb' : [ G ; Γ ⊢ ib' ≈ ib : IA' @ s2 ])
      by (eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Hibb | exact EA] | exact Hl2]).
    assert (Hs' : forall x y, flipR RA x y -> flipR RA y x) by (unfold flipR; intros x y H; exact (Hps _ _ H)).
    assert (Ht' : forall x y z, flipR RA x y -> flipR RA y z -> flipR RA x z)
      by (unfold flipR; intros x y z H1 H2; exact (Hpt _ _ _ H2 H1)).
    eapply (LRid n (LRbelow n) G Γ T' T l s2 s1 IA' IA ia' ia ib' ib (flipR RA)).
    + exact (lequiv_trans _ _ _ _ Hl Hl2').
    + exact Hl2'.
    + exact (lequiv_wf_l _ _ _ Hl2).
    + exact HT'.
    + exact HT.
    + exact (lconv_ty HIA' Hl2').
    + exact HAA'.
    + exact Haa'.
    + exact Hbb'.
    + exact (LR_lconv _ _ _ _ _ _ _ _ _ IHRA Hl2).
    + exact Hra.
    + exact Hrb.
    + exact Hs'.
    + exact Ht'.
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split; intros X.
      * exact (IdRel_flip Hl2 HIAA Hiaa Hibb HIA Hra Hrb Hps Hpt X).
      * exact (IdRel_flip (RA := flipR RA) Hl2' HAA' Haa' Hbb' (lconv_ty HIA' Hl2') Hra Hrb Hs' Ht' X).
  - (* Empty *)
    eapply (LRempty n (LRbelow n) G Γ T' T l s2 s1).
    + exact (lequiv_trans _ _ _ _ Hl (lequiv_sym _ _ _ Hl2)).
    + exact (lequiv_sym _ _ _ Hl2).
    + exact (lequiv_wf_l _ _ _ Hl2).
    + exact HT'.
    + exact HT.
    + intros t t'; unfold flipR; rewrite (HR t' t), (EmptyRel_lconv (lequiv_sym _ _ _ Hl2) t' t).
      split; apply EmptyRel_sym.
  - (* + *)
    pose proof (lequiv_sym _ _ _ Hl3) as Hl3'. pose proof (lequiv_sym _ _ _ Hl4) as Hl4'.
    pose proof (geq_ty_lconv (geq_ty_sym HUAA) Hl3) as HAA'.
    pose proof (geq_ty_lconv (geq_ty_sym HUBB) Hl4) as HBB'.
    eapply (LRsum n (LRbelow n) G Γ T' T l u3 u4 u1 u2 UA' UA UB' UB (flipR RA) (flipR RB)).
    + exact (lequiv_trans _ _ _ _ Hl (lequiv_sym _ _ _ (lequiv_max _ _ _ _ _ Hl3 Hl4))).
    + exact Hl3'.
    + exact Hl4'.
    + exact (lequiv_wf_l _ _ _ Hl3).
    + exact (lequiv_wf_l _ _ _ Hl4).
    + exact HT'.
    + exact HT.
    + exact (lconv_ty (eqty_wf_r ge_typeof (geq_ty_sound HUAA)) Hl3').
    + exact HAA'.
    + exact (lconv_ty (eqty_wf_r ge_typeof (geq_ty_sound HUBB)) Hl4').
    + exact HBB'.
    + exact (LR_lconv _ _ _ _ _ _ _ _ _ IHRA Hl3).
    + exact (LR_lconv _ _ _ _ _ _ _ _ _ IHRB Hl4).
    + unfold flipR; intros x y H; exact (Hpa _ _ H).
    + unfold flipR; intros x y z H1 H2; exact (Hta _ _ _ H2 H1).
    + unfold flipR; intros x y H; exact (Hpb _ _ H).
    + unfold flipR; intros x y z H1 H2; exact (Htb _ _ _ H2 H1).
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split; intros X.
      * exact (SumRel_flip Hl3 Hl4 HUAA HUBB X).
      * exact (SumRel_flip (RA := flipR RA) (RB := flipR RB) Hl3' Hl4' HAA' HBB' X).
  - (* W *)
    pose proof (poly_flip P) as P'.
    destruct P as [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
    assert (HC : forall (ρ : kwk G Γ) x y (h : domR ρ x y),
               [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle x] ≈ (ktyl ρ B')[lsingle y] @ l2 ])
      by (intros; exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (codAd ρ x y h))))).
    eapply (LRw n (LRbelow n) G Γ T' T l l3 l4 l1 l2 A' B' A B (flipD domR) (flipC codR)).
    + exact P'.
    + intros ρ. eapply LR_lconv; [exact (IHdom ρ) | exact (kw_lequiv ρ Hl3)].
    + intros ρ a a' ha. eapply LR_lconv; [exact (IHcod ρ a' a ha) | exact (kw_lequiv ρ Hl4)].
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split; intros X.
      * exact (WRel_flip _ _ _ _ _ _ _ _ _ _ X l3 l4 A' B' Hl3 Hl4 HA HA' HAA HBB HC).
      * destruct P' as [_ Hl3' Hl4' _ _ _ _ HA'3 HA3 _ _ HAA' HBB'].
        exact (WRel_flip _ _ _ _ _ _ _ _ _ _ X l1 l2 A B Hl3' Hl4' HA'3 HA3 HAA' HBB'
                 (fun ρ x y h => geq_ty_lconv (geq_ty_sym (HC ρ y x h)) (kw_lequiv ρ Hl4))).
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
