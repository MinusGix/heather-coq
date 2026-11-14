(** * Symmetry (ch. 7)

    [LR T T' R] gives [LR T' T (flip R)].  By strong induction on the stage
    (the universe case uses symmetry one stage down) and induction on the
    derivation.  The symmetric Π derivation uses the flipped domain and
    codomain relations, which saturation makes available without choice. *)
From DeLaM.LogRel Require Export Irrelevance.
From DeLaM.LogRel Require Import IWfAux MAux IWiAux.

Definition flipR (R : tm -> tm -> Prop) : tm -> tm -> Prop := fun t t' => R t' t.

Section Symmetry.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Declarative and generic helpers *)

Lemma lconv_ty {G Γ T l l'} : [ G ; Γ ⊢g T @ l ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢g T @ l' ].
Proof using . intros; eapply wft_lconv; eauto using lequiv_sym. Qed.

(** Changing the level annotation of the last context entry. *)
Lemma ctx_lvl_ty {G Γ A la la' T l} :
  [ G ; Γ ⊢g A @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A @ la ⊢g T @ l ] -> [ G ; Γ ,, A @ la' ⊢g T @ l ].
Proof using .
  intros HA Hl HT. eapply (stab_ty ge_typeof (eqty_refl _ _ _ _ _ HA) Hl); [|exact HT].
  apply ext_wf_g; [now apply (lconv_ty HA) | eauto using lequiv_wf_r].
Qed.

Lemma ctx_lvl_tm {G Γ A la la' t T l} :
  [ G ; Γ ⊢g A @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A @ la ⊢g t : T @ l ] -> [ G ; Γ ,, A @ la' ⊢g t : T @ l ].
Proof using .
  intros HA Hl Ht. eapply (stab_tm ge_typeof (eqty_refl _ _ _ _ _ HA) Hl); [|exact Ht].
  apply ext_wf_g; [now apply (lconv_ty HA) | eauto using lequiv_wf_r].
Qed.

Lemma ctx_lvl_geq {G Γ A la la' T T' l} :
  [ G ; Γ ⊢g A @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A @ la ⊢ T ≈ T' @ l ] -> [ G ; Γ ,, A @ la' ⊢ T ≈ T' @ l ].
Proof using EL.
  intros HA Hl HT. eapply geq_ty_ctxconv; [apply eqty_refl, HA | exact Hl | | exact HT].
  apply ext_wf_g; [now apply (lconv_ty HA) | eauto using lequiv_wf_r].
Qed.

Lemma tmred_U_conv {G Γ t w l1 l2} :
  [ G ; Γ ⊢g t ⤳* w : tyU l1 @ lsuc l1 ] -> lequiv (gL G) l1 l2 ->
  [ G ; Γ ⊢g t ⤳* w : tyU l2 @ lsuc l2 ].
Proof using .
  intros Ht Hl. eapply tmred_lconv; [|apply lequiv_suc, lequiv_sym, Hl].
  eapply tmred_conv; [apply ge_typeof | exact Ht |].
  apply eqty_U; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, Ht | exact Hl].
Qed.

Lemma geq_U_conv {G Γ w w' l1 l2} :
  [ G ; Γ ⊢g ] -> [ G ; Γ ⊢ w ≈ w' : tyU l1 @ lsuc l1 ] -> lequiv (gL G) l1 l2 ->
  [ G ; Γ ⊢ w ≈ w' : tyU l2 @ lsuc l2 ].
Proof using EL.
  intros HΓ Hw Hl. eapply geq_tm_lconv; [|apply lequiv_suc, lequiv_sym, Hl].
  eapply geq_tm_conv; [exact Hw |].
  apply eqty_U; [exact ge_notV | now rewrite ge_typeof | exact Hl].
Qed.

(** ** Natural numbers and neutrals *)

Lemma NatRel_sym G Γ : forall t t', NatRel G Γ t t' -> NatRel G Γ t' t.
Proof using EL.
  apply (NatRel_mut G Γ (fun t t' _ => NatRel G Γ t' t) (fun t t' _ => NatNf G Γ t' t)).
  - intros t t' w w' Hw Hw' Heq _ IH. econstructor; eauto using geq_tm_sym.
  - constructor.
  - intros; now constructor.
  - intros; constructor; now apply gne_tm_sym.
Qed.

Lemma NatRel_flip G Γ : releq (flipR (NatRel G Γ)) (NatRel G Γ).
Proof using EL. intros t t'; split; apply NatRel_sym. Qed.

Lemma NeRel_flip G Γ V V' l : releq (flipR (NeRel G Γ V V' l)) (NeRel G Γ V' V l).
Proof using EL.
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
Proof using EL H13 H24 HA HA'.
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
Proof using EL H13 H24 HA HA'.
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
Proof using EL.
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
Proof using EL.
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
Proof using EL.
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
    eapply LR_lconv; [exact (Hsym _ _ _ _ _ _ H0) | solve [apply lequiv_sym; assumption]].
Qed.

(** ** The shared type-level data of a binder former, flipped *)

Lemma poly_flip {F G Γ T T' l l1 l2 l3 l4 A B A' B'} :
  PolyFacts G Γ F T T' l l1 l2 l3 l4 A B A' B' -> PolyFacts G Γ F T' T l l3 l4 l1 l2 A' B' A B.
Proof using EL.
  intros [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
  assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
  assert (HA3 : [ G ; Γ ⊢g A @ l3 ]) by (eapply lconv_ty; [exact HA | solve [apply lequiv_sym; assumption]]).
  assert (HA'3 : [ G ; Γ ⊢g A' @ l3 ]) by (eapply lconv_ty; [exact HA' | solve [apply lequiv_sym; assumption]]).
  split.
  - eapply lequiv_trans; [exact Hl | apply lequiv_sym, Hm].
  - solve [apply lequiv_sym; assumption].
  - solve [apply lequiv_sym; assumption].
  - eauto using lequiv_wf_l.
  - eauto using lequiv_wf_l.
  - exact HT'.
  - exact HT.
  - exact HA'3.
  - exact HA3.
  - eapply (lconv_ty (l := l2)); [|solve [apply lequiv_sym; assumption]]. eapply ctx_lvl_ty; [exact HA' | solve [apply lequiv_sym; assumption] | exact HB'].
  - eapply (lconv_ty (l := l2)); [|solve [apply lequiv_sym; assumption]]. eapply ctx_lvl_ty; [exact HA | solve [apply lequiv_sym; assumption] | exact HB].
  - eapply geq_ty_lconv; [apply geq_ty_sym, HAA | exact Hl3].
  - eapply geq_ty_lconv; [|exact Hl4].
    eapply geq_ty_ctxconv; [apply geq_ty_sound, HAA | solve [apply lequiv_sym; assumption] | | apply geq_ty_sym, HBB].
    apply ext_wf_g; [exact HA'3 | eauto using lequiv_wf_l].
Qed.

(** ** The identity type, flipped (M11a): the carrier's relation is a PER *)

Lemma IdRel_flip {G Γ l1 l2 A A' a a' b b' RA t t'} :
  lequiv (gL G) l2 l1 ->
  [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢ a ≈ a' : A @ l1 ] -> [ G ; Γ ⊢ b ≈ b' : A @ l1 ] ->
  [ G ; Γ ⊢g A @ l1 ] -> RA a a' -> RA b b' ->
  (forall x y, RA x y -> RA y x) -> (forall x y z, RA x y -> RA y z -> RA x z) ->
  IdRel G Γ l1 A a b RA t' t -> IdRel G Γ l2 A' a' b' (flipR RA) t t'.
Proof using EL.
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
Proof using EL.
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
Proof using EL.
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
    assert (HA'3 : [ G ; Γ ⊢g A' @ l3 ]) by (eapply lconv_ty; [exact HA' | solve [apply lequiv_sym; assumption]]).
    assert (CA : forall X, [ G ; Γ ⊢ A ≈ X @ l1 ] -> [ G ; Γ ⊢ A' ≈ X @ l3 ]).
    { intros X HX. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HX] | exact Hl3]. }
    assert (CB : forall X, [ G ; Γ ,, A @ l1 ⊢ B ≈ X @ l2 ] -> [ G ; Γ ,, A' @ l3 ⊢ B' ≈ X @ l4 ]).
    { intros X HX. eapply geq_ty_lconv; [|exact Hl4].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, HAA | solve [apply lequiv_sym; assumption] | apply ext_wf_g; [exact HA'3 | exact W3] |].
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
    { intros X HX. eapply geq_ty_trans; [exact EC | eapply geq_ty_lconv; [exact HX | solve [apply lequiv_sym; assumption]]]. }
    assert (MB : forall X, [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B')[lsingle (ktm ρ a')] @ l4
                             ⊢ (tyW l3 l4 (kty ρ A') (ktyl ρ B'))⟨↑⟩ ≈ X @ lmax l3 l4 ] ->
                   [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B)[lsingle (ktm ρ a)] @ l2
                             ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ X @ lmax l1 l2 ]).
    { intros X HX.
      assert (HΔ' : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B')[lsingle (ktm ρ a')] @ l4 ⊢g ])
        by (apply ext_wf_g; [eapply lconv_ty; [exact HB'a | solve [apply lequiv_sym; assumption]] | exact (kw_lwf ρ W4)]).
      assert (Y : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B')[lsingle (ktm ρ a')] @ l4
                    ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ X @ lmax l1 l2 ]).
      { eapply geq_ty_trans; [exact (geq_ty_wk (wkr_shift1 _ _ _) HΔ' EW)
                             | eapply geq_ty_lconv; [exact HX | solve [apply lequiv_sym; assumption]]]. }
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

(** ** Finitary trees, flipped (M15a)

    By induction on the relation, the child spine flipped together with
    the trees: a spine is flipped along a right length [NatRel]-related to
    its own, which is how the right arity relates to the left one ([HC]).
    The flipped spine is at the right length, so its reductions and
    annotations move along [Vec] at related lengths ([geq_vec_nat]). *)
Section WfFlip.

Definition WfFlipHyps G Γ l A N (d : DomRel G Γ) l' A' N' :=
  lequiv (gL G) l' l /\ [ G ; Γ ⊢g A @ l ] /\ [ G ; Γ ⊢ A ≈ A' @ l ] /\
  [ G ; Γ ,, A @ l ⊢ N ≈ N' : tyNat @ lzero ] /\
  (forall (ρ : kwk G Γ) x y, d ρ x y ->
     NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle x] (ktml ρ N')[lsingle y]).

Lemma WfFlipHyps_kw {G Γ l A N d l' A' N'} (ρ : kwk G Γ) :
  WfFlipHyps G Γ l A N d l' A' N' ->
  WfFlipHyps (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => d (kw_comp ρ ρ')) l' (kty ρ A') (ktml ρ N').
Proof using EL.
  intros (Hl & HA & HAA & HNN & HC). pose proof (lequiv_wf_r _ _ _ Hl) as W.
  refine (conj (kw_lequiv ρ Hl) (conj (kw_ty ρ HA) (conj (kw_geq_ty ρ HAA) (conj (kw_geq_nat_l ρ HA W HNN) _)))).
  intros ρ' x y h. rewrite <- !ktml_comp. exact (HC (kw_comp ρ ρ') x y h).
Qed.

(** The data the cases share. *)
Lemma WfFlip_data {G Γ l A N d l' A' N'} : WfFlipHyps G Γ l A N d l' A' N' ->
  lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢g tyWf l A N @ l ] /\ [ G ; Γ ⊢g tyWf l' A' N' @ l' ] /\
  [ G ; Γ ⊢ tyWf l A N ≈ tyWf l' A' N' @ l ] /\ [ G ; Γ ⊢g tyWf l A N ≅ tyWf l' A' N' @ l ].
Proof using EL.
  intros (Hl & HA & HAA & HNN & _).
  pose proof (geq_ty_wf (lequiv_sym _ _ _ Hl) HA HAA HNN) as EWg.
  pose proof (geq_ty_sound EWg) as EW.
  refine (conj (lequiv_wf_r _ _ _ Hl) (conj (lequiv_wf_l _ _ _ Hl) (conj (eqty_wf_l ge_typeof EW) (conj _ (conj EWg EW))))).
  exact (lconv_ty (eqty_wf_r ge_typeof EW) (lequiv_sym _ _ _ Hl)).
Qed.

Lemma WfRel_flip_all :
  (forall G Γ l A N d t t', WfRel G Γ l A N d t t' ->
     forall l' A' N', WfFlipHyps G Γ l A N d l' A' N' -> WfRel G Γ l' A' N' (flipD d) t' t) /\
  (forall G Γ l A N d t t', WfNf G Γ l A N d t t' ->
     forall l' A' N', WfFlipHyps G Γ l A N d l' A' N' -> WfNf G Γ l' A' N' (flipD d) t' t) /\
  (forall G Γ l A N d k cs cs', VecSp G Γ l A N d k cs cs' ->
     forall l' A' N', WfFlipHyps G Γ l A N d l' A' N' ->
     forall k', NatRel G Γ k k' -> VecSp G Γ l' A' N' (flipD d) k' cs' cs).
Proof using EL.
  apply WfRel_comb.
  - intros G Γ l A N d t t' w w' Hw Hw' Heq _ IH l' A' N' Hy.
    destruct (WfFlip_data Hy) as (W & W' & HWf & HWf' & EWg & EW).
    pose proof (proj1 Hy) as Hl.
    econstructor.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw' | exact EW] | exact Hl].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw | exact EW] | exact Hl].
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact EW] | exact Hl].
    + exact (IH l' A' N' Hy).
  - intros G Γ l A N d k k' C C' M M' a a' cs cs' Hk Hk' HAC HAC' HNM HNM' Ha Hcs IH l' A' N' Hy.
    destruct (WfFlip_data Hy) as (W & W' & HWf & HWf' & EWg & EW).
    pose proof Hy as (Hl & HA & HAA & HNN & HC).
    pose proof (eqty_wf_r ge_typeof (geq_ty_sound HAA)) as HA'.
    assert (CA : forall X, [ G ; Γ ⊢ A ≈ X @ l ] -> [ G ; Γ ⊢ A' ≈ X @ l' ]).
    { intros X HX. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HX] | exact Hl]. }
    assert (CN : forall X, [ G ; Γ ,, A @ l ⊢ N ≈ X : tyNat @ lzero ] -> [ G ; Γ ,, A' @ l' ⊢ N' ≈ X : tyNat @ lzero ]).
    { intros X HX.
      eapply geq_tm_ctxconv; [apply geq_ty_sound, HAA | solve [apply lequiv_sym; assumption]
                             | apply ext_wf_g; [exact (lconv_ty HA' (lequiv_sym _ _ _ Hl)) | exact W'] |].
      eapply geq_tm_trans; [apply geq_tm_sym, HNN | exact HX]. }
    apply wfnf_sup.
    + exact (lequiv_trans _ _ _ _ Hk' (lequiv_sym _ _ _ Hl)).
    + exact (lequiv_trans _ _ _ _ Hk (lequiv_sym _ _ _ Hl)).
    + exact (CA _ HAC').
    + exact (CA _ HAC).
    + exact (CN _ HNM').
    + exact (CN _ HNM).
    + intros ρ. exact (Ha ρ).
    + intros ρ. exact (IH ρ l' (kty ρ A') (ktml ρ N') (WfFlipHyps_kw ρ Hy) _ (HC ρ _ _ (Ha ρ))).
  - intros G Γ l A N d ν ν' Hν l' A' N' Hy.
    destruct (WfFlip_data Hy) as (W & W' & HWf & HWf' & EWg & EW).
    apply wfnf_ne. eapply gne_tm_lconv; [eapply gne_tm_conv; [apply gne_tm_sym, Hν | exact EW] | exact (proj1 Hy)].
  - intros G Γ l A N d k cs cs' Hk Hu l' A' N' Hy k' Hkk.
    apply vsp_zero; [exact (NatRel_inv_zero Hkk Hk) |].
    apply (UnitRel_lconv (proj1 Hy)), UnitRel_sym, Hu.
  - intros G Γ l A N d k m cs cs' w w' Hk Hcs Hcs' Hwh Hwh' Heq Hfst IHfst Hsnd IHsnd l' A' N' Hy k' Hkk.
    destruct (WfFlip_data Hy) as (W & W' & HWf & HWf' & EWg & EW).
    pose proof (proj1 Hy) as Hl.
    destruct (NatRel_inv_succ Hkk Hk) as (m' & Hk' & Hmm).
    pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
    pose proof (sigvec_eq (lequiv_sym _ _ _ Hl) W HWf EW Em) as ES.
    assert (Hml : lequiv (gL G) (lmax l' l') (lmax l l)) by now apply lequiv_max.
    assert (MA : forall X, [ G ; Γ ⊢ tyWf l' A' N' ≈ X @ l' ] -> [ G ; Γ ⊢ tyWf l A N ≈ X @ l ]).
    { intros X HX. eapply geq_ty_trans; [exact EWg | eapply geq_ty_lconv; [exact HX | solve [apply lequiv_sym; assumption]]]. }
    assert (MB : forall X, [ G ; Γ ,, tyWf l' A' N' @ l' ⊢ tyVec l' (tyWf l' A' N')⟨↑⟩ m'⟨↑⟩ ≈ X @ l' ] ->
                   [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ X @ l ]).
    { intros X HX.
      assert (HΓ' : [ G ; Γ ,, tyWf l' A' N' @ l' ⊢g ]) by now apply ext_wf_g.
      assert (Y : [ G ; Γ ,, tyWf l' A' N' @ l' ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ X @ l ]).
      { eapply geq_ty_trans;
          [exact (geq_ty_wk (wkr_shift1 _ _ _) HΓ' (geq_vec_nat m m' Hmm l l' _ _ (lequiv_sym _ _ _ Hl) HWf EWg))
          | eapply geq_ty_lconv; [exact HX | solve [apply lequiv_sym; assumption]]]. }
      eapply geq_ty_ctxconv; [| exact Hl | apply ext_wf_g; [exact HWf | exact W] | exact Y].
      eapply eqty_lconv; [apply eqty_sym, EW | exact Hl]. }
    apply (vsp_succ G Γ l' A' N' (flipD d) k' m' cs' cs w' w).
    + exact Hk'.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs' | exact ES] | exact Hml].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs | exact ES] | exact Hml].
    + exact Hwh'.
    + exact Hwh.
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact ES] | exact Hml].
    + intros la' lb' A1' B1' la lb A1 B1 H1' H2' H1 H2 HA1' HB1' HA1 HB1.
      exact (IHfst la lb A1 B1 la' lb' A1' B1'
               (lequiv_trans _ _ _ _ H1 Hl) (lequiv_trans _ _ _ _ H2 Hl)
               (lequiv_trans _ _ _ _ H1' Hl) (lequiv_trans _ _ _ _ H2' Hl)
               (MA _ HA1) (MB _ HB1) (MA _ HA1') (MB _ HB1') l' A' N' Hy).
    + intros la' lb' A1' B1' la lb A1 B1 H1' H2' H1 H2 HA1' HB1' HA1 HB1.
      exact (IHsnd la lb A1 B1 la' lb' A1' B1'
               (lequiv_trans _ _ _ _ H1 Hl) (lequiv_trans _ _ _ _ H2 Hl)
               (lequiv_trans _ _ _ _ H1' Hl) (lequiv_trans _ _ _ _ H2' Hl)
               (MA _ HA1) (MB _ HB1) (MA _ HA1') (MB _ HB1') l' A' N' Hy m' Hmm).
  - intros G Γ l A N d k ν cs cs' Hk Hν Hne l' A' N' Hy k' Hkk.
    destruct (WfFlip_data Hy) as (W & W' & HWf & HWf' & EWg & EW).
    pose proof (proj1 Hy) as Hl.
    destruct (NatRel_inv_ne Hkk Hk (gne_tm_whne_l Hν)) as (ν' & Hk' & Hνν).
    apply (vsp_ne G Γ l' A' N' (flipD d) k' ν' cs' cs); [exact Hk' | eapply gne_tm_trans; [apply gne_tm_sym|]; exact Hνν |].
    pose proof (geq_ty_sound (gne_ty_geq (gne_ty_vec (lequiv_sym _ _ _ Hl) HWf EWg Hνν))) as EV.
    apply (NeRel_lconv _ _ _ _ _ _ Hl).
    eapply NeRel_conv2; [exact EV | exact EV |].
    apply NeRel_flip; exact Hne.
Qed.

End WfFlip.

(** ** Indexed trees, flipped (M17b)

    As [Wf]'s, by induction on the relation, the child spine flipped
    together with the trees, along the right family of child indices: a
    spine is flipped along a right length and family whose positions are
    related to its own ([PosRel]), which is how the right child index
    relates to the left one. The output index moves along the index
    relation, a PER. The annotations' agreement ([IWfEq]) and the
    projections' annotations are declarative equations, moved by
    [IWfEq_flip] and along the spine's type equations. *)
Section IWfFlip.

Lemma PosRel_sym {G Γ k k' p p'} : PosRel G Γ k k' p p' -> PosRel G Γ k' k p' p.
Proof using EL.
  induction 1 as [k k' m m' Hk Hk' Hm | k k' m m' p p' Hk Hk' _ IH | k k' p p' Ek Hp].
  - apply pos_hd; [exact Hk' | exact Hk | now apply NatRel_sym].
  - apply pos_tl; [exact Hk' | exact Hk | exact IH].
  - apply pos_ne; [now apply eqtm_sym |].
    eapply gne_tm_conv; [apply gne_tm_sym, Hp | apply eqty_fin; [exact ge_notV | exact Ek]].
Qed.

Definition IWfFlipHyps G Γ l li X A N Ot C (ix dm : DomRel G Γ) l' li' X' A' N' Ot' C' :=
  IWfEq (G := G) (i := ge_layer) Γ l li l' li' X X' A A' N N' Ot Ot' C C' /\
  (forall (ρ : kwk G Γ) x y, ix ρ x y -> ix ρ y x) /\
  (forall (ρ : kwk G Γ) x y z, ix ρ x y -> ix ρ y z -> ix ρ x z) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' ->
     [ kw_G ρ ; kw_Δ ρ ⊢g a : kty ρ A @ l ] /\ [ kw_G ρ ; kw_Δ ρ ⊢g a' : kty ρ A @ l ] /\
     [ kw_G ρ ; kw_Δ ρ ⊢g a ≅ a' : kty ρ A @ l ]) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' ->
     NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a']) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' -> ix ρ (ktml ρ Ot)[lsingle a] (ktml ρ Ot')[lsingle a']) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' -> forall p p',
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
     ix ρ (ktmll ρ C)[lsingle2 a p] (ktmll ρ C')[lsingle2 a' p']) /\
  IWfGeq G Γ l li X X' A A' N N' Ot Ot' C C' /\
  (forall (ρ : kwk G Γ) x y, ix ρ x y -> [ kw_G ρ ; kw_Δ ρ ⊢ x ≈ y : kty ρ X @ li ]).

Lemma IWfFlip_lv {G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C'} :
  IWfFlipHyps G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C' -> lequiv (gL G) (lmax l' li') (lmax l li).
Proof using . intros ((Hl & Hli & _) & _). apply lequiv_max; solve [apply lequiv_sym; assumption]. Qed.

Lemma IWfFlipHyps_kw {G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C'} (ρ : kwk G Γ) :
  IWfFlipHyps G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C' ->
  IWfFlipHyps (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
    (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ'))
    l' li' (kty ρ X') (kty ρ A') (ktml ρ N') (ktml ρ Ot') (ktmll ρ C').
Proof using EL.
  intros (HE & Hs & Ht & Hd & Har & Hot & Hch & HG & Hie).
  refine (conj (IWfEq_kw ρ HE) (conj (fun ρ' => Hs _) (conj (fun ρ' => Ht _)
            (conj _ (conj _ (conj _ (conj _ (conj (IWfGeq_kw ρ HE HG) _)))))))).
  - intros ρ' a a' h. rewrite <- kty_comp. exact (Hd _ a a' h).
  - intros ρ' a a' h. rewrite <- !ktml_comp. exact (Har _ a a' h).
  - intros ρ' a a' h. rewrite <- !ktml_comp. exact (Hot _ a a' h).
  - intros ρ' a a' h p p'. rewrite <- !ktml_comp, <- !ktmll_comp. exact (Hch _ a a' h p p').
  - intros ρ' x y h. rewrite <- kty_comp. exact (Hie _ x y h).
Qed.

Lemma IWfFlipHyps_flip {G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C'} :
  IWfFlipHyps G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C' ->
  IWfGeq G Γ l' li' X' X A' A N' N Ot' Ot C' C ->
  IWfFlipHyps G Γ l' li' X' A' N' Ot' C' (flipD ix) (flipD dm) l li X A N Ot C.
Proof using EL.
  intros (HE & Hs & Ht & Hd & Har & Hot & Hch & _ & Hie) HG'.
  pose proof HE as (Hll & Hlli & _ & HXX & HAA & _).
  pose proof (lequiv_sym _ _ _ Hll) as Hll'.
  refine (conj (IWfEq_sym ge_typeof ge_notV HE) (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj HG' _))))))));
    unfold flipD, flipR.
  - intros ρ x y h. exact (Hs ρ _ _ h).
  - intros ρ x y z h1 h2. exact (Ht ρ _ _ _ h2 h1).
  - intros ρ a a' h. destruct (Hd ρ a' a h) as (Ha' & Ha & Haa).
    pose proof (eqty_sym _ _ _ _ _ _ (kw_eqty ρ HAA)) as EA. pose proof (kw_lequiv ρ Hll') as Hlρ.
    refine (conj _ (conj _ _)).
    + eapply wf_lconv; [eapply wf_conv; [exact Ha | rewrite ge_typeof; exact EA] | exact Hlρ].
    + eapply wf_lconv; [eapply wf_conv; [exact Ha' | rewrite ge_typeof; exact EA] | exact Hlρ].
    + eapply eqtm_lconv; [eapply eqtm_conv; [apply eqtm_sym, Haa | rewrite ge_typeof; exact EA] | exact Hlρ].
  - intros ρ a a' h. apply NatRel_sym, Har, h.
  - intros ρ a a' h. exact (Hot ρ _ _ h).
  - intros ρ a a' h p p' Hp. exact (Hch ρ _ _ h p' p (PosRel_sym Hp)).
  - intros ρ x y h. eapply geq_tm_lconv; [| exact (kw_lequiv ρ (lequiv_sym _ _ _ Hlli))].
    eapply geq_tm_conv; [apply geq_tm_sym, Hie, h | exact (kw_eqty ρ HXX)].
Qed.

Lemma IWfRel_flip_all :
  (forall G Γ l li X A N Ot C ix dm m t t', IWfRel G Γ l li X A N Ot C ix dm m t t' ->
     forall l' li' X' A' N' Ot' C' m', IWfFlipHyps G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C' ->
     [ G ; Γ ⊢g tyIWf l li X A N Ot C m ≅ tyIWf l' li' X' A' N' Ot' C' m' @ lmax l li ] ->
     (forall ρ : kwk G Γ, ix ρ (ktm ρ m) (ktm ρ m')) ->
     IWfRel G Γ l' li' X' A' N' Ot' C' (flipD ix) (flipD dm) m' t' t) /\
  (forall G Γ l li X A N Ot C ix dm m t t', IWfNf G Γ l li X A N Ot C ix dm m t t' ->
     forall l' li' X' A' N' Ot' C' m', IWfFlipHyps G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C' ->
     [ G ; Γ ⊢g tyIWf l li X A N Ot C m ≅ tyIWf l' li' X' A' N' Ot' C' m' @ lmax l li ] ->
     (forall ρ : kwk G Γ, ix ρ (ktm ρ m) (ktm ρ m')) ->
     IWfNf G Γ l' li' X' A' N' Ot' C' (flipD ix) (flipD dm) m' t' t) /\
  (forall G Γ l li X A N Ot C ix dm c k cs cs', DVecISp G Γ l li X A N Ot C ix dm c k cs cs' ->
     forall l' li' X' A' N' Ot' C' c' k', IWfFlipHyps G Γ l li X A N Ot C ix dm l' li' X' A' N' Ot' C' ->
     NatRel G Γ k k' -> (forall ρ : kwk G Γ, NatRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k) (ktm ρ k')) ->
     [ G ; Γ ,, tyFin k @ lzero ⊢g iwfFamT l li X A N Ot C c ≅ iwfFamT l' li' X' A' N' Ot' C' c' @ lmax l li ] ->
     (forall (ρ : kwk G Γ) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k) (ktm ρ k') p p' ->
        ix ρ (ktml ρ c)[lsingle p] (ktml ρ c')[lsingle p']) ->
     DVecISp G Γ l' li' X' A' N' Ot' C' (flipD ix) (flipD dm) c' k' cs' cs).
Proof using EL.
  apply IWfRel_comb.
  - intros G Γ l li X A N Ot C ix dm m t t' w w' Hw Hw' Heq _ IH l' li' X' A' N' Ot' C' m' Hy ET Hix.
    pose proof (IWfFlip_lv Hy) as Hml.
    econstructor.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw' | exact ET] | exact Hml].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw | exact ET] | exact Hml].
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact ET] | exact Hml].
    + exact (IH l' li' X' A' N' Ot' C' m' Hy ET Hix).
  - intros G Γ l li X A N Ot C ix dm m k ki k' ki' X1 A1 N1 O1 C1 X1' A1' N1' O1' C1' a a' cs cs'
      E1 E2 Hd Ho Hcs IH l' li' X' A' N' Ot' C' m' Hy ET Hix.
    pose proof Hy as (HE & Hs & Ht & Hesc & Har & Hot & Hch & _).
    apply iwfnf_sup.
    + exact (IWfEq_flip ge_typeof ge_notV HE E2).
    + exact (IWfEq_flip ge_typeof ge_notV HE E1).
    + intros ρ. exact (Hd ρ).
    + intros ρ. unfold flipD, flipR.
      exact (Ht ρ _ _ _ (Hs ρ _ _ (Hix ρ)) (Ht ρ _ _ _ (Hs ρ _ _ (Ho ρ)) (Hot ρ _ _ (Hd ρ)))).
    + intros ρ.
      destruct (Hesc ρ _ _ (Hd ρ)) as (Ha & Ha' & Haa).
      refine (IH ρ l' li' (kty ρ X') (kty ρ A') (ktml ρ N') (ktml ρ Ot') (ktmll ρ C')
                (ktmll ρ C')[llift (lsingle (ktm ρ a'))] (ktml ρ N')[lsingle (ktm ρ a')]
                (IWfFlipHyps_kw ρ Hy) (Har ρ _ _ (Hd ρ)) _ _ _).
      * intros ρ'. rewrite !ktm_comp_single. exact (Har _ _ _ (Hd (kw_comp ρ ρ'))).
      * exact (IWf_fam_eq ge_typeof ge_notV (IWfEq_kw ρ HE) Ha Ha' Haa).
      * intros ρ' p p' Hp. rewrite !ktml_comp_child. rewrite !ktm_comp_single in Hp.
        exact (Hch _ _ _ (Hd (kw_comp ρ ρ')) p p' Hp).
  - intros G Γ l li X A N Ot C ix dm m ν ν' Hν l' li' X' A' N' Ot' C' m' Hy ET Hix.
    apply iwfnf_ne.
    eapply gne_tm_lconv; [eapply gne_tm_conv; [apply gne_tm_sym, Hν | exact ET] | exact (IWfFlip_lv Hy)].
  - intros G Γ l li X A N Ot C ix dm c k cs cs' Hk Hu l' li' X' A' N' Ot' C' c' k' Hy Hkk _ _ _.
    apply visp_zero; [exact (NatRel_inv_zero Hkk Hk) |].
    apply (UnitRel_lconv (IWfFlip_lv Hy)), UnitRel_sym, Hu.
  - intros G Γ l li X A N Ot C ix dm c k m cs cs' w w' Hk Hcs Hcs' Hwh Hwh' Heq Hfst IHfst Hsnd IHsnd
      l' li' X' A' N' Ot' C' c' k' Hy Hkk HkkW HF HP.
    pose proof Hy as (HE & _).
    pose proof HE as (Hll & Hlli & (Wl & Wli & HX & HA & HN & HO & HC) & _ & _ & _ & _ & _
                      & HX' & HA' & HN' & HO' & HC').
    pose proof (IWfFlip_lv Hy) as Hml. pose proof (lequiv_sym _ _ _ Hml) as Hml'.
    assert (HL : lwf (gL G) (lmax l li)) by (split; assumption).
    assert (HL' : lwf (gL G) (lmax l' li')) by exact (lequiv_wf_l _ _ _ Hml).
    assert (Hml2 : lequiv (gL G) (lmax (lmax l' li') (lmax l' li')) (lmax (lmax l li) (lmax l li)))
      by now apply lequiv_max.
    destruct (NatRel_inv_succ Hkk Hk) as (m' & Hk' & Hmm).
    pose proof (NatRel_kw_pred HkkW Hk Hk') as HmmW.
    pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
    pose proof (eqtm_wf_l ge_typeof Em) as Hm. pose proof (eqtm_wf_r ge_typeof Em) as Hm'.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hk) as Ek.
    set (F := iwfFamT l li X A N Ot C c) in *. set (F' := iwfFamT l' li' X' A' N' Ot' C' c') in *.
    assert (HF1 : [ G ; Γ ,, tyFin (succ m) @ lzero ⊢g F ≅ F' @ lmax l li ]).
    { refine (stab_eqty ge_typeof _ (lequiv_refl (gL G) lzero I) _ HF).
      - apply eqty_fin; [exact ge_notV | exact Ek].
      - apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV |].
        exact (eqtm_wf_r ge_typeof Ek). }
    pose proof (eqty_wf_l ge_typeof HF1) as HF1w.
    pose proof (dvec_sig_eqty ge_typeof ge_notV ge_compt Hml' HL Hm Hm' Em HF1w HF1) as ES.
    pose proof (dvecHd_eqty ge_typeof ge_notV ge_compt Hm Hm' Em HF1w HF1) as EH.
    assert (HH : [ G ; Γ ⊢g dvecHd m F @ lmax l li ])
      by exact (wf_ty_single ge_typeof HF1w (fin_inl_wf ge_typeof ge_notV ge_compt Hm)).
    assert (HH' : [ G ; Γ ⊢g dvecHd m' F' @ lmax l' li' ])
      by (eapply wft_lconv; [exact (eqty_wf_r ge_typeof EH) | exact Hml]).
    pose proof Hy as (_ & _ & _ & _ & _ & _ & _ & HGy & Hiey).
    destruct (iwf_succ_geq HE HGy Hk Hk' Hmm HF (fun ρ p p' Hp => Hiey ρ _ _ (HP ρ p p' Hp))) as [GH GT].
    assert (MA : forall Y, [ G ; Γ ⊢ dvecHd m' F' ≈ Y @ lmax l' li' ] -> [ G ; Γ ⊢ dvecHd m F ≈ Y @ lmax l li ]).
    { intros Y HY. eapply geq_ty_trans; [exact GH | eapply geq_ty_lconv; [exact HY | exact Hml']]. }
    assert (MB : forall Y, [ G ; Γ ,, dvecHd m' F' @ lmax l' li' ⊢ dvecTl (lmax l' li') m' F' ≈ Y @ lmax l' li' ] ->
                  [ G ; Γ ,, dvecHd m F @ lmax l li ⊢ dvecTl (lmax l li) m F ≈ Y @ lmax l li ]).
    { intros Y HY.
      assert (HΓ' : [ G ; Γ ,, dvecHd m' F' @ lmax l' li' ⊢g ]) by (apply ext_wf_g; [exact HH' | exact HL']).
      assert (Y1 : [ G ; Γ ,, dvecHd m' F' @ lmax l' li' ⊢ dvecTl (lmax l li) m F ≈ Y @ lmax l li ]).
      { eapply geq_ty_trans; [exact (GT _ _ HΓ') | eapply geq_ty_lconv; [exact HY | exact Hml']]. }
      refine (geq_ty_ctxconv _ Hml _ Y1).
      - eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EH) | exact Hml].
      - apply ext_wf_g; [exact HH | exact HL]. }
    pose proof (kw_tmred_succ Hk) as Rk. pose proof (kw_tmred_succ Hk') as Rk'.
    apply (visp_succ G Γ l' li' X' A' N' Ot' C' (flipD ix) (flipD dm) c' k' m' cs' cs w' w).
    + exact Hk'.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs' | exact ES] | exact Hml2].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs | exact ES] | exact Hml2].
    + exact Hwh'.
    + exact Hwh.
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact ES] | exact Hml2].
    + intros pa pb PA PB qa qb QA QB Hpa Hpb Hqa Hqb HPA HPB HQA HQB.
      refine (IHfst qa qb QA QB pa pb PA PB
               (lequiv_trans _ _ _ _ Hqa Hml) (lequiv_trans _ _ _ _ Hqb Hml)
               (lequiv_trans _ _ _ _ Hpa Hml) (lequiv_trans _ _ _ _ Hpb Hml)
               (MA _ HQA) (MB _ HQB) (MA _ HPA) (MB _ HPB) l' li' X' A' N' Ot' C' c'[lsingle (posHd m')] Hy _ _).
      * subst F F'. rewrite !iwfFamT_single in EH by eauto using wf_ty_nf, wf_tm_nf. exact EH.
      * intros ρ. rewrite !ktm_single, !ktm_posHd. apply HP.
        apply pos_hd; [exact (Rk ρ) | exact (Rk' ρ) | exact (HmmW ρ)].
    + intros pa pb PA PB qa qb QA QB Hpa Hpb Hqa Hqb HPA HPB HQA HQB.
      refine (IHsnd qa qb QA QB pa pb PA PB
               (lequiv_trans _ _ _ _ Hqa Hml) (lequiv_trans _ _ _ _ Hqb Hml)
               (lequiv_trans _ _ _ _ Hpa Hml) (lequiv_trans _ _ _ _ Hpb Hml)
               (MA _ HQA) (MB _ HQB) (MA _ HPA) (MB _ HPB) l' li' X' A' N' Ot' C' (posMv m' c') m'
               Hy Hmm HmmW _ _).
      * rewrite <- !iwfFamT_mv. exact (dvecMv_eqty ge_typeof ge_notV ge_compt Hm Hm' Em HF1w HF1).
      * intros ρ p p' Hp. rewrite !ktml_posMv_single by eauto using wf_tm_nf. apply HP.
        apply pos_tl; [exact (Rk ρ) | exact (Rk' ρ) | exact Hp].
  - intros G Γ l li X A N Ot C ix dm c k ν cs cs' Hk Hν Hne l' li' X' A' N' Ot' C' c' k' Hy Hkk _ HF _.
    pose proof (IWfFlip_lv Hy) as Hml. pose proof (lequiv_sym _ _ _ Hml) as Hml'.
    destruct (NatRel_inv_ne Hkk Hk (gne_tm_whne_l Hν)) as (ν' & Hk' & Hνν).
    apply (visp_ne G Γ l' li' X' A' N' Ot' C' (flipD ix) (flipD dm) c' k' ν' cs' cs);
      [exact Hk' | eapply gne_tm_trans; [apply gne_tm_sym|]; exact Hνν |].
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Eν.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hk) as Ek.
    assert (HFν : [ G ; Γ ,, tyFin ν @ lzero ⊢g iwfFamT l li X A N Ot C c ≅ iwfFamT l' li' X' A' N' Ot' C' c' @ lmax l li ]).
    { refine (stab_eqty ge_typeof _ (lequiv_refl (gL G) lzero I) _ HF).
      - apply eqty_fin; [exact ge_notV | exact Ek].
      - apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV |].
        exact (eqtm_wf_r ge_typeof Ek). }
    assert (EV : [ G ; Γ ⊢g tyDVec (lmax l li) ν (iwfFamT l li X A N Ot C c)
                    ≅ tyDVec (lmax l' li') ν' (iwfFamT l' li' X' A' N' Ot' C' c') @ lmax l li ]).
    { apply eqty_dvec; [exact (compt_notV _ ge_compt) | exact Hml' | exact (eqtm_wf_l ge_typeof Eν) | exact Eν
                       | exact (eqty_wf_l ge_typeof HFν) | exact HFν]. }
    apply (NeRel_lconv _ _ _ _ _ _ Hml).
    eapply NeRel_conv2; [exact EV | exact EV |].
    apply NeRel_flip; exact Hne.
Qed.

End IWfFlip.

(** ** Indexed trees with infinitary children, flipped (M19b)

    As [IWf]'s, with [W]'s children premise per field. A spine is flipped
    along right families whose domains and child indices are generically
    equal to its own at related positions ([IWiPosGeq]), with the
    argument relations met at canonical positions: the flipped spine's
    relation at a right position gives the spine's own at the left one
    ([PosCan_det_l]), and the left one's arguments give child indices
    related by the index relation in every world and generically equal
    here. The domains' relation flips by swapping its sides ([iflipP]). *)
Section IWiFlip.

Definition IWiFlipHyps G Γ l lp li X A N D Ot C (ix dm : DomRel G Γ) (pd : IPosDomRel G Γ) l' lp' li' X' A' N' D' Ot' C' :=
  IWiEq (G := G) (i := ge_layer) Γ l lp li l' lp' li' X X' A A' N N' D D' Ot Ot' C C' /\
  (forall (ρ : kwk G Γ) x y, ix ρ x y -> ix ρ y x) /\
  (forall (ρ : kwk G Γ) x y z, ix ρ x y -> ix ρ y z -> ix ρ x z) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' ->
     [ kw_G ρ ; kw_Δ ρ ⊢g a : kty ρ A @ l ] /\ [ kw_G ρ ; kw_Δ ρ ⊢g a' : kty ρ A @ l ] /\
     [ kw_G ρ ; kw_Δ ρ ⊢g a ≅ a' : kty ρ A @ l ]) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' ->
     NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a']) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' -> ix ρ (ktml ρ Ot)[lsingle a] (ktml ρ Ot')[lsingle a']) /\
  (forall (ρ : kwk G Γ) a a' p p' y y', pd ρ a a' p p' y y' ->
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a'] p p') /\
  (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' p p' y y', pd ρ a a' p p' y y' ->
     pd (kw_comp ρ ρ') (ktm ρ' a) (ktm ρ' a') (ktm ρ' p) (ktm ρ' p') (ktm ρ' y) (ktm ρ' y')) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' -> forall p p' y y', pd ρ a a' p p' y y' ->
     ix ρ (ktmlll ρ C)[lsingle3 a p y] (ktmlll ρ C')[lsingle3 a' p' y']) /\
  (forall (ρ : kwk G Γ) a a', dm ρ a a' -> forall p p',
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
     [ kw_G ρ ; kw_Δ ρ ⊢g (ktyll ρ D)[lsingle2 a p] @ lp ] /\
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyll ρ D)[lsingle2 a p] ≈ (ktyll ρ D')[lsingle2 a' p'] @ lp ] /\
     [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ D)[lsingle2 a p] @ lp
         ⊢ (ktmlll ρ C)[llift (lsingle2 a p)] ≈ (ktmlll ρ C')[llift (lsingle2 a' p')] : (kty ρ X)⟨↑⟩ @ li ]) /\
  IWiGeq G Γ l lp li X X' A A' N N' D D' Ot Ot' C C' /\
  (forall (ρ : kwk G Γ) x y, ix ρ x y -> [ kw_G ρ ; kw_Δ ρ ⊢ x ≈ y : kty ρ X @ li ]).

Lemma IWiFlip_lv {G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C'} :
  IWiFlipHyps G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C' ->
  lequiv (gL G) (iwiL l' lp' li') (iwiL l lp li).
Proof using . intros ((Hl & Hlp & Hli & _) & _). apply IWi_lvl_eq; apply lequiv_sym; assumption. Qed.

Lemma IWiFlipHyps_kw {G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C'} (ρ : kwk G Γ) :
  IWiFlipHyps G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C' ->
  IWiFlipHyps (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
    (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ'))
    l' lp' li' (kty ρ X') (kty ρ A') (ktml ρ N') (ktyll ρ D') (ktml ρ Ot') (ktmlll ρ C').
Proof using EL.
  intros (HE & Hs & Ht & Hd & Har & Hot & Hpe & Hpm & Hch & Hpg & HG & Hie).
  refine (conj (IWiEq_kw ρ HE) (conj (fun ρ' => Hs _) (conj (fun ρ' => Ht _)
            (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj (IWiGeq_kw ρ HE HG) _))))))))))).
  - intros ρ' a a' h. rewrite <- kty_comp. exact (Hd _ a a' h).
  - intros ρ' a a' h. rewrite <- !ktml_comp. exact (Har _ a a' h).
  - intros ρ' a a' h. rewrite <- !ktml_comp. exact (Hot _ a a' h).
  - intros ρ' a a' p p' y y' h. rewrite <- !ktml_comp. exact (Hpe _ _ _ _ _ _ _ h).
  - intros ρ' ρ'' a a' p p' y y' h. exact (Hpm (kw_comp ρ ρ') ρ'' _ _ _ _ _ _ h).
  - intros ρ' a a' h p p' y y' hp. rewrite <- !ktmlll_comp. exact (Hch _ _ _ h _ _ _ _ hp).
  - intros ρ' a a' h p p' Hp. rewrite <- !ktml_comp in Hp. rewrite <- !ktyll_comp, <- !ktmlll_comp, <- kty_comp.
    exact (Hpg _ _ _ h p p' Hp).
  - intros ρ' x y h. rewrite <- kty_comp. exact (Hie _ x y h).
Qed.

Lemma IWiFlipHyps_flip {G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C'} :
  IWiFlipHyps G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C' ->
  IWiGeq G Γ l' lp' li' X' X A' A N' N D' D Ot' Ot C' C ->
  (forall (ρ : kwk G Γ) a a', dm ρ a' a -> forall p p',
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N')[lsingle a] (ktml ρ N)[lsingle a'] p p' ->
     [ kw_G ρ ; kw_Δ ρ ⊢g (ktyll ρ D')[lsingle2 a p] @ lp' ] /\
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyll ρ D')[lsingle2 a p] ≈ (ktyll ρ D)[lsingle2 a' p'] @ lp' ] /\
     [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ D')[lsingle2 a p] @ lp'
         ⊢ (ktmlll ρ C')[llift (lsingle2 a p)] ≈ (ktmlll ρ C)[llift (lsingle2 a' p')] : (kty ρ X')⟨↑⟩ @ li' ]) ->
  IWiFlipHyps G Γ l' lp' li' X' A' N' D' Ot' C' (flipD ix) (flipD dm) (iflipP pd) l lp li X A N D Ot C.
Proof using EL.
  intros (HE & Hs & Ht & Hd & Har & Hot & Hpe & Hpm & Hch & _ & _ & Hie) HG' Hpg'.
  pose proof HE as (Hll & Hllp & Hlli & _ & HXX & HAA & _).
  pose proof (lequiv_sym _ _ _ Hll) as Hll'.
  refine (conj (IWiEq_sym ge_typeof ge_notV HE) (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
            (conj _ (conj Hpg' (conj HG' _)))))))))));
    unfold flipD, flipR, iflipP.
  - intros ρ x y h. exact (Hs ρ _ _ h).
  - intros ρ x y z h1 h2. exact (Ht ρ _ _ _ h2 h1).
  - intros ρ a a' h. destruct (Hd ρ a' a h) as (Ha' & Ha & Haa).
    pose proof (eqty_sym _ _ _ _ _ _ (kw_eqty ρ HAA)) as EA. pose proof (kw_lequiv ρ Hll') as Hlρ.
    refine (conj _ (conj _ _)).
    + eapply wf_lconv; [eapply wf_conv; [exact Ha | rewrite ge_typeof; exact EA] | exact Hlρ].
    + eapply wf_lconv; [eapply wf_conv; [exact Ha' | rewrite ge_typeof; exact EA] | exact Hlρ].
    + eapply eqtm_lconv; [eapply eqtm_conv; [apply eqtm_sym, Haa | rewrite ge_typeof; exact EA] | exact Hlρ].
  - intros ρ a a' h. apply NatRel_sym, Har, h.
  - intros ρ a a' h. exact (Hot ρ _ _ h).
  - intros ρ a a' p p' y y' h. exact (PosRel_sym (Hpe ρ _ _ _ _ _ _ h)).
  - intros ρ ρ' a a' p p' y y' h. exact (Hpm ρ ρ' _ _ _ _ _ _ h).
  - intros ρ a a' h p p' y y' hp. exact (Hch ρ _ _ h _ _ _ _ hp).
  - intros ρ x y h. eapply geq_tm_lconv; [| exact (kw_lequiv ρ (lequiv_sym _ _ _ Hlli))].
    eapply geq_tm_conv; [apply geq_tm_sym, Hie, h | exact (kw_eqty ρ HXX)].
Qed.

Lemma IWiRel_flip_all :
  (forall G Γ l lp li X A N D Ot C ix dm pd m t t', IWiRel G Γ l lp li X A N D Ot C ix dm pd m t t' ->
     forall l' lp' li' X' A' N' D' Ot' C' m',
     IWiFlipHyps G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C' ->
     [ G ; Γ ⊢g tyIWi l lp li X A N D Ot C m ≅ tyIWi l' lp' li' X' A' N' D' Ot' C' m' @ iwiL l lp li ] ->
     (forall ρ : kwk G Γ, ix ρ (ktm ρ m) (ktm ρ m')) ->
     IWiRel G Γ l' lp' li' X' A' N' D' Ot' C' (flipD ix) (flipD dm) (iflipP pd) m' t' t) /\
  (forall G Γ l lp li X A N D Ot C ix dm pd m t t', IWiNf G Γ l lp li X A N D Ot C ix dm pd m t t' ->
     forall l' lp' li' X' A' N' D' Ot' C' m',
     IWiFlipHyps G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C' ->
     [ G ; Γ ⊢g tyIWi l lp li X A N D Ot C m ≅ tyIWi l' lp' li' X' A' N' D' Ot' C' m' @ iwiL l lp li ] ->
     (forall ρ : kwk G Γ, ix ρ (ktm ρ m) (ktm ρ m')) ->
     IWiNf G Γ l' lp' li' X' A' N' D' Ot' C' (flipD ix) (flipD dm) (iflipP pd) m' t' t) /\
  (forall G Γ l lp li X A N D Ot C ix dm pd yR d c k cs cs',
     DVecWSp G Γ l lp li X A N D Ot C ix dm pd yR d c k cs cs' ->
     forall l' lp' li' X' A' N' D' Ot' C' yR' d' c' k',
     IWiFlipHyps G Γ l lp li X A N D Ot C ix dm pd l' lp' li' X' A' N' D' Ot' C' ->
     NatRel G Γ k k' -> (forall ρ : kwk G Γ, NatRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k) (ktm ρ k')) ->
     [ G ; Γ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c
         ≅ iwiFamT l' lp' li' X' A' N' D' Ot' C' d' c' @ iwiL l lp li ] ->
     IWiPosGeq G Γ lp li X k k' d d' c c' ->
     (forall p p', PosCan G Γ k k' p p' -> forall y y', yR' p' y' y -> yR p y y') ->
     (forall p p', PosCan G Γ k k' p p' -> forall y y', yR p y y' ->
        forall ρ : kwk G Γ, ix ρ (ktm ρ c[lsingle2 p y]) (ktm ρ c'[lsingle2 p' y'])) ->
     (forall p p', PosCan G Γ k k' p p' -> forall y y', yR p y y' ->
        [ G ; Γ ⊢g c[lsingle2 p y] ≅ c'[lsingle2 p' y'] : X @ li ]) ->
     DVecWSp G Γ l' lp' li' X' A' N' D' Ot' C' (flipD ix) (flipD dm) (iflipP pd) yR' d' c' k' cs' cs).
Proof using EL.
  apply IWiRel_comb.
  - intros G Γ l lp li X A N D Ot C ix dm pd m t t' w w' Hw Hw' Heq _ IH l' lp' li' X' A' N' D' Ot' C' m' Hy ET Hix.
    pose proof (IWiFlip_lv Hy) as Hml.
    econstructor.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw' | exact ET] | exact Hml].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw | exact ET] | exact Hml].
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact ET] | exact Hml].
    + exact (IH l' lp' li' X' A' N' D' Ot' C' m' Hy ET Hix).
  - intros G Γ l lp li X A N D Ot C ix dm pd m k kp ki k' kp' ki' X1 A1 N1 D1 O1 C1 X1' A1' N1' D1' O1' C1'
      a a' cs cs' E1 E2 Hd Ho Hcs IH l' lp' li' X' A' N' D' Ot' C' m' Hy ET Hix.
    pose proof Hy as (HE & Hs & Ht & Hesc & Har & Hot & Hpe & Hpm & Hch & Hpg & _ & Hie).
    apply iwinf_sup.
    + exact (IWiEq_flip ge_typeof ge_notV HE E2).
    + exact (IWiEq_flip ge_typeof ge_notV HE E1).
    + intros ρ. exact (Hd ρ).
    + intros ρ. unfold flipD, flipR.
      exact (Ht ρ _ _ _ (Hs ρ _ _ (Hix ρ)) (Ht ρ _ _ _ (Hs ρ _ _ (Ho ρ)) (Hot ρ _ _ (Hd ρ)))).
    + intros ρ.
      destruct (Hesc ρ _ _ (Hd ρ)) as (Ha & Ha' & Haa).
      refine (IH ρ l' lp' li' (kty ρ X') (kty ρ A') (ktml ρ N') (ktyll ρ D') (ktml ρ Ot') (ktmlll ρ C')
                (fun p' y' y => exists p, pd ρ (ktm ρ a) (ktm ρ a') p p' y y')
                (ktyll ρ D')[llift (lsingle (ktm ρ a'))] (ktmlll ρ C')[llift (llift (lsingle (ktm ρ a')))]
                (ktml ρ N')[lsingle (ktm ρ a')]
                (IWiFlipHyps_kw ρ Hy) (Har ρ _ _ (Hd ρ)) _ _ _ _ _ _).
      * intros ρ'. rewrite !ktm_comp_single. exact (Har _ _ _ (Hd (kw_comp ρ ρ'))).
      * exact (IWi_fam_eq ge_typeof ge_notV (IWiEq_kw ρ HE) Ha Ha' Haa).
      * intros ρ' p p' Hp. rewrite !ktm_comp_single in Hp.
        rewrite !ktyl_iwiD_single, !ktmll_iwiC_single, <- kty_comp.
        exact (Hpg _ _ _ (Hd (kw_comp ρ ρ')) p p' Hp).
      * intros p p' Hpc y y' (p0 & Hp0). exists p'.
        pose proof (Hpe ρ _ _ _ _ _ _ Hp0) as Hr. rewrite (PosCan_det_l Hpc _ Hr) in Hp0. exact Hp0.
      * intros p p' Hpc y y' (p1 & Hp1) ρ'.
        pose proof (Hpe ρ _ _ _ _ _ _ Hp1) as Hr. rewrite (PosCan_det_r Hpc _ Hr) in Hp1.
        pose proof (Hpm ρ ρ' _ _ _ _ _ _ Hp1) as Hm1. rewrite <- !ktm_comp in Hm1.
        rewrite !ktm_iwiC_single2. exact (Hch (kw_comp ρ ρ') _ _ (Hd (kw_comp ρ ρ')) _ _ _ _ Hm1).
      * intros p p' Hpc y y' (p1 & Hp1).
        pose proof (Hpe ρ _ _ _ _ _ _ Hp1) as Hr. rewrite (PosCan_det_r Hpc _ Hr) in Hp1.
        rewrite !llift2_single_single2 by (unfold ktm; apply ren_nf).
        exact (geq_tm_sound (Hie ρ _ _ (Hch ρ _ _ (Hd ρ) _ _ _ _ Hp1))).
  - intros G Γ l lp li X A N D Ot C ix dm pd m ν ν' Hν l' lp' li' X' A' N' D' Ot' C' m' Hy ET Hix.
    apply iwinf_ne.
    eapply gne_tm_lconv; [eapply gne_tm_conv; [apply gne_tm_sym, Hν | exact ET] | exact (IWiFlip_lv Hy)].
  - intros G Γ l lp li X A N D Ot C ix dm pd yR d c k cs cs' Hk Hu l' lp' li' X' A' N' D' Ot' C' yR' d' c' k'
      Hy Hkk _ _ _ _ _ _.
    apply wsp_zero; [exact (NatRel_inv_zero Hkk Hk) |].
    apply (UnitRel_lconv (IWiFlip_lv Hy)), UnitRel_sym, Hu.
  - intros G Γ l lp li X A N D Ot C ix dm pd yR d c k m cs cs' w w' Hk Hcs Hcs' Hwh Hwh' Heq Hfst Happ IHapp
      Hsnd IHsnd l' lp' li' X' A' N' D' Ot' C' yR' d' c' k' Hy Hkk HkkW HF HP HYR HIX HIX0.
    pose proof Hy as (HE & _).
    pose proof HE as (Hll & Hllp & Hlli & HS & _).
    pose proof HS as (Wl & Wlp & Wli & HX & HA & HN & HD & HO & HC).
    pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
    pose proof (IWiSig_nf (IWiEq_sig_r ge_typeof ge_notV HE)) as (NX' & NA' & NN' & ND' & NO' & NC').
    pose proof (IWiFlip_lv Hy) as Hml. pose proof (lequiv_sym _ _ _ Hml) as Hml'.
    assert (HL : lwf (gL G) (iwiL l lp li)) by (repeat split; cbn; auto).
    assert (HL' : lwf (gL G) (iwiL l' lp' li')) by exact (lequiv_wf_l _ _ _ Hml).
    assert (Hml2 : lequiv (gL G) (lmax (iwiL l' lp' li') (iwiL l' lp' li')) (lmax (iwiL l lp li) (iwiL l lp li)))
      by now apply lequiv_max.
    destruct (NatRel_inv_succ Hkk Hk) as (m' & Hk' & Hmm).
    pose proof (NatRel_kw_pred HkkW Hk Hk') as HmmW.
    pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
    pose proof (eqtm_wf_l ge_typeof Em) as Hm. pose proof (eqtm_wf_r ge_typeof Em) as Hm'.
    pose proof (wf_tm_nf Hm) as Nm. pose proof (wf_tm_nf Hm') as Nm'.
    pose proof (ctx_of_tm Hm) as HΓ.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hk) as Ek.
    pose proof (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_l ge_typeof HF))) as (Nd & Nc).
    pose proof (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_r ge_typeof HF))) as (Nd' & Nc').
    set (F := iwiFamT l lp li X A N D Ot C d c) in *. set (F' := iwiFamT l' lp' li' X' A' N' D' Ot' C' d' c') in *.
    pose proof (fin_stab_eqty Ek HF) as HF1.
    pose proof (eqty_wf_l ge_typeof HF1) as HF1w.
    pose proof (dvec_sig_eqty ge_typeof ge_notV ge_compt Hml' HL Hm Hm' Em HF1w HF1) as ES.
    pose proof (dvecHd_eqty ge_typeof ge_notV ge_compt Hm Hm' Em HF1w HF1) as EH.
    assert (HH : [ G ; Γ ⊢g dvecHd m F @ iwiL l lp li ])
      by exact (wf_ty_single ge_typeof HF1w (fin_inl_wf ge_typeof ge_notV ge_compt Hm)).
    assert (HH' : [ G ; Γ ⊢g dvecHd m' F' @ iwiL l' lp' li' ])
      by (eapply wft_lconv; [exact (eqty_wf_r ge_typeof EH) | exact Hml]).
    pose proof Hy as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGy & Hiey).
    destruct (iwi_succ_geq HE HGy Hk Hk' Hmm HF HP) as [GH GT].
    assert (MA : forall Y, [ G ; Γ ⊢ dvecHd m' F' ≈ Y @ iwiL l' lp' li' ] -> [ G ; Γ ⊢ dvecHd m F ≈ Y @ iwiL l lp li ]).
    { intros Y HY. eapply geq_ty_trans; [exact GH | eapply geq_ty_lconv; [exact HY | exact Hml']]. }
    assert (MB : forall Y, [ G ; Γ ,, dvecHd m' F' @ iwiL l' lp' li' ⊢ dvecTl (iwiL l' lp' li') m' F' ≈ Y @ iwiL l' lp' li' ] ->
                  [ G ; Γ ,, dvecHd m F @ iwiL l lp li ⊢ dvecTl (iwiL l lp li) m F ≈ Y @ iwiL l lp li ]).
    { intros Y HY.
      assert (HΓ' : [ G ; Γ ,, dvecHd m' F' @ iwiL l' lp' li' ⊢g ]) by (apply ext_wf_g; [exact HH' | exact HL']).
      assert (Y1 : [ G ; Γ ,, dvecHd m' F' @ iwiL l' lp' li' ⊢ dvecTl (iwiL l lp li) m F ≈ Y @ iwiL l lp li ]).
      { eapply geq_ty_trans; [exact (GT _ _ HΓ') | eapply geq_ty_lconv; [exact HY | exact Hml']]. }
      refine (geq_ty_ctxconv _ Hml _ Y1).
      - eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EH) | exact Hml].
      - apply ext_wf_g; [exact HH | exact HL]. }
    (* the head position: its domains and child indices *)
    destruct (HP (kw_self HΓ) (posHd m) (posHd m')) as (Hd0 & Gd & Gc).
    { pose proof (wf_tm_nf (eqtm_wf_l ge_typeof Ek)) as Nk.
      pose proof (wf_tm_nf (eqtm_wf_l ge_typeof (tmred_eq _ _ _ _ _ _ _ Hk'))) as Nk'.
      rewrite !ktm_self by assumption.
      apply pos_hd; [exact Hk | exact Hk' | exact Hmm]. }
    rewrite ktyl_self in Hd0 by assumption. rewrite !ktyl_self in Gd by assumption.
    rewrite ktyl_self, !ktmll_self, kty_self in Gc by assumption.
    assert (HΓd : [ G ; Γ ,, d[lsingle (posHd m)] @ lp ⊢g ]) by exact (ext_wf_g Hd0 Wlp).
    assert (Ed : [ G ; Γ ⊢g d[lsingle (posHd m)] ≅ d'[lsingle (posHd m')] @ lp ]) by exact (geq_ty_sound Gd).
    assert (Hd0' : [ G ; Γ ⊢g d'[lsingle (posHd m')] @ lp' ])
      by (eapply wft_lconv; [exact (eqty_wf_r ge_typeof Ed) | exact (lequiv_sym _ _ _ Hllp)]).
    assert (MD : forall Y, [ G ; Γ ⊢ d'[lsingle (posHd m')] ≈ Y @ lp' ] -> [ G ; Γ ⊢ d[lsingle (posHd m)] ≈ Y @ lp ]).
    { intros Y HY. eapply geq_ty_trans; [exact Gd | eapply geq_ty_lconv; [exact HY | exact Hllp]]. }
    assert (Ec : [ G ; Γ ,, d[lsingle (posHd m)] @ lp
                   ⊢ (iwiFamCodT l lp li X A N D Ot C c)[llift (lsingle (posHd m))]
                   ≈ (iwiFamCodT l' lp' li' X' A' N' D' Ot' C' c')[llift (lsingle (posHd m'))] @ iwiL l lp li ]).
    { rewrite !iwiFamCodT_single by assumption.
      exact (iwi_geq_at (IWiEq_wk1 ge_typeof ge_notV HE HΓd) (IWiGeq_wk1 HE HGy HΓd) Gc). }
    assert (MC : forall Y, [ G ; Γ ,, d'[lsingle (posHd m')] @ lp'
                             ⊢ (iwiFamCodT l' lp' li' X' A' N' D' Ot' C' c')[llift (lsingle (posHd m'))] ≈ Y @ iwiL l' lp' li' ] ->
                  [ G ; Γ ,, d[lsingle (posHd m)] @ lp
                             ⊢ (iwiFamCodT l lp li X A N D Ot C c)[llift (lsingle (posHd m))] ≈ Y @ iwiL l lp li ]).
    { intros Y HY. eapply geq_ty_trans; [exact Ec |].
      refine (geq_ty_ctxconv _ (lequiv_sym _ _ _ Hllp) HΓd _).
      - eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ Ed) | exact (lequiv_sym _ _ _ Hllp)].
      - eapply geq_ty_lconv; [exact HY | exact Hml']. }
    pose proof (kw_tmred_succ Hk) as Rk. pose proof (kw_tmred_succ Hk') as Rk'.
    pose proof (pc_hd G Γ k k' m m' Hk Hk' Hmm) as Phd.
    apply (wsp_succ G Γ l' lp' li' X' A' N' D' Ot' C' (flipD ix) (flipD dm) (iflipP pd) yR' d' c' k' m' cs' cs w' w).
    + exact Hk'.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs' | exact ES] | exact Hml2].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs | exact ES] | exact Hml2].
    + exact Hwh'.
    + exact Hwh.
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Heq | exact ES] | exact Hml2].
    + intros pa pb PA PB qa qb QA QB Hpa Hpb Hqa Hqb HPA HPB HQA HQB.
      apply WhRel_sym. eapply WhRel_conv; [| exact (geq_ty_sound GH) | exact Hml].
      exact (Hfst qa qb QA QB pa pb PA PB
               (lequiv_trans _ _ _ _ Hqa Hml) (lequiv_trans _ _ _ _ Hqb Hml)
               (lequiv_trans _ _ _ _ Hpa Hml) (lequiv_trans _ _ _ _ Hpb Hml)
               (MA _ HQA) (MB _ HQB) (MA _ HPA) (MB _ HPB)).
    + intros pa pb PA PB qa qb QA QB Hpa Hpb Hqa Hqb HPA HPB HQA HQB y' y Hyy
        pa2 pb2 PA3 PB3 qa2 qb2 QA3 QB3 Hpa2 Hpb2 Hqa2 Hqb2 HPA3 HPB3 HQA3 HQB3.
      pose proof (HYR _ _ Phd y y' Hyy) as Hy0.
      pose proof (HIX0 _ _ Phd y y' Hy0) as Ec0.
      pose proof (IWi_ty_eq ge_typeof ge_notV HE Ec0) as ET0.
      pose proof (lequiv_sym _ _ _ Hllp) as Hllp'.
      exact (IHapp qa qb QA QB pa pb PA PB
               (lequiv_trans _ _ _ _ Hqa Hml) (lequiv_trans _ _ _ _ Hqb Hml)
               (lequiv_trans _ _ _ _ Hpa Hml) (lequiv_trans _ _ _ _ Hpb Hml)
               (MA _ HQA) (MB _ HQB) (MA _ HPA) (MB _ HPB) y y' Hy0
               qa2 qb2 QA3 QB3 pa2 pb2 PA3 PB3
               (lequiv_trans _ _ _ _ Hqa2 Hllp') (lequiv_trans _ _ _ _ Hqb2 Hml)
               (lequiv_trans _ _ _ _ Hpa2 Hllp') (lequiv_trans _ _ _ _ Hpb2 Hml)
               (MD _ HQA3) (MC _ HQB3) (MD _ HPA3) (MC _ HPB3)
               l' lp' li' X' A' N' D' Ot' C' c'[lsingle2 (posHd m') y'] Hy ET0 (HIX _ _ Phd y y' Hy0)).
    + intros pa pb PA PB qa qb QA QB Hpa Hpb Hqa Hqb HPA HPB HQA HQB.
      refine (IHsnd qa qb QA QB pa pb PA PB
               (lequiv_trans _ _ _ _ Hqa Hml) (lequiv_trans _ _ _ _ Hqb Hml)
               (lequiv_trans _ _ _ _ Hpa Hml) (lequiv_trans _ _ _ _ Hpb Hml)
               (MA _ HQA) (MB _ HQB) (MA _ HPA) (MB _ HPB) l' lp' li' X' A' N' D' Ot' C'
               (fun p => yR' (posTl m' p)) (posMvT m' d') (posMv2 m' c') m'
               Hy Hmm HmmW _ (IWiPosGeq_tl HP Hk Hk') _ _ _).
      * rewrite <- !iwiFamT_mv. exact (dvecMv_eqty ge_typeof ge_notV ge_compt Hm Hm' Em HF1w HF1).
      * intros p p' Hpc y y' H. exact (HYR _ _ (pc_tl G Γ k k' m m' p p' Hk Hk' Hpc) y y' H).
      * intros p p' Hpc y y' H ρ. rewrite !posMv2_single2 by assumption.
        exact (HIX _ _ (pc_tl G Γ k k' m m' p p' Hk Hk' Hpc) y y' H ρ).
      * intros p p' Hpc y y' H. rewrite !posMv2_single2 by assumption.
        exact (HIX0 _ _ (pc_tl G Γ k k' m m' p p' Hk Hk' Hpc) y y' H).
  - intros G Γ l lp li X A N D Ot C ix dm pd yR d c k ν cs cs' Hk Hν Hne l' lp' li' X' A' N' D' Ot' C' yR' d' c' k'
      Hy Hkk _ HF _ _ _ _.
    pose proof (IWiFlip_lv Hy) as Hml. pose proof (lequiv_sym _ _ _ Hml) as Hml'.
    destruct (NatRel_inv_ne Hkk Hk (gne_tm_whne_l Hν)) as (ν' & Hk' & Hνν).
    apply (wsp_ne G Γ l' lp' li' X' A' N' D' Ot' C' (flipD ix) (flipD dm) (iflipP pd) yR' d' c' k' ν' cs' cs);
      [exact Hk' | eapply gne_tm_trans; [apply gne_tm_sym|]; exact Hνν |].
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Eν.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hk) as Ek.
    pose proof (fin_stab_eqty Ek HF) as HFν.
    assert (EV : [ G ; Γ ⊢g tyDVec (iwiL l lp li) ν (iwiFamT l lp li X A N D Ot C d c)
                    ≅ tyDVec (iwiL l' lp' li') ν' (iwiFamT l' lp' li' X' A' N' D' Ot' C' d' c') @ iwiL l lp li ]).
    { apply eqty_dvec; [exact (compt_notV _ ge_compt) | exact Hml' | exact (eqtm_wf_l ge_typeof Eν) | exact Eν
                       | exact (eqty_wf_l ge_typeof HFν) | exact HFν]. }
    apply (NeRel_lconv _ _ _ _ _ _ Hml).
    eapply NeRel_conv2; [exact EV | exact EV |].
    apply NeRel_flip; exact Hne.
Qed.

End IWiFlip.

(** ** Indexed [M], flipped (M18b)

    By induction on the depth, along both sides' data ([MSide] and its
    flip [MSide_flip]): the generic clauses swap, [out]'s observations
    flip by [SigRel_flip] and, in its codomain, [PiRel_flip], whose
    codomain is the induction hypothesis on the two sides' children,
    moved back by [SigRel_dir]/[PiRel_dir]. *)
Section MFlip.

(** [out]'s children's functions, at one shape. *)
Definition MKidRel n G Γ l1 l2 li (X A B : ty) (C : tm) r1 r2 ri (X' A' B' : ty) (C' : tm)
    (shR : MShRel G Γ) (posR : MPosRel G Γ) (m m' : tm) (ρ : kwk G Γ) (a a' : tm) : tm -> tm -> Prop :=
  PiRel (kw_G ρ) (kw_Δ ρ) l2 (mlvl l1 l2 li) r2 (mlvl r1 r2 ri)
    (ktyl ρ B[llift (lsingle m)])[lsingle a] (ktyll ρ (mKidTy l1 l2 li X A B C m))[llift (lsingle a)]
    (ktyl ρ B'[llift (lsingle m')])[lsingle a'] (ktyll ρ (mKidTy r1 r2 ri X' A' B' C' m'))[llift (lsingle a')]
    (fun ρ' => posR (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' a'))
    (fun ρ' p p' _ =>
       MRn n (kw_G ρ') (kw_Δ ρ')
         l1 l2 li (kty (kw_comp ρ ρ') X) (ktyl (kw_comp ρ ρ') A) (ktyll (kw_comp ρ ρ') B)
         (ktmlll (kw_comp ρ ρ') C)
         r1 r2 ri (kty (kw_comp ρ ρ') X') (ktyl (kw_comp ρ ρ') A') (ktyll (kw_comp ρ ρ') B')
         (ktmlll (kw_comp ρ ρ') C')
         (fun ρ'' => shR (kw_comp (kw_comp ρ ρ') ρ''))
         (fun ρ'' => posR (kw_comp (kw_comp ρ ρ') ρ''))
         (ktmlll (kw_comp ρ ρ') C)[lsingle3 (ktm (kw_comp ρ ρ') m) (ktm ρ' a) p]
         (ktmlll (kw_comp ρ ρ') C')[lsingle3 (ktm (kw_comp ρ ρ') m') (ktm ρ' a') p']).

Definition MFlipAt n := forall G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m',
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR -> nftm m -> nftm m' ->
  (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) ->
  forall t t', MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t' t ->
    MRn n G Γ r1 r2 ri X' A' B' C' l1 l2 li X A B C (mflipS shR) (mflipP posR) m' m t t'.

Lemma MPi_flip n (IH : MFlipAt n) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m'}
    (HM : MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR) (Nm : nftm m) (Nm' : nftm m')
    (I : forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) (ρ : kwk G Γ) a a' (ha : shR ρ (ktm ρ m) (ktm ρ m') a a') u u' :
  MKidRel n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' ρ a a' u' u ->
  MKidRel n G Γ r1 r2 ri X' A' B' C' l1 l2 li X A B C (mflipS shR) (mflipP posR) m' m ρ a' a u u'.
Proof using EL.
  pose proof (MSide_flip HM) as HMf.
  pose proof (ms_geq HM) as HG.
  pose proof HG as (H1 & H2 & H3 & (W1 & W2 & Wi & _) & _).
  pose proof (lequiv_sym _ _ _ H2) as H2'.
  pose proof (lequiv_wf_r _ _ _ H2) as W2'.
  assert (Hm : lequiv (gL G) (mlvl r1 r2 ri) (mlvl l1 l2 li))
    by (apply lequiv_mlvl; apply lequiv_sym; assumption).
  unfold MKidRel. rewrite !kw_B_single, !kw_mKid. rewrite !mKid_single by kw_nf.
  intros Y.
  pose proof (ms_gBa HM ρ _ _ a a' (I ρ) ha) as GB.
  pose proof (ms_gBa HMf ρ _ _ a' a (I ρ) ha) as GBf.
  pose proof (geq_ty_sound GB) as DB.
  pose proof (eqty_wf_l ge_typeof DB) as HB. pose proof (eqty_wf_r ge_typeof DB) as HB'.
  pose proof (PiRel_flip (kw_lequiv ρ H2') (kw_lequiv ρ Hm) HB HB' u u' Y) as Y'.
  assert (HBr : [ kw_G ρ ; kw_Δ ρ ⊢g (ktyll ρ B')[lsingle2 (ktm ρ m') a'] @ r2 ])
    by (eapply wft_lconv; [exact HB' | exact (kw_lequiv ρ H2')]).
  assert (HBl : [ kw_G ρ ; kw_Δ ρ ⊢g (ktyll ρ B)[lsingle2 (ktm ρ m) a] @ r2 ])
    by (eapply wft_lconv; [exact HB | exact (kw_lequiv ρ H2')]).
  pose proof (ext_wf_g HBr (kw_lwf ρ W2')) as HΔB.
  pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ (ms_geq HMf)) HΔB) (ms_gCa HMf ρ _ _ a' a (I ρ) ha)) as K.
  pose proof (geq_ty_sound (geq_ty_pi (kw_lequiv ρ H2') (kw_lequiv ρ Hm) HBr GBf K)) as DP.
  refine (PiRel_dir (kw_lwf ρ W2') HBr HBl HBl GBf GBf K K
            (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ DP) DP) _ _ u u' Y').
  - intros ρ' t t'. reflexivity.
  - intros ρ' p p' hp hp' v v'. split; intros Z.
    + destruct (MSide_child ρ ρ' a a' p' p HM Nm Nm' I ha hp) as (N1 & N2 & Ic).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MSide_kw (kw_comp ρ ρ') HM) N1 N2 Ic _ _ Z).
    + destruct (MSide_child ρ ρ' a' a p p' HMf Nm' Nm I ha hp') as (N1 & N2 & Ic).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MSide_kw (kw_comp ρ ρ') HMf) N1 N2 Ic _ _ Z).
Qed.

(** The observations, given the children's. *)
Lemma MObs_flip n (IH : MFlipAt n) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m'}
    (HM : MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR) (Nm : nftm m) (Nm' : nftm m')
    (I : forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) t t' :
  MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t' t ->
  MObs (MRn n) G Γ r1 r2 ri X' A' B' C' l1 l2 li X A B C (mflipS shR) (mflipP posR) m' m t t'.
Proof using EL.
  intros Ht. pose proof (ms_geq HM) as HG; pose proof (MSide_flip HM) as HMf.
  pose proof HG as (H1 & H2 & H3 & (W1 & W2 & Wi & _) & _).
  assert (Hm : lequiv (gL G) (mlvl r1 r2 ri) (mlvl l1 l2 li))
    by (apply lequiv_mlvl; apply lequiv_sym; assumption).
  intros k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann'.
  specialize (Ht k1' k2' ki' X1' A1' B1' C1' j1' k1 k2 ki X1 A1 B1 C1 j1 Ann' Ann).
  pose proof (lequiv_sym _ _ _ H1) as H1'.
  pose proof (lequiv_wf_r _ _ _ H1) as W1'.
  destruct (MSide_root HM Nm Nm' I) as (_ & EA & _).
  destruct (MSide_root HMf Nm' Nm I) as (_ & EAf & EBf & ECf).
  pose proof (geq_ty_sound EA) as DA.
  pose proof (SigRel_flip H1' Hm (eqty_wf_l ge_typeof DA) (eqty_wf_r ge_typeof DA) _ _ Ht) as Ht'.
  pose proof (M_outB_geq (ms_geq HMf) EBf ECf) as K.
  pose proof (geq_ty_sound EAf) as DAf.
  pose proof (eqty_wf_l ge_typeof DAf) as HAf. pose proof (eqty_wf_r ge_typeof DAf) as HAf'.
  pose proof (geq_ty_sound (geq_ty_sig H1' Hm HAf EAf K)) as DS.
  refine (SigRel_dir W1' HAf HAf' HAf' EAf EAf K K (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ DS) DS)
            _ _ _ _ Ht').
  - intros ρ v v'. reflexivity.
  - intros ρ a a' ha ha' v v'. split; intros Z.
    + exact (MPi_flip n IH HM Nm Nm' I ρ a' a ha v v' Z).
    + exact (MPi_flip n IH HMf Nm' Nm I ρ a a' ha' v' v Z).
Qed.

Lemma MRn_flip n : MFlipAt n.
Proof using EL.
  induction n as [|n IH]; intros G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m' HM Nm Nm' I t t' Ht.
  all: pose proof (ms_geq HM) as HG.
  all: pose proof HG as (H1 & H2 & H3 & (W1 & W2 & Wi & _) & _).
  all: assert (Hm : lequiv (gL G) (mlvl r1 r2 ri) (mlvl l1 l2 li))
         by (apply lequiv_mlvl; apply lequiv_sym; assumption).
  all: destruct Ht as [(w & w' & R1 & R2 & Wh & Wh' & E1 & E2) Ht]; split;
    [ exists w', w; refine (conj _ (conj _ (conj Wh' (conj Wh (conj _ _)))));
      [ eapply tmred_lconv; [exact R2 | exact Hm] | eapply tmred_lconv; [exact R1 | exact Hm]
      | eapply geq_tm_lconv; [apply geq_tm_sym, E2 | exact Hm]
      | eapply geq_tm_lconv; [apply geq_tm_sym, E1 | exact Hm] ] |].
  1: exact Logic.I.
  intros ρ. exact (MObs_flip n IH (MSide_kw ρ HM) ltac:(kw_nf) ltac:(kw_nf) (MIdx_kw ρ I) _ _ (Ht ρ)).
Qed.

End MFlip.

(** ** Symmetry *)

Lemma LR_sym_step n : (forall m, m < n -> Psym m) -> Psym n.
Proof using EL VL.
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
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN
                     domAd IHdom arAd HR
                 | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                     HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                     widxAd IHwidx Hwisym Hwistr wdomAd IHwdom warAd wotAd wchAd wixAd HR
                 | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                     Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                     HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd IHvidx Hvisym Hvistr vdomAd IHvdom varAd votAd vpdAd IHvpd vpdE vpdMon vchAd vgC vixAd HR].
  - eapply LRnat; eauto.
    intros t t'; unfold flipR; rewrite (HR t' t); apply NatRel_flip.
  - assert (Hm : lmeasure l2 = lmeasure l1) by (eapply lequiv_measure; eauto).
    eapply (LRU n (LRbelow n) G Γ T' T l l2 l1).
    + eapply lequiv_trans; [exact Hl | apply lequiv_suc, lequiv_sym, Hl2].
    + solve [apply lequiv_sym; assumption].
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
  - (* Wf *)
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'. pose proof (lequiv_wf_l _ _ _ Hl2) as W2.
    assert (HA'2 : [ G ; Γ ⊢g A' @ l2 ]) by exact (lconv_ty HA' Hl2').
    assert (HAA' : [ G ; Γ ⊢ A' ≈ A @ l2 ]) by exact (geq_ty_lconv (geq_ty_sym HAA) Hl2).
    assert (HNN' : [ G ; Γ ,, A' @ l2 ⊢ N' ≈ N : tyNat @ lzero ]).
    { eapply geq_tm_ctxconv; [apply geq_ty_sound, HAA | exact Hl2' | apply ext_wf_g; [exact HA'2 | exact W2] |].
      now apply geq_tm_sym. }
    assert (Hy : WfFlipHyps G Γ l1 A N domR l2 A' N') by exact (conj Hl2 (conj HA (conj HAA (conj HNN arAd)))).
    assert (Hy' : WfFlipHyps G Γ l2 A' N' (flipD domR) l1 A N).
    { refine (conj Hl2' (conj HA'2 (conj HAA' (conj HNN' _)))).
      intros ρ x y h. apply NatRel_sym, arAd, h. }
    eapply (LRwf n (LRbelow n) G Γ T' T l l2 l1 A' A N' N (flipD domR)).
    + exact (lequiv_trans _ _ _ _ Hl Hl2').
    + exact Hl2'.
    + exact W2.
    + exact HT'.
    + exact HT.
    + exact HA'2.
    + exact (lconv_ty HA Hl2').
    + exact (ctx_lvl_tm HA' Hl2' HNt').
    + exact (ctx_lvl_tm HA Hl2' HNt).
    + exact HAA'.
    + exact HNN'.
    + intros ρ. eapply LR_lconv; [exact (IHdom ρ) | exact (kw_lequiv ρ Hl2)].
    + intros ρ a a' h. apply NatRel_sym, arAd, h.
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split; intros X.
      * exact (proj1 WfRel_flip_all _ _ _ _ _ _ _ _ X l2 A' N' Hy).
      * exact (proj1 WfRel_flip_all _ _ _ _ _ _ _ _ X l1 A N Hy').
  - (* ∥·∥: the carrier flipped, the relation read on its diagonal *)
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'.
    assert (HA' : [ G ; Γ ⊢g A' @ l2 ]) by exact (lconv_ty (eqty_wf_r ge_typeof (geq_ty_sound HAA)) Hl2').
    assert (HAA' : [ G ; Γ ⊢ A' ≈ A @ l2 ]) by exact (geq_ty_lconv (geq_ty_sym HAA) Hl2).
    eapply (LRsq n (LRbelow n) G Γ T' T l l2 l1 A' A (flipR RQ)).
    + exact (lequiv_trans _ _ _ _ Hl Hl2').
    + exact Hl2'.
    + exact (lequiv_wf_l _ _ _ Hl2).
    + exact HT'.
    + exact HT.
    + exact HA'.
    + exact HAA'.
    + exact (LR_lconv _ _ _ _ _ _ _ _ _ IHRQ Hl2).
    + unfold flipR; intros x y H; exact (Hqs _ _ H).
    + unfold flipR; intros x y z H1 H2; exact (Hqt _ _ _ H2 H1).
    + intros t t'; unfold flipR at 1; rewrite (HR t' t).
      rewrite (SqRel_conv (RA := RQ) (RA' := flipR RQ) Hl2' HA HAA (fun a => iff_refl _) t' t).
      split; apply SqRel_sym.
  - (* IWf *)
    pose proof (lequiv_sym _ _ _ Hl2) as Hl2'. pose proof (lequiv_sym _ _ _ Hwli2) as Hli2'.
    pose proof (lequiv_wf_l _ _ _ Hl2) as W2. pose proof (lequiv_wf_l _ _ _ Hwli2) as Wi2.
    pose proof (geq_ty_sound HwXX) as EX. pose proof (geq_ty_sound HwAA) as EA.
    pose proof (geq_tm_sound HwNN) as EN. pose proof (geq_tm_sound HwOO) as EO.
    pose proof (geq_tm_sound HwCC) as EC. pose proof (geq_tm_sound Hwmm) as Em.
    assert (HE : IWfEq (G := G) (i := ge_layer) Γ wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC').
    { apply IWfEq_intro; [exact Hl2' | exact Hli2' | exact EX | exact EA | exact EN | exact EO | exact EC
        | exact Hw | exact Hwwi | exact HwX | exact HwA | exact HwN | exact HwO | exact HwC
        | exact HwX' | exact HwA' | exact (eqtm_wf_r ge_typeof EN) | exact (eqtm_wf_r ge_typeof EO)
        | exact (eqtm_wf_r ge_typeof EC)]. }
    assert (Hy : IWfFlipHyps G Γ wl1 wli1 wX wA wN wO wC widxR wdomR wl2 wli2 wX' wA' wN' wO' wC').
    { refine (conj HE (conj Hwisym (conj Hwistr (conj _ (conj warAd (conj wotAd (conj wchAd
                (conj (conj HwXX (conj HwAA (conj HwNN (conj HwOO HwCC)))) _)))))))).
      - intros ρ a a' h.
        destruct (escape_tm _ _ _ _ _ _ _ _ (wdomAd ρ) a a' h) as (Ha & Ha' & Haa).
        exact (conj Ha (conj Ha' (geq_tm_sound Haa))).
      - intros ρ x y h. exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (widxAd ρ) x y h))). }
    pose proof (IWf_ty_eq ge_typeof ge_notV HE Em) as ET.
    assert (Em' : [ G ; Γ ⊢g wm' ≅ wm : wX' @ wli2 ]).
    { eapply eqtm_lconv; [eapply eqtm_conv; [apply eqtm_sym, Em | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ EX)] | exact Hwli2]. }
    pose proof (IWf_ty_eq ge_typeof ge_notV (IWfEq_sym ge_typeof ge_notV HE) Em') as ET'.
    assert (HA'2 : [ G ; Γ ⊢g wA' @ wl2 ]) by exact (lconv_ty HwA' Hl2').
    assert (HA2 : [ G ; Γ ⊢g wA @ wl2 ]) by exact (lconv_ty HwA Hl2').
    assert (HΓA' : [ G ; Γ ,, wA' @ wl2 ⊢g ]) by exact (ext_wf_g HA'2 W2).
    assert (HΓA : [ G ; Γ ,, wA @ wl2 ⊢g ]) by exact (ext_wf_g HA2 W2).
    assert (HN'2 : [ G ; Γ ,, wA' @ wl2 ⊢g wN' : tyNat @ lzero ]) by exact (ctx_lvl_tm HwA' Hl2' HwN').
    assert (HN2 : [ G ; Γ ,, wA @ wl2 ⊢g wN : tyNat @ lzero ]) by exact (ctx_lvl_tm HwA Hl2' HwN).
    assert (HΓAN' : [ G ; Γ ,, wA' @ wl2 ,, tyFin wN' @ lzero ⊢g ])
      by (apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact HN'2] | exact I]).
    assert (HΓAN : [ G ; Γ ,, wA @ wl2 ,, tyFin wN @ lzero ⊢g ])
      by (apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact HN2] | exact I]).
    assert (EX1 : [ G ; Γ ,, wA' @ wl2 ⊢g wX⟨↑⟩ ≅ wX'⟨↑⟩ @ wli1 ])
      by exact (wk1_eqty G ge_layer ge_typeof _ _ _ _ _ _ HΓA' EX).
    assert (EX2 : [ G ; Γ ,, wA' @ wl2 ,, tyFin wN' @ lzero ⊢g wX⟨↑⟩⟨↑⟩ ≅ wX'⟨↑⟩⟨↑⟩ @ wli1 ])
      by exact (wk1_eqty G ge_layer ge_typeof _ _ _ _ _ _ HΓAN' EX1).
    assert (HG' : IWfGeq G Γ wl2 wli2 wX' wX wA' wA wN' wN wO' wO wC' wC).
    { refine (conj _ (conj _ (conj _ (conj _ _)))).
      - exact (geq_ty_lconv (geq_ty_sym HwXX) Hwli2).
      - exact (geq_ty_lconv (geq_ty_sym HwAA) Hl2).
      - eapply geq_tm_ctxconv; [exact EA | exact Hl2' | exact HΓA' |]. now apply geq_tm_sym.
      - eapply geq_tm_lconv; [| exact Hwli2]. eapply geq_tm_conv; [| exact EX1].
        eapply geq_tm_ctxconv; [exact EA | exact Hl2' | exact HΓA' |]. now apply geq_tm_sym.
      - eapply geq_tm_lconv; [| exact Hwli2]. eapply geq_tm_conv; [| exact EX2].
        eapply geq_tm_ctxconv2; [exact EA | exact Hl2' | exact HΓAN' |].
        eapply geq_tm_ctxconv; [| exact (lequiv_refl (gL G) lzero I) | |].
        + apply eqty_fin; [exact ge_notV | exact EN].
        + apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact (eqtm_wf_r ge_typeof EN)] | exact I].
        + now apply geq_tm_sym. }
    pose proof (IWfFlipHyps_flip Hy HG') as Hy'.
    destruct HG' as (GX' & GA' & GN' & GO' & GC').
    eapply (LRiwf n (LRbelow n) G Γ T' T l wl2 wli2 wl1 wli1 wX' wX wA' wA wN' wN wO' wO wC' wC wm' wm
              (flipD widxR) (flipD wdomR)).
    + exact (lequiv_trans _ _ _ _ Hl (lequiv_sym _ _ _ (lequiv_max _ _ _ _ _ Hl2 Hwli2))).
    + exact Hl2'.
    + exact Hli2'.
    + exact W2.
    + exact Wi2.
    + exact HT'.
    + exact HT.
    + exact (lconv_ty HwX' Hli2').
    + exact (lconv_ty HwX Hli2').
    + exact HA'2.
    + exact HA2.
    + exact HN'2.
    + exact HN2.
    + eapply wf_lconv; [exact (ctx_lvl_tm HwA' Hl2' HwO') | exact Hwli2].
    + eapply wf_lconv; [exact (ctx_lvl_tm HwA Hl2' HwO) | exact Hwli2].
    + eapply wf_lconv; [| exact Hwli2].
      exact (mv_tm ge_typeof (stab2_lsub ge_typeof (eqty_refl _ _ _ _ _ HwA') Hl2' HΓAN') HwC').
    + eapply wf_lconv; [| exact Hwli2].
      exact (mv_tm ge_typeof (stab2_lsub ge_typeof (eqty_refl _ _ _ _ _ HwA) Hl2' HΓAN) HwC).
    + eapply wf_lconv; [exact Hwm' | exact Hwli2].
    + eapply wf_lconv; [exact Hwm | exact Hwli2].
    + exact GX'.
    + exact GA'.
    + exact GN'.
    + exact GO'.
    + exact GC'.
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Hwmm | exact EX] | exact Hwli2].
    + intros ρ. eapply LR_lconv; [exact (IHwidx ρ) | exact (kw_lequiv ρ Hwli2)].
    + unfold flipD, flipR; intros ρ x y h; exact (Hwisym ρ _ _ h).
    + unfold flipD, flipR; intros ρ x y z h1 h2; exact (Hwistr ρ _ _ _ h2 h1).
    + intros ρ. eapply LR_lconv; [exact (IHwdom ρ) | exact (kw_lequiv ρ Hl2)].
    + intros ρ a a' h. apply NatRel_sym, warAd, h.
    + intros ρ a a' h. exact (wotAd ρ a' a h).
    + intros ρ a a' h p p' Hp. exact (wchAd ρ a' a h p' p (PosRel_sym Hp)).
    + intros ρ. exact (wixAd ρ).
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split; intros Y.
      * exact (proj1 IWfRel_flip_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ _ _ _ Hy ET wixAd).
      * exact (proj1 IWfRel_flip_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ _ _ _ Hy' ET' wixAd).
  - (* M: the two sides swap, the relations flip *)
    pose proof (MSide_of_LR Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HmX HmA HmB HmC HmXX HmAA HmBB HmCC
                  midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon) as HM.
    pose proof (MSide_flip HM) as HMf.
    pose proof (ms_geq HMf) as (Hf1 & Hf2 & Hf3 & (Wf1 & Wf2 & Wfi & HfX & HfA & HfB & HfC) & GX & GA & GB & GC).
    pose proof (lequiv_sym _ _ _ Hmr1) as Hmr1'. pose proof (lequiv_sym _ _ _ Hmr2) as Hmr2'.
    pose proof (lequiv_sym _ _ _ Hmri) as Hmri'.
    pose proof (MSig_lconv ge_typeof ge_notV (conj Hmw1 (conj Hmw2 (conj Hmwi (conj HmX (conj HmA (conj HmB HmC))))))
                  Hmr1' Hmr2' Hmri') as (_ & _ & _ & HrX & HrA & HrB & HrC).
    pose proof (wf_tm_nf Hmm) as Nm. pose proof (wf_tm_nf Hmm') as Nm'.
    eapply (LRm n (LRbelow n) G Γ T' T l mr1 mr2 mri ml1 ml2 mli mX' mX mA' mA mB' mB mC' mC mm' mm
              (flipD midxR) (mflipS mshR) (mflipP mposR)).
    + exact (lequiv_trans _ _ _ _ Hl (lequiv_mlvl Hmr1' Hmr2' Hmri')).
    + exact Hmr1'.
    + exact Hmr2'.
    + exact Hmri'.
    + exact Wf1.
    + exact Wf2.
    + exact Wfi.
    + exact HT'.
    + exact HT.
    + exact HfX.
    + exact HrX.
    + exact HfA.
    + exact HrA.
    + exact HfB.
    + exact HrB.
    + exact HfC.
    + exact HrC.
    + eapply wf_lconv; [exact Hmm' | exact Hmri].
    + eapply wf_lconv; [exact Hmm | exact Hmri].
    + exact GX.
    + exact GA.
    + exact GB.
    + exact GC.
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Hmmm | exact (geq_ty_sound HmXX)] | exact Hmri].
    + intros ρ. eapply LR_lconv; [exact (IHmidx ρ) | exact (kw_lequiv ρ Hmri)].
    + intros ρ x x' h. eapply LR_lconv; [exact (IHmsh ρ x' x h) | exact (kw_lequiv ρ Hmr1)].
    + intros ρ x x' a a' h ha. eapply LR_lconv; [exact (IHmpos ρ x' x a' a h ha) | exact (kw_lequiv ρ Hmr2)].
    + exact (ms_ch HMf).
    + exact (ms_gB HMf).
    + exact (ms_gC HMf).
    + exact (ms_gCa HMf).
    + exact (ms_imon HMf).
    + exact (ms_shmon HMf).
    + exact (ms_posmon HMf).
    + intros ρ. exact (mixAd ρ).
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split; intros Y k.
      * exact (MRn_flip k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Nm Nm' mixAd _ _ (Y k)).
      * exact (MRn_flip k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMf Nm' Nm mixAd _ _ (Y k)).
  - (* IWi: as IWf, with the domains' relation flipped by swapping its sides *)
    pose proof (lequiv_sym _ _ _ Hvl2) as Hl2'. pose proof (lequiv_sym _ _ _ Hvlp2) as Hlp2'.
    pose proof (lequiv_sym _ _ _ Hvli2) as Hli2'.
    pose proof (lequiv_wf_l _ _ _ Hvl2) as W2. pose proof (lequiv_wf_l _ _ _ Hvlp2) as Wp2.
    pose proof (lequiv_wf_l _ _ _ Hvli2) as Wi2.
    pose proof (geq_ty_sound HvXX) as EX. pose proof (geq_ty_sound HvAA) as EA.
    pose proof (geq_tm_sound HvNN) as EN. pose proof (geq_ty_sound HvDD) as ED.
    pose proof (geq_tm_sound HvOO) as EO. pose proof (geq_tm_sound HvCC) as EC. pose proof (geq_tm_sound Hvmm) as Em.
    assert (HE : IWiEq (G := G) (i := ge_layer) Γ vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC').
    { apply IWiEq_intro; [exact Hl2' | exact Hlp2' | exact Hli2' | exact EX | exact EA | exact EN | exact ED | exact EO
        | exact EC | exact Hvw | exact Hvwp | exact Hvwi | exact HvX | exact HvA | exact HvN | exact HvD | exact HvO
        | exact HvC | exact HvX' | exact HvA' | exact (eqtm_wf_r ge_typeof EN) | exact (eqty_wf_r ge_typeof ED)
        | exact (eqtm_wf_r ge_typeof EO) | exact (eqtm_wf_r ge_typeof EC)]. }
    assert (HG : IWiGeq G Γ vl1 vlp1 vli1 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC')
      by exact (conj HvXX (conj HvAA (conj HvNN (conj HvDD (conj HvOO HvCC))))).
    assert (Hy : IWiFlipHyps G Γ vl1 vlp1 vli1 vX vA vN vD vO vC vidxR vdomR vpdR vl2 vlp2 vli2 vX' vA' vN' vD' vO' vC').
    { refine (conj HE (conj Hvisym (conj Hvistr (conj _ (conj varAd (conj votAd (conj vpdE (conj vpdMon
                (conj vchAd (conj _ (conj HG _))))))))))).
      - intros ρ a a' h.
        destruct (escape_tm _ _ _ _ _ _ _ _ (vdomAd ρ) a a' h) as (Ha & Ha' & Haa).
        exact (conj Ha (conj Ha' (geq_tm_sound Haa))).
      - intros ρ a a' h p p' Hp.
        destruct (escape_ty _ _ _ _ _ _ _ _ (vpdAd ρ a a' h p p' Hp)) as (HDa & _ & GDa).
        exact (conj HDa (conj GDa (vgC ρ a a' h p p' Hp))).
      - intros ρ x y h. exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (vidxAd ρ) x y h))). }
    pose proof (IWi_ty_eq ge_typeof ge_notV HE Em) as ET.
    assert (Em' : [ G ; Γ ⊢g vm' ≅ vm : vX' @ vli2 ]).
    { eapply eqtm_lconv; [eapply eqtm_conv; [apply eqtm_sym, Em | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ EX)]
                         | exact Hvli2]. }
    pose proof (IWi_ty_eq ge_typeof ge_notV (IWiEq_sym ge_typeof ge_notV HE) Em') as ET'.
    pose proof (IWiGeq_flip HE HG) as HG'.
    (* the flipped domains and child indices, from the flipped domains' relation *)
    assert (HgC' : forall (ρ : kwk G Γ) a a', vdomR ρ a' a -> forall p p',
              PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ vN')[lsingle a] (ktml ρ vN)[lsingle a'] p p' ->
              [ kw_G ρ ; kw_Δ ρ ⊢g (ktyll ρ vD')[lsingle2 a p] @ vlp2 ] /\
              [ kw_G ρ ; kw_Δ ρ ⊢ (ktyll ρ vD')[lsingle2 a p] ≈ (ktyll ρ vD)[lsingle2 a' p'] @ vlp2 ] /\
              [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ vD')[lsingle2 a p] @ vlp2
                  ⊢ (ktmlll ρ vC')[llift (lsingle2 a p)] ≈ (ktmlll ρ vC)[llift (lsingle2 a' p')] : (kty ρ vX')⟨↑⟩ @ vli2 ]).
    { intros ρ a a' h p p' Hp. pose proof (PosRel_sym Hp) as Hp'.
      destruct (escape_ty _ _ _ _ _ _ _ _ (vpdAd ρ a' a h p' p Hp')) as (HDa & HD'a & GDa).
      pose proof (lconv_ty HD'a (kw_lequiv ρ Hlp2')) as HD'2.
      refine (conj HD'2 (conj (geq_ty_lconv (geq_ty_sym GDa) (kw_lequiv ρ Hvlp2)) _)).
      assert (HΔ : [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ vD')[lsingle2 a p] @ vlp2 ⊢g ])
        by exact (ext_wf_g HD'2 (kw_lwf ρ Wp2)).
      assert (HΔ1 : [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ vD)[lsingle2 a' p'] @ vlp1 ⊢g ])
        by exact (ext_wf_g HDa (kw_lwf ρ Hvwp)).
      assert (EXk : [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ vD)[lsingle2 a' p'] @ vlp1 ⊢g (kty ρ vX)⟨↑⟩ ≅ (kty ρ vX')⟨↑⟩ @ vli1 ])
        by exact (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΔ1 (kw_eqty ρ EX)).
      refine (geq_tm_ctxconv (geq_ty_sound GDa) (kw_lequiv ρ Hlp2') HΔ _).
      eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, (vgC ρ a' a h p' p Hp') | exact EXk]
                           | exact (kw_lequiv ρ Hvli2)]. }
    pose proof (IWiFlipHyps_flip Hy HG' HgC') as Hy'.
    pose proof (IWiEq_sig_r ge_typeof ge_notV HE) as (_ & _ & _ & HrX' & HrA' & HrN' & HrD' & HrO' & HrC').
    pose proof HE as (_ & _ & _ & HSl & _).
    pose proof (IWiSig_lconv HSl Hl2' Hlp2' Hli2') as (_ & _ & _ & HrX & HrA & HrN & HrD & HrO & HrC).
    destruct HG' as (GX' & GA' & GN' & GD' & GO' & GC').
    eapply (LRiwi n (LRbelow n) G Γ T' T l vl2 vlp2 vli2 vl1 vlp1 vli1 vX' vX vA' vA vN' vN vD' vD vO' vO vC' vC vm' vm
              (flipD vidxR) (flipD vdomR) (iflipP vpdR)).
    + exact (lequiv_trans _ _ _ _ Hl (IWi_lvl_eq Hl2' Hlp2' Hli2')).
    + exact Hl2'.
    + exact Hlp2'.
    + exact Hli2'.
    + exact W2.
    + exact Wp2.
    + exact Wi2.
    + exact HT'.
    + exact HT.
    + exact HrX'.
    + exact HrX.
    + exact HrA'.
    + exact HrA.
    + exact HrN'.
    + exact HrN.
    + exact HrD'.
    + exact HrD.
    + exact HrO'.
    + exact HrO.
    + exact HrC'.
    + exact HrC.
    + eapply wf_lconv; [exact Hvm' | exact Hvli2].
    + eapply wf_lconv; [exact Hvm | exact Hvli2].
    + exact GX'.
    + exact GA'.
    + exact GN'.
    + exact GD'.
    + exact GO'.
    + exact GC'.
    + eapply geq_tm_lconv; [eapply geq_tm_conv; [apply geq_tm_sym, Hvmm | exact EX] | exact Hvli2].
    + intros ρ. eapply LR_lconv; [exact (IHvidx ρ) | exact (kw_lequiv ρ Hvli2)].
    + unfold flipD, flipR; intros ρ x y h; exact (Hvisym ρ _ _ h).
    + unfold flipD, flipR; intros ρ x y z h1 h2; exact (Hvistr ρ _ _ _ h2 h1).
    + intros ρ. eapply LR_lconv; [exact (IHvdom ρ) | exact (kw_lequiv ρ Hvl2)].
    + intros ρ a a' h. apply NatRel_sym, varAd, h.
    + intros ρ a a' h. exact (votAd ρ a' a h).
    + intros ρ a a' h p p' Hp. eapply LR_lconv; [exact (IHvpd ρ a' a h p' p (PosRel_sym Hp)) | exact (kw_lequiv ρ Hvlp2)].
    + intros ρ a a' p p' y y' h. exact (PosRel_sym (vpdE ρ _ _ _ _ _ _ h)).
    + intros ρ ρ' a a' p p' y y' h. exact (vpdMon ρ ρ' _ _ _ _ _ _ h).
    + intros ρ a a' h p p' y y' hp. exact (vchAd ρ _ _ h _ _ _ _ hp).
    + intros ρ a a' h p p' Hp. exact (proj2 (proj2 (HgC' ρ a a' h p p' Hp))).
    + intros ρ. exact (vixAd ρ).
    + intros t t'; unfold flipR at 1; rewrite (HR t' t); split; intros Y.
      * exact (proj1 IWiRel_flip_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ _ _ _ _ _ Hy ET vixAd).
      * exact (proj1 IWiRel_flip_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ _ _ _ _ _ Hy' ET' vixAd).
Qed.

Theorem LR_sym n : Psym n.
Proof using EL VL.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_sym_step, IHn.
Qed.

Corollary LogRel_sym l G Γ T T' l' R :
  LogRel l G Γ T T' l' R -> LogRel l G Γ T' T l' (flipR R).
Proof using EL VL. apply LR_sym. Qed.

End Symmetry.
