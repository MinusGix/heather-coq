(** * Related local contexts, and transport of validity along them

    With pairs of global substitutions [σ ≈ σ'], a judgment's context
    becomes two contexts [Γ⦃σ⦄] and [Γ⦃σ'⦄].  Validity stays one-sided (at
    the left context); [CtxRel] relates the two contexts entrywise, each
    entry valid over its own side, and transport moves validity between
    related contexts (M2_DESIGN.md, option B). *)
From DeLaM.Validity Require Export Props.

Section CtxRel.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Fixpoint CtxRel (G : gctx) (Γ Γ' : ctx) : Prop :=
  match Γ, Γ' with
  | cnil, cnil => True
  | cvar g, cvar g' => g = g'
  | cext Γ A l, cext Γ' A' l' =>
      CtxRel G Γ Γ' /\ lequiv (gL G) l l' /\ VTy G Γ A A' l /\ VTy G Γ' A' A l'
  | _, _ => False
  end.

Lemma CtxRel_sym G : forall Γ Γ', CtxRel G Γ Γ' -> CtxRel G Γ' Γ.
Proof.
  induction Γ as [| g | Γ IH A l]; intros [| g' | Γ' A' l']; cbn [CtxRel]; try tauto; [congruence|].
  intros (HΓ & Hl & HA & HA'). refine (conj (IH _ HΓ) (conj (lequiv_sym _ _ _ Hl) (conj HA' HA))).
Qed.

(** ** Transport of related substitutions *)

Lemma SubRel_transport G : forall Γ Γ' Δ d d',
  CtxRel G Γ Γ' -> SubRel G Γ' Δ d d' -> SubRel G Γ Δ d d'.
Proof.
  induction Γ as [| g | Γ IH A l]; intros [| g' | Γ' A' l'] Δ d d'; cbn [CtxRel]; try tauto.
  - intros ->; tauto.
  - intros (HΓ & Hl & HA & _) [Ht Hh]. cbn [SubRel].
    pose proof (IH _ _ _ _ HΓ Ht) as Ht'. split; [exact Ht'|].
    pose proof (LRtm_lconv Hh Hl) as Hh'.
    eapply LRtm_irrel_r; [eapply LRtm_irrel_l; [exact Hh' | exact (HA _ _ _ Ht')]|].
    exact (VTy_refl_l HA _ _ _ Ht').
Qed.

Lemma CtxRel_trans G : forall Γ1 Γ2 Γ3, CtxRel G Γ1 Γ2 -> CtxRel G Γ2 Γ3 -> CtxRel G Γ1 Γ3.
Proof.
  induction Γ1 as [| g | Γ1 IH A1 l1]; intros [| g2 | Γ2 A2 l2] [| g3 | Γ3 A3 l3]; cbn [CtxRel];
    try tauto; [congruence|].
  intros (H12 & Hl12 & HA12 & HA21) (H23 & Hl23 & HA23 & HA32).
  refine (conj (IH _ _ H12 H23) (conj (lequiv_trans _ _ _ _ Hl12 Hl23) (conj _ _))).
  - (* [A2 ≈ A3] over [Γ2], moved to [Γ1] *)
    eapply VTy_trans; [exact HA12|].
    intros Δ d d' Hd. apply (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ H12)) in Hd.
    exact (LRty_lconv (HA23 _ _ _ Hd) Hl12).
  - eapply VTy_trans; [exact HA32|].
    intros Δ d d' Hd. apply (SubRel_transport _ _ _ _ _ _ H23) in Hd.
    exact (LRty_lconv (HA21 _ _ _ Hd) (lequiv_sym _ _ _ Hl23)).
Qed.

Lemma VTy_transport {G Γ Γ' T T' l} : CtxRel G Γ Γ' -> VTy G Γ T T' l -> VTy G Γ' T T' l.
Proof.
  intros HΓ H Δ d d' Hd. exact (H _ _ _ (SubRel_transport _ _ _ _ _ _ HΓ Hd)).
Qed.
Lemma VTm_transport {G Γ Γ' t t' T l} : CtxRel G Γ Γ' -> VTm G Γ t t' T l -> VTm G Γ' t t' T l.
Proof.
  intros HΓ H Δ d d' Hd. exact (H _ _ _ (SubRel_transport _ _ _ _ _ _ HΓ Hd)).
Qed.

(** ** Under global weakenings *)

Definition CtxRelG (G : gctx) (Γ Γ' : ctx) : Prop :=
  forall G' γ, gwk_ok γ G' G -> CtxRel G' Γ⟦γ⟧ Γ'⟦γ⟧.

Lemma CtxRelG_sym {G Γ Γ'} : CtxRelG G Γ Γ' -> CtxRelG G Γ' Γ.
Proof. intros H G' γ Hγ. exact (CtxRel_sym _ _ _ (H _ _ Hγ)). Qed.
Lemma CtxRelG_trans {G Γ1 Γ2 Γ3} : CtxRelG G Γ1 Γ2 -> CtxRelG G Γ2 Γ3 -> CtxRelG G Γ1 Γ3.
Proof. intros H1 H2 G' γ Hγ. exact (CtxRel_trans _ _ _ _ (H1 _ _ Hγ) (H2 _ _ Hγ)). Qed.

Lemma CtxRelG_gwk {G Γ Γ' G' γ} : CtxRelG G Γ Γ' -> gwk_ok γ G' G -> CtxRelG G' Γ⟦γ⟧ Γ'⟦γ⟧.
Proof.
  intros H Hγ G'' γ' Hγ'. rewrite !gwa_comp_ctx. exact (H _ _ (gwk_ok_comp Hγ' Hγ)).
Qed.

Lemma VTyG_transport {G Γ Γ' T T' l} : CtxRelG G Γ Γ' -> VTyG G Γ T T' l -> VTyG G Γ' T T' l.
Proof. intros HΓ H G' γ Hγ. exact (VTy_transport (HΓ _ _ Hγ) (H _ _ Hγ)). Qed.
Lemma VTmG_transport {G Γ Γ' t t' T l} : CtxRelG G Γ Γ' -> VTmG G Γ t t' T l -> VTmG G Γ' t t' T l.
Proof. intros HΓ H G' γ Hγ. exact (VTm_transport (HΓ _ _ Hγ) (H _ _ Hγ)). Qed.

(** Constructors. *)
Lemma CtxRelG_nil {G} : CtxRelG G cnil cnil.
Proof. intros G' γ Hγ. now rewrite gwa_cnil. Qed.
Lemma CtxRelG_var {G g} : CtxRelG G (cvar g) (cvar g).
Proof. intros G' γ Hγ. now rewrite gwa_cvar. Qed.
Lemma CtxRelG_ext {G Γ Γ' A A' l l'} :
  CtxRelG G Γ Γ' -> lequiv (gL G) l l' -> VTyG G Γ A A' l -> VTyG G Γ' A' A l' ->
  CtxRelG G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof.
  intros HΓ Hl HA HA' G' γ Hγ. rewrite !gwa_cext; cbn [CtxRel].
  refine (conj (HΓ _ _ Hγ) (conj _ (conj (HA _ _ Hγ) (HA' _ _ Hγ)))).
  now rewrite (proj1 Hγ).
Qed.

(** ** The identity substitution, and escape

    A context related to another one has valid entries, so the identity
    substitution is related to itself there (as [Consequences.SubRel_id]
    obtains from the fundamental theorem), and related contexts escape to
    the generic relation. *)

Lemma SubRel_id_rel {G} : forall Γ Γ', CtxRel G Γ Γ' -> [ G ; Γ ⊢g ] ->
  SubRel G Γ Γ (lshift 0) (lshift 0).
Proof.
  induction Γ as [| g | Γ IH A l]; intros Γ' HR HΓ; cbn [SubRel].
  1-2: refine (conj HΓ (conj _ (conj _ (conj _ _)))); try apply tail_id; intros n; exact I.
  destruct Γ' as [| g' | Γ' A' l']; cbn in HR; try contradiction.
  destruct HR as (HR & _ & HA & _).
  inversion HΓ as [| | ? ? ? ? ? HΓ0 HAw Hl]; subst.
  assert (Hw : wk_step wk_id : (Γ ,, A @ l) ≤ Γ) by (constructor; constructor).
  assert (Hsh : SubRel G Γ (Γ ,, A @ l) (lshift 1) (lshift 1)).
  { eapply SubRel_ext; [| | exact (SubRel_wk _ _ _ _ _ _ _ Hw HΓ (IH _ HR HΓ0))];
      intros n; rewrite llk_lren; cbn; f_equal; lia. }
  cbn [ldrop llk]. split; [exact Hsh|].
  assert (E1 : A[lshift 1] = A⟨↑⟩) by (symmetry; apply ren_as_subst_ty; reflexivity).
  change (LRtm l G (Γ ,, A @ l) A[lshift 1] A[lshift 1] (var 0) (var 0)). rewrite E1.
  apply var0_LRtm; [| exact HΓ].
  pose proof (VTy_refl_l HA _ _ _ Hsh) as X. now rewrite E1 in X.
Qed.

Lemma CtxRel_escape {G} : forall Γ Γ', CtxRel G Γ Γ' -> [ G ; Γ ⊢g ] -> [ G ; Γ' ⊢g ] ->
  geq_ctx G Γ Γ'.
Proof.
  induction Γ as [| g | Γ IH A l]; intros Γ' HR HΓ HΓ';
    destruct Γ' as [| g' | Γ' A' l']; cbn in HR; try contradiction.
  - constructor; exact (ctx_glob _ _ _ HΓ).
  - subst g'. inversion HΓ; subst. constructor; assumption.
  - destruct HR as (HR & Hl & HA & _).
    inversion HΓ as [| | ? ? ? ? ? HΓ0 HAw Hlw]; subst.
    inversion HΓ' as [| | ? ? ? ? ? HΓ0' HAw' Hlw']; subst.
    constructor; [exact (IH _ HR HΓ0 HΓ0') | exact HAw | | exact Hl].
    destruct (HA _ _ _ (SubRel_id_rel _ _ HR HΓ0)) as [R HRA].
    destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (_ & _ & X).
    assert (Hid : forall n, llk (lshift 0) n = var n) by (intros n; cbn; f_equal; lia).
    rewrite (subst_id_ty _ _ (wf_ty_nf HAw) Hid), (subst_id_ty _ _ (wf_ty_nf HAw') Hid) in X. exact X.
Qed.

End CtxRel.

(** ** Level equivalence of syntax (M3_DESIGN.md E6')

    Validity is invariant under [≡ₗ]: related syntax, each side valid on
    its own, is related. From the relation's level invariance. *)

Section LevelEq.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma LRty_leq {l G Γ T1 T2 T3} : LRty l G Γ T1 T2 -> LRty l G Γ T3 T3 -> ty_leq T2 T3 -> LRty l G Γ T1 T3.
Proof. intros [R H] [R3 H3] Ex. exists R. exact (LogRel_leq_ty H H3 Ex). Qed.

Lemma LRtm_leq {l G Γ T T' t1 t2 t3} :
  LRtm l G Γ T T' t1 t2 -> LRtm l G Γ T' T' t3 t3 -> tm_leq t2 t3 -> LRtm l G Γ T T' t1 t3.
Proof.
  intros (R & H & Ht) (R3 & H3 & Ht3) Ex. exists R; split; [exact H|].
  exact (LogRel_leq_tm H H3 (ty_leq_refl _) Ht Ht3 Ex).
Qed.

Lemma VTy_leq {G Γ T T' l} : VTy G Γ T T l -> VTy G Γ T' T' l -> ty_leq T T' -> VTy G Γ T T' l.
Proof.
  intros V V' Ex Δ d d' Hd.
  exact (LRty_leq (V _ _ _ Hd) (V' _ _ _ (SubRel_refl_r Hd)) (subst_leq_ty _ _ _ Ex)).
Qed.

Lemma VTm_leq {G Γ t t' T l} : VTm G Γ t t T l -> VTm G Γ t' t' T l -> tm_leq t t' -> VTm G Γ t t' T l.
Proof.
  intros V V' Ex Δ d d' Hd.
  refine (LRtm_leq (V _ _ _ Hd) (V' _ _ _ (SubRel_refl_r Hd)) _).
  apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl | exact Ex].
Qed.

Lemma VTyG_leq {G Γ T T' l} : VTyG G Γ T T l -> VTyG G Γ T' T' l -> ty_leq T T' -> VTyG G Γ T T' l.
Proof. intros V V' Ex G' γ Hγ. exact (VTy_leq (V _ _ Hγ) (V' _ _ Hγ) (ty_leq_gwa _ _ _ Ex)). Qed.
Lemma VTmG_leq {G Γ t t' T l} : VTmG G Γ t t T l -> VTmG G Γ t' t' T l -> tm_leq t t' -> VTmG G Γ t t' T l.
Proof. intros V V' Ex G' γ Hγ. exact (VTm_leq (V _ _ Hγ) (V' _ _ Hγ) (tm_leq_gwa _ _ _ Ex)). Qed.

Lemma CtxRel_leq G : forall Γ Γ', CtxRel G Γ Γ -> CtxRel G Γ' Γ' -> ctx_leq Γ Γ' -> CtxRel G Γ Γ'.
Proof.
  induction Γ as [| g | Γ IH A l]; intros [| g' | Γ' A' l']; cbn [CtxRel ctx_leq]; try tauto.
  intros (HΓ & Hl & HA & _) (HΓ' & Hl' & HA' & _) (EΓ & EA & El).
  pose proof (IH _ HΓ HΓ' EΓ) as H.
  pose proof (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl) (lequiv_wf_l _ _ _ Hl') El) as Q.
  (* [A'] over [Γ] at [l] *)
  assert (HA'' : VTy G Γ A' A' l)
    by (intros Δ d d' Hd; exact (LRty_lconv (HA' _ _ _ (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ H) Hd)) Q)).
  pose proof (VTy_leq HA HA'' EA) as HAA.
  refine (conj H (conj Q (conj HAA _))).
  intros Δ d d' Hd.
  exact (LRty_lconv (VTy_sym HAA _ _ _ (SubRel_transport _ _ _ _ _ _ H Hd))
           (lequiv_sym _ _ _ Q)).
Qed.

Lemma CtxRelG_leq {G Γ Γ'} : CtxRelG G Γ Γ -> CtxRelG G Γ' Γ' -> ctx_leq Γ Γ' -> CtxRelG G Γ Γ'.
Proof.
  intros H H' Ex G' γ Hγ. apply CtxRel_leq; [exact (H _ _ Hγ) | exact (H' _ _ Hγ)|].
  destruct γ; cbn; auto; apply (proj1 (proj2 (proj2 leq_gren_all))), Ex.
Qed.

End LevelEq.
