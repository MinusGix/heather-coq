(** * Validity of strict equality (M10_DESIGN.md, M10a)

    Formation of [sEq] and [sEmpty], [srefl], [sEmpty]'s eliminator, and
    proof irrelevance at both. The term relations only ask for weak-head
    normal forms ([SEqRel]) or self-related neutrals ([SEmptyRel]), so
    irrelevance is immediate, as η is at [Unit]. The eliminator is neutral
    on the neutral its scrutinee reduces to. *)
From DeLaM.Validity Require Export Unit.

Section SEq.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** The irrelevant empty type *)

Lemma wft_sempty_g {G Δ l k} : [ G ; Δ ⊢g ] -> lequiv (gL G) l k -> [ G ; Δ ⊢g tySEmpty k @ l ].
Proof.
  intros HΔ Hk. eapply wft_lconv; [|exact Hk].
  apply wft_sempty; [exact ge_compt | now rewrite ge_typeof | eauto using lequiv_wf_r].
Qed.

Lemma LR_sempty_here {G Δ l l'} : [ G ; Δ ⊢g ] -> lwf (gL G) l -> lequiv (gL G) l l' ->
  LogRel l G Δ (tySEmpty l) (tySEmpty l') l (SEmptyRel G Δ l).
Proof.
  intros HΔ Hw Hl. eapply LRsempty with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_refl, wft_sempty_g; [exact HΔ | now apply lequiv_refl].
  - apply tyred_refl, wft_sempty_g; [exact HΔ | exact Hl].
  - apply releq_refl.
Qed.

Lemma LRtm_sempty {G Δ l t t'} : lwf (gL G) l ->
  LRtm l G Δ (tySEmpty l) (tySEmpty l) t t' <-> SEmptyRel G Δ l t t'.
Proof.
  intros Hw; split.
  - intros H. assert (HΔ : [ G ; Δ ⊢g ])
      by (destruct H as (R & HR & _); exact (ctx_of_ty (proj1 (escape_ty _ _ _ _ _ _ _ _ HR)))).
    exact (LRtm_inv (LR_sempty_here HΔ Hw (lequiv_refl _ _ Hw)) H).
  - intros H. assert (HΔ : [ G ; Δ ⊢g ])
      by (destruct H as (w & _ & Hr & _); exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ Hr))).
    exact (LRtm_of (LR_sempty_here HΔ Hw (lequiv_refl _ _ Hw)) H).
Qed.

Lemma V_sempty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTy G Γ (tySEmpty l) (tySEmpty l') l.
Proof. intros Hw Hl Δ d d' Hd. eexists; apply LR_sempty_here; auto. exact (SubRel_ctx Hd). Qed.

(** Irrelevance: the left sides of the two validities, related. *)
Lemma V_sempty_irr {G Γ l t t1 t' t1'} : lwf (gL G) l ->
  VTm G Γ t t1 (tySEmpty l) l -> VTm G Γ t' t1' (tySEmpty l) l -> VTm G Γ t t1' (tySEmpty l) l.
Proof.
  intros Hw Vt Vt' Δ d d' Hd. specialize (Vt _ _ _ Hd). specialize (Vt' _ _ _ Hd).
  rewrite !subst_tySEmpty in Vt, Vt' |- *. apply (LRtm_sempty Hw) in Vt, Vt'. apply (LRtm_sempty Hw).
  destruct Vt as (w1 & _ & H1 & _ & N1 & _). destruct Vt' as (_ & w4 & _ & H4 & _ & N4).
  exists w1, w4. auto.
Qed.

(** The eliminator reduces its scrutinee only. *)
Lemma tmred_elimSEmpty_cong {G Δ l1 l2 M e ν} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  [ G ; Δ ⊢g M @ l2 ] -> [ G ; Δ ⊢g e ⤳* ν : tySEmpty l1 @ l1 ] ->
  [ G ; Δ ⊢g elimSEmpty l1 l2 M e ⤳* elimSEmpty l1 l2 M ν : M @ l2 ].
Proof.
  intros H1 H2 HM [He Hr Heq]. split.
  - apply wf_elimSEmpty; auto using ge_compt.
  - now apply reds_elimSEmpty.
  - apply eqtm_elimSEmpty; auto using ge_compt, lequiv_refl, eqty_refl.
Qed.

Lemma V_elimSEmpty {G Γ l1 l2 l3 l4 M M' e e'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
  VTy G Γ M M' l2 -> VTm G Γ e e' (tySEmpty l1) l1 ->
  VTm G Γ (elimSEmpty l1 l2 M e) (elimSEmpty l3 l4 M' e') M l2.
Proof.
  intros H1 H2 H3 H4 VM Ve Δ d d' Hd. push_subst.
  destruct (VTy_refl_l VM _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HMd & HMd' & EMM).
  destruct (VM _ _ _ Hd) as [R1 HR1]. destruct (escape_ty _ _ _ _ _ _ _ _ HR1) as (_ & _ & EM1).
  destruct (VM _ _ _ (SubRel_refl_r Hd)) as [R2 HR2].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR2) as (_ & HM'd' & EM2).
  pose proof (Ve _ _ _ Hd) as X. rewrite !subst_tySEmpty in X. apply (LRtm_sempty H1) in X.
  destruct X as (ν & ν' & Hν & Hν' & Nν & Nν').
  pose proof (gne_tm_elimSEmpty (lequiv_sym _ _ _ H3) (lequiv_sym _ _ _ H4) HMd EM1 Nν Nν') as Hne.
  exists R; split; [exact HR|].
  apply (LR_red_tm _ _ _ _ _ _ _ _ HR (elimSEmpty l1 l2 M[d] ν) (elimSEmpty l3 l4 M'[d'] ν')).
  - apply (LR_neutral _ _ _ _ _ _ _ HR); [exact Hne|].
    eapply gne_tm_conv; [exact Hne | now apply geq_ty_sound].
  - exact (tmred_elimSEmpty_cong H1 H2 HMd Hν).
  - (* the right side: at [M'], then converted *)
    assert (HM'4 : [ G ; Δ ⊢g M'[d'] @ l4 ]) by exact (lconv_ty HM'd' (lequiv_sym _ _ _ H4)).
    assert (Hν3 : [ G ; Δ ⊢g e'[d'] ⤳* ν' : tySEmpty l3 @ l3 ])
      by exact (sempty_tmred_conv (lequiv_sym _ _ _ H3) Hν').
    eapply (tmred_lconv _ _ _ _ l4); [|exact (lequiv_sym _ _ _ H4)].
    eapply tmred_conv; [apply ge_typeof | exact (tmred_elimSEmpty_cong (lequiv_wf_l _ _ _ H3)
                                                   (lequiv_wf_l _ _ _ H4) HM'4 Hν3) |].
    eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, EM2 | exact H4].
Qed.

(** ** Strict equality *)

Lemma LR_seq_here {G Δ l l' A A' a a' b b'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢g A @ l ] -> [ G ; Δ ⊢ A ≈ A' @ l ] ->
  [ G ; Δ ⊢ a ≈ a' : A @ l ] -> [ G ; Δ ⊢ b ≈ b' : A @ l ] ->
  LogRel l G Δ (tySEq l A a b) (tySEq l' A' a' b') l (SEqRel G Δ (tySEq l A a b) l).
Proof.
  intros Hw Hl HA HAA Haa Hbb.
  pose proof (geq_ty_sound (geq_ty_seq Hl HA HAA Haa Hbb)) as EV.
  eapply LRseq with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_refl, (eqty_wf_l ge_typeof EV).
  - apply tyred_refl, (eqty_wf_r ge_typeof EV).
  - exact HA.
  - exact HAA.
  - exact Haa.
  - exact Hbb.
  - apply releq_refl.
Qed.

(** The components at related substitutions. *)
Lemma seq_at {G Γ Δ d d' l A A' a a'} : VTy G Γ A A' l -> VTm G Γ a a' A l -> SubRel G Γ Δ d d' ->
  [ G ; Δ ⊢g A[d] @ l ] /\ [ G ; Δ ⊢ A[d] ≈ A'[d'] @ l ] /\ [ G ; Δ ⊢ a[d] ≈ a'[d'] : A[d] @ l ].
Proof.
  intros VA Va Hd. destruct (VA _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HA & _ & EA).
  exact (conj HA (conj EA (LRtm_geq (Va _ _ _ Hd)))).
Qed.

Lemma V_seq {G Γ l l' A A' a a' b b'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTm G Γ a a' A l -> VTm G Γ b b' A l ->
  VTy G Γ (tySEq l A a b) (tySEq l' A' a' b') l.
Proof.
  intros Hw Hl VA Va Vb Δ d d' Hd. push_subst.
  destruct (seq_at VA Va Hd) as (HA & EA & Ea). destruct (seq_at VA Vb Hd) as (_ & _ & Eb).
  eexists; exact (LR_seq_here Hw Hl HA EA Ea Eb).
Qed.

Lemma V_srefl {G Γ l l' A A' a a'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTm G Γ a a' A l -> VTm G Γ (srefl l A a) (srefl l' A' a') (tySEq l A a a) l.
Proof.
  intros Hw Hl VA Va Δ d d' Hd. push_subst.
  pose proof (VTy_refl_l VA) as VAA. pose proof (VTm_trans Va (VTm_sym Va)) as Vaa.
  destruct (seq_at VAA Vaa Hd) as (HA & EAA & Eaa).
  destruct (seq_at VA Va Hd) as (_ & EA & Ea).
  pose proof (geq_ty_sound EA) as DA. pose proof (geq_tm_sound Ea) as Da.
  eapply LRtm_of; [exact (LR_seq_here Hw (lequiv_refl _ _ Hw) HA EAA Eaa Eaa)|].
  exists (srefl l A[d] a[d]), (srefl l' A'[d'] a'[d']).
  refine (conj (tmred_refl _ _ _ _) (conj (tmred_refl _ _ _ _) (conj (whnf_srefl _ _ _) (whnf_srefl _ _ _)))).
  - apply wf_srefl; [exact ge_compt | exact Hw | exact HA | exact (eqtm_wf_l ge_typeof Da)].
  - exact (pre_srefl_r ge_typeof ge_notV Hl HA DA (eqty_wf_r ge_typeof DA) Da (eqtm_wf_r ge_typeof Da)).
Qed.

(** Irrelevance: the relation at any [sEq] pair is [SEqRel], whatever the
    derivation. *)
Lemma V_seq_irr {G Γ l A a b t t1 t' t1'} :
  VTm G Γ t t1 (tySEq l A a b) l -> VTm G Γ t' t1' (tySEq l A a b) l ->
  VTm G Γ t t1' (tySEq l A a b) l.
Proof.
  intros Vt Vt' Δ d d' Hd. specialize (Vt _ _ _ Hd). specialize (Vt' _ _ _ Hd).
  rewrite !subst_tySEq in Vt, Vt' |- *.
  destruct Vt as (R & HR & H1). destruct Vt' as (R' & HR' & H2).
  apply (LR_irrel _ _ _ _ _ _ _ _ _ _ HR HR') in H2.
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HT & _ & _).
  destruct (LR_inv_seq HR (tyred_refl _ _ HT)) as (? & ? & ? & ? & _ & _ & _ & _ & _ & _ & _ & _ & HS).
  exists R; split; [exact HR|]. apply HS in H1, H2. apply HS.
  destruct H1 as (w1 & _ & Hr1 & _ & N1 & _). destruct H2 as (_ & w4 & _ & Hr4 & _ & N4).
  exists w1, w4. auto.
Qed.

End SEq.
