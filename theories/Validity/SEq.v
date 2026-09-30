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
  apply wft_sempty; [exact ge_notV | now rewrite ge_typeof | eauto using lequiv_wf_r].
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
  - apply wf_elimSEmpty; auto using ge_notV.
  - now apply reds_elimSEmpty.
  - apply eqtm_elimSEmpty; auto using ge_notV, lequiv_refl, eqty_refl.
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
  - apply wf_srefl; [exact ge_notV | exact Hw | exact HA | exact (eqtm_wf_l ge_typeof Da)].
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

(** ** The codes (M10c) and their decodings *)

(** Decoding a code whose annotation [k] is equivalent to the level [l]
    at which its pieces are typed. *)
Lemma tyred_El_seq {G Δ la l k s t u} : lequiv (gL G) la l -> lequiv (gL G) k l ->
  [ G ; Δ ⊢g s : tyU l @ lsuc l ] -> [ G ; Δ ⊢g t : tyEl l s @ l ] -> [ G ; Δ ⊢g u : tyEl l s @ l ] ->
  [ G ; Δ ⊢g tyEl la (tmSEq k s t u) ⤳* tySEq k (tyEl k s) t u @ l ].
Proof.
  intros Hla Hk Hs Ht Hu.
  assert (Hkl : lequiv (gL G) l k) by now apply lequiv_sym.
  pose proof (lequiv_wf_l _ _ _ Hk) as Hwk.
  pose proof (conv_U' Hs Hkl) as Hsk.
  assert (EEl : [ G ; Δ ⊢g tyEl k s ≅ tyEl l s @ k ])
    by (apply eqty_El; [exact ge_notV | exact Hk | apply eqtm_refl, Hsk]).
  assert (F : forall x, [ G ; Δ ⊢g x : tyEl l s @ l ] -> [ G ; Δ ⊢g x : tyEl k s @ k ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx Hk) | rewrite ge_typeof; exact EEl]. }
  assert (Hc : [ G ; Δ ⊢g tmSEq k s t u : tyU k @ lsuc k ])
    by (apply wf_code_seq; [exact ge_notV | exact Hwk | exact Hsk | apply F, Ht | apply F, Hu]).
  pose proof (conv_U' Hc Hk) as Hcl.
  destruct (El_annot Hcl Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl k (tmSEq k s t u))).
  - apply eqty_El; [exact ge_notV | exact Hkl | apply eqtm_refl, Hcl].
  - apply (eqty_lconv _ _ _ _ _ l k); [|exact Hkl].
    apply eqty_sym, eqty_El_seq; [exact ge_compt | exact Hwk | exact Hsk | apply F, Ht | apply F, Hu].
Qed.

Lemma V_El_seq {G Γ l s t u} : lwf (gL G) l ->
  VTm G Γ s s (tyU l) (lsuc l) -> VTm G Γ t t (tyEl l s) l -> VTm G Γ u u (tyEl l s) l ->
  VTy G Γ (tySEq l (tyEl l s) t u) (tyEl l (tmSEq l s t u)) l.
Proof.
  intros Hw Vs Vt Vu Δ d d' Hd.
  pose proof (V_El Hw (lequiv_refl _ _ Hw) Vs) as VA.
  destruct (V_seq Hw (lequiv_refl _ _ Hw) VA Vt Vu _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HP & _ & _).
  pose proof (Vs _ _ _ (SubRel_refl_r Hd)) as Xs. pose proof (Vt _ _ _ (SubRel_refl_r Hd)) as Xt.
  pose proof (Vu _ _ _ (SubRel_refl_r Hd)) as Xu.
  rewrite !subst_tyU in Xs. rewrite !subst_tyEl in Xt, Xu.
  exists R. eapply LR_red_ty; [exact HR | apply tyred_refl, HP |]. push_subst.
  apply tyred_El_seq; [now apply lequiv_refl | now apply lequiv_refl | exact (proj1 (LRtm_escape Xs))
                      | exact (proj1 (LRtm_escape Xt)) | exact (proj1 (LRtm_escape Xu))].
Qed.

Lemma V_code_seq {G Γ l l' s s' t t' u u'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ s s' (tyU l) (lsuc l) -> VTm G Γ t t' (tyEl l s) l -> VTm G Γ u u' (tyEl l s) l ->
  VTm G Γ (tmSEq l s t u) (tmSEq l' s' t' u') (tyU l) (lsuc l).
Proof.
  intros Hw Hl Vs Vt Vu Δ d d' Hd.
  pose proof (V_El Hw Hl Vs) as VA.
  destruct (V_seq Hw Hl VA Vt Vu _ _ _ Hd) as [R HR].
  pose proof (Vs _ _ _ Hd) as Xs. pose proof (Vt _ _ _ Hd) as Xt. pose proof (Vu _ _ _ Hd) as Xu.
  rewrite !subst_tyU in Xs. rewrite !subst_tyEl in Xt, Xu.
  destruct (LRtm_escape Xs) as [Hsd Hs'd'].
  pose proof (geq_tm_code_seq Hl Hsd (LRtm_geq Xs) (LRtm_geq Xt) (LRtm_geq Xu)) as Hgeq.
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  assert (EEl : [ G ; Δ ⊢g tyEl l s'[d'] ≅ tyEl l s[d] @ l ]).
  { apply eqty_sym, eqty_El; [exact ge_notV | now apply lequiv_refl | exact (geq_tm_sound (LRtm_geq Xs))]. }
  assert (F : forall x, [ G ; Δ ⊢g x : tyEl l s[d] @ l ] -> [ G ; Δ ⊢g x : tyEl l s'[d'] @ l ]).
  { intros x Hx. eapply wf_conv; [exact Hx | rewrite ge_typeof; exact EEl]. }
  push_subst. apply (LRtm_U Hw).
  exists (tmSEq l s[d] t[d] u[d]), (tmSEq l' s'[d'] t'[d'] u'[d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmSEq _ _ _ _) (conj (whnf_tmSEq _ _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists R. eapply LR_red_ty; [exact HR | |]; push_subst.
  - apply tyred_El_seq; [exact Hla | now apply lequiv_refl | exact Hsd
                        | exact (proj1 (LRtm_escape Xt)) | exact (proj1 (LRtm_escape Xu))].
  - apply tyred_El_seq; [exact Hlb | now apply lequiv_sym | exact Hs'd'
                        | exact (F _ (proj2 (LRtm_escape Xt))) | exact (F _ (proj2 (LRtm_escape Xu)))].
Qed.

Lemma tyred_El_sempty {G Δ la k l} : [ G ; Δ ⊢g ] -> lequiv (gL G) la l -> lequiv (gL G) k l ->
  [ G ; Δ ⊢g tyEl la (tmSEmpty k) ⤳* tySEmpty k @ l ].
Proof.
  intros HΔ Hla Hk.
  pose proof (lequiv_wf_l _ _ _ Hk) as Hwk.
  assert (Hc0 : [ G ; Δ ⊢g tmSEmpty k : tyU k @ lsuc k ])
    by (apply wf_code_sempty; [exact ge_notV | now rewrite ge_typeof | exact Hwk]).
  pose proof (conv_U' Hc0 Hk) as Hc.
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl k (tmSEmpty k)));
    [apply eqty_El; [exact ge_notV | now apply lequiv_sym | now apply eqtm_refl]|].
  apply (eqty_lconv _ _ _ _ _ l k); [|now apply lequiv_sym].
  apply eqty_sym, eqty_El_sempty; [exact ge_compt | now rewrite ge_typeof | exact Hwk].
Qed.

Lemma V_El_sempty {G Γ l} : lwf (gL G) l -> VTy G Γ (tySEmpty l) (tyEl l (tmSEmpty l)) l.
Proof.
  intros Hw Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  exists (SEmptyRel G Δ l). eapply LRsempty with (l1 := l) (l2 := l).
  - now apply lequiv_refl.
  - now apply lequiv_refl.
  - exact Hw.
  - apply tyred_refl, wft_sempty_g; [exact HΔ | now apply lequiv_refl].
  - apply tyred_El_sempty; [exact HΔ | now apply lequiv_refl | now apply lequiv_refl].
  - apply releq_refl.
Qed.

Lemma V_code_sempty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ (tmSEmpty l) (tmSEmpty l') (tyU l) (lsuc l).
Proof.
  intros Hw Hl Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  apply (LRtm_U (l := l) Hw).
  assert (Hc : forall k, lequiv (gL G) l k -> [ G ; Δ ⊢g tmSEmpty k : tyU l @ lsuc l ]).
  { intros k Hk. apply (conv_U' (l := k)); [|now apply lequiv_sym].
    apply wf_code_sempty; [exact ge_notV | now rewrite ge_typeof | eauto using lequiv_wf_r]. }
  exists (tmSEmpty l), (tmSEmpty l').
  refine (conj (tmred_refl _ _ _ (Hc _ (lequiv_refl _ _ Hw)))
            (conj (tmred_refl _ _ _ (Hc _ Hl)) (conj (whnf_tmSEmpty _) (conj (whnf_tmSEmpty _)
            (conj (geq_tm_code_sempty HΔ Hl) _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists (SEmptyRel G Δ l). eapply LRsempty with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_El_sempty; [exact HΔ | exact Hla | now apply lequiv_refl].
  - apply tyred_El_sempty; [exact HΔ | exact Hlb | now apply lequiv_sym].
  - apply releq_refl.
Qed.

End SEq.
