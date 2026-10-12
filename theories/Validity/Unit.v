(** * Validity of the unit type (M8_DESIGN.md K6)

    Formation, code and decoding, [⟨⟩], and η. The relation at [Unit] only
    asks both sides to reach a weak-head normal form ([UnitRel]), so η is
    immediate: the left term's form and the right term's form witness it. *)
From DeLaM.Validity Require Export Basic.

Section Unit.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Lemma wft_unit_g {G Δ l k} : [ G ; Δ ⊢g ] -> lequiv (gL G) l k -> [ G ; Δ ⊢g tyUnit k @ l ].
Proof.
  intros HΔ Hk. eapply wft_lconv; [|exact Hk].
  apply wft_unit; [exact ge_notV | now rewrite ge_typeof | eauto using lequiv_wf_r].
Qed.

Lemma LR_unit_here {G Δ l l'} : [ G ; Δ ⊢g ] -> lwf (gL G) l -> lequiv (gL G) l l' ->
  LogRel l G Δ (tyUnit l) (tyUnit l') l (UnitRel G Δ l).
Proof.
  intros HΔ Hw Hl. eapply LRunit with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_refl, wft_unit_g; [exact HΔ | now apply lequiv_refl].
  - apply tyred_refl, wft_unit_g; [exact HΔ | exact Hl].
  - apply releq_refl.
Qed.

Lemma LRtm_unit {G Δ l t t'} : lwf (gL G) l ->
  LRtm l G Δ (tyUnit l) (tyUnit l) t t' <-> UnitRel G Δ l t t'.
Proof.
  intros Hw; split.
  - intros H. assert (HΔ : [ G ; Δ ⊢g ])
      by (destruct H as (R & HR & _); exact (ctx_of_ty (proj1 (escape_ty _ _ _ _ _ _ _ _ HR)))).
    exact (LRtm_inv (LR_unit_here HΔ Hw (lequiv_refl _ _ Hw)) H).
  - intros H. assert (HΔ : [ G ; Δ ⊢g ])
      by (destruct H as (w & _ & Hr & _); exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ Hr))).
    exact (LRtm_of (LR_unit_here HΔ Hw (lequiv_refl _ _ Hw)) H).
Qed.

(** The decoding of the code reduces to the type. *)
Lemma tyred_El_unit {G Δ la k l} : [ G ; Δ ⊢g ] -> lequiv (gL G) la l -> lequiv (gL G) k l ->
  [ G ; Δ ⊢g tyEl la (tmUnit k) ⤳* tyUnit k @ l ].
Proof.
  intros HΔ Hla Hk.
  pose proof (lequiv_wf_l _ _ _ Hk) as Hwk.
  assert (Hc0 : [ G ; Δ ⊢g tmUnit k : tyU k @ lsuc k ])
    by (apply wf_code_unit; [exact ge_notV | now rewrite ge_typeof | exact Hwk]).
  pose proof (conv_U' Hc0 Hk) as Hc.
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl k (tmUnit k)));
    [apply eqty_El; [exact ge_notV | now apply lequiv_sym | now apply eqtm_refl]|].
  apply (eqty_lconv _ _ _ _ _ l k); [|now apply lequiv_sym].
  apply eqty_sym, eqty_El_unit; [exact ge_compt | now rewrite ge_typeof | exact Hwk].
Qed.

Lemma V_unit {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTy G Γ (tyUnit l) (tyUnit l') l.
Proof. intros Hw Hl Δ d d' Hd. eexists; apply LR_unit_here; auto. exact (SubRel_ctx Hd). Qed.

Lemma V_El_unit {G Γ l} : lwf (gL G) l -> VTy G Γ (tyUnit l) (tyEl l (tmUnit l)) l.
Proof.
  intros Hw Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  exists (UnitRel G Δ l). eapply LRunit with (l1 := l) (l2 := l).
  - now apply lequiv_refl.
  - now apply lequiv_refl.
  - exact Hw.
  - apply tyred_refl, wft_unit_g; [exact HΔ | now apply lequiv_refl].
  - apply tyred_El_unit; [exact HΔ | now apply lequiv_refl | now apply lequiv_refl].
  - apply releq_refl.
Qed.

Lemma V_code_unit {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ (tmUnit l) (tmUnit l') (tyU l) (lsuc l).
Proof.
  intros Hw Hl Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  apply (LRtm_U (l := l) Hw).
  assert (Hc : forall k, lequiv (gL G) l k -> [ G ; Δ ⊢g tmUnit k : tyU l @ lsuc l ]).
  { intros k Hk. apply (conv_U' (l := k)); [|now apply lequiv_sym].
    apply wf_code_unit; [exact ge_notV | now rewrite ge_typeof | eauto using lequiv_wf_r]. }
  exists (tmUnit l), (tmUnit l').
  refine (conj (tmred_refl _ _ _ (Hc _ (lequiv_refl _ _ Hw)))
            (conj (tmred_refl _ _ _ (Hc _ Hl)) (conj (whnf_tmUnit _) (conj (whnf_tmUnit _)
            (conj (geq_tm_code_unit HΔ Hl) _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists (UnitRel G Δ l). eapply LRunit with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_El_unit; [exact HΔ | exact Hla | now apply lequiv_refl].
  - apply tyred_El_unit; [exact HΔ | exact Hlb | now apply lequiv_sym].
  - apply releq_refl.
Qed.

Lemma V_triv {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ (tmTriv l) (tmTriv l') (tyUnit l) l.
Proof.
  intros Hw Hl Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  apply (LRtm_unit Hw).
  assert (Hc : forall k, lequiv (gL G) l k -> [ G ; Δ ⊢g tmTriv k : tyUnit l @ l ]).
  { intros k Hk. eapply conv_tm; [apply wf_triv; [exact ge_notV | now rewrite ge_typeof | eauto using lequiv_wf_r]
                                 | | exact Hk].
    apply eqty_unit; [exact ge_notV | now rewrite ge_typeof | exact Hk]. }
  exists (tmTriv l), (tmTriv l').
  exact (conj (tmred_refl _ _ _ (Hc _ (lequiv_refl _ _ Hw)))
           (conj (tmred_refl _ _ _ (Hc _ Hl)) (conj (whnf_triv _) (whnf_triv _)))).
Qed.

(** η: the left sides of the two validities, related. *)
Lemma V_unit_eta {G Γ l t t1 t' t1'} : lwf (gL G) l ->
  VTm G Γ t t1 (tyUnit l) l -> VTm G Γ t' t1' (tyUnit l) l -> VTm G Γ t t1' (tyUnit l) l.
Proof.
  intros Hw Vt Vt' Δ d d' Hd. specialize (Vt _ _ _ Hd). specialize (Vt' _ _ _ Hd).
  rewrite !subst_tyUnit in Vt, Vt' |- *. apply (LRtm_unit Hw) in Vt, Vt'. apply (LRtm_unit Hw).
  destruct Vt as (w1 & _ & H1 & _ & N1 & _). destruct Vt' as (_ & w4 & _ & H4 & _ & N4).
  exists w1, w4. auto.
Qed.

End Unit.
