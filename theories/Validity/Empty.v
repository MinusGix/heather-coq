(** * Validity of the empty type (M12_DESIGN.md, M12a)

    Formation of [Empty], its eliminator, and proof irrelevance. The term
    relation at [Empty] asks for self-related neutrals ([EmptyRel]), as at
    [sEmpty], so irrelevance is immediate. There is no canonical form, so
    the eliminator is neutral on the neutral its scrutinee reduces to, and
    its motive is instantiated at that neutral through the motive's
    validity. *)
From DeLaM.Validity Require Export Id.

Section Empty.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** The type *)

Lemma wft_empty_g {G Δ l k} : [ G ; Δ ⊢g ] -> lequiv (gL G) l k -> [ G ; Δ ⊢g tyEmpty k @ l ].
Proof.
  intros HΔ Hk. eapply wft_lconv; [|exact Hk].
  apply wft_empty; [exact ge_notV | now rewrite ge_typeof | eauto using lequiv_wf_r].
Qed.

Lemma LR_empty_here {G Δ l l'} : [ G ; Δ ⊢g ] -> lwf (gL G) l -> lequiv (gL G) l l' ->
  LogRel l G Δ (tyEmpty l) (tyEmpty l') l (EmptyRel G Δ l).
Proof.
  intros HΔ Hw Hl. eapply LRempty with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_refl, wft_empty_g; [exact HΔ | now apply lequiv_refl].
  - apply tyred_refl, wft_empty_g; [exact HΔ | exact Hl].
  - apply releq_refl.
Qed.

Lemma LRtm_empty {G Δ l t t'} : lwf (gL G) l ->
  LRtm l G Δ (tyEmpty l) (tyEmpty l) t t' <-> EmptyRel G Δ l t t'.
Proof.
  intros Hw; split.
  - intros H. assert (HΔ : [ G ; Δ ⊢g ])
      by (destruct H as (R & HR & _); exact (ctx_of_ty (proj1 (escape_ty _ _ _ _ _ _ _ _ HR)))).
    exact (LRtm_inv (LR_empty_here HΔ Hw (lequiv_refl _ _ Hw)) H).
  - intros H. assert (HΔ : [ G ; Δ ⊢g ])
      by (destruct H as (w & _ & Hr & _); exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ Hr))).
    exact (LRtm_of (LR_empty_here HΔ Hw (lequiv_refl _ _ Hw)) H).
Qed.

Lemma V_empty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTy G Γ (tyEmpty l) (tyEmpty l') l.
Proof. intros Hw Hl Δ d d' Hd. eexists; apply LR_empty_here; auto. exact (SubRel_ctx Hd). Qed.

(** Irrelevance: the left sides of the two validities, related. *)
Lemma V_empty_irr {G Γ l t t1 t' t1'} : lwf (gL G) l ->
  VTm G Γ t t1 (tyEmpty l) l -> VTm G Γ t' t1' (tyEmpty l) l -> VTm G Γ t t1' (tyEmpty l) l.
Proof.
  intros Hw Vt Vt' Δ d d' Hd. specialize (Vt _ _ _ Hd). specialize (Vt' _ _ _ Hd).
  rewrite !subst_tyEmpty in Vt, Vt' |- *. apply (LRtm_empty Hw) in Vt, Vt'. apply (LRtm_empty Hw).
  destruct Vt as (w1 & _ & H1 & _ & N1 & _). destruct Vt' as (_ & w4 & _ & H4 & _ & N4).
  exists w1, w4. auto.
Qed.

(** ** The eliminator *)

(** The motive at related neutrals, through its validity. *)
Lemma VTy_empty_at {G Γ Δ A B l l' e e' n n'} : lwf (gL G) l' ->
  VTy G (Γ ,, tyEmpty l' @ l') A B l -> SubRel G Γ Δ e e' -> EmptyRel G Δ l' n n' ->
  LRty l G Δ A[llift e][lsingle n] B[llift e'][lsingle n'].
Proof.
  intros Hw V He Hn. destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  rewrite !lift_single_ty by assumption.
  apply V, SubRel_cons; [exact He | exact (proj2 (LRtm_empty Hw) Hn)].
Qed.

(** A term and its neutral reduct are related. *)
Lemma EmptyRel_to_ne {G Δ l t ν} : [ G ; Δ ⊢g t ⤳* ν : tyEmpty l @ l ] ->
  [ G ; Δ ⊢ ν ~ ν : tyEmpty l @ l ] -> EmptyRel G Δ l ν t.
Proof.
  intros Hr Hn. exists ν, ν. refine (conj _ (conj Hr (conj Hn Hn))).
  apply tmred_refl. exact (gne_tm_typed_l Hn).
Qed.

Lemma tmred_elimEmpty_cong {G Δ l l' M n w} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Δ ,, tyEmpty l' @ l' ⊢g M @ l ] -> [ G ; Δ ⊢g n ⤳* w : tyEmpty l' @ l' ] ->
  [ G ; Δ ⊢g elimEmpty l l' M n ⤳* elimEmpty l l' M w : M[lsingle n] @ l ].
Proof.
  intros H1 H2 HM [Hn Hr Heq]. split.
  - apply wf_elimEmpty; auto using ge_notV.
  - now apply reds_elimEmpty.
  - apply eqtm_elimEmpty; auto using ge_notV, lequiv_refl, eqty_refl.
Qed.

Lemma V_elimEmpty {G Γ l1 l2 l3 l4 M M' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢g M @ l1 ] ->
  VTy G (Γ ,, tyEmpty l2 @ l2) M M' l1 -> VTm G Γ t t' (tyEmpty l2) l2 ->
  VTm G Γ (elimEmpty l1 l2 M t) (elimEmpty l3 l4 M' t') M[lsingle t] l1.
Proof.
  intros H1 H2 H13 H24 HM VM Vt Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (SubRel_ctx Hd) as HΔ.
  push_subst. rewrite !single_subst_ty by assumption.
  pose proof (VTm_trans Vt (VTm_sym Vt)) as Vtt.
  (* the scrutinees reduce to neutrals, each related to itself *)
  pose proof (Vt _ _ _ Hd) as X. rewrite !subst_tyEmpty in X. apply (LRtm_empty H2) in X.
  destruct X as (ν & ν' & Hν & Hν' & Hνν & Hν'ν').
  pose proof (Vtt _ _ _ Hd) as Xtt. rewrite !subst_tyEmpty in Xtt. apply (LRtm_empty H2) in Xtt.
  (* the motive under the lifted substitutions *)
  assert (HE : [ G ; Δ ⊢g tyEmpty l2 @ l2 ]) by (apply wft_empty_g; [exact HΔ | now apply lequiv_refl]).
  assert (Hlift : SubRel G (Γ ,, tyEmpty l2 @ l2) (Δ ,, tyEmpty l2 @ l2) (llift d) (llift d'))
    by exact (SubRel_lift (A := tyEmpty l2) Hd (V_empty H2 (lequiv_refl _ _ H2)) HE H2).
  destruct (VM _ _ _ Hlift) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HMd & HM'd' & EqM).
  (* the result type's relation, at the left's type on both sides *)
  destruct (VTy_empty_at H2 (VTy_refl_l VM) Hd Xtt) as [R HR].
  exists R; split; [exact HR|].
  (* the neutral, at the neutral's motive instance, then at the scrutinee's *)
  pose proof (gne_tm_elimEmpty H13 H24 HMd EqM Hνν Hν'ν') as Hne'.
  destruct (VTy_empty_at H2 (VTy_refl_l VM) (SubRel_refl_l Hd) (EmptyRel_to_ne Hν Hνν)) as [R1 HR1].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR1) as (_ & _ & Eν).
  pose proof (gne_tm_conv Hne' (geq_ty_sound Eν)) as Hne''.
  apply (LR_red_tm _ _ _ _ _ _ _ _ HR (elimEmpty l1 l2 M[llift d] ν) (elimEmpty l3 l4 M'[llift d'] ν')).
  - apply (LR_neutral _ _ _ _ _ _ _ HR); [exact Hne''|].
    destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & ET).
    eapply gne_tm_conv; [exact Hne'' | now apply geq_ty_sound].
  - exact (tmred_elimEmpty_cong H1 H2 HMd Hν).
  - (* the right side: at [M'] and the right scrutinee, then converted *)
    assert (HM'3 : [ G ; Δ ,, tyEmpty l2 @ l2 ⊢g M'[llift d'] @ l3 ])
      by exact (lconv_ty HM'd' H13).
    assert (HΓ4 : [ G ; Δ ,, tyEmpty l4 @ l4 ⊢g ])
      by (apply ext_wf_g; [apply wft_empty_g; [exact HΔ | now apply lequiv_refl, (lequiv_wf_r _ _ _ H24)]
                          | exact (lequiv_wf_r _ _ _ H24)]).
    pose proof (stab_ty ge_typeof (empty_eqty HΔ H24) H24 HΓ4 HM'3) as HM'4.
    pose proof (empty_tmred_conv H24 Hν') as Hν'4.
    pose proof (tmred_elimEmpty_cong (lequiv_wf_r _ _ _ H13) (lequiv_wf_r _ _ _ H24) HM'4 Hν'4) as Rr.
    (* its type, [M'[llift d'][lsingle t'[d']]], to the left's [M[llift d'][lsingle t[d']]] *)
    pose proof (Vt _ _ _ (SubRel_refl_r Hd)) as Xr. rewrite !subst_tyEmpty in Xr. apply (LRtm_empty H2) in Xr.
    destruct (VTy_empty_at H2 (VTy_sym VM) (SubRel_refl_r Hd) (EmptyRel_sym Xr)) as [R2 HR2].
    destruct (escape_ty _ _ _ _ _ _ _ _ HR2) as (_ & _ & E2).
    eapply (tmred_lconv _ _ _ _ l3); [|exact H13].
    eapply tmred_conv; [apply ge_typeof | exact Rr |].
    eapply eqty_lconv; [apply geq_ty_sound, E2 | exact (lequiv_sym _ _ _ H13)].
Qed.

(** ** The code (M12c) and its decoding *)

Lemma tyred_El_empty {G Δ la k l} : [ G ; Δ ⊢g ] -> lequiv (gL G) la l -> lequiv (gL G) k l ->
  [ G ; Δ ⊢g tyEl la (tmEmpty k) ⤳* tyEmpty k @ l ].
Proof.
  intros HΔ Hla Hk.
  pose proof (lequiv_wf_l _ _ _ Hk) as Hwk.
  assert (Hc0 : [ G ; Δ ⊢g tmEmpty k : tyU k @ lsuc k ])
    by (apply wf_code_empty; [exact ge_notV | now rewrite ge_typeof | exact Hwk]).
  pose proof (conv_U' Hc0 Hk) as Hc.
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl k (tmEmpty k)));
    [apply eqty_El; [exact ge_notV | now apply lequiv_sym | now apply eqtm_refl]|].
  apply (eqty_lconv _ _ _ _ _ l k); [|now apply lequiv_sym].
  apply eqty_sym, eqty_El_empty; [exact ge_compt | now rewrite ge_typeof | exact Hwk].
Qed.

Lemma V_El_empty {G Γ l} : lwf (gL G) l -> VTy G Γ (tyEmpty l) (tyEl l (tmEmpty l)) l.
Proof.
  intros Hw Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  exists (EmptyRel G Δ l). eapply LRempty with (l1 := l) (l2 := l).
  - now apply lequiv_refl.
  - now apply lequiv_refl.
  - exact Hw.
  - apply tyred_refl, wft_empty_g; [exact HΔ | now apply lequiv_refl].
  - apply tyred_El_empty; [exact HΔ | now apply lequiv_refl | now apply lequiv_refl].
  - apply releq_refl.
Qed.

Lemma V_code_empty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ (tmEmpty l) (tmEmpty l') (tyU l) (lsuc l).
Proof.
  intros Hw Hl Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  apply (LRtm_U (l := l) Hw).
  assert (Hc : forall k, lequiv (gL G) l k -> [ G ; Δ ⊢g tmEmpty k : tyU l @ lsuc l ]).
  { intros k Hk. apply (conv_U' (l := k)); [|now apply lequiv_sym].
    apply wf_code_empty; [exact ge_notV | now rewrite ge_typeof | eauto using lequiv_wf_r]. }
  exists (tmEmpty l), (tmEmpty l').
  refine (conj (tmred_refl _ _ _ (Hc _ (lequiv_refl _ _ Hw)))
            (conj (tmred_refl _ _ _ (Hc _ Hl)) (conj (whnf_tmEmpty _) (conj (whnf_tmEmpty _)
            (conj (geq_tm_code_empty HΔ Hl) _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists (EmptyRel G Δ l). eapply LRempty with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_El_empty; [exact HΔ | exact Hla | now apply lequiv_refl].
  - apply tyred_El_empty; [exact HΔ | exact Hlb | now apply lequiv_sym].
  - apply releq_refl.
Qed.

End Empty.
