(** * Validity of [corec] (M18_DESIGN.md, M18b)

    A [corec]'s observations are its step's: [out] of a [corec] steps to
    [mOutCorec], a pair whose first component is the step's first
    projection and whose second is a function casing on the step's
    continuation, which is either a further [corec] (at the child's own
    index) or a finished [M] term. The relation at [M] is the limit of
    its depth approximations [MRn], so related [corec]s are proved
    related at every depth, by induction on the depth: at depth [S n],
    the children are [corec]s related at depth [n] (the induction
    hypothesis) or the step's finished terms (related at every depth).

    The generic lemmas first: the projections of related pairs, the
    applications of related functions and the shape of related sums, at
    [LRtm]. *)
From DeLaM.Validity Require Export M Sum.
From DeLaM.LogRel Require Import MAux.
From DeLaM.Typing Require Import PresupM.

Section MCorec.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Projections, applications and sums of related terms *)

(** The identity world acts trivially on normal forms. *)
Lemma kw_loc_id_ty {G Δ HΔ} (T : ty) : nfty T -> kty (kw_loc (G := G) wk_id (wkwf_id Δ) HΔ) T = T.
Proof using . intros NT; unfold kty, kw_loc; cbn [kw_γ kw_r gwa wk_ren]; now apply ren_id_ty. Qed.
Lemma kw_loc_id_tyl {G Δ HΔ} (T : ty) : nfty T -> ktyl (kw_loc (G := G) wk_id (wkwf_id Δ) HΔ) T = T.
Proof using . intros NT; unfold ktyl, kw_loc; cbn [kw_γ kw_r gwa wk_ren]; now apply ren_lift_id_ty. Qed.

Lemma lmeasure_le_l {G L l1 l2} : lequiv (gL G) L (lmax l1 l2) -> lmeasure l1 <= lmeasure L.
Proof using . intros H; rewrite (lequiv_measure _ _ _ H), lmeasure_max; lia. Qed.
Lemma lmeasure_le_r {G L l1 l2} : lequiv (gL G) L (lmax l1 l2) -> lmeasure l2 <= lmeasure L.
Proof using . intros H; rewrite (lequiv_measure _ _ _ H), lmeasure_max; lia. Qed.

(** The projections of terms related at [Σ], at the [Σ]'s own
    annotations. *)
Lemma LRtm_sig_proj {L G Γ l1 l2 l3 l4 A B A2 B2 p p'} :
  LRtm L G Γ (tySig l1 l2 A B) (tySig l3 l4 A2 B2) p p' ->
  LRtm l1 G Γ A A2 (tmFst l1 l2 A B p) (tmFst l3 l4 A2 B2 p') /\
  LRtm l2 G Γ B[lsingle (tmFst l1 l2 A B p)] B2[lsingle (tmFst l3 l4 A2 B2 p')]
    (tmSnd l1 l2 A B p) (tmSnd l3 l4 A2 B2 p').
Proof using EL VL.
  intros (R & HR & Hp).
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HT & HT' & _).
  destruct (LR_inv_sig HR (tyred_refl _ _ HT))
    as (m3 & m4 & C' & D' & domR & codR & PF & HdomR & HcodR & Heq).
  destruct PF as [Hlv H3 H4 Hw1 Hw2 _ Hred' HA HA2 HB HB2 HAA HBB].
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ (tyred_refl _ _ HT') Hred' (whnf_tySig _ _ _ _) (whnf_tySig _ _ _ _))
    as Eq. injection Eq as <- <- <- <-.
  pose proof (proj1 (Heq p p') Hp) as HS.
  pose proof (ctx_of_ty HA) as HΓ.
  pose proof (wf_ty_nf HA) as NA. pose proof (wf_ty_nf HA2) as NA2.
  pose proof (wf_ty_nf HB) as NB. pose proof (wf_ty_nf HB2) as NB2.
  assert (RA : [ G ; Γ ⊢ A ≈ A @ l1 ]) by (eapply geq_ty_trans; [exact HAA | apply geq_ty_sym, HAA]).
  assert (RA2 : [ G ; Γ ⊢ A2 ≈ A2 @ l1 ]) by (eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HAA]).
  assert (RB : [ G ; Γ ,, A @ l1 ⊢ B ≈ B @ l2 ]) by (eapply geq_ty_trans; [exact HBB | apply geq_ty_sym, HBB]).
  assert (HΓA2 : [ G ; Γ ,, A2 @ l1 ⊢g ]) by exact (ctx_of_ty HB2).
  assert (RB2 : [ G ; Γ ,, A2 @ l1 ⊢ B2 ≈ B2 @ l2 ]).
  { eapply geq_ty_ctxconv; [apply geq_ty_sound, HAA | apply lequiv_refl, Hw1 | exact HΓA2 |].
    eapply geq_ty_trans; [apply geq_ty_sym, HBB | exact HBB]. }
  destruct (SigRel_id HΓ NA NA2 NB NB2 HS) as (w & w' & Hw & Hw' & K).
  destruct (K l1 l2 l3 l4 A B A2 B2 (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) H3 H4 RA RB RA2 RB2)
    as (h & c).
  set (ρ0 := kw_loc wk_id (wkwf_id Γ) HΓ) in *.
  (* the typings of the right-hand annotations at its own levels *)
  assert (HA23 : [ G ; Γ ⊢g A2 @ l3 ]) by (eapply lconv_ty; [exact HA2 | now apply lequiv_sym]).
  assert (HB23 : [ G ; Γ ,, A2 @ l3 ⊢g B2 @ l4 ]).
  { apply (lconv_ty (l := l2)); [|now apply lequiv_sym].
    eapply (stab_ty ge_typeof (eqty_refl _ _ _ _ _ HA2) (lequiv_sym _ _ _ H3)); [|exact HB2].
    apply ext_wf_g; [exact HA23 | eauto using lequiv_wf_l]. }
  assert (Hw'3 : [ G ; Γ ⊢g p' ⤳* w' : tySig l3 l4 A2 B2 @ lmax l3 l4 ])
    by (eapply tmred_lconv; [exact Hw' | apply lequiv_max; assumption]).
  (* the first projections *)
  pose proof (HdomR ρ0) as HD. change (kw_G ρ0) with G in HD; change (kw_Δ ρ0) with Γ in HD.
  unfold ρ0 in HD; rewrite (kw_loc_id_ty (HΔ := HΓ) _ NA), (kw_loc_id_ty (HΔ := HΓ) _ NA2) in HD.
  assert (Hf : LRtm l1 G Γ A A2 (tmFst l1 l2 A B w) (tmFst l3 l4 A2 B2 w')).
  { apply (LRtm_stage (lmeasure_le_l Hlv)). exists (domR ρ0). exact (conj HD h). }
  pose proof (tmred_fst_cong Hw1 Hw2 HA HB Hw) as Rf.
  assert (Rf' : [ G ; Γ ⊢g tmFst l3 l4 A2 B2 p' ⤳* tmFst l3 l4 A2 B2 w' : A2 @ l1 ]).
  { eapply tmred_lconv; [apply tmred_fst_cong; eauto using lequiv_wf_l | now apply lequiv_sym]. }
  pose proof (LRtm_red Hf Rf Rf') as Hfp.
  split; [exact Hfp|].
  (* the second projections *)
  pose proof (HcodR ρ0 _ _ h) as HC. change (kw_G ρ0) with G in HC; change (kw_Δ ρ0) with Γ in HC.
  unfold ρ0 in HC; rewrite (kw_loc_id_tyl (HΔ := HΓ) _ NB), (kw_loc_id_tyl (HΔ := HΓ) _ NB2) in HC.
  (* the codomain at related first components *)
  assert (Cod : forall a a', LRtm l1 G Γ A A2 a a' -> LRty l2 G Γ B[lsingle a] B2[lsingle a']).
  { intros a a' Ha. apply (LRtm_stage (lmeasure_le_l Hlv)) in Ha.
    assert (ha : domR ρ0 a a').
    { apply (LRrel_canon _ _ _ _ _ _ _ HD). exact Ha. }
    pose proof (HcodR ρ0 _ _ ha) as HCa. change (kw_G ρ0) with G in HCa; change (kw_Δ ρ0) with Γ in HCa.
    unfold ρ0 in HCa; rewrite (kw_loc_id_tyl (HΔ := HΓ) _ NB), (kw_loc_id_tyl (HΔ := HΓ) _ NB2) in HCa.
    exists (codR ρ0 a a' ha). apply (LogRel_stage (lmeasure L)); [exact (lmeasure_le_r Hlv) | exact HCa]. }
  assert (Hs : LRtm l2 G Γ B[lsingle (tmFst l1 l2 A B w)] B2[lsingle (tmFst l3 l4 A2 B2 w')]
                 (tmSnd l1 l2 A B w) (tmSnd l3 l4 A2 B2 w')).
  { apply (LRtm_stage (lmeasure_le_r Hlv)). exists (codR ρ0 _ _ h). exact (conj HC c). }
  pose proof (tmred_eq _ _ _ _ _ _ _ Rf) as Ef. pose proof (tmred_eq _ _ _ _ _ _ _ Rf') as Ef'.
  pose proof (tmred_wf _ _ _ _ _ _ _ Rf) as Hfpt. pose proof (eqtm_wf_r ge_typeof Ef) as Hfw.
  pose proof (tmred_wf _ _ _ _ _ _ _ Rf') as Hfpt'. pose proof (eqtm_wf_r ge_typeof Ef') as Hfw'.
  (* the reductions, at the instances at the whnfs' first projections *)
  assert (Rs : [ G ; Γ ⊢g tmSnd l1 l2 A B p ⤳* tmSnd l1 l2 A B w : B[lsingle (tmFst l1 l2 A B w)] @ l2 ]).
  { eapply tmred_conv; [apply ge_typeof | apply tmred_snd_cong; assumption |].
    apply (wf_ty_func ge_typeof HB). apply (lsub_eq_single ge_typeof); [exact Hfpt | exact Hfw | exact Ef]. }
  assert (HB2l : [ G ; Γ ,, A2 @ l3 ⊢g B2 @ l2 ]) by exact (lconv_ty HB23 H4).
  assert (Rs' : [ G ; Γ ⊢g tmSnd l3 l4 A2 B2 p' ⤳* tmSnd l3 l4 A2 B2 w'
                  : B2[lsingle (tmFst l3 l4 A2 B2 w')] @ l2 ]).
  { apply (tmred_lconv _ _ _ _ l4); [|now apply lequiv_sym].
    eapply tmred_conv; [apply ge_typeof | apply tmred_snd_cong; eauto using lequiv_wf_l |].
    eapply eqty_lconv; [|exact H4].
    apply (wf_ty_func ge_typeof HB2l). apply (lsub_eq_single ge_typeof).
    - eapply wf_lconv; [exact Hfpt' | exact H3].
    - eapply wf_lconv; [exact Hfw' | exact H3].
    - eapply eqtm_lconv; [exact Ef' | exact H3]. }
  pose proof (LRtm_red Hs Rs Rs') as Y.
  (* back to the instances at the projections of [p] and [p'] *)
  pose proof (Cod _ _ Hf) as Cww'.
  pose proof (Cod _ _ (LRtm_red_l Hf Rf)) as Cpw'.
  assert (Hwp' : LRtm l1 G Γ A A2 (tmFst l1 l2 A B w) (tmFst l3 l4 A2 B2 p')).
  { eapply LRtm_red; [exact Hf | apply tmred_refl, Hfw | exact Rf']. }
  pose proof (Cod _ _ Hwp') as Cwp'.
  eapply LRtm_conv_r; [eapply LRtm_conv_l; [exact Y|] |].
  - exact (LRty_trans Cpw' (LRty_sym Cww')).
  - exact (LRty_trans (LRty_sym Cww') Cwp').
Qed.

(** The applications of terms related at [Π] to related arguments, at the
    [Π]'s own annotations. *)
Lemma LRtm_pi_app {L G Γ l1 l2 l3 l4 A B A2 B2 f f' a a'} :
  LRtm L G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A2 B2) f f' ->
  LRtm l1 G Γ A A2 a a' ->
  LRtm l2 G Γ B[lsingle a] B2[lsingle a'] (app f l1 l2 A B a) (app f' l3 l4 A2 B2 a').
Proof using EL VL.
  intros (R & HR & Hf) Ha.
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HT & HT' & _).
  destruct (LR_inv_pi HR (tyred_refl _ _ HT))
    as (m3 & m4 & C' & D' & domR & codR & PF & HdomR & HcodR & Heq).
  destruct PF as [Hlv H3 H4 Hw1 Hw2 _ Hred' HA HA2 HB HB2 HAA HBB].
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ (tyred_refl _ _ HT') Hred' (whnf_tyPi _ _ _ _) (whnf_tyPi _ _ _ _))
    as Eq. injection Eq as <- <- <- <-.
  pose proof (proj1 (Heq f f') Hf) as HP.
  pose proof (ctx_of_ty HA) as HΓ.
  pose proof (wf_ty_nf HA) as NA. pose proof (wf_ty_nf HA2) as NA2.
  pose proof (wf_ty_nf HB) as NB. pose proof (wf_ty_nf HB2) as NB2.
  assert (RA : [ G ; Γ ⊢ A ≈ A @ l1 ]) by (eapply geq_ty_trans; [exact HAA | apply geq_ty_sym, HAA]).
  assert (RA2 : [ G ; Γ ⊢ A2 ≈ A2 @ l1 ]) by (eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HAA]).
  assert (RB : [ G ; Γ ,, A @ l1 ⊢ B ≈ B @ l2 ]) by (eapply geq_ty_trans; [exact HBB | apply geq_ty_sym, HBB]).
  assert (HΓA2 : [ G ; Γ ,, A2 @ l1 ⊢g ]) by exact (ctx_of_ty HB2).
  assert (RB2 : [ G ; Γ ,, A2 @ l1 ⊢ B2 ≈ B2 @ l2 ]).
  { eapply geq_ty_ctxconv; [apply geq_ty_sound, HAA | apply lequiv_refl, Hw1 | exact HΓA2 |].
    eapply geq_ty_trans; [apply geq_ty_sym, HBB | exact HBB]. }
  destruct (PiRel_id HΓ NA NA2 NB NB2 HP) as (w & w' & Hw & Hw' & K).
  set (ρ0 := kw_loc wk_id (wkwf_id Γ) HΓ) in *.
  pose proof (HdomR ρ0) as HD. change (kw_G ρ0) with G in HD; change (kw_Δ ρ0) with Γ in HD.
  unfold ρ0 in HD; rewrite (kw_loc_id_ty (HΔ := HΓ) _ NA), (kw_loc_id_ty (HΔ := HΓ) _ NA2) in HD.
  assert (ha : domR ρ0 a a').
  { apply (LRrel_canon _ _ _ _ _ _ _ HD). exact (proj1 (LRtm_stage (lmeasure_le_l Hlv)) Ha). }
  pose proof (K a a' ha l1 l2 l3 l4 A B A2 B2 (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) H3 H4 RA RB RA2 RB2)
    as c.
  pose proof (HcodR ρ0 _ _ ha) as HC. change (kw_G ρ0) with G in HC; change (kw_Δ ρ0) with Γ in HC.
  unfold ρ0 in HC; rewrite (kw_loc_id_tyl (HΔ := HΓ) _ NB), (kw_loc_id_tyl (HΔ := HΓ) _ NB2) in HC.
  assert (Hc : LRtm l2 G Γ B[lsingle a] B2[lsingle a'] (app w l1 l2 A B a) (app w' l3 l4 A2 B2 a')).
  { apply (LRtm_stage (lmeasure_le_r Hlv)). eexists. exact (conj HC c). }
  (* the typings of the right-hand annotations at its own levels *)
  assert (HA23 : [ G ; Γ ⊢g A2 @ l3 ]) by (eapply lconv_ty; [exact HA2 | now apply lequiv_sym]).
  assert (HB23 : [ G ; Γ ,, A2 @ l3 ⊢g B2 @ l4 ]).
  { apply (lconv_ty (l := l2)); [|now apply lequiv_sym].
    eapply (stab_ty ge_typeof (eqty_refl _ _ _ _ _ HA2) (lequiv_sym _ _ _ H3)); [|exact HB2].
    apply ext_wf_g; [exact HA23 | eauto using lequiv_wf_l]. }
  assert (Hw'3 : [ G ; Γ ⊢g f' ⤳* w' : tyPi l3 l4 A2 B2 @ lmax l3 l4 ])
    by (eapply tmred_lconv; [exact Hw' | apply lequiv_max; assumption]).
  destruct (LRtm_escape Ha) as (Hat & Hat').
  assert (Hat'3 : [ G ; Γ ⊢g a' : A2 @ l3 ]).
  { eapply wf_lconv; [eapply wf_conv; [exact Hat' | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ (geq_ty_sound HAA))] | exact H3]. }
  eapply LRtm_red; [exact Hc | apply tmred_app_cong; assumption |].
  apply (tmred_lconv _ _ _ _ l4); [|now apply lequiv_sym].
  apply tmred_app_cong; eauto using lequiv_wf_l.
Qed.

(** Terms related at [+] are related sums of [LRtm]-related payloads. *)
Lemma LRtm_sum_rel {L G Γ l1 l2 l3 l4 A B A2 B2 s s'} :
  LRtm L G Γ (tySum l1 l2 A B) (tySum l3 l4 A2 B2) s s' ->
  SumRel G Γ l1 l2 A B (LRtm l1 G Γ A A2) (LRtm l2 G Γ B B2) s s'.
Proof using EL VL.
  intros (R & HR & Hs).
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HT & HT' & _).
  destruct (LR_inv_sum HR (tyred_refl _ _ HT))
    as (m3 & m4 & X' & Y' & RA & RB & Hlv & _ & _ & _ & _ & Hred' & _ & _ & _ & _ & HRA & HRB & _ & _ & _ & _ & Heq).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ (tyred_refl _ _ HT') Hred' (whnf_tySum _ _ _ _) (whnf_tySum _ _ _ _))
    as Eq. injection Eq as <- <- <- <-.
  eapply SumRel_releq; [| | exact (proj1 (Heq s s') Hs)]; intros u v.
  - rewrite (LRtm_stage (lmeasure_le_l Hlv)). exact (iff_sym (LRrel_canon _ _ _ _ _ _ _ HRA u v)).
  - rewrite (LRtm_stage (lmeasure_le_r Hlv)). exact (iff_sym (LRrel_canon _ _ _ _ _ _ _ HRB u v)).
Qed.

End MCorec.
