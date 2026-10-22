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

(** ** Syntax: β's reduct in pieces *)

(** [meq], through the leaves whose pointwise comparison unfolds a
    substituted entry. *)
Local Ltac mfold := repeat change (ren_ty ?x ?r) with x⟨r⟩; repeat change (subst_ty ?x ?e) with x[e];
  repeat change (ren_tm ?x ?r) with x⟨r⟩; repeat change (subst_tm ?x ?e) with x[e].
Local Ltac meq' := meq; repeat (rewrite ?Nat.add_0_r, ?llk_llift; mfold; meq).

(** The reduct's second component and the body of its λ. *)
Definition mBody (l l' li : lvl) (X A B : ty) (C : tm) (k : lvl) (Y : ty) (c j y : tm) : tm :=
  tmCase k (mlvl l l' li) (mlvl l l' li)
    Y⟨rlift ↑⟩[lsingle (mOutIdx l l' li X A B C k Y c j y)]
    (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
       (mOutIdx l l' li X A B C k Y c j y))
    (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
       (mOutIdx l l' li X A B C k Y c j y))⟨↑⟩
    (tmCorec l l' li X⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
       C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ k Y⟨rlift ↑⟩⟨rlift ↑⟩
       c⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (mOutIdx l l' li X A B C k Y c j y)⟨↑⟩ (var 0))
    (var 0)
    (app (tmSnd l (lmax k (mlvl l l' li)) A[lsingle j] (mStepSnd l l' li X A B C k Y j) c[lsingle2 j y])⟨↑⟩
       l' (lmax k (mlvl l l' li))
       B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)]⟨↑⟩
       (tySum k (mlvl l l' li) Y⟨rlift ↑⟩[lsingle (mOutIdx l l' li X A B C k Y c j y)]
          (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
             (mOutIdx l l' li X A B C k Y c j y)))⟨rlift ↑⟩
       (var 0)).
Arguments mBody : simpl never.

Definition mLam (l l' li : lvl) (X A B : ty) (C : tm) (k : lvl) (Y : ty) (c j y : tm) : tm :=
  lam l' (mlvl l l' li) B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)] (mBody l l' li X A B C k Y c j y).
Arguments mLam : simpl never.

Lemma mOutCorec_pair l l' li X A B C k Y c j y :
  mOutCorec l l' li X A B C k Y c j y =
  tmPair l (mlvl l l' li) A[lsingle j]
    (tyPi l' (mlvl l l' li) B[llift (lsingle j)]
       (tyM l l' li X⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
          C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C[llift (llift (lsingle j))]))
    (mOutFst l l' li X A B C k Y c j y) (mLam l l' li X A B C k Y c j y).
Proof using . reflexivity. Qed.

(** The λ's body at a position: [case] on the step's second projection
    applied to it, the child index [C[j, fst r, p]] *)
Notation mIdxP l l' li X A B C k Y c j y p := (C[lsingle3 j (mOutFst l l' li X A B C k Y c j y) p]).

Lemma mBody_single l l' li X A B C k Y c j y p :
  nfty X -> nfty A -> nfty B -> nftm C -> nfty Y -> nftm c -> nftm j -> nftm y ->
  (mBody l l' li X A B C k Y c j y)[lsingle p] =
  tmCase k (mlvl l l' li) (mlvl l l' li) Y[lsingle (mIdxP l l' li X A B C k Y c j y p)]
    (tyM l l' li X A B C (mIdxP l l' li X A B C k Y c j y p))
    (tyM l l' li X A B C (mIdxP l l' li X A B C k Y c j y p))⟨↑⟩
    (tmCorec l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ k Y⟨rlift ↑⟩
       c⟨rlift (rlift ↑)⟩ (mIdxP l l' li X A B C k Y c j y p)⟨↑⟩ (var 0))
    (var 0)
    (app (tmSnd l (lmax k (mlvl l l' li)) A[lsingle j] (mStepSnd l l' li X A B C k Y j) c[lsingle2 j y])
       l' (lmax k (mlvl l l' li)) B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)]
       (tySum k (mlvl l l' li) Y⟨rlift ↑⟩[lsingle (mOutIdx l l' li X A B C k Y c j y)]
          (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
             (mOutIdx l l' li X A B C k Y c j y)))
       p).
Proof using . intros. unfold mBody. meq'. Qed.

(** The step type under a substitution. *)
Lemma subst_mStepTy_lift l l' li X A B C k Y e : LK nftm e ->
  (mStepTy l l' li X A B C k Y)[llift e] =
  mStepTy l l' li X[e] A[llift e] B[llift (llift e)] C[llift (llift (llift e))] k Y[llift e].
Proof using .
  intros He. meq'.
  all: repeat (rewrite ?shift_llift, ?shift_single by apply He; mfold; meq').
Qed.

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

(** ** Syntax in a world *)

Lemma gwa_mOutCorec γ l l' li X A B C k Y c j y :
  (mOutCorec l l' li X A B C k Y c j y)⟦γ⟧ = mOutCorec l l' li X⟦γ⟧ A⟦γ⟧ B⟦γ⟧ C⟦γ⟧ k Y⟦γ⟧ c⟦γ⟧ j⟦γ⟧ y⟦γ⟧.
Proof using . destruct γ; cbn [gwa]; [reflexivity | apply gren_mOutCorec ..]. Qed.

Section KwOut.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma ktm_mOutCorec l l' li X A B C k Y c j y :
  ktm ρ (mOutCorec l l' li X A B C k Y c j y) =
  mOutCorec l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) k (ktyl ρ Y) (ktmll ρ c) (ktm ρ j) (ktm ρ y).
Proof using . unfold ktm, kty, ktyl, ktyll, ktmll, ktmlll. now rewrite gwa_mOutCorec, mOutCorec_ren. Qed.

Lemma ktm_mLam l l' li X A B C k Y c j y :
  ktm ρ (mLam l l' li X A B C k Y c j y) =
  mLam l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) k (ktyl ρ Y) (ktmll ρ c) (ktm ρ j) (ktm ρ y).
Proof using .
  pose proof (ktm_mOutCorec l l' li X A B C k Y c j y) as Eo.
  rewrite !mOutCorec_pair, ktm_pair in Eo. now injection Eo.
Qed.

Lemma ktm_mOutFst l l' li X A B C k Y c j y :
  ktm ρ (mOutFst l l' li X A B C k Y c j y) =
  mOutFst l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) k (ktyl ρ Y) (ktmll ρ c) (ktm ρ j) (ktm ρ y).
Proof using .
  pose proof (ktm_mOutCorec l l' li X A B C k Y c j y) as Eo.
  rewrite !mOutCorec_pair, ktm_pair in Eo. now injection Eo.
Qed.

Lemma ktml_mBody l l' li X A B C k Y c j y :
  ktml ρ (mBody l l' li X A B C k Y c j y) =
  mBody l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) k (ktyl ρ Y) (ktmll ρ c) (ktm ρ j) (ktm ρ y).
Proof using .
  pose proof (ktm_mLam l l' li X A B C k Y c j y) as Eo.
  unfold mLam at 1 in Eo. rewrite ktm_lam in Eo. unfold mLam in Eo. now injection Eo.
Qed.

End KwOut.

Lemma gwa_mStepTy γ l l' li X A B C k Y :
  (mStepTy l l' li X A B C k Y)⟦γ⟧ = mStepTy l l' li X⟦γ⟧ A⟦γ⟧ B⟦γ⟧ C⟦γ⟧ k Y⟦γ⟧.
Proof using .
  repeat rewrite ?gwa_tySig, ?gwa_tyPi, ?gwa_tySum, ?gwa_tyM, ?gwa_subst_ty, ?gwa_lsingle, ?gwa_ren_ty, ?gwa_ren.
  reflexivity.
Qed.

(** The step type at a world's substitution. *)
Lemma kw_mStepTy {G Δ} (ρ : kwk G Δ) d l l' li X A B C k Y : LK nftm d ->
  (mStepTy l l' li X A B C k Y)⟦kw_γ ρ⟧[llift (kwsub ρ d)] =
  mStepTy l l' li (kty ρ X[d]) (ktyl ρ A[llift d]) (ktyll ρ B[llift (llift d)])
    (ktmlll ρ C[llift (llift (llift d))]) k (ktyl ρ Y[llift d]).
Proof using .
  intros Nd. rewrite gwa_mStepTy, (subst_mStepTy_lift _ _ _ _ _ _ _ _ _ _ (kwsub_nf ρ d Nd)).
  now rewrite kty_subst, !ktyl_subst_lift, ktyll_subst_lift', ktmlll_subst_lift.
Qed.

Lemma ktmll_subst_lift2 {G Δ} (ρ : kwk G Δ) (t : tm) e :
  ktmll ρ t[llift (llift e)] = t⟦kw_γ ρ⟧[llift (llift (kwsub ρ e))].
Proof using .
  unfold ktmll, kwsub. rewrite gwa_subst, subst_ren_lren.
  apply subst_ext. intros n. rewrite llk_lren.
  destruct n as [|[|n]]; repeat rewrite ?llk_llift_gwa, ?llk_llift, ?llk_lren; try reflexivity.
  change (ren_tm ?x ?r') with x⟨r'⟩. rewrite !ren_ren_comp. apply ren_ext_tm. intros k. rlk_simpl. lia.
Qed.
Lemma ktmll_single2 {G Δ} (ρ : kwk G Δ) (t : tm) e a p : LK nftm e ->
  (ktmll ρ t[llift (llift e)])[lsingle2 a p] = t⟦kw_γ ρ⟧[lcons (lcons (kwsub ρ e) a) p].
Proof using . intros Ne. rewrite ktmll_subst_lift2. apply lift2_single2, kwsub_nf, Ne. Qed.

(** ** [out] of a [corec], typed

    At any annotations on [out] equal to the signature and to an index
    [j] equal to the [corec]'s own [j0]: one step to β's reduct, at
    [out]'s type at [j]. *)
Lemma tmred_out_corec {G Γ l l' li X A B C kc Y c j0 y j k1 k2 ki X1 A1 B1 C1 j1} :
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C -> lwf (gL G) kc ->
  [ G ; Γ ,, X @ li ⊢g Y @ kc ] ->
  [ G ; Γ ,, X @ li ,, Y @ kc ⊢g c : (mStepTy l l' li X A B C kc Y)⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ] ->
  [ G ; Γ ⊢g j0 : X @ li ] -> [ G ; Γ ⊢g y : Y[lsingle j0] @ kc ] -> [ G ; Γ ⊢g j0 ≅ j : X @ li ] ->
  MAnn G Γ l l' li X A B C j k1 k2 ki X1 A1 B1 C1 j1 ->
  [ G ; Γ ⊢g tmOut k1 k2 ki X1 A1 B1 C1 j1 (tmCorec l l' li X A B C kc Y c j0 y)
      ⤳* mOutCorec l l' li X A B C kc Y c j0 y : mOutTy l l' li X A B C j @ lmax l (mlvl l l' li) ].
Proof using EL.
  intros HS Hkc HY Hc Hj0 Hy Ej Ann.
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  pose proof (eqtm_wf_r ge_typeof Ej) as Hj.
  pose proof (MEq_of_MAnn HS (MAnn_refl HS Hj0)) as HE0.
  pose proof Ann as (K1 & K2 & Ki & EX1 & EA1 & EB1 & EC1 & Ej1).
  assert (Hcor : [ G ; Γ ⊢g tmCorec l l' li X A B C kc Y c j0 y : tyM l l' li X A B C j0 @ mlvl l l' li ])
    by (apply wf_corec; auto using ge_compt).
  assert (Hcor' : [ G ; Γ ⊢g tmCorec l l' li X A B C kc Y c j0 y : tyM l l' li X A B C j @ mlvl l l' li ]).
  { eapply wf_conv; [exact Hcor | rewrite ge_typeof].
    exact (M_ty_eq ge_typeof ge_notV HE0 (eqtm_sym _ _ _ _ _ _ _ Ej)). }
  pose proof (tmred_wf _ _ _ _ _ _ _ (tmred_out_ann HS Ann (tmred_refl _ _ _ Hcor'))) as Hwf.
  assert (E1 : [ G ; Γ ⊢g tmOut l l' li X A B C j0 (tmCorec l l' li X A B C kc Y c j0 y)
                 ≅ tmOut k1 k2 ki X1 A1 B1 C1 j1 (tmCorec l l' li X A B C kc Y c j0 y)
                 : mOutTy l l' li X A B C j0 @ lmax l (mlvl l l' li) ]).
  { apply eqtm_out; auto using ge_compt, lequiv_sym, eqtm_refl.
    exact (eqtm_trans _ _ _ _ _ _ _ _ Ej Ej1). }
  assert (E2 : [ G ; Γ ⊢g tmOut l l' li X A B C j0 (tmCorec l l' li X A B C kc Y c j0 y)
                 ≅ mOutCorec l l' li X A B C kc Y c j0 y : mOutTy l l' li X A B C j0 @ lmax l (mlvl l l' li) ])
    by (apply eqtm_out_corec; auto using ge_compt).
  split; [exact Hwf | econstructor; [apply red_out_corec | constructor] |].
  eapply eqtm_conv; [exact (eqtm_trans _ _ _ _ _ _ _ _ (eqtm_sym _ _ _ _ _ _ _ E1) E2) | rewrite ge_typeof].
  exact (M_out_eq ge_typeof ge_notV HE0 Hj Hj0 (eqtm_sym _ _ _ _ _ _ _ Ej)).
Qed.

(** The right-hand step at its own signature, carrier and context, from
    its typing at the left-hand ones (as in [pre_corec_r]). *)
Lemma pre_step_r {G Γ l l' li k k' ki X X' A A' B B' C C' kc kc' Y Y' c'} :
  MEq (G := G) (i := ge_layer) Γ l l' li k k' ki X X' A A' B B' C C' -> lequiv (gL G) kc kc' ->
  [ G ; Γ ,, X @ li ⊢g Y ≅ Y' @ kc ] -> [ G ; Γ ,, X @ li ⊢g Y @ kc ] -> [ G ; Γ ,, X @ li ⊢g Y' @ kc ] ->
  [ G ; Γ ,, X @ li ,, Y @ kc ⊢g c' : (mStepTy l l' li X A B C kc Y)⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ] ->
  [ G ; Γ ,, X' @ ki ⊢g Y' @ kc' ] /\
  [ G ; Γ ,, X' @ ki ,, Y' @ kc' ⊢g c' : (mStepTy k k' ki X' A' B' C' kc' Y')⟨↑⟩
      @ lmax k (lmax kc' (mlvl k k' ki)) ].
Proof using .
  intros HE Hkc HYY HY HY' Hc'.
  pose proof (MEq_ids ge_typeof ge_notV HE) as (Hid1 & _).
  pose proof HE as (Hlk & Hlk' & Hlik & HS & HXX & _).
  assert (Hff : lequiv (gL G) (mlvl l l' li) (mlvl k k' ki))
    by exact (lequiv_max _ _ _ _ _ (lequiv_max _ _ _ _ _ Hlk Hlk') Hlik).
  assert (HLc : lequiv (gL G) (lmax l (lmax kc (mlvl l l' li))) (lmax k (lmax kc' (mlvl k k' ki))))
    by exact (lequiv_max _ _ _ _ _ Hlk (lequiv_max _ _ _ _ _ Hkc Hff)).
  assert (HΓXY : [ G ; Γ ,, X @ li ,, Y @ kc ⊢g ]) by exact (ext_wf_g HY (lequiv_wf_l _ _ _ Hkc)).
  pose proof (M_id ge_typeof Hid1 HY HYY HY' Hkc) as HidY.
  assert (ES : [ G ; Γ ,, X @ li ,, Y @ kc ⊢g (mStepTy l l' li X A B C kc Y)⟨↑⟩
                 ≅ (mStepTy k k' ki X' A' B' C' kc' Y')⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ])
    by exact (M_wk_eqty ge_typeof (M_step_eq ge_typeof ge_notV HE Hkc HY HYY) (wkr_shift1 _ _ _) HΓXY).
  split.
  - eapply wft_lconv; [exact (M_mv_ty ge_typeof Hid1 HY') | apply lequiv_sym, Hkc].
  - eapply wf_lconv; [| apply lequiv_sym, HLc].
    exact (M_mv_tm ge_typeof HidY (conv_tm' ge_typeof Hc' (eqty_sym _ _ _ _ _ _ ES))).
Qed.

(** ** [corec] at related premises *)

Section CorecV.
Context {G : gctx} {Γ : ctx} {l l' li k k' ki kc kc' : lvl} {X X' A A' B B' Y Y' : ty} {C C' c c' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l') (Hwli : lwf (gL G) li) (Hwc : lwf (gL G) kc)
  (Hk : lequiv (gL G) k l) (Hk' : lequiv (gL G) k' l') (Hki : lequiv (gL G) ki li) (Hkc : lequiv (gL G) kc' kc)
  (VX : VTyG G Γ X X' li) (VA : VTyG G (Γ ,, X @ li) A A' l)
  (VB : VTyG G (Γ ,, X @ li ,, A @ l) B B' l')
  (VC : VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li)
  (VY : VTyG G (Γ ,, X @ li) Y Y' kc)
  (Vstep : VTyG G (Γ ,, X @ li) (mStepTy l l' li X A B C kc Y) (mStepTy k k' ki X' A' B' C' kc' Y')
             (lmax l (lmax kc (mlvl l l' li))))
  (Vc : VTmG G (Γ ,, X @ li ,, Y @ kc) c c' (mStepTy l l' li X A B C kc Y)⟨↑⟩ (lmax l (lmax kc (mlvl l l' li))))
  {Δ : ctx} {d d' : lsub} (Hd : SubRel G Γ Δ d d').

Let Lc := lmax l (lmax kc (mlvl l l' li)).
Let Nd := proj1 (SubRel_nf _ _ _ _ _ Hd).
Let Nd' := proj2 (SubRel_nf _ _ _ _ _ Hd).

(** The premises in a world [U], at [d] and at [d']. *)
Local Notation sX U := (kty U X[d]).
Local Notation sA U := (ktyl U A[llift d]).
Local Notation sB U := (ktyll U B[llift (llift d)]).
Local Notation sC U := (ktmlll U C[llift (llift (llift d))]).
Local Notation sY U := (ktyl U Y[llift d]).
Local Notation sc U := (ktmll U c[llift (llift d)]).
Local Notation qX U := (kty U X[d']).
Local Notation qY U := (ktyl U Y[llift d']).
Local Notation rX U := (kty U X'[d']).
Local Notation rA U := (ktyl U A'[llift d']).
Local Notation rB U := (ktyll U B'[llift (llift d')]).
Local Notation rC U := (ktmlll U C'[llift (llift (llift d'))]).
Local Notation rY U := (ktyl U Y'[llift d']).
Local Notation rc U := (ktmll U c'[llift (llift d')]).

(** The step at related indices and seeds, at both sides' own step
    types. *)
Lemma c_at (U : kwk G Δ) j0 j0' y0 y0' :
  LRtm li (kw_G U) (kw_Δ U) (sX U) (qX U) j0 j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y0 y0' ->
  LRtm Lc (kw_G U) (kw_Δ U)
    (mStepTy l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U))[lsingle j0]
    (mStepTy k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U))[lsingle j0']
    (sc U)[lsingle2 j0 y0] (rc U)[lsingle2 j0' y0'].
Proof using EL VL VN Vc Vstep Hd.
  intros hj hy. pose proof (SubRel_kw _ _ _ U _ _ Hd) as HdU.
  rewrite !kty_subst in hj. rewrite !ktyl_subst_single in hy.
  pose proof (Vc _ _ (kw_gok U)) as VcU. rewrite !gwa_cext, gwa_ren_ty, gwa_mStepTy in VcU.
  pose proof (VcU _ _ _ (SubRel_cons (SubRel_cons HdU hj) hy)) as Xc.
  rewrite !shift_cons_ty', <- !(ktmll_single2 _ _ _ _ _ Nd), <- !(ktmll_single2 _ _ _ _ _ Nd') in Xc.
  pose proof (Vstep _ _ (kw_gok U)) as VsU. rewrite gwa_cext, !gwa_mStepTy in VsU.
  pose proof (VsU _ _ _ (SubRel_cons HdU hj)) as Xs.
  rewrite <- (lift_single_ty _ _ _ (kwsub_nf U _ Nd)), <- (lift_single_ty _ _ _ (kwsub_nf U _ Nd')) in Xc.
  rewrite <- (lift_single_ty _ _ _ (kwsub_nf U _ Nd)), <- (lift_single_ty _ _ _ (kwsub_nf U _ Nd')) in Xs.
  rewrite <- !gwa_mStepTy, (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd), (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd') in Xc.
  rewrite <- !gwa_mStepTy, (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd), (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd') in Xs.
  exact (LRtm_irrel_r Xc Xs).
Qed.

(** The premises' escapes in a world: the signatures, the carrier and
    the step (both steps in the left-hand context at the left-hand step
    type). *)
Lemma esc_at (U : kwk G Δ) :
  MGeq (kw_G U) (kw_Δ U) l l' li (sX U) (sA U) (sB U) (sC U) k k' ki (rX U) (rA U) (rB U) (rC U) /\
  [ kw_G U ; kw_Δ U ,, sX U @ li ⊢g sY U @ kc ] /\ [ kw_G U ; kw_Δ U ,, sX U @ li ⊢ sY U ≈ rY U @ kc ] /\
  [ kw_G U ; kw_Δ U ,, sX U @ li ,, sY U @ kc ⊢g sc U
      : (mStepTy l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U))⟨↑⟩ @ Lc ] /\
  [ kw_G U ; kw_Δ U ,, sX U @ li ,, sY U @ kc ⊢g rc U
      : (mStepTy l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U))⟨↑⟩ @ Lc ] /\
  [ kw_G U ; kw_Δ U ,, sX U @ li ,, sY U @ kc ⊢ sc U ≈ rc U
      : (mStepTy l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U))⟨↑⟩ @ Lc ].
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hd.
  pose proof (MSide_kw U (m_side Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd)) as HM.
  pose proof (SubRel_kw _ _ _ U _ _ Hd) as HdU.
  pose proof (VTyG_loc (VTyG_gwk VX (kw_gok U))) as VXU.
  destruct (VXU _ _ _ HdU) as [RX HRX]. destruct (escape_ty _ _ _ _ _ _ _ _ HRX) as (HXD & _ & _).
  pose proof (SubRel_lift HdU (VTy_refl_l VXU) HXD (kw_lwf U Hwli)) as Hl1.
  pose proof (VY _ _ (kw_gok U)) as VYU. rewrite gwa_cext in VYU.
  destruct (VYU _ _ _ Hl1) as [RY HRY]. destruct (escape_ty _ _ _ _ _ _ _ _ HRY) as (HYD & _ & EY).
  pose proof (SubRel_lift Hl1 (VTy_refl_l VYU) HYD (kw_lwf U Hwc)) as Hl2.
  pose proof (Vc _ _ (kw_gok U)) as VcU. rewrite !gwa_cext, gwa_ren_ty, gwa_mStepTy in VcU.
  pose proof (VcU _ _ _ Hl2) as Xc. destruct (LRtm_escape Xc) as [Hc Hc']. pose proof (LRtm_geq Xc) as Ec.
  rewrite !shift_llift_ty, <- !gwa_mStepTy, (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd) in Hc, Hc', Ec.
  rewrite <- !(ktmll_subst_lift2 U c d) in Hc, Ec. rewrite <- !(ktmll_subst_lift2 U c' d') in Hc', Ec.
  rewrite <- !(ktyl_subst_lift U d Y) in HYD, EY, Hc, Hc', Ec.
  rewrite <- !(ktyl_subst_lift U d' Y') in EY.
  rewrite <- !(kty_subst U X d) in HYD, EY, Hc, Hc', Ec.
  exact (conj (ms_geq HM) (conj HYD (conj EY (conj Hc (conj Hc' Ec))))).
Qed.

End CorecV.

End MCorec.
