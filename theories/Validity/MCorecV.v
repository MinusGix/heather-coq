(** * Validity of [corec], the depth induction (M18_DESIGN.md, M18b)

    Related [corec]s, at related premises, are related at [M] at every
    depth [n]: at depth [S n] their [out]s step to [mOutCorec]'s pairs,
    whose first components are the steps' first projections and whose
    second components' applications [case] on the steps' continuations,
    a further [corec] (related at depth [n] by the induction hypothesis)
    or a finished [M] term (related at every depth). *)
From DeLaM.Validity Require Export MCorec.
From DeLaM.LogRel Require Import MAux.
From DeLaM.Typing Require Import PresupM.

Local Ltac mfold := repeat change (ren_ty ?x ?r) with x⟨r⟩; repeat change (subst_ty ?x ?e) with x[e];
  repeat change (ren_tm ?x ?r) with x⟨r⟩; repeat change (subst_tm ?x ?e) with x[e].
Local Ltac meq' := meq; repeat (rewrite ?Nat.add_0_r, ?llk_llift; mfold; meq).

(** The step type at an index is a [Σ] over the second component. *)
Lemma mStepTy_single l l' li X A B C k Y j :
  (mStepTy l l' li X A B C k Y)[lsingle j] =
  tySig l (lmax k (mlvl l l' li)) A[lsingle j] (mStepSnd l l' li X A B C k Y j).
Proof using . reflexivity. Qed.

(** The step's continuation type at a position. *)
Lemma mSum_single l l' li k (X A B Y : ty) (C j s p : tm) :
  nfty X -> nfty A -> nfty B -> nfty Y -> nftm C -> nftm j -> nftm s ->
  (tySum k (mlvl l l' li) Y⟨rlift ↑⟩[lsingle C[llift (lsingle2 j s)]]
     (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle2 j s)]))[lsingle p] =
  tySum k (mlvl l l' li) Y[lsingle C[lsingle3 j s p]] (tyM l l' li X A B C C[lsingle3 j s p]).
Proof using . intros. meq'. Qed.

Section MCorecV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.
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

(** The two sides' [corec]s in a world, and the canonical relations. *)
Local Notation crL U j0 y0 := (tmCorec l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0).
Local Notation crR U j0 y0 := (tmCorec k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0).
Local Notation mI := (mIdx (G := G) (X := X) (X' := X') (l := l) (l' := l') (li := li) Δ d d').
Local Notation mS := (mSh (G := G) (A := A) (A' := A') (l := l) (l' := l') (li := li) Δ d d').
Local Notation mP := (mPos (G := G) (B := B) (B' := B') (l := l) (l' := l') (li := li) Δ d d').

(** The arguments of related [corec]s in a world: indices [i], [i']
    related by [mI] that the [corec]s claim, their own indices [j0], [j0']
    related to the claimed ones, and seeds related at the carrier at the
    own indices. Their typings and generic equalities, at the left. *)
Lemma args_at (U : kwk G Δ) i i' j0 j0' y y' :
  mI U i i' -> LRtm li (kw_G U) (kw_Δ U) (sX U) (sX U) i j0 -> LRtm li (kw_G U) (kw_Δ U) (qX U) (qX U) i' j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  LRtm li (kw_G U) (kw_Δ U) (sX U) (qX U) j0 j0' /\
  [ kw_G U ; kw_Δ U ⊢g i : sX U @ li ] /\ [ kw_G U ; kw_Δ U ⊢g i' : sX U @ li ] /\
  [ kw_G U ; kw_Δ U ⊢g j0 : sX U @ li ] /\ [ kw_G U ; kw_Δ U ⊢g j0' : sX U @ li ] /\
  [ kw_G U ; kw_Δ U ⊢ i ≈ i' : sX U @ li ] /\ [ kw_G U ; kw_Δ U ⊢ i ≈ j0 : sX U @ li ] /\
  [ kw_G U ; kw_Δ U ⊢ j0 ≈ j0' : sX U @ li ] /\
  [ kw_G U ; kw_Δ U ⊢g y : (sY U)[lsingle j0] @ kc ] /\ [ kw_G U ; kw_Δ U ⊢g y' : (sY U)[lsingle j0] @ kc ] /\
  [ kw_G U ; kw_Δ U ⊢ y ≈ y' : (sY U)[lsingle j0] @ kc ].
Proof using EL VL VN VX Hd.
  intros hi hj hj' hy. pose proof (proj1 (mIdx_iff VX Hd U i i') hi) as Hii.
  pose proof (LRtm_trans (LRtm_sym hj) (LRtm_trans Hii hj')) as hjj.
  destruct (LRtm_escape Hii) as [Hi Hi']. destruct (LRtm_escape hjj) as [Hj0 Hj0'].
  destruct (LRtm_escape hy) as [Hy Hy'].
  exact (conj hjj (conj Hi (conj Hi' (conj Hj0 (conj Hj0' (conj (LRtm_geq Hii) (conj (LRtm_geq hj)
           (conj (LRtm_geq hjj) (conj Hy (conj Hy' (LRtm_geq hy))))))))))).
Qed.

(** Both sides typed at the left signature at the claimed index, and
    generically equal there. *)
Lemma typ_at (U : kwk G Δ) i i' j0 j0' y y' :
  mI U i i' -> LRtm li (kw_G U) (kw_Δ U) (sX U) (sX U) i j0 -> LRtm li (kw_G U) (kw_Δ U) (qX U) (qX U) i' j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  [ kw_G U ; kw_Δ U ⊢g crL U j0 y : tyM l l' li (sX U) (sA U) (sB U) (sC U) i @ mlvl l l' li ] /\
  [ kw_G U ; kw_Δ U ⊢g crR U j0' y' : tyM l l' li (sX U) (sA U) (sB U) (sC U) i @ mlvl l l' li ] /\
  [ kw_G U ; kw_Δ U ⊢ crL U j0 y ≈ crR U j0' y' : tyM l l' li (sX U) (sA U) (sB U) (sC U) i @ mlvl l l' li ].
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hi hj hj' hy.
  destruct (args_at U i i' j0 j0' y y' hi hj hj' hy)
    as (hjj & Hi & Hi' & Hj0 & Hj0' & Eii & Eij & Ejj & Hy & Hy' & Eyy).
  destruct (esc_at U) as (HG & HY & EY & Hc & Hc' & Ec).
  pose proof (MEq_of_MGeq HG) as HE. pose proof HE as (_ & _ & _ & HS & _).
  pose proof HG as (H1 & H2 & H3 & _ & EX & EA & EB & EC).
  pose proof HS as (W1 & W2 & Wi & HX & HA & HB & HC).
  pose proof (kw_lwf U Hwc) as Wc.
  pose proof (geq_ty_sound EY) as DY. pose proof (eqty_wf_r ge_typeof DY) as HY'.
  pose proof (geq_tm_sound Eij) as Dij.
  pose proof (MEq_of_MAnn HS (MAnn_refl HS Hi)) as HE0.
  assert (Ei : [ kw_G U ; kw_Δ U ⊢g tyM l l' li (sX U) (sA U) (sB U) (sC U) i
                  ≅ tyM l l' li (sX U) (sA U) (sB U) (sC U) j0 @ mlvl l l' li ])
    by exact (M_ty_eq ge_typeof ge_notV HE0 Dij).
  assert (HL : [ kw_G U ; kw_Δ U ⊢g crL U j0 y : tyM l l' li (sX U) (sA U) (sB U) (sC U) j0 @ mlvl l l' li ])
    by (apply wf_corec; auto using ge_compt).
  assert (Hyi' : [ kw_G U ; kw_Δ U ⊢g y' : (sY U)[lsingle i] @ kc ]).
  { eapply wf_conv; [exact Hy' | rewrite ge_typeof].
    apply (wf_ty_func ge_typeof HY), (lsub_eq_single ge_typeof); [exact Hi | exact Hj0 | exact Dij]. }
  assert (HR : [ kw_G U ; kw_Δ U ⊢g crR U j0' y' : tyM l l' li (sX U) (sA U) (sB U) (sC U) i @ mlvl l l' li ]).
  { eapply (pre_corec_r ge_typeof ge_notV HE (lequiv_sym _ _ _ (kw_lequiv U Hkc)) DY HY HY' Hc' Hi Hj0').
    - eapply eqtm_trans; [exact Dij | exact (geq_tm_sound Ejj)].
    - exact Hyi'. }
  refine (conj (wf_conv _ _ _ _ _ _ _ HL _) (conj HR _)); [rewrite ge_typeof; exact Ei |].
  eapply geq_tm_conv; [| apply eqty_sym, Ei].
  apply geq_tm_corec; auto using geq_ty_sound, geq_tm_sound, lequiv_sym, kw_lequiv.
Qed.

(** The step's projections at the own indices: its first projections,
    and its continuations at related positions. *)
Local Notation fL U j0 y0 := (mOutFst l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0).
Local Notation fR U j0 y0 := (mOutFst k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0).
Local Notation iL U j0 y0 p := ((sC U)[lsingle3 j0 (fL U j0 y0) p]).
Local Notation iR U j0 y0 p := ((rC U)[lsingle3 j0 (fR U j0 y0) p]).
Local Notation scL U j0 y0 p :=
  (app (tmSnd l (lmax kc (mlvl l l' li)) (sA U)[lsingle j0]
          (mStepSnd l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) j0) (sc U)[lsingle2 j0 y0])
     l' (lmax kc (mlvl l l' li)) (sB U)[lsingle2 j0 (fL U j0 y0)]
     (tySum kc (mlvl l l' li) (sY U)⟨rlift ↑⟩[lsingle (mOutIdx l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0)]
        (tyM l l' li (sX U)⟨↑⟩ (sA U)⟨rlift ↑⟩ (sB U)⟨rlift (rlift ↑)⟩ (sC U)⟨rlift (rlift (rlift ↑))⟩
           (mOutIdx l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0))) p).
Local Notation scR U j0 y0 p :=
  (app (tmSnd k (lmax kc' (mlvl k k' ki)) (rA U)[lsingle j0]
          (mStepSnd k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) j0) (rc U)[lsingle2 j0 y0])
     k' (lmax kc' (mlvl k k' ki)) (rB U)[lsingle2 j0 (fR U j0 y0)]
     (tySum kc' (mlvl k k' ki) (rY U)⟨rlift ↑⟩[lsingle (mOutIdx k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0)]
        (tyM k k' ki (rX U)⟨↑⟩ (rA U)⟨rlift ↑⟩ (rB U)⟨rlift (rlift ↑)⟩ (rC U)⟨rlift (rlift (rlift ↑))⟩
           (mOutIdx k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0))) p).

Lemma steps_at (U : kwk G Δ) j0 j0' y y' :
  LRtm li (kw_G U) (kw_Δ U) (sX U) (qX U) j0 j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  LRtm l (kw_G U) (kw_Δ U) (sA U)[lsingle j0] (rA U)[lsingle j0'] (fL U j0 y) (fR U j0' y') /\
  forall p p', LRtm l' (kw_G U) (kw_Δ U) (sB U)[lsingle2 j0 (fL U j0 y)] (rB U)[lsingle2 j0' (fR U j0' y')] p p' ->
  LRtm (lmax kc (mlvl l l' li)) (kw_G U) (kw_Δ U)
    (tySum kc (mlvl l l' li) (sY U)[lsingle (iL U j0 y p)] (tyM l l' li (sX U) (sA U) (sB U) (sC U) (iL U j0 y p)))
    (tySum kc' (mlvl k k' ki) (rY U)[lsingle (iR U j0' y' p')] (tyM k k' ki (rX U) (rA U) (rB U) (rC U) (iR U j0' y' p')))
    (scL U j0 y p) (scR U j0' y' p').
Proof using EL VL VN Vc Vstep Hd.
  intros hjj hy. pose proof (c_at U j0 j0' y y' hjj hy) as Xc.
  rewrite !mStepTy_single in Xc. destruct (LRtm_sig_proj Xc) as [Ff Fs].
  split; [exact Ff|]. intros p p' hp.
  destruct (LRtm_escape hjj) as [Hj0 Hj0']. destruct (LRtm_escape Ff) as [Hf Hf'].
  rewrite (M_E_snd _ _ _ _ _ _ _ _ _ j0) in Fs by first [kw_nf | exact (wf_tm_nf Hj0)].
  rewrite (M_E_snd _ _ _ _ _ _ _ _ _ j0') in Fs by first [kw_nf | exact (wf_tm_nf Hj0')].
  pose proof (LRtm_pi_app Fs hp) as Xa.
  rewrite (mSum_single _ _ _ _ _ _ _ _ _ j0) in Xa by first [kw_nf | exact (wf_tm_nf Hj0) | exact (wf_tm_nf Hf)].
  rewrite (mSum_single _ _ _ _ _ _ _ _ _ j0') in Xa by first [kw_nf | exact (wf_tm_nf Hj0') | exact (wf_tm_nf Hf')].
  exact Xa.
Qed.

End CorecV.

End MCorecV.
