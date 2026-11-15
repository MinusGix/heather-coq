(** * [elim_IWi]'s children's [dnth], valid (M19_DESIGN.md, M19b)

    As [IWfElim]'s [elimIWf_Vdnth]: the [dnth] of the induction
    hypothesis's body, in [Γ, x : A, cs : csty, i : Fin N], valid at the
    children's family [iwiFc] (a field's [Π] there), and at a Kripke
    weakening of the shape and children's substitution, at related indices,
    related at the field's [Π]. The family's validity is [IWi]'s
    ([VG_iwi]) under the field's [Π], with the signature weakened under its
    binders ([VG_lift2_ty], [VG_lift3_tm]). *)
From DeLaM.Validity Require Export IWiElimBase.
From DeLaM.Typing Require Import IWiIH.
From DeLaM.LogRel Require Import IWfAux IWiAux MAux.
From DeLaM.Validity Require Import DVecNth WfNth WfElim M MCorec.

(** ** Validity under inserted binders *)

Section Lift.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Lemma lift3_subst_ty (T : ty) e :
  T⟨rlift (rlift (rlift ↑))⟩[e] =
  T[lcons (lcons (lcons (ldrop 1 (ldrop 1 (ldrop 1 (ldrop 1 e)))) (llk (ldrop 1 (ldrop 1 e)) 0))
          (llk (ldrop 1 e) 0)) (llk e 0)].
Proof using .
  apply ren_subst_ty.
  intros [|[|[|m]]]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.
Lemma lift3_subst_tm (t : tm) e :
  t⟨rlift (rlift (rlift ↑))⟩[e] =
  t[lcons (lcons (lcons (ldrop 1 (ldrop 1 (ldrop 1 (ldrop 1 e)))) (llk (ldrop 1 (ldrop 1 e)) 0))
          (llk (ldrop 1 e) 0)) (llk e 0)].
Proof using .
  apply ren_subst.
  intros [|[|[|m]]]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.

Lemma VTy_lift2 {G Γ A B T T' D kd ka k l} : VTy G (Γ ,, A @ ka ,, B @ k) T T' l ->
  VTy G (Γ ,, D @ kd ,, A⟨↑⟩ @ ka ,, B⟨rlift ↑⟩ @ k) T⟨rlift (rlift ↑)⟩ T'⟨rlift (rlift ↑)⟩ l.
Proof using .
  intros H Δ d d' [[[Hd _] Ha] Hb]. rewrite !shift_subst_ty in Ha. rewrite !lift1_subst_ty in Hb.
  rewrite !lift2_subst_ty. exact (H _ _ _ (SubRel_cons (SubRel_cons Hd Ha) Hb)).
Qed.
Lemma VG_lift2_ty {G Γ A B T T' D kd ka k l} : VTyG G (Γ ,, A @ ka ,, B @ k) T T' l ->
  VTyG G (Γ ,, D @ kd ,, A⟨↑⟩ @ ka ,, B⟨rlift ↑⟩ @ k) T⟨rlift (rlift ↑)⟩ T'⟨rlift (rlift ↑)⟩ l.
Proof using . intros. gl_lift. now apply VTy_lift2. Qed.

Lemma VTm_lift3 {G Γ A B C t t' T D kd ka kb k l} : VTm G (Γ ,, A @ ka ,, B @ kb ,, C @ k) t t' T l ->
  VTm G (Γ ,, D @ kd ,, A⟨↑⟩ @ ka ,, B⟨rlift ↑⟩ @ kb ,, C⟨rlift (rlift ↑)⟩ @ k)
    t⟨rlift (rlift (rlift ↑))⟩ t'⟨rlift (rlift (rlift ↑))⟩ T⟨rlift (rlift (rlift ↑))⟩ l.
Proof using .
  intros H Δ d d' [[[[Hd _] Ha] Hb] Hc]. rewrite !shift_subst_ty in Ha. rewrite !lift1_subst_ty in Hb.
  rewrite !lift2_subst_ty in Hc.
  rewrite !lift3_subst_ty, !lift3_subst_tm. exact (H _ _ _ (SubRel_cons (SubRel_cons (SubRel_cons Hd Ha) Hb) Hc)).
Qed.
Lemma VG_lift3_tm {G Γ A B C t t' T D kd ka kb k l} : VTmG G (Γ ,, A @ ka ,, B @ kb ,, C @ k) t t' T l ->
  VTmG G (Γ ,, D @ kd ,, A⟨↑⟩ @ ka ,, B⟨rlift ↑⟩ @ kb ,, C⟨rlift (rlift ↑)⟩ @ k)
    t⟨rlift (rlift (rlift ↑))⟩ t'⟨rlift (rlift (rlift ↑))⟩ T⟨rlift (rlift (rlift ↑))⟩ l.
Proof using . intros. gl_lift. now apply VTm_lift3. Qed.

Lemma VG_iwi {G Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' m m'} :
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li ->
  lequiv (gL G) k l -> lequiv (gL G) kp lp -> lequiv (gL G) ki li ->
  VTyG G Γ X X' li -> VTyG G Γ A A' l -> VTmG G (Γ ,, A @ l) N N' tyNat lzero ->
  VTyG G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp ->
  VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li ->
  VTmG G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  VTmG G Γ m m' X li ->
  VTyG G Γ (tyIWi l lp li X A N D Ot C m) (tyIWi k kp ki X' A' N' D' Ot' C' m') (iwiL l lp li).
Proof using EL VL VN.
  intros Hwl Hwlp Hwli Hk Hkp Hki VX VA VNt VD VO VC Vm. apply VTyG_intro. intros G' γ Hγ _.
  pose proof (VTyG_gwk VX Hγ) as VXγ. pose proof (VTyG_gwk VA Hγ) as VAγ.
  pose proof (VTmG_gwk VNt Hγ) as VNγ. rewrite gwa_cext, gwa_tyNat in VNγ.
  pose proof (VTyG_gwk VD Hγ) as VDγ. rewrite !gwa_cext, gwa_tyFin in VDγ.
  pose proof (VTmG_gwk VO Hγ) as VOγ. rewrite gwa_cext, gwa_ren_ty in VOγ.
  pose proof (VTmG_gwk VC Hγ) as VCγ. rewrite !gwa_cext, gwa_tyFin, !gwa_ren_ty in VCγ.
  pose proof (VTmG_loc (VTmG_gwk Vm Hγ)) as Vmγ.
  rewrite !gwa_tyIWi.
  exact (V_iwi_at (lwf_weaken _ _ _ (proj1 Hγ) Hwl) (lwf_weaken _ _ _ (proj1 Hγ) Hwlp)
           (lwf_weaken _ _ _ (proj1 Hγ) Hwli) (lequiv_weaken _ _ _ _ (proj1 Hγ) Hk)
           (lequiv_weaken _ _ _ _ (proj1 Hγ) Hkp) (lequiv_weaken _ _ _ _ (proj1 Hγ) Hki)
           VXγ VAγ VNγ VDγ VOγ VCγ Vmγ).
Qed.

Lemma kγ_tmlll {G Δ} (ρ : kwk G Δ) (t : tm) γ e :
  ktmlll ρ t⟦γ⟧[llift (llift (llift e))] = t⟦gwk_comp (kw_γ ρ) γ⟧[llift (llift (llift (kwsub ρ e)))].
Proof using . now rewrite ktmlll_subst_lift, gwa_comp_tm. Qed.

Lemma ktml_lam {G Δ} (ρ : kwk G Δ) l l' A t : ktml ρ (lam l l' A t) = lam l l' (ktyl ρ A) (ktmll ρ t).
Proof using . unfold ktml, ktyl, ktmll. now rewrite gwa_lam. Qed.
Lemma ktyl_tyPi' {G Δ} (ρ : kwk G Δ) l l' A B : ktyl ρ (tyPi l l' A B) = tyPi l l' (ktyl ρ A) (ktyll ρ B).
Proof using . unfold ktyl, ktyll. now rewrite gwa_tyPi. Qed.

(** λ-introduction under two binders: two double λs whose bodies are
    related at related arguments in every world are related at the
    [Π]s. *)
Lemma LRtm_lam2_K {L G Δ l1 l2 l3 k1 k2 k3 A A' B B' C T b b'} :
  LRty L G Δ (tyPi l1 (lmax l2 l3) A (tyPi l2 l3 B C)) T ->
  lequiv (gL G) k1 l1 -> lequiv (gL G) k2 l2 -> lequiv (gL G) k3 l3 ->
  [ G ; Δ ⊢ A ≈ A' @ l1 ] -> nfty B' -> nftm b -> nftm b' ->
  (forall (ρ : kwk G Δ) i i' T1, LRtm l1 (kw_G ρ) (kw_Δ ρ) (kty ρ A) T1 i i' ->
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle i] ≈ (ktyl ρ B')[lsingle i'] @ l2 ]) ->
  (forall (ρ : kwk G Δ) i i' T1 y y' T2, LRtm l1 (kw_G ρ) (kw_Δ ρ) (kty ρ A) T1 i i' ->
     LRtm l2 (kw_G ρ) (kw_Δ ρ) (ktyl ρ B)[lsingle i] T2 y y' ->
     LRtm l3 (kw_G ρ) (kw_Δ ρ) (ktyll ρ C)[lsingle2 i y] (ktyll ρ C)[lsingle2 i y]
       (ktmll ρ b)[lsingle2 i y] (ktmll ρ b')[lsingle2 i' y']) ->
  LRtm L G Δ (tyPi l1 (lmax l2 l3) A (tyPi l2 l3 B C)) T
    (lam l1 (lmax l2 l3) A (lam l2 l3 B b)) (lam k1 (lmax k2 k3) A' (lam k2 k3 B' b')).
Proof using EL VL VN.
  intros HT H1 H2 H3 EA NB' Nb Nb' EB HK.
  pose proof HT as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HPi & _ & _).
  pose proof (wf_ty_nf HPi) as NPi. cbn [nfty] in NPi. destruct NPi as (_ & NB & _).
  destruct (LR_inv_pi HR (tyred_refl _ _ HPi)) as (p3 & p4 & P2 & Q2 & domR & codR & PF & domAd & codAd & HRR).
  destruct PF as [Hlv _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof (lmeasure_le_l Hlv) as Hle1. pose proof (lmeasure_le_r Hlv) as Hle2.
  apply (LRtm_lam_K HT H1 (lequiv_max _ _ _ _ _ H2 H3) EA); [cbn; auto | cbn; auto |].
  intros ρ i i' T1 Hi.
  pose proof (domAd ρ) as DOM. apply (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle1)) in DOM.
  pose proof (LRtm_inv DOM (LRtm_irrel_r Hi (ex_intro _ _ DOM))) as hy.
  pose proof (codAd ρ i i' hy) as COD. apply (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle2)) in COD.
  destruct (LRtm_escape Hi) as [Hit Hi't]. pose proof (wf_tm_nf Hit) as Ni. pose proof (wf_tm_nf Hi't) as Ni'.
  rewrite ktyl_tyPi', subst_tyPi in COD |- *. rewrite !ktml_lam, !subst_lam.
  apply LR_refl_l in COD. apply (LRtm_lam_K (ex_intro _ _ COD) (kw_lequiv ρ H2) (kw_lequiv ρ H3) (EB ρ i i' T1 Hi)).
  - apply subst_nf; [apply ren_nf | apply lk_llift, lk_lsingle, Ni].
  - apply subst_nf; [apply ren_nf | apply lk_llift, lk_lsingle, Ni'].
  - intros ρ' y y' T2 Hy.
    rewrite kty_single, <- ktyl_comp in Hy.
    pose proof (LRtm_kw ρ' Hi) as Hi2. rewrite <- kty_comp in Hi2.
    pose proof (HK (kw_comp ρ ρ') _ _ _ _ _ _ Hi2 Hy) as X0.
    assert (Ni2 : nftm (ktm ρ' i)) by apply ren_nf. assert (Ni2' : nftm (ktm ρ' i')) by apply ren_nf.
    rewrite ktyl_llift_single, <- !ktmll_llift_single, <- ktyll_comp, <- !ktmll_comp,
      llift_single_single_ty, !llift_single_single by assumption.
    exact X0.
Qed.

End Lift.

(** ** The children's family under the step's telescope

    [iwicsty]'s family in [Γ, x : A, cs : csty, i : Fin N], under its own
    position binder: [iwiFam] at the shape variable. *)
Notation iwiFc l lp li X A N D Ot C :=
  (iwiFam l lp li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
     D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
     C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ (var 2)).

Lemma iwi_d3_single (D : ty) :
  D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[llift (lsingle (var 2))] = D⟨rlift ↑⟩⟨rlift ↑⟩.
Proof using .
  rewrite !ren_ren_comp_ty, ren_as_r2l_ty, (ren_as_r2l_ty D), subst_comp_ty. apply subst_ext_ty.
  intros [|[|n]]; pw.
Qed.
Lemma iwi_c3_single (C : tm) :
  C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩[llift (llift (lsingle (var 2)))]
  = C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩.
Proof using .
  rewrite !ren_ren_comp, ren_as_r2l, (ren_as_r2l C), subst_comp. apply subst_ext.
  intros [|[|[|n]]]; pw.
Qed.

(** ** The family at the step's substitution *)

Lemma iwiFc_subst l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) d a cs y : LK nftm d ->
  (iwiFc l lp li X A N D Ot C)[llift (lcons (lcons (lcons d a) cs) y)] =
  iwiFam l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))] a.
Proof using .
  intros Hd. unfold iwiFam, iwiFamCod. meq.
  all: rewrite ?shift_llift, ?shift_single by apply Hd.
  all: replace (n + 0) with n by lia; reflexivity.
Qed.

Lemma iwi_dnthv_subst l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) d a cs y : LK nftm d ->
  nftm a -> nftm cs -> nftm y ->
  (tmDNth (iwiL l lp li) N⟨↑⟩⟨↑⟩ (iwiFc l lp li X A N D Ot C) (var 1) (var 0))[lcons (lcons (lcons d a) cs) y] =
  tmDNth (iwiL l lp li) N[llift d][lsingle a]
    (iwiFam l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))] a) cs y.
Proof using .
  intros Hd Na Ncs Ny.
  assert (Hd3 : LK nftm (lcons (lcons (lcons d a) cs) y)) by (intros [|[|[|n]]]; cbn; auto).
  rewrite subst_tmDNth, iwiFc_subst by first [exact Hd3 | exact Hd].
  rewrite !shift_subst_tm. cbn [ldrop]. rewrite lift_single_tm by exact Hd. reflexivity.
Qed.

Lemma iwiFc_single_subst l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) d a cs y : LK nftm d ->
  nftm a -> nftm cs -> nftm y ->
  nfty X[d] -> nfty A[d] -> nftm N[llift d] -> nfty D[llift (llift d)] -> nftm Ot[llift d] ->
  nftm C[llift (llift (llift d))] ->
  (iwiFc l lp li X A N D Ot C)[lsingle (var 0)][lcons (lcons (lcons d a) cs) y] =
  iwiFieldT l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))]
    D[llift (llift d)][lsingle2 a y] C[llift (llift (llift d))][llift (lsingle2 a y)].
Proof using .
  intros Hd Na Ncs Ny NX NA NN ND NO NC.
  assert (Hd3 : LK nftm (lcons (lcons (lcons d a) cs) y)) by (intros [|[|[|n]]]; cbn; auto).
  rewrite single_subst_ty, iwiFc_subst by first [exact Hd3 | exact Hd]. cbn [subst_tm llk].
  rewrite iwiFam_T, iwiFamT_single, llift_single_single_ty, llift2_single_llift_single by assumption.
  reflexivity.
Qed.


Section Dnth.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.
Context {G : gctx} {Γ : ctx} {l lp li l3 lp3 li3 : lvl} {X X' A A' D D' : ty} {N N' Ot Ot' C C' : tm}
  (Hwl : lwf (gL G) l) (Hwlp : lwf (gL G) lp) (Hwli : lwf (gL G) li)
  (H13 : lequiv (gL G) l l3) (Hp3 : lequiv (gL G) lp lp3) (Hi3 : lequiv (gL G) li li3)
  (HS : IWiSig (G := G) (i := ge_layer) Γ l lp li X A N D Ot C)
  (VX : VTyG G Γ X X' li) (VA : VTyG G Γ A A' l)
  (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (VD : VTyG G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp)
  (VO : VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li)
  (VC : VTmG G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li).

Local Notation L := (iwiL l lp li).

Local Ltac gwkn H := first [ exact H | eapply (wk1_ty _ _ ge_typeof); [eassumption | gwkn H]
                           | eapply (wk1_tm _ _ ge_typeof); [eassumption | gwkn H] ].
Local Ltac gvar := eapply wf_tm_retype; [eapply wf_var; [rewrite ge_typeof; eassumption | repeat constructor]
                                        | cbn; try reflexivity].
Local Ltac vvar := eapply VG_var; [repeat constructor | cbn; try reflexivity].

(** The step's context up to the position, its signature weakened there,
    and the shape variable. *)
Local Notation Θ := (Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ L ,, tyFin N⟨↑⟩ @ lzero).

Lemma elimIWi_ctx :
  [ G ; Θ ⊢g ] /\ IWiSig (G := G) (i := ge_layer) Θ l lp li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
       D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
       C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ /\
    [ G ; Θ ⊢g N⟨↑⟩⟨↑⟩ : tyNat @ lzero ] /\ [ G ; Θ ⊢g var 2 : A⟨↑⟩⟨↑⟩⟨↑⟩ @ l ].
Proof using HS Hwl Hwli Hwlp.
  pose proof HS as (_ & _ & _ & HX & HA & HN & _).
  assert (HwL : lwf (gL G) L) by (repeat split; assumption).
  pose proof (IWi_cs_wf ge_typeof ge_notV HS) as HCs.
  pose proof (ext_wf_g HA Hwl) as H1. pose proof (ext_wf_g HCs HwL) as H2.
  assert (HN1 : [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ L ⊢g N⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [gwkn HN | reflexivity]).
  assert (HF1 : [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ L ⊢g tyFin N⟨↑⟩ @ lzero ])
    by (apply wft_fin; [exact ge_notV | exact HN1]).
  assert (Hw0 : lwf (gL G) lzero) by exact I. pose proof (ext_wf_g HF1 Hw0) as H3.
  refine (conj H3 (conj _ (conj _ _))).
  - exact (IWiSig_wk1 ge_typeof ge_notV (IWiSig_wk1 ge_typeof ge_notV (IWiSig_wk1 ge_typeof ge_notV HS H1) H2) H3).
  - eapply wf_tm_retype; [gwkn HN1 | reflexivity].
  - gvar.
Qed.

(** The children's family, valid under its position binder. *)
Lemma elimIWi_VF :
  [ G ; Θ ,, tyFin N⟨↑⟩⟨↑⟩ @ lzero ⊢g iwiFc l lp li X A N D Ot C @ L ] /\
  VTyG G (Θ ,, tyFin N⟨↑⟩⟨↑⟩ @ lzero)
    (iwiFc l lp li X A N D Ot C) (iwiFc l3 lp3 li3 X' A' N' D' Ot' C') L.
Proof using EL Hi3 H13 HS Hp3 Hwl Hwli Hwlp VA VC VD VL VN VNt VO VX.
  pose proof elimIWi_ctx as (HΘ & HS3 & HN2 & Hv2).
  pose proof (IWi_fam_wf ge_typeof ge_notV HS3 Hv2) as HFam. rewrite n3_single in HFam.
  pose proof (IWi_famcod_wf ge_typeof ge_notV HS3 Hv2) as HCod. rewrite n3_single, iwi_d3_single in HCod.
  split; [exact HFam |].
  eapply VTyG_lconv; [| exact (iwiL_pi _ _ _ _ Hwl Hwlp Hwli)].
  unfold iwiFam. rewrite !iwi_d3_single.
  apply VG_pi; [exact Hwlp | repeat split; assumption | apply lequiv_sym; exact Hp3 | apply lequiv_sym, lequiv_max; [apply lequiv_max|]; assumption | exact HCod | |].
  - exact (VG_lift1 (VG_lift1 VD)).
  - unfold iwiFamCod. rewrite !iwi_c3_single.
    apply VG_iwi; [exact Hwl | exact Hwlp | exact Hwli | exact (lequiv_sym _ _ _ H13) | exact (lequiv_sym _ _ _ Hp3)
                  | exact (lequiv_sym _ _ _ Hi3)
                  | exact (VG_shift (VG_shift (VG_shift (VG_shift (VG_shift VX)))))
                  | exact (VG_shift (VG_shift (VG_shift (VG_shift (VG_shift VA))))) | | | | |].
    + eapply VTmG_retype; [exact (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm VNt))))) | reflexivity].
    + exact (VG_lift2_ty (VG_lift2_ty (VG_lift2_ty (VG_lift2_ty (VG_lift2_ty VD))))).
    + eapply VTmG_retype; [exact (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm VO))))) |].
      now rewrite !IWf_E_ren.
    + eapply VTmG_retype; [exact (VG_lift3_tm (VG_lift3_tm (VG_lift3_tm (VG_lift3_tm (VG_lift3_tm VC))))) |].
      now rewrite !IWi_E_ren3.
    + eapply VTmG_retype; [exact (VG_lift2_tm (VG_lift2_tm VC)) |]. ren_comm.
Qed.

(** M19_DESIGN.md's index lemma at the induction hypothesis's [dnth]. *)
Lemma elimIWi_Vdnth :
  VTmG G Θ (tmDNth L N⟨↑⟩⟨↑⟩ (iwiFc l lp li X A N D Ot C) (var 1) (var 0))
    (tmDNth (iwiL l3 lp3 li3) N'⟨↑⟩⟨↑⟩ (iwiFc l3 lp3 li3 X' A' N' D' Ot' C') (var 1) (var 0))
    (iwiFc l lp li X A N D Ot C)[lsingle (var 0)] L.
Proof using EL Hi3 H13 HS Hp3 Hwl Hwli Hwlp VA VC VD VL VN VNt VO VX.
  assert (HwL : lwf (gL G) L) by (repeat split; assumption).
  assert (HLL : lequiv (gL G) L (iwiL l3 lp3 li3)) by (repeat apply lequiv_max; assumption).
  pose proof elimIWi_ctx as (_ & _ & HN2 & _). pose proof elimIWi_VF as (HFam & VF).
  apply (V_dnth HwL HLL HN2 (VTmG_retype (VG_shift_tm (VG_shift_tm VNt)) eq_refl) HFam VF).
  - eapply VG_var; [repeat constructor |]. rewrite IWi_E_var1, n3_single. reflexivity.
  - vvar.
Qed.

Local Notation sX γ e := (X⟦γ⟧[e]).
Local Notation sX' γ e := (X'⟦γ⟧[e]).
Local Notation sA γ e := (A⟦γ⟧[e]).
Local Notation sA' γ e := (A'⟦γ⟧[e]).
Local Notation sN γ e := (N⟦γ⟧[llift e]).
Local Notation sN' γ e := (N'⟦γ⟧[llift e]).
Local Notation sD γ e := (D⟦γ⟧[llift (llift e)]).
Local Notation sD' γ e := (D'⟦γ⟧[llift (llift e)]).
Local Notation sO γ e := (Ot⟦γ⟧[llift e]).
Local Notation sO' γ e := (Ot'⟦γ⟧[llift e]).
Local Notation sC γ e := (C⟦γ⟧[llift (llift (llift e))]).
Local Notation sC' γ e := (C'⟦γ⟧[llift (llift (llift e))]).

(** The [dnth] in the induction hypothesis's body at a Kripke weakening of
    the shape and children's substitution, at related indices: a field,
    at the field's [Π]. *)
Lemma elimIWi_dnth_kw {G0 γ Δ0 e e' a a' cs cs'} (ρ : kwk G0 Δ0) {y y'} :
  gwk_ok γ G0 G ->
  SubRel G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, iwicsty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ @ L) Δ0
    (lcons (lcons e a) cs) (lcons (lcons e' a') cs') ->
  LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktml ρ (sN γ e))[lsingle (ktm ρ a)])
    (tyFin (ktml ρ (sN γ e'))[lsingle (ktm ρ a')]) y y' ->
  LRtm L (kw_G ρ) (kw_Δ ρ)
    (iwiFieldT l lp li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktyll ρ (sD γ e)) (ktml ρ (sO γ e))
       (ktmlll ρ (sC γ e)) (ktyll ρ (sD γ e))[lsingle2 (ktm ρ a) y] (ktmlll ρ (sC γ e))[llift (lsingle2 (ktm ρ a) y)])
    (iwiFieldT l lp li (kty ρ (sX γ e')) (kty ρ (sA γ e')) (ktml ρ (sN γ e')) (ktyll ρ (sD γ e'))
       (ktml ρ (sO γ e')) (ktmlll ρ (sC γ e')) (ktyll ρ (sD γ e'))[lsingle2 (ktm ρ a') y']
       (ktmlll ρ (sC γ e'))[llift (lsingle2 (ktm ρ a') y')])
    (tmDNth L (ktml ρ (sN γ e))[lsingle (ktm ρ a)]
       (iwiFam l lp li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktyll ρ (sD γ e)) (ktml ρ (sO γ e))
          (ktmlll ρ (sC γ e)) (ktm ρ a)) (ktm ρ cs) y)
    (tmDNth (iwiL l3 lp3 li3) (ktml ρ (sN' γ e'))[lsingle (ktm ρ a')]
       (iwiFam l3 lp3 li3 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e')) (ktyll ρ (sD' γ e'))
          (ktml ρ (sO' γ e')) (ktmlll ρ (sC' γ e')) (ktm ρ a')) (ktm ρ cs') y').
Proof using EL Hi3 H13 HS Hp3 Hwl Hwli Hwlp VA VC VD VL VN VNt VO VX.
  intros Hγ HSc Hy.
  pose proof (SubRel_kw _ _ _ ρ _ _ HSc) as HSρ.
  rewrite !gwa_cext, gwa_iwicsty, gwa_comp_ctx, !gwa_comp_ty, !gwa_comp_tm in HSρ.
  pose proof (elimIWi_Vdnth _ _ (gwk_ok_comp (kw_gok ρ) Hγ)) as Vn.
  rewrite !gwa_cext, gwa_iwicsty in Vn.
  repeat first [rewrite gwa_tyFin in Vn | rewrite gwa_tmDNth in Vn | rewrite gwa_ren_ty in Vn | rewrite gwa_ren in Vn
               | rewrite gwa_iwiFam in Vn | rewrite gwa_var in Vn | rewrite gwa_subst_ty in Vn
               | rewrite gwa_lsingle in Vn].
  assert (Ne : LK nftm (kwsub ρ e)) by (intros n; rewrite llk_kwsub; apply ren_nf).
  assert (Ne' : LK nftm (kwsub ρ e')) by (intros n; rewrite llk_kwsub; apply ren_nf).
  assert (Xy : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin N⟦gwk_comp (kw_γ ρ) γ⟧⟨↑⟩)[kwsub ρ (lcons (lcons e a) cs)]
                 (tyFin N⟦gwk_comp (kw_γ ρ) γ⟧⟨↑⟩)[kwsub ρ (lcons (lcons e' a') cs')] y y').
  { rewrite (subst_ext_ty _ _ _ (kwsub_cons2 ρ e a cs)), (subst_ext_ty _ _ _ (kwsub_cons2 ρ e' a' cs')).
    rewrite !finv_subst, <- !kγ_tml by assumption. exact Hy. }
  pose proof (Vn _ _ _ (SubRel_cons HSρ Xy)) as X0.
  rewrite (subst_ext_ty _ _ _ (kwsub_cons3 ρ e a cs y)), (subst_ext_ty _ _ _ (kwsub_cons3 ρ e' a' cs' y')),
    (subst_ext _ _ _ (kwsub_cons3 ρ e a cs y)), (subst_ext _ _ _ (kwsub_cons3 ρ e' a' cs' y')) in X0.
  pose proof (wf_tm_nf (proj1 (LRtm_escape Hy))) as Ny. pose proof (wf_tm_nf (proj2 (LRtm_escape Hy))) as Ny'.
  assert (Na : nftm (ktm ρ a)) by apply ren_nf. assert (Na' : nftm (ktm ρ a')) by apply ren_nf.
  assert (Ncs : nftm (ktm ρ cs)) by apply ren_nf. assert (Ncs' : nftm (ktm ρ cs')) by apply ren_nf.
  rewrite !iwi_dnthv_subst in X0 by assumption.
  rewrite !iwiFc_single_subst in X0
    by first [assumption | rewrite <- kγ_ty; apply ren_nf_ty | rewrite <- kγ_tml; apply ren_nf
             | rewrite <- kγ_tyll; apply ren_nf_ty | rewrite <- kγ_tmlll; apply ren_nf].
  rewrite <- !kγ_ty, <- !kγ_tml, <- !kγ_tyll, <- !kγ_tmlll in X0.
  exact X0.
Qed.

End Dnth.
