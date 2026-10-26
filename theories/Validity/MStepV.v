(** * Validity of [corec]'s step type and of [out]'s type (M18_DESIGN.md, M18b)

    [corec]'s and [out]'s rules have only their premises: the step type's
    validity ([corec]'s two sides' step types related) is built here from
    [Σ], [Π], [+] and [M] at the signature weakened past the step's
    binders, and [out]'s type's is read off [LR_out_kw] in the identity
    world, as in [V_out]. *)
From DeLaM.Validity Require Export M GLift.
From DeLaM.LogRel Require Import MAux.
From DeLaM.Typing Require Import PresupM.

(** ** Syntax: the signature past three binders *)

Lemma x3_cons_ty (T : ty) d a :
  T⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lcons d a] = T[lcons (ldrop 1 (ldrop 1 (ldrop 1 d))) a].
Proof using .
  rewrite !ren_ren_comp_ty. apply ren_subst_ty.
  intros [|m]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.

Lemma x3_llift_ty (T : ty) d :
  T⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[llift d] = T[llift (ldrop 1 (ldrop 1 (ldrop 1 d)))].
Proof using .
  rewrite !ren_ren_comp_ty. apply ren_subst_ty.
  intros [|m]; rlk_simpl; rewrite ?llk_llift; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; f_equal; lia.
Qed.

Lemma x3_llift2_ty (T : ty) d :
  T⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[llift (llift d)] =
  T[llift (llift (ldrop 1 (ldrop 1 (ldrop 1 d))))].
Proof using .
  rewrite !ren_ren_comp_ty. apply ren_subst_ty.
  intros [|[|m]]; rlk_simpl; rewrite ?llk_llift; cbn [llk]; rewrite ?llk_llift, ?llk_ldrop; try reflexivity;
    f_equal; f_equal; f_equal; lia.
Qed.

Lemma x3_llift3 (t : tm) d :
  t⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩[llift (llift (llift d))] =
  t[llift (llift (llift (ldrop 1 (ldrop 1 (ldrop 1 d)))))].
Proof using .
  rewrite !ren_ren_comp. apply ren_subst.
  intros [|[|[|m]]]; rlk_simpl; rewrite ?llk_llift; cbn [llk]; rewrite ?llk_llift, ?llk_ldrop; try reflexivity;
    f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Section MStepV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** The step type's summands, past the signature's binders *)

Section Summands.
Context {G : gctx} {Γ : ctx} {l l' li k k' ki kc kc' : lvl} {X X' A A' B B' Y Y' : ty} {C C' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l') (Hwli : lwf (gL G) li) (Hwc : lwf (gL G) kc)
  (Hk : lequiv (gL G) k l) (Hk' : lequiv (gL G) k' l') (Hki : lequiv (gL G) ki li) (Hkc : lequiv (gL G) kc' kc)
  (VX : VTyG G Γ X X' li) (VA : VTyG G (Γ ,, X @ li) A A' l)
  (VB : VTyG G (Γ ,, X @ li ,, A @ l) B B' l')
  (VC : VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li)
  (VY : VTyG G (Γ ,, X @ li) Y Y' kc).

(** The carrier at the child index. *)
Lemma VTy_Y3 : VTy G (Γ ,, X @ li ,, A @ l ,, B @ l')
  Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C] Y'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C'] kc.
Proof using EL VL VC VY.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof Hd as Hd0. cbn [SubRel] in Hd0. destruct Hd0 as (((Hd3 & _) & _) & _).
  pose proof (VTmG_loc VC _ _ _ Hd) as XC. rewrite !shift_subst_ty in XC.
  rewrite !single_subst_ty, !lift_single_ty, !x3_cons_ty by assumption.
  exact (VTyG_loc VY _ _ _ (SubRel_cons Hd3 XC)).
Qed.

(** [M] at the child index. *)
Lemma VTy_M3 : VTy G (Γ ,, X @ li ,, A @ l ,, B @ l')
  (tyM l l' li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
     C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C)
  (tyM k k' ki X'⟨↑⟩⟨↑⟩⟨↑⟩ A'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
     C'⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C')
  (mlvl l l' li).
Proof using EL VL VN Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC.
  intros Δ d d' Hd.
  pose proof Hd as Hd0. cbn [SubRel] in Hd0. destruct Hd0 as (((Hd3 & _) & _) & _).
  pose proof (VTmG_loc VC _ _ _ Hd) as XC. rewrite !shift_subst_ty in XC.
  rewrite !subst_tyM, !shift_subst_ty, !x3_llift_ty, !x3_llift2_ty, !x3_llift3.
  eexists. exact (LR_M_at Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC _ _ _ _ _ Hd3 XC).
Qed.

(** The step's continuation type. *)
Lemma VTy_mSum : VTy G (Γ ,, X @ li ,, A @ l ,, B @ l')
  (tySum kc (mlvl l l' li) Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C]
     (tyM l l' li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
        C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C))
  (tySum kc' (mlvl k k' ki) Y'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C']
     (tyM k k' ki X'⟨↑⟩⟨↑⟩⟨↑⟩ A'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
        C'⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C'))
  (lmax kc (mlvl l l' li)).
Proof using EL VL VN Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY.
  apply V_sum; [exact Hwc | cbn; repeat split; assumption | exact (lequiv_sym _ _ _ Hkc)
               | exact (lequiv_sym _ _ _ (lequiv_mlvl Hk Hk' Hki)) | exact VTy_Y3 | exact VTy_M3].
Qed.

End Summands.

Lemma VG_mSum {G Γ l l' li k k' ki kc kc' X X' A A' B B' Y Y' C C'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li -> lwf (gL G) kc ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li -> lequiv (gL G) kc' kc ->
  VTyG G Γ X X' li -> VTyG G (Γ ,, X @ li) A A' l -> VTyG G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTyG G (Γ ,, X @ li) Y Y' kc ->
  VTyG G (Γ ,, X @ li ,, A @ l ,, B @ l')
  (tySum kc (mlvl l l' li) Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C]
     (tyM l l' li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
        C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C))
  (tySum kc' (mlvl k k' ki) Y'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C']
     (tyM k k' ki X'⟨↑⟩⟨↑⟩⟨↑⟩ A'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
        C'⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C'))
  (lmax kc (mlvl l l' li)).
Proof using EL VL VN. intros. gl_lift. eapply VTy_mSum; eassumption. Qed.

(** ** The step type *)

Section Step.
Context {G : gctx} {Γ : ctx} {l l' li k k' ki kc kc' : lvl} {X X' A A' B B' Y Y' : ty} {C C' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l') (Hwli : lwf (gL G) li) (Hwc : lwf (gL G) kc)
  (Hk : lequiv (gL G) k l) (Hk' : lequiv (gL G) k' l') (Hki : lequiv (gL G) ki li) (Hkc : lequiv (gL G) kc' kc)
  (VX : VTyG G Γ X X' li) (VA : VTyG G (Γ ,, X @ li) A A' l)
  (VB : VTyG G (Γ ,, X @ li ,, A @ l) B B' l')
  (VC : VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li)
  (VY : VTyG G (Γ ,, X @ li) Y Y' kc)
  (HX : [ G ; Γ ⊢g X @ li ]) (HA : [ G ; Γ ,, X @ li ⊢g A @ l ]) (HB : [ G ; Γ ,, X @ li ,, A @ l ⊢g B @ l' ])
  (HC : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ]) (HY : [ G ; Γ ,, X @ li ⊢g Y @ kc ]).

Let Hf : lwf (gL G) (mlvl l l' li) := conj (conj Hwl Hwl') Hwli.
Let Ef : lequiv (gL G) (lmax kc' (mlvl k k' ki)) (lmax kc (mlvl l l' li)) :=
  lequiv_max _ _ _ _ _ Hkc (lequiv_mlvl Hk Hk' Hki).

(** The step type's second component. *)
Lemma VTy_mStepB : VTy G (Γ ,, X @ li ,, A @ l)
  (tyPi l' (lmax kc (mlvl l l' li)) B
     (tySum kc (mlvl l l' li) Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C]
        (tyM l l' li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
           C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C)))
  (tyPi k' (lmax kc' (mlvl k k' ki)) B'
     (tySum kc' (mlvl k k' ki) Y'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C']
        (tyM k k' ki X'⟨↑⟩⟨↑⟩⟨↑⟩ A'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
           C'⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C')))
  (lmax kc (mlvl l l' li)).
Proof using EL VL VN Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY HX HA HB HC HY.
  assert (HS : MSig (G := G) (i := ge_layer) Γ l l' li X A B C) by (repeat split; assumption).
  pose proof (ext_wf_g HX Hwli) as HΓX. pose proof (ext_wf_g HA Hwl) as HΓXA. pose proof (ext_wf_g HB Hwl') as HΓ3.
  assert (HSum : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g
                   tySum kc (mlvl l l' li) Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C]
                     (tyM l l' li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                        B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
                        C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C)
                   @ lmax kc (mlvl l l' li) ]).
  { apply (wft_sum _ _ _ _ _ _ _ ge_notV Hwc Hf).
    - exact (wf_ty_single ge_typeof (M_Y3_wf ge_typeof ge_notV HS HY) HC).
    - exact (M_ty_wf ge_typeof ge_notV
               (MSig_wk1 ge_typeof ge_notV (MSig_wk1 ge_typeof ge_notV (MSig_wk1 ge_typeof ge_notV HS HΓX) HΓXA) HΓ3)
               HC). }
  eapply VTy_lconv; [| apply lequiv_sym, M_lv_kf; assumption].
  exact (V_pi Hwl' (lwf_max Hwc Hf) Hk' Ef HSum VB (VG_mSum Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY)).
Qed.

End Step.

Lemma VG_mStepB {G Γ l l' li k k' ki kc kc' X X' A A' B B' Y Y' C C'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li -> lwf (gL G) kc ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li -> lequiv (gL G) kc' kc ->
  VTyG G Γ X X' li -> VTyG G (Γ ,, X @ li) A A' l -> VTyG G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTyG G (Γ ,, X @ li) Y Y' kc ->
  [ G ; Γ ⊢g X @ li ] -> [ G ; Γ ,, X @ li ⊢g A @ l ] -> [ G ; Γ ,, X @ li ,, A @ l ⊢g B @ l' ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] -> [ G ; Γ ,, X @ li ⊢g Y @ kc ] ->
  VTyG G (Γ ,, X @ li ,, A @ l)
  (tyPi l' (lmax kc (mlvl l l' li)) B
     (tySum kc (mlvl l l' li) Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C]
        (tyM l l' li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
           C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C)))
  (tyPi k' (lmax kc' (mlvl k k' ki)) B'
     (tySum kc' (mlvl k k' ki) Y'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C']
        (tyM k k' ki X'⟨↑⟩⟨↑⟩⟨↑⟩ A'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
           C'⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C')))
  (lmax kc (mlvl l l' li)).
Proof using EL VL VN. intros. gl_lift. eapply VTy_mStepB; eassumption. Qed.

(** [corec]'s two sides' step types, related. *)
Lemma VTy_mStepTy {G Γ l l' li k k' ki kc kc' X X' A A' B B' Y Y' C C'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li -> lwf (gL G) kc ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li -> lequiv (gL G) kc' kc ->
  VTyG G Γ X X' li -> VTyG G (Γ ,, X @ li) A A' l -> VTyG G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTyG G (Γ ,, X @ li) Y Y' kc ->
  [ G ; Γ ⊢g X @ li ] -> [ G ; Γ ,, X @ li ⊢g A @ l ] -> [ G ; Γ ,, X @ li ,, A @ l ⊢g B @ l' ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] -> [ G ; Γ ,, X @ li ⊢g Y @ kc ] ->
  VTy G (Γ ,, X @ li) (mStepTy l l' li X A B C kc Y) (mStepTy k k' ki X' A' B' C' kc' Y')
    (lmax l (lmax kc (mlvl l l' li))).
Proof using EL VL VN.
  intros Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY HX HA HB HC HY.
  assert (HS : MSig (G := G) (i := ge_layer) Γ l l' li X A B C) by (repeat split; assumption).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  exact (V_sig Hwl (lwf_max Hwc Hf) Hk (lequiv_max _ _ _ _ _ Hkc (lequiv_mlvl Hk Hk' Hki))
           (M_stepB_wf ge_typeof ge_notV HS Hwc HY) VA
           (VG_mStepB Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY HX HA HB HC HY)).
Qed.

Lemma VG_mStepTy {G Γ l l' li k k' ki kc kc' X X' A A' B B' Y Y' C C'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li -> lwf (gL G) kc ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li -> lequiv (gL G) kc' kc ->
  VTyG G Γ X X' li -> VTyG G (Γ ,, X @ li) A A' l -> VTyG G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTyG G (Γ ,, X @ li) Y Y' kc ->
  [ G ; Γ ⊢g X @ li ] -> [ G ; Γ ,, X @ li ⊢g A @ l ] -> [ G ; Γ ,, X @ li ,, A @ l ⊢g B @ l' ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] -> [ G ; Γ ,, X @ li ⊢g Y @ kc ] ->
  VTyG G (Γ ,, X @ li) (mStepTy l l' li X A B C kc Y) (mStepTy k k' ki X' A' B' C' kc' Y')
    (lmax l (lmax kc (mlvl l l' li))).
Proof using EL VL VN. intros. gl_lift. eapply VTy_mStepTy; eassumption. Qed.

(** ** [out]'s type *)

Lemma V_mOutTy {G Γ l l' li k k' ki X X' A A' B B' C C' m m'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li ->
  VTyG G Γ X X' li -> VTyG G (Γ ,, X @ li) A A' l -> VTyG G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTm G Γ m m' X li ->
  VTy G Γ (mOutTy l l' li X A B C m) (mOutTy k k' ki X' A' B' C' m') (lmax l (mlvl l l' li)).
Proof using EL VL VN.
  intros Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Vm Δ d d' Hd.
  destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd']. pose proof (SubRel_ctx Hd) as HΔ.
  rewrite !subst_mOutTy by assumption.
  pose proof (Vm _ _ _ Hd) as Xm. destruct (LRtm_escape Xm) as [Hmd Hm'd].
  pose proof (wf_tm_nf Hmd) as Nm. pose proof (wf_tm_nf Hm'd) as Nm'.
  set (ρ0 := kw_self HΔ).
  assert (hi : forall ρ : kwk (kw_G ρ0) (kw_Δ ρ0),
             mIdx (X := X) (X' := X') (l := l) (l' := l') (li := li) Δ d d' (kw_comp ρ0 ρ) (ktm ρ m[d]) (ktm ρ m'[d'])).
  { intros ρ. apply (mIdx_iff VX Hd). pose proof (LRtm_kw (kw_comp ρ0 ρ) Xm) as Y.
    rewrite !ktm_comp in Y. unfold ρ0 in Y. rewrite !ktm_self in Y by assumption. exact Y. }
  pose proof (LR_out_kw Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd ρ0 _ _ Nm Nm' hi) as Hout.
  destruct (MGeq_nf (ms_geq (m_side Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd)))
    as (NX & NA & NB & NC & NX' & NA' & NB' & NC').
  unfold ρ0 in Hout. rewrite !kty_self, !ktyl_self, !ktyll_self, !ktmlll_self in Hout by assumption.
  unfold LRty, LogRel. rewrite lmeasure_out. eexists. exact Hout.
Qed.

End MStepV.
