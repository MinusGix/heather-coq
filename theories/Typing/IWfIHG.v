(** * [elim_IWf]'s step telescope at every layer but V (M17c)

    [IWfIH]'s and [PresupIWf]'s typings of the children's type, the
    induction hypothesis's type and the step's type hold at D and M; these
    are their ports to every layer but V, as [StaticCode]'s [WfGen] ports
    [Wf]'s (M15b): contexts at [typeof i], weakening through
    [weakening_all], and [dnth] typed by [DNthG]. The type checker's
    [sup_i] and [elim_IWf] at layer C build their premises from them. *)
From DeLaM.Typing Require Export IWfIH DNthG StaticCode.

Section IWfIHG.
Context {G : gctx} {i : layer} (Hv : i <> lV).
Local Notation IWfSig := (@IWfSig G i).

Let up {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) : [ G ; Γ ⊢[ typeof i ] T @ l ] :=
  lift_ty H (lle_self_typeof i).
Let ctxi {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) : [ G ; Γ ⊢[ typeof i ] ] :=
  proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H.
Let ctxt {Γ t T l} (H : [ G ; Γ ⊢[ i ] t : T @ l ]) : [ G ; Γ ⊢[ typeof i ] ] :=
  proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H.

(** Two single substitutions at once. *)
Lemma lsub_wf_single2_g {Γ A B t q l l'} :
  [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] t : A @ l ] -> [ G ; Γ ⊢[ i ] q : B[lsingle t] @ l' ] ->
  [ G ; Γ ⊢[ i ] lsingle2 t q : Γ ,, A @ l ,, B @ l' ].
Proof using.
  intros HΓ Ht Hq.
  constructor; [exact HΓ | apply lk_dnf_lsingle2; eauto using wf_tm_dnf
               | split; auto; intros n; cbn; f_equal; lia |].
  intros n T l0 Hin.
  inversion Hin as [Γ0 A0 l1|Γ0 A0 l1 T0 l2 m Hm]; subst; cbn.
  - rewrite (ren_subst_ty _ _ _ (lsingle t)); [exact Hq|].
    intros k; rewrite rlk_shift1; reflexivity.
  - inversion Hm as [Γ1 A1 l3|Γ1 A1 l3 T1 l4 m' Hm']; subst; cbn.
    + rewrite shift2_single2_ty by exact (wf_tm_nf_ty Ht). exact Ht.
    + rewrite shift2_single2_ty by eauto using in_ctx_nf. rewrite Nat.add_0_r.
      apply wf_var; [exact HΓ | exact Hm'].
Qed.

Lemma IWfSig_wk1_g {Γ Y ly l li X A N Ot C} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ,, Y @ ly ⊢[ typeof i ] ] ->
  IWfSig (Γ ,, Y @ ly) l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩.
Proof using Hv.
  intros (Hl & Hli & HX & HA & HN & HO & HC) HY.
  destruct (IWf_wk_g Hv Hl HY HX HA HN HO HC) as (X1 & A1 & N1 & O1 & C1).
  unfold IWfSig. auto 8.
Qed.

Lemma IWf_Na_wf_g {Γ A N a l} : [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] N[lsingle a] : tyNat @ lzero ].
Proof using.
  intros HN Ha.
  eapply wf_tm_retype; [exact (wf_tm_subst_g HN (lsub_wf_single_g _ _ _ _ _ _ (ctxt Ha) Ha)) | reflexivity].
Qed.

(** The output index at a shape. *)
Lemma IWf_ot_wf_g {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] Ot[lsingle a] : X @ li ].
Proof using.
  intros (Hl & Hli & HX & HA & HN & HO & HC) Ha.
  pose proof (wf_tm_subst_g HO (lsub_wf_single_g _ _ _ _ _ _ (ctxt Ha) Ha)) as X0.
  rewrite IWf_E_ot in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** The child index at a shape, in [Γ, i : Fin N[a/x]]. *)
Lemma IWf_ci_wf_g {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] C[llift (lsingle a)] : X⟨↑⟩ @ li ].
Proof using Hv.
  intros (Hl & Hli & HX & HA & HN & HO & HC) Ha.
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; [exact Hv | exact (IWf_Na_wf_g HN Ha)]).
  assert (Hd : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] llift (lsingle a) : Γ ,, A @ l ,, tyFin N @ lzero ])
    by (eapply lsub_wf_lift_g'; [exact (lsub_wf_single_g _ _ _ _ _ _ (ctxt Ha) Ha) | exact (up HF) | exact I
                                | reflexivity]).
  pose proof (wf_tm_subst_g HC Hd) as X0. rewrite IWf_E_C in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** The children's family and tuple type at a shape. *)
Lemma IWf_fam_wf_g {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwfFam l li X A N Ot C a @ lmax l li ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; [exact Hv | exact (IWf_Na_wf_g HN Ha)]).
  pose proof (wfc_ext _ _ _ _ _ (ctxt Ha) (up HF) I) as H1.
  destruct (IWfSig_wk1_g HS H1) as (_ & _ & X1 & A1 & N1 & O1 & C1).
  unfold iwfFam. apply wft_iwf; [exact Hv | exact Hl | exact Hli | exact X1 | exact A1 | exact N1 | exact O1
                                | exact C1 | exact (IWf_ci_wf_g HS Ha)].
Qed.

Lemma IWf_csa_wf_g {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  apply wft_dvec; [exact Hv | exact (lwf_max Hl Hli) | exact (IWf_Na_wf_g HN Ha) | exact (IWf_fam_wf_g HS Ha)].
Qed.

(** The child at the bound index, in [Γ, i : Fin N[a/x]]. *)
Lemma IWf_dnth_wf_g {Γ l li X A N Ot C a cs} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwfdnth l li X A N Ot C a cs : iwfFam l li X A N Ot C a @ lmax l li ].
Proof using Hv.
  intros HS Ha Hcs. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (IWf_Na_wf_g HN Ha) as HNa.
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; [exact Hv | exact HNa]).
  pose proof (wfc_ext _ _ _ _ _ (ctxt Ha) (up HF) I) as HΓ1.
  assert (HN1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] N[lsingle a]⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [exact (wk1_tm_g G i _ _ _ _ _ _ HΓ1 HNa) | reflexivity]).
  pose proof (IWf_fam_wf_g HS Ha) as HFam.
  assert (HF1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] tyFin N[lsingle a]⟨↑⟩ @ lzero ])
    by (apply wft_fin; [exact Hv | exact HN1]).
  pose proof (wfc_ext _ _ _ _ _ HΓ1 (up HF1) I) as HΓ2.
  assert (HFam1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, tyFin N[lsingle a]⟨↑⟩ @ lzero
                    ⊢[ i ] (iwfFam l li X A N Ot C a)⟨rlift ↑⟩ @ lmax l li ])
    by (eapply (proj1 (proj2 (proj2 weakening_all))); [exact HFam | | exact HΓ2];
        eapply wkr_up'; [apply wkr_shift1 | reflexivity]).
  assert (Hcs1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] cs⟨↑⟩
                   : tyDVec (lmax l li) N[lsingle a]⟨↑⟩ (iwfFam l li X A N Ot C a)⟨rlift ↑⟩ @ lmax l li ])
    by (eapply wf_tm_retype; [exact (wk1_tm_g G i _ _ _ _ _ _ HΓ1 Hcs) | reflexivity]).
  assert (Hv0 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] var 0 : tyFin N[lsingle a]⟨↑⟩ @ lzero ])
    by (apply wf_var; [exact HΓ1 | constructor]).
  pose proof (dnth_wf_g Hv (lwf_max Hl Hli) HN1 HFam1 Hcs1 Hv0) as X0.
  rewrite liftshift_single_var_ty in X0 by exact (wf_ty_nf HFam). exact X0.
Qed.

(** The motive weakened past one local, under its two binders. *)
Lemma IWf_M_wk1_g {Γ Y ly l li X A N Ot C M l'} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ,, Y @ ly ⊢[ typeof i ] ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, iwfmotty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ @ lmax l li
      ⊢[ i ] M⟨rlift (rlift ↑)⟩ @ l' ].
Proof using Hv.
  intros HS HY HM. pose proof (IWfSig_wk1_g HS HY) as (Hl & Hli & X1 & A1 & N1 & O1 & C1).
  pose proof (wfc_ext _ _ _ _ _ HY (up X1) Hli) as H1.
  pose proof (IWf_mot_wf_g Hv Hl Hli X1 A1 N1 O1 C1) as Hmot1.
  pose proof (wfc_ext _ _ _ _ _ H1 (up Hmot1) (lwf_max Hl Hli)) as H2.
  eapply (proj1 (proj2 (proj2 weakening_all))); [exact HM | | exact H2].
  eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | symmetry; apply IWf_mot_ren].
Qed.

(** The induction hypothesis's codomain and type, from the motive. *)
Lemma IWf_cod_wf_g {Γ l li l' X A N Ot C M a cs} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwfcod l li X A N Ot C M a cs @ l' ].
Proof using Hv.
  intros HS HM Ha Hcs. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; [exact Hv | exact (IWf_Na_wf_g HN Ha)]).
  pose proof (wfc_ext _ _ _ _ _ (ctxt Ha) (up HF) I) as HΓ1.
  pose proof (IWf_M_wk1_g HS HΓ1 HM) as HM1.
  pose proof (IWf_ci_wf_g HS Ha) as Hci.
  pose proof (IWf_dnth_wf_g HS Ha Hcs) as Hd.
  assert (E : iwfFam l li X A N Ot C a
             = (iwfmotty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩)[lsingle C[llift (lsingle a)]])
    by (unfold iwfFam; rewrite IWf_E_mot by auto using ren_nf_ty, ren_nf; reflexivity).
  exact (wf_ty_subst_g HM1 (lsub_wf_single2_g HΓ1 Hci (ltac:(eapply wf_tm_retype; [exact Hd | exact E])))).
Qed.

Lemma IWf_ihty_wf_g {Γ l li l' X A N Ot C M} : IWfSig Γ l li X A N Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ].
Proof using Hv.
  intros HS Hl' HM. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (wfc_ext _ _ _ _ _ (ctxi HA) (up HA) Hl) as HΓA.
  pose proof (IWf_cs_wf_g Hv Hl Hli HX HA HN HO HC) as HCs.
  pose proof (wfc_ext _ _ _ _ _ HΓA (up HCs) (lwf_max Hl Hli)) as HΘ.
  pose proof (IWfSig_wk1_g HS HΓA) as HS1.
  pose proof (IWfSig_wk1_g HS1 HΘ) as HS2.
  pose proof (IWf_M_wk1_g HS1 HΘ (IWf_M_wk1_g HS HΓA HM)) as HM2.
  assert (Ha : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] var 1 : A⟨↑⟩⟨↑⟩ @ l ])
    by (apply wf_var; [exact HΘ | repeat constructor]).
  assert (Hcs : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] var 0
                  : tyDVec (lmax l li) (N⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 1)]
                      (iwfFam l li X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩
                         C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 1)) @ lmax l li ]).
  { eapply wf_tm_retype; [apply wf_var; [exact HΘ | constructor] |].
    unfold iwfFam. push_ren. push_subst. f_equal; [teq_core |]. f_equal; first [teq_core | ren_comm]. }
  rewrite IWf_E_ihcod. apply wft_pi; [exact Hv | exact I | exact Hl' | |].
  - apply wft_fin; [exact Hv | exact (IWf_Na_wf_g (proj1 (proj2 (proj2 (proj2 (proj2 HS2))))) Ha)].
  - exact (IWf_cod_wf_g HS2 HM2 Ha Hcs).
Qed.

(** The step's type, in the step's telescope (with any induction
    hypothesis entry). *)
Lemma IWf_step_wf_g {Γ l li l' X A N Ot C M I lI} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, I @ lI ⊢[ typeof i ] ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, I @ lI ⊢[ i ] iwfstepty l li X A N Ot C M @ l' ].
Proof using Hv.
  intros HS HM HΘ. pose proof (cpre HΘ) as H2. pose proof (cpre H2) as H1.
  pose proof (IWfSig_wk1_g HS H1) as HS1. pose proof (IWfSig_wk1_g HS1 H2) as HS2.
  pose proof (IWfSig_wk1_g HS2 HΘ) as HS3.
  pose proof (IWfSig_nf HS3) as (NX & NA & NN & NO & NC).
  pose proof HS3 as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (Hv2 : [ G ; _ ⊢[ i ] var 2 : A⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by (apply wf_var; [exact HΘ | do 3 constructor]).
  assert (Hv1 : [ G ; _ ⊢[ i ] var 1 : tyDVec (lmax l li) (N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)]
                    (iwfFam l li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                       C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 2)) @ lmax l li ])
    by (eapply wf_tm_retype; [apply wf_var; [exact HΘ | do 2 constructor] | apply IWf_E_var1]).
  pose proof (wf_supi _ _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hli HX HA HN HO HC Hv2 Hv1) as Hs.
  pose proof (IWf_ot_wf_g HS3 Hv2) as Ho.
  rewrite ?Wf_E2 in Hs, Ho.
  pose proof (IWf_M_wk1_g HS2 HΘ (IWf_M_wk1_g HS1 H2 (IWf_M_wk1_g HS H1 HM))) as HM3.
  apply (wf_ty_subst_g HM3). apply (lsub_wf_single2_g HΘ Ho). rewrite IWf_E_mot by assumption. exact Hs.
Qed.

End IWfIHG.
