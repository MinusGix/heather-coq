(** * [elim_IWi]'s step telescope at every layer but V (M19b)

    As [IWfIHG] for [IWf]: [IWiIH]'s and [PresupIWi]'s typings of the
    children's type, the induction hypothesis's type and the step's type,
    ported to every layer but V (contexts at [typeof i], weakening through
    [weakening_all], [dnth] typed by [DNthG]). The type checker's [sup_ii]
    and [elim_IWi] build their premises from them. At D and M the
    induction hypothesis's type is never typed on its own (the rule carries
    it as a premise); the checker has to build it, which is why its typing
    is here only. *)
From DeLaM.Typing Require Export IWiIH IWfIHG.

(** The [ih] entry's type, as the codomain at the telescope's own shape
    and children (as [IWf_E_ihcod]). *)
Lemma IWi_E_ihcod l lp li l' (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) :
  iwiihty l lp li l' X A N D Ot C M =
  tyPi lzero (lmax lp l') (tyFin (N⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 1)])
    (tyPi lp l' (D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩)[llift (lsingle (var 1))]
      (iwicod l lp li X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
         Ot⟨rlift ↑⟩⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩
         M⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 1) (var 0))).
Proof.
  f_equal; [f_equal; teq_core |]. f_equal; [teq_core |].
  rewrite !ren_ren_comp_ty. f_equal. f_equal; [teq_core |].
  f_equal; [| teq_core | unfold iwiFamCod; push_ren; f_equal; teq_core].
  f_equal; [teq_core |].
  unfold iwiFam, iwiFamCod. push_ren. f_equal; [teq_core |]. f_equal; teq_core.
Qed.

Section IWiIHG.
Context {G : gctx} {i : layer} (Hv : i <> lV).
Local Notation IWiSig := (@IWiSig G i).

Let up {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) : [ G ; Γ ⊢[ typeof i ] T @ l ] :=
  lift_ty H (lle_self_typeof i).
Let ctxi {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) : [ G ; Γ ⊢[ typeof i ] ] :=
  proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H.
Let ctxt {Γ t T l} (H : [ G ; Γ ⊢[ i ] t : T @ l ]) : [ G ; Γ ⊢[ typeof i ] ] :=
  proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H.

Lemma IWiSig_wk1_g {Γ Y ly l lp li X A N D Ot C} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, Y @ ly ⊢[ typeof i ] ] ->
  IWiSig (Γ ,, Y @ ly) l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩.
Proof using Hv.
  intros (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) HY.
  destruct (IWi_wk_g Hv Hl Hlp HY HX HA HN HD HO HC) as (X1 & A1 & N1 & D1 & O1 & C1).
  unfold IWiSig. auto 10.
Qed.

(** The output index at a shape. *)
Lemma IWi_ot_wf_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] Ot[lsingle a] : X @ li ].
Proof using.
  intros (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) Ha.
  pose proof (wf_tm_subst_g HO (lsub_wf_single_g _ _ _ _ _ _ (ctxt Ha) Ha)) as X0.
  rewrite IWf_E_ot in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** The substitutions into the arity's and the domain's contexts. *)
Lemma IWi_sub1_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] llift (lsingle a) : Γ ,, A @ l ,, tyFin N @ lzero ].
Proof using Hv.
  intros (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) Ha.
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; [exact Hv | exact (IWf_Na_wf_g HN Ha)]).
  eapply lsub_wf_lift_g'; [exact (lsub_wf_single_g _ _ _ _ _ _ (ctxt Ha) Ha) | exact (up HF) | exact I | reflexivity].
Qed.

Lemma IWi_dom_wf_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] D[llift (lsingle a)] @ lp ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  exact (wf_ty_subst_g HD (IWi_sub1_g HS Ha)).
Qed.

Lemma IWi_sub2_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ] llift (llift (lsingle a))
      : Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & _).
  eapply lsub_wf_lift_g'; [exact (IWi_sub1_g HS Ha) | exact (up (IWi_dom_wf_g HS Ha)) | exact Hlp | reflexivity].
Qed.

(** The child index at a shape, in [Γ, k : Fin N[a/x], y : D[a/x, k]]. *)
Lemma IWi_ci_wf_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
      C[llift (llift (lsingle a))] : X⟨↑⟩⟨↑⟩ @ li ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (wf_tm_subst_g HC (IWi_sub2_g HS Ha)) as X0.
  rewrite IWi_E_C in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** The two binders' contexts at a shape. *)
Lemma IWi_ctx_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ typeof i ] ] /\
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ typeof i ] ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; [exact Hv | exact (IWf_Na_wf_g HN Ha)]).
  pose proof (wfc_ext _ _ _ _ _ (ctxt Ha) (up HF) I) as HΓ1.
  exact (conj HΓ1 (wfc_ext _ _ _ _ _ HΓ1 (up (IWi_dom_wf_g HS Ha)) Hlp)).
Qed.

(** The children's family at a shape, and their tuple type. *)
Lemma IWi_famcod_wf_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
      iwiFamCod l lp li X A N D Ot C a @ iwiL l lp li ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & _).
  destruct (IWi_ctx_g HS Ha) as (HΓ1 & HΓ2).
  pose proof (IWiSig_wk1_g (IWiSig_wk1_g HS HΓ1) HΓ2) as (_ & _ & _ & X2 & A2 & N2 & D2 & O2 & C2).
  unfold iwiFamCod. apply wft_iwi; [exact Hv | exact Hl | exact Hlp | exact Hli | exact X2 | exact A2 | exact N2
                                   | exact D2 | exact O2 | exact C2 | exact (IWi_ci_wf_g HS Ha)].
Qed.

Lemma IWi_fam_wf_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwiFam l lp li X A N D Ot C a @ iwiL l lp li ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & _).
  eapply wft_lconv; [| exact (iwiL_pi _ _ _ _ Hl Hlp Hli)].
  unfold iwiFam. apply wft_pi; [exact Hv | exact Hlp | cbn; auto | exact (IWi_dom_wf_g HS Ha)
                                | exact (IWi_famcod_wf_g HS Ha)].
Qed.

Lemma IWi_csa_wf_g {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ].
Proof using Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  apply wft_dvec; [exact Hv | cbn; auto | exact (IWf_Na_wf_g HN Ha) | exact (IWi_fam_wf_g HS Ha)].
Qed.

(** The child at the bound position, and applied to the bound domain
    element. *)
Lemma IWi_dnth0_wf_g {Γ l lp li X A N D Ot C a cs} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ]
      tmDNth (iwiL l lp li) N[lsingle a]⟨↑⟩ (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩ cs⟨↑⟩ (var 0)
      : iwiFam l lp li X A N D Ot C a @ iwiL l lp li ].
Proof using Hv.
  intros HS Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (IWf_Na_wf_g HN Ha) as HNa.
  destruct (IWi_ctx_g HS Ha) as (HΓ1 & _).
  assert (HN1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] N[lsingle a]⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [exact (wk1_tm_g G i _ _ _ _ _ _ HΓ1 HNa) | reflexivity]).
  pose proof (IWi_fam_wf_g HS Ha) as HFam.
  assert (HF1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] tyFin N[lsingle a]⟨↑⟩ @ lzero ])
    by (apply wft_fin; [exact Hv | exact HN1]).
  pose proof (wfc_ext _ _ _ _ _ HΓ1 (up HF1) I) as HΓ2.
  assert (HFam1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, tyFin N[lsingle a]⟨↑⟩ @ lzero
                    ⊢[ i ] (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩ @ iwiL l lp li ])
    by (eapply (proj1 (proj2 (proj2 weakening_all))); [exact HFam | | exact HΓ2];
        eapply wkr_up'; [apply wkr_shift1 | reflexivity]).
  assert (Hcs1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] cs⟨↑⟩
                   : tyDVec (iwiL l lp li) N[lsingle a]⟨↑⟩ (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩ @ iwiL l lp li ])
    by (eapply wf_tm_retype; [exact (wk1_tm_g G i _ _ _ _ _ _ HΓ1 Hcs) | reflexivity]).
  assert (Hv0 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] var 0 : tyFin N[lsingle a]⟨↑⟩ @ lzero ])
    by (apply wf_var; [exact HΓ1 | constructor]).
  pose proof (dnth_wf_g Hv (iwiL_wf Hl Hlp Hli) HN1 HFam1 Hcs1 Hv0) as X0.
  rewrite liftshift_single_var_ty in X0 by exact (wf_ty_nf HFam). exact X0.
Qed.

Lemma IWi_app_wf_g {Γ l lp li X A N D Ot C a cs} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
      iwiapp l lp li X A N D Ot C a cs : iwiFamCod l lp li X A N D Ot C a @ iwiL l lp li ].
Proof using Hv.
  intros HS Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (iwiL_wf Hl Hlp Hli) as HwL.
  pose proof (IWi_dom_wf_g HS Ha) as HDa.
  destruct (IWi_ctx_g HS Ha) as (HΓ1 & HΓ2).
  pose proof (IWi_dnth0_wf_g HS Ha Hcs) as Hd.
  assert (Hd1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
                  iwidnth l lp li X A N D Ot C a cs
                  : tyPi lp (iwiL l lp li) D[llift (lsingle a)]⟨↑⟩ (iwiFamCod l lp li X A N D Ot C a)⟨rlift ↑⟩
                  @ iwiL l lp li ]).
  { pose proof (wk1_tm_g G i _ _ _ _ _ _ HΓ2 Hd) as Y. rewrite ren_tmDNth in Y. exact Y. }
  assert (HDa1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
                   D[llift (lsingle a)]⟨↑⟩ @ lp ]) by exact (wk1_ty_g G i _ _ _ _ _ HΓ2 HDa).
  pose proof (wfc_ext _ _ _ _ _ HΓ2 (up HDa1) Hlp) as HΓ3.
  assert (HCod1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ,, D[llift (lsingle a)]⟨↑⟩ @ lp
                    ⊢[ i ] (iwiFamCod l lp li X A N D Ot C a)⟨rlift ↑⟩ @ iwiL l lp li ])
    by (eapply (proj1 (proj2 (proj2 weakening_all))); [exact (IWi_famcod_wf_g HS Ha) | | exact HΓ3];
        eapply wkr_up'; [apply wkr_shift1 | reflexivity]).
  assert (Hv0 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
                  var 0 : D[llift (lsingle a)]⟨↑⟩ @ lp ])
    by (apply wf_var; [exact HΓ2 | constructor]).
  pose proof (wf_app _ _ _ _ _ _ _ _ _ Hv Hlp HwL HDa1 HCod1
                (wf_lconv _ _ _ _ _ _ _ Hd1 (lequiv_sym _ _ _ (iwiL_pi _ _ _ _ Hl Hlp Hli))) Hv0) as X0.
  rewrite liftshift_single_var_ty in X0 by exact (wf_ty_nf (IWi_famcod_wf_g HS Ha)). exact X0.
Qed.

(** The motive weakened past one local, under its two binders. *)
Lemma IWi_M_wk1_g {Γ Y ly l lp li X A N D Ot C M l'} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, Y @ ly ⊢[ typeof i ] ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,,
      iwimotty l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩ @ iwiL l lp li
      ⊢[ i ] M⟨rlift (rlift ↑)⟩ @ l' ].
Proof using Hv.
  intros HS HY HM. pose proof (IWiSig_wk1_g HS HY) as (Hl & Hlp & Hli & X1 & A1 & N1 & D1 & O1 & C1).
  pose proof (wfc_ext _ _ _ _ _ HY (up X1) Hli) as H1.
  pose proof (IWi_mot_wf_g Hv Hl Hlp Hli X1 A1 N1 D1 O1 C1) as Hmot1.
  pose proof (wfc_ext _ _ _ _ _ H1 (up Hmot1) (iwiL_wf Hl Hlp Hli)) as H2.
  eapply (proj1 (proj2 (proj2 weakening_all))); [exact HM | | exact H2].
  eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | symmetry; apply IWi_mot_ren].
Qed.

(** The induction hypothesis's codomain at a shape and children. *)
Lemma IWi_cod_wf_g {Γ l lp li l' X A N D Ot C M a cs} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
      iwicod l lp li X A N D Ot C M a cs @ l' ].
Proof using Hv.
  intros HS HM Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
  destruct (IWi_ctx_g HS Ha) as (HΓ1 & HΓ2).
  pose proof (IWiSig_wk1_g HS HΓ1) as HS1.
  pose proof (IWi_M_wk1_g HS1 HΓ2 (IWi_M_wk1_g HS HΓ1 HM)) as HM2.
  pose proof (IWi_ci_wf_g HS Ha) as Hci.
  pose proof (IWi_app_wf_g HS Ha Hcs) as Hap.
  assert (E : iwiFamCod l lp li X A N D Ot C a
             = (iwimotty l lp li X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
                  Ot⟨rlift ↑⟩⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩)
                 [lsingle C[llift (llift (lsingle a))]])
    by (unfold iwiFamCod; rewrite IWi_E_mot by auto using ren_nf_ty, ren_nf; reflexivity).
  exact (wf_ty_subst_g HM2 (lsub_wf_single2_g HΓ2 Hci (ltac:(eapply wf_tm_retype; [exact Hap | exact E])))).
Qed.

(** The [ih] entry's type, in the step's telescope. *)
Lemma IWi_ihty_wf_g {Γ l lp li l' X A N D Ot C M} : IWiSig Γ l lp li X A N D Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ].
Proof using Hv.
  intros HS Hl' HM. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (wfc_ext _ _ _ _ _ (ctxi HA) (up HA) Hl) as HΓA.
  pose proof (IWi_cs_wf_g Hv Hl Hlp Hli HX HA HN HD HO HC) as HCs.
  pose proof (wfc_ext _ _ _ _ _ HΓA (up HCs) (iwiL_wf Hl Hlp Hli)) as HΘ.
  pose proof (IWiSig_wk1_g HS HΓA) as HS1.
  pose proof (IWiSig_wk1_g HS1 HΘ) as HS2.
  pose proof (IWi_M_wk1_g HS1 HΘ (IWi_M_wk1_g HS HΓA HM)) as HM2.
  assert (Ha : [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] var 1 : A⟨↑⟩⟨↑⟩ @ l ])
    by (apply wf_var; [exact HΘ | repeat constructor]).
  assert (Hcs : [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] var 0
                  : tyDVec (iwiL l lp li) (N⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 1)]
                      (iwiFam l lp li X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
                         Ot⟨rlift ↑⟩⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ (var 1))
                      @ iwiL l lp li ]).
  { eapply wf_tm_retype; [apply wf_var; [exact HΘ | constructor] |].
    unfold iwiFam, iwiFamCod. push_ren. push_subst.
    f_equal. all: try teq_core. all: f_equal. all: try teq_core. all: f_equal. all: teq_core. }
  rewrite IWi_E_ihcod. apply wft_pi; [exact Hv | exact I | exact (lwf_max Hlp Hl') | |].
  - apply wft_fin; [exact Hv | exact (IWf_Na_wf_g (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HS2)))))) Ha)].
  - apply wft_pi; [exact Hv | exact Hlp | exact Hl' | exact (IWi_dom_wf_g HS2 Ha) |].
    exact (IWi_cod_wf_g HS2 HM2 Ha Hcs).
Qed.

(** The step's type, in the step's telescope (with any induction
    hypothesis entry). *)
Lemma IWi_step_wf_g {Γ l lp li l' X A N D Ot C M I lI} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, I @ lI ⊢[ typeof i ] ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, I @ lI ⊢[ i ] iwistepty l lp li X A N D Ot C M @ l' ].
Proof using Hv.
  intros HS HM HΘ. pose proof (cpre HΘ) as H2. pose proof (cpre H2) as H1.
  pose proof (IWiSig_wk1_g HS H1) as HS1. pose proof (IWiSig_wk1_g HS1 H2) as HS2.
  pose proof (IWiSig_wk1_g HS2 HΘ) as HS3.
  pose proof (IWiSig_nf HS3) as (NX & NA & NN & ND & NO & NC).
  pose proof HS3 as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  assert (Hv2 : [ G ; _ ⊢[ i ] var 2 : A⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by (apply wf_var; [exact HΘ | do 3 constructor]).
  assert (Hv1 : [ G ; _ ⊢[ i ] var 1 : tyDVec (iwiL l lp li) (N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)]
                    (iwiFam l lp li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                       D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                       C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ (var 2)) @ iwiL l lp li ])
    by (eapply wf_tm_retype; [apply wf_var; [exact HΘ | do 2 constructor] | apply IWi_E_var1]).
  pose proof (wf_supii _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hlp Hli HX HA HN HD HO HC Hv2 Hv1) as Hs.
  pose proof (IWi_ot_wf_g HS3 Hv2) as Ho.
  rewrite ?Wf_E2 in Hs, Ho.
  pose proof (IWi_M_wk1_g HS2 HΘ (IWi_M_wk1_g HS1 H2 (IWi_M_wk1_g HS H1 HM))) as HM3.
  apply (wf_ty_subst_g HM3). apply (lsub_wf_single2_g HΘ Ho). rewrite IWi_E_mot by assumption. exact Hs.
Qed.

End IWiIHG.
