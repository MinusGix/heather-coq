(** * Symmetry and transitivity of algorithmic conversion: the shared lemmas

    On typed syntax. The swapped derivation compares binders of the other
    side ([Γ ,, A'], [gdTy Δ'], the right motives' branch scopes), so each
    case moves the induction hypothesis there by the conversion lemma.
    Neutrals infer some type; its equation with the other side's follows
    from soundness of both derivations. *)
From DeLaM.Validity Require Export AlgConv.
From DeLaM.Typing Require Import PresupM.

(** ** The conversion lemma at one global context *)

Section Conv.
Context {G : gctx} (HG : [ ⊢ G ]).

Lemma cv_ty {i Γ Γ2 T T' k k'} : compt i -> ac_ty G Γ T T' -> [ G ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_ty G Γ2 T T'.
Proof. intros Hc D Hctx HT HT'. exact (proj1 ac_conv_all _ _ _ _ D i G Γ2 k k' Hc (GEq_refl _ HG) Hctx HT HT'). Qed.

Lemma cv_tm {i Γ Γ2 t t' T T2 k} : compt i -> ac_tm G Γ t t' T -> [ G ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G ; Γ ⊢[ i ] T2 ≅ T @ k ] ->
  ac_tm G Γ2 t t' T2.
Proof.
  intros Hc D Hctx Ht Ht' ET.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_conv_all)))) _ _ _ _ _ D i G Γ2 T2 k Hc (GEq_refl _ HG) Hctx Ht Ht' ET).
Qed.

End Conv.

(** The step telescopes of two [elim_W]s with equal parts are equal contexts,
    both ways, and the step types are equal (M13a). *)
Lemma W_tele_eq {G i Γ l1 l2 l3 l4 l5 l6 A A' B B' M M'} : compt i ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l4 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A' @ l4 ⊢[ i ] B' @ l5 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' @ l6 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ⊢[ i ] Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ≅ Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ,, wihty l4 l5 l6 A' B' M' @ lmax l5 l6 ] /\
  [ G ⊢[ i ] Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ,, wihty l4 l5 l6 A' B' M' @ lmax l5 l6
      ≅ Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3 ] /\
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3 ⊢[ i ]
      wstepty l1 l2 A B M ≅ wstepty l4 l5 A' B' M' @ l3 ].
Proof.
  intros Hc H14 H25 H36 HA HA' EA HB HB' EB HM HM' EM.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (lequiv_wf_l _ _ _ H14) as W1. pose proof (lequiv_wf_l _ _ _ H25) as W2.
  pose proof (lequiv_wf_l _ _ _ H36) as W3.
  pose proof (lequiv_wf_r _ _ _ H14) as W4. pose proof (lequiv_wf_r _ _ _ H25) as W5.
  pose proof (lequiv_wf_r _ _ _ H36) as W6.
  pose proof (lequiv_sym _ _ _ H14) as H41. pose proof (lequiv_sym _ _ _ H25) as H52.
  pose proof (lequiv_sym _ _ _ H36) as H63.
  assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
  assert (WL' : lwf (gL G) (lmax l4 l5)) by (cbn; split; assumption).
  assert (HL : lequiv (gL G) (lmax l4 l5) (lmax l1 l2)) by (apply lequiv_max; assumption).
  assert (HLF : lequiv (gL G) (lmax l5 (lmax l4 l5)) (lmax l2 (lmax l1 l2))) by (apply lequiv_max; assumption).
  assert (HLI : lequiv (gL G) (lmax l5 l6) (lmax l2 l3)) by (apply lequiv_max; assumption).
  assert (EA4 : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ]) by (eapply eqty_lconv; [apply eqty_sym, EA | exact H41]).
  pose proof (ext_wf Hi HA' W4) as HΓA'.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (HB'A : [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ])
    by (eapply wft_lconv; [exact (stab_ty Hi EA4 H41 HΓA HB') | exact H25]).
  assert (HBA' : [ G ; Γ ,, A' @ l4 ⊢[ i ] B @ l2 ]) by exact (stab_ty Hi EA H14 HΓA' HB).
  assert (EB' : [ G ; Γ ,, A' @ l4 ⊢[ i ] B' ≅ B @ l5 ]).
  { eapply eqty_lconv; [|exact H52]. exact (stab_eqty Hi EA H14 HΓA' (eqty_sym _ _ _ _ _ _ EB)). }
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (HW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' @ lmax l4 l5 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ]) by (apply eqty_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' ≅ tyW l1 l2 A B @ lmax l4 l5 ])
    by (apply eqty_W; first [(apply compt_notV; exact Hc) | exact Hc | assumption]).
  (* the child functions *)
  pose proof (W_fty_wf Hi Hv (X := A) (lx := l1) W1 W2 HW HB) as HF.
  pose proof (W_fty_wf Hi Hv (X := A') (lx := l4) W4 W5 HW' HB') as HF'.
  pose proof (ext_wf Hi HB W2) as HΓAB. pose proof (ext_wf Hi HB' W5) as HΓA'B'.
  assert (EF : [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l4 l5 A' B' @ lmax l2 (lmax l1 l2) ]).
  { apply eqty_pi; first [exact Hv | assumption | apply lequiv_max; assumption | idtac].
    exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓAB (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA EW)). }
  assert (EF' : [ G ; Γ ,, A' @ l4 ⊢[ i ] wfty l4 l5 A' B' ≅ wfty l1 l2 A B @ lmax l5 (lmax l4 l5) ]).
  { apply eqty_pi; first [exact Hv | assumption | apply lequiv_max; assumption | idtac].
    exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA'B' (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' EW')). }
  (* the induction hypotheses *)
  pose proof (ext_wf Hi HF (lwf_max W2 WL)) as HΓAF.
  pose proof (ext_wf Hi HF' (lwf_max W5 WL')) as HΓA'F'.
  pose proof (ext_wf Hi HW WL) as HΓW. pose proof (ext_wf Hi HW' WL') as HΓW'.
  assert (EM' : [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' ≅ M @ l6 ]).
  { eapply eqty_lconv; [|exact H63]. exact (stab_eqty Hi EW (lequiv_sym _ _ _ HL) HΓW' (eqty_sym _ _ _ _ _ _ EM)). }
  pose proof (W_ih_wf Hi Hv W1 W2 W3 HW HB HM HΓAF (eqty_refl' HF) (lequiv_refl _ _ (lwf_max W2 WL))) as HI.
  pose proof (W_ih_wf Hi Hv W4 W5 W6 HW' HB' HM' HΓA'F' (eqty_refl' HF') (lequiv_refl _ _ (lwf_max W5 WL')))
    as HI'.
  pose proof (W_ih_eq Hi Hv H14 H25 H36 HA HB EB HB'A HM EM HW' EW HF EF) as EI.
  pose proof (W_ih_eq Hi Hv H41 H52 H63 HA' HB' EB' (wft_lconv _ _ _ _ _ _ HBA' H52) HM' EM' HW EW' HF' EF')
    as EI'.
  pose proof (ext_wf Hi HI (lwf_max W2 W3)) as HΓT.
  split; [|split].
  - apply eqc_ext; [apply eqc_ext; [apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact H14]
                                   | exact HF | exact EF | solve [apply lequiv_sym; assumption]]
                   | exact HI | exact EI | solve [apply lequiv_sym; assumption]].
  - apply eqc_ext; [apply eqc_ext; [apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA' | exact EA4 | exact H41]
                                   | exact HF' | exact EF' | exact HLF]
                   | exact HI' | exact EI' | exact HLI].
  - exact (W_step_eq Hi Hv H14 H25 H36 HA EA HA' HB EB HB' HM EM EW HF EF HΓT).
Qed.

(** The same for [elim_Wf] (M15a), and the children's tuple type at equal
    shapes. *)
Lemma Wf_tele_eq {G i Γ l1 l2 l3 l4 A A' N N' M M'} : compt i ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l3 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A' @ l3 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] -> [ G ; Γ ,, tyWf l3 A' N' @ l3 ⊢[ i ] M' @ l4 ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ⊢[ i ] Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ≅ Γ ,, A' @ l3 ,, wfcsty l3 A' N' @ l3 ,, wfihty l3 l4 A' N' M' @ lmax lzero l4 ] /\
  [ G ⊢[ i ] Γ ,, A' @ l3 ,, wfcsty l3 A' N' @ l3 ,, wfihty l3 l4 A' N' M' @ lmax lzero l4
      ≅ Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2 ] /\
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2 ⊢[ i ]
      wfstepty l1 A N M ≅ wfstepty l3 A' N' M' @ l2 ].
Proof.
  intros Hc H13 H24 HA HA' EA HN HN' EN HM HM' EM.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (lequiv_wf_l _ _ _ H13) as W1. pose proof (lequiv_wf_l _ _ _ H24) as W2.
  pose proof (lequiv_wf_r _ _ _ H13) as W3. pose proof (lequiv_wf_r _ _ _ H24) as W4.
  pose proof (lequiv_sym _ _ _ H13) as H31. pose proof (lequiv_sym _ _ _ H24) as H42.
  assert (EA3 : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ]) by (eapply eqty_lconv; [apply eqty_sym, EA | exact H31]).
  pose proof (ext_wf Hi HA W1) as HΓA. pose proof (ext_wf Hi HA' W3) as HΓA'.
  pose proof (stab_tm Hi EA H13 HΓA' HN) as HNA'. pose proof (stab_tm Hi EA3 H31 HΓA HN') as HN'A.
  assert (EN' : [ G ; Γ ,, A' @ l3 ⊢[ i ] N' ≅ N : tyNat @ lzero ])
    by (apply eqtm_sym, (stab_eqtm Hi EA H13 HΓA' EN)).
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (HW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' @ l3 ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' ≅ tyWf l1 A N @ l3 ])
    by (eapply eqty_lconv; [apply eqty_sym, EW | exact H31]).
  (* the children *)
  pose proof (Wf_cs_wf Hi Hv W1 HW HN) as HC. pose proof (Wf_cs_wf Hi Hv W3 HW' HN') as HC'.
  assert (EC : [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l1 A N ≅ wfcsty l3 A' N' @ l1 ]).
  { apply eqty_vec; first [exact Hv | exact H13 | exact EN | idtac].
    - exact (wk1_ty _ _ Hi _ _ _ _ _ HΓA HW).
    - exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA EW). }
  assert (EC' : [ G ; Γ ,, A' @ l3 ⊢[ i ] wfcsty l3 A' N' ≅ wfcsty l1 A N @ l3 ]).
  { apply eqty_vec; first [exact Hv | exact H31 | exact EN' | idtac].
    - exact (wk1_ty _ _ Hi _ _ _ _ _ HΓA' HW').
    - exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' EW'). }
  (* the induction hypotheses *)
  pose proof (ext_wf Hi HC W1) as HΓAC. pose proof (ext_wf Hi HC' W3) as HΓA'C'.
  pose proof (ext_wf Hi HW' W3) as HΓW'. pose proof (ext_wf Hi HW W1) as HΓW.
  assert (EM' : [ G ; Γ ,, tyWf l3 A' N' @ l3 ⊢[ i ] M' ≅ M @ l4 ]).
  { eapply eqty_lconv; [|exact H42]. exact (stab_eqty Hi EW H13 HΓW' (eqty_sym _ _ _ _ _ _ EM)). }
  pose proof (Wf_ih_wf Hi Hv W1 W2 HW HN HM HΓAC (eqty_refl _ _ _ _ _ HC) (lequiv_refl _ _ W1)) as HI.
  pose proof (Wf_ih_wf Hi Hv W3 W4 HW' HN' HM' HΓA'C' (eqty_refl _ _ _ _ _ HC') (lequiv_refl _ _ W3)) as HI'.
  pose proof (Wf_ih_eq Hi Hv H13 H24 HA EA HA' HN EN HN'A HM EM) as EI.
  pose proof (Wf_ih_eq Hi Hv H31 H42 HA' EA3 HA HN' EN' HNA' HM' EM') as EI'.
  assert (WZ : lwf (gL G) lzero) by (cbn; auto).
  pose proof (ext_wf Hi HI (lwf_max WZ W2)) as HΓT.
  split; [|split].
  - apply eqc_ext; [apply eqc_ext; [apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact H13]
                                   | exact HC | exact EC | exact H13]
                   | exact HI | exact EI | apply lequiv_max; [apply lequiv_refl, WZ | exact H24]].
  - apply eqc_ext; [apply eqc_ext; [apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA' | exact EA3 | exact H31]
                                   | exact HC' | exact EC' | exact H31]
                   | exact HI' | exact EI' | apply lequiv_max; [apply lequiv_refl, WZ | exact H42]].
  - exact (Wf_step_eq Hi Hv H13 H24 HA EA HA' HN EN HN' HM EM HΓT).
Qed.

(** The same for [IWf] (M17b): two equal signatures' contexts are equal,
    and the index type weakens into the shape's. *)
Lemma IWf_fwd {G i Γ l li k ki X X' A A' N N' Ot Ot' C C'} : compt i ->
  IWfEq (G := G) (i := i) Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ⊢[ i ] Γ ,, A @ l ≅ Γ ,, A' @ k ] /\
  [ G ⊢[ i ] Γ ,, A @ l ,, tyFin N @ lzero ≅ Γ ,, A' @ k ,, tyFin N' @ lzero ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] X'⟨↑⟩ ≅ X⟨↑⟩ @ li ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] X'⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩ @ li ] /\
  [ G ⊢[ i ] Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li
      ≅ Γ ,, X' @ ki ,, iwfmotty k ki X' A' N' Ot' C' @ lmax k ki ] /\
  [ G ⊢[ i ] Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li
      ≅ Γ ,, A' @ k ,, iwfcsty k ki X' A' N' Ot' C' @ lmax k ki ].
Proof.
  intros Hc HE. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof HE as (Hlk & Hlik & HS & EX & EA & EN & _).
  pose proof HS as (Hl & Hli & HX & HA & HN & _).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (ext_wf Hi HA Hl) as HΓA.
  assert (HF : [ G ; Γ ,, A @ l ⊢[ i ] tyFin N @ lzero ]) by (apply wft_fin; [exact Hv | exact HN]).
  assert (HΓAF : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi HF); exact I).
  assert (HctxA : [ G ⊢[ i ] Γ ,, A @ l ≅ Γ ,, A' @ k ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact Hlk]).
  pose proof (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA (eqty_sym _ _ _ _ _ _ EX)) as EX1.
  refine (conj HctxA (conj _ (conj EX1 (conj (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓAF EX1) (conj _ _))))).
  - apply eqc_ext; [exact HctxA | exact HF | apply eqty_fin; [exact Hv | exact EN] | apply lequiv_refl; exact I].
  - apply eqc_ext; [apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HX | exact EX | exact Hlik]
                   | exact (IWf_mot_wf Hi Hv HS) | exact (IWf_mot_eq Hi Hv HE) | exact (lequiv_max _ _ _ _ _ Hlk Hlik)].
  - apply eqc_ext; [exact HctxA | exact (IWf_cs_wf Hi Hv HS) | exact (IWf_cs_eq Hi Hv HE)
                   | exact (lequiv_max _ _ _ _ _ Hlk Hlik)].
Qed.

(** Two signatures the algorithm relates are equal. *)
Lemma iwf_ac_eq {G i Γ l li k ki X X' A A' N N' Ot Ot' C C'} : compt i ->
  lequiv (gL G) l k -> lequiv (gL G) li ki ->
  IWfSig (G := G) (i := i) Γ l li X A N Ot C -> IWfSig (G := G) (i := i) Γ k ki X' A' N' Ot' C' ->
  ac_ty G Γ X X' -> ac_ty G Γ A A' -> ac_tm G (Γ ,, A @ l) N N' tyNat ->
  ac_tm G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ -> ac_tm G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ ->
  IWfEq (G := G) (i := i) Γ l li k ki X X' A A' N N' Ot Ot' C C'.
Proof.
  intros Hc E1 E2 HS HS' DX DA DN DO DC.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof HS as (_ & _ & HX & HA & HN & HO & HC). pose proof HS' as (_ & _ & HX' & HA' & _).
  pose proof (ac_ty_sound Hc DX HX (wft_lconv _ _ _ _ _ _ HX' E2)) as EX.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E1)) as EA.
  destruct (IWf_r_mv Hi Hv HS HS' E1 E2 EX EA) as (_ & _ & HN'l & HO'l & HC'l).
  pose proof (ac_tm_sound Hc DN HN HN'l) as EN.
  exact (IWfEq_of_eqs Hi HS E1 E2 EX EA EN (ac_tm_sound Hc DO HO HO'l) (ac_tm_sound Hc DC HC (HC'l EN))).
Qed.

(** The code of [IWf] (M17c): its signature's equation from the codes'
    derivations. *)
Lemma iwfc_ac_eq {G i Γ l q k k' ki ki' x x' s s' n n' o o' c c' m m'} : compt i ->
  [ G ; Γ ⊢[ i ] tmIWf k ki x s n o c m : tyU l @ q ] ->
  [ G ; Γ ⊢[ i ] tmIWf k' ki' x' s' n' o' c' m' : tyU l @ q ] ->
  leqv k k' -> leqv ki ki' ->
  ac_tm G Γ x x' (tyU ki) -> ac_tm G Γ s s' (tyU k) -> ac_tm G (Γ ,, tyEl k s @ k) n n' tyNat ->
  ac_tm G (Γ ,, tyEl k s @ k) o o' (tyEl ki x⟨↑⟩) ->
  ac_tm G (Γ ,, tyEl k s @ k ,, tyFin n @ lzero) c c' (tyEl ki x⟨↑⟩⟨↑⟩) ->
  IWfEq (G := G) (i := i) Γ k ki k' ki' (tyEl ki x) (tyEl ki' x') (tyEl k s) (tyEl k' s') n n' o o' c c' /\
  [ G ; Γ ⊢[ i ] x' : tyU ki @ lsuc ki ] /\ [ G ; Γ ⊢[ i ] s' : tyU k @ lsuc k ] /\
  [ G ; Γ ⊢[ i ] m : tyEl ki x @ ki ] /\ [ G ; Γ ⊢[ i ] m' : tyEl ki x @ ki ].
Proof.
  intros Hc Ht Ht' Hk0 Hki0 Dx Ds DN DO DC.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (code_iwf_prem Hc Ht) as (Wa & Wb & Hx & Hs & HN & HO & HC & Hm).
  destruct (code_iwf_prem Hc Ht') as (Wc & Wd & Hx' & Hs' & HN' & HO' & HC' & Hm').
  pose proof (leqv_lequiv _ _ _ Wa Wc Hk0) as E13. pose proof (leqv_lequiv _ _ _ Wb Wd Hki0) as E24.
  pose proof (code_U_conv Hc E24 Hx') as Hx1. pose proof (code_U_conv Hc E13 Hs') as Hs1.
  pose proof (ac_tm_sound Hc Dx Hx Hx1) as Ex. pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (HS : IWfSig (G := G) (i := i) Γ k ki (tyEl ki x) (tyEl k s) n o c)
    by (unfold IWfSig; repeat split; first [assumption | apply wft_El; assumption]).
  assert (HS' : IWfSig (G := G) (i := i) Γ k' ki' (tyEl ki' x') (tyEl k' s') n' o' c')
    by (unfold IWfSig; repeat split; first [assumption | apply wft_El; assumption]).
  assert (EX : [ G ; Γ ⊢[ i ] tyEl ki x ≅ tyEl ki' x' @ ki ]) by (apply eqty_El; assumption).
  assert (EA : [ G ; Γ ⊢[ i ] tyEl k s ≅ tyEl k' s' @ k ]) by (apply eqty_El; assumption).
  destruct (IWf_r_mv Hi Hv HS HS' E13 E24 EX EA) as (_ & _ & HN'l & HO'l & HC'l).
  pose proof (ac_tm_sound Hc DN HN HN'l) as EN.
  assert (Hm'l : [ G ; Γ ⊢[ i ] m' : tyEl ki x @ ki ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact Hm' | exact E24] | exact EX]).
  refine (conj (IWfEq_of_eqs Hi HS E13 E24 EX EA EN (ac_tm_sound Hc DO HO HO'l)
                  (ac_tm_sound Hc DC HC (HC'l EN))) _).
  repeat split; assumption.
Qed.

Lemma wf_cs_conv {G i Γ l A N a a'} : compt i -> lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyVec l (tyWf l A N) N[lsingle a] ≅ tyVec l (tyWf l A N) N[lsingle a'] @ l ].
Proof.
  intros Hc Wl HA HN Ha Ha' Ea.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  apply eqty_vec; first [exact Hv | apply lequiv_refl, Wl | exact HW | apply eqty_refl, HW | idtac].
  exact (Wf_Na_eq Hi HN (eqtm_refl _ _ _ _ _ _ HN) Ha Ha' Ea).
Qed.

Lemma eqc_refl_c {G i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G ⊢[ i ] Γ ≅ Γ ].
Proof. apply eqc_refl. Qed.

(** [M] (M18b): two signatures the algorithm relates are equal; the
    identities from the left signature's contexts to the right one's; and
    the two signatures' contexts are equal, both ways. *)
Lemma M_ac_eq {G i Γ l l' li k k' ki X X' A A' B B' C C'} : compt i ->
  lequiv (gL G) l k -> lequiv (gL G) l' k' -> lequiv (gL G) li ki ->
  MSig (G := G) (i := i) Γ l l' li X A B C -> MSig (G := G) (i := i) Γ k k' ki X' A' B' C' ->
  ac_ty G Γ X X' -> ac_ty G (Γ ,, X @ li) A A' -> ac_ty G (Γ ,, X @ li ,, A @ l) B B' ->
  ac_tm G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ ->
  MEq (G := G) (i := i) Γ l l' li k k' ki X X' A A' B B' C C'.
Proof.
  intros Hc E1 E2 E3 HS HS' DX DA DB DC. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof HS as (Wl & Wl' & Wli & HX & HA & HB & HC).
  pose proof HS' as (Wk & Wk' & Wki & HX' & HA' & HB' & HC').
  pose proof (wft_lconv _ _ _ _ _ _ HX' E3) as HX'l.
  pose proof (ac_ty_sound Hc DX HX HX'l) as EX.
  assert (Hid0 : [ G ; Γ ⊢[ i ] lshift 0 : Γ ]) by (eapply lsub_wf_id; eauto using ctx_of_wf_ty).
  destruct (ids_ext Hi Hid0 Hid0 HX EX HX' E3) as (I1 & I1r).
  pose proof (wft_lconv _ _ _ _ _ _ (mv_ty Hi I1r HA') E1) as HA'l.
  pose proof (ac_ty_sound Hc DA HA HA'l) as EA.
  destruct (ids_ext Hi I1 I1r HA EA HA' E1) as (I2 & I2r).
  pose proof (wft_lconv _ _ _ _ _ _ (mv_ty Hi I2r HB') E2) as HB'l.
  pose proof (ac_ty_sound Hc DB HB HB'l) as EB.
  destruct (ids_ext Hi I2 I2r HB EB HB' E2) as (I3 & I3r).
  assert (EX3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] X⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wk3_eqty; [exact Hi | exact (ctx_of_wf_tm Hi HC) | exact EX]).
  assert (HC'l : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact (mv_tm Hi I3r HC') | exact E3] | exact EX3]).
  pose proof (ac_tm_sound Hc DC HC HC'l) as EC.
  apply MEq_intro; assumption.
Qed.

Lemma MEq_ids_r {G i Γ l l' li k k' ki X X' A A' B B' C C'} : compt i ->
  MEq (G := G) (i := i) Γ l l' li k k' ki X X' A A' B B' C C' ->
  [ G ; Γ ,, X @ li ⊢[ i ] lshift 0 : Γ ,, X' @ ki ] /\
  [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] lshift 0 : Γ ,, X' @ ki ,, A' @ k ] /\
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] lshift 0 : Γ ,, X' @ ki ,, A' @ k ,, B' @ k' ].
Proof.
  intros Hc HE. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof (MEq_sig_r Hi Hv HE) as (_ & _ & _ & HX' & HA' & HB' & _).
  destruct HE as (E1 & E2 & E3 & (_ & _ & _ & HX & HA & HB & _) & EX & EA & EB & _).
  assert (Hid0 : [ G ; Γ ⊢[ i ] lshift 0 : Γ ]) by (eapply lsub_wf_id; eauto using ctx_of_wf_ty).
  destruct (ids_ext Hi Hid0 Hid0 HX EX HX' E3) as (I1 & I1r).
  destruct (ids_ext Hi I1 I1r HA EA HA' E1) as (I2 & I2r).
  destruct (ids_ext Hi I2 I2r HB EB HB' E2) as (I3 & I3r).
  tauto.
Qed.

Lemma M_ctxs {G i Γ l l' li k k' ki X X' A A' B B' C C'} : compt i ->
  MEq (G := G) (i := i) Γ l l' li k k' ki X X' A A' B B' C C' ->
  [ G ⊢[ i ] Γ ,, X @ li ≅ Γ ,, X' @ ki ] /\
  [ G ⊢[ i ] Γ ,, X @ li ,, A @ l ≅ Γ ,, X' @ ki ,, A' @ k ] /\
  [ G ⊢[ i ] Γ ,, X @ li ,, A @ l ,, B @ l' ≅ Γ ,, X' @ ki ,, A' @ k ,, B' @ k' ] /\
  [ G ⊢[ i ] Γ ,, X' @ ki ≅ Γ ,, X @ li ] /\
  [ G ⊢[ i ] Γ ,, X' @ ki ,, A' @ k ≅ Γ ,, X @ li ,, A @ l ] /\
  [ G ⊢[ i ] Γ ,, X' @ ki ,, A' @ k ,, B' @ k' ≅ Γ ,, X @ li ,, A @ l ,, B @ l' ] /\
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] X⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] /\
  [ G ; Γ ,, X' @ ki ,, A' @ k ,, B' @ k' ⊢[ i ] X⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩⟨↑⟩ @ ki ].
Proof.
  intros Hc HE. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof (MEq_sig_r Hi Hv HE) as (_ & _ & _ & HX' & HA' & HB' & HC').
  pose proof (MEq_ids Hi Hv HE) as (Id1 & Id2 & _).
  destruct HE as (E1 & E2 & E3 & (_ & _ & _ & HX & HA & HB & HC) & EX & EA & EB & _).
  pose proof (ctx_of_wf_ty Hi HX) as HΓ.
  pose proof (lequiv_sym _ _ _ E1) as E1'. pose proof (lequiv_sym _ _ _ E2) as E2'.
  pose proof (lequiv_sym _ _ _ E3) as E3'.
  assert (L1 : [ G ⊢[ i ] Γ ,, X @ li ≅ Γ ,, X' @ ki ]) by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HX | exact EX | exact E3]).
  assert (L2 : [ G ⊢[ i ] Γ ,, X @ li ,, A @ l ≅ Γ ,, X' @ ki ,, A' @ k ]) by (apply eqc_ext; [exact L1 | exact HA | exact EA | exact E1]).
  assert (EX' : [ G ; Γ ⊢[ i ] X' ≅ X @ ki ]) by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EX) | exact E3']).
  assert (EA' : [ G ; Γ ,, X' @ ki ⊢[ i ] A' ≅ A @ k ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ (mv_eqty Hi Id1 EA)) | exact E1']).
  assert (EB' : [ G ; Γ ,, X' @ ki ,, A' @ k ⊢[ i ] B' ≅ B @ k' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ (mv_eqty Hi Id2 EB)) | exact E2']).
  assert (R1 : [ G ⊢[ i ] Γ ,, X' @ ki ≅ Γ ,, X @ li ]) by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HX' | exact EX' | exact E3']).
  assert (R2 : [ G ⊢[ i ] Γ ,, X' @ ki ,, A' @ k ≅ Γ ,, X @ li ,, A @ l ]) by (apply eqc_ext; [exact R1 | exact HA' | exact EA' | exact E1']).
  refine (conj L1 (conj L2 (conj _ (conj R1 (conj R2 (conj _ (conj _ _))))))).
  - apply eqc_ext; [exact L2 | exact HB | exact EB | exact E2].
  - apply eqc_ext; [exact R2 | exact HB' | exact EB' | exact E2'].
  - eapply wk3_eqty; [exact Hi | exact (ctx_of_wf_tm Hi HC) | exact EX].
  - eapply wk3_eqty; [exact Hi | exact (ctx_of_wf_tm Hi HC') | eapply eqty_lconv; [exact EX | exact E3']].
Qed.
