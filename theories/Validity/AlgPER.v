(** * Symmetry and transitivity of algorithmic conversion (08:199; M6_DESIGN.md step 4)

    On typed syntax. The swapped derivation compares binders of the other
    side ([Γ ,, A'], [gdTy Δ'], the right motives' branch scopes), so each
    case moves the induction hypothesis there by the conversion lemma.
    Neutrals infer some type; its equation with the other side's follows
    from soundness of both derivations. *)
From DeLaM.Validity Require Export AlgConv.

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
                                   | exact HF | exact EF | now apply lequiv_sym]
                   | exact HI | exact EI | now apply lequiv_sym].
  - apply eqc_ext; [apply eqc_ext; [apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA' | exact EA4 | exact H41]
                                   | exact HF' | exact EF' | exact HLF]
                   | exact HI' | exact EI' | exact HLI].
  - exact (W_step_eq Hi Hv H14 H25 H36 HA EA HA' HB EB HB' HM EM EW HF EF HΓT).
Qed.

Lemma eqc_refl_c {G i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G ⊢[ i ] Γ ≅ Γ ].
Proof. apply eqc_refl. Qed.

(** ** Symmetry: the statements *)

Definition Y_ty G Γ T T' : Prop := forall i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_ty G Γ T' T.
Definition Y_tynf G Γ T T' : Prop := forall i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_tynf G Γ T' T.
Definition Y_tyne G Γ T T' : Prop := forall i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_tyne G Γ T' T.
Definition Y_ctx G Δ Δ' : Prop := [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> ac_ctx G Δ' Δ.
Definition Y_tm G Γ t t' T : Prop := forall i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> ac_tm G Γ t' t T.
Definition Y_tmnf G Γ t t' T : Prop := forall i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> ac_tmnf G Γ t' t T.
Definition Y_ne G Γ ν ν' (T : ty) : Prop := forall i k k' A A', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> exists T', ac_tmne G Γ ν' ν T'.
Definition Y_nee G Γ ν ν' (W : ty) : Prop := forall i k k' A A', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> exists W', ac_tmnee G Γ ν' ν W'.
Definition Y_sub G Γ d d' Θ : Prop := forall i, compt i -> [ G ; Θ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] d : Θ ] -> [ G ; Γ ⊢[ i ] d' : Θ ] -> ac_sub G Γ d' d Θ.

(** ** Types *)

Lemma Y_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  Y_tynf G Γ W W' -> Y_ty G Γ T T'.
Proof.
  intros Hr Hr' Hw Hw' IH i k k' Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT Hr Hw)) as HW.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT' Hr' Hw')) as HW'.
  eapply act_red; [exact Hr' | exact Hr | exact Hw' | exact Hw | exact (IH i k k' Hc HW HW')].
Qed.

Lemma Y_actnf_nat {G Γ} : Y_tynf G Γ tyNat tyNat.
Proof. red; intros; apply actnf_nat. Qed.
Lemma Y_actnf_U {G Γ l l'} : leqv l l' -> Y_tynf G Γ (tyU l) (tyU l').
Proof. intros Hl; red; intros; apply actnf_U, leqv_sym, Hl. Qed.

Lemma Y_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> Y_ty G (Γ ,, A @ l1) B B' ->
  Y_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA DB IHB i k k' Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_pi HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  assert (Hctx : [ G ⊢[ i ] Γ ,, A @ l1 ≅ Γ ,, A' @ l3 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact E13]).
  apply actnf_pi; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | exact (IHA i l1 l3 Hc HA HA') |].
  pose proof (IHB i l2 l4 Hc HB HB1) as X.
  exact (cv_ty (ctx_glob _ _ _ HΓ) Hc X Hctx HB1 HB).
Qed.

Lemma Y_actnf_ne {G Γ V V'} : Y_tyne G Γ V V' -> Y_tynf G Γ V V'.
Proof. intros IH i k k' Hc HT HT'. apply actnf_ne. exact (IH i k k' Hc HT HT'). Qed.

Lemma Y_actnf_CTyp {G Γ Δ Δ' l l'} : Y_ctx G Δ Δ' -> leqv l l' -> Y_tynf G Γ (tyCTyp Δ l) (tyCTyp Δ' l').
Proof.
  intros IH Hl i k k' Hc HT HT'.
  destruct (inv_ty_CTyp HT) as ((_ & _ & HΔ & _) & _). destruct (inv_ty_CTyp HT') as ((_ & _ & HΔ' & _) & _).
  apply actnf_CTyp; [exact (IH HΔ HΔ') | exact (leqv_sym _ _ Hl)].
Qed.

Lemma Y_actnf_CTrm {G Γ Δ Δ' T T' l l'} : ac_ctx G Δ Δ' -> Y_ctx G Δ Δ' -> Y_ty G Δ T T' -> leqv l l' ->
  Y_tynf G Γ (tyCTrm Δ T l) (tyCTrm Δ' T' l').
Proof.
  intros Dc IHc IHT Hl i k k' Hc HX HX'.
  destruct (inv_ty_CTrm HX) as ((_ & HΓ & HΔ & HT & W) & _).
  destruct (inv_ty_CTrm HX') as ((_ & _ & HΔ' & HT' & W') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E)) as HT1.
  apply actnf_CTrm; [exact (IHc HΔ HΔ') | | exact (leqv_sym _ _ Hl)].
  exact (cv_ty (ctx_glob _ _ _ HΔ) compt_D (IHT lD l l compt_D HT HT1) Ec HT1 HT).
Qed.

Lemma Y_actnf_upi {G Γ n l l' T T'} : leqv l l' -> Y_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  Y_tynf G Γ (tyUPi n l T) (tyUPi n l' T').
Proof.
  intros Hl IH i k k' Hc HX HX'.
  destruct (inv_ty_upi HX) as ((-> & _ & _ & _ & HT) & _). destruct (inv_ty_upi HX') as ((_ & _ & _ & _ & HT') & _).
  apply actnf_upi; [exact (leqv_sym _ _ Hl) | exact (IH lM l l' compt_M HT HT')].
Qed.

Lemma Y_actnf_cpi {G Γ l l' T T'} : leqv l l' -> Y_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  Y_tynf G Γ (tyCPi l T) (tyCPi l' T').
Proof.
  intros Hl IH i k k' Hc HX HX'.
  destruct (inv_ty_cpi HX) as ((-> & _ & _ & HT) & _). destruct (inv_ty_cpi HX') as ((_ & _ & _ & HT') & _).
  apply actnf_cpi; [exact (leqv_sym _ _ Hl) | exact (IH lM l l' compt_M HT HT')].
Qed.

Lemma Y_actnf_tpi {G Γ Δ Δ' l1 l2 l3 l4 T T'} : ac_ctx G Δ Δ' -> Y_ctx G Δ Δ' -> leqv l1 l3 -> leqv l2 l4 ->
  Y_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T' -> Y_tynf G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ' l3 l4 T').
Proof.
  intros Dc IHc H13 H24 IH i k k' Hc HX HX'.
  destruct (inv_ty_tpi HX) as ((-> & HΓ & HΔ & W1 & W2 & HT) & _).
  destruct (inv_ty_tpi HX') as ((_ & _ & HΔ' & W3 & W4 & HT') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HGD : [ ⊢ gext G (gdTy Δ lD l1) ]) by (apply wfg_ty; auto).
  assert (HGD' : [ ⊢ gext G (gdTy Δ' lD l3) ]) by (apply wfg_ty; auto).
  pose proof (gbind_obj_ty (lle_refl lD) ltac:(discriminate) HGD Ec E13) as Ho.
  pose proof (gbind_ty HG HGD Ho HT') as HT1.
  pose proof (GEq_ext (GEq_refl _ HG) HGD HGD' (conj eq_refl (conj (or_intror eq_refl) (conj E13 Ec)))) as HE.
  pose proof (IH lM l2 l4 compt_M HT HT1) as X.
  apply actnf_tpi; [exact (IHc HΔ HΔ') | exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) |].
  exact (proj1 ac_conv_all _ _ _ _ X lM _ _ l4 l2 compt_M HE
           (eqc_refl _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT')) HT1 HT).
Qed.

Lemma Y_actne_gvar {G Γ U Δ i' l d d'} : in_gctx (gΨ G) U (gdTy Δ i' l) -> Y_sub G Γ d d' Δ ->
  Y_tyne G Γ (tyGvar U d) (tyGvar U d').
Proof.
  intros Hin IH i k k' Hc HX HX'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_gvar HX) as (Δ0 & i0 & l0 & (Hv & HΓ & Hin0 & Hle & Ht & Hn & He) & _).
  destruct (inv_ty_gvar HX') as (Δ1 & i1 & l1 & (_ & _ & Hin1 & _ & Ht' & Hn' & He') & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <-.
  rewrite Hi in HΓ.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (HΔ & _).
  eapply actne_gvar; [exact Hin |].
  exact (IH i Hc (lift_ctx HΔ (lle_D_compt _ Hc)) (lsub_wf_prem Hi HΓ Ht Hn He) (lsub_wf_prem Hi HΓ Ht' Hn' He')).
Qed.

Lemma Y_actne_El {G Γ l l' ν ν' W} : leqv l l' -> Y_nee G Γ ν ν' W -> Y_tyne G Γ (tyEl l ν) (tyEl l' ν').
Proof.
  intros Hl IH i k k' Hc HX HX'.
  destruct (inv_ty_El HX) as ((_ & _ & Hν) & _). destruct (inv_ty_El HX') as ((_ & _ & Hν') & _).
  destruct (IH i _ _ _ _ Hc Hν Hν') as (W' & X).
  eapply actne_El; [exact (leqv_sym _ _ Hl) | exact X].
Qed.

(** ** Local contexts *)

Lemma Y_acc_nil {G} : Y_ctx G cnil cnil.
Proof. red; intros; apply acc_nil. Qed.
Lemma Y_acc_var {G g} : Y_ctx G (cvar g) (cvar g).
Proof. red; intros; apply acc_var. Qed.

Lemma Y_acc_ext {G Γ Γ' A A' l l'} : ac_ctx G Γ Γ' -> Y_ctx G Γ Γ' -> Y_ty G Γ A A' -> leqv l l' ->
  Y_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof.
  intros Dc IHc IHA Hl H H'.
  destruct (wfc_ext_inv H) as (HΓ & HA & W). destruct (wfc_ext_inv H') as (HΓ' & HA' & W').
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ctx_sound' Dc HΓ HΓ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HA' (lequiv_sym _ _ _ E)) as HA1.
  apply acc_ext; [exact (IHc HΓ HΓ') | | exact (leqv_sym _ _ Hl)].
  exact (cv_ty (ctx_glob _ _ _ HΓ) compt_D (IHA lD l l compt_D HA HA1) Ec HA1 HA).
Qed.

(** ** Terms *)

Lemma Y_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> Y_tmnf G Γ w w' W -> Y_tm G Γ t t' T.
Proof.
  intros HrT HwT Hr Hr' Hw Hw' IH i k Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (red_ty_sound Hc (wf_tm_ty Hi Ht) HrT HwT) as ET.
  pose proof (red_tm_sound Hc Ht Hr Hw) as Et. pose proof (red_tm_sound Hc Ht' Hr' Hw') as Et'.
  assert (EW : [ G ; Γ ⊢[ typeof i ] W ≅ T @ k ]) by (rewrite Hi; exact (eqty_sym _ _ _ _ _ _ ET)).
  eapply actm_red; [exact HrT | exact HwT | exact Hr' | exact Hr | exact Hw' | exact Hw |].
  exact (IH i k Hc (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Et) EW) (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Et') EW)).
Qed.

Lemma Y_actmnf_code_nat {G Γ l} : Y_tmnf G Γ tmNat tmNat (tyU l).
Proof. red; intros; apply actmnf_code_nat. Qed.
Lemma Y_actmnf_code_U {G Γ l k k'} : leqv k k' -> Y_tmnf G Γ (tmU k) (tmU k') (tyU l).
Proof. intros Hl; red; intros; apply actmnf_code_U, leqv_sym, Hl. Qed.

Lemma Y_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> Y_tm G Γ s s' (tyU l1) ->
  ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) -> Y_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  Y_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs Dt IHt i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_pi Hi Hx) as ((Hv & W1 & W2 & Hs & Ht) & _).
  destruct (inv_code_pi Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; [exact Hv | exact E13 | exact Es]).
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_tm Hi EEl' (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  apply actmnf_code_pi; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | |].
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs (eqty_sym _ _ _ _ _ _ EU1)).
  - assert (Hctx : [ G ⊢[ i ] Γ ,, tyEl l1 s @ l1 ≅ Γ ,, tyEl l3 s' @ l3 ])
      by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HEl | exact EEl | exact E13]).
    exact (cv_tm HG Hc (IHt i _ Hc Ht Ht2) Hctx Ht2 Ht (eqty_sym _ _ _ _ _ _ EU2)).
Qed.

Lemma Y_actmnf_zero {G Γ} : Y_tmnf G Γ zero zero tyNat.
Proof. red; intros; apply actmnf_zero. Qed.

Lemma Y_actmnf_succ {G Γ t t'} : Y_tm G Γ t t' tyNat -> Y_tmnf G Γ (succ t) (succ t') tyNat.
Proof.
  intros IH i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_succ Hi Hx) as ((_ & Ht) & _). destruct (inv_succ Hi Hx') as ((_ & Ht') & _).
  apply actmnf_succ. exact (IH i lzero Hc Ht Ht').
Qed.

Lemma Y_actmnf_ne {G Γ ν ν' W W'} : posty W -> Y_nee G Γ ν ν' W' -> Y_tmnf G Γ ν ν' W.
Proof.
  intros Hp IH i k Hc Hν Hν'. destruct (IH i _ _ _ _ Hc Hν Hν') as (W2 & X).
  eapply actmnf_ne; [exact Hp | exact X].
Qed.

Lemma Y_actmnf_eta {G Γ l l' A B w w'} :
  Y_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  Y_tmnf G Γ w w' (tyPi l l' A B).
Proof.
  intros IH i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi (wf_tm_ty Hi Hw)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  apply actmnf_eta. exact (IH i l' Hc (pre_eta_body Hi Hv W1 W2 HA HB Hw1) (pre_eta_body Hi Hv W1 W2 HA HB Hw1')).
Qed.

Lemma Y_actmnf_ueta {G Γ n l T w w'} :
  Y_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  Y_tmnf G Γ w w' (tyUPi n l T).
Proof.
  intros IH i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_upi (wf_tm_ty Hi Hw)) as ((-> & HΓ & Hn & W & HT) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  apply actmnf_ueta. exact (IH lM l compt_M (wf_ueta_body W HT Hw1) (wf_ueta_body W HT Hw1')).
Qed.

Lemma Y_actmnf_ceta {G Γ l T w w'} :
  Y_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T -> Y_tmnf G Γ w w' (tyCPi l T).
Proof.
  intros IH i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_cpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & W & HT) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  apply actmnf_ceta. exact (IH lM l compt_M (wf_ceta_body W HT Hw1) (wf_ceta_body W HT Hw1')).
Qed.

Lemma Y_actmnf_teta {G Γ Δ l l' T w w'} :
  Y_tm (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  Y_tmnf G Γ w w' (tyTPi Δ l l' T).
Proof.
  intros IH i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_tpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & HΔ & W1 & W2 & HT) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  apply actmnf_teta. exact (IH lM l' compt_M (wf_teta_body HΔ W1 W2 HT Hw1) (wf_teta_body HΔ W1 W2 HT Hw1')).
Qed.

Lemma Y_actmnf_boxT {G Γ Δ l T T'} : ty_leq T T' -> Y_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ l).
Proof. intros H; red; intros; apply actmnf_boxT, ty_leq_sym, H. Qed.
Lemma Y_actmnf_boxt {G Γ Δ A l t t'} : tm_leq t t' -> Y_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ A l).
Proof. intros H; red; intros; apply actmnf_boxt, tm_leq_sym, H. Qed.

(** ** Neutral terms *)

Lemma compt_notV {i} : compt i -> i <> lV.
Proof. intros [-> | ->]; discriminate. Qed.

Lemma Y_actmnee_red {G Γ ν ν' T W} : Y_ne G Γ ν ν' T -> reds_ty T W -> whnf_ty W -> Y_nee G Γ ν ν' W.
Proof.
  intros IH _ _ i k k' A A' Hc Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (IH i k k' A A' Hc Hν Hν') as (T' & X).
  destruct (ac_ne_sound' X Hc Hν' Hν) as (EA' & _ & _).
  destruct (tgt_whnf Hc (eqty_wf_r Hi EA')) as (W' & Hr' & Hw' & _).
  exists W'. exact (actmnee_red _ _ _ _ _ _ X Hr' Hw').
Qed.

Lemma Y_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> ac_tm G Γ (llk d n) (llk d' n) A[d]) ->
  (forall n A k, in_ctx Θ n A k -> Y_tm G Γ (llk d n) (llk d' n) A[d]) -> Y_sub G Γ d d' Θ.
Proof.
  intros D IH i Hc HΘ Hd Hd'. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all))))))) _ _ _ _ _
                (acs_pt _ _ _ _ _ D) i Hc HΘ Hd Hd') as Edd.
  destruct Edd as (_ & _ & Ee).
  apply acs_pt. intros n A k Hin.
  pose proof (lsw_var _ _ _ _ _ Hd _ _ _ Hin) as H1.
  pose proof (eqtm_wf_r Hi (Ee _ _ _ Hin)) as H2.
  pose proof (IH n A k Hin i k Hc H1 H2) as X.
  pose proof (wf_ty_func Hi (in_ctx_wf Hi HΘ Hin)
                (conj Hd (conj Hd' Ee))) as EA.
  exact (cv_tm (ctx_glob _ _ _ (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H1)) Hc X
           (eqc_refl _ _ _ (ctx_of_wf_tm Hi H1)) H2 H1 (eqty_sym _ _ _ _ _ _ EA)).
Qed.

Lemma Y_actmne_var {G Γ n T l} : in_ctx Γ n T l -> Y_ne G Γ (var n) (var n) T.
Proof. intros Hin; red; intros. exists T. exact (actmne_var _ _ _ _ _ Hin). Qed.

Lemma Y_actmne_gvar {G Γ u Δ i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ i' T l) -> Y_sub G Γ d d' Δ ->
  Y_ne G Γ (gvar u d) (gvar u d') T[d].
Proof.
  intros Hin IH i k k' X X' Hc Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_gvar Hi Hν) as (Δ0 & i0 & T0 & l0 & (HΓ & Hin0 & Hle & Ht & Hn & He) & _ & _).
  destruct (inv_gvar Hi Hν') as (Δ1 & i1 & T1 & l1 & (_ & Hin1 & _ & Ht' & Hn' & He') & _ & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <- <-.
  pose proof HΓ as HΓi. rewrite Hi in HΓi.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓi) Hin) as (HΔ & _).
  exists T[d']. eapply actmne_gvar; [exact Hin |].
  exact (IH i Hc (lift_ctx HΔ (lle_D_compt _ Hc)) (lsub_wf_prem Hi HΓi Ht Hn He) (lsub_wf_prem Hi HΓi Ht' Hn' He')).
Qed.

Lemma Y_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  ac_ty G (Γ ,, tyNat @ lzero) M M' -> Y_ty G (Γ ,, tyNat @ lzero) M M' ->
  ac_tm G Γ s s' M[lsingle zero] -> Y_tm G Γ s s' M[lsingle zero] ->
  ac_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> Y_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] ->
  Y_nee G Γ ν ν' W ->
  Y_ne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof.
  intros Hl DM IHM Ds IHs Dz IHz IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_natrec Hi Hx) as ((Hv & Wl & HM & Hs & Hz & Hν) & _ & _).
  destruct (inv_natrec Hi Hx') as ((_ & Wl' & HM' & Hs' & Hz' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as E.
  pose proof (wft_lconv _ _ _ _ _ _ HM' E) as HM1.
  pose proof (ac_ty_sound Hc DM HM HM1) as EM.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HN : [ G ; Γ ⊢[ i ] tyNat @ lzero ]) by (apply wft_nat; [exact Hv | rewrite Hi; exact HΓ]).
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HN | exact I]).
  assert (H0 : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; [exact Hv | rewrite Hi; exact HΓ]).
  pose proof (eqty_single Hi EM H0) as EM0.
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E] | rewrite Hi; exact EM0]).
  assert (HΓM : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] ]) by (apply wfc_ext; assumption).
  assert (EM' : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' ≅ M @ l' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM) | exact (lequiv_sym _ _ _ E)]).
  pose proof (stab_tm Hi EM' (lequiv_sym _ _ _ E) HΓM Hz') as Hz1.
  pose proof (eqty_subst Hi EM (lsub_wf_lsucc Hi Hv HΓM)) as EMs.
  assert (Hz2 : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hz1 | exact E] | rewrite Hi; exact EMs]).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W' & Xν).
  exists M'[lsingle ν']. eapply actmne_natrec; [exact (leqv_sym _ _ Hl) | | | | exact Xν].
  - exact (IHM i l l Hc HM HM1).
  - exact (cv_tm HG Hc (IHs i l Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs (eqty_sym _ _ _ _ _ _ EM0)).
  - assert (Hctx : [ G ⊢[ i ] Γ ,, tyNat @ lzero ,, M @ l ≅ Γ ,, tyNat @ lzero ,, M' @ l' ])
      by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓN) | exact HM | exact EM | exact E]).
    exact (cv_tm HG Hc (IHz i l Hc Hz Hz2) Hctx Hz2 Hz (eqty_sym _ _ _ _ _ _ EMs)).
Qed.

Lemma Y_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> Y_nee G Γ ν ν' (tyPi m m' A0 B0) ->
  ac_tm G Γ s s' A0 -> Y_tm G Γ s s' A0 ->
  Y_ne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof.
  intros Dν IHν Ds IHs i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν & Hs) & _ & _).
  destruct (inv_app Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν' & Hs') & _ & _).
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (pi_inj_c Hc E0) as (Em1 & Em2 & EA0 & EB0).
  destruct (pi_inj_c Hc E1) as (Em3 & Em4 & EA1 & EB1).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em1) Em3) as E13.
  assert (EA : [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ]).
  { eapply eqty_trans; [exact EA0 |]. apply eqty_sym.
    eapply eqty_lconv; [exact EA1 | exact E13]. }
  assert (Hs0 : [ G ; Γ ⊢[ i ] s : A0 @ l1 ])
    by (eapply wf_conv; [exact Hs | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA0)]).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : A @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E13] | rewrite Hi; exact EA]).
  assert (Hs1' : [ G ; Γ ⊢[ i ] s' : A0 @ l1 ])
    by (eapply wf_conv; [exact Hs1 | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA0)]).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W & Xν).
  destruct (ac_nee_sound' Xν Hc Hν' Hν) as (EW & _ & _).
  pose proof (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E1) as EW0.
  destruct (head_pi W (decl_head_c Hc EW0 (ac_tmnee_whnf Xν) (whnf_tyPi _ _ _ _))) as (n1 & n2 & A2 & B2 & ->).
  destruct (pi_inj_c Hc (eqty_sym _ _ _ _ _ _ EW0)) as (_ & _ & EA2 & _).
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  exists B2[lsingle s']. eapply actmne_app; [exact Xν |].
  apply (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHs i l1 Hc Hs0 Hs1') (eqc_refl _ _ _ HΓ) Hs1' Hs0).
  exact (eqty_sym _ _ _ _ _ _ (eqty_lconv _ _ _ _ _ _ _ EA2 (lequiv_sym _ _ _ Em1))).
Qed.

Lemma Y_actmne_uapp {G Γ n l T ν ν' ls ls'} :
  ac_tmnee G Γ ν ν' (tyUPi n l T) -> Y_nee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' -> Y_ne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros Dν IHν Hn Hls i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_uapp Hi Hx) as (n0 & l0 & T0 & (-> & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_uapp Hi Hx') as (n1 & l1 & T1 & (_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (_ & E1 & _).
  destruct (IHν lM _ _ _ _ compt_M Hν Hν') as (W & Xν).
  destruct (ac_nee_sound' Xν compt_M Hν' Hν) as (EW & _ & _).
  pose proof (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E1) as EW0.
  destruct (head_upi W (decl_head_c compt_M EW0 (ac_tmnee_whnf Xν) (whnf_tyUPi _ _ _))) as (n2 & m & T2 & ->).
  destruct (declM_upi_inj (eqty_sym _ _ _ _ _ _ EW0)) as (-> & _ & _).
  exists T2[uext ls' lvar]ᵤ. eapply actmne_uapp; [exact Xν | | exact (leqvs_sym _ _ Hls)].
  rewrite <- (Forall2_length Hls). exact Hn.
Qed.

Lemma Y_actmne_capp {G Γ l T ν ν' Δ Δ'} :
  ac_tmnee G Γ ν ν' (tyCPi l T) -> Y_nee G Γ ν ν' (tyCPi l T) -> Y_ctx G Δ Δ' ->
  Y_ne G Γ (capp ν Δ) (capp ν' Δ') T⦃gsingle (GCtx Δ)⦄.
Proof.
  intros Dν IHν IHc i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_capp Hi Hx) as (l0 & T0 & (-> & _ & _ & HΔ & Hν & _) & _ & _).
  destruct (inv_capp Hi Hx') as (l1 & T1 & (_ & _ & _ & HΔ' & Hν' & _) & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (_ & E1 & _).
  destruct (IHν lM _ _ _ _ compt_M Hν Hν') as (W & Xν).
  destruct (ac_nee_sound' Xν compt_M Hν' Hν) as (EW & _ & _).
  pose proof (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E1) as EW0.
  destruct (head_cpi W (decl_head_c compt_M EW0 (ac_tmnee_whnf Xν) (whnf_tyCPi _ _))) as (m & T2 & ->).
  exists T2⦃gsingle (GCtx Δ')⦄. eapply actmne_capp; [exact Xν | exact (IHc HΔ HΔ')].
Qed.

Lemma Y_actmne_tapp {G Γ Δ l l' T ν ν' A A'} :
  ac_tmnee G Γ ν ν' (tyTPi Δ l l' T) -> Y_nee G Γ ν ν' (tyTPi Δ l l' T) -> Y_ty G Δ A A' ->
  Y_ne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof.
  intros Dν IHν IHA i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T0 & (-> & Hν & HΔ0 & W0 & W0' & HT0 & HA & _) & _ & _).
  destruct (inv_tapp Hi Hx') as (Δ1 & l1 & l1' & T1 & (_ & Hν' & HΔ1 & W1 & W1' & HT1 & HA' & _) & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & E1 & _).
  destruct (declM_tpi_inj E0) as (Ec0 & El0 & _ & _).
  destruct (declM_tpi_inj E1) as (Ec1 & El1 & _ & _).
  pose proof (decl_ty_ctxconv_D Ec0 HA (lequiv_refl _ _ W0)) as HAΔ.
  pose proof (decl_ty_ctxconv_D Ec1 HA' (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ El1) El0)) as HA'Δ.
  destruct (IHν lM _ _ _ _ compt_M Hν Hν') as (W & Xν).
  destruct (ac_nee_sound' Xν compt_M Hν' Hν) as (EW & _ & _).
  pose proof (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E1) as EW0.
  destruct (head_tpi W (decl_head_c compt_M EW0 (ac_tmnee_whnf Xν) (whnf_tyTPi _ _ _ _))) as (Δ2 & m & m' & T2 & ->).
  destruct (declM_tpi_inj (eqty_sym _ _ _ _ _ _ EW0)) as (HΔΔ2 & _ & _ & _).
  exists T2⦃gsingle (GTy A')⦄. eapply actmne_tapp; [exact Xν |].
  exact (cv_ty (ctx_glob _ _ _ HΔ0) compt_D (IHA lD l0 l0 compt_D HAΔ HA'Δ) HΔΔ2 HA'Δ HAΔ).
Qed.

Lemma Y_actmne_letboxT {G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ctx G Δ Δ' -> Y_ctx G Δ Δ' ->
  ac_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' -> Y_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' ->
  Y_tm (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  Y_nee G Γ ν ν' W ->
  Y_ne G Γ (letboxT l1 l2 Δ M t1 ν) (letboxT l3 l4 Δ' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 Dc IHc DM IHM IHt IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxT Hi Hx) as ((-> & W1 & W2 & HΔ & HM & Ht1 & Hν) & _ & _).
  destruct (inv_letboxT Hi Hx') as ((_ & W3 & W4 & HΔ' & HM' & Ht2 & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ' l4 @ lzero ]) by (apply eqty_CTyp; assumption).
  assert (HC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 @ lzero ]) by (apply wft_CTyp; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC)
                                        (lequiv_refl (gL G) lzero I) HΓ1 HM') E13) as HM1.
  pose proof (ac_ty_sound compt_M DM HM HM1) as EM.
  assert (HGD : [ ⊢ gext G (gdTy Δ lC l2) ]) by (apply wfg_ty; [exact HG | exact HΔ | left; reflexivity | exact W2]).
  assert (HGD' : [ ⊢ gext G (gdTy Δ' lC l4) ]) by (apply wfg_ty; [exact HG | exact HΔ' | left; reflexivity | exact W4]).
  pose proof (gbind_obj_ty (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) HGD Ec E24) as Ho.
  pose proof (gbind_tm HG HGD Ho eq_refl Ht2) as Ht2a.
  pose proof (letboxT_body_eq HGD HΔ W2 EM) as EMb.
  assert (Ht2b : [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E13] | exact EMb]).
  pose proof (GEq_ext (GEq_refl _ HG) HGD HGD' (conj eq_refl (conj (or_introl eq_refl) (conj E24 Ec)))) as HE.
  destruct (IHν lM _ _ _ _ compt_M Hν Hν') as (W' & Xν).
  exists M'[lsingle ν']. eapply actmne_letboxT; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24)
                                                 | exact (IHc HΔ HΔ') | | | exact Xν].
  - assert (Hctx : [ G ⊢[ lM ] Γ ,, tyCTyp Δ l2 @ lzero ≅ Γ ,, tyCTyp Δ' l4 @ lzero ])
      by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HC | exact HCC | exact (lequiv_refl (gL G) lzero I)]).
    exact (cv_ty HG compt_M (IHM lM l1 l1 compt_M HM HM1) Hctx HM1 HM).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_conv_all)))) _ _ _ _ _ (IHt lM l1 compt_M Ht1 Ht2b) lM _ _ _ l1
             compt_M HE (eqc_refl _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht2)) Ht2b Ht1
             (eqty_sym _ _ _ _ _ _ (gconv_eqty HE eq_refl EMb))).
Qed.

Lemma Y_actmne_letboxt {G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ctx G Δ Δ' -> Y_ctx G Δ Δ' -> ac_ty G Δ T T' -> Y_ty G Δ T T' ->
  ac_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' -> Y_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' ->
  Y_tm (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  Y_nee G Γ ν ν' W ->
  Y_ne G Γ (letboxt l1 l2 Δ T M t1 ν) (letboxt l3 l4 Δ' T' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 Dc IHc DT IHT DM IHM IHt IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxt Hi Hx) as ((-> & W1 & W2 & HΔ & HT & HM & Ht1 & Hν) & _ & _).
  destruct (inv_letboxt Hi Hx') as ((_ & W3 & W4 & HΔ' & HT' & HM' & Ht2 & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E24)) as HT1.
  pose proof (ac_ty_sound compt_D DT HT HT1) as ET.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ' T' l4 @ lzero ]) by (apply eqty_CTrm; assumption).
  assert (HC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 @ lzero ]) by (apply wft_CTrm; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC)
                                        (lequiv_refl (gL G) lzero I) HΓ1 HM') E13) as HM1.
  pose proof (ac_ty_sound compt_M DM HM HM1) as EM.
  assert (HGD : [ ⊢ gext G (gdTm Δ lC T l2) ]) by (apply wfg_tm; [exact HG | exact HT | right; reflexivity | exact W2]).
  assert (HGD' : [ ⊢ gext G (gdTm Δ' lC T' l4) ]) by (apply wfg_tm; [exact HG | exact HT' | right; reflexivity | exact W4]).
  pose proof (gbind_obj_tm HGD Ec ET E24) as Ho.
  pose proof (gbind_tm HG HGD Ho eq_refl Ht2) as Ht2a.
  pose proof (letboxt_body_eq HGD HΔ HT W2 EM) as EMb.
  assert (Ht2b : [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E13] | exact EMb]).
  pose proof (GEq_ext (GEq_refl _ HG) HGD HGD' (conj eq_refl (conj (or_intror eq_refl) (conj E24 (conj Ec ET)))))
    as HE.
  destruct (IHν lM _ _ _ _ compt_M Hν Hν') as (W' & Xν).
  exists M'[lsingle ν']. eapply actmne_letboxt; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24)
                                                 | exact (IHc HΔ HΔ') | | | | exact Xν].
  - exact (cv_ty (ctx_glob _ _ _ HΔ) compt_D (IHT lD l2 l2 compt_D HT HT1) Ec HT1 HT).
  - assert (Hctx : [ G ⊢[ lM ] Γ ,, tyCTrm Δ T l2 @ lzero ≅ Γ ,, tyCTrm Δ' T' l4 @ lzero ])
      by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HC | exact HCC | exact (lequiv_refl (gL G) lzero I)]).
    exact (cv_ty HG compt_M (IHM lM l1 l1 compt_M HM HM1) Hctx HM1 HM).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_conv_all)))) _ _ _ _ _ (IHt lM l1 compt_M Ht1 Ht2b) lM _ _ _ l1
             compt_M HE (eqc_refl _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht2)) Ht2b Ht1
             (eqty_sym _ _ _ _ _ _ (gconv_eqty HE eq_refl EMb))).
Qed.

(** The recursors: the motives are compared in the same scope; the
    branches move to the right motives' scope ([brΓ_conv]). *)
Lemma Y_rec_core {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs'} :
  ac_ty (recGT G) (recΓT Γ) MT MT' -> Y_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> Y_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> Y_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  [ G ; Γ ⊢[ lM ] ] -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] -> [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] -> [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                         bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ]) ->
  ac_ty (recGT G) (recΓT Γ) MT' MT /\ ac_ty (recGt G) (recΓt Γ) Mt' Mt /\
  (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2')
                         (bs' j) (bs j) (brRes j (wrapMT MT') (wrapMt Mt'))).
Proof.
  intros DMT IHT DMt IHt IHb HΓ E1 E2 HMT HMT' HMt HMt' Hbc Hbc' Hbs Hbs'.
  pose proof (wft_lconv _ _ _ _ _ _ HMT' (lequiv_ush 1 E1)) as HMT1.
  pose proof (wft_lconv _ _ _ _ _ _ HMt' (lequiv_ush 1 E2)) as HMt1.
  pose proof (ac_ty_sound compt_M DMT HMT HMT1) as EMT.
  pose proof (ac_ty_sound compt_M DMt HMt HMt1) as EMt.
  refine (conj (IHT lM _ _ compt_M HMT HMT1) (conj (IHt lM _ _ compt_M HMt HMt1) _)).
  intros j Hj.
  pose proof (branch_conv j Hj EMT EMt E1 E2 HΓ (Hbc j Hj) (Hbc' j Hj) (Hbs' j Hj)) as Hb1.
  destruct (brΓ_conv j Hj EMT EMt E1 E2 HΓ (Hbc j Hj)) as [HCC HR].
  exact (cv_tm (ctx_glob _ _ _ (Hbc j Hj)) compt_M (IHb j Hj lM _ compt_M (Hbs j Hj) Hb1) HCC Hb1 (Hbs j Hj)
           (eqty_sym _ _ _ _ _ _ HR)).
Qed.

Ltac yrec_core IHT IHt IHb DMT DMt :=
  let HΓ := fresh "HΓ" in
  match goal with Hν : [ _ ; ?Γ ⊢[ lM ] _ : _ @ _ ] |- _ =>
    pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ end;
  match goal with
  | W1 : lwf _ ?l1, W1' : lwf _ ?l1', H1 : leqv ?l1 ?l1', W2 : lwf _ ?l2, W2' : lwf _ ?l2', H2 : leqv ?l2 ?l2',
    HMT : [ recGT _ ; _ ⊢[ lM ] ?MT @ _ ], HMT' : [ recGT _ ; _ ⊢[ lM ] ?MT' @ _ ],
    HMt : [ recGt _ ; _ ⊢[ lM ] ?Mt @ _ ], HMt' : [ recGt _ ; _ ⊢[ lM ] ?Mt' @ _ ],
    Hbc : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT) _ _ _ ⊢[ lM ] ],
    Hbc' : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT') _ _ _ ⊢[ lM ] ],
    Hbs : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT) _ _ _ ⊢[ lM ] _ : _ @ _ ],
    Hbs' : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT') _ _ _ ⊢[ lM ] _ : _ @ _ ],
    Eb : forall k, k < nbr -> ?bs k = _, Eb' : forall k, k < nbr -> ?bs' k = _ |- _ =>
    let Hbs0 := fresh "Hbs0" in let Hbs1 := fresh "Hbs1" in
    assert (Hbs0 : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT MT) _ _ _ ⊢[ lM ]
                                        bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
      by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj));
    assert (Hbs1 : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT MT') _ _ _ ⊢[ lM ]
                                        bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ])
      by (intros j Hj; rewrite (Eb' j Hj); exact (Hbs' j Hj));
    destruct (Y_rec_core DMT IHT DMt IHt IHb HΓ (leqv_lequiv _ _ _ W1 W1' H1)
                (leqv_lequiv _ _ _ W2 W2' H2) HMT HMT' HMt HMt' Hbc Hbc' Hbs0 Hbs1) as (XMT & XMt & Xb)
  end.

Lemma Y_actmne_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> Y_ctx G Δ Δ' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> Y_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> Y_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> Y_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  Y_nee G Γ ν ν' W ->
  Y_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν')
    (motT (wrapMT MT) l Δ ν).
Proof.
  intros H1 H2 Hl IHc DMT IHT DMt IHt IHb IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'. yrec_core IHT IHt IHb DMT DMt.
  destruct (IHν lM _ _ _ _ compt_M Hν Hν') as (W' & Xν).
  eexists. eapply actmne_elimT; [exact (leqv_sym _ _ H1) | exact (leqv_sym _ _ H2) | exact (leqv_sym _ _ Hl)
                                | exact (IHc HΔ HΔ') | exact XMT | exact XMt | exact Xb | exact Xν].
Qed.

Lemma Y_actmne_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' U d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> Y_ctx G Δ Δ' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> Y_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> Y_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> Y_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  Y_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d)))
    (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' (boxT (tyGvar U d')))
    (motT (wrapMT MT) l Δ (boxT (tyGvar U d))).
Proof.
  intros H1 H2 Hl IHc DMT IHT DMt IHt IHb Hd i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'. yrec_core IHT IHt IHb DMT DMt.
  eexists. eapply actmne_elimT_gvar; [exact (leqv_sym _ _ H1) | exact (leqv_sym _ _ H2) | exact (leqv_sym _ _ Hl)
                                     | exact (IHc HΔ HΔ') | exact XMT | exact XMt | exact Xb |].
  exact (proj2 (proj2 (proj2 leq_sym_all)) _ _ Hd).
Qed.

Lemma Y_actmne_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> Y_ctx G Δ Δ' -> Y_ty G Δ T T' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> Y_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> Y_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> Y_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  Y_nee G Γ ν ν' W ->
  Y_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' ν')
    (mott (wrapMt Mt) l Δ T ν).
Proof.
  intros H1 H2 Hl Dc IHc IHi DMT IHT DMt IHt IHb IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'. yrec_core IHT IHt IHb DMT DMt.
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as El.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ El)) as HT1.
  destruct (IHν lM _ _ _ _ compt_M Hν Hν') as (W' & Xν).
  eexists. eapply actmne_elimt; [exact (leqv_sym _ _ H1) | exact (leqv_sym _ _ H2) | exact (leqv_sym _ _ Hl)
                                | exact (IHc HΔ HΔ') | | exact XMT | exact XMt | exact Xb | exact Xν].
  exact (cv_ty (ctx_glob _ _ _ HΔ) compt_D (IHi lD l l compt_D HT HT1) Ec HT1 HT).
Qed.

Lemma Y_actmne_elimt_glob {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' c c'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> Y_ctx G Δ Δ' -> Y_ty G Δ T T' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> Y_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> Y_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> Y_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  boxed_global c -> tm_leq c c' ->
  Y_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c))
    (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' (boxt c'))
    (mott (wrapMt Mt) l Δ T (boxt c)).
Proof.
  intros H1 H2 Hl Dc IHc IHi DMT IHT DMt IHt IHb Hg Hd i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'. yrec_core IHT IHt IHb DMT DMt.
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as El.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ El)) as HT1.
  eexists. eapply actmne_elimt_glob; [exact (leqv_sym _ _ H1) | exact (leqv_sym _ _ H2) | exact (leqv_sym _ _ Hl)
                                     | exact (IHc HΔ HΔ') | | exact XMT | exact XMt | exact Xb | exact (boxed_global_leq _ _ Hg Hd) |].
  - exact (cv_ty (ctx_glob _ _ _ HΔ) compt_D (IHi lD l l compt_D HT HT1) Ec HT1 HT).
  - exact (tm_leq_sym _ _ Hd).
Qed.

(** ** Symmetry *)

(** ** Dependent pairs (M8) *)

Lemma Y_actnf_sig {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> Y_ty G (Γ ,, A @ l1) B B' ->
  Y_tynf G Γ (tySig l1 l2 A B) (tySig l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA DB IHB i k k' Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_sig HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_sig HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  assert (Hctx : [ G ⊢[ i ] Γ ,, A @ l1 ≅ Γ ,, A' @ l3 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact E13]).
  apply actnf_sig; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | exact (IHA i l1 l3 Hc HA HA') |].
  pose proof (IHB i l2 l4 Hc HB HB1) as X.
  exact (cv_ty (ctx_glob _ _ _ HΓ) Hc X Hctx HB1 HB).
Qed.

Lemma Y_actmnf_code_sig {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> Y_tm G Γ s s' (tyU l1) ->
  ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) -> Y_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  Y_tmnf G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs Dt IHt i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_sig Hi Hx) as ((Hc0 & W1 & W2 & Hs & Ht) & _).
  destruct (inv_code_sig Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  pose proof Hc0 as Hv.
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; [exact Hv | exact E13 | exact Es]).
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_tm Hi EEl' (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  apply actmnf_code_sig; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | |].
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs (eqty_sym _ _ _ _ _ _ EU1)).
  - assert (Hctx : [ G ⊢[ i ] Γ ,, tyEl l1 s @ l1 ≅ Γ ,, tyEl l3 s' @ l3 ])
      by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HEl | exact EEl | exact E13]).
    exact (cv_tm HG Hc (IHt i _ Hc Ht Ht2) Hctx Ht2 Ht (eqty_sym _ _ _ _ _ _ EU2)).
Qed.
Lemma Y_actmnf_code_W {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> Y_tm G Γ s s' (tyU l1) ->
  ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) -> Y_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  Y_tmnf G Γ (tmW l1 l2 s t) (tmW l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs Dt IHt i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_W Hi Hx) as ((_ & W1 & W2 & Hs & Ht) & _).
  destruct (inv_code_W Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; [exact Hv | exact E13 | exact Es]).
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_tm Hi EEl' (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  apply actmnf_code_W; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | |].
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs (eqty_sym _ _ _ _ _ _ EU1)).
  - assert (Hctx : [ G ⊢[ i ] Γ ,, tyEl l1 s @ l1 ≅ Γ ,, tyEl l3 s' @ l3 ])
      by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HEl | exact EEl | exact E13]).
    exact (cv_tm HG Hc (IHt i _ Hc Ht Ht2) Hctx Ht2 Ht (eqty_sym _ _ _ _ _ _ EU2)).
Qed.

(** The second projections are compared at the other side's first
    projection: the conversion lemma moves them. *)
Lemma Y_actmnf_sig_eta {G Γ l l' A B w w'} :
  ac_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w') A ->
  Y_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w') A ->
  Y_tm G Γ (tmSnd l l' A B w) (tmSnd l l' A B w') B[lsingle (tmFst l l' A B w)] ->
  Y_tmnf G Γ w w' (tySig l l' A B).
Proof.
  intros D1 IH1 IH2 i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_sig (wf_tm_ty Hi Hw)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1) as Hf.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1') as Hf'.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1) as Hs.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1') as Hs'.
  pose proof (ac_tm_sound Hc D1 Hf Hf') as E1.
  pose proof (sig_fam_eq Hi HB (eqty_refl _ _ _ _ _ HB) (eqtm_sym _ _ _ _ _ _ _ E1) Hf' Hf) as EBs.
  assert (Hs1 : [ G ; Γ ⊢[ i ] tmSnd l l' A B w' : B[lsingle (tmFst l l' A B w)] @ l' ])
    by (eapply wf_conv; [exact Hs' | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EBs)]).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  apply actmnf_sig_eta; [exact (IH1 i l Hc Hf Hf') |].
  exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IH2 i l' Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs EBs).
Qed.

Lemma Y_actmne_fst {G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tySig m m' A0 B0) -> Y_nee G Γ ν ν' (tySig m m' A0 B0) ->
  Y_ne G Γ (tmFst l1 l2 A B ν) (tmFst l3 l4 A' B' ν') A0.
Proof.
  intros Dν IHν i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_fst Hi Hx) as ((_ & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_fst Hi Hx') as ((_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (_ & E1 & _).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W & Xν).
  destruct (ac_nee_sound' Xν Hc Hν' Hν) as (EW & _ & _).
  pose proof (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E1) as EW0.
  destruct (head_sig W (decl_head_c Hc EW0 (ac_tmnee_whnf Xν) (whnf_tySig _ _ _ _))) as (n1 & n2 & A2 & B2 & ->).
  eexists. eapply actmne_fst; exact Xν.
Qed.

Lemma Y_actmne_snd {G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tySig m m' A0 B0) -> Y_nee G Γ ν ν' (tySig m m' A0 B0) ->
  Y_ne G Γ (tmSnd l1 l2 A B ν) (tmSnd l3 l4 A' B' ν') B0[lsingle (tmFst m m' A0 B0 ν)].
Proof.
  intros Dν IHν i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_snd Hi Hx) as ((_ & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_snd Hi Hx') as ((_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (_ & E1 & _).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W & Xν).
  destruct (ac_nee_sound' Xν Hc Hν' Hν) as (EW & _ & _).
  pose proof (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EW) E1) as EW0.
  destruct (head_sig W (decl_head_c Hc EW0 (ac_tmnee_whnf Xν) (whnf_tySig _ _ _ _))) as (n1 & n2 & A2 & B2 & ->).
  eexists. eapply actmne_snd; exact Xν.
Qed.

(** The unit type (M8c). *)
Lemma Y_actnf_unit {G Γ l l'} : leqv l l' -> Y_tynf G Γ (tyUnit l) (tyUnit l').
Proof. intros Hl; red; intros; apply actnf_unit, leqv_sym, Hl. Qed.
Lemma Y_actmnf_code_unit {G Γ l k k'} : leqv k k' -> Y_tmnf G Γ (tmUnit k) (tmUnit k') (tyU l).
Proof. intros Hl; red; intros; apply actmnf_code_unit, leqv_sym, Hl. Qed.
(** The codes of [Empty] and [+] (M12c). *)
Lemma Y_actmnf_code_empty {G Γ l k k'} : leqv k k' -> Y_tmnf G Γ (tmEmpty k) (tmEmpty k') (tyU l).
Proof. intros Hl; red; intros; apply actmnf_code_empty, leqv_sym, Hl. Qed.
Lemma Y_actmnf_code_sum {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> Y_tm G Γ s s' (tyU l1) -> ac_tm G Γ t t' (tyU l2) -> Y_tm G Γ t t' (tyU l2) ->
  Y_tmnf G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs Dt IHt i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (code_sum_prem Hc Hx) as (W1 & W2 & Hs & Ht). destruct (code_sum_prem Hc Hx') as (W3 & W4 & Hs' & Ht').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (code_U_conv Hc E13 Hs') as Hs1. pose proof (code_U_conv Hc E24 Ht') as Ht1.
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l3 ≅ tyU l1 @ lsuc l1 ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | apply lequiv_sym, E13]
                       | exact (lequiv_suc _ _ _ E13)]. }
  assert (EU2 : [ G ; Γ ⊢[ i ] tyU l4 ≅ tyU l2 @ lsuc l2 ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | apply lequiv_sym, E24]
                       | exact (lequiv_suc _ _ _ E24)]. }
  apply actmnf_code_sum; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | |].
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs EU1).
  - exact (cv_tm HG Hc (IHt i _ Hc Ht Ht1) (eqc_refl _ _ _ HΓ) Ht1 Ht EU2).
Qed.

Lemma Y_actmnf_code_sempty {G Γ l k k'} : leqv k k' -> Y_tmnf G Γ (tmSEmpty k) (tmSEmpty k') (tyU l).
Proof. intros Hl; red; intros; apply actmnf_code_sempty, leqv_sym, Hl. Qed.
Lemma Y_actmnf_unit_eta {G Γ l w w'} : Y_tmnf G Γ w w' (tyUnit l).
Proof. red; intros; apply actmnf_unit_eta. Qed.

(** Strict equality (M10a). *)
Lemma Y_actnf_seq {G Γ l l' A A' a a' b b'} : leqv l l' ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_tm G Γ a a' A -> Y_tm G Γ a a' A ->
  ac_tm G Γ b b' A -> Y_tm G Γ b b' A -> Y_tynf G Γ (tySEq l A a b) (tySEq l' A' a' b').
Proof.
  intros Hl DA IHA Da IHa Db IHb i k k' Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_seq HT) as ((_ & W & HA & Ha & Hb) & _).
  destruct (inv_ty_seq HT') as ((_ & W' & HA' & Ha' & Hb') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EA]. }
  pose proof (eqty_sym _ _ _ _ _ _ EA) as EA'.
  apply actnf_seq; [exact (leqv_sym _ _ Hl) | exact (IHA i l l' Hc HA HA') | |].
  - exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHa i l Hc Ha (F _ Ha')) (eqc_refl _ _ _ HΓ) (F _ Ha') Ha EA').
  - exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHb i l Hc Hb (F _ Hb')) (eqc_refl _ _ _ HΓ) (F _ Hb') Hb EA').
Qed.
(** The identity type (M11a). *)
Lemma Y_actnf_id {G Γ l l' A A' a a' b b'} : leqv l l' ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_tm G Γ a a' A -> Y_tm G Γ a a' A ->
  ac_tm G Γ b b' A -> Y_tm G Γ b b' A -> Y_tynf G Γ (tyId l A a b) (tyId l' A' a' b').
Proof.
  intros Hl DA IHA Da IHa Db IHb i k k' Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_id HT) as ((_ & W & HA & Ha & Hb) & _).
  destruct (inv_ty_id HT') as ((_ & W' & HA' & Ha' & Hb') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EA]. }
  pose proof (eqty_sym _ _ _ _ _ _ EA) as EA'.
  apply actnf_id; [exact (leqv_sym _ _ Hl) | exact (IHA i l l' Hc HA HA') | |].
  - exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHa i l Hc Ha (F _ Ha')) (eqc_refl _ _ _ HΓ) (F _ Ha') Ha EA').
  - exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHb i l Hc Hb (F _ Hb')) (eqc_refl _ _ _ HΓ) (F _ Hb') Hb EA').
Qed.
Lemma Y_actmnf_refl {G Γ l A a b k k' C C' c c'} : Y_tmnf G Γ (tmRefl k C c) (tmRefl k' C' c') (tyId l A a b).
Proof. red; intros; apply actmnf_refl. Qed.
Lemma Y_actmne_J {G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_tm G Γ a a' A -> Y_tm G Γ a a' A ->
  ac_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  Y_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  ac_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] -> Y_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] ->
  ac_tm G Γ u u' A -> Y_tm G Γ u u' A -> Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmJ l1 l2 A a M c u ν) (tmJ l3 l4 A' a' M' c' u' ν') M[lsingle2 u ν].
Proof.
  intros H13 H24 DA IHA Da IHa DM IHM Dc IHc Du IHu IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (inv_J Hi Hx) as ((_ & W1 & W2 & HA & Ha & HI & HM & Hcc & Hu & He) & _ & _).
  destruct (inv_J Hi Hx') as ((_ & W3 & W4 & HA' & Ha' & HI' & HM' & Hc' & Hu' & He') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (F : forall y, [ G ; Γ ⊢[ i ] y : A' @ l3 ] -> [ G ; Γ ⊢[ i ] y : A @ l1 ]).
  { intros y Hy. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hy E13) | rewrite Hi; exact EA]. }
  pose proof (F _ Ha') as Ha'1. pose proof (F _ Hu') as Hu'1.
  pose proof (ac_tm_sound Hc Da Ha Ha'1) as Ea.
  pose proof (J_ctx_conv Hi Hc E13 HA HA' EA Ea) as Hid.
  pose proof (wf_ty_subst Hi HM' Hid) as HM'1. rewrite nf_id_ty in HM'1 by exact (wf_ty_nf HM').
  assert (HM'2 : [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M' @ l2 ])
    by exact (wft_lconv _ _ _ _ _ _ HM'1 E24).
  pose proof (ac_ty_sound Hc DM HM HM'2) as EM.
  assert (Hr : [ G ; Γ ⊢[ i ] tmRefl l1 A a : tyId l1 A a a @ l1 ]) by (apply wf_idrefl; auto).
  pose proof (pre_idrefl_r Hi Hv E13 HA EA (eqty_wf_r Hi EA) Ea Ha'1) as Hr'.
  assert (Hrr : [ G ; Γ ⊢[ i ] tmRefl l1 A a ≅ tmRefl l3 A' a' : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; auto).
  pose proof (lsub_eq_J Hi Hv W1 HA Ha Ha Ha'1 Ea Hr Hr' Hrr) as Hs.
  assert (HMs : [ G ; Γ ⊢[ i ] M[lsingle2 a (tmRefl l1 A a)] ≅ M'[lsingle2 a' (tmRefl l3 A' a')] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi EM (lsub_eq_l Hs)) | exact (wf_ty_func Hi HM'2 Hs)]. }
  assert (Hc'1 : [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc' E24) | rewrite Hi; exact HMs]. }
  pose proof (eqty_sym _ _ _ _ _ _ EA) as EA'.
  destruct (IHν i _ _ _ _ Hc He He') as (W' & Xν).
  exists M'[lsingle2 u' ν']. eapply actmne_J; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | | | | | | exact Xν].
  - exact (IHA i l1 l3 Hc HA HA').
  - exact (cv_tm HG Hc (IHa i l1 Hc Ha Ha'1) (eqc_refl _ _ _ HΓ) Ha'1 Ha EA').
  - exact (cv_ty HG Hc (IHM i l2 l2 Hc HM HM'2) (J_ctx_eq Hi Hv E13 HA EA Ea) HM'2 HM).
  - exact (cv_tm HG Hc (IHc i l2 Hc Hcc Hc'1) (eqc_refl _ _ _ HΓ) Hc'1 Hcc (eqty_sym _ _ _ _ _ _ HMs)).
  - exact (cv_tm HG Hc (IHu i l1 Hc Hu Hu'1) (eqc_refl _ _ _ HΓ) Hu'1 Hu EA').
Qed.

(** The empty type (M12a). *)
Lemma Y_actnf_empty {G Γ l l'} : leqv l l' -> Y_tynf G Γ (tyEmpty l) (tyEmpty l').
Proof. intros Hl; red; intros; apply actnf_empty, leqv_sym, Hl. Qed.

Lemma Y_actmne_elimEmpty {G Γ l1 l2 l3 l4 M M' ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G (Γ ,, tyEmpty l2 @ l2) M M' -> Y_ty G (Γ ,, tyEmpty l2 @ l2) M M' -> Y_nee G Γ ν ν' W ->
  Y_ne G Γ (elimEmpty l1 l2 M ν) (elimEmpty l3 l4 M' ν') M[lsingle ν].
Proof.
  intros H13 H24 DM IHM IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimEmpty Hi Hx) as ((_ & W1 & W2 & HM & Hν) & _ & _).
  destruct (inv_elimEmpty Hi Hx') as ((_ & W3 & W4 & HM' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HE2 : [ G ; Γ ⊢[ i ] tyEmpty l2 @ l2 ]) by (apply wft_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact W2]).
  assert (HE : [ G ; Γ ⊢[ i ] tyEmpty l4 ≅ tyEmpty l2 @ l4 ])
    by (apply eqty_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact (lequiv_sym _ _ _ E24)]).
  assert (HΓE : [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HE2 | exact W2]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi HE (lequiv_sym _ _ _ E24) HΓE HM') E13) as HM'2.
  assert (Hctx : [ G ⊢[ i ] Γ ,, tyEmpty l2 @ l2 ≅ Γ ,, tyEmpty l4 @ l4 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HE2
                       | apply eqty_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact E24] | exact E24]).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W' & Xν).
  exists M'[lsingle ν']. eapply actmne_elimEmpty; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | | exact Xν].
  exact (cv_ty HG Hc (IHM i l1 l1 Hc HM HM'2) Hctx HM'2 HM).
Qed.

(** Binary sums (M12b). *)
Lemma Y_actnf_sum {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  Y_ty G Γ A A' -> Y_ty G Γ B B' -> Y_tynf G Γ (tySum l1 l2 A B) (tySum l3 l4 A' B').
Proof.
  intros H13 H24 IHA IHB i k k' Hc HT HT'.
  destruct (inv_ty_sum HT) as ((_ & _ & _ & HA & HB) & _).
  destruct (inv_ty_sum HT') as ((_ & _ & _ & HA' & HB') & _).
  apply actnf_sum; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | exact (IHA i l1 l3 Hc HA HA')
                   | exact (IHB i l2 l4 Hc HB HB')].
Qed.
Lemma Y_actmnf_inl {G Γ l l' A B k1 k2 k3 k4 C D C' D' a a'} : Y_tm G Γ a a' A ->
  Y_tmnf G Γ (tmInl k1 k2 C D a) (tmInl k3 k4 C' D' a') (tySum l l' A B).
Proof. intros IHa i k Hc Ht Ht'. apply actmnf_inl, (IHa i l Hc (inl_payload Hc Ht) (inl_payload Hc Ht')). Qed.
Lemma Y_actmnf_inr {G Γ l l' A B k1 k2 k3 k4 C D C' D' b b'} : Y_tm G Γ b b' B ->
  Y_tmnf G Γ (tmInr k1 k2 C D b) (tmInr k3 k4 C' D' b') (tySum l l' A B).
Proof. intros IHb i k Hc Ht Ht'. apply actmnf_inr, (IHb i l' Hc (inr_payload Hc Ht) (inr_payload Hc Ht')). Qed.

Lemma Y_actmne_case {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' ν ν' W} :
  leqv l1 l4 -> leqv l2 l5 -> leqv l3 l6 ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_ty G Γ B B' -> Y_ty G Γ B B' ->
  ac_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' -> Y_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' ->
  Y_tm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] -> Y_tm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] -> Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) (tmCase l4 l5 l6 A' B' M' c1' c2' ν') M[lsingle ν].
Proof.
  intros H14 H25 H36 DA IHA DB IHB DM IHM IHc1 IHc2 IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Hν) & _ & _).
  destruct (inv_case Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & Hc1' & Hc2' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W4 H14) as E14. pose proof (leqv_lequiv _ _ _ W2 W5 H25) as E25.
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E14)) as EA.
  pose proof (ac_ty_sound Hc DB HB (wft_lconv _ _ _ _ _ _ HB' E25)) as EB.
  destruct (case_right_left (M := M) (c1' := c1') (c2' := c2') (ν' := ν') Hc E14 E25 E36 HA HB HA' HB' EA EB HM')
    as [HM'3 Hbr].
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  destruct (Hbr HM EM Hc1' Hc2' Hν') as (EBA & EBB & Hc1'2 & Hc2'2 & _).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HS : [ G ; Γ ⊢[ i ] tySum l1 l2 A B @ lmax l1 l2 ]) by (apply wft_sum; [now apply compt_notV | ..]; assumption).
  assert (HctxS : [ G ⊢[ i ] Γ ,, tySum l1 l2 A B @ lmax l1 l2 ≅ Γ ,, tySum l4 l5 A' B' @ lmax l4 l5 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HS | apply eqty_sum; [now apply compt_notV | ..]; assumption
                       | apply lequiv_max; assumption]).
  assert (HctxA : [ G ⊢[ i ] Γ ,, A @ l1 ≅ Γ ,, A' @ l4 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact E14]).
  assert (HctxB : [ G ⊢[ i ] Γ ,, B @ l2 ≅ Γ ,, B' @ l5 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HB | exact EB | exact E25]).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W' & Xν).
  exists M'[lsingle ν'].
  eapply actmne_case; [exact (leqv_sym _ _ H14) | exact (leqv_sym _ _ H25) | exact (leqv_sym _ _ H36) | | | | | | exact Xν].
  - exact (IHA i l1 l4 Hc HA HA').
  - exact (IHB i l2 l5 Hc HB HB').
  - exact (cv_ty HG Hc (IHM i l3 l3 Hc HM HM'3) HctxS HM'3 HM).
  - exact (cv_tm HG Hc (IHc1 i l3 Hc Hc1 Hc1'2) HctxA Hc1'2 Hc1 (eqty_sym _ _ _ _ _ _ EBA)).
  - exact (cv_tm HG Hc (IHc2 i l3 Hc Hc2 Hc2'2) HctxB Hc2'2 Hc2 (eqty_sym _ _ _ _ _ _ EBB)).
Qed.

(** Well-founded trees (M13a). *)
Lemma Y_actnf_W {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> Y_ty G (Γ ,, A @ l1) B B' ->
  Y_tynf G Γ (tyW l1 l2 A B) (tyW l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA DB IHB i k k' Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_W HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_W HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  assert (Hctx : [ G ⊢[ i ] Γ ,, A @ l1 ≅ Γ ,, A' @ l3 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact E13]).
  apply actnf_W; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | exact (IHA i l1 l3 Hc HA HA') |].
  pose proof (IHB i l2 l4 Hc HB HB1) as X.
  exact (cv_ty (ctx_glob _ _ _ HΓ) Hc X Hctx HB1 HB).
Qed.

Lemma Y_actmnf_sup {G Γ l l' A B k1 k2 k3 k4 C D C' D' a a' f f'} :
  ac_tm G Γ a a' A -> Y_tm G Γ a a' A ->
  Y_tm G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) ->
  Y_tmnf G Γ (tmSup k1 k2 C D a f) (tmSup k3 k4 C' D' a' f') (tyW l l' A B).
Proof.
  intros Da IHa IHf i k Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (sup_parts Hc Ht) as (Wl & Wl' & HA & HB & Ha & Hf).
  destruct (sup_parts Hc Ht') as (_ & _ & _ & _ & Ha' & Hf').
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (fty_conv Hc Wl Wl' HA HB Ha' Ha (ac_tm_sound Hc Da Ha Ha')) as EF.
  assert (Hf'1 : [ G ; Γ ⊢[ i ] f' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ])
    by (eapply wf_conv; [exact Hf' | rewrite Hi; exact EF]).
  apply actmnf_sup; [exact (IHa i l Hc Ha Ha') |].
  exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHf i _ Hc Hf Hf'1) (eqc_refl _ _ _ HΓ) Hf'1 Hf
           (eqty_sym _ _ _ _ _ _ EF)).
Qed.

Lemma Y_actmne_elimW {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c c' ν ν' W} :
  leqv l1 l4 -> leqv l2 l5 -> leqv l3 l6 ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> Y_ty G (Γ ,, A @ l1) B B' ->
  ac_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' -> Y_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' ->
  Y_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
    c c' (wstepty l1 l2 A B M) ->
  Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmElimW l1 l2 l3 A B M c ν) (tmElimW l4 l5 l6 A' B' M' c' ν') M[lsingle ν].
Proof.
  intros H14 H25 H36 DA IHA DB IHB DM IHM IHc IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimW Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & HF' & HI' & Hc0' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W4 H14) as E14. pose proof (leqv_lequiv _ _ _ W2 W5 H25) as E25.
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E14)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA4 : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E14)]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EA4 (lequiv_sym _ _ _ E14) HΓA HB') E25) as HB'A.
  pose proof (ac_ty_sound Hc DB HB HB'A) as EB.
  assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
  assert (HL : lequiv (gL G) (lmax l4 l5) (lmax l1 l2)) by (apply lequiv_max; now apply lequiv_sym).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ]) by (apply eqty_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' ≅ tyW l1 l2 A B @ lmax l4 l5 ]).
  { eapply eqty_lconv; [apply eqty_sym, EW | exact HL]. }
  pose proof (ext_wf Hi HW WL) as HΓW.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' HL HΓW HM') E36) as HM'3.
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  pose proof (elimW_step_left Hc E14 E25 E36 HA HA' EA HB HB' EB HM HM' EM HF HI Hc0') as Hc0'2.
  destruct (W_tele_eq Hc E14 E25 E36 HA HA' EA HB HB' EB HM HM' EM) as (HctxT & _ & ES).
  assert (HctxA : [ G ⊢[ i ] Γ ,, A @ l1 ≅ Γ ,, A' @ l4 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact E14]).
  assert (HctxW : [ G ⊢[ i ] Γ ,, tyW l1 l2 A B @ lmax l1 l2 ≅ Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HW | exact EW | apply lequiv_max; assumption]).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W' & Xν).
  exists M'[lsingle ν'].
  eapply actmne_elimW; [exact (leqv_sym _ _ H14) | exact (leqv_sym _ _ H25) | exact (leqv_sym _ _ H36) | | | | | exact Xν].
  - exact (IHA i l1 l4 Hc HA HA').
  - exact (cv_ty HG Hc (IHB i l2 l2 Hc HB HB'A) HctxA HB'A HB).
  - exact (cv_ty HG Hc (IHM i l3 l3 Hc HM HM'3) HctxW HM'3 HM).
  - exact (cv_tm HG Hc (IHc i l3 Hc Hc0 Hc0'2) HctxT Hc0'2 Hc0 (eqty_sym _ _ _ _ _ _ ES)).
Qed.

Lemma Y_actmnf_code_id {G Γ l k k' s s' t t' u u'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> Y_tm G Γ s s' (tyU k) ->
  ac_tm G Γ t t' (tyEl k s) -> Y_tm G Γ t t' (tyEl k s) ->
  ac_tm G Γ u u' (tyEl k s) -> Y_tm G Γ u u' (tyEl k s) ->
  Y_tmnf G Γ (tmId k s t u) (tmId k' s' t' u') (tyU l).
Proof.
  intros Hk0 Ds IHs Dt IHt Du IHu i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (code_id_prem Hc Hx) as (W & Hs & Ht & Hu). destruct (code_id_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  destruct (code_El_conv Hc E Es) as (F & EEl).
  assert (EU : [ G ; Γ ⊢[ i ] tyU k' ≅ tyU k @ lsuc k ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | apply lequiv_sym, E]
                       | exact (lequiv_suc _ _ _ E)]. }
  apply actmnf_code_id; [exact (leqv_sym _ _ Hk0) | | |].
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs EU).
  - exact (cv_tm HG Hc (IHt i _ Hc Ht (F _ Ht')) (eqc_refl _ _ _ HΓ) (F _ Ht') Ht
             (eqty_sym _ _ _ _ _ _ EEl)).
  - exact (cv_tm HG Hc (IHu i _ Hc Hu (F _ Hu')) (eqc_refl _ _ _ HΓ) (F _ Hu') Hu
             (eqty_sym _ _ _ _ _ _ EEl)).
Qed.
Lemma Y_actmnf_code_seq {G Γ l k k' s s' t t' u u'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> Y_tm G Γ s s' (tyU k) ->
  ac_tm G Γ t t' (tyEl k s) -> Y_tm G Γ t t' (tyEl k s) ->
  ac_tm G Γ u u' (tyEl k s) -> Y_tm G Γ u u' (tyEl k s) ->
  Y_tmnf G Γ (tmSEq k s t u) (tmSEq k' s' t' u') (tyU l).
Proof.
  intros Hk0 Ds IHs Dt IHt Du IHu i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (code_seq_prem Hc Hx) as (W & Hs & Ht & Hu). destruct (code_seq_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  destruct (code_El_conv Hc E Es) as (F & EEl).
  assert (EU : [ G ; Γ ⊢[ i ] tyU k' ≅ tyU k @ lsuc k ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | apply lequiv_sym, E]
                       | exact (lequiv_suc _ _ _ E)]. }
  apply actmnf_code_seq; [exact (leqv_sym _ _ Hk0) | | |].
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs EU).
  - exact (cv_tm HG Hc (IHt i _ Hc Ht (F _ Ht')) (eqc_refl _ _ _ HΓ) (F _ Ht') Ht
             (eqty_sym _ _ _ _ _ _ EEl)).
  - exact (cv_tm HG Hc (IHu i _ Hc Hu (F _ Hu')) (eqc_refl _ _ _ HΓ) (F _ Hu') Hu
             (eqty_sym _ _ _ _ _ _ EEl)).
Qed.

Lemma Y_actnf_sempty {G Γ l l'} : leqv l l' -> Y_tynf G Γ (tySEmpty l) (tySEmpty l').
Proof. intros Hl; red; intros; apply actnf_sempty, leqv_sym, Hl. Qed.
Lemma Y_actmnf_seq_irr {G Γ l A a b w w'} : Y_tmnf G Γ w w' (tySEq l A a b).
Proof. red; intros; apply actmnf_seq_irr. Qed.
Lemma Y_actmnf_sempty_irr {G Γ l w w'} : Y_tmnf G Γ w w' (tySEmpty l).
Proof. red; intros; apply actmnf_sempty_irr. Qed.
Lemma Y_actmne_elimSEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ M M' -> Y_ty G Γ M M' -> whne ν -> whne ν' ->
  Y_ne G Γ (elimSEmpty l1 l2 M ν) (elimSEmpty l3 l4 M' ν') M.
Proof.
  intros H13 H24 DM IHM Hn Hn' i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimSEmpty Hi Hx) as ((_ & _ & _ & HM & _) & _ & _).
  destruct (inv_elimSEmpty Hi Hx') as ((_ & _ & _ & HM' & _) & _ & _).
  exists M'. apply actmne_elimSEmpty; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24)
                                     | exact (IHM i _ _ Hc HM HM') | exact Hn' | exact Hn].
Qed.

Theorem ac_sym_all :
  (forall G Γ T T', ac_ty G Γ T T' -> Y_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> Y_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> Y_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> Y_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> Y_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> Y_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> Y_ne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> Y_nee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> Y_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first
    [ solve [eapply Y_act_red; eassumption] | solve [eapply Y_actnf_nat] | solve [eapply Y_actnf_U; eassumption]
    | solve [eapply Y_actnf_pi; eassumption] | solve [eapply Y_actnf_ne; eassumption]
    | solve [eapply Y_actnf_CTyp; eassumption] | solve [eapply Y_actnf_CTrm; eassumption]
    | solve [eapply Y_actnf_upi; eassumption] | solve [eapply Y_actnf_cpi; eassumption]
    | solve [eapply Y_actnf_tpi; eassumption]
    | solve [eapply Y_actne_gvar; eassumption] | solve [eapply Y_actne_El; eassumption]
    | solve [eapply Y_acc_nil] | solve [eapply Y_acc_var] | solve [eapply Y_acc_ext; eassumption]
    | solve [eapply Y_actm_red; eassumption]
    | solve [eapply Y_actmnf_code_nat] | solve [eapply Y_actmnf_code_U; eassumption]
    | solve [eapply Y_actmnf_code_pi; eassumption] | solve [eapply Y_actmnf_zero]
    | solve [eapply Y_actmnf_succ; eassumption] | solve [eapply Y_actmnf_ne; eassumption]
    | solve [eapply Y_actmnf_eta; eassumption] | solve [eapply Y_actmnf_ueta; eassumption]
    | solve [eapply Y_actmnf_ceta; eassumption] | solve [eapply Y_actmnf_teta; eassumption]
    | solve [eapply Y_actmnf_boxT; eassumption] | solve [eapply Y_actmnf_boxt; eassumption]
    | solve [eapply Y_actmne_var; eassumption] | solve [eapply Y_actmne_gvar; eassumption]
    | solve [eapply Y_actmne_natrec; eassumption] | solve [eapply Y_actmne_app; eassumption]
    | solve [eapply Y_actmne_letboxT; eassumption] | solve [eapply Y_actmne_letboxt; eassumption]
    | solve [eapply Y_actmne_elimT; eassumption] | solve [eapply Y_actmne_elimT_gvar; eassumption]
    | solve [eapply Y_actmne_elimt; eassumption] | solve [eapply Y_actmne_elimt_glob; eassumption]
    | solve [eapply Y_actmne_uapp; eassumption] | solve [eapply Y_actmne_capp; eassumption]
    | solve [eapply Y_actmne_tapp; eassumption] | solve [eapply Y_actmnee_red; eassumption]
    | solve [eapply Y_acs_pt; eassumption]
    | solve [eapply Y_actnf_sig; eassumption] | solve [eapply Y_actmnf_code_sig; eassumption]
    | solve [eapply Y_actmnf_sig_eta; eassumption] | solve [eapply Y_actmne_fst; eassumption]
    | solve [eapply Y_actmne_snd; eassumption]
    | solve [eapply Y_actnf_unit; eassumption] | solve [eapply Y_actmnf_code_unit; eassumption]
    | solve [eapply Y_actmnf_unit_eta]
    | solve [eapply Y_actnf_seq; eassumption] | solve [eapply Y_actnf_sempty; eassumption]
    | solve [eapply Y_actmnf_seq_irr] | solve [eapply Y_actmnf_sempty_irr]
    | solve [eapply Y_actmne_elimSEmpty; eassumption]
    | solve [eapply Y_actnf_id; eassumption] | solve [eapply Y_actmnf_refl]
    | solve [eapply Y_actmne_J; eassumption] | solve [eapply Y_actmnf_code_id; eassumption]
    | solve [eapply Y_actmnf_code_seq; eassumption] | solve [eapply Y_actmnf_code_sempty; eassumption]
    | solve [eapply Y_actnf_empty; eassumption] | solve [eapply Y_actmne_elimEmpty; eassumption]
    | solve [eapply Y_actnf_sum; eassumption] | solve [eapply Y_actmnf_inl; eassumption]
    | solve [eapply Y_actmnf_inr; eassumption] | solve [eapply Y_actmne_case; eassumption]
    | solve [eapply Y_actnf_W; eassumption] | solve [eapply Y_actmnf_sup; eassumption]
    | solve [eapply Y_actmne_elimW; eassumption]
    | solve [eapply Y_actmnf_code_empty; eassumption] | solve [eapply Y_actmnf_code_sum; eassumption]
    | solve [eapply Y_actmnf_code_W; eassumption] ].
Qed.

(** ** Inversion of the algorithm on the left side's head *)

(** A value is not neutral. *)
Ltac kill_ne :=
  match goal with
  | H : ac_tmnee _ _ ?x _ _ |- _ =>
      let Hw := fresh in destruct (ac_tmnee_whne H) as [Hw _]; solve [inversion Hw]
  | H : ac_tmne _ _ ?x _ _ |- _ =>
      let Hw := fresh in destruct (ac_tmne_whne H) as [Hw _]; solve [inversion Hw]
  | H : ac_tyne _ _ ?x _ |- _ => solve [inversion H]
  | H : posty _ |- _ => solve [inversion H; match goal with Hn : whne_ty _ |- _ => inversion Hn end]
  end.

Ltac ainv H := inversion H; subst; try kill_ne; eauto 12.

Lemma ainv_ty {G Γ T X} : ac_ty G Γ T X -> exists W W', reds_ty T W /\ reds_ty X W' /\ whnf_ty W /\ whnf_ty W' /\
  ac_tynf G Γ W W'.
Proof. intros H; ainv H. Qed.
Lemma ainv_nat {G Γ X} : ac_tynf G Γ tyNat X -> X = tyNat.
Proof. intros H; ainv H. Qed.
Lemma ainv_U {G Γ l X} : ac_tynf G Γ (tyU l) X -> exists l', X = tyU l' /\ leqv l l'.
Proof. intros H; ainv H. Qed.
Lemma ainv_unit {G Γ l X} : ac_tynf G Γ (tyUnit l) X -> exists l', X = tyUnit l' /\ leqv l l'.
Proof. intros H; ainv H. Qed.
Lemma ainv_seq {G Γ l A a b X} : ac_tynf G Γ (tySEq l A a b) X ->
  exists l' A' a' b', X = tySEq l' A' a' b' /\ leqv l l' /\ ac_ty G Γ A A' /\
    ac_tm G Γ a a' A /\ ac_tm G Γ b b' A.
Proof. intros H; ainv H. Qed.
Lemma ainv_id {G Γ l A a b X} : ac_tynf G Γ (tyId l A a b) X ->
  exists l' A' a' b', X = tyId l' A' a' b' /\ leqv l l' /\ ac_ty G Γ A A' /\
    ac_tm G Γ a a' A /\ ac_tm G Γ b b' A.
Proof. intros H; ainv H. Qed.
Lemma ainv_refl {G Γ k C c X l A a b} : ac_tmnf G Γ (tmRefl k C c) X (tyId l A a b) ->
  exists k' C' c', X = tmRefl k' C' c'.
Proof. intros H; ainv H. Qed.
Lemma ainv_J {G Γ l1 l2 A a M c u ν X T} : ac_tmne G Γ (tmJ l1 l2 A a M c u ν) X T ->
  exists l3 l4 A' a' M' c' u' ν' W, X = tmJ l3 l4 A' a' M' c' u' ν' /\ leqv l1 l3 /\ leqv l2 l4 /\
    ac_ty G Γ A A' /\ ac_tm G Γ a a' A /\
    ac_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' /\
    ac_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] /\ ac_tm G Γ u u' A /\ ac_tmnee G Γ ν ν' W.
Proof. intros H; inversion H; subst; do 9 eexists; split; [reflexivity|]; repeat split; eassumption. Qed.
Lemma ainv_code_id {G Γ l k s t u X} : ac_tmnf G Γ (tmId k s t u) X (tyU l) ->
  exists k' s' t' u', X = tmId k' s' t' u' /\ leqv k k' /\ ac_tm G Γ s s' (tyU k) /\
    ac_tm G Γ t t' (tyEl k s) /\ ac_tm G Γ u u' (tyEl k s).
Proof. intros H; ainv H. Qed.
Lemma ainv_code_seq {G Γ l k s t u X} : ac_tmnf G Γ (tmSEq k s t u) X (tyU l) ->
  exists k' s' t' u', X = tmSEq k' s' t' u' /\ leqv k k' /\ ac_tm G Γ s s' (tyU k) /\
    ac_tm G Γ t t' (tyEl k s) /\ ac_tm G Γ u u' (tyEl k s).
Proof. intros H; ainv H. Qed.
Lemma ainv_sempty {G Γ l X} : ac_tynf G Γ (tySEmpty l) X -> exists l', X = tySEmpty l' /\ leqv l l'.
Proof. intros H; ainv H. Qed.
Lemma ainv_empty {G Γ l X} : ac_tynf G Γ (tyEmpty l) X -> exists l', X = tyEmpty l' /\ leqv l l'.
Proof. intros H; ainv H. Qed.
Lemma ainv_elimEmpty {G Γ l1 l2 M ν X T} : ac_tmne G Γ (elimEmpty l1 l2 M ν) X T ->
  exists l3 l4 M' ν' W, X = elimEmpty l3 l4 M' ν' /\ leqv l1 l3 /\ leqv l2 l4 /\
    ac_ty G (Γ ,, tyEmpty l2 @ l2) M M' /\ ac_tmnee G Γ ν ν' W.
Proof. intros H; ainv H. Qed.
Lemma ainv_sum {G Γ l1 l2 A B X} : ac_tynf G Γ (tySum l1 l2 A B) X ->
  exists l3 l4 A' B', X = tySum l3 l4 A' B' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_ty G Γ A A' /\ ac_ty G Γ B B'.
Proof. intros H; ainv H. Qed.
Lemma ainv_inl {G Γ k1 k2 C D a X l l' A B} : ac_tmnf G Γ (tmInl k1 k2 C D a) X (tySum l l' A B) ->
  exists k3 k4 C' D' a', X = tmInl k3 k4 C' D' a' /\ ac_tm G Γ a a' A.
Proof. intros H; ainv H. Qed.
Lemma ainv_inr {G Γ k1 k2 C D b X l l' A B} : ac_tmnf G Γ (tmInr k1 k2 C D b) X (tySum l l' A B) ->
  exists k3 k4 C' D' b', X = tmInr k3 k4 C' D' b' /\ ac_tm G Γ b b' B.
Proof. intros H; ainv H. Qed.
Lemma ainv_case {G Γ l1 l2 l3 A B M c1 c2 ν X T} : ac_tmne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) X T ->
  exists l4 l5 l6 A' B' M' c1' c2' ν' W, X = tmCase l4 l5 l6 A' B' M' c1' c2' ν' /\
    leqv l1 l4 /\ leqv l2 l5 /\ leqv l3 l6 /\ ac_ty G Γ A A' /\ ac_ty G Γ B B' /\
    ac_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' /\
    ac_tm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] /\ ac_tm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] /\ ac_tmnee G Γ ν ν' W.
Proof. intros H; inversion H; subst; do 10 eexists; split; [reflexivity|]; repeat split; eassumption. Qed.
Lemma ainv_W {G Γ l1 l2 A B X} : ac_tynf G Γ (tyW l1 l2 A B) X ->
  exists l3 l4 A' B', X = tyW l3 l4 A' B' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_ty G Γ A A' /\
    ac_ty G (Γ ,, A @ l1) B B'.
Proof. intros H; ainv H. Qed.
Lemma ainv_sup {G Γ k1 k2 C D a f X l l' A B} : ac_tmnf G Γ (tmSup k1 k2 C D a f) X (tyW l l' A B) ->
  exists k3 k4 C' D' a' f', X = tmSup k3 k4 C' D' a' f' /\ ac_tm G Γ a a' A /\
    ac_tm G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩).
Proof. intros H; ainv H. Qed.
Lemma ainv_elimW {G Γ l1 l2 l3 A B M c ν X T} : ac_tmne G Γ (tmElimW l1 l2 l3 A B M c ν) X T ->
  exists l4 l5 l6 A' B' M' c' ν' W, X = tmElimW l4 l5 l6 A' B' M' c' ν' /\
    leqv l1 l4 /\ leqv l2 l5 /\ leqv l3 l6 /\ ac_ty G Γ A A' /\ ac_ty G (Γ ,, A @ l1) B B' /\
    ac_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' /\
    ac_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
      c c' (wstepty l1 l2 A B M) /\ ac_tmnee G Γ ν ν' W.
Proof. intros H; inversion H; subst; do 9 eexists; split; [reflexivity|]; repeat split; eassumption. Qed.

Lemma ainv_elimSEmpty {G Γ l1 l2 M ν X T} : ac_tmne G Γ (elimSEmpty l1 l2 M ν) X T ->
  exists l3 l4 M' ν', X = elimSEmpty l3 l4 M' ν' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_ty G Γ M M' /\ whne ν'.
Proof. intros H; inversion H; subst; do 4 eexists; eauto. Qed.
Lemma ainv_pi {G Γ l1 l2 A B X} : ac_tynf G Γ (tyPi l1 l2 A B) X ->
  exists l3 l4 A' B', X = tyPi l3 l4 A' B' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_ty G Γ A A' /\
    ac_ty G (Γ ,, A @ l1) B B'.
Proof. intros H; ainv H. Qed.
Lemma ainv_CTyp {G Γ Δ l X} : ac_tynf G Γ (tyCTyp Δ l) X ->
  exists Δ' l', X = tyCTyp Δ' l' /\ ac_ctx G Δ Δ' /\ leqv l l'.
Proof. intros H; ainv H. Qed.
Lemma ainv_CTrm {G Γ Δ T l X} : ac_tynf G Γ (tyCTrm Δ T l) X ->
  exists Δ' T' l', X = tyCTrm Δ' T' l' /\ ac_ctx G Δ Δ' /\ ac_ty G Δ T T' /\ leqv l l'.
Proof. intros H; ainv H. Qed.
Lemma ainv_upi {G Γ n l T X} : ac_tynf G Γ (tyUPi n l T) X ->
  exists l' T', X = tyUPi n l' T' /\ leqv l l' /\ ac_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T'.
Proof. intros H; ainv H. Qed.
Lemma ainv_cpi {G Γ l T X} : ac_tynf G Γ (tyCPi l T) X ->
  exists l' T', X = tyCPi l' T' /\ leqv l l' /\ ac_ty (gext G gdCtx) Γ⟪S⟫ T T'.
Proof. intros H; ainv H. Qed.
Lemma ainv_tpi {G Γ Δ l1 l2 T X} : ac_tynf G Γ (tyTPi Δ l1 l2 T) X ->
  exists Δ' l3 l4 T', X = tyTPi Δ' l3 l4 T' /\ ac_ctx G Δ Δ' /\ leqv l1 l3 /\ leqv l2 l4 /\
    ac_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T'.
Proof. intros H; ainv H. Qed.
Lemma ainv_nfne {G Γ V X} : whne_ty V -> ac_tynf G Γ V X -> ac_tyne G Γ V X.
Proof. intros Hn H; inversion H; subst; auto; inversion Hn. Qed.
Lemma ainv_tygvar {G Γ U d X} : ac_tyne G Γ (tyGvar U d) X ->
  exists Δ i' l d', X = tyGvar U d' /\ in_gctx (gΨ G) U (gdTy Δ i' l) /\ ac_sub G Γ d d' Δ.
Proof. intros H; ainv H. Qed.
Lemma ainv_El {G Γ l ν X} : ac_tyne G Γ (tyEl l ν) X ->
  exists l' ν' W, X = tyEl l' ν' /\ leqv l l' /\ ac_tmnee G Γ ν ν' W.
Proof. intros H; ainv H. Qed.

Lemma ainv_cnil {G X} : ac_ctx G cnil X -> X = cnil.
Proof. intros H; ainv H. Qed.
Lemma ainv_cvar {G g X} : ac_ctx G (cvar g) X -> X = cvar g.
Proof. intros H; ainv H. Qed.
Lemma ainv_cext {G Γ A l X} : ac_ctx G (Γ ,, A @ l) X ->
  exists Γ' A' l', X = Γ' ,, A' @ l' /\ ac_ctx G Γ Γ' /\ ac_ty G Γ A A' /\ leqv l l'.
Proof. intros H; ainv H. Qed.

Lemma ainv_tm {G Γ t X T} : ac_tm G Γ t X T -> exists W w w', reds_ty T W /\ whnf_ty W /\
  reds t w /\ reds X w' /\ whnf w /\ whnf w' /\ ac_tmnf G Γ w w' W.
Proof. intros H; ainv H. Qed.

Lemma ainv_code_nat {G Γ l X} : ac_tmnf G Γ tmNat X (tyU l) -> X = tmNat.
Proof. intros H; ainv H. Qed.
Lemma ainv_code_unit {G Γ l k X} : ac_tmnf G Γ (tmUnit k) X (tyU l) -> exists k', X = tmUnit k' /\ leqv k k'.
Proof. intros H; ainv H. Qed.
Lemma ainv_code_empty {G Γ l k X} : ac_tmnf G Γ (tmEmpty k) X (tyU l) -> exists k', X = tmEmpty k' /\ leqv k k'.
Proof. intros H; ainv H. Qed.
Lemma ainv_code_sum {G Γ l l1 l2 s t X} : ac_tmnf G Γ (tmSum l1 l2 s t) X (tyU l) ->
  exists l3 l4 s' t', X = tmSum l3 l4 s' t' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_tm G Γ s s' (tyU l1) /\
    ac_tm G Γ t t' (tyU l2).
Proof. intros H; ainv H. Qed.
Lemma ainv_code_sempty {G Γ l k X} : ac_tmnf G Γ (tmSEmpty k) X (tyU l) -> exists k', X = tmSEmpty k' /\ leqv k k'.
Proof. intros H; ainv H. Qed.
Lemma ainv_code_U {G Γ l k X} : ac_tmnf G Γ (tmU k) X (tyU l) -> exists k', X = tmU k' /\ leqv k k'.
Proof. intros H; ainv H. Qed.
Lemma ainv_code_pi {G Γ l l1 l2 s t X} : ac_tmnf G Γ (tmPi l1 l2 s t) X (tyU l) ->
  exists l3 l4 s' t', X = tmPi l3 l4 s' t' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_tm G Γ s s' (tyU l1) /\
    ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2).
Proof. intros H; ainv H. Qed.
Lemma ainv_zero {G Γ X} : ac_tmnf G Γ zero X tyNat -> X = zero.
Proof. intros H; ainv H. Qed.
Lemma ainv_succ {G Γ t X} : ac_tmnf G Γ (succ t) X tyNat -> exists t', X = succ t' /\ ac_tm G Γ t t' tyNat.
Proof. intros H; ainv H. Qed.
Lemma ainv_nfne_tm {G Γ ν X W} : posty W -> whne ν -> ac_tmnf G Γ ν X W -> exists W', ac_tmnee G Γ ν X W'.
Proof. intros Hp Hn H; inversion H; subst; eauto; first [solve [inversion Hn] | solve [inversion Hp; match goal with Hv : whne_ty _ |- _ => inversion Hv end]]. Qed.
Lemma ainv_eta {G Γ l l' A B w X} : ac_tmnf G Γ w X (tyPi l l' A B) ->
  ac_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app X⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B.
Proof. intros H; ainv H. Qed.
Lemma ainv_ueta {G Γ n l T w X} : ac_tmnf G Γ w X (tyUPi n l T) ->
  ac_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp X⟨ush n⟩ᵤ (ubvars n)) T.
Proof. intros H; ainv H. Qed.
Lemma ainv_ceta {G Γ l T w X} : ac_tmnf G Γ w X (tyCPi l T) ->
  ac_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp X⟪S⟫ (cvar 0)) T.
Proof. intros H; ainv H. Qed.
Lemma ainv_teta {G Γ Δ l l' T w X} : ac_tmnf G Γ w X (tyTPi Δ l l' T) ->
  ac_tm (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp X⟪S⟫ (tyGvar 0 (lshift 0))) T.
Proof. intros H; ainv H. Qed.
Lemma ainv_boxT {G Γ Δ l T X} : ac_tmnf G Γ (boxT T) X (tyCTyp Δ l) -> exists T', X = boxT T' /\ ty_leq T T'.
Proof. intros H; ainv H. Qed.
Lemma ainv_boxt {G Γ Δ A l t X} : ac_tmnf G Γ (boxt t) X (tyCTrm Δ A l) -> exists t', X = boxt t' /\ tm_leq t t'.
Proof. intros H; ainv H. Qed.

Lemma ainv_nee {G Γ ν X W} : ac_tmnee G Γ ν X W -> exists T, ac_tmne G Γ ν X T /\ reds_ty T W /\ whnf_ty W.
Proof. intros H; ainv H. Qed.
Lemma ainv_sub {G Γ d X Θ} : ac_sub G Γ d X Θ ->
  forall n A k, in_ctx Θ n A k -> ac_tm G Γ (llk d n) (llk X n) A[d].
Proof. intros H; inversion H; subst; assumption. Qed.

Ltac kill_box := try match goal with
  | Hn : whne (boxT _) |- _ => solve [inversion Hn]
  | Hn : whne (boxt _) |- _ => solve [inversion Hn]
  end.

Lemma ainv_var {G Γ n X T} : ac_tmne G Γ (var n) X T -> X = var n.
Proof. intros H; ainv H. Qed.
Lemma ainv_gvar {G Γ u d X T} : ac_tmne G Γ (gvar u d) X T ->
  exists Δ i' T0 l d', X = gvar u d' /\ in_gctx (gΨ G) u (gdTm Δ i' T0 l) /\ ac_sub G Γ d d' Δ.
Proof. intros H; ainv H. Qed.
Lemma ainv_natrec {G Γ l M s z ν X T} : ac_tmne G Γ (natrec l M s z ν) X T ->
  exists l' M' s' z' ν' W, X = natrec l' M' s' z' ν' /\ leqv l l' /\ ac_ty G (Γ ,, tyNat @ lzero) M M' /\
    ac_tm G Γ s s' M[lsingle zero] /\ ac_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] /\
    ac_tmnee G Γ ν ν' W.
Proof. intros H; ainv H. Qed.
Lemma ainv_app {G Γ l1 l2 A B ν s X T} : ac_tmne G Γ (app ν l1 l2 A B s) X T ->
  exists l3 l4 A' B' ν' s' m m' A0 B0, X = app ν' l3 l4 A' B' s' /\
    ac_tmnee G Γ ν ν' (tyPi m m' A0 B0) /\ ac_tm G Γ s s' A0.
Proof. intros H; inversion H; subst; do 10 eexists; eauto. Qed.
Lemma ainv_letboxT {G Γ l1 l2 Δ M t1 ν X T} : ac_tmne G Γ (letboxT l1 l2 Δ M t1 ν) X T ->
  exists l3 l4 Δ' M' t2 ν' W, X = letboxT l3 l4 Δ' M' t2 ν' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_ctx G Δ Δ' /\
    ac_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' /\
    ac_tm (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) /\
    ac_tmnee G Γ ν ν' W.
Proof. intros H; inversion H; subst; do 7 eexists; eauto 10. Qed.
Lemma ainv_letboxt {G Γ l1 l2 Δ T M t1 ν X T0} : ac_tmne G Γ (letboxt l1 l2 Δ T M t1 ν) X T0 ->
  exists l3 l4 Δ' T' M' t2 ν' W, X = letboxt l3 l4 Δ' T' M' t2 ν' /\ leqv l1 l3 /\ leqv l2 l4 /\
    ac_ctx G Δ Δ' /\ ac_ty G Δ T T' /\ ac_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' /\
    ac_tm (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) /\
    ac_tmnee G Γ ν ν' W.
Proof. intros H; inversion H; subst; do 8 eexists; eauto 12. Qed.

Lemma ainv_elimT {G Γ l1 l2 rb l Δ ν X T} : whne ν -> ac_tmne G Γ (elimT l1 l2 rb l Δ ν) X T ->
  exists MT Mt bs l1' l2' MT' Mt' bs' l' Δ' ν' W, rb = mkrb MT Mt bs /\
    X = elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν' /\ leqv l1 l1' /\ leqv l2 l2' /\ leqv l l' /\
    ac_ctx G Δ Δ' /\ ac_ty (recGT G) (recΓT Γ) MT MT' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
    (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) /\
    ac_tmnee G Γ ν ν' W.
Proof. intros Hn H; inversion H; subst; kill_box; do 12 eexists; eauto 20. Qed.
Lemma ainv_elimT_gvar {G Γ l1 l2 rb l Δ U d X T} : ac_tmne G Γ (elimT l1 l2 rb l Δ (boxT (tyGvar U d))) X T ->
  exists MT Mt bs l1' l2' MT' Mt' bs' l' Δ' d', rb = mkrb MT Mt bs /\
    X = elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' (boxT (tyGvar U d')) /\ leqv l1 l1' /\ leqv l2 l2' /\
    leqv l l' /\ ac_ctx G Δ Δ' /\ ac_ty (recGT G) (recΓT Γ) MT MT' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
    (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) /\
    lsub_leq d d'.
Proof. intros H; inversion H; subst; try kill_ne; do 11 eexists; eauto 20. Qed.
Lemma ainv_elimt {G Γ l1 l2 rb l Δ A ν X T} : whne ν -> ac_tmne G Γ (elimt l1 l2 rb l Δ A ν) X T ->
  exists MT Mt bs l1' l2' MT' Mt' bs' l' Δ' A' ν' W, rb = mkrb MT Mt bs /\
    X = elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' A' ν' /\ leqv l1 l1' /\ leqv l2 l2' /\ leqv l l' /\
    ac_ctx G Δ Δ' /\ ac_ty G Δ A A' /\ ac_ty (recGT G) (recΓT Γ) MT MT' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
    (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) /\
    ac_tmnee G Γ ν ν' W.
Proof. intros Hn H; inversion H; subst; kill_box; do 13 eexists; eauto 20. Qed.
Lemma ainv_elimt_glob {G Γ l1 l2 rb l Δ A c X T} : boxed_global c ->
  ac_tmne G Γ (elimt l1 l2 rb l Δ A (boxt c)) X T ->
  exists MT Mt bs l1' l2' MT' Mt' bs' l' Δ' A' c', rb = mkrb MT Mt bs /\
    X = elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' A' (boxt c') /\ leqv l1 l1' /\ leqv l2 l2' /\
    leqv l l' /\ ac_ctx G Δ Δ' /\ ac_ty G Δ A A' /\ ac_ty (recGT G) (recΓT Γ) MT MT' /\
    ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
    (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) /\
    tm_leq c c'.
Proof. intros Hg H; inversion H; subst; try kill_ne; do 12 eexists; eauto 20. Qed.

Lemma ainv_uapp {G Γ ν ls X T} : ac_tmne G Γ (uapp ν ls) X T ->
  exists n l T0 ν' ls', X = uapp ν' ls' /\ ac_tmnee G Γ ν ν' (tyUPi n l T0) /\ length ls = n /\
    Forall2 leqv ls ls'.
Proof. intros H; ainv H. Qed.
Lemma ainv_capp {G Γ ν Δ X T} : ac_tmne G Γ (capp ν Δ) X T ->
  exists l T0 ν' Δ', X = capp ν' Δ' /\ ac_tmnee G Γ ν ν' (tyCPi l T0) /\ ac_ctx G Δ Δ'.
Proof. intros H; ainv H. Qed.
Lemma ainv_tapp {G Γ ν A X T} : ac_tmne G Γ (tapp ν A) X T ->
  exists Δ l l' T0 ν' A', X = tapp ν' A' /\ ac_tmnee G Γ ν ν' (tyTPi Δ l l' T0) /\ ac_ty G Δ A A'.
Proof. intros H; ainv H. Qed.

(** Dependent pairs (M8). *)
Lemma ainv_sig {G Γ l1 l2 A B X} : ac_tynf G Γ (tySig l1 l2 A B) X ->
  exists l3 l4 A' B', X = tySig l3 l4 A' B' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_ty G Γ A A' /\
    ac_ty G (Γ ,, A @ l1) B B'.
Proof. intros H; ainv H. Qed.
Lemma ainv_code_sig {G Γ l l1 l2 s t X} : ac_tmnf G Γ (tmSig l1 l2 s t) X (tyU l) ->
  exists l3 l4 s' t', X = tmSig l3 l4 s' t' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_tm G Γ s s' (tyU l1) /\
    ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2).
Proof. intros H; ainv H. Qed.
Lemma ainv_code_W {G Γ l l1 l2 s t X} : ac_tmnf G Γ (tmW l1 l2 s t) X (tyU l) ->
  exists l3 l4 s' t', X = tmW l3 l4 s' t' /\ leqv l1 l3 /\ leqv l2 l4 /\ ac_tm G Γ s s' (tyU l1) /\
    ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2).
Proof. intros H; ainv H. Qed.
Lemma ainv_sig_eta {G Γ l l' A B w X} : ac_tmnf G Γ w X (tySig l l' A B) ->
  ac_tm G Γ (tmFst l l' A B w) (tmFst l l' A B X) A /\
  ac_tm G Γ (tmSnd l l' A B w) (tmSnd l l' A B X) B[lsingle (tmFst l l' A B w)].
Proof. intros H; ainv H. Qed.
Lemma ainv_fst {G Γ l1 l2 A B ν X T} : ac_tmne G Γ (tmFst l1 l2 A B ν) X T ->
  exists l3 l4 A' B' ν' m m' A0 B0, X = tmFst l3 l4 A' B' ν' /\ ac_tmnee G Γ ν ν' (tySig m m' A0 B0).
Proof. intros H; inversion H; subst; do 9 eexists; eauto. Qed.
Lemma ainv_snd {G Γ l1 l2 A B ν X T} : ac_tmne G Γ (tmSnd l1 l2 A B ν) X T ->
  exists l3 l4 A' B' ν' m m' A0 B0, X = tmSnd l3 l4 A' B' ν' /\ ac_tmnee G Γ ν ν' (tySig m m' A0 B0).
Proof. intros H; inversion H; subst; do 9 eexists; eauto. Qed.


(** ** Transitivity: the statements

    Induction on the first derivation, inversion of the second on the
    middle side's head. The second derivation compares the middle side's
    binders; the conversion lemma moves it to the left side's. *)

Definition T_ty G Γ T T' : Prop := forall T'' i k k' k'', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> [ G ; Γ ⊢[ i ] T'' @ k'' ] ->
  ac_ty G Γ T' T'' -> ac_ty G Γ T T''.
Definition T_tynf G Γ T T' : Prop := forall T'' i k k' k'', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> [ G ; Γ ⊢[ i ] T'' @ k'' ] ->
  ac_tynf G Γ T' T'' -> ac_tynf G Γ T T''.
Definition T_tyne G Γ T T' : Prop := forall T'' i k k' k'', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> [ G ; Γ ⊢[ i ] T'' @ k'' ] ->
  ac_tyne G Γ T' T'' -> ac_tyne G Γ T T''.
Definition T_ctx G Δ Δ' : Prop := forall Δ'',
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ; Δ'' ⊢[ lD ] ] -> ac_ctx G Δ' Δ'' -> ac_ctx G Δ Δ''.
Definition T_tm G Γ t t' T : Prop := forall t'' i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G ; Γ ⊢[ i ] t'' : T @ k ] ->
  ac_tm G Γ t' t'' T -> ac_tm G Γ t t'' T.
Definition T_tmnf G Γ t t' T : Prop := forall t'' i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G ; Γ ⊢[ i ] t'' : T @ k ] ->
  ac_tmnf G Γ t' t'' T -> ac_tmnf G Γ t t'' T.
Definition T_ne G Γ ν ν' T : Prop := forall ν'' T' i k k' k'' A A' A'', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> [ G ; Γ ⊢[ i ] ν'' : A'' @ k'' ] ->
  ac_tmne G Γ ν' ν'' T' -> ac_tmne G Γ ν ν'' T.
Definition T_nee G Γ ν ν' W : Prop := forall ν'' W' i k k' k'' A A' A'', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> [ G ; Γ ⊢[ i ] ν'' : A'' @ k'' ] ->
  ac_tmnee G Γ ν' ν'' W' -> ac_tmnee G Γ ν ν'' W.
Definition T_sub G Γ d d' Θ : Prop := forall d'' i, compt i -> [ G ; Θ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] d : Θ ] -> [ G ; Γ ⊢[ i ] d' : Θ ] -> [ G ; Γ ⊢[ i ] d'' : Θ ] ->
  ac_sub G Γ d' d'' Θ -> ac_sub G Γ d d'' Θ.

Lemma mvD {G Δ Δ' T l} : [ G ⊢[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ' ⊢[ lD ] T @ l ].
Proof. intros Hc HT. exact (decl_ty_ctxconv_D Hc HT (lequiv_refl _ _ (lwfD_ty HT))). Qed.

(** ** Types *)

Lemma T_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  T_tynf G Γ W W' -> T_ty G Γ T T'.
Proof.
  intros Hr Hr' Hw Hw' IH T'' i k k' k'' Hc HT HT' HT'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_ty D2) as (W2 & W3 & Hr2 & Hr3 & Hw2 & Hw3 & D2').
  rewrite <- (reds_ty_whnf_det _ _ _ Hr' Hr2 Hw' Hw2) in D2'.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT Hr Hw)) as HW.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT' Hr' Hw')) as HW'.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT'' Hr3 Hw3)) as HW3.
  eapply act_red; [exact Hr | exact Hr3 | exact Hw | exact Hw3 | exact (IH W3 i k k' k'' Hc HW HW' HW3 D2')].
Qed.

Lemma T_actnf_nat {G Γ} : T_tynf G Γ tyNat tyNat.
Proof. red; intros * _ _ _ _ D2. rewrite (ainv_nat D2). apply actnf_nat. Qed.
Lemma T_actnf_U {G Γ l l'} : leqv l l' -> T_tynf G Γ (tyU l) (tyU l').
Proof.
  intros Hl; red; intros * _ _ _ _ D2. destruct (ainv_U D2) as (l'' & -> & Hl2).
  apply actnf_U, (leqv_trans _ _ _ Hl Hl2).
Qed.

Lemma T_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> T_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> T_ty G (Γ ,, A @ l1) B B' ->
  T_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA DB IHB T'' i k k' k'' Hc HT HT' HT'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_pi D2) as (l5 & l6 & A'' & B'' & -> & H35 & H46 & DA2 & DB2).
  destruct (inv_ty_pi HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_pi HT') as ((_ & W3 & W4 & HA' & HB') & _).
  destruct (inv_ty_pi HT'') as ((_ & W5 & W6 & HA'' & HB'') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ac_ty_sound Hc DA2 HA' (wft_lconv _ _ _ _ _ _ HA'' E35)) as EA2.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (HΓA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA' | exact W3]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  assert (EA2' : [ G ; Γ ⊢[ i ] A'' ≅ A' @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA2) | exact (lequiv_sym _ _ _ E35)]).
  pose proof (lequiv_trans _ _ _ _ E13 E35) as E15.
  assert (EA'' : [ G ; Γ ⊢[ i ] A'' ≅ A @ l5 ]).
  { eapply eqty_lconv; [| exact (lequiv_sym _ _ _ E15)]. apply eqty_sym.
    eapply eqty_trans; [exact EA | exact (eqty_lconv _ _ _ _ _ _ _ EA2 E13)]. }
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  pose proof (stab_ty Hi EA2' (lequiv_sym _ _ _ E35) HΓA' HB'') as HB2'.
  pose proof (stab_ty Hi EA'' (lequiv_sym _ _ _ E15) HΓA HB'') as HB2.
  assert (Hctx : [ G ⊢[ i ] Γ ,, A' @ l3 ≅ Γ ,, A @ l1 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA' | exact EA' | exact (lequiv_sym _ _ _ E13)]).
  pose proof (cv_ty HG Hc DB2 Hctx HB' HB2') as DB2'.
  apply actnf_pi; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46)
                  | exact (IHA A'' i _ _ _ Hc HA HA' HA'' DA2) | exact (IHB B'' i _ _ _ Hc HB HB1 HB2 DB2')].
Qed.

Lemma T_actnf_ne {G Γ V V'} : ac_tyne G Γ V V' -> T_tyne G Γ V V' -> T_tynf G Γ V V'.
Proof.
  intros D IH T'' i k k' k'' Hc HT HT' HT'' D2. apply actnf_ne.
  exact (IH T'' i k k' k'' Hc HT HT' HT'' (ainv_nfne (proj2 (ac_tyne_whne D)) D2)).
Qed.

Lemma T_actnf_CTyp {G Γ Δ Δ' l l'} : T_ctx G Δ Δ' -> leqv l l' -> T_tynf G Γ (tyCTyp Δ l) (tyCTyp Δ' l').
Proof.
  intros IH Hl T'' i k k' k'' Hc HT HT' HT'' D2.
  destruct (ainv_CTyp D2) as (Δ'' & l'' & -> & Dc2 & Hl2).
  destruct (inv_ty_CTyp HT) as ((_ & _ & HΔ & _) & _). destruct (inv_ty_CTyp HT') as ((_ & _ & HΔ' & _) & _).
  destruct (inv_ty_CTyp HT'') as ((_ & _ & HΔ'' & _) & _).
  apply actnf_CTyp; [exact (IH Δ'' HΔ HΔ' HΔ'' Dc2) | exact (leqv_trans _ _ _ Hl Hl2)].
Qed.

Lemma T_actnf_CTrm {G Γ Δ Δ' T T' l l'} : ac_ctx G Δ Δ' -> T_ctx G Δ Δ' -> T_ty G Δ T T' -> leqv l l' ->
  T_tynf G Γ (tyCTrm Δ T l) (tyCTrm Δ' T' l').
Proof.
  intros Dc IHc IHT Hl X'' i k k' k'' Hc HX HX' HX'' D2.
  destruct (ainv_CTrm D2) as (Δ'' & T'' & l'' & -> & Dc2 & DT2 & Hl2).
  destruct (inv_ty_CTrm HX) as ((_ & _ & HΔ & HT & _) & _).
  destruct (inv_ty_CTrm HX') as ((_ & _ & HΔ' & HT' & _) & _).
  destruct (inv_ty_CTrm HX'') as ((_ & _ & HΔ'' & HT'' & _) & _).
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec. pose proof (ac_ctx_sound' Dc2 HΔ' HΔ'') as Ec2.
  pose proof (eqctx_trans_D Ec Ec2) as Ec02.
  pose proof (cv_ty (ctx_glob _ _ _ HΔ) compt_D DT2 (eqctx_sym_D Ec) HT' (mvD (eqctx_sym_D Ec2) HT'')) as DT2'.
  apply actnf_CTrm; [exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2) | | exact (leqv_trans _ _ _ Hl Hl2)].
  exact (IHT T'' lD _ _ _ compt_D HT (mvD (eqctx_sym_D Ec) HT') (mvD (eqctx_sym_D Ec02) HT'') DT2').
Qed.

Lemma T_actnf_upi {G Γ n l l' T T'} : leqv l l' -> T_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  T_tynf G Γ (tyUPi n l T) (tyUPi n l' T').
Proof.
  intros Hl IH X'' i k k' k'' Hc HX HX' HX'' D2.
  destruct (ainv_upi D2) as (l'' & T'' & -> & Hl2 & DT2).
  destruct (inv_ty_upi HX) as ((-> & _ & _ & _ & HT) & _). destruct (inv_ty_upi HX') as ((_ & _ & _ & _ & HT') & _).
  destruct (inv_ty_upi HX'') as ((_ & _ & _ & _ & HT'') & _).
  apply actnf_upi; [exact (leqv_trans _ _ _ Hl Hl2) | exact (IH T'' lM _ _ _ compt_M HT HT' HT'' DT2)].
Qed.

Lemma T_actnf_cpi {G Γ l l' T T'} : leqv l l' -> T_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  T_tynf G Γ (tyCPi l T) (tyCPi l' T').
Proof.
  intros Hl IH X'' i k k' k'' Hc HX HX' HX'' D2.
  destruct (ainv_cpi D2) as (l'' & T'' & -> & Hl2 & DT2).
  destruct (inv_ty_cpi HX) as ((-> & _ & _ & HT) & _). destruct (inv_ty_cpi HX') as ((_ & _ & _ & HT') & _).
  destruct (inv_ty_cpi HX'') as ((_ & _ & _ & HT'') & _).
  apply actnf_cpi; [exact (leqv_trans _ _ _ Hl Hl2) | exact (IH T'' lM _ _ _ compt_M HT HT' HT'' DT2)].
Qed.

(** Moving a judgment between two equal type bindings. *)
Lemma GEq_bind {G Δ Δ' l l'} : [ ⊢ G ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] -> lequiv (gL G) l l' ->
  GEq (gext G (gdTy Δ lD l)) (gext G (gdTy Δ' lD l')).
Proof.
  intros HG Ec El. apply (GEq_ext (GEq_refl _ HG)).
  - apply (wfg_gext HG); [split; [exact (eqctx_wf_l (i := lD) eq_refl Ec) | exact (lequiv_wf_l _ _ _ El)]
                         | right; reflexivity].
  - apply (wfg_gext HG); [split; [exact (eqctx_wf_r (i := lD) eq_refl Ec) | exact (lequiv_wf_r _ _ _ El)]
                         | right; reflexivity].
  - exact (conj eq_refl (conj (or_intror eq_refl) (conj El Ec))).
Qed.

Lemma T_actnf_tpi {G Γ Δ Δ' l1 l2 l3 l4 T T'} : ac_ctx G Δ Δ' -> T_ctx G Δ Δ' -> leqv l1 l3 -> leqv l2 l4 ->
  T_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T' -> T_tynf G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ' l3 l4 T').
Proof.
  intros Dc IHc H13 H24 IH X'' i k k' k'' Hc HX HX' HX'' D2.
  destruct (ainv_tpi D2) as (Δ'' & l5 & l6 & T'' & -> & Dc2 & H35 & H46 & DT2).
  destruct (inv_ty_tpi HX) as ((-> & HΓ & HΔ & W1 & W2 & HT) & _).
  destruct (inv_ty_tpi HX') as ((_ & _ & HΔ' & W3 & W4 & HT') & _).
  destruct (inv_ty_tpi HX'') as ((_ & _ & HΔ'' & W5 & W6 & HT'') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec. pose proof (ac_ctx_sound' Dc2 HΔ' HΔ'') as Ec2.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (GEq_bind HG (eqctx_sym_D Ec) (lequiv_sym _ _ _ E13)) as HE10.
  pose proof (GEq_bind HG (eqctx_sym_D Ec2) (lequiv_sym _ _ _ E35)) as HE21.
  pose proof (GEq_bind HG (eqctx_sym_D (eqctx_trans_D Ec Ec2))
                (lequiv_sym _ _ _ (lequiv_trans _ _ _ _ E13 E35))) as HE20.
  pose proof (proj1 ac_conv_all _ _ _ _ DT2 lM _ _ _ _ compt_M HE10
                (eqc_refl _ _ _ (gconv_ctx HE10 compt_M (ctx_of_wf_ty (i := lM) eq_refl HT'))) HT'
                (gconv_ty HE21 HT'')) as DT2'.
  apply actnf_tpi; [exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2) | exact (leqv_trans _ _ _ H13 H35)
                   | exact (leqv_trans _ _ _ H24 H46) |].
  exact (IH T'' lM _ _ _ compt_M HT (gconv_ty HE10 HT') (gconv_ty HE20 HT'') DT2').
Qed.

Lemma T_actne_gvar {G Γ U Δ i' l d d'} : in_gctx (gΨ G) U (gdTy Δ i' l) -> T_sub G Γ d d' Δ ->
  T_tyne G Γ (tyGvar U d) (tyGvar U d').
Proof.
  intros Hin IH X'' i k k' k'' Hc HX HX' HX'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_tygvar D2) as (Δ2 & i2 & l2 & d'' & -> & Hin2 & Ds2).
  pose proof (in_gctx_det Hin Hin2) as E. injection E as <- <- <-.
  destruct (inv_ty_gvar HX) as (Δ0 & i0 & l0 & (Hv & HΓ & Hin0 & Hle & Ht & Hn & He) & _).
  destruct (inv_ty_gvar HX') as (Δ1 & i1 & l1 & (_ & _ & Hin1 & _ & Ht' & Hn' & He') & _).
  destruct (inv_ty_gvar HX'') as (Δ3 & i3 & l3 & (_ & _ & Hin3 & _ & Ht'' & Hn'' & He'') & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <-.
  pose proof (in_gctx_det Hin Hin3) as E3. injection E3 as <- <- <-.
  rewrite Hi in HΓ.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (HΔ & _).
  eapply actne_gvar; [exact Hin |].
  exact (IH d'' i Hc (lift_ctx HΔ (lle_D_compt _ Hc)) (lsub_wf_prem Hi HΓ Ht Hn He)
           (lsub_wf_prem Hi HΓ Ht' Hn' He') (lsub_wf_prem Hi HΓ Ht'' Hn'' He'') Ds2).
Qed.

Lemma T_actne_El {G Γ l l' ν ν' W} : leqv l l' -> T_nee G Γ ν ν' W -> T_tyne G Γ (tyEl l ν) (tyEl l' ν').
Proof.
  intros Hl IH X'' i k k' k'' Hc HX HX' HX'' D2.
  destruct (ainv_El D2) as (l'' & ν'' & W2 & -> & Hl2 & Dν2).
  destruct (inv_ty_El HX) as ((_ & _ & Hν) & _). destruct (inv_ty_El HX') as ((_ & _ & Hν') & _).
  destruct (inv_ty_El HX'') as ((_ & _ & Hν'') & _).
  eapply actne_El; [exact (leqv_trans _ _ _ Hl Hl2) | exact (IH ν'' W2 i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2)].
Qed.

(** ** Local contexts *)

Lemma T_acc_nil {G} : T_ctx G cnil cnil.
Proof. red; intros * _ _ _ D2. rewrite (ainv_cnil D2). apply acc_nil. Qed.
Lemma T_acc_var {G g} : T_ctx G (cvar g) (cvar g).
Proof. red; intros * _ _ _ D2. rewrite (ainv_cvar D2). apply acc_var. Qed.

Lemma T_acc_ext {G Γ Γ' A A' l l'} : ac_ctx G Γ Γ' -> T_ctx G Γ Γ' -> T_ty G Γ A A' -> leqv l l' ->
  T_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof.
  intros Dc IHc IHA Hl X'' H H' H'' D2.
  destruct (ainv_cext D2) as (Γ'' & A'' & l'' & -> & Dc2 & DA2 & Hl2).
  destruct (wfc_ext_inv H) as (HΓ & HA & _). destruct (wfc_ext_inv H') as (HΓ' & HA' & _).
  destruct (wfc_ext_inv H'') as (HΓ'' & HA'' & _).
  pose proof (ac_ctx_sound' Dc HΓ HΓ') as Ec. pose proof (ac_ctx_sound' Dc2 HΓ' HΓ'') as Ec2.
  pose proof (cv_ty (ctx_glob _ _ _ HΓ) compt_D DA2 (eqctx_sym_D Ec) HA' (mvD (eqctx_sym_D Ec2) HA'')) as DA2'.
  apply acc_ext; [exact (IHc Γ'' HΓ HΓ' HΓ'' Dc2) | | exact (leqv_trans _ _ _ Hl Hl2)].
  exact (IHA A'' lD _ _ _ compt_D HA (mvD (eqctx_sym_D Ec) HA') (mvD (eqctx_sym_D (eqctx_trans_D Ec Ec2)) HA'') DA2').
Qed.

(** ** Terms *)

Lemma T_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> T_tmnf G Γ w w' W -> T_tm G Γ t t' T.
Proof.
  intros HrT HwT Hr Hr' Hw Hw' IH t'' i k Hc Ht Ht' Ht'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_tm D2) as (W2 & w2 & w3 & HrT2 & HwT2 & Hr2 & Hr3 & Hw2 & Hw3 & D2').
  rewrite <- (reds_ty_whnf_det _ _ _ HrT HrT2 HwT HwT2) in D2'.
  rewrite <- (reds_whnf_det _ _ _ Hr' Hr2 Hw' Hw2) in D2'.
  pose proof (red_ty_sound Hc (wf_tm_ty Hi Ht) HrT HwT) as ET.
  assert (EW : [ G ; Γ ⊢[ typeof i ] W ≅ T @ k ]) by (rewrite Hi; exact (eqty_sym _ _ _ _ _ _ ET)).
  pose proof (eqtm_wf_r Hi (red_tm_sound Hc Ht Hr Hw)) as Hw0.
  pose proof (eqtm_wf_r Hi (red_tm_sound Hc Ht' Hr' Hw')) as Hw0'.
  pose proof (eqtm_wf_r Hi (red_tm_sound Hc Ht'' Hr3 Hw3)) as Hw0''.
  eapply actm_red; [exact HrT | exact HwT | exact Hr | exact Hr3 | exact Hw | exact Hw3 |].
  exact (IH w3 i k Hc (wf_conv _ _ _ _ _ _ _ Hw0 EW) (wf_conv _ _ _ _ _ _ _ Hw0' EW)
           (wf_conv _ _ _ _ _ _ _ Hw0'' EW) D2').
Qed.

Lemma T_actmnf_code_nat {G Γ l} : T_tmnf G Γ tmNat tmNat (tyU l).
Proof. red; intros * _ _ _ _ D2. rewrite (ainv_code_nat D2). apply actmnf_code_nat. Qed.
Lemma T_actmnf_code_U {G Γ l k k'} : leqv k k' -> T_tmnf G Γ (tmU k) (tmU k') (tyU l).
Proof.
  intros Hl; red; intros * _ _ _ _ D2. destruct (ainv_code_U D2) as (k'' & -> & Hl2).
  apply actmnf_code_U, (leqv_trans _ _ _ Hl Hl2).
Qed.

(** The code of [Π] at a universe: the premises of a typed [tmPi l1 l2 s t]. *)
Lemma code_pi_prem {G i Γ l l1 l2 s t k} : compt i -> [ G ; Γ ⊢[ i ] tmPi l1 l2 s t : tyU l @ k ] ->
  i <> lV /\ lwf (gL G) l1 /\ lwf (gL G) l2 /\ [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] /\
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t : tyU l2 @ lsuc l2 ].
Proof. intros Hc H. exact (proj1 (inv_code_pi (compt_typeof_self _ Hc) H)). Qed.

Lemma T_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> T_tm G Γ s s' (tyU l1) ->
  ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) -> T_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  T_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs Dt IHt x'' i k Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_code_pi D2) as (l5 & l6 & s'' & t'' & -> & H35 & H46 & Ds2 & Dt2).
  destruct (code_pi_prem Hc Hx) as (Hv & W1 & W2 & Hs & Ht).
  destruct (code_pi_prem Hc Hx') as (_ & W3 & W4 & Hs' & Ht').
  destruct (code_pi_prem Hc Hx'') as (_ & W5 & W6 & Hs'' & Ht'').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35. pose proof (leqv_lequiv _ _ _ W4 W6 H46) as E46.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  (* the universes of the codes' domains *)
  assert (EU13 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (EU35 : [ G ; Γ ⊢[ i ] tyU l3 ≅ tyU l5 @ lsuc l3 ]) by (apply eqty_U; assumption).
  assert (EU15 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l5 @ lsuc l1 ])
    by (apply eqty_U; [exact Hv | exact HΓt | exact (lequiv_trans _ _ _ _ E13 E35)]).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU13]. }
  assert (Hs2 : [ G ; Γ ⊢[ i ] s'' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs'' | exact (lequiv_suc _ _ _ (lequiv_trans _ _ _ _ E13 E35))]
                    | rewrite Hi; exact EU15]. }
  assert (Hs2' : [ G ; Γ ⊢[ i ] s'' : tyU l3 @ lsuc l3 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs'' | exact (lequiv_suc _ _ _ E35)] | rewrite Hi; exact EU35]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  pose proof (ac_tm_sound Hc Ds2 Hs' Hs2') as Es2.
  (* the second's domain, at the first's universe *)
  pose proof (cv_tm HG Hc Ds2 (eqc_refl _ _ _ HΓ) Hs' Hs2'
                (eqty_lconv _ _ _ _ _ _ _ EU13 (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13)))) as Ds2'.
  (* the bodies' contexts *)
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' @ l3 ]) by (apply wft_El; assumption).
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; [exact Hv | exact E13 | exact Es]).
  assert (Es2u : [ G ; Γ ⊢[ i ] s' ≅ s'' : tyU l3 @ lsuc l3 ]) by exact Es2.
  assert (EEl2 : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l5 s'' @ l3 ]) by (apply eqty_El; [exact Hv | exact E35 | exact Es2u]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E13)]).
  assert (EEl'' : [ G ; Γ ⊢[ i ] tyEl l5 s'' ≅ tyEl l1 s @ l5 ]).
  { eapply eqty_lconv; [| exact (lequiv_sym _ _ _ (lequiv_trans _ _ _ _ E13 E35))]. apply eqty_sym.
    eapply eqty_trans; [exact EEl | exact (eqty_lconv _ _ _ _ _ _ _ EEl2 E13)]. }
  assert (EEl2' : [ G ; Γ ⊢[ i ] tyEl l5 s'' ≅ tyEl l3 s' @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl2) | exact (lequiv_sym _ _ _ E35)]).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  assert (HΓ3 : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl' | exact W3]).
  (* the bodies at the first's universe, in the first's context *)
  assert (Ht1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl' (lequiv_sym _ _ _ E13) HΓ1 Ht') |
                                       exact (lequiv_suc _ _ _ E24)] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]. }
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t'' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl'' (lequiv_sym _ _ _ (lequiv_trans _ _ _ _ E13 E35))
                                                HΓ1 Ht'') | exact (lequiv_suc _ _ _ (lequiv_trans _ _ _ _ E24 E46))] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact (lequiv_trans _ _ _ _ E24 E46)]. }
  assert (Ht2' : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] t'' : tyU l4 @ lsuc l4 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl2' (lequiv_sym _ _ _ E35) HΓ3 Ht'') |
                                       exact (lequiv_suc _ _ _ E46)] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ3 | exact E46]. }
  assert (Hctx : [ G ⊢[ i ] Γ ,, tyEl l3 s' @ l3 ≅ Γ ,, tyEl l1 s @ l1 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HEl' | exact EEl' | exact (lequiv_sym _ _ _ E13)]).
  assert (EU24 : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l4 ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ3 | exact E24] |].
    exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E24)). }
  pose proof (cv_tm HG Hc Dt2 Hctx Ht' Ht2' EU24) as Dt2'.
  apply actmnf_code_pi; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46) | |].
  - exact (IHs s'' i _ Hc Hs Hs1 Hs2 Ds2').
  - exact (IHt t'' i _ Hc Ht Ht1 Ht2 Dt2').
Qed.

Lemma T_actmnf_zero {G Γ} : T_tmnf G Γ zero zero tyNat.
Proof. red; intros * _ _ _ _ D2. rewrite (ainv_zero D2). apply actmnf_zero. Qed.

Lemma T_actmnf_succ {G Γ t t'} : T_tm G Γ t t' tyNat -> T_tmnf G Γ (succ t) (succ t') tyNat.
Proof.
  intros IH x'' i k Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_succ D2) as (t'' & -> & Dt2).
  destruct (inv_succ Hi Hx) as ((_ & Ht) & _). destruct (inv_succ Hi Hx') as ((_ & Ht') & _).
  destruct (inv_succ Hi Hx'') as ((_ & Ht'') & _).
  apply actmnf_succ. exact (IH t'' i lzero Hc Ht Ht' Ht'' Dt2).
Qed.

Lemma T_actmnf_ne {G Γ ν ν' W W'} : posty W -> ac_tmnee G Γ ν ν' W' -> T_nee G Γ ν ν' W' -> T_tmnf G Γ ν ν' W.
Proof.
  intros Hp D IH x'' i k Hc Hν Hν' Hν'' D2.
  destruct (ainv_nfne_tm Hp (proj2 (ac_tmnee_whne D)) D2) as (W2 & Dν2).
  eapply actmnf_ne; [exact Hp | exact (IH x'' W2 i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2)].
Qed.

Lemma T_actmnf_eta {G Γ l l' A B w w'} :
  T_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  T_tmnf G Γ w w' (tyPi l l' A B).
Proof.
  intros IH w'' i k Hc Hw Hw' Hw'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi (wf_tm_ty Hi Hw)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  apply actmnf_eta.
  exact (IH _ i l' Hc (pre_eta_body Hi Hv W1 W2 HA HB (lvl_eq_tm' Hk Hw))
           (pre_eta_body Hi Hv W1 W2 HA HB (lvl_eq_tm' Hk Hw')) (pre_eta_body Hi Hv W1 W2 HA HB (lvl_eq_tm' Hk Hw''))
           (ainv_eta D2)).
Qed.

Lemma T_actmnf_ueta {G Γ n l T w w'} :
  T_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  T_tmnf G Γ w w' (tyUPi n l T).
Proof.
  intros IH w'' i k Hc Hw Hw' Hw'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_upi (wf_tm_ty Hi Hw)) as ((-> & HΓ & Hn & W & HT) & Hk).
  apply actmnf_ueta.
  exact (IH _ lM l compt_M (wf_ueta_body W HT (lvl_eq_tm' Hk Hw)) (wf_ueta_body W HT (lvl_eq_tm' Hk Hw'))
           (wf_ueta_body W HT (lvl_eq_tm' Hk Hw'')) (ainv_ueta D2)).
Qed.

Lemma T_actmnf_ceta {G Γ l T w w'} :
  T_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T -> T_tmnf G Γ w w' (tyCPi l T).
Proof.
  intros IH w'' i k Hc Hw Hw' Hw'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_cpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & W & HT) & Hk).
  apply actmnf_ceta.
  exact (IH _ lM l compt_M (wf_ceta_body W HT (lvl_eq_tm' Hk Hw)) (wf_ceta_body W HT (lvl_eq_tm' Hk Hw'))
           (wf_ceta_body W HT (lvl_eq_tm' Hk Hw'')) (ainv_ceta D2)).
Qed.

Lemma T_actmnf_teta {G Γ Δ l l' T w w'} :
  T_tm (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  T_tmnf G Γ w w' (tyTPi Δ l l' T).
Proof.
  intros IH w'' i k Hc Hw Hw' Hw'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_tpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & HΔ & W1 & W2 & HT) & Hk).
  apply actmnf_teta.
  exact (IH _ lM l' compt_M (wf_teta_body HΔ W1 W2 HT (lvl_eq_tm' Hk Hw)) (wf_teta_body HΔ W1 W2 HT (lvl_eq_tm' Hk Hw'))
           (wf_teta_body HΔ W1 W2 HT (lvl_eq_tm' Hk Hw'')) (ainv_teta D2)).
Qed.

Lemma T_actmnf_boxT {G Γ Δ l T T'} : ty_leq T T' -> T_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ l).
Proof.
  intros H; red; intros * _ _ _ _ D2. destruct (ainv_boxT D2) as (T'' & -> & H2).
  apply actmnf_boxT, (ty_leq_trans _ _ _ H H2).
Qed.
Lemma T_actmnf_boxt {G Γ Δ A l t t'} : tm_leq t t' -> T_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ A l).
Proof.
  intros H; red; intros * _ _ _ _ D2. destruct (ainv_boxt D2) as (t3 & -> & H2).
  apply actmnf_boxt, (tm_leq_trans _ _ _ H H2).
Qed.

(** ** Neutral terms *)

Lemma T_actmnee_red {G Γ ν ν' T W} : T_ne G Γ ν ν' T -> reds_ty T W -> whnf_ty W -> T_nee G Γ ν ν' W.
Proof.
  intros IH Hr Hw ν'' W' i k k' k'' A A' A'' Hc Hν Hν' Hν'' D2.
  destruct (ainv_nee D2) as (T2 & D2' & _ & _).
  exact (actmnee_red _ _ _ _ _ _ (IH ν'' T2 i _ _ _ _ _ _ Hc Hν Hν' Hν'' D2') Hr Hw).
Qed.

Lemma T_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> ac_tm G Γ (llk d n) (llk d' n) A[d]) ->
  (forall n A k, in_ctx Θ n A k -> T_tm G Γ (llk d n) (llk d' n) A[d]) -> T_sub G Γ d d' Θ.
Proof.
  intros D IH d'' i Hc HΘ Hd Hd' Hd'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all))))))) _ _ _ _ _
                (acs_pt _ _ _ _ _ D) i Hc HΘ Hd Hd') as (_ & _ & Ee).
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all))))))) _ _ _ _ _
                D2 i Hc HΘ Hd' Hd'') as (_ & _ & Ee2).
  apply acs_pt. intros n A k Hin.
  pose proof (lsw_var _ _ _ _ _ Hd _ _ _ Hin) as H1.
  pose proof (eqtm_wf_r Hi (Ee _ _ _ Hin)) as H2.
  pose proof (wf_ty_func Hi (in_ctx_wf Hi HΘ Hin) (conj Hd (conj Hd' Ee))) as EA.
  assert (EAt : [ G ; Γ ⊢[ typeof i ] A[d] ≅ A[d'] @ k ]) by (rewrite Hi; exact EA).
  pose proof (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi (Ee2 _ _ _ Hin)) EAt) as H3.
  pose proof (cv_tm (ctx_glob _ _ _ (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H1)) Hc
                (ainv_sub D2 n A k Hin) (eqc_refl _ _ _ (ctx_of_wf_tm Hi H1))
                (lsw_var _ _ _ _ _ Hd' _ _ _ Hin) (eqtm_wf_r Hi (Ee2 _ _ _ Hin)) EA) as D2e.
  exact (IH n A k Hin _ i k Hc H1 H2 H3 D2e).
Qed.

Lemma T_actmne_var {G Γ n T l} : in_ctx Γ n T l -> T_ne G Γ (var n) (var n) T.
Proof. intros Hin; red; intros * _ _ _ _ D2. rewrite (ainv_var D2). exact (actmne_var _ _ _ _ _ Hin). Qed.

Lemma T_actmne_gvar {G Γ u Δ i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ i' T l) -> T_sub G Γ d d' Δ ->
  T_ne G Γ (gvar u d) (gvar u d') T[d].
Proof.
  intros Hin IH x'' T' i k k' k'' X X' X'' Hc Hν Hν' Hν'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_gvar D2) as (Δ2 & i2 & T2 & l2 & d'' & -> & Hin2 & Ds2).
  pose proof (in_gctx_det Hin Hin2) as E. injection E as <- <- <- <-.
  destruct (inv_gvar Hi Hν) as (Δ0 & i0 & T0 & l0 & (HΓ & Hin0 & Hle & Ht & Hn & He) & _ & _).
  destruct (inv_gvar Hi Hν') as (Δ1 & i1 & T1 & l1 & (_ & Hin1 & _ & Ht' & Hn' & He') & _ & _).
  destruct (inv_gvar Hi Hν'') as (Δ3 & i3 & T3 & l3 & (_ & Hin3 & _ & Ht'' & Hn'' & He'') & _ & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <- <-.
  pose proof (in_gctx_det Hin Hin3) as E3. injection E3 as <- <- <- <-.
  pose proof HΓ as HΓi. rewrite Hi in HΓi.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓi) Hin) as (HΔ & _).
  eapply actmne_gvar; [exact Hin |].
  exact (IH d'' i Hc (lift_ctx HΔ (lle_D_compt _ Hc)) (lsub_wf_prem Hi HΓi Ht Hn He)
           (lsub_wf_prem Hi HΓi Ht' Hn' He') (lsub_wf_prem Hi HΓi Ht'' Hn'' He'') Ds2).
Qed.

Lemma T_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  ac_ty G (Γ ,, tyNat @ lzero) M M' -> T_ty G (Γ ,, tyNat @ lzero) M M' ->
  ac_tm G Γ s s' M[lsingle zero] -> T_tm G Γ s s' M[lsingle zero] ->
  ac_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> T_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] ->
  T_nee G Γ ν ν' W ->
  T_ne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof.
  intros Hl DM IHM Ds IHs Dz IHz IHν x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_natrec D2) as (l'' & M'' & s'' & z'' & ν'' & W2 & -> & Hl2 & DM2 & Ds2 & Dz2 & Dν2).
  destruct (inv_natrec Hi Hx) as ((Hv & Wl & HM & Hs & Hz & Hν) & _ & _).
  destruct (inv_natrec Hi Hx') as ((_ & Wl' & HM' & Hs' & Hz' & Hν') & _ & _).
  destruct (inv_natrec Hi Hx'') as ((_ & Wl'' & HM'' & Hs'' & Hz'' & Hν'') & _ & _).
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as E. pose proof (leqv_lequiv _ _ _ Wl' Wl'' Hl2) as E2.
  pose proof (lequiv_trans _ _ _ _ E E2) as E02.
  pose proof (ac_ty_sound Hc DM HM (wft_lconv _ _ _ _ _ _ HM' E)) as EM.
  pose proof (ac_ty_sound Hc DM2 HM' (wft_lconv _ _ _ _ _ _ HM'' E2)) as EM2.
  assert (EM02 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M ≅ M'' @ l ])
    by (eapply eqty_trans; [exact EM | exact (eqty_lconv _ _ _ _ _ _ _ EM2 E)]).
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HN : [ G ; Γ ⊢[ i ] tyNat @ lzero ]) by (apply wft_nat; [exact Hv | rewrite Hi; exact HΓ]).
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HN | exact I]).
  assert (H0 : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; [exact Hv | rewrite Hi; exact HΓ]).
  (* the base cases, at the first's motive *)
  pose proof (eqty_single Hi EM H0) as EM0. pose proof (eqty_single Hi EM02 H0) as EM00.
  pose proof (eqty_single Hi EM2 H0) as EM20.
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E] | rewrite Hi; exact EM0]).
  assert (Hs2 : [ G ; Γ ⊢[ i ] s'' : M[lsingle zero] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs'' | exact E02] | rewrite Hi; exact EM00]).
  assert (Hs2' : [ G ; Γ ⊢[ i ] s'' : M'[lsingle zero] @ l' ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs'' | exact E2] | rewrite Hi; exact EM20]).
  pose proof (cv_tm HG Hc Ds2 (eqc_refl _ _ _ HΓ) Hs' Hs2'
                (eqty_lconv _ _ _ _ _ _ _ EM0 (lequiv_sym _ _ _ E))) as Ds2'.
  (* the steps, in the first's context at the first's motive *)
  assert (HΓM : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] ]) by (apply wfc_ext; assumption).
  assert (HΓM' : [ G ; Γ ,, tyNat @ lzero ,, M' @ l' ⊢[ i ] ]) by (apply wfc_ext; assumption).
  assert (EM' : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' ≅ M @ l' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM) | exact (lequiv_sym _ _ _ E)]).
  assert (EM2' : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M'' ≅ M' @ l'' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM2) | exact (lequiv_sym _ _ _ E2)]).
  assert (EM02' : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M'' ≅ M @ l'' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM02) | exact (lequiv_sym _ _ _ E02)]).
  pose proof (eqty_subst Hi EM (lsub_wf_lsucc Hi Hv HΓM)) as EMs.
  pose proof (eqty_subst Hi EM02 (lsub_wf_lsucc Hi Hv HΓM)) as EMs02.
  pose proof (eqty_subst Hi EM2 (lsub_wf_lsucc Hi Hv HΓM')) as EMs2.
  assert (Hz1 : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EM' (lequiv_sym _ _ _ E) HΓM Hz') | exact E]
                        | rewrite Hi; exact EMs]).
  assert (Hz2 : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z'' : M[lsucc] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EM02' (lequiv_sym _ _ _ E02) HΓM Hz'') | exact E02]
                        | rewrite Hi; exact EMs02]).
  assert (Hz2' : [ G ; Γ ,, tyNat @ lzero ,, M' @ l' ⊢[ i ] z'' : M'[lsucc] @ l' ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EM2' (lequiv_sym _ _ _ E2) HΓM' Hz'') | exact E2]
                        | rewrite Hi; exact EMs2]).
  assert (Hctx : [ G ⊢[ i ] Γ ,, tyNat @ lzero ,, M' @ l' ≅ Γ ,, tyNat @ lzero ,, M @ l ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓN) | exact HM' | exact EM' | exact (lequiv_sym _ _ _ E)]).
  assert (EMsc : [ G ; Γ ,, tyNat @ lzero ,, M' @ l' ⊢[ i ] M[lsucc] ≅ M'[lsucc] @ l' ]).
  { pose proof (eqty_subst Hi EM' (lsub_wf_lsucc Hi Hv HΓM')) as X1.
    exact (eqty_sym _ _ _ _ _ _ X1). }
  pose proof (cv_tm HG Hc Dz2 Hctx Hz' Hz2' EMsc) as Dz2'.
  eapply actmne_natrec; [exact (leqv_trans _ _ _ Hl Hl2) | | | |].
  - exact (IHM M'' i _ _ _ Hc HM HM' HM'' DM2).
  - exact (IHs s'' i l Hc Hs Hs1 Hs2 Ds2').
  - exact (IHz z'' i l Hc Hz Hz1 Hz2 Dz2').
  - exact (IHν ν'' W2 i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2).
Qed.

(** A typing at an equal type and an equivalent level. *)
Lemma retype {G i Γ t A A' l l'} : typeof i = i -> [ G ; Γ ⊢[ i ] t : A' @ l' ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] t : A @ l ].
Proof. intros Hi Ht El E. eapply wf_conv; [eapply wf_lconv; [exact Ht | exact El] | rewrite Hi; exact E]. Qed.

Lemma T_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> T_nee G Γ ν ν' (tyPi m m' A0 B0) ->
  ac_tm G Γ s s' A0 -> T_tm G Γ s s' A0 ->
  T_ne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof.
  intros Dν IHν Ds IHs x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_app D2) as (l5 & l6 & A'' & B'' & ν'' & s'' & m2 & m2' & A1 & B1 & -> & Dν2 & Ds2).
  destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν & Hs) & _ & _).
  destruct (inv_app Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν' & Hs') & _ & _).
  destruct (inv_app Hi Hx'') as ((_ & W5 & W6 & HA'' & HB'' & Hν'' & Hs'') & _ & _).
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (ac_nee_sound' Dν2 Hc Hν' Hν'') as (F1 & F2 & _).
  destruct (pi_inj_c Hc E0) as (Em1 & _ & EA0 & _).
  destruct (pi_inj_c Hc E1) as (Em3 & _ & EA1 & _).
  destruct (pi_inj_c Hc F1) as (Fm3 & _ & FA1 & _).
  destruct (pi_inj_c Hc F2) as (Fm5 & _ & FA2 & _).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em1) Em3) as E13.
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Fm3) Fm5) as E35.
  (* the domains: A0 ≅ A' ≅ A1 *)
  assert (E01 : [ G ; Γ ⊢[ i ] A0 ≅ A1 @ l3 ]) by (eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ EA1) | exact FA1]).
  assert (EA0'' : [ G ; Γ ⊢[ i ] A1 ≅ A'' @ l3 ])
    by exact (eqty_sym _ _ _ _ _ _ (eqty_lconv _ _ _ _ _ _ _ FA2 E35)).
  pose proof (retype Hi Hs (lequiv_refl _ _ W1) (eqty_sym _ _ _ _ _ _ EA0)) as Hs0.
  pose proof (retype Hi Hs' E13 (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EA1) E13)) as Hs1.
  assert (E0'' : [ G ; Γ ⊢[ i ] A0 ≅ A'' @ l1 ])
    by exact (eqty_lconv _ _ _ _ _ _ _ (eqty_trans _ _ _ _ _ _ _ E01 EA0'') E13).
  pose proof (retype Hi Hs'' (lequiv_trans _ _ _ _ E13 E35) E0'') as Hs2.
  (* the second, at the first's domain *)
  pose proof (retype Hi Hs' (lequiv_refl _ _ W3) (eqty_sym _ _ _ _ _ _ FA1)) as Hs1'.
  pose proof (retype Hi Hs'' E35 (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ FA2) E35)) as Hs2'.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  pose proof (cv_tm (ctx_glob _ _ _ HΓ) Hc Ds2 (eqc_refl _ _ _ HΓ) Hs1' Hs2' E01) as Ds2'.
  eapply actmne_app; [exact (IHν ν'' _ i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2) | exact (IHs s'' i l1 Hc Hs0 Hs1 Hs2 Ds2')].
Qed.

Lemma T_actmne_uapp {G Γ n l T ν ν' ls ls'} :
  T_nee G Γ ν ν' (tyUPi n l T) -> length ls = n -> Forall2 leqv ls ls' ->
  T_ne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros IHν Hn Hls x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_uapp D2) as (n2 & l2 & T2 & ν'' & ls'' & -> & Dν2 & _ & Hls2).
  destruct (inv_uapp Hi Hx) as (n0 & l0 & T0 & (-> & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_uapp Hi Hx') as (n1 & l1 & T1 & (_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (inv_uapp Hi Hx'') as (n3 & l3 & T3 & (_ & _ & _ & _ & _ & Hν'') & _ & _).
  eapply actmne_uapp; [exact (IHν ν'' _ lM _ _ _ _ _ _ compt_M Hν Hν' Hν'' Dν2) | exact Hn
                      | exact (leqvs_trans _ _ _ Hls Hls2)].
Qed.

Lemma T_actmne_capp {G Γ l T ν ν' Δ Δ'} :
  T_nee G Γ ν ν' (tyCPi l T) -> T_ctx G Δ Δ' -> T_ne G Γ (capp ν Δ) (capp ν' Δ') T⦃gsingle (GCtx Δ)⦄.
Proof.
  intros IHν IHc x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_capp D2) as (l2 & T2 & ν'' & Δ'' & -> & Dν2 & Dc2).
  destruct (inv_capp Hi Hx) as (l0 & T0 & (-> & _ & _ & HΔ & Hν & _) & _ & _).
  destruct (inv_capp Hi Hx') as (l1 & T1 & (_ & _ & _ & HΔ' & Hν' & _) & _ & _).
  destruct (inv_capp Hi Hx'') as (l3 & T3 & (_ & _ & _ & HΔ'' & Hν'' & _) & _ & _).
  eapply actmne_capp; [exact (IHν ν'' _ lM _ _ _ _ _ _ compt_M Hν Hν' Hν'' Dν2) | exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2)].
Qed.

Lemma T_actmne_tapp {G Γ Δ l l' T ν ν' A A'} :
  ac_tmnee G Γ ν ν' (tyTPi Δ l l' T) -> T_nee G Γ ν ν' (tyTPi Δ l l' T) -> T_ty G Δ A A' ->
  T_ne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof.
  intros Dν IHν IHA x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_tapp D2) as (Δ2 & l2 & l2' & T2 & ν'' & A'' & -> & Dν2 & DA2).
  destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T0 & (-> & Hν & HΔ0 & _ & _ & _ & HA & _) & _ & _).
  destruct (inv_tapp Hi Hx') as (Δ1 & l1 & l1' & T1 & (_ & Hν' & HΔ1 & _ & _ & _ & HA' & _) & _ & _).
  destruct (inv_tapp Hi Hx'') as (Δ3 & l3 & l3' & T3 & (_ & Hν'' & HΔ3 & _ & _ & _ & HA'' & _) & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & E1 & _).
  destruct (ac_nee_sound' Dν2 compt_M Hν' Hν'') as (F1 & F2 & _).
  destruct (declM_tpi_inj E0) as (Ec0 & _ & _ & _). destruct (declM_tpi_inj E1) as (Ec1 & _ & _ & _).
  destruct (declM_tpi_inj F1) as (Fc1 & _ & _ & _). destruct (declM_tpi_inj F2) as (Fc3 & _ & _ & _).
  pose proof (eqctx_trans_D (eqctx_sym_D Ec1) Fc1) as E2.
  pose proof (eqctx_trans_D Fc3 (eqctx_sym_D E2)) as E3.
  pose proof (cv_ty (ctx_glob _ _ _ HΔ0) compt_D DA2 (eqctx_sym_D E2) (mvD Fc1 HA') (mvD Fc3 HA'')) as DA2'.
  eapply actmne_tapp; [exact (IHν ν'' _ lM _ _ _ _ _ _ compt_M Hν Hν' Hν'' Dν2) |].
  exact (IHA A'' lD _ _ _ compt_D (mvD Ec0 HA) (mvD Ec1 HA') (mvD E3 HA'') DA2').
Qed.

Lemma T_actmne_letboxT {G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ctx G Δ Δ' -> T_ctx G Δ Δ' ->
  ac_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' -> T_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' ->
  T_tm (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  T_nee G Γ ν ν' W ->
  T_ne G Γ (letboxT l1 l2 Δ M t1 ν) (letboxT l3 l4 Δ' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 Dc IHc DM IHM IHt IHν x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_letboxT D2) as (l5 & l6 & Δ'' & M'' & t3 & ν'' & W2 & -> & H35 & H46 & Dc2 & DM2 & Dt2 & Dν2).
  destruct (inv_letboxT Hi Hx) as ((-> & W1 & W2' & HΔ & HM & Ht1 & Hν) & _ & _).
  destruct (inv_letboxT Hi Hx') as ((_ & W3 & W4 & HΔ' & HM' & Ht2 & Hν') & _ & _).
  destruct (inv_letboxT Hi Hx'') as ((_ & W5 & W6 & HΔ'' & HM'' & Ht3 & Hν'') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2' W4 H24) as E24.
  pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35. pose proof (leqv_lequiv _ _ _ W4 W6 H46) as E46.
  pose proof (lequiv_trans _ _ _ _ E13 E35) as E15. pose proof (lequiv_trans _ _ _ _ E24 E46) as E26.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec. pose proof (ac_ctx_sound' Dc2 HΔ' HΔ'') as Ec2.
  pose proof (eqctx_trans_D Ec Ec2) as Ec02.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 @ lzero ]) by (apply wft_CTyp; assumption).
  assert (HC' : [ G ; Γ ⊢[ lM ] tyCTyp Δ' l4 @ lzero ]) by (apply wft_CTyp; assumption).
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ' l4 @ lzero ]) by (apply eqty_CTyp; assumption).
  assert (HCC2 : [ G ; Γ ⊢[ lM ] tyCTyp Δ' l4 ≅ tyCTyp Δ'' l6 @ lzero ]) by (apply eqty_CTyp; assumption).
  assert (HCC02 : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ'' l6 @ lzero ]) by (apply eqty_CTyp; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  assert (HΓ1' : [ G ; Γ ,, tyCTyp Δ' l4 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC' | exact I]).
  pose proof (lequiv_refl (gL G) lzero I) as E00.
  (* the motives, in the first's context *)
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC) E00 HΓ1 HM') E13) as HM1.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC02) E00 HΓ1 HM'') E15) as HM2.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC2) E00 HΓ1' HM'') E35) as HM2'.
  pose proof (ac_ty_sound compt_M DM HM HM1) as EM.
  pose proof (ac_ty_sound compt_M DM2 HM' HM2') as EM2.
  assert (EM02 : [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M ≅ M'' @ l1 ]).
  { eapply eqty_trans; [exact EM |]. eapply eqty_lconv; [| exact E13].
    exact (stab_eqty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC) E00 HΓ1 EM2). }
  assert (Hctx : [ G ⊢[ lM ] Γ ,, tyCTyp Δ' l4 @ lzero ≅ Γ ,, tyCTyp Δ l2 @ lzero ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HC' | exact (eqty_sym _ _ _ _ _ _ HCC) | exact E00]).
  pose proof (cv_ty HG compt_M DM2 Hctx HM' HM2') as DM2'.
  (* the bodies, under the first's binding *)
  assert (HGD : [ ⊢ gext G (gdTy Δ lC l2) ]) by (apply wfg_ty; [exact HG | exact HΔ | left; reflexivity | exact W2']).
  assert (HGD' : [ ⊢ gext G (gdTy Δ' lC l4) ]) by (apply wfg_ty; [exact HG | exact HΔ' | left; reflexivity | exact W4]).
  pose proof (gbind_tm HG HGD (gbind_obj_ty (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) HGD Ec E24)
                eq_refl Ht2) as Ht2a.
  pose proof (gbind_tm HG HGD (gbind_obj_ty (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) HGD Ec02 E26)
                eq_refl Ht3) as Ht3a.
  pose proof (gbind_tm HG HGD' (gbind_obj_ty (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) HGD' Ec2 E46)
                eq_refl Ht3) as Ht3a'.
  pose proof (letboxT_body_eq HGD HΔ W2' EM) as EMb.
  pose proof (letboxT_body_eq HGD HΔ W2' EM02) as EMb02.
  pose proof (letboxT_body_eq HGD' HΔ' W4 EM2) as EMb2.
  assert (Ht2b : [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E13] | exact EMb]).
  assert (Ht3b : [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t3 : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht3a | exact E15] | exact EMb02]).
  assert (Ht3b' : [ gext G (gdTy Δ' lC l4) ; Γ⟪S⟫ ⊢[ lM ] t3 : M'⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l3 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht3a' | exact E35] | exact EMb2]).
  pose proof (GEq_ext (GEq_refl _ HG) HGD' HGD
                (conj eq_refl (conj (or_introl eq_refl) (conj (lequiv_sym _ _ _ E24) (eqctx_sym_D Ec))))) as HE.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 ac_conv_all)))) _ _ _ _ _ Dt2 lM _ _ _ l3 compt_M HE
                (eqc_refl _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht1)) Ht2 Ht3b'
                (eqty_lconv _ _ _ _ _ _ _ EMb (lequiv_sym _ _ _ E13))) as Dt2'.
  eapply actmne_letboxT; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46)
                         | exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2) | exact (IHM M'' lM _ _ _ compt_M HM HM1 HM2 DM2')
                         | exact (IHt t3 lM l1 compt_M Ht1 Ht2b Ht3b Dt2')
                         | exact (IHν ν'' W2 lM _ _ _ _ _ _ compt_M Hν Hν' Hν'' Dν2)].
Qed.

Lemma T_actmne_letboxt {G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ctx G Δ Δ' -> T_ctx G Δ Δ' -> ac_ty G Δ T T' -> T_ty G Δ T T' ->
  ac_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' -> T_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' ->
  T_tm (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  T_nee G Γ ν ν' W ->
  T_ne G Γ (letboxt l1 l2 Δ T M t1 ν) (letboxt l3 l4 Δ' T' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 Dc IHc DT IHT DM IHM IHt IHν x'' T0 i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_letboxt D2) as (l5 & l6 & Δ'' & T'' & M'' & t3 & ν'' & W2 & -> & H35 & H46 & Dc2 & DT2 & DM2 & Dt2 & Dν2).
  destruct (inv_letboxt Hi Hx) as ((-> & W1 & W2' & HΔ & HT & HM & Ht1 & Hν) & _ & _).
  destruct (inv_letboxt Hi Hx') as ((_ & W3 & W4 & HΔ' & HT' & HM' & Ht2 & Hν') & _ & _).
  destruct (inv_letboxt Hi Hx'') as ((_ & W5 & W6 & HΔ'' & HT'' & HM'' & Ht3 & Hν'') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2' W4 H24) as E24.
  pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35. pose proof (leqv_lequiv _ _ _ W4 W6 H46) as E46.
  pose proof (lequiv_trans _ _ _ _ E13 E35) as E15. pose proof (lequiv_trans _ _ _ _ E24 E46) as E26.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec. pose proof (ac_ctx_sound' Dc2 HΔ' HΔ'') as Ec2.
  pose proof (eqctx_trans_D Ec Ec2) as Ec02.
  (* the payload types *)
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E24)) as HT1.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec02) HT'' (lequiv_sym _ _ _ E26)) as HT2.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec2) HT'' (lequiv_sym _ _ _ E46)) as HT2'.
  pose proof (ac_ty_sound compt_D DT HT HT1) as ET.
  pose proof (ac_ty_sound compt_D DT2 HT' HT2') as ET2.
  assert (ET02 : [ G ; Δ ⊢[ lD ] T ≅ T'' @ l2 ]).
  { eapply eqty_trans; [exact ET |]. eapply eqty_lconv; [| exact E24].
    exact (ctxconv_eqty (eqctx_sym_D Ec) (i := lD) eq_refl ET2). }
  assert (ET' : [ G ; Δ' ⊢[ lD ] T' ≅ T @ l4 ]).
  { eapply eqty_lconv; [| exact (lequiv_sym _ _ _ E24)].
    exact (ctxconv_eqty Ec (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ ET)). }
  pose proof (cv_ty (ctx_glob _ _ _ HΔ) compt_D DT2 (eqctx_sym_D Ec) HT' HT2') as DT2'.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 @ lzero ]) by (apply wft_CTrm; assumption).
  assert (HC' : [ G ; Γ ⊢[ lM ] tyCTrm Δ' T' l4 @ lzero ]) by (apply wft_CTrm; assumption).
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ' T' l4 @ lzero ]) by (apply eqty_CTrm; assumption).
  assert (HCC2 : [ G ; Γ ⊢[ lM ] tyCTrm Δ' T' l4 ≅ tyCTrm Δ'' T'' l6 @ lzero ]) by (apply eqty_CTrm; assumption).
  assert (HCC02 : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ'' T'' l6 @ lzero ]) by (apply eqty_CTrm; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  assert (HΓ1' : [ G ; Γ ,, tyCTrm Δ' T' l4 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC' | exact I]).
  pose proof (lequiv_refl (gL G) lzero I) as E00.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC) E00 HΓ1 HM') E13) as HM1.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC02) E00 HΓ1 HM'') E15) as HM2.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC2) E00 HΓ1' HM'') E35) as HM2'.
  pose proof (ac_ty_sound compt_M DM HM HM1) as EM.
  pose proof (ac_ty_sound compt_M DM2 HM' HM2') as EM2.
  assert (EM02 : [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M ≅ M'' @ l1 ]).
  { eapply eqty_trans; [exact EM |]. eapply eqty_lconv; [| exact E13].
    exact (stab_eqty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC) E00 HΓ1 EM2). }
  assert (Hctx : [ G ⊢[ lM ] Γ ,, tyCTrm Δ' T' l4 @ lzero ≅ Γ ,, tyCTrm Δ T l2 @ lzero ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HC' | exact (eqty_sym _ _ _ _ _ _ HCC) | exact E00]).
  pose proof (cv_ty HG compt_M DM2 Hctx HM' HM2') as DM2'.
  assert (HGD : [ ⊢ gext G (gdTm Δ lC T l2) ]) by (apply wfg_tm; [exact HG | exact HT | right; reflexivity | exact W2']).
  assert (HGD' : [ ⊢ gext G (gdTm Δ' lC T' l4) ]) by (apply wfg_tm; [exact HG | exact HT' | right; reflexivity | exact W4]).
  pose proof (gbind_tm HG HGD (gbind_obj_tm HGD Ec ET E24) eq_refl Ht2) as Ht2a.
  pose proof (gbind_tm HG HGD (gbind_obj_tm HGD Ec02 ET02 E26) eq_refl Ht3) as Ht3a.
  pose proof (gbind_tm HG HGD' (gbind_obj_tm HGD' Ec2 ET2 E46) eq_refl Ht3) as Ht3a'.
  pose proof (letboxt_body_eq HGD HΔ HT W2' EM) as EMb.
  pose proof (letboxt_body_eq HGD HΔ HT W2' EM02) as EMb02.
  pose proof (letboxt_body_eq HGD' HΔ' HT' W4 EM2) as EMb2.
  assert (Ht2b : [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E13] | exact EMb]).
  assert (Ht3b : [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] t3 : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht3a | exact E15] | exact EMb02]).
  assert (Ht3b' : [ gext G (gdTm Δ' lC T' l4) ; Γ⟪S⟫ ⊢[ lM ] t3 : M'⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l3 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht3a' | exact E35] | exact EMb2]).
  pose proof (GEq_ext (GEq_refl _ HG) HGD' HGD
                (conj eq_refl (conj (or_intror eq_refl) (conj (lequiv_sym _ _ _ E24) (conj (eqctx_sym_D Ec) ET'))))) as HE.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 ac_conv_all)))) _ _ _ _ _ Dt2 lM _ _ _ l3 compt_M HE
                (eqc_refl _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht1)) Ht2 Ht3b'
                (eqty_lconv _ _ _ _ _ _ _ EMb (lequiv_sym _ _ _ E13))) as Dt2'.
  eapply actmne_letboxt; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46)
                         | exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2) | exact (IHT T'' lD _ _ _ compt_D HT HT1 HT2 DT2')
                         | exact (IHM M'' lM _ _ _ compt_M HM HM1 HM2 DM2')
                         | exact (IHt t3 lM l1 compt_M Ht1 Ht2b Ht3b Dt2')
                         | exact (IHν ν'' W2 lM _ _ _ _ _ _ compt_M Hν Hν' Hν'' Dν2)].
Qed.

(** ** The recursors *)

Lemma T_rec_core {G Γ l1 l2 l1' l2' l1'' l2'' MT MT' MT'' Mt Mt' Mt'' bs bs' bs''} :
  ac_ty (recGT G) (recΓT Γ) MT MT' -> T_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> T_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> T_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  ac_ty (recGT G) (recΓT Γ) MT' MT'' -> ac_ty (recGt G) (recΓt Γ) Mt' Mt'' ->
  (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2')
                         (bs' j) (bs'' j) (brRes j (wrapMT MT') (wrapMt Mt'))) ->
  [ G ; Γ ⊢[ lM ] ] -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  lequiv (gL G) l1' l1'' -> lequiv (gL G) l2' l2'' ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] -> [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT'' @ lvren l1'' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] -> [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt'' @ lvren l2'' (ush 1) ] ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT'') (wrapMt Mt'') l1'' l2'' ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                         bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT'') (wrapMt Mt'') l1'' l2'' ⊢[ lM ]
                         bs'' j : brRes j (wrapMT MT'') (wrapMt Mt'') @ brLv j l1'' l2'' ]) ->
  ac_ty (recGT G) (recΓT Γ) MT MT'' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt'' /\
  (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs'' j) (brRes j (wrapMT MT) (wrapMt Mt))).
Proof.
  intros DMT IHT DMt IHt IHb DMT2 DMt2 Db2 HΓ E1 E2 E1' E2' HMT HMT' HMT'' HMt HMt' HMt'' Hbc Hbc' Hbc''
    Hbs Hbs' Hbs''.
  pose proof (lequiv_trans _ _ _ _ E1 E1') as E11. pose proof (lequiv_trans _ _ _ _ E2 E2') as E22.
  pose proof (wft_lconv _ _ _ _ _ _ HMT' (lequiv_ush 1 E1)) as HMT1.
  pose proof (wft_lconv _ _ _ _ _ _ HMT'' (lequiv_ush 1 E11)) as HMT2.
  pose proof (wft_lconv _ _ _ _ _ _ HMT'' (lequiv_ush 1 E1')) as HMT2'.
  pose proof (wft_lconv _ _ _ _ _ _ HMt' (lequiv_ush 1 E2)) as HMt1.
  pose proof (wft_lconv _ _ _ _ _ _ HMt'' (lequiv_ush 1 E22)) as HMt2.
  pose proof (wft_lconv _ _ _ _ _ _ HMt'' (lequiv_ush 1 E2')) as HMt2'.
  pose proof (ac_ty_sound compt_M DMT HMT HMT1) as EMT.
  pose proof (ac_ty_sound compt_M DMt HMt HMt1) as EMt.
  pose proof (ac_ty_sound compt_M DMT2 HMT' HMT2') as EMT2.
  pose proof (ac_ty_sound compt_M DMt2 HMt' HMt2') as EMt2.
  pose proof (eqty_trans _ _ _ _ _ _ _ EMT (eqty_lconv _ _ _ _ _ _ _ EMT2 (lequiv_ush 1 E1))) as EMT02.
  pose proof (eqty_trans _ _ _ _ _ _ _ EMt (eqty_lconv _ _ _ _ _ _ _ EMt2 (lequiv_ush 1 E2))) as EMt02.
  pose proof (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EMT) (lequiv_ush 1 (lequiv_sym _ _ _ E1))) as EMT'.
  pose proof (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EMt) (lequiv_ush 1 (lequiv_sym _ _ _ E2))) as EMt'.
  refine (conj (IHT MT'' lM _ _ _ compt_M HMT HMT1 HMT2 DMT2) (conj (IHt Mt'' lM _ _ _ compt_M HMt HMt1 HMt2 DMt2) _)).
  intros j Hj.
  pose proof (branch_conv j Hj EMT EMt E1 E2 HΓ (Hbc j Hj) (Hbc' j Hj) (Hbs' j Hj)) as Hb1.
  pose proof (branch_conv j Hj EMT02 EMt02 E11 E22 HΓ (Hbc j Hj) (Hbc'' j Hj) (Hbs'' j Hj)) as Hb2.
  pose proof (branch_conv j Hj EMT2 EMt2 E1' E2' HΓ (Hbc' j Hj) (Hbc'' j Hj) (Hbs'' j Hj)) as Hb2'.
  destruct (brΓ_conv j Hj EMT' EMt' (lequiv_sym _ _ _ E1) (lequiv_sym _ _ _ E2) HΓ (Hbc' j Hj)) as [HCC HR].
  pose proof (cv_tm (ctx_glob _ _ _ (Hbc' j Hj)) compt_M (Db2 j Hj) HCC (Hbs' j Hj) Hb2' (eqty_sym _ _ _ _ _ _ HR))
    as Db2'.
  exact (IHb j Hj (bs'' j) lM _ compt_M (Hbs j Hj) Hb1 Hb2 Db2').
Qed.

Ltac trec_core IHT IHt IHb DMT DMt DMT2 DMt2 Db2 Eba :=
  let HΓ := fresh "HΓ" in
  match goal with Hν : [ _ ; ?Γ ⊢[ lM ] _ : _ @ _ ] |- _ =>
    pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ end;
  match goal with
  | W1 : lwf _ ?l1, W1' : lwf _ ?l1', H1 : leqv ?l1 ?l1', W1'' : lwf _ ?l1'', H1' : leqv ?l1' ?l1'',
    W2 : lwf _ ?l2, W2' : lwf _ ?l2', H2 : leqv ?l2 ?l2', W2'' : lwf _ ?l2'', H2' : leqv ?l2' ?l2'',
    HMT : [ recGT _ ; _ ⊢[ lM ] ?MT @ _ ], HMT' : [ recGT _ ; _ ⊢[ lM ] ?MT' @ _ ],
    HMT'' : [ recGT _ ; _ ⊢[ lM ] ?MT'' @ _ ],
    HMt : [ recGt _ ; _ ⊢[ lM ] ?Mt @ _ ], HMt' : [ recGt _ ; _ ⊢[ lM ] ?Mt' @ _ ],
    HMt'' : [ recGt _ ; _ ⊢[ lM ] ?Mt'' @ _ ],
    Hbc : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT) _ _ _ ⊢[ lM ] ],
    Hbc' : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT') _ _ _ ⊢[ lM ] ],
    Hbc'' : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT'') _ _ _ ⊢[ lM ] ],
    Hbs : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT) _ _ _ ⊢[ lM ] _ : _ @ _ ],
    Hbs' : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT') _ _ _ ⊢[ lM ] _ : _ @ _ ],
    Hbs'' : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT'') _ _ _ ⊢[ lM ] _ : _ @ _ ],
    Eb : forall k, k < nbr -> ?bs k = _, Eb' : forall k, k < nbr -> ?bs' k = _,
    Eb3 : forall k, k < nbr -> ?bs'' k = _ |- _ =>
    let Hbs0 := fresh "Hbs0" in let Hbs1 := fresh "Hbs1" in let Hbs2 := fresh "Hbs2" in let Db2' := fresh "Db2'" in
    assert (Hbs0 : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT MT) _ _ _ ⊢[ lM ]
                                        bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
      by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj));
    assert (Hbs1 : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT MT') _ _ _ ⊢[ lM ]
                                        bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ])
      by (intros j Hj; rewrite (Eb' j Hj); exact (Hbs' j Hj));
    assert (Hbs2 : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT MT'') _ _ _ ⊢[ lM ]
                                        bs'' j : brRes j (wrapMT MT'') (wrapMt Mt'') @ brLv j l1'' l2'' ])
      by (intros j Hj; rewrite (Eb3 j Hj); exact (Hbs'' j Hj));
    assert (Db2' : forall j, j < nbr -> ac_tm _ (brΓ j _ (wrapMT MT') (wrapMt Mt') l1' l2')
                                        (bs' j) (bs'' j) (brRes j (wrapMT MT') (wrapMt Mt')))
      by (intros j Hj; rewrite (Eba j Hj); exact (Db2 j Hj));
    destruct (T_rec_core DMT IHT DMt IHt IHb DMT2 DMt2 Db2' HΓ (leqv_lequiv _ _ _ W1 W1' H1)
                (leqv_lequiv _ _ _ W2 W2' H2) (leqv_lequiv _ _ _ W1' W1'' H1') (leqv_lequiv _ _ _ W2' W2'' H2')
                HMT HMT' HMT'' HMt HMt' HMt'' Hbc Hbc' Hbc'' Hbs0 Hbs1 Hbs2) as (XMT & XMt & Xb)
  end.

Lemma T_actmne_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> T_ctx G Δ Δ' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> T_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> T_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> T_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  ac_tmnee G Γ ν ν' W -> T_nee G Γ ν ν' W ->
  T_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν')
    (motT (wrapMT MT) l Δ ν).
Proof.
  intros H1 H2 Hl IHc DMT IHT DMt IHt IHb Dν IHν x'' T0 i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'.
  destruct (ainv_elimT (proj2 (ac_tmnee_whne Dν)) D2)
    as (MTa & Mta & bsa & l1'' & l2'' & MTb & Mtb & bsb & l'' & Δ'' & ν'' & W3 & Erba & -> & H1' & H2' & Hl'
        & Dc2 & DMT2 & DMt2 & Db2 & Dν2).
  destruct (mkrb_inj_MT Erba) as [<- <-]. pose proof (mkrb_inj_br Erba) as Eba.
  destruct (inv_elimT Hi Hx'') as (MT3 & Mt3 & bs3 & (Erb3 & _ & _ & W1'' & W2'' & Wl'' & HΔ'' & HMT'' & HMt''
                                   & Hbc'' & Hbs'' & Hν'') & _ & _).
  destruct (mkrb_inj_MT Erb3) as [<- <-]. pose proof (mkrb_inj_br Erb3) as Eb3.
  trec_core IHT IHt IHb DMT DMt DMT2 DMt2 Db2 Eba.
  eapply actmne_elimT; [exact (leqv_trans _ _ _ H1 H1') | exact (leqv_trans _ _ _ H2 H2')
                       | exact (leqv_trans _ _ _ Hl Hl') | exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2) | exact XMT | exact XMt
                       | exact Xb | exact (IHν ν'' W3 lM _ _ _ _ _ _ compt_M Hν Hν' Hν'' Dν2)].
Qed.

Lemma T_actmne_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' U d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> T_ctx G Δ Δ' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> T_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> T_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> T_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  T_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d)))
    (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' (boxT (tyGvar U d')))
    (motT (wrapMT MT) l Δ (boxT (tyGvar U d))).
Proof.
  intros H1 H2 Hl IHc DMT IHT DMt IHt IHb Hd x'' T0 i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'.
  destruct (ainv_elimT_gvar D2)
    as (MTa & Mta & bsa & l1'' & l2'' & MTb & Mtb & bsb & l'' & Δ'' & d'' & Erba & -> & H1' & H2' & Hl'
        & Dc2 & DMT2 & DMt2 & Db2 & Hd2).
  destruct (mkrb_inj_MT Erba) as [<- <-]. pose proof (mkrb_inj_br Erba) as Eba.
  destruct (inv_elimT Hi Hx'') as (MT3 & Mt3 & bs3 & (Erb3 & _ & _ & W1'' & W2'' & Wl'' & HΔ'' & HMT'' & HMt''
                                   & Hbc'' & Hbs'' & Hν'') & _ & _).
  destruct (mkrb_inj_MT Erb3) as [<- <-]. pose proof (mkrb_inj_br Erb3) as Eb3.
  trec_core IHT IHt IHb DMT DMt DMT2 DMt2 Db2 Eba.
  eapply actmne_elimT_gvar; [exact (leqv_trans _ _ _ H1 H1') | exact (leqv_trans _ _ _ H2 H2')
                            | exact (leqv_trans _ _ _ Hl Hl') | exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2) | exact XMT
                            | exact XMt | exact Xb | exact (lsub_leq_trans _ _ _ Hd Hd2)].
Qed.

Lemma T_actmne_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> T_ctx G Δ Δ' -> T_ty G Δ T T' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> T_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> T_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> T_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  ac_tmnee G Γ ν ν' W -> T_nee G Γ ν ν' W ->
  T_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' ν')
    (mott (wrapMt Mt) l Δ T ν).
Proof.
  intros H1 H2 Hl Dc IHc IHi DMT IHT DMt IHt IHb Dν IHν x'' T0 i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'.
  destruct (ainv_elimt (proj2 (ac_tmnee_whne Dν)) D2)
    as (MTa & Mta & bsa & l1'' & l2'' & MTb & Mtb & bsb & l'' & Δ'' & T'' & ν'' & W3 & Erba & -> & H1' & H2' & Hl'
        & Dc2 & DT2 & DMT2 & DMt2 & Db2 & Dν2).
  destruct (mkrb_inj_MT Erba) as [<- <-]. pose proof (mkrb_inj_br Erba) as Eba.
  destruct (inv_elimt Hi Hx'') as (MT3 & Mt3 & bs3 & (Erb3 & _ & _ & W1'' & W2'' & Wl'' & HΔ'' & HMT'' & HMt''
                                   & Hbc'' & Hbs'' & HT'' & Hν'') & _ & _).
  destruct (mkrb_inj_MT Erb3) as [<- <-]. pose proof (mkrb_inj_br Erb3) as Eb3.
  trec_core IHT IHt IHb DMT DMt DMT2 DMt2 Db2 Eba.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec. pose proof (ac_ctx_sound' Dc2 HΔ' HΔ'') as Ec2.
  pose proof (cv_ty (ctx_glob _ _ _ HΔ) compt_D DT2 (eqctx_sym_D Ec) HT' (mvD (eqctx_sym_D Ec2) HT'')) as DT2'.
  eapply actmne_elimt; [exact (leqv_trans _ _ _ H1 H1') | exact (leqv_trans _ _ _ H2 H2')
                       | exact (leqv_trans _ _ _ Hl Hl') | exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2)
                       | exact (IHi T'' lD _ _ _ compt_D HT (mvD (eqctx_sym_D Ec) HT')
                                  (mvD (eqctx_sym_D (eqctx_trans_D Ec Ec2)) HT'') DT2')
                       | exact XMT | exact XMt | exact Xb | exact (IHν ν'' W3 lM _ _ _ _ _ _ compt_M Hν Hν' Hν'' Dν2)].
Qed.

Lemma T_actmne_elimt_glob {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' c c'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> T_ctx G Δ Δ' -> T_ty G Δ T T' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> T_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> T_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> T_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  boxed_global c -> tm_leq c c' ->
  T_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c))
    (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' (boxt c'))
    (mott (wrapMt Mt) l Δ T (boxt c)).
Proof.
  intros H1 H2 Hl Dc IHc IHi DMT IHT DMt IHt IHb Hg Hd x'' T0 i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'.
  destruct (ainv_elimt_glob (boxed_global_leq _ _ Hg Hd) D2)
    as (MTa & Mta & bsa & l1'' & l2'' & MTb & Mtb & bsb & l'' & Δ'' & T'' & d'' & Erba & -> & H1' & H2' & Hl'
        & Dc2 & DT2 & DMT2 & DMt2 & Db2 & Hd2).
  destruct (mkrb_inj_MT Erba) as [<- <-]. pose proof (mkrb_inj_br Erba) as Eba.
  destruct (inv_elimt Hi Hx'') as (MT3 & Mt3 & bs3 & (Erb3 & _ & _ & W1'' & W2'' & Wl'' & HΔ'' & HMT'' & HMt''
                                   & Hbc'' & Hbs'' & HT'' & Hν'') & _ & _).
  destruct (mkrb_inj_MT Erb3) as [<- <-]. pose proof (mkrb_inj_br Erb3) as Eb3.
  trec_core IHT IHt IHb DMT DMt DMT2 DMt2 Db2 Eba.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec. pose proof (ac_ctx_sound' Dc2 HΔ' HΔ'') as Ec2.
  pose proof (cv_ty (ctx_glob _ _ _ HΔ) compt_D DT2 (eqctx_sym_D Ec) HT' (mvD (eqctx_sym_D Ec2) HT'')) as DT2'.
  eapply actmne_elimt_glob; [exact (leqv_trans _ _ _ H1 H1') | exact (leqv_trans _ _ _ H2 H2')
                            | exact (leqv_trans _ _ _ Hl Hl') | exact (IHc Δ'' HΔ HΔ' HΔ'' Dc2)
                            | exact (IHi T'' lD _ _ _ compt_D HT (mvD (eqctx_sym_D Ec) HT')
                                       (mvD (eqctx_sym_D (eqctx_trans_D Ec Ec2)) HT'') DT2')
                            | exact XMT | exact XMt | exact Xb | exact Hg | exact (tm_leq_trans _ _ _ Hd Hd2)].
Qed.

(** ** Transitivity *)

(** ** Dependent pairs (M8) *)

Lemma T_actnf_sig {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> T_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> T_ty G (Γ ,, A @ l1) B B' ->
  T_tynf G Γ (tySig l1 l2 A B) (tySig l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA DB IHB T'' i k k' k'' Hc HT HT' HT'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_sig D2) as (l5 & l6 & A'' & B'' & -> & H35 & H46 & DA2 & DB2).
  destruct (inv_ty_sig HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_sig HT') as ((_ & W3 & W4 & HA' & HB') & _).
  destruct (inv_ty_sig HT'') as ((_ & W5 & W6 & HA'' & HB'') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ac_ty_sound Hc DA2 HA' (wft_lconv _ _ _ _ _ _ HA'' E35)) as EA2.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (HΓA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA' | exact W3]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  assert (EA2' : [ G ; Γ ⊢[ i ] A'' ≅ A' @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA2) | exact (lequiv_sym _ _ _ E35)]).
  pose proof (lequiv_trans _ _ _ _ E13 E35) as E15.
  assert (EA'' : [ G ; Γ ⊢[ i ] A'' ≅ A @ l5 ]).
  { eapply eqty_lconv; [| exact (lequiv_sym _ _ _ E15)]. apply eqty_sym.
    eapply eqty_trans; [exact EA | exact (eqty_lconv _ _ _ _ _ _ _ EA2 E13)]. }
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  pose proof (stab_ty Hi EA2' (lequiv_sym _ _ _ E35) HΓA' HB'') as HB2'.
  pose proof (stab_ty Hi EA'' (lequiv_sym _ _ _ E15) HΓA HB'') as HB2.
  assert (Hctx : [ G ⊢[ i ] Γ ,, A' @ l3 ≅ Γ ,, A @ l1 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA' | exact EA' | exact (lequiv_sym _ _ _ E13)]).
  pose proof (cv_ty HG Hc DB2 Hctx HB' HB2') as DB2'.
  apply actnf_sig; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46)
                  | exact (IHA A'' i _ _ _ Hc HA HA' HA'' DA2) | exact (IHB B'' i _ _ _ Hc HB HB1 HB2 DB2')].
Qed.

Lemma code_sig_prem {G i Γ l l1 l2 s t k} : compt i -> [ G ; Γ ⊢[ i ] tmSig l1 l2 s t : tyU l @ k ] ->
  i <> lV /\ lwf (gL G) l1 /\ lwf (gL G) l2 /\ [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] /\
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t : tyU l2 @ lsuc l2 ].
Proof.
  intros Hc H. destruct (proj1 (inv_code_sig (compt_typeof_self _ Hc) H)) as (_ & W1 & W2 & Hs & Ht).
  exact (conj (compt_notV Hc) (conj W1 (conj W2 (conj Hs Ht)))).
Qed.
Lemma code_W_prem {G i Γ l l1 l2 s t k} : compt i -> [ G ; Γ ⊢[ i ] tmW l1 l2 s t : tyU l @ k ] ->
  i <> lV /\ lwf (gL G) l1 /\ lwf (gL G) l2 /\ [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] /\
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t : tyU l2 @ lsuc l2 ].
Proof.
  intros Hc H. destruct (proj1 (inv_code_W (compt_typeof_self _ Hc) H)) as (_ & W1 & W2 & Hs & Ht).
  exact (conj (compt_notV Hc) (conj W1 (conj W2 (conj Hs Ht)))).
Qed.

Lemma T_actmnf_code_sig {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> T_tm G Γ s s' (tyU l1) ->
  ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) -> T_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  T_tmnf G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs Dt IHt x'' i k Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_code_sig D2) as (l5 & l6 & s'' & t'' & -> & H35 & H46 & Ds2 & Dt2).
  destruct (code_sig_prem Hc Hx) as (Hv & W1 & W2 & Hs & Ht).
  destruct (code_sig_prem Hc Hx') as (_ & W3 & W4 & Hs' & Ht').
  destruct (code_sig_prem Hc Hx'') as (_ & W5 & W6 & Hs'' & Ht'').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35. pose proof (leqv_lequiv _ _ _ W4 W6 H46) as E46.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  (* the universes of the codes' domains *)
  assert (EU13 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (EU35 : [ G ; Γ ⊢[ i ] tyU l3 ≅ tyU l5 @ lsuc l3 ]) by (apply eqty_U; assumption).
  assert (EU15 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l5 @ lsuc l1 ])
    by (apply eqty_U; [exact Hv | exact HΓt | exact (lequiv_trans _ _ _ _ E13 E35)]).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU13]. }
  assert (Hs2 : [ G ; Γ ⊢[ i ] s'' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs'' | exact (lequiv_suc _ _ _ (lequiv_trans _ _ _ _ E13 E35))]
                    | rewrite Hi; exact EU15]. }
  assert (Hs2' : [ G ; Γ ⊢[ i ] s'' : tyU l3 @ lsuc l3 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs'' | exact (lequiv_suc _ _ _ E35)] | rewrite Hi; exact EU35]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  pose proof (ac_tm_sound Hc Ds2 Hs' Hs2') as Es2.
  (* the second's domain, at the first's universe *)
  pose proof (cv_tm HG Hc Ds2 (eqc_refl _ _ _ HΓ) Hs' Hs2'
                (eqty_lconv _ _ _ _ _ _ _ EU13 (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13)))) as Ds2'.
  (* the bodies' contexts *)
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' @ l3 ]) by (apply wft_El; assumption).
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; [exact Hv | exact E13 | exact Es]).
  assert (Es2u : [ G ; Γ ⊢[ i ] s' ≅ s'' : tyU l3 @ lsuc l3 ]) by exact Es2.
  assert (EEl2 : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l5 s'' @ l3 ]) by (apply eqty_El; [exact Hv | exact E35 | exact Es2u]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E13)]).
  assert (EEl'' : [ G ; Γ ⊢[ i ] tyEl l5 s'' ≅ tyEl l1 s @ l5 ]).
  { eapply eqty_lconv; [| exact (lequiv_sym _ _ _ (lequiv_trans _ _ _ _ E13 E35))]. apply eqty_sym.
    eapply eqty_trans; [exact EEl | exact (eqty_lconv _ _ _ _ _ _ _ EEl2 E13)]. }
  assert (EEl2' : [ G ; Γ ⊢[ i ] tyEl l5 s'' ≅ tyEl l3 s' @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl2) | exact (lequiv_sym _ _ _ E35)]).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  assert (HΓ3 : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl' | exact W3]).
  (* the bodies at the first's universe, in the first's context *)
  assert (Ht1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl' (lequiv_sym _ _ _ E13) HΓ1 Ht') |
                                       exact (lequiv_suc _ _ _ E24)] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]. }
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t'' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl'' (lequiv_sym _ _ _ (lequiv_trans _ _ _ _ E13 E35))
                                                HΓ1 Ht'') | exact (lequiv_suc _ _ _ (lequiv_trans _ _ _ _ E24 E46))] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact (lequiv_trans _ _ _ _ E24 E46)]. }
  assert (Ht2' : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] t'' : tyU l4 @ lsuc l4 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl2' (lequiv_sym _ _ _ E35) HΓ3 Ht'') |
                                       exact (lequiv_suc _ _ _ E46)] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ3 | exact E46]. }
  assert (Hctx : [ G ⊢[ i ] Γ ,, tyEl l3 s' @ l3 ≅ Γ ,, tyEl l1 s @ l1 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HEl' | exact EEl' | exact (lequiv_sym _ _ _ E13)]).
  assert (EU24 : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l4 ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ3 | exact E24] |].
    exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E24)). }
  pose proof (cv_tm HG Hc Dt2 Hctx Ht' Ht2' EU24) as Dt2'.
  apply actmnf_code_sig; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46) | |].
  - exact (IHs s'' i _ Hc Hs Hs1 Hs2 Ds2').
  - exact (IHt t'' i _ Hc Ht Ht1 Ht2 Dt2').
Qed.
Lemma T_actmnf_code_W {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> T_tm G Γ s s' (tyU l1) ->
  ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) -> T_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  T_tmnf G Γ (tmW l1 l2 s t) (tmW l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs Dt IHt x'' i k Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_code_W D2) as (l5 & l6 & s'' & t'' & -> & H35 & H46 & Ds2 & Dt2).
  destruct (code_W_prem Hc Hx) as (Hv & W1 & W2 & Hs & Ht).
  destruct (code_W_prem Hc Hx') as (_ & W3 & W4 & Hs' & Ht').
  destruct (code_W_prem Hc Hx'') as (_ & W5 & W6 & Hs'' & Ht'').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35. pose proof (leqv_lequiv _ _ _ W4 W6 H46) as E46.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  (* the universes of the codes' domains *)
  assert (EU13 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (EU35 : [ G ; Γ ⊢[ i ] tyU l3 ≅ tyU l5 @ lsuc l3 ]) by (apply eqty_U; assumption).
  assert (EU15 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l5 @ lsuc l1 ])
    by (apply eqty_U; [exact Hv | exact HΓt | exact (lequiv_trans _ _ _ _ E13 E35)]).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU13]. }
  assert (Hs2 : [ G ; Γ ⊢[ i ] s'' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs'' | exact (lequiv_suc _ _ _ (lequiv_trans _ _ _ _ E13 E35))]
                    | rewrite Hi; exact EU15]. }
  assert (Hs2' : [ G ; Γ ⊢[ i ] s'' : tyU l3 @ lsuc l3 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs'' | exact (lequiv_suc _ _ _ E35)] | rewrite Hi; exact EU35]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  pose proof (ac_tm_sound Hc Ds2 Hs' Hs2') as Es2.
  (* the second's domain, at the first's universe *)
  pose proof (cv_tm HG Hc Ds2 (eqc_refl _ _ _ HΓ) Hs' Hs2'
                (eqty_lconv _ _ _ _ _ _ _ EU13 (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13)))) as Ds2'.
  (* the bodies' contexts *)
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' @ l3 ]) by (apply wft_El; assumption).
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; [exact Hv | exact E13 | exact Es]).
  assert (Es2u : [ G ; Γ ⊢[ i ] s' ≅ s'' : tyU l3 @ lsuc l3 ]) by exact Es2.
  assert (EEl2 : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l5 s'' @ l3 ]) by (apply eqty_El; [exact Hv | exact E35 | exact Es2u]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E13)]).
  assert (EEl'' : [ G ; Γ ⊢[ i ] tyEl l5 s'' ≅ tyEl l1 s @ l5 ]).
  { eapply eqty_lconv; [| exact (lequiv_sym _ _ _ (lequiv_trans _ _ _ _ E13 E35))]. apply eqty_sym.
    eapply eqty_trans; [exact EEl | exact (eqty_lconv _ _ _ _ _ _ _ EEl2 E13)]. }
  assert (EEl2' : [ G ; Γ ⊢[ i ] tyEl l5 s'' ≅ tyEl l3 s' @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl2) | exact (lequiv_sym _ _ _ E35)]).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  assert (HΓ3 : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl' | exact W3]).
  (* the bodies at the first's universe, in the first's context *)
  assert (Ht1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl' (lequiv_sym _ _ _ E13) HΓ1 Ht') |
                                       exact (lequiv_suc _ _ _ E24)] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]. }
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t'' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl'' (lequiv_sym _ _ _ (lequiv_trans _ _ _ _ E13 E35))
                                                HΓ1 Ht'') | exact (lequiv_suc _ _ _ (lequiv_trans _ _ _ _ E24 E46))] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact (lequiv_trans _ _ _ _ E24 E46)]. }
  assert (Ht2' : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] t'' : tyU l4 @ lsuc l4 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl2' (lequiv_sym _ _ _ E35) HΓ3 Ht'') |
                                       exact (lequiv_suc _ _ _ E46)] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ3 | exact E46]. }
  assert (Hctx : [ G ⊢[ i ] Γ ,, tyEl l3 s' @ l3 ≅ Γ ,, tyEl l1 s @ l1 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HEl' | exact EEl' | exact (lequiv_sym _ _ _ E13)]).
  assert (EU24 : [ G ; Γ ,, tyEl l3 s' @ l3 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l4 ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ3 | exact E24] |].
    exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E24)). }
  pose proof (cv_tm HG Hc Dt2 Hctx Ht' Ht2' EU24) as Dt2'.
  apply actmnf_code_W; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46) | |].
  - exact (IHs s'' i _ Hc Hs Hs1 Hs2 Ds2').
  - exact (IHt t'' i _ Hc Ht Ht1 Ht2 Dt2').
Qed.

Lemma T_actmnf_sig_eta {G Γ l l' A B w w'} :
  ac_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w') A ->
  T_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w') A ->
  T_tm G Γ (tmSnd l l' A B w) (tmSnd l l' A B w') B[lsingle (tmFst l l' A B w)] ->
  T_tmnf G Γ w w' (tySig l l' A B).
Proof.
  intros D1 IH1 IH2 w'' i k Hc Hw Hw' Hw'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_sig_eta D2) as (D2f & D2s).
  destruct (inv_ty_sig (wf_tm_ty Hi Hw)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (lvl_eq_tm' Hk Hw'') as Hw1''.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1) as Hf.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1') as Hf'.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1'') as Hf''.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1) as Hs.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1') as Hs'.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1'') as Hs''.
  pose proof (ac_tm_sound Hc D1 Hf Hf') as E1. pose proof (ac_tm_sound Hc D2f Hf' Hf'') as E2.
  pose proof (sig_fam_eq Hi HB (eqty_refl _ _ _ _ _ HB) (eqtm_sym _ _ _ _ _ _ _ E1) Hf' Hf) as EB1.
  pose proof (sig_fam_eq Hi HB (eqty_refl _ _ _ _ _ HB) (eqtm_sym _ _ _ _ _ _ _ E2) Hf'' Hf') as EB2.
  assert (Hs1 : [ G ; Γ ⊢[ i ] tmSnd l l' A B w' : B[lsingle (tmFst l l' A B w)] @ l' ])
    by (eapply wf_conv; [exact Hs' | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EB1)]).
  assert (Hs2 : [ G ; Γ ⊢[ i ] tmSnd l l' A B w'' : B[lsingle (tmFst l l' A B w)] @ l' ])
    by (eapply wf_conv; [exact Hs'' | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ (eqty_trans _ _ _ _ _ _ _ EB2 EB1))]).
  assert (Hs2' : [ G ; Γ ⊢[ i ] tmSnd l l' A B w'' : B[lsingle (tmFst l l' A B w')] @ l' ])
    by (eapply wf_conv; [exact Hs'' | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EB2)]).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (cv_tm (ctx_glob _ _ _ HΓ) Hc D2s (eqc_refl _ _ _ HΓ) Hs' Hs2' (eqty_sym _ _ _ _ _ _ EB1)) as D2s'.
  apply actmnf_sig_eta; [exact (IH1 _ i l Hc Hf Hf' Hf'' D2f) | exact (IH2 _ i l' Hc Hs Hs1 Hs2 D2s')].
Qed.

Lemma T_actmne_fst {G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tySig m m' A0 B0) -> T_nee G Γ ν ν' (tySig m m' A0 B0) ->
  T_ne G Γ (tmFst l1 l2 A B ν) (tmFst l3 l4 A' B' ν') A0.
Proof.
  intros Dν IHν x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_fst D2) as (l5 & l6 & A'' & B'' & ν'' & m2 & m2' & A1 & B1 & -> & Dν2).
  destruct (inv_fst Hi Hx) as ((_ & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_fst Hi Hx') as ((_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (inv_fst Hi Hx'') as ((_ & _ & _ & _ & _ & Hν'') & _ & _).
  eapply actmne_fst. exact (IHν ν'' _ i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2).
Qed.

Lemma T_actmne_snd {G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tySig m m' A0 B0) -> T_nee G Γ ν ν' (tySig m m' A0 B0) ->
  T_ne G Γ (tmSnd l1 l2 A B ν) (tmSnd l3 l4 A' B' ν') B0[lsingle (tmFst m m' A0 B0 ν)].
Proof.
  intros Dν IHν x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_snd D2) as (l5 & l6 & A'' & B'' & ν'' & m2 & m2' & A1 & B1 & -> & Dν2).
  destruct (inv_snd Hi Hx) as ((_ & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_snd Hi Hx') as ((_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (inv_snd Hi Hx'') as ((_ & _ & _ & _ & _ & Hν'') & _ & _).
  eapply actmne_snd. exact (IHν ν'' _ i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2).
Qed.

(** The unit type (M8c). *)
Lemma T_actnf_unit {G Γ l l'} : leqv l l' -> T_tynf G Γ (tyUnit l) (tyUnit l').
Proof.
  intros Hl; red; intros * _ _ _ _ D2. destruct (ainv_unit D2) as (l'' & -> & Hl2).
  apply actnf_unit, (leqv_trans _ _ _ Hl Hl2).
Qed.
Lemma T_actmnf_code_unit {G Γ l k k'} : leqv k k' -> T_tmnf G Γ (tmUnit k) (tmUnit k') (tyU l).
Proof.
  intros Hl; red; intros * _ _ _ _ D2. destruct (ainv_code_unit D2) as (k'' & -> & Hl2).
  apply actmnf_code_unit, (leqv_trans _ _ _ Hl Hl2).
Qed.
(** The codes of [Empty] and [+] (M12c). *)
Lemma T_actmnf_code_empty {G Γ l k k'} : leqv k k' -> T_tmnf G Γ (tmEmpty k) (tmEmpty k') (tyU l).
Proof.
  intros Hl; red; intros * _ _ _ _ D2. destruct (ainv_code_empty D2) as (k'' & -> & Hl2).
  apply actmnf_code_empty, (leqv_trans _ _ _ Hl Hl2).
Qed.
Lemma T_actmnf_code_sum {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> T_tm G Γ s s' (tyU l1) -> ac_tm G Γ t t' (tyU l2) -> T_tm G Γ t t' (tyU l2) ->
  T_tmnf G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs Dt IHt x'' i m Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (ainv_code_sum D2) as (l5 & l6 & s'' & t'' & -> & H35 & H46 & Ds2 & Dt2).
  destruct (code_sum_prem Hc Hx) as (W1 & W2 & Hs & Ht).
  destruct (code_sum_prem Hc Hx') as (W3 & W4 & Hs' & Ht').
  destruct (code_sum_prem Hc Hx'') as (W5 & W6 & Hs'' & Ht'').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35. pose proof (leqv_lequiv _ _ _ W4 W6 H46) as E46.
  pose proof (lequiv_trans _ _ _ _ E13 E35) as E15. pose proof (lequiv_trans _ _ _ _ E24 E46) as E26.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l3 ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | exact E13]
                       | exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13))]. }
  assert (EU2 : [ G ; Γ ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l4 ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | exact E24]
                       | exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E24))]. }
  apply actmnf_code_sum; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46) | |].
  - exact (IHs s'' i _ Hc Hs (code_U_conv Hc E13 Hs') (code_U_conv Hc E15 Hs'')
             (cv_tm HG Hc Ds2 (eqc_refl _ _ _ HΓ) Hs' (code_U_conv Hc E35 Hs'') EU1)).
  - exact (IHt t'' i _ Hc Ht (code_U_conv Hc E24 Ht') (code_U_conv Hc E26 Ht'')
             (cv_tm HG Hc Dt2 (eqc_refl _ _ _ HΓ) Ht' (code_U_conv Hc E46 Ht'') EU2)).
Qed.

Lemma T_actmnf_code_sempty {G Γ l k k'} : leqv k k' -> T_tmnf G Γ (tmSEmpty k) (tmSEmpty k') (tyU l).
Proof.
  intros Hl; red; intros * _ _ _ _ D2. destruct (ainv_code_sempty D2) as (k'' & -> & Hl2).
  apply actmnf_code_sempty, (leqv_trans _ _ _ Hl Hl2).
Qed.
Lemma T_actmnf_unit_eta {G Γ l w w'} : T_tmnf G Γ w w' (tyUnit l).
Proof. red; intros; apply actmnf_unit_eta. Qed.

(** Strict equality (M10a). *)
Lemma T_actnf_seq {G Γ l l' A A' a a' b b'} : leqv l l' ->
  ac_ty G Γ A A' -> T_ty G Γ A A' -> ac_tm G Γ a a' A -> T_tm G Γ a a' A ->
  ac_tm G Γ b b' A -> T_tm G Γ b b' A -> T_tynf G Γ (tySEq l A a b) (tySEq l' A' a' b').
Proof.
  intros Hl DA IHA Da IHa Db IHb; red; intros T'' i k k' k'' Hc HT HT' HT'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_seq D2) as (l'' & A'' & a'' & b'' & -> & Hl2 & DA2 & Da2 & Db2).
  destruct (inv_ty_seq HT) as ((_ & W & HA & Ha & Hb) & _).
  destruct (inv_ty_seq HT') as ((_ & W' & HA' & Ha' & Hb') & _).
  destruct (inv_ty_seq HT'') as ((_ & W'' & HA'' & Ha'' & Hb'') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E. pose proof (leqv_lequiv _ _ _ W' W'' Hl2) as E2.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  pose proof (ac_ty_sound Hc DA2 HA' (wft_lconv _ _ _ _ _ _ HA'' E2)) as EA2.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  (* [A] and [A'] at [l'] *)
  assert (EA1 : [ G ; Γ ⊢[ i ] A ≅ A' @ l' ])
    by (eapply eqty_lconv; [exact EA | exact (lequiv_sym _ _ _ E)]).
  assert (F1 : forall x, [ G ; Γ ⊢[ i ] x : A' @ l' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EA]. }
  assert (F2 : forall x, [ G ; Γ ⊢[ i ] x : A'' @ l'' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. apply F1. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E2) | rewrite Hi; exact EA2]. }
  assert (G1 : forall x, [ G ; Γ ⊢[ i ] x : A'' @ l'' ] -> [ G ; Γ ⊢[ i ] x : A' @ l' ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E2) | rewrite Hi; exact EA2]. }
  apply actnf_seq; [exact (leqv_trans _ _ _ Hl Hl2) | exact (IHA A'' i l l' l'' Hc HA HA' HA'' DA2) | |].
  - apply (IHa a'' i l Hc Ha (F1 _ Ha') (F2 _ Ha'')).
    exact (cv_tm (ctx_glob _ _ _ HΓ) Hc Da2 (eqc_refl _ _ _ HΓ) Ha' (G1 _ Ha'') EA1).
  - apply (IHb b'' i l Hc Hb (F1 _ Hb') (F2 _ Hb'')).
    exact (cv_tm (ctx_glob _ _ _ HΓ) Hc Db2 (eqc_refl _ _ _ HΓ) Hb' (G1 _ Hb'') EA1).
Qed.
(** The identity type (M11a). *)
Lemma T_actnf_id {G Γ l l' A A' a a' b b'} : leqv l l' ->
  ac_ty G Γ A A' -> T_ty G Γ A A' -> ac_tm G Γ a a' A -> T_tm G Γ a a' A ->
  ac_tm G Γ b b' A -> T_tm G Γ b b' A -> T_tynf G Γ (tyId l A a b) (tyId l' A' a' b').
Proof.
  intros Hl DA IHA Da IHa Db IHb; red; intros T'' i k k' k'' Hc HT HT' HT'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_id D2) as (l'' & A'' & a'' & b'' & -> & Hl2 & DA2 & Da2 & Db2).
  destruct (inv_ty_id HT) as ((_ & W & HA & Ha & Hb) & _).
  destruct (inv_ty_id HT') as ((_ & W' & HA' & Ha' & Hb') & _).
  destruct (inv_ty_id HT'') as ((_ & W'' & HA'' & Ha'' & Hb'') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E. pose proof (leqv_lequiv _ _ _ W' W'' Hl2) as E2.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  pose proof (ac_ty_sound Hc DA2 HA' (wft_lconv _ _ _ _ _ _ HA'' E2)) as EA2.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (EA1 : [ G ; Γ ⊢[ i ] A ≅ A' @ l' ])
    by (eapply eqty_lconv; [exact EA | exact (lequiv_sym _ _ _ E)]).
  assert (F1 : forall x, [ G ; Γ ⊢[ i ] x : A' @ l' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EA]. }
  assert (F2 : forall x, [ G ; Γ ⊢[ i ] x : A'' @ l'' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. apply F1. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E2) | rewrite Hi; exact EA2]. }
  assert (G1 : forall x, [ G ; Γ ⊢[ i ] x : A'' @ l'' ] -> [ G ; Γ ⊢[ i ] x : A' @ l' ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E2) | rewrite Hi; exact EA2]. }
  apply actnf_id; [exact (leqv_trans _ _ _ Hl Hl2) | exact (IHA A'' i l l' l'' Hc HA HA' HA'' DA2) | |].
  - apply (IHa a'' i l Hc Ha (F1 _ Ha') (F2 _ Ha'')).
    exact (cv_tm (ctx_glob _ _ _ HΓ) Hc Da2 (eqc_refl _ _ _ HΓ) Ha' (G1 _ Ha'') EA1).
  - apply (IHb b'' i l Hc Hb (F1 _ Hb') (F2 _ Hb'')).
    exact (cv_tm (ctx_glob _ _ _ HΓ) Hc Db2 (eqc_refl _ _ _ HΓ) Hb' (G1 _ Hb'') EA1).
Qed.
Lemma T_actmnf_refl {G Γ l A a b k k' C C' c c'} : T_tmnf G Γ (tmRefl k C c) (tmRefl k' C' c') (tyId l A a b).
Proof. red; intros * _ _ _ _ D2. destruct (ainv_refl D2) as (? & ? & ? & ->). apply actmnf_refl. Qed.
Lemma T_actmne_J {G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> T_ty G Γ A A' -> ac_tm G Γ a a' A -> T_tm G Γ a a' A ->
  ac_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  T_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  ac_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] -> T_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] ->
  ac_tm G Γ u u' A -> T_tm G Γ u u' A -> T_nee G Γ ν ν' W ->
  T_ne G Γ (tmJ l1 l2 A a M c u ν) (tmJ l3 l4 A' a' M' c' u' ν') M[lsingle2 u ν].
Proof.
  intros H13 H24 DA IHA Da IHa DM IHM Dc IHc Du IHu IHν x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi. assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (ainv_J D2) as (l5 & l6 & A'' & a'' & M'' & c'' & u'' & ν'' & W2 & -> & H35 & H46 & DA2 & Da2 & DM2
                           & Dc2 & Du2 & Dν2).
  destruct (inv_J Hi Hx) as ((_ & W1 & W2' & HA & Ha & HI & HM & Hcc & Hu & He) & _ & _).
  destruct (inv_J Hi Hx') as ((_ & W3 & W4 & HA' & Ha' & HI' & HM' & Hc' & Hu' & He') & _ & _).
  destruct (inv_J Hi Hx'') as ((_ & W5 & W6 & HA'' & Ha'' & HI'' & HM'' & Hc'' & Hu'' & He'') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2' W4 H24) as E24.
  pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35. pose proof (leqv_lequiv _ _ _ W4 W6 H46) as E46.
  pose proof (lequiv_trans _ _ _ _ E13 E35) as E15. pose proof (lequiv_trans _ _ _ _ E24 E46) as E26.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  (* the carriers and the points, at the first's *)
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ac_ty_sound Hc DA2 HA' (wft_lconv _ _ _ _ _ _ HA'' E35)) as EA2.
  assert (EA02 : [ G ; Γ ⊢[ i ] A ≅ A'' @ l1 ])
    by (eapply eqty_trans; [exact EA | exact (eqty_lconv _ _ _ _ _ _ _ EA2 E13)]).
  assert (EA1 : [ G ; Γ ⊢[ i ] A ≅ A' @ l3 ])
    by (eapply eqty_lconv; [exact EA | exact (lequiv_sym _ _ _ E13)]).
  assert (G1 : forall y, [ G ; Γ ⊢[ i ] y : A'' @ l5 ] -> [ G ; Γ ⊢[ i ] y : A' @ l3 ]).
  { intros y Hy. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hy E35) | rewrite Hi; exact EA2]. }
  assert (F1 : forall y, [ G ; Γ ⊢[ i ] y : A' @ l3 ] -> [ G ; Γ ⊢[ i ] y : A @ l1 ]).
  { intros y Hy. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hy E13) | rewrite Hi; exact EA]. }
  pose proof (F1 _ Ha') as Ha'1. pose proof (F1 _ (G1 _ Ha'')) as Ha''1.
  pose proof (ac_tm_sound Hc Da Ha Ha'1) as Ea.
  pose proof (ac_tm_sound Hc Da2 Ha' (G1 _ Ha'')) as Ea2.
  assert (Ea02 : [ G ; Γ ⊢[ i ] a ≅ a'' : A @ l1 ]).
  { eapply eqtm_trans; [exact Ea|]. eapply eqtm_conv; [exact (eqtm_lconv _ _ _ _ _ _ _ _ Ea2 E13) | rewrite Hi; exact EA]. }
  (* the motives, in the first's context *)
  pose proof (J_ctx_conv Hi Hc E13 HA HA' EA Ea) as Hid1.
  pose proof (J_ctx_conv Hi Hc E15 HA HA'' EA02 Ea02) as Hid2.
  pose proof (J_ctx_conv Hi Hc E35 HA' HA'' EA2 Ea2) as Hid12.
  pose proof (wf_ty_subst Hi HM' Hid1) as HM'1. rewrite nf_id_ty in HM'1 by exact (wf_ty_nf HM').
  apply (fun H => wft_lconv _ _ _ _ _ _ H E24) in HM'1.
  pose proof (wf_ty_subst Hi HM'' Hid2) as HM''1. rewrite nf_id_ty in HM''1 by exact (wf_ty_nf HM'').
  apply (fun H => wft_lconv _ _ _ _ _ _ H E26) in HM''1.
  pose proof (wf_ty_subst Hi HM'' Hid12) as HM''m. rewrite nf_id_ty in HM''m by exact (wf_ty_nf HM'').
  apply (fun H => wft_lconv _ _ _ _ _ _ H E46) in HM''m.
  assert (Hctx : [ G ⊢[ i ] Γ ,, A' @ l3 ,, tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3
                            ≅ Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ]).
  { apply (J_ctx_eq Hi Hv (lequiv_sym _ _ _ E13) HA' (eqty_sym _ _ _ _ _ _ EA1)).
    eapply eqtm_lconv; [|exact (lequiv_sym _ _ _ E13)].
    eapply eqtm_conv; [apply eqtm_sym, Ea | rewrite Hi; apply eqty_sym, EA]. }
  pose proof (cv_ty HG Hc DM2 Hctx HM' HM''m) as DM2'.
  pose proof (ac_ty_sound Hc DM HM HM'1) as EM.
  pose proof (ac_ty_sound Hc DM2 HM' HM''m) as EM2.
  pose proof (eqty_subst Hi EM2 Hid1) as EM2'. rewrite !nf_id_ty in EM2' by first [exact (wf_ty_nf HM') | exact (wf_ty_nf HM'')].
  assert (EM02 : [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M ≅ M'' @ l2 ])
    by (eapply eqty_trans; [exact EM | exact (eqty_lconv _ _ _ _ _ _ _ EM2' E24)]).
  (* the base cases, at the first's instance *)
  assert (Hr : [ G ; Γ ⊢[ i ] tmRefl l1 A a : tyId l1 A a a @ l1 ]) by (apply wf_idrefl; auto).
  pose proof (pre_idrefl_r Hi Hv E13 HA EA (eqty_wf_r Hi EA) Ea Ha'1) as Hr'.
  pose proof (pre_idrefl_r Hi Hv E15 HA EA02 (eqty_wf_r Hi EA02) Ea02 Ha''1) as Hr''.
  assert (Hrr : [ G ; Γ ⊢[ i ] tmRefl l1 A a ≅ tmRefl l3 A' a' : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; auto).
  assert (Hrr2 : [ G ; Γ ⊢[ i ] tmRefl l1 A a ≅ tmRefl l5 A'' a'' : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; auto).
  pose proof (lsub_eq_J Hi Hv W1 HA Ha Ha Ha'1 Ea Hr Hr' Hrr) as Hs.
  pose proof (lsub_eq_J Hi Hv W1 HA Ha Ha Ha''1 Ea02 Hr Hr'' Hrr2) as Hs2.
  assert (HMs : [ G ; Γ ⊢[ i ] M[lsingle2 a (tmRefl l1 A a)] ≅ M'[lsingle2 a' (tmRefl l3 A' a')] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi EM (lsub_eq_l Hs)) | exact (wf_ty_func Hi HM'1 Hs)]. }
  assert (HMs2 : [ G ; Γ ⊢[ i ] M[lsingle2 a (tmRefl l1 A a)] ≅ M''[lsingle2 a'' (tmRefl l5 A'' a'')] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi EM02 (lsub_eq_l Hs2)) | exact (wf_ty_func Hi HM''1 Hs2)]. }
  assert (Hc'1 : [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc' E24) | rewrite Hi; exact HMs]. }
  assert (Hc''1 : [ G ; Γ ⊢[ i ] c'' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc'' E26) | rewrite Hi; exact HMs2]. }
  assert (HMs12 : [ G ; Γ ⊢[ i ] M'[lsingle2 a' (tmRefl l3 A' a')] ≅ M''[lsingle2 a'' (tmRefl l5 A'' a'')] @ l4 ]).
  { eapply eqty_lconv; [|exact (lequiv_sym _ _ _ E24)].
    eapply eqty_trans; [apply eqty_sym, HMs | exact HMs2]. }
  assert (Hc''m : [ G ; Γ ⊢[ i ] c'' : M'[lsingle2 a' (tmRefl l3 A' a')] @ l4 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc'' E46) | rewrite Hi; exact HMs12]. }
  assert (HMs1 : [ G ; Γ ⊢[ i ] M[lsingle2 a (tmRefl l1 A a)] ≅ M'[lsingle2 a' (tmRefl l3 A' a')] @ l4 ])
    by (eapply eqty_lconv; [exact HMs | exact (lequiv_sym _ _ _ E24)]).
  pose proof (cv_tm HG Hc Dc2 (eqc_refl _ _ _ HΓ) Hc' Hc''m HMs1) as Dc2'.
  eapply actmne_J; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46) | | | | | |].
  - exact (IHA A'' i _ _ _ Hc HA HA' HA'' DA2).
  - apply (IHa a'' i l1 Hc Ha Ha'1 Ha''1).
    exact (cv_tm HG Hc Da2 (eqc_refl _ _ _ HΓ) Ha' (G1 _ Ha'') EA1).
  - exact (IHM M'' i _ _ _ Hc HM HM'1 HM''1 DM2').
  - exact (IHc c'' i l2 Hc Hcc Hc'1 Hc''1 Dc2').
  - apply (IHu u'' i l1 Hc Hu (F1 _ Hu') (F1 _ (G1 _ Hu''))).
    exact (cv_tm HG Hc Du2 (eqc_refl _ _ _ HΓ) Hu' (G1 _ Hu'') EA1).
  - exact (IHν ν'' W2 i _ _ _ _ _ _ Hc He He' He'' Dν2).
Qed.

Lemma T_actmnf_code_id {G Γ l k k' s s' t t' u u'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> T_tm G Γ s s' (tyU k) ->
  ac_tm G Γ t t' (tyEl k s) -> T_tm G Γ t t' (tyEl k s) ->
  ac_tm G Γ u u' (tyEl k s) -> T_tm G Γ u u' (tyEl k s) ->
  T_tmnf G Γ (tmId k s t u) (tmId k' s' t' u') (tyU l).
Proof.
  intros Hk0 Ds IHs Dt IHt Du IHu x'' i m Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (ainv_code_id D2) as (k'' & s'' & t'' & u'' & -> & Hk2 & Ds2 & Dt2 & Du2).
  destruct (code_id_prem Hc Hx) as (W & Hs & Ht & Hu).
  destruct (code_id_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  destruct (code_id_prem Hc Hx'') as (W'' & Hs'' & Ht'' & Hu'').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E. pose proof (leqv_lequiv _ _ _ W' W'' Hk2) as E2.
  pose proof (lequiv_trans _ _ _ _ E E2) as E02.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (code_U_conv Hc E Hs') as Hs1. pose proof (code_U_conv Hc E02 Hs'') as Hs2.
  pose proof (code_U_conv Hc E2 Hs'') as Hs2'.
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es. pose proof (ac_tm_sound Hc Ds2 Hs' Hs2') as Es2.
  destruct (code_El_conv Hc E Es) as (F1 & EEl). destruct (code_El_conv Hc E2 Es2) as (F2 & _).
  assert (EU : [ G ; Γ ⊢[ i ] tyU k ≅ tyU k' @ lsuc k' ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | exact E]
                       | exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E))]. }
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl k s ≅ tyEl k' s' @ k' ])
    by (eapply eqty_lconv; [exact EEl | exact (lequiv_sym _ _ _ E)]).
  apply actmnf_code_id; [exact (leqv_trans _ _ _ Hk0 Hk2) | | |].
  - exact (IHs s'' i _ Hc Hs Hs1 Hs2 (cv_tm HG Hc Ds2 (eqc_refl _ _ _ HΓ) Hs' Hs2' EU)).
  - exact (IHt t'' i _ Hc Ht (F1 _ Ht') (F1 _ (F2 _ Ht''))
             (cv_tm HG Hc Dt2 (eqc_refl _ _ _ HΓ) Ht' (F2 _ Ht'') EEl')).
  - exact (IHu u'' i _ Hc Hu (F1 _ Hu') (F1 _ (F2 _ Hu''))
             (cv_tm HG Hc Du2 (eqc_refl _ _ _ HΓ) Hu' (F2 _ Hu'') EEl')).
Qed.
Lemma T_actmnf_code_seq {G Γ l k k' s s' t t' u u'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> T_tm G Γ s s' (tyU k) ->
  ac_tm G Γ t t' (tyEl k s) -> T_tm G Γ t t' (tyEl k s) ->
  ac_tm G Γ u u' (tyEl k s) -> T_tm G Γ u u' (tyEl k s) ->
  T_tmnf G Γ (tmSEq k s t u) (tmSEq k' s' t' u') (tyU l).
Proof.
  intros Hk0 Ds IHs Dt IHt Du IHu x'' i m Hc Hx Hx' Hx'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (ainv_code_seq D2) as (k'' & s'' & t'' & u'' & -> & Hk2 & Ds2 & Dt2 & Du2).
  destruct (code_seq_prem Hc Hx) as (W & Hs & Ht & Hu).
  destruct (code_seq_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  destruct (code_seq_prem Hc Hx'') as (W'' & Hs'' & Ht'' & Hu'').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E. pose proof (leqv_lequiv _ _ _ W' W'' Hk2) as E2.
  pose proof (lequiv_trans _ _ _ _ E E2) as E02.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (code_U_conv Hc E Hs') as Hs1. pose proof (code_U_conv Hc E02 Hs'') as Hs2.
  pose proof (code_U_conv Hc E2 Hs'') as Hs2'.
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es. pose proof (ac_tm_sound Hc Ds2 Hs' Hs2') as Es2.
  destruct (code_El_conv Hc E Es) as (F1 & EEl). destruct (code_El_conv Hc E2 Es2) as (F2 & _).
  assert (EU : [ G ; Γ ⊢[ i ] tyU k ≅ tyU k' @ lsuc k' ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | exact E]
                       | exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E))]. }
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl k s ≅ tyEl k' s' @ k' ])
    by (eapply eqty_lconv; [exact EEl | exact (lequiv_sym _ _ _ E)]).
  apply actmnf_code_seq; [exact (leqv_trans _ _ _ Hk0 Hk2) | | |].
  - exact (IHs s'' i _ Hc Hs Hs1 Hs2 (cv_tm HG Hc Ds2 (eqc_refl _ _ _ HΓ) Hs' Hs2' EU)).
  - exact (IHt t'' i _ Hc Ht (F1 _ Ht') (F1 _ (F2 _ Ht''))
             (cv_tm HG Hc Dt2 (eqc_refl _ _ _ HΓ) Ht' (F2 _ Ht'') EEl')).
  - exact (IHu u'' i _ Hc Hu (F1 _ Hu') (F1 _ (F2 _ Hu''))
             (cv_tm HG Hc Du2 (eqc_refl _ _ _ HΓ) Hu' (F2 _ Hu'') EEl')).
Qed.

Lemma T_actnf_sempty {G Γ l l'} : leqv l l' -> T_tynf G Γ (tySEmpty l) (tySEmpty l').
Proof.
  intros Hl; red; intros * _ _ _ _ D2. destruct (ainv_sempty D2) as (l'' & -> & Hl2).
  apply actnf_sempty, (leqv_trans _ _ _ Hl Hl2).
Qed.
(** The empty type (M12a). *)
Lemma T_actnf_empty {G Γ l l'} : leqv l l' -> T_tynf G Γ (tyEmpty l) (tyEmpty l').
Proof.
  intros Hl; red; intros * _ _ _ _ D2. destruct (ainv_empty D2) as (l'' & -> & Hl2).
  apply actnf_empty, (leqv_trans _ _ _ Hl Hl2).
Qed.

Lemma T_actmne_elimEmpty {G Γ l1 l2 l3 l4 M M' ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G (Γ ,, tyEmpty l2 @ l2) M M' -> T_ty G (Γ ,, tyEmpty l2 @ l2) M M' -> T_nee G Γ ν ν' W ->
  T_ne G Γ (elimEmpty l1 l2 M ν) (elimEmpty l3 l4 M' ν') M[lsingle ν].
Proof.
  intros H13 H24 DM IHM IHν x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_elimEmpty D2) as (l5 & l6 & M'' & ν'' & Wν & -> & H35 & H46 & DM2 & Dν2).
  destruct (inv_elimEmpty Hi Hx) as ((_ & W1 & W2 & HM & Hν) & _ & _).
  destruct (inv_elimEmpty Hi Hx') as ((_ & W3 & W4 & HM' & Hν') & _ & _).
  destruct (inv_elimEmpty Hi Hx'') as ((_ & W5 & W6 & HM'' & Hν'') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35. pose proof (leqv_lequiv _ _ _ W4 W6 H46) as E46.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  (* moving the motives between the three contexts *)
  assert (St : forall a b T k0, lwf (gL G) b -> lequiv (gL G) a b ->
            [ G ; Γ ,, tyEmpty a @ a ⊢[ i ] T @ k0 ] -> [ G ; Γ ,, tyEmpty b @ b ⊢[ i ] T @ k0 ]).
  { intros a b T k0 Wb Eab HT. refine (stab_ty Hi _ Eab _ HT).
    - apply eqty_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact Eab].
    - apply wfc_ext; [exact HΓ | apply wft_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact Wb] | exact Wb]. }
  assert (Cx : forall a b, lwf (gL G) a -> lequiv (gL G) a b ->
            [ G ⊢[ i ] Γ ,, tyEmpty a @ a ≅ Γ ,, tyEmpty b @ b ]).
  { intros a b Wa Eab. apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | apply wft_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact Wa]
                                      | apply eqty_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact Eab] | exact Eab]. }
  pose proof (St _ _ _ _ W2 (lequiv_sym _ _ _ E24) HM') as HM'1.
  pose proof (St _ _ _ _ W2 (lequiv_sym _ _ _ (lequiv_trans _ _ _ _ E24 E46)) HM'') as HM''1.
  pose proof (St _ _ _ _ W4 (lequiv_sym _ _ _ E46) HM'') as HM''4.
  pose proof (cv_ty HG Hc DM2 (Cx _ _ W4 (lequiv_sym _ _ _ E24)) HM' HM''4) as DM2'.
  eapply actmne_elimEmpty; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46) | |].
  - exact (IHM M'' i _ _ _ Hc HM HM'1 HM''1 DM2').
  - exact (IHν ν'' Wν i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2).
Qed.

(** Binary sums (M12b). The second comparison is at the middle side's
    contexts: its motive and branches move to the left side's. *)
Lemma T_actnf_sum {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  T_ty G Γ A A' -> T_ty G Γ B B' -> T_tynf G Γ (tySum l1 l2 A B) (tySum l3 l4 A' B').
Proof.
  intros H13 H24 IHA IHB T'' i k k' k'' Hc HT HT' HT'' D2.
  destruct (ainv_sum D2) as (l5 & l6 & A'' & B'' & -> & H35 & H46 & DA2 & DB2).
  destruct (inv_ty_sum HT) as ((_ & _ & _ & HA & HB) & _).
  destruct (inv_ty_sum HT') as ((_ & _ & _ & HA' & HB') & _).
  destruct (inv_ty_sum HT'') as ((_ & _ & _ & HA'' & HB'') & _).
  apply actnf_sum; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46)
                   | exact (IHA A'' i _ _ _ Hc HA HA' HA'' DA2) | exact (IHB B'' i _ _ _ Hc HB HB' HB'' DB2)].
Qed.
Lemma T_actmnf_inl {G Γ l l' A B k1 k2 k3 k4 C D C' D' a a'} : T_tm G Γ a a' A ->
  T_tmnf G Γ (tmInl k1 k2 C D a) (tmInl k3 k4 C' D' a') (tySum l l' A B).
Proof.
  intros IHa t'' i k Hc Ht Ht' Ht'' D2. destruct (ainv_inl D2) as (k5 & k6 & C'' & D'' & a'' & -> & Da2).
  apply actmnf_inl, (IHa a'' i l Hc (inl_payload Hc Ht) (inl_payload Hc Ht') (inl_payload Hc Ht'') Da2).
Qed.
Lemma T_actmnf_inr {G Γ l l' A B k1 k2 k3 k4 C D C' D' b b'} : T_tm G Γ b b' B ->
  T_tmnf G Γ (tmInr k1 k2 C D b) (tmInr k3 k4 C' D' b') (tySum l l' A B).
Proof.
  intros IHb t'' i k Hc Ht Ht' Ht'' D2. destruct (ainv_inr D2) as (k5 & k6 & C'' & D'' & b'' & -> & Db2).
  apply actmnf_inr, (IHb b'' i l' Hc (inr_payload Hc Ht) (inr_payload Hc Ht') (inr_payload Hc Ht'') Db2).
Qed.

Lemma T_actmne_case {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' ν ν' W} :
  leqv l1 l4 -> leqv l2 l5 -> leqv l3 l6 ->
  ac_ty G Γ A A' -> T_ty G Γ A A' -> ac_ty G Γ B B' -> T_ty G Γ B B' ->
  ac_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' -> T_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' ->
  T_tm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] -> T_tm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] -> T_nee G Γ ν ν' W ->
  T_ne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) (tmCase l4 l5 l6 A' B' M' c1' c2' ν') M[lsingle ν].
Proof.
  intros H14 H25 H36 DA IHA DB IHB DM IHM IHc1 IHc2 IHν x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_case D2) as (l7 & l8 & l9 & A'' & B'' & M'' & c1'' & c2'' & ν'' & Wν & -> & H47 & H58 & H69
                              & DA2 & DB2 & DM2 & Dc12 & Dc22 & Dν2).
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Hν) & _ & _).
  destruct (inv_case Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & Hc1' & Hc2' & Hν') & _ & _).
  destruct (inv_case Hi Hx'') as ((_ & W7 & W8 & W9 & HA'' & HB'' & HM'' & Hc1'' & Hc2'' & Hν'') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W4 H14) as E14. pose proof (leqv_lequiv _ _ _ W2 W5 H25) as E25.
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  pose proof (leqv_lequiv _ _ _ W4 W7 H47) as E47. pose proof (leqv_lequiv _ _ _ W5 W8 H58) as E58.
  pose proof (leqv_lequiv _ _ _ W6 W9 H69) as E69.
  pose proof (lequiv_trans _ _ _ _ E14 E47) as E17. pose proof (lequiv_trans _ _ _ _ E25 E58) as E28.
  pose proof (lequiv_trans _ _ _ _ E36 E69) as E39.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  (* the summands, pairwise *)
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E14)) as EA.
  pose proof (ac_ty_sound Hc DB HB (wft_lconv _ _ _ _ _ _ HB' E25)) as EB.
  pose proof (ac_ty_sound Hc DA2 HA' (wft_lconv _ _ _ _ _ _ HA'' E47)) as EA2.
  pose proof (ac_ty_sound Hc DB2 HB' (wft_lconv _ _ _ _ _ _ HB'' E58)) as EB2.
  assert (EA13 : [ G ; Γ ⊢[ i ] A ≅ A'' @ l1 ])
    by (eapply eqty_trans; [exact EA | exact (eqty_lconv _ _ _ _ _ _ _ EA2 E14)]).
  assert (EB13 : [ G ; Γ ⊢[ i ] B ≅ B'' @ l2 ])
    by (eapply eqty_trans; [exact EB | exact (eqty_lconv _ _ _ _ _ _ _ EB2 E25)]).
  (* the other sides' premises at the left's (and the middle's) contexts *)
  destruct (case_right_left (M := M) (c1' := c1') (c2' := c2') (ν' := ν') Hc E14 E25 E36 HA HB HA' HB' EA EB HM')
    as [HM'3 Hbr12].
  destruct (case_right_left (M := M') (c1' := c1'') (c2' := c2'') (ν' := ν'') Hc E47 E58 E69 HA' HB' HA'' HB''
              EA2 EB2 HM'') as [HM''6 Hbr23].
  destruct (case_right_left (M := M) (c1' := c1'') (c2' := c2'') (ν' := ν'') Hc E17 E28 E39 HA HB HA'' HB''
              EA13 EB13 HM'') as [HM''3 Hbr13].
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  destruct (Hbr12 HM EM Hc1' Hc2' Hν') as (EBA & EBB & Hc1'2 & Hc2'2 & _).
  pose proof (ac_ty_sound Hc DM2 HM' HM''6) as EM2.
  destruct (Hbr23 HM' EM2 Hc1'' Hc2'' Hν'') as (_ & _ & Hc1''6 & Hc2''6 & _).
  (* the middle's contexts, converted to the left's *)
  assert (HS' : [ G ; Γ ⊢[ i ] tySum l4 l5 A' B' @ lmax l4 l5 ]) by (apply wft_sum; [now apply compt_notV | ..]; assumption).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | now apply lequiv_sym]).
  assert (EB' : [ G ; Γ ⊢[ i ] B' ≅ B @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EB) | now apply lequiv_sym]).
  assert (HctxS : [ G ⊢[ i ] Γ ,, tySum l4 l5 A' B' @ lmax l4 l5 ≅ Γ ,, tySum l1 l2 A B @ lmax l1 l2 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HS'
                       | apply eqty_sum; [now apply compt_notV | now apply lequiv_sym | now apply lequiv_sym | exact EA' | exact EB']
                       | apply lequiv_max; now apply lequiv_sym]).
  assert (HctxA : [ G ⊢[ i ] Γ ,, A' @ l4 ≅ Γ ,, A @ l1 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA' | exact EA' | now apply lequiv_sym]).
  assert (HctxB : [ G ⊢[ i ] Γ ,, B' @ l5 ≅ Γ ,, B @ l2 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HB' | exact EB' | now apply lequiv_sym]).
  pose proof (IHM M'' i _ _ _ Hc HM HM'3 HM''3 (cv_ty HG Hc DM2 HctxS HM' HM''6)) as XM.
  pose proof (ac_ty_sound Hc XM HM HM''3) as EM13.
  destruct (Hbr13 HM EM13 Hc1'' Hc2'' Hν'') as (_ & _ & Hc1''2 & Hc2''2 & _).
  (* the second comparison's branches, at the left's contexts and branch types *)
  assert (Dc12' : ac_tm G (Γ ,, A @ l1) c1' c1'' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))]).
  { pose proof (cv_tm HG Hc Dc12 HctxA Hc1' Hc1''6 (eqty_refl _ _ _ _ _ (wf_tm_ty Hi Hc1'))) as Y.
    pose proof (eqty_sym _ _ _ _ _ _ EBA) as EBA'.
    refine (cv_tm HG Hc Y (eqc_refl _ _ _ (ctx_of_wf_tm Hi Hc1)) _ _ EBA).
    - eapply wf_conv; [exact Hc1'2 | rewrite Hi; exact EBA'].
    - eapply wf_conv; [exact Hc1''2 | rewrite Hi; exact EBA']. }
  assert (Dc22' : ac_tm G (Γ ,, B @ l2) c2' c2'' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))]).
  { pose proof (cv_tm HG Hc Dc22 HctxB Hc2' Hc2''6 (eqty_refl _ _ _ _ _ (wf_tm_ty Hi Hc2'))) as Y.
    pose proof (eqty_sym _ _ _ _ _ _ EBB) as EBB'.
    refine (cv_tm HG Hc Y (eqc_refl _ _ _ (ctx_of_wf_tm Hi Hc2)) _ _ EBB).
    - eapply wf_conv; [exact Hc2'2 | rewrite Hi; exact EBB'].
    - eapply wf_conv; [exact Hc2''2 | rewrite Hi; exact EBB']. }
  eapply actmne_case; [exact (leqv_trans _ _ _ H14 H47) | exact (leqv_trans _ _ _ H25 H58)
                      | exact (leqv_trans _ _ _ H36 H69) | | | | | | ].
  - exact (IHA A'' i _ _ _ Hc HA HA' HA'' DA2).
  - exact (IHB B'' i _ _ _ Hc HB HB' HB'' DB2).
  - exact XM.
  - exact (IHc1 c1'' i l3 Hc Hc1 Hc1'2 Hc1''2 Dc12').
  - exact (IHc2 c2'' i l3 Hc Hc2 Hc2'2 Hc2''2 Dc22').
  - exact (IHν ν'' Wν i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2).
Qed.

(** Well-founded trees (M13a). As for [case], the second comparison's step
    moves from the middle side's telescope to the left side's. *)
Lemma T_actnf_W {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> T_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> T_ty G (Γ ,, A @ l1) B B' ->
  T_tynf G Γ (tyW l1 l2 A B) (tyW l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA DB IHB T'' i k k' k'' Hc HT HT' HT'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_W D2) as (l5 & l6 & A'' & B'' & -> & H35 & H46 & DA2 & DB2).
  destruct (inv_ty_W HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_W HT') as ((_ & W3 & W4 & HA' & HB') & _).
  destruct (inv_ty_W HT'') as ((_ & W5 & W6 & HA'' & HB'') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W3 W5 H35) as E35.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ac_ty_sound Hc DA2 HA' (wft_lconv _ _ _ _ _ _ HA'' E35)) as EA2.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (HΓA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA' | exact W3]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  assert (EA2' : [ G ; Γ ⊢[ i ] A'' ≅ A' @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA2) | exact (lequiv_sym _ _ _ E35)]).
  pose proof (lequiv_trans _ _ _ _ E13 E35) as E15.
  assert (EA'' : [ G ; Γ ⊢[ i ] A'' ≅ A @ l5 ]).
  { eapply eqty_lconv; [| exact (lequiv_sym _ _ _ E15)]. apply eqty_sym.
    eapply eqty_trans; [exact EA | exact (eqty_lconv _ _ _ _ _ _ _ EA2 E13)]. }
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  pose proof (stab_ty Hi EA2' (lequiv_sym _ _ _ E35) HΓA' HB'') as HB2'.
  pose proof (stab_ty Hi EA'' (lequiv_sym _ _ _ E15) HΓA HB'') as HB2.
  assert (Hctx : [ G ⊢[ i ] Γ ,, A' @ l3 ≅ Γ ,, A @ l1 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA' | exact EA' | exact (lequiv_sym _ _ _ E13)]).
  pose proof (cv_ty HG Hc DB2 Hctx HB' HB2') as DB2'.
  apply actnf_W; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46)
                 | exact (IHA A'' i _ _ _ Hc HA HA' HA'' DA2) | exact (IHB B'' i _ _ _ Hc HB HB1 HB2 DB2')].
Qed.

Lemma T_actmnf_sup {G Γ l l' A B k1 k2 k3 k4 C D C' D' a a' f f'} :
  ac_tm G Γ a a' A -> T_tm G Γ a a' A ->
  T_tm G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) ->
  T_tmnf G Γ (tmSup k1 k2 C D a f) (tmSup k3 k4 C' D' a' f') (tyW l l' A B).
Proof.
  intros Da IHa IHf t'' i k Hc Ht Ht' Ht'' D2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_sup D2) as (k5 & k6 & C'' & D'' & a'' & f'' & -> & Da2 & Df2).
  destruct (sup_parts Hc Ht) as (Wl & Wl' & HA & HB & Ha & Hf).
  destruct (sup_parts Hc Ht') as (_ & _ & _ & _ & Ha' & Hf').
  destruct (sup_parts Hc Ht'') as (_ & _ & _ & _ & Ha'' & Hf'').
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (fty_conv Hc Wl Wl' HA HB Ha' Ha (ac_tm_sound Hc Da Ha Ha')) as EF1.
  pose proof (fty_conv Hc Wl Wl' HA HB Ha'' Ha' (ac_tm_sound Hc Da2 Ha' Ha'')) as EF2.
  assert (Hf'1 : [ G ; Γ ⊢[ i ] f' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ])
    by (eapply wf_conv; [exact Hf' | rewrite Hi; exact EF1]).
  assert (Hf''2 : [ G ; Γ ⊢[ i ] f'' : tyPi l' (lmax l l') B[lsingle a'] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ])
    by (eapply wf_conv; [exact Hf'' | rewrite Hi; exact EF2]).
  assert (Hf''1 : [ G ; Γ ⊢[ i ] f'' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ])
    by (eapply wf_conv; [exact Hf''2 | rewrite Hi; exact EF1]).
  pose proof (cv_tm (ctx_glob _ _ _ HΓ) Hc Df2 (eqc_refl _ _ _ HΓ) Hf' Hf''2 EF1) as Df2'.
  apply actmnf_sup; [exact (IHa a'' i l Hc Ha Ha' Ha'' Da2) | exact (IHf f'' i _ Hc Hf Hf'1 Hf''1 Df2')].
Qed.

Lemma T_actmne_elimW {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c c' ν ν' W} :
  leqv l1 l4 -> leqv l2 l5 -> leqv l3 l6 ->
  ac_ty G Γ A A' -> T_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> T_ty G (Γ ,, A @ l1) B B' ->
  ac_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' -> T_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' ->
  T_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
    c c' (wstepty l1 l2 A B M) ->
  T_nee G Γ ν ν' W ->
  T_ne G Γ (tmElimW l1 l2 l3 A B M c ν) (tmElimW l4 l5 l6 A' B' M' c' ν') M[lsingle ν].
Proof.
  intros H14 H25 H36 DA IHA DB IHB DM IHM IHc IHν x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_elimW D2) as (l7 & l8 & l9 & A'' & B'' & M'' & c'' & ν'' & Wν & -> & H47 & H58 & H69
                               & DA2 & DB2 & DM2 & Dc2 & Dν2).
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimW Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & HF' & HI' & Hc0' & Hν') & _ & _).
  destruct (inv_elimW Hi Hx'') as ((_ & W7 & W8 & W9 & HA'' & HB'' & HM'' & HF'' & HI'' & Hc0'' & Hν'') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W4 H14) as E14. pose proof (leqv_lequiv _ _ _ W2 W5 H25) as E25.
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  pose proof (leqv_lequiv _ _ _ W4 W7 H47) as E47. pose proof (leqv_lequiv _ _ _ W5 W8 H58) as E58.
  pose proof (leqv_lequiv _ _ _ W6 W9 H69) as E69.
  pose proof (lequiv_trans _ _ _ _ E14 E47) as E17. pose proof (lequiv_trans _ _ _ _ E25 E58) as E28.
  pose proof (lequiv_trans _ _ _ _ E36 E69) as E39.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (ext_wf Hi HA W1) as HΓA. pose proof (ext_wf Hi HA' W4) as HΓA'.
  (* the shapes *)
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E14)) as EA.
  pose proof (ac_ty_sound Hc DA2 HA' (wft_lconv _ _ _ _ _ _ HA'' E47)) as EA2.
  assert (EA13 : [ G ; Γ ⊢[ i ] A ≅ A'' @ l1 ])
    by (eapply eqty_trans; [exact EA | exact (eqty_lconv _ _ _ _ _ _ _ EA2 E14)]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | now apply lequiv_sym]).
  assert (EA2' : [ G ; Γ ⊢[ i ] A'' ≅ A' @ l7 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA2) | now apply lequiv_sym]).
  assert (EA13' : [ G ; Γ ⊢[ i ] A'' ≅ A @ l7 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA13) | now apply lequiv_sym]).
  (* the positions, at the left shape *)
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EA' (lequiv_sym _ _ _ E14) HΓA HB') E25) as HB'A.
  pose proof (stab_ty Hi EA2' (lequiv_sym _ _ _ E47) HΓA' HB'') as HB''A'.
  pose proof (stab_ty Hi EA13' (lequiv_sym _ _ _ E17) HΓA HB'') as HB''A.
  pose proof (ac_ty_sound Hc DB HB HB'A) as EB.
  pose proof (ac_ty_sound Hc DB2 HB' (wft_lconv _ _ _ _ _ _ HB''A' E58)) as EB2.
  assert (HctxA : [ G ⊢[ i ] Γ ,, A' @ l4 ≅ Γ ,, A @ l1 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA' | exact EA' | now apply lequiv_sym]).
  pose proof (IHB B'' i _ _ _ Hc HB HB'A HB''A (cv_ty HG Hc DB2 HctxA HB' HB''A')) as XB.
  pose proof (ac_ty_sound Hc XB HB (wft_lconv _ _ _ _ _ _ HB''A E28)) as EB13.
  (* the motives, at the left [W] *)
  assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
  assert (WL' : lwf (gL G) (lmax l4 l5)) by (cbn; split; assumption).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (HW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' @ lmax l4 l5 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  pose proof (ext_wf Hi HW WL) as HΓW. pose proof (ext_wf Hi HW' WL') as HΓW'.
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ]) by (apply eqty_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW2 : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' ≅ tyW l7 l8 A'' B'' @ lmax l4 l5 ]) by (apply eqty_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW13 : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l7 l8 A'' B'' @ lmax l1 l2 ]) by (apply eqty_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' ≅ tyW l1 l2 A B @ lmax l4 l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EW) | apply lequiv_max; now apply lequiv_sym]).
  assert (EW2' : [ G ; Γ ⊢[ i ] tyW l7 l8 A'' B'' ≅ tyW l4 l5 A' B' @ lmax l7 l8 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EW2) | apply lequiv_max; now apply lequiv_sym]).
  assert (EW13' : [ G ; Γ ⊢[ i ] tyW l7 l8 A'' B'' ≅ tyW l1 l2 A B @ lmax l7 l8 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EW13) | apply lequiv_max; now apply lequiv_sym]).
  assert (HL41 : lequiv (gL G) (lmax l4 l5) (lmax l1 l2)) by (apply lequiv_max; now apply lequiv_sym).
  assert (HL74 : lequiv (gL G) (lmax l7 l8) (lmax l4 l5)) by (apply lequiv_max; now apply lequiv_sym).
  assert (HL71 : lequiv (gL G) (lmax l7 l8) (lmax l1 l2)) by (apply lequiv_max; now apply lequiv_sym).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' HL41 HΓW HM') E36) as HM'3.
  pose proof (stab_ty Hi EW2' HL74 HΓW' HM'') as HM''6.
  pose proof (stab_ty Hi EW13' HL71 HΓW HM'') as HM''3.
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  pose proof (ac_ty_sound Hc DM2 HM' (wft_lconv _ _ _ _ _ _ HM''6 E69)) as EM2.
  assert (HctxW : [ G ⊢[ i ] Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ≅ Γ ,, tyW l1 l2 A B @ lmax l1 l2 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HW' | exact EW' | apply lequiv_max; now apply lequiv_sym]).
  pose proof (IHM M'' i _ _ _ Hc HM HM'3 HM''3 (cv_ty HG Hc DM2 HctxW HM' HM''6)) as XM.
  pose proof (ac_ty_sound Hc XM HM (wft_lconv _ _ _ _ _ _ HM''3 E39)) as EM13.
  (* the steps, at the left telescope *)
  pose proof (elimW_step_left Hc E14 E25 E36 HA HA' EA HB HB' EB HM HM' EM HF HI Hc0') as Hc0'2.
  pose proof (elimW_step_left Hc E17 E28 E39 HA HA'' EA13 HB HB'' EB13 HM HM'' EM13 HF HI Hc0'') as Hc0''2.
  pose proof (elimW_step_left Hc E47 E58 E69 HA' HA'' EA2 HB' HB'' EB2 HM' HM'' EM2 HF' HI' Hc0'') as Hc0''6.
  destruct (W_tele_eq Hc E14 E25 E36 HA HA' EA HB HB' EB HM HM' EM) as (_ & HctxT & ES).
  assert (Dc2' : ac_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
                   c' c'' (wstepty l1 l2 A B M)).
  { pose proof (cv_tm HG Hc Dc2 HctxT Hc0' Hc0''6 (eqty_refl _ _ _ _ _ (wf_tm_ty Hi Hc0'))) as Y.
    refine (cv_tm HG Hc Y (eqc_refl _ _ _ (ctx_of_wf_tm Hi Hc0)) _ _ ES).
    - eapply wf_conv; [exact Hc0'2 | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ ES)].
    - eapply wf_conv; [exact Hc0''2 | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ ES)]. }
  eapply actmne_elimW; [exact (leqv_trans _ _ _ H14 H47) | exact (leqv_trans _ _ _ H25 H58)
                       | exact (leqv_trans _ _ _ H36 H69) | | | | | ].
  - exact (IHA A'' i _ _ _ Hc HA HA' HA'' DA2).
  - exact XB.
  - exact XM.
  - exact (IHc c'' i l3 Hc Hc0 Hc0'2 Hc0''2 Dc2').
  - exact (IHν ν'' Wν i _ _ _ _ _ _ Hc Hν Hν' Hν'' Dν2).
Qed.

Lemma T_actmnf_seq_irr {G Γ l A a b w w'} : T_tmnf G Γ w w' (tySEq l A a b).
Proof. red; intros; apply actmnf_seq_irr. Qed.
Lemma T_actmnf_sempty_irr {G Γ l w w'} : T_tmnf G Γ w w' (tySEmpty l).
Proof. red; intros; apply actmnf_sempty_irr. Qed.
Lemma T_actmne_elimSEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ M M' -> T_ty G Γ M M' -> whne ν -> whne ν' ->
  T_ne G Γ (elimSEmpty l1 l2 M ν) (elimSEmpty l3 l4 M' ν') M.
Proof.
  intros H13 H24 DM IHM Hn Hn' x'' T' i k k' k'' X X' X'' Hc Hx Hx' Hx'' D2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (ainv_elimSEmpty D2) as (l5 & l6 & M'' & ν'' & -> & H35 & H46 & DM2 & Hn'').
  destruct (inv_elimSEmpty Hi Hx) as ((_ & _ & _ & HM & _) & _ & _).
  destruct (inv_elimSEmpty Hi Hx') as ((_ & _ & _ & HM' & _) & _ & _).
  destruct (inv_elimSEmpty Hi Hx'') as ((_ & _ & _ & HM'' & _) & _ & _).
  apply actmne_elimSEmpty; [exact (leqv_trans _ _ _ H13 H35) | exact (leqv_trans _ _ _ H24 H46)
                           | exact (IHM M'' i _ _ _ Hc HM HM' HM'' DM2) | exact Hn | exact Hn''].
Qed.

Theorem ac_trans_all :
  (forall G Γ T T', ac_ty G Γ T T' -> T_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> T_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> T_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> T_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> T_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> T_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> T_ne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> T_nee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> T_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first
    [ solve [eapply T_act_red; eassumption] | solve [eapply T_actnf_nat] | solve [eapply T_actnf_U; eassumption]
    | solve [eapply T_actnf_pi; eassumption] | solve [eapply T_actnf_ne; eassumption]
    | solve [eapply T_actnf_CTyp; eassumption] | solve [eapply T_actnf_CTrm; eassumption]
    | solve [eapply T_actnf_upi; eassumption] | solve [eapply T_actnf_cpi; eassumption]
    | solve [eapply T_actnf_tpi; eassumption]
    | solve [eapply T_actne_gvar; eassumption] | solve [eapply T_actne_El; eassumption]
    | solve [eapply T_acc_nil] | solve [eapply T_acc_var] | solve [eapply T_acc_ext; eassumption]
    | solve [eapply T_actm_red; eassumption]
    | solve [eapply T_actmnf_code_nat] | solve [eapply T_actmnf_code_U; eassumption]
    | solve [eapply T_actmnf_code_pi; eassumption] | solve [eapply T_actmnf_zero]
    | solve [eapply T_actmnf_succ; eassumption] | solve [eapply T_actmnf_ne; eassumption]
    | solve [eapply T_actmnf_eta; eassumption] | solve [eapply T_actmnf_ueta; eassumption]
    | solve [eapply T_actmnf_ceta; eassumption] | solve [eapply T_actmnf_teta; eassumption]
    | solve [eapply T_actmnf_boxT; eassumption] | solve [eapply T_actmnf_boxt; eassumption]
    | solve [eapply T_actmne_var; eassumption] | solve [eapply T_actmne_gvar; eassumption]
    | solve [eapply T_actmne_natrec; eassumption] | solve [eapply T_actmne_app; eassumption]
    | solve [eapply T_actmne_letboxT; eassumption] | solve [eapply T_actmne_letboxt; eassumption]
    | solve [eapply T_actmne_elimT; eassumption] | solve [eapply T_actmne_elimT_gvar; eassumption]
    | solve [eapply T_actmne_elimt; eassumption] | solve [eapply T_actmne_elimt_glob; eassumption]
    | solve [eapply T_actmne_uapp; eassumption] | solve [eapply T_actmne_capp; eassumption]
    | solve [eapply T_actmne_tapp; eassumption] | solve [eapply T_actmnee_red; eassumption]
    | solve [eapply T_acs_pt; eassumption]
    | solve [eapply T_actnf_sig; eassumption] | solve [eapply T_actmnf_code_sig; eassumption]
    | solve [eapply T_actmnf_sig_eta; eassumption] | solve [eapply T_actmne_fst; eassumption]
    | solve [eapply T_actmne_snd; eassumption]
    | solve [eapply T_actnf_unit; eassumption] | solve [eapply T_actmnf_code_unit; eassumption]
    | solve [eapply T_actmnf_unit_eta]
    | solve [eapply T_actnf_seq; eassumption] | solve [eapply T_actnf_sempty; eassumption]
    | solve [eapply T_actmnf_seq_irr] | solve [eapply T_actmnf_sempty_irr]
    | solve [eapply T_actmne_elimSEmpty; eassumption]
    | solve [eapply T_actnf_id; eassumption] | solve [eapply T_actmnf_refl]
    | solve [eapply T_actmne_J; eassumption] | solve [eapply T_actmnf_code_id; eassumption]
    | solve [eapply T_actmnf_code_seq; eassumption] | solve [eapply T_actmnf_code_sempty; eassumption]
    | solve [eapply T_actnf_empty; eassumption] | solve [eapply T_actmne_elimEmpty; eassumption]
    | solve [eapply T_actnf_sum; eassumption] | solve [eapply T_actmnf_inl; eassumption]
    | solve [eapply T_actmnf_inr; eassumption] | solve [eapply T_actmne_case; eassumption]
    | solve [eapply T_actnf_W; eassumption] | solve [eapply T_actmnf_sup; eassumption]
    | solve [eapply T_actmne_elimW; eassumption]
    | solve [eapply T_actmnf_code_empty; eassumption] | solve [eapply T_actmnf_code_sum; eassumption]
    | solve [eapply T_actmnf_code_W; eassumption] ].
Qed.
