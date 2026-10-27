(** * Symmetry of algorithmic conversion (08:199), beside [AlgPERTrans] *)
From DeLaM.Validity Require Export AlgPERBase.
From DeLaM.Typing Require Import PresupM.

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

(** [Vec] and [Fin] at a neutral length (M14a). *)
Lemma Y_actne_vec {G Γ l l' A A' ν ν' W} : leqv l l' -> Y_ty G Γ A A' -> Y_nee G Γ ν ν' W ->
  Y_tyne G Γ (tyVec l A ν) (tyVec l' A' ν').
Proof.
  intros Hl IHA IH i k k' Hc HX HX'.
  destruct (inv_ty_vec HX) as ((_ & _ & HA & Hν) & _). destruct (inv_ty_vec HX') as ((_ & _ & HA' & Hν') & _).
  destruct (IH i _ _ _ _ Hc Hν Hν') as (W' & X).
  eapply actne_vec; [exact (leqv_sym _ _ Hl) | exact (IHA i _ _ Hc HA HA') | exact X].
Qed.

Lemma Y_actne_fin {G Γ ν ν' W} : Y_nee G Γ ν ν' W -> Y_tyne G Γ (tyFin ν) (tyFin ν').
Proof.
  intros IH i k k' Hc HX HX'.
  destruct (inv_ty_fin HX) as ((_ & Hν) & _). destruct (inv_ty_fin HX') as ((_ & Hν') & _).
  destruct (IH i _ _ _ _ Hc Hν Hν') as (W' & X).
  eapply actne_fin; exact X.
Qed.

(** [DVec] at a neutral length (M17a): the family moves to the other
    length's index type. *)
Lemma Y_actne_dvec {G Γ l l' ν ν' F F' W} : leqv l l' -> ac_tmnee G Γ ν ν' W -> Y_nee G Γ ν ν' W ->
  Y_ty G (Γ ,, tyFin ν @ lzero) F F' -> Y_tyne G Γ (tyDVec l ν F) (tyDVec l' ν' F').
Proof.
  intros Hl DN IH IHF i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_ty_dvec HX) as ((_ & W1 & Hν & HF) & _).
  destruct (inv_ty_dvec HX') as ((_ & W2 & Hν' & HF') & _).
  destruct (ac_nee_sound' DN Hc Hν Hν') as (_ & _ & Eν).
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  assert (HFin : [ G ; Γ ⊢[ i ] tyFin ν @ lzero ]) by (apply wft_fin; [exact Hv | exact Hν]).
  assert (EFin : [ G ; Γ ⊢[ i ] tyFin ν ≅ tyFin ν' @ lzero ]) by (apply eqty_fin; [exact Hv | exact Eν]).
  assert (HΓF : [ G ; Γ ,, tyFin ν @ lzero ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HFin | exact I]).
  pose proof (stab_ty Hi (eqty_sym _ _ _ _ _ _ EFin) (lequiv_refl _ lzero I) HΓF HF') as HF1.
  assert (Hctx : [ G ⊢[ i ] Γ ,, tyFin ν @ lzero ≅ Γ ,, tyFin ν' @ lzero ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HFin | exact EFin | exact (lequiv_refl _ lzero I)]).
  destruct (IH i _ _ _ _ Hc Hν Hν') as (W' & X).
  eapply actne_dvec; [exact (leqv_sym _ _ Hl) | exact X |].
  exact (cv_ty (ctx_glob _ _ _ HΓ) Hc (IHF i l l' Hc HF HF1) Hctx HF1 HF).
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

(** The code of [Wf] (M15b), as [W]'s: the arity at [Nat]. *)
Lemma Y_actmnf_code_wf {G Γ l k k' s s' n n'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> Y_tm G Γ s s' (tyU k) ->
  ac_tm G (Γ ,, tyEl k s @ k) n n' tyNat -> Y_tm G (Γ ,, tyEl k s @ k) n n' tyNat ->
  Y_tmnf G Γ (tmWf k s n) (tmWf k' s' n') (tyU l).
Proof.
  intros Hk0 Ds IHs Dn IHn i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (code_wf_prem Hc Hx) as (W1 & Hs & Hn). destruct (code_wf_prem Hc Hx') as (W3 & Hs' & Hn').
  pose proof (compt_notV _ Hc) as Hv.
  pose proof (leqv_lequiv _ _ _ W1 W3 Hk0) as E13.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU k ≅ tyU k' @ lsuc k ]) by (apply eqty_U; assumption).
  pose proof (code_U_conv Hc E13 Hs') as Hs1.
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl k s ≅ tyEl k' s' @ k ]) by (apply eqty_El; [exact Hv | exact E13 | exact Es]).
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl k s @ k ]) by (apply wft_El; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyEl k s @ k ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl k' s' ≅ tyEl k s @ k' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_tm Hi EEl' (lequiv_sym _ _ _ E13) HΓ1 Hn') as Hn1.
  apply actmnf_code_wf; [exact (leqv_sym _ _ Hk0) | |].
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs (eqty_sym _ _ _ _ _ _ EU1)).
  - assert (Hctx : [ G ⊢[ i ] Γ ,, tyEl k s @ k ≅ Γ ,, tyEl k' s' @ k' ])
      by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HEl | exact EEl | exact E13]).
    exact (cv_tm HG Hc (IHn i _ Hc Hn Hn1) Hctx Hn1 Hn (eqty_refl _ _ _ _ _ (wf_tm_ty Hi Hn))).
Qed.

(** The codes of [DVec] and [IWf] (M17c), as [Wf]'s and [IWf]'s. *)
Lemma Y_actmnf_code_dvec {G Γ l k k' n n' f f'} : leqv k k' ->
  ac_tm G Γ n n' tyNat -> Y_tm G Γ n n' tyNat ->
  ac_tm G (Γ ,, tyFin n @ lzero) f f' (tyU k) -> Y_tm G (Γ ,, tyFin n @ lzero) f f' (tyU k) ->
  Y_tmnf G Γ (tmDVec k n f) (tmDVec k' n' f') (tyU l).
Proof.
  intros Hk0 Dn IHn Df IHf i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (code_dvec_prem Hc Hx) as (W1 & Hn & Hf). destruct (code_dvec_prem Hc Hx') as (W3 & Hn' & Hf').
  pose proof (compt_notV _ Hc) as Hv.
  pose proof (leqv_lequiv _ _ _ W1 W3 Hk0) as E13.
  pose proof (ctx_of_wf_tm Hi Hn) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (ac_tm_sound Hc Dn Hn Hn') as En.
  assert (EF : [ G ; Γ ⊢[ i ] tyFin n ≅ tyFin n' @ lzero ]) by (apply eqty_fin; assumption).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin n @ lzero ]) by (apply wft_fin; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HF | exact I]).
  pose proof (stab_tm Hi (eqty_sym _ _ _ _ _ _ EF) (lequiv_refl _ lzero I) HΓ1 (code_U_conv Hc E13 Hf')) as Hf1.
  assert (EU2 : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] tyU k ≅ tyU k' @ lsuc k ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E13]).
  apply actmnf_code_dvec; [exact (leqv_sym _ _ Hk0) | |].
  - exact (cv_tm HG Hc (IHn i _ Hc Hn Hn') (eqc_refl _ _ _ HΓ) Hn' Hn (eqty_refl _ _ _ _ _ (wf_tm_ty Hi Hn))).
  - assert (Hctx : [ G ⊢[ i ] Γ ,, tyFin n @ lzero ≅ Γ ,, tyFin n' @ lzero ])
      by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HF | exact EF | exact (lequiv_refl _ lzero I)]).
    exact (cv_tm HG Hc (IHf i _ Hc Hf Hf1) Hctx Hf1 Hf (eqty_sym _ _ _ _ _ _ EU2)).
Qed.

Lemma Y_actmnf_code_iwf {G Γ l k k' ki ki' x x' s s' n n' o o' c c' m m'} : leqv k k' -> leqv ki ki' ->
  ac_tm G Γ x x' (tyU ki) -> Y_tm G Γ x x' (tyU ki) -> ac_tm G Γ s s' (tyU k) -> Y_tm G Γ s s' (tyU k) ->
  ac_tm G (Γ ,, tyEl k s @ k) n n' tyNat -> Y_tm G (Γ ,, tyEl k s @ k) n n' tyNat ->
  ac_tm G (Γ ,, tyEl k s @ k) o o' (tyEl ki x⟨↑⟩) -> Y_tm G (Γ ,, tyEl k s @ k) o o' (tyEl ki x⟨↑⟩) ->
  ac_tm G (Γ ,, tyEl k s @ k ,, tyFin n @ lzero) c c' (tyEl ki x⟨↑⟩⟨↑⟩) ->
  Y_tm G (Γ ,, tyEl k s @ k ,, tyFin n @ lzero) c c' (tyEl ki x⟨↑⟩⟨↑⟩) ->
  ac_tm G Γ m m' (tyEl ki x) -> Y_tm G Γ m m' (tyEl ki x) ->
  Y_tmnf G Γ (tmIWf k ki x s n o c m) (tmIWf k' ki' x' s' n' o' c' m') (tyU l).
Proof.
  intros Hk0 Hki0 Dx IHx Ds IHs DN IHN DO IHO DC IHC Dm IHm i q Hc Ht Ht'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (iwfc_ac_eq Hc Ht Ht' Hk0 Hki0 Dx Ds DN DO DC) as (HE & Hx1 & Hs1 & Hm & Hm'l).
  pose proof HE as (E13 & E24 & HS & EX & _ & _ & _ & _ & _ & _ & HN'l & HO'l & HC'l).
  pose proof HS as (_ & _ & _ & _ & HN & HO & HC).
  destruct (code_iwf_prem Hc Ht) as (_ & _ & Hx & Hs & _).
  pose proof (ctx_of_wf_tm Hi Hx) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  destruct (IWf_fwd Hc HE) as (HctxA & HctxAF & EX1 & EX2 & _ & _).
  assert (EUx : [ G ; Γ ⊢[ i ] tyU ki ≅ tyU ki' @ lsuc ki ]) by (apply eqty_U; assumption).
  assert (EUs : [ G ; Γ ⊢[ i ] tyU k ≅ tyU k' @ lsuc k ]) by (apply eqty_U; assumption).
  apply actmnf_code_iwf; [exact (leqv_sym _ _ Hk0) | exact (leqv_sym _ _ Hki0) | | | | | |].
  - exact (cv_tm HG Hc (IHx i _ Hc Hx Hx1) (eqc_refl _ _ _ HΓ) Hx1 Hx (eqty_sym _ _ _ _ _ _ EUx)).
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs (eqty_sym _ _ _ _ _ _ EUs)).
  - exact (cv_tm HG Hc (IHN i lzero Hc HN HN'l) HctxA HN'l HN (eqty_refl _ _ _ _ _ (wf_tm_ty Hi HN))).
  - exact (cv_tm HG Hc (IHO i ki Hc HO HO'l) HctxA HO'l HO EX1).
  - exact (cv_tm HG Hc (IHC i ki Hc HC HC'l) HctxAF HC'l HC EX2).
  - exact (cv_tm HG Hc (IHm i ki Hc Hm Hm'l) (eqc_refl _ _ _ HΓ) Hm'l Hm (eqty_sym _ _ _ _ _ _ EX)).
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

(** The codes of [Vec] and [Fin] (M14b). *)
Lemma Y_actmnf_code_vec {G Γ l k k' s s' n n'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> Y_tm G Γ s s' (tyU k) -> ac_tm G Γ n n' tyNat -> Y_tm G Γ n n' tyNat ->
  Y_tmnf G Γ (tmVec k s n) (tmVec k' s' n') (tyU l).
Proof.
  intros Hk0 Ds IHs Dn IHn i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (code_vec_prem Hc Hx) as (Wk & Hs & Hn). destruct (code_vec_prem Hc Hx') as (Wk' & Hs' & Hn').
  pose proof (leqv_lequiv _ _ _ Wk Wk' Hk0) as E.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  assert (EU : [ G ; Γ ⊢[ i ] tyU k' ≅ tyU k @ lsuc k ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | apply lequiv_sym, E]
                       | exact (lequiv_suc _ _ _ E)]. }
  apply actmnf_code_vec; [exact (leqv_sym _ _ Hk0) | |].
  - exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs EU).
  - exact (IHn i lzero Hc Hn Hn').
Qed.
(** The code of [∥·∥] (M16b). *)
Lemma Y_actmnf_code_sq {G Γ l k k' s s'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> Y_tm G Γ s s' (tyU k) ->
  Y_tmnf G Γ (tmSqCode k s) (tmSqCode k' s') (tyU l).
Proof.
  intros Hk0 Ds IHs i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (code_sq_prem Hc Hx) as (Wk & Hs). destruct (code_sq_prem Hc Hx') as (Wk' & Hs').
  pose proof (leqv_lequiv _ _ _ Wk Wk' Hk0) as E.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  assert (EU : [ G ; Γ ⊢[ i ] tyU k' ≅ tyU k @ lsuc k ]).
  { eapply eqty_lconv; [apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | apply lequiv_sym, E]
                       | exact (lequiv_suc _ _ _ E)]. }
  apply actmnf_code_sq; [exact (leqv_sym _ _ Hk0) |].
  exact (cv_tm HG Hc (IHs i _ Hc Hs Hs1) (eqc_refl _ _ _ HΓ) Hs1 Hs EU).
Qed.
Lemma Y_actmnf_code_fin {G Γ l n n'} : ac_tm G Γ n n' tyNat -> Y_tm G Γ n n' tyNat ->
  Y_tmnf G Γ (tmFin n) (tmFin n') (tyU l).
Proof.
  intros Dn IHn i m Hc Hx Hx'.
  apply actmnf_code_fin. exact (IHn i lzero Hc (code_fin_prem Hc Hx) (code_fin_prem Hc Hx')).
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
Lemma Y_actmne_J {G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' ν ν' W} : leqv l2 l4 ->
  ac_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  Y_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  ac_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] -> Y_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] ->
  ac_tmnee G Γ ν ν' W -> Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmJ l1 l2 A a M c u ν) (tmJ l3 l4 A' a' M' c' u' ν') M[lsingle2 u ν].
Proof.
  intros H24 DM IHM Dc IHc Dν IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (inv_J Hi Hx) as ((_ & W1 & W2 & HA & Ha & HI & HM & Hcc & Hu & He) & _ & _).
  destruct (inv_J Hi Hx') as ((_ & W3 & W4 & HA' & Ha' & HI' & HM' & Hc' & Hu' & He') & _ & _).
  pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  destruct (ac_nee_sound' Dν Hc He He') as (E0 & E1 & _).
  destruct (J_annots Hi Hc W1 E0 E1) as (E13 & EA & Ea & _).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (eqtm_wf_r Hi Ea) as Ha'1.
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
  destruct (IHν i _ _ _ _ Hc He He') as (W' & Xν).
  exists M'[lsingle2 u' ν']. eapply actmne_J; [exact (leqv_sym _ _ H24) | | | exact Xν].
  - exact (cv_ty HG Hc (IHM i l2 l2 Hc HM HM'2) (J_ctx_eq Hi Hv E13 HA EA Ea) HM'2 HM).
  - exact (cv_tm HG Hc (IHc i l2 Hc Hcc Hc'1) (eqc_refl _ _ _ HΓ) Hc'1 Hcc (eqty_sym _ _ _ _ _ _ HMs)).
Qed.

(** The empty type (M12a). *)
Lemma Y_actnf_empty {G Γ l l'} : leqv l l' -> Y_tynf G Γ (tyEmpty l) (tyEmpty l').
Proof. intros Hl; red; intros; apply actnf_empty, leqv_sym, Hl. Qed.

Lemma Y_actmnf_empty_irr {G Γ l w w'} : Y_tmnf G Γ w w' (tyEmpty l).
Proof. red; intros; apply actmnf_empty_irr. Qed.

Lemma Y_actmne_elimEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G (Γ ,, tyEmpty l2 @ l2) M M' -> Y_ty G (Γ ,, tyEmpty l2 @ l2) M M' -> whne ν -> whne ν' ->
  Y_ne G Γ (elimEmpty l1 l2 M ν) (elimEmpty l3 l4 M' ν') M[lsingle ν].
Proof.
  intros H13 H24 DM IHM Hn Hn' i k k' X X' Hc Hx Hx'.
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
  exists M'[lsingle ν']. apply actmne_elimEmpty; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | | exact Hn' | exact Hn].
  exact (cv_ty HG Hc (IHM i l1 l1 Hc HM HM'2) Hctx HM'2 HM).
Qed.

(** Propositional truncation (M16a). *)
Lemma Y_actnf_sq {G Γ l l' A A'} : leqv l l' -> Y_ty G Γ A A' -> Y_tynf G Γ (tySq l A) (tySq l' A').
Proof.
  intros Hl IHA i k k' Hc HT HT'.
  destruct (inv_ty_sq HT) as ((_ & _ & HA) & _). destruct (inv_ty_sq HT') as ((_ & _ & HA') & _).
  apply actnf_sq; [exact (leqv_sym _ _ Hl) | exact (IHA i l l' Hc HA HA')].
Qed.

Lemma Y_actmnf_sq_irr {G Γ l A w w'} : Y_tmnf G Γ w w' (tySq l A).
Proof. red; intros; apply actmnf_sq_irr. Qed.

Lemma Y_actmne_elimSq {G Γ l1 l2 l3 l4 A A' M M' c c' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' ->
  ac_ty G (Γ ,, tySq l1 A @ l1) M M' -> Y_ty G (Γ ,, tySq l1 A @ l1) M M' -> whne ν -> whne ν' ->
  Y_ne G Γ (tmElimSq l1 l2 A M c ν) (tmElimSq l3 l4 A' M' c' ν') (tySq l2 M[lsingle ν]).
Proof.
  intros H13 H24 DA IHA DM IHM Hn Hn' i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimSq Hi Hx) as ((_ & W1 & W2 & HA & HM & _ & Hν) & _ & _).
  destruct (inv_elimSq Hi Hx') as ((_ & W3 & W4 & HA' & HM' & _ & _) & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (HS1 : [ G ; Γ ⊢[ i ] tySq l1 A @ l1 ]) by (apply wft_sq; [(apply compt_notV; exact Hc) | exact W1 | exact HA]).
  assert (ES : [ G ; Γ ⊢[ i ] tySq l1 A ≅ tySq l3 A' @ l1 ])
    by (apply eqty_sq; [(apply compt_notV; exact Hc) | exact E13 | exact HA | exact EA]).
  assert (HS : [ G ; Γ ⊢[ i ] tySq l3 A' ≅ tySq l1 A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ ES) | exact (lequiv_sym _ _ _ E13)]).
  assert (HΓS : [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HS1 | exact W1]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi HS (lequiv_sym _ _ _ E13) HΓS HM') E24) as HM'2.
  assert (Hctx : [ G ⊢[ i ] Γ ,, tySq l1 A @ l1 ≅ Γ ,, tySq l3 A' @ l3 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HS1 | exact ES | exact E13]).
  exists (tySq l4 M'[lsingle ν']).
  apply actmne_elimSq; [exact (leqv_sym _ _ H13) | exact (leqv_sym _ _ H24) | exact (IHA i l1 l3 Hc HA HA')
                       | | exact Hn' | exact Hn].
  exact (cv_ty HG Hc (IHM i l2 l2 Hc HM HM'2) Hctx HM'2 HM).
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
  leqv l3 l6 ->
  ac_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' -> Y_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' ->
  Y_tm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] -> Y_tm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] -> ac_tmnee G Γ ν ν' W -> Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) (tmCase l4 l5 l6 A' B' M' c1' c2' ν') M[lsingle ν].
Proof.
  intros H36 DM IHM IHc1 IHc2 Dν IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Hν) & _ & _).
  destruct (inv_case Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & Hc1' & Hc2' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (case_annots Hi Hc W1 W2 E0 E1) as (E14 & E25 & EA & EB).
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
  eapply actmne_case; [exact (leqv_sym _ _ H36) | | | | exact Xν].
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
  leqv l3 l6 ->
  ac_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' -> Y_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' ->
  Y_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
    c c' (wstepty l1 l2 A B M) ->
  ac_tmnee G Γ ν ν' W -> Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmElimW l1 l2 l3 A B M c ν) (tmElimW l4 l5 l6 A' B' M' c' ν') M[lsingle ν].
Proof.
  intros H36 DM IHM IHc Dν IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimW Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & HF' & HI' & Hc0' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (W_annots Hi Hc W1 W2 E0 E1) as (E14 & E25 & EA & EB).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA4 : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E14)]).
  assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
  assert (HL : lequiv (gL G) (lmax l4 l5) (lmax l1 l2)) by (apply lequiv_max; solve [apply lequiv_sym; assumption]).
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
  eapply actmne_elimW; [exact (leqv_sym _ _ H36) | | | exact Xν].
  - exact (cv_ty HG Hc (IHM i l3 l3 Hc HM HM'3) HctxW HM'3 HM).
  - exact (cv_tm HG Hc (IHc i l3 Hc Hc0 Hc0'2) HctxT Hc0'2 Hc0 (eqty_sym _ _ _ _ _ _ ES)).
Qed.

(** Finitary well-founded trees (M15a). *)
Lemma Y_actnf_wf {G Γ l1 l3 A A' N N'} : leqv l1 l3 ->
  ac_ty G Γ A A' -> Y_ty G Γ A A' -> ac_tm G (Γ ,, A @ l1) N N' tyNat -> Y_tm G (Γ ,, A @ l1) N N' tyNat ->
  Y_tynf G Γ (tyWf l1 A N) (tyWf l3 A' N').
Proof.
  intros H13 DA IHA DN IHN i k k' Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_wf HT) as ((_ & W1 & HA & HN) & _).
  destruct (inv_ty_wf HT') as ((_ & W3 & HA' & HN') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_tm Hi EA' (lequiv_sym _ _ _ E13) HΓA HN') as HN1.
  assert (Hctx : [ G ⊢[ i ] Γ ,, A @ l1 ≅ Γ ,, A' @ l3 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact E13]).
  apply actnf_wf; [exact (leqv_sym _ _ H13) | exact (IHA i l1 l3 Hc HA HA') |].
  exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHN i lzero Hc HN HN1) Hctx HN1 HN
           (eqty_refl _ _ _ _ _ (wf_tm_ty Hi HN))).
Qed.

Lemma Y_actmnf_supf {G Γ l A N k k' C D C' D' a a' cs cs'} :
  ac_tm G Γ a a' A -> Y_tm G Γ a a' A ->
  Y_tm G Γ cs cs' (tyVec l (tyWf l A N) N[lsingle a]) ->
  Y_tmnf G Γ (tmSupf k C D a cs) (tmSupf k' C' D' a' cs') (tyWf l A N).
Proof.
  intros Da IHa IHcs i m Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (supf_parts Hc Ht) as (Wl & HA & HN & Ha & Hcs).
  destruct (supf_parts Hc Ht') as (_ & _ & _ & Ha' & Hcs').
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (wf_cs_conv Hc Wl HA HN Ha Ha' (ac_tm_sound Hc Da Ha Ha')) as EC.
  assert (Hcs'1 : [ G ; Γ ⊢[ i ] cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ])
    by (eapply wf_conv; [exact Hcs' | rewrite Hi; exact EC]).
  apply actmnf_supf; [exact (IHa i l Hc Ha Ha') |].
  exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHcs i _ Hc Hcs Hcs'1) (eqc_refl _ _ _ HΓ) Hcs'1 Hcs
           (eqty_sym _ _ _ _ _ _ EC)).
Qed.

Lemma Y_actmne_elimWf {G Γ l1 l2 l3 l4 A A' N N' M M' c c' ν ν' W} :
  leqv l2 l4 ->
  ac_ty G (Γ ,, tyWf l1 A N @ l1) M M' -> Y_ty G (Γ ,, tyWf l1 A N @ l1) M M' ->
  Y_tm G (Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2)
    c c' (wfstepty l1 A N M) ->
  ac_tmnee G Γ ν ν' W -> Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmElimWf l1 l2 A N M c ν) (tmElimWf l3 l4 A' N' M' c' ν') M[lsingle ν].
Proof.
  intros H24 DM IHM IHc Dν IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimWf Hi Hx) as ((_ & W1 & W2 & HA & HN & HM & HC & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimWf Hi Hx') as ((_ & W3 & W4 & HA' & HN' & HM' & HC' & HI' & Hc0' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (Wf_annots Hi Hc W1 E0 E1) as (E13 & EA & EN).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA3 : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_tm Hi EA3 (lequiv_sym _ _ _ E13) HΓA HN') as HN'A.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' ≅ tyWf l1 A N @ l3 ])
    by (eapply eqty_lconv; [apply eqty_sym, EW | exact (lequiv_sym _ _ _ E13)]).
  pose proof (ext_wf Hi HW W1) as HΓW.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' (lequiv_sym _ _ _ E13) HΓW HM') E24) as HM'3.
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  pose proof (elimWf_step_left Hc E13 E24 HA HA' EA HN HN' EN HM HM' EM HI Hc0') as Hc0'2.
  destruct (Wf_tele_eq Hc E13 E24 HA HA' EA HN HN' EN HM HM' EM) as (HctxT & _ & ES).
  assert (HctxA : [ G ⊢[ i ] Γ ,, A @ l1 ≅ Γ ,, A' @ l3 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact EA | exact E13]).
  assert (HctxW : [ G ⊢[ i ] Γ ,, tyWf l1 A N @ l1 ≅ Γ ,, tyWf l3 A' N' @ l3 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HW | exact EW | exact E13]).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W' & Xν).
  exists M'[lsingle ν'].
  eapply actmne_elimWf; [exact (leqv_sym _ _ H24) | | | exact Xν].
  - exact (cv_ty HG Hc (IHM i l2 l2 Hc HM HM'3) HctxW HM'3 HM).
  - exact (cv_tm HG Hc (IHc i l2 Hc Hc0 Hc0'2) HctxT Hc0'2 Hc0 (eqty_sym _ _ _ _ _ _ ES)).
Qed.

(** Indexed W-types (M17b). *)
Lemma Y_actnf_iwf {G Γ l li k ki X X' A A' N N' Ot Ot' C C' m m'} : leqv l k -> leqv li ki ->
  ac_ty G Γ X X' -> Y_ty G Γ X X' -> ac_ty G Γ A A' -> Y_ty G Γ A A' ->
  ac_tm G (Γ ,, A @ l) N N' tyNat -> Y_tm G (Γ ,, A @ l) N N' tyNat ->
  ac_tm G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ -> Y_tm G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ ->
  ac_tm G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ -> Y_tm G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ ->
  ac_tm G Γ m m' X -> Y_tm G Γ m m' X ->
  Y_tynf G Γ (tyIWf l li X A N Ot C m) (tyIWf k ki X' A' N' Ot' C' m').
Proof.
  intros Hl Hli DX IHX DA IHA DN IHN DO IHO DC IHC Dm IHm i q q' Hc HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_ty_iwf HT) as ((_ & W1 & W2 & HX & HA & HN & HO & HC & Hm) & _).
  destruct (inv_ty_iwf HT') as ((_ & W3 & W4 & HX' & HA' & HN' & HO' & HC' & Hm') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 Hl) as E1. pose proof (leqv_lequiv _ _ _ W2 W4 Hli) as E2.
  assert (HS : IWfSig (G := G) (i := i) Γ l li X A N Ot C) by (unfold IWfSig; auto 8).
  assert (HS' : IWfSig (G := G) (i := i) Γ k ki X' A' N' Ot' C') by (unfold IWfSig; auto 8).
  pose proof (iwf_ac_eq Hc E1 E2 HS HS' DX DA DN DO DC) as HE.
  pose proof HE as (_ & _ & _ & EX & _ & _ & _ & _ & _ & _ & HN'l & HO'l & HC'l).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (IWf_fwd Hc HE) as (HctxA & HctxAF & EX1 & EX2 & _ & _).
  assert (Hm'l : [ G ; Γ ⊢[ i ] m' : X @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact Hm' | exact E2] | exact EX]).
  apply actnf_iwf; [exact (leqv_sym _ _ Hl) | exact (leqv_sym _ _ Hli) | exact (IHX i li ki Hc HX HX')
                   | exact (IHA i l k Hc HA HA') | | | |].
  - exact (cv_tm HG Hc (IHN i lzero Hc HN HN'l) HctxA HN'l HN (eqty_refl _ _ _ _ _ (wf_tm_ty Hi HN))).
  - exact (cv_tm HG Hc (IHO i li Hc HO HO'l) HctxA HO'l HO EX1).
  - exact (cv_tm HG Hc (IHC i li Hc HC HC'l) HctxAF HC'l HC EX2).
  - exact (cv_tm HG Hc (IHm i li Hc Hm Hm'l) (eqc_refl _ _ _ HΓ) Hm'l Hm (eqty_sym _ _ _ _ _ _ EX)).
Qed.

Lemma Y_actmnf_supi {G Γ l li X A N Ot C m k ki X1 A1 N1 O1 C1 k' ki' X1' A1' N1' O1' C1' a a' cs cs'} :
  ac_tm G Γ a a' A -> Y_tm G Γ a a' A ->
  Y_tm G Γ cs cs' (tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a)) ->
  Y_tmnf G Γ (tmSupi k ki X1 A1 N1 O1 C1 a cs) (tmSupi k' ki' X1' A1' N1' O1' C1' a' cs')
    (tyIWf l li X A N Ot C m).
Proof.
  intros Da IHa IHcs i q Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (supi_parts Hc Ht) as (HS & _ & Ha & Hcs & _ & _).
  destruct (supi_parts Hc Ht') as (_ & _ & Ha' & Hcs' & _ & _).
  pose proof (ctx_of_wf_tm Hi Ha) as HΓ.
  pose proof (IWf_csa_eq Hi Hv (IWfEq_refl HS) Ha Ha' (ac_tm_sound Hc Da Ha Ha')) as EC.
  pose proof (conv_tm' Hi Hcs' EC) as Hcs'1.
  apply actmnf_supi; [exact (IHa i l Hc Ha Ha') |].
  exact (cv_tm (ctx_glob _ _ _ HΓ) Hc (IHcs i _ Hc Hcs Hcs'1) (eqc_refl _ _ _ HΓ) Hcs'1 Hcs (eqty_sym _ _ _ _ _ _ EC)).
Qed.

Lemma Y_actmne_elimIWf {G Γ l li l' k ki k' X X' A A' N N' Ot Ot' C C' M M' c c' m m' ν ν' W} :
  leqv l' k' ->
  ac_ty G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M' ->
  Y_ty G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M' ->
  Y_tm G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l')
    c c' (iwfstepty l li X A N Ot C M) ->
  ac_tmnee G Γ ν ν' W -> Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmElimIWf l li l' X A N Ot C M c m ν) (tmElimIWf k ki k' X' A' N' Ot' C' M' c' m' ν')
    M[lsingle2 m ν].
Proof.
  intros H3 DM IHM IHc Dν IHν i q q' Z Z' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_elimIWf Hi Hx)
    as ((_ & W3 & W1 & W2 & HX & HA & HN & HO & HC & Hmot & HM & Hcs & HI & Hc0 & Hm & Hν) & _ & _).
  destruct (inv_elimIWf Hi Hx')
    as ((_ & W3' & W1' & W2' & HX' & HA' & HN' & HO' & HC' & Hmot' & HM' & Hcs' & HI' & Hc0' & Hm' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W3 W3' H3) as E3.
  assert (HS : IWfSig (G := G) (i := i) Γ l li X A N Ot C) by (unfold IWfSig; auto 8).
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (F0 & F1 & _).
  destruct (IWf_annots Hi Hc HS F0 F1) as (HE & _).
  pose proof HE as (E1 & E2 & _).
  pose proof HE as (_ & _ & _ & EX & _ & _ & _ & _ & _ & _ & HN'l & HO'l & HC'l).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (IWf_fwd Hc HE) as (HctxA & HctxAF & EX1 & EX2 & HctxM & HctxCs).
  pose proof (IWf_mot_left Hi Hv HE E3 HM') as HM'l. pose proof (ac_ty_sound Hc DM HM HM'l) as EM.
  pose proof (IWf_ih_left Hi Hv HE E3 HI') as HI'l. pose proof (IWf_ihty_eq Hc HE E3 EM HI'l) as EI.
  pose proof (IWf_step_left Hi Hv HE E3 HM EM HI HI' EI Hc0') as Hc0'l.
  assert (WL : lwf (gL G) (lmax lzero l')) by (cbn; split; [exact I | exact W3]).
  pose proof (IWf_step_eq Hi Hv HE HM EM (ext_wf Hi HI WL)) as ES.
  assert (HctxT : [ G ⊢[ i ] Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
                    ≅ Γ ,, A' @ k ,, iwfcsty k ki X' A' N' Ot' C' @ lmax k ki ,, iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero k' ])
    by (apply eqc_ext; [exact HctxCs | exact HI | exact EI | apply lequiv_max; [apply lequiv_refl; exact I | exact E3]]).
  assert (Hm'l : [ G ; Γ ⊢[ i ] m' : X @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact Hm' | exact E2] | exact EX]).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W' & Xν).
  exists M'[lsingle2 m' ν'].
  eapply actmne_elimIWf; [exact (leqv_sym _ _ H3) | | | exact Xν].
  - exact (cv_ty HG Hc (IHM i l' l' Hc HM HM'l) HctxM HM'l HM).
  - exact (cv_tm HG Hc (IHc i l' Hc Hc0 Hc0'l) HctxT Hc0'l Hc0 (eqty_sym _ _ _ _ _ _ ES)).
Qed.

(** [M] (M18b). *)
Lemma Y_actnf_M {G Γ l l' li k k' ki X X' A A' B B' C C' j j'} : leqv l k -> leqv l' k' -> leqv li ki ->
  ac_ty G Γ X X' -> Y_ty G Γ X X' -> ac_ty G (Γ ,, X @ li) A A' -> Y_ty G (Γ ,, X @ li) A A' ->
  ac_ty G (Γ ,, X @ li ,, A @ l) B B' -> Y_ty G (Γ ,, X @ li ,, A @ l) B B' ->
  ac_tm G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ ->
  Y_tm G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ ->
  ac_tm G Γ j j' X -> Y_tm G Γ j j' X ->
  Y_tynf G Γ (tyM l l' li X A B C j) (tyM k k' ki X' A' B' C' j').
Proof.
  intros Hl Hl' Hli DX IHX DA IHA DB IHB DC IHC Dj IHj i q q' Hc HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_M HT) as ((_ & W1 & W2 & W3 & HX & HA & HB & HC & Hj) & _).
  destruct (inv_ty_M HT') as ((_ & W1' & W2' & W3' & HX' & HA' & HB' & HC' & Hj') & _).
  pose proof (leqv_lequiv _ _ _ W1 W1' Hl) as E1. pose proof (leqv_lequiv _ _ _ W2 W2' Hl') as E2.
  pose proof (leqv_lequiv _ _ _ W3 W3' Hli) as E3.
  assert (HS : MSig (G := G) (i := i) Γ l l' li X A B C) by (unfold MSig; auto 8).
  assert (HS' : MSig (G := G) (i := i) Γ k k' ki X' A' B' C') by (unfold MSig; auto 8).
  pose proof (M_ac_eq Hc E1 E2 E3 HS HS' DX DA DB DC) as HE.
  pose proof HE as (_ & _ & _ & _ & EX & _ & _ & _ & _ & HA'l & HB'l & HC'l).
  destruct (M_ctxs Hc HE) as (L1 & L2 & L3 & _ & _ & _ & EX3 & _).
  pose proof (ctx_of_wf_ty Hi HX) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (Hj'l : [ G ; Γ ⊢[ i ] j' : X @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact Hj' | exact E3] | exact EX]).
  apply actnf_M; [exact (leqv_sym _ _ Hl) | exact (leqv_sym _ _ Hl') | exact (leqv_sym _ _ Hli)
                 | exact (IHX i li ki Hc HX HX') | | | |].
  - exact (cv_ty HG Hc (IHA i l l Hc HA HA'l) L1 HA'l HA).
  - exact (cv_ty HG Hc (IHB i l' l' Hc HB HB'l) L2 HB'l HB).
  - exact (cv_tm HG Hc (IHC i li Hc HC HC'l) L3 HC'l HC (eqty_sym _ _ _ _ _ _ EX3)).
  - exact (cv_tm HG Hc (IHj i li Hc Hj Hj'l) (eqc_refl _ _ _ HΓ) Hj'l Hj (eqty_sym _ _ _ _ _ _ EX)).
Qed.

Lemma Y_actmnf_corec {G Γ l l' li X A B C j k1 k2 k3 X1 A1 B1 C1 j1 k1' k2' k3' X1' A1' B1' C1' j1'
    kc kc' Y Y' c c' y y'} : leqv kc kc' ->
  ac_ty G (Γ ,, X @ li) Y Y' -> Y_ty G (Γ ,, X @ li) Y Y' ->
  Y_tm G (Γ ,, X @ li ,, Y @ kc) c c' (mStepTy l l' li X A B C kc Y)⟨↑⟩ ->
  Y_tm G Γ y y' Y[lsingle j] ->
  Y_tmnf G Γ (tmCorec k1 k2 k3 X1 A1 B1 C1 kc Y c j1 y) (tmCorec k1' k2' k3' X1' A1' B1' C1' kc' Y' c' j1' y')
    (tyM l l' li X A B C j).
Proof.
  intros Hkc DY IHY IHc IHy i q Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (corec_parts Hc Ht) as (HE & Wkc & Ej & HY & Hc0 & Hy & _).
  destruct (corec_parts Hc Ht') as (_ & Wkc' & _ & HY' & Hc0' & Hy' & _).
  pose proof (leqv_lequiv _ _ _ Wkc Wkc' Hkc) as Ekc.
  pose proof HE as (_ & _ & _ & HS & _).
  pose proof (eqtm_wf_l Hi Ej) as Hj.
  pose proof (ac_ty_sound Hc DY HY (wft_lconv _ _ _ _ _ _ HY' Ekc)) as EY.
  destruct (corec_right Hc HS Hj Ekc Wkc HY EY Hc0' Hy') as (Hc'l & Hy'l).
  pose proof (ctx_of_wf_ty Hi HY) as HΓX. pose proof (ctx_of_wf_tm Hi Hj) as HΓ.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (Lc : [ G ⊢[ i ] Γ ,, X @ li ,, Y @ kc ≅ Γ ,, X @ li ,, Y' @ kc' ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓX) | exact HY | exact EY | exact Ekc]).
  pose proof (M_wk_eqty Hi (M_step_eq Hi Hv (MEq_refl' HS) Ekc HY EY) (wkr_shift1 _ _ _) (ext_wf Hi HY Wkc)) as ES.
  pose proof (M_func2_ty Hi HY EY (lsub_eq_single Hi Hj Hj (eqtm_refl _ _ _ _ _ _ Hj))) as EYs.
  apply actmnf_corec; [exact (leqv_sym _ _ Hkc) | exact (IHY i kc kc' Hc HY HY') | |].
  - exact (cv_tm HG Hc (IHc i _ Hc Hc0 Hc'l) Lc Hc'l Hc0 (eqty_sym _ _ _ _ _ _ ES)).
  - exact (cv_tm HG Hc (IHy i kc Hc Hy Hy'l) (eqc_refl _ _ _ HΓ) Hy'l Hy (eqty_sym _ _ _ _ _ _ EYs)).
Qed.

Lemma Y_actmne_out {G Γ l l' li k k' ki X X' A A' B B' C C' j j' ν ν' W} :
  Y_nee G Γ ν ν' W ->
  Y_ne G Γ (tmOut l l' li X A B C j ν) (tmOut k k' ki X' A' B' C' j' ν') (mOutTy l l' li X A B C j).
Proof.
  intros IHν i q q' Z Z' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_out Hi Hx) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hν) & _).
  destruct (inv_out Hi Hx') as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hν') & _).
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (W' & Xν).
  eexists. eapply actmne_out; exact Xν.
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
    | solve [eapply Y_actne_vec; eassumption] | solve [eapply Y_actne_fin; eassumption]
    | solve [eapply Y_actne_dvec; eassumption]
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
    | solve [eapply Y_actmnf_seq_irr] | solve [eapply Y_actmnf_sempty_irr] | solve [eapply Y_actmnf_empty_irr]
    | solve [eapply Y_actmne_elimSEmpty; eassumption]
    | solve [eapply Y_actnf_id; eassumption] | solve [eapply Y_actmnf_refl]
    | solve [eapply Y_actmne_J; eassumption] | solve [eapply Y_actmnf_code_id; eassumption]
    | solve [eapply Y_actmnf_code_seq; eassumption] | solve [eapply Y_actmnf_code_sempty; eassumption]
    | solve [eapply Y_actnf_empty; eassumption] | solve [eapply Y_actmne_elimEmpty; eassumption]
    | solve [eapply Y_actnf_sq; eassumption] | solve [eapply Y_actmnf_sq_irr]
    | solve [eapply Y_actmne_elimSq; eassumption]
    | solve [eapply Y_actnf_sum; eassumption] | solve [eapply Y_actmnf_inl; eassumption]
    | solve [eapply Y_actmnf_inr; eassumption] | solve [eapply Y_actmne_case; eassumption]
    | solve [eapply Y_actnf_W; eassumption] | solve [eapply Y_actmnf_sup; eassumption]
    | solve [eapply Y_actmne_elimW; eassumption]
    | solve [eapply Y_actnf_wf; eassumption] | solve [eapply Y_actmnf_supf; eassumption]
    | solve [eapply Y_actmne_elimWf; eassumption]
    | solve [eapply Y_actnf_iwf; eassumption] | solve [eapply Y_actmnf_supi; eassumption]
    | solve [eapply Y_actmne_elimIWf; eassumption]
    | solve [eapply Y_actnf_M; eassumption] | solve [eapply Y_actmnf_corec; eassumption]
    | solve [eapply Y_actmne_out; eassumption]
    | solve [eapply Y_actmnf_code_empty; eassumption] | solve [eapply Y_actmnf_code_sum; eassumption]
    | solve [eapply Y_actmnf_code_vec; eassumption] | solve [eapply Y_actmnf_code_fin; eassumption]
    | solve [eapply Y_actmnf_code_sq; eassumption]
    | solve [eapply Y_actmnf_code_W; eassumption]
    | solve [eapply Y_actmnf_code_wf; eassumption]
    | solve [eapply Y_actmnf_code_dvec; eassumption] | solve [eapply Y_actmnf_code_iwf; eassumption] ].
Qed.
