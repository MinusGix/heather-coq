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
