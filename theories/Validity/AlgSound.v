(** * Soundness of algorithmic conversion (06:700, M6_DESIGN.md step 2)

    Algorithmically convertible, well-typed syntax is declaratively equal,
    at the computing layers D and M. Each rule is a lemma over the
    induction hypotheses ([S_*]); the mutual induction dispatches them.

    Neutral terms infer their type: [S_ne] says that the inferred type is
    a type of both sides (up to equality) and that they are equal at any
    of their common types. The right-hand pieces the declarative
    congruences need (instance equations, right bodies, branches) come
    from [AlgPrereq]. *)
From DeLaM.Typing Require Export Algorithmic.
From DeLaM.Validity Require Export AlgPrereq.

(** ** Helpers *)

Lemma lvl_eq_eqty {G i Γ T T' k l} : lvl_eq (gL G) k l ->
  [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. intros [->|H] E; [exact E | exact (eqty_lconv _ _ _ _ _ _ _ E H)]. Qed.
Lemma lvl_eq_eqtm {G i Γ t t' T k l} : lvl_eq (gL G) k l ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof. intros [->|H] E; [exact E | exact (eqtm_lconv _ _ _ _ _ _ _ _ E H)]. Qed.
Lemma lvl_eq_ty {G i Γ T k l} : lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T @ k ].
Proof. intros [->|H] E; [exact E | exact (wft_lconv _ _ _ _ _ _ E H)]. Qed.
Lemma lvl_eq_tm {G i Γ t T k l} : lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t : T @ k ].
Proof. intros [->|H] E; [exact E | exact (wf_lconv _ _ _ _ _ _ _ E H)]. Qed.
(** From a level related to [k] back to [k]'s partner. *)
Lemma lvl_eq_tm' {G i Γ t T k l} : lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t : T @ l ].
Proof. intros [->|H] E; [exact E | exact (wf_lconv _ _ _ _ _ _ _ E (lequiv_sym _ _ _ H))]. Qed.
Lemma lvl_eq_ty' {G i Γ T k l} : lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T @ l ].
Proof. intros [->|H] E; [exact E | exact (wft_lconv _ _ _ _ _ _ E (lequiv_sym _ _ _ H))]. Qed.

(** Untyped reduction of well-typed syntax to a whnf is typed reduction:
    normalization gives one, and whnf reduction is deterministic
    (M6_DESIGN.md H6). *)
Lemma red_ty_sound {G i Γ T W k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> reds_ty T W -> whnf_ty W ->
  [ G ; Γ ⊢[ i ] T ≅ W @ k ].
Proof.
  intros Hc HT Hr Hw. destruct Hc as [-> | ->].
  - destruct (decl_whnf_tyred HT) as (W' & HW' & Hw').
    rewrite (reds_ty_whnf_det _ _ _ Hr (tyred_red _ _ _ _ _ _ HW') Hw Hw'). exact (tyred_eq _ _ _ _ _ _ HW').
  - destruct (declM_whnf_tyred HT) as (W' & HW' & Hw').
    rewrite (reds_ty_whnf_det _ _ _ Hr (tyred_red _ _ _ _ _ _ HW') Hw Hw'). exact (tyred_eq _ _ _ _ _ _ HW').
Qed.

Lemma red_tm_sound {G i Γ t w T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] -> reds t w -> whnf w ->
  [ G ; Γ ⊢[ i ] t ≅ w : T @ k ].
Proof.
  intros Hc Ht Hr Hw. destruct Hc as [-> | ->].
  - destruct (decl_whnf_tmred Ht) as (w' & Hw' & Hw'').
    rewrite (reds_whnf_det _ _ _ Hr (tmred_red _ _ _ _ _ _ _ Hw') Hw Hw''). exact (tmred_eq _ _ _ _ _ _ _ Hw').
  - destruct (declM_whnf_tmred Ht) as (w' & Hw' & Hw'').
    rewrite (reds_whnf_det _ _ _ Hr (tmred_red _ _ _ _ _ _ _ Hw') Hw Hw''). exact (tmred_eq _ _ _ _ _ _ _ Hw').
Qed.

(** ** The statements *)

Definition S_ty G Γ T T' : Prop := forall i k, compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Definition S_ctx G Δ Δ' : Prop :=
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ].
Definition S_tm G Γ t t' T : Prop := forall i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Definition S_ne G Γ ν ν' T : Prop := forall i k k' A A', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  [ G ; Γ ⊢[ i ] A ≅ T @ k ] /\ [ G ; Γ ⊢[ i ] A' ≅ T @ k' ] /\ [ G ; Γ ⊢[ i ] ν ≅ ν' : A @ k ].
Definition S_sub G Γ d d' Δ : Prop := forall i, compt i -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] d : Δ ] -> [ G ; Γ ⊢[ i ] d' : Δ ] -> [ G ; Γ ⊢[ i ] d ≅ d' : Δ ].

(** ** Types *)

Lemma S_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  S_ty G Γ W W' -> S_ty G Γ T T'.
Proof.
  intros Hr Hr' Hw Hw' IH i k Hc HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (red_ty_sound Hc HT Hr Hw) as E. pose proof (red_ty_sound Hc HT' Hr' Hw') as E'.
  pose proof (IH i k Hc (eqty_wf_r Hi E) (eqty_wf_r Hi E')) as X.
  eapply eqty_trans; [exact E|]. eapply eqty_trans; [exact X | exact (eqty_sym _ _ _ _ _ _ E')].
Qed.

Lemma S_actnf_nat {G Γ} : S_ty G Γ tyNat tyNat.
Proof. intros i k Hc HT _. exact (eqty_refl _ _ _ _ _ HT). Qed.

Lemma S_actnf_U {G Γ l l'} : leqv l l' -> S_ty G Γ (tyU l) (tyU l').
Proof.
  intros Hl i k Hc HT HT'.
  destruct (inv_ty_U HT) as ((Hv & HΓ & W) & Hk). destruct (inv_ty_U HT') as ((_ & _ & W') & _).
  apply (lvl_eq_eqty Hk). apply eqty_U; [exact Hv | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  S_ty G Γ A A' -> S_ty G (Γ ,, A @ l1) B B' -> S_ty G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof.
  intros H13 H24 IHA IHB i k Hc HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi HT) as ((Hv & W1 & W2 & HA & HB) & Hk).
  destruct (inv_ty_pi HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  pose proof (IHB i l2 Hc HB (wft_lconv _ _ _ _ _ _ HB1 E24)) as EB.
  apply (lvl_eq_eqty Hk). apply eqty_pi; assumption.
Qed.

Lemma S_actnf_CTyp {G Γ Δ Δ' l l'} : S_ctx G Δ Δ' -> leqv l l' -> S_ty G Γ (tyCTyp Δ l) (tyCTyp Δ' l').
Proof.
  intros IH Hl i k Hc HT HT'.
  destruct (inv_ty_CTyp HT) as ((-> & HΓ & HΔ & W) & Hk). destruct (inv_ty_CTyp HT') as ((_ & _ & HΔ' & W') & _).
  apply (lvl_eq_eqty Hk). apply eqty_CTyp; [exact HΓ | exact (IH HΔ HΔ') | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actnf_CTrm {G Γ Δ Δ' T T' l l'} : S_ctx G Δ Δ' -> S_ty G Δ T T' -> leqv l l' ->
  S_ty G Γ (tyCTrm Δ T l) (tyCTrm Δ' T' l').
Proof.
  intros IHc IHT Hl i k Hc HX HX'.
  destruct (inv_ty_CTrm HX) as ((-> & HΓ & HΔ & HT & W) & Hk).
  destruct (inv_ty_CTrm HX') as ((_ & _ & HΔ' & HT' & W') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (IHc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E)) as HT1.
  pose proof (IHT lD l compt_D HT HT1) as ET.
  apply (lvl_eq_eqty Hk). apply eqty_CTrm; assumption.
Qed.

Lemma S_actnf_upi {G Γ n l l' T T'} : leqv l l' -> S_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  S_ty G Γ (tyUPi n l T) (tyUPi n l' T').
Proof.
  intros Hl IH i k Hc HX HX'.
  destruct (inv_ty_upi HX) as ((-> & HΓ & Hn & W & HT) & Hk).
  destruct (inv_ty_upi HX') as ((_ & _ & _ & W' & HT') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (IH lM l compt_M HT (wft_lconv _ _ _ _ _ _ HT' E)) as ET.
  apply (lvl_eq_eqty Hk). apply eqty_upi; assumption.
Qed.

Lemma S_actnf_cpi {G Γ l l' T T'} : leqv l l' -> S_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  S_ty G Γ (tyCPi l T) (tyCPi l' T').
Proof.
  intros Hl IH i k Hc HX HX'.
  destruct (inv_ty_cpi HX) as ((-> & HΓ & W & HT) & Hk).
  destruct (inv_ty_cpi HX') as ((_ & _ & W' & HT') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (IH lM l compt_M HT (wft_lconv _ _ _ _ _ _ HT' E)) as ET.
  apply (lvl_eq_eqty Hk). apply eqty_cpi; assumption.
Qed.

Lemma S_actnf_tpi {G Γ Δ Δ' l1 l2 l3 l4 T T'} : S_ctx G Δ Δ' -> leqv l1 l3 -> leqv l2 l4 ->
  S_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T' -> S_ty G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ' l3 l4 T').
Proof.
  intros IHc H13 H24 IH i k Hc HX HX'.
  destruct (inv_ty_tpi HX) as ((-> & HΓ & HΔ & W1 & W2 & HT) & Hk).
  destruct (inv_ty_tpi HX') as ((_ & _ & HΔ' & W3 & W4 & HT') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHc HΔ HΔ') as Ec.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HGD : [ ⊢ gext G (gdTy Δ lD l1) ]) by (apply wfg_ty; auto).
  pose proof (gbind_obj_ty (lle_refl lD) ltac:(discriminate) HGD Ec E13) as Ho.
  pose proof (gbind_ty HG HGD Ho HT') as HT1.
  pose proof (IH lM l2 compt_M HT (wft_lconv _ _ _ _ _ _ HT1 E24)) as ET.
  apply (lvl_eq_eqty Hk). eapply eqty_tpi; eassumption.
Qed.

Lemma S_actne_gvar {G Γ U Δ i' l d d'} : in_gctx (gΨ G) U (gdTy Δ i' l) -> S_sub G Γ d d' Δ ->
  S_ty G Γ (tyGvar U d) (tyGvar U d').
Proof.
  intros Hin IH i k Hc HX HX'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_gvar HX) as (Δ0 & i0 & l0 & (Hv & HΓ & Hin0 & Hle & Ht & Hn & He) & Hk).
  destruct (inv_ty_gvar HX') as (Δ1 & i1 & l1 & (_ & _ & Hin1 & _ & Ht' & Hn' & He') & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <-.
  rewrite Hi in HΓ.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (HΔ & _).
  pose proof (lift_ctx HΔ (lle_D_compt _ Hc)) as HΔi.
  pose proof (IH i Hc HΔi (lsub_wf_prem Hi HΓ Ht Hn He) (lsub_wf_prem Hi HΓ Ht' Hn' He')) as (_ & _ & Hd).
  apply (lvl_eq_eqty Hk). eapply eqty_gvar; try eassumption. now rewrite Hi.
Qed.

Lemma S_actne_El {G Γ l l' ν ν' W} : leqv l l' -> S_ne G Γ ν ν' W -> S_ty G Γ (tyEl l ν) (tyEl l' ν').
Proof.
  intros Hl IH i k Hc HX HX'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HX) as ((Hv & W1 & Hν) & Hk). destruct (inv_ty_El HX') as ((_ & W2 & Hν') & _).
  pose proof (leqv_lequiv _ _ _ W1 W2 Hl) as E.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  assert (EU : [ G ; Γ ⊢[ i ] tyU l ≅ tyU l' @ lsuc l ]) by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | exact E]).
  assert (Hν1 : [ G ; Γ ⊢[ i ] ν' : tyU l @ lsuc l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hν' | exact (lequiv_suc _ _ _ E)] | rewrite Hi; exact EU]. }
  destruct (IH i (lsuc l) (lsuc l) (tyU l) (tyU l) Hc Hν Hν1) as (_ & _ & Eν).
  apply (lvl_eq_eqty Hk). apply eqty_El; assumption.
Qed.

(** ** Local contexts (at D) *)

Lemma S_acc_nil {G} : S_ctx G cnil cnil.
Proof. intros H _. apply eqc_nil, (ctx_glob _ _ _ H). Qed.

Lemma S_acc_var {G g} : S_ctx G (cvar g) (cvar g).
Proof. intros H _. inversion H; subst. apply eqc_var; assumption. Qed.

Lemma S_acc_ext {G Γ Γ' A A' l l'} : S_ctx G Γ Γ' -> S_ty G Γ A A' -> leqv l l' ->
  S_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof.
  intros IHc IHA Hl H H'.
  destruct (wfc_ext_inv H) as (HΓ & HA & W). destruct (wfc_ext_inv H') as (HΓ' & HA' & W').
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (IHc HΓ HΓ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HA' (lequiv_sym _ _ _ E)) as HA1.
  apply eqc_ext; [exact Ec | exact HA | exact (IHA lD l compt_D HA HA1) | exact E].
Qed.

(** ** Terms *)

Lemma S_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> S_tm G Γ w w' W -> S_tm G Γ t t' T.
Proof.
  intros HrT HwT Hr Hr' Hw Hw' IH i k Hc Ht Ht'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (red_ty_sound Hc (wf_tm_ty Hi Ht) HrT HwT) as ET.
  pose proof (red_tm_sound Hc Ht Hr Hw) as Et. pose proof (red_tm_sound Hc Ht' Hr' Hw') as Et'.
  assert (EW : [ G ; Γ ⊢[ typeof i ] W ≅ T @ k ]) by (rewrite Hi; exact (eqty_sym _ _ _ _ _ _ ET)).
  pose proof (IH i k Hc (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Et) EW)
                (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Et') EW)) as X.
  eapply eqtm_trans; [exact Et|]. eapply eqtm_trans; [| exact (eqtm_sym _ _ _ _ _ _ _ Et')].
  eapply eqtm_conv; [exact X | rewrite Hi; exact ET].
Qed.

Lemma S_actmnf_code_nat {G Γ l} : S_tm G Γ tmNat tmNat (tyU l).
Proof. intros i k Hc Ht _. exact (eqtm_refl _ _ _ _ _ _ Ht). Qed.

Lemma S_actmnf_code_U {G Γ l k k'} : leqv k k' -> S_tm G Γ (tmU k) (tmU k') (tyU l).
Proof.
  intros Hl i kk Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_U Hi Ht) as ((Hv & HΓ & W) & Hk & HT). destruct (inv_code_U Hi Ht') as ((_ & _ & W') & _).
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_U; [exact Hv | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  S_tm G Γ s s' (tyU l1) -> S_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  S_tm G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 IHs IHt i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_pi Hi Hx) as ((Hv & W1 & W2 & Hs & Ht) & Hk & HT).
  destruct (inv_code_pi Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (IHs i (lsuc l1) Hc Hs Hs1) as Es.
  (* [t'] in [Γ, El l1 s] *)
  assert (Es' : [ G ; Γ ⊢[ i ] s' ≅ s : tyU l3 @ lsuc l3 ]).
  { eapply eqtm_lconv; [| exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13))].
    eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ Es) | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EU1)]. }
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (apply eqty_El; [exact Hv | exact (lequiv_sym _ _ _ E13) | exact Es']).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | apply wft_El; assumption | exact W1]).
  pose proof (stab_tm Hi EEl (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  pose proof (IHt i (lsuc l2) Hc Ht Ht2) as Et.
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_pi; assumption.
Qed.

Lemma S_actmnf_zero {G Γ} : S_tm G Γ zero zero tyNat.
Proof. intros i k Hc Ht _. exact (eqtm_refl _ _ _ _ _ _ Ht). Qed.

Lemma S_actmnf_succ {G Γ t t'} : S_tm G Γ t t' tyNat -> S_tm G Γ (succ t) (succ t') tyNat.
Proof.
  intros IH i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_succ Hi Hx) as ((Hv & Ht) & Hk & HT). destruct (inv_succ Hi Hx') as ((_ & Ht') & _).
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_succ; [exact Hv | exact (IH i lzero Hc Ht Ht')].
Qed.

Lemma S_actmnf_ne {G Γ ν ν' W W'} : posty W -> S_ne G Γ ν ν' W' -> S_tm G Γ ν ν' W.
Proof. intros _ IH i k Hc Hν Hν'. exact (proj2 (proj2 (IH i k k W W Hc Hν Hν'))). Qed.

Lemma S_actmnf_eta {G Γ l l' A B w w'} :
  S_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  S_tm G Γ w w' (tyPi l l' A B).
Proof.
  intros IH i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi (wf_tm_ty Hi Hw)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (IH i l' Hc (pre_eta_body Hi Hv W1 W2 HA HB Hw1) (pre_eta_body Hi Hv W1 W2 HA HB Hw1')) as X.
  apply (lvl_eq_eqtm Hk). exact (decl_funext i Hc G Γ l l' A B w w' W1 W2 HA HB Hw1 Hw1' X).
Qed.

(** The body of [UΠ]'s η (as in [pre_ueta_l]). *)
Lemma wf_ueta_body {G Γ n l T t} : lwf (n + gL G) l ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] t : tyUPi n l T @ lomega ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] uapp t⟨ush n⟩ᵤ (ubvars n) : T @ l ].
Proof.
  intros Hl HT Ht. pose proof (wf_ty_dnf HT) as HTd.
  pose proof (uwk_tm n Ht) as X. cbn [uren_ty lvren] in X.
  pose proof (uwk_under_ty n HT) as HT2.
  assert (Hl2 : lwf (n + gL (gctx_uwk n G)) (lvren l (uuprn n (ush n))))
    by (eapply lwf_lvren; [apply uwk_under_ok | exact Hl]).
  pose proof (wf_uapp (gctx_uwk n G) (Γ⟨ush n⟩ᵤ) n _ _ _ (ubvars n) Hl2 HT2 (ubvars_length n)
                (lwfs_ubvars n _) X) as Y.
  rewrite ueta_ty, ueta_lvl in Y by exact HTd. exact Y.
Qed.

Lemma S_actmnf_ueta {G Γ n l T w w'} :
  S_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  S_tm G Γ w w' (tyUPi n l T).
Proof.
  intros IH i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_upi (wf_tm_ty Hi Hw)) as ((-> & HΓ & Hn & W & HT) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (IH lM l compt_M (wf_ueta_body W HT Hw1) (wf_ueta_body W HT Hw1')) as X.
  apply (lvl_eq_eqtm Hk). exact (@geq_tm_uext _ _ DeclEqM G Γ n l T w w' Hn W HT Hw1 Hw1' X).
Qed.

Lemma S_actmnf_ceta {G Γ l T w w'} :
  S_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T -> S_tm G Γ w w' (tyCPi l T).
Proof.
  intros IH i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_cpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & W & HT) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (IH lM l compt_M (wf_ceta_body W HT Hw1) (wf_ceta_body W HT Hw1')) as X.
  apply (lvl_eq_eqtm Hk). exact (@geq_tm_cext _ _ DeclEqM G Γ l T w w' W HT Hw1 Hw1' X).
Qed.

Lemma S_actmnf_teta {G Γ Δ l l' T w w'} :
  S_tm (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  S_tm G Γ w w' (tyTPi Δ l l' T).
Proof.
  intros IH i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_tpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & HΔ & W1 & W2 & HT) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (IH lM l' compt_M (wf_teta_body HΔ W1 W2 HT Hw1) (wf_teta_body HΔ W1 W2 HT Hw1')) as X.
  apply (lvl_eq_eqtm Hk). exact (@geq_tm_text _ _ DeclEqM G Γ Δ l l' T w w' HΔ W1 W2 HT Hw1 Hw1' X).
Qed.

Lemma S_actmnf_boxT {G Γ Δ l T T'} : ty_leq T T' -> S_tm G Γ (boxT T) (boxT T') (tyCTyp Δ l).
Proof.
  intros Hl i k Hc Hb Hb'.
  destruct (inv_boxT (compt_typeof_self _ Hc) Hb) as (Δ0 & l0 & ((-> & _) & _)).
  exact (eqtm_leq _ _ _ _ _ _ Hb Hb' Hl).
Qed.

Lemma S_actmnf_boxt {G Γ Δ A l t t'} : tm_leq t t' -> S_tm G Γ (boxt t) (boxt t') (tyCTrm Δ A l).
Proof.
  intros Hl i k Hc Hb Hb'.
  destruct (inv_boxt (compt_typeof_self _ Hc) Hb) as (Δ0 & A0 & l0 & ((-> & _) & _)).
  exact (eqtm_leq _ _ _ _ _ _ Hb Hb' Hl).
Qed.

Lemma S_actmnee_red {G Γ ν ν' T W} : S_ne G Γ ν ν' T -> reds_ty T W -> whnf_ty W -> S_ne G Γ ν ν' W.
Proof.
  intros IH Hr Hw i k k' A A' Hc Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (IH i k k' A A' Hc Hν Hν') as (EA & EA' & Eν).
  pose proof (red_ty_sound Hc (eqty_wf_r Hi EA) Hr Hw) as ET.
  pose proof (red_ty_sound Hc (eqty_wf_r Hi EA') Hr Hw) as ET'.
  split; [| split]; [eapply eqty_trans; eassumption | eapply eqty_trans; eassumption | exact Eν].
Qed.

Lemma S_acs_pt {G Γ d d' Δ} :
  (forall n A k, in_ctx Δ n A k -> S_tm G Γ (llk d n) (llk d' n) A[d]) -> S_sub G Γ d d' Δ.
Proof.
  intros IH i Hc HΔ Hd Hd'. pose proof (compt_typeof_self _ Hc) as Hi.
  apply (lsub_eq_pt Hi Δ Γ d d' HΔ Hd Hd'). intros n A k Hin Hr.
  exact (IH n A k Hin i k Hc (lsub_wf_var Hd Hin) Hr).
Qed.

(** ** Neutral terms *)

Lemma S_actmne_var {G Γ n T l} : in_ctx Γ n T l -> S_ne G Γ (var n) (var n) T.
Proof.
  intros Hin i k k' X X' Hc Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_var Hi Hν) as (T0 & l0 & (_ & Hin0) & _ & HX).
  destruct (inv_var Hi Hν') as (T1 & l1 & (_ & Hin1) & _ & HX').
  destruct (in_ctx_det Hin Hin0) as [<- _]. destruct (in_ctx_det Hin Hin1) as [<- _].
  split; [exact HX | split; [exact HX' | exact (eqtm_refl _ _ _ _ _ _ Hν)]].
Qed.

Lemma S_actmne_gvar {G Γ u Δ i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ i' T l) -> S_sub G Γ d d' Δ ->
  S_ne G Γ (gvar u d) (gvar u d') T[d].
Proof.
  intros Hin IH i k k' X X' Hc Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_gvar Hi Hν) as (Δ0 & i0 & T0 & l0 & (HΓ & Hin0 & Hle & Ht & Hn & He) & Hk & HX).
  destruct (inv_gvar Hi Hν') as (Δ1 & i1 & T1 & l1 & (_ & Hin1 & _ & Ht' & Hn' & He') & Hk' & HX').
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <- <-.
  pose proof HΓ as HΓi. rewrite Hi in HΓi.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓi) Hin) as (HΔ & HT & _).
  pose proof (lift_ctx HΔ (lle_D_compt _ Hc)) as HΔi. pose proof (lift_ty HT (lle_D_compt _ Hc)) as HTi.
  pose proof (IH i Hc HΔi (lsub_wf_prem Hi HΓi Ht Hn He) (lsub_wf_prem Hi HΓi Ht' Hn' He')) as Hd.
  pose proof (wf_ty_func Hi HTi Hd) as ET.
  assert (E : [ G ; Γ ⊢[ i ] gvar u d ≅ gvar u d' : T[d] @ l ])
    by (eapply eqtm_gvar; try eassumption; exact (proj2 (proj2 Hd))).
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' | exact (eqty_sym _ _ _ _ _ _ (lvl_eq_eqty Hk' ET))].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk E) | rewrite Hi; exact HX].
Qed.

Lemma S_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  S_ty G (Γ ,, tyNat @ lzero) M M' -> S_tm G Γ s s' M[lsingle zero] ->
  S_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> S_ne G Γ ν ν' W ->
  S_ne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof.
  intros Hl IHM IHs IHz IHν i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_natrec Hi Hx) as ((Hv & Wl & HM & Hs & Hz & Hν) & Hk & HX).
  destruct (inv_natrec Hi Hx') as ((_ & Wl' & HM' & Hs' & Hz' & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as E.
  pose proof (IHM i l Hc HM (wft_lconv _ _ _ _ _ _ HM' E)) as EM.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_nat; [exact Hv | rewrite Hi; exact HΓ] | exact I]).
  assert (H0 : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; [exact Hv | rewrite Hi; exact HΓ]).
  pose proof (eqty_single Hi EM H0) as EM0.
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E] | rewrite Hi; exact EM0]).
  pose proof (IHs i l Hc Hs Hs1) as Es.
  assert (HΓM : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] ]) by (apply wfc_ext; assumption).
  assert (EM' : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' ≅ M @ l' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM) | exact (lequiv_sym _ _ _ E)]).
  pose proof (stab_tm Hi EM' (lequiv_sym _ _ _ E) HΓM Hz') as Hz1.
  pose proof (eqty_subst Hi EM (lsub_wf_lsucc Hi Hv HΓM)) as EMs.
  assert (Hz2 : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hz1 | exact E] | rewrite Hi; exact EMs]).
  pose proof (IHz i l Hc Hz Hz2) as Ez.
  destruct (IHν i lzero lzero tyNat tyNat Hc Hν Hν') as (_ & _ & Eν).
  pose proof (eqtm_natrec _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E HM EM Es Ez Eν) as Econg.
  assert (EMν : [ G ; Γ ⊢[ i ] M[lsingle ν] ≅ M'[lsingle ν'] @ l ]).
  { eapply eqty_trans; [exact (eqty_single Hi EM Hν) |].
    exact (wf_ty_func Hi (wft_lconv _ _ _ _ _ _ HM' E) (lsub_eq_single Hi Hν Hν' Eν)). }
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact (lequiv_sym _ _ _ E)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

(** [Π] injectivity at a computing layer. *)
Lemma pi_inj_c {G i Γ l l1 l2 l3 l4 A A' B B'} : compt i ->
  [ G ; Γ ⊢[ i ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ].
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_pi_inj H) | exact (declM_pi_inj H)]. Qed.

Lemma sig_inj_c {G i Γ l l1 l2 l3 l4 A A' B B'} : compt i ->
  [ G ; Γ ⊢[ i ] tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ].
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_sig_inj H) | exact (declM_sig_inj H)]. Qed.

Lemma unit_inj_c {G i Γ l l1 l2} : compt i ->
  [ G ; Γ ⊢[ i ] tyUnit l1 ≅ tyUnit l2 @ l ] -> lequiv (gL G) l2 l1.
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_unit_inj H) | exact (declM_unit_inj H)]. Qed.

Lemma id_inj_c {G i Γ l l1 l2 A A' a a' b b'} : compt i ->
  [ G ; Γ ⊢[ i ] tyId l1 A a b ≅ tyId l2 A' a' b' @ l ] ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] /\ [ G ; Γ ⊢[ i ] b ≅ b' : A @ l1 ].
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_id_inj H) | exact (declM_id_inj H)]. Qed.

Lemma S_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  S_ne G Γ ν ν' (tyPi m m' A0 B0) -> S_tm G Γ s s' A0 ->
  S_ne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof.
  intros IHν IHs i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν & Hs) & Hk & HX).
  destruct (inv_app Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν' & Hs') & Hk' & HX').
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (E0 & E1 & Eν).
  (* the annotations agree with the inferred function type, hence with each other *)
  destruct (pi_inj_c Hc E0) as (Em1 & Em2 & EA0 & EB0).
  destruct (pi_inj_c Hc E1) as (Em3 & Em4 & EA1 & EB1).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em1) Em3) as E13.
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em2) Em4) as E24.
  assert (EA : [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ]).
  { eapply eqty_trans; [exact EA0 |]. apply eqty_sym.
    eapply eqty_lconv; [exact EA1 | exact E13]. }
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_eqty Hi EA' (lequiv_sym _ _ _ E13) HΓA EB1) as EB1'.
  assert (EB : [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ]).
  { eapply eqty_trans; [exact EB0 |]. apply eqty_sym.
    eapply eqty_lconv; [exact EB1' | exact E24]. }
  (* the arguments, at the inferred domain *)
  assert (Hs0 : [ G ; Γ ⊢[ i ] s : A0 @ l1 ])
    by (eapply wf_conv; [exact Hs | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA0)]).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : A @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E13] | rewrite Hi; exact EA]).
  assert (Hs1' : [ G ; Γ ⊢[ i ] s' : A0 @ l1 ])
    by (eapply wf_conv; [exact Hs1 | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA0)]).
  pose proof (IHs i l1 Hc Hs0 Hs1') as Es0.
  assert (Es : [ G ; Γ ⊢[ i ] s ≅ s' : A @ l1 ]) by (eapply eqtm_conv; [exact Es0 | rewrite Hi; exact EA0]).
  pose proof (eqtm_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E13 E24 HA EA EB Eν Es) as Econg.
  split; [| split].
  - eapply eqty_trans; [exact HX | apply (lvl_eq_eqty Hk)]. exact (eqty_single Hi EB0 Hs).
  - eapply eqty_trans; [exact HX' | apply (lvl_eq_eqty Hk')].
    assert (Es3 : [ G ; Γ ⊢[ i ] s' ≅ s : A' @ l3 ]).
    { eapply eqtm_lconv; [| exact (lequiv_sym _ _ _ E13)].
      eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ Es) | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA)]. }
    eapply eqty_trans; [exact (eqty_single Hi EB1 Hs') |].
    exact (wf_ty_func Hi (eqty_wf_r Hi EB1) (lsub_eq_single Hi Hs' (eqtm_wf_r Hi Es3) Es3)).
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

(** ** Dependent pairs (M8) *)

Lemma S_actnf_sig {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  S_ty G Γ A A' -> S_ty G (Γ ,, A @ l1) B B' -> S_ty G Γ (tySig l1 l2 A B) (tySig l3 l4 A' B').
Proof.
  intros H13 H24 IHA IHB i k Hc HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_sig HT) as ((Hv & W1 & W2 & HA & HB) & Hk).
  destruct (inv_ty_sig HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  pose proof (IHB i l2 Hc HB (wft_lconv _ _ _ _ _ _ HB1 E24)) as EB.
  apply (lvl_eq_eqty Hk). apply eqty_sig; assumption.
Qed.

Lemma S_actmnf_code_sig {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  S_tm G Γ s s' (tyU l1) -> S_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  S_tm G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 IHs IHt i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_sig Hi Hx) as ((Hc0 & W1 & W2 & Hs & Ht) & Hk & HT).
  destruct (inv_code_sig Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  pose proof Hc0 as Hv.
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (IHs i (lsuc l1) Hc Hs Hs1) as Es.
  assert (Es' : [ G ; Γ ⊢[ i ] s' ≅ s : tyU l3 @ lsuc l3 ]).
  { eapply eqtm_lconv; [| exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13))].
    eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ Es) | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EU1)]. }
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (apply eqty_El; [exact Hv | exact (lequiv_sym _ _ _ E13) | exact Es']).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | apply wft_El; assumption | exact W1]).
  pose proof (stab_tm Hi EEl (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  pose proof (IHt i (lsuc l2) Hc Ht Ht2) as Et.
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_sig; assumption.
Qed.

Lemma S_actmnf_sig_eta {G Γ l l' A B w w'} :
  S_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w') A ->
  S_tm G Γ (tmSnd l l' A B w) (tmSnd l l' A B w') B[lsingle (tmFst l l' A B w)] ->
  S_tm G Γ w w' (tySig l l' A B).
Proof.
  intros IH1 IH2 i k Hc Hw Hw'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_sig (wf_tm_ty Hi Hw)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1) as Hf.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1') as Hf'.
  pose proof (IH1 i l Hc Hf Hf') as E1.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1) as Hs.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1') as Hs'.
  pose proof (sig_fam_eq Hi HB (eqty_refl _ _ _ _ _ HB) (eqtm_sym _ _ _ _ _ _ _ E1) Hf' Hf) as EB.
  assert (Hs1 : [ G ; Γ ⊢[ i ] tmSnd l l' A B w' : B[lsingle (tmFst l l' A B w)] @ l' ])
    by (eapply wf_conv; [exact Hs' | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EB)]).
  pose proof (IH2 i l' Hc Hs Hs1) as E2.
  apply (lvl_eq_eqtm Hk). exact (decl_sig_ext i Hc G Γ l l' A B w w' W1 W2 HA HB Hw1 Hw1' E1 E2).
Qed.

(** The annotations of a projection agree with the inferred [Σ] type. *)
(** The unit type (M8c). *)
Lemma S_actnf_unit {G Γ l l'} : leqv l l' -> S_ty G Γ (tyUnit l) (tyUnit l').
Proof.
  intros Hl i k Hc HT HT'.
  destruct (inv_ty_unit HT) as ((_ & HΓ & W) & Hk). destruct (inv_ty_unit HT') as ((_ & _ & W') & _).
  apply (lvl_eq_eqty Hk). apply eqty_unit; [exact (compt_notV _ Hc) | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actmnf_code_unit {G Γ l k k'} : leqv k k' -> S_tm G Γ (tmUnit k) (tmUnit k') (tyU l).
Proof.
  intros Hl i kk Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_unit Hi Ht) as ((_ & HΓ & W) & Hk & HT). destruct (inv_code_unit Hi Ht') as ((_ & _ & W') & _).
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_unit; [exact (compt_notV _ Hc) | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actmnf_unit_eta {G Γ l w w'} : S_tm G Γ w w' (tyUnit l).
Proof.
  intros i k Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_unit (wf_tm_ty Hi Ht)) as ((_ & _ & W) & Hk).
  apply (lvl_eq_eqtm Hk). apply eqtm_unit_eta; [exact Hc | exact W | exact (lvl_eq_tm' Hk Ht) | exact (lvl_eq_tm' Hk Ht')].
Qed.

(** Strict equality (M10a). *)
Lemma S_actnf_seq {G Γ l l' A A' a a' b b'} : leqv l l' ->
  S_ty G Γ A A' -> S_tm G Γ a a' A -> S_tm G Γ b b' A -> S_ty G Γ (tySEq l A a b) (tySEq l' A' a' b').
Proof.
  intros Hl IHA IHa IHb i k Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_seq HT) as ((_ & W & HA & Ha & Hb) & Hk).
  destruct (inv_ty_seq HT') as ((_ & W' & HA' & Ha' & Hb') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (IHA i l Hc HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EA]. }
  pose proof (IHa i l Hc Ha (F _ Ha')) as Ea. pose proof (IHb i l Hc Hb (F _ Hb')) as Eb.
  apply (lvl_eq_eqty Hk). apply eqty_seq; assumption.
Qed.

Lemma S_actnf_sempty {G Γ l l'} : leqv l l' -> S_ty G Γ (tySEmpty l) (tySEmpty l').
Proof.
  intros Hl i k Hc HT HT'.
  destruct (inv_ty_sempty HT) as ((_ & HΓ & W) & Hk). destruct (inv_ty_sempty HT') as ((_ & _ & W') & _).
  apply (lvl_eq_eqty Hk). apply eqty_sempty; [exact Hc | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actmnf_seq_irr {G Γ l A a b w w'} : S_tm G Γ w w' (tySEq l A a b).
Proof.
  intros i k Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_seq (wf_tm_ty Hi Ht)) as ((_ & W & _) & Hk).
  apply (lvl_eq_eqtm Hk). apply eqtm_seq_irr; [exact Hc | exact W | exact (lvl_eq_tm' Hk Ht) | exact (lvl_eq_tm' Hk Ht')].
Qed.

Lemma S_actmnf_sempty_irr {G Γ l w w'} : S_tm G Γ w w' (tySEmpty l).
Proof.
  intros i k Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_sempty (wf_tm_ty Hi Ht)) as ((_ & _ & W) & Hk).
  apply (lvl_eq_eqtm Hk). apply eqtm_sempty_irr; [exact Hc | exact W | exact (lvl_eq_tm' Hk Ht) | exact (lvl_eq_tm' Hk Ht')].
Qed.

Lemma S_actmne_elimSEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  S_ty G Γ M M' -> S_ne G Γ (elimSEmpty l1 l2 M ν) (elimSEmpty l3 l4 M' ν') M.
Proof.
  intros H13 H24 IHM i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimSEmpty Hi Hx) as ((_ & W1 & W2 & HM & He) & Hk & HX).
  destruct (inv_elimSEmpty Hi Hx') as ((_ & W3 & W4 & HM' & He') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHM i l2 Hc HM (wft_lconv _ _ _ _ _ _ HM' E24)) as EM.
  assert (He1 : [ G ; Γ ⊢[ i ] ν' : tySEmpty l1 @ l1 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ He' E13) | rewrite Hi].
    apply eqty_sempty; [exact Hc | rewrite Hi; exact (ctx_of_wf_tm Hi He) | exact E13]. }
  pose proof (eqtm_sempty_irr _ _ _ _ _ _ Hc W1 He He1) as Ee.
  pose proof (eqtm_elimSEmpty _ _ _ _ _ _ _ _ _ _ _ Hc E13 E24 HM EM Ee) as Econg.
  split; [| split].
  - exact HX.
  - eapply eqty_trans; [exact HX' |]. apply (lvl_eq_eqty Hk'), eqty_sym.
    eapply eqty_lconv; [exact EM | exact (lequiv_sym _ _ _ E24)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

(** The identity type (M11a). *)
Lemma S_actnf_id {G Γ l l' A A' a a' b b'} : leqv l l' ->
  S_ty G Γ A A' -> S_tm G Γ a a' A -> S_tm G Γ b b' A -> S_ty G Γ (tyId l A a b) (tyId l' A' a' b').
Proof.
  intros Hl IHA IHa IHb i k Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_id HT) as ((_ & W & HA & Ha & Hb) & Hk).
  destruct (inv_ty_id HT') as ((_ & W' & HA' & Ha' & Hb') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (IHA i l Hc HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EA]. }
  pose proof (IHa i l Hc Ha (F _ Ha')) as Ea. pose proof (IHb i l Hc Hb (F _ Hb')) as Eb.
  apply (lvl_eq_eqty Hk). apply eqty_id; assumption.
Qed.

(** Two [refl]s at an [Id] type: their points are its left endpoint. *)
Lemma S_actmnf_refl {G Γ l A a b k k' C C' c c'} :
  S_tm G Γ (tmRefl k C c) (tmRefl k' C' c') (tyId l A a b).
Proof.
  intros i m Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_idrefl Hi Ht) as ((_ & Wk & HC & Hcc) & Hk & ET).
  destruct (inv_idrefl Hi Ht') as ((_ & _ & _ & _) & _ & ET').
  destruct (id_inj_c Hc (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ ET) ET')) as (Ekk & ECC & Ecc & _).
  pose proof (eqtm_idrefl _ _ _ _ _ _ _ _ _ Hc (lequiv_sym _ _ _ Ekk) HC ECC Ecc) as Econg.
  eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact ET].
Qed.

(** The code of [Id] (M11b): its pieces, and the other side's at this
    side's carrier. *)
Lemma code_id_prem {G i Γ k s t u T m} : compt i -> [ G ; Γ ⊢[ i ] tmId k s t u : T @ m ] ->
  lwf (gL G) k /\ [ G ; Γ ⊢[ i ] s : tyU k @ lsuc k ] /\
  [ G ; Γ ⊢[ i ] t : tyEl k s @ k ] /\ [ G ; Γ ⊢[ i ] u : tyEl k s @ k ].
Proof.
  intros Hc H. destruct (proj1 (inv_code_id (compt_typeof_self _ Hc) H)) as (_ & W & Hs & Ht & Hu). auto.
Qed.

Lemma code_U_conv {G i Γ k k' s} : compt i -> lequiv (gL G) k k' ->
  [ G ; Γ ⊢[ i ] s : tyU k' @ lsuc k' ] -> [ G ; Γ ⊢[ i ] s : tyU k @ lsuc k ].
Proof.
  intros Hc E Hs. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  eapply wf_conv; [eapply wf_lconv; [exact Hs | exact (lequiv_suc _ _ _ E)] | rewrite Hi].
  apply eqty_U; [exact Hv | rewrite Hi; exact (ctx_of_wf_tm Hi Hs) | exact E].
Qed.

Lemma code_El_conv {G i Γ k k' s s'} : compt i -> lequiv (gL G) k k' ->
  [ G ; Γ ⊢[ i ] s ≅ s' : tyU k @ lsuc k ] ->
  (forall x, [ G ; Γ ⊢[ i ] x : tyEl k' s' @ k' ] -> [ G ; Γ ⊢[ i ] x : tyEl k s @ k ]) /\
  [ G ; Γ ⊢[ i ] tyEl k s ≅ tyEl k' s' @ k ].
Proof.
  intros Hc E Es. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl k s ≅ tyEl k' s' @ k ]) by (apply eqty_El; assumption).
  split; [| exact EEl].
  intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EEl].
Qed.

Lemma S_actmnf_code_id {G Γ l k k' s s' t t' u u'} : leqv k k' ->
  S_tm G Γ s s' (tyU k) -> S_tm G Γ t t' (tyEl k s) -> S_tm G Γ u u' (tyEl k s) ->
  S_tm G Γ (tmId k s t u) (tmId k' s' t' u') (tyU l).
Proof.
  intros Hk0 IHs IHt IHu i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_id Hi Hx) as (_ & Hk & HT).
  destruct (code_id_prem Hc Hx) as (W & Hs & Ht & Hu). destruct (code_id_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  pose proof (IHs i (lsuc k) Hc Hs Hs1) as Es.
  destruct (code_El_conv Hc E Es) as (F & _).
  pose proof (IHt i k Hc Ht (F _ Ht')) as Et. pose proof (IHu i k Hc Hu (F _ Hu')) as Eu.
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_id; assumption.
Qed.

(** [J]'s motive context at the other side's carrier and point. *)
Lemma J_ctx_conv {G i Γ l1 l3 A A' a a'} : typeof i = i -> compt i -> lequiv (gL G) l1 l3 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l3 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] lshift 0
      : Γ ,, A' @ l3 ,, tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3 ].
Proof.
  intros Hi Hc H13 HA HA' HAA Haa.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (H31 : lequiv (gL G) l3 l1) by now apply lequiv_sym.
  assert (HA3 : [ G ; Γ ⊢[ i ] A @ l3 ]) by (eapply wft_lconv; [exact HA | exact H31]).
  assert (EA3 : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ]) by (eapply eqty_lconv; [apply eqty_sym, HAA | exact H31]).
  destruct (ctx_conv_ext Hi (lsub_wf_id G i Hi Γ HΓ) HA' EA3 HA3 H31) as [_ Hid1].
  assert (HΓA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply (ext_wf Hi); eauto using lequiv_wf_r).
  assert (Ea3 : [ G ; Γ ⊢[ i ] a' ≅ a : A' @ l3 ]).
  { eapply eqtm_lconv; [|exact H31]. eapply eqtm_conv; [apply eqtm_sym, Haa | rewrite Hi; apply eqty_sym, HAA]. }
  assert (Hv0 : [ G ; Γ ,, A' @ l3 ⊢[ i ] var 0 : A'⟨↑⟩ @ l3 ]) by (apply var0_wf; auto).
  assert (EId : [ G ; Γ ,, A' @ l3 ⊢[ i ] tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) ≅ tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l3 ]).
  { apply eqty_id; auto.
    - apply wk1_ty; auto.
    - apply wk1_eqty; auto.
    - apply wk1_eqtm with (T := A'); auto.
    - apply eqtm_refl; exact Hv0. }
  destruct (ctx_conv_ext Hi Hid1 (eqty_wf_l Hi EId) EId (eqty_wf_r Hi EId) H31) as [_ Hid2].
  exact Hid2.
Qed.

(** The two motive contexts are equal. *)
Lemma J_ctx_eq {G i Γ l1 l3 A A' a a'} : typeof i = i -> compt i -> lequiv (gL G) l1 l3 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ⊢[ i ] Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1
           ≅ Γ ,, A' @ l3 ,, tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3 ].
Proof.
  intros Hi Hc H13 HA HAA Haa.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; eauto using lequiv_wf_l).
  assert (EId : [ G ; Γ ,, A @ l1 ⊢[ i ] tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) ≅ tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l1 ]).
  { apply eqty_id; auto.
    - apply wk1_ty; auto.
    - apply wk1_eqty; auto.
    - apply wk1_eqtm with (T := A); auto.
    - apply eqtm_refl, var0_wf; auto. }
  apply eqc_ext; [| exact (eqty_wf_l Hi EId) | exact EId | exact H13].
  apply eqc_ext; [apply eqc_refl, HΓ | exact HA | exact HAA | exact H13].
Qed.

Lemma S_actmne_J {G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  S_ty G Γ A A' -> S_tm G Γ a a' A ->
  S_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  S_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] -> S_tm G Γ u u' A -> S_ne G Γ ν ν' W ->
  S_ne G Γ (tmJ l1 l2 A a M c u ν) (tmJ l3 l4 A' a' M' c' u' ν') M[lsingle2 u ν].
Proof.
  intros H13 H24 IHA IHa IHM IHc IHu IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_J Hi Hx) as ((_ & W1 & W2 & HA & Ha & HI & HM & Hcc & Hu & He) & Hk & HX).
  destruct (inv_J Hi Hx') as ((_ & W3 & W4 & HA' & Ha' & HI' & HM' & Hc' & Hu' & He') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l3 ] -> [ G ; Γ ⊢[ i ] x : A @ l1 ]).
  { intros x Hx0. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx0 E13) | rewrite Hi; exact EA]. }
  pose proof (IHa i l1 Hc Ha (F _ Ha')) as Ea. pose proof (IHu i l1 Hc Hu (F _ Hu')) as Eu.
  (* the motive, in the left context *)
  pose proof (J_ctx_conv Hi Hc E13 HA HA' EA Ea) as Hid.
  pose proof (wf_ty_subst Hi HM' Hid) as HM'1. rewrite nf_id_ty in HM'1 by exact (wf_ty_nf HM').
  assert (HM'2 : [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M' @ l2 ])
    by exact (wft_lconv _ _ _ _ _ _ HM'1 E24).
  pose proof (IHM i l2 Hc HM HM'2) as EM.
  (* the base case, at the left instance *)
  pose proof (eqtm_wf_r Hi Ea) as Ha'1.
  assert (Hr : [ G ; Γ ⊢[ i ] tmRefl l1 A a : tyId l1 A a a @ l1 ])
    by (apply wf_idrefl; auto).
  pose proof (pre_idrefl_r Hi Hv E13 HA EA (eqty_wf_r Hi EA) Ea Ha'1) as Hr'.
  assert (Hrr : [ G ; Γ ⊢[ i ] tmRefl l1 A a ≅ tmRefl l3 A' a' : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; auto).
  pose proof (lsub_eq_J Hi Hv W1 HA Ha Ha Ha'1 Ea Hr Hr' Hrr) as Hs.
  assert (HMs : [ G ; Γ ⊢[ i ] M[lsingle2 a (tmRefl l1 A a)] ≅ M'[lsingle2 a' (tmRefl l3 A' a')] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi EM (lsub_eq_l Hs)) | exact (wf_ty_func Hi HM'2 Hs)]. }
  assert (Hc'1 : [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc' E24) | rewrite Hi; exact HMs]. }
  pose proof (IHc i l2 Hc Hcc Hc'1) as Ec.
  destruct (IHν i l1 l3 _ _ Hc He He') as (_ & _ & Eν).
  pose proof (eqtm_J _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc E13 E24 HA EA Ea HI HM EM Ec Eu Eν) as Econg.
  (* the result types *)
  pose proof (eqtm_wf_r Hi Eu) as Hu'1. pose proof (eqtm_wf_r Hi Eν) as He'1.
  pose proof (lsub_eq_J Hi Hv W1 HA Ha Hu Hu'1 Eu He He'1 Eν) as Hs2.
  assert (EMν : [ G ; Γ ⊢[ i ] M[lsingle2 u ν] ≅ M'[lsingle2 u' ν'] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi EM (lsub_eq_l Hs2)) | exact (wf_ty_func Hi HM'2 Hs2)]. }
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact (lequiv_sym _ _ _ E24)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

Lemma proj_annots {G i Γ l1 l2 l3 l4 A A' B B' m m' A0 B0} : typeof i = i -> compt i ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> lwf (gL G) l1 ->
  [ G ; Γ ⊢[ i ] tySig l1 l2 A B ≅ tySig m m' A0 B0 @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tySig l3 l4 A' B' ≅ tySig m m' A0 B0 @ lmax l3 l4 ] ->
  lequiv (gL G) l1 l3 /\ lequiv (gL G) l2 l4 /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ].
Proof.
  intros Hi Hc HA W1 E0 E1.
  destruct (sig_inj_c Hc E0) as (Em1 & Em2 & EA0 & EB0).
  destruct (sig_inj_c Hc E1) as (Em3 & Em4 & EA1 & EB1).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em1) Em3) as E13.
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em2) Em4) as E24.
  assert (EA : [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ]).
  { eapply eqty_trans; [exact EA0 |]. apply eqty_sym.
    eapply eqty_lconv; [exact EA1 | exact E13]. }
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_eqty Hi EA' (lequiv_sym _ _ _ E13) HΓA EB1) as EB1'.
  split; [exact E13 | split; [exact E24 | split; [exact EA |]]].
  eapply eqty_trans; [exact EB0 |]. apply eqty_sym.
  eapply eqty_lconv; [exact EB1' | exact E24].
Qed.

Lemma S_actmne_fst {G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0} :
  S_ne G Γ ν ν' (tySig m m' A0 B0) ->
  S_ne G Γ (tmFst l1 l2 A B ν) (tmFst l3 l4 A' B' ν') A0.
Proof.
  intros IHν i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_fst Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν) & Hk & HX).
  destruct (inv_fst Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν') & Hk' & HX').
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (E0 & E1 & Eν).
  destruct (proj_annots Hi Hc HA W1 E0 E1) as (E13 & E24 & EA & EB).
  destruct (sig_inj_c Hc E0) as (_ & _ & EA0 & _).
  destruct (sig_inj_c Hc E1) as (_ & _ & EA1 & _).
  pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E13 E24 HA EA EB Eν) as Econg.
  split; [| split].
  - eapply eqty_trans; [exact HX | exact (lvl_eq_eqty Hk EA0)].
  - eapply eqty_trans; [exact HX' | exact (lvl_eq_eqty Hk' EA1)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

Lemma S_actmne_snd {G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0} :
  S_ne G Γ ν ν' (tySig m m' A0 B0) ->
  S_ne G Γ (tmSnd l1 l2 A B ν) (tmSnd l3 l4 A' B' ν') B0[lsingle (tmFst m m' A0 B0 ν)].
Proof.
  intros IHν i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_snd Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν) & Hk & HX).
  destruct (inv_snd Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν') & Hk' & HX').
  destruct (IHν i _ _ _ _ Hc Hν Hν') as (E0 & E1 & Eν).
  destruct (proj_annots Hi Hc HA W1 E0 E1) as (E13 & E24 & EA & EB).
  destruct (sig_inj_c Hc E0) as (Em1 & Em2 & EA0 & EB0).
  pose proof (eqtm_snd _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E13 E24 HA EA EB Eν) as Econg.
  (* the first projections the types mention *)
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hν) as Hf.
  pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ Em1) (lequiv_sym _ _ _ Em2) HA EA0 EB0
                (eqtm_refl _ _ _ _ _ _ Hν)) as Ef0.
  pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E13 E24 HA EA EB Eν) as Ef1.
  pose proof (sig_fam_eq Hi HB EB0 Ef0 Hf (eqtm_wf_r Hi Ef0)) as EBB0.
  pose proof (sig_fam_eq Hi HB EB Ef1 Hf (eqtm_wf_r Hi Ef1)) as EBB'.
  split; [| split].
  - eapply eqty_trans; [exact HX | exact (lvl_eq_eqty Hk EBB0)].
  - eapply eqty_trans; [exact HX' | apply (lvl_eq_eqty Hk')].
    eapply eqty_lconv; [| exact (lequiv_sym _ _ _ E24)].
    eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ EBB') | exact EBB0].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

(** The body types of [letbox] under their binding, at equal motives. *)
Lemma letboxT_body_eq {G Γ Δ l1 l2 M M'} : [ ⊢ gext G (gdTy Δ lC l2) ] -> [ G ; Δ ⊢[ lD ] ] ->
  lwf (gL G) l2 -> [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
  [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]
      ≅ M'⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ].
Proof.
  intros HGD HΔ Hl HMM.
  pose proof (MInst.gwk_ok_step (G := G) (D := gdTy Δ lC l2)) as Hγ.
  pose proof (gwk_eqty Hγ HGD HMM) as X. cbn [gcren] in X.
  pose proof (ctx_of_ext (ctx_of_eqty (i := lM) eq_refl X)) as HΓs.
  apply (eqty_single (i := lM) eq_refl X).
  apply wf_boxT; [exact HΓs | exact Hl | exact (gwk_ctx Hγ HGD HΔ) |].
  eapply wf_gv; [discriminate | exact (gwk_ctx Hγ HGD HΔ) | exact (ing_here _ (gdTy Δ lC l2))
                | apply lle_refl | reflexivity].
Qed.

Lemma letboxt_body_eq {G Γ Δ T l1 l2 M M'} : [ ⊢ gext G (gdTm Δ lC T l2) ] -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] T @ l2 ] -> lwf (gL G) l2 -> [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
  [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]
      ≅ M'⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ].
Proof.
  intros HGD HΔ HT Hl HMM.
  pose proof (MInst.gwk_ok_step (G := G) (D := gdTm Δ lC T l2)) as Hγ.
  pose proof (gwk_eqty Hγ HGD HMM) as X. cbn [gcren gren_ty] in X.
  pose proof (ctx_of_ext (ctx_of_eqty (i := lM) eq_refl X)) as HΓs.
  apply (eqty_single (i := lM) eq_refl X).
  apply wf_boxt; [exact HΓs | exact Hl | exact (gwk_ctx Hγ HGD HΔ) | exact (gwk_ty Hγ HGD HT) |].
  eapply wf_gu; [exact (gwk_ctx Hγ HGD HΔ) | exact (ing_here _ (gdTm Δ lC T l2)) | apply lle_refl |].
  exact (wf_ty_nf (gwk_ty Hγ HGD HT)).
Qed.

Lemma S_actmne_letboxT {G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  S_ctx G Δ Δ' -> S_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' ->
  S_tm (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  S_ne G Γ ν ν' W ->
  S_ne G Γ (letboxT l1 l2 Δ M t1 ν) (letboxT l3 l4 Δ' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 IHc IHM IHt IHν i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxT Hi Hx) as ((-> & W1 & W2 & HΔ & HM & Ht1 & Hν) & Hk & HX).
  destruct (inv_letboxT Hi Hx') as ((_ & W3 & W4 & HΔ' & HM' & Ht2 & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHc HΔ HΔ') as Ec.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ' l4 @ lzero ]) by (apply eqty_CTyp; assumption).
  pose proof (wf_conv _ _ _ _ _ _ _ Hν' HCC) as Hν1.
  destruct (IHν lM lzero lzero _ _ compt_M Hν Hν1) as (_ & _ & Eν).
  assert (HΓ1 : [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_CTyp; assumption | exact I]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC)
                                        (lequiv_refl (gL G) lzero I) HΓ1 HM') E13) as HM1.
  pose proof (IHM lM l1 compt_M HM HM1) as EM.
  assert (HGD : [ ⊢ gext G (gdTy Δ lC l2) ]) by (apply wfg_ty; [exact HG | exact HΔ | left; reflexivity | exact W2]).
  pose proof (gbind_obj_ty (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) HGD Ec E24) as Ho.
  pose proof (gbind_tm HG HGD Ho eq_refl Ht2) as Ht2a.
  pose proof (letboxT_body_eq HGD HΔ W2 EM) as EMb.
  assert (Ht2b : [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E13] | exact EMb]).
  pose proof (IHt lM l1 compt_M Ht1 Ht2b) as Et.
  pose proof (eqtm_letboxT _ _ _ _ _ _ _ _ _ _ _ _ _ _ E13 E24 HΔ HΔ' Ec HM EM HM' Et Ht2 Eν) as Econg.
  pose proof (pre_letbox_ty EM HM1 Eν Hν Hν1) as EMν.
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact (lequiv_sym _ _ _ E13)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
Qed.

Lemma S_actmne_letboxt {G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  S_ctx G Δ Δ' -> S_ty G Δ T T' -> S_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' ->
  S_tm (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  S_ne G Γ ν ν' W ->
  S_ne G Γ (letboxt l1 l2 Δ T M t1 ν) (letboxt l3 l4 Δ' T' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 IHc IHT IHM IHt IHν i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxt Hi Hx) as ((-> & W1 & W2 & HΔ & HT & HM & Ht1 & Hν) & Hk & HX).
  destruct (inv_letboxt Hi Hx') as ((_ & W3 & W4 & HΔ' & HT' & HM' & Ht2 & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E24)) as HT1.
  pose proof (IHT lD l2 compt_D HT HT1) as ET.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ' T' l4 @ lzero ]) by (apply eqty_CTrm; assumption).
  pose proof (wf_conv _ _ _ _ _ _ _ Hν' HCC) as Hν1.
  destruct (IHν lM lzero lzero _ _ compt_M Hν Hν1) as (_ & _ & Eν).
  assert (HΓ1 : [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_CTrm; assumption | exact I]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC)
                                        (lequiv_refl (gL G) lzero I) HΓ1 HM') E13) as HM1.
  pose proof (IHM lM l1 compt_M HM HM1) as EM.
  assert (HGD : [ ⊢ gext G (gdTm Δ lC T l2) ]) by (apply wfg_tm; [exact HG | exact HT | right; reflexivity | exact W2]).
  pose proof (gbind_obj_tm HGD Ec ET E24) as Ho.
  pose proof (gbind_tm HG HGD Ho eq_refl Ht2) as Ht2a.
  pose proof (letboxt_body_eq HGD HΔ HT W2 EM) as EMb.
  assert (Ht2b : [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E13] | exact EMb]).
  pose proof (IHt lM l1 compt_M Ht1 Ht2b) as Et.
  pose proof (eqtm_letboxt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E13 E24 HΔ HΔ' Ec HT HT' ET HM EM HM' Et Ht2 Eν)
    as Econg.
  pose proof (pre_letbox_ty EM HM1 Eν Hν Hν1) as EMν.
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact (lequiv_sym _ _ _ E13)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
Qed.

(** ** The recursors *)

(** [mkrb] is injective in its branches (the thirteen that exist). *)
Lemma mkrb_inj_br {MT Mt bs MT' Mt' bs'} : mkrb MT Mt bs = mkrb MT' Mt' bs' ->
  forall k, k < nbr -> bs k = bs' k.
Proof.
  intros H k Hk. unfold mkrb in H. injection H; intros.
  br_all ltac:(destruct k as [|k]; [assumption|]). lia.
Qed.

Lemma elimT_core {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' t t' i k k' X X'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> S_ctx G Δ Δ' ->
  S_ty (recGT G) (recΓT Γ) MT MT' -> S_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> S_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  compt i ->
  [ G ; Γ ⊢[ i ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : X @ k ] ->
  [ G ; Γ ⊢[ i ] elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' t' : X' @ k' ] ->
  ([ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] -> [ G ; Γ ⊢[ lM ] t' : tyCTyp Δ l @ lzero ] ->
   [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTyp Δ l @ lzero ]) ->
  [ G ; Γ ⊢[ i ] X ≅ motT (wrapMT MT) l Δ t @ k ] /\ [ G ; Γ ⊢[ i ] X' ≅ motT (wrapMT MT) l Δ t @ k' ] /\
  [ G ; Γ ⊢[ i ] elimT l1 l2 (mkrb MT Mt bs) l Δ t ≅ elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' t' : X @ k ].
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb Hc Hx Hx' Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimT Hi Hx) as (MT0 & Mt0 & bs0 & (Erb & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs & Hν)
                                   & Hk & HX).
  destruct (inv_elimT Hi Hx') as (MT1 & Mt1 & bs1 & (Erb' & _ & _ & W1' & W2' & Wl' & HΔ' & HMT' & HMt' & Hbc'
                                                     & Hbs' & Hν') & Hk' & HX').
  destruct (mkrb_inj_MT Erb) as [<- <-]. destruct (mkrb_inj_MT Erb') as [<- <-].
  pose proof (mkrb_inj_br Erb) as Eb. pose proof (mkrb_inj_br Erb') as Eb'.
  pose proof (leqv_lequiv _ _ _ W1 W1' H1) as E1. pose proof (leqv_lequiv _ _ _ W2 W2' H2) as E2.
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as El.
  pose proof (IHc HΔ HΔ') as Ec.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  pose proof (IHT lM _ compt_M HMT (wft_lconv _ _ _ _ _ _ HMT' (lequiv_ush 1 E1))) as EMT.
  pose proof (IHt lM _ compt_M HMt (wft_lconv _ _ _ _ _ _ HMt' (lequiv_ush 1 E2))) as EMt.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l ≅ tyCTyp Δ' l' @ lzero ]) by (apply eqty_CTyp; assumption).
  pose proof (Ht Hν (wf_conv _ _ _ _ _ _ _ Hν' HCC)) as Eν.
  pose proof (declM_motT_eq EMT W1 El Ec Eν) as Emot.
  assert (Hbs0 : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                                        bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
    by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj)).
  assert (Hbs1 : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                                        bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ])
    by (intros j Hj; rewrite (Eb' j Hj); exact (Hbs' j Hj)).
  assert (Ebr : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                                       bs j ≅ bs' j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ]).
  { intros j Hj. apply (IHb j Hj lM _ compt_M (Hbs0 j Hj)).
    exact (branch_conv j Hj EMT EMt E1 E2 HΓ (Hbc j Hj) (Hbc' j Hj) (Hbs1 j Hj)). }
  pose proof (eqtm_elimT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Emot E1 E2 El HΔ HΔ' Ec HMT EMT HMT' HMt EMt HMt'
                Hbc Hbc' Ebr Hbs1 Eν) as Econg.
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact Emot | exact (lequiv_sym _ _ _ E1)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
Qed.

Lemma S_actmne_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> S_ctx G Δ Δ' ->
  S_ty (recGT G) (recΓT Γ) MT MT' -> S_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> S_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  S_ne G Γ ν ν' W ->
  S_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν')
    (motT (wrapMT MT) l Δ ν).
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb IHν i k k' X X' Hc Hx Hx'.
  apply (elimT_core H1 H2 Hl IHc IHT IHt IHb Hc Hx Hx').
  intros Hν Hν'. exact (proj2 (proj2 (IHν lM lzero lzero _ _ compt_M Hν Hν'))).
Qed.

Lemma S_actmne_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' U d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> S_ctx G Δ Δ' ->
  S_ty (recGT G) (recΓT Γ) MT MT' -> S_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> S_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  S_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d)))
    (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' (boxT (tyGvar U d')))
    (motT (wrapMT MT) l Δ (boxT (tyGvar U d))).
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb Hd i k k' X X' Hc Hx Hx'.
  apply (elimT_core H1 H2 Hl IHc IHT IHt IHb Hc Hx Hx').
  intros Hν Hν'. exact (eqtm_leq _ _ _ _ _ _ Hν Hν' (conj eq_refl Hd)).
Qed.

Lemma elimt_core {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' t t' i k k' X X'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> S_ctx G Δ Δ' -> S_ty G Δ T T' ->
  S_ty (recGT G) (recΓT Γ) MT MT' -> S_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> S_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  compt i ->
  [ G ; Γ ⊢[ i ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t : X @ k ] ->
  [ G ; Γ ⊢[ i ] elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' t' : X' @ k' ] ->
  ([ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l @ lzero ] -> [ G ; Γ ⊢[ lM ] t' : tyCTrm Δ T l @ lzero ] ->
   [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTrm Δ T l @ lzero ]) ->
  [ G ; Γ ⊢[ i ] X ≅ mott (wrapMt Mt) l Δ T t @ k ] /\ [ G ; Γ ⊢[ i ] X' ≅ mott (wrapMt Mt) l Δ T t @ k' ] /\
  [ G ; Γ ⊢[ i ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t ≅ elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' t' : X @ k ].
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb Hc Hx Hx' Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimt Hi Hx) as (MT0 & Mt0 & bs0 & (Erb & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs
                                   & HT & Hν) & Hk & HX).
  destruct (inv_elimt Hi Hx') as (MT1 & Mt1 & bs1 & (Erb' & _ & _ & W1' & W2' & Wl' & HΔ' & HMT' & HMt' & Hbc'
                                                     & Hbs' & HT' & Hν') & Hk' & HX').
  destruct (mkrb_inj_MT Erb) as [<- <-]. destruct (mkrb_inj_MT Erb') as [<- <-].
  pose proof (mkrb_inj_br Erb) as Eb. pose proof (mkrb_inj_br Erb') as Eb'.
  pose proof (leqv_lequiv _ _ _ W1 W1' H1) as E1. pose proof (leqv_lequiv _ _ _ W2 W2' H2) as E2.
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as El.
  pose proof (IHc HΔ HΔ') as Ec.
  pose proof (IHi lD l compt_D HT (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ El))) as ET.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  pose proof (IHT lM _ compt_M HMT (wft_lconv _ _ _ _ _ _ HMT' (lequiv_ush 1 E1))) as EMT.
  pose proof (IHt lM _ compt_M HMt (wft_lconv _ _ _ _ _ _ HMt' (lequiv_ush 1 E2))) as EMt.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l ≅ tyCTrm Δ' T' l' @ lzero ]) by (apply eqty_CTrm; assumption).
  pose proof (Ht Hν (wf_conv _ _ _ _ _ _ _ Hν' HCC)) as Eν.
  pose proof (declM_mott_eq EMt W2 El Ec ET Eν) as Emot.
  assert (Hbs0 : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                                        bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
    by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj)).
  assert (Hbs1 : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                                        bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ])
    by (intros j Hj; rewrite (Eb' j Hj); exact (Hbs' j Hj)).
  assert (Ebr : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                                       bs j ≅ bs' j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ]).
  { intros j Hj. apply (IHb j Hj lM _ compt_M (Hbs0 j Hj)).
    exact (branch_conv j Hj EMT EMt E1 E2 HΓ (Hbc j Hj) (Hbc' j Hj) (Hbs1 j Hj)). }
  pose proof (eqtm_elimt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Emot E1 E2 El HΔ HΔ' Ec HT HT' ET
                HMT EMT HMT' HMt EMt HMt' Hbc Hbc' Ebr Hbs1 Eν) as Econg.
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact Emot | exact (lequiv_sym _ _ _ E2)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
Qed.

Lemma S_actmne_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> S_ctx G Δ Δ' -> S_ty G Δ T T' ->
  S_ty (recGT G) (recΓT Γ) MT MT' -> S_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> S_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  S_ne G Γ ν ν' W ->
  S_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' ν')
    (mott (wrapMt Mt) l Δ T ν).
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb IHν i k k' X X' Hc Hx Hx'.
  apply (elimt_core H1 H2 Hl IHc IHi IHT IHt IHb Hc Hx Hx').
  intros Hν Hν'. exact (proj2 (proj2 (IHν lM lzero lzero _ _ compt_M Hν Hν'))).
Qed.

Lemma S_actmne_elimt_glob {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' c c'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> S_ctx G Δ Δ' -> S_ty G Δ T T' ->
  S_ty (recGT G) (recΓT Γ) MT MT' -> S_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> S_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  boxed_global c -> tm_leq c c' ->
  S_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c))
    (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' (boxt c'))
    (mott (wrapMt Mt) l Δ T (boxt c)).
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb Hg Hd i k k' X X' Hc Hx Hx'.
  apply (elimt_core H1 H2 Hl IHc IHi IHT IHt IHb Hc Hx Hx').
  intros Hν Hν'. exact (eqtm_leq _ _ _ _ _ _ Hν Hν' Hd).
Qed.

(** ** The applications of [UΠ], [CΠ], [TΠ] *)

(** Instances of an equation (as [inst_ty]). *)
Lemma inst_eqty {G Γ D o T T' l} : [ G ; Γ ⊢[ lM ] ] -> dnfo o -> dnf_decl D -> gobj_wf G o D ->
  [ gext G D ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ lM ] T⦃gsingle o⦄ ≅ T'⦃gsingle o⦄ @ l ].
Proof.
  intros HΓ Ho HD Hwf HT.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gsubstitution)))) _ _ _ _ _ _ HT (gΨ G) _
                (gsub_wf_single' HΓ Ho HD Hwf)) as X.
  unfold gwk_to in X; cbn in X. rewrite gcren_S_gsingle in X by exact (wf_ctx_dnf HΓ). exact X.
Qed.
Lemma inst_c_eqty {G Γ Δ T T' l} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ)⦄ ≅ T'⦃gsingle (GCtx Δ)⦄ @ l ].
Proof. intros HΓ HΔ; apply inst_eqty; [exact HΓ | exact (wf_ctx_dnf HΔ) | exact I | exact HΔ]. Qed.
Lemma inst_t_eqty {G Γ Δ A l T T' l'} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l' ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A)⦄ ≅ T'⦃gsingle (GTy A)⦄ @ l' ].
Proof. intros HΓ HA; apply inst_eqty; [exact HΓ | exact (wf_ty_dnf HA) | exact (wf_ty_dnf_ctx HA) | exact HA]. Qed.

Lemma lvl_eq_lequiv' {L k a b} : lvl_eq L k a -> lequiv L a b -> lequiv L k b.
Proof. intros [->|H] E; [exact E | exact (lequiv_trans _ _ _ _ H E)]. Qed.
Lemma lvl_eq_both {L k a b} : lvl_eq L k a -> lvl_eq L k b -> lwf L a -> lwf L b -> lequiv L a b.
Proof.
  intros [->|H1] [->|H2] Wa Wb.
  - now apply lequiv_refl.
  - exact H2.
  - exact (lequiv_sym _ _ _ H1).
  - exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ H1) H2).
Qed.

Lemma lequivs_of_leqvs L ls ls' : Forall2 leqv ls ls' -> Forall (lwf L) ls -> Forall (lwf L) ls' ->
  Forall2 (lequiv L) ls ls'.
Proof.
  induction 1 as [|l l' ls ls' Hl Hs IH]; intros W W'; [constructor|].
  inversion W; inversion W'; subst. constructor; [apply leqv_lequiv; assumption | auto].
Qed.

Lemma S_actmne_uapp {G Γ n l T ν ν' ls ls'} : S_ne G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' ->
  S_ne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros IH _ Hls i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_uapp Hi Hx) as (n0 & l0 & T0 & (-> & W0 & HT0 & Hlen & Hw & Hν) & Hk & HX).
  destruct (inv_uapp Hi Hx') as (n1 & l1 & T1 & (_ & W1 & HT1 & Hlen' & Hw' & Hν') & Hk' & HX').
  destruct (IH lM lomega lomega _ _ compt_M Hν Hν') as (E0 & E1 & Eν).
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (declM_upi_inj E0) as (-> & El0 & EB0).
  destruct (declM_upi_inj E1) as (En & El1 & EB1). subst n1.
  pose proof (Forall2_length Hls) as Hlen2.
  pose proof (lequivs_of_leqvs _ _ _ Hls Hw Hw') as Hls'.
  pose proof (eqtm_uapp _ _ _ _ _ _ _ _ _ W0 HT0 Hlen Hls' Eν) as Econg.
  pose proof (eqty_wf_r (i := lM) eq_refl EB0) as HT.
  subst n0.
  pose proof (uinst_eqty HG (wf_ctx_dnf HΓ) Hw EB0) as I0.
  pose proof (uinst_eqty HG (wf_ctx_dnf HΓ) Hw' EB1) as I1.
  pose proof (lequiv_uinst _ _ _ _ W0 Hls') as Ek'.
  assert (HT' : [ gctx_uwk (length ls') G ; Γ⟨ush (length ls')⟩ᵤ ⊢[ lM ] T @ l0 ]) by (rewrite <- Hlen2; exact HT).
  assert (HTs : [ G ; Γ ⊢[ lM ] T[uext ls lvar]ᵤ ≅ T[uext ls' lvar]ᵤ @ lvsubst l0 (uext ls lvar) ]).
  { apply eqty_leq.
    - exact (uinst_ty HG (wf_ctx_dnf HΓ) Hw HT).
    - eapply wft_lconv; [exact (uinst_ty HG (wf_ctx_dnf HΓ) Hw' HT') | exact Ek'].
    - apply (proj1 leq_usubst_all); [apply leqv_uext, (lequivs_leqv _ _ _ Hls') | apply ty_leq_refl]. }
  (* the two instance levels agree *)
  assert (Hok : usub_ok (uext ls' lvar) (gL G) (length ls' + gL G))
    by (apply usub_ok_uext; [exact Hw' | apply usub_ok_id]).
  pose proof (lequiv_lvsubst _ _ _ _ _ Hok El1) as E1l.
  assert (El01 : lequiv (length ls' + gL G) l0 l1).
  { rewrite <- Hlen2. exact (lequiv_trans _ _ _ _ El0 (lequiv_sym _ _ _ (eq_rect _ (fun m => lequiv (m + gL G) l1 l) El1 _ (eq_sym Hlen2)))). }
  pose proof (lequiv_lvsubst _ _ _ _ _ Hok El01) as E01.
  split; [| split].
  - eapply eqty_trans; [exact HX | exact (lvl_eq_eqty Hk I0)].
  - eapply eqty_trans; [exact HX' |].
    eapply eqty_trans; [exact (lvl_eq_eqty Hk' I1) |].
    apply eqty_sym, (lvl_eq_eqty Hk'). eapply eqty_lconv; [exact HTs |].
    exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ E01) (lequiv_sym _ _ _ Ek')).
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
Qed.

Lemma S_actmne_capp {G Γ l T ν ν' Δ Δ'} : S_ne G Γ ν ν' (tyCPi l T) -> S_ctx G Δ Δ' ->
  S_ne G Γ (capp ν Δ) (capp ν' Δ') T⦃gsingle (GCtx Δ)⦄.
Proof.
  intros IH IHc i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_capp Hi Hx) as (l0 & T0 & (-> & W0 & HT0 & HΔ & Hν & _) & Hk & HX).
  destruct (inv_capp Hi Hx') as (l1 & T1 & (_ & W1 & HT1 & HΔ' & Hν' & _) & Hk' & HX').
  destruct (IH lM _ _ _ _ compt_M Hν Hν') as (E0 & E1 & Eν).
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  pose proof (IHc HΔ HΔ') as Ec.
  destruct (declM_cpi_inj E0) as (El0 & EB0).
  destruct (declM_cpi_inj E1) as (El1 & EB1).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ El0) El1) as E01.
  pose proof (eqtm_capp _ _ _ _ _ _ _ _ W0 HT0 HΔ HΔ' Ec (declM_inst_c_eq HΓ W0 HT0 Ec) Eν) as Econg.
  pose proof (eqty_wf_r (i := lM) eq_refl EB0) as HT.
  pose proof (inst_c_eqty HΓ HΔ EB0) as I0.
  pose proof (inst_c_eqty HΓ HΔ' EB1) as I1.
  pose proof (declM_inst_c_eq HΓ W0 HT Ec) as IT.
  split; [| split].
  - eapply eqty_trans; [exact HX | exact (lvl_eq_eqty Hk I0)].
  - eapply eqty_trans; [exact HX' |].
    eapply eqty_trans; [exact (lvl_eq_eqty Hk' I1) |].
    apply eqty_sym, (lvl_eq_eqty Hk'). eapply eqty_lconv; [exact IT | exact (lequiv_sym _ _ _ E01)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
Qed.

Lemma S_actmne_tapp {G Γ Δ l l' T ν ν' A A'} : S_ne G Γ ν ν' (tyTPi Δ l l' T) -> S_ty G Δ A A' ->
  S_ne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof.
  intros IH IHA i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T0 & (-> & Hν & HΔ0 & W0 & W0' & HT0 & HA & _) & Hk & HX).
  destruct (inv_tapp Hi Hx') as (Δ1 & l1 & l1' & T1 & (_ & Hν' & HΔ1 & W1 & W1' & HT1 & HA' & _) & Hk' & HX').
  destruct (IH lM _ _ _ _ compt_M Hν Hν') as (E0 & E1 & Eν).
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  destruct (declM_tpi_inj E0) as (Ec0 & El0 & El0' & EB0).
  destruct (declM_tpi_inj E1) as (Ec1 & El1 & El1' & EB1).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ El0') El1') as E01'.
  (* the arguments, compared in the inferred type's context *)
  pose proof (decl_ty_ctxconv_D Ec0 HA (lequiv_refl _ _ W0)) as HAΔ.
  pose proof (decl_ty_ctxconv_D Ec1 HA' (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ El1) El0)) as HA'Δ.
  pose proof (IHA lD l0 compt_D HAΔ HA'Δ) as EAΔ.
  pose proof (ctxconv_eqty (eqctx_sym_D Ec0) (i := lD) eq_refl EAΔ) as EA0.
  pose proof (eqtm_tapp _ _ _ _ _ _ _ _ _ _ Eν HΔ0 W0 W0' HT0 HA EA0 (declM_inst_t_eq HΓ W0' HT0 EA0))
    as Econg.
  pose proof (inst_t_eqty HΓ HA EB0) as I0.
  pose proof (inst_t_eqty HΓ HA' EB1) as I1.
  pose proof (eqty_wf_r (i := lM) eq_refl E0) as HX0. destruct (inv_ty_tpi HX0) as ((_ & _ & HΔ & Wl & Wl' & HT) & Hl).
  pose proof (eqty_lconv _ _ _ _ _ _ _ EAΔ El0) as EAl.
  pose proof (declM_inst_t_eq HΓ Wl' HT EAl) as IT.
  split; [| split].
  - eapply eqty_trans; [exact HX | exact (lvl_eq_eqty Hk I0)].
  - eapply eqty_trans; [exact HX' |].
    eapply eqty_trans; [exact (lvl_eq_eqty Hk' I1) |].
    apply eqty_sym, (lvl_eq_eqty Hk'). eapply eqty_lconv; [exact IT | exact (lequiv_sym _ _ _ El1')].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
Qed.

(** ** Soundness *)

Theorem ac_sound_all :
  (forall G Γ T T', ac_ty G Γ T T' -> S_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> S_ty G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> S_ty G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> S_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> S_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> S_tm G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> S_ne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> S_ne G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> S_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros; try assumption;
    first
    [ solve [eapply S_act_red; eassumption] | solve [eapply S_actnf_nat] | solve [eapply S_actnf_U; eassumption]
    | solve [eapply S_actnf_pi; eassumption] | solve [eapply S_actnf_CTyp; eassumption]
    | solve [eapply S_actnf_CTrm; eassumption] | solve [eapply S_actnf_upi; eassumption]
    | solve [eapply S_actnf_cpi; eassumption] | solve [eapply S_actnf_tpi; eassumption]
    | solve [eapply S_actne_gvar; eassumption] | solve [eapply S_actne_El; eassumption]
    | solve [eapply S_acc_nil] | solve [eapply S_acc_var] | solve [eapply S_acc_ext; eassumption]
    | solve [eapply S_actm_red; eassumption]
    | solve [eapply S_actmnf_code_nat] | solve [eapply S_actmnf_code_U; eassumption]
    | solve [eapply S_actmnf_code_pi; eassumption] | solve [eapply S_actmnf_zero]
    | solve [eapply S_actmnf_succ; eassumption] | solve [eapply S_actmnf_ne; eassumption]
    | solve [eapply S_actmnf_eta; eassumption] | solve [eapply S_actmnf_ueta; eassumption]
    | solve [eapply S_actmnf_ceta; eassumption] | solve [eapply S_actmnf_teta; eassumption]
    | solve [eapply S_actmnf_boxT; eassumption] | solve [eapply S_actmnf_boxt; eassumption]
    | solve [eapply S_actmne_var; eassumption] | solve [eapply S_actmne_gvar; eassumption]
    | solve [eapply S_actmne_natrec; eassumption] | solve [eapply S_actmne_app; eassumption]
    | solve [eapply S_actmne_letboxT; eassumption] | solve [eapply S_actmne_letboxt; eassumption]
    | solve [eapply S_actmne_elimT; eassumption] | solve [eapply S_actmne_elimT_gvar; eassumption]
    | solve [eapply S_actmne_elimt; eassumption] | solve [eapply S_actmne_elimt_glob; eassumption]
    | solve [eapply S_actmne_uapp; eassumption] | solve [eapply S_actmne_capp; eassumption]
    | solve [eapply S_actmne_tapp; eassumption] | solve [eapply S_actmnee_red; eassumption]
    | solve [eapply S_acs_pt; eassumption]
    | solve [eapply S_actnf_sig; eassumption] | solve [eapply S_actmnf_code_sig; eassumption]
    | solve [eapply S_actmnf_sig_eta; eassumption] | solve [eapply S_actmne_fst; eassumption]
    | solve [eapply S_actmne_snd; eassumption]
    | solve [eapply S_actnf_unit; eassumption] | solve [eapply S_actmnf_code_unit; eassumption]
    | solve [eapply S_actmnf_unit_eta]
    | solve [eapply S_actnf_seq; eassumption] | solve [eapply S_actnf_sempty; eassumption]
    | solve [eapply S_actmnf_seq_irr] | solve [eapply S_actmnf_sempty_irr]
    | solve [eapply S_actmne_elimSEmpty; eassumption]
    | solve [eapply S_actnf_id; eassumption] | solve [eapply S_actmnf_refl]
    | solve [eapply S_actmne_J; eassumption] | solve [eapply S_actmnf_code_id; eassumption] ].
Qed.

(** Algorithmically convertible types (terms) of the computing layers,
    well formed (typed) at a level, are declaratively equal. *)
Theorem ac_ty_sound {G i Γ T T' k} : compt i -> ac_ty G Γ T T' ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. intros Hc H; exact (proj1 ac_sound_all _ _ _ _ H i k Hc). Qed.

Theorem ac_tm_sound {G i Γ t t' T k} : compt i -> ac_tm G Γ t t' T ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof. intros Hc H; exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_sound_all)))) _ _ _ _ _ H i k Hc). Qed.
