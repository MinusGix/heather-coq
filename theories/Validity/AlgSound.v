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

Lemma in_ctx_det {Γ n T l T' l'} : in_ctx Γ n T l -> in_ctx Γ n T' l' -> T = T' /\ l = l'.
Proof.
  intros H; revert T' l'; induction H as [Γ A l | Γ A l B l'' n H IH]; intros T' l' H';
    inversion H' as [? ? ? | ? ? ? ? ? ? H'']; subst; auto.
  destruct (IH _ _ H'') as [-> ->]; auto.
Qed.

Lemma in_gctx_det {Ψ n D D'} : in_gctx Ψ n D -> in_gctx Ψ n D' -> D = D'.
Proof.
  intros H; revert D'; induction H as [Ψ D | Ψ D D0 n H IH]; intros D' H';
    inversion H' as [? ? | ? ? ? ? H'']; subst; auto.
  now rewrite (IH _ H'').
Qed.

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
Definition S_ne G Γ ν ν' T : Prop := forall i k A A', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k ] ->
  [ G ; Γ ⊢[ i ] A ≅ T @ k ] /\ [ G ; Γ ⊢[ i ] A' ≅ T @ k ] /\ [ G ; Γ ⊢[ i ] ν ≅ ν' : A @ k ].
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
  destruct (IH i (lsuc l) (tyU l) (tyU l) Hc Hν Hν1) as (_ & _ & Eν).
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
Proof. intros _ IH i k Hc Hν Hν'. exact (proj2 (proj2 (IH i k W W Hc Hν Hν'))). Qed.

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
  intros IH Hr Hw i k A A' Hc Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (IH i k A A' Hc Hν Hν') as (EA & EA' & Eν).
  pose proof (red_ty_sound Hc (eqty_wf_r Hi EA) Hr Hw) as ET.
  split; [| split]; [eapply eqty_trans; eassumption | eapply eqty_trans; eassumption | exact Eν].
Qed.

Lemma S_acs_pt {G Γ d d' Δ} :
  (forall n A k, in_ctx Δ n A k -> S_tm G Γ (llk d n) (llk d' n) A[d]) -> S_sub G Γ d d' Δ.
Proof.
  intros IH i Hc HΔ Hd Hd'. pose proof (compt_typeof_self _ Hc) as Hi.
  apply (lsub_eq_pt Hi Δ Γ d d' HΔ Hd Hd'). intros n A k Hin Hr.
  exact (IH n A k Hin i k Hc (lsub_wf_var Hd Hin) Hr).
Qed.
