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
From DeLaM.Validity Require Export AlgPrereq DeclConsequences.

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

(** [Vec] and [Fin] at a neutral length (M14a). *)
Lemma S_actne_vec {G Γ l l' A A' ν ν' W} : leqv l l' -> S_ty G Γ A A' -> S_ne G Γ ν ν' W ->
  S_ty G Γ (tyVec l A ν) (tyVec l' A' ν').
Proof.
  intros Hl IHA IHν i k Hc HX HX'.
  destruct (inv_ty_vec HX) as ((_ & W1 & HA & Hν) & Hk). destruct (inv_ty_vec HX') as ((_ & W2 & HA' & Hν') & _).
  pose proof (leqv_lequiv _ _ _ W1 W2 Hl) as E.
  pose proof (IHA i l Hc HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  destruct (IHν i lzero lzero tyNat tyNat Hc Hν Hν') as (_ & _ & Eν).
  apply (lvl_eq_eqty Hk). apply eqty_vec; auto using compt_notV.
Qed.

Lemma S_actne_fin {G Γ ν ν' W} : S_ne G Γ ν ν' W -> S_ty G Γ (tyFin ν) (tyFin ν').
Proof.
  intros IHν i k Hc HX HX'.
  destruct (inv_ty_fin HX) as ((_ & Hν) & Hk). destruct (inv_ty_fin HX') as ((_ & Hν') & _).
  destruct (IHν i lzero lzero tyNat tyNat Hc Hν Hν') as (_ & _ & Eν).
  apply (lvl_eq_eqty Hk). apply eqty_fin; auto using compt_notV.
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

(** The empty type (M12a). *)
Lemma S_actnf_empty {G Γ l l'} : leqv l l' -> S_ty G Γ (tyEmpty l) (tyEmpty l').
Proof.
  intros Hl i k Hc HT HT'.
  destruct (inv_ty_empty HT) as ((_ & HΓ & W) & Hk). destruct (inv_ty_empty HT') as ((_ & _ & W') & _).
  apply (lvl_eq_eqty Hk). apply eqty_empty; [(apply compt_notV; exact Hc) | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actmnf_empty_irr {G Γ l w w'} : S_tm G Γ w w' (tyEmpty l).
Proof.
  intros i k Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_empty (wf_tm_ty Hi Ht)) as ((_ & _ & W) & Hk).
  apply (lvl_eq_eqtm Hk). apply eqtm_empty_irr; [exact Hc | exact W | exact (lvl_eq_tm' Hk Ht) | exact (lvl_eq_tm' Hk Ht')].
Qed.

(** The scrutinees are not compared: irrelevance relates them. *)
Lemma S_actmne_elimEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  S_ty G (Γ ,, tyEmpty l2 @ l2) M M' ->
  S_ne G Γ (elimEmpty l1 l2 M ν) (elimEmpty l3 l4 M' ν') M[lsingle ν].
Proof.
  intros H13 H24 IHM i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimEmpty Hi Hx) as ((_ & W1 & W2 & HM & Hν) & Hk & HX).
  destruct (inv_elimEmpty Hi Hx') as ((_ & W3 & W4 & HM' & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  (* the right pieces at the left's types *)
  assert (HE : [ G ; Γ ⊢[ i ] tyEmpty l4 ≅ tyEmpty l2 @ l4 ])
    by (apply eqty_empty; [(apply compt_notV; exact Hc) | rewrite Hi; exact HΓ | exact (lequiv_sym _ _ _ E24)]).
  assert (HΓE : [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_empty; [(apply compt_notV; exact Hc) | rewrite Hi; exact HΓ | exact W2] | exact W2]).
  pose proof (stab_ty Hi HE (lequiv_sym _ _ _ E24) HΓE HM') as HM'1.
  pose proof (IHM i l1 Hc HM (wft_lconv _ _ _ _ _ _ HM'1 E13)) as EM.
  assert (Hν'1 : [ G ; Γ ⊢[ i ] ν' : tyEmpty l2 @ l2 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hν' | exact E24] | rewrite Hi; apply eqty_sym;
          eapply eqty_lconv; [exact HE | exact E24]]).
  pose proof (eqtm_empty_irr _ _ _ _ _ _ Hc W2 Hν Hν'1) as Eν.
  pose proof (eqtm_elimEmpty _ _ _ _ _ _ _ _ _ _ _ (compt_notV _ Hc) E13 E24 HM EM Eν) as Econg.
  assert (EMν : [ G ; Γ ⊢[ i ] M[lsingle ν] ≅ M'[lsingle ν'] @ l1 ]).
  { eapply eqty_trans; [exact (eqty_single Hi EM Hν) |].
    exact (wf_ty_func Hi (wft_lconv _ _ _ _ _ _ HM'1 E13) (lsub_eq_single Hi Hν Hν'1 Eν)). }
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact (lequiv_sym _ _ _ E13)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

(** Propositional truncation (M16a). *)
Lemma S_actnf_sq {G Γ l l' A A'} : leqv l l' -> S_ty G Γ A A' -> S_ty G Γ (tySq l A) (tySq l' A').
Proof.
  intros Hl IHA i k Hc HT HT'.
  destruct (inv_ty_sq HT) as ((_ & W & HA) & Hk). destruct (inv_ty_sq HT') as ((_ & W' & HA') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (IHA i l Hc HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  apply (lvl_eq_eqty Hk). apply eqty_sq; [exact Hc | exact E | exact HA | exact EA].
Qed.

Lemma S_actmnf_sq_irr {G Γ l A w w'} : S_tm G Γ w w' (tySq l A).
Proof.
  intros i k Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_sq (wf_tm_ty Hi Ht)) as ((_ & W & _) & Hk).
  apply (lvl_eq_eqtm Hk). apply eqtm_sq_irr; [exact Hc | exact W | exact (lvl_eq_tm' Hk Ht) | exact (lvl_eq_tm' Hk Ht')].
Qed.

(** Neither the scrutinees nor the steps are compared: irrelevance relates
    them, at the squash each lives in. *)
Lemma S_actmne_elimSq {G Γ l1 l2 l3 l4 A A' M M' c c' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  S_ty G Γ A A' -> S_ty G (Γ ,, tySq l1 A @ l1) M M' ->
  S_ne G Γ (tmElimSq l1 l2 A M c ν) (tmElimSq l3 l4 A' M' c' ν') (tySq l2 M[lsingle ν]).
Proof.
  intros H13 H24 IHA IHM i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimSq Hi Hx) as ((_ & W1 & W2 & HA & HM & Hcc & Hν) & Hk & HX).
  destruct (inv_elimSq Hi Hx') as ((_ & W3 & W4 & HA' & HM' & Hcc' & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (lequiv_sym _ _ _ E13) as E31. pose proof (lequiv_sym _ _ _ E24) as E42.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (ES : [ G ; Γ ⊢[ i ] tySq l1 A ≅ tySq l3 A' @ l1 ])
    by (apply eqty_sq; [exact Hc | exact E13 | exact HA | exact EA]).
  assert (HS : [ G ; Γ ⊢[ i ] tySq l3 A' ≅ tySq l1 A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ ES) | exact E31]).
  assert (HΓS : [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_sq; [exact Hc | exact W1 | exact HA] | exact W1]).
  assert (HΓS' : [ G ; Γ ,, tySq l3 A' @ l3 ⊢[ i ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_sq; [exact Hc | exact W3 | exact HA'] | exact W3]).
  (* the right motive in the left's context, and the left's in the right's *)
  pose proof (stab_ty Hi HS E31 HΓS HM') as HM'1.
  pose proof (IHM i l2 Hc HM (wft_lconv _ _ _ _ _ _ HM'1 E24)) as EM.
  pose proof (stab_eqty Hi ES E13 HΓS' EM) as EM3.
  pose proof (stab_ty Hi ES E13 HΓS' HM) as HM3.
  (* the right scrutinee and step at the left's types *)
  assert (Hν'1 : [ G ; Γ ⊢[ i ] ν' : tySq l1 A @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hν' | exact E13] | rewrite Hi; exact ES]).
  pose proof (eqtm_sq_irr _ _ _ _ _ _ _ Hc W1 Hν Hν'1) as Eν.
  assert (Hcc'1 : [ G ; Γ ,, A @ l1 ⊢[ i ] c' : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ]).
  { refine (sq_branch_r Hi Hc E31 E42 HA' _ (wft_lconv _ _ _ _ _ _ HA E31) HM' _ (wft_lconv _ _ _ _ _ _ HM3 E42) Hcc').
    - eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact E31].
    - eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM3) | exact E42]. }
  pose proof (eqtm_sq_irr _ _ _ _ _ _ _ Hc W2 Hcc Hcc'1) as Ecc.
  pose proof (eqtm_elimSq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc E13 E24 HA EA HM EM Ecc Eν) as Econg.
  assert (EMν : [ G ; Γ ⊢[ i ] tySq l2 M[lsingle ν] ≅ tySq l4 M'[lsingle ν'] @ l2 ]).
  { apply eqty_sq; [exact Hc | exact E24 | exact (wf_ty_single Hi HM Hν) |].
    eapply eqty_trans; [exact (eqty_single Hi EM Hν) |].
    exact (wf_ty_func Hi (wft_lconv _ _ _ _ _ _ HM'1 E24) (lsub_eq_single Hi Hν Hν'1 Eν)). }
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact E42].
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

(** Binary sums (M12b). *)
Lemma sum_inj_c {G i Γ l l1 l2 l3 l4 A A' B B'} : compt i ->
  [ G ; Γ ⊢[ i ] tySum l1 l2 A B ≅ tySum l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\ [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ].
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_sum_inj H) | exact (declM_sum_inj H)]. Qed.

(** An injection's payload, at the summand of a [+] type it has. *)
Lemma inl_payload {G i Γ l l' A B k1 k2 C D a m} : compt i ->
  [ G ; Γ ⊢[ i ] tmInl k1 k2 C D a : tySum l l' A B @ m ] -> [ G ; Γ ⊢[ i ] a : A @ l ].
Proof.
  intros Hc Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_inl Hi Ht) as ((_ & _ & _ & _ & _ & Ha) & _ & ET).
  destruct (sum_inj_c Hc ET) as (E1 & _ & EAC & _).
  eapply wf_conv; [eapply wf_lconv; [exact Ha | now apply lequiv_sym] | rewrite Hi; exact EAC].
Qed.
Lemma inr_payload {G i Γ l l' A B k1 k2 C D b m} : compt i ->
  [ G ; Γ ⊢[ i ] tmInr k1 k2 C D b : tySum l l' A B @ m ] -> [ G ; Γ ⊢[ i ] b : B @ l' ].
Proof.
  intros Hc Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_inr Hi Ht) as ((_ & _ & _ & _ & _ & Hb) & _ & ET).
  destruct (sum_inj_c Hc ET) as (_ & E2 & _ & EBD).
  eapply wf_conv; [eapply wf_lconv; [exact Hb | now apply lequiv_sym] | rewrite Hi; exact EBD].
Qed.

Lemma S_actnf_sum {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  S_ty G Γ A A' -> S_ty G Γ B B' -> S_ty G Γ (tySum l1 l2 A B) (tySum l3 l4 A' B').
Proof.
  intros H13 H24 IHA IHB i k Hc HT HT'.
  destruct (inv_ty_sum HT) as ((_ & W1 & W2 & HA & HB) & Hk).
  destruct (inv_ty_sum HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (IHB i l2 Hc HB (wft_lconv _ _ _ _ _ _ HB' E24)) as EB.
  apply (lvl_eq_eqty Hk). apply eqty_sum; [(apply compt_notV; exact Hc) | ..]; assumption.
Qed.

(** Two injections at a [+] type: their payloads at its summand. *)
Lemma S_actmnf_inl {G Γ l l' A B k1 k2 k3 k4 C D C' D' a a'} : S_tm G Γ a a' A ->
  S_tm G Γ (tmInl k1 k2 C D a) (tmInl k3 k4 C' D' a') (tySum l l' A B).
Proof.
  intros IHa i m Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_inl Hi Ht) as ((_ & W1 & W2 & HC & HD & Ha) & Hk & ET).
  destruct (inv_inl Hi Ht') as ((_ & W3 & W4 & HC' & HD' & Ha') & _ & ET').
  destruct (sum_inj_c Hc ET) as (E1 & E2 & EAC & EBD).
  destruct (sum_inj_c Hc (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ ET) ET')) as (E31 & E42 & ECC & EDD).
  assert (EAC' : [ G ; Γ ⊢[ i ] A ≅ C' @ l ]).
  { eapply eqty_trans; [exact EAC | eapply eqty_lconv; [exact ECC | now apply lequiv_sym]]. }
  assert (Ha1 : [ G ; Γ ⊢[ i ] a : A @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ha | now apply lequiv_sym] | rewrite Hi; exact EAC]. }
  assert (Ha'1 : [ G ; Γ ⊢[ i ] a' : A @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ha' | eapply lequiv_trans; [apply lequiv_sym, E1 | apply lequiv_sym, E31]]
                    | rewrite Hi; exact EAC']. }
  pose proof (IHa i l Hc Ha1 Ha'1) as Ea.
  assert (Ea1 : [ G ; Γ ⊢[ i ] a ≅ a' : C @ k1 ]).
  { eapply eqtm_conv; [eapply eqtm_lconv; [exact Ea | exact E1] | rewrite Hi].
    eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EAC) | exact E1]. }
  assert (Econg : [ G ; Γ ⊢[ i ] tmInl k1 k2 C D a ≅ tmInl k3 k4 C' D' a' : tySum k1 k2 C D @ lmax k1 k2 ])
    by (apply eqtm_inl; first [(apply compt_notV; exact Hc) | now apply lequiv_sym | assumption]).
  eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact ET].
Qed.

Lemma S_actmnf_inr {G Γ l l' A B k1 k2 k3 k4 C D C' D' b b'} : S_tm G Γ b b' B ->
  S_tm G Γ (tmInr k1 k2 C D b) (tmInr k3 k4 C' D' b') (tySum l l' A B).
Proof.
  intros IHb i m Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_inr Hi Ht) as ((_ & W1 & W2 & HC & HD & Hb) & Hk & ET).
  destruct (inv_inr Hi Ht') as ((_ & W3 & W4 & HC' & HD' & Hb') & _ & ET').
  destruct (sum_inj_c Hc ET) as (E1 & E2 & EAC & EBD).
  destruct (sum_inj_c Hc (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ ET) ET')) as (E31 & E42 & ECC & EDD).
  assert (EBD' : [ G ; Γ ⊢[ i ] B ≅ D' @ l' ]).
  { eapply eqty_trans; [exact EBD | eapply eqty_lconv; [exact EDD | now apply lequiv_sym]]. }
  assert (Hb1 : [ G ; Γ ⊢[ i ] b : B @ l' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hb | now apply lequiv_sym] | rewrite Hi; exact EBD]. }
  assert (Hb'1 : [ G ; Γ ⊢[ i ] b' : B @ l' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hb' | eapply lequiv_trans; [apply lequiv_sym, E2 | apply lequiv_sym, E42]]
                    | rewrite Hi; exact EBD']. }
  pose proof (IHb i l' Hc Hb1 Hb'1) as Eb.
  assert (Eb1 : [ G ; Γ ⊢[ i ] b ≅ b' : D @ k2 ]).
  { eapply eqtm_conv; [eapply eqtm_lconv; [exact Eb | exact E2] | rewrite Hi].
    eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EBD) | exact E2]. }
  assert (Econg : [ G ; Γ ⊢[ i ] tmInr k1 k2 C D b ≅ tmInr k3 k4 C' D' b' : tySum k1 k2 C D @ lmax k1 k2 ])
    by (apply eqtm_inr; first [(apply compt_notV; exact Hc) | now apply lequiv_sym | assumption]).
  eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact ET].
Qed.

(** [case]'s right-hand premises at the left's contexts, types and levels:
    the motive first, then (given the motives equal) the branches and the
    scrutinee. *)
Lemma case_right_left {G i Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1' c2' ν'} : compt i ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] A' @ l4 ] -> [ G ; Γ ⊢[ i ] B' @ l5 ] ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, tySum l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' @ l6 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] /\
  ([ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
   [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
   [ G ; Γ ,, A' @ l4 ⊢[ i ] c1' : M'⟨rlift ↑⟩[lsingle (tmInl l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ l6 ] ->
   [ G ; Γ ,, B' @ l5 ⊢[ i ] c2' : M'⟨rlift ↑⟩[lsingle (tmInr l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ l6 ] ->
   [ G ; Γ ⊢[ i ] ν' : tySum l4 l5 A' B' @ lmax l4 l5 ] ->
   [ G ; Γ ,, A @ l1 ⊢[ i ] M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))]
       ≅ M'⟨rlift ↑⟩[lsingle (tmInl l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ l3 ] /\
   [ G ; Γ ,, B @ l2 ⊢[ i ] M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))]
       ≅ M'⟨rlift ↑⟩[lsingle (tmInr l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ l3 ] /\
   [ G ; Γ ,, A @ l1 ⊢[ i ] c1' : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] /\
   [ G ; Γ ,, B @ l2 ⊢[ i ] c2' : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] /\
   [ G ; Γ ⊢[ i ] ν' : tySum l1 l2 A B @ lmax l1 l2 ]).
Proof.
  intros Hc E14 E25 E36 HA HB HA' HB' EA EB HM'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof (lequiv_wf_l _ _ _ E14) as W1. pose proof (lequiv_wf_l _ _ _ E25) as W2.
  pose proof (wft_lconv _ _ _ _ _ _ HA' E14) as HA'1. pose proof (wft_lconv _ _ _ _ _ _ HB' E25) as HB'2.
  assert (HS : [ G ; Γ ⊢[ i ] tySum l1 l2 A B @ lmax l1 l2 ]) by (apply wft_sum; assumption).
  pose proof (ext_wf Hi HS (conj W1 W2)) as HΓS.
  assert (Hm : lequiv (gL G) (lmax l4 l5) (lmax l1 l2)) by (apply lequiv_max; now apply lequiv_sym).
  assert (ESS : [ G ; Γ ⊢[ i ] tySum l1 l2 A B ≅ tySum l4 l5 A' B' @ lmax l1 l2 ]) by (apply eqty_sum; assumption).
  assert (ES' : [ G ; Γ ⊢[ i ] tySum l4 l5 A' B' ≅ tySum l1 l2 A B @ lmax l4 l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ ESS) | exact Hm]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi ES' Hm HΓS HM') E36) as HM'3.
  split; [exact HM'3|]. intros HM EM Hc1' Hc2' Hν'.
  pose proof (ext_wf Hi HA W1) as HΓA. pose proof (ext_wf Hi HB W2) as HΓB.
  pose proof (var0_wf _ _ Hi _ _ _ HΓA) as Hv0A. pose proof (var0_wf _ _ Hi _ _ _ HΓB) as Hv0B.
  assert (EBA : [ G ; Γ ,, A @ l1 ⊢[ i ] M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))]
                   ≅ M'⟨rlift ↑⟩[lsingle (tmInl l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ l3 ]).
  { apply (case_branch_eq Hi HΓA HM EM HM'3).
    - apply wf_inl; [exact Hv | exact W1 | exact W2 | exact (wk1_ty _ _ Hi _ _ _ _ _ HΓA HA)
                    | exact (wk1_ty _ _ Hi _ _ _ _ _ HΓA HB) | exact Hv0A].
    - exact (pre_inl_r Hi Hv E14 E25 (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA EA) (wk1_ty _ _ Hi _ _ _ _ _ HΓA HA'1)
               (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA EB) (wk1_ty _ _ Hi _ _ _ _ _ HΓA HB'2) Hv0A).
    - apply eqtm_inl; [exact Hv | exact E14 | exact E25 | exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA EA)
                      | exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA EB) | exact (eqtm_refl _ _ _ _ _ _ Hv0A)]. }
  assert (EBB : [ G ; Γ ,, B @ l2 ⊢[ i ] M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))]
                   ≅ M'⟨rlift ↑⟩[lsingle (tmInr l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ l3 ]).
  { apply (case_branch_eq Hi HΓB HM EM HM'3).
    - apply wf_inr; [exact Hv | exact W1 | exact W2 | exact (wk1_ty _ _ Hi _ _ _ _ _ HΓB HA)
                    | exact (wk1_ty _ _ Hi _ _ _ _ _ HΓB HB) | exact Hv0B].
    - exact (pre_inr_r Hi Hv E14 E25 (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB EA) (wk1_ty _ _ Hi _ _ _ _ _ HΓB HA'1)
               (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB EB) (wk1_ty _ _ Hi _ _ _ _ _ HΓB HB'2) Hv0B).
    - apply eqtm_inr; [exact Hv | exact E14 | exact E25 | exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB EA)
                      | exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB EB) | exact (eqtm_refl _ _ _ _ _ _ Hv0B)]. }
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | now apply lequiv_sym]).
  assert (EB' : [ G ; Γ ⊢[ i ] B' ≅ B @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EB) | now apply lequiv_sym]).
  pose proof (stab_tm Hi EA' (lequiv_sym _ _ _ E14) HΓA Hc1') as Hc1'1.
  pose proof (stab_tm Hi EB' (lequiv_sym _ _ _ E25) HΓB Hc2') as Hc2'1.
  refine (conj EBA (conj EBB (conj _ (conj _ _)))).
  - eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc1'1 E36) | rewrite Hi; exact EBA].
  - eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc2'1 E36) | rewrite Hi; exact EBB].
  - eapply wf_conv; [eapply wf_lconv; [exact Hν' | apply lequiv_sym, Hm] | rewrite Hi; exact ESS].
Qed.

Lemma S_actmne_case {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' ν ν' W} :
  leqv l1 l4 -> leqv l2 l5 -> leqv l3 l6 -> S_ty G Γ A A' -> S_ty G Γ B B' ->
  S_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' ->
  S_tm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
  S_tm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
  S_ne G Γ ν ν' W ->
  S_ne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) (tmCase l4 l5 l6 A' B' M' c1' c2' ν') M[lsingle ν].
Proof.
  intros H14 H25 H36 IHA IHB IHM IHc1 IHc2 IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Hν) & Hk & HX).
  destruct (inv_case Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & Hc1' & Hc2' & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W4 H14) as E14. pose proof (leqv_lequiv _ _ _ W2 W5 H25) as E25.
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E14)) as EA.
  pose proof (IHB i l2 Hc HB (wft_lconv _ _ _ _ _ _ HB' E25)) as EB.
  destruct (case_right_left (M := M) (c1' := c1') (c2' := c2') (ν' := ν') Hc E14 E25 E36 HA HB HA' HB' EA EB HM') as [HM'3 Hbr].
  pose proof (IHM i l3 Hc HM HM'3) as EM.
  destruct (Hbr HM EM Hc1' Hc2' Hν') as (_ & _ & Hc1'2 & Hc2'2 & Hν'1).
  pose proof (IHc1 i l3 Hc Hc1 Hc1'2) as Ec1. pose proof (IHc2 i l3 Hc Hc2 Hc2'2) as Ec2.
  destruct (IHν i (lmax l1 l2) (lmax l1 l2) (tySum l1 l2 A B) (tySum l1 l2 A B) Hc Hν Hν'1) as (_ & _ & Eν).
  assert (Econg : [ G ; Γ ⊢[ i ] tmCase l1 l2 l3 A B M c1 c2 ν ≅ tmCase l4 l5 l6 A' B' M' c1' c2' ν'
                     : M[lsingle ν] @ l3 ])
    by (apply eqtm_case; [(apply compt_notV; exact Hc) | ..]; assumption).
  assert (EMν : [ G ; Γ ⊢[ i ] M[lsingle ν] ≅ M'[lsingle ν'] @ l3 ]).
  { eapply eqty_trans; [exact (eqty_single Hi EM Hν) |].
    exact (wf_ty_func Hi HM'3 (lsub_eq_single Hi Hν Hν'1 Eν)). }
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact (lequiv_sym _ _ _ E36)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

(** Well-founded trees (M13a). *)
Lemma W_inj_c {G i Γ l l1 l2 l3 l4 A A' B B'} : compt i ->
  [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ].
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_W_inj H) | exact (declM_W_inj H)]. Qed.

(** Propositional truncation (M16a). *)
Lemma sq_inj_c {G i Γ l l1 l2 A A'} : compt i ->
  [ G ; Γ ⊢[ i ] tySq l1 A ≅ tySq l2 A' @ l ] -> lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ].
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_sq_inj H) | exact (declM_sq_inj H)]. Qed.

Lemma S_actnf_W {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  S_ty G Γ A A' -> S_ty G (Γ ,, A @ l1) B B' -> S_ty G Γ (tyW l1 l2 A B) (tyW l3 l4 A' B').
Proof.
  intros H13 H24 IHA IHB i k Hc HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_W HT) as ((_ & W1 & W2 & HA & HB) & Hk).
  destruct (inv_ty_W HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  pose proof (IHB i l2 Hc HB (wft_lconv _ _ _ _ _ _ HB1 E24)) as EB.
  apply (lvl_eq_eqty Hk). apply eqty_W; first [assumption | (apply compt_notV; eassumption)].
Qed.

(** Two [sup]s at a [W] type: their shapes at the shape type, their child
    functions at the children's type. *)
Lemma S_actmnf_sup {G Γ l l' A B k1 k2 k3 k4 C D C' D' a a' f f'} : S_tm G Γ a a' A ->
  S_tm G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) ->
  S_tm G Γ (tmSup k1 k2 C D a f) (tmSup k3 k4 C' D' a' f') (tyW l l' A B).
Proof.
  intros IHa IHf i m Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_sup Hi Ht) as ((_ & W1 & W2 & HC & HD & Ha & Hf) & Hk & ET).
  destruct (inv_sup Hi Ht') as ((_ & W3 & W4 & HC' & HD' & Ha' & Hf') & _ & ET').
  destruct (W_inj_c Hc ET) as (E1 & E2 & EAC & EBD).
  destruct (W_inj_c Hc ET') as (E3 & E4 & EAC' & EBD').
  pose proof (lequiv_wf_r _ _ _ E1) as Wl. pose proof (lequiv_wf_r _ _ _ E2) as Wl'.
  pose proof (eqty_wf_l Hi EAC) as HA. pose proof (eqty_wf_l Hi EBD) as HB.
  assert (Ha1 : [ G ; Γ ⊢[ i ] a : A @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ha | now apply lequiv_sym] | rewrite Hi; exact EAC]. }
  assert (Ha'1 : [ G ; Γ ⊢[ i ] a' : A @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ha' | now apply lequiv_sym] | rewrite Hi; exact EAC']. }
  pose proof (IHa i l Hc Ha1 Ha'1) as Ea.
  assert (HW : [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW : [ G ; Γ ⊢[ i ] tyW l l' A B ≅ tyW k1 k2 C D @ lmax l l' ])
    by (apply eqty_W; first [assumption | (apply compt_notV; eassumption) | now apply lequiv_sym]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l l' A B ≅ tyW k3 k4 C' D' @ lmax l l' ])
    by (apply eqty_W; first [assumption | (apply compt_notV; eassumption) | now apply lequiv_sym]).
  assert (HBa : [ G ; Γ ⊢[ i ] B[lsingle a] @ l' ]) by exact (wf_ty_single Hi HB Ha1).
  pose proof (ext_wf Hi HBa Wl') as HΓB.
  assert (Hm : lequiv (gL G) (lmax l l') (lmax k1 k2)) by (apply lequiv_max; now apply lequiv_sym).
  assert (Hm' : lequiv (gL G) (lmax l l') (lmax k3 k4)) by (apply lequiv_max; now apply lequiv_sym).
  assert (EF : [ G ; Γ ⊢[ i ] tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩
                 ≅ tyPi k2 (lmax k1 k2) D[lsingle a] (tyW k1 k2 C D)⟨↑⟩ @ lmax l' (lmax l l') ]).
  { apply eqty_pi; first [exact Hv | now apply lequiv_sym | exact Hm | exact HBa | idtac].
    - exact (eqty_single Hi EBD Ha1).
    - exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB EW). }
  assert (EF' : [ G ; Γ ⊢[ i ] tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩
                  ≅ tyPi k4 (lmax k3 k4) D'[lsingle a'] (tyW k3 k4 C' D')⟨↑⟩ @ lmax l' (lmax l l') ]).
  { apply eqty_pi; first [exact Hv | now apply lequiv_sym | exact Hm' | exact HBa | idtac].
    - eapply eqty_trans; [apply (wf_ty_func Hi HB (d' := lsingle a')); now apply lsub_eq_single|].
      exact (eqty_single Hi EBD' Ha'1).
    - exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB EW'). }
  assert (HmF : lequiv (gL G) (lmax l' (lmax l l')) (lmax k2 (lmax k1 k2)))
    by (apply lequiv_max; [now apply lequiv_sym | exact Hm]).
  assert (HmF' : lequiv (gL G) (lmax l' (lmax l l')) (lmax k4 (lmax k3 k4)))
    by (apply lequiv_max; [now apply lequiv_sym | exact Hm']).
  assert (Hf1 : [ G ; Γ ⊢[ i ] f : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hf | exact HmF] | rewrite Hi; exact EF]. }
  assert (Hf'1 : [ G ; Γ ⊢[ i ] f' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hf' | exact HmF'] | rewrite Hi; exact EF']. }
  pose proof (IHf i _ Hc Hf1 Hf'1) as Ef.
  (* the congruence at the [sup]s' annotations, then back to the type *)
  assert (Econg : [ G ; Γ ⊢[ i ] tmSup l l' A B a f ≅ tmSup k3 k4 C' D' a' f' : tyW l l' A B @ lmax l l' ])
    by (apply eqtm_sup; first [(apply compt_notV; exact Hc) | exact Hc | now apply lequiv_sym | assumption]).
  assert (Ecan : [ G ; Γ ⊢[ i ] tmSup l l' A B a f ≅ tmSup k1 k2 C D a f : tyW l l' A B @ lmax l l' ])
    by (apply eqtm_sup; first [(apply compt_notV; exact Hc) | exact Hc | now apply lequiv_sym | assumption
                              | apply eqtm_refl; assumption]).
  pose proof (eqtm_trans _ _ _ _ _ _ _ _ (eqtm_sym _ _ _ _ _ _ _ Ecan) Econg) as E0.
  apply (lvl_eq_eqtm Hk). eapply eqtm_lconv; [exact E0 | apply lequiv_max; assumption].
Qed.

(** The children's type at equal shapes. *)
Lemma fty_conv {G i Γ l l' A B a a'} : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a' ≅ a : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyPi l' (lmax l l') B[lsingle a'] (tyW l l' A B)⟨↑⟩
      ≅ tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ].
Proof.
  intros Hc Wl Wl' HA HB Ha Ha' Eaa. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  assert (HW : [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  pose proof (wf_ty_single Hi HB Ha') as HBa'.
  pose proof (ext_wf Hi HBa' Wl') as HΓB.
  apply eqty_pi; first [exact Hv | apply lequiv_refl; assumption | apply lequiv_refl; cbn; split; assumption
                       | exact HBa' | idtac].
  - apply (wf_ty_func Hi HB (d' := lsingle a)). now apply lsub_eq_single.
  - apply eqty_refl. exact (wk1_ty _ _ Hi _ _ _ _ _ HΓB HW).
Qed.

(** A [sup] at a [W] type: its pieces at the type's. *)
Lemma sup_parts {G i Γ l l' A B k1 k2 C D a f m} : compt i ->
  [ G ; Γ ⊢[ i ] tmSup k1 k2 C D a f : tyW l l' A B @ m ] ->
  lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] a : A @ l ] /\
  [ G ; Γ ⊢[ i ] f : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ].
Proof.
  intros Hc Ht. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_sup Hi Ht) as ((_ & W1 & W2 & HC & HD & Ha & Hf) & Hk & ET).
  destruct (W_inj_c Hc ET) as (E1 & E2 & EAC & EBD).
  pose proof (lequiv_wf_r _ _ _ E2) as Wl'.
  pose proof (eqty_wf_l Hi EAC) as HA. pose proof (eqty_wf_l Hi EBD) as HB.
  assert (Ha1 : [ G ; Γ ⊢[ i ] a : A @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ha | now apply lequiv_sym] | rewrite Hi; exact EAC]. }
  assert (EW : [ G ; Γ ⊢[ i ] tyW l l' A B ≅ tyW k1 k2 C D @ lmax l l' ])
    by (apply eqty_W; first [assumption | (apply compt_notV; eassumption) | now apply lequiv_sym]).
  assert (HBa : [ G ; Γ ⊢[ i ] B[lsingle a] @ l' ]) by exact (wf_ty_single Hi HB Ha1).
  pose proof (ext_wf Hi HBa Wl') as HΓB.
  assert (Hm : lequiv (gL G) (lmax l l') (lmax k1 k2)) by (apply lequiv_max; now apply lequiv_sym).
  assert (EF : [ G ; Γ ⊢[ i ] tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩
                 ≅ tyPi k2 (lmax k1 k2) D[lsingle a] (tyW k1 k2 C D)⟨↑⟩ @ lmax l' (lmax l l') ]).
  { apply eqty_pi; first [exact Hv | now apply lequiv_sym | exact Hm | exact HBa | idtac].
    - exact (eqty_single Hi EBD Ha1).
    - exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB EW). }
  assert (HmF : lequiv (gL G) (lmax l' (lmax l l')) (lmax k2 (lmax k1 k2)))
    by (apply lequiv_max; [now apply lequiv_sym | exact Hm]).
  refine (conj (lequiv_wf_r _ _ _ E1) (conj Wl' (conj HA (conj HB (conj Ha1 _))))).
  eapply wf_conv; [eapply wf_lconv; [exact Hf | exact HmF] | rewrite Hi; exact EF].
Qed.

(** [elim_W]'s step telescope at the other side's pieces. *)
Lemma W_ctx_conv {G i Γ l1 l2 l3 l4 l5 l6 A A' B B' M M'} : typeof i = i -> compt i ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l4 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A' @ l4 ⊢[ i ] B' @ l5 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' @ l6 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3 ⊢[ i ]
      lshift 0 : Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ,, wihty l4 l5 l6 A' B' M' @ lmax l5 l6 ].
Proof.
  intros Hi Hc H14 H25 H36 HA HA' EA HB HB' EB HM HM' EM. pose proof (compt_notV _ Hc) as Hv.
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
  (* the shapes *)
  assert (HA4 : [ G ; Γ ⊢[ i ] A @ l4 ]) by (eapply wft_lconv; [exact HA | exact H41]).
  assert (EA4 : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ]) by (eapply eqty_lconv; [apply eqty_sym, EA | exact H41]).
  destruct (ctx_conv_ext Hi (lsub_wf_id G i Hi Γ HΓ) HA' EA4 HA4 H41) as [_ Hid1].
  pose proof (ext_wf Hi HA' W4) as HΓA'.
  pose proof (ext_wf Hi HA W1) as HΓA.
  (* the positions, on the primed shapes *)
  assert (HB'A : [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ])
    by (eapply wft_lconv; [exact (stab_ty Hi EA4 H41 HΓA HB') | exact H25]).
  assert (HBA' : [ G ; Γ ,, A' @ l4 ⊢[ i ] B @ l2 ]) by exact (stab_ty Hi EA H14 HΓA' HB).
  assert (EB' : [ G ; Γ ,, A' @ l4 ⊢[ i ] B' ≅ B @ l5 ]).
  { eapply eqty_lconv; [|exact H52]. exact (stab_eqty Hi EA H14 HΓA' (eqty_sym _ _ _ _ _ _ EB)). }
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (HW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' @ lmax l4 l5 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' ≅ tyW l1 l2 A B @ lmax l4 l5 ])
    by (apply eqty_W; first [(apply compt_notV; exact Hc) | exact Hc | assumption | eapply eqty_lconv; [|exact H41]; apply eqty_sym, EA]).
  (* the child functions *)
  pose proof (W_fty_wf Hi Hv (X := A') (lx := l4) W4 W5 HW' HB') as HF'.
  assert (HFA' : [ G ; Γ ,, A' @ l4 ⊢[ i ] wfty l1 l2 A B @ lmax l5 (lmax l4 l5) ])
    by (eapply wft_lconv; [exact (W_fty_wf Hi Hv (X := A') (lx := l4) W1 W2 HW HBA') | exact HLF]).
  pose proof (ext_wf Hi HB' W5) as HΓA'B'.
  assert (EF : [ G ; Γ ,, A' @ l4 ⊢[ i ] wfty l4 l5 A' B' ≅ wfty l1 l2 A B @ lmax l5 (lmax l4 l5) ]).
  { apply eqty_pi; first [exact Hv | assumption | apply lequiv_max; assumption | idtac].
    exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA'B' (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' EW')). }
  destruct (ctx_conv_ext Hi Hid1 HF' EF HFA' HLF) as [_ Hid2].
  (* the induction hypotheses *)
  pose proof (ext_wf Hi HF' (lwf_max W5 WL')) as HΓA'F'.
  pose proof (ext_wf Hi HW WL) as HΓW. pose proof (ext_wf Hi HW' WL') as HΓW'.
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ]) by (apply eqty_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EM' : [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' ≅ M @ l6 ]).
  { eapply eqty_lconv; [|exact H63]. exact (stab_eqty Hi EW (lequiv_sym _ _ _ HL) HΓW' (eqty_sym _ _ _ _ _ _ EM)). }
  assert (HM4 : [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M @ l6 ])
    by (eapply wft_lconv; [exact (stab_ty Hi EW (lequiv_sym _ _ _ HL) HΓW' HM) | exact H63]).
  pose proof (W_ih_wf Hi Hv W4 W5 W6 HW' HB' HM' HΓA'F' (eqty_refl' HF') (lequiv_refl _ _ (lwf_max W5 WL')))
    as HI'.
  pose proof (W_ih_eq Hi Hv H41 H52 H63 HA' HB' EB' (wft_lconv _ _ _ _ _ _ HBA' H52) HM' EM' HW EW' HF' EF) as EI.
  assert (HIA' : [ G ; Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ⊢[ i ] wihty l1 l2 l3 A B M @ lmax l5 l6 ]).
  { eapply wft_lconv; [|exact HLI].
    exact (W_ih_wf Hi Hv W1 W2 W3 HW HBA' HM HΓA'F' EF HLF). }
  destruct (ctx_conv_ext Hi Hid2 HI' EI HIA' HLI) as [_ Hid3].
  exact Hid3.
Qed.

(** The right [elim_W]'s step at the left telescope and step type. *)
Lemma elimW_step_left {G i Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c'} : compt i ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l4 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A' @ l4 ⊢[ i ] B' @ l5 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' @ l6 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] wihty l1 l2 l3 A B M @ lmax l2 l3 ] ->
  [ G ; Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ,, wihty l4 l5 l6 A' B' M' @ lmax l5 l6
      ⊢[ i ] c' : wstepty l4 l5 A' B' M' @ l6 ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ⊢[ i ] c' : wstepty l1 l2 A B M @ l3 ].
Proof.
  intros Hc E14 E25 E36 HA HA' EA HB HB' EB HM HM' EM HF HI Hc0'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof (lequiv_wf_l _ _ _ E14) as W1. pose proof (lequiv_wf_l _ _ _ E25) as W2.
  pose proof (lequiv_wf_l _ _ _ E36) as W3.
  pose proof (W_ctx_conv Hi Hc E14 E25 E36 HA HA' EA HB HB' EB HM HM' EM) as Hid.
  pose proof (wf_tm_subst Hi Hc0' Hid) as Hc0'1.
  rewrite nf_id, nf_id_ty in Hc0'1 by first [exact (wf_tm_nf Hc0') | exact (wf_ty_nf (wf_tm_ty Hi Hc0'))].
  pose proof (ext_wf Hi HI (lwf_max W2 W3)) as HΓT.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ]) by (apply eqty_W; first [assumption | (apply compt_notV; eassumption)]).
  pose proof (ext_wf Hi HB W2) as HΓAB.
  assert (EF : [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l4 l5 A' B' @ lmax l2 (lmax l1 l2) ]).
  { apply eqty_pi; first [exact Hv | assumption | apply lequiv_max; assumption | idtac].
    exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓAB (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA EW)). }
  pose proof (W_step_eq Hi Hv E14 E25 E36 HA EA HA' HB EB HB' HM EM EW HF EF HΓT) as ES.
  eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc0'1 E36) | rewrite Hi; exact ES].
Qed.

Lemma S_actmne_elimW {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c c' ν ν' W} :
  leqv l1 l4 -> leqv l2 l5 -> leqv l3 l6 -> S_ty G Γ A A' -> S_ty G (Γ ,, A @ l1) B B' ->
  S_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' ->
  S_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
    c c' (wstepty l1 l2 A B M) ->
  S_ne G Γ ν ν' W ->
  S_ne G Γ (tmElimW l1 l2 l3 A B M c ν) (tmElimW l4 l5 l6 A' B' M' c' ν') M[lsingle ν].
Proof.
  intros H14 H25 H36 IHA IHB IHM IHc IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Hν) & Hk & HX).
  destruct (inv_elimW Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & HF' & HI' & Hc0' & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W4 H14) as E14. pose proof (leqv_lequiv _ _ _ W2 W5 H25) as E25.
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E14)) as EA.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA4 : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E14)]).
  pose proof (IHB i l2 Hc HB (wft_lconv _ _ _ _ _ _ (stab_ty Hi EA4 (lequiv_sym _ _ _ E14) HΓA HB') E25)) as EB.
  assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
  assert (HL : lequiv (gL G) (lmax l4 l5) (lmax l1 l2)) by (apply lequiv_max; now apply lequiv_sym).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' ≅ tyW l1 l2 A B @ lmax l4 l5 ]).
  { eapply eqty_lconv; [apply eqty_sym, eqty_W; first [assumption | (apply compt_notV; eassumption)] | exact HL]. }
  pose proof (ext_wf Hi HW WL) as HΓW.
  pose proof (IHM i l3 Hc HM (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' HL HΓW HM') E36)) as EM.
  (* the step, in the left telescope *)
  pose proof (W_ctx_conv Hi Hc E14 E25 E36 HA HA' EA HB HB' EB HM HM' EM) as Hid.
  pose proof (wf_tm_subst Hi Hc0' Hid) as Hc0'1.
  rewrite nf_id, nf_id_ty in Hc0'1 by first [exact (wf_tm_nf Hc0') | exact (wf_ty_nf (wf_tm_ty Hi Hc0'))].
  pose proof (ctx_of_wf_tm Hi Hc0) as HΓT.
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ]) by (apply eqty_W; first [assumption | (apply compt_notV; eassumption)]).
  pose proof (ext_wf Hi HB W2) as HΓAB.
  assert (EF : [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l4 l5 A' B' @ lmax l2 (lmax l1 l2) ]).
  { apply eqty_pi; first [exact Hv | assumption | apply lequiv_max; assumption | idtac].
    exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓAB (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA EW)). }
  pose proof (W_step_eq Hi Hv E14 E25 E36 HA EA HA' HB EB HB' HM EM EW HF EF HΓT) as ES.
  assert (Hc0'2 : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
                    ⊢[ i ] c' : wstepty l1 l2 A B M @ l3 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc0'1 E36) | rewrite Hi; exact ES]. }
  pose proof (IHc i l3 Hc Hc0 Hc0'2) as Ec.
  (* the scrutinees *)
  assert (Hν'1 : [ G ; Γ ⊢[ i ] ν' : tyW l1 l2 A B @ lmax l1 l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hν' | apply lequiv_sym, HL] | rewrite Hi; exact EW]. }
  destruct (IHν i (lmax l1 l2) (lmax l1 l2) _ _ Hc Hν Hν'1) as (_ & _ & Eν).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' HL HΓW HM') E36) as HM'3.
  assert (Econg : [ G ; Γ ⊢[ i ] tmElimW l1 l2 l3 A B M c ν ≅ tmElimW l4 l5 l6 A' B' M' c' ν'
                     : M[lsingle ν] @ l3 ])
    by (apply eqtm_elimW; first [assumption | (apply compt_notV; eassumption)]).
  assert (EMν : [ G ; Γ ⊢[ i ] M[lsingle ν] ≅ M'[lsingle ν'] @ l3 ]).
  { eapply eqty_trans; [exact (eqty_single Hi EM Hν) |].
    exact (wf_ty_func Hi HM'3 (lsub_eq_single Hi Hν Hν'1 Eν)). }
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact (lequiv_sym _ _ _ E36)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

(** Finitary well-founded trees (M15a). *)
Lemma Wf_inj_c {G i Γ l l1 l2 A A' N N'} : compt i ->
  [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l2 A' N' @ l ] ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ].
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_Wf_inj H) | exact (declM_Wf_inj H)]. Qed.

Lemma S_actnf_wf {G Γ l l' A A' N N'} : leqv l l' -> S_ty G Γ A A' -> S_tm G (Γ ,, A @ l) N N' tyNat ->
  S_ty G Γ (tyWf l A N) (tyWf l' A' N').
Proof.
  intros Hl IHA IHN i k Hc HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_wf HT) as ((_ & W1 & HA & HN) & Hk).
  destruct (inv_ty_wf HT') as ((_ & W2 & HA' & HN') & _).
  pose proof (leqv_lequiv _ _ _ W1 W2 Hl) as E.
  pose proof (IHA i l Hc HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E)]).
  pose proof (IHN i lzero Hc HN (stab_tm Hi EA' (lequiv_sym _ _ _ E) HΓA HN')) as EN.
  apply (lvl_eq_eqty Hk). apply eqty_wf; [(apply compt_notV; exact Hc) | assumption ..].
Qed.

(** Two [sup_f]s at a [Wf] type: their shapes at the shape type, their
    children at the children's tuple type. *)
Lemma S_actmnf_supf {G Γ l A N k k' C D C' D' a a' cs cs'} : S_tm G Γ a a' A ->
  S_tm G Γ cs cs' (tyVec l (tyWf l A N) N[lsingle a]) ->
  S_tm G Γ (tmSupf k C D a cs) (tmSupf k' C' D' a' cs') (tyWf l A N).
Proof.
  intros IHa IHcs i m Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_supf Hi Ht) as ((_ & Wk & HC & HD & Ha & Hcs) & Hk & ET).
  destruct (inv_supf Hi Ht') as ((_ & Wk' & HC' & HD' & Ha' & Hcs') & _ & ET').
  destruct (Wf_inj_c Hc ET) as (E1 & EAC & END).
  destruct (Wf_inj_c Hc ET') as (E2 & EAC' & END').
  pose proof (lequiv_wf_r _ _ _ E1) as Wl.
  pose proof (eqty_wf_l Hi EAC) as HA. pose proof (eqtm_wf_l Hi END) as HN.
  assert (Ha1 : [ G ; Γ ⊢[ i ] a : A @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ha | now apply lequiv_sym] | rewrite Hi; exact EAC]. }
  assert (Ha'1 : [ G ; Γ ⊢[ i ] a' : A @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ha' | now apply lequiv_sym] | rewrite Hi; exact EAC']. }
  pose proof (IHa i l Hc Ha1 Ha'1) as Ea.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l A N ≅ tyWf k C D @ l ])
    by (apply eqty_wf; first [(apply compt_notV; exact Hc) | assumption | now apply lequiv_sym]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyWf l A N ≅ tyWf k' C' D' @ l ])
    by (apply eqty_wf; first [(apply compt_notV; exact Hc) | assumption | now apply lequiv_sym]).
  assert (ECs : [ G ; Γ ⊢[ i ] tyVec l (tyWf l A N) N[lsingle a] ≅ tyVec k (tyWf k C D) D[lsingle a] @ l ]).
  { apply eqty_vec; first [exact Hv | now apply lequiv_sym | exact HW | exact EW | idtac].
    exact (Wf_Na_eq Hi HN END Ha1 Ha1 (eqtm_refl _ _ _ _ _ _ Ha1)). }
  assert (ECs' : [ G ; Γ ⊢[ i ] tyVec l (tyWf l A N) N[lsingle a] ≅ tyVec k' (tyWf k' C' D') D'[lsingle a'] @ l ]).
  { apply eqty_vec; first [exact Hv | now apply lequiv_sym | exact HW | exact EW' | idtac].
    exact (Wf_Na_eq Hi HN END' Ha1 Ha'1 Ea). }
  assert (Hcs1 : [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hcs | now apply lequiv_sym] | rewrite Hi; exact ECs]. }
  assert (Hcs'1 : [ G ; Γ ⊢[ i ] cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hcs' | now apply lequiv_sym] | rewrite Hi; exact ECs']. }
  pose proof (IHcs i l Hc Hcs1 Hcs'1) as Ecs.
  (* the congruence at the [sup_f]s' annotations, then back to the type *)
  assert (Econg : [ G ; Γ ⊢[ i ] tmSupf l A N a cs ≅ tmSupf k' C' D' a' cs' : tyWf l A N @ l ])
    by (apply eqtm_supf; first [(apply compt_notV; exact Hc) | exact Hc | now apply lequiv_sym | assumption]).
  assert (Ecan : [ G ; Γ ⊢[ i ] tmSupf l A N a cs ≅ tmSupf k C D a cs : tyWf l A N @ l ])
    by (apply eqtm_supf; first [(apply compt_notV; exact Hc) | exact Hc | now apply lequiv_sym | assumption | apply eqtm_refl; assumption]).
  pose proof (eqtm_trans _ _ _ _ _ _ _ _ (eqtm_sym _ _ _ _ _ _ _ Ecan) Econg) as E0.
  apply (lvl_eq_eqtm Hk). eapply eqtm_lconv; [exact E0 | exact E1].
Qed.

(** [elim_Wf]'s step telescope at the other side's pieces. *)
Lemma Wf_ctx_conv {G i Γ l1 l2 l3 l4 A A' N N' M M'} : typeof i = i -> compt i ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l3 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A' @ l3 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] -> [ G ; Γ ,, tyWf l3 A' N' @ l3 ⊢[ i ] M' @ l4 ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2 ⊢[ i ]
      lshift 0 : Γ ,, A' @ l3 ,, wfcsty l3 A' N' @ l3 ,, wfihty l3 l4 A' N' M' @ lmax lzero l4 ].
Proof.
  intros Hi Hc H13 H24 HA HA' EA HN HN' EN HM HM' EM. pose proof (compt_notV _ Hc) as Hv.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (lequiv_wf_l _ _ _ H13) as W1. pose proof (lequiv_wf_r _ _ _ H13) as W3.
  pose proof (lequiv_sym _ _ _ H13) as H31. pose proof (lequiv_sym _ _ _ H24) as H42.
  (* the shapes *)
  assert (HA3 : [ G ; Γ ⊢[ i ] A @ l3 ]) by (eapply wft_lconv; [exact HA | exact H31]).
  assert (EA3 : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ]) by (eapply eqty_lconv; [apply eqty_sym, EA | exact H31]).
  destruct (ctx_conv_ext Hi (lsub_wf_id G i Hi Γ HΓ) HA' EA3 HA3 H31) as [_ Hid1].
  pose proof (ext_wf Hi HA W1) as HΓA. pose proof (ext_wf Hi HA' W3) as HΓA'.
  (* the children *)
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (HW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' @ l3 ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' ≅ tyWf l1 A N @ l3 ])
    by (eapply eqty_lconv; [apply eqty_sym, EW | exact H31]).
  pose proof (stab_tm Hi EA H13 HΓA' HN) as HN1.
  assert (EN' : [ G ; Γ ,, A' @ l3 ⊢[ i ] N' ≅ N : tyNat @ lzero ])
    by (apply eqtm_sym, (stab_eqtm Hi EA H13 HΓA' EN)).
  assert (EC : [ G ; Γ ,, A' @ l3 ⊢[ i ] wfcsty l3 A' N' ≅ wfcsty l1 A N @ l3 ]).
  { apply eqty_vec; first [exact Hv | exact H31 | exact EN' | idtac].
    - exact (wk1_ty _ _ Hi _ _ _ _ _ HΓA' HW').
    - exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' EW'). }
  destruct (ctx_conv_ext Hi Hid1 (eqty_wf_l Hi EC) EC (eqty_wf_r Hi EC) H31) as [_ Hid2].
  (* the induction hypotheses *)
  pose proof (ext_wf Hi HW' W3) as HΓW'.
  assert (EM' : [ G ; Γ ,, tyWf l3 A' N' @ l3 ⊢[ i ] M' ≅ M @ l4 ]).
  { eapply eqty_lconv; [|exact H42]. exact (stab_eqty Hi EW H13 HΓW' (eqty_sym _ _ _ _ _ _ EM)). }
  pose proof (Wf_ih_eq Hi Hv H31 H42 HA' EA3 HA HN' EN' HN1 HM' EM') as EI.
  assert (HL : lequiv (gL G) (lmax lzero l4) (lmax lzero l2))
    by (apply lequiv_max; [apply lequiv_refl; cbn; auto | exact H42]).
  destruct (ctx_conv_ext Hi Hid2 (eqty_wf_l Hi EI) EI (eqty_wf_r Hi EI) HL) as [_ Hid3].
  exact Hid3.
Qed.

(** The right [elim_Wf]'s step at the left telescope and step type. *)
Lemma elimWf_step_left {G i Γ l1 l2 l3 l4 A A' N N' M M' c'} : compt i ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l3 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A' @ l3 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] -> [ G ; Γ ,, tyWf l3 A' N' @ l3 ⊢[ i ] M' @ l4 ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ] wfihty l1 l2 A N M @ lmax lzero l2 ] ->
  [ G ; Γ ,, A' @ l3 ,, wfcsty l3 A' N' @ l3 ,, wfihty l3 l4 A' N' M' @ lmax lzero l4
      ⊢[ i ] c' : wfstepty l3 A' N' M' @ l4 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ⊢[ i ] c' : wfstepty l1 A N M @ l2 ].
Proof.
  intros Hc E13 E24 HA HA' EA HN HN' EN HM HM' EM HI Hc0'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  pose proof (lequiv_wf_l _ _ _ E24) as W2.
  pose proof (Wf_ctx_conv Hi Hc E13 E24 HA HA' EA HN HN' EN HM HM' EM) as Hid.
  pose proof (wf_tm_subst Hi Hc0' Hid) as Hc0'1.
  rewrite nf_id, nf_id_ty in Hc0'1 by first [exact (wf_tm_nf Hc0') | exact (wf_ty_nf (wf_tm_ty Hi Hc0'))].
  assert (HΓT : [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2 ⊢[ i ] ])
    by (apply (ext_wf Hi HI); cbn; split; auto).
  pose proof (Wf_step_eq Hi Hv E13 E24 HA EA HA' HN EN HN' HM EM HΓT) as ES.
  eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc0'1 E24) | rewrite Hi; exact ES].
Qed.

Lemma S_actmne_elimWf {G Γ l1 l2 l3 l4 A A' N N' M M' c c' ν ν' W} :
  leqv l1 l3 -> leqv l2 l4 -> S_ty G Γ A A' -> S_tm G (Γ ,, A @ l1) N N' tyNat ->
  S_ty G (Γ ,, tyWf l1 A N @ l1) M M' ->
  S_tm G (Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2)
    c c' (wfstepty l1 A N M) ->
  S_ne G Γ ν ν' W ->
  S_ne G Γ (tmElimWf l1 l2 A N M c ν) (tmElimWf l3 l4 A' N' M' c' ν') M[lsingle ν].
Proof.
  intros H13 H24 IHA IHN IHM IHc IHν i k k' X X' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_elimWf Hi Hx) as ((_ & W1 & W2 & HA & HN & HM & HC & HI & Hc0 & Hν) & Hk & HX).
  destruct (inv_elimWf Hi Hx') as ((_ & W3 & W4 & HA' & HN' & HM' & HC' & HI' & Hc0' & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHA i l1 Hc HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA3 : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (IHN i lzero Hc HN (stab_tm Hi EA3 (lequiv_sym _ _ _ E13) HΓA HN')) as EN.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' ≅ tyWf l1 A N @ l3 ])
    by (eapply eqty_lconv; [apply eqty_sym, EW | exact (lequiv_sym _ _ _ E13)]).
  pose proof (ext_wf Hi HW W1) as HΓW.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' (lequiv_sym _ _ _ E13) HΓW HM') E24) as HM'3.
  pose proof (IHM i l2 Hc HM HM'3) as EM.
  (* the step, in the left telescope *)
  pose proof (Wf_ctx_conv Hi Hc E13 E24 HA HA' EA HN HN' EN HM HM' EM) as Hid.
  pose proof (wf_tm_subst Hi Hc0' Hid) as Hc0'1.
  rewrite nf_id, nf_id_ty in Hc0'1 by first [exact (wf_tm_nf Hc0') | exact (wf_ty_nf (wf_tm_ty Hi Hc0'))].
  pose proof (ctx_of_wf_tm Hi Hc0) as HΓT.
  pose proof (Wf_step_eq Hi Hv E13 E24 HA EA HA' HN EN HN' HM EM HΓT) as ES.
  assert (Hc0'2 : [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
                    ⊢[ i ] c' : wfstepty l1 A N M @ l2 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc0'1 E24) | rewrite Hi; exact ES]. }
  pose proof (IHc i l2 Hc Hc0 Hc0'2) as Ec.
  (* the scrutinees *)
  assert (Hν'1 : [ G ; Γ ⊢[ i ] ν' : tyWf l1 A N @ l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hν' | exact E13] | rewrite Hi; exact EW]. }
  destruct (IHν i l1 l1 _ _ Hc Hν Hν'1) as (_ & _ & Eν).
  assert (Econg : [ G ; Γ ⊢[ i ] tmElimWf l1 l2 A N M c ν ≅ tmElimWf l3 l4 A' N' M' c' ν'
                     : M[lsingle ν] @ l2 ])
    by (apply eqtm_elimWf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EMν : [ G ; Γ ⊢[ i ] M[lsingle ν] ≅ M'[lsingle ν'] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_single Hi EM Hν) |].
    exact (wf_ty_func Hi HM'3 (lsub_eq_single Hi Hν Hν'1 Eν)). }
  split; [exact HX | split].
  - eapply eqty_trans; [exact HX' |]. apply eqty_sym, (lvl_eq_eqty Hk').
    eapply eqty_lconv; [exact EMν | exact (lequiv_sym _ _ _ E24)].
  - eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

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
Lemma S_actmnf_code_W {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  S_tm G Γ s s' (tyU l1) -> S_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  S_tm G Γ (tmW l1 l2 s t) (tmW l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 IHs IHt i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_W Hi Hx) as ((_ & W1 & W2 & Hs & Ht) & Hk & HT).
  destruct (inv_code_W Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
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
  apply eqtm_code_W; first [assumption | (apply compt_notV; eassumption)].
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
  apply (lvl_eq_eqty Hk). apply eqty_unit; [(apply compt_notV; exact Hc) | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actmnf_code_unit {G Γ l k k'} : leqv k k' -> S_tm G Γ (tmUnit k) (tmUnit k') (tyU l).
Proof.
  intros Hl i kk Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_unit Hi Ht) as ((_ & HΓ & W) & Hk & HT). destruct (inv_code_unit Hi Ht') as ((_ & _ & W') & _).
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_unit; [(apply compt_notV; exact Hc) | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
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
  apply (lvl_eq_eqty Hk). apply eqty_seq; try assumption. (apply compt_notV; exact Hc).
Qed.

Lemma S_actnf_sempty {G Γ l l'} : leqv l l' -> S_ty G Γ (tySEmpty l) (tySEmpty l').
Proof.
  intros Hl i k Hc HT HT'.
  destruct (inv_ty_sempty HT) as ((_ & HΓ & W) & Hk). destruct (inv_ty_sempty HT') as ((_ & _ & W') & _).
  apply (lvl_eq_eqty Hk). apply eqty_sempty; [(apply compt_notV; exact Hc) | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
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
    apply eqty_sempty; [(apply compt_notV; exact Hc) | rewrite Hi; exact (ctx_of_wf_tm Hi He) | exact E13]. }
  pose proof (eqtm_sempty_irr _ _ _ _ _ _ Hc W1 He He1) as Ee.
  pose proof (eqtm_elimSEmpty _ _ _ _ _ _ _ _ _ _ _ (compt_notV _ Hc) E13 E24 HM EM Ee) as Econg.
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
  apply (lvl_eq_eqty Hk). apply eqty_id; try assumption. (apply compt_notV; exact Hc).
Qed.

(** Two [refl]s at an [Id] type: their points are its left endpoint. *)
Lemma S_actmnf_refl {G Γ l A a b k k' C C' c c'} :
  S_tm G Γ (tmRefl k C c) (tmRefl k' C' c') (tyId l A a b).
Proof.
  intros i m Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_idrefl Hi Ht) as ((_ & Wk & HC & Hcc) & Hk & ET).
  destruct (inv_idrefl Hi Ht') as ((_ & _ & _ & _) & _ & ET').
  destruct (id_inj_c Hc (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ ET) ET')) as (Ekk & ECC & Ecc & _).
  pose proof (eqtm_idrefl _ _ _ _ _ _ _ _ _ (compt_notV _ Hc) (lequiv_sym _ _ _ Ekk) HC ECC Ecc) as Econg.
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
  apply eqtm_code_id; try assumption. (apply compt_notV; exact Hc).
Qed.

(** Strict equality's codes (M10c), as [Id]'s and [Unit]'s. *)
Lemma code_seq_prem {G i Γ k s t u T m} : compt i -> [ G ; Γ ⊢[ i ] tmSEq k s t u : T @ m ] ->
  lwf (gL G) k /\ [ G ; Γ ⊢[ i ] s : tyU k @ lsuc k ] /\
  [ G ; Γ ⊢[ i ] t : tyEl k s @ k ] /\ [ G ; Γ ⊢[ i ] u : tyEl k s @ k ].
Proof.
  intros Hc H. destruct (proj1 (inv_code_seq (compt_typeof_self _ Hc) H)) as (_ & W & Hs & Ht & Hu). auto.
Qed.

Lemma S_actmnf_code_seq {G Γ l k k' s s' t t' u u'} : leqv k k' ->
  S_tm G Γ s s' (tyU k) -> S_tm G Γ t t' (tyEl k s) -> S_tm G Γ u u' (tyEl k s) ->
  S_tm G Γ (tmSEq k s t u) (tmSEq k' s' t' u') (tyU l).
Proof.
  intros Hk0 IHs IHt IHu i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_seq Hi Hx) as (_ & Hk & HT).
  destruct (code_seq_prem Hc Hx) as (W & Hs & Ht & Hu). destruct (code_seq_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  pose proof (IHs i (lsuc k) Hc Hs Hs1) as Es.
  destruct (code_El_conv Hc E Es) as (F & _).
  pose proof (IHt i k Hc Ht (F _ Ht')) as Et. pose proof (IHu i k Hc Hu (F _ Hu')) as Eu.
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_seq; try assumption. (apply compt_notV; exact Hc).
Qed.

(** The codes of [Empty] and [+] (M12c). *)
Lemma code_sum_prem {G i Γ l l1 l2 s t k} : compt i -> [ G ; Γ ⊢[ i ] tmSum l1 l2 s t : tyU l @ k ] ->
  lwf (gL G) l1 /\ lwf (gL G) l2 /\ [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] /\ [ G ; Γ ⊢[ i ] t : tyU l2 @ lsuc l2 ].
Proof.
  intros Hc H. destruct (proj1 (inv_code_sum (compt_typeof_self _ Hc) H)) as (_ & W1 & W2 & Hs & Ht). auto.
Qed.

Lemma S_actmnf_code_empty {G Γ l k k'} : leqv k k' -> S_tm G Γ (tmEmpty k) (tmEmpty k') (tyU l).
Proof.
  intros Hl i kk Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_empty Hi Ht) as ((_ & HΓ & W) & Hk & HT). destruct (inv_code_empty Hi Ht') as ((_ & _ & W') & _).
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_empty; [(apply compt_notV; exact Hc) | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

Lemma S_actmnf_code_sum {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  S_tm G Γ s s' (tyU l1) -> S_tm G Γ t t' (tyU l2) -> S_tm G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 IHs IHt i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_sum Hi Hx) as ((_ & W1 & W2 & Hs & Ht) & Hk & HT).
  destruct (inv_code_sum Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (IHs i (lsuc l1) Hc Hs (code_U_conv Hc E13 Hs')) as Es.
  pose proof (IHt i (lsuc l2) Hc Ht (code_U_conv Hc E24 Ht')) as Et.
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_sum; [(apply compt_notV; exact Hc) | ..]; assumption.
Qed.

(** The codes of [Vec] and [Fin] (M14b). *)
Lemma code_vec_prem {G i Γ l k s n m} : compt i -> [ G ; Γ ⊢[ i ] tmVec k s n : tyU l @ m ] ->
  lwf (gL G) k /\ [ G ; Γ ⊢[ i ] s : tyU k @ lsuc k ] /\ [ G ; Γ ⊢[ i ] n : tyNat @ lzero ].
Proof.
  intros Hc H. destruct (proj1 (inv_code_vec (compt_typeof_self _ Hc) H)) as (_ & W & Hs & Hn). auto.
Qed.
Lemma code_fin_prem {G i Γ l n m} : compt i -> [ G ; Γ ⊢[ i ] tmFin n : tyU l @ m ] ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ].
Proof. intros Hc H. exact (proj2 (proj1 (inv_code_fin (compt_typeof_self _ Hc) H))). Qed.

Lemma S_actmnf_code_vec {G Γ l k k' s s' n n'} : leqv k k' ->
  S_tm G Γ s s' (tyU k) -> S_tm G Γ n n' tyNat -> S_tm G Γ (tmVec k s n) (tmVec k' s' n') (tyU l).
Proof.
  intros Hk0 IHs IHn i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_vec Hi Hx) as (_ & Hk & HT).
  destruct (code_vec_prem Hc Hx) as (W & Hs & Hn). destruct (code_vec_prem Hc Hx') as (W' & Hs' & Hn').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (IHs i (lsuc k) Hc Hs (code_U_conv Hc E Hs')) as Es.
  pose proof (IHn i lzero Hc Hn Hn') as En.
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_vec; auto using compt_notV.
Qed.

Lemma S_actmnf_code_fin {G Γ l n n'} : S_tm G Γ n n' tyNat -> S_tm G Γ (tmFin n) (tmFin n') (tyU l).
Proof.
  intros IHn i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_fin Hi Hx) as (_ & Hk & HT).
  pose proof (IHn i lzero Hc (code_fin_prem Hc Hx) (code_fin_prem Hc Hx')) as En.
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_fin; auto using compt_notV.
Qed.

(** The code of [Wf] (M15b): the arity in the left shape's context. *)
Lemma code_wf_prem {G i Γ l k s n m} : compt i -> [ G ; Γ ⊢[ i ] tmWf k s n : tyU l @ m ] ->
  lwf (gL G) k /\ [ G ; Γ ⊢[ i ] s : tyU k @ lsuc k ] /\ [ G ; Γ ,, tyEl k s @ k ⊢[ i ] n : tyNat @ lzero ].
Proof.
  intros Hc H. destruct (proj1 (inv_code_wf (compt_typeof_self _ Hc) H)) as (_ & W & Hs & Hn). auto.
Qed.

Lemma S_actmnf_code_wf {G Γ l k k' s s' n n'} : leqv k k' ->
  S_tm G Γ s s' (tyU k) -> S_tm G (Γ ,, tyEl k s @ k) n n' tyNat ->
  S_tm G Γ (tmWf k s n) (tmWf k' s' n') (tyU l).
Proof.
  intros Hk0 IHs IHn i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_wf Hi Hx) as (_ & Hk & HT).
  destruct (code_wf_prem Hc Hx) as (W & Hs & Hn). destruct (code_wf_prem Hc Hx') as (W' & Hs' & Hn').
  pose proof (compt_notV _ Hc) as Hv.
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (IHs i (lsuc k) Hc Hs (code_U_conv Hc E Hs')) as Es.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  assert (EU : [ G ; Γ ⊢[ i ] tyU k ≅ tyU k' @ lsuc k ]) by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ | exact E]).
  assert (Es' : [ G ; Γ ⊢[ i ] s' ≅ s : tyU k' @ lsuc k' ]).
  { eapply eqtm_lconv; [| exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E))].
    eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ Es) | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EU)]. }
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl k' s' ≅ tyEl k s @ k' ])
    by (apply eqty_El; [exact Hv | exact (lequiv_sym _ _ _ E) | exact Es']).
  assert (HΓ1 : [ G ; Γ ,, tyEl k s @ k ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | apply wft_El; assumption | exact W]).
  pose proof (IHn i lzero Hc Hn (stab_tm Hi EEl (lequiv_sym _ _ _ E) HΓ1 Hn')) as En.
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_wf; first [(apply compt_notV; exact Hc) | assumption].
Qed.

Lemma S_actmnf_code_sempty {G Γ l k k'} : leqv k k' -> S_tm G Γ (tmSEmpty k) (tmSEmpty k') (tyU l).
Proof.
  intros Hl i kk Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_code_sempty Hi Ht) as ((_ & HΓ & W) & Hk & HT). destruct (inv_code_sempty Hi Ht') as ((_ & _ & W') & _).
  eapply eqtm_conv; [| rewrite Hi; exact HT]. apply (lvl_eq_eqtm Hk).
  apply eqtm_code_sempty; [(apply compt_notV; exact Hc) | exact HΓ | exact (leqv_lequiv _ _ _ W W' Hl)].
Qed.

(** [J]'s motive context at the other side's carrier and point. *)
Lemma J_ctx_conv {G i Γ l1 l3 A A' a a'} : typeof i = i -> compt i -> lequiv (gL G) l1 l3 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l3 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] lshift 0
      : Γ ,, A' @ l3 ,, tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3 ].
Proof.
  intros Hi Hc H13 HA HA' HAA Haa. pose proof (compt_notV _ Hc) as Hv.
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
  pose proof (eqtm_J _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E13 E24 HA EA Ea HI HM EM Ec Eu Eν) as Econg.
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
Proof. intros H; exact (proj2 (proj2 (mkrb_inj H))). Qed.

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
    | solve [eapply S_actmnf_seq_irr] | solve [eapply S_actmnf_sempty_irr] | solve [eapply S_actmnf_empty_irr]
    | solve [eapply S_actmne_elimSEmpty; eassumption]
    | solve [eapply S_actnf_id; eassumption] | solve [eapply S_actmnf_refl]
    | solve [eapply S_actmne_J; eassumption] | solve [eapply S_actmnf_code_id; eassumption]
    | solve [eapply S_actmnf_code_seq; eassumption] | solve [eapply S_actmnf_code_sempty; eassumption]
    | solve [eapply S_actnf_empty; eassumption] | solve [eapply S_actmne_elimEmpty; eassumption]
    | solve [eapply S_actnf_sq; eassumption] | solve [eapply S_actmnf_sq_irr]
    | solve [eapply S_actmne_elimSq; eassumption]
    | solve [eapply S_actnf_sum; eassumption] | solve [eapply S_actmnf_inl; eassumption]
    | solve [eapply S_actmnf_inr; eassumption] | solve [eapply S_actmne_case; eassumption]
    | solve [eapply S_actmnf_code_empty; eassumption] | solve [eapply S_actmnf_code_sum; eassumption]
    | solve [eapply S_actmnf_code_vec; eassumption] | solve [eapply S_actmnf_code_fin; eassumption]
    | solve [eapply S_actnf_W; eassumption] | solve [eapply S_actmnf_sup; eassumption]
    | solve [eapply S_actmne_elimW; eassumption]
    | solve [eapply S_actmnf_code_W; eassumption]
    | solve [eapply S_actnf_wf; eassumption] | solve [eapply S_actmnf_supf; eassumption]
    | solve [eapply S_actmne_elimWf; eassumption]
    | solve [eapply S_actmnf_code_wf; eassumption]
    | solve [eapply S_actne_vec; eassumption] | solve [eapply S_actne_fin; eassumption] ].
Qed.

(** Algorithmically convertible types (terms) of the computing layers,
    well formed (typed) at a level, are declaratively equal. *)
Theorem ac_ty_sound {G i Γ T T' k} : compt i -> ac_ty G Γ T T' ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. intros Hc H; exact (proj1 ac_sound_all _ _ _ _ H i k Hc). Qed.

Theorem ac_tm_sound {G i Γ t t' T k} : compt i -> ac_tm G Γ t t' T ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof. intros Hc H; exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_sound_all)))) _ _ _ _ _ H i k Hc). Qed.
