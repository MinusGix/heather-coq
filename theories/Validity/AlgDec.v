(** * Decidability of algorithmic conversion (08:236; M6_DESIGN.md step 6)

    Induction on a derivation whose left side is the given one (by
    completeness, reflexivity supplies it), for every typed right side.
    The right side is normalized (typed syntax has a whnf) and compared by
    head; a component under a binder is decided once the binder's
    components are, the binder moved to the left side's by soundness. A
    negative answer inverts the algorithm on the left side's head ([ainv_*]);
    neutrals infer a unique type ([ac_infer_uniq]). Decidability is in
    [Prop] (H1). *)
From DeLaM.Validity Require Export AlgDecNe AlgDecCode AlgDecId AlgDecW AlgDecIWf AlgDecIWi AlgDecM.

(** ** Decidability *)

Theorem ac_dec_all :
  (forall G Γ T T', ac_ty G Γ T T' -> Dc_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> Dc_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> Dc_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> Dc_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> Dc_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> Dc_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> Dc_ne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> Dc_nee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> Dc_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first
    [ solve [eapply Dc_act_red; eassumption] | solve [eapply Dc_actnf_nat] | solve [eapply Dc_actnf_U]
    | solve [eapply Dc_actnf_pi; eassumption] | solve [eapply Dc_actnf_ne; eassumption]
    | solve [eapply Dc_actnf_CTyp; eassumption] | solve [eapply Dc_actnf_CTrm; eassumption]
    | solve [eapply Dc_actnf_upi; eassumption] | solve [eapply Dc_actnf_cpi; eassumption]
    | solve [eapply Dc_actnf_tpi; eassumption]
    | solve [eapply Dc_actne_gvar; eassumption] | solve [eapply Dc_actne_El; eassumption]
    | solve [eapply Dc_actne_vec; eassumption] | solve [eapply Dc_actne_fin; eassumption]
    | solve [eapply Dc_actne_dvec; eassumption]
    | solve [eapply Dc_acc_nil] | solve [eapply Dc_acc_var] | solve [eapply Dc_acc_ext; eassumption]
    | solve [eapply Dc_actm_red; eassumption]
    | solve [eapply Dc_actmnf_code_nat] | solve [eapply Dc_actmnf_code_U]
    | solve [eapply Dc_actmnf_code_pi; eassumption] | solve [eapply Dc_actmnf_zero]
    | solve [eapply Dc_actmnf_succ; eassumption] | solve [eapply Dc_actmnf_ne; eassumption]
    | solve [eapply Dc_actmnf_eta; eassumption] | solve [eapply Dc_actmnf_ueta; eassumption]
    | solve [eapply Dc_actmnf_ceta; eassumption] | solve [eapply Dc_actmnf_teta; eassumption]
    | solve [eapply Dc_actmnf_boxT] | solve [eapply Dc_actmnf_boxt]
    | solve [eapply Dc_actmne_var; eassumption] | solve [eapply Dc_actmne_gvar; eassumption]
    | solve [eapply Dc_actmne_natrec; eassumption] | solve [eapply Dc_actmne_app; eassumption]
    | solve [eapply Dc_actmne_letboxT; eassumption] | solve [eapply Dc_actmne_letboxt; eassumption]
    | solve [eapply Dc_actmne_elimT; eassumption] | solve [eapply Dc_actmne_elimT_gvar; eassumption]
    | solve [eapply Dc_actmne_elimt; eassumption] | solve [eapply Dc_actmne_elimt_glob; eassumption]
    | solve [eapply Dc_actmne_uapp; eassumption] | solve [eapply Dc_actmne_capp; eassumption]
    | solve [eapply Dc_actmne_tapp; eassumption] | solve [eapply Dc_actmnee_red; eassumption]
    | solve [eapply Dc_acs_pt; eassumption]
    | solve [eapply Dc_actnf_sig; eassumption] | solve [eapply Dc_actmnf_code_sig; eassumption]
    | solve [eapply Dc_actmnf_sig_eta; eassumption] | solve [eapply Dc_actmne_fst; eassumption]
    | solve [eapply Dc_actmne_snd; eassumption]
    | solve [eapply Dc_actnf_unit] | solve [eapply Dc_actmnf_code_unit] | solve [eapply Dc_actmnf_unit_eta]
    | solve [eapply Dc_actnf_seq; eassumption] | solve [eapply Dc_actnf_sempty]
    | solve [eapply Dc_actmnf_seq_irr] | solve [eapply Dc_actmnf_sempty_irr] | solve [eapply Dc_actmnf_empty_irr]
    | solve [eapply Dc_actmne_elimSEmpty; eassumption]
    | solve [eapply Dc_actnf_id; eassumption] | solve [eapply Dc_actmnf_refl]
    | solve [eapply Dc_actmne_J; eassumption] | solve [eapply Dc_actmnf_code_id; eassumption]
    | solve [eapply Dc_actmnf_code_seq; eassumption] | solve [eapply Dc_actmnf_code_sempty; eassumption]
    | solve [eapply Dc_actnf_empty; eassumption] | solve [eapply Dc_actmne_elimEmpty; eassumption]
    | solve [eapply Dc_actnf_sq; eassumption] | solve [eapply Dc_actmnf_sq_irr]
    | solve [eapply Dc_actmne_elimSq; eassumption]
    | solve [eapply Dc_actnf_sum; eassumption] | solve [eapply Dc_actmnf_inl; eassumption]
    | solve [eapply Dc_actmnf_inr; eassumption] | solve [eapply Dc_actmne_case; eassumption]
    | solve [eapply Dc_actnf_W; eassumption] | solve [eapply Dc_actmnf_sup; eassumption]
    | solve [eapply Dc_actmne_elimW; eassumption]
    | solve [eapply Dc_actnf_wf; eassumption] | solve [eapply Dc_actmnf_supf; eassumption]
    | solve [eapply Dc_actmne_elimWf; eassumption]
    | solve [eapply Dc_actnf_iwf; eassumption] | solve [eapply Dc_actmnf_supi; eassumption]
    | solve [eapply Dc_actmne_elimIWf; eassumption]
    | solve [eapply Dc_actnf_iwi; eassumption] | solve [eapply Dc_actmnf_supii; eassumption]
    | solve [eapply Dc_actmne_elimIWi; eassumption]
    | solve [eapply Dc_actnf_M; eassumption] | solve [eapply Dc_actmnf_corec; eassumption]
    | solve [eapply Dc_actmne_out; eassumption]
    | solve [eapply Dc_actmnf_code_empty; eassumption] | solve [eapply Dc_actmnf_code_sum; eassumption]
    | solve [eapply Dc_actmnf_code_vec; eassumption] | solve [eapply Dc_actmnf_code_fin; eassumption]
    | solve [eapply Dc_actmnf_code_sq; eassumption]
    | solve [eapply Dc_actmnf_code_W; eassumption]
    | solve [eapply Dc_actmnf_code_wf; eassumption]
    | solve [eapply Dc_actmnf_code_dvec; eassumption] | solve [eapply Dc_actmnf_code_iwf; eassumption]
    | solve [eapply Dc_actmnf_code_iwi; eassumption] ].
Qed.

(** Algorithmic conversion of well-formed types (typed terms) of the
    computing layers is decidable: completeness supplies the reflexive
    derivation to induct on. *)
Theorem ac_ty_dec {G i Γ T T' k k'} : compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> Dec (ac_ty G Γ T T').
Proof.
  intros Hc HT HT'. exact (proj1 ac_dec_all _ _ _ _ (ac_complete_ty Hc (eqty_refl _ _ _ _ _ HT)) T' i k k' Hc HT HT').
Qed.

Theorem ac_tm_dec {G i Γ t t' T k} : compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec (ac_tm G Γ t t' T).
Proof.
  intros Hc Ht Ht'.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_dec_all)))) _ _ _ _ _
           (ac_complete_tm Hc (eqtm_refl _ _ _ _ _ _ Ht)) t' i k Hc Ht Ht').
Qed.

(** Declarative equality of well-formed types (typed terms) of the
    computing layers is decidable. *)
Theorem decl_eqty_dec {G i Γ T T' k} : compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k ] -> Dec ([ G ; Γ ⊢[ i ] T ≅ T' @ k ]).
Proof.
  intros Hc HT HT'. apply (dec_iff (P := ac_ty G Γ T T')); [| exact (ac_ty_dec Hc HT HT')].
  split; [intros D; exact (ac_ty_sound Hc D HT HT') | exact (ac_complete_ty Hc)].
Qed.

Theorem decl_eqtm_dec {G i Γ t t' T k} : compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec ([ G ; Γ ⊢[ i ] t ≅ t' : T @ k ]).
Proof.
  intros Hc Ht Ht'. apply (dec_iff (P := ac_tm G Γ t t' T)); [| exact (ac_tm_dec Hc Ht Ht')].
  split; [intros D; exact (ac_tm_sound Hc D Ht Ht') | exact (ac_complete_tm Hc)].
Qed.

(** At every layer: below D, equality is [≡ₗ] ([StaticCodeEq]); at D and M,
    by the algorithm. *)
Theorem decl_eqty_dec_any {G i Γ T T' k} :
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k ] -> Dec ([ G ; Γ ⊢[ i ] T ≅ T' @ k ]).
Proof.
  destruct i.
  - apply decl_eqty_dec_static. unfold lle; cbn; lia.
  - apply decl_eqty_dec_static. apply lle_refl.
  - apply decl_eqty_dec, compt_D.
  - apply decl_eqty_dec, compt_M.
Qed.

Theorem decl_eqtm_dec_any {G i Γ t t' T k} :
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec ([ G ; Γ ⊢[ i ] t ≅ t' : T @ k ]).
Proof.
  destruct i.
  - apply decl_eqtm_dec_static. unfold lle; cbn; lia.
  - apply decl_eqtm_dec_static. apply lle_refl.
  - apply decl_eqtm_dec, compt_D.
  - apply decl_eqtm_dec, compt_M.
Qed.
