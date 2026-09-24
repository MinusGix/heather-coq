(** * Lifting: a judgment at layer [i] holds at every layer above (05:996)

    Rules available at [i] are available above it ([i <> V], [compt] and
    "M only" are upward closed), and [typeof] is monotone.  Premises at a
    fixed layer (the [box] contents at C, contexts of contextual types at
    P) are unchanged. *)
From DeLaM.Typing Require Export GWeakening.

Lemma lle_refl i : lle i i.
Proof. unfold lle; lia. Qed.
Lemma lle_trans i j k : lle i j -> lle j k -> lle i k.
Proof. unfold lle; lia. Qed.
Lemma lle_typeof i j : lle i j -> lle (typeof i) (typeof j).
Proof. unfold lle; destruct i, j; cbn; lia. Qed.
Lemma lle_notV i j : lle i j -> i <> lV -> j <> lV.
Proof. unfold lle; destruct i, j; cbn; try lia; congruence. Qed.
Lemma lle_compt i j : lle i j -> compt i -> compt j.
Proof. unfold lle, compt; destruct i, j; cbn; intuition (try lia; discriminate). Qed.
Lemma lle_M i : lle lM i -> i = lM.
Proof. unfold lle; destruct i; cbn; auto; lia. Qed.
Lemma lle_self_typeof i : lle i (typeof i).
Proof. unfold lle; destruct i; cbn; lia. Qed.

#[export] Hint Resolve lle_refl lle_typeof lle_notV lle_compt lle_self_typeof : lift.
#[export] Hint Extern 2 (lle _ _) => eapply lle_trans; eassumption : lift.
#[export] Hint Extern 1 (lwf _ _) => assumption : lift.
#[export] Hint Resolve lequiv_wf_l lequiv_wf_r : lift.

Ltac lift_premises := eauto 6 with lift.

Ltac lift_step :=
  match goal with
  | |- wf_ctx _ _ _ =>
      first [ solve [eapply wfc_nil; lift_premises] | solve [eapply wfc_var; lift_premises]
            | solve [eapply wfc_ext; lift_premises] ]
  | |- eq_ctx _ _ _ _ =>
      first [ solve [eapply eqc_nil; lift_premises] | solve [eapply eqc_var; lift_premises]
            | solve [eapply eqc_ext; lift_premises] ]
  | |- wf_ty _ _ _ _ _ =>
      first [ solve [eapply wft_nat; lift_premises] | solve [eapply wft_pi; lift_premises]
            | solve [eapply wft_U; lift_premises] | solve [eapply wft_El; lift_premises]
            | solve [eapply wft_lconv; lift_premises] | solve [eapply wft_gvar; lift_premises]
            | solve [eapply wft_CTyp; lift_premises] | solve [eapply wft_CTrm; lift_premises] ]
  | |- wf_tm _ _ _ _ _ _ =>
      first [ solve [eapply wf_var; lift_premises] | solve [eapply wf_code_nat; lift_premises]
            | solve [eapply wf_code_U; lift_premises] | solve [eapply wf_code_pi; lift_premises]
            | solve [eapply wf_zero; lift_premises] | solve [eapply wf_succ; lift_premises]
            | solve [eapply wf_natrec; lift_premises] | solve [eapply wf_lam; lift_premises]
            | solve [eapply wf_app; lift_premises] | solve [eapply wf_conv; lift_premises]
            | solve [eapply wf_lconv; lift_premises] | solve [eapply wf_gvar; lift_premises]
            | solve [eapply wf_boxT; lift_premises] | solve [eapply wf_boxt; lift_premises]
            | solve [eapply wf_letboxT; lift_premises] | solve [eapply wf_letboxt; lift_premises] ]
  | |- eq_ty _ _ _ _ _ _ =>
      first [ solve [eapply eqty_refl; lift_premises] | solve [eapply eqty_sym; lift_premises]
            | solve [eapply eqty_trans; lift_premises] | solve [eapply eqty_pi; lift_premises]
            | solve [eapply eqty_U; lift_premises] | solve [eapply eqty_El; lift_premises]
            | solve [eapply eqty_El_nat; lift_premises] | solve [eapply eqty_El_U; lift_premises]
            | solve [eapply eqty_El_pi; lift_premises] | solve [eapply eqty_lconv; lift_premises]
            | solve [eapply eqty_gvar; lift_premises]
            | solve [eapply eqty_CTyp; lift_premises] | solve [eapply eqty_CTrm; lift_premises] ]
  | |- eq_tm _ _ _ _ _ _ _ =>
      first [ solve [eapply eqtm_refl; lift_premises] | solve [eapply eqtm_sym; lift_premises]
            | solve [eapply eqtm_trans; lift_premises] | solve [eapply eqtm_code_U; lift_premises]
            | solve [eapply eqtm_code_pi; lift_premises] | solve [eapply eqtm_succ; lift_premises]
            | solve [eapply eqtm_natrec; lift_premises] | solve [eapply eqtm_lam; lift_premises]
            | solve [eapply eqtm_app; lift_premises] | solve [eapply eqtm_conv; lift_premises]
            | solve [eapply eqtm_lconv; lift_premises] | solve [eapply eqtm_gvar; lift_premises]
            | solve [eapply eqtm_natrec_zero; lift_premises]
            | solve [eapply eqtm_natrec_succ; lift_premises]
            | solve [eapply eqtm_beta; lift_premises] | solve [eapply eqtm_eta; lift_premises]
            | solve [eapply eqtm_boxT; lift_premises] | solve [eapply eqtm_boxt; lift_premises]
            | solve [eapply eqtm_letboxT; lift_premises] | solve [eapply eqtm_letboxt; lift_premises]
            | solve [eapply eqtm_letboxT_beta; lift_premises]
            | solve [eapply eqtm_letboxt_beta; lift_premises] ]
  end.

Theorem lifting :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> forall j, lle i j -> [ G ; Γ ⊢[ j ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> forall j, lle i j -> [ G ; Γ ⊢[ j ] T @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> forall j, lle i j -> [ G ; Γ ⊢[ j ] t : T @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> forall j, lle i j ->
     [ G ; Γ ⊢[ j ] T ≅ T' @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> forall j, lle i j ->
     [ G ; Γ ⊢[ j ] t ≅ t' : T @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> forall j, lle i j -> [ G ⊢[ j ] Γ ≅ Γ' ]).
Proof.
  apply typing_mut; intros; try exact I;
    try match goal with H : lle lM ?j |- _ => apply lle_M in H; subst j end.
  all: lift_step.
Qed.

Lemma lift_ty {G i j Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> lle i j -> [ G ; Γ ⊢[ j ] T @ l ].
Proof. intros H; exact (proj1 (proj2 (proj2 lifting)) _ _ _ _ _ H j). Qed.
Lemma lift_tm {G i j Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> lle i j -> [ G ; Γ ⊢[ j ] t : T @ l ].
Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 lifting))) _ _ _ _ _ _ H j). Qed.
Lemma lift_ctx {G i j Γ} : [ G ; Γ ⊢[ i ] ] -> lle i j -> [ G ; Γ ⊢[ j ] ].
Proof. intros H; exact (proj1 (proj2 lifting) _ _ _ H j). Qed.
Lemma lift_eqty {G i j Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> lle i j -> [ G ; Γ ⊢[ j ] T ≅ T' @ l ].
Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 (proj2 lifting)))) _ _ _ _ _ _ H j). Qed.
Lemma lift_eqtm {G i j Γ t t' T l} :
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> lle i j -> [ G ; Γ ⊢[ j ] t ≅ t' : T @ l ].
Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 lifting))))) _ _ _ _ _ _ _ H j). Qed.
