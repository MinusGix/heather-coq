(** * Validity with global substitutions, rule by rule

    Each M1 validity lemma lifted along related global substitutions (and
    the global weakenings after them): the premises are taken at
    [σ ≈ σ'], typing premises move along [σ] by the global substitution
    lemma, [⦃σ⦄] is pushed through the syntax, and the M1 lemma applies at
    the target global context.  Computation rules relate a redex under [σ]
    to a contractum under [σ']: they go through the diagonal ([σ ≈ σ],
    where M1's lemma applies) and the contractum's validity.

    The rules build in parts beside one another: the tactics
    ([RulesSBase]), [IWf]'s eliminator ([RulesSIWf], [RulesSIWfSupi]
    and their [Ty] parts, a third of the time) and the rest ([RulesSCore]). *)
From DeLaM.Validity Require Export RulesSCore RulesSCoreW RulesSIWf RulesSIWfTy RulesSIWfSupi RulesSIWfSupiTy.

(** Each rule's semantic lemma, its side conditions closed by [side]
    (the fundamental theorems at P and M). A new rule is added here. *)
Ltac vs_rules side :=
  first
  [ solve [simple eapply VS_var; side]
  | solve [simple eapply VS_nat; side] | solve [simple eapply VS_zero; side] | solve [simple eapply VS_code_nat; side]
  | solve [simple eapply VS_El_nat; side]
  | solve [simple eapply VS_succ; side]
  | solve [simple eapply VS_U; side] | solve [simple eapply VS_El; side]
  | solve [simple eapply VS_code_U; side] | solve [simple eapply VS_El_U; side]
  | solve [simple eapply VS_pi; side] | solve [simple eapply VS_app; side]
  | solve [simple eapply VS_lam; side] | solve [simple eapply VS_natrec; side]
  | solve [simple eapply VS_code_pi; side]
  | solve [simple eapply VS_beta; side] | solve [simple eapply VS_eta; side]
  | solve [simple eapply VS_natrec_zero; side] | solve [simple eapply VS_natrec_succ; side]
  | solve [simple eapply VS_El_pi; side]
  (* dependent pairs (M8) *)
  | solve [simple eapply VS_sig; side] | solve [simple eapply VS_code_sig; side]
  | solve [simple eapply VS_pair; side] | solve [simple eapply VS_fst; side]
  | solve [simple eapply VS_snd; side]
  | solve [simple eapply VS_fst_beta; side] | solve [simple eapply VS_snd_beta; side]
  | solve [simple eapply VS_sig_eta; side] | solve [simple eapply VS_El_sig; side]
  (* the unit type (M8c) *)
  | solve [simple eapply VS_unit; side] | solve [simple eapply VS_code_unit; side]
  | solve [simple eapply VS_triv; side] | solve [simple eapply VS_El_unit; side]
  | solve [simple eapply VS_unit_eta; side]
  (* strict equality (M10a) *)
  | solve [simple eapply VS_seq; side] | solve [simple eapply VS_sempty; side]
  | solve [simple eapply VS_srefl; side] | solve [simple eapply VS_elimSEmpty; side]
  | solve [simple eapply VS_seq_irr; side] | solve [simple eapply VS_sempty_irr; side]
  | solve [simple eapply VS_empty_irr; side]
  (* the identity type (M11a) *)
  | solve [simple eapply VS_id; side] | solve [simple eapply VS_idrefl; side]
  | solve [simple eapply VS_J; side] | solve [simple eapply VS_J_beta; side]
  | solve [simple eapply VS_code_id; side] | solve [simple eapply VS_El_id; side]
  (* strict equality's codes (M10c) *)
  | solve [simple eapply VS_code_seq; side] | solve [simple eapply VS_El_seq; side]
  | solve [simple eapply VS_code_sempty; side] | solve [simple eapply VS_El_sempty; side]
  (* the empty type (M12a) *)
  | solve [simple eapply VS_empty; side] | solve [simple eapply VS_elimEmpty; side]
  (* binary sums (M12b) *)
  | solve [simple eapply VS_sum; side] | solve [simple eapply VS_inl; side]
  | solve [simple eapply VS_inr; side] | solve [simple eapply VS_case; side]
  | solve [simple eapply VS_case_inl; side] | solve [simple eapply VS_case_inr; side]
  (* the codes of Empty and + (M12c) *)
  | solve [simple eapply VS_code_empty; side] | solve [simple eapply VS_El_empty; side]
  | solve [simple eapply VS_code_sum; side] | solve [simple eapply VS_El_sum; side]
  (* well-founded trees (M13a) *)
  | solve [simple eapply VS_W; side] | solve [simple eapply VS_sup; side]
  | solve [simple eapply VS_elimW; side] | solve [simple eapply VS_elimW_sup; side]
  (* the code of W (M13b) *)
  | solve [simple eapply VS_code_W; side] | solve [simple eapply VS_El_W; side]
  (* Vec and Fin (M14a) *)
  | solve [simple eapply VS_vec; side] | solve [simple eapply VS_fin; side]
  | solve [simple eapply VS_vec_zero; side] | solve [simple eapply VS_vec_succ; side]
  | solve [simple eapply VS_fin_zero; side] | solve [simple eapply VS_fin_succ; side]
  (* their codes (M14b) *)
  | solve [simple eapply VS_code_vec; side] | solve [simple eapply VS_El_vec; side]
  | solve [simple eapply VS_code_fin; side] | solve [simple eapply VS_El_fin; side]
  (* finitary well-founded trees (M15a) *)
  | solve [simple eapply VS_wf; side] | solve [simple eapply VS_supf; side]
  | solve [simple eapply VS_elimWf; side] | solve [simple eapply VS_elimWf_supf; side]
  (* the code of Wf (M15b) *)
  | solve [simple eapply VS_code_wf; side] | solve [simple eapply VS_El_wf; side]
  (* propositional truncation (M16a) *)
  | solve [simple eapply VS_sq; side] | solve [simple eapply VS_sq_intro; side]
  | solve [simple eapply VS_sq_irr; side] | solve [simple eapply VS_elimSq; side]
  | solve [simple eapply VS_elimSq_sq; side]
  | solve [simple eapply VS_sq_single; side] | solve [simple eapply VS_sq_single_sq; side]
  (* the code of ∥·∥ (M16b) *)
  | solve [simple eapply VS_code_sq; side] | solve [simple eapply VS_El_sq; side]
  (* dependent tuples (M17a) *)
  | solve [simple eapply VS_dvec; side] | solve [simple eapply VS_dvec_zero; side]
  | solve [simple eapply VS_dvec_succ; side]
  (* indexed well-founded trees (M17b) *)
  | solve [simple eapply VS_iwf; side] | solve [simple eapply VS_supi; side]
  | solve [simple eapply VS_elimIWf; side] | solve [simple eapply VS_elimIWf_supi; side]
  | solve [simple eapply VS_supi_ty; side] | solve [simple eapply VS_elimIWf_ty; side]
  | solve [simple eapply VS_elimIWf_supi_ty; side]
  (* the codes of DVec and IWf (M17c) *)
  | solve [simple eapply VS_code_dvec; side] | solve [simple eapply VS_El_dvec; side]
  | solve [simple eapply VS_code_iwf; side] | solve [simple eapply VS_El_iwf; side]
  (* indexed coinductive types (M18b) *)
  | solve [simple eapply VS_M; side] | solve [simple eapply VS_mOutTy; side]
  | solve [simple eapply VS_out; side] | solve [simple eapply VS_corec; side]
  | solve [simple eapply VS_out_corec; side] ].
