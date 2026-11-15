(** * Validity with global substitutions: the lifting tactics

    The typings along [σ] and the tactics that lift an M1 validity case
    along related global substitutions [σ ≈ σ'] ([s_lift], [s_diag]), for
    the rules of [RulesS]: its parts ([RulesSCore], [RulesSIWf],
    [RulesSIWfSupi]) each require only this file, so they build in
    parallel. The tactics are outside the section (a section's [Ltac]s
    end with it), so they name its lemmas with [EP] and [EM] left to
    unification. *)
From DeLaM.Validity Require Export ValidS.

#[local] Existing Instance LR_P.

Section RulesS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation GValid := (GValid EP EM).

(** ** Typing along the left substitution *)

Section Along.
Context {G' G : gctx} {σ σ' : gsub} (Hσ : GSubRel G' G σ σ').

(** The source is first grown to the target's levels. *)
Lemma gsub_wf_src {H0 τ H1 G1} : gΨ G1 = gΨ H1 -> [ H0 ⊢ τ : H1 ] -> [ H0 ⊢ τ : G1 ].
Proof using . intros E [Hg Hn Hv]; constructor; [exact Hg | exact Hn |]. rewrite E; exact Hv. Qed.

Local Ltac glob_of H :=
  first [ exact (ctx_glob _ _ _ H)
        | eapply ctx_glob; exact (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H)
        | eapply ctx_glob; exact (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H)
        | eapply ctx_glob; exact (proj1 (proj2 (proj2 (proj2 (proj2 ctx_extract)))) _ _ _ _ _ _ H)
        | eapply ctx_glob; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ctx_extract))))) _ _ _ _ _ _ _ H) ].

Local Ltac along k :=
  intros H; pose proof (gsr_wf_l _ _ _ _ _ _ Hσ) as Hw; pose proof (gsr_L _ _ _ _ _ _ Hσ) as HL;
  assert (Hg : [ ⊢ mkG (gL G') (gΨ G) ]) by (destruct G; apply (wfg_grow _ _ _ HL); glob_of H);
  first [ apply (gwa_ctx (γ := gwk_id) (G' := mkG (gL G') (gΨ G)) (G := G) (conj HL (gwkwf_id _)) Hg) in H
        | apply (gwa_ty (γ := gwk_id) (G' := mkG (gL G') (gΨ G)) (G := G) (conj HL (gwkwf_id _)) Hg) in H
        | apply (gwa_tm (γ := gwk_id) (G' := mkG (gL G') (gΨ G)) (G := G) (conj HL (gwkwf_id _)) Hg) in H
        | apply (gwa_eqty (γ := gwk_id) (G' := mkG (gL G') (gΨ G)) (G := G) (conj HL (gwkwf_id _)) Hg) in H
        | apply (gwa_eqtm (γ := gwk_id) (G' := mkG (gL G') (gΨ G)) (G := G) (conj HL (gwkwf_id _)) Hg) in H ];
  cbn [gwa] in H; apply (gsub_wf_src (H1 := G) (G1 := mkG (gL G') (gΨ G)) eq_refl) in Hw; destruct G' as [L' Ψ'];
  first [ exact (k _ _ _ _ _ _ _ H _ _ Hw) | exact (k _ _ _ _ _ _ H _ _ Hw)
        | exact (k _ _ _ _ _ H _ _ Hw) | exact (k _ _ _ _ H _ _ Hw) | exact (k _ _ _ H _ _ Hw) ].

Lemma gs_ctx {i Γ} : [ G ; Γ ⊢[ i ] ] -> compt i -> [ G' ; Γ⦃σ⦄ ⊢[ i ] ].
Proof using Hσ.
  intros H Hc; pose proof (gsr_wf_l _ _ _ _ _ _ Hσ) as Hw; pose proof (gsr_L _ _ _ _ _ _ Hσ) as HL.
  assert (Hg : [ ⊢ mkG (gL G') (gΨ G) ]) by (destruct G; apply (wfg_grow _ _ _ HL); glob_of H).
  apply (gwa_ctx (γ := gwk_id) (G' := mkG (gL G') (gΨ G)) (G := G) (conj HL (gwkwf_id _)) Hg) in H; cbn [gwa] in H; apply (gsub_wf_src (H1 := G) (G1 := mkG (gL G') (gΨ G)) eq_refl) in Hw; destruct G' as [L' Ψ'].
  exact (proj1 (proj2 gsubstitution) _ _ _ H _ _ Hw Hc).
Qed.
Lemma gs_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G' ; Γ⦃σ⦄ ⊢[ i ] T⦃σ⦄ @ l ].
Proof using Hσ. along (proj1 (proj2 (proj2 gsubstitution))). Qed.
Lemma gs_tm {i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G' ; Γ⦃σ⦄ ⊢[ i ] t⦃σ⦄ : T⦃σ⦄ @ l ].
Proof using Hσ. along (proj1 (proj2 (proj2 (proj2 gsubstitution)))). Qed.
Lemma gs_eqty {i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G' ; Γ⦃σ⦄ ⊢[ i ] T⦃σ⦄ ≅ T'⦃σ⦄ @ l ].
Proof using Hσ. along (proj1 (proj2 (proj2 (proj2 (proj2 gsubstitution))))). Qed.
Lemma gs_eqtm {i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G' ; Γ⦃σ⦄ ⊢[ i ] t⦃σ⦄ ≅ t'⦃σ⦄ : T⦃σ⦄ @ l ].
Proof using Hσ. along (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 gsubstitution)))))). Qed.

End Along.

End RulesS.


(** ** Lifting an M1 case along [σ ≈ σ'] *)

(** Presupposed typings (left-hand sides and types), for the lemmas'
    premises. *)
Ltac s_types :=
  repeat match goal with
  | Hi : typeof ?i = ?i, H : wf_tm ?G ?i ?Γ ?t ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G i Γ T l |- _ => fail
      | _ => pose proof (wf_tm_ty Hi H)
      end
  | Hi : typeof ?i = ?i, H : eq_ty ?G ?i ?Γ ?T ?T' ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G i Γ T l |- _ => fail
      | _ => pose proof (eqty_wf_l Hi H)
      end
  | Hi : typeof ?i = ?i, H : eq_tm ?G ?i ?Γ ?t ?t' ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_tm G i Γ t T l |- _ => fail
      | _ => pose proof (eqtm_wf_l Hi H)
      end
  end.

Ltac s_along_at E0 LP0 :=
  match goal with Hσ : GSubRel _ _ ?G' ?G ?σ ?σ' |- _ =>
    repeat match goal with
    | H : @VTyS _ _ E0 LP0 G _ _ _ _ |- _ => pose proof (H _ _ _ Hσ); clear H
    | H : @VTmS _ _ E0 LP0 G _ _ _ _ _ |- _ => pose proof (H _ _ _ Hσ); clear H
    | H : @VTyS _ _ _ _ G _ _ _ _ |- _ => clear H
    | H : @VTmS _ _ _ _ G _ _ _ _ _ |- _ => clear H
    | H : @VCtxS _ _ _ _ G _ |- _ => clear H
    | H : GValid _ _ G |- _ => clear H
    | H : wf_ctx G _ _ |- _ =>
        pose proof (gs_ctx _ _ Hσ H ltac:(first [exact compt_D | exact compt_M | assumption])); clear H
    | H : wf_ty G _ _ _ _ |- _ => pose proof (gs_ty _ _ Hσ H); clear H
    | H : wf_tm G _ _ _ _ _ |- _ => pose proof (gs_tm _ _ Hσ H); clear H
    | H : eq_ty G _ _ _ _ _ |- _ => pose proof (gs_eqty _ _ Hσ H); clear H
    | H : eq_tm G _ _ _ _ _ _ |- _ => pose proof (gs_eqtm _ _ Hσ H); clear H
    | H : in_ctx ?Γ0 _ _ _ |- _ =>
        lazymatch Γ0 with gsubst _ _ => fail | _ => pose proof (in_ctx_gsubst _ _ _ _ σ H); clear H end
    | H : lequiv (gL G) _ _ |- _ => apply (lequiv_weaken _ _ _ _ (gsr_L _ _ _ _ _ _ Hσ)) in H
    | H : lwf (gL G) _ |- _ => apply (lwf_weaken _ _ _ (gsr_L _ _ _ _ _ _ Hσ)) in H
    end
  end.

(** Only the goal's instance matters; the other one's hypotheses go. *)
Ltac s_along :=
  lazymatch goal with
  | |- @VTyG ?E0 ?LP0 _ _ _ _ _ => s_along_at E0 LP0
  | |- @VTmG ?E0 ?LP0 _ _ _ _ _ _ => s_along_at E0 LP0
  end.

(** [s_push]: generated by [tools/gen_push.py] from its lemma list. *)
Ltac s_push_at h k := lazymatch h with
  | @subst => first [k gs_single_ty | k gs_single | k gs_single2_ty | k gs_single2 | k gs_lsucc_ty | k gs_single3
                    | k gs_llift_single_ty | k gs_llift2_single]
  | @ren => first [k gsubst_ren_ty' | k gs_ren]
  | @tyNat => k gs_tyNat
  | @tyPi => k gs_tyPi
  | @tyU => k gs_tyU
  | @tyEl => k gs_tyEl
  | @var => k gs_var
  | @tmNat => k gs_tmNat
  | @tmPi => k gs_tmPi
  | @tmU => k gs_tmU
  | @zero => k gs_zero
  | @succ => k gs_succ
  | @natrec => k gs_natrec
  | @lam => k gs_lam
  | @app => k gs_app
  | @cnil => k gs_cnil
  | @cext => k gs_cext
  | @tySig => k gs_tySig
  | @tySum => k gs_tySum
  | @tyW => k gs_tyW
  | @tyVec => k gs_tyVec
  | @tyFin => k gs_tyFin
  | @tmSup => k gs_sup
  | @tmElimW => k gs_elimW
  | @wIH => k gs_wIH
  | @tyWf => k gs_tyWf
  | @tmSupf => k gs_supf
  | @tmElimWf => k gs_elimWf
  | @tmNth => k gs_tmNth
  | @wfIH => k gs_wfIH
  | @tmInl => k gs_inl
  | @tmInr => k gs_inr
  | @tmCase => k gs_case
  | @tmSig => k gs_tmSig
  | @tmPair => k gs_pair
  | @tmFst => k gs_fst
  | @tmSnd => k gs_snd
  | @tyUnit => k gs_tyUnit
  | @tmUnit => k gs_tmUnit
  | @tmSEmpty => k gs_tmSEmpty
  | @tmEmpty => k gs_tmEmpty
  | @tmSum => k gs_tmSum
  | @tmW => k gs_tmW
  | @tmVec => k gs_tmVec
  | @tmFin => k gs_tmFin
  | @tmWf => k gs_tmWf
  | @tmTriv => k gs_triv
  | @tySEq => k gs_tySEq
  | @tySEmpty => k gs_tySEmpty
  | @tyEmpty => k gs_tyEmpty
  | @srefl => k gs_srefl
  | @elimSEmpty => k gs_elimSEmpty
  | @elimEmpty => k gs_elimEmpty
  | @tyId => k gs_tyId
  | @tmRefl => k gs_refl
  | @tmId => k gs_tmId
  | @tmSEq => k gs_tmSEq
  | @tmJ => k gs_J
  | @tySq => k gs_tySq
  | @tyDVec => k gs_tyDVec
  | @tmSq => k gs_sq
  | @tmElimSq => k gs_elimSq
  | @tmSqCode => k gs_tmSqCode
  | @tmDVec => k gs_tmDVec
  | @tmIWf => k gs_tmIWf
  | @tmIWi => k gs_tmIWi
  | @tyIWf => k gs_tyIWf
  | @tmSupi => k gs_supi
  | @tmElimIWf => k gs_elimIWf
  | @tmDNth => k gs_tmDNth
  | @iwfFam => k gs_iwfFam
  | @iwfIH => k gs_iwfIH
  | @tyM => k gs_tyM
  | @tmCorec => k gs_corec
  | @tmOut => k gs_out
  | @mOutCorec => k gs_mOutCorec
  | @tyIWi => k gs_tyIWi
  | @tmSupii => k gs_supii
  | @tmElimIWi => k gs_elimIWi
  | @iwiFam => k gs_iwiFam
  | @iwiFamCod => k gs_iwiFamCod
  | @iwiIH => k gs_iwiIH
  end.
Ltac s_push := repeat match goal with
  | |- context [@gsubst _ _ ?t _] => let h := head_of t in s_push_at h ltac:(fun L => rewrite !L)
  | H : context [@gsubst _ _ ?t _] |- _ => let h := head_of t in s_push_at h ltac:(fun L => rewrite !L in H)
  end.

(** Side conditions of the general lemmas: levels. *)
Ltac s_lwf := first [eassumption | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption].
Ltac s_side :=
  first [ eassumption | apply lequiv_refl; s_lwf | apply lequiv_sym; eassumption | s_lwf
        | eapply VTyG_refl_l; eassumption | eapply VTy_refl_l; eassumption
        (* [IWf]'s signature (M17b) *)
        | lazymatch goal with |- context [IWfSig] => unfold IWfSig; repeat split; first [s_lwf | eassumption] end
        (* [IWi]'s (M19b) *)
        | lazymatch goal with |- context [IWiSig] => unfold IWiSig; repeat split; first [s_lwf | eassumption] end ].

(** The two sides differ ([σ] and [σ']), so the rule-shaped wrappers do
    not apply: the general lemmas do. *)
Ltac fts_case :=
  first
  [ ft_case
  | solve [simple eapply V_pi; s_side] | solve [simple eapply V_El; s_side] | solve [simple eapply V_U; s_side]
  | solve [simple eapply V_code_U; s_side] | solve [simple eapply V_code_pi; s_side]
  | solve [simple eapply V_natrec; s_side] | solve [simple eapply V_lam; s_side] | solve [simple eapply V_app; s_side]
  | solve [simple eapply V_sig; s_side] | solve [simple eapply V_code_sig; s_side]
  | solve [simple eapply V_pair; s_side] | solve [simple eapply V_fst; s_side] | solve [simple eapply V_snd; s_side]
  | solve [simple eapply V_unit; s_side] | solve [simple eapply V_code_unit; s_side]
  | solve [simple eapply V_triv; s_side]
  (* strict equality (M10a) *)
  | solve [simple eapply V_seq; s_side] | solve [simple eapply V_sempty; s_side]
  | solve [simple eapply V_srefl; s_side] | solve [simple eapply V_elimSEmpty; s_side]
  | solve [simple eapply V_seq_irr; s_side] | solve [simple eapply V_sempty_irr; s_side]
  | solve [simple eapply V_empty_irr; s_side]
  (* the identity type (M11a) *)
  | solve [simple eapply V_id; s_side] | solve [simple eapply V_idrefl; s_side]
  | solve [simple eapply V_J; s_side]
  | solve [simple eapply V_code_id; s_side] | solve [simple eapply V_El_id; s_side]
  (* strict equality's codes (M10c) *)
  | solve [simple eapply V_code_seq; s_side] | solve [simple eapply V_El_seq; s_side]
  | solve [simple eapply V_code_sempty; s_side] | solve [simple eapply V_El_sempty; s_side]
  (* the empty type (M12a) *)
  | solve [simple eapply V_empty; s_side] | solve [simple eapply V_elimEmpty; s_side]
  (* binary sums (M12b) *)
  | solve [simple eapply V_sum; s_side] | solve [simple eapply V_inl; s_side]
  | solve [simple eapply V_inr; s_side] | solve [simple eapply V_case; s_side]
  (* the codes of Empty and + (M12c) *)
  | solve [simple eapply V_code_empty; s_side] | solve [simple eapply V_El_empty; s_side]
  | solve [simple eapply V_code_sum; s_side] | solve [simple eapply V_El_sum; s_side]
  (* well-founded trees (M13a) *)
  | solve [simple eapply V_W; s_side] | solve [simple eapply V_sup; s_side]
  | solve [simple eapply V_elimW; s_side] | solve [simple eapply V_elimW_sup; s_side]
  (* the code of W (M13b) *)
  | solve [simple eapply V_code_W; s_side] | solve [simple eapply V_El_W; eassumption]
  (* Vec and Fin (M14a) *)
  | solve [simple eapply V_vec; s_side] | solve [simple eapply V_fin; s_side]
  | solve [simple eapply V_vec_zero; s_side] | solve [simple eapply V_vec_succ; s_side]
  | solve [simple eapply V_fin_zero; s_side] | solve [simple eapply V_fin_succ; s_side]
  (* their codes (M14b) *)
  | solve [simple eapply V_code_vec; s_side] | solve [simple eapply V_El_vec; s_side]
  | solve [simple eapply V_code_fin; s_side] | solve [simple eapply V_El_fin; s_side]
  (* finitary well-founded trees (M15a) *)
  | solve [simple eapply V_wf; s_side] | solve [simple eapply V_supf; s_side]
  | solve [simple eapply V_elimWf; s_side] | solve [simple eapply V_elimWf_supf; s_side]
  (* the code of Wf (M15b) *)
  | solve [simple eapply V_code_wf; s_side] | solve [simple eapply V_El_wf; eassumption]
  (* propositional truncation (M16a) *)
  | solve [simple eapply V_sq; s_side] | solve [simple eapply V_sq_intro; s_side]
  | solve [simple eapply V_sq_irr; s_side] | solve [simple eapply V_elimSq; s_side]
  (* the code of ∥·∥ (M16b) *)
  | solve [simple eapply V_code_sq; s_side] | solve [simple eapply V_El_sq; s_side]
  (* dependent tuples (M17a) *)
  | solve [simple eapply V_dvec; s_side] | solve [simple eapply V_dvec_zero; s_side]
  | solve [simple eapply V_dvec_succ; s_side]
  (* indexed well-founded trees (M17b) *)
  | solve [simple eapply V_iwf; s_side] | solve [simple eapply V_supi; s_side]
  | solve [simple eapply V_elimIWf; s_side] | solve [simple eapply V_elimIWf_supi; s_side]
  | solve [simple eapply V_supi_ty; s_side] | solve [simple eapply V_elimIWf_ty_at; s_side]
  | solve [simple eapply V_elimIWf_supi_ty; s_side]
  (* the codes of DVec and IWf (M17c) *)
  | solve [simple eapply V_code_dvec; s_side] | solve [simple eapply V_El_dvec; s_side]
  | solve [simple eapply V_code_iwf; s_side] | solve [simple eapply V_El_iwf; s_side]
  (* indexed coinductive types (M18b) *)
  | solve [simple eapply V_M; s_side] | solve [simple eapply V_out; s_side]
  | solve [simple eapply V_mOutTy; s_side]
  | solve [simple eapply V_corec; s_side] | solve [simple eapply V_out_corec; s_side]
  (* indexed families with infinitary children (M19b) *)
  | solve [simple eapply V_iwi_at; s_side] | solve [simple eapply V_supii; s_side]
  | solve [simple eapply V_elimIWi; s_side] | solve [simple eapply V_elimIWi_supii; s_side]
  | solve [simple eapply V_supii_ty; s_side] | solve [simple eapply V_elimIWi_ty_at; s_side]
  | solve [simple eapply V_elimIWi_supii_ty; s_side]
  (* the code of IWi (M19c) *)
  | solve [simple eapply V_code_iwi; s_side] | solve [simple eapply V_El_iwi; s_side] ].

(** Typings at a layer below the instance's are lifted to it. *)
Ltac gl_liftL :=
  repeat match goal with
  | Hl : lle ?i (@ge_layer _), H : wf_ctx _ ?i _ |- _ => pose proof (lift_ctx H Hl); clear H
  | Hl : lle ?i (@ge_layer _), H : wf_ty _ ?i _ _ _ |- _ => pose proof (lift_ty H Hl); clear H
  | Hl : lle ?i (@ge_layer _), H : wf_tm _ ?i _ _ _ _ |- _ => pose proof (lift_tm H Hl); clear H
  | Hl : lle ?i (@ge_layer _), H : eq_ty _ ?i _ _ _ _ |- _ => pose proof (lift_eqty H Hl); clear H
  | Hl : lle ?i (@ge_layer _), H : eq_tm _ ?i _ _ _ _ _ |- _ => pose proof (lift_eqtm H Hl); clear H
  end.

Ltac s_lift :=
  s_types;
  match goal with
  | |- @VTyS _ _ _ _ _ _ _ _ _ => intros ? ? ? ?
  | |- @VTmS _ _ _ _ _ _ _ _ _ _ => intros ? ? ? ?
  end;
  s_along; s_push; gl_lift; gl_liftL; fts_case.

(** At a substitution related to itself, the rule-shaped wrappers apply. *)
Tactic Notation "s_diag" uconstr(lem) :=
  s_types; intros ? ? ?; s_along; s_push; gl_lift; gl_liftL; simple eapply lem; eassumption.


(** ** The rules *)
