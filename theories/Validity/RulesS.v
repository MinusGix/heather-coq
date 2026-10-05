(** * Validity with global substitutions, rule by rule

    Each M1 validity lemma lifted along related global substitutions (and
    the global weakenings after them): the premises are taken at
    [σ ≈ σ'], typing premises move along [σ] by the global substitution
    lemma, [⦃σ⦄] is pushed through the syntax, and the M1 lemma applies at
    the target global context.  Computation rules relate a redex under [σ]
    to a contractum under [σ']: they go through the diagonal ([σ ≈ σ],
    where M1's lemma applies) and the contractum's validity. *)
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
  match goal with Hσ : GSubRel ?G' ?G ?σ ?σ' |- _ =>
    repeat match goal with
    | H : @VTyS _ _ E0 LP0 G _ _ _ _ |- _ => pose proof (H _ _ _ Hσ); clear H
    | H : @VTmS _ _ E0 LP0 G _ _ _ _ _ |- _ => pose proof (H _ _ _ Hσ); clear H
    | H : @VTyS _ _ _ _ G _ _ _ _ |- _ => clear H
    | H : @VTmS _ _ _ _ G _ _ _ _ _ |- _ => clear H
    | H : @VCtxS _ _ _ _ G _ |- _ => clear H
    | H : GValid G |- _ => clear H
    | H : wf_ctx G _ _ |- _ =>
        pose proof (gs_ctx Hσ H ltac:(first [exact compt_D | exact compt_M | assumption])); clear H
    | H : wf_ty G _ _ _ _ |- _ => pose proof (gs_ty Hσ H); clear H
    | H : wf_tm G _ _ _ _ _ |- _ => pose proof (gs_tm Hσ H); clear H
    | H : eq_ty G _ _ _ _ _ |- _ => pose proof (gs_eqty Hσ H); clear H
    | H : eq_tm G _ _ _ _ _ _ |- _ => pose proof (gs_eqtm Hσ H); clear H
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
  | @subst => first [k gs_single_ty | k gs_single | k gs_single2_ty | k gs_single2 | k gs_lsucc_ty | k gs_single3]
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
  end.
Ltac s_push := repeat match goal with
  | |- context [@gsubst _ _ ?t _] => let h := head_of t in s_push_at h ltac:(fun L => rewrite L)
  | H : context [@gsubst _ _ ?t _] |- _ => let h := head_of t in s_push_at h ltac:(fun L => rewrite L in H)
  end.

(** Side conditions of the general lemmas: levels. *)
Ltac s_lwf := first [eassumption | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption].
Ltac s_side :=
  first [ eassumption | apply lequiv_refl; s_lwf | apply lequiv_sym; eassumption | s_lwf
        | eapply VTyG_refl_l; eassumption | eapply VTy_refl_l; eassumption ].

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
  | solve [simple eapply V_fin_zero; s_side] | solve [simple eapply V_fin_succ; s_side] ].

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

Section Rules.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Local Notation VCtxS := (@VCtxS EP EM E LP).
Local Notation VTyS := (@VTyS EP EM E LP).
Local Notation VTmS := (@VTmS EP EM E LP).

Lemma VS_var {G Γ n T l} : in_ctx Γ n T l -> VTmS G Γ (var n) (var n) T l.
Proof using . intros; s_lift. Qed.
Lemma VS_nat {G Γ} : VTyS G Γ tyNat tyNat lzero.
Proof using . s_lift. Qed.
Lemma VS_zero {G Γ} : VTmS G Γ zero zero tyNat lzero.
Proof using EL VL. s_lift. Qed.
Lemma VS_succ {G Γ t t'} : VTmS G Γ t t' tyNat lzero -> VTmS G Γ (succ t) (succ t') tyNat lzero.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_U {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tyU l) (tyU l') (lsuc l).
Proof using . intros; s_lift. Qed.
Lemma VS_El {G Γ l l' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ t t' (tyU l) (lsuc l) -> VTyS G Γ (tyEl l t) (tyEl l' t') l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_code_nat {G Γ} : VTmS G Γ tmNat tmNat (tyU lzero) (lsuc lzero).
Proof using EL VL. s_lift. Qed.
Lemma VS_code_U {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmU l) (tmU l') (tyU (lsuc l)) (lsuc (lsuc l)).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_nat {G Γ} : VTyS G Γ tyNat (tyEl lzero tmNat) lzero.
Proof using . s_lift. Qed.
Lemma VS_El_U {G Γ l} : lwf (gL G) l -> VTyS G Γ (tyU l) (tyEl (lsuc l) (tmU l)) (lsuc l).
Proof using . intros; s_lift. Qed.

Lemma VS_pi {ly G Γ l l' l3 l4 A A' B B'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTyS G Γ (tyPi l l' A B) (tyPi l3 l4 A' B') (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_app {ly G Γ l l' l3 l4 A A' B B' t t' s s'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ t t' (tyPi l l' A B) (lmax l l') -> VTmS G Γ s s' A l ->
  VTmS G Γ (app t l l' A B s) (app t' l3 l4 A' B' s') B[lsingle s] l'.
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_lam {ly G Γ l l' l3 l4 A A' B t t'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ ly ] t : B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G (Γ ,, A @ l) t t' B l' ->
  VTmS G Γ (lam l l' A t) (lam l3 l4 A' t') (tyPi l l' A B) (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_natrec {ly G Γ l l' M M' s s' z z' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ ly ] M @ l ] -> [ G ; Γ ⊢[ ly ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ ly ] z : M[lsucc] @ l ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G (Γ ,, tyNat @ lzero) M M' l -> VTmS G Γ s s' M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] l -> VTmS G Γ t t' tyNat lzero ->
  VTmS G Γ (natrec l M s z t) (natrec l' M' s' z' t') M[lsingle t] l.
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_code_pi {ly G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ ly ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ ly ] t : tyU l2 @ lsuc l2 ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL VL VN. intros; s_lift. Qed.

(** ** Computation rules *)

Lemma VS_beta {ly G Γ l l' A B t s} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> [ G ; Γ ,, A @ l ⊢[ ly ] t : B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTmS G (Γ ,, A @ l) t t B l' -> VTmS G Γ s s A l ->
  VTmS G Γ (app (lam l l' A t) l l' A B s) t[lsingle s] B[lsingle s] l'.
Proof using EL VL.
  intros. eapply (VTmS_trans_diag EP EM (t2 := t[lsingle s])); [s_diag V_beta | eapply VTmS_single; eassumption].
Qed.

Lemma VS_eta {ly G Γ l l' A B t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  [ G ; Γ ⊢[ ly ] t : tyPi l l' A B @ lmax l l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ t t (tyPi l l' A B) (lmax l l') ->
  VTmS G Γ (lam l l' A (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))) t (tyPi l l' A B) (lmax l l').
Proof using EL VL VN. intros. eapply (VTmS_trans_diag EP EM (t2 := t)); [s_diag V_eta | eassumption]. Qed.

Lemma VS_natrec_zero {ly G Γ l M s z} : lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ ly ] M @ l ] -> [ G ; Γ ⊢[ ly ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ ly ] z : M[lsucc] @ l ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G (Γ ,, tyNat @ lzero) M M l -> VTmS G Γ s s M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l ->
  VTmS G Γ (natrec l M s z zero) s M[lsingle zero] l.
Proof using EL VL. intros. eapply (VTmS_trans_diag EP EM (t2 := s)); [s_diag V_natrec_zero | eassumption]. Qed.

Lemma VS_natrec_succ {ly G Γ l M s z t} : lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ ly ] M @ l ] -> [ G ; Γ ⊢[ ly ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ ly ] z : M[lsucc] @ l ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G (Γ ,, tyNat @ lzero) M M l -> VTmS G Γ s s M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l -> VTmS G Γ t t tyNat lzero ->
  VTmS G Γ (natrec l M s z (succ t)) z[lsingle2 t (natrec l M s z t)] M[lsingle (succ t)] l.
Proof using EL VL VN.
  intros. eapply (VTmS_trans_diag EP EM (t2 := z[lsingle2 t (natrec l M s z t)])); [s_diag V_natrec_succ|].
  eapply VTmS_single2; try eassumption.
  eapply VS_natrec; try eassumption. apply lequiv_refl; assumption.
Qed.

Lemma VS_El_pi {ly G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ ly ] t : tyU l' @ lsuc l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTyS G Γ (tyPi l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmPi l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Hs Ht Hly Hty Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmPi l l' s t))); [s_diag V_El_pi|].
  apply VS_El; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  eapply VS_code_pi; try eassumption; apply lequiv_refl; assumption.
Qed.

(** ** Dependent pairs (M8) *)

Lemma VS_sig {ly G Γ l l' l3 l4 A A' B B'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTyS G Γ (tySig l l' A B) (tySig l3 l4 A' B') (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_code_sig {ly G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ ly ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ ly ] t : tyU l2 @ lsuc l2 ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_pair {ly G Γ l l' l3 l4 A A' B B' a a' b b'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ a a' A l -> VTmS G Γ b b' B[lsingle a] l' ->
  VTmS G Γ (tmPair l l' A B a b) (tmPair l3 l4 A' B' a' b') (tySig l l' A B) (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_fst {ly G Γ l l' l3 l4 A A' B B' p p'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ p p' (tySig l l' A B) (lmax l l') ->
  VTmS G Γ (tmFst l l' A B p) (tmFst l3 l4 A' B' p') A l.
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_snd {ly G Γ l l' l3 l4 A A' B B' p p'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ p p' (tySig l l' A B) (lmax l l') ->
  VTmS G Γ (tmSnd l l' A B p) (tmSnd l3 l4 A' B' p') B[lsingle (tmFst l l' A B p)] l'.
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_fst_beta {ly G Γ l l' A B a b} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> [ G ; Γ ⊢[ ly ] a : A @ l ] ->
  [ G ; Γ ⊢[ ly ] b : B[lsingle a] @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ a a A l -> VTmS G Γ b b B[lsingle a] l' ->
  VTmS G Γ (tmFst l l' A B (tmPair l l' A B a b)) a A l.
Proof using EL VL. intros. eapply (VTmS_trans_diag EP EM (t2 := a)); [s_diag V_fst_beta | eassumption]. Qed.

Lemma VS_snd_beta {ly G Γ l l' A B a b} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> [ G ; Γ ⊢[ ly ] a : A @ l ] ->
  [ G ; Γ ⊢[ ly ] b : B[lsingle a] @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ a a A l -> VTmS G Γ b b B[lsingle a] l' ->
  VTmS G Γ (tmSnd l l' A B (tmPair l l' A B a b)) b B[lsingle a] l'.
Proof using EL VL. intros. eapply (VTmS_trans_diag EP EM (t2 := b)); [s_diag V_snd_beta | eassumption]. Qed.

Lemma VS_sig_eta {ly G Γ l l' A B p} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  [ G ; Γ ⊢[ ly ] p : tySig l l' A B @ lmax l l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ p p (tySig l l' A B) (lmax l l') ->
  VTmS G Γ (tmPair l l' A B (tmFst l l' A B p) (tmSnd l l' A B p)) p (tySig l l' A B) (lmax l l').
Proof using EL VL VN. intros. eapply (VTmS_trans_diag EP EM (t2 := p)); [s_diag V_sig_eta | eassumption]. Qed.

Lemma VS_El_sig {ly G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ ly ] t : tyU l' @ lsuc l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTyS G Γ (tySig l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmSig l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Hs Ht Hly Hty Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmSig l l' s t))); [s_diag V_El_sig|].
  apply VS_El; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  eapply VS_code_sig; try eassumption; apply lequiv_refl; assumption.
Qed.

(** The unit type (M8c). *)
Lemma VS_unit {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tyUnit l) (tyUnit l') l.
Proof using . intros; s_lift. Qed.
Lemma VS_code_unit {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmUnit l) (tmUnit l') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_triv {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTmS G Γ (tmTriv l) (tmTriv l') (tyUnit l) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_unit {G Γ l} : lwf (gL G) l -> VTyS G Γ (tyUnit l) (tyEl l (tmUnit l)) l.
Proof using . intros; s_lift. Qed.
Lemma VS_unit_eta {G Γ l t t'} : lwf (gL G) l ->
  VTmS G Γ t t (tyUnit l) l -> VTmS G Γ t' t' (tyUnit l) l -> VTmS G Γ t t' (tyUnit l) l.
Proof using EL VL. intros; s_lift. Qed.

(** Strict equality (M10a). *)
Lemma VS_seq {G Γ l l' A A' a a' b b'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ b b' A l ->
  VTyS G Γ (tySEq l A a b) (tySEq l' A' a' b') l.
Proof using EL. intros; s_lift. Qed.
Lemma VS_sempty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tySEmpty l) (tySEmpty l') l.
Proof using . intros; s_lift. Qed.
Lemma VS_srefl {G Γ l l' A A' a a'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ (srefl l A a) (srefl l' A' a') (tySEq l A a a) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_elimSEmpty {G Γ l1 l2 l3 l4 M M' e e'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
  VTyS G Γ M M' l2 -> VTmS G Γ e e' (tySEmpty l1) l1 ->
  VTmS G Γ (elimSEmpty l1 l2 M e) (elimSEmpty l3 l4 M' e') M l2.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_seq_irr {G Γ l A a b t t'} :
  VTmS G Γ t t (tySEq l A a b) l -> VTmS G Γ t' t' (tySEq l A a b) l -> VTmS G Γ t t' (tySEq l A a b) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_sempty_irr {G Γ l t t'} : lwf (gL G) l ->
  VTmS G Γ t t (tySEmpty l) l -> VTmS G Γ t' t' (tySEmpty l) l -> VTmS G Γ t t' (tySEmpty l) l.
Proof using EL VL. intros; s_lift. Qed.

(** The identity type (M11a). *)
Lemma VS_id {G Γ l l' A A' a a' b b'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ b b' A l ->
  VTyS G Γ (tyId l A a b) (tyId l' A' a' b') l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_idrefl {G Γ l l' A A' a a'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ (tmRefl l A a) (tmRefl l' A' a') (tyId l A a a) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_J {G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' e e'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTmS G Γ a a' A l1 ->
  VTyS G (Γ ,, A @ l1) (tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0)) (tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0)) l1 ->
  VTyS G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' l2 ->
  VTmS G Γ c c' M[lsingle2 a (tmRefl l1 A a)] l2 ->
  VTmS G Γ u u' A l1 -> VTmS G Γ e e' (tyId l1 A a u) l1 ->
  VTmS G Γ (tmJ l1 l2 A a M c u e) (tmJ l3 l4 A' a' M' c' u' e') M[lsingle2 u e] l2.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_J_beta {G Γ l l' A a M c} : lwf (gL G) l -> lwf (gL G) l' ->
  VTyS G Γ A A l -> VTmS G Γ a a A l ->
  VTyS G (Γ ,, A @ l) (tyId l A⟨↑⟩ a⟨↑⟩ (var 0)) (tyId l A⟨↑⟩ a⟨↑⟩ (var 0)) l ->
  VTyS G (Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l) M M l' ->
  VTmS G Γ c c M[lsingle2 a (tmRefl l A a)] l' ->
  VTmS G Γ (tmJ l l' A a M c a (tmRefl l A a)) c M[lsingle2 a (tmRefl l A a)] l'.
Proof using EL VL VN. intros. eapply (VTmS_trans_diag EP EM (t2 := c)); [s_diag V_J_beta | eassumption]. Qed.

(** The identity type's code (M11b). *)
Lemma VS_code_id {G Γ l l' s s' t t' u u'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ s s' (tyU l) (lsuc l) -> VTmS G Γ t t' (tyEl l s) l -> VTmS G Γ u u' (tyEl l s) l ->
  VTmS G Γ (tmId l s t u) (tmId l' s' t' u') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_id {G Γ l s t u} : lwf (gL G) l ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G Γ t t (tyEl l s) l -> VTmS G Γ u u (tyEl l s) l ->
  VTyS G Γ (tyId l (tyEl l s) t u) (tyEl l (tmId l s t u)) l.
Proof using EL VL VN.
  intros Hw Vs Vt Vu. eapply (VTyS_trans_diag EP EM (T2 := tyEl l (tmId l s t u))); [s_diag V_El_id|].
  apply VS_El; [exact Hw | apply lequiv_refl, Hw |].
  apply VS_code_id; [exact Hw | apply lequiv_refl, Hw | exact Vs | exact Vt | exact Vu].
Qed.

(** Strict equality's codes (M10c). *)
Lemma VS_code_seq {G Γ l l' s s' t t' u u'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ s s' (tyU l) (lsuc l) -> VTmS G Γ t t' (tyEl l s) l -> VTmS G Γ u u' (tyEl l s) l ->
  VTmS G Γ (tmSEq l s t u) (tmSEq l' s' t' u') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_seq {G Γ l s t u} : lwf (gL G) l ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G Γ t t (tyEl l s) l -> VTmS G Γ u u (tyEl l s) l ->
  VTyS G Γ (tySEq l (tyEl l s) t u) (tyEl l (tmSEq l s t u)) l.
Proof using EL VL VN.
  intros Hw Vs Vt Vu. eapply (VTyS_trans_diag EP EM (T2 := tyEl l (tmSEq l s t u))); [s_diag V_El_seq|].
  apply VS_El; [exact Hw | apply lequiv_refl, Hw |].
  apply VS_code_seq; [exact Hw | apply lequiv_refl, Hw | exact Vs | exact Vt | exact Vu].
Qed.
Lemma VS_code_sempty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmSEmpty l) (tmSEmpty l') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_sempty {G Γ l} : lwf (gL G) l -> VTyS G Γ (tySEmpty l) (tyEl l (tmSEmpty l)) l.
Proof using . intros; s_lift. Qed.

(** The empty type (M12a). *)
Lemma VS_empty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tyEmpty l) (tyEmpty l') l.
Proof using . intros; s_lift. Qed.
Lemma VS_elimEmpty {ly G Γ l1 l2 l3 l4 M M' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ ly ] M @ l1 ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G (Γ ,, tyEmpty l2 @ l2) M M' l1 -> VTmS G Γ t t' (tyEmpty l2) l2 ->
  VTmS G Γ (elimEmpty l1 l2 M t) (elimEmpty l3 l4 M' t') M[lsingle t] l1.
Proof using EL VL VN. intros; s_lift. Qed.

(** Binary sums (M12b). *)
Lemma VS_sum {G Γ l1 l2 l3 l4 A A' B B'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTyS G Γ B B' l2 -> VTyS G Γ (tySum l1 l2 A B) (tySum l3 l4 A' B') (lmax l1 l2).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_inl {G Γ l1 l2 l3 l4 A A' B B' a a'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTyS G Γ B B' l2 -> VTmS G Γ a a' A l1 ->
  VTmS G Γ (tmInl l1 l2 A B a) (tmInl l3 l4 A' B' a') (tySum l1 l2 A B) (lmax l1 l2).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_inr {G Γ l1 l2 l3 l4 A A' B B' b b'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTyS G Γ B B' l2 -> VTmS G Γ b b' B l2 ->
  VTmS G Γ (tmInr l1 l2 A B b) (tmInr l3 l4 A' B' b') (tySum l1 l2 A B) (lmax l1 l2).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_case {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' t t'} :
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l3 ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  VTyS G Γ A A' l1 -> VTyS G Γ B B' l2 -> VTyS G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' l3 ->
  VTmS G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3 ->
  VTmS G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3 ->
  VTmS G Γ t t' (tySum l1 l2 A B) (lmax l1 l2) ->
  VTmS G Γ (tmCase l1 l2 l3 A B M c1 c2 t) (tmCase l4 l5 l6 A' B' M' c1' c2' t') M[lsingle t] l3.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_case_inl {ly G Γ l l' l'' A B M c1 c2 a} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ⊢[ ly ] B @ l' ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G Γ B B l' -> VTyS G (Γ ,, tySum l l' A B @ lmax l l') M M l'' ->
  VTmS G (Γ ,, A @ l) c1 c1 M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] l'' ->
  VTmS G (Γ ,, B @ l') c2 c2 M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] l'' ->
  VTmS G Γ a a A l ->
  VTmS G Γ (tmCase l l' l'' A B M c1 c2 (tmInl l l' A B a)) c1[lsingle a] M[lsingle (tmInl l l' A B a)] l''.
Proof using EL VL VN.
  intros. eapply (VTmS_trans_diag EP EM (t2 := c1[lsingle a])); [s_diag V_case_inl|].
  rewrite <- (case_inl_single M l l' A B a) by (eapply wf_ty_nf; eassumption).
  eapply VTmS_single; eassumption.
Qed.
Lemma VS_case_inr {ly G Γ l l' l'' A B M c1 c2 b} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ⊢[ ly ] B @ l' ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G Γ B B l' -> VTyS G (Γ ,, tySum l l' A B @ lmax l l') M M l'' ->
  VTmS G (Γ ,, A @ l) c1 c1 M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] l'' ->
  VTmS G (Γ ,, B @ l') c2 c2 M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] l'' ->
  VTmS G Γ b b B l' ->
  VTmS G Γ (tmCase l l' l'' A B M c1 c2 (tmInr l l' A B b)) c2[lsingle b] M[lsingle (tmInr l l' A B b)] l''.
Proof using EL VL VN.
  intros. eapply (VTmS_trans_diag EP EM (t2 := c2[lsingle b])); [s_diag V_case_inr|].
  rewrite <- (case_inr_single M l l' A B b) by (eapply wf_ty_nf; eassumption).
  eapply VTmS_single; eassumption.
Qed.

(** The codes of Empty and + (M12c). *)
Lemma VS_code_empty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmEmpty l) (tmEmpty l') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_empty {G Γ l} : lwf (gL G) l -> VTyS G Γ (tyEmpty l) (tyEl l (tmEmpty l)) l.
Proof using . intros; s_lift. Qed.
Lemma VS_code_sum {G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G Γ t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_sum {G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G Γ t t (tyU l') (lsuc l') ->
  VTyS G Γ (tySum l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmSum l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmSum l l' s t))); [s_diag V_El_sum|].
  apply VS_El; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  apply VS_code_sum; [exact Hw | exact Hw' | apply lequiv_refl, Hw | apply lequiv_refl, Hw' | exact Vs | exact Vt].
Qed.

(** Well-founded trees (M13a). *)
Lemma VS_W {ly G Γ l l' l3 l4 A A' B B'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTyS G Γ (tyW l l' A B) (tyW l3 l4 A' B') (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_sup {ly G Γ l l' l3 l4 A A' B B' a a' f f'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' -> VTmS G Γ a a' A l ->
  VTmS G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) (lmax l' (lmax l l')) ->
  VTmS G Γ (tmSup l l' A B a f) (tmSup l3 l4 A' B' a' f') (tyW l l' A B) (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_elimW {ly G Γ l l' l'' l4 l5 l6 A A' B B' M M' c c' t t'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  lequiv (gL G) l l4 -> lequiv (gL G) l' l5 -> lequiv (gL G) l'' l6 ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' -> VTyS G (Γ ,, tyW l l' A B @ lmax l l') M M' l'' ->
  VTyS G (Γ ,, A @ l) (wfty l l' A B) (wfty l l' A B) (lmax l' (lmax l l')) ->
  VTyS G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l')) (wihty l l' l'' A B M) (wihty l l' l'' A B M)
    (lmax l' l'') ->
  VTmS G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l'')
    c c' (wstepty l l' A B M) l'' ->
  VTmS G Γ t t' (tyW l l' A B) (lmax l l') ->
  VTmS G Γ (tmElimW l l' l'' A B M c t) (tmElimW l4 l5 l6 A' B' M' c' t') M[lsingle t] l''.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_elimW_sup {ly G Γ l l' l'' A B M c a f} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTyS G (Γ ,, tyW l l' A B @ lmax l l') M M l'' ->
  VTyS G (Γ ,, A @ l) (wfty l l' A B) (wfty l l' A B) (lmax l' (lmax l l')) ->
  VTyS G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l')) (wihty l l' l'' A B M) (wihty l l' l'' A B M)
    (lmax l' l'') ->
  VTmS G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l'')
    c c (wstepty l l' A B M) l'' ->
  VTmS G Γ a a A l ->
  VTmS G Γ f f (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) (lmax l' (lmax l l')) ->
  VTmS G Γ (tmElimW l l' l'' A B M c (tmSup l l' A B a f)) c[lsingle3 a f (wIH l l' l'' A B M c a f)]
    M[lsingle (tmSup l l' A B a f)] l''.
Proof using EL VL VN. intros; s_lift. Qed.

(** The code of W (M13b), as Σ's. *)
Lemma VS_code_W {ly G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ ly ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ ly ] t : tyU l2 @ lsuc l2 ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmW l1 l2 s t) (tmW l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_El_W {ly G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ ly ] t : tyU l' @ lsuc l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTyS G Γ (tyW l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmW l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Hs Ht Hly Hty Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmW l l' s t))); [s_diag V_El_W|].
  apply VS_El; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  eapply VS_code_W; try eassumption; apply lequiv_refl; assumption.
Qed.

(** Vec and Fin (M14a). *)
Lemma VS_vec {G Γ l l' A A' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ n n' tyNat lzero -> VTyS G Γ (tyVec l A n) (tyVec l' A' n') l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_fin {G Γ n n'} : VTmS G Γ n n' tyNat lzero -> VTyS G Γ (tyFin n) (tyFin n') lzero.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_vec_zero {G Γ l l' A A'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTyS G Γ (tyVec l A zero) (tyUnit l') l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_vec_succ {G Γ l l' A A' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ n n' tyNat lzero ->
  VTyS G Γ (tyVec l A (succ n)) (tySig l' l' A' (tyVec l' A'⟨↑⟩ n'⟨↑⟩)) l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_fin_zero {G Γ} : VTyS G Γ (tyFin zero) (tyEmpty lzero) lzero.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_fin_succ {G Γ n n'} : VTmS G Γ n n' tyNat lzero ->
  VTyS G Γ (tyFin (succ n)) (tySum lzero lzero (tyUnit lzero) (tyFin n')) lzero.
Proof using EL VL VN. intros; s_lift. Qed.

End Rules.

End RulesS.

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
  | solve [simple eapply VS_fin_zero; side] | solve [simple eapply VS_fin_succ; side] ].
