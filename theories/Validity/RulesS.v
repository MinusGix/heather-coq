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

Local Ltac along k :=
  intros H; pose proof (gsr_wf_l _ _ _ _ _ _ Hσ) as Hw; pose proof (GSubRel_to _ _ Hσ) as EG;
  rewrite EG in Hw |- *; exact (k _ _ _ _ _ _ _ H _ _ Hw) || exact (k _ _ _ _ _ _ H _ _ Hw)
  || exact (k _ _ _ _ _ H _ _ Hw) || exact (k _ _ _ _ H _ _ Hw) || exact (k _ _ _ H _ _ Hw).

Lemma gs_ctx {i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G' ; Γ⦃σ⦄ ⊢[ i ] ].
Proof. along (proj1 (proj2 gsubstitution)). Qed.
Lemma gs_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G' ; Γ⦃σ⦄ ⊢[ i ] T⦃σ⦄ @ l ].
Proof. along (proj1 (proj2 (proj2 gsubstitution))). Qed.
Lemma gs_tm {i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G' ; Γ⦃σ⦄ ⊢[ i ] t⦃σ⦄ : T⦃σ⦄ @ l ].
Proof. along (proj1 (proj2 (proj2 (proj2 gsubstitution)))). Qed.
Lemma gs_eqty {i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G' ; Γ⦃σ⦄ ⊢[ i ] T⦃σ⦄ ≅ T'⦃σ⦄ @ l ].
Proof. along (proj1 (proj2 (proj2 (proj2 (proj2 gsubstitution))))). Qed.
Lemma gs_eqtm {i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G' ; Γ⦃σ⦄ ⊢[ i ] t⦃σ⦄ ≅ t'⦃σ⦄ : T⦃σ⦄ @ l ].
Proof. along (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 gsubstitution)))))). Qed.

End Along.

(** ** Lifting an M1 case along [σ ≈ σ'] *)

(** Presupposed typings (left-hand sides and types), for the lemmas'
    premises. *)
Ltac s_types :=
  repeat match goal with
  | H : wf_tm ?G lD ?Γ ?t ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G lD Γ T l |- _ => fail
      | _ => pose proof (wf_tm_ty (i := lD) eq_refl H)
      end
  | H : eq_ty ?G lD ?Γ ?T ?T' ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G lD Γ T l |- _ => fail
      | _ => pose proof (eqty_wf_l (i := lD) eq_refl H)
      end
  | H : eq_tm ?G lD ?Γ ?t ?t' ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_tm G lD Γ t T l |- _ => fail
      | _ => pose proof (eqtm_wf_l (i := lD) eq_refl H)
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
    | H : wf_ctx G _ _ |- _ => pose proof (gs_ctx Hσ H); clear H
    | H : wf_ty G _ _ _ _ |- _ => pose proof (gs_ty Hσ H); clear H
    | H : wf_tm G _ _ _ _ _ |- _ => pose proof (gs_tm Hσ H); clear H
    | H : eq_ty G _ _ _ _ _ |- _ => pose proof (gs_eqty Hσ H); clear H
    | H : eq_tm G _ _ _ _ _ _ |- _ => pose proof (gs_eqtm Hσ H); clear H
    | H : in_ctx ?Γ0 _ _ _ |- _ =>
        lazymatch Γ0 with gsubst _ _ => fail | _ => pose proof (in_ctx_gsubst _ _ _ _ σ H); clear H end
    | H : lequiv (gL G) _ _ |- _ => rewrite <- (gsr_L _ _ _ _ _ _ Hσ) in H
    | H : lwf (gL G) _ |- _ => rewrite <- (gsr_L _ _ _ _ _ _ Hσ) in H
    end
  end.

(** Only the goal's instance matters; the other one's hypotheses go. *)
Ltac s_along :=
  lazymatch goal with
  | |- @VTyG ?E0 ?LP0 _ _ _ _ _ => s_along_at E0 LP0
  | |- @VTmG ?E0 ?LP0 _ _ _ _ _ _ => s_along_at E0 LP0
  end.

Ltac s_push :=
  repeat progress (
    rewrite ?gs_single_ty, ?gs_single, ?gs_single2, ?gs_lsucc_ty, ?gsubst_ren_ty', ?gs_ren in *;
    rewrite ?gs_tyNat, ?gs_tyPi, ?gs_tyU, ?gs_tyEl, ?gs_var, ?gs_tmNat, ?gs_tmPi, ?gs_tmU, ?gs_zero,
            ?gs_succ, ?gs_natrec, ?gs_lam, ?gs_app, ?gs_cnil, ?gs_cext in *).

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
  | solve [simple eapply V_natrec; s_side] | solve [simple eapply V_lam; s_side] | solve [simple eapply V_app; s_side] ].

Ltac s_lift :=
  s_types;
  match goal with
  | |- @VTyS _ _ _ _ _ _ _ _ _ => intros ? ? ? ?
  | |- @VTmS _ _ _ _ _ _ _ _ _ _ => intros ? ? ? ?
  end;
  s_along; s_push; gl_lift; fts_case.

(** At a substitution related to itself, the rule-shaped wrappers apply. *)
Tactic Notation "s_diag" uconstr(lem) :=
  s_types; intros ? ? ?; s_along; s_push; gl_lift; simple eapply lem; eassumption.


(** ** The rules *)

Section Rules.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Local Notation VCtxS := (@VCtxS EP EM E LP).
Local Notation VTyS := (@VTyS EP EM E LP).
Local Notation VTmS := (@VTmS EP EM E LP).

Lemma VS_var {G Γ n T l} : in_ctx Γ n T l -> VTmS G Γ (var n) (var n) T l.
Proof. intros; s_lift. Qed.
Lemma VS_nat {G Γ} : VTyS G Γ tyNat tyNat lzero.
Proof. s_lift. Qed.
Lemma VS_zero {G Γ} : VTmS G Γ zero zero tyNat lzero.
Proof. s_lift. Qed.
Lemma VS_succ {G Γ t t'} : VTmS G Γ t t' tyNat lzero -> VTmS G Γ (succ t) (succ t') tyNat lzero.
Proof. intros; s_lift. Qed.
Lemma VS_U {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tyU l) (tyU l') (lsuc l).
Proof. intros; s_lift. Qed.
Lemma VS_El {G Γ l l' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ t t' (tyU l) (lsuc l) -> VTyS G Γ (tyEl l t) (tyEl l' t') l.
Proof. intros; s_lift. Qed.
Lemma VS_code_nat {G Γ} : VTmS G Γ tmNat tmNat (tyU lzero) (lsuc lzero).
Proof. s_lift. Qed.
Lemma VS_code_U {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmU l) (tmU l') (tyU (lsuc l)) (lsuc (lsuc l)).
Proof. intros; s_lift. Qed.
Lemma VS_El_nat {G Γ} : VTyS G Γ tyNat (tyEl lzero tmNat) lzero.
Proof. s_lift. Qed.
Lemma VS_El_U {G Γ l} : lwf (gL G) l -> VTyS G Γ (tyU l) (tyEl (lsuc l) (tmU l)) (lsuc l).
Proof. intros; s_lift. Qed.

Lemma VS_pi {G Γ l l' l3 l4 A A' B B'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ lD ] B @ l' ] ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTyS G Γ (tyPi l l' A B) (tyPi l3 l4 A' B') (lmax l l').
Proof. intros; s_lift. Qed.

Lemma VS_app {G Γ l l' l3 l4 A A' B B' t t' s s'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ lD ] B @ l' ] ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ t t' (tyPi l l' A B) (lmax l l') -> VTmS G Γ s s' A l ->
  VTmS G Γ (app t l l' A B s) (app t' l3 l4 A' B' s') B[lsingle s] l'.
Proof. intros; s_lift. Qed.

Lemma VS_lam {G Γ l l' l3 l4 A A' B t t'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ lD ] B @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ lD ] t : B @ l' ] ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G (Γ ,, A @ l) t t' B l' ->
  VTmS G Γ (lam l l' A t) (lam l3 l4 A' t') (tyPi l l' A B) (lmax l l').
Proof. intros; s_lift. Qed.

Lemma VS_natrec {G Γ l l' M M' s s' z z' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ lD ] M @ l ] -> [ G ; Γ ⊢[ lD ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ lD ] z : M[lsucc] @ l ] ->
  VTyS G (Γ ,, tyNat @ lzero) M M' l -> VTmS G Γ s s' M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] l -> VTmS G Γ t t' tyNat lzero ->
  VTmS G Γ (natrec l M s z t) (natrec l' M' s' z' t') M[lsingle t] l.
Proof. intros; s_lift. Qed.

Lemma VS_code_pi {G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ lD ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ lD ] t : tyU l2 @ lsuc l2 ] ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof. intros; s_lift. Qed.

(** ** Computation rules *)

Lemma VS_beta {G Γ l l' A B t s} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢[ lD ] B @ l' ] -> [ G ; Γ ,, A @ l ⊢[ lD ] t : B @ l' ] ->
  VTyS G Γ A A l -> VTmS G (Γ ,, A @ l) t t B l' -> VTmS G Γ s s A l ->
  VTmS G Γ (app (lam l l' A t) l l' A B s) t[lsingle s] B[lsingle s] l'.
Proof.
  intros. eapply (VTmS_trans_diag EP EM (t2 := t[lsingle s])); [s_diag V_beta | eapply VTmS_single; eassumption].
Qed.

Lemma VS_eta {G Γ l l' A B t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ lD ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ lD ] B @ l' ] ->
  [ G ; Γ ⊢[ lD ] t : tyPi l l' A B @ lmax l l' ] ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ t t (tyPi l l' A B) (lmax l l') ->
  VTmS G Γ (lam l l' A (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))) t (tyPi l l' A B) (lmax l l').
Proof. intros. eapply (VTmS_trans_diag EP EM (t2 := t)); [s_diag V_eta | eassumption]. Qed.

Lemma VS_natrec_zero {G Γ l M s z} : lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ lD ] M @ l ] -> [ G ; Γ ⊢[ lD ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ lD ] z : M[lsucc] @ l ] ->
  VTyS G (Γ ,, tyNat @ lzero) M M l -> VTmS G Γ s s M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l ->
  VTmS G Γ (natrec l M s z zero) s M[lsingle zero] l.
Proof. intros. eapply (VTmS_trans_diag EP EM (t2 := s)); [s_diag V_natrec_zero | eassumption]. Qed.

Lemma VS_natrec_succ {G Γ l M s z t} : lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ lD ] M @ l ] -> [ G ; Γ ⊢[ lD ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ lD ] z : M[lsucc] @ l ] ->
  VTyS G (Γ ,, tyNat @ lzero) M M l -> VTmS G Γ s s M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l -> VTmS G Γ t t tyNat lzero ->
  VTmS G Γ (natrec l M s z (succ t)) z[lsingle2 t (natrec l M s z t)] M[lsingle (succ t)] l.
Proof.
  intros. eapply (VTmS_trans_diag EP EM (t2 := z[lsingle2 t (natrec l M s z t)])); [s_diag V_natrec_succ|].
  eapply VTmS_single2; try eassumption.
  eapply VS_natrec; try eassumption. apply lequiv_refl; assumption.
Qed.

Lemma VS_El_pi {G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ lD ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ lD ] t : tyU l' @ lsuc l' ] ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTyS G Γ (tyPi l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmPi l l' s t)) (lmax l l').
Proof.
  intros Hw Hw' Hs Ht Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmPi l l' s t))); [s_diag V_El_pi|].
  apply VS_El; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  eapply VS_code_pi; try eassumption; apply lequiv_refl; assumption.
Qed.

End Rules.

End RulesS.
