(** * Syntactic metatheory needed before the logical relation

    - context extraction ("boundary" for contexts), all layers;
    - weakening of every judgment, for layers with [typeof i = i]
      (D and M -- layer C would need the paper's lifting lemma). *)
From DeLaM.Typing Require Export Declarative.

(** ** Lookup under weakening *)

Lemma in_ctx_nf Γ n T l : in_ctx Γ n T l -> nfty T.
Proof. destruct 1; apply ren_nf_ty. Qed.

Lemma in_ctx_wk Γ n T l ρ Δ : in_ctx Γ n T l -> ρ : Δ ≤ Γ -> in_ctx Δ (rlk ρ n) T⟨ρ⟩ l.
Proof.
  intros Hin Hρ; revert n T l Hin; induction Hρ as [Γ|ρ Δ Γ A l' Hρ IH|ρ Δ Γ A l' Hρ IH];
    intros n T l Hin; cbn [wk_ren].
  - replace (rlk (rshift 0) n) with n by (cbn; lia).
    rewrite ren_id_ty by eauto using in_ctx_nf. exact Hin.
  - rewrite rlk_rup. replace T⟨rup ρ⟩ with T⟨ρ⟩⟨↑⟩.
    + constructor; auto.
    + rewrite ren_ren_comp_ty. apply ren_ext_ty; intros m; rlk_simpl; lia.
  - inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 B l1 m Hm]; subst; rewrite rlk_rlift.
    + rewrite shift_lift_ty. constructor.
    + rewrite shift_lift_ty. constructor; auto.
Qed.

(** ** Weakenings as renamings *)

Inductive wkr : rsub -> ctx -> ctx -> Prop :=
| wkr_id Γ : wkr (rshift 0) Γ Γ
| wkr_step r Δ Γ A l : wkr r Δ Γ -> wkr (rup r) (Δ ,, A @ l) Γ
| wkr_up r Δ Γ A l : wkr r Δ Γ -> wkr (rlift r) (Δ ,, A⟨r⟩ @ l) (Γ ,, A @ l).

Lemma wk_wf_wkr ρ Δ Γ : ρ : Δ ≤ Γ -> wkr ρ Δ Γ.
Proof. induction 1; cbn; now constructor. Qed.

Lemma in_ctx_wkr Γ n T l r Δ : in_ctx Γ n T l -> wkr r Δ Γ -> in_ctx Δ (rlk r n) T⟨r⟩ l.
Proof.
  intros Hin Hr; revert n T l Hin; induction Hr as [Γ|r Δ Γ A l' Hr IH|r Δ Γ A l' Hr IH];
    intros n T l Hin.
  - replace (rlk (rshift 0) n) with n by (cbn; lia).
    rewrite ren_id_ty by eauto using in_ctx_nf. exact Hin.
  - rewrite rlk_rup. replace T⟨rup r⟩ with T⟨r⟩⟨↑⟩.
    + constructor; auto.
    + rewrite ren_ren_comp_ty. apply ren_ext_ty; intros m; rlk_simpl; lia.
  - inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 B l1 m Hm]; subst; rewrite rlk_rlift.
    + rewrite shift_lift_ty. constructor.
    + rewrite shift_lift_ty. constructor; auto.
Qed.

#[export] Hint Constructors wkr : wk.

(** ** Context extraction *)

Theorem ctx_extract :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]).
Proof.
  apply typing_mut; intros; rewrite ?typeof_idem in *; auto.
  all: destruct i; cbn in *; auto.
Qed.

(** ** Weakening *)

(** Fold raw renamings/substitutions (exposed by [cbn]) back into notation form. *)
Ltac fold_subst :=
  repeat match goal with
         | |- context [ren_tm ?x ?y] => change (ren_tm x y) with (@ren tm Ren_tm x y)
         | |- context [ren_ty ?x ?y] => change (ren_ty x y) with (@ren ty Ren_ty x y)
         | |- context [subst_tm ?x ?y] => change (subst_tm x y) with (@subst tm Subst_tm x y)
         | |- context [subst_ty ?x ?y] => change (subst_ty x y) with (@subst ty Subst_ty x y)
         end.

Ltac wk_rewrite :=
  rewrite ?single_ren_ty, ?single_ren, ?lsucc_ren_ty, ?single2_ren,
          ?shift_lift, ?shift_lift_ty, ?liftshift_lift_ty.

#[export] Hint Resolve wfc_ext : wk.
#[export] Hint Resolve in_ctx_wkr : wk.
#[export] Hint Resolve wft_nat wft_El lequiv_wf_l lequiv_wf_r : wk.

Lemma wkr_up' r Δ Γ A A' l : wkr r Δ Γ -> A' = A⟨r⟩ -> wkr (rlift r) (Δ ,, A' @ l) (Γ ,, A @ l).
Proof. intros ? ->; now constructor. Qed.
Lemma wf_tm_retype G i Δ x T T' l :
  [ G ; Δ ⊢[ i ] x : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? ->. Qed.
Lemma eq_tm_retype G i Δ x y T T' l :
  [ G ; Δ ⊢[ i ] x ≅ y : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? ->. Qed.

#[export] Hint Extern 2 (wkr (rlift _) _ _) =>
  eapply wkr_up'; [ | push_ren; reflexivity ] : wk.
#[export] Hint Extern 20 (wf_tm _ _ _ _ _ _) => eapply wf_tm_retype : wk.
#[export] Hint Extern 20 (eq_tm _ _ _ _ _ _ _) => eapply eq_tm_retype : wk.
#[export] Hint Extern 1 (lwf _ _) =>
  (cbn; first [exact I | assumption | split; assumption]) : wk.
#[export] Hint Extern 1 =>
  match goal with Hi : typeof ?i = ?i |- context [typeof ?i] => rewrite Hi end : wk.
#[export] Hint Extern 1 (@eq ty _ _) => (push_ren; wk_rewrite; push_ren; reflexivity) : wk.

Ltac fix_layer :=
  repeat match goal with
         | Hi : typeof ?i = ?i |- context [typeof ?i] => rewrite Hi
         end.

Ltac wk_premises := fix_layer; eauto 6 with wk.

(** Try every constructor of the goal's judgment. *)
Ltac wk_step :=
  match goal with
  | |- wf_ty _ _ _ _ _ =>
      first [ solve [eapply wft_nat; wk_premises] | solve [eapply wft_pi; wk_premises]
            | solve [eapply wft_U; wk_premises] | solve [eapply wft_El; wk_premises]
            | solve [eapply wft_lconv; wk_premises] ]
  | |- wf_tm _ _ _ _ _ _ =>
      first [ solve [eapply wf_var; wk_premises] | solve [eapply wf_code_nat; wk_premises]
            | solve [eapply wf_code_U; wk_premises] | solve [eapply wf_code_pi; wk_premises]
            | solve [eapply wf_zero; wk_premises] | solve [eapply wf_succ; wk_premises]
            | solve [eapply wf_natrec; wk_premises] | solve [eapply wf_lam; wk_premises]
            | solve [eapply wf_app; wk_premises] | solve [eapply wf_conv; wk_premises]
            | solve [eapply wf_lconv; wk_premises] ]
  | |- eq_ty _ _ _ _ _ _ =>
      first [ solve [eapply eqty_refl; wk_premises] | solve [eapply eqty_sym; wk_premises]
            | solve [eapply eqty_trans; wk_premises] | solve [eapply eqty_pi; wk_premises]
            | solve [eapply eqty_U; wk_premises] | solve [eapply eqty_El; wk_premises]
            | solve [eapply eqty_El_nat; wk_premises] | solve [eapply eqty_El_U; wk_premises]
            | solve [eapply eqty_El_pi; wk_premises] | solve [eapply eqty_lconv; wk_premises] ]
  | |- eq_tm _ _ _ _ _ _ _ =>
      first [ solve [eapply eqtm_refl; wk_premises] | solve [eapply eqtm_sym; wk_premises]
            | solve [eapply eqtm_trans; wk_premises] | solve [eapply eqtm_code_U; wk_premises]
            | solve [eapply eqtm_code_pi; wk_premises] | solve [eapply eqtm_succ; wk_premises]
            | solve [eapply eqtm_natrec; wk_premises] | solve [eapply eqtm_lam; wk_premises]
            | solve [eapply eqtm_app; wk_premises] | solve [eapply eqtm_conv; wk_premises]
            | solve [eapply eqtm_lconv; wk_premises]
            | solve [eapply eqtm_natrec_zero; wk_premises]
            | solve [eapply eqtm_natrec_succ; wk_premises]
            | solve [eapply eqtm_beta; wk_premises] | solve [eapply eqtm_eta; wk_premises] ]
  end.

Lemma wf_ctx_nat G i Δ : i <> lV -> typeof i = i -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ,, tyNat @ lzero ⊢[ i ] ].
Proof.
  intros Hv Hi HΔ. apply wfc_ext; [exact HΔ | apply wft_nat; [exact Hv | now rewrite Hi] | exact I].
Qed.
#[export] Hint Resolve wf_ctx_nat : wk.
Lemma compt_notV i : compt i -> i <> lV.
Proof. now intros [-> | ->]. Qed.
#[export] Hint Resolve compt_notV : wk.

Ltac wk_eq := push_ren; wk_rewrite; push_ren; reflexivity.

(** One premise: directly, or through an induction hypothesis up to a type equation. *)
Ltac wk_premise :=
  fix_layer;
  first [ solve [eauto 8 with wk]
        | solve [eapply wf_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with wk] end | wk_eq]]
        | solve [eapply eq_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with wk] end | wk_eq]] ].

Ltac wk_manual :=
  match goal with
  | |- wf_tm _ _ _ (natrec _ _ _ _ _) _ _ => eapply wf_natrec
  | |- eq_tm _ _ _ (tmPi _ _ _ _) _ _ _ => eapply eqtm_code_pi
  | |- eq_tm _ _ _ (natrec _ _ _ _ _) (natrec _ _ _ _ _) _ _ => eapply eqtm_natrec
  | |- eq_tm _ _ _ (natrec _ _ _ _ zero) _ _ _ => eapply eqtm_natrec_zero
  | |- eq_tm _ _ _ (natrec _ _ _ _ (succ _)) _ _ _ => eapply eqtm_natrec_succ
  end; wk_premise.

Theorem weakening_r :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ : T⟨r⟩ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ ≅ T'⟨r⟩ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ ≅ t'⟨r⟩ : T⟨r⟩ @ l ]).
Proof.
  apply typing_mut; intros; try exact I;
    match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end;
    push_ren; wk_rewrite; push_ren.
  all: try wk_step.
  all: wk_manual.
Qed.
