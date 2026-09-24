(** * Syntactic metatheory needed before the logical relation

    - context extraction ("boundary" for contexts), all layers;
    - (local) weakening of every judgment, at every layer: the weakened
      context is well formed at [typeof i]; context extensions use lifting,
      and the letbox body uses global weakening. *)
From DeLaM.Typing Require Export Lifting.

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

Lemma wkr_tail r Δ Γ : wkr r Δ Γ -> ctx_tail Δ = ctx_tail Γ /\ forall n, rlk r (clen Γ + n) = clen Δ + n.
Proof.
  induction 1 as [Γ|r Δ Γ A l H [IH1 IH2]|r Δ Γ A l H [IH1 IH2]]; cbn [ctx_tail clen];
    split; auto; intros n.
  - rewrite rlk_rup, IH2; lia.
  - replace (S (clen Γ) + n) with (S (clen Γ + n)) by lia.
    rewrite rlk_rlift, IH2; lia.
Qed.

Lemma lsub_tail_wkr d Δ Γ Γ' r : wkr r Γ' Γ -> lsub_tail d Δ Γ -> lsub_tail (lren d r) Δ Γ'.
Proof.
  intros Hr [Ht Hl]. destruct (wkr_tail _ _ _ Hr) as [Ht' Hl']. split; [congruence|].
  intros n; rewrite llk_lren, Hl; cbn; now rewrite Hl'.
Qed.

Lemma nfl_lren d r : dnfl d -> dnfl (lren d r).
Proof. apply dnfl_lren. Qed.

Lemma wkr_gren r Δ Γ ξ : wkr r Δ Γ -> wkr r Δ⟪ξ⟫ Γ⟪ξ⟫.
Proof.
  induction 1; rewrite ?gren_cext.
  - apply wkr_id.
  - now apply wkr_step.
  - rewrite gren_ren_ty'. now apply wkr_up.
Qed.

(** ** Context extraction *)

Theorem ctx_extract :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; rewrite ?typeof_idem in *; auto.
  all: try solve [destruct i; cbn in *; auto].
  all: match goal with H : wf_ctx _ _ (cext _ _ _) |- _ => inversion H; subst; auto end.
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
         end;
  rewrite ?typeof_idem.

Lemma ctx_glob G i Γ : [ G ; Γ ⊢[ i ] ] -> [ ⊢ G ].
Proof. induction 1; auto. Qed.

#[export] Hint Resolve wft_CTyp wft_CTrm : wk.
#[export] Hint Extern 3 (wf_ty _ (typeof _) _ _ _) => eapply lift_ty; [ | apply lle_self_typeof ] : wk.
#[export] Hint Extern 3 (wf_tm _ (typeof _) _ _ _ _) => eapply lift_tm; [ | apply lle_self_typeof ] : wk.
#[export] Hint Extern 1 (wf_ctx _ (typeof (typeof _)) _) => rewrite typeof_idem : wk.
#[export] Hint Resolve lsub_tail_wkr nfl_lren : wk.

Ltac wk_premises := fix_layer; eauto 6 with wk.

(** Try every constructor of the goal's judgment. *)
Ltac wk_step :=
  match goal with
  | |- wf_ty _ _ _ _ _ =>
      first [ solve [eapply wft_nat; wk_premises] | solve [eapply wft_pi; wk_premises]
            | solve [eapply wft_U; wk_premises] | solve [eapply wft_El; wk_premises]
            | solve [eapply wft_lconv; wk_premises] | solve [eapply wft_CTyp; wk_premises]
            | solve [eapply wft_CTrm; wk_premises] ]
  | |- wf_tm _ _ _ _ _ _ =>
      first [ solve [eapply wf_var; wk_premises] | solve [eapply wf_code_nat; wk_premises]
            | solve [eapply wf_code_U; wk_premises] | solve [eapply wf_code_pi; wk_premises]
            | solve [eapply wf_zero; wk_premises] | solve [eapply wf_succ; wk_premises]
            | solve [eapply wf_natrec; wk_premises] | solve [eapply wf_lam; wk_premises]
            | solve [eapply wf_app; wk_premises] | solve [eapply wf_conv; wk_premises]
            | solve [eapply wf_lconv; wk_premises] | solve [eapply wf_boxT; wk_premises]
            | solve [eapply wf_boxt; wk_premises] ]
  | |- eq_ty _ _ _ _ _ _ =>
      first [ solve [eapply eqty_refl; wk_premises] | solve [eapply eqty_sym; wk_premises]
            | solve [eapply eqty_trans; wk_premises] | solve [eapply eqty_pi; wk_premises]
            | solve [eapply eqty_U; wk_premises] | solve [eapply eqty_El; wk_premises]
            | solve [eapply eqty_El_nat; wk_premises] | solve [eapply eqty_El_U; wk_premises]
            | solve [eapply eqty_El_pi; wk_premises] | solve [eapply eqty_lconv; wk_premises]
            | solve [eapply eqty_CTyp; wk_premises] | solve [eapply eqty_CTrm; wk_premises] ]
  | |- eq_tm _ _ _ _ _ _ _ =>
      first [ solve [eapply eqtm_refl; wk_premises] | solve [eapply eqtm_sym; wk_premises]
            | solve [eapply eqtm_trans; wk_premises] | solve [eapply eqtm_code_U; wk_premises]
            | solve [eapply eqtm_code_pi; wk_premises] | solve [eapply eqtm_succ; wk_premises]
            | solve [eapply eqtm_natrec; wk_premises] | solve [eapply eqtm_lam; wk_premises]
            | solve [eapply eqtm_app; wk_premises] | solve [eapply eqtm_conv; wk_premises]
            | solve [eapply eqtm_lconv; wk_premises]
            | solve [eapply eqtm_natrec_zero; wk_premises]
            | solve [eapply eqtm_natrec_succ; wk_premises]
            | solve [eapply eqtm_beta; wk_premises] | solve [eapply eqtm_eta; wk_premises]
            | solve [eapply eqtm_boxT; wk_premises] | solve [eapply eqtm_boxt; wk_premises] ]
  end.

Lemma wf_ctx_nat G i Δ : i <> lV -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tyNat @ lzero ⊢[ typeof i ] ].
Proof.
  intros Hv HΔ. apply wfc_ext; [exact HΔ | apply wft_nat; [destruct i; cbn; congruence | now rewrite typeof_idem] | exact I].
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

(** The lookup-typed local substitution of [u^δ]/[U^δ]: its entries are
    renamed, and its target context [Δ] is untouched. *)
Ltac wk_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin; rewrite !llk_lren;
  rewrite <- (subst_ren_ty A _ _ _ (fun m => llk_lren _ _ m));
  match goal with IH : forall n A k (_ : in_ctx _ n A k), _ |- _ => eapply (IH n A k Hin) end;
  eauto with wk.

(** The letbox body: weaken [Γ⟪↑⟫] under [Ψ, U]. *)
Ltac wk_body :=
  match goal with
  | IH : forall Δ' r', wkr r' Δ' (?Γ⟪S⟫) -> wf_ctx (gext ?G ?D) _ Δ' -> _,
    Hr : wkr ?r ?Δ ?Γ, HΔ : wf_ctx ?G _ ?Δ |- _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext G D ])
        by (unfold gext; first [eapply wfg_ty | eapply wfg_tm];
            first [exact (ctx_glob _ _ _ HΔ) | eassumption | left; reflexivity | right; reflexivity
                  | cbn; eassumption | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption]);
      assert (X : [ gext G D ; Δ⟪S⟫ ⊢[ lM ] ]);
      [ exact (proj1 (proj2 gweakening) _ _ _ HΔ (D :: gΨ G) (gwk_step gwk_id)
                 (gwkwf_step _ _ _ _ (gwkwf_id _)) Hg)
      | pose proof (IH _ _ (wkr_gren _ _ _ S Hr) X) as X';
        rewrite single_ren_ty, <- gren_ren_ty', ?ren_boxT, ?ren_boxt in X'; exact X' ]
  end.

Ltac wk_manual :=
  match goal with
  | |- wf_tm _ _ _ (natrec _ _ _ _ _) _ _ => eapply wf_natrec; wk_premise
  | |- eq_tm _ _ _ (tmPi _ _ _ _) _ _ _ => eapply eqtm_code_pi; wk_premise
  | |- wf_tm _ _ _ (tmPi _ _ _ _) _ _ => eapply wf_code_pi; wk_premise
  | |- eq_ty _ _ _ (tyPi _ _ _ _) (tyEl _ _) _ => eapply eqty_El_pi; wk_premise
  | |- eq_ty _ _ _ (tyPi _ _ _ _) (tyPi _ _ _ _) _ => eapply eqty_pi; wk_premise
  | |- eq_tm _ _ _ (lam _ _ _ _) (lam _ _ _ _) _ _ => eapply eqtm_lam; wk_premise
  | |- eq_tm _ _ _ (app _ _ _ _ _ _) (app _ _ _ _ _ _) _ _ => eapply eqtm_app; wk_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ zero) _ _ _ => eapply eqtm_natrec_zero; wk_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ (succ _)) _ _ _ => eapply eqtm_natrec_succ; wk_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ _) (natrec _ _ _ _ _) _ _ => eapply eqtm_natrec; wk_premise
  | |- wf_ty _ _ _ (tyGvar _ _) _ => eapply wft_gvar; [ .. | wk_entries]; eauto with wk
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      eapply eqty_gvar; [ .. | wk_entries | wk_entries | wk_entries]; eauto with wk
  | |- wf_tm _ _ _ (gvar _ _) _ _ =>
      rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m));
      eapply wf_gvar; [ .. | wk_entries]; eauto with wk
  | |- eq_tm _ _ _ (gvar _ _) _ _ _ =>
      rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m));
      eapply eqtm_gvar; [ .. | wk_entries | wk_entries | wk_entries]; eauto with wk
  | |- wf_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ => eapply wf_letboxT; try wk_body; wk_premise
  | |- wf_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ => eapply wf_letboxt; try wk_body; wk_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ (boxT _)) _ _ _ =>
      rewrite <- gsubst_ren; eapply eqtm_letboxT_beta; try wk_body; wk_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      rewrite <- gsubst_ren; eapply eqtm_letboxt_beta; try wk_body; wk_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxT; try wk_body; wk_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxt; try wk_body; wk_premise
  end.

Theorem weakening_all :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ : T⟨r⟩ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ ≅ T'⟨r⟩ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ ≅ t'⟨r⟩ : T⟨r⟩ @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I; cbn [typeof] in *; push_ren; wk_rewrite; push_ren.
  all: try wk_step.
  all: wk_manual.
Qed.

(** The M1 form: layers with [typeof i = i]. *)
Theorem weakening_r :
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ : T⟨r⟩ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ ≅ T'⟨r⟩ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ ≅ t'⟨r⟩ : T⟨r⟩ @ l ]).
Proof.
  destruct weakening_all as (_ & _ & H1 & H2 & H3 & H4 & _).
  refine (conj _ (conj _ (conj _ _))); intros * H Hi Δ r Hr HΔ; rewrite <- Hi in HΔ; eauto.
Qed.
