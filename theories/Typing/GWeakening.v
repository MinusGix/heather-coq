(** * Global weakening of every judgment

    [γ : Ψ' ≤ Ψ] (OPE data, [gwk_wf]) sends every judgment under [Ψ] to one
    under [Ψ'], at every layer.  The only binder of the global dimension so
    far is [letbox]'s body, typed under [Ψ, U] / [Ψ, u] with the local
    context globally shifted: it is handled by [gwk_up]. *)
From DeLaM.Typing Require Export Declarative.

Coercion gwk_fn : gweak >-> Funclass.

(** ** Syntax under global renaming *)

Lemma gren_ren_ty' (A : ty) r ξ : (A⟨r⟩)⟪ξ⟫ = (A⟪ξ⟫)⟨r⟩.
Proof. apply gren_ren_ty. Qed.

Lemma gcren_gcren (Γ : ctx) ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> Γ⟪ξ⟫⟪ζ⟫ = Γ⟪θ⟫.
Proof. apply (proj1 (proj2 (proj2 gren_gren_all))). Qed.
Lemma gren_gren_ty (T : ty) ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> T⟪ξ⟫⟪ζ⟫ = T⟪θ⟫.
Proof. apply (proj1 gren_gren_all). Qed.
Lemma gren_gren_tm' (t : tm) ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> t⟪ξ⟫⟪ζ⟫ = t⟪θ⟫.
Proof. apply (proj1 (proj2 gren_gren_all)). Qed.

Lemma in_ctx_gren Γ n T l ξ : in_ctx Γ n T l -> in_ctx Γ⟪ξ⟫ n T⟪ξ⟫ l.
Proof.
  induction 1; cbn [gren GRen_ctx gcren]; change (gren_ty ?A ?ξ) with A⟪ξ⟫;
    rewrite gren_ren_ty'; now constructor.
Qed.

Lemma in_ctx_gren_inv Γ n T l ξ : in_ctx Γ⟪ξ⟫ n T l -> exists T0, in_ctx Γ n T0 l /\ T = T0⟪ξ⟫.
Proof.
  revert n T; induction Γ as [| g | Γ IH A k]; intros n T H; inversion H; subst.
  - exists A⟨↑⟩; split; [constructor | symmetry; apply gren_ren_ty'].
  - match goal with Hm : in_ctx _ _ _ _ |- _ => destruct (IH _ _ Hm) as (T0 & HT0 & ->) end.
    exists T0⟨↑⟩; split; [now constructor | symmetry; apply gren_ren_ty'].
Qed.

Lemma clen_gren Γ ξ : clen Γ⟪ξ⟫ = clen Γ.
Proof. induction Γ; cbn; auto. Qed.
Lemma ctx_tail_gren Γ ξ : ctx_tail Γ⟪ξ⟫ = (ctx_tail Γ)⟪ξ⟫.
Proof. induction Γ; cbn; auto. Qed.

Lemma lsub_tail_gren d Δ Γ ξ : lsub_tail d Δ Γ -> lsub_tail d⟪ξ⟫ Δ⟪ξ⟫ Γ⟪ξ⟫.
Proof.
  intros [Ht Hl]; split.
  - rewrite !ctx_tail_gren; now f_equal.
  - intros n; rewrite !clen_gren. cbn [gren GRen_lsub]. rewrite llk_glren, Hl; reflexivity.
Qed.

Lemma nfl_gren d ξ : dnfl d -> dnfl d⟪ξ⟫.
Proof. intros; apply gren_dnf_all. Qed.

Lemma gren_lsingle a ξ : (lsingle a)⟪ξ⟫ = lsingle a⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_lsingle2 t q ξ : (lsingle2 t q)⟪ξ⟫ = lsingle2 t⟪ξ⟫ q⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_lsucc ξ : lsucc⟪ξ⟫ = lsucc.
Proof. reflexivity. Qed.

Lemma gren_single_ty (M : ty) a ξ : M[lsingle a]⟪ξ⟫ = M⟪ξ⟫[lsingle a⟪ξ⟫].
Proof. rewrite gren_subst_ty; reflexivity. Qed.
Lemma gren_single (b a : tm) ξ : b[lsingle a]⟪ξ⟫ = b⟪ξ⟫[lsingle a⟪ξ⟫].
Proof. rewrite gren_subst; reflexivity. Qed.
Lemma gren_single2 (z t q : tm) ξ : z[lsingle2 t q]⟪ξ⟫ = z⟪ξ⟫[lsingle2 t⟪ξ⟫ q⟪ξ⟫].
Proof. rewrite gren_subst; reflexivity. Qed.
Lemma gren_lsucc_ty (M : ty) ξ : M[lsucc]⟪ξ⟫ = M⟪ξ⟫[lsucc].
Proof. rewrite gren_subst_ty; reflexivity. Qed.

(** The letbox body's type [M⟪↑⟫[box U^id/x]] under [⇑ξ]. *)
Lemma gren_letbox_ty (M : ty) b ξ : b⟪gupr ξ⟫ = b ->
  M⟪S⟫[lsingle b]⟪gupr ξ⟫ = M⟪ξ⟫⟪S⟫[lsingle b].
Proof.
  intros Hb. rewrite gren_single_ty, Hb. f_equal.
  rewrite !(gren_gren_ty _ _ _ (fun i => S (ξ i))); auto.
Qed.
Lemma gcren_shift_up (Γ : ctx) ξ : Γ⟪S⟫⟪gupr ξ⟫ = Γ⟪ξ⟫⟪S⟫.
Proof. rewrite !(gcren_gcren _ _ _ (fun i => S (ξ i))); auto. Qed.

(** Letbox β under global renaming: [t'⦃o/U⦄⟪ξ⟫ = t'⟪⇑ξ⟫⦃o⟪ξ⟫/U⦄]. *)
Lemma gren_gsingle (t : tm) o ξ : t⦃gsingle o⦄⟪ξ⟫ = t⟪gupr ξ⟫⦃gsingle (goren o ξ)⦄.
Proof.
  cbn [gsubst gren GSubst_tm GRen_tm].
  rewrite (proj1 (proj2 gren_gsubst_all) _ _ _ (fun i => goren (gsingle o i) ξ)) by auto.
  symmetry; apply (proj1 (proj2 gsubst_gren_all)). intros [|i]; reflexivity.
Qed.

(** ** Global lookups under a global weakening *)

Lemma gdecl_ren_comp D ξ ζ θ : (forall i, θ i = ζ (ξ i)) ->
  gdecl_ren (gdecl_ren D ξ) ζ = gdecl_ren D θ.
Proof.
  intros H; destruct D; cbn; f_equal; eauto using gcren_gcren, gren_gren_ty.
Qed.

Lemma in_gctx_gwk γ Ψ' Ψ n D : gwk_wf γ Ψ' Ψ -> in_gctx Ψ n D ->
  in_gctx Ψ' (γ n) (gdecl_ren D γ).
Proof.
  intros Hγ; revert n D; induction Hγ as [Ψ|γ Ψ' Ψ D' Hγ IH|γ Ψ' Ψ D' Hγ IH]; intros n D Hin.
  - cbn. inversion Hin as [Ψ0 D0|Ψ0 D0 D1 m Hm]; subst;
      rewrite (gdecl_ren_comp _ _ _ S) by reflexivity; now constructor.
  - cbn. rewrite <- (gdecl_ren_comp D γ S) by reflexivity. constructor; auto.
  - inversion Hin as [Ψ0 D0|Ψ0 D0 D1 m Hm]; subst; cbn.
    + rewrite !(gdecl_ren_comp _ _ _ (fun i => S (γ i))) by reflexivity.
      rewrite <- (gdecl_ren_comp D' γ S (fun i => S (γ i))) by reflexivity. constructor.
    + rewrite (gdecl_ren_comp _ _ _ (fun i => S (γ i))) by reflexivity.
      rewrite <- (gdecl_ren_comp D0 γ S (fun i => S (γ i))) by reflexivity. constructor; auto.
Qed.

Lemma gctx_var_gwk γ Ψ' Ψ L g : gwk_wf γ Ψ' Ψ -> gctx_var (mkG L Ψ) g -> gctx_var (mkG L Ψ') (γ g).
Proof.
  unfold gctx_var; cbn. intros Hγ; revert g; induction Hγ; intros g Hg; cbn; auto.
  destruct g; cbn in *; auto. inversion Hg; subst; reflexivity.
Qed.

(** ** Constructor equations for global renaming, in notation form *)

Section PushG.
Variable (ξ : nat -> nat).
Lemma gren_tyNat : tyNat⟪ξ⟫ = tyNat. Proof. reflexivity. Qed.
Lemma gren_tyPi l l' A B : (tyPi l l' A B)⟪ξ⟫ = tyPi l l' A⟪ξ⟫ B⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tyU l : (tyU l)⟪ξ⟫ = tyU l. Proof. reflexivity. Qed.
Lemma gren_tyEl l t : (tyEl l t)⟪ξ⟫ = tyEl l t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tyGvar U d : (tyGvar U d)⟪ξ⟫ = tyGvar (ξ U) d⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tyCTyp Δ l : (tyCTyp Δ l)⟪ξ⟫ = tyCTyp Δ⟪ξ⟫ l. Proof. reflexivity. Qed.
Lemma gren_tyCTrm Δ T l : (tyCTrm Δ T l)⟪ξ⟫ = tyCTrm Δ⟪ξ⟫ T⟪ξ⟫ l. Proof. reflexivity. Qed.
Lemma gren_var n : (var n)⟪ξ⟫ = var n. Proof. reflexivity. Qed.
Lemma gren_tmNat : tmNat⟪ξ⟫ = tmNat. Proof. reflexivity. Qed.
Lemma gren_tmPi l l' s t : (tmPi l l' s t)⟪ξ⟫ = tmPi l l' s⟪ξ⟫ t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tmU l : (tmU l)⟪ξ⟫ = tmU l. Proof. reflexivity. Qed.
Lemma gren_zero : zero⟪ξ⟫ = zero. Proof. reflexivity. Qed.
Lemma gren_succ t : (succ t)⟪ξ⟫ = succ t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_natrec l M s z t : (natrec l M s z t)⟪ξ⟫ = natrec l M⟪ξ⟫ s⟪ξ⟫ z⟪ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_lam l l' A t : (lam l l' A t)⟪ξ⟫ = lam l l' A⟪ξ⟫ t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_app t l l' A B s : (app t l l' A B s)⟪ξ⟫ = app t⟪ξ⟫ l l' A⟪ξ⟫ B⟪ξ⟫ s⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_gvar u d : (gvar u d)⟪ξ⟫ = gvar (ξ u) d⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_boxT T : (boxT T)⟪ξ⟫ = boxT T⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_boxt t : (boxt t)⟪ξ⟫ = boxt t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_letboxT l' l Δ M t' t :
  (letboxT l' l Δ M t' t)⟪ξ⟫ = letboxT l' l Δ⟪ξ⟫ M⟪ξ⟫ t'⟪gupr ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_letboxt l' l Δ T M t' t :
  (letboxt l' l Δ T M t' t)⟪ξ⟫ = letboxt l' l Δ⟪ξ⟫ T⟪ξ⟫ M⟪ξ⟫ t'⟪gupr ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_cnil : cnil⟪ξ⟫ = cnil. Proof. reflexivity. Qed.
Lemma gren_cvar g : (cvar g)⟪ξ⟫ = cvar (ξ g). Proof. reflexivity. Qed.
Lemma gren_cext Γ A l : (Γ ,, A @ l)⟪ξ⟫ = Γ⟪ξ⟫ ,, A⟪ξ⟫ @ l. Proof. reflexivity. Qed.
Lemma gren_lshift k : (lshift k)⟪ξ⟫ = lshift k. Proof. reflexivity. Qed.
End PushG.

Ltac push_gren := repeat progress (
  rewrite ?gren_tyNat, ?gren_tyPi, ?gren_tyU, ?gren_tyEl, ?gren_tyGvar, ?gren_tyCTyp, ?gren_tyCTrm,
          ?gren_var, ?gren_tmNat, ?gren_tmPi, ?gren_tmU, ?gren_zero, ?gren_succ, ?gren_natrec,
          ?gren_lam, ?gren_app, ?gren_gvar, ?gren_boxT, ?gren_boxt, ?gren_letboxT, ?gren_letboxt,
          ?gren_cnil, ?gren_cvar, ?gren_cext, ?gren_lshift).

Ltac gren_rewrite :=
  rewrite ?gren_single_ty, ?gren_single, ?gren_single2, ?gren_lsucc_ty, ?gren_ren_ty', ?gren_ren,
          ?gren_letbox_ty, ?gcren_shift_up, ?gren_gsingle.

(** ** The theorem *)

Definition gwk_to (G : gctx) (Ψ' : list gdecl) : gctx := mkG (gL G) Ψ'.

Lemma wf_tm_regty G i Δ x T T' l :
  [ G ; Δ ⊢[ i ] x : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? ->. Qed.
Lemma eq_tm_regty G i Δ x y T T' l :
  [ G ; Δ ⊢[ i ] x ≅ y : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? ->. Qed.
Lemma wf_ty_regctx G i Δ Δ' T l : [ G ; Δ' ⊢[ i ] T @ l ] -> Δ' = Δ -> [ G ; Δ ⊢[ i ] T @ l ].
Proof. now intros ? ->. Qed.

Ltac gw_eq := push_gren; gren_rewrite; push_gren; first [reflexivity | f_equal; reflexivity].

#[export] Hint Resolve in_ctx_gren in_gctx_gwk gctx_var_gwk lsub_tail_gren nfl_gren : gwk.
#[export] Hint Constructors gwk_wf : gwk.
#[export] Hint Extern 1 (in_gctx _ _ _) =>
  match goal with
  | Hγ : gwk_wf ?γ _ _, Hin : in_gctx _ _ _ |- _ => exact (in_gctx_gwk _ _ _ _ _ Hγ Hin)
  end : gwk.
#[export] Hint Resolve wfc_nil wfc_var wfc_ext wfg_ty wfg_tm lequiv_wf_l lequiv_wf_r : gwk.
#[export] Hint Extern 5 (wf_tm _ _ _ _ _ _) => eapply wf_tm_regty; [ | gw_eq ] : gwk.
#[export] Hint Extern 5 (eq_tm _ _ _ _ _ _ _) => eapply eq_tm_regty; [ | gw_eq ] : gwk.
#[export] Hint Extern 1 (lwf _ _) => (cbn; first [exact I | assumption]) : gwk.
#[export] Hint Extern 1 (lequiv _ _ _) => (cbn; assumption) : gwk.
#[export] Hint Extern 1 (lle _ _) => assumption : gwk.
#[export] Hint Extern 1 (_ <> _) => assumption : gwk.
#[export] Hint Extern 1 (compt _) => assumption : gwk.
#[export] Hint Extern 1 (_ = _ \/ _ = _) => first [left; reflexivity | right; reflexivity] : gwk.

Ltac gw_premises := eauto 6 with gwk.

Ltac gw_step :=
  match goal with
  | |- wf_ctx _ _ _ =>
      first [ solve [eapply wfc_nil; gw_premises] | solve [eapply wfc_var; gw_premises]
            | solve [eapply wfc_ext; gw_premises] ]
  | |- eq_ctx _ _ _ _ =>
      first [ solve [eapply eqc_nil; gw_premises] | solve [eapply eqc_var; gw_premises]
            | solve [eapply eqc_ext; gw_premises] ]
  | |- wf_ty _ _ _ _ _ =>
      first [ solve [eapply wft_nat; gw_premises] | solve [eapply wft_pi; gw_premises]
            | solve [eapply wft_U; gw_premises] | solve [eapply wft_El; gw_premises]
            | solve [eapply wft_lconv; gw_premises] | solve [eapply wft_CTyp; gw_premises]
            | solve [eapply wft_CTrm; gw_premises] ]
  | |- wf_tm _ _ _ _ _ _ =>
      first [ solve [eapply wf_var; gw_premises] | solve [eapply wf_code_nat; gw_premises]
            | solve [eapply wf_code_U; gw_premises] | solve [eapply wf_code_pi; gw_premises]
            | solve [eapply wf_zero; gw_premises] | solve [eapply wf_succ; gw_premises]
            | solve [eapply wf_natrec; gw_premises] | solve [eapply wf_lam; gw_premises]
            | solve [eapply wf_app; gw_premises] | solve [eapply wf_conv; gw_premises]
            | solve [eapply wf_lconv; gw_premises] | solve [eapply wf_boxT; gw_premises]
            | solve [eapply wf_boxt; gw_premises] ]
  | |- eq_ty _ _ _ _ _ _ =>
      first [ solve [eapply eqty_refl; gw_premises] | solve [eapply eqty_sym; gw_premises]
            | solve [eapply eqty_trans; gw_premises] | solve [eapply eqty_pi; gw_premises]
            | solve [eapply eqty_U; gw_premises] | solve [eapply eqty_El; gw_premises]
            | solve [eapply eqty_El_nat; gw_premises] | solve [eapply eqty_El_U; gw_premises]
            | solve [eapply eqty_El_pi; gw_premises] | solve [eapply eqty_lconv; gw_premises]
            | solve [eapply eqty_CTyp; gw_premises] | solve [eapply eqty_CTrm; gw_premises] ]
  | |- eq_tm _ _ _ _ _ _ _ =>
      first [ solve [eapply eqtm_refl; gw_premises] | solve [eapply eqtm_sym; gw_premises]
            | solve [eapply eqtm_trans; gw_premises] | solve [eapply eqtm_code_U; gw_premises]
            | solve [eapply eqtm_code_pi; gw_premises] | solve [eapply eqtm_succ; gw_premises]
            | solve [eapply eqtm_natrec; gw_premises] | solve [eapply eqtm_lam; gw_premises]
            | solve [eapply eqtm_app; gw_premises] | solve [eapply eqtm_conv; gw_premises]
            | solve [eapply eqtm_lconv; gw_premises]
            | solve [eapply eqtm_natrec_zero; gw_premises]
            | solve [eapply eqtm_natrec_succ; gw_premises]
            | solve [eapply eqtm_beta; gw_premises] | solve [eapply eqtm_eta; gw_premises]
            | solve [eapply eqtm_boxT; gw_premises] | solve [eapply eqtm_boxt; gw_premises] ]
  end.

(** One premise: directly, or through an induction hypothesis up to a type equation. *)
Ltac gw_premise :=
  first [ solve [eauto 6 with gwk]
        | solve [eapply wf_tm_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        | solve [eapply eq_tm_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]] ].

(** The lookup-typed local substitution of [u^δ]/[U^δ]. *)
Ltac gw_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin;
  let A0 := fresh "A0" in let HA0 := fresh "HA0" in
  destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & HA0 & ->);
  cbn [gren GRen_lsub]; rewrite !llk_glren; change (gren_tm ?x ?y) with x⟪y⟫;
  rewrite <- gren_subst_ty;
  match goal with IH : forall n A k (_ : in_ctx _ n A k), _ |- _ => eapply (IH n A0 k HA0) end;
  eauto with gwk.

(** The letbox body, typed under [Ψ, U] with the local context shifted. *)
Ltac gw_body :=
  match goal with
  | IH : forall Ψ'' (γ' : gweak), gwk_wf γ' Ψ'' (gΨ (gext ?G ?D)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G) |- _ =>
      let X := fresh "X" in let Hw := fresh "Hw" in
      assert (Hw : [ ⊢ gwk_to (gext G D) (gdecl_ren D γ :: Ψ') ])
        by (unfold gwk_to; cbn [gdecl_ren gΨ gL gext]; eauto 7 with gwk);
      pose proof (IH _ (gwk_up γ) (gwkwf_up _ _ _ D Hγ) Hw) as X;
      cbn [gwk_fn] in X; rewrite gcren_shift_up in X;
      rewrite ?gren_letbox_ty in X by reflexivity; exact X
  end.

Ltac gw_Δ tac :=
  match goal with
  | Hin : in_gctx _ _ (gdTy ?Δ _ _), Hγ : gwk_wf ?γ _ _ |- _ => tac (Δ⟪gwk_fn γ⟫)
  | Hin : in_gctx _ _ (gdTm ?Δ _ _ _), Hγ : gwk_wf ?γ _ _ |- _ => tac (Δ⟪gwk_fn γ⟫)
  end.

Ltac gw_manual :=
  match goal with
  | |- wf_ty _ _ _ (tyGvar _ _) _ =>
      gw_Δ ltac:(fun D => eapply wft_gvar with (Δ := D)); [ .. | gw_entries]; eauto with gwk
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      gw_Δ ltac:(fun D => eapply eqty_gvar with (Δ := D));
      [ .. | gw_entries | gw_entries | gw_entries]; eauto with gwk
  | |- wf_tm _ _ _ (gvar _ _) _ _ =>
      rewrite gren_subst_ty;
      gw_Δ ltac:(fun D => eapply wf_gvar with (Δ := D)); [ .. | gw_entries]; eauto with gwk
  | |- eq_tm _ _ _ (gvar _ _) _ _ _ =>
      rewrite gren_subst_ty;
      gw_Δ ltac:(fun D => eapply eqtm_gvar with (Δ := D));
      [ .. | gw_entries | gw_entries | gw_entries]; eauto with gwk
  | |- wf_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ =>
      eapply wf_letboxT; try gw_body; gw_premise
  | |- wf_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ =>
      eapply wf_letboxt; try gw_body; gw_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ (boxT _)) _ _ _ =>
      cbn [goren]; eapply eqtm_letboxT_beta; try gw_body; gw_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      cbn [goren]; eapply eqtm_letboxt_beta; try gw_body; gw_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_letboxT; try gw_body; gw_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_letboxt; try gw_body; gw_premise
  | |- wf_tm _ _ _ (natrec _ _ _ _ _) _ _ => eapply wf_natrec; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ zero) _ _ _ => eapply eqtm_natrec_zero; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ (succ _)) _ _ _ => eapply eqtm_natrec_succ; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ _) (natrec _ _ _ _ _) _ _ => eapply eqtm_natrec; gw_premise
  | |- eq_tm _ _ _ (lam _ _ _ _) _ _ _ => eapply eqtm_eta; gw_premise
  end.

Theorem gweakening :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> forall Ψ' (γ : gweak), gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ gwk_to G Ψ' ] -> [ gwk_to G Ψ' ; Γ⟪γ⟫ ⊢[ i ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> forall Ψ' (γ : gweak), gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ gwk_to G Ψ' ] -> [ gwk_to G Ψ' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> forall Ψ' (γ : gweak), gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ gwk_to G Ψ' ] -> [ gwk_to G Ψ' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ : T⟪γ⟫ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> forall Ψ' (γ : gweak), gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ gwk_to G Ψ' ] -> [ gwk_to G Ψ' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ ≅ T'⟪γ⟫ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> forall Ψ' (γ : gweak), gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ gwk_to G Ψ' ] -> [ gwk_to G Ψ' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ ≅ t'⟪γ⟫ : T⟪γ⟫ @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> forall Ψ' (γ : gweak), gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ gwk_to G Ψ' ] -> [ gwk_to G Ψ' ⊢[ i ] Γ⟪γ⟫ ≅ Γ'⟪γ⟫ ]).
Proof.
  apply typing_mut; intros; try exact I; unfold gwk_to in *; push_gren; gren_rewrite; push_gren.
  all: try gw_step.
  all: gw_manual.
Qed.
