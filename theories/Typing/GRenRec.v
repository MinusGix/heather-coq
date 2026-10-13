(** * The recursors and reduction under global renaming

    The syntactic laws [GWeakening] uses that need the recursor
    specification but no typing: the recursors' data, scopes and global
    lookups under global renaming, the [push_gren] tactic, and reduction.
    Split off [GWeakening] so that they build beside the typing
    metatheory ([RecWf]) instead of after it. *)
From DeLaM.Typing Require Export GRenSyntax RecSpec.

(** ** The recursor specification under global renaming *)

Definition guprn (n : nat) (ξ : nat -> nat) : nat -> nat := Nat.iter n gupr ξ.
Lemma guprn_ush n ξ i : guprn n ξ (n + i) = n + ξ i.
Proof. induction n; cbn; auto. Qed.
Lemma guprn_S' n ξ i : guprn (S n) ξ i = guprn n (gupr ξ) i.
Proof. unfold guprn; now rewrite Nat.iter_succ_r. Qed.

Lemma wrapU_gren n b ξ : (wrapU n b)⟪ξ⟫ = wrapU n b⟪ξ⟫.
Proof. induction n; cbn; congruence. Qed.
Lemma wrapG_gren n b ξ : (wrapG n b)⟪ξ⟫ = wrapG n b⟪guprn n ξ⟫.
Proof.
  revert ξ; induction n; intros ξ; cbn [wrapG gren GRen_tm gren_tm]; auto.
  change (gren_tm (wrapG n b) (gupr ξ)) with (wrapG n b)⟪gupr ξ⟫. rewrite IHn. f_equal. f_equal.
  apply gren_ext_all; intros i; symmetry; apply guprn_S'.
Qed.
Lemma wrapL_gren n b ξ : (wrapL n b)⟪ξ⟫ = wrapL n b⟪ξ⟫.
Proof. induction n; cbn; congruence. Qed.
Lemma wrap_gren nu ng nl b ξ : (wrap nu ng nl b)⟪ξ⟫ = wrap nu ng nl b⟪guprn ng ξ⟫.
Proof. unfold wrap. now rewrite wrapU_gren, wrapG_gren, wrapL_gren. Qed.

Lemma mkrb_gren MT Mt bs ξ :
  (mkrb MT Mt bs)⟪ξ⟫ = mkrb MT⟪gupr ξ⟫ Mt⟪gupr (gupr ξ)⟫ (fun k => (bs k)⟪guprn (br_ng k) ξ⟫).
Proof. unfold mkrb. cbn [tup_from gren GRen_tm gren_tm br_ar]. rewrite !wrap_gren. reflexivity. Qed.
Lemma wrapMT_gren MT ξ : (wrapMT MT)⟪ξ⟫ = wrapMT MT⟪gupr ξ⟫.
Proof. reflexivity. Qed.
Lemma wrapMt_gren Mt ξ : (wrapMt Mt)⟪ξ⟫ = wrapMt Mt⟪gupr (gupr ξ)⟫.
Proof. reflexivity. Qed.

Lemma getTy_gren t ξ : (getTy t)⟪ξ⟫ = getTy t⟪ξ⟫.
Proof. destruct t; reflexivity. Qed.
Lemma motT_gren w lv g c ξ : (motT w lv g c)⟪ξ⟫ = motT w⟪ξ⟫ lv g⟪ξ⟫ c⟪ξ⟫.
Proof.
  unfold motT. rewrite getTy_gren, <- peelL_gren, <- peelG_gren, <- peelU_gren. reflexivity.
Qed.
Lemma mott_gren w lv g U c ξ : (mott w lv g U c)⟪ξ⟫ = mott w⟪ξ⟫ lv g⟪ξ⟫ U⟪ξ⟫ c⟪ξ⟫.
Proof.
  unfold mott. rewrite getTy_gren, <- peelL_gren, <- !peelG_gren, <- peelU_gren. reflexivity.
Qed.

Lemma wkb_gren nu ng nl w ξ : (wkb nu ng nl w)⟪guprn ng ξ⟫ = wkb nu ng nl w⟪ξ⟫.
Proof.
  unfold wkb. cbn [gren GRen_tm]. rewrite (proj1 (proj2 gren_ren_all)). f_equal.
  rewrite (proj1 (proj2 gren_gren_all) _ _ _ (fun i => ng + ξ i)) by (intros; symmetry; apply guprn_ush).
  rewrite (proj1 (proj2 uren_gren_all)).
  symmetry; apply (proj1 (proj2 gren_gren_all)); reflexivity.
Qed.

Lemma wkc_gren nu ng Γ ξ : (wkc nu ng Γ)⟪guprn ng ξ⟫ = wkc nu ng Γ⟪ξ⟫.
Proof.
  unfold wkc. cbn [gren GRen_ctx].
  rewrite (proj1 (proj2 (proj2 gren_gren_all)) _ _ _ (fun i => ng + ξ i))
    by (intros; symmetry; apply guprn_ush).
  rewrite (proj1 (proj2 (proj2 uren_gren_all))).
  symmetry; apply (proj1 (proj2 (proj2 gren_gren_all))); reflexivity.
Qed.

Lemma cexts_gren Γ As ξ :
  (cexts Γ As)⟪ξ⟫ = cexts Γ⟪ξ⟫ (map (fun '(A, l) => (A⟪ξ⟫, l)) As).
Proof. revert Γ; induction As as [|[A l] As IH]; intros Γ; cbn; auto. Qed.

Lemma brLocs_gren k wT wt a1 a2 ξ : k < nbr ->
  map (fun '(A, l) => (A⟪guprn (br_ng k) ξ⟫, l)) (brLocs k wT wt a1 a2) =
  brLocs k wT⟪ξ⟫ wt⟪ξ⟫ a1 a2.
Proof.
  intros Hk. br_all ltac:(destruct k;
    [cbn [brLocs map br_ng br_ar mkLocs call_ty call_lv br_calls br_nu]; rewrite ?motT_gren, ?mott_gren, ?wkb_gren; reflexivity|]).
  lia.
Qed.
Lemma brΓ_gren k Γ wT wt l1 l2 ξ : k < nbr ->
  (brΓ k Γ wT wt l1 l2)⟪guprn (br_ng k) ξ⟫ = brΓ k Γ⟪ξ⟫ wT⟪ξ⟫ wt⟪ξ⟫ l1 l2.
Proof. intros Hk. unfold brΓ. now rewrite cexts_gren, wkc_gren, brLocs_gren. Qed.
Lemma brRes_gren k wT wt ξ : k < nbr ->
  (brRes k wT wt)⟪guprn (br_ng k) ξ⟫ = brRes k wT⟪ξ⟫ wt⟪ξ⟫.
Proof.
  intros Hk. br_all ltac:(destruct k;
    [cbn [brRes br_ng br_ar call_ty br_head br_nu br_nl]; rewrite ?motT_gren, ?mott_gren, ?wkb_gren; reflexivity|]).
  lia.
Qed.
Lemma recΓT_gren Γ ξ : (recΓT Γ)⟪gupr ξ⟫ = recΓT Γ⟪ξ⟫.
Proof. unfold recΓT. cbn [gren GRen_ctx gcren]. now rewrite (wkc_gren 1 1). Qed.
Lemma recΓt_gren Γ ξ : (recΓt Γ)⟪gupr (gupr ξ)⟫ = recΓt Γ⟪ξ⟫.
Proof.
  unfold recΓt. cbn [gren GRen_ctx gcren]. change (gupr (gupr ξ)) with (guprn 2 ξ).
  now rewrite (wkc_gren 1 2).
Qed.

(** ** Global lookups under a global weakening *)

Lemma gdecl_ren_comp D ξ ζ θ : (forall i, θ i = ζ (ξ i)) ->
  gdecl_ren (gdecl_ren D ξ) ζ = gdecl_ren D θ.
Proof.
  intros H; destruct D; cbn; f_equal; eauto using gcren_gcren, gren_gren_ty, gren_gren_tm'.
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

(** ** The recursors' scopes under a global weakening *)

Lemma gdecl_ren_uren D ξ ρ : gdecl_uren (gdecl_ren D ξ) ρ = gdecl_ren (gdecl_uren D ρ) ξ.
Proof.
  destruct D; cbn; f_equal; try reflexivity;
    first [apply (proj1 (proj2 (proj2 uren_gren_all))) | apply (proj1 uren_gren_all) | apply (proj1 (proj2 uren_gren_all))].
Qed.

Lemma gwk_wf_uren γ Ψ' Ψ ρ : gwk_wf γ Ψ' Ψ ->
  gwk_wf γ (map (fun D => gdecl_uren D ρ) Ψ') (map (fun D => gdecl_uren D ρ) Ψ).
Proof. induction 1; cbn; rewrite ?gdecl_ren_uren; now constructor. Qed.

Lemma gwkwf_up' γ Ψ' Ψ D D' : gwk_wf γ Ψ' Ψ -> D' = gdecl_ren D (gwk_fn γ) ->
  gwk_wf (gwk_up γ) (D' :: Ψ') (D :: Ψ).
Proof. intros H ->; now constructor. Qed.

Definition gwk_upn (n : nat) (γ : gweak) : gweak := Nat.iter n gwk_up γ.
Lemma gwk_upn_fn n γ i : gwk_fn (gwk_upn n γ) i = guprn n (gwk_fn γ) i.
Proof. revert i; induction n; intros [|i]; cbn; auto. Qed.

Lemma brG_gwk k γ G' G : k < nbr -> gwk_ok γ G' G ->
  gwk_wf (gwk_upn (br_ng k) γ) (gΨ (brG k G')) (gΨ (brG k G)).
Proof.
  intros Hk [_ Hw]. apply (gwk_wf_uren _ _ _ (ush (br_nu k))) in Hw. unfold brG; cbn [gΨ gctx_uwk].
  br_all ltac:(destruct k; [cbn [brDecls List.app br_ng br_nu br_ar gwk_upn Nat.iter];
                      repeat (apply gwkwf_up'; [|reflexivity]); exact Hw|]).
  lia.
Qed.
Lemma recGT_gwk γ G' G : gwk_ok γ G' G -> gwk_wf (gwk_up γ) (gΨ (recGT G')) (gΨ (recGT G)).
Proof.
  intros [_ Hw]. apply (gwk_wf_uren _ _ _ (ush 1)) in Hw. unfold recGT; cbn [gΨ gctx_uwk].
  now apply gwkwf_up'.
Qed.
Lemma recGt_gwk γ G' G : gwk_ok γ G' G ->
  gwk_wf (gwk_up (gwk_up γ)) (gΨ (recGt G')) (gΨ (recGt G)).
Proof.
  intros [_ Hw]. apply (gwk_wf_uren _ _ _ (ush 1)) in Hw. unfold recGt; cbn [gΨ gctx_uwk].
  apply gwkwf_up'; [apply gwkwf_up'; [exact Hw | reflexivity] | reflexivity].
Qed.

Lemma gren_gwk_upn_tm (t : tm) n γ : t⟪gwk_fn (gwk_upn n γ)⟫ = t⟪guprn n (gwk_fn γ)⟫.
Proof. apply gren_ext_all, gwk_upn_fn. Qed.
Lemma gren_gwk_upn_ty (T : ty) n γ : T⟪gwk_fn (gwk_upn n γ)⟫ = T⟪guprn n (gwk_fn γ)⟫.
Proof. apply gren_ext_all, gwk_upn_fn. Qed.
Lemma gren_gwk_upn_ctx (Γ : ctx) n γ : Γ⟪gwk_fn (gwk_upn n γ)⟫ = Γ⟪guprn n (gwk_fn γ)⟫.
Proof. apply gren_ext_all, gwk_upn_fn. Qed.

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
Lemma gren_gdef u b d : (gdef u b d)⟪ξ⟫ = gdef (ξ u) b⟪ξ⟫ d⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tyId l A a b : (tyId l A a b)⟪ξ⟫ = tyId l A⟪ξ⟫ a⟪ξ⟫ b⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_refl l A a : (tmRefl l A a)⟪ξ⟫ = tmRefl l A⟪ξ⟫ a⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tmId l s t u : (tmId l s t u)⟪ξ⟫ = tmId l s⟪ξ⟫ t⟪ξ⟫ u⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tmSEq l s t u : (tmSEq l s t u)⟪ξ⟫ = tmSEq l s⟪ξ⟫ t⟪ξ⟫ u⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_J l l' A a M c u e :
  (tmJ l l' A a M c u e)⟪ξ⟫ = tmJ l l' A⟪ξ⟫ a⟪ξ⟫ M⟪ξ⟫ c⟪ξ⟫ u⟪ξ⟫ e⟪ξ⟫.
Proof. reflexivity. Qed.
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
Lemma gren_elimT l1 l2 rb l Δ t : (elimT l1 l2 rb l Δ t)⟪ξ⟫ = elimT l1 l2 rb⟪ξ⟫ l Δ⟪ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_elimt l1 l2 rb l Δ T t :
  (elimt l1 l2 rb l Δ T t)⟪ξ⟫ = elimt l1 l2 rb⟪ξ⟫ l Δ⟪ξ⟫ T⟪ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_tyUPi n l T : (tyUPi n l T)⟪ξ⟫ = tyUPi n l T⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_ulam n l T t : (ulam n l T t)⟪ξ⟫ = ulam n l T⟪ξ⟫ t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_uapp t ls : (uapp t ls)⟪ξ⟫ = uapp t⟪ξ⟫ ls. Proof. reflexivity. Qed.
Lemma gren_tyCPi l T : (tyCPi l T)⟪ξ⟫ = tyCPi l T⟪gupr ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tyTPi Δ l l' T : (tyTPi Δ l l' T)⟪ξ⟫ = tyTPi Δ⟪ξ⟫ l l' T⟪gupr ξ⟫. Proof. reflexivity. Qed.
Lemma gren_clam l T t : (clam l T t)⟪ξ⟫ = clam l T⟪gupr ξ⟫ t⟪gupr ξ⟫. Proof. reflexivity. Qed.
Lemma gren_capp t Δ : (capp t Δ)⟪ξ⟫ = capp t⟪ξ⟫ Δ⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tlam Δ l l' T t : (tlam Δ l l' T t)⟪ξ⟫ = tlam Δ⟪ξ⟫ l l' T⟪gupr ξ⟫ t⟪gupr ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tapp t T : (tapp t T)⟪ξ⟫ = tapp t⟪ξ⟫ T⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tySig l l' A B : (tySig l l' A B)⟪ξ⟫ = tySig l l' A⟪ξ⟫ B⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tySum l l' A B : (tySum l l' A B)⟪ξ⟫ = tySum l l' A⟪ξ⟫ B⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_inl l l' A B a : (tmInl l l' A B a)⟪ξ⟫ = tmInl l l' A⟪ξ⟫ B⟪ξ⟫ a⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_inr l l' A B a : (tmInr l l' A B a)⟪ξ⟫ = tmInr l l' A⟪ξ⟫ B⟪ξ⟫ a⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_case l l' l'' A B M c1 c2 t :
  (tmCase l l' l'' A B M c1 c2 t)⟪ξ⟫ = tmCase l l' l'' A⟪ξ⟫ B⟪ξ⟫ M⟪ξ⟫ c1⟪ξ⟫ c2⟪ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_tmSig l l' s t : (tmSig l l' s t)⟪ξ⟫ = tmSig l l' s⟪ξ⟫ t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_pair l l' A B a b : (tmPair l l' A B a b)⟪ξ⟫ = tmPair l l' A⟪ξ⟫ B⟪ξ⟫ a⟪ξ⟫ b⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_fst l l' A B p : (tmFst l l' A B p)⟪ξ⟫ = tmFst l l' A⟪ξ⟫ B⟪ξ⟫ p⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_snd l l' A B p : (tmSnd l l' A B p)⟪ξ⟫ = tmSnd l l' A⟪ξ⟫ B⟪ξ⟫ p⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tyUnit l : (tyUnit l)⟪ξ⟫ = tyUnit l. Proof. reflexivity. Qed.
Lemma gren_tmUnit l : (tmUnit l)⟪ξ⟫ = tmUnit l. Proof. reflexivity. Qed.
Lemma gren_tmSEmpty l : (tmSEmpty l)⟪ξ⟫ = tmSEmpty l. Proof. reflexivity. Qed.
Lemma gren_tmEmpty l : (tmEmpty l)⟪ξ⟫ = tmEmpty l. Proof. reflexivity. Qed.
Lemma gren_tmSum l l' s t : (tmSum l l' s t)⟪ξ⟫ = tmSum l l' s⟪ξ⟫ t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tmW l l' s t : (tmW l l' s t)⟪ξ⟫ = tmW l l' s⟪ξ⟫ t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tmVec l s n : (tmVec l s n)⟪ξ⟫ = tmVec l s⟪ξ⟫ n⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tmWf l s n : (tmWf l s n)⟪ξ⟫ = tmWf l s⟪ξ⟫ n⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tmFin n : (tmFin n)⟪ξ⟫ = tmFin n⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_triv l : (tmTriv l)⟪ξ⟫ = tmTriv l. Proof. reflexivity. Qed.
Lemma gren_tyW l l' A B : (tyW l l' A B)⟪ξ⟫ = tyW l l' A⟪ξ⟫ B⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tyVec l A n : (tyVec l A n)⟪ξ⟫ = tyVec l A⟪ξ⟫ n⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tyFin n : (tyFin n)⟪ξ⟫ = tyFin n⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_sup l l' A B a f : (tmSup l l' A B a f)⟪ξ⟫ = tmSup l l' A⟪ξ⟫ B⟪ξ⟫ a⟪ξ⟫ f⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_elimW l l' l'' A B M c t :
  (tmElimW l l' l'' A B M c t)⟪ξ⟫ = tmElimW l l' l'' A⟪ξ⟫ B⟪ξ⟫ M⟪ξ⟫ c⟪ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
(** [elim_W]'s induction hypothesis (M13a). *)
Lemma gren_wIH l l' l'' A B M c a f :
  (wIH l l' l'' A B M c a f)⟪ξ⟫ = wIH l l' l'' A⟪ξ⟫ B⟪ξ⟫ M⟪ξ⟫ c⟪ξ⟫ a⟪ξ⟫ f⟪ξ⟫.
Proof.
  unfold wIH. rewrite gren_lam, gren_elimW, gren_app, gren_var.
  repeat rewrite ?gren_ren_ty', ?gren_ren, ?gren_single_ty, ?gren_tyW. reflexivity.
Qed.
(** Wf trees (M15a), [nth] and [elim_Wf]'s induction hypothesis. *)
Lemma gren_tyWf l A N : (tyWf l A N)⟪ξ⟫ = tyWf l A⟪ξ⟫ N⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_supf l A N a cs : (tmSupf l A N a cs)⟪ξ⟫ = tmSupf l A⟪ξ⟫ N⟪ξ⟫ a⟪ξ⟫ cs⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_elimWf l l' A N M c t :
  (tmElimWf l l' A N M c t)⟪ξ⟫ = tmElimWf l l' A⟪ξ⟫ N⟪ξ⟫ M⟪ξ⟫ c⟪ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
(** Propositional truncation (M16a). *)
Lemma gren_tySq l A : (tySq l A)⟪ξ⟫ = tySq l A⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_sq l A a : (tmSq l A a)⟪ξ⟫ = tmSq l A⟪ξ⟫ a⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_elimSq l l' A M c t :
  (tmElimSq l l' A M c t)⟪ξ⟫ = tmElimSq l l' A⟪ξ⟫ M⟪ξ⟫ c⟪ξ⟫ t⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_tmSqCode l s : (tmSqCode l s)⟪ξ⟫ = tmSqCode l s⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_tmNth l T k cs i : (tmNth l T k cs i)⟪ξ⟫ = tmNth l T⟪ξ⟫ k⟪ξ⟫ cs⟪ξ⟫ i⟪ξ⟫.
Proof.
  unfold tmNth, nthMot, nthBase, nthStep. cbn [gren GRen_tm gren_tm GRen_ty gren_ty].
  change (gren_tm ?x ?ξ) with x⟪ξ⟫; change (gren_ty ?x ?ξ) with x⟪ξ⟫.
  repeat rewrite ?gren_ren_ty', ?gren_ren. reflexivity.
Qed.
Lemma gren_wfIH l l' A N M c a cs :
  (wfIH l l' A N M c a cs)⟪ξ⟫ = wfIH l l' A⟪ξ⟫ N⟪ξ⟫ M⟪ξ⟫ c⟪ξ⟫ a⟪ξ⟫ cs⟪ξ⟫.
Proof.
  unfold wfIH. rewrite gren_lam, gren_elimWf, gren_tmNth, gren_var, gren_tyFin.
  repeat rewrite ?gren_ren_ty', ?gren_ren, ?gren_single, ?gren_tyWf. reflexivity.
Qed.
(** [UΠ]'s scope and instances. *)
Lemma gren_uren_ctx (Γ : ctx) ρ : Γ⟨ρ⟩ᵤ⟪ξ⟫ = Γ⟪ξ⟫⟨ρ⟩ᵤ.
Proof. symmetry; apply (proj1 (proj2 (proj2 uren_gren_all))). Qed.
Lemma gren_uren_tm (t : tm) ρ : t⟨ρ⟩ᵤ⟪ξ⟫ = t⟪ξ⟫⟨ρ⟩ᵤ.
Proof. symmetry; apply (proj1 (proj2 uren_gren_all)). Qed.
Lemma gren_usubst_ty (T : ty) φ : T[φ]ᵤ⟪ξ⟫ = T⟪ξ⟫[φ]ᵤ.
Proof. symmetry; apply usubst_gren_ty. Qed.
Lemma gren_usubst_tm (t : tm) φ : t[φ]ᵤ⟪ξ⟫ = t⟪ξ⟫[φ]ᵤ.
Proof. symmetry; apply usubst_gren. Qed.
End PushG.

(** Generated by [tools/gen_push.py] (M1_DESIGN.md, build-time gotchas):
    each push found syntactically and done with its head's lemma. *)
Ltac push_gren_at h k := lazymatch h with
  | @tyNat => k gren_tyNat
  | @tyPi => k gren_tyPi
  | @tyU => k gren_tyU
  | @tyEl => k gren_tyEl
  | @tyGvar => k gren_tyGvar
  | @tyCTyp => k gren_tyCTyp
  | @tyCTrm => k gren_tyCTrm
  | @var => k gren_var
  | @tmNat => k gren_tmNat
  | @tmPi => k gren_tmPi
  | @tmU => k gren_tmU
  | @zero => k gren_zero
  | @succ => k gren_succ
  | @natrec => k gren_natrec
  | @lam => k gren_lam
  | @app => k gren_app
  | @gvar => k gren_gvar
  | @boxT => k gren_boxT
  | @boxt => k gren_boxt
  | @letboxT => k gren_letboxT
  | @letboxt => k gren_letboxt
  | @cnil => k gren_cnil
  | @cvar => k gren_cvar
  | @cext => k gren_cext
  | @lshift => k gren_lshift
  | @elimT => k gren_elimT
  | @elimt => k gren_elimt
  | @tyUPi => k gren_tyUPi
  | @ulam => k gren_ulam
  | @uapp => k gren_uapp
  | @uren => first [k gren_uren_ctx | k gren_uren_tm]
  | @usubst => first [k gren_usubst_ty | k gren_usubst_tm]
  | @tyCPi => k gren_tyCPi
  | @tyTPi => k gren_tyTPi
  | @clam => k gren_clam
  | @capp => k gren_capp
  | @tlam => k gren_tlam
  | @tapp => k gren_tapp
  | @tySig => k gren_tySig
  | @tySum => k gren_tySum
  | @tmInl => k gren_inl
  | @tmInr => k gren_inr
  | @tmCase => k gren_case
  | @tmSig => k gren_tmSig
  | @tmPair => k gren_pair
  | @tmFst => k gren_fst
  | @tmSnd => k gren_snd
  | @tyUnit => k gren_tyUnit
  | @tmUnit => k gren_tmUnit
  | @tmSEmpty => k gren_tmSEmpty
  | @tmEmpty => k gren_tmEmpty
  | @tmSum => k gren_tmSum
  | @tmW => k gren_tmW
  | @tmVec => k gren_tmVec
  | @tmWf => k gren_tmWf
  | @tmFin => k gren_tmFin
  | @tmTriv => k gren_triv
  | @gdef => k gren_gdef
  | @tyId => k gren_tyId
  | @tmRefl => k gren_refl
  | @tmId => k gren_tmId
  | @tmSEq => k gren_tmSEq
  | @tmJ => k gren_J
  | @tyW => k gren_tyW
  | @tyVec => k gren_tyVec
  | @tyFin => k gren_tyFin
  | @tmSup => k gren_sup
  | @tmElimW => k gren_elimW
  | @wIH => k gren_wIH
  | @tyWf => k gren_tyWf
  | @tmSupf => k gren_supf
  | @tmElimWf => k gren_elimWf
  | @tmNth => k gren_tmNth
  | @wfIH => k gren_wfIH
  | @tySq => k gren_tySq
  | @tmSq => k gren_sq
  | @tmElimSq => k gren_elimSq
  | @tmSqCode => k gren_tmSqCode
  end.
Ltac push_gren := repeat match goal with
  | |- context [@gren _ _ ?t _] => let h := head_of t in push_gren_at h ltac:(fun L => rewrite L)
  end.

Ltac gren_rewrite :=
  rewrite ?gren_single_ty, ?gren_single, ?gren_single2, ?gren_single3, ?gren_single2_ty, ?gren_lsucc_ty, ?gren_ren_ty', ?gren_ren,
          ?gren_letbox_ty, ?gcren_shift_up, ?gren_gsingle, ?gren_gsingle_ty, ?gren_shift_up_tm, ?mkrb_gren, ?motT_gren, ?mott_gren,
          ?wrapMT_gren, ?wrapMt_gren.

(** ** Reduction under global renaming *)

Lemma red_gren_both :
  (forall t u, red t u -> forall ξ, red t⟪ξ⟫ u⟪ξ⟫) /\
  (forall T U, red_ty T U -> forall ξ, red_ty T⟪ξ⟫ U⟪ξ⟫).
Proof.
  apply red_both; intros; cbn [gren GRen_tm gren_tm GRen_ty gren_ty];
    change (gren_tm ?x ?ξ) with x⟪ξ⟫; change (gren_ty ?x ?ξ) with x⟪ξ⟫;
    change (gcren ?x ?ξ) with x⟪ξ⟫.
  all: rewrite ?gren_single2, ?gren_single, ?gren_single3, ?gren_wIH, ?gren_wfIH, ?gren_gsingle; try now constructor.
  all: try (constructor; auto; fail).
  all: first [ constructor; now apply redT_gren | constructor; now apply redt_gren
             | rewrite <- usubst_gren; now constructor
             (* δ: the body's instance *)
             | rewrite gren_subst; now constructor
             (* [Vec]'s successor step: the tail's shifts *)
             | rewrite gren_ren_ty', gren_ren; now constructor ].
Qed.

Lemma red_gren t u ξ : red t u -> red t⟪ξ⟫ u⟪ξ⟫.
Proof. intros H; now apply red_gren_both. Qed.
Lemma red_ty_gren T U ξ : red_ty T U -> red_ty T⟪ξ⟫ U⟪ξ⟫.
Proof. intros H; now apply red_gren_both. Qed.
Lemma reds_gren t u ξ : reds t u -> reds t⟪ξ⟫ u⟪ξ⟫.
Proof. unfold reds; induction 1; [constructor|econstructor; eauto using red_gren]. Qed.
Lemma reds_ty_gren T U ξ : reds_ty T U -> reds_ty T⟪ξ⟫ U⟪ξ⟫.
Proof. unfold reds_ty; induction 1; [constructor|econstructor; eauto using red_ty_gren]. Qed.
