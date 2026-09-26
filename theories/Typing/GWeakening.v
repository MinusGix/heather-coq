(** * Global weakening of every judgment

    [γ : Ψ' ≤ Ψ] (OPE data, [gwk_wf]) sends every judgment under [Ψ] to one
    under [Ψ'], at every layer.  The only binder of the global dimension so
    far is [letbox]'s body, typed under [Ψ, U] / [Ψ, u] with the local
    context globally shifted: it is handled by [gwk_up]. *)
From DeLaM.Typing Require Export RecWf TypedDnf.

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

(** The reducts commute with global renaming. *)
Lemma tup_nth_gren t k ξ : tup_nth t⟪ξ⟫ k = (tup_nth t k)⟪ξ⟫.
Proof. revert t; induction k; intros []; cbn; auto. Qed.
Lemma peelU_gren b l ξ : peelU b⟪ξ⟫ l = (peelU b l)⟪ξ⟫.
Proof. destruct b; cbn; auto. apply usubst_gren. Qed.
Lemma peelG_gren b o ξ : peelG b⟪ξ⟫ (goren o ξ) = (peelG b o)⟪ξ⟫.
Proof. destruct b; cbn; auto. symmetry; apply gren_gsingle. Qed.
Lemma peelL_gren b a ξ : peelL b⟪ξ⟫ a⟪ξ⟫ = (peelL b a)⟪ξ⟫.
Proof. destruct b; cbn; auto. symmetry; apply gren_single. Qed.

Lemma gren_ty_subst_raw M d ξ : gren_ty (subst_ty M d) ξ = subst_ty (gren_ty M ξ) (glren d ξ).
Proof. exact (gren_subst_ty M d ξ). Qed.

Ltac gpeel_push :=
  repeat first [ rewrite <- peelL_gren | rewrite <- peelG_gren | rewrite <- peelU_gren ];
  unfold rb_br; rewrite tup_nth_gren;
  cbn [goren gren GRen_tm GRen_ty GRen_ctx gren_tm recT rect]; rewrite ?gren_ty_subst_raw;
  reflexivity.

Lemma redT_gren l1 l2 rb l Δ c v ξ : redT l1 l2 rb l Δ c = Some v ->
  redT l1 l2 rb⟪ξ⟫ l Δ⟪ξ⟫ c⟪ξ⟫ = Some v⟪ξ⟫.
Proof. destruct c; cbn [redT gren GRen_ty gren_ty]; intros E; inversion E; subst; f_equal; gpeel_push. Qed.
Lemma redt_gren l1 l2 rb l Δ T c v ξ : redt l1 l2 rb l Δ T c = Some v ->
  redt l1 l2 rb⟪ξ⟫ l Δ⟪ξ⟫ T⟪ξ⟫ c⟪ξ⟫ = Some v⟪ξ⟫.
Proof.
  destruct c; cbn [redt gren GRen_tm gren_tm]; try destruct T; cbn [gren_ty];
    intros E; inversion E; subst; f_equal; gpeel_push.
Qed.


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

Lemma brLocs_gren k wT wt a1 a2 ξ : k < 13 ->
  map (fun '(A, l) => (A⟪guprn (br_ng k) ξ⟫, l)) (brLocs k wT wt a1 a2) =
  brLocs k wT⟪ξ⟫ wt⟪ξ⟫ a1 a2.
Proof.
  intros Hk. do 13 (destruct k;
    [cbn [brLocs map br_ng br_ar]; rewrite ?motT_gren, ?mott_gren, ?wkb_gren; reflexivity|]).
  lia.
Qed.
Lemma brΓ_gren k Γ wT wt l1 l2 ξ : k < 13 ->
  (brΓ k Γ wT wt l1 l2)⟪guprn (br_ng k) ξ⟫ = brΓ k Γ⟪ξ⟫ wT⟪ξ⟫ wt⟪ξ⟫ l1 l2.
Proof. intros Hk. unfold brΓ. now rewrite cexts_gren, wkc_gren, brLocs_gren. Qed.
Lemma brRes_gren k wT wt ξ : k < 13 ->
  (brRes k wT wt)⟪guprn (br_ng k) ξ⟫ = brRes k wT⟪ξ⟫ wt⟪ξ⟫.
Proof.
  intros Hk. do 13 (destruct k;
    [cbn [brRes br_ng br_ar]; rewrite ?motT_gren, ?mott_gren, ?wkb_gren; reflexivity|]).
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

(** ** The recursors' scopes under a global weakening *)

Lemma gdecl_ren_uren D ξ ρ : gdecl_uren (gdecl_ren D ξ) ρ = gdecl_ren (gdecl_uren D ρ) ξ.
Proof.
  destruct D; cbn; f_equal; try reflexivity;
    first [apply (proj1 (proj2 (proj2 uren_gren_all))) | apply (proj1 uren_gren_all)].
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

Lemma brG_gwk k γ G' G : k < 13 -> gwk_ok γ G' G ->
  gwk_wf (gwk_upn (br_ng k) γ) (gΨ (brG k G')) (gΨ (brG k G)).
Proof.
  intros Hk [_ Hw]. apply (gwk_wf_uren _ _ _ (ush (br_nu k))) in Hw. unfold brG; cbn [gΨ gctx_uwk].
  do 13 (destruct k; [cbn [brDecls List.app br_ng br_nu br_ar gwk_upn Nat.iter];
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
Lemma gren_ulam n l t : (ulam n l t)⟪ξ⟫ = ulam n l t⟪ξ⟫. Proof. reflexivity. Qed.
Lemma gren_uapp t ls : (uapp t ls)⟪ξ⟫ = uapp t⟪ξ⟫ ls. Proof. reflexivity. Qed.
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

Ltac push_gren := repeat progress (
  rewrite ?gren_tyNat, ?gren_tyPi, ?gren_tyU, ?gren_tyEl, ?gren_tyGvar, ?gren_tyCTyp, ?gren_tyCTrm,
          ?gren_var, ?gren_tmNat, ?gren_tmPi, ?gren_tmU, ?gren_zero, ?gren_succ, ?gren_natrec,
          ?gren_lam, ?gren_app, ?gren_gvar, ?gren_boxT, ?gren_boxt, ?gren_letboxT, ?gren_letboxt,
          ?gren_cnil, ?gren_cvar, ?gren_cext, ?gren_lshift, ?gren_elimT, ?gren_elimt,
          ?gren_tyUPi, ?gren_ulam, ?gren_uapp, ?gren_uren_ctx, ?gren_uren_tm, ?gren_usubst_ty,
          ?gren_usubst_tm).

Ltac gren_rewrite :=
  rewrite ?gren_single_ty, ?gren_single, ?gren_single2, ?gren_lsucc_ty, ?gren_ren_ty', ?gren_ren,
          ?gren_letbox_ty, ?gcren_shift_up, ?gren_gsingle, ?mkrb_gren, ?motT_gren, ?mott_gren,
          ?wrapMT_gren, ?wrapMt_gren.

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
Lemma wf_ty_regty G i Δ A A' l : [ G ; Δ ⊢[ i ] A @ l ] -> A = A' -> [ G ; Δ ⊢[ i ] A' @ l ].
Proof. now intros ? ->. Qed.
Lemma eq_ty_regty G i Δ A B A' B' l :
  [ G ; Δ ⊢[ i ] A ≅ B @ l ] -> A = A' -> B = B' -> [ G ; Δ ⊢[ i ] A' ≅ B' @ l ].
Proof. now intros ? -> ->. Qed.

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
#[export] Hint Extern 2 (lwf _ _) => (cbn; eapply lwf_weaken; [| eassumption]; cbn; lia) : gwk.
#[export] Hint Extern 2 (lequiv _ _ _) => (cbn; eapply lequiv_weaken; [| eassumption]; cbn; lia) : gwk.
#[export] Hint Extern 1 (_ <= _) => (cbn; lia) : gwk.
#[export] Hint Extern 2 (Forall (lwf _) _) => (cbn; eapply lwfs_weaken; [| eassumption]; cbn; lia) : gwk.
#[export] Hint Extern 2 (Forall2 (lequiv _) _ _) => (cbn; eapply lequivs_weaken; [| eassumption]; cbn; lia) : gwk.
#[export] Hint Extern 1 (lle _ _) => assumption : gwk.
#[export] Hint Extern 1 (_ <> _) => assumption : gwk.
#[export] Hint Extern 1 (compt _) => assumption : gwk.
#[export] Hint Extern 1 (ty_leq _ _) => apply (proj1 leq_gren_all); assumption : gwk.
#[export] Hint Extern 1 (tm_leq _ _) => apply (proj1 (proj2 leq_gren_all)); assumption : gwk.
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
            | solve [eapply eqtm_beta; gw_premises] | solve [eapply eqtm_eta; gw_premises] ]
  end.

(** One premise: directly, or through an induction hypothesis up to a type equation. *)
Ltac gw_premise :=
  first [ solve [eauto 6 with gwk]
        | solve [eapply wf_tm_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        | solve [eapply eq_tm_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        (* the recursors' motive instances (M3_DESIGN.md E10) *)
        | solve [eapply wf_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        | solve [eapply eq_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq | gw_eq]] ].

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
  | IH : forall L'' Ψ'' (γ' : gweak), _ <= L'' -> gwk_wf γ' Ψ'' (gΨ (gext ?G ?D)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L' |- _ =>
      let X := fresh "X" in let Hw := fresh "Hw" in
      assert (Hw : [ ⊢ mkG L' (gdecl_ren D γ :: Ψ') ])
        by (cbn [gdecl_ren gΨ gL gext]; eauto 7 with gwk);
      pose proof (IH L' _ (gwk_up γ) HL (gwkwf_up _ _ _ D Hγ) Hw) as X;
      cbn [gwk_fn] in X; rewrite gcren_shift_up in X;
      rewrite ?gren_letbox_ty in X by reflexivity; exact X
  end.

(** The recursors' motives and branches, under [⇑γ] and [⇑ⁿγ]. *)
Ltac gw_motT :=
  match goal with
  | IH : forall L'' Ψ'' (γ' : gweak), _ <= L'' -> gwk_wf γ' Ψ'' (gΨ (recGT ?G)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L', HG : [ ⊢ mkG ?L' ?Ψ' ] |- _ =>
      let X := fresh "X" in
      pose proof (IH _ _ (gwk_up γ) (le_n_S _ _ HL) (recGT_gwk γ (mkG L' Ψ') G (conj HL Hγ)) (wf_recGT HG)) as X;
      cbn [gwk_fn] in X; rewrite recΓT_gren in X; exact X
  end.
Ltac gw_mott :=
  match goal with
  | IH : forall L'' Ψ'' (γ' : gweak), _ <= L'' -> gwk_wf γ' Ψ'' (gΨ (recGt ?G)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L', HG : [ ⊢ mkG ?L' ?Ψ' ] |- _ =>
      let X := fresh "X" in
      pose proof (IH _ _ (gwk_up (gwk_up γ)) (le_n_S _ _ HL) (recGt_gwk γ (mkG L' Ψ') G (conj HL Hγ))
                    (wf_recGt HG)) as X;
      cbn [gwk_fn] in X; rewrite recΓt_gren in X; exact X
  end.
Ltac gw_branches :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
  match goal with
  | IH : forall k, k < 13 -> forall L'' Ψ'' (γ' : gweak), _ <= L'' -> gwk_wf γ' Ψ'' (gΨ (brG k ?G)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L', HG : [ ⊢ mkG ?L' ?Ψ' ] |- _ =>
      let X := fresh "X" in
      pose proof (IH k Hk _ _ (gwk_upn (br_ng k) γ) (proj1 (Nat.add_le_mono_l _ _ (br_nu k)) HL)
                    (brG_gwk k γ (mkG L' Ψ') G Hk (conj HL Hγ)) (wf_brG HG k Hk)) as X;
      rewrite ?gren_gwk_upn_ctx, ?gren_gwk_upn_tm, ?gren_gwk_upn_ty in X;
      rewrite brΓ_gren in X by exact Hk; rewrite ?brRes_gren in X by exact Hk;
      exact X
  end.

(** [UΠ]'s body, under [n] fresh levels: the same weakening at the
    universe-weakened scope. *)
Ltac gw_upi_body :=
  match goal with
  | IH : forall L'' Ψ'' (γ' : gweak), gL (gctx_uwk ?n ?G) <= L'' -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L', HG : [ ⊢ mkG ?L' ?Ψ' ] |- _ =>
      let X := fresh "X" in
      pose proof (IH (n + L') _ γ (proj1 (Nat.add_le_mono_l _ _ n) HL) (gwk_wf_uren _ _ _ (ush n) Hγ)
                    (uwk_glob n _ HG)) as X;
      rewrite gren_uren_ctx in X; exact X
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
  | |- wf_tm _ _ _ (elimT _ _ _ _ _ _) _ _ =>
      eapply wf_elimT; [ .. | gw_motT | gw_mott | gw_branches | gw_branches | ]; gw_premise
  | |- wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ =>
      eapply wf_elimt; [ .. | gw_motT | gw_mott | gw_branches | gw_branches | | ]; gw_premise
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ (boxT _)) _ _ _ =>
      eapply eqtm_elimT_beta; [gw_premise | now apply redT_gren | gw_premise]
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      eapply eqtm_elimt_beta; [gw_premise | now apply redt_gren | gw_premise]
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimT;
      [ .. | gw_motT | gw_motT | gw_motT | gw_mott | gw_mott | gw_mott
           | gw_branches | gw_branches | gw_branches | gw_branches | ];
      gw_premise
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimt;
      [ .. | gw_motT | gw_motT | gw_motT | gw_mott | gw_mott | gw_mott
           | gw_branches | gw_branches | gw_branches | gw_branches | ];
      gw_premise
  | |- wf_ty _ _ _ (tyUPi _ _ _) _ => eapply wft_upi; try gw_upi_body; gw_premise
  | |- eq_ty _ _ _ (tyUPi _ _ _) _ _ => eapply eqty_upi; try gw_upi_body; gw_premise
  | |- wf_tm _ _ _ (ulam _ _ _) _ _ => eapply wf_ulam; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (ulam _ _ (uapp _ (ubvars _))) _ _ _ => eapply eqtm_ueta; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (ulam _ _ _) _ _ _ => eapply eqtm_ulam; try gw_upi_body; gw_premise
  | |- wf_tm _ _ _ (uapp _ _) _ _ => eapply wf_uapp; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (uapp (ulam _ _ _) _) _ _ _ => eapply eqtm_ubeta; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (uapp _ _) _ _ _ => eapply eqtm_uapp; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (boxT _) _ _ _ => eapply eqtm_boxT; gw_premise
  | |- eq_tm _ _ _ (boxt _) _ _ _ => eapply eqtm_boxt; gw_premise
  | |- wf_tm _ _ _ (natrec _ _ _ _ _) _ _ => eapply wf_natrec; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ zero) _ _ _ => eapply eqtm_natrec_zero; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ (succ _)) _ _ _ => eapply eqtm_natrec_succ; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ _) (natrec _ _ _ _ _) _ _ => eapply eqtm_natrec; gw_premise
  | |- eq_tm _ _ _ (lam _ _ _ _) _ _ _ => eapply eqtm_eta; gw_premise
  | |- eq_ty _ lM _ _ _ _ => eapply eqty_leq; gw_premise
  | |- eq_tm _ lM _ _ _ _ _ => eapply eqtm_leq; gw_premise
  end.

Theorem gweakening :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ : T⟪γ⟫ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ ≅ T'⟪γ⟫ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ ≅ t'⟪γ⟫ : T⟪γ⟫ @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ⊢[ i ] Γ⟪γ⟫ ≅ Γ'⟪γ⟫ ]).
Proof.
  apply typing_mut; intros; try exact I; push_gren; gren_rewrite; push_gren.
  all: try gw_step.
  all: gw_manual.
Qed.

(** ** Named corollaries, for a weakening [γ : G' ≤ G] *)

Section Named.
Context {γ : gweak} {G' G : gctx} (Hγ : gwk_ok γ G' G) (HG' : [ ⊢ G' ]).

Ltac gwk_named k :=
  destruct G' as [L' Ψ']; destruct Hγ as [Hl Hw]; cbn in Hl, Hw;
  intros H; exact (k _ _ _ _ _ _ H _ _ _ Hl Hw HG') || exact (k _ _ _ _ _ H _ _ _ Hl Hw HG')
  || exact (k _ _ _ _ _ _ _ H _ _ _ Hl Hw HG') || exact (k _ _ _ H _ _ _ Hl Hw HG')
  || exact (k _ _ _ _ H _ _ _ Hl Hw HG').

Lemma gwk_ctx {i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G' ; Γ⟪γ⟫ ⊢[ i ] ].
Proof. gwk_named (proj1 (proj2 gweakening)). Qed.
Lemma gwk_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ @ l ].
Proof. gwk_named (proj1 (proj2 (proj2 gweakening))). Qed.
Lemma gwk_tm {i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ : T⟪γ⟫ @ l ].
Proof. gwk_named (proj1 (proj2 (proj2 (proj2 gweakening)))). Qed.
Lemma gwk_eqty {i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ ≅ T'⟪γ⟫ @ l ].
Proof. gwk_named (proj1 (proj2 (proj2 (proj2 (proj2 gweakening))))). Qed.
Lemma gwk_eqtm {i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ ≅ t'⟪γ⟫ : T⟪γ⟫ @ l ].
Proof. gwk_named (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening)))))). Qed.
Lemma gwk_eqctx {i Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G' ⊢[ i ] Γ⟪γ⟫ ≅ Γ'⟪γ⟫ ].
Proof. gwk_named (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening)))))). Qed.

End Named.


(** ** Reduction under global renaming *)

Lemma red_gren_both :
  (forall t u, red t u -> forall ξ, red t⟪ξ⟫ u⟪ξ⟫) /\
  (forall T U, red_ty T U -> forall ξ, red_ty T⟪ξ⟫ U⟪ξ⟫).
Proof.
  apply red_both; intros; cbn [gren GRen_tm gren_tm GRen_ty gren_ty];
    change (gren_tm ?x ?ξ) with x⟪ξ⟫; change (gren_ty ?x ?ξ) with x⟪ξ⟫;
    change (gcren ?x ?ξ) with x⟪ξ⟫.
  all: rewrite ?gren_single2, ?gren_single, ?gren_gsingle; try now constructor.
  all: try (constructor; auto; fail).
  all: first [ constructor; now apply redT_gren | constructor; now apply redt_gren
             | rewrite <- usubst_gren; now constructor ].
Qed.

Lemma red_gren t u ξ : red t u -> red t⟪ξ⟫ u⟪ξ⟫.
Proof. intros H; now apply red_gren_both. Qed.
Lemma red_ty_gren T U ξ : red_ty T U -> red_ty T⟪ξ⟫ U⟪ξ⟫.
Proof. intros H; now apply red_gren_both. Qed.
Lemma reds_gren t u ξ : reds t u -> reds t⟪ξ⟫ u⟪ξ⟫.
Proof. unfold reds; induction 1; [constructor|econstructor; eauto using red_gren]. Qed.
Lemma reds_ty_gren T U ξ : reds_ty T U -> reds_ty T⟪ξ⟫ U⟪ξ⟫.
Proof. unfold reds_ty; induction 1; [constructor|econstructor; eauto using red_ty_gren]. Qed.

(** ** Local weakenings under global renaming *)

Lemma wk_wf_gren (ρ : wk) Δ Γ ξ : ρ : Δ ≤ Γ -> ρ : Δ⟪ξ⟫ ≤ Γ⟪ξ⟫.
Proof.
  induction 1; cbn [gren GRen_ctx gcren]; change (gren_ty ?A ?ξ) with A⟪ξ⟫;
    change (gcren ?A ?ξ) with A⟪ξ⟫; try rewrite gren_ren_ty'; now constructor.
Qed.

(** ** Composition of global weakenings *)

Fixpoint gwk_comp (γ' γ : gweak) : gweak :=          (* first γ, then γ' *)
  match γ', γ with
  | gwk_id, γ => γ
  | gwk_step γ', γ => gwk_step (gwk_comp γ' γ)
  | gwk_up γ', gwk_id => gwk_up γ'
  | gwk_up γ', gwk_step γ => gwk_step (gwk_comp γ' γ)
  | gwk_up γ', gwk_up γ => gwk_up (gwk_comp γ' γ)
  end.

Lemma gwk_fn_comp γ' γ n : gwk_comp γ' γ n = γ' (γ n).
Proof.
  revert γ n; induction γ' as [|γ' IH|γ' IH]; intros γ n.
  - destruct γ; reflexivity.
  - cbn. now rewrite IH.
  - destruct γ as [|γ|γ]; cbn; [reflexivity | now rewrite IH |].
    destruct n; cbn; [reflexivity | now rewrite IH].
Qed.

Lemma gwk_comp_id_r γ : gwk_comp γ gwk_id = γ.
Proof. induction γ; cbn; congruence. Qed.

Lemma gwk_comp_wf γ' γ Ψ'' Ψ' Ψ : gwk_wf γ' Ψ'' Ψ' -> gwk_wf γ Ψ' Ψ -> gwk_wf (gwk_comp γ' γ) Ψ'' Ψ.
Proof.
  intros H'; revert γ Ψ; induction H' as [Θ|γ' Ξ Θ D H' IH|γ' Ξ Θ D H' IH]; intros γ Ψ0 H.
  - destruct γ; exact H.
  - constructor; auto.
  - inversion H as [Θ0|γ0 Θ0 Ψ1 D0 H0|γ0 Θ0 Ψ1 D0 H0]; subst; cbn.
    + constructor; auto.
    + constructor; auto.
    + rewrite (gdecl_ren_comp _ _ _ (gwk_comp γ' γ0)) by (intros; apply gwk_fn_comp).
      constructor; auto.
Qed.

Lemma gwk_ok_id G : gwk_ok gwk_id G G.
Proof. split; [apply le_n | constructor]. Qed.
Lemma gwk_ok_id_inv {G' G} : gwk_ok gwk_id G' G -> G' = mkG (gL G') (gΨ G).
Proof.
  destruct G' as [L' Ψ'], G as [L Ψ]; intros [Hl Hw]; cbn in *.
  inversion Hw; subst; reflexivity.
Qed.
Lemma gwk_ok_comp {γ' γ G'' G' G} : gwk_ok γ' G'' G' -> gwk_ok γ G' G ->
  gwk_ok (gwk_comp γ' γ) G'' G.
Proof. intros [H1 H2] [H3 H4]; split; [lia | eapply gwk_comp_wf; eauto]. Qed.

(** ** The action of a global weakening

    [x⟦γ⟧] is [x⟪γ⟫], except that the identity weakening acts as the
    identity *by definition* (renaming by the identity function is the
    identity only on deep-normal syntax).  The Kripke quantification of the
    logical relation uses it, so that its purely local instances are
    literally M1's. *)

Definition gwa {X} `{GRen X} (γ : gweak) (x : X) : X :=
  match γ with gwk_id => x | _ => x⟪γ⟫ end.
Notation "x ⟦ γ ⟧" := (gwa γ x) (at level 5, format "x ⟦ γ ⟧").

Lemma gwa_gren {X} `{GRen X} (γ : gweak) (x : X) : γ <> gwk_id -> x⟦γ⟧ = x⟪γ⟫.
Proof. destruct γ; cbn; congruence. Qed.

(** Composition, for each syntactic class. *)
Lemma gwk_comp_not_id γ' γ : γ <> gwk_id -> gwk_comp γ' γ <> gwk_id.
Proof. destruct γ', γ; cbn; congruence. Qed.

Lemma gwa_comp_gen {X} `{GRen X}
  (gg : forall (x : X) ξ ζ θ, (forall i, θ i = ζ (ξ i)) -> x⟪ξ⟫⟪ζ⟫ = x⟪θ⟫)
  (x : X) γ' γ : x⟦γ⟧⟦γ'⟧ = x⟦gwk_comp γ' γ⟧.
Proof.
  destruct γ' as [|γ1|γ1]; [reflexivity|..];
    (destruct γ as [|γ2|γ2]; [now rewrite gwk_comp_id_r|..]);
    rewrite !gwa_gren by (discriminate || (apply gwk_comp_not_id; discriminate));
    apply gg; intros; apply gwk_fn_comp.
Qed.

Lemma gwa_comp_ty (T : ty) γ' γ : T⟦γ⟧⟦γ'⟧ = T⟦gwk_comp γ' γ⟧.
Proof. apply gwa_comp_gen, gren_gren_ty. Qed.
Lemma gwa_comp_tm (t : tm) γ' γ : t⟦γ⟧⟦γ'⟧ = t⟦gwk_comp γ' γ⟧.
Proof. apply gwa_comp_gen, gren_gren_tm'. Qed.
Lemma gwa_comp_ctx (Γ : ctx) γ' γ : Γ⟦γ⟧⟦γ'⟧ = Γ⟦gwk_comp γ' γ⟧.
Proof. apply gwa_comp_gen, gcren_gcren. Qed.

(** Commutation with the local operations. *)
Lemma gwa_ren_ty (T : ty) (r : rsub) γ : T⟨r⟩⟦γ⟧ = T⟦γ⟧⟨r⟩.
Proof. destruct γ; cbn [gwa]; auto using gren_ren_ty. Qed.
Lemma gwa_ren (t : tm) (r : rsub) γ : t⟨r⟩⟦γ⟧ = t⟦γ⟧⟨r⟩.
Proof. destruct γ; cbn [gwa]; auto using gren_ren. Qed.
Lemma gwa_subst_ty (T : ty) d γ : T[d]⟦γ⟧ = T⟦γ⟧[d⟦γ⟧].
Proof. destruct γ; cbn [gwa]; auto using gren_subst_ty. Qed.
Lemma gwa_subst (t : tm) d γ : t[d]⟦γ⟧ = t⟦γ⟧[d⟦γ⟧].
Proof. destruct γ; cbn [gwa]; auto using gren_subst. Qed.
Lemma gwa_lsingle (a : tm) γ : (lsingle a)⟦γ⟧ = lsingle a⟦γ⟧.
Proof. destruct γ; reflexivity. Qed.

(** Constructor equations. *)
Section PushGwa.
Variable (γ : gweak).
Lemma gwa_tyNat : tyNat⟦γ⟧ = tyNat. Proof. now destruct γ. Qed.
Lemma gwa_tyPi l l' A B : (tyPi l l' A B)⟦γ⟧ = tyPi l l' A⟦γ⟧ B⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyU l : (tyU l)⟦γ⟧ = tyU l. Proof. now destruct γ. Qed.
Lemma gwa_tyEl l t : (tyEl l t)⟦γ⟧ = tyEl l t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyCTyp Δ l : (tyCTyp Δ l)⟦γ⟧ = tyCTyp Δ⟦γ⟧ l. Proof. now destruct γ. Qed.
Lemma gwa_tyCTrm Δ T l : (tyCTrm Δ T l)⟦γ⟧ = tyCTrm Δ⟦γ⟧ T⟦γ⟧ l. Proof. now destruct γ. Qed.
Lemma gwa_var n : (var n)⟦γ⟧ = var n. Proof. now destruct γ. Qed.
Lemma gwa_zero : zero⟦γ⟧ = zero. Proof. now destruct γ. Qed.
Lemma gwa_succ t : (succ t)⟦γ⟧ = succ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmNat : tmNat⟦γ⟧ = tmNat. Proof. now destruct γ. Qed.
Lemma gwa_tmU l : (tmU l)⟦γ⟧ = tmU l. Proof. now destruct γ. Qed.
Lemma gwa_tmPi l l' s t : (tmPi l l' s t)⟦γ⟧ = tmPi l l' s⟦γ⟧ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_lam l l' A t : (lam l l' A t)⟦γ⟧ = lam l l' A⟦γ⟧ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_app t l l' A B s : (app t l l' A B s)⟦γ⟧ = app t⟦γ⟧ l l' A⟦γ⟧ B⟦γ⟧ s⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_natrec l M s z t : (natrec l M s z t)⟦γ⟧ = natrec l M⟦γ⟧ s⟦γ⟧ z⟦γ⟧ t⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_cext Γ A l : (Γ ,, A @ l)⟦γ⟧ = Γ⟦γ⟧ ,, A⟦γ⟧ @ l. Proof. now destruct γ. Qed.
Lemma gwa_cnil : cnil⟦γ⟧ = cnil. Proof. now destruct γ. Qed.
Lemma gwa_cvar g : (cvar g)⟦γ⟧ = cvar (γ g). Proof. now destruct γ. Qed.
End PushGwa.

Ltac push_gwa := repeat progress (
  rewrite ?gwa_tyNat, ?gwa_tyPi, ?gwa_tyU, ?gwa_tyEl, ?gwa_tyCTyp, ?gwa_tyCTrm,
          ?gwa_var, ?gwa_zero, ?gwa_succ, ?gwa_tmNat, ?gwa_tmU, ?gwa_tmPi, ?gwa_lam, ?gwa_app,
          ?gwa_natrec, ?gwa_cext).

(** Normal forms, reduction, local weakenings. *)
Lemma whne_gwa t γ : whne t -> whne t⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using whne_gren. Qed.
Lemma whnf_gwa t γ : whnf t -> whnf t⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using whnf_gren. Qed.
Lemma whne_ty_gwa T γ : whne_ty T -> whne_ty T⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using whne_ty_gren. Qed.
Lemma whnf_ty_gwa T γ : whnf_ty T -> whnf_ty T⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using whnf_ty_gren. Qed.
Lemma reds_gwa t u γ : reds t u -> reds t⟦γ⟧ u⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using reds_gren. Qed.
Lemma reds_ty_gwa T U γ : reds_ty T U -> reds_ty T⟦γ⟧ U⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using reds_ty_gren. Qed.
Lemma wk_wf_gwa (ρ : wk) Δ Γ γ : ρ : Δ ≤ Γ -> ρ : Δ⟦γ⟧ ≤ Γ⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using wk_wf_gren. Qed.

(** Judgments. *)
(** The identity global renaming is the identity on deep-normal syntax. *)
Lemma gren_id_ty' (T : ty) : dnfty T -> T⟪gwk_fn gwk_id⟫ = T.
Proof. intros H; apply (proj1 gren_id_all); auto. Qed.
Lemma gren_id_tm' (t : tm) : dnftm t -> t⟪gwk_fn gwk_id⟫ = t.
Proof. intros H; apply (proj1 (proj2 gren_id_all)); auto. Qed.
Lemma gren_id_ctx' (Γ : ctx) : dnfctx Γ -> Γ⟪gwk_fn gwk_id⟫ = Γ.
Proof. intros H; apply (proj1 (proj2 (proj2 gren_id_all))); auto. Qed.

(** Level growth of a global context (M3_DESIGN.md E14). *)
Lemma wfg_grow L L' Ψ : L <= L' -> [ ⊢ mkG L Ψ ] -> [ ⊢ mkG L' Ψ ].
Proof.
  intros HL; induction Ψ as [|D Ψ IH]; intros H; [constructor|].
  inversion H; subst; pose proof (IH ltac:(assumption)) as Hg.
  - now constructor.
  - econstructor; [exact Hg | | eassumption | eapply lwf_weaken; eassumption].
    pose proof (proj1 (proj2 gweakening) _ _ _ ltac:(eassumption) L' Ψ gwk_id HL (gwkwf_id _) Hg) as X.
    rewrite gren_id_ctx' in X by (eapply wf_ctx_dnf; eassumption). exact X.
  - econstructor; [exact Hg | | eassumption | eapply lwf_weaken; eassumption].
    pose proof (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ ltac:(eassumption) L' Ψ gwk_id HL (gwkwf_id _) Hg) as X.
    rewrite gren_id_ctx', gren_id_ty' in X by first [eapply wf_ty_dnf_ctx; eassumption | eapply wf_ty_dnf; eassumption].
    exact X.
Qed.

Ltac dnf_of H :=
  first [ exact (wf_ctx_dnf H) | exact (wf_ty_dnf H) | exact (wf_ty_dnf_ctx H) | exact (wf_tm_dnf H)
        | exact (wf_tm_dnf_ty H) | exact (wf_tm_dnf_ctx H) | exact (proj1 (eqty_dnf H))
        | exact (proj2 (eqty_dnf H)) | exact (eqty_dnf_ctx H) | exact (proj1 (eqtm_dnf H))
        | exact (proj1 (proj2 (eqtm_dnf H))) | exact (proj2 (proj2 (eqtm_dnf H))) | exact (eqtm_dnf_ctx H)
        | exact (proj1 (eqctx_dnf H)) | exact (proj2 (eqctx_dnf H)) ].

Section NamedGwa.
Context {γ : gweak} {G' G : gctx} (Hγ : gwk_ok γ G' G) (HG' : [ ⊢ G' ]).

Ltac gwa_named k :=
  destruct γ as [|γ0|γ0] eqn:Eγ; cbn [gwa];
  [ let H := fresh "H" in let H0 := fresh "H0" in
    intros H; pose proof H as H0; apply (k _ _ _ Hγ HG') in H;
    rewrite ?gren_id_ctx', ?gren_id_ty', ?gren_id_tm' in H by dnf_of H0; exact H
  | rewrite <- Eγ in *; apply (k _ _ _ Hγ HG') .. ].

Lemma gwa_ctx {i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] ].
Proof. gwa_named @gwk_ctx. Qed.
Lemma gwa_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] T⟦γ⟧ @ l ].
Proof. gwa_named @gwk_ty. Qed.
Lemma gwa_tm {i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] t⟦γ⟧ : T⟦γ⟧ @ l ].
Proof. gwa_named @gwk_tm. Qed.
Lemma gwa_eqty {i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G' ; Γ⟦γ⟧ ⊢[ i ] T⟦γ⟧ ≅ T'⟦γ⟧ @ l ].
Proof. gwa_named @gwk_eqty. Qed.
Lemma gwa_eqtm {i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G' ; Γ⟦γ⟧ ⊢[ i ] t⟦γ⟧ ≅ t'⟦γ⟧ : T⟦γ⟧ @ l ].
Proof. gwa_named @gwk_eqtm. Qed.

End NamedGwa.

(** Local substitutions under [⟦γ⟧]. *)
Lemma llk_gwa (d : lsub) γ n : llk d⟦γ⟧ n = (llk d n)⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using llk_glren. Qed.
Lemma dnf_gwa (t : tm) γ : dnftm t -> dnftm t⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma lsub_tail_gwa d Δ Γ γ : lsub_tail d Δ Γ -> lsub_tail d⟦γ⟧ Δ⟦γ⟧ Γ⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using lsub_tail_gren. Qed.
Lemma llk_llift_gwa (d : lsub) γ n : llk (llift d)⟦γ⟧ n = llk (llift d⟦γ⟧) n.
Proof.
  rewrite llk_gwa, !llk_llift. destruct n; [now rewrite gwa_var|].
  change (ren_tm ?x ?r) with x⟨r⟩. now rewrite gwa_ren, llk_gwa.
Qed.
Lemma in_ctx_gwa Γ n T l γ : in_ctx Γ n T l -> in_ctx Γ⟦γ⟧ n T⟦γ⟧ l.
Proof. destruct γ; cbn [gwa]; auto using in_ctx_gren. Qed.
Lemma gwa_lsucc γ : lsucc⟦γ⟧ = lsucc.
Proof. now destruct γ. Qed.
Lemma gwa_lsingle2 (t q : tm) γ : (lsingle2 t q)⟦γ⟧ = lsingle2 t⟦γ⟧ q⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_eqctx {γ G' G i Γ Γ'} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G' ⊢[ i ] Γ⟦γ⟧ ≅ Γ'⟦γ⟧ ].
Proof.
  intros Hγ HG' H. destruct γ as [|γ0|γ0] eqn:Eγ; cbn [gwa];
    [ pose proof H as H0; apply (gwk_eqctx Hγ HG') in H;
      rewrite ?gren_id_ctx' in H by dnf_of H0; exact H
    | exact (gwk_eqctx Hγ HG' H) ..].
Qed.

(** Global variables and lookups under [⟦γ⟧]. *)
Lemma gwa_tyGvar γ U d : (tyGvar U d)⟦γ⟧ = tyGvar (γ U) d⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_gvar γ u d : (gvar u d)⟦γ⟧ = gvar (γ u) d⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma dnfl_gwa (d : lsub) γ : dnfl d -> dnfl d⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma in_ctx_gwa_inv Γ n T l γ : in_ctx Γ⟦γ⟧ n T l -> exists T0, in_ctx Γ n T0 l /\ T = T0⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [eauto | apply in_ctx_gren_inv ..]. Qed.

Definition gdecl_gwa (D : gdecl) (γ : gweak) : gdecl :=
  match D with
  | gdCtx => gdCtx
  | gdTy Δ i l => gdTy Δ⟦γ⟧ i l
  | gdTm Δ i T l => gdTm Δ⟦γ⟧ i T⟦γ⟧ l
  end.

Lemma gwk_wf_id_eq {Ψ' Ψ} : gwk_wf gwk_id Ψ' Ψ -> Ψ' = Ψ.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma in_gctx_gwa {γ G' G n D} : gwk_ok γ G' G -> in_gctx (gΨ G) n D ->
  in_gctx (gΨ G') (γ n) (gdecl_gwa D γ).
Proof.
  intros [_ Hw] Hin. destruct γ as [|γ0|γ0] eqn:Eγ.
  - rewrite (gwk_wf_id_eq Hw). destruct D; exact Hin.
  - rewrite <- Eγ in *. pose proof (in_gctx_gwk _ _ _ _ _ Hw Hin) as X. subst γ. destruct D; exact X.
  - rewrite <- Eγ in *. pose proof (in_gctx_gwk _ _ _ _ _ Hw Hin) as X. subst γ. destruct D; exact X.
Qed.
