(** * Prerequisites of the soundness of algorithmic conversion (M6_DESIGN.md H8)

    Declarative facts the algorithm's soundness needs beyond typing
    inversion and the consequences: moving a judgment across an equal
    global binding (the right-hand bodies of [letbox] and [TΠ] are typed
    under their own binding). *)
From DeLaM.Typing Require Export Inversion.
From DeLaM.Validity Require Export DeclConsequences.

(** ** Converting a global binding

    A judgment under [gext G D'] holds under [gext G D] when [D] and [D']
    are equal declarations: the new binding goes to its identity instance
    ([gsub_up_id D' gid]), well typed up to conversion, and typed syntax is
    unchanged by it ([equiv_gsubst]). *)

Section GBind.
Context {G : gctx} {D D' : gdecl} (HG : [ ⊢ G ]) (HGD : [ ⊢ gext G D ])
  (Hobj : gobj_wf (gext G D) (id_obj D' 0) (gdecl_gsubst D' (gsub_wk gid (gwk_step gwk_id)))).

Lemma gbind_sub : [ gext G D ⊢ gsub_up_id D' gid : gext G D' ].
Proof.
  apply gsub_wf_cons; [| destruct D'; cbn; auto | exact Hobj].
  exact (gsub_wf_wk (gsub_wf_gid HG) MInst.gwk_ok_step HGD ltac:(discriminate)).
Qed.

Lemma gup_gid j : gup gid j = GId j.
Proof. destruct j; reflexivity. Qed.

Lemma gbind_ctx_eq {i Γ} : [ gext G D' ; Γ ⊢[ i ] ] -> Γ⦃gsub_up_id D' gid⦄ = Γ.
Proof.
  intros H. rewrite <- (proj1 (proj2 equiv_gsubst) _ _ _ H _ _ (gsub_equiv_up_id G D' gid)
                          (dnfo_gsub_up_id D' gid)).
  apply gsubst_id_ctx; [exact (wf_ctx_dnf H) | exact gup_gid].
Qed.

Lemma gbind_ty_eq {i Γ T l} : [ gext G D' ; Γ ⊢[ i ] T @ l ] -> T⦃gsub_up_id D' gid⦄ = T.
Proof.
  intros H. rewrite <- (proj1 (proj2 (proj2 equiv_gsubst)) _ _ _ _ _ H _ _ (gsub_equiv_up_id G D' gid)
                          (dnfo_gsub_up_id D' gid)).
  apply gsubst_id_ty; [exact (wf_ty_dnf H) | exact gup_gid].
Qed.

Lemma gbind_tm_eq {i Γ t T l} : [ gext G D' ; Γ ⊢[ i ] t : T @ l ] -> t⦃gsub_up_id D' gid⦄ = t.
Proof.
  intros H. rewrite <- (gsubst_up_id_tm i D' gid H).
  apply gsubst_id; [exact (wf_tm_dnf H) | exact gup_gid].
Qed.

Lemma gbind_ty {i Γ T l} : [ gext G D' ; Γ ⊢[ i ] T @ l ] -> [ gext G D ; Γ ⊢[ i ] T @ l ].
Proof.
  intros H. pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ H (D :: gΨ G) _ gbind_sub) as X.
  unfold gwk_to in X; cbn [gL gext] in X.
  rewrite (gbind_ctx_eq (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H)), (gbind_ty_eq H) in X.
  exact X.
Qed.

Lemma gbind_tm {i Γ t T l} : typeof i = i ->
  [ gext G D' ; Γ ⊢[ i ] t : T @ l ] -> [ gext G D ; Γ ⊢[ i ] t : T @ l ].
Proof.
  intros Hi H. pose proof (proj1 (proj2 (proj2 (proj2 gsubstitution))) _ _ _ _ _ _ H (D :: gΨ G) _ gbind_sub)
    as X.
  unfold gwk_to in X; cbn [gL gext] in X.
  rewrite (gbind_ctx_eq (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H)), (gbind_ty_eq (wf_tm_ty Hi H)),
    (gbind_tm_eq H) in X.
  exact X.
Qed.

End GBind.

(** A variable typed at D is typed at every layer [i ≤ D] (it only needs
    its context at D). *)
Lemma var_below_D {G i Γ n A k} : lle i lD -> i <> lV ->
  [ G ; Γ ⊢[ lD ] var n : A @ k ] -> [ G ; Γ ⊢[ i ] var n : A @ k ].
Proof.
  intros Hle Hv H. destruct i; [contradiction | | exact H | exfalso; exact (lle_D_notM Hle eq_refl)].
  destruct (inv_var eq_refl H) as (T0 & l0 & (HΓ & Hin) & Hk & HT).
  assert (X : [ G ; Γ ⊢[ lC ] var n : T0 @ l0 ]) by (apply wf_var; [exact HΓ | exact Hin]).
  destruct Hk as [-> | Hk]; [| eapply wf_lconv in X; [| exact Hk]];
    exact (wf_conv _ _ _ _ _ _ _ X HT).
Qed.

(** The identity instance of a type binding at a layer [i ∈ {C, D}], at an
    equal declaration. *)
Lemma gbind_obj_ty {G Δ Δ' i l l'} : lle i lD -> i <> lV -> [ ⊢ gext G (gdTy Δ i l) ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] -> lequiv (gL G) l l' ->
  gobj_wf (gext G (gdTy Δ i l)) (id_obj (gdTy Δ' i l') 0)
    (gdecl_gsubst (gdTy Δ' i l') (gsub_wk gid (gwk_step gwk_id))).
Proof.
  intros Hle Hv HGD HΔ Hll. cbn [id_obj gdecl_gsubst gobj_wf].
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  rewrite <- gwa_gsubst_ctx, (gsubst_id_ctx Δ' gid (wf_ctx_dnf HD') (fun _ => eq_refl)).
  pose proof (gwk_eqctx (MInst.gwk_ok_step (G := G) (D := gdTy Δ i l)) HGD HΔ) as HΔs.
  pose proof (eqctx_id (i := lD) eq_refl HΔs) as Hid.
  eapply wft_lconv; [| exact (lequiv_sym _ _ _ Hll)].
  eapply (wft_gvar _ _ _ 0 _ i).
  - exact Hv.
  - rewrite (lle_D_typeof _ Hle). exact (lsub_wf_ctx Hid).
  - exact (ing_here _ (gdTy Δ i l)).
  - apply lle_refl.
  - exact (lsub_wf_tail Hid).
  - exact I.
  - intros n A k Hin. exact (var_below_D Hle Hv (lsub_wf_var Hid Hin)).
Qed.

(** The identity instance of a term binding at C, at an equal declaration. *)
Lemma gbind_obj_tm {G Δ Δ' T T' l l'} : [ ⊢ gext G (gdTm Δ lC T l) ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] -> lequiv (gL G) l l' ->
  gobj_wf (gext G (gdTm Δ lC T l)) (id_obj (gdTm Δ' lC T' l') 0)
    (gdecl_gsubst (gdTm Δ' lC T' l') (gsub_wk gid (gwk_step gwk_id))).
Proof.
  intros HGD HΔ HTT Hll. cbn [id_obj gdecl_gsubst gobj_wf].
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  pose proof (ctxconv_eqty HΔ (i := lD) eq_refl HTT) as HTT'.
  rewrite <- gwa_gsubst_ctx, (gsubst_id_ctx Δ' gid (wf_ctx_dnf HD') (fun _ => eq_refl)),
    <- gwa_gsubst_ty, (gsubst_id_ty T' gid (wf_ty_dnf (eqty_wf_r (i := lD) eq_refl HTT')) (fun _ => eq_refl)).
  pose proof (MInst.gwk_ok_step (G := G) (D := gdTm Δ lC T l)) as Hγ.
  pose proof (gwk_eqctx Hγ HGD HΔ) as HΔs.
  pose proof (eqctx_id (i := lD) eq_refl HΔs) as Hid.
  pose proof (gwk_eqty Hγ HGD HTT') as HTTs.
  eapply wf_lconv; [| exact (lequiv_sym _ _ _ Hll)].
  eapply wf_conv; [| exact (eqty_sym _ _ _ _ _ _ HTTs)].
  assert (Hg : [ gext G (gdTm Δ lC T l) ; Δ'⟪gwk_step gwk_id⟫ ⊢[ lC ]
                gvar 0 (lshift 0) : T⟪S⟫[lshift 0] @ l ]).
  { eapply (wf_gvar _ _ _ 0 _ lC).
    - exact (lsub_wf_ctx Hid).
    - exact (ing_here _ (gdTm Δ lC T l)).
    - apply lle_refl.
    - exact (lsub_wf_tail Hid).
    - exact I.
    - intros n A k Hin. exact (var_below_D (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) (lsub_wf_var Hid Hin)). }
  rewrite nf_id_ty in Hg; [exact Hg |].
  exact (wf_ty_nf (eqty_wf_l (i := lD) eq_refl HTTs)).
Qed.

(** ** Motives weakened into a branch scope

    The branch scopes add [nu] levels, [ng] global bindings [Ds] and
    local entries to the ambient scope; the motives are weakened under
    their own binders ([wkb]). An equation between motives survives. *)

Lemma motT_eq_wk {G Γ MT MT' k nu Ds Γ0 j} :
  [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ k ] ->
  [ ⊢ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ] ->
  wkr (rshift j) Γ0 (wkc nu (length Ds) Γ) ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; Γ0 ⊢[ lM ] ] ->
  [ recGT (mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G))) ; recΓT Γ0 ⊢[ lM ]
      MT⟨uupr (ush nu)⟩ᵤ⟪gupr (ush (length Ds))⟫⟨rlift (rshift j)⟩
      ≅ MT'⟨uupr (ush nu)⟩ᵤ⟪gupr (ush (length Ds))⟫⟨rlift (rshift j)⟩ @ lvren k (uupr (ush nu)) ].
Proof.
  intros H HG0 Hr HΓ0.
  set (φ := fun j => lvar (ush nu j)).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ H (S (nu + gL G)) (uup φ)
                (usub_ok_uup _ _ _ (usub_ok_ush nu (gL G)))) as X1.
  unfold G_us in X1. rewrite recGT_usubst, recΓT_usubst, <- gctx_uwk_as in X1.
  rewrite <- (proj1 (proj2 (proj2 uren_as_usubst_all)) Γ (ush nu)) in X1 by reflexivity.
  assert (Eφ : forall n, uup φ n = lvar (uupr (ush nu) n)) by (intros [|n]; reflexivity).
  rewrite <- !(proj1 uren_as_usubst_all _ _ _ Eφ), <- (lvren_as_lvsubst k _ _ Eφ) in X1.
  set (G0 := mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G))) in *.
  assert (Hok : gwk_ok (gwk_stepn (length Ds)) G0 (gctx_uwk nu G))
    by (split; [reflexivity | apply gwk_stepn_wf]).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gweakening)))) _ _ _ _ _ _ X1 (S (nu + gL G))
                (gΨ (recGT G0)) (gwk_up (gwk_stepn (length Ds))) (le_n _) (recGT_gwk _ _ _ Hok)
                (wf_recGT HG0)) as X2.
  cbn [gwk_fn] in X2. rewrite recΓT_gren in X2.
  assert (Eξ : forall i, gwk_fn (gwk_stepn (length Ds)) i = ush (length Ds) i)
    by (intros; now rewrite gwk_stepn_fn).
  assert (Eξ' : forall i, gupr (gwk_fn (gwk_stepn (length Ds))) i = gupr (ush (length Ds)) i)
    by (intros [|i]; cbn; [reflexivity | now rewrite Eξ]).
  rewrite (proj1 (proj2 (proj2 gren_ext_all)) _ _ _ Eξ), !(proj1 gren_ext_all _ _ _ Eξ') in X2.
  exact (proj1 (proj2 (proj2 weakening_r)) _ _ _ _ _ _ X2 eq_refl _ _ (wkr_recΓT _ _ _ Hr)
           (wf_recΓT _ _ HΓ0)).
Qed.

Lemma mott_eq_wk {G Γ Mt Mt' k nu Ds Γ0 j} :
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ k ] ->
  [ ⊢ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ] ->
  wkr (rshift j) Γ0 (wkc nu (length Ds) Γ) ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; Γ0 ⊢[ lM ] ] ->
  [ recGt (mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G))) ; recΓt Γ0 ⊢[ lM ]
      Mt⟨uupr (ush nu)⟩ᵤ⟪gupr (gupr (ush (length Ds)))⟫⟨rlift (rshift j)⟩
      ≅ Mt'⟨uupr (ush nu)⟩ᵤ⟪gupr (gupr (ush (length Ds)))⟫⟨rlift (rshift j)⟩ @ lvren k (uupr (ush nu)) ].
Proof.
  intros H HG0 Hr HΓ0.
  set (φ := fun j => lvar (ush nu j)).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ H (S (nu + gL G)) (uup φ)
                (usub_ok_uup _ _ _ (usub_ok_ush nu (gL G)))) as X1.
  unfold G_us in X1. rewrite recGt_usubst, recΓt_usubst, <- gctx_uwk_as in X1.
  rewrite <- (proj1 (proj2 (proj2 uren_as_usubst_all)) Γ (ush nu)) in X1 by reflexivity.
  assert (Eφ : forall n, uup φ n = lvar (uupr (ush nu) n)) by (intros [|n]; reflexivity).
  rewrite <- !(proj1 uren_as_usubst_all _ _ _ Eφ), <- (lvren_as_lvsubst k _ _ Eφ) in X1.
  set (G0 := mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G))) in *.
  assert (Hok : gwk_ok (gwk_stepn (length Ds)) G0 (gctx_uwk nu G))
    by (split; [reflexivity | apply gwk_stepn_wf]).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gweakening)))) _ _ _ _ _ _ X1 (S (nu + gL G))
                (gΨ (recGt G0)) (gwk_up (gwk_up (gwk_stepn (length Ds)))) (le_n _) (recGt_gwk _ _ _ Hok)
                (wf_recGt HG0)) as X2.
  cbn [gwk_fn] in X2. rewrite recΓt_gren in X2.
  assert (Eξ : forall i, gwk_fn (gwk_stepn (length Ds)) i = ush (length Ds) i)
    by (intros; now rewrite gwk_stepn_fn).
  assert (Eξ' : forall i, gupr (gupr (gwk_fn (gwk_stepn (length Ds)))) i = gupr (gupr (ush (length Ds))) i)
    by (intros [|[|i]]; cbn; [reflexivity | reflexivity | now rewrite Eξ]).
  rewrite (proj1 (proj2 (proj2 gren_ext_all)) _ _ _ Eξ), !(proj1 gren_ext_all _ _ _ Eξ') in X2.
  exact (proj1 (proj2 (proj2 weakening_r)) _ _ _ _ _ _ X2 eq_refl _ _ (wkr_recΓt _ _ _ Hr)
           (wf_recΓt _ _ HΓ0)).
Qed.

Lemma lvren_ush1_uupr l nu : lvren (lvren l (ush 1)) (uupr (ush nu)) = lvren (lvren l (ush nu)) (ush 1).
Proof.
  rewrite (lvren_lvren l _ _ (fun n => S (nu + n))) by reflexivity.
  rewrite (lvren_lvren l _ _ (fun n => S (nu + n))) by reflexivity. reflexivity.
Qed.

(** An entry of a branch scope (or its result type): a motive instance at
    fixed objects, equal at equal motives. *)
Lemma motT_wkb_eq {G Γ MT MT' l1 nu Ds Γ0 j lv g c} :
  [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
  [ ⊢ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ] ->
  wkr (rshift j) Γ0 (wkc nu (length Ds) Γ) ->
  lwf (nu + gL G) lv ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; g ⊢[ lD ] ] ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; Γ0 ⊢[ lM ] c : tyCTyp g lv @ lzero ] ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; Γ0 ⊢[ lM ]
      motT (wkb nu (length Ds) j (wrapMT MT)) lv g c ≅ motT (wkb nu (length Ds) j (wrapMT MT')) lv g c
      @ lvren l1 (ush nu) ].
Proof.
  intros H HG0 Hr Hlv Hg Hc.
  pose proof (motT_eq_wk H HG0 Hr (ctx_of_wf_tm (i := lM) eq_refl Hc)) as X.
  rewrite lvren_ush1_uupr in X.
  exact (motT_eq_inst _ _ _ _ _ _ _ _ X Hlv Hg Hc).
Qed.

Lemma mott_wkb_eq {G Γ Mt Mt' l2 nu Ds Γ0 j lv g U c} :
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
  [ ⊢ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ] ->
  wkr (rshift j) Γ0 (wkc nu (length Ds) Γ) ->
  lwf (nu + gL G) lv ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; g ⊢[ lD ] ] ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; g ⊢[ lD ] U @ lv ] ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; Γ0 ⊢[ lM ] c : tyCTrm g U lv @ lzero ] ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; Γ0 ⊢[ lM ]
      mott (wkb nu (length Ds) j (wrapMt Mt)) lv g U c ≅ mott (wkb nu (length Ds) j (wrapMt Mt')) lv g U c
      @ lvren l2 (ush nu) ].
Proof.
  intros H HG0 Hr Hlv Hg HU Hc.
  pose proof (mott_eq_wk H HG0 Hr (ctx_of_wf_tm (i := lM) eq_refl Hc)) as X.
  rewrite lvren_ush1_uupr in X.
  exact (mott_eq_inst _ _ _ _ _ _ _ _ _ X Hlv Hg HU Hc).
Qed.

(** ** The branch scopes at equal motives *)

Lemma wfc_ext_inv {G i Γ A l} : [ G ; Γ ,, A @ l ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] ] /\ [ G ; Γ ⊢[ i ] A @ l ] /\ lwf (gL G) l.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma wkr_shift_S {j Δ Γ A l} : wkr (rshift j) Δ Γ -> wkr (rshift (S j)) (Δ ,, A @ l) Γ.
Proof. intros H. exact (wkr_step _ _ _ A l H). Qed.

(** Global type variables at the non-identity instances of the [elimN]
    branch ([U_M^{id, a/x}], [U_M^{id, succ x/x}]), at any index. *)
Lemma wf_gv_single {G i i' g U A k l a} : i <> lV -> [ G ; cvar g ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g ,, A @ k) i' l) -> lle i' i -> dnftm a ->
  [ G ; cvar g ⊢[ i ] a : A @ k ] -> [ G ; cvar g ⊢[ i ] tyGvar U (lsingle a) @ l ].
Proof.
  intros Hv HΓ Hin Hle Ha Hat. eapply wft_gvar; [exact Hv | exact HΓ | exact Hin | exact Hle | | | ].
  - split; [reflexivity | intros; cbn; f_equal; lia].
  - cbn; tauto.
  - intros n B k' HB. inversion HB as [? ? ? | ? ? ? ? ? ? HB']; subst; [|inversion HB'].
    cbn. rewrite shift_single_ty by exact (wf_tm_nf_ty Hat). exact Hat.
Qed.

Lemma wf_gv_succ {G i i' g U l} : i <> lV ->
  [ G ; cvar g ,, tyNat @ lzero ,, tyGvar U (lshift 0) @ l ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g ,, tyNat @ lzero) i' l) -> lle i' i ->
  [ G ; cvar g ,, tyNat @ lzero ,, tyGvar U (lshift 0) @ l ⊢[ i ] tyGvar U lsucc @ l ].
Proof.
  intros Hv HΓ Hin Hle. eapply wft_gvar; [exact Hv | exact HΓ | exact Hin | exact Hle | | | ].
  - split; [reflexivity | intros; cbn; f_equal; lia].
  - cbn; tauto.
  - intros n A k HA. inversion HA as [? ? ? | ? ? ? ? ? ? HA']; subst; [|inversion HA'].
    cbn. apply wf_succ; [exact Hv|].
    exact (wf_var _ i _ 1 _ _ HΓ (in_there _ _ _ _ _ _ (in_here _ _ _))).
Qed.

(** Side conditions in a concrete branch scope: levels, lookups, weakenings,
    and the typing of the objects (contexts at D, codes at C, boxes at M). *)
Ltac br_lvl := cbn; repeat split; try lia.
Ltac br_tac :=
  repeat first
    [ assumption | exact I | reflexivity | discriminate | apply lle_refl
    | solve [unfold lle; cbn; lia] | solve [br_lvl] | glookup
    | apply wkr_id | apply wkr_shift_S
    | apply wfc_var | apply wfc_ext
    | eapply wf_boxT | eapply wf_boxt
    | apply wft_nat | apply wft_U | eapply wft_pi | eapply wft_El
    | eapply wf_code_nat | eapply wf_code_U | eapply wf_code_pi
    | apply wf_zero | apply wf_succ | eapply wf_natrec | eapply wf_lam | eapply wf_app
    | eapply wf_gv | eapply wf_gu | eapply wf_gv_single | eapply wf_gv_succ ].

Lemma lequiv_ush nu {L l l'} : lequiv L l l' -> lequiv (nu + L) (lvren l (ush nu)) (lvren l' (ush nu)).
Proof. apply lequiv_lvren. intros n Hn; unfold ush; lia. Qed.

(** One branch: invert its scope's well-formedness, relate the entries
    pairwise, then the result types. *)
Ltac br_eq HMT HMt HG0 :=
  match goal with |- context [brG ?K _] =>
    first [ eapply (motT_wkb_eq (Ds := brDecls K)) | eapply (mott_wkb_eq (Ds := brDecls K)) ];
    [ first [exact HMT | exact HMt] | exact HG0 | .. ]; br_tac
  end.
Ltac br_solve HMT HMt HG0 HB :=
  unfold brΓ, brLocs, brRes, brLv in *; cbn [cexts br_nu br_ng br_nl br_ar br_isT Nat.ltb Nat.leb mkLocs call_ty call_lv br_calls br_head] in *;
  repeat match goal with H : wf_ctx _ _ (_ ,, _ @ _) |- _ =>
    let H1 := fresh "HC" in let H2 := fresh "HA" in let H3 := fresh "Hl" in
    destruct (wfc_ext_inv H) as (H1 & H2 & H3); clear H end;
  split;
  [ repeat (eapply eqc_ext; [ | eassumption | br_eq HMT HMt HG0 | apply lequiv_ush; assumption ]);
    apply eqc_refl; exact HB
  | br_eq HMT HMt HG0 ].

Lemma brΓ_conv {G Γ MT MT' Mt Mt' l1 l2 l1' l2'} k : k < nbr ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> [ G ; Γ ⊢[ lM ] ] ->
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ] ->
  [ brG k G ⊢[ lM ] brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ≅ brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ] /\
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
      brRes k (wrapMT MT) (wrapMt Mt) ≅ brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1 l2 ].
Proof.
  intros Hk HMT HMt Hl1 Hl2 HΓ HC.
  pose proof (wf_brG (ctx_glob _ _ _ HΓ) k Hk) as HG0.
  pose proof (wf_wkc_br G Γ k Hk HΓ) as HB.
  br_all ltac:(try (destruct k as [|k])).
  all: try (exfalso; lia).
  all: br_solve HMT HMt HG0 HB.
Qed.

(** A branch typed in the right recursor's scope is typed in the left's. *)
Lemma branch_conv {G Γ MT MT' Mt Mt' l1 l2 l1' l2' b} k : k < nbr ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> [ G ; Γ ⊢[ lM ] ] ->
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ] ->
  [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ] ->
  [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
      b : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ] ->
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
      b : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ].
Proof.
  intros Hk HMT HMt Hl1 Hl2 HΓ HC HC' Hb.
  assert (Hlv : lequiv (gL (brG k G)) (brLv k l1 l2) (brLv k l1' l2')).
  { unfold brLv. destruct (br_isT k); apply lequiv_ush; assumption. }
  assert (HMT' : [ recGT G ; recΓT Γ ⊢[ lM ] MT' ≅ MT @ lvren l1' (ush 1) ]).
  { eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ HMT) | apply lequiv_ush, lequiv_sym, Hl1]. }
  assert (HMt' : [ recGt G ; recΓt Γ ⊢[ lM ] Mt' ≅ Mt @ lvren l2' (ush 1) ]).
  { eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ HMt) | apply lequiv_ush, lequiv_sym, Hl2]. }
  destruct (brΓ_conv k Hk HMT' HMt' (lequiv_sym _ _ _ Hl1) (lequiv_sym _ _ _ Hl2) HΓ HC') as [HCC _].
  destruct (brΓ_conv k Hk HMT HMt Hl1 Hl2 HΓ HC) as [_ HR].
  pose proof (wf_tm_subst (i := lM) eq_refl Hb (eqctx_id (i := lM) eq_refl HCC)) as X.
  rewrite (nf_id_ty _ (wf_tm_nf_ty Hb)), (nf_id _ (wf_tm_nf Hb)) in X.
  eapply wf_lconv; [| exact Hlv].
  eapply wf_conv; [exact X |]. eapply eqty_lconv; [exact HR | exact (lequiv_sym _ _ _ Hlv)].
Qed.

(** ** Local substitutions entrywise

    The right entries of two substitutions are typed at [A[d']]; they are
    converted to [A[d]] by the equation of the deeper entries (induction on
    the domain, by the tails [ldrop 1]). *)

Lemma shift_subst_ldrop1 (A : ty) d : A⟨↑⟩[d] = A[ldrop 1 d].
Proof. apply ren_subst_ty. intros n; rewrite llk_ldrop; cbn; f_equal; lia. Qed.

Lemma lsub_wf_drop1 {G i Γ Δ B lB d} : [ G ; Γ ⊢[ i ] d : Δ ,, B @ lB ] -> [ G ; Γ ⊢[ i ] ldrop 1 d : Δ ].
Proof.
  intros [HΓ Hn Ht Hv]. constructor; [exact HΓ | apply lk_dnf_ldrop, Hn | exact (tail_ldrop1' Ht) |].
  intros n A k Hin. pose proof (Hv _ _ _ (in_there _ _ _ _ _ _ Hin)) as X.
  rewrite shift_subst_ldrop1 in X. rewrite llk_ldrop. exact X.
Qed.

Lemma lsub_eq_pt {G i} (Hi : typeof i = i) : forall Δ Γ d d', [ G ; Δ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] d : Δ ] -> [ G ; Γ ⊢[ i ] d' : Δ ] ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d] @ k ] ->
     [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] d ≅ d' : Δ ].
Proof.
  induction Δ as [| g | Δ0 IH B lB]; intros Γ d d' HΔ Hd Hd' Hpt.
  - refine (conj Hd (conj Hd' _)). intros n A k Hin; inversion Hin.
  - refine (conj Hd (conj Hd' _)). intros n A k Hin; exfalso; exact (no_in_ctx_var _ _ _ _ Hin).
  - destruct (wfc_ext_inv HΔ) as (HΔ0 & HB & _).
    assert (E0 : [ G ; Γ ⊢[ i ] ldrop 1 d ≅ ldrop 1 d' : Δ0 ]).
    { apply IH; [exact HΔ0 | exact (lsub_wf_drop1 Hd) | exact (lsub_wf_drop1 Hd') |].
      intros n A k Hin Hr. rewrite llk_ldrop in Hr. rewrite !llk_ldrop. cbn [Nat.add] in *.
      pose proof (Hpt (S n) _ _ (in_there _ _ _ _ _ _ Hin)) as Y.
      rewrite shift_subst_ldrop1 in Y. exact (Y Hr). }
    refine (conj Hd (conj Hd' _)). intros n A k Hin.
    inversion Hin as [Γ1 A1 l1 | Γ1 A1 l1 B1 l1' m Hm]; subst.
    + apply Hpt; [constructor |].
      pose proof (lsub_wf_var Hd' (in_here _ _ _)) as X.
      rewrite shift_subst_ldrop1 in X |- *.
      eapply wf_conv; [exact X |]. rewrite Hi.
      exact (wf_ty_func Hi HB E0).
    + pose proof (proj2 (proj2 E0) _ _ _ Hm) as X. rewrite !llk_ldrop in X. cbn [Nat.add] in X.
      rewrite shift_subst_ldrop1. exact X.
Qed.
