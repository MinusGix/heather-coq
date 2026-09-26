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
