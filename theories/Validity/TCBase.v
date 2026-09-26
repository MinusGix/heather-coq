(** * Decidable type checking: the statements and their helpers (M7_DESIGN.md C1, J3.5)

    The four decision problems, each under the presuppositions a checker
    establishes before asking it:
    - [TYD T]: well-formedness of [T], in a context well formed at
      [typeof i];
    - [CKD t]: checking [t] against a type well formed at [typeof i];
    - [SYD t]: whether [t] has some type (for synthesizing terms, whose
      type is then unique, [type_uniq]);
    - [CXD Γ]: well-formedness of [Γ], in a well-formed global context.

    Helpers: the scopes under a new global binding, the type of the
    [letbox] bodies, the entries of a local substitution (a telescope:
    each entry's type is well formed once the later ones are typed,
    [sub_dec]), and views of a whnf type by its head. *)
From DeLaM.Typing Require Export RecAdm DecSide.
From DeLaM.Validity Require Export TypeUniq.

Definition TYD (T : ty) : Prop :=
  forall G i Γ k, [ G ; Γ ⊢[ typeof i ] ] -> Dec ([ G ; Γ ⊢[ i ] T @ k ]).
Definition CKD (t : tm) : Prop :=
  forall G i Γ T k, [ G ; Γ ⊢[ typeof i ] T @ k ] -> Dec ([ G ; Γ ⊢[ i ] t : T @ k ]).
Definition SYD (t : tm) : Prop :=
  forall G i Γ, [ G ; Γ ⊢[ typeof i ] ] ->
  (exists T k, [ G ; Γ ⊢[ i ] t : T @ k ]) \/ (forall T k, ~ [ G ; Γ ⊢[ i ] t : T @ k ]).
Definition CXD (Γ : ctx) : Prop := forall G i, [ ⊢ G ] -> Dec ([ G ; Γ ⊢[ i ] ]).

(** ** Layers *)

Lemma lle_D_typeof i : lle lD (typeof i).
Proof. destruct i; unfold lle; cbn; lia. Qed.
Lemma typeof_notV i : typeof i <> lV.
Proof. destruct i; discriminate. Qed.
Lemma lift_to_typeof_ty {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ typeof i ] T @ l ].
Proof. intros H; exact (lift_ty H (lle_self_typeof i)). Qed.
Lemma lift_to_typeof_tm {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ typeof i ] t : T @ l ].
Proof. intros H; exact (lift_tm H (lle_self_typeof i)). Qed.
Lemma lift_ctx_typeof {G i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ typeof i ] ].
Proof. intros H; exact (lift_ctx H (lle_self_typeof i)). Qed.
Lemma D_to_typeof_ty {G i Γ T l} : [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ typeof i ] T @ l ].
Proof. intros H; exact (lift_ty H (lle_D_typeof i)). Qed.

(** ** Under one more global binding *)

Lemma ctx_S {G i Γ D} : [ ⊢ gext G D ] -> [ G ; Γ ⊢[ i ] ] -> [ gext G D ; Γ⟪S⟫ ⊢[ i ] ].
Proof.
  intros HG H. pose proof (gwk_ctx (gwk_ok_step (G := G) (D := D)) HG H) as X.
  unfold gren, GRen_ctx in X |- *. rewrite (proj1 (proj2 (proj2 gren_ext_all)) Γ _ S) in X
    by reflexivity. exact X.
Qed.

Lemma ty_S {G i Γ T l D} : [ ⊢ gext G D ] -> [ G ; Γ ⊢[ i ] T @ l ] -> [ gext G D ; Γ⟪S⟫ ⊢[ i ] T⟪S⟫ @ l ].
Proof.
  intros HG H. pose proof (gwk_ty (gwk_ok_step (G := G) (D := D)) HG H) as X.
  unfold gren, GRen_ctx, GRen_ty in X |- *.
  rewrite (proj1 (proj2 (proj2 gren_ext_all)) Γ _ S), (proj1 gren_ext_all T _ S) in X by reflexivity.
  exact X.
Qed.

Lemma wfg_ctx' {G} : [ ⊢ G ] -> [ ⊢ gext G gdCtx ].
Proof. destruct G; apply wfg_ctx. Qed.
Lemma wfg_ty' {G Δ i l} : [ G ; Δ ⊢[ lD ] ] -> (i = lC \/ i = lD) -> lwf (gL G) l -> [ ⊢ gext G (gdTy Δ i l) ].
Proof. destruct G; intros; apply wfg_ty; auto. exact (ctx_glob _ _ _ H). Qed.
Lemma wfg_tm' {G Δ i T l} : [ G ; Δ ⊢[ lD ] T @ l ] -> (i = lV \/ i = lC) -> lwf (gL G) l ->
  [ ⊢ gext G (gdTm Δ i T l) ].
Proof. destruct G; intros; apply wfg_tm; auto. exact (ctx_glob _ _ _ (ctx_of_wf_ty (i := lD) eq_refl H)). Qed.

(** ** The types of the [letbox] bodies *)

Lemma letboxT_body_wf {G Γ Δ l l' M} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l ->
  [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] ->
  [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ].
Proof.
  intros HΔ Hl HM. pose proof (wfg_ty' HΔ (or_introl eq_refl) Hl) as HG1.
  pose proof (ty_S HG1 HM) as X.
  change ((Γ ,, tyCTyp Δ l @ lzero)⟪S⟫) with (Γ⟪S⟫ ,, tyCTyp Δ⟪S⟫ l @ lzero) in X.
  apply (wf_ty_single (i := lM) eq_refl X).
  pose proof (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)) as HΓ.
  apply wf_boxT; [exact (ctx_S HG1 HΓ) | exact Hl | exact (ctx_S HG1 HΔ) |].
  eapply (wf_gv _ lC _ 0 Δ⟪S⟫ lC l); [discriminate | exact (ctx_S HG1 HΔ) | | apply lle_refl | reflexivity].
  exact (ing_here (gΨ G) (gdTy Δ lC l)).
Qed.

Lemma letboxt_body_wf {G Γ Δ T l l' M} : [ G ; Δ ⊢[ lD ] T @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, tyCTrm Δ T l @ lzero ⊢[ lM ] M @ l' ] ->
  [ gext G (gdTm Δ lC T l) ; Γ⟪S⟫ ⊢[ lM ] M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ].
Proof.
  intros HT Hl HM. pose proof (wfg_tm' HT (or_intror eq_refl) Hl) as HG1.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HT) as HΔ.
  pose proof (ty_S HG1 HM) as X.
  change ((Γ ,, tyCTrm Δ T l @ lzero)⟪S⟫) with (Γ⟪S⟫ ,, tyCTrm Δ⟪S⟫ T⟪S⟫ l @ lzero) in X.
  apply (wf_ty_single (i := lM) eq_refl X).
  pose proof (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)) as HΓ.
  apply wf_boxt; [exact (ctx_S HG1 HΓ) | exact Hl | exact (ctx_S HG1 HΔ) | exact (ty_S HG1 HT) |].
  eapply (wf_gu _ lC 0 Δ⟪S⟫ lC T⟪S⟫ l); [exact (ctx_S HG1 HΔ) | | apply lle_refl |].
  { exact (ing_here (gΨ G) (gdTm Δ lC T l)). }
  exact (dnfty_nfty _ (wf_ty_dnf (ty_S HG1 HT))).
Qed.

(** ** The entries of a local substitution *)

Lemma sub_dec {G i Γ} Δ : forall d, [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ lD ] ] ->
  lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, [ G ; Γ ⊢[ typeof i ] A @ k ] -> Dec ([ G ; Γ ⊢[ i ] llk d n : A @ k ])) ->
  Dec (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]).
Proof.
  induction Δ as [| g | Δ IH B lB]; intros d HΓ HΔ Ht Hd Hc;
    try (left; intros n A k Hin; inversion Hin; fail).
  inversion HΔ as [| | ? ? ? ? ? HΔ' HB HlB]; subst.
  assert (Er : forall T : ty, T⟨↑⟩[d] = T[ldrop 1 d])
    by (intros T; apply ren_subst_ty; intros n; rewrite llk_ldrop; cbn; f_equal; lia).
  assert (Ht' : lsub_tail (ldrop 1 d) Δ Γ).
  { destruct Ht as [E1 E2]. split; [exact E1 |]. intros n. rewrite llk_ldrop. exact (E2 n). }
  destruct (IH (ldrop 1 d) HΓ HΔ' Ht' (dnfl_ldrop 1 d Hd)
              (fun n A k HA => ltac:(rewrite llk_ldrop; exact (Hc (1 + n) A k HA)))) as [Y | N].
  - assert (Hs : [ G ; Γ ⊢[ i ] ldrop 1 d : Δ ]).
    { constructor; [exact HΓ | intros n; apply dnfl_llk, dnfl_ldrop, Hd | exact Ht' |].
      exact Y. }
    pose proof (wf_ty_subst_g (D_to_typeof_ty (i := i) HB) (lsub_wf_lle _ _ _ _ _ _ (lle_self_typeof i) Hs))
      as HB'.
    destruct (Hc 0 _ _ HB') as [Y0 | N0].
    + left; intros n A k Hin. inversion Hin as [? ? ? | ? ? ? ? ? m Hm]; subst.
      * rewrite Er. exact Y0.
      * rewrite Er. change (llk d (S m)) with (llk d (1 + m)). rewrite <- llk_ldrop. exact (Y _ _ _ Hm).
    + right; intros H. apply N0. rewrite <- Er. exact (H 0 _ _ (in_here _ _ _)).
  - right; intros H. apply N. intros m A k Hm. rewrite llk_ldrop.
    pose proof (H (S m) _ _ (in_there _ _ _ _ _ _ Hm)) as X. rewrite Er in X. exact X.
Qed.

(** ** Views of a whnf type by its head *)

Lemma pi_view W : (exists m m' A B, W = tyPi m m' A B) \/ ty_head W <> 3.
Proof. destruct W; first [left; do 4 eexists; reflexivity | right; discriminate]. Qed.
Lemma ctyp_view W : (exists Δ l, W = tyCTyp Δ l) \/ ty_head W <> 4.
Proof. destruct W; first [left; do 2 eexists; reflexivity | right; discriminate]. Qed.
Lemma ctrm_view W : (exists Δ A l, W = tyCTrm Δ A l) \/ ty_head W <> 5.
Proof. destruct W; first [left; do 3 eexists; reflexivity | right; discriminate]. Qed.
Lemma upi_view W : (exists n l T, W = tyUPi n l T) \/ ty_head W <> 6.
Proof. destruct W; first [left; do 3 eexists; reflexivity | right; discriminate]. Qed.
Lemma cpi_view W : (exists l T, W = tyCPi l T) \/ ty_head W <> 7.
Proof. destruct W; first [left; do 2 eexists; reflexivity | right; discriminate]. Qed.
Lemma tpi_view W : (exists Δ l l' T, W = tyTPi Δ l l' T) \/ ty_head W <> 8.
Proof. destruct W; first [left; do 4 eexists; reflexivity | right; discriminate]. Qed.

(** A type equal to a whnf [W] and to a whnf former has [W]'s head. *)
Lemma head_of_eq {G j Γ T W F k} : compt j -> whnf_ty W -> whnf_ty F ->
  [ G ; Γ ⊢[ j ] T ≅ W @ k ] -> [ G ; Γ ⊢[ j ] T ≅ F @ k ] -> ty_head W = ty_head F.
Proof.
  intros Hc HW HF E1 E2. refine (decl_head_c Hc _ HW HF).
  eapply eqty_trans; [apply eqty_sym; exact E1 | exact E2].
Qed.
