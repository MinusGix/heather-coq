(** * Context conversion along context equivalence at P

    [[G ⊢[D] Δ ≅ Δ']] moves judgments over [Δ] to [Δ'] at every layer
    whose contexts live at P ([typeof i = D], i.e. C and P).  Used for the
    payloads of static code (M2_DESIGN.md, 5d). *)
From DeLaM.Typing Require Export Presupposition.

(** Typings of a variable only depend on the layer of their contexts. *)
Lemma var_layer {G i Γ n T l} : [ G ; Γ ⊢[ i ] var n : T @ l ] ->
  forall i', typeof i' = typeof i -> [ G ; Γ ⊢[ i' ] var n : T @ l ].
Proof.
  intros H; remember (var n) as x eqn:Ex; induction H; inversion Ex; subst; intros i' Hi'.
  - apply wf_var; [rewrite Hi'; assumption | assumption].
  - eapply wf_conv; [now apply IHwf_tm | rewrite Hi'; assumption].
  - eapply wf_lconv; [now apply IHwf_tm | assumption].
Qed.

Section CtxConv.
Context {G : gctx} {Δ Δ' : ctx} (Hc : [ G ⊢[ lD ] Δ ≅ Δ' ]).

Lemma eqctx_id_at {i} : typeof i = lD -> [ G ; Δ' ⊢[ i ] lshift 0 : Δ ].
Proof.
  intros Hi. pose proof (eqctx_id (i := lD) eq_refl Hc) as [Hw Hn Ht Hv].
  constructor; [rewrite Hi; exact Hw | exact Hn | exact Ht |].
  intros n T l Hin. exact (var_layer (Hv _ _ _ Hin) i Hi).
Qed.

Let P3 := proj1 (proj2 (proj2 substitution_all)).
Let P4 := proj1 (proj2 (proj2 (proj2 substitution_all))).
Let P5 := proj1 (proj2 (proj2 (proj2 (proj2 substitution_all)))).
Let P6 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 substitution_all))))).

Lemma ctxconv_ty {i T l} : typeof i = lD -> [ G ; Δ ⊢[ i ] T @ l ] -> [ G ; Δ' ⊢[ i ] T @ l ].
Proof.
  intros Hi H. pose proof (P3 _ _ _ _ _ H _ _ (eqctx_id_at Hi)) as X.
  now rewrite nf_id_ty in X by exact (wf_ty_nf H).
Qed.
Lemma ctxconv_tm {i t T l} : typeof i = lD -> [ G ; Δ ⊢[ i ] t : T @ l ] -> [ G ; Δ' ⊢[ i ] t : T @ l ].
Proof.
  intros Hi H. pose proof (P4 _ _ _ _ _ _ H _ _ (eqctx_id_at Hi)) as X.
  now rewrite nf_id_ty, nf_id in X by first [exact (wf_tm_nf H) | exact (wf_tm_nf_ty H)].
Qed.
Lemma ctxconv_eqty {i T T' l} : typeof i = lD -> [ G ; Δ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Δ' ⊢[ i ] T ≅ T' @ l ].
Proof.
  intros Hi H. pose proof (P5 _ _ _ _ _ _ H _ _ (eqctx_id_at Hi)) as X.
  destruct (typed_nf) as (_ & _ & _ & _ & HN & _).
  destruct (HN _ _ _ _ _ _ H) as [N1 N2].
  now rewrite !nf_id_ty in X by assumption.
Qed.
Lemma ctxconv_eqtm {i t t' T l} : typeof i = lD -> [ G ; Δ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G ; Δ' ⊢[ i ] t ≅ t' : T @ l ].
Proof.
  intros Hi H. pose proof (P6 _ _ _ _ _ _ _ H _ _ (eqctx_id_at Hi)) as X.
  destruct (typed_nf) as (_ & _ & _ & _ & _ & HN).
  destruct (HN _ _ _ _ _ _ _ H) as (N1 & N2 & N3).
  now rewrite nf_id_ty, !nf_id in X by assumption.
Qed.

End CtxConv.

(** ** Symmetry and transitivity of context equivalence at P *)

Lemma eqctx_sym_D {G Γ Γ'} : [ G ⊢[ lD ] Γ ≅ Γ' ] -> [ G ⊢[ lD ] Γ' ≅ Γ ].
Proof.
  intros H; remember lD as i eqn:Ei;
    induction H as [G i HG | G i g HG Hg | G i Γ Γ' A A' l l' HΓ IH HA HAA Hl]; subst.
  - now apply eqc_nil.
  - now apply eqc_var.
  - specialize (IH eq_refl). pose proof (eqty_wf_r (i := lD) eq_refl HAA) as HA'.
    apply eqc_ext.
    + exact IH.
    + eapply wft_lconv; [exact (ctxconv_ty (i := lD) HΓ eq_refl HA') | solve [apply lequiv_sym; assumption]].
    + eapply eqty_lconv; [exact (ctxconv_eqty (i := lD) HΓ eq_refl (eqty_sym _ _ _ _ _ _ HAA)) | solve [apply lequiv_sym; assumption]].
    + solve [apply lequiv_sym; assumption].
Qed.

Lemma eqctx_trans_D {G Γ1 Γ2 Γ3} :
  [ G ⊢[ lD ] Γ1 ≅ Γ2 ] -> [ G ⊢[ lD ] Γ2 ≅ Γ3 ] -> [ G ⊢[ lD ] Γ1 ≅ Γ3 ].
Proof.
  intros H; revert Γ3; remember lD as i eqn:Ei;
    induction H as [G i HG | G i g HG Hg | G i Γ1 Γ2 A1 A2 l1 l2 H12 IH HA1 HA12 Hl12];
    subst; intros Γ3 H23; [exact H23 | exact H23 |].
  inversion H23; subst.
  apply eqc_ext; [now apply IH | exact HA1 | | eapply lequiv_trans; eassumption].
  eapply eqty_trans; [exact HA12|].
  eapply eqty_lconv; [|exact Hl12].
  match goal with Hq : eq_ty G lD Γ2 A2 _ _ |- _ => exact (ctxconv_eqty (i := lD) (eqctx_sym_D H12) eq_refl Hq) end.
Qed.
