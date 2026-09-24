(** * Related local substitutions and their composition (07a:52)

    [VSub G Γ δ δ' Δ] ([δ ≈ δ' : Γ → Δ]): composed with related
    substitutions into [Γ], [δ] and [δ'] give related substitutions into
    [Δ].  Built from the validity of their entries and of [Δ]. *)
From DeLaM.Validity Require Export CtxRel.

Section SubstV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Definition VSub (G : gctx) (Γ : ctx) (δ δ' : lsub) (Δ : ctx) : Prop :=
  forall Θ d d', SubRel G Γ Θ d d' -> SubRel G Δ Θ δ[d] δ'[d'].

Lemma tail_ldrop1 {δ Δ Γ A l} : lsub_tail δ (Δ ,, A @ l) Γ -> lsub_tail (ldrop 1 δ) Δ Γ.
Proof.
  intros [Ht Hl]; split; [exact Ht|]. intros n. rewrite llk_ldrop.
  replace (1 + (clen Δ + n)) with (clen (Δ ,, A @ l) + n) by (cbn; lia). apply Hl.
Qed.

Lemma VSub_intro {G} : forall Δ Γ δ δ',
  CtxRel G Δ Δ -> lsub_tail δ Δ Γ -> lsub_tail δ' Δ Γ -> LK dnftm δ -> LK dnftm δ' ->
  (forall n A k, in_ctx Δ n A k -> VTm G Γ (llk δ n) (llk δ' n) A[δ] k) ->
  VSub G Γ δ δ' Δ.
Proof.
  induction Δ as [| g | Δ IH A l]; intros Γ δ δ' HΔ Ht Ht' Nδ Nδ' Hv Θ d d' Hd.
  1-2: destruct (SubRel_dnf _ _ _ _ _ Hd) as [Nd Nd']; destruct (SubRel_tail _ _ _ _ _ Hd) as [Td Td'];
    cbn [SubRel]; refine (conj (SubRel_ctx Hd) (conj _ (conj _ (conj _ _))));
    try (intros n; rewrite llk_lcomp; apply subst_dnf; auto);
    eapply tail_lcomp; eassumption.
  cbn [CtxRel] in HΔ. destruct HΔ as (HΔ & _ & HA & _).
  assert (Hdrop : SubRel G Δ Θ (ldrop 1 δ)[d] (ldrop 1 δ')[d']).
  { apply (IH Γ); [exact HΔ | exact (tail_ldrop1 Ht) | exact (tail_ldrop1 Ht')
                  | intros n; rewrite llk_ldrop; apply Nδ | intros n; rewrite llk_ldrop; apply Nδ'
                  | | exact Hd].
    intros n A0 k Hin. rewrite !llk_ldrop, <- shift_subst_ty. exact (Hv _ _ _ (in_there _ _ _ _ _ _ Hin)). }
  cbn [SubRel]. split.
  - refine (SubRel_ext _ _ _ _ _ _ _ _ _ Hdrop); intros n; rewrite llk_ldrop, !llk_lcomp, llk_ldrop;
      reflexivity.
  - pose proof (Hv _ _ _ (in_here Δ A l) _ _ _ Hd) as X.
    rewrite shift_subst_ty in X. rewrite !llk_lcomp.
    assert (E1 : forall e f, A[ldrop 1 e][f] = A[ldrop 1 e[f]])
      by (intros; apply subst_subst_ty; intros n; now rewrite !llk_ldrop, llk_lcomp).
    rewrite !E1 in X.
    assert (E2 : forall e f, A[(ldrop 1 e)[f]] = A[ldrop 1 e[f]])
      by (intros; apply subst_ext_ty; intros n; now rewrite !llk_ldrop, !llk_lcomp, llk_ldrop).
    (* the right-hand type: through the validity of [A] *)
    eapply LRtm_irrel_r; [exact X|].
    pose proof (HA _ _ _ Hdrop) as Y. rewrite !E2 in Y. exact Y.
Qed.

End SubstV.
