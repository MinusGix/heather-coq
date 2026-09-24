(** * Related global substitutions and semantic global contexts
    (07a:250–420, M2_DESIGN.md "Validity with global substitutions")

    [GSubRel G' G σ σ']: [σ] and [σ'] are typed global substitutions from
    [G] to [G'] whose images are related pointwise: context variables to
    the same context variable, type and term bindings to the same global
    variable or to objects related by [⊩^{≥P}_P] in the left substituted
    context.  Validity is one-sided, so [σ] and [σ'] are also each related
    to themselves.  Symmetry needs the validity of the bindings' contexts
    and types ([GValid]), which is part of the fundamental theorem. *)
From DeLaM.Validity Require Export Payload.

#[local] Existing Instance LR_P.

Section GSubRel.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation VTyGP := (@VTyG EP LR_P).
Local Notation VTyGM := (@VTyG EM LR_P).
Local Notation VTmGP := (@VTmG EP LR_P).
Local Notation VTmGM := (@VTmG EM LR_P).

(** ** Related images *)

Definition GObjRel (G' : gctx) (D : gdecl) (o o' : gobj) : Prop :=
  match D, o, o' with
  | gdCtx, GId g, GId g' => g = g'
  | gdTy _ _ _, GId x, GId x' => x = x'
  | gdTy Δ _ l, GTy T, GTy T' => VTyGP G' Δ T T' l /\ VTyGM G' Δ T T' l
  | gdTm _ _ _ _, GId x, GId x' => x = x'
  | gdTm Δ _ A l, GTm t, GTm t' => VTmGP G' Δ t t' A l /\ VTmGM G' Δ t t' A l
  | _, _, _ => False
  end.

Definition GRel0 (G' G : gctx) (σ σ' : gsub) : Prop :=
  forall n D, in_gctx (gΨ G) n D -> GObjRel G' (gdecl_gsubst D σ) (σ n) (σ' n).

Record GSubRel (G' G : gctx) (σ σ' : gsub) : Prop := {
  gsr_L : gL G' = gL G ;
  gsr_wf_l : [ G' ⊢ σ : G ] ;
  gsr_wf_r : [ G' ⊢ σ' : G ] ;
  gsr_rel : GRel0 G' G σ σ' ;
  gsr_l : GRel0 G' G σ σ ;
  gsr_r : GRel0 G' G σ' σ'
}.

Lemma GSubRel_refl_l {G' G σ σ'} : GSubRel G' G σ σ' -> GSubRel G' G σ σ.
Proof. intros []; now constructor. Qed.
Lemma GSubRel_refl_r {G' G σ σ'} : GSubRel G' G σ σ' -> GSubRel G' G σ' σ'.
Proof. intros []; now constructor. Qed.

(** The universe context is shared, as the global substitution lemma
    requires. *)
Lemma GSubRel_to {G' G σ σ'} : GSubRel G' G σ σ' -> G' = gwk_to G (gΨ G').
Proof.
  intros H. pose proof (gsr_L _ _ _ _ H) as HL. destruct G' as [L' Ψ']; cbn in HL.
  unfold gwk_to; cbn. now rewrite HL.
Qed.

(** ** Restriction to a prefix of the global context *)

Definition gsub_tl (σ : gsub) : gsub := fun n => σ (S n).

Lemma gdecl_gsubst_tl D σ : gdecl_gsubst (gdecl_ren D S) σ = gdecl_gsubst D (gsub_tl σ).
Proof.
  destruct D; unfold gdecl_gsubst, gdecl_ren; f_equal;
    first [reflexivity | apply gsubst_gren_ctx | apply gsubst_gren_ty]; intros; reflexivity.
Qed.

Lemma gsub_wf_tl {G' L D Ψ σ} : [ G' ⊢ σ : mkG L (D :: Ψ) ] -> [ G' ⊢ gsub_tl σ : mkG L Ψ ].
Proof.
  intros [Hg Hn Hv]; constructor; [exact Hg | intros n; apply Hn |].
  intros n D0 Hin. rewrite <- gdecl_gsubst_tl. exact (Hv _ _ (ing_there _ _ _ _ Hin)).
Qed.

Lemma GRel0_tl {G' L D Ψ σ σ'} : GRel0 G' (mkG L (D :: Ψ)) σ σ' ->
  GRel0 G' (mkG L Ψ) (gsub_tl σ) (gsub_tl σ').
Proof. intros H n D0 Hin. rewrite <- gdecl_gsubst_tl. exact (H _ _ (ing_there _ _ _ _ Hin)). Qed.

Lemma GSubRel_tl {G' L D Ψ σ σ'} : GSubRel G' (mkG L (D :: Ψ)) σ σ' ->
  GSubRel G' (mkG L Ψ) (gsub_tl σ) (gsub_tl σ').
Proof.
  intros [HL H1 H2 H3 H4 H5]; constructor;
    [exact HL | exact (gsub_wf_tl H1) | exact (gsub_wf_tl H2) | exact (GRel0_tl H3)
    | exact (GRel0_tl H4) | exact (GRel0_tl H5)].
Qed.

(** ** Validity with global substitutions (one-sided, as locally) *)

Section Valid.
Context {E : GenericEq} {LP : LRParams}.

Definition VCtxS (G : gctx) (Γ : ctx) : Prop :=
  forall G' σ σ', GSubRel G' G σ σ' -> @CtxRelG E LP G' Γ⦃σ⦄ Γ⦃σ'⦄.
Definition VTyS (G : gctx) (Γ : ctx) (T T' : ty) (l : lvl) : Prop :=
  forall G' σ σ', GSubRel G' G σ σ' -> @VTyG E LP G' Γ⦃σ⦄ T⦃σ⦄ T'⦃σ'⦄ l.
Definition VTmS (G : gctx) (Γ : ctx) (t t' : tm) (T : ty) (l : lvl) : Prop :=
  forall G' σ σ', GSubRel G' G σ σ' -> @VTmG E LP G' Γ⦃σ⦄ t⦃σ⦄ t'⦃σ'⦄ T⦃σ⦄ l.

End Valid.

(** ** Semantic global contexts: the bindings' contexts and types are
    valid at layer P, at both instances *)

Definition DValid (G : gctx) (D : gdecl) : Prop :=
  match D with
  | gdCtx => True
  | gdTy Δ _ _ => @VCtxS EP LR_P G Δ /\ @VCtxS EM LR_P G Δ
  | gdTm Δ _ A l =>
      @VCtxS EP LR_P G Δ /\ @VCtxS EM LR_P G Δ /\ @VTyS EP LR_P G Δ A A l /\ @VTyS EM LR_P G Δ A A l
  end.

Definition GValid (G : gctx) : Prop := forall n D, in_gctx (gΨ G) n D -> DValid G D.

Lemma DValid_tl {L D0 Ψ D} : DValid (mkG L Ψ) D -> DValid (mkG L (D0 :: Ψ)) (gdecl_ren D S).
Proof.
  assert (Hc : forall E, forall Δ : ctx, @VCtxS E LR_P (mkG L Ψ) Δ -> @VCtxS E LR_P (mkG L (D0 :: Ψ)) Δ⟪S⟫)
    by (intros E Δ H G' σ σ' Hσ; rewrite !(gsubst_gren_ctx _ _ _ (gsub_tl _)) by reflexivity;
        exact (H _ _ _ (GSubRel_tl Hσ))).
  assert (Ht : forall E, forall Δ A l, @VTyS E LR_P (mkG L Ψ) Δ A A l ->
                 @VTyS E LR_P (mkG L (D0 :: Ψ)) Δ⟪S⟫ A⟪S⟫ A⟪S⟫ l)
    by (intros E Δ A l H G' σ σ' Hσ;
        rewrite !(gsubst_gren_ctx _ _ _ (gsub_tl _)), !(gsubst_gren_ty _ _ _ (gsub_tl _)) by reflexivity;
        exact (H _ _ _ (GSubRel_tl Hσ))).
  destruct D; cbn; intuition auto.
Qed.

(** ** Symmetry *)

Lemma GObjRel_sym {G' G D σ σ' n} : GValid G -> GSubRel G' G σ σ' -> in_gctx (gΨ G) n D ->
  GObjRel G' (gdecl_gsubst D σ) (σ n) (σ' n) -> GObjRel G' (gdecl_gsubst D σ') (σ' n) (σ n).
Proof.
  intros HG Hσ Hin. pose proof (HG _ _ Hin) as HD.
  destruct D as [| Δ i l | Δ i A l]; cbn in HD |- *;
    destruct (σ n), (σ' n); cbn; try tauto; try congruence.
  - destruct HD as [HP HM]. intros [XP XM].
    exact (conj (VTyG_transport (HP _ _ _ Hσ) (VTyG_sym XP)) (VTyG_transport (HM _ _ _ Hσ) (VTyG_sym XM))).
  - destruct HD as (HP & HM & HAP & HAM). intros [XP XM]. split.
    + apply (VTmG_transport (HP _ _ _ Hσ)) in XP.
      eapply VTmG_conv; [exact (VTmG_sym XP)|].
      apply VTyG_sym, (VTyG_transport (HP _ _ _ Hσ)), (HAP _ _ _ Hσ).
    + apply (VTmG_transport (HM _ _ _ Hσ)) in XM.
      eapply VTmG_conv; [exact (VTmG_sym XM)|].
      apply VTyG_sym, (VTyG_transport (HM _ _ _ Hσ)), (HAM _ _ _ Hσ).
Qed.

Lemma GSubRel_sym {G' G σ σ'} : GValid G -> GSubRel G' G σ σ' -> GSubRel G' G σ' σ.
Proof.
  intros HG Hσ.
  constructor; [exact (gsr_L _ _ _ _ Hσ) | exact (gsr_wf_r _ _ _ _ Hσ) | exact (gsr_wf_l _ _ _ _ Hσ)
               | | exact (gsr_r _ _ _ _ Hσ) | exact (gsr_l _ _ _ _ Hσ)].
  intros n D Hin. exact (GObjRel_sym HG Hσ Hin (gsr_rel _ _ _ _ Hσ _ _ Hin)).
Qed.

End GSubRel.
