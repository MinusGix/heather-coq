(** * Related global substitutions and semantic global contexts
    (07a:250–420, M2_DESIGN.md "Validity with global substitutions")

    [GSubRel G' G σ σ']: [σ] and [σ'] are typed global substitutions from
    [G] to [G'] whose images are related pointwise: context variables to
    the same context variable, type and term bindings to the same global
    variable or to objects related by [⊩^{≥P}_P] in the left substituted
    context; the images of static bindings (layers C and V) are moreover
    equal (07a:390), as boxed code is equal only to itself.  Validity is one-sided, so [σ] and [σ'] are also each related
    to themselves.  Symmetry needs the validity of the bindings' contexts
    and types ([GValid]), which is part of the fundamental theorem. *)
From DeLaM.Typing Require Export GSubstitution GStatic.
From DeLaM.Validity Require Export Payload PiComp Natrec Id.

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
  (* a context variable may go to related contexts (M3_DESIGN.md E9) *)
  | gdCtx, GCtx Δ, GCtx Δ' => @CtxRelG EP LR_P G' Δ Δ' /\ @CtxRelG EM LR_P G' Δ Δ'
  | gdTy _ _ _, GId x, GId x' => x = x'
  (* static images are compared up to level equivalence (E11) *)
  | gdTy Δ i l, GTy T, GTy T' => (lle i lC -> ty_leq T T') /\ VTyGP G' Δ T T' l /\ VTyGM G' Δ T T' l
  | gdTm _ _ _ _, GId x, GId x' => x = x'
  | gdTm Δ _ A l, GTm t, GTm t' => tm_leq t t' /\ VTmGP G' Δ t t' A l /\ VTmGM G' Δ t t' A l
  (* a definition only to the same definition (M9_DESIGN.md) *)
  | gdDef _ _ _ _, GId x, GId x' => x = x'
  | _, _, _ => False
  end.

Definition GRel0 (G' G : gctx) (σ σ' : gsub) : Prop :=
  forall n D, in_gctx (gΨ G) n D -> GObjRel G' (gdecl_gsubst D σ) (σ n) (σ' n).

Record GSubRel (G' G : gctx) (σ σ' : gsub) : Prop := {
  gsr_L : gL G <= gL G' ;   (* the target may have more levels (M3_DESIGN.md E14) *)
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



(** Related substitutions agree on static bindings up to level
    equivalence, so they send static code to level-equivalent code
    ([static_gsubst]). *)
Lemma GSubRel_agree {G' G σ σ'} : GSubRel G' G σ σ' -> gsub_agree G σ σ'.
Proof.
  intros Hσ n D Hin HS. pose proof (gsr_rel _ _ _ _ Hσ _ _ Hin) as R.
  destruct D; cbn in R, HS; destruct (σ n), (σ' n); cbn in R |- *; try contradiction; try congruence.
  - exact (proj1 R HS).
  - exact (proj1 R).
Qed.

(** ** Restriction to a prefix of the global context *)

Definition gsub_tl (σ : gsub) : gsub := fun n => σ (S n).

Lemma gdecl_gsubst_tl D σ : gdecl_gsubst (gdecl_ren D S) σ = gdecl_gsubst D (gsub_tl σ).
Proof.
  destruct D; unfold gdecl_gsubst, gdecl_ren; f_equal;
    first [reflexivity | apply gsubst_gren_ctx | apply gsubst_gren_ty | apply gsubst_gren_tm]; intros; reflexivity.
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
  (* as a term binding; the body's validity comes with each occurrence (M9_DESIGN.md N1) *)
  | gdDef Δ A l _ =>
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

Lemma GValid_nil L : GValid (mkG L nil).
Proof. intros n D Hin; inversion Hin. Qed.

Lemma GValid_ext {L Ψ D} : GValid (mkG L Ψ) -> DValid (mkG L Ψ) D -> GValid (mkG L (D :: Ψ)).
Proof.
  intros HG HD n D' Hin; inversion Hin; subst; apply DValid_tl; [exact HD |].
  match goal with Hm : in_gctx Ψ _ _ |- _ => exact (HG _ _ Hm) end.
Qed.

(** ** Symmetry *)

Lemma GObjRel_sym {G' G D σ σ' n} : GValid G -> GSubRel G' G σ σ' -> in_gctx (gΨ G) n D ->
  GObjRel G' (gdecl_gsubst D σ) (σ n) (σ' n) -> GObjRel G' (gdecl_gsubst D σ') (σ' n) (σ n).
Proof.
  intros HG Hσ Hin. pose proof (HG _ _ Hin) as HD.
  destruct D as [| Δ i l | Δ i A l | Δ A l t0]; cbn in HD |- *;
    destruct (σ n), (σ' n); cbn; try tauto; try congruence;
    try (intros [XP XM]; split; apply CtxRelG_sym; assumption).
  - destruct HD as [HP HM]. intros (XE & XP & XM).
    refine (conj (fun Hi => ty_leq_sym _ _ (XE Hi)) (conj _ _));
      [exact (VTyG_transport (HP _ _ _ Hσ) (VTyG_sym XP)) | exact (VTyG_transport (HM _ _ _ Hσ) (VTyG_sym XM))].
  - destruct HD as (HP & HM & HAP & HAM). intros (XE & XP & XM). split; [exact (tm_leq_sym _ _ XE) | split].
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
