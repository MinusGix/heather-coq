(** * Related global substitutions after a global weakening

    [σ] followed by [γ : G'' ≤ G'] is again a global substitution
    ([gsub_wk]), and related substitutions stay related.  So validity with
    global substitutions can be proved without its global-weakening
    quantifier ([VTyS_intro_loc]/[VTmS_intro_loc]). *)
From DeLaM.Validity Require Export GSubRel.

#[local] Existing Instance LR_P.

(** [σ] followed by [γ]; literally [σ] at the identity weakening, as
    [x⟦gwk_id⟧] is literally [x]. *)
Definition gsub_wk (σ : gsub) (γ : gweak) : gsub :=
  match γ with gwk_id => σ | _ => fun n => goren (σ n) γ end.

Lemma gsub_wk_ne σ γ n : γ <> gwk_id -> gsub_wk σ γ n = goren (σ n) γ.
Proof. destruct γ; [congruence | reflexivity ..]. Qed.

Lemma gwa_gsubst_ty (T : ty) σ γ : T⦃σ⦄⟦γ⟧ = T⦃gsub_wk σ γ⦄.
Proof. destruct γ; [reflexivity | apply gren_gsubst_ty; reflexivity ..]. Qed.
Lemma gwa_gsubst_tm (t : tm) σ γ : t⦃σ⦄⟦γ⟧ = t⦃gsub_wk σ γ⦄.
Proof. destruct γ; [reflexivity | apply gren_gsubst_tm; reflexivity ..]. Qed.
Lemma gwa_gsubst_ctx (Γ : ctx) σ γ : Γ⦃σ⦄⟦γ⟧ = Γ⦃gsub_wk σ γ⦄.
Proof. destruct γ; [reflexivity | apply gren_gsubst_ctx; reflexivity ..]. Qed.

Lemma gdecl_gsubst_wk D σ γ : γ <> gwk_id -> gdecl_ren (gdecl_gsubst D σ) γ = gdecl_gsubst D (gsub_wk σ γ).
Proof.
  intros Hγ. destruct D; cbn [gdecl_gsubst gdecl_ren]; f_equal; try reflexivity;
    first [apply gren_gsubst_ctx | apply gren_gsubst_ty | apply gren_gsubst_tm]; intros; apply gsub_wk_ne, Hγ.
Qed.

Lemma gsub_wf_wk {G'' G' G γ σ} : [ G' ⊢ σ : G ] -> gwk_ok γ G'' G' -> [ ⊢ G'' ] -> γ <> gwk_id ->
  [ G'' ⊢ gsub_wk σ γ : G ].
Proof.
  intros [Hg Hn Hv] Hγ HG Hne. constructor; [exact HG | intros n; rewrite gsub_wk_ne by exact Hne; apply dnfo_goren |].
  intros n D Hin. rewrite <- gdecl_gsubst_wk, gsub_wk_ne by exact Hne.
  destruct G'' as [L'' Ψ''].
  exact (gobj_wf_gwk _ _ _ γ _ _ (Hv _ _ Hin) (proj2 Hγ) (proj1 Hγ) HG).
Qed.

(** Level growth of the target (M3_DESIGN.md E14). *)
Lemma gobj_wf_grow {G'' G' o D} : gwk_ok gwk_id G'' G' -> [ ⊢ G'' ] -> gobj_wf G' o D -> gobj_wf G'' o D.
Proof.
  intros Hγ HG. pose proof (gwk_ok_id_inv Hγ) as EG.
  destruct D, o; cbn [gobj_wf]; try tauto.
  - rewrite EG. unfold gctx_var; cbn. tauto.
  - intros H. exact (gwa_ctx (γ := gwk_id) Hγ HG H).
  - intros (i' & Hi' & Hin). exists i'; split; [exact Hi' | rewrite EG; exact Hin].
  - intros H. exact (gwa_ty (γ := gwk_id) Hγ HG H).
  - intros (i' & Hi' & Hin). exists i'; split; [exact Hi' | rewrite EG; exact Hin].
  - intros H. exact (gwa_tm (γ := gwk_id) Hγ HG H).
  - intros Hin. rewrite EG; exact Hin.
Qed.

Lemma gsub_wf_grow {G'' G' G σ} : [ G' ⊢ σ : G ] -> gwk_ok gwk_id G'' G' -> [ ⊢ G'' ] -> [ G'' ⊢ σ : G ].
Proof.
  intros [Hg Hn Hv] Hγ HG. constructor; [exact HG | exact Hn |].
  intros n D Hin. exact (gobj_wf_grow Hγ HG (Hv _ _ Hin)).
Qed.

Section GSubRelW.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation GSubRel := (GSubRel EP EM).

Lemma GObjRel_gwk {G'' G' D o o' γ} : gwk_ok γ G'' G' -> γ <> gwk_id ->
  GObjRel EP EM G' D o o' -> GObjRel EP EM G'' (gdecl_ren D γ) (goren o γ) (goren o' γ).
Proof.
  intros Hγ Hne. destruct D, o, o'; cbn [GObjRel gdecl_ren goren]; try tauto; try congruence;
    change (gren_ty ?x ?ξ) with (gren x ξ); change (gren_tm ?x ?ξ) with (gren x ξ).
  - intros (HP & HM). change (gcren ?x ?ξ) with (gren x ξ). rewrite <- !(gwa_gren γ) by exact Hne.
    split; eapply CtxRelG_gwk; eassumption.
  - intros (HE & HP & HM). refine (conj (fun Hi => proj1 leq_gren_all _ _ _ (HE Hi)) (conj _ _));
      rewrite <- !(gwa_gren γ) by exact Hne; apply (VTyG_gwk (G := G')); assumption.
  - intros (HE & HP & HM). refine (conj (proj1 (proj2 leq_gren_all) _ _ _ HE) (conj _ _));
      rewrite <- !(gwa_gren γ) by exact Hne; apply (VTmG_gwk (G := G')); assumption.
Qed.

Lemma GRel0_gwk {G'' G' G σ σ' γ} : gwk_ok γ G'' G' -> γ <> gwk_id ->
  GRel0 EP EM G' G σ σ' -> GRel0 EP EM G'' G (gsub_wk σ γ) (gsub_wk σ' γ).
Proof.
  intros Hγ Hne H n D Hin. rewrite <- gdecl_gsubst_wk, !gsub_wk_ne by exact Hne.
  exact (GObjRel_gwk Hγ Hne (H _ _ Hin)).
Qed.

Lemma GObjRel_grow {G'' G' D o o'} : gwk_ok gwk_id G'' G' ->
  GObjRel EP EM G' D o o' -> GObjRel EP EM G'' D o o'.
Proof.
  intros Hγ. pose proof (gwk_ok_id_inv Hγ) as EG.
  destruct D, o, o'; cbn [GObjRel]; try tauto; try congruence.
  - intros (HP & HM). split; (eapply (CtxRelG_gwk (γ := gwk_id)); [eassumption | exact Hγ]).
  - intros (HE & HP & HM). refine (conj HE (conj _ _)); (eapply (VTyG_gwk (γ := gwk_id) (G := G')); [eassumption | exact Hγ]).
  - intros (HE & HP & HM). refine (conj HE (conj _ _)); (eapply (VTmG_gwk (γ := gwk_id) (G := G')); [eassumption | exact Hγ]).
Qed.

Lemma GSubRel_wk {G'' G' G γ σ σ'} : GSubRel G' G σ σ' -> gwk_ok γ G'' G' -> [ ⊢ G'' ] ->
  GSubRel G'' G (gsub_wk σ γ) (gsub_wk σ' γ).
Proof.
  intros Hσ Hγ HG.
  assert (Hc : γ = gwk_id \/ γ <> gwk_id) by (destruct γ; [left; reflexivity | right; discriminate ..]).
  destruct Hσ as [HL Hl Hr H1 H2 H3].
  destruct Hc as [-> | Hne].
  - cbn. constructor.
    + exact (Nat.le_trans _ _ _ HL (proj1 Hγ)).
    + exact (gsub_wf_grow Hl Hγ HG).
    + exact (gsub_wf_grow Hr Hγ HG).
    + intros n D Hin; exact (GObjRel_grow Hγ (H1 _ _ Hin)).
    + intros n D Hin; exact (GObjRel_grow Hγ (H2 _ _ Hin)).
    + intros n D Hin; exact (GObjRel_grow Hγ (H3 _ _ Hin)).
  - constructor.
    + exact (Nat.le_trans _ _ _ HL (proj1 Hγ)).
    + exact (gsub_wf_wk Hl Hγ HG Hne).
    + exact (gsub_wf_wk Hr Hγ HG Hne).
    + exact (GRel0_gwk Hγ Hne H1).
    + exact (GRel0_gwk Hγ Hne H2).
    + exact (GRel0_gwk Hγ Hne H3).
Qed.

(** Validity with global substitutions, without global weakenings. *)
Section Intro.
Context {E : GenericEq} {LP : LRParams}.

Lemma VTyS_intro_loc {G Γ T T' l} :
  (forall G' σ σ', GSubRel G' G σ σ' -> @VTy E LP G' Γ⦃σ⦄ T⦃σ⦄ T'⦃σ'⦄ l) -> @VTyS EP EM E LP G Γ T T' l.
Proof.
  intros H G' σ σ' Hσ G'' γ Hγ Θ e e' He.
  pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG.
  rewrite !gwa_gsubst_ctx in He. rewrite !gwa_gsubst_ty.
  exact (H _ _ _ (GSubRel_wk Hσ Hγ HG) _ _ _ He).
Qed.

Lemma VTmS_intro_loc {G Γ t t' T l} :
  (forall G' σ σ', GSubRel G' G σ σ' -> @VTm E LP G' Γ⦃σ⦄ t⦃σ⦄ t'⦃σ'⦄ T⦃σ⦄ l) -> @VTmS EP EM E LP G Γ t t' T l.
Proof.
  intros H G' σ σ' Hσ G'' γ Hγ Θ e e' He.
  pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG.
  rewrite !gwa_gsubst_ctx in He. rewrite !gwa_gsubst_ty, !gwa_gsubst_tm.
  exact (H _ _ _ (GSubRel_wk Hσ Hγ HG) _ _ _ He).
Qed.

End Intro.

End GSubRelW.
