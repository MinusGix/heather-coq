(** * The universe substitution algebra (M3)

    Universe substitution [x[φ]ᵤ] replaces level variables by levels. It
    traverses everything (box contents included) and changes only level
    positions. As for the other operations: one mutual induction per law,
    with the lookup lemmas for the stored local substitutions. *)
From Coq Require Import Arith Lia.
From DeLaM.Syntax Require Export GSubst.

#[export] Hint Resolve uup_ext uup_uupr uup_lvren uup_lvsubst uup_id : subst.
#[export] Hint Resolve uupn_ext uupn_uuprn uupn_lvren uupn_lvsubst uupn_id : subst.
#[export] Hint Resolve lvsubst_ext lvren_lvsubst lvsubst_lvren lvsubst_lvsubst : subst.

(** ** Extensionality, commutation with the local and global renamings *)

Lemma usubst_ext_all :
  let Pty T := forall φ φ', (forall n, φ n = φ' n) -> usubst_ty T φ = usubst_ty T φ' in
  let Ptm t := forall φ φ', (forall n, φ n = φ' n) -> usubst_tm t φ = usubst_tm t φ' in
  let Pctx Γ := forall φ φ', (forall n, φ n = φ' n) -> ucsubst Γ φ = ucsubst Γ φ' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof. syn_start3; try lk_cases; law_auto. Qed.

Lemma usubst_ren_all :
  let Pty T := forall r φ, usubst_ty (ren_ty T r) φ = ren_ty (usubst_ty T φ) r in
  let Ptm t := forall r φ, usubst_tm (ren_tm t r) φ = ren_tm (usubst_tm t φ) r in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof. syn_start; try lk_cases; law_auto. Qed.

Lemma usubst_gren_all :
  let Pty T := forall ξ φ, usubst_ty (gren_ty T ξ) φ = gren_ty (usubst_ty T φ) ξ in
  let Ptm t := forall ξ φ, usubst_tm (gren_tm t ξ) φ = gren_tm (usubst_tm t φ) ξ in
  let Pctx Γ := forall ξ φ, ucsubst (gcren Γ ξ) φ = gcren (ucsubst Γ φ) ξ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof. syn_start3; try lk_cases; law_auto. Qed.

(** ** Composition with universe renaming and substitution *)

Lemma uren_usubst_all :
  let Pty T := forall ρ φ φ', (forall n, φ' n = φ (ρ n)) -> usubst_ty (uren_ty T ρ) φ = usubst_ty T φ' in
  let Ptm t := forall ρ φ φ', (forall n, φ' n = φ (ρ n)) -> usubst_tm (uren_tm t ρ) φ = usubst_tm t φ' in
  let Pctx Γ := forall ρ φ φ', (forall n, φ' n = φ (ρ n)) -> ucsubst (ucren Γ ρ) φ = ucsubst Γ φ' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof. syn_start3; try lk_cases; law_auto. Qed.

Lemma usubst_uren_all :
  let Pty T := forall φ ρ φ', (forall n, φ' n = lvren (φ n) ρ) -> uren_ty (usubst_ty T φ) ρ = usubst_ty T φ' in
  let Ptm t := forall φ ρ φ', (forall n, φ' n = lvren (φ n) ρ) -> uren_tm (usubst_tm t φ) ρ = usubst_tm t φ' in
  let Pctx Γ := forall φ ρ φ', (forall n, φ' n = lvren (φ n) ρ) -> ucren (ucsubst Γ φ) ρ = ucsubst Γ φ' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof. syn_start3; try lk_cases; law_auto. Qed.

Lemma usubst_usubst_all :
  let Pty T := forall φ ψ θ, (forall n, θ n = lvsubst (φ n) ψ) -> usubst_ty (usubst_ty T φ) ψ = usubst_ty T θ in
  let Ptm t := forall φ ψ θ, (forall n, θ n = lvsubst (φ n) ψ) -> usubst_tm (usubst_tm t φ) ψ = usubst_tm t θ in
  let Pctx Γ := forall φ ψ θ, (forall n, θ n = lvsubst (φ n) ψ) -> ucsubst (ucsubst Γ φ) ψ = ucsubst Γ θ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof. syn_start3; try lk_cases; law_auto. Qed.

Lemma uren_as_usubst_all :
  let Pty T := forall ρ φ, (forall n, φ n = lvar (ρ n)) -> uren_ty T ρ = usubst_ty T φ in
  let Ptm t := forall ρ φ, (forall n, φ n = lvar (ρ n)) -> uren_tm t ρ = usubst_tm t φ in
  let Pctx Γ := forall ρ φ, (forall n, φ n = lvar (ρ n)) -> ucren Γ ρ = ucsubst Γ φ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  assert (Hl : forall l ρ φ, (forall n, φ n = lvar (ρ n)) -> lvren l ρ = lvsubst l φ).
  { intros; now apply lvren_as_lvsubst. }
  syn_start3; try lk_cases; cbn; try solve [f_equal; eauto using uup_as, uupn_as].
  all: f_equal; try lsub_eq; try (apply map_ext; intros); eauto using uup_as, uupn_as.
Qed.

Definition usubst_ren_tm t := proj1 (proj2 usubst_ren_all) t.
Definition usubst_gren_tm t := proj1 (proj2 usubst_gren_all) t.
Definition uren_usubst_tm t := proj1 (proj2 uren_usubst_all) t.
Definition usubst_uren_tm t := proj1 (proj2 usubst_uren_all) t.

(** ** Distribution over local substitution *)

Lemma llift_usubst d d' φ : (forall n, llk d' n = usubst_tm (llk d n) φ) ->
  forall n, llk (llift d') n = usubst_tm (llk (llift d) n) φ.
Proof. intros H [|n]; rewrite !llk_llift; auto. rewrite H. symmetry; apply usubst_ren_tm. Qed.
Lemma gwk_usubst d d' φ : (forall n, llk d' n = usubst_tm (llk d n) φ) ->
  forall n, llk (gwk d') n = usubst_tm (llk (gwk d) n) φ.
Proof. intros H n; unfold gwk; rewrite !llk_glren, H. symmetry; apply usubst_gren_tm. Qed.
Lemma uwk_usubst d d' φ : (forall n, llk d' n = usubst_tm (llk d n) φ) ->
  forall n, llk (uwk d') n = usubst_tm (llk (uwk d) n) (uup φ).
Proof.
  intros H n; unfold uwk; rewrite !llk_ulren, H.
  rewrite (usubst_uren_tm _ _ _ (fun m => lvren (φ m) S)) by reflexivity.
  symmetry; apply uren_usubst_tm; reflexivity.
Qed.
#[export] Hint Resolve llift_usubst gwk_usubst uwk_usubst : subst.
Lemma uwkn_usubst k d d' φ : (forall n, llk d' n = usubst_tm (llk d n) φ) ->
  forall n, llk (uwkn k d') n = usubst_tm (llk (uwkn k d) n) (uupn k φ).
Proof. intros H; unfold uwkn, uupn; induction k; [assumption | apply uwk_usubst; assumption]. Qed.
#[export] Hint Resolve uwkn_usubst : subst.

Lemma usubst_subst_all :
  let Pty T := forall d d' φ, (forall n, llk d' n = usubst_tm (llk d n) φ) ->
               usubst_ty (subst_ty T d) φ = subst_ty (usubst_ty T φ) d' in
  let Ptm t := forall d d' φ, (forall n, llk d' n = usubst_tm (llk d n) φ) ->
               usubst_tm (subst_tm t d) φ = subst_tm (usubst_tm t φ) d' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases; law_auto.
  all: now rewrite H.
Qed.
Definition usubst_subst_tm t := proj1 (proj2 usubst_subst_all) t.

(** ** Distribution over global substitution *)

Lemma gousubst_goren o φ ξ : gousubst (goren o ξ) φ = goren (gousubst o φ) ξ.
Proof.
  destruct o; cbn; f_equal.
  - apply (proj1 (proj2 (proj2 usubst_gren_all))).
  - apply (proj1 usubst_gren_all).
  - apply (proj1 (proj2 usubst_gren_all)).
Qed.
Lemma gousubst_gouren o φ : gousubst (gouren o S) (uup φ) = gouren (gousubst o φ) S.
Proof.
  destruct o; cbn; f_equal.
  - rewrite (proj1 (proj2 (proj2 usubst_uren_all)) _ _ _ (fun m => lvren (φ m) S)) by reflexivity.
    apply (proj1 (proj2 (proj2 uren_usubst_all))); reflexivity.
  - rewrite (proj1 usubst_uren_all _ _ _ (fun m => lvren (φ m) S)) by reflexivity.
    apply (proj1 uren_usubst_all); reflexivity.
  - rewrite (proj1 (proj2 usubst_uren_all) _ _ _ (fun m => lvren (φ m) S)) by reflexivity.
    apply (proj1 (proj2 uren_usubst_all)); reflexivity.
Qed.
Lemma gup_gousubst σ τ φ : (forall i, τ i = gousubst (σ i) φ) -> forall i, gup τ i = gousubst (gup σ i) φ.
Proof. intros H [|i]; cbn; auto. rewrite H. symmetry; apply gousubst_goren. Qed.
Lemma guwk_gousubst σ τ φ : (forall i, τ i = gousubst (σ i) φ) ->
  forall i, guwk τ i = gousubst (guwk σ i) (uup φ).
Proof. intros H i; unfold guwk; rewrite H. symmetry; apply gousubst_gouren. Qed.
#[export] Hint Resolve gup_gousubst guwk_gousubst : subst.
Lemma guwkn_gousubst k σ τ φ : (forall i, τ i = gousubst (σ i) φ) ->
  forall i, guwkn k τ i = gousubst (guwkn k σ i) (uupn k φ).
Proof. intros H; unfold guwkn, uupn; induction k; [assumption | apply guwk_gousubst; assumption]. Qed.
#[export] Hint Resolve guwkn_gousubst : subst.

Lemma pty_usubst o e φ : usubst_ty (pty o e) φ = pty (gousubst o φ) (ulsubst e φ).
Proof. destruct o; cbn; auto. apply (proj1 usubst_subst_all). intros; apply llk_ulsubst. Qed.
Lemma ptm_usubst o e φ : usubst_tm (ptm o e) φ = ptm (gousubst o φ) (ulsubst e φ).
Proof. destruct o; cbn; auto. apply (proj1 (proj2 usubst_subst_all)). intros; apply llk_ulsubst. Qed.
Lemma pdef_usubst o b e φ : usubst_tm (pdef o b e) φ = pdef (gousubst o φ) (usubst_tm b φ) (ulsubst e φ).
Proof. destruct o; try reflexivity; apply ptm_usubst. Qed.
Lemma pctx_usubst o φ : ucsubst (pctx o) φ = pctx (gousubst o φ).
Proof. destruct o; reflexivity. Qed.

Lemma usubst_gsubst_all :
  let Pty T := forall σ φ τ, (forall i, τ i = gousubst (σ i) φ) -> usubst_ty (gsubst_ty T σ) φ = gsubst_ty (usubst_ty T φ) τ in
  let Ptm t := forall σ φ τ, (forall i, τ i = gousubst (σ i) φ) -> usubst_tm (gsubst_tm t σ) φ = gsubst_tm (usubst_tm t φ) τ in
  let Pctx Γ := forall σ φ τ, (forall i, τ i = gousubst (σ i) φ) -> ucsubst (gcsubst Γ σ) φ = gcsubst (ucsubst Γ φ) τ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn; rewrite ?pty_usubst, ?ptm_usubst, ?pdef_usubst, ?pctx_usubst; law_auto.
Qed.

(** ** Identity (deep normal forms, since universe substitution enters boxes) *)

Lemma usubst_id_all :
  let Pty T := dnfty T -> forall φ, (forall n, φ n = lvar n) -> usubst_ty T φ = T in
  let Ptm t := dnftm t -> forall φ, (forall n, φ n = lvar n) -> usubst_tm t φ = t in
  let Pctx Γ := dnfctx Γ -> forall φ, (forall n, φ n = lvar n) -> ucsubst Γ φ = Γ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, dnfl d -> LK Ptm d).
Proof.
  assert (Hl : forall l φ, (forall n, φ n = lvar n) -> lvsubst l φ = l).
  { intros; now apply lvsubst_id. }
  syn_start3; try lk_cases_dnf; cbn in *; try tauto;
    try solve [f_equal; intuition eauto with subst].
  all: f_equal; repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: first
    [ (* a defined global's body *)
      match goal with IH : dnftm ?b -> _ |- _ ?b _ = ?b => apply IH; assumption end
    | apply l_canon; auto with nf; intros n;
      rewrite llk_ulsubst; match goal with IH : dnfl ?d -> LK _ ?d |- _ => apply IH end; auto with nf ].
Qed.

(** Universe substitution outputs are deep-normal (it never instantiates a
    global or local variable). *)
Lemma usubst_dnf_all :
  let Pty T := forall φ, dnfty (usubst_ty T φ) in
  let Ptm t := forall φ, dnftm (usubst_tm t φ) in
  let Pctx Γ := forall φ, dnfctx (ucsubst Γ φ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, forall φ, dnfl (ulsubst d φ)).
Proof.
  intros Pty Ptm Pctx; apply syn_ind; subst Pty Ptm Pctx; cbn beta; intros; try exact I;
    cbn; intuition auto using dnfl_lcons'.
Qed.

(** ** Exported laws, in notation form *)

Section ULaws.
Lemma usubst_ren_ty (T : ty) r φ : T⟨r⟩[φ]ᵤ = T[φ]ᵤ⟨r⟩.
Proof. apply (proj1 usubst_ren_all). Qed.
Lemma usubst_ren (t : tm) r φ : t⟨r⟩[φ]ᵤ = t[φ]ᵤ⟨r⟩.
Proof. apply (proj1 (proj2 usubst_ren_all)). Qed.
Lemma usubst_subst_ty (T : ty) d φ : T[d][φ]ᵤ = T[φ]ᵤ[d[φ]ᵤ].
Proof. apply (proj1 usubst_subst_all). intros; apply llk_ulsubst. Qed.
Lemma usubst_subst (t : tm) d φ : t[d][φ]ᵤ = t[φ]ᵤ[d[φ]ᵤ].
Proof. apply (proj1 (proj2 usubst_subst_all)). intros; apply llk_ulsubst. Qed.
Lemma usubst_gren_ty (T : ty) ξ φ : T⟪ξ⟫[φ]ᵤ = T[φ]ᵤ⟪ξ⟫.
Proof. apply (proj1 usubst_gren_all). Qed.
Lemma usubst_gren (t : tm) ξ φ : t⟪ξ⟫[φ]ᵤ = t[φ]ᵤ⟪ξ⟫.
Proof. apply (proj1 (proj2 usubst_gren_all)). Qed.
Lemma usubst_gren_ctx (Γ : ctx) ξ φ : Γ⟪ξ⟫[φ]ᵤ = Γ[φ]ᵤ⟪ξ⟫.
Proof. apply (proj1 (proj2 (proj2 usubst_gren_all))). Qed.
Lemma usubst_gsubst_ty (T : ty) σ φ : T⦃σ⦄[φ]ᵤ = T[φ]ᵤ⦃fun i => gousubst (σ i) φ⦄.
Proof. apply (proj1 usubst_gsubst_all); reflexivity. Qed.
Lemma usubst_gsubst (t : tm) σ φ : t⦃σ⦄[φ]ᵤ = t[φ]ᵤ⦃fun i => gousubst (σ i) φ⦄.
Proof. apply (proj1 (proj2 usubst_gsubst_all)); reflexivity. Qed.
Lemma usubst_gsubst_ctx (Γ : ctx) σ φ : Γ⦃σ⦄[φ]ᵤ = Γ[φ]ᵤ⦃fun i => gousubst (σ i) φ⦄.
Proof. apply (proj1 (proj2 (proj2 usubst_gsubst_all))); reflexivity. Qed.
Lemma usubst_usubst_ty (T : ty) φ ψ θ : (forall n, θ n = lvsubst (φ n) ψ) -> T[φ]ᵤ[ψ]ᵤ = T[θ]ᵤ.
Proof. apply (proj1 usubst_usubst_all). Qed.
Lemma usubst_usubst (t : tm) φ ψ θ : (forall n, θ n = lvsubst (φ n) ψ) -> t[φ]ᵤ[ψ]ᵤ = t[θ]ᵤ.
Proof. apply (proj1 (proj2 usubst_usubst_all)). Qed.
Lemma usubst_usubst_ctx (Γ : ctx) φ ψ θ : (forall n, θ n = lvsubst (φ n) ψ) -> Γ[φ]ᵤ[ψ]ᵤ = Γ[θ]ᵤ.
Proof. apply (proj1 (proj2 (proj2 usubst_usubst_all))). Qed.
Lemma usubst_id_ty (T : ty) φ : dnfty T -> (forall n, φ n = lvar n) -> T[φ]ᵤ = T.
Proof. intros; apply (proj1 usubst_id_all); auto. Qed.
Lemma usubst_id (t : tm) φ : dnftm t -> (forall n, φ n = lvar n) -> t[φ]ᵤ = t.
Proof. intros; apply (proj1 (proj2 usubst_id_all)); auto. Qed.
Lemma usubst_id_ctx (Γ : ctx) φ : dnfctx Γ -> (forall n, φ n = lvar n) -> Γ[φ]ᵤ = Γ.
Proof. intros; apply (proj1 (proj2 (proj2 usubst_id_all))); auto. Qed.
End ULaws.

Print Assumptions usubst_gsubst.
