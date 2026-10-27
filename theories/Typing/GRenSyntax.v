(** * Syntax under global renaming

    The syntactic laws of global renaming that need no typing, split off
    [GWeakening] so that they build beside the typing metatheory instead
    of after it. *)
From DeLaM.Typing Require Export Context.

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
Lemma gren_single2_ty (M : ty) t q ξ : M[lsingle2 t q]⟪ξ⟫ = M⟪ξ⟫[lsingle2 t⟪ξ⟫ q⟪ξ⟫].
Proof. rewrite gren_subst_ty; reflexivity. Qed.
Lemma gren_lsucc_ty (M : ty) ξ : M[lsucc]⟪ξ⟫ = M⟪ξ⟫[lsucc].
Proof. rewrite gren_subst_ty; reflexivity. Qed.
Lemma gren_single3 (c a f h : tm) ξ : c[lsingle3 a f h]⟪ξ⟫ = c⟪ξ⟫[lsingle3 a⟪ξ⟫ f⟪ξ⟫ h⟪ξ⟫].
Proof. rewrite gren_subst; reflexivity. Qed.

(** The letbox body's type [M⟪↑⟫[box U^id/x]] under [⇑ξ]. *)
Lemma gren_letbox_ty (M : ty) b ξ : b⟪gupr ξ⟫ = b ->
  M⟪S⟫[lsingle b]⟪gupr ξ⟫ = M⟪ξ⟫⟪S⟫[lsingle b].
Proof.
  intros Hb. rewrite gren_single_ty, Hb. f_equal.
  rewrite !(gren_gren_ty _ _ _ (fun i => S (ξ i))); auto.
Qed.
Lemma gcren_shift_up (Γ : ctx) ξ : Γ⟪S⟫⟪gupr ξ⟫ = Γ⟪ξ⟫⟪S⟫.
Proof. rewrite !(gcren_gcren _ _ _ (fun i => S (ξ i))); auto. Qed.

(** η of the meta-functions (M5): the function weakened under the binder. *)
Lemma gren_shift_up_tm (t : tm) ξ : t⟪S⟫⟪gupr ξ⟫ = t⟪ξ⟫⟪S⟫.
Proof. rewrite !(gren_gren_tm _ _ _ (fun i => S (ξ i))); auto. Qed.

(** Letbox β under global renaming: [t'⦃o/U⦄⟪ξ⟫ = t'⟪⇑ξ⟫⦃o⟪ξ⟫/U⦄]. *)
Lemma gren_gsingle (t : tm) o ξ : t⦃gsingle o⦄⟪ξ⟫ = t⟪gupr ξ⟫⦃gsingle (goren o ξ)⦄.
Proof.
  cbn [gsubst gren GSubst_tm GRen_tm].
  rewrite (proj1 (proj2 gren_gsubst_all) _ _ _ (fun i => goren (gsingle o i) ξ)) by auto.
  symmetry; apply (proj1 (proj2 gsubst_gren_all)). intros [|i]; reflexivity.
Qed.
(** The instances of the meta-functions (M5). *)
Lemma gren_gsingle_ty (T : ty) o ξ : T⦃gsingle o⦄⟪ξ⟫ = T⟪gupr ξ⟫⦃gsingle (goren o ξ)⦄.
Proof.
  cbn [gsubst gren GSubst_ty GRen_ty].
  rewrite (proj1 gren_gsubst_all _ _ _ (fun i => goren (gsingle o i) ξ)) by auto.
  symmetry; apply (proj1 gsubst_gren_all). intros [|i]; reflexivity.
Qed.

(** The reducts commute with global renaming. *)
Lemma peelU_gren b l ξ : peelU b⟪ξ⟫ l = (peelU b l)⟪ξ⟫.
Proof. destruct b; cbn; auto. apply usubst_gren. Qed.
Lemma peelG_gren b o ξ : peelG b⟪ξ⟫ (goren o ξ) = (peelG b o)⟪ξ⟫.
Proof. destruct b; cbn; auto. symmetry; apply gren_gsingle. Qed.
Lemma peelL_gren b a ξ : peelL b⟪ξ⟫ a⟪ξ⟫ = (peelL b a)⟪ξ⟫.
Proof. destruct b; cbn; auto. symmetry; apply gren_single. Qed.
