(** * The global substitution lemma (05:1075)

    [G' ⊢ σ : Ψ] sends every binding of [Ψ] to an object typed in [G'] at
    the binding's layer (or to a variable of [G'] with the same binding).
    A context variable may be sent to a context variable or to a concrete
    context well formed at P (M3_DESIGN.md E9). A context ending in [g] then
    becomes its entries followed by the image: lengths grow by the image's
    length and the tail condition of typed local substitutions shifts
    ("tail expansion"). *)
From DeLaM.Typing Require Export RecGSubst.

(** ** Typed global substitutions *)

Definition gdecl_gsubst (D : gdecl) (σ : gsub) : gdecl :=
  match D with
  | gdCtx => gdCtx
  | gdTy Δ i l => gdTy Δ⦃σ⦄ i l
  | gdTm Δ i T l => gdTm Δ⦃σ⦄ i T⦃σ⦄ l
  end.

(** What a binding may be sent to. *)
Definition gobj_wf (G' : gctx) (o : gobj) (D : gdecl) : Prop :=
  match D, o with
  | gdCtx, GId j => gctx_var G' j
  | gdCtx, GCtx Δ0 => [ G' ; Δ0 ⊢[ lD ] ]
  | gdTy Δ i l, GId j => exists i', lle i' i /\ in_gctx (gΨ G') j (gdTy Δ i' l)
  | gdTy Δ i l, GTy T => [ G' ; Δ ⊢[ i ] T @ l ]
  | gdTm Δ i T l, GId j => exists i', lle i' i /\ in_gctx (gΨ G') j (gdTm Δ i' T l)
  | gdTm Δ i T l, GTm t => [ G' ; Δ ⊢[ i ] t : T @ l ]
  | _, _ => False
  end.

Record gsub_wf (G' : gctx) (σ : gsub) (G : gctx) : Prop := {
  gsw_glob : [ ⊢ G' ] ;
  gsw_dnf : forall n, dnfo (σ n) ;
  gsw_var : forall n D, in_gctx (gΨ G) n D -> gobj_wf G' (σ n) (gdecl_gsubst D σ)
}.

Notation "[ G' ⊢ σ : G ]" := (gsub_wf G' σ G) (at level 0, G', σ, G at level 50).

(** Context variables go to context variables. *)
Definition gsub_cvars (σ : gsub) (Γ : ctx) : Prop :=
  forall g, ctx_tail Γ = cvar g -> exists j, σ g = GId j.

(** ** Syntax under global substitution *)

Lemma gsubst_ren_ty' (A : ty) r σ : (A⟨r⟩)⦃σ⦄ = (A⦃σ⦄)⟨r⟩.
Proof. apply gsubst_ren_ty. Qed.

Lemma gcsubst_cext Γ A l σ : (Γ ,, A @ l)⦃σ⦄ = Γ⦃σ⦄ ,, A⦃σ⦄ @ l.
Proof. reflexivity. Qed.

Lemma in_ctx_gsubst Γ n T l σ : in_ctx Γ n T l -> in_ctx Γ⦃σ⦄ n T⦃σ⦄ l.
Proof. induction 1; rewrite gcsubst_cext, gsubst_ren_ty'; now constructor. Qed.

Lemma in_ctx_gsubst_inv Γ n T l σ : gsub_cvars σ Γ -> in_ctx Γ⦃σ⦄ n T l ->
  exists T0, in_ctx Γ n T0 l /\ T = T0⦃σ⦄.
Proof.
  revert n T; induction Γ as [| g | Γ IH A k]; intros n T Hc H.
  - inversion H.
  - destruct (Hc g eq_refl) as (j & Hj). cbn in H. rewrite Hj in H. inversion H.
  - inversion H; subst.
    + exists A⟨↑⟩; split; [constructor | symmetry; apply gsubst_ren_ty'].
    + match goal with Hm : in_ctx _ _ _ _ |- _ => destruct (IH _ _ Hc Hm) as (T0 & HT0 & ->) end.
      exists T0⟨↑⟩; split; [now constructor | symmetry; apply gsubst_ren_ty'].
Qed.

Lemma clen_gsubst Γ σ : gsub_cvars σ Γ -> clen Γ⦃σ⦄ = clen Γ.
Proof.
  induction Γ as [| g | Γ IH A k]; intros Hc; cbn; auto.
  destruct (Hc g eq_refl) as (j & ->); reflexivity.
Qed.
Lemma ctx_tail_gsubst Γ σ : gsub_cvars σ Γ -> ctx_tail Γ⦃σ⦄ = (ctx_tail Γ)⦃σ⦄.
Proof.
  induction Γ as [| g | Γ IH A k]; intros Hc; cbn; auto.
  destruct (Hc g eq_refl) as (j & Hj); cbn; rewrite Hj; reflexivity.
Qed.

Lemma lsub_tail_gsubst d Δ Γ σ : gsub_cvars σ Δ -> gsub_cvars σ Γ ->
  lsub_tail d Δ Γ -> lsub_tail d⦃σ⦄ Δ⦃σ⦄ Γ⦃σ⦄.
Proof.
  intros HΔ HΓ [Ht Hl]; split.
  - rewrite !ctx_tail_gsubst by assumption; now f_equal.
  - intros n; rewrite !clen_gsubst by assumption. cbn [gsubst GSubst_lsub].
    rewrite llk_glsubst, Hl; reflexivity.
Qed.

Lemma gsub_cvars_tail σ Γ Δ : ctx_tail Γ = ctx_tail Δ -> gsub_cvars σ Γ -> gsub_cvars σ Δ.
Proof. intros H Hc g Hg; apply Hc; congruence. Qed.

(** ** Tail expansion *)

Definition tlen (σ : gsub) (Γ : ctx) : nat :=
  match ctx_tail Γ with cvar g => clen (pctx (σ g)) | _ => 0 end.

Lemma tlen_ext σ Γ A l : tlen σ (Γ ,, A @ l) = tlen σ Γ.
Proof. reflexivity. Qed.

Lemma clen_gsubst' Γ σ : clen Γ⦃σ⦄ = clen Γ + tlen σ Γ.
Proof. induction Γ as [| g | Γ IH A k]; cbn; auto. Qed.
Lemma ctx_tail_gsubst' Γ σ : ctx_tail Γ⦃σ⦄ = ctx_tail ((ctx_tail Γ)⦃σ⦄).
Proof. induction Γ as [| g | Γ IH A k]; cbn; auto. Qed.

Lemma lsub_tail_gsubst' d Δ Γ σ : lsub_tail d Δ Γ -> lsub_tail d⦃σ⦄ Δ⦃σ⦄ Γ⦃σ⦄.
Proof.
  intros [Ht Hl]; split.
  - rewrite (ctx_tail_gsubst' Δ), (ctx_tail_gsubst' Γ); now rewrite Ht.
  - intros n; rewrite !clen_gsubst'. assert (E : tlen σ Δ = tlen σ Γ) by (unfold tlen; now rewrite Ht).
    rewrite E, <- !Nat.add_assoc. cbn [gsubst GSubst_lsub]. rewrite llk_glsubst, Hl; reflexivity.
Qed.

Lemma in_ctx_gsubst_tail Γ g σ m T l : ctx_tail Γ = cvar g -> in_ctx (pctx (σ g)) m T l ->
  in_ctx Γ⦃σ⦄ (clen Γ + m) T⟨rshift (clen Γ)⟩ l.
Proof.
  revert m T; induction Γ as [| g' | Γ IH A k]; intros m T Ht Hin; cbn in Ht; try discriminate.
  - injection Ht as ->. cbn. rewrite ren_id_ty by eauto using in_ctx_nf. exact Hin.
  - cbn [clen gsubst GSubst_ctx gcsubst]. change (gcsubst Γ σ) with Γ⦃σ⦄.
    replace (T⟨rshift (S (clen Γ))⟩) with (T⟨rshift (clen Γ)⟩⟨↑⟩)
      by (rewrite ren_ren_comp_ty; apply ren_ext_ty; intros n; rlk_simpl; lia).
    constructor. now apply IH.
Qed.

Lemma in_ctx_gsubst_inv' Γ n T l σ : in_ctx Γ⦃σ⦄ n T l ->
  (exists T0, in_ctx Γ n T0 l /\ T = T0⦃σ⦄) \/
  (exists g m T1, ctx_tail Γ = cvar g /\ n = clen Γ + m /\ in_ctx (pctx (σ g)) m T1 l /\ T = T1⟨rshift (clen Γ)⟩).
Proof.
  revert n T; induction Γ as [| g | Γ IH A k]; intros n T H.
  - inversion H.
  - right. exists g, n, T. cbn in *. repeat split; auto.
    symmetry; apply ren_id_ty; eauto using in_ctx_nf.
  - inversion H; subst.
    + left. exists A⟨↑⟩; split; [constructor | symmetry; apply gsubst_ren_ty'].
    + match goal with Hm : in_ctx _ _ _ _ |- _ => destruct (IH _ _ Hm) as
        [(T0 & HT0 & ->) | (g & m & T1 & Hg & -> & Hm1 & ->)] end.
      * left. exists T0⟨↑⟩; split; [now constructor | symmetry; apply gsubst_ren_ty'].
      * right. exists g, m, T1. cbn. repeat split; auto.
        rewrite ren_ren_comp_ty; apply ren_ext_ty; intros n; rlk_simpl; lia.
Qed.

(** The tail entries of [d⦃σ⦄] are variables of [Γ⦃σ⦄]'s image part. *)
Lemma tail_entry_ty d Δ Γ σ (T1 : ty) : lsub_tail d Δ Γ -> nfty T1 ->
  (T1⟨rshift (clen Δ)⟩)[d⦃σ⦄] = T1⟨rshift (clen Γ)⟩.
Proof.
  intros [_ Hl] HT. rewrite (ren_subst_ty _ _ _ (lshift (clen Γ))).
  - symmetry; apply ren_as_subst_ty. intros n; cbn; f_equal; lia.
  - intros n. cbn [gsubst GSubst_lsub rlk]. rewrite llk_glsubst, (Nat.add_comm n), Hl. cbn. f_equal; lia.
Qed.

(** An entry of a substitution [d⦃σ⦄] in the image part of its domain. *)
Lemma gs_tail_var d Δ Γ σ m : lsub_tail d Δ Γ -> llk d⦃σ⦄ (clen Δ + m) = var (clen Γ + m).
Proof. intros [_ Hl]. cbn [gsubst GSubst_lsub]. rewrite llk_glsubst, Hl; reflexivity. Qed.

Lemma gs_tail_entry G' i Γ Δ d σ g m T1 k :
  [ G' ; Γ⦃σ⦄ ⊢[ typeof i ] ] -> lsub_tail d Δ Γ -> ctx_tail Δ = cvar g ->
  in_ctx (pctx (σ g)) m T1 k ->
  [ G' ; Γ⦃σ⦄ ⊢[ i ] llk d⦃σ⦄ (clen Δ + m) : (T1⟨rshift (clen Δ)⟩)[d⦃σ⦄] @ k ].
Proof.
  intros HΓ Ht Hg Hm. rewrite (tail_entry_ty d Δ Γ σ T1 Ht (in_ctx_nf _ _ _ _ Hm)).
  rewrite (gs_tail_var d Δ Γ σ m Ht). apply wf_var; [exact HΓ|].
  apply (in_ctx_gsubst_tail Γ g); [|exact Hm]. rewrite <- (proj1 Ht); exact Hg.
Qed.

Lemma gs_tail_entry_eq G' i Γ Δ d d' σ g m T1 k :
  [ G' ; Γ⦃σ⦄ ⊢[ typeof i ] ] -> lsub_tail d Δ Γ -> lsub_tail d' Δ Γ -> ctx_tail Δ = cvar g ->
  in_ctx (pctx (σ g)) m T1 k ->
  [ G' ; Γ⦃σ⦄ ⊢[ i ] llk d⦃σ⦄ (clen Δ + m) ≅ llk d'⦃σ⦄ (clen Δ + m) : (T1⟨rshift (clen Δ)⟩)[d⦃σ⦄] @ k ].
Proof.
  intros HΓ Ht Ht' Hg Hm. rewrite (gs_tail_var d' Δ Γ σ m Ht'), <- (gs_tail_var d Δ Γ σ m Ht).
  apply eqtm_refl; eapply gs_tail_entry; eassumption.
Qed.

Lemma lle_D_compt i : compt i -> lle lD i.
Proof. intros [-> | ->]; unfold lle; cbn; lia. Qed.

(** Renaming then substitution, and back, in notation form. *)
Lemma gsubst_gren_ctx (Γ : ctx) ξ σ τ : (forall i, τ i = σ (ξ i)) -> Γ⟪ξ⟫⦃σ⦄ = Γ⦃τ⦄.
Proof. apply (proj1 (proj2 (proj2 gsubst_gren_all))). Qed.
Lemma gsubst_gren_ty (T : ty) ξ σ τ : (forall i, τ i = σ (ξ i)) -> T⟪ξ⟫⦃σ⦄ = T⦃τ⦄.
Proof. apply (proj1 gsubst_gren_all). Qed.
Lemma gsubst_gren_tm (t : tm) ξ σ τ : (forall i, τ i = σ (ξ i)) -> t⟪ξ⟫⦃σ⦄ = t⦃τ⦄.
Proof. apply (proj1 (proj2 gsubst_gren_all)). Qed.
Lemma gren_gsubst_ctx (Γ : ctx) σ ξ τ : (forall i, τ i = goren (σ i) ξ) -> Γ⦃σ⦄⟪ξ⟫ = Γ⦃τ⦄.
Proof. apply (proj1 (proj2 (proj2 gren_gsubst_all))). Qed.
Lemma gren_gsubst_ty (T : ty) σ ξ τ : (forall i, τ i = goren (σ i) ξ) -> T⦃σ⦄⟪ξ⟫ = T⦃τ⦄.
Proof. apply (proj1 gren_gsubst_all). Qed.
Lemma gren_gsubst_tm (t : tm) σ ξ τ : (forall i, τ i = goren (σ i) ξ) -> t⦃σ⦄⟪ξ⟫ = t⦃τ⦄.
Proof. apply (proj1 (proj2 gren_gsubst_all)). Qed.

(** Shifting past a binder commutes with [gup]. *)
Lemma gshift_up_ctx (Γ : ctx) σ : Γ⟪S⟫⦃gup σ⦄ = Γ⦃σ⦄⟪S⟫.
Proof.
  rewrite (gsubst_gren_ctx _ _ _ (fun i => goren (σ i) S)) by reflexivity.
  symmetry; now apply gren_gsubst_ctx.
Qed.
Lemma gshift_up_ty (T : ty) σ : T⟪S⟫⦃gup σ⦄ = T⦃σ⦄⟪S⟫.
Proof.
  rewrite (gsubst_gren_ty _ _ _ (fun i => goren (σ i) S)) by reflexivity.
  symmetry; now apply gren_gsubst_ty.
Qed.
Lemma gshift_up_tm (t : tm) σ : t⟪S⟫⦃gup σ⦄ = t⦃σ⦄⟪S⟫.
Proof.
  rewrite (gsubst_gren_tm _ _ _ (fun i => goren (σ i) S)) by reflexivity.
  symmetry; now apply gren_gsubst_tm.
Qed.

(** The binding lookups. *)
Lemma gdecl_gsubst_ren_up D σ : gdecl_gsubst (gdecl_ren D S) (gup σ) = gdecl_ren (gdecl_gsubst D σ) S.
Proof. destruct D; cbn; f_equal; auto using gshift_up_ctx, gshift_up_ty. Qed.

(** Well-formed contexts end in declared context variables. *)
Lemma wf_ctx_tail G i Γ g : [ G ; Γ ⊢[ i ] ] -> ctx_tail Γ = cvar g -> gctx_var G g.
Proof. induction 1; cbn; intros Ht; try discriminate; auto. now injection Ht as ->. Qed.

Lemma gctx_var_in G g : gctx_var G g -> in_gctx (gΨ G) g gdCtx.
Proof.
  unfold gctx_var. generalize (gΨ G) as Ψ; intros Ψ; revert g.
  induction Ψ as [|D Ψ IH]; intros [|g] H; cbn in H; try discriminate.
  - injection H as ->. exact (ing_here Ψ gdCtx).
  - exact (ing_there Ψ _ D g (IH g H)).
Qed.

(** ** Pushing a typed global substitution under one global binder *)

Lemma gobj_wf_gwk G' o D γ Ψ'' :
  gobj_wf G' o D -> gwk_wf γ Ψ'' (gΨ G') -> [ ⊢ gwk_to G' Ψ'' ] ->
  gobj_wf (gwk_to G' Ψ'') (goren o γ) (gdecl_ren D γ).
Proof.
  intros Ho Hγ Hg. destruct D, o; cbn in *; try contradiction.
  all: first
    [ eapply gctx_var_gwk; eauto
    | exact (proj1 (proj2 gweakening) _ _ _ Ho _ _ Hγ Hg)
    | exact (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ Ho _ _ Hγ Hg)
    | exact (proj1 (proj2 (proj2 (proj2 gweakening))) _ _ _ _ _ _ Ho _ _ Hγ Hg)
    | let i' := fresh "i'" in let Hi' := fresh "Hi'" in let Hin := fresh "Hin" in
      destruct Ho as (i' & Hi' & Hin); exists i'; split; [exact Hi'|];
      exact (in_gctx_gwk _ _ _ _ _ Hγ Hin) ].
Qed.

Lemma gsub_wf_up G' σ G D :
  [ G' ⊢ σ : G ] -> [ ⊢ gext G' (gdecl_gsubst D σ) ] ->
  [ gext G' (gdecl_gsubst D σ) ⊢ gup σ : gext G D ].
Proof.
  intros [Hg Hn Hv] Hg'. constructor; [exact Hg' | intros [|n]; cbn; auto using dnfo_goren |].
  intros n D0 Hin. inversion Hin as [Ψ0 D1 | Ψ0 D1 D2 m Hm]; subst; cbn [gup].
  - rewrite gdecl_gsubst_ren_up. destruct D; cbn.
    + reflexivity.
    + exists i; split; [apply lle_refl | exact (ing_here _ (gdTy _ _ _))].
    + exists i; split; [apply lle_refl | exact (ing_here _ (gdTm _ _ _ _))].
  - rewrite gdecl_gsubst_ren_up.
    exact (gobj_wf_gwk _ _ _ (gwk_step gwk_id) _ (Hv _ _ Hm)
             (gwkwf_step _ _ _ _ (gwkwf_id _)) Hg').
Qed.

(** ** Pushing a typed global substitution into the recursors' scopes *)

Lemma in_gctx_uren Ψ n D ρ : in_gctx Ψ n D ->
  in_gctx (map (fun D => gdecl_uren D ρ) Ψ) n (gdecl_uren D ρ).
Proof. induction 1; cbn; rewrite gdecl_ren_uren; now constructor. Qed.

Lemma in_gctx_uren_inv Ψ n D' ρ : in_gctx (map (fun D => gdecl_uren D ρ) Ψ) n D' ->
  exists D, in_gctx Ψ n D /\ D' = gdecl_uren D ρ.
Proof.
  revert n D'; induction Ψ as [|D0 Ψ IH]; intros n D' H; [inversion H|].
  change (in_gctx (gdecl_uren D0 ρ :: map (fun D => gdecl_uren D ρ) Ψ) n D') in H.
  inversion H; subst.
  - exists (gdecl_ren D0 S); split; [constructor | symmetry; apply gdecl_ren_uren].
  - match goal with Hm : in_gctx _ _ _ |- _ => destruct (IH _ _ Hm) as (D1 & HD1 & ->) end.
    exists (gdecl_ren D1 S); split; [now constructor | symmetry; apply gdecl_ren_uren].
Qed.

Lemma gdecl_gsubst_uren D n σ : gdnf σ ->
  gdecl_gsubst (gdecl_uren D (ush n)) (guwkn n σ) = gdecl_uren (gdecl_gsubst D σ) (ush n).
Proof.
  intros Hσ. assert (H : forall i, guwkn n σ i = gouren (σ i) (ush n)) by (intros; apply guwkn_lk, Hσ).
  destruct D; cbn; f_equal; try reflexivity; symmetry;
    first [ apply (proj1 (proj2 (proj2 uren_gsubst_all))); exact H
          | apply (proj1 uren_gsubst_all); exact H ].
Qed.

Lemma gsub_wf_uwkn n G' σ G : [ G' ⊢ σ : G ] -> [ gctx_uwk n G' ⊢ guwkn n σ : gctx_uwk n G ].
Proof.
  intros [Hg Hn Hv]. constructor; [now apply uwk_glob | now apply gdnf_guwkn |].
  intros m D' Hin. unfold gctx_uwk in Hin; cbn [gΨ] in Hin.
  destruct (in_gctx_uren_inv _ _ _ _ Hin) as (D & HD & ->).
  rewrite gdecl_gsubst_uren by exact Hn. rewrite guwkn_lk by apply Hn.
  pose proof (Hv _ _ HD) as Ho. destruct D, (σ m); cbn in Ho |- *; try contradiction.
  - rewrite gctx_uwk_as; now apply gctx_var_usubst.
  - now apply uwk_ctx.
  - destruct Ho as (i' & Hi' & Hin'). exists i'; split; [exact Hi'|].
    exact (in_gctx_uren _ _ _ (ush n) Hin').
  - now apply uwk_ty.
  - destruct Ho as (i' & Hi' & Hin'). exists i'; split; [exact Hi'|].
    exact (in_gctx_uren _ _ _ (ush n) Hin').
  - now apply uwk_tm.
Qed.

Lemma gsub_wf_up' L Ψ' L0 Ψ σ D D' :
  [ mkG L Ψ' ⊢ σ : mkG L0 Ψ ] -> D' = gdecl_gsubst D σ -> [ ⊢ mkG L (D' :: Ψ') ] ->
  [ mkG L (D' :: Ψ') ⊢ gup σ : mkG L0 (D :: Ψ) ].
Proof. intros H -> Hg. exact (gsub_wf_up _ _ _ D H Hg). Qed.

Lemma wf_glob_cons L D Ψ : [ ⊢ mkG L (D :: Ψ) ] -> [ ⊢ mkG L Ψ ].
Proof. inversion 1; assumption. Qed.

Ltac wf_suffixes :=
  repeat match goal with
  | H : [ ⊢ mkG ?L (?D :: ?Ψ) ] |- _ =>
      lazymatch goal with
      | _ : [ ⊢ mkG L Ψ ] |- _ => fail
      | _ => pose proof (wf_glob_cons _ _ _ H)
      end
  end.

Ltac gs_ups := repeat (apply gsub_wf_up'; [ | reflexivity | assumption ]).

Lemma gsub_wf_recGT G' σ G : [ G' ⊢ σ : G ] -> [ recGT G' ⊢ gup (guwk σ) : recGT G ].
Proof.
  intros Hσ. pose proof (wf_recGT (gsw_glob _ _ _ Hσ)) as Hg.
  pose proof (gsub_wf_uwkn 1 _ _ _ Hσ) as Hu.
  unfold recGT, gctx_uwk in *; cbn [gL gΨ] in *. wf_suffixes. gs_ups. exact Hu.
Qed.
Lemma gsub_wf_recGt G' σ G : [ G' ⊢ σ : G ] -> [ recGt G' ⊢ gup (gup (guwk σ)) : recGt G ].
Proof.
  intros Hσ. pose proof (wf_recGt (gsw_glob _ _ _ Hσ)) as Hg.
  pose proof (gsub_wf_uwkn 1 _ _ _ Hσ) as Hu.
  unfold recGt, gctx_uwk in *; cbn [gL gΨ] in *. wf_suffixes. gs_ups. exact Hu.
Qed.
Lemma gsub_wf_brG k G' σ G : k < 13 -> [ G' ⊢ σ : G ] -> [ brG k G' ⊢ gbsub k σ : brG k G ].
Proof.
  intros Hk Hσ. pose proof (wf_brG (gsw_glob _ _ _ Hσ) k Hk) as Hg.
  pose proof (gsub_wf_uwkn (br_nu k) _ _ _ Hσ) as Hu.
  unfold brG, gbsub, gctx_uwk in *; cbn [gL gΨ] in *.
  do 13 (destruct k; [cbn [brDecls List.app br_ng br_nu br_ar gupn Nat.iter] in *;
                      wf_suffixes; gs_ups; exact Hu|]).
  lia.
Qed.

(** ** Constructor equations for global substitution *)

Section PushGS.
Variable (σ : gsub).
Lemma gs_tyNat : tyNat⦃σ⦄ = tyNat. Proof. reflexivity. Qed.
Lemma gs_tyPi l l' A B : (tyPi l l' A B)⦃σ⦄ = tyPi l l' A⦃σ⦄ B⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tyU l : (tyU l)⦃σ⦄ = tyU l. Proof. reflexivity. Qed.
Lemma gs_tyEl l t : (tyEl l t)⦃σ⦄ = tyEl l t⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tyCTyp Δ l : (tyCTyp Δ l)⦃σ⦄ = tyCTyp Δ⦃σ⦄ l. Proof. reflexivity. Qed.
Lemma gs_tyCTrm Δ T l : (tyCTrm Δ T l)⦃σ⦄ = tyCTrm Δ⦃σ⦄ T⦃σ⦄ l. Proof. reflexivity. Qed.
Lemma gs_var n : (var n)⦃σ⦄ = var n. Proof. reflexivity. Qed.
Lemma gs_tmNat : tmNat⦃σ⦄ = tmNat. Proof. reflexivity. Qed.
Lemma gs_tmPi l l' s t : (tmPi l l' s t)⦃σ⦄ = tmPi l l' s⦃σ⦄ t⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tmU l : (tmU l)⦃σ⦄ = tmU l. Proof. reflexivity. Qed.
Lemma gs_zero : zero⦃σ⦄ = zero. Proof. reflexivity. Qed.
Lemma gs_succ t : (succ t)⦃σ⦄ = succ t⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_natrec l M s z t : (natrec l M s z t)⦃σ⦄ = natrec l M⦃σ⦄ s⦃σ⦄ z⦃σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
Lemma gs_lam l l' A t : (lam l l' A t)⦃σ⦄ = lam l l' A⦃σ⦄ t⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_app t l l' A B s : (app t l l' A B s)⦃σ⦄ = app t⦃σ⦄ l l' A⦃σ⦄ B⦃σ⦄ s⦃σ⦄.
Proof. reflexivity. Qed.
Lemma gs_boxT T : (boxT T)⦃σ⦄ = boxT T⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_boxt t : (boxt t)⦃σ⦄ = boxt t⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_letboxT l' l Δ M t' t :
  (letboxT l' l Δ M t' t)⦃σ⦄ = letboxT l' l Δ⦃σ⦄ M⦃σ⦄ t'⦃gup σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
Lemma gs_letboxt l' l Δ T M t' t :
  (letboxt l' l Δ T M t' t)⦃σ⦄ = letboxt l' l Δ⦃σ⦄ T⦃σ⦄ M⦃σ⦄ t'⦃gup σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
Lemma gs_cnil : cnil⦃σ⦄ = cnil. Proof. reflexivity. Qed.
Lemma gs_cext Γ A l : (Γ ,, A @ l)⦃σ⦄ = Γ⦃σ⦄ ,, A⦃σ⦄ @ l. Proof. reflexivity. Qed.
Lemma gs_lshift k : (lshift k)⦃σ⦄ = lshift k. Proof. reflexivity. Qed.
Lemma gs_tyGvar U d : (tyGvar U d)⦃σ⦄ = pty (σ U) d⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_gvar u d : (gvar u d)⦃σ⦄ = ptm (σ u) d⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_cvar g : (cvar g)⦃σ⦄ = pctx (σ g). Proof. reflexivity. Qed.
Lemma gs_elimT l1 l2 rb l Δ t : (elimT l1 l2 rb l Δ t)⦃σ⦄ = elimT l1 l2 rb⦃σ⦄ l Δ⦃σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
Lemma gs_elimt l1 l2 rb l Δ T t :
  (elimt l1 l2 rb l Δ T t)⦃σ⦄ = elimt l1 l2 rb⦃σ⦄ l Δ⦃σ⦄ T⦃σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
End PushGS.

Ltac push_gsubst := repeat progress (
  rewrite ?gs_tyNat, ?gs_tyPi, ?gs_tyU, ?gs_tyEl, ?gs_tyCTyp, ?gs_tyCTrm, ?gs_var, ?gs_tmNat,
          ?gs_tmPi, ?gs_tmU, ?gs_zero, ?gs_succ, ?gs_natrec, ?gs_lam, ?gs_app, ?gs_boxT,
          ?gs_boxt, ?gs_letboxT, ?gs_letboxt, ?gs_cnil, ?gs_cext, ?gs_lshift,
          ?gs_tyGvar, ?gs_gvar, ?gs_cvar, ?gs_elimT, ?gs_elimt).

Lemma gs_single_ty (M : ty) a σ : M[lsingle a]⦃σ⦄ = M⦃σ⦄[lsingle a⦃σ⦄].
Proof. rewrite gsubst_subst_ty; reflexivity. Qed.
Lemma gs_single (b a : tm) σ : b[lsingle a]⦃σ⦄ = b⦃σ⦄[lsingle a⦃σ⦄].
Proof. rewrite gsubst_subst; reflexivity. Qed.
Lemma gs_single2 (z t q : tm) σ : z[lsingle2 t q]⦃σ⦄ = z⦃σ⦄[lsingle2 t⦃σ⦄ q⦃σ⦄].
Proof. rewrite gsubst_subst; reflexivity. Qed.
Lemma gs_lsucc_ty (M : ty) σ : M[lsucc]⦃σ⦄ = M⦃σ⦄[lsucc].
Proof. rewrite gsubst_subst_ty; reflexivity. Qed.
Lemma gs_ren (t : tm) r σ : t⟨r⟩⦃σ⦄ = t⦃σ⦄⟨r⟩.
Proof. apply gsubst_ren. Qed.

(** The letbox body's type [M⟪↑⟫[box U^id/x]] under [⇑σ]. *)
Lemma gs_letbox_ty (M : ty) b σ : b⦃gup σ⦄ = b ->
  M⟪S⟫[lsingle b]⦃gup σ⦄ = M⦃σ⦄⟪S⟫[lsingle b].
Proof. intros Hb. rewrite gs_single_ty, Hb, gshift_up_ty; reflexivity. Qed.

Ltac gs_rewrite :=
  rewrite ?gs_single_ty, ?gs_single, ?gs_single2, ?gs_lsucc_ty, ?gsubst_ren_ty', ?gs_ren.

Lemma gs_tm_regty G i Δ x T T' l :
  [ G ; Δ ⊢[ i ] x : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? ->. Qed.
Lemma gs_eqtm_regty G i Δ x y T T' l :
  [ G ; Δ ⊢[ i ] x ≅ y : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? ->. Qed.

Ltac gs_eq := push_gsubst; gs_rewrite; push_gsubst; first [reflexivity | f_equal; reflexivity].

#[export] Hint Resolve in_ctx_gsubst gsw_glob : gsub.
#[export] Hint Resolve wfc_nil wfc_var wfc_ext wfg_ty wfg_tm lequiv_wf_l lequiv_wf_r : gsub.
#[export] Hint Extern 5 (wf_tm _ _ _ _ _ _) => eapply gs_tm_regty; [ | gs_eq ] : gsub.
#[export] Hint Extern 5 (eq_tm _ _ _ _ _ _ _) => eapply gs_eqtm_regty; [ | gs_eq ] : gsub.
#[export] Hint Extern 1 (lwf _ _) => (cbn; first [exact I | assumption]) : gsub.
#[export] Hint Extern 1 (lequiv _ _ _) => (cbn; assumption) : gsub.
#[export] Hint Extern 1 (lle _ _) => assumption : gsub.
#[export] Hint Extern 1 (_ <> _) => assumption : gsub.
#[export] Hint Extern 1 (compt _) =>
  first [assumption | apply compt_typeof | (left; reflexivity) | (right; reflexivity)] : gsub.
#[export] Hint Extern 1 (_ = _ \/ _ = _) => first [left; reflexivity | right; reflexivity] : gsub.

Ltac gs_premises := eauto 6 with gsub.

Ltac gs_step :=
  match goal with
  | |- wf_ctx _ _ _ =>
      first [ solve [eapply wfc_nil; gs_premises] | solve [eapply wfc_ext; gs_premises] ]
  | |- eq_ctx _ _ _ _ =>
      first [ solve [eapply eqc_nil; gs_premises] | solve [eapply eqc_ext; gs_premises] ]
  | |- wf_ty _ _ _ _ _ =>
      first [ solve [eapply wft_nat; gs_premises] | solve [eapply wft_pi; gs_premises]
            | solve [eapply wft_U; gs_premises] | solve [eapply wft_El; gs_premises]
            | solve [eapply wft_lconv; gs_premises] | solve [eapply wft_CTyp; gs_premises]
            | solve [eapply wft_CTrm; gs_premises] ]
  | |- wf_tm _ _ _ _ _ _ =>
      first [ solve [eapply wf_var; gs_premises] | solve [eapply wf_code_nat; gs_premises]
            | solve [eapply wf_code_U; gs_premises] | solve [eapply wf_code_pi; gs_premises]
            | solve [eapply wf_zero; gs_premises] | solve [eapply wf_succ; gs_premises]
            | solve [eapply wf_lam; gs_premises]
            | solve [eapply wf_app; gs_premises] | solve [eapply wf_conv; gs_premises]
            | solve [eapply wf_lconv; gs_premises] | solve [eapply wf_boxT; gs_premises]
            | solve [eapply wf_boxt; gs_premises] ]
  | |- eq_ty _ _ _ _ _ _ =>
      first [ solve [eapply eqty_refl; gs_premises] | solve [eapply eqty_sym; gs_premises]
            | solve [eapply eqty_trans; gs_premises] | solve [eapply eqty_pi; gs_premises]
            | solve [eapply eqty_U; gs_premises] | solve [eapply eqty_El; gs_premises]
            | solve [eapply eqty_El_nat; gs_premises] | solve [eapply eqty_El_U; gs_premises]
            | solve [eapply eqty_El_pi; gs_premises] | solve [eapply eqty_lconv; gs_premises]
            | solve [eapply eqty_CTyp; gs_premises] | solve [eapply eqty_CTrm; gs_premises] ]
  | |- eq_tm _ _ _ _ _ _ _ =>
      first [ solve [eapply eqtm_refl; gs_premises] | solve [eapply eqtm_sym; gs_premises]
            | solve [eapply eqtm_trans; gs_premises] | solve [eapply eqtm_code_U; gs_premises]
            | solve [eapply eqtm_code_pi; gs_premises] | solve [eapply eqtm_succ; gs_premises]
            | solve [eapply eqtm_lam; gs_premises]
            | solve [eapply eqtm_app; gs_premises] | solve [eapply eqtm_conv; gs_premises]
            | solve [eapply eqtm_lconv; gs_premises]
            | solve [eapply eqtm_beta; gs_premises] ]
  end.

(** The recursors' specification laws (defined below). *)
Ltac gs_rec_rw := fail.

Ltac gs_premise :=
  first [ solve [eauto 6 with gsub]
        | solve [eapply gs_tm_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eq]]
        | solve [eapply gs_eqtm_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eq]]
        (* the recursors' motive instances (M3_DESIGN.md E10) *)
        | solve [eapply wf_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end
                 | gs_rec_rw; reflexivity]]
        | solve [eapply eq_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end
                 | gs_rec_rw; reflexivity | gs_rec_rw; reflexivity]] ].

(** The lookup-typed substitution of [u^δ]/[U^δ], under [σ]. *)
Ltac gs_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin;
  let A0 := fresh "A0" in let HA0 := fresh "HA0" in
  let g := fresh "g" in let m := fresh "m" in let T1 := fresh "T1" in
  let Hg := fresh "Hg" in let Hm := fresh "Hm" in
  destruct (in_ctx_gsubst_inv' _ _ _ _ _ Hin) as [(A0 & HA0 & ->) | (g & m & T1 & Hg & -> & Hm & ->)];
  [ cbn [gsubst GSubst_lsub]; rewrite !llk_glsubst; change (gsubst_tm ?x ?y) with x⦃y⦄;
    rewrite <- gsubst_subst_ty;
    match goal with IH : forall n A k (_ : in_ctx _ n A k), _ |- _ => eapply (IH n A0 k HA0) end;
    eauto with gsub
  | first [ eapply gs_tail_entry_eq | eapply gs_tail_entry ]; eauto with gsub ].

Ltac gs_tail := apply lsub_tail_gsubst'; assumption.

Ltac gs_dnfl :=
  match goal with Hσ : gsub_wf _ _ _ |- dnfl _ =>
    apply gsubst_dnf_all; [assumption | exact (gsw_dnf _ _ _ Hσ)] end.

(** The substitution [d⦃σ⦄] as a typed substitution, to instantiate [σ(u)]. *)
Ltac gs_ctx :=
  first [ assumption
        | match goal with IH : forall Ψ' σ', gsub_wf _ σ' _ -> compt _ -> wf_ctx _ _ _ |- wf_ctx _ _ _ =>
            eapply IH; [eassumption | eauto with gsub] end ].

Ltac gs_lsub :=
  constructor; [ gs_ctx | intros ?m; apply dnfl_llk; gs_dnfl | gs_tail | gs_entries ].

Ltac gs_obj Hσ Hin := pose proof (gsw_var _ _ _ Hσ _ _ Hin) as Ho; cbn in Ho.

Ltac gs_manual :=
  match goal with
  | Hσ : gsub_wf _ ?σ _, Hc : gctx_var _ ?g |- wf_ctx _ _ (pctx (?σ ?g)) =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ (gctx_var_in _ _ Hc)) as Ho; cbn in Ho;
      destruct (σ g); cbn [pctx]; try contradiction;
      [ apply wfc_var; [exact (gsw_glob _ _ _ Hσ) | exact Ho]
      | eapply lift_ctx; [exact Ho | apply lle_D_compt; assumption] ]
  | Hσ : gsub_wf _ ?σ _, Hc : gctx_var _ ?g |- eq_ctx _ _ (pctx (?σ ?g)) _ =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ (gctx_var_in _ _ Hc)) as Ho; cbn in Ho;
      destruct (σ g); cbn [pctx]; try contradiction;
      [ apply eqc_var; [exact (gsw_glob _ _ _ Hσ) | exact Ho]
      | apply eqc_refl; eapply lift_ctx; [exact Ho | apply lle_D_compt; assumption] ]
  | Hσ : gsub_wf _ ?σ _, Hin : in_gctx _ ?U (gdTy ?Δ _ _) |- wf_ty _ _ _ (pty (?σ ?U) _) _ =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ Hin) as Ho; cbn in Ho;
      destruct (σ U); cbn in *; try contradiction;
      [ let i1 := fresh "i1" in let Hi1 := fresh "Hi1" in let Hin1 := fresh "Hin1" in
        destruct Ho as (i1 & Hi1 & Hin1);
        eapply wft_gvar with (Δ := Δ⦃σ⦄); [ .. | gs_entries];
        first [exact Hin1 | gs_ctx | gs_tail | gs_dnfl | eauto using lle_trans]
      | eapply wf_ty_subst_g; [ eapply lift_ty; [exact Ho | assumption] | gs_lsub ] ]
  | Hσ : gsub_wf _ ?σ _, Hin : in_gctx _ ?u (gdTm ?Δ _ _ _) |- wf_tm _ _ _ (ptm (?σ ?u) _) _ _ =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ Hin) as Ho; cbn in Ho;
      rewrite gsubst_subst_ty; destruct (σ u); cbn in *; try contradiction;
      [ let i1 := fresh "i1" in let Hi1 := fresh "Hi1" in let Hin1 := fresh "Hin1" in
        destruct Ho as (i1 & Hi1 & Hin1);
        eapply wf_gvar with (Δ := Δ⦃σ⦄); [ .. | gs_entries];
        first [exact Hin1 | gs_ctx | gs_tail | gs_dnfl | eauto using lle_trans]
      | eapply wf_tm_subst_g; [ eapply lift_tm; [exact Ho | assumption] | gs_lsub ] ]
  | Hσ : gsub_wf _ ?σ _, Hin : in_gctx _ ?U (gdTy ?Δ _ _) |- eq_ty _ _ _ (pty (?σ ?U) _) _ _ =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ Hin) as Ho; cbn in Ho;
      destruct (σ U); cbn in *; try contradiction;
      [ let i1 := fresh "i1" in let Hi1 := fresh "Hi1" in let Hin1 := fresh "Hin1" in
        destruct Ho as (i1 & Hi1 & Hin1);
        eapply eqty_gvar with (Δ := Δ⦃σ⦄); [ .. | gs_entries | gs_entries | gs_entries];
        first [exact Hin1 | gs_ctx | gs_tail | gs_dnfl | eauto using lle_trans]
      | eapply (proj1 (proj2 (proj2 functionality_all)));
        [ eapply lift_ty; [exact Ho | assumption]
        | split; [gs_lsub | split; [gs_lsub | gs_entries]] ] ]
  | Hσ : gsub_wf _ ?σ _, Hin : in_gctx _ ?u (gdTm ?Δ _ _ _) |- eq_tm _ _ _ (ptm (?σ ?u) _) _ _ _ =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ Hin) as Ho; cbn in Ho;
      rewrite gsubst_subst_ty; destruct (σ u); cbn in *; try contradiction;
      [ let i1 := fresh "i1" in let Hi1 := fresh "Hi1" in let Hin1 := fresh "Hin1" in
        destruct Ho as (i1 & Hi1 & Hin1);
        eapply eqtm_gvar with (Δ := Δ⦃σ⦄); [ .. | gs_entries | gs_entries | gs_entries];
        first [exact Hin1 | gs_ctx | gs_tail | gs_dnfl | eauto using lle_trans]
      | eapply (proj1 (proj2 (proj2 (proj2 functionality_all))));
        [ eapply lift_tm; [exact Ho | assumption]
        | split; [gs_lsub | split; [gs_lsub | gs_entries]] ] ]
  end.

(** The letbox body, typed under [Ψ, U], under [⇑σ]. *)
Ltac gs_body :=
  match goal with
  | IH : forall Ψ'' σ', gsub_wf _ σ' (gext ?G ?D) -> _,
    Hσ : gsub_wf _ ?σ ?G |- _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext {| gL := gL G ; gΨ := _ |} (gdecl_gsubst D σ) ])
        by (unfold gext; cbn [gdecl_gsubst gΨ gL]; first [eapply wfg_ty | eapply wfg_tm];
            eauto with gsub);
      pose proof (IH _ (gup σ) (gsub_wf_up _ _ _ D Hσ Hg)) as X;
      rewrite gshift_up_ctx, ?gs_letbox_ty in X by reflexivity; exact X
  end.

Ltac gs_manual2 :=
  match goal with
  | |- wf_tm _ _ _ (natrec _ _ _ _ _) _ _ => eapply wf_natrec; gs_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ zero) _ _ _ => eapply eqtm_natrec_zero; gs_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ (succ _)) _ _ _ => eapply eqtm_natrec_succ; gs_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ _) (natrec _ _ _ _ _) _ _ => eapply eqtm_natrec; gs_premise
  | |- eq_tm _ _ _ (lam _ _ _ _) _ _ _ => eapply eqtm_eta; gs_premise
  | |- wf_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ => eapply wf_letboxT; try gs_body; gs_premise
  | |- wf_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ => eapply wf_letboxt; try gs_body; gs_premise
  | Hσ : gsub_wf _ _ _ |- eq_tm _ _ _ (letboxT _ _ _ _ _ (boxT _)) _ _ _ =>
      rewrite (gs_gsingle _ _ _ (gsw_dnf _ _ _ Hσ)); cbn [gosubst];
      eapply eqtm_letboxT_beta; try gs_body; gs_premise
  | Hσ : gsub_wf _ _ _ |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      rewrite (gs_gsingle _ _ _ (gsw_dnf _ _ _ Hσ)); cbn [gosubst];
      eapply eqtm_letboxt_beta; try gs_body; gs_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxT; try gs_body; gs_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxt; try gs_body; gs_premise
  end.

(** The recursors: motives under [⇑(σ↑ᵤ)], branches under [gbsub k σ]. *)
Ltac gs_motive :=
  match goal with
  | IH : forall Ψ'' σ', gsub_wf (mkG (gL (recGT ?G)) Ψ'') σ' (recGT ?G) -> _,
    Hσ : gsub_wf (mkG (gL ?G) ?Ψ') ?σ ?G |- _ =>
      let X := fresh "X" in
      pose proof (IH _ _ (gsub_wf_recGT _ _ _ Hσ)) as X;
      rewrite (recΓT_gsubst _ _ (gsw_dnf _ _ _ Hσ)) in X; exact X
  | IH : forall Ψ'' σ', gsub_wf (mkG (gL (recGt ?G)) Ψ'') σ' (recGt ?G) -> _,
    Hσ : gsub_wf (mkG (gL ?G) ?Ψ') ?σ ?G |- _ =>
      let X := fresh "X" in
      pose proof (IH _ _ (gsub_wf_recGt _ _ _ Hσ)) as X;
      rewrite (recΓt_gsubst _ _ (gsw_dnf _ _ _ Hσ)) in X; exact X
  end.

Ltac gs_branches :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
  match goal with
  | IH : forall k, k < 13 -> forall Ψ'' σ', gsub_wf (mkG (gL (brG k ?G)) Ψ'') σ' (brG k ?G) -> _,
    Hσ : gsub_wf (mkG (gL ?G) ?Ψ') ?σ ?G |- _ =>
      let X := fresh "X" in
      pose proof (IH k Hk _ _ (gsub_wf_brG k _ _ _ Hk Hσ)) as X;
      try specialize (X ltac:(right; reflexivity));
      rewrite (brΓ_gsubst k _ _ _ _ _ _ Hk (gsw_dnf _ _ _ Hσ)) in X;
      rewrite ?(brRes_gsubst k _ _ _ Hk (gsw_dnf _ _ _ Hσ)) in X;
      rewrite ?wrapMT_gsubst, ?wrapMt_gsubst in X; exact X
  end.

Ltac gs_rec_rw ::=
  match goal with Hσ : gsub_wf _ ?σ _ |- _ =>
    rewrite ?mkrb_gsubst;
    rewrite ?motT_gsubst, ?mott_gsubst by first [hd_tac | exact (gsw_dnf _ _ _ Hσ)];
    rewrite ?wrapMT_gsubst, ?wrapMt_gsubst
  end.

Ltac gs_rec :=
  match goal with
  | |- wf_tm _ _ _ (elimT _ _ _ _ _ _) _ _ =>
      gs_rec_rw; eapply wf_elimT; [ .. | gs_motive | gs_motive | gs_branches | gs_branches | ];
      gs_premise
  | |- wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ =>
      gs_rec_rw; eapply wf_elimt; [ .. | gs_motive | gs_motive | gs_branches | gs_branches | | ];
      gs_premise
  | Hσ : gsub_wf _ ?σ _ |- eq_tm _ _ _ (elimT _ _ _ _ _ (boxT _)) _ _ _ =>
      match goal with
      | w : wf_tm _ _ _ (elimT _ _ _ _ _ (boxT _)) _ _ |- _ =>
          destruct (elimT_rb_shape _ _ _ _ _ _ _ _ _ _ _ w) as (? & ? & ? & ->);
          eapply eqtm_elimT_beta;
          [ gs_premise | apply redT_gsubst; [exact (gsw_dnf _ _ _ Hσ) | assumption] | gs_premise ]
      end
  | Hσ : gsub_wf _ ?σ _ |- eq_tm _ _ _ (elimt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      match goal with
      | w : wf_tm _ _ _ (elimt _ _ _ _ _ _ (boxt _)) _ _ |- _ =>
          destruct (elimt_rb_shape _ _ _ _ _ _ _ _ _ _ _ _ w) as (? & ? & ? & ->);
          eapply eqtm_elimt_beta;
          [ gs_premise | apply redt_gsubst; [exact (gsw_dnf _ _ _ Hσ) | assumption] | gs_premise ]
      end
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ _) _ _ _ =>
      gs_rec_rw; eapply eqtm_elimT;
      [ .. | gs_motive | gs_motive | gs_motive | gs_motive | gs_motive | gs_motive
           | gs_branches | gs_branches | gs_branches | gs_branches | ]; gs_premise
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ _ =>
      gs_rec_rw; eapply eqtm_elimt;
      [ .. | gs_motive | gs_motive | gs_motive | gs_motive | gs_motive | gs_motive
           | gs_branches | gs_branches | gs_branches | gs_branches | ]; gs_premise
  end.

Ltac notrec := lazymatch goal with
  | |- context [elimT] => fail | |- context [elimt] => fail | _ => idtac end.

Theorem gsubstitution :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> forall Ψ' σ, [ gwk_to G Ψ' ⊢ σ : G ] -> compt i ->
     [ gwk_to G Ψ' ; Γ⦃σ⦄ ⊢[ i ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> forall Ψ' σ, [ gwk_to G Ψ' ⊢ σ : G ] ->
     [ gwk_to G Ψ' ; Γ⦃σ⦄ ⊢[ i ] T⦃σ⦄ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> forall Ψ' σ, [ gwk_to G Ψ' ⊢ σ : G ] ->
     [ gwk_to G Ψ' ; Γ⦃σ⦄ ⊢[ i ] t⦃σ⦄ : T⦃σ⦄ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> forall Ψ' σ, [ gwk_to G Ψ' ⊢ σ : G ] ->
     [ gwk_to G Ψ' ; Γ⦃σ⦄ ⊢[ i ] T⦃σ⦄ ≅ T'⦃σ⦄ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> forall Ψ' σ, [ gwk_to G Ψ' ⊢ σ : G ] ->
     [ gwk_to G Ψ' ; Γ⦃σ⦄ ⊢[ i ] t⦃σ⦄ ≅ t'⦃σ⦄ : T⦃σ⦄ @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> forall Ψ' σ, [ gwk_to G Ψ' ⊢ σ : G ] -> compt i ->
     [ gwk_to G Ψ' ⊢[ i ] Γ⦃σ⦄ ≅ Γ'⦃σ⦄ ]).
Proof.
  apply typing_mut; intros; try exact I; unfold gwk_to in *; push_gsubst; gs_rewrite; push_gsubst.
  all: try (notrec; gs_step).
  all: try (notrec; gs_manual).
  all: try (notrec; gs_manual2).
  all: gs_rec.
Qed.

(** ** Declared bindings are well formed *)

Definition decl_ok (G : gctx) (D : gdecl) : Prop :=
  match D with
  | gdCtx => True
  | gdTy Δ i l => [ G ; Δ ⊢[ lD ] ] /\ lwf (gL G) l
  | gdTm Δ i T l => [ G ; Δ ⊢[ lD ] ] /\ [ G ; Δ ⊢[ lD ] T @ l ] /\ lwf (gL G) l
  end.

Lemma decl_ok_wk1 L Ψ D0 D : [ ⊢ mkG L (D0 :: Ψ) ] -> decl_ok (mkG L Ψ) D ->
  decl_ok (mkG L (D0 :: Ψ)) (gdecl_ren D S).
Proof.
  intros Hg HD.
  assert (Hw : gwk_wf (gwk_step gwk_id) (D0 :: Ψ) Ψ) by (constructor; constructor).
  destruct D; cbn in *; auto.
  - destruct HD as [HΔ Hl]. split; [|exact Hl].
    exact (proj1 (proj2 gweakening) _ _ _ HΔ _ _ Hw Hg).
  - destruct HD as (HΔ & HT & Hl). refine (conj _ (conj _ Hl)).
    + exact (proj1 (proj2 gweakening) _ _ _ HΔ _ _ Hw Hg).
    + exact (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ HT _ _ Hw Hg).
Qed.

Lemma gctx_decl_ok G n D : [ ⊢ G ] -> in_gctx (gΨ G) n D -> decl_ok G D.
Proof.
  destruct G as [L Ψ]; cbn. intros Hg Hin; revert Hg; induction Hin as [Ψ D | Ψ D D' n Hin IH]; intros Hg.
  - apply decl_ok_wk1; [exact Hg|]. inversion Hg; subst; cbn; auto.
    repeat split; auto. exact (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ ltac:(eassumption)).
  - apply decl_ok_wk1; [exact Hg|]. apply IH. inversion Hg; subst; assumption.
Qed.

(** ** Single global substitutions (the letbox β-rules) *)

Lemma gdecl_gsubst_ren_single D o : dnf_decl D -> gdecl_gsubst (gdecl_ren D S) (gsingle o) = D.
Proof.
  intros HD; destruct D; cbn in *; f_equal; try reflexivity.
  all: first
    [ rewrite (gsubst_gren_ctx _ _ _ (fun j => GId j)) by reflexivity; apply gsubst_id_ctx; [tauto | auto]
    | rewrite (gsubst_gren_ty _ _ _ (fun j => GId j)) by reflexivity; apply gsubst_id_ty; [tauto | auto] ].
Qed.

Lemma in_gctx_ctx_var' Ψ L n D : in_gctx Ψ n D -> D = gdCtx -> gctx_var (mkG L Ψ) n.
Proof.
  unfold gctx_var; cbn. induction 1 as [Ψ D | Ψ D D' n Hin IH]; intros HD.
  - destruct D; cbn in HD; try discriminate; reflexivity.
  - destruct D; cbn in HD; try discriminate. now apply IH.
Qed.
Lemma in_gctx_ctx_var Ψ L n : in_gctx Ψ n gdCtx -> gctx_var (mkG L Ψ) n.
Proof. intros H; exact (in_gctx_ctx_var' _ _ _ _ H eq_refl). Qed.

Lemma gsub_wf_single G D o :
  [ ⊢ G ] -> dnfo o -> gobj_wf G o (gdecl_gsubst (gdecl_ren D S) (gsingle o)) ->
  [ G ⊢ gsingle o : gext G D ].
Proof.
  intros Hg Ho Hwf. constructor; [exact Hg | intros [|n]; cbn; auto |].
  intros n D0 Hin. inversion Hin as [Ψ0 D1 | Ψ0 D1 D2 m Hm]; subst; cbn [gsingle]; [exact Hwf|].
  rewrite gdecl_gsubst_ren_single by exact (in_gctx_dnf _ _ _ Hm).
  destruct D1; cbn.
  - destruct G as [L Ψ]; exact (in_gctx_ctx_var _ _ _ Hm).
  - exists i; split; [apply lle_refl | exact Hm].
  - exists i; split; [apply lle_refl | exact Hm].
Qed.
