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
  | gdDef Δ T l t => gdDef Δ⦃σ⦄ T⦃σ⦄ l t⦃σ⦄
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
  (* a definition goes to a definition with the substituted body (M9_DESIGN.md) *)
  | gdDef Δ T l t, GId j => in_gctx (gΨ G') j (gdDef Δ T l t)
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
Proof. destruct D; cbn; f_equal; auto using gshift_up_ctx, gshift_up_ty, gshift_up_tm. Qed.

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

Lemma gobj_wf_gwk G' o D γ L'' Ψ'' :
  gobj_wf G' o D -> gwk_wf γ Ψ'' (gΨ G') -> gL G' <= L'' -> [ ⊢ mkG L'' Ψ'' ] ->
  gobj_wf (mkG L'' Ψ'') (goren o γ) (gdecl_ren D γ).
Proof.
  intros Ho Hγ HL Hg. destruct D, o; cbn in *; try contradiction.
  all: first
    [ eapply gctx_var_gwk; eauto
    | exact (proj1 (proj2 gweakening) _ _ _ Ho _ _ _ HL Hγ Hg)
    | exact (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ Ho _ _ _ HL Hγ Hg)
    | exact (proj1 (proj2 (proj2 (proj2 gweakening))) _ _ _ _ _ _ Ho _ _ _ HL Hγ Hg)
    | let i' := fresh "i'" in let Hi' := fresh "Hi'" in let Hin := fresh "Hin" in
      destruct Ho as (i' & Hi' & Hin); exists i'; split; [exact Hi'|];
      exact (in_gctx_gwk _ _ _ _ _ Hγ Hin)
    | exact (in_gctx_gwk _ _ _ _ _ Hγ Ho) ].
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
    + exact (ing_here _ (gdDef _ _ _ _)).
  - rewrite gdecl_gsubst_ren_up.
    exact (gobj_wf_gwk _ _ _ (gwk_step gwk_id) _ _ (Hv _ _ Hm)
             (gwkwf_step _ _ _ _ (gwkwf_id _)) (le_n _) Hg').
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
          | apply (proj1 uren_gsubst_all); exact H
          | apply (proj1 (proj2 uren_gsubst_all)); exact H ].
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
  - exact (in_gctx_uren _ _ _ (ush n) Ho).
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
Lemma gsub_wf_brG k G' σ G : k < nbr -> [ G' ⊢ σ : G ] -> [ brG k G' ⊢ gbsub k σ : brG k G ].
Proof.
  intros Hk Hσ. pose proof (wf_brG (gsw_glob _ _ _ Hσ) k Hk) as Hg.
  pose proof (gsub_wf_uwkn (br_nu k) _ _ _ Hσ) as Hu.
  unfold brG, gbsub, gctx_uwk in *; cbn [gL gΨ] in *.
  br_all ltac:(destruct k; [cbn [brDecls List.app br_ng br_nu br_ar gupn Nat.iter] in *;
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
Lemma gs_tyUPi n l T : (tyUPi n l T)⦃σ⦄ = tyUPi n l T⦃guwkn n σ⦄. Proof. reflexivity. Qed.
Lemma gs_ulam n l T t : (ulam n l T t)⦃σ⦄ = ulam n l T⦃guwkn n σ⦄ t⦃guwkn n σ⦄. Proof. reflexivity. Qed.
Lemma gs_uapp t ls : (uapp t ls)⦃σ⦄ = uapp t⦃σ⦄ ls. Proof. reflexivity. Qed.
Lemma gs_tyCPi l T : (tyCPi l T)⦃σ⦄ = tyCPi l T⦃gup σ⦄. Proof. reflexivity. Qed.
Lemma gs_tyTPi Δ l l' T : (tyTPi Δ l l' T)⦃σ⦄ = tyTPi Δ⦃σ⦄ l l' T⦃gup σ⦄. Proof. reflexivity. Qed.
Lemma gs_clam l T t : (clam l T t)⦃σ⦄ = clam l T⦃gup σ⦄ t⦃gup σ⦄. Proof. reflexivity. Qed.
Lemma gs_capp t Δ : (capp t Δ)⦃σ⦄ = capp t⦃σ⦄ Δ⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tlam Δ l l' T t : (tlam Δ l l' T t)⦃σ⦄ = tlam Δ⦃σ⦄ l l' T⦃gup σ⦄ t⦃gup σ⦄. Proof. reflexivity. Qed.
Lemma gs_tapp t T : (tapp t T)⦃σ⦄ = tapp t⦃σ⦄ T⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tySig l l' A B : (tySig l l' A B)⦃σ⦄ = tySig l l' A⦃σ⦄ B⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tySum l l' A B : (tySum l l' A B)⦃σ⦄ = tySum l l' A⦃σ⦄ B⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_inl l l' A B a : (tmInl l l' A B a)⦃σ⦄ = tmInl l l' A⦃σ⦄ B⦃σ⦄ a⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_inr l l' A B a : (tmInr l l' A B a)⦃σ⦄ = tmInr l l' A⦃σ⦄ B⦃σ⦄ a⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_case l l' l'' A B M c1 c2 t :
  (tmCase l l' l'' A B M c1 c2 t)⦃σ⦄ = tmCase l l' l'' A⦃σ⦄ B⦃σ⦄ M⦃σ⦄ c1⦃σ⦄ c2⦃σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
Lemma gs_tmSig l l' s t : (tmSig l l' s t)⦃σ⦄ = tmSig l l' s⦃σ⦄ t⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_pair l l' A B a b : (tmPair l l' A B a b)⦃σ⦄ = tmPair l l' A⦃σ⦄ B⦃σ⦄ a⦃σ⦄ b⦃σ⦄.
Proof. reflexivity. Qed.
Lemma gs_fst l l' A B p : (tmFst l l' A B p)⦃σ⦄ = tmFst l l' A⦃σ⦄ B⦃σ⦄ p⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_snd l l' A B p : (tmSnd l l' A B p)⦃σ⦄ = tmSnd l l' A⦃σ⦄ B⦃σ⦄ p⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tyUnit l : (tyUnit l)⦃σ⦄ = tyUnit l. Proof. reflexivity. Qed.
Lemma gs_tmUnit l : (tmUnit l)⦃σ⦄ = tmUnit l. Proof. reflexivity. Qed.
Lemma gs_tmSEmpty l : (tmSEmpty l)⦃σ⦄ = tmSEmpty l. Proof. reflexivity. Qed.
Lemma gs_tmEmpty l : (tmEmpty l)⦃σ⦄ = tmEmpty l. Proof. reflexivity. Qed.
Lemma gs_tmSum l l' s t : (tmSum l l' s t)⦃σ⦄ = tmSum l l' s⦃σ⦄ t⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tmW l l' s t : (tmW l l' s t)⦃σ⦄ = tmW l l' s⦃σ⦄ t⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tmVec l s n : (tmVec l s n)⦃σ⦄ = tmVec l s⦃σ⦄ n⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tmWf l s n : (tmWf l s n)⦃σ⦄ = tmWf l s⦃σ⦄ n⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tmFin n : (tmFin n)⦃σ⦄ = tmFin n⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_triv l : (tmTriv l)⦃σ⦄ = tmTriv l. Proof. reflexivity. Qed.
Lemma gs_tySEq l A a b : (tySEq l A a b)⦃σ⦄ = tySEq l A⦃σ⦄ a⦃σ⦄ b⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tySEmpty l : (tySEmpty l)⦃σ⦄ = tySEmpty l. Proof. reflexivity. Qed.
Lemma gs_tyEmpty l : (tyEmpty l)⦃σ⦄ = tyEmpty l. Proof. reflexivity. Qed.
Lemma gs_srefl l A a : (srefl l A a)⦃σ⦄ = srefl l A⦃σ⦄ a⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_elimSEmpty l l' M e : (elimSEmpty l l' M e)⦃σ⦄ = elimSEmpty l l' M⦃σ⦄ e⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_elimEmpty l l' M e : (elimEmpty l l' M e)⦃σ⦄ = elimEmpty l l' M⦃σ⦄ e⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tyId l A a b : (tyId l A a b)⦃σ⦄ = tyId l A⦃σ⦄ a⦃σ⦄ b⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_refl l A a : (tmRefl l A a)⦃σ⦄ = tmRefl l A⦃σ⦄ a⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tmId l s t u : (tmId l s t u)⦃σ⦄ = tmId l s⦃σ⦄ t⦃σ⦄ u⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tmSEq l s t u : (tmSEq l s t u)⦃σ⦄ = tmSEq l s⦃σ⦄ t⦃σ⦄ u⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_J l l' A a M c u e :
  (tmJ l l' A a M c u e)⦃σ⦄ = tmJ l l' A⦃σ⦄ a⦃σ⦄ M⦃σ⦄ c⦃σ⦄ u⦃σ⦄ e⦃σ⦄.
Proof. reflexivity. Qed.
Lemma gs_gdef u b d : (gdef u b d)⦃σ⦄ = pdef (σ u) b⦃σ⦄ d⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tyW l l' A B : (tyW l l' A B)⦃σ⦄ = tyW l l' A⦃σ⦄ B⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tyVec l A n : (tyVec l A n)⦃σ⦄ = tyVec l A⦃σ⦄ n⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_tyFin n : (tyFin n)⦃σ⦄ = tyFin n⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_sup l l' A B a f : (tmSup l l' A B a f)⦃σ⦄ = tmSup l l' A⦃σ⦄ B⦃σ⦄ a⦃σ⦄ f⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_elimW l l' l'' A B M c t :
  (tmElimW l l' l'' A B M c t)⦃σ⦄ = tmElimW l l' l'' A⦃σ⦄ B⦃σ⦄ M⦃σ⦄ c⦃σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
(** [elim_W]'s induction hypothesis (M13a). *)
Lemma gs_wIH l l' l'' A B M c a f :
  (wIH l l' l'' A B M c a f)⦃σ⦄ = wIH l l' l'' A⦃σ⦄ B⦃σ⦄ M⦃σ⦄ c⦃σ⦄ a⦃σ⦄ f⦃σ⦄.
Proof.
  unfold wIH. rewrite gs_lam, gs_elimW, gs_app, gs_var.
  repeat rewrite ?gsubst_ren_ty', ?gsubst_ren, ?gsubst_subst_ty, ?gs_tyW. reflexivity.
Qed.
Lemma gs_tyWf l A N : (tyWf l A N)⦃σ⦄ = tyWf l A⦃σ⦄ N⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_supf l A N a cs : (tmSupf l A N a cs)⦃σ⦄ = tmSupf l A⦃σ⦄ N⦃σ⦄ a⦃σ⦄ cs⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_elimWf l l' A N M c t :
  (tmElimWf l l' A N M c t)⦃σ⦄ = tmElimWf l l' A⦃σ⦄ N⦃σ⦄ M⦃σ⦄ c⦃σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
(** Propositional truncation (M16a). *)
Lemma gs_tySq l A : (tySq l A)⦃σ⦄ = tySq l A⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_sq l A a : (tmSq l A a)⦃σ⦄ = tmSq l A⦃σ⦄ a⦃σ⦄. Proof. reflexivity. Qed.
Lemma gs_elimSq l l' A M c t : (tmElimSq l l' A M c t)⦃σ⦄ = tmElimSq l l' A⦃σ⦄ M⦃σ⦄ c⦃σ⦄ t⦃σ⦄.
Proof. reflexivity. Qed.
(** [nth] and [elim_Wf]'s induction hypothesis (M15a). *)
Lemma gs_tmNth l T k cs i : (tmNth l T k cs i)⦃σ⦄ = tmNth l T⦃σ⦄ k⦃σ⦄ cs⦃σ⦄ i⦃σ⦄.
Proof.
  unfold tmNth, nthMot, nthBase, nthStep. cbn [gsubst GSubst_tm GSubst_ty gsubst_tm gsubst_ty].
  change (gsubst_tm ?x ?σ) with x⦃σ⦄; change (gsubst_ty ?x ?σ) with x⦃σ⦄.
  repeat rewrite ?gsubst_ren_ty', ?gsubst_ren. reflexivity.
Qed.
Lemma gs_wfIH l l' A N M c a cs :
  (wfIH l l' A N M c a cs)⦃σ⦄ = wfIH l l' A⦃σ⦄ N⦃σ⦄ M⦃σ⦄ c⦃σ⦄ a⦃σ⦄ cs⦃σ⦄.
Proof.
  unfold wfIH. rewrite gs_lam, gs_elimWf, gs_tmNth, gs_var, gs_tyFin.
  repeat rewrite ?gsubst_ren_ty', ?gsubst_ren, ?gsubst_subst, ?gs_tyWf. reflexivity.
Qed.
End PushGS.

(** [push_gsubst]: generated by [tools/gen_push.py] from its lemma list. *)
Ltac push_gsubst_at h k := lazymatch h with
  | @tyNat => k gs_tyNat
  | @tyPi => k gs_tyPi
  | @tyU => k gs_tyU
  | @tyEl => k gs_tyEl
  | @tyCTyp => k gs_tyCTyp
  | @tyCTrm => k gs_tyCTrm
  | @var => k gs_var
  | @tmNat => k gs_tmNat
  | @tmPi => k gs_tmPi
  | @tmU => k gs_tmU
  | @zero => k gs_zero
  | @succ => k gs_succ
  | @natrec => k gs_natrec
  | @lam => k gs_lam
  | @app => k gs_app
  | @boxT => k gs_boxT
  | @boxt => k gs_boxt
  | @letboxT => k gs_letboxT
  | @letboxt => k gs_letboxt
  | @cnil => k gs_cnil
  | @cext => k gs_cext
  | @lshift => k gs_lshift
  | @tyGvar => k gs_tyGvar
  | @gvar => k gs_gvar
  | @cvar => k gs_cvar
  | @elimT => k gs_elimT
  | @elimt => k gs_elimt
  | @tyUPi => k gs_tyUPi
  | @ulam => k gs_ulam
  | @uapp => k gs_uapp
  | @tyCPi => k gs_tyCPi
  | @tyTPi => k gs_tyTPi
  | @clam => k gs_clam
  | @capp => k gs_capp
  | @tlam => k gs_tlam
  | @tapp => k gs_tapp
  | @tySig => k gs_tySig
  | @tySum => k gs_tySum
  | @tmInl => k gs_inl
  | @tmInr => k gs_inr
  | @tmCase => k gs_case
  | @tyW => k gs_tyW
  | @tyVec => k gs_tyVec
  | @tyFin => k gs_tyFin
  | @tmSup => k gs_sup
  | @tmElimW => k gs_elimW
  | @wIH => k gs_wIH
  | @tyWf => k gs_tyWf
  | @tmSupf => k gs_supf
  | @tmElimWf => k gs_elimWf
  | @tmNth => k gs_tmNth
  | @wfIH => k gs_wfIH
  | @tySq => k gs_tySq
  | @tmSq => k gs_sq
  | @tmElimSq => k gs_elimSq
  | @tmSig => k gs_tmSig
  | @tmPair => k gs_pair
  | @tmFst => k gs_fst
  | @tmSnd => k gs_snd
  | @tyUnit => k gs_tyUnit
  | @tmUnit => k gs_tmUnit
  | @tmSEmpty => k gs_tmSEmpty
  | @tmEmpty => k gs_tmEmpty
  | @tmSum => k gs_tmSum
  | @tmW => k gs_tmW
  | @tmVec => k gs_tmVec
  | @tmWf => k gs_tmWf
  | @tmFin => k gs_tmFin
  | @tmTriv => k gs_triv
  | @gdef => k gs_gdef
  | @tySEq => k gs_tySEq
  | @tySEmpty => k gs_tySEmpty
  | @tyEmpty => k gs_tyEmpty
  | @srefl => k gs_srefl
  | @elimSEmpty => k gs_elimSEmpty
  | @elimEmpty => k gs_elimEmpty
  | @tyId => k gs_tyId
  | @tmRefl => k gs_refl
  | @tmId => k gs_tmId
  | @tmSEq => k gs_tmSEq
  | @tmJ => k gs_J
  end.
Ltac push_gsubst := repeat match goal with
  | |- context [@gsubst _ _ ?t _] => let h := head_of t in push_gsubst_at h ltac:(fun L => rewrite L)
  end.

Lemma gs_single_ty (M : ty) a σ : M[lsingle a]⦃σ⦄ = M⦃σ⦄[lsingle a⦃σ⦄].
Proof. rewrite gsubst_subst_ty; reflexivity. Qed.
Lemma gs_single (b a : tm) σ : b[lsingle a]⦃σ⦄ = b⦃σ⦄[lsingle a⦃σ⦄].
Proof. rewrite gsubst_subst; reflexivity. Qed.
Lemma gs_single2 (z t q : tm) σ : z[lsingle2 t q]⦃σ⦄ = z⦃σ⦄[lsingle2 t⦃σ⦄ q⦃σ⦄].
Proof. rewrite gsubst_subst; reflexivity. Qed.
Lemma gs_single2_ty (M : ty) t q σ : M[lsingle2 t q]⦃σ⦄ = M⦃σ⦄[lsingle2 t⦃σ⦄ q⦃σ⦄].
Proof. rewrite gsubst_subst_ty; reflexivity. Qed.
Lemma gs_lsucc_ty (M : ty) σ : M[lsucc]⦃σ⦄ = M⦃σ⦄[lsucc].
Proof. rewrite gsubst_subst_ty; reflexivity. Qed.
Lemma gs_ren (t : tm) r σ : t⟨r⟩⦃σ⦄ = t⦃σ⦄⟨r⟩.
Proof. apply gsubst_ren. Qed.
Lemma gs_single3 (c a f h : tm) σ : c[lsingle3 a f h]⦃σ⦄ = c⦃σ⦄[lsingle3 a⦃σ⦄ f⦃σ⦄ h⦃σ⦄].
Proof. rewrite gsubst_subst; reflexivity. Qed.

(** The letbox body's type [M⟪↑⟫[box U^id/x]] under [⇑σ]. *)
Lemma gs_letbox_ty (M : ty) b σ : b⦃gup σ⦄ = b ->
  M⟪S⟫[lsingle b]⦃gup σ⦄ = M⦃σ⦄⟪S⟫[lsingle b].
Proof. intros Hb. rewrite gs_single_ty, Hb, gshift_up_ty; reflexivity. Qed.

Ltac gs_rewrite :=
  rewrite ?gs_single_ty, ?gs_single, ?gs_single2, ?gs_single3, ?gs_single2_ty, ?gs_lsucc_ty, ?gsubst_ren_ty', ?gs_ren.

Lemma gs_tm_regty G i Δ x T T' l :
  [ G ; Δ ⊢[ i ] x : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? ->. Qed.
Lemma gs_eqtm_regty G i Δ x y T T' l :
  [ G ; Δ ⊢[ i ] x ≅ y : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? ->. Qed.

(* twice: [case]'s branch types (M12b) shift summands inside an injection *)
Ltac gs_eq := push_gsubst; gs_rewrite; push_gsubst; gs_rewrite; push_gsubst; first [reflexivity | f_equal; reflexivity].

#[export] Hint Resolve in_ctx_gsubst gsw_glob : gsub.
#[export] Hint Resolve wfc_nil wfc_var wfc_ext wfg_ty wfg_tm lequiv_wf_l lequiv_wf_r : gsub.
#[export] Hint Extern 5 (wf_tm _ _ _ _ _ _) => eapply gs_tm_regty; [ | gs_eq ] : gsub.
#[export] Hint Extern 5 (eq_tm _ _ _ _ _ _ _) => eapply gs_eqtm_regty; [ | gs_eq ] : gsub.
#[export] Hint Extern 1 (lwf _ _) => (cbn; first [exact I | assumption]) : gsub.
#[export] Hint Extern 1 (lequiv _ _ _) => (cbn; assumption) : gsub.
#[export] Hint Extern 1 (lle _ _) => assumption : gsub.
#[export] Hint Extern 1 (_ <> _) => assumption : gsub.
#[export] Hint Extern 1 (ty_leq _ _) =>
  apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl | assumption] : gsub.
#[export] Hint Extern 1 (tm_leq _ _) =>
  apply (proj1 (proj2 leq_gsubst_all)); [intros; apply gobj_leq_refl | assumption] : gsub.
#[export] Hint Extern 1 (compt _) =>
  first [assumption | apply compt_typeof | (left; reflexivity) | (right; reflexivity)] : gsub.
#[export] Hint Extern 1 (_ = _ \/ _ = _) => first [left; reflexivity | right; reflexivity] : gsub.

Ltac gs_premises := eauto 6 with gsub.

Ltac gs_step := any_rule gs_premises.

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
  (* defined globals (M9): a well-formed σ sends them to defined globals *)
  | Hσ : gsub_wf _ ?σ _, Hin : in_gctx _ ?u (gdDef ?Δ _ _ _) |- wf_tm _ _ _ (pdef (?σ ?u) _ _) _ _ =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ Hin) as Ho; cbn in Ho;
      rewrite gsubst_subst_ty; destruct (σ u); cbn in *; try contradiction;
      eapply wf_gdef with (Δ := Δ⦃σ⦄); [ .. | gs_entries | gs_premise ];
      first [exact Ho | assumption | gs_ctx | gs_tail | gs_dnfl | solve [eauto with gsub]]
  | Hσ : gsub_wf _ ?σ _, Hin : in_gctx _ ?u (gdDef ?Δ _ _ _) |- eq_tm _ _ _ (pdef (?σ ?u) _ _) (pdef _ _ _) _ _ =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ Hin) as Ho; cbn in Ho;
      rewrite gsubst_subst_ty; destruct (σ u); cbn in *; try contradiction;
      eapply eqtm_gdef with (Δ := Δ⦃σ⦄); [ .. | gs_entries | gs_entries | gs_entries | gs_premise ];
      first [exact Ho | assumption | gs_ctx | gs_tail | gs_dnfl | solve [eauto with gsub]]
  | Hσ : gsub_wf _ ?σ _, Hin : in_gctx _ ?u (gdDef ?Δ _ _ _) |- eq_tm _ _ _ (pdef (?σ ?u) _ _) _ _ _ =>
      let Ho := fresh "Ho" in pose proof (gsw_var _ _ _ Hσ _ _ Hin) as Ho; cbn in Ho;
      rewrite gsubst_subst_ty, gsubst_subst; destruct (σ u); cbn in *; try contradiction;
      eapply eqtm_delta with (Δ := Δ⦃σ⦄); [ .. | gs_entries | gs_premise ];
      first [exact Ho | assumption | gs_ctx | gs_tail | gs_dnfl | solve [eauto with gsub]]
  end.

(** [UΠ] (M4): [σ] under the [n] level binders is [guwkn n σ]. *)
Lemma uren_ush_gsubst_ctx n (Γ : ctx) σ : gdnf σ -> Γ⟨ush n⟩ᵤ⦃guwkn n σ⦄ = Γ⦃σ⦄⟨ush n⟩ᵤ.
Proof. intros Hσ. symmetry; apply (proj1 (proj2 (proj2 uren_gsubst_all))). intros i; apply guwkn_lk, Hσ. Qed.
Lemma uren_ush_gsubst_tm n (t : tm) σ : gdnf σ -> t⟨ush n⟩ᵤ⦃guwkn n σ⦄ = t⦃σ⦄⟨ush n⟩ᵤ.
Proof. intros Hσ. symmetry; apply (proj1 (proj2 uren_gsubst_all)). intros i; apply guwkn_lk, Hσ. Qed.

Lemma gousubst_gouren_uext o n ls : length ls = n -> dnfo o ->
  gousubst (gouren o (ush n)) (uext ls lvar) = o.
Proof.
  intros Hn Ho. destruct o; cbn in *; f_equal.
  - rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ lvar) by (intros; symmetry; apply uext_ush_lvar, Hn).
    apply usubst_id_ctx; auto.
  - rewrite (proj1 uren_usubst_all _ _ _ lvar) by (intros; symmetry; apply uext_ush_lvar, Hn).
    apply usubst_id_ty; auto.
  - rewrite (proj1 (proj2 uren_usubst_all) _ _ _ lvar) by (intros; symmetry; apply uext_ush_lvar, Hn).
    apply usubst_id; auto.
Qed.
Lemma gsubst_uinst_ty n ls (T : ty) σ : length ls = n -> gdnf σ ->
  T[uext ls lvar]ᵤ⦃σ⦄ = T⦃guwkn n σ⦄[uext ls lvar]ᵤ.
Proof.
  intros Hn Hσ. rewrite usubst_gsubst_ty. apply (proj1 gsubst_ext_all); intros i.
  rewrite guwkn_lk by apply Hσ. symmetry; apply gousubst_gouren_uext; auto.
Qed.
Lemma gsubst_uinst_tm n ls (t : tm) σ : length ls = n -> gdnf σ ->
  t[uext ls lvar]ᵤ⦃σ⦄ = t⦃guwkn n σ⦄[uext ls lvar]ᵤ.
Proof.
  intros Hn Hσ. rewrite usubst_gsubst. apply (proj1 (proj2 gsubst_ext_all)); intros i.
  rewrite guwkn_lk by apply Hσ. symmetry; apply gousubst_gouren_uext; auto.
Qed.

Ltac gs_upi_body :=
  match goal with
  | IH : forall Ψ'' σ', gsub_wf (mkG (gL (gctx_uwk ?n ?G)) Ψ'') σ' (gctx_uwk ?n ?G) -> _,
    Hσ : gsub_wf (mkG (gL ?G) ?Ψ') ?σ ?G |- _ =>
      let X := fresh "X" in
      pose proof (IH _ _ (gsub_wf_uwkn n _ _ _ Hσ)) as X;
      rewrite (uren_ush_gsubst_ctx n _ _ (gsw_dnf _ _ _ Hσ)) in X; exact X
  end.
Ltac gs_upi_rw :=
  match goal with Hσ : gsub_wf _ ?σ _ |- _ =>
    try match goal with Hn : length ?ls = ?n |- _ =>
      rewrite ?(gsubst_uinst_ty n ls _ σ Hn (gsw_dnf _ _ _ Hσ)),
        ?(gsubst_uinst_tm n ls _ σ Hn (gsw_dnf _ _ _ Hσ)) end;
    rewrite ?(uren_ush_gsubst_tm _ _ σ (gsw_dnf _ _ _ Hσ))
  end.
Ltac gs_upi :=
  match goal with
  | |- wf_ty _ _ _ (tyUPi _ _ _) _ => eapply wft_upi; try gs_upi_body; gs_premise
  | |- eq_ty _ _ _ (tyUPi _ _ _) _ _ => eapply eqty_upi; try gs_upi_body; gs_premise
  | |- wf_tm _ _ _ (ulam _ _ _ _) _ _ => eapply wf_ulam; try gs_upi_body; gs_premise
  | |- eq_tm _ _ _ (ulam _ _ _ (uapp _ (ubvars _))) _ _ _ =>
      gs_upi_rw; eapply eqtm_ueta; try gs_upi_body; gs_premise
  | |- eq_tm _ _ _ (ulam _ _ _ _) _ _ _ => eapply eqtm_ulam; try gs_upi_body; gs_premise
  | |- wf_tm _ _ _ (uapp _ _) _ _ => gs_upi_rw; eapply wf_uapp; try gs_upi_body; gs_premise
  | |- eq_tm _ _ _ (uapp (ulam _ _ _ _) _) _ _ _ =>
      gs_upi_rw; eapply eqtm_ubeta; try gs_upi_body; gs_premise
  | |- eq_tm _ _ _ (uapp _ _) _ _ _ => gs_upi_rw; eapply eqtm_uapp; try gs_upi_body; gs_premise
  end.

(** The letbox body, typed under [Ψ, U], under [⇑σ]. *)
Ltac gs_body :=
  match goal with
  | IH : forall Ψ'' σ', gsub_wf _ σ' (gext ?G ?D) -> _,
    Hσ : gsub_wf _ ?σ ?G |- _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext {| gL := gL G ; gΨ := _ |} (gdecl_gsubst D σ) ])
        by (unfold gext; cbn [gdecl_gsubst gΨ gL]; first [eapply wfg_ctx | eapply wfg_ty | eapply wfg_tm];
            eauto with gsub);
      pose proof (IH _ (gup σ) (gsub_wf_up _ _ _ D Hσ Hg)) as X;
      rewrite gshift_up_ctx, ?gs_letbox_ty in X by reflexivity; exact X
  end.

(** The meta-functions (M5): the instances under [σ]. *)
Ltac gs_mf_rw :=
  match goal with Hσ : gsub_wf _ ?σ _ |- _ =>
    rewrite ?(gs_gsingle_ty _ _ σ (gsw_dnf _ _ _ Hσ)), ?(gs_gsingle _ _ σ (gsw_dnf _ _ _ Hσ)),
      ?gshift_up_tm; cbn [gosubst]
  end.

(** [J] (M11a): the motive context's [Id] type commutes with [σ] by an
    equation. *)
Ltac gs_Jprem :=
  first [ solve [eapply wf_ty_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eq]]
        | solve [eapply eq_ty_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eq]]
        | solve [eapply wf_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eq]]
        | gs_premise ].
Ltac gs_J :=
  match goal with
  | |- wf_tm _ _ _ (tmJ _ _ _ _ _ _ _ _) _ _ => eapply wf_J; gs_Jprem
  | |- eq_tm _ _ _ (tmJ _ _ _ _ _ _ _ (tmRefl _ _ _)) _ _ _ => eapply eqtm_J_beta; gs_Jprem
  | |- eq_tm _ _ _ (tmJ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_J; gs_Jprem
  end.

(** [elim_W]'s step (M13a): its context and type hold shifted types, which
    commute with [σ] by an equation. *)
Ltac gs_eqW := do 3 (push_gsubst; gs_rewrite); push_gsubst; reflexivity.
Ltac gs_Wprem :=
  first [ solve [eapply wf_tm_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eqW | gs_eqW]]
        | solve [eapply eq_tm_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eqW | gs_eqW]]
        | solve [eapply wf_ty_regboth;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eqW | gs_eqW]]
        | solve [eapply wf_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gsub] end | gs_eqW]]
        | gs_premise ].

Ltac gs_manual2 :=
  match goal with
  (* [Wf] (M15a) *)
  | |- wf_tm _ _ _ (tmSupf _ _ _ _ _) _ _ => eapply wf_supf; gs_Wprem
  | |- eq_tm _ _ _ (tmSupf _ _ _ _ _) _ _ _ => eapply eqtm_supf; gs_Wprem
  | |- wf_tm _ _ _ (tmElimWf _ _ _ _ _ _ _) _ _ => eapply wf_elimWf; gs_Wprem
  | |- eq_tm _ _ _ (tmElimWf _ _ _ _ _ _ (tmSupf _ _ _ _ _)) _ _ _ => eapply eqtm_elimWf_supf; gs_Wprem
  | |- eq_tm _ _ _ (tmElimWf _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimWf; gs_Wprem
  (* [W] (M13a) *)
  | |- wf_tm _ _ _ (tmSup _ _ _ _ _ _) _ _ => eapply wf_sup; gs_Wprem
  | |- eq_tm _ _ _ (tmSup _ _ _ _ _ _) _ _ _ => eapply eqtm_sup; gs_Wprem
  | |- wf_tm _ _ _ (tmElimW _ _ _ _ _ _ _ _) _ _ => eapply wf_elimW; gs_Wprem
  | |- eq_tm _ _ _ (tmElimW _ _ _ _ _ _ _ (tmSup _ _ _ _ _ _)) _ _ _ => eapply eqtm_elimW_sup; gs_Wprem
  | |- eq_tm _ _ _ (tmElimW _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimW; gs_Wprem
  (* [ind_∥∥] (M16a): its step's type, through the induction hypotheses *)
  | |- wf_tm _ _ _ (tmElimSq _ _ _ _ _ _) _ _ => eapply wf_elimSq; gs_premise
  | |- eq_tm _ _ _ (tmElimSq _ _ _ _ _ (tmSq _ _ _)) _ _ _ => eapply eqtm_elimSq_sq; gs_premise
  | |- eq_tm _ _ _ (tmElimSq _ _ _ _ _ _) _ _ _ => eapply eqtm_elimSq; gs_premise
  (* [case] (M12b): its branches' types, through the induction hypotheses *)
  | |- wf_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ _) _ _ => eapply wf_case; gs_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ (tmInl _ _ _ _ _)) _ _ _ => eapply eqtm_case_inl; gs_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ (tmInr _ _ _ _ _)) _ _ _ => eapply eqtm_case_inr; gs_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_case; gs_premise
  | |- wf_ty _ _ _ (tyCPi _ _) _ => eapply wft_cpi; try gs_body; gs_premise
  | |- wf_ty _ _ _ (tyTPi _ _ _ _) _ => eapply wft_tpi; try gs_body; gs_premise
  | |- eq_ty _ _ _ (tyCPi _ _) _ _ => eapply eqty_cpi; try gs_body; gs_premise
  | |- eq_ty _ _ _ (tyTPi _ _ _ _) _ _ => eapply eqty_tpi; try gs_body; gs_premise
  | |- wf_tm _ _ _ (clam _ _ _) _ _ => eapply wf_clam; try gs_body; gs_premise
  | |- wf_tm _ _ _ (tlam _ _ _ _ _) _ _ => eapply wf_tlam; try gs_body; gs_premise
  | |- wf_tm _ _ _ (capp _ _) _ _ => gs_mf_rw; eapply wf_capp; try gs_body; gs_premise
  | |- wf_tm _ _ _ (tapp _ _) _ _ => gs_mf_rw; eapply wf_tapp; try gs_body; gs_premise
  | |- eq_tm _ _ _ (clam _ _ (capp _ _)) _ _ _ => gs_mf_rw; eapply eqtm_ceta; try gs_body; gs_premise
  | |- eq_tm _ _ _ (tlam _ _ _ _ (tapp _ _)) _ _ _ => gs_mf_rw; eapply eqtm_teta; try gs_body; gs_premise
  | |- eq_tm _ _ _ (clam _ _ _) _ _ _ => eapply eqtm_clam; try gs_body; gs_premise
  | |- eq_tm _ _ _ (tlam _ _ _ _ _) _ _ _ => eapply eqtm_tlam; try gs_body; gs_premise
  | |- eq_tm _ _ _ (capp (clam _ _ _) _) _ _ _ => gs_mf_rw; eapply eqtm_cbeta; try gs_body; gs_premise
  | |- eq_tm _ _ _ (tapp (tlam _ _ _ _ _) _) _ _ _ => gs_mf_rw; eapply eqtm_tbeta; try gs_body; gs_premise
  | |- eq_tm _ _ _ (capp _ _) _ _ _ => gs_mf_rw; eapply eqtm_capp; try gs_body; gs_premise
  | |- eq_tm _ _ _ (tapp _ _) _ _ _ => gs_mf_rw; eapply eqtm_tapp; try gs_body; gs_premise
  (* the unit type (M8c) *)
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
  | IH : forall k, k < nbr -> forall Ψ'' σ', gsub_wf (mkG (gL (brG k ?G)) Ψ'') σ' (brG k ?G) -> _,
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
  end;
  (* and the meta-functions' instances (M5) *)
  try gs_mf_rw.

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
  (* level equivalence at M *)
  | |- eq_ty _ lM _ _ _ _ => eapply eqty_leq; gs_premise
  | |- eq_tm _ lM _ _ _ _ _ => eapply eqtm_leq; gs_premise
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
  (* manual cases first, when they close the goal: a failing [gs_step]
     backtracks through every rule *)
  all: try (notrec; first [solve [gs_J] | solve [gs_manual] | solve [gs_manual2] | solve [gs_upi]]).
  all: try (notrec; gs_step).
  all: try (notrec; gs_manual).
  all: try (notrec; gs_manual2).
  all: try (notrec; any_rule gs_premise).
  all: try (notrec; gs_upi).
  all: gs_rec.
Qed.

(** ** Declared bindings are well formed *)

Definition decl_ok (G : gctx) (D : gdecl) : Prop :=
  match D with
  | gdCtx => True
  | gdTy Δ i l => [ G ; Δ ⊢[ lD ] ] /\ lwf (gL G) l
  | gdTm Δ i T l => [ G ; Δ ⊢[ lD ] ] /\ [ G ; Δ ⊢[ lD ] T @ l ] /\ lwf (gL G) l
  | gdDef Δ T l t => [ G ; Δ ⊢[ lD ] ] /\ [ G ; Δ ⊢[ lD ] T @ l ] /\ lwf (gL G) l /\
      [ G ; Δ ⊢[ lC ] t : T @ l ]
  end.

Lemma decl_ok_wk1 L Ψ D0 D : [ ⊢ mkG L (D0 :: Ψ) ] -> decl_ok (mkG L Ψ) D ->
  decl_ok (mkG L (D0 :: Ψ)) (gdecl_ren D S).
Proof.
  intros Hg HD.
  assert (Hw : gwk_wf (gwk_step gwk_id) (D0 :: Ψ) Ψ) by (constructor; constructor).
  destruct D; cbn in *; auto.
  - destruct HD as [HΔ Hl]. split; [|exact Hl].
    exact (proj1 (proj2 gweakening) _ _ _ HΔ _ _ _ (le_n _) Hw Hg).
  - destruct HD as (HΔ & HT & Hl). refine (conj _ (conj _ Hl)).
    + exact (proj1 (proj2 gweakening) _ _ _ HΔ _ _ _ (le_n _) Hw Hg).
    + exact (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ HT _ _ _ (le_n _) Hw Hg).
  - destruct HD as (HΔ & HT & Hl & Ht). refine (conj _ (conj _ (conj Hl _))).
    + exact (proj1 (proj2 gweakening) _ _ _ HΔ _ _ _ (le_n _) Hw Hg).
    + exact (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ HT _ _ _ (le_n _) Hw Hg).
    + exact (proj1 (proj2 (proj2 (proj2 gweakening))) _ _ _ _ _ _ Ht _ _ _ (le_n _) Hw Hg).
Qed.

Lemma gctx_decl_ok G n D : [ ⊢ G ] -> in_gctx (gΨ G) n D -> decl_ok G D.
Proof.
  destruct G as [L Ψ]; cbn. intros Hg Hin; revert Hg; induction Hin as [Ψ D | Ψ D D' n Hin IH]; intros Hg.
  - apply decl_ok_wk1; [exact Hg|]. inversion Hg; subst; cbn; auto.
    all: repeat split; auto;
      first [ exact (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ ltac:(eassumption))
            | eapply lift_tm; [eassumption | unfold lle; cbn; lia] ].
  - apply decl_ok_wk1; [exact Hg|]. apply IH. inversion Hg; subst; assumption.
Qed.

(** ** Single global substitutions (the letbox β-rules) *)

Lemma gdecl_gsubst_ren_single D o : dnf_decl D -> gdecl_gsubst (gdecl_ren D S) (gsingle o) = D.
Proof.
  intros HD; destruct D; cbn in *; f_equal; try reflexivity.
  all: first
    [ rewrite (gsubst_gren_ctx _ _ _ (fun j => GId j)) by reflexivity; apply gsubst_id_ctx; [tauto | auto]
    | rewrite (gsubst_gren_ty _ _ _ (fun j => GId j)) by reflexivity; apply gsubst_id_ty; [tauto | auto]
    | rewrite (gsubst_gren_tm _ _ _ (fun j => GId j)) by reflexivity; apply gsubst_id; [tauto | auto] ].
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
  - exact Hm.
Qed.
