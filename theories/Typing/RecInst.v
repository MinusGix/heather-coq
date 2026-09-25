(** * Instances of the recursors' motives are well typed (M3)

    [M_Typ[l/ℓ, Δ/g, t/x_T]] and [M_Trm[l/ℓ, Δ/g, T/U_T, t/x_t]] are
    obtained from the motive's typing in its scope by the universe, global
    and local substitution lemmas, in that order; the global step sends
    the context variable [g] to the concrete context [Δ] (M3_DESIGN.md E9). *)
From DeLaM.Typing Require Export GSubstitution.

(** ** The motive scopes after instantiating the level *)

Lemma glob_dnf L Ψ : [ ⊢ mkG L Ψ ] -> forall D, In D Ψ -> dnf_decl D.
Proof.
  induction Ψ as [|D0 Ψ IH]; intros H D Hin; [destruct Hin|].
  destruct Hin as [<- | Hin]; inversion H; subst; eauto; cbn.
  all: first [ exact I | eapply wf_ctx_dnf; eassumption
             | split; [ eapply wf_ctx_dnf, (proj1 (proj2 (proj2 ctx_extract))); eassumption
                      | eapply wf_ty_dnf; eassumption ] ].
Qed.

Lemma gdecl_us_ur_single D l : dnf_decl D -> gdecl_usubst (gdecl_uren D (ush 1)) (usingle l) = D.
Proof.
  intros HD; destruct D; cbn [gdecl_uren gdecl_usubst dnf_decl] in *; f_equal.
  all: first
    [ reflexivity
    | rewrite (lvren_lvsubst _ _ _ lvar) by reflexivity; apply lvsubst_id; reflexivity
    | rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ lvar) by reflexivity;
      apply usubst_id_ctx; [tauto | auto]
    | rewrite (proj1 uren_usubst_all _ _ _ lvar) by reflexivity; apply usubst_id_ty; [tauto | auto] ].
Qed.

Lemma map_us_ur_single L Ψ l : [ ⊢ mkG L Ψ ] ->
  map (fun D => gdecl_usubst D (usingle l)) (map (fun D => gdecl_uren D (ush 1)) Ψ) = Ψ.
Proof.
  intros H. rewrite map_map. transitivity (map (fun D => D) Ψ); [| apply map_id].
  apply map_ext_in; intros D HD. apply gdecl_us_ur_single, (glob_dnf _ _ H _ HD).
Qed.

Lemma G_us_recGT L Ψ l : [ ⊢ mkG L Ψ ] ->
  G_us (recGT (mkG L Ψ)) L (usingle l) = mkG L (gdCtx :: Ψ).
Proof.
  intros H. unfold G_us, gctx_usubst, recGT, gctx_uwk; cbn [gL gΨ map gdecl_usubst].
  now rewrite (map_us_ur_single _ _ l H).
Qed.
Lemma G_us_recGt L Ψ l : [ ⊢ mkG L Ψ ] ->
  G_us (recGt (mkG L Ψ)) L (usingle l) = mkG L (gdTy (cvar 0) lD l :: gdCtx :: Ψ).
Proof.
  intros H. unfold G_us, gctx_usubst, recGt, gctx_uwk; cbn [gL gΨ map gdecl_usubst].
  now rewrite (map_us_ur_single _ _ l H).
Qed.

(** ** The motive contexts after instantiation *)

Lemma ctx_inst_base Γ l θ : dnfctx Γ -> (forall j, θ j = GId j) ->
  gcsubst (ucsubst (ucren Γ (ush 1)) (usingle l)) θ = Γ.
Proof.
  intros HΓ Hθ.
  rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ lvar) by reflexivity.
  transitivity (gcsubst Γ θ).
  - f_equal. apply usubst_id_ctx; auto.
  - apply gsubst_id_ctx; auto.
Qed.

Lemma recΓT_inst Γ l Δ : dnfctx Γ ->
  gcsubst (ucsubst (recΓT Γ) (usingle l)) (gsingle (GCtx Δ)) = Γ ,, tyCTyp Δ l @ lzero.
Proof.
  intros HΓ. unfold recΓT, wkc. cbn [ucsubst gcsubst usubst_ty gsubst_ty lvsubst usingle pctx gsingle].
  f_equal. rewrite (proj1 (proj2 (proj2 usubst_gren_all))).
  rewrite (proj1 (proj2 (proj2 gsubst_gren_all)) _ _ _ (fun j => GId j)) by reflexivity.
  apply ctx_inst_base; auto.
Qed.

Lemma recΓt_inst Γ l Δ T : dnfctx Γ -> dnfctx Δ -> nfty T ->
  gcsubst (gcsubst (ucsubst (recΓt Γ) (usingle l)) (gup (gsingle (GCtx Δ)))) (gsingle (GTy T)) =
  Γ ,, tyCTrm Δ T l @ lzero.
Proof.
  intros HΓ HΔ HT. unfold recΓt, wkc, gv.
  cbn [ucsubst gcsubst usubst_ty gsubst_ty ulsubst lvsubst usingle pctx pty gsingle gup goren glsubst].
  f_equal.
  - rewrite (proj1 (proj2 (proj2 usubst_gren_all))).
    rewrite (proj1 (proj2 (proj2 gsubst_gren_all)) _ _ _ (fun j => goren (GId j) S)) by reflexivity.
    rewrite (proj1 (proj2 (proj2 gsubst_gsubst_all)) _ _ _ (fun j => GId j)) by reflexivity.
    apply ctx_inst_base; auto.
  - f_equal.
    + rewrite (proj1 (proj2 (proj2 gsubst_gren_all)) _ _ _ (fun j => GId j)) by reflexivity.
      apply gsubst_id_ctx; auto.
    + apply subst_id_ty; [exact HT | intros n; cbn; f_equal; lia].
Qed.

(** ** The motive instances *)

Lemma lvsubst_ush1_single l1 l : lvsubst (lvren l1 (ush 1)) (usingle l) = l1.
Proof. rewrite (lvren_lvsubst _ _ _ lvar) by reflexivity. apply lvsubst_id; reflexivity. Qed.

Lemma motT_wf G Γ MT l1 l Δ t :
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t @ l1 ].
Proof.
  destruct G as [L Ψ]. intros HMT Hl HΔ Ht.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht)) as Hg.
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ HMT L (usingle l) (usub_ok_single L l Hl)) as X1.
  rewrite (G_us_recGT _ _ _ Hg), lvsubst_ush1_single in X1.
  assert (Hσ : [ mkG L Ψ ⊢ gsingle (GCtx Δ) : mkG L (gdCtx :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) gdCtx); [exact Hg | exact (wf_ctx_dnf HΔ) | exact HΔ]. }
  pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X1 Ψ _ Hσ) as X2.
  unfold gwk_to in X2; cbn [gL] in X2. change (gsubst ?x ?s) with (gcsubst x s) in X2 at 1.
  rewrite (recΓT_inst _ _ _ (wf_ctx_dnf (ctx_of_wf_tm (i := lM) eq_refl Ht))) in X2.
  exact (wf_ty_single (i := lM) eq_refl X2 Ht).
Qed.

Lemma mott_wf G Γ Mt l2 l Δ T t :
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t @ l2 ].
Proof.
  destruct G as [L Ψ]. intros HMt Hl HΔ HT Ht.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht)) as Hg.
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ HMt L (usingle l) (usub_ok_single L l Hl)) as X1.
  rewrite (G_us_recGt _ _ _ Hg), lvsubst_ush1_single in X1.
  assert (Hσ0 : [ mkG L Ψ ⊢ gsingle (GCtx Δ) : mkG L (gdCtx :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) gdCtx); [exact Hg | exact (wf_ctx_dnf HΔ) | exact HΔ]. }
  assert (Hg1 : [ ⊢ mkG L (gdTy Δ lD l :: Ψ) ]) by (apply wfg_ty; auto).
  assert (Hσ1 : [ mkG L (gdTy Δ lD l :: Ψ) ⊢ gup (gsingle (GCtx Δ)) : mkG L (gdTy (cvar 0) lD l :: gdCtx :: Ψ) ])
    by exact (gsub_wf_up _ _ _ (gdTy (cvar 0) lD l) Hσ0 Hg1).
  assert (Hσ2 : [ mkG L Ψ ⊢ gsingle (GTy T) : mkG L (gdTy Δ lD l :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) (gdTy Δ lD l)); [exact Hg | exact (wf_ty_dnf HT) |].
    rewrite gdecl_gsubst_ren_single by exact (wf_ctx_dnf HΔ). exact HT. }
  pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X1 _ _ Hσ1) as X2.
  unfold gwk_to in X2; cbn [gL] in X2.
  pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X2 Ψ _ Hσ2) as X3.
  unfold gwk_to in X3; cbn [gL] in X3.
  change (gsubst (gsubst ?x ?s1) ?s2) with (gcsubst (gcsubst x s1) s2) in X3 at 1.
  rewrite (recΓt_inst _ _ _ _ (wf_ctx_dnf (ctx_of_wf_tm (i := lM) eq_refl Ht)) (wf_ctx_dnf HΔ) (wf_ty_nf HT)) in X3.
  exact (wf_ty_single (i := lM) eq_refl X3 Ht).
Qed.
