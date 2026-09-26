(** * Equations between the recursors' motive instances (M6_DESIGN.md H8)

    The recursors' typing rules take the motive-instance equation as a
    premise (M3_DESIGN.md E10). Its syntactic ingredients are here: level
    equivalence ([≡ₗ]) of instances at related arguments, and instances of
    an equation between motives. Functionality in the context object is a
    consequence of the fundamental theorem (DeclConsequences). *)
From DeLaM.Typing Require Export Presupposition.

(** ** [≡ₗ] of the instances *)

Lemma peelU_leq b b' l l' : tm_leq b b' -> leqv l l' -> tm_leq (peelU b l) (peelU b' l').
Proof.
  intros Hb Hl. destruct b; destruct b'; first [exact I | exact (False_ind _ Hb) | cbn in Hb |- *].
  apply (proj1 (proj2 leq_usubst_all)); [intros [|n]; cbn; [exact Hl | apply leqv_refl] | exact Hb].
Qed.

Lemma peelG_leq b b' o o' : tm_leq b b' -> gobj_leq o o' -> tm_leq (peelG b o) (peelG b' o').
Proof.
  intros Hb Ho. destruct b; destruct b'; first [exact I | exact (False_ind _ Hb) | cbn in Hb |- *].
  apply (proj1 (proj2 leq_gsubst_all)); [intros [|n]; cbn; [exact Ho | reflexivity] | exact Hb].
Qed.

Lemma peelL_leq b b' a a' : tm_leq b b' -> tm_leq a a' -> tm_leq (peelL b a) (peelL b' a').
Proof.
  intros Hb Ha. destruct b; destruct b'; first [exact I | exact (False_ind _ Hb) | cbn in Hb |- *].
  apply (proj1 (proj2 leq_subst_all)); [split; [reflexivity | exact Ha] | exact Hb].
Qed.

Lemma getTy_leq t t' : tm_leq t t' -> ty_leq (getTy t) (getTy t').
Proof.
  intros H. destruct t; destruct t'; first [exact (ty_leq_refl tyErr) | exact (False_ind _ H) | exact H].
Qed.

Lemma motT_leq w w' lv lv' g g' c c' : tm_leq w w' -> leqv lv lv' -> ctx_leq g g' -> tm_leq c c' ->
  ty_leq (motT w lv g c) (motT w' lv' g' c').
Proof.
  intros Hw Hl Hg Hc. unfold motT.
  apply getTy_leq, peelL_leq; [apply peelG_leq; [apply peelU_leq |] | ]; assumption.
Qed.

Lemma mott_leq w w' lv lv' g g' U U' c c' : tm_leq w w' -> leqv lv lv' -> ctx_leq g g' ->
  ty_leq U U' -> tm_leq c c' -> ty_leq (mott w lv g U c) (mott w' lv' g' U' c').
Proof.
  intros Hw Hl Hg HU Hc. unfold mott.
  apply getTy_leq, peelL_leq; [apply peelG_leq; [apply peelG_leq; [apply peelU_leq |] |] |]; assumption.
Qed.

(** ** Instances of an equation between motives (as [motT_wf], [mott_wf]) *)

Lemma motT_eq_inst G Γ MT MT' l1 l Δ t :
  [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t ≅ motT (wrapMT MT') l Δ t @ l1 ].
Proof.
  destruct G as [L Ψ]. intros HMT Hl HΔ Ht.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht)) as Hg.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ HMT L (usingle l)
                (usub_ok_single L l Hl)) as X1.
  rewrite (G_us_recGT _ _ _ Hg), lvsubst_ush1_single in X1.
  assert (Hσ : [ mkG L Ψ ⊢ gsingle (GCtx Δ) : mkG L (gdCtx :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) gdCtx); [exact Hg | exact (wf_ctx_dnf HΔ) | exact HΔ]. }
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gsubstitution)))) _ _ _ _ _ _ X1 Ψ _ Hσ) as X2.
  unfold gwk_to in X2; cbn [gL] in X2. change (gsubst ?x ?s) with (gcsubst x s) in X2 at 1.
  rewrite (recΓT_inst _ _ _ (wf_ctx_dnf (ctx_of_wf_tm (i := lM) eq_refl Ht))) in X2.
  exact (eqty_single (i := lM) eq_refl X2 Ht).
Qed.

Lemma mott_eq_inst G Γ Mt Mt' l2 l Δ T t :
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t ≅ mott (wrapMt Mt') l Δ T t @ l2 ].
Proof.
  destruct G as [L Ψ]. intros HMt Hl HΔ HT Ht.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht)) as Hg.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ HMt L (usingle l)
                (usub_ok_single L l Hl)) as X1.
  rewrite (G_us_recGt _ _ _ Hg), lvsubst_ush1_single in X1.
  assert (Hσ0 : [ mkG L Ψ ⊢ gsingle (GCtx Δ) : mkG L (gdCtx :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) gdCtx); [exact Hg | exact (wf_ctx_dnf HΔ) | exact HΔ]. }
  assert (Hg1 : [ ⊢ mkG L (gdTy Δ lD l :: Ψ) ]) by (apply wfg_ty; auto).
  assert (Hσ1 : [ mkG L (gdTy Δ lD l :: Ψ) ⊢ gup (gsingle (GCtx Δ)) : mkG L (gdTy (cvar 0) lD l :: gdCtx :: Ψ) ])
    by exact (gsub_wf_up _ _ _ (gdTy (cvar 0) lD l) Hσ0 Hg1).
  assert (Hσ2 : [ mkG L Ψ ⊢ gsingle (GTy T) : mkG L (gdTy Δ lD l :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) (gdTy Δ lD l)); [exact Hg | exact (wf_ty_dnf HT) |].
    rewrite gdecl_gsubst_ren_single by exact (wf_ctx_dnf HΔ). exact HT. }
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gsubstitution)))) _ _ _ _ _ _ X1 _ _ Hσ1) as X2.
  unfold gwk_to in X2; cbn [gL] in X2.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gsubstitution)))) _ _ _ _ _ _ X2 Ψ _ Hσ2) as X3.
  unfold gwk_to in X3; cbn [gL] in X3.
  change (gsubst (gsubst ?x ?s1) ?s2) with (gcsubst (gcsubst x s1) s2) in X3 at 1.
  rewrite (recΓt_inst _ _ _ _ (wf_ctx_dnf (ctx_of_wf_tm (i := lM) eq_refl Ht)) (wf_ctx_dnf HΔ) (wf_ty_nf HT)) in X3.
  exact (eqty_single (i := lM) eq_refl X3 Ht).
Qed.
