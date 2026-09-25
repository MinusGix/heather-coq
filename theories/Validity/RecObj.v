(** * Related images from syntax (M3_DESIGN.md E13)

    Well-typed images at a static declaration, [≡ₗ]-related and
    declaratively equal at P, are related as images of related global
    substitutions: the fundamental theorem at P at the identity instance
    gives their validity at both instances. *)
From DeLaM.Validity Require Export ReducibleP.

Section RecObj.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation VTyGP := (@VTyG EP LR_P).
Local Notation VTyGM := (@VTyG EM LR_P).
Local Notation VTmGP := (@VTmG EP LR_P).
Local Notation VTmGM := (@VTmG EM LR_P).
Local Notation CtxRelGP := (@CtxRelG EP LR_P).
Local Notation CtxRelGM := (@CtxRelG EM LR_P).

Lemma VTyG_of_eq {G Δ T T' l} : [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] -> VTyGP G Δ T T' l /\ VTyGM G Δ T T' l.
Proof.
  intros H. destruct (proj1 (proj2 (proj2 (proj2 (proj2 (fundamentalS EP EM))))) _ _ _ _ _ _ H eq_refl)
    as (_ & VP & VM).
  pose proof (eqty_wf_l (i := lD) eq_refl H) as HT. pose proof (eqty_wf_r (i := lD) eq_refl H) as HT'.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HT) as HΔ. pose proof (ctx_glob _ _ _ HΔ) as HG.
  pose proof (VP _ _ _ (GSubRel_gid EP EM HG)) as X. pose proof (VM _ _ _ (GSubRel_gid EP EM HG)) as Y.
  rewrite gsubst_id_ctx, !gsubst_id_ty in X, Y
    by first [exact (wf_ctx_dnf HΔ) | exact (wf_ty_dnf HT) | exact (wf_ty_dnf HT') | reflexivity].
  exact (conj X Y).
Qed.

Lemma VTmG_of_eq {G Δ t t' A l} : [ G ; Δ ⊢[ lD ] t ≅ t' : A @ l ] ->
  VTmGP G Δ t t' A l /\ VTmGM G Δ t t' A l.
Proof.
  intros H. destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalS EP EM)))))) _ _ _ _ _ _ _ H eq_refl)
    as (_ & _ & _ & VP & VM).
  pose proof (eqtm_wf_l (i := lD) eq_refl H) as Ht. pose proof (eqtm_wf_r (i := lD) eq_refl H) as Ht'.
  pose proof (wf_tm_ty (i := lD) eq_refl Ht) as HA.
  pose proof (ctx_of_wf_ty (i := lD) eq_refl HA) as HΔ. pose proof (ctx_glob _ _ _ HΔ) as HG.
  pose proof (VP _ _ _ (GSubRel_gid EP EM HG)) as X. pose proof (VM _ _ _ (GSubRel_gid EP EM HG)) as Y.
  rewrite gsubst_id_ctx, gsubst_id_ty, !gsubst_id in X, Y
    by first [exact (wf_ctx_dnf HΔ) | exact (wf_ty_dnf HA) | exact (wf_tm_dnf Ht) | exact (wf_tm_dnf Ht')
             | reflexivity].
  exact (conj X Y).
Qed.

Lemma CtxRelG_of_eq {G Δ Δ'} : [ G ⊢[ lD ] Δ ≅ Δ' ] -> CtxRelGP G Δ Δ' /\ CtxRelGM G Δ Δ'.
Proof.
  intros H. destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalS EP EM)))))) _ _ _ _ H eq_refl)
    as [VP VM].
  pose proof (eqctx_wf_l (i := lD) eq_refl H) as HΔ. pose proof (eqctx_wf_r (i := lD) eq_refl H) as HΔ'.
  pose proof (ctx_glob _ _ _ HΔ) as HG.
  pose proof (VP _ _ _ (GSubRel_gid EP EM HG)) as X. pose proof (VM _ _ _ (GSubRel_gid EP EM HG)) as Y.
  rewrite !gsubst_id_ctx in X, Y by first [exact (wf_ctx_dnf HΔ) | exact (wf_ctx_dnf HΔ') | reflexivity].
  exact (conj X Y).
Qed.

(** ** Images *)

Lemma GObjRel_ctx {G Δ Δ'} : [ G ⊢[ lD ] Δ ≅ Δ' ] -> GObjRel EP EM G gdCtx (GCtx Δ) (GCtx Δ').
Proof. intros H; exact (CtxRelG_of_eq H). Qed.

Lemma GObjRel_ty {G Δ i l T T'} : (lle i lC -> ty_leq T T') -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] ->
  GObjRel EP EM G (gdTy Δ i l) (GTy T) (GTy T').
Proof. intros E H; exact (conj E (VTyG_of_eq H)). Qed.

Lemma GObjRel_tm {G Δ i A l t t'} : tm_leq t t' -> [ G ; Δ ⊢[ lD ] t ≅ t' : A @ l ] ->
  GObjRel EP EM G (gdTm Δ i A l) (GTm t) (GTm t').
Proof. intros E H; exact (conj E (VTmG_of_eq H)). Qed.

End RecObj.
