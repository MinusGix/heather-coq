(** * Neutral scrutinees of the code recursors (M3_DESIGN.md E13, E14)

    The neutral recursion laws need the motives and branches generically
    related under their binders ([ElimPrem]). They come from the motives'
    and branches' validity at the identity extension of the substitutions:
    the level binders by universe weakening ([LR_uwk] and friends), the
    fresh global variables as identity images, the fresh local variables
    as neutrals at their (valid) types. *)
From DeLaM.Validity Require Export RecS UPermV.

Section RecNe.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VPP : VPPerm lr_vp}.

Lemma SubRel_uwk {L Ψ Γ Δ d d'} : [ ⊢ mkG L Ψ ] -> ctx_lwf L Γ ->
  SubRel (mkG L Ψ) Γ Δ d d' -> SubRel (gctx_uwk 1 (mkG L Ψ)) Γ⟨ush 1⟩ᵤ Δ⟨ush 1⟩ᵤ (uwk d) (uwk d').
Proof.
  intros HG WΓ Hd.
  assert (Hgrow : gwk_ok gwk_id (mkG (S L) Ψ) (mkG L Ψ)) by exact (conj (le_S _ _ (le_n _)) (gwkwf_id _)).
  pose proof (wfg_grow L (S L) Ψ (le_S _ _ (le_n _)) HG) as HG'.
  assert (EG : Gp (rot L) (mkG (S L) Ψ) = gctx_uwk 1 (mkG L Ψ)).
  { unfold Gp, G_us, gctx_usubst, gctx_uwk; cbn. f_equal. exact (rot_decls L Ψ (wfg_lwf _ HG)). }
  assert (Eag : forall m, m < L -> pφ (rot L) m = pφ (ush 1) m) by exact (fun m Hm => rot_ush L m Hm).
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Wd. pose proof (SubRel_wf_l _ _ _ _ _ (SubRel_refl_r Hd)) as Wd'.
  pose proof (lsub_wf_lwf Wd) as Ld. pose proof (lsub_wf_lwf Wd') as Ld'.
  pose proof (wf_ctx_lwf (SubRel_ctx Hd)) as WΔ.
  pose proof (SubRel_gwa Hd Hgrow HG') as X; cbn [gwa] in X.
  pose proof (SubRel_perm (G := mkG (S L) Ψ) (uperm_rot L) _ _ _ _ X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_ctx WΔ Eag), <- !uren_us_ctx in Y.
  refine (SubRel_ext _ _ _ _ _ _ _ _ _ Y); intros n; cbn [usubst USubst_lsub];
    rewrite llk_ulsubst; unfold uwk; rewrite llk_ulren;
    first [ rewrite ((proj1 (proj2 lwf_us_ext_all)) _ _ _ _ (Ld n) Eag)
          | rewrite ((proj1 (proj2 lwf_us_ext_all)) _ _ _ _ (Ld' n) Eag) ];
    symmetry; apply (proj1 (proj2 uren_as_usubst_all)); reflexivity.
Qed.

End RecNe.
