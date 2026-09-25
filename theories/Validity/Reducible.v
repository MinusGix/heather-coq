(** * Reducibility of every judgment at M (M2_DESIGN.md, 5g)

    The fundamental theorem at M, at the identity global substitution
    ([ReducibleP]). *)
From DeLaM.Validity Require Export ReducibleP FundamentalM.

Section ReducibleM.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsRM : VPLaws (@lr_vp LRM) := vpM_laws EP EM.

(** ** At M *)

Lemma reducibleM_eqty {G Γ T T' l} : [ G ; Γ ⊢[ lM ] T ≅ T' @ l ] -> @LRty EM LRM l G Γ T T'.
Proof.
  intros H. destruct (proj1 (proj2 (proj2 (proj2 (proj2 (fundamentalM EP EM))))) _ _ _ _ _ _ H eq_refl)
    as ((_ & VΓ) & VT).
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  rewrite <- (@gm_layer_M EP EM EMl) in HT, HT'.
  exact (VTyS_red EP EM HT HT' VΓ VT).
Qed.

Lemma reducibleM_eqtm {G Γ t t' T l} : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ] -> @LRtm EM LRM l G Γ T T t t'.
Proof.
  intros H. destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalM EP EM)))))) _ _ _ _ _ _ _ H eq_refl)
    as ((_ & VΓ) & _ & Vt).
  pose proof (eqtm_wf_l (i := lM) eq_refl H) as Ht. pose proof (eqtm_wf_r (i := lM) eq_refl H) as Ht'.
  rewrite <- (@gm_layer_M EP EM EMl) in Ht, Ht'.
  exact (VTmS_red EP EM Ht Ht' VΓ Vt).
Qed.

End ReducibleM.
