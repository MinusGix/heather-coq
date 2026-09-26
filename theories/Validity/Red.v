(** * Typed reductions used by the validity lemmas *)
From DeLaM.Validity Require Export Pi.

Section Red.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Lemma tmred_app_cong {G Γ l l' A B t w s} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ,, A @ l ⊢g B @ l' ] -> [ G ; Γ ⊢g s : A @ l ] ->
  [ G ; Γ ⊢g t ⤳* w : tyPi l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢g app t l l' A B s ⤳* app w l l' A B s : B[lsingle s] @ l' ].
Proof.
  intros Hl Hl' HA HB Hs [Ht Hr Heq]. split.
  - apply wf_app; auto using ge_notV.
  - now apply reds_app.
  - apply eqtm_app; auto using ge_notV, lequiv_refl, eqty_refl, eqtm_refl.
Qed.

(** β through equivalent annotations on the application. *)
Lemma tmred_beta {G Γ l l' la lb A0 B0 A1 B1 b a} :
  lwf (gL G) l -> lwf (gL G) l' -> lequiv (gL G) la l -> lequiv (gL G) lb l' ->
  [ G ; Γ ⊢g A0 @ l ] -> [ G ; Γ ,, A0 @ l ⊢g B0 @ l' ] ->
  [ G ; Γ ,, A0 @ l ⊢g b : B0 @ l' ] -> [ G ; Γ ⊢g a : A0 @ l ] ->
  [ G ; Γ ⊢g A0 ≅ A1 @ l ] -> [ G ; Γ ,, A0 @ l ⊢g B0 ≅ B1 @ l' ] ->
  [ G ; Γ ⊢g app (lam l l' A0 b) la lb A1 B1 a ⤳* b[lsingle a] : B0[lsingle a] @ l' ].
Proof.
  intros Hl Hl' H1 H2 HA0 HB0 Hb Ha HA1 HB1.
  assert (HF : [ G ; Γ ⊢g lam l l' A0 b : tyPi l l' A0 B0 @ lmax l l' ])
    by (apply wf_lam; auto using ge_notV).
  assert (Eq1 : [ G ; Γ ⊢g app (lam l l' A0 b) l l' A0 B0 a ≅ app (lam l l' A0 b) la lb A1 B1 a
                    : B0[lsingle a] @ l' ])
    by (apply eqtm_app; auto using ge_notV, lequiv_sym, eqtm_refl).
  assert (Eq2 : [ G ; Γ ⊢g app (lam l l' A0 b) l l' A0 B0 a ≅ b[lsingle a] : B0[lsingle a] @ l' ])
    by (apply eqtm_beta; auto using ge_compt).
  split.
  - exact (eqtm_wf_r ge_typeof Eq1).
  - econstructor; [constructor | constructor].
  - eapply eqtm_trans; [apply eqtm_sym, Eq1 | exact Eq2].
Qed.

End Red.
