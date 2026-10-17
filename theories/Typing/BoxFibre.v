(** * The fibres of [□] are invariant under D-conversion

    The groupoid model of Heather's [docs/no-uip-model.md] (§4) interprets
    [□(Δ ⊢ @l)] and [□(Δ ⊢ T @ l)] as discrete sets of code: the C-types
    [T] with [[G ; Δ ⊢[lC] T @ l]], and the C-terms [t] with
    [[G ; Δ ⊢[lC] t : T @ l]]. [eqty_CTyp] and [eqty_CTrm] (and with them
    [eqtm_capp], [eqtm_tapp] and the other congruences that compare a
    context or a type at D) relate boxes whose context and type are only
    D-convertible, so the model needs these sets to depend on [Δ], [T] and
    [l] only up to D-conversion and level equivalence (the model review's
    R2, item 2). They do: a C-judgment's types and context live at
    [typeof lC = lD], so [wf_conv] at C converts its type at D, and context
    conversion ([CtxConv.v]) moves it to [Δ'].

    Each lemma takes exactly the premises of the matching rule, and its
    [_iff] form says the two fibres are the same set. *)
From DeLaM.Typing Require Import CtxConv.

(** ** Type codes: [□(Δ ⊢ @l)], along [eqty_CTyp] *)

Lemma box_fibre_ty {G Δ Δ' l l' T} : [ G ⊢[ lD ] Δ ≅ Δ' ] -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Δ' ⊢[ lC ] T @ l' ].
Proof.
  intros Hc Hl HT. apply (ctxconv_ty Hc (i := lC) eq_refl).
  eapply wft_lconv; [exact HT | now apply lequiv_sym].
Qed.

Lemma box_fibre_ty_iff {G Δ Δ' l l' T} : [ G ⊢[ lD ] Δ ≅ Δ' ] -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢[ lC ] T @ l ] <-> [ G ; Δ' ⊢[ lC ] T @ l' ].
Proof.
  intros Hc Hl; split; apply box_fibre_ty; auto using eqctx_sym_D, lequiv_sym.
Qed.

(** ** Term codes: [□(Δ ⊢ T @ l)], along [eqty_CTrm] *)

Lemma box_fibre_tm {G Δ Δ' T T' l l' t} : [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢[ lC ] t : T @ l ] -> [ G ; Δ' ⊢[ lC ] t : T' @ l' ].
Proof.
  intros Hc HT Hl Ht. apply (ctxconv_tm Hc (i := lC) eq_refl).
  eapply wf_lconv with (l' := l); [| now apply lequiv_sym].
  eapply wf_conv; [exact Ht | exact (eqty_sym _ _ _ _ _ _ HT)].
Qed.

Lemma box_fibre_tm_iff {G Δ Δ' T T' l l' t} : [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢[ lC ] t : T @ l ] <-> [ G ; Δ' ⊢[ lC ] t : T' @ l' ].
Proof.
  intros Hc HT Hl; split; [now apply box_fibre_tm |].
  apply box_fibre_tm; [now apply eqctx_sym_D | | now apply lequiv_sym].
  (* [T' ≅ T] over [Δ'], at [l'] *)
  eapply eqty_lconv with (l' := l); [| now apply lequiv_sym].
  exact (ctxconv_eqty Hc (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HT)).
Qed.
