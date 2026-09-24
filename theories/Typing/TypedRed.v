(** * Typed weak-head reduction

    [[G;Γ ⊢[i] T ⤳* W @ l]]: [T] is well formed, reduces (untyped) to [W],
    and is judgmentally equal to it.  As in logrel-coq, the equation is part
    of the definition: this avoids needing preservation (hence Π-injectivity)
    before the logical relation exists.  Every reduction the logical relation
    builds comes with its equation from a computation rule. *)
From DeLaM.Typing Require Export Properties.

Record tyred (G : gctx) (i : layer) (Γ : ctx) (T W : ty) (l : lvl) : Prop := {
  tyred_wf : [ G ; Γ ⊢[ i ] T @ l ] ;
  tyred_red : reds_ty T W ;
  tyred_eq : [ G ; Γ ⊢[ i ] T ≅ W @ l ]
}.

Record tmred (G : gctx) (i : layer) (Γ : ctx) (t w : tm) (T : ty) (l : lvl) : Prop := {
  tmred_wf : [ G ; Γ ⊢[ i ] t : T @ l ] ;
  tmred_red : reds t w ;
  tmred_eq : [ G ; Γ ⊢[ i ] t ≅ w : T @ l ]
}.

Notation "[ G ; Γ ⊢[ i ] T ⤳* W @ l ]" := (tyred G i Γ T W l)
  (at level 0, G, Γ, i, T, W, l at level 50).
Notation "[ G ; Γ ⊢[ i ] t ⤳* w : T @ l ]" := (tmred G i Γ t w T l)
  (at level 0, G, Γ, i, t, w, T, l at level 50).

Section TypedRed.
Context {G : gctx} {i : layer} {Γ : ctx}.

Lemma tyred_refl T l : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ⤳* T @ l ].
Proof. intros H; split; auto using eqty_refl. constructor. Qed.

Lemma tmred_refl t T l : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t ⤳* t : T @ l ].
Proof. intros H; split; auto using eqtm_refl. constructor. Qed.

Lemma tyred_trans T U W l :
  [ G ; Γ ⊢[ i ] T ⤳* U @ l ] -> [ G ; Γ ⊢[ i ] U ⤳* W @ l ] -> [ G ; Γ ⊢[ i ] T ⤳* W @ l ].
Proof.
  intros [] []; split; eauto using reds_ty_trans, eqty_trans.
Qed.

Lemma tmred_trans t u w T l :
  [ G ; Γ ⊢[ i ] t ⤳* u : T @ l ] -> [ G ; Γ ⊢[ i ] u ⤳* w : T @ l ] ->
  [ G ; Γ ⊢[ i ] t ⤳* w : T @ l ].
Proof.
  intros [] []; split; eauto using reds_trans, eqtm_trans.
Qed.

Lemma tmred_conv t w T T' l :
  typeof i = i -> [ G ; Γ ⊢[ i ] t ⤳* w : T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] t ⤳* w : T' @ l ].
Proof.
  intros Hi [] HT; split; auto.
  - eapply wf_conv; eauto. rewrite Hi. now apply eqty_sym.
  - eapply eqtm_conv; eauto. rewrite Hi. now apply eqty_sym.
Qed.

Lemma tyred_lconv T W l l' :
  [ G ; Γ ⊢[ i ] T ⤳* W @ l' ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] T ⤳* W @ l ].
Proof. intros [] Hl; split; eauto using wft_lconv, eqty_lconv. Qed.

Lemma tmred_lconv t w T l l' :
  [ G ; Γ ⊢[ i ] t ⤳* w : T @ l' ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] t ⤳* w : T @ l ].
Proof. intros [] Hl; split; eauto using wf_lconv, eqtm_lconv. Qed.

End TypedRed.

(** Weakening, for the computing layers. *)
Lemma tyred_wk G i Γ Δ r T W l :
  typeof i = i -> wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] T ⤳* W @ l ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ ⤳* W⟨r⟩ @ l ].
Proof.
  intros Hi Hr HΔ []; split.
  - eapply weakening_r; eauto.
  - now apply reds_ty_ren.
  - eapply weakening_r; eauto.
Qed.

Lemma tmred_wk G i Γ Δ r t w T l :
  typeof i = i -> wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] t ⤳* w : T @ l ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ ⤳* w⟨r⟩ : T⟨r⟩ @ l ].
Proof.
  intros Hi Hr HΔ []; split.
  - eapply weakening_r; eauto.
  - now apply reds_ren.
  - eapply weakening_r; eauto.
Qed.

(** Two reductions to weak-head normal forms end at the same form. *)
Lemma tyred_whnf_det G i Γ T W W' l l' :
  [ G ; Γ ⊢[ i ] T ⤳* W @ l ] -> [ G ; Γ ⊢[ i ] T ⤳* W' @ l' ] ->
  whnf_ty W -> whnf_ty W' -> W = W'.
Proof. intros [] [] ??; eapply reds_ty_whnf_det; eauto. Qed.

Lemma tmred_whnf_det G i Γ t w w' T T' l l' :
  [ G ; Γ ⊢[ i ] t ⤳* w : T @ l ] -> [ G ; Γ ⊢[ i ] t ⤳* w' : T' @ l' ] ->
  whnf w -> whnf w' -> w = w'.
Proof. intros [] [] ??; eapply reds_whnf_det; eauto. Qed.
