(** * The declarative instance of the generic equivalence

    logrel-coq's [WeakDeclarativeTypingData]: the neutral relations relate
    two weak-head neutral forms that are declaratively equal, and the other
    two relations are declarative equality.  Parameterised by a computing
    layer [i] (D or M); at such a layer [typeof i = i], so weakening and
    conversion stay inside the layer. *)
From DeLaM.Typing Require Export Generic.

Section Decl.
Context (i : layer) (Hi : compt i).

Definition decl_ne_ty G Γ V V' l :=
  whne_ty V /\ whne_ty V' /\ [ G ; Γ ⊢[ i ] V ≅ V' @ l ].
Definition decl_ne_tm G Γ t t' T l :=
  whne t /\ whne t' /\ [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ].

#[export] Instance DeclEq : GenericEq := {|
  ge_layer := i ;
  ge_compt := Hi ;
  gne_ty := decl_ne_ty ;
  geq_ty := fun G Γ T T' l => [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ;
  gne_tm := decl_ne_tm ;
  geq_tm := fun G Γ t t' T l => [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]
|}.

Let Hty : typeof i = i := compt_typeof_self i Hi.
Let Hv : i <> lV := compt_notV i Hi.

(** Context well-formedness at [i] from any judgment at [i]. *)
Lemma decl_ctx_ty G Γ T l : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] ].
Proof. intros H. rewrite <- Hty. exact (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H). Qed.
Lemma decl_ctx_tm G Γ t T l : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] ].
Proof.
  intros H. rewrite <- Hty. exact (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H).
Qed.

Lemma decl_wk_eqty G Γ Δ r T T' l : wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ ≅ T'⟨r⟩ @ l ].
Proof. intros Hr HΔ H. eapply weakening_r; eauto. Qed.
Lemma decl_wk_eqtm G Γ Δ r t t' T l : wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ ≅ t'⟨r⟩ : T⟨r⟩ @ l ].
Proof. intros Hr HΔ H. eapply weakening_r; eauto. Qed.

(** η-expansion at the identity: both sides of [funext] are η-equal to the
    λ of their application to [var 0]. *)
Lemma decl_funext G Γ l l' A B t t' :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] t' : tyPi l l' A B @ lmax l l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)
                        ≅ app t'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0) : B @ l' ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyPi l l' A B @ lmax l l' ].
Proof.
  intros Hl Hl' HA HB Ht Ht' Happ.
  eapply eqtm_trans; [apply eqtm_sym, eqtm_eta; eauto|].
  eapply eqtm_trans; [|apply eqtm_eta; eauto].
  apply eqtm_lam; auto using lequiv_refl, eqty_refl.
Qed.

#[export] Instance DeclEqLaws : @GenericEqLaws DeclEq.
Proof.
  constructor; cbn; unfold decl_ne_ty, decl_ne_tm.
  (* subsumption, whne extraction *)
  1-8: now intuition.
  (* PER *)
  1-8: intros; intuition eauto using eqty_sym, eqty_trans, eqtm_sym, eqtm_trans.
  (* conversion *)
  1-2: intros; intuition (eapply eqtm_conv; [eassumption | rewrite Hty; now apply eqty_sym]).
  1-4: intros; intuition eauto using eqty_lconv, eqtm_lconv.
  (* weakening *)
  1-4: intros; intuition eauto using whne_ty_ren, whne_ren, decl_wk_eqty, decl_wk_eqtm.
  (* weak head closure *)
  - intros * [_ _ HT] [_ _ HT'] HW.
    eauto using eqty_trans, eqty_sym.
  - intros * [_ _ Ht] [_ _ Ht'] Hw.
    eauto using eqtm_trans, eqtm_sym.
  (* type constructors *)
  - intros; apply eqty_refl, wft_nat; [exact Hv | now rewrite Hty].
  - intros; apply eqty_U; [exact Hv | now rewrite Hty | assumption].
  - intros; apply eqty_pi; auto.
  - intros; apply eqtm_refl, wf_code_nat; [exact Hv | now rewrite Hty].
  - intros; apply eqtm_code_U; [exact Hv | now rewrite Hty | assumption].
  - intros; apply eqtm_code_pi; auto.
  (* neutral types *)
  - intros * Hl (Hn & Hn' & Heq). refine (conj _ (conj _ _)); [constructor; auto .. |].
    now apply eqty_El.
  (* term congruences *)
  - intros; apply eqtm_refl, wf_zero; [exact Hv | now rewrite Hty].
  - intros; now apply eqtm_succ.
  - exact decl_funext.
  (* neutral congruences *)
  - intros; refine (conj _ (conj _ _)); [constructor .. | now apply eqtm_refl].
  - intros * Hl HM HMM Hs Hz (Hn & Hn' & Heq).
    refine (conj _ (conj _ _)); [constructor; auto .. |]. now apply eqtm_natrec.
  - intros * Hl1 Hl2 HA HAA HB (Hn & Hn' & Heq) Hs.
    refine (conj _ (conj _ _)); [constructor; auto .. |]. now apply eqtm_app.
Qed.

End Decl.
