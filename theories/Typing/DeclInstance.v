(** * The declarative instance of the generic equivalence

    logrel-coq's [WeakDeclarativeTypingData]: the neutral relations relate
    two weak-head neutral forms that are declaratively equal, and the other
    two relations are declarative equality.  Parameterised by a computing
    layer [i] (D or M); at such a layer [typeof i = i], so weakening and
    conversion stay inside the layer. *)
From DeLaM.Typing Require Export Generic Presupposition.

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

(** Σ-extensionality: both sides are η-equal to the pair of their projections. *)
Lemma decl_sig_ext G Γ l l' A B p p' :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] p' : tySig l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] tmFst l l' A B p ≅ tmFst l l' A B p' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmSnd l l' A B p ≅ tmSnd l l' A B p' : B[lsingle (tmFst l l' A B p)] @ l' ] ->
  [ G ; Γ ⊢[ i ] p ≅ p' : tySig l l' A B @ lmax l l' ].
Proof.
  intros Hl Hl' HA HB Hp Hp' Hf Hs.
  eapply eqtm_trans; [apply eqtm_sym, eqtm_sig_eta; eauto|].
  eapply eqtm_trans; [|apply eqtm_sig_eta; eauto].
  apply eqtm_pair; auto using lequiv_refl, eqty_refl.
Qed.

#[export] Instance DeclEqLaws : @GenericEqLaws DeclEq.
Proof.
  constructor; cbn; unfold decl_ne_ty, decl_ne_tm.
  (* subsumption, whne extraction *)
  1-8: now intuition.
  (* PER *)
  1-8: intros; intuition eauto using eqty_sym, eqty_trans, eqtm_sym, eqtm_trans.
  (* level equivalence *)
  1: { intros * (Hn & _ & H) (_ & Hn' & H') E; refine (conj Hn (conj Hn' _)).
        exact (leq_eqty Hi (eqty_wf_l Hty H) (eqty_wf_l Hty H') E). }
  1: { intros * H H' E; exact (leq_eqty Hi (eqty_wf_l Hty H) (eqty_wf_l Hty H') E). }
  1: { intros * (Hn & _ & H) (_ & Hn' & H') E; refine (conj Hn (conj Hn' _)).
        exact (leq_eqtm Hi (eqtm_wf_l Hty H) (eqtm_wf_l Hty H') E). }
  1: { intros * H H' E; exact (leq_eqtm Hi (eqtm_wf_l Hty H) (eqtm_wf_l Hty H') E). }
  (* conversion *)
  1-2: intros; intuition (eapply eqtm_conv; [eassumption | rewrite Hty; now apply eqty_sym]).
  1-4: intros; intuition eauto using eqty_lconv, eqtm_lconv.
  (* weakening *)
  1-4: intros; intuition eauto using whne_ty_ren, whne_ren, decl_wk_eqty, decl_wk_eqtm.
  (* context conversion *)
  1-4: intros; intuition eauto using stab_eqty, stab_eqtm.
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
  (* global weakening *)
  - intros * Hγ HG' (Hn & Hn' & H).
    exact (conj (whne_ty_gren _ _ Hn) (conj (whne_ty_gren _ _ Hn') (gwk_eqty Hγ HG' H))).
  - intros * Hγ HG' H; exact (gwk_eqty Hγ HG' H).
  - intros * Hγ HG' (Hn & Hn' & H).
    exact (conj (whne_gren _ _ Hn) (conj (whne_gren _ _ Hn') (gwk_eqtm Hγ HG' H))).
  - intros * Hγ HG' H; exact (gwk_eqtm Hγ HG' H).
  (* universe substitution *)
  - intros * Hφ (Hn & Hn' & H).
    exact (conj (whne_ty_usubst _ _ Hn) (conj (whne_ty_usubst _ _ Hn')
            (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ H _ _ Hφ))).
  - intros * Hφ H; exact (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ H _ _ Hφ).
  - intros * Hφ (Hn & Hn' & H).
    exact (conj (whne_usubst _ _ Hn) (conj (whne_usubst _ _ Hn')
            (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ _ _ _ H _ _ Hφ))).
  - intros * Hφ H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ _ _ _ H _ _ Hφ).
  (* global variables *)
  - intros * Hin Hl [HΓ Ht Hd Ht' Hd' Hw Hw' He]; cbn in *.
    refine (conj _ (conj _ _)); [constructor .. |].
    eapply eqty_gvar; eauto. now rewrite Hty.
  - intros * Hin Hl [HΓ Ht Hd Ht' Hd' Hw Hw' He]; cbn in *.
    refine (conj _ (conj _ _)); [constructor .. |].
    eapply eqtm_gvar; eauto. now rewrite Hty.
  (* dependent pairs *)
  - intros; apply eqty_sig; auto.
  - intros; apply eqtm_code_sig; auto.
  - exact decl_sig_ext.
  - intros * Hl1 Hl2 HA HAA HB (Hn & Hn' & Heq).
    refine (conj _ (conj _ _)); [constructor; auto .. |]. now apply eqtm_fst.
  - intros * Hl1 Hl2 HA HAA HB (Hn & Hn' & Heq).
    refine (conj _ (conj _ _)); [constructor; auto .. |]. now apply eqtm_snd.
  (* the unit type *)
  - intros; apply eqty_unit; [exact Hv | now rewrite Hty | assumption].
  - intros; apply eqtm_code_unit; [exact Hv | now rewrite Hty | assumption].
  - intros; apply eqtm_unit_eta; auto.
  (* strict equality *)
  - intros; apply eqty_seq; auto.
  - intros; apply eqty_sempty; [exact Hi | now rewrite Hty | assumption].
  - intros; apply eqtm_seq_irr; auto.
  - intros; apply eqtm_sempty_irr; auto.
  - intros * Hl1 Hl2 HM HMM (Hn & _ & Hν) (Hn' & _ & Hν').
    refine (conj _ (conj _ _)); [constructor; auto .. |].
    apply eqtm_elimSEmpty; auto.
    apply eqtm_sempty_irr; eauto using lequiv_wf_l, eqtm_wf_l.
  (* the identity type *)
  - intros; apply eqty_id; auto.
  - intros; apply eqtm_idrefl; auto.
  - intros * Hl1 Hl2 HA HAA Haa HId HM HMM Hcc Huu (Hn & Hn' & Hν).
    refine (conj _ (conj _ _)); [constructor; auto .. |]. apply eqtm_J; auto.
  - intros; apply eqtm_code_id; auto.
Qed.

Lemma decl_geq_ctx {G Γ Γ'} : @geq_ctx DeclEq G Γ Γ' -> [ G ⊢[ i ] Γ ≅ Γ' ].
Proof. exact (@geq_ctx_sound _ DeclEqLaws G Γ Γ'). Qed.

End Decl.


(** Conversion along a context equivalence at P (and a level equivalence). *)
Lemma decl_ty_ctxconv_D {G Δ Δ' T l l'} : [ G ⊢[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢[ lD ] T @ l ] ->
  lequiv (gL G) l l' -> [ G ; Δ' ⊢[ lD ] T @ l' ].
Proof.
  intros Hc HT Hl.
  pose proof (wf_ty_subst (i := lD) eq_refl HT (eqctx_id (i := lD) eq_refl Hc)) as X.
  rewrite nf_id_ty in X by exact (wf_ty_nf HT).
  eapply wft_lconv; [exact X | now apply lequiv_sym].
Qed.

Ltac decl_elim_prem :=
  match goal with HΔ : @geq_ctx _ _ _ _ |- _ =>
    let HΔ' := fresh "HΔ'" in pose proof (decl_geq_ctx _ _ HΔ) as HΔ';
    pose proof (eqctx_wf_l (i := lD) eq_refl HΔ'); pose proof (eqctx_wf_r (i := lD) eq_refl HΔ')
  end.

(** The layer-M laws, relating the instances at P and M. *)
#[export] Instance DeclEqM : GenericEqM (DeclEq lD compt_D) (DeclEq lM compt_M).
Proof.
  constructor; cbn; unfold decl_ne_tm; [reflexivity | reflexivity | ..].
  - intros * HΓ HΔ Hl. apply eqty_CTyp; [exact HΓ | exact (decl_geq_ctx _ _ HΔ) | exact Hl].
  - intros * HΓ HΔ HT HTT Hl. pose proof (decl_geq_ctx _ _ HΔ) as HΔ'.
    apply eqty_CTrm; [exact HΓ | exact (eqctx_wf_l (i := lD) eq_refl HΔ') | exact HΔ' | exact HT
                     | exact HTT | exact Hl].
  - intros; now apply eqtm_boxT.
  - intros; now apply eqtm_boxt.
  - intros * Hl1 Hl2 HΔ HM HMM HM' Ht Ht2 (Hn & Hn' & Hν).
    pose proof (decl_geq_ctx _ _ HΔ) as HΔ'.
    refine (conj _ (conj _ _)); [constructor; auto .. |].
    apply eqtm_letboxT; auto.
    + exact (eqctx_wf_l (i := lD) eq_refl HΔ').
    + exact (eqctx_wf_r (i := lD) eq_refl HΔ').
  - intros * Hl1 Hl2 HΔ HT HTT HM HMM HM' Ht Ht2 (Hn & Hn' & Hν).
    pose proof (decl_geq_ctx _ _ HΔ) as HΔ'.
    refine (conj _ (conj _ _)); [constructor; auto .. |].
    apply eqtm_letboxt; auto.
    + exact (eqctx_wf_l (i := lD) eq_refl HΔ').
    + exact (eqctx_wf_r (i := lD) eq_refl HΔ').
    + exact (decl_ty_ctxconv_D HΔ' (eqty_wf_r (i := lD) eq_refl HTT) Hl2).
  (* neutral recursion on code *)
  - intros * Hmot [H1 H2 H3 HΔ HMT HMTe HMT' HMt HMte HMt' Hc Hc' Hb Hb'] (Hn & Hn' & Hν).
    decl_elim_prem. refine (conj _ (conj _ _)); [whne_step .. |]. apply eqtm_elimT; auto.
  - intros * Hmot [H1 H2 H3 HΔ HMT HMTe HMT' HMt HMte HMt' Hc Hc' Hb Hb'] Ht.
    decl_elim_prem. refine (conj _ (conj _ _)); [whne_step .. |]. apply eqtm_elimT; auto.
  - intros * Hmot [H1 H2 H3 HΔ HMT HMTe HMT' HMt HMte HMt' Hc Hc' Hb Hb'] HT HT' HTT (Hn & Hn' & Hν).
    decl_elim_prem. refine (conj _ (conj _ _)); [whne_step .. |]. apply eqtm_elimt; auto.
  - intros * Hg Hg' Hmot [H1 H2 H3 HΔ HMT HMTe HMT' HMt HMte HMt' Hc Hc' Hb Hb'] HT HT' HTT Ht.
    decl_elim_prem. refine (conj (whne_elimt_glob _ _ _ _ _ _ _ Hg) (conj (whne_elimt_glob _ _ _ _ _ _ _ Hg') _)).
    apply eqtm_elimt; auto.
  (* universe polymorphism *)
  - intros; now apply eqty_upi.
  - (* extensionality: both sides are η-equal to their Λ at the bound variables *)
    intros * Hn Hl HT Ht Ht' Happ.
    pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
    eapply eqtm_trans; [apply eqtm_sym, eqtm_ueta; eauto|].
    eapply eqtm_trans; [|apply eqtm_ueta; eauto].
    apply eqtm_ulam; auto using lequiv_refl, eqty_refl.
  - intros * Hl HT Hn Hls (Hne & Hne' & Hν).
    refine (conj _ (conj _ _)); [constructor; auto .. |]. eapply eqtm_uapp; eauto.
  (* meta-functions *)
  - intros; now apply eqty_cpi.
  - intros * HΓ HΔ Hc H13 H24 HT HTT HT'. pose proof (decl_geq_ctx _ _ Hc) as Hc'.
    eapply eqty_tpi; eauto. exact (eqctx_wf_r (i := lD) eq_refl Hc').
  - (* extensionality: both sides are η-equal to their Λ of the application to [g] *)
    intros * Hl HT Ht Ht' Happ. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
    eapply eqtm_trans; [apply eqtm_sym, eqtm_ceta; eauto|].
    eapply eqtm_trans; [|apply eqtm_ceta; eauto].
    apply eqtm_clam; auto using lequiv_refl, eqty_refl.
  - intros * HΔ Hl Hl' HT Ht Ht' Happ. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
    eapply eqtm_trans; [apply eqtm_sym, eqtm_teta; eauto|].
    eapply eqtm_trans; [|apply eqtm_teta; eauto].
    apply eqtm_tlam; auto using lequiv_refl, eqty_refl, eqc_refl. exact (eqtm_wf_r (i := lM) eq_refl Happ).
  - intros * Hl HT HΔ Hc HE (Hne & Hne' & Hν). pose proof (decl_geq_ctx _ _ Hc) as Hc'.
    refine (conj _ (conj _ _)); [constructor; auto .. |].
    apply eqtm_capp; auto. exact (eqctx_wf_r (i := lD) eq_refl Hc').
  - intros * HΔ Hl Hl' HT HA HAA HE (Hne & Hne' & Hν).
    refine (conj _ (conj _ _)); [constructor; auto .. |]. eapply eqtm_tapp; eauto.
Qed.
