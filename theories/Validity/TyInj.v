(** * Injectivity of the M-only type formers (M7_DESIGN.md C1, J3.4)

    Equal [UΠ], [CΠ], [TΠ], [□Typ], [□Trm] types have equal components.
    Through the algorithm: an equation of whnfs is an algorithmic one
    between the whnfs themselves ([ac_whnf]), whose inversion gives
    algorithmic component equations, sound once both components are typed
    (by inversion of the formers, the right one moved into the left one's
    scope). ([Π] and [U] have [pi_inj_c] and [U_inj_c].) *)
From DeLaM.Typing Require Export InvAny.
From DeLaM.Validity Require Export Uniform.

Lemma ac_whnf {G i Γ W W' k} : compt i -> [ G ; Γ ⊢[ i ] W ≅ W' @ k ] -> whnf_ty W -> whnf_ty W' ->
  ac_tynf G Γ W W'.
Proof.
  intros Hc E HW HW'. pose proof (ac_complete_ty Hc E) as D. inversion D as [? ? ? ? W1 W1' Hr Hr' Hw1 Hw1' Dn]; subst.
  rewrite (reds_ty_whnf_det _ _ _ (Relation_Operators.rt1n_refl _ _ _) Hr HW Hw1),
          (reds_ty_whnf_det _ _ _ (Relation_Operators.rt1n_refl _ _ _) Hr' HW' Hw1'). exact Dn.
Qed.

Ltac no_tyne := match goal with D : ac_tyne _ _ _ _ |- _ => inversion D end.

Lemma upi_inj {G Γ n n' l l' T T' k} : [ G ; Γ ⊢[ lM ] tyUPi n l T ≅ tyUPi n' l' T' @ k ] ->
  n' = n /\ lequiv (n + gL G) l l' /\ [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T ≅ T' @ l ].
Proof.
  intros E. pose proof (ac_whnf compt_M E (whnf_tyUPi _ _ _) (whnf_tyUPi _ _ _)) as D.
  destruct (inv_ty_upi (eqty_wf_l (i := lM) eq_refl E)) as ((_ & _ & _ & Hl & HT) & _).
  destruct (inv_ty_upi (eqty_wf_r (i := lM) eq_refl E)) as ((_ & _ & _ & Hl' & HT') & _).
  inversion D; subst; try no_tyne.
  match goal with Hq : leqv _ _ |- _ => pose proof (leqv_lequiv _ _ _ Hl Hl' Hq) as Q end.
  refine (conj eq_refl (conj Q _)).
  match goal with A : ac_ty _ _ _ _ |- _ =>
    exact (ac_ty_sound compt_M A HT (wft_lconv _ _ _ _ _ _ HT' Q)) end.
Qed.

Lemma cpi_inj {G Γ l l' T T' k} : [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyCPi l' T' @ k ] ->
  lequiv (gL G) l l' /\ [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ].
Proof.
  intros E. pose proof (ac_whnf compt_M E (whnf_tyCPi _ _) (whnf_tyCPi _ _)) as D.
  destruct (inv_ty_cpi (eqty_wf_l (i := lM) eq_refl E)) as ((_ & _ & Hl & HT) & _).
  destruct (inv_ty_cpi (eqty_wf_r (i := lM) eq_refl E)) as ((_ & _ & Hl' & HT') & _).
  inversion D; subst; try no_tyne.
  match goal with Hq : leqv _ _ |- _ => pose proof (leqv_lequiv _ _ _ Hl Hl' Hq) as Q end.
  refine (conj Q _).
  match goal with A : ac_ty _ _ _ _ |- _ =>
    exact (ac_ty_sound compt_M A HT (wft_lconv _ _ _ _ _ _ HT' Q)) end.
Qed.

Lemma ctyp_inj {G Γ Δ Δ' l l' k} : [ G ; Γ ⊢[ lM ] tyCTyp Δ l ≅ tyCTyp Δ' l' @ k ] ->
  lequiv (gL G) l l' /\ [ G ⊢[ lD ] Δ ≅ Δ' ].
Proof.
  intros E. pose proof (ac_whnf compt_M E (whnf_tyCTyp _ _) (whnf_tyCTyp _ _)) as D.
  destruct (inv_ty_CTyp (eqty_wf_l (i := lM) eq_refl E)) as ((_ & _ & HΔ & Hl) & _).
  destruct (inv_ty_CTyp (eqty_wf_r (i := lM) eq_refl E)) as ((_ & _ & HΔ' & Hl') & _).
  inversion D; subst; try no_tyne.
  match goal with Hq : leqv _ _ |- _ => pose proof (leqv_lequiv _ _ _ Hl Hl' Hq) as Q end.
  refine (conj Q _).
  match goal with A : ac_ctx _ _ _ |- _ => exact (ac_ctx_sound' A HΔ HΔ') end.
Qed.

Lemma ctrm_inj {G Γ Δ Δ' A A' l l' k} : [ G ; Γ ⊢[ lM ] tyCTrm Δ A l ≅ tyCTrm Δ' A' l' @ k ] ->
  lequiv (gL G) l l' /\ [ G ⊢[ lD ] Δ ≅ Δ' ] /\ [ G ; Δ ⊢[ lD ] A ≅ A' @ l ].
Proof.
  intros E. pose proof (ac_whnf compt_M E (whnf_tyCTrm _ _ _) (whnf_tyCTrm _ _ _)) as D.
  destruct (inv_ty_CTrm (eqty_wf_l (i := lM) eq_refl E)) as ((_ & _ & HΔ & HA & Hl) & _).
  destruct (inv_ty_CTrm (eqty_wf_r (i := lM) eq_refl E)) as ((_ & _ & HΔ' & HA' & Hl') & _).
  inversion D; subst; try no_tyne.
  match goal with Hq : leqv _ _ |- _ => pose proof (leqv_lequiv _ _ _ Hl Hl' Hq) as Q end.
  match goal with Ac : ac_ctx _ _ _ |- _ => pose proof (ac_ctx_sound' Ac HΔ HΔ') as EΔ end.
  refine (conj Q (conj EΔ _)).
  pose proof (ctxconv_ty (eqctx_sym_D EΔ) (i := lD) eq_refl HA') as HA'1.
  match goal with Aa : ac_ty _ _ _ _ |- _ =>
    exact (ac_ty_sound compt_D Aa HA (wft_lconv _ _ _ _ _ _ HA'1 Q)) end.
Qed.

Lemma tpi_inj {G Γ Δ Δ' l1 l2 l1' l2' T T' k} :
  [ G ; Γ ⊢[ lM ] tyTPi Δ l1 l2 T ≅ tyTPi Δ' l1' l2' T' @ k ] ->
  lequiv (gL G) l1 l1' /\ lequiv (gL G) l2 l2' /\ [ G ⊢[ lD ] Δ ≅ Δ' ] /\
  [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ].
Proof.
  intros E. pose proof (ac_whnf compt_M E (whnf_tyTPi _ _ _ _) (whnf_tyTPi _ _ _ _)) as D.
  destruct (inv_ty_tpi (eqty_wf_l (i := lM) eq_refl E)) as ((_ & _ & HΔ & Hl1 & Hl2 & HT) & _).
  destruct (inv_ty_tpi (eqty_wf_r (i := lM) eq_refl E)) as ((_ & _ & HΔ' & Hl1' & Hl2' & HT') & _).
  inversion D; subst; try no_tyne.
  match goal with Hq : leqv l1 l1' |- _ => pose proof (leqv_lequiv _ _ _ Hl1 Hl1' Hq) as Q1 end.
  match goal with Hq : leqv l2 l2' |- _ => pose proof (leqv_lequiv _ _ _ Hl2 Hl2' Hq) as Q2 end.
  match goal with Ac : ac_ctx _ _ _ |- _ => pose proof (ac_ctx_sound' Ac HΔ HΔ') as EΔ end.
  refine (conj Q1 (conj Q2 (conj EΔ _))).
  (* the right body, in the left binder's scope *)
  assert (HE : GEq (gext G (gdTy Δ' lD l1')) (gext G (gdTy Δ lD l1))).
  { apply GEq_ext; [exact (GEq_refl _ (ctx_glob _ _ _ HΔ)) |
                    exact (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT')) |
                    exact (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT)) |].
    cbn. refine (conj eq_refl (conj (or_intror eq_refl) (conj (lequiv_sym _ _ _ Q1) (eqctx_sym_D EΔ)))). }
  pose proof (gconv_ty HE HT') as HT'1.
  match goal with Aa : ac_ty _ _ _ _ |- _ =>
    exact (ac_ty_sound compt_M Aa HT (wft_lconv _ _ _ _ _ _ HT'1 Q2)) end.
Qed.
