(** * Injectivity of the M-only type formers, in the shape C1 uses (M7_DESIGN.md C1, J3.4)

    Corollaries of the M4/M5 injectivity theorems ([declM_upi_inj],
    [declM_cpi_inj], [declM_tpi_inj], [declM_CTyp_inj], [declM_CTrm_inj]),
    with the levels related left to right. ([Π] and [U] have [pi_inj_c]
    and [U_inj_c].) *)
From DeLaM.Typing Require Export InvAny.
From DeLaM.Validity Require Export DeclConsequences.

Lemma upi_inj {G Γ n n' l l' T T' k} : [ G ; Γ ⊢[ lM ] tyUPi n l T ≅ tyUPi n' l' T' @ k ] ->
  n' = n /\ lequiv (n + gL G) l l' /\ [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T ≅ T' @ l ].
Proof. exact declM_upi_inj. Qed.

Lemma cpi_inj {G Γ l l' T T' k} : [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyCPi l' T' @ k ] ->
  lequiv (gL G) l l' /\ [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ].
Proof. intros E. destruct (declM_cpi_inj E) as [Q ET]. exact (conj (lequiv_sym _ _ _ Q) ET). Qed.

Lemma ctyp_inj {G Γ Δ Δ' l l' k} : [ G ; Γ ⊢[ lM ] tyCTyp Δ l ≅ tyCTyp Δ' l' @ k ] ->
  lequiv (gL G) l l' /\ [ G ⊢[ lD ] Δ ≅ Δ' ].
Proof. intros E. destruct (declM_CTyp_inj E) as [EΔ Q]. exact (conj Q EΔ). Qed.

Lemma ctrm_inj {G Γ Δ Δ' A A' l l' k} : [ G ; Γ ⊢[ lM ] tyCTrm Δ A l ≅ tyCTrm Δ' A' l' @ k ] ->
  lequiv (gL G) l l' /\ [ G ⊢[ lD ] Δ ≅ Δ' ] /\ [ G ; Δ ⊢[ lD ] A ≅ A' @ l ].
Proof. intros E. destruct (declM_CTrm_inj E) as (EΔ & EA & Q). exact (conj Q (conj EΔ EA)). Qed.

Lemma tpi_inj {G Γ Δ Δ' l1 l2 l1' l2' T T' k} :
  [ G ; Γ ⊢[ lM ] tyTPi Δ l1 l2 T ≅ tyTPi Δ' l1' l2' T' @ k ] ->
  lequiv (gL G) l1 l1' /\ lequiv (gL G) l2 l2' /\ [ G ⊢[ lD ] Δ ≅ Δ' ] /\
  [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ].
Proof.
  intros E. destruct (declM_tpi_inj E) as (EΔ & Q1 & Q2 & ET).
  exact (conj (lequiv_sym _ _ _ Q1) (conj (lequiv_sym _ _ _ Q2) (conj EΔ ET))).
Qed.
