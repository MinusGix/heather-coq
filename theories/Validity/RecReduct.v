(** * The recursors' β-reducts are typed (M7_DESIGN.md A2b)

    Discharges [Preservation.RecRedTyped]. A reduct is its branch body at
    extended substitutions ([RecPeel.peel_wrap]):
      [((bs k)[uext ls lvar]ᵤ)⦃gext_s os id⦄[lext xs id]]
    with [ls] the code's levels, [os] the scrutinee's context and the
    code's pieces, [xs] the recursive calls. Its typing ([br_typed]) is the
    branch's typing under the universe, global and local substitution
    lemmas; per code shape, the pieces are typed by inverting the code's
    C-typing, and the recursive calls by the recursor rule at the
    sub-codes (no induction). The type is the branch type's instance,
    which [motT_wkb_inst]/[mott_wkb_inst] identify with the motive at the
    code. *)
From DeLaM.Validity Require Export Preservation RecReductCases.

(** ** The reducts are typed *)

Theorem rec_red_typed : RecRedTyped.
Proof.
  split.
  - intros G Γ l1 l2 rb l Δ c r T k Hx Hred.
    destruct (elimT_prem Hx) as (MT & Mt & bs & -> & Hrb).
    destruct (inv_elimT (i := lM) eq_refl Hx) as (MTa & Mta & bsa & (Erb & _ & _ & W1 & W2 & Wl & HΔ & _) & Hk & ET).
    destruct (mkrb_inj_MT Erb) as [<- <-].
    pose proof (ctx_of_wf_tm (i := lM) eq_refl Hx) as HΓ.
    destruct (inv_elimT (i := lM) eq_refl Hx) as (MTb & Mtb & bsb & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs) & _).
    destruct (inv_boxT (i := lM) eq_refl Hs) as (Δ1 & l1' & (_ & _ & _ & HΔ1 & Hc1) & _ & EC).
    destruct (declM_CTyp_inj EC) as (Ec & El).
    pose proof (wft_lconv _ _ _ _ _ _ (sc_cty (i := lC) HCD' (eqctx_sym_D Ec) Hc1) El) as Hc.
    pose proof (rr_T_all HΓ Hrb Wl HΔ Hc Hred) as X.
    refine (wf_conv _ lM _ _ _ _ _ _ ET).
    destruct Hk as [-> | Hk]; [exact X | exact (wf_lconv _ _ _ _ _ _ _ X Hk)].
  - intros G Γ l1 l2 rb l Δ A c r T k Hx Hred.
    destruct (elimt_prem Hx) as (MT & Mt & bs & -> & Hrb).
    destruct (inv_elimt (i := lM) eq_refl Hx)
      as (MTa & Mta & bsa & (Erb & _ & _ & W1 & W2 & Wl & HΔ & _ & _ & _ & _ & HA & Hs) & Hk & ET).
    destruct (mkrb_inj_MT Erb) as [<- <-].
    pose proof (ctx_of_wf_tm (i := lM) eq_refl Hx) as HΓ.
    destruct (inv_boxt (i := lM) eq_refl Hs) as (Δ1 & A1 & l1' & (_ & _ & _ & HΔ1 & HA1 & Hc1) & _ & EC).
    destruct (declM_CTrm_inj EC) as (Ec & EA & El).
    pose proof (sc_conv (i := lC) HCD' (wf_lconv _ _ _ _ _ _ _ (sc_ctm (i := lC) HCD' (eqctx_sym_D Ec) Hc1) El) EA) as Hc.
    pose proof (rec_t_code Hc eq_refl Hc Γ l1 l2 MT Mt bs HΓ Hrb HΔ l A r (lequiv_refl _ _ Wl)
                  (eqty_refl _ _ _ _ _ HA) Hred) as X.
    refine (wf_conv _ lM _ _ _ _ _ _ ET).
    destruct Hk as [-> | Hk]; [exact X | exact (wf_lconv _ _ _ _ _ _ _ X Hk)].
Qed.

(** ** Soundness of reduction and preservation, unconditionally *)

Theorem reduction_sound_tm {G i Γ t t' T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] -> red t t' ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof. exact (red_sound_tm rec_red_typed). Qed.
Theorem reduction_sound_ty {G i Γ T T' k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> red_ty T T' ->
  [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. exact (red_sound_ty rec_red_typed). Qed.
Theorem subject_reduction_tm {G i Γ t t' T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] -> red t t' ->
  [ G ; Γ ⊢[ i ] t' : T @ k ].
Proof. exact (preservation_tm rec_red_typed). Qed.
Theorem subject_reduction_ty {G i Γ T T' k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> red_ty T T' ->
  [ G ; Γ ⊢[ i ] T' @ k ].
Proof. exact (preservation_ty rec_red_typed). Qed.
Theorem reductions_sound_tm {G i Γ t t' T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] -> reds t t' ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof. exact (reds_sound_tm rec_red_typed). Qed.
Theorem reductions_sound_ty {G i Γ T T' k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> reds_ty T T' ->
  [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. exact (reds_sound_ty rec_red_typed). Qed.
