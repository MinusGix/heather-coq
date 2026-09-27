(** * The lift of neutrals to algorithmic conversion (M6_DESIGN.md H9)

    Two neutrals related by [ac_tmne] at an inferred type equal to [T] are
    related by [ac_tm] at [T]. At a positive type this is one step; at the
    function types it η-expands, and the bodies are again neutrals at the
    codomain. So the proof is by induction on the declarative relation's
    reducibility of [T] (Abel et al.'s [lift~toConv]), whose [Π] case gives
    the codomain at the bound variable, reflected into the domain
    ([LR_neutral]).

    This file: the steps, stated with the lifts they recurse on as
    hypotheses. *)
From DeLaM.Validity Require Export AlgPER.

Definition Lift (i : layer) (G : gctx) (Γ : ctx) (T : ty) (l : lvl) : Prop :=
  forall t t' T0, [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t' : T @ l ] ->
  ac_tmne G Γ t t' T0 -> [ G ; Γ ⊢[ i ] T ≅ T0 @ l ] -> ac_tm G Γ t t' T.

(** The inferred type, normalized, and equal to [T]'s whnf. *)
Lemma lift_inferred {G i Γ T W l t t' T0} : compt i -> [ G ; Γ ⊢[ i ] T ⤳* W @ l ] ->
  ac_tmne G Γ t t' T0 -> [ G ; Γ ⊢[ i ] T ≅ T0 @ l ] ->
  exists W0, ac_tmnee G Γ t t' W0 /\ whnf_ty W0 /\ [ G ; Γ ⊢[ i ] W ≅ W0 @ l ].
Proof.
  intros Hc HT D ET. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (tgt_whnf Hc (eqty_wf_r Hi ET)) as (W0 & Hr0 & Hw0 & E0).
  exists W0. split; [exact (actmnee_red _ _ _ _ _ _ D Hr0 Hw0) | split; [exact Hw0 |]].
  eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ (tyred_eq _ _ _ _ _ _ HT)) |].
  eapply eqty_trans; [exact ET | exact E0].
Qed.

Lemma lift_posty {G i Γ T W l} : compt i -> [ G ; Γ ⊢[ i ] T ⤳* W @ l ] -> whnf_ty W -> posty W ->
  Lift i G Γ T l.
Proof.
  intros Hc HT Hw Hp t t' T0 Ht Ht' D ET.
  destruct (lift_inferred Hc HT D ET) as (W0 & X & _ & _).
  destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact Hw | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | exact (actmnf_ne _ _ _ _ _ _ Hp X)].
Qed.

(** [Π]: η, the bound variable lifted at the domain, the application at
    the codomain. *)
Lemma lift_pi {G i Γ T l l1 l2 A B} : compt i -> [ G ; Γ ⊢[ i ] T ⤳* tyPi l1 l2 A B @ l ] ->
  lequiv (gL G) l (lmax l1 l2) -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] ->
  Lift i G (Γ ,, A @ l1) A⟨↑⟩ l1 -> Lift i G (Γ ,, A @ l1) B l2 -> Lift i G Γ T l.
Proof.
  intros Hc HT Hl W1 W2 HA HB IHA IHB t t' T0 Ht Ht' D ET.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV Hc) as Hv.
  destruct (lift_inferred Hc HT D ET) as (W0 & Xν & Hw0 & EW0).
  destruct (head_pi W0 (eq_sym (decl_head_c Hc EW0 (whnf_tyPi _ _ _ _) Hw0))) as (m & m' & A0 & B0 & ->).
  destruct (pi_inj_c Hc EW0) as (_ & _ & EA & EB).
  pose proof (ctx_of_wf_ty Hi HA) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  (* the function, at its [Π] *)
  pose proof (tyred_eq _ _ _ _ _ _ HT) as EP.
  assert (Ht1 : [ G ; Γ ⊢[ i ] t : tyPi l1 l2 A B @ lmax l1 l2 ])
    by exact (retype Hi Ht (lequiv_sym _ _ _ Hl) (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EP)
                                                   (lequiv_sym _ _ _ Hl))).
  assert (Ht1' : [ G ; Γ ⊢[ i ] t' : tyPi l1 l2 A B @ lmax l1 l2 ])
    by exact (retype Hi Ht' (lequiv_sym _ _ _ Hl) (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EP)
                                                    (lequiv_sym _ _ _ Hl))).
  (* the bound variable, lifted at the domain *)
  assert (Hv0 : [ G ; Γ ,, A @ l1 ⊢[ i ] var 0 : A⟨↑⟩ @ l1 ]) by (apply wf_var; [rewrite Hi; exact HΓA | constructor]).
  pose proof (IHA (var 0) (var 0) A⟨↑⟩ Hv0 Hv0 (actmne_var _ _ _ _ _ (in_here _ _ _))
                (eqty_refl _ _ _ _ _ (wf_tm_ty Hi Hv0))) as X0.
  assert (EA1 : [ G ; Γ ,, A @ l1 ⊢[ i ] A0⟨↑⟩ ≅ A⟨↑⟩ @ l1 ]) by (eapply wk1_eqty; [exact Hi | exact HΓA | exact (eqty_sym _ _ _ _ _ _ EA)]).
  pose proof (cv_tm HG Hc X0 (eqc_refl _ _ _ HΓA) Hv0 Hv0 EA1) as X0'.
  (* the function, weakened, applied to the bound variable *)
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_wk_all))))))) _ _ _ _ _ Xν _ _
                (wkr_shift1 Γ A l1)) as Xν1.
  push_ren_in Xν1.
  pose proof (actmne_app _ _ l1 l2 l1 l2 A⟨↑⟩ A⟨↑⟩ B⟨rlift ↑⟩ B⟨rlift ↑⟩ _ _ _ _ _ _ _ _ Xν1 X0') as Dapp.
  rewrite liftshift_single_var_ty in Dapp by exact (wf_ty_nf (eqty_wf_r Hi EB)).
  pose proof (IHB _ _ _ (pre_eta_body Hi Hv W1 W2 HA HB Ht1) (pre_eta_body Hi Hv W1 W2 HA HB Ht1') Dapp EB) as Xb.
  destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tyPi _ _ _ _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | exact (actmnf_eta _ _ _ _ _ _ _ _ Xb)].
Qed.

(** ** The weakenings of the inferred function types *)

Lemma gwk1_tmnee {G D Γ ν ν' W} : ac_tmnee G Γ ν ν' W -> ac_tmnee (gext G D) Γ⟪S⟫ ν⟪S⟫ ν'⟪S⟫ W⟪S⟫.
Proof.
  intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_gwk_all))))))) _ _ _ _ _ H _ _
                     (MInst.gwk_ok_step (G := G) (D := D))).
Qed.

Lemma uwk_tmnee n {G Γ ν ν' W} : ac_tmnee G Γ ν ν' W ->
  ac_tmnee (gctx_uwk n G) Γ⟨ush n⟩ᵤ ν⟨ush n⟩ᵤ ν'⟨ush n⟩ᵤ W⟨ush n⟩ᵤ.
Proof.
  intros H. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_us_all))))))) _ _ _ _ _ H
                          (n + gL G) (fun j => lvar (ush n j))) as X.
  rewrite <- gctx_uwk_as, <- uren_ush_ctx, <- !uren_ush_tm, <- uren_ush_ty in X. exact X.
Qed.

(** [CΠ]: η at the bound context variable. *)
Lemma lift_cpi {G Γ T l l1 T1} : [ G ; Γ ⊢[ lM ] T ⤳* tyCPi l1 T1 @ l ] -> lequiv (gL G) l l1 ->
  lwf (gL G) l1 -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T1 @ l1 ] -> Lift lM (gext G gdCtx) Γ⟪S⟫ T1 l1 ->
  Lift lM G Γ T l.
Proof.
  intros HT Hl W1 HT1 IH t t' T0 Ht Ht' D ET.
  destruct (lift_inferred compt_M HT D ET) as (W0 & Xν & Hw0 & EW0).
  destruct (head_cpi W0 (eq_sym (decl_head_c compt_M EW0 (whnf_tyCPi _ _) Hw0))) as (m & T2 & ->).
  destruct (declM_cpi_inj EW0) as (_ & ET2).
  pose proof (tyred_eq _ _ _ _ _ _ HT) as EP.
  pose proof (retype eq_refl Ht (lequiv_sym _ _ _ Hl) (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EP)
                                                        (lequiv_sym _ _ _ Hl))) as Ht1.
  pose proof (retype eq_refl Ht' (lequiv_sym _ _ _ Hl) (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EP)
                                                         (lequiv_sym _ _ _ Hl))) as Ht1'.
  pose proof (gwk1_tmnee (D := gdCtx) Xν) as Xν1. push_gren_in Xν1.
  pose proof (actmne_capp _ _ _ _ _ _ (cvar 0) (cvar 0) Xν1 (acc_var _ 0)) as Dc.
  rewrite (eta_c_ty (eqty_wf_r (i := lM) eq_refl ET2)) in Dc.
  pose proof (IH _ _ _ (wf_ceta_body W1 HT1 Ht1) (wf_ceta_body W1 HT1 Ht1') Dc ET2) as Xb.
  destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tyCPi _ _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | exact (actmnf_ceta _ _ _ _ _ _ Xb)].
Qed.

(** [TΠ]: η at the bound type variable [U₀^id], whose identity
    substitution is related to itself (the lift at D, [Hsub]). *)
Lemma lift_tpi {G Γ T l Δ1 l1 l2 T1}
  (Hsub : forall G Θ, [ G ; Θ ⊢[ lD ] ] -> ac_sub G Θ (lshift 0) (lshift 0) Θ) :
  [ G ; Γ ⊢[ lM ] T ⤳* tyTPi Δ1 l1 l2 T1 @ l ] -> lequiv (gL G) l l2 -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  [ G ; Δ1 ⊢[ lD ] ] -> [ gext G (gdTy Δ1 lD l1) ; Γ⟪S⟫ ⊢[ lM ] T1 @ l2 ] ->
  Lift lM (gext G (gdTy Δ1 lD l1)) Γ⟪S⟫ T1 l2 -> Lift lM G Γ T l.
Proof.
  intros HT Hl W1 W2 HΔ HT1 IH t t' T0 Ht Ht' D ET.
  destruct (lift_inferred compt_M HT D ET) as (W0 & Xν & Hw0 & EW0).
  destruct (head_tpi W0 (eq_sym (decl_head_c compt_M EW0 (whnf_tyTPi _ _ _ _) Hw0))) as (Δ2 & m & m' & T2 & ->).
  destruct (declM_tpi_inj EW0) as (HΔΔ & _ & _ & ET2).
  pose proof (tyred_eq _ _ _ _ _ _ HT) as EP.
  pose proof (retype eq_refl Ht (lequiv_sym _ _ _ Hl) (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EP)
                                                        (lequiv_sym _ _ _ Hl))) as Ht1.
  pose proof (retype eq_refl Ht' (lequiv_sym _ _ _ Hl) (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EP)
                                                         (lequiv_sym _ _ _ Hl))) as Ht1'.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT1)) as HG1.
  (* the argument [U₀^id], in the inferred context *)
  pose proof (proj1 (proj2 gweakening) _ _ _ HΔ _ (gdTy Δ1 lD l1 :: gΨ G) (gwk_step gwk_id) (le_n _)
                (gwkwf_step _ _ _ _ (gwkwf_id _)) HG1) as HΔS.
  change [ gext G (gdTy Δ1 lD l1) ; Δ1⟪S⟫ ⊢[ lD ] ] in HΔS.
  assert (HU : [ gext G (gdTy Δ1 lD l1) ; Δ1⟪S⟫ ⊢[ lD ] tyGvar 0 (lshift 0) @ l1 ])
    by (eapply wf_gv; [discriminate | exact HΔS | exact (ing_here _ (gdTy Δ1 lD l1)) | apply lle_refl | reflexivity]).
  assert (XU : ac_ty (gext G (gdTy Δ1 lD l1)) Δ1⟪S⟫ (tyGvar 0 (lshift 0)) (tyGvar 0 (lshift 0))).
  { eapply act_red; [constructor | constructor | apply whnf_ty_ne; constructor | apply whnf_ty_ne; constructor |].
    apply actnf_ne. eapply actne_gvar; [exact (ing_here _ (gdTy Δ1 lD l1)) | exact (Hsub _ _ HΔS)]. }
  pose proof (cv_ty HG1 compt_D XU (eqctx_gext HG1 HΔΔ) HU HU) as XU'.
  pose proof (gwk1_tmnee (D := gdTy Δ1 lD l1) Xν) as Xν1. push_gren_in Xν1.
  pose proof (actmne_tapp _ _ _ _ _ _ _ _ _ _ Xν1 XU') as Dt.
  rewrite (eta_t_ty (eqty_wf_r (i := lM) eq_refl ET2)) in Dt.
  pose proof (IH _ _ _ (wf_teta_body HΔ W1 W2 HT1 Ht1) (wf_teta_body HΔ W1 W2 HT1 Ht1') Dt ET2) as Xb.
  destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tyTPi _ _ _ _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | exact (actmnf_teta _ _ _ _ _ _ _ _ Xb)].
Qed.

(** [UΠ] (at ω): η at the bound levels. *)
Lemma lift_upi {G Γ T n l1 T1} : [ G ; Γ ⊢[ lM ] T ⤳* tyUPi n l1 T1 @ lomega ] -> lwf (n + gL G) l1 ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T1 @ l1 ] -> Lift lM (gctx_uwk n G) Γ⟨ush n⟩ᵤ T1 l1 ->
  Lift lM G Γ T lomega.
Proof.
  intros HT W HT1 IH t t' T0 Ht Ht' D ET.
  destruct (lift_inferred compt_M HT D ET) as (W0 & Xν & Hw0 & EW0).
  destruct (head_upi W0 (eq_sym (decl_head_c compt_M EW0 (whnf_tyUPi _ _ _) Hw0))) as (n2 & m & T2 & ->).
  destruct (declM_upi_inj EW0) as (-> & _ & ET2).
  pose proof (tyred_eq _ _ _ _ _ _ HT) as EP.
  assert (Ht1 : [ G ; Γ ⊢[ lM ] t : tyUPi n l1 T1 @ lomega ])
    by (eapply wf_conv; [exact Ht | exact (eqty_sym _ _ _ _ _ _ EP)]).
  assert (Ht1' : [ G ; Γ ⊢[ lM ] t' : tyUPi n l1 T1 @ lomega ])
    by (eapply wf_conv; [exact Ht' | exact (eqty_sym _ _ _ _ _ _ EP)]).
  pose proof (uwk_tmnee n Xν) as Xν1. cbn [uren_ty] in Xν1.
  pose proof (actmne_uapp _ _ _ _ _ _ _ (ubvars n) (ubvars n) Xν1 (ubvars_length n) (leqvs_refl _)) as Dua.
  rewrite ueta_ty in Dua by exact (wf_ty_dnf (eqty_wf_r (i := lM) eq_refl ET2)).
  pose proof (IH _ _ _ (wf_ueta_body W HT1 Ht1) (wf_ueta_body W HT1 Ht1') Dua ET2) as Xb.
  destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tyUPi _ _ _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | exact (actmnf_ueta _ _ _ _ _ _ _ Xb)].
Qed.

(** ** The inductions on reducibility *)

Section LiftLR.

Local Notation DEP := (DeclEq lD compt_D).
Local Notation DEM := (DeclEq lM compt_M).
Local Notation LRM := (LR_M DEP DEM).
Local Instance DeclEqM_inst' : GenericEqM DEP DEM := DeclEqM.
Local Instance LRM_laws' : VPLaws (@lr_vp LRM) := vpM_laws DEP DEM.

(** The bound variable of a [Π], reflected into its domain's relation. *)
Lemma var0_dom {E : GenericEq} {EL : GenericEqLaws} {LP : LRParams} {VL : VPLaws lr_vp} {VN : VPNe}
  {i Hi n G Γ A A' l1 R} : E = DeclEq i Hi ->
  @LR E LP n (@LRbelow E LP n) G (Γ ,, A @ l1) A⟨↑⟩ A'⟨↑⟩ l1 R ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> R (var 0) (var 0).
Proof.
  intros -> HR HΓA EA. pose proof (compt_typeof_self _ Hi) as Hty.
  assert (Hv : [ G ; Γ ,, A @ l1 ⊢[ i ] var 0 : A⟨↑⟩ @ l1 ]) by (apply wf_var; [rewrite Hty; exact HΓA | constructor]).
  assert (EA1 : [ G ; Γ ,, A @ l1 ⊢[ i ] A⟨↑⟩ ≅ A'⟨↑⟩ @ l1 ]) by (eapply wk1_eqty; [exact Hty | exact HΓA | exact EA]).
  apply (LR_neutral _ _ _ _ _ _ _ HR).
  - refine (conj (whne_var 0) (conj (whne_var 0) _)). exact (eqtm_refl _ _ _ _ _ _ Hv).
  - refine (conj (whne_var 0) (conj (whne_var 0) _)).
    eapply eqtm_conv; [exact (eqtm_refl _ _ _ _ _ _ Hv) | rewrite Hty; exact (eqty_sym _ _ _ _ _ _ EA1)].
Qed.

Lemma LR_lift_D n G Γ T T' l R : @LR DEP LR_P n (@LRbelow DEP LR_P n) G Γ T T' l R -> Lift lD G Γ T l.
Proof.
  induction 1 as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                     HA HA' HB HB' HAA HBB domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                     HA HA' HB HB' HAA HBB domAd IHdom codAd IHcod HR];
    try (cbn in Hj; discriminate).
  - exact (lift_posty compt_D HT whnf_tyNat posty_nat).
  - exact (lift_posty compt_D HT (whnf_tyU _) (posty_U _)).
  - destruct HV as (HnV & _ & _). exact (lift_posty compt_D HT (whnf_ty_ne _ HnV) (posty_ne _ HnV)).
  - assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ lD ] ])
      by (apply wfc_ext; [exact (ctx_of_wf_ty (i := lD) eq_refl HA) | exact HA | exact Hw1]).
    assert (Hwk : wk1 : (Γ ,, A @ l1) ≤ Γ) by (constructor; constructor).
    pose proof (IHdom (kw_loc (E := DEP) wk1 Hwk HΓA)) as XA.
    pose proof (domAd (kw_loc (E := DEP) wk1 Hwk HΓA)) as HRA.
    unfold kty, kw_loc in XA, HRA; cbn [kw_G kw_Δ kw_γ kw_r gwa] in XA, HRA.
    change (wk_ren wk1) with ↑ in XA, HRA.
    pose proof (var0_dom (i := lD) (Hi := compt_D) eq_refl HRA HΓA HAA) as ha0.
    pose proof (IHcod (kw_loc (E := DEP) wk1 Hwk HΓA) (var 0) (var 0) ha0) as XB.
    unfold ktyl, kw_loc in XB; cbn [kw_G kw_Δ kw_γ kw_r gwa] in XB. change (wk_ren wk1) with ↑ in XB.
    rewrite liftshift_single_var_ty in XB by exact (wf_ty_nf HB).
    exact (lift_pi compt_D HT Hl Hw1 Hw2 HA HB XA XB).
  - (* M8 TEMPORARY: Σ, until the algorithm has Σ rules *)
    admit.
Admitted.

(** The identity substitution is related to itself. *)
Lemma lift_D {G Γ T l} : [ G ; Γ ⊢[ lD ] T @ l ] -> Lift lD G Γ T l.
Proof.
  intros HT. destruct (redP_eqty _ _ _ _ _ (eqty_refl _ _ _ _ _ HT)) as [R HR].
  exact (LR_lift_D _ _ _ _ _ _ _ HR).
Qed.

Lemma ac_sub_id {G Θ} : [ G ; Θ ⊢[ lD ] ] -> ac_sub G Θ (lshift 0) (lshift 0) Θ.
Proof.
  intros HΘ. apply acs_pt. intros n A k Hin. cbn [llk]. rewrite ?Nat.add_0_l, ?Nat.add_0_r.
  pose proof (in_ctx_wf (i := lD) eq_refl HΘ Hin) as HA.
  rewrite (nf_id_ty A (wf_ty_nf HA)).
  assert (Hv : [ G ; Θ ⊢[ lD ] var n : A @ k ]) by (apply wf_var; [exact HΘ | exact Hin]).
  exact (lift_D HA _ _ _ Hv Hv (actmne_var _ _ _ _ _ Hin) (eqty_refl _ _ _ _ _ HA)).
Qed.

Lemma LR_lift_M n G Γ T T' l R : @LR DEM LRM n (@LRbelow DEM LRM n) G Γ T T' l R -> Lift lM G Γ T l.
Proof.
  induction 1 as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                     HA HA' HB HB' HAA HBB domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                     HA HA' HB HB' HAA HBB domAd IHdom codAd IHcod HR].
  - exact (lift_posty compt_M HT whnf_tyNat posty_nat).
  - exact (lift_posty compt_M HT (whnf_tyU _) (posty_U _)).
  - destruct HV as (HnV & _ & _). exact (lift_posty compt_M HT (whnf_ty_ne _ HnV) (posty_ne _ HnV)).
  - assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ lM ] ])
      by (apply wfc_ext; [exact (ctx_of_wf_ty (i := lM) eq_refl HA) | exact HA | exact Hw1]).
    assert (Hwk : wk1 : (Γ ,, A @ l1) ≤ Γ) by (constructor; constructor).
    pose proof (IHdom (kw_loc (E := DEM) wk1 Hwk HΓA)) as XA.
    pose proof (domAd (kw_loc (E := DEM) wk1 Hwk HΓA)) as HRA.
    unfold kty, kw_loc in XA, HRA; cbn [kw_G kw_Δ kw_γ kw_r gwa] in XA, HRA.
    change (wk_ren wk1) with ↑ in XA, HRA.
    pose proof (var0_dom (i := lM) (Hi := compt_M) eq_refl HRA HΓA HAA) as ha0.
    pose proof (IHcod (kw_loc (E := DEM) wk1 Hwk HΓA) (var 0) (var 0) ha0) as XB.
    unfold ktyl, kw_loc in XB; cbn [kw_G kw_Δ kw_γ kw_r gwa] in XB. change (wk_ren wk1) with ↑ in XB.
    rewrite liftshift_single_var_ty in XB by exact (wf_ty_nf HB).
    exact (lift_pi compt_M HT Hl Hw1 Hw2 HA HB XA XB).
  - destruct HM as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                   | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR].
    + exact (lift_posty compt_M HT (whnf_tyCTyp _ _) (posty_CTyp _ _)).
    + exact (lift_posty compt_M HT (whnf_tyCTrm _ _ _) (posty_CTrm _ _ _)).
  - pose proof (ctx_of_wf_ty (i := lM) eq_refl HT1) as HΓS. pose proof (ctx_glob _ _ _ HΓS) as HG1.
    pose proof (ctx_of_wf_ty (i := lM) eq_refl (eqty_wf_l (i := lM) eq_refl (tyred_eq _ _ _ _ _ _ HT))) as HΓ.
    assert (HΓg : [ G ; Γ ⊢g ]) by (rewrite (@gm_layer_M DEP DEM _); exact HΓ).
    set (ρS := kw_gstep (E := DEM) gdCtx HG1 HΓg).
    assert (hS : vp_ctx (@lr_vp LRM) (kw_G ρS) (cvar 0) (cvar 0))
      by exact (conj (eqc_var _ _ 0 HG1 eq_refl) (conj CtxRelG_var CtxRelG_var)).
    pose proof (IHinst ρS _ _ hS) as X. unfold ρS in X.
    rewrite kbody_gstep, (eta_c_ty HT1) in X. cbn [kw_gstep kw_G kw_Δ gwa] in X.
    change (Γ⟪gwk_step gwk_id⟫) with Γ⟪S⟫ in X.
    exact (lift_cpi HT Hl Hw1 HT1 X).
  - destruct HΔ as (HΔΔ & XP & XM).
    pose proof (eqctx_wf_l (i := lD) eq_refl HΔΔ) as HΔ1.
    pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT1)) as HG1.
    pose proof (ctx_of_wf_ty (i := lM) eq_refl (eqty_wf_l (i := lM) eq_refl (tyred_eq _ _ _ _ _ _ HT))) as HΓ.
    assert (HΓg : [ G ; Γ ⊢g ]) by (rewrite (@gm_layer_M DEP DEM _); exact HΓ).
    set (ρS := kw_gstep (E := DEM) (gdTy Δ1 lD l1) HG1 HΓg).
    pose proof (vp_ty_gvar0_at DEP DEM HΔ1 HG1 (CtxRelG_trans XP (CtxRelG_sym XP))
                  (CtxRelG_trans XM (CtxRelG_sym XM))) as hS.
    pose proof (IHinst ρS _ _ hS) as X. unfold ρS in X.
    rewrite kbody_gstep, (eta_t_ty HT1) in X. cbn [kw_gstep kw_G kw_Δ gwa] in X.
    change (Γ⟪gwk_step gwk_id⟫) with Γ⟪S⟫ in X.
    exact (lift_tpi (@ac_sub_id) HT Hl Hw1 Hw2 HΔ1 HT1 X).
  - (* M8 TEMPORARY: Σ, until the algorithm has Σ rules *)
    admit.
Admitted.

(** At M: at a well-formed level by reducibility, at ω through [UΠ]. *)
Lemma lift_M_lwf {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] -> lwf (gL G) l -> Lift lM G Γ T l.
Proof.
  intros HT Hl. destruct (redM_eqty _ _ _ _ _ (eqty_refl _ _ _ _ _ HT) Hl) as [R HR].
  exact (LR_lift_M _ _ _ _ _ _ _ HR).
Qed.

Lemma lift_M {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] -> Lift lM G Γ T l.
Proof.
  intros HT. destruct (lvlM_ty HT) as [Hl | ->]; [exact (lift_M_lwf HT Hl) |].
  destruct (omegaM_red_l (eqty_refl _ _ _ _ _ HT)) as (n & l1 & T1 & HR).
  pose proof (eqty_wf_r (i := lM) eq_refl (tyred_eq _ _ _ _ _ _ HR)) as HU.
  destruct (inv_ty_upi HU) as ((_ & _ & _ & W & HT1) & _).
  exact (lift_upi HR W HT1 (lift_M_lwf HT1 W)).
Qed.

End LiftLR.

Theorem lift_c {G i Γ T l} : compt i -> [ G ; Γ ⊢[ i ] T @ l ] -> Lift i G Γ T l.
Proof. intros [-> | ->]; [apply lift_D | apply lift_M]. Qed.
