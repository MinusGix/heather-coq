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

(** [Σ]: η, the projections lifted at the components; the second's type
    is the family at the first projection. *)
Lemma lift_sig {G i Γ T l l1 l2 A B} : compt i -> [ G ; Γ ⊢[ i ] T ⤳* tySig l1 l2 A B @ l ] ->
  lequiv (gL G) l (lmax l1 l2) -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> Lift i G Γ A l1 ->
  (forall p, whne p -> [ G ; Γ ⊢[ i ] p : tySig l1 l2 A B @ lmax l1 l2 ] ->
     Lift i G Γ B[lsingle (tmFst l1 l2 A B p)] l2) ->
  Lift i G Γ T l.
Proof.
  intros Hc HT Hl W1 W2 HA HB IHA IHB t t' T0 Ht Ht' D ET.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (lift_inferred Hc HT D ET) as (W0 & Xν & Hw0 & EW0).
  destruct (head_sig W0 (eq_sym (decl_head_c Hc EW0 (whnf_tySig _ _ _ _) Hw0))) as (m & m' & A0 & B0 & ->).
  destruct (sig_inj_c Hc EW0) as (Em & Em' & EA & EB).
  pose proof (tyred_eq _ _ _ _ _ _ HT) as EP.
  assert (Ht1 : [ G ; Γ ⊢[ i ] t : tySig l1 l2 A B @ lmax l1 l2 ])
    by exact (retype Hi Ht (lequiv_sym _ _ _ Hl) (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EP)
                                                   (lequiv_sym _ _ _ Hl))).
  assert (Ht1' : [ G ; Γ ⊢[ i ] t' : tySig l1 l2 A B @ lmax l1 l2 ])
    by exact (retype Hi Ht' (lequiv_sym _ _ _ Hl) (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EP)
                                                    (lequiv_sym _ _ _ Hl))).
  destruct (ac_tmne_whne D) as [Hn Hn'].
  (* the first projections *)
  pose proof (wf_fst _ _ _ _ _ _ _ _ (compt_notV Hc) W1 W2 HA HB Ht1) as Hf.
  pose proof (wf_fst _ _ _ _ _ _ _ _ (compt_notV Hc) W1 W2 HA HB Ht1') as Hf'.
  assert (D1 : ac_tmne G Γ (tmFst l1 l2 A B t) (tmFst l1 l2 A B t') A0) by (eapply actmne_fst; exact Xν).
  pose proof (IHA _ _ _ Hf Hf' D1 EA) as X1.
  (* the second projections, at the first's instance *)
  destruct (ac_nee_sound' Xν Hc Ht1 Ht1') as (_ & _ & Ett).
  pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ (compt_notV Hc) (lequiv_refl _ _ W1) (lequiv_refl _ _ W2) HA
                (eqty_refl _ _ _ _ _ HA) (eqty_refl _ _ _ _ _ HB) Ett) as Ef.
  pose proof (wf_snd _ _ _ _ _ _ _ _ (compt_notV Hc) W1 W2 HA HB Ht1) as Hs.
  pose proof (wf_snd _ _ _ _ _ _ _ _ (compt_notV Hc) W1 W2 HA HB Ht1') as Hs'.
  pose proof (sig_fam_eq Hi HB (eqty_refl _ _ _ _ _ HB) Ef Hf Hf') as EBs.
  assert (Hs1 : [ G ; Γ ⊢[ i ] tmSnd l1 l2 A B t' : B[lsingle (tmFst l1 l2 A B t)] @ l2 ])
    by (eapply wf_conv; [exact Hs' | rewrite Hi; exact EBs]).
  assert (D2 : ac_tmne G Γ (tmSnd l1 l2 A B t) (tmSnd l1 l2 A B t') B0[lsingle (tmFst m m' A0 B0 t)])
    by (eapply actmne_snd; exact Xν).
  pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ (compt_notV Hc) (lequiv_sym _ _ _ Em) (lequiv_sym _ _ _ Em') HA EA EB
                (eqtm_refl _ _ _ _ _ _ Ht1)) as Ef0.
  pose proof (sig_fam_eq Hi HB EB Ef0 Hf (eqtm_wf_r Hi Ef0)) as E2.
  pose proof (IHB t Hn Ht1 _ _ _ Hs Hs1 D2 E2) as X2.
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tySig _ _ _ _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | apply actmnf_sig_eta; [exact X1 | exact X2]].
Qed.

(** [Unit]: η, whatever the neutrals. *)
Lemma lift_unit {G i Γ T l l1} : [ G ; Γ ⊢[ i ] T ⤳* tyUnit l1 @ l ] -> Lift i G Γ T l.
Proof.
  intros HT t t' T0 Ht Ht' D ET. destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tyUnit _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | apply actmnf_unit_eta].
Qed.

(** Strict equality (M10a): irrelevance, whatever the neutrals. *)
Lemma lift_seq {G i Γ T l l1 A a b} : [ G ; Γ ⊢[ i ] T ⤳* tySEq l1 A a b @ l ] -> Lift i G Γ T l.
Proof.
  intros HT t t' T0 Ht Ht' D ET. destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tySEq _ _ _ _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | apply actmnf_seq_irr].
Qed.
Lemma lift_sempty {G i Γ T l l1} : [ G ; Γ ⊢[ i ] T ⤳* tySEmpty l1 @ l ] -> Lift i G Γ T l.
Proof.
  intros HT t t' T0 Ht Ht' D ET. destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tySEmpty _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | apply actmnf_sempty_irr].
Qed.

(** The empty type: irrelevance, whatever the neutrals. *)
Lemma lift_empty {G i Γ T l l1} : [ G ; Γ ⊢[ i ] T ⤳* tyEmpty l1 @ l ] -> Lift i G Γ T l.
Proof.
  intros HT t t' T0 Ht Ht' D ET. destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tyEmpty _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | apply actmnf_empty_irr].
Qed.

(** The squash type (M16a): irrelevance, as at [Empty]. *)
Lemma lift_sq {G i Γ T l l1 A} : [ G ; Γ ⊢[ i ] T ⤳* tySq l1 A @ l ] -> Lift i G Γ T l.
Proof.
  intros HT t t' T0 Ht Ht' D ET. destruct (ac_tmne_whne D) as [Hn Hn'].
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HT) | exact (whnf_tySq _ _) | constructor | constructor
                   | exact (whnf_ne _ Hn) | exact (whnf_ne _ Hn') | apply actmnf_sq_irr].
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

(** A neutral of the domain, reflected into its relation. *)
Lemma ne_dom {E : GenericEq} {EL : GenericEqLaws} {LP : LRParams} {VL : VPLaws lr_vp} {VN : VPNe}
  {i Hi n G Γ A A' l1 R a} : E = DeclEq i Hi ->
  @LR E LP n (@LRbelow E LP n) G Γ A A' l1 R -> whne a ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> R a a.
Proof.
  intros -> HR Hn Ha EA. pose proof (compt_typeof_self _ Hi) as Hty.
  apply (LR_neutral _ _ _ _ _ _ _ HR).
  - refine (conj Hn (conj Hn _)). exact (eqtm_refl _ _ _ _ _ _ Ha).
  - refine (conj Hn (conj Hn _)).
    eapply eqtm_conv; [exact (eqtm_refl _ _ _ _ _ _ Ha) | rewrite Hty; exact (eqty_sym _ _ _ _ _ _ EA)].
Qed.

Lemma LR_lift_D n G Γ T T' l R : @LR DEP LR_P n (@LRbelow DEP LR_P n) G Γ T T' l R -> Lift lD G Γ T l.
Proof.
  induction 1 as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd IHdom arAd HR
                 | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                     HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                     widxAd IHwidx Hwisym Hwistr wdomAd IHwdom warAd wotAd wchAd wixAd HR
                 | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                     Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                     HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
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
  - assert (HΓ : [ G ; Γ ⊢[ lD ] ]) by exact (ctx_of_wf_ty (i := lD) eq_refl HA).
    pose proof (IHdom (kw_loc (E := DEP) wk_id (wkwf_id Γ) HΓ)) as XA.
    pose proof (domAd (kw_loc (E := DEP) wk_id (wkwf_id Γ) HΓ)) as HRA.
    unfold kty, kw_loc in XA, HRA; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in XA, HRA.
    rewrite ren_id_ty in XA by exact (wf_ty_nf HA).
    rewrite !ren_id_ty in HRA by first [exact (wf_ty_nf HA) | exact (wf_ty_nf HA')].
    apply (lift_sig compt_D HT Hl Hw1 Hw2 HA HB XA). intros p Hp Hpt.
    pose proof (wf_fst _ _ _ _ _ _ _ _ (compt_notV compt_D) Hw1 Hw2 HA HB Hpt) as Hf.
    pose proof (ne_dom (i := lD) (Hi := compt_D) eq_refl HRA (whne_fst _ _ _ _ _ Hp) Hf HAA) as ha.
    pose proof (IHcod (kw_loc (E := DEP) wk_id (wkwf_id Γ) HΓ) _ _ ha) as XB.
    unfold ktyl, kw_loc in XB; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in XB.
    rewrite ren_lift_id_ty in XB by exact (wf_ty_nf HB). exact XB.
  - exact (lift_unit HT).
  - exact (lift_seq HT).
  - exact (lift_sempty HT).
  - exact (lift_posty compt_D HT (whnf_tyId _ _ _ _) (posty_id _ _ _ _)).
  - exact (lift_empty HT).
  - exact (lift_posty compt_D HT (whnf_tySum _ _ _ _) (posty_sum _ _ _ _)).
  - exact (lift_posty compt_D HT (whnf_tyW _ _ _ _) (posty_W _ _ _ _)).
  - exact (lift_posty compt_D HT (whnf_tyWf _ _ _) (posty_wf _ _ _)).
  - exact (lift_sq HT).
  - exact (lift_posty compt_D HT (whnf_tyIWf _ _ _ _ _ _ _ _) (posty_iwf _ _ _ _ _ _ _ _)).
Qed.

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
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd IHdom arAd HR
                 | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                     HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                     widxAd IHwidx Hwisym Hwistr wdomAd IHwdom warAd wotAd wchAd wixAd HR
                 | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                     Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                     HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR].
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
  - assert (HΓ : [ G ; Γ ⊢[ lM ] ]) by exact (ctx_of_wf_ty (i := lM) eq_refl HA).
    pose proof (IHdom (kw_loc (E := DEM) wk_id (wkwf_id Γ) HΓ)) as XA.
    pose proof (domAd (kw_loc (E := DEM) wk_id (wkwf_id Γ) HΓ)) as HRA.
    unfold kty, kw_loc in XA, HRA; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in XA, HRA.
    rewrite ren_id_ty in XA by exact (wf_ty_nf HA).
    rewrite !ren_id_ty in HRA by first [exact (wf_ty_nf HA) | exact (wf_ty_nf HA')].
    apply (lift_sig compt_M HT Hl Hw1 Hw2 HA HB XA). intros p Hp Hpt.
    pose proof (wf_fst _ _ _ _ _ _ _ _ (compt_notV compt_M) Hw1 Hw2 HA HB Hpt) as Hf.
    pose proof (ne_dom (i := lM) (Hi := compt_M) eq_refl HRA (whne_fst _ _ _ _ _ Hp) Hf HAA) as ha.
    pose proof (IHcod (kw_loc (E := DEM) wk_id (wkwf_id Γ) HΓ) _ _ ha) as XB.
    unfold ktyl, kw_loc in XB; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in XB.
    rewrite ren_lift_id_ty in XB by exact (wf_ty_nf HB). exact XB.
  - exact (lift_unit HT).
  - exact (lift_seq HT).
  - exact (lift_sempty HT).
  - exact (lift_posty compt_M HT (whnf_tyId _ _ _ _) (posty_id _ _ _ _)).
  - exact (lift_empty HT).
  - exact (lift_posty compt_M HT (whnf_tySum _ _ _ _) (posty_sum _ _ _ _)).
  - exact (lift_posty compt_M HT (whnf_tyW _ _ _ _) (posty_W _ _ _ _)).
  - exact (lift_posty compt_M HT (whnf_tyWf _ _ _) (posty_wf _ _ _)).
  - exact (lift_sq HT).
  - exact (lift_posty compt_M HT (whnf_tyIWf _ _ _ _ _ _ _ _) (posty_iwf _ _ _ _ _ _ _ _)).
Qed.

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
