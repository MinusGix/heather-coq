(** * Decidability of algorithmic conversion (08:236; M6_DESIGN.md step 6)

    Induction on a derivation whose left side is the given one (by
    completeness, reflexivity supplies it), for every typed right side.
    The right side is normalized (typed syntax has a whnf) and compared by
    head; a component under a binder is decided once the binder's
    components are, the binder moved to the left side's by soundness. A
    negative answer inverts the algorithm on the left side's head ([ainv_*]);
    neutrals infer a unique type ([ac_infer_uniq]). Decidability is in
    [Prop] (H1). *)
From DeLaM.Validity Require Export AlgComplete.

(** ** Uniqueness of the inferred type *)

Lemma ac_infer_uniq_all :
  (forall G Γ T T', ac_ty G Γ T T' -> True) /\
  (forall G Γ W W', ac_tynf G Γ W W' -> True) /\
  (forall G Γ V V', ac_tyne G Γ V V' -> True) /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> True) /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> True) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> True) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> forall ν2 T2, ac_tmne G Γ ν ν2 T2 -> T = T2) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> forall ν2 W2, ac_tmnee G Γ ν ν2 W2 -> W = W2) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> True).
Proof.
  apply ac_mut; intros; try exact I;
    lazymatch goal with D2 : ?J |- _ =>
      lazymatch J with ac_tmne _ _ _ _ _ => inversion D2; subst; try kill_ne; try kill_box
                 | ac_tmnee _ _ _ _ _ => inversion D2; subst end end;
    repeat match goal with E : mkrb _ _ _ = mkrb _ _ _ |- _ => destruct (mkrb_inj_MT E) as [<- <-]; clear E end;
    try reflexivity;
    first
    [ match goal with H1 : in_ctx _ _ _ _, H2 : in_ctx _ _ _ _ |- _ =>
        destruct (in_ctx_det H1 H2) as [-> _]; reflexivity end
    | match goal with H1 : in_gctx _ _ _, H2 : in_gctx _ _ _ |- _ =>
        let E := fresh "E" in pose proof (in_gctx_det H1 H2) as E; injection E; intros; subst; reflexivity end
    | match goal with IH : forall _ _, ac_tmnee _ _ _ _ _ -> _ = _, D : ac_tmnee _ _ _ _ _ |- _ =>
        let E := fresh "E" in pose proof (IH _ _ D) as E; injection E; intros; subst; reflexivity end
    | match goal with IH : forall _ _, ac_tmne _ _ _ _ _ -> _ = _, D : ac_tmne _ _ _ _ _ |- _ =>
        let E := fresh "E" in pose proof (IH _ _ D) as E; subst; eapply reds_ty_whnf_det; eassumption end ].
Qed.

Lemma ac_ne_uniq {G Γ ν ν1 ν2 T1 T2} : ac_tmne G Γ ν ν1 T1 -> ac_tmne G Γ ν ν2 T2 -> T1 = T2.
Proof. intros D1 D2. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_infer_uniq_all)))))) _ _ _ _ _ D1 _ _ D2). Qed.
Lemma ac_nee_uniq {G Γ ν ν1 ν2 W1 W2} : ac_tmnee G Γ ν ν1 W1 -> ac_tmnee G Γ ν ν2 W2 -> W1 = W2.
Proof. intros D1 D2. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_infer_uniq_all))))))) _ _ _ _ _ D1 _ _ D2). Qed.

(** ** The statements

    The second index is the derivation's other side, unused: any
    derivation with the given left side will do. *)

Definition Dc_ty G Γ T (_ : ty) : Prop := forall T' i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> Dec (ac_ty G Γ T T').
Definition Dc_tynf G Γ T (_ : ty) : Prop := forall T' i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> Dec (ac_tynf G Γ T T').
Definition Dc_tyne G Γ T (_ : ty) : Prop := forall T' i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> Dec (ac_tyne G Γ T T').
Definition Dc_ctx G Δ (_ : ctx) : Prop := forall Δ',
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> Dec (ac_ctx G Δ Δ').
Definition Dc_tm G Γ t (_ : tm) T : Prop := forall t' i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec (ac_tm G Γ t t' T).
Definition Dc_tmnf G Γ t (_ : tm) T : Prop := forall t' i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec (ac_tmnf G Γ t t' T).
Definition Dc_ne G Γ ν (_ : tm) T : Prop := forall ν' i k k' A A', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> Dec (ac_tmne G Γ ν ν' T).
Definition Dc_nee G Γ ν (_ : tm) W : Prop := forall ν' i k k' A A', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> Dec (ac_tmnee G Γ ν ν' W).
Definition Dc_sub G Γ d (_ : lsub) Θ : Prop := forall d' i, compt i -> [ G ; Θ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] d : Θ ] -> [ G ; Γ ⊢[ i ] d' : Θ ] -> Dec (ac_sub G Γ d d' Θ).

(** A negative answer, by inversion of the algorithm. *)
Ltac refute := right; let D := fresh "D" in intros D; inversion D; subst; try kill_ne; kill_box;
  try solve [contradiction | congruence].


(** ** Types *)

Lemma Dc_act_red {G Γ T T0 W W0} : reds_ty T W -> whnf_ty W -> Dc_tynf G Γ W W0 -> Dc_ty G Γ T T0.
Proof.
  intros Hr Hw IH T' i k k' Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (tgt_whnf Hc HT') as (W' & Hr' & Hw' & E').
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT Hr Hw)) as HW.
  destruct (IH W' i k k' Hc HW (eqty_wf_r Hi E')) as [D | N].
  - left. exact (act_red _ _ _ _ _ _ Hr Hr' Hw Hw' D).
  - right. intros D. destruct (ainv_ty D) as (W1 & W1' & Hr1 & Hr1' & Hw1 & Hw1' & D1).
    rewrite <- (reds_ty_whnf_det _ _ _ Hr Hr1 Hw Hw1), <- (reds_ty_whnf_det _ _ _ Hr' Hr1' Hw' Hw1') in D1.
    exact (N D1).
Qed.

Lemma Dc_actnf_nat {G Γ} : Dc_tynf G Γ tyNat tyNat.
Proof. intros X *; destruct X; try solve [refute]. left; apply actnf_nat. Qed.

Lemma Dc_actnf_U {G Γ l l0} : Dc_tynf G Γ (tyU l) (tyU l0).
Proof.
  intros X *; destruct X; try solve [refute]. intros.
  match goal with |- Dec (ac_tynf _ _ _ (tyU ?l')) =>
    destruct (leqv_dec l l') as [Hl | N]; [left; exact (actnf_U _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actnf_pi {G Γ l1 l2 l3 l4 A A0 B B0} :
  Dc_ty G Γ A A0 -> Dc_ty G (Γ ,, A @ l1) B B0 -> Dc_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A0 B0).
Proof.
  intros IHA IHB X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyPi ?a ?b ?c ?d)) =>
    rename a into l5, b into l6, c into A', d into B' end.
  destruct (inv_ty_pi HX) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_pi HX') as ((_ & W5 & W6 & HA' & HB') & _).
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E15)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E15) HΓA HB') as HB1.
  destruct (IHB B' i _ _ Hc HB HB1) as [DB | N]; [left; apply actnf_pi; assumption | refute].
Qed.

Lemma Dc_actnf_ne {G Γ V V0} : ac_tyne G Γ V V0 -> Dc_tyne G Γ V V0 -> Dc_tynf G Γ V V0.
Proof.
  intros D0 IH X i k k' Hc HX HX'.
  destruct (IH X i k k' Hc HX HX') as [D | N]; [left; exact (actnf_ne _ _ _ _ D) |].
  right; intros D; exact (N (ainv_nfne (proj1 (ac_tyne_whne D0)) D)).
Qed.

Lemma Dc_actnf_CTyp {G Γ Δ Δ0 l l0} : Dc_ctx G Δ Δ0 -> Dc_tynf G Γ (tyCTyp Δ l) (tyCTyp Δ0 l0).
Proof.
  intros IH X i k k' Hc HX HX'. destruct X; try solve [refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyCTyp ?a ?b)) => rename a into Δ', b into l' end.
  destruct (inv_ty_CTyp HX) as ((_ & _ & HΔ & _) & _). destruct (inv_ty_CTyp HX') as ((_ & _ & HΔ' & _) & _).
  destruct (IH Δ' HΔ HΔ') as [Dc | N]; [| refute].
  destruct (leqv_dec l l') as [Hl | N]; [left; apply actnf_CTyp; assumption | refute].
Qed.

Lemma Dc_actnf_CTrm {G Γ Δ Δ0 T T0 l l0} : ac_ctx G Δ Δ0 -> Dc_ctx G Δ Δ0 -> Dc_ty G Δ T T0 ->
  Dc_tynf G Γ (tyCTrm Δ T l) (tyCTrm Δ0 T0 l0).
Proof.
  intros _ IHc IHT X i k k' Hc HX HX'. destruct X; try solve [refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyCTrm ?a ?b ?c)) => rename a into Δ', b into T', c into l' end.
  destruct (inv_ty_CTrm HX) as ((_ & _ & HΔ & HT & _) & _).
  destruct (inv_ty_CTrm HX') as ((_ & _ & HΔ' & HT' & _) & _).
  destruct (IHc Δ' HΔ HΔ') as [Dc | N]; [| refute].
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  destruct (IHT T' lD _ _ compt_D HT (mvD (eqctx_sym_D Ec) HT')) as [DT | N]; [| refute].
  destruct (leqv_dec l l') as [Hl | N]; [left; apply actnf_CTrm; assumption | refute].
Qed.

Lemma Dc_actnf_upi {G Γ n l l0 T T0} : Dc_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T0 ->
  Dc_tynf G Γ (tyUPi n l T) (tyUPi n l0 T0).
Proof.
  intros IH X i k k' Hc HX HX'. destruct X; try solve [refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyUPi ?a ?b ?c)) => rename a into n', b into l', c into T' end.
  destruct (dec_nat_eq n n') as [<- | N]; [| refute].
  destruct (inv_ty_upi HX) as ((_ & _ & _ & _ & HT) & _). destruct (inv_ty_upi HX') as ((_ & _ & _ & _ & HT') & _).
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  destruct (IH T' lM _ _ compt_M HT HT') as [DT | N]; [left; apply actnf_upi; assumption | refute].
Qed.

Lemma Dc_actnf_cpi {G Γ l l0 T T0} : Dc_ty (gext G gdCtx) Γ⟪S⟫ T T0 -> Dc_tynf G Γ (tyCPi l T) (tyCPi l0 T0).
Proof.
  intros IH X i k k' Hc HX HX'. destruct X; try solve [refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyCPi ?b ?c)) => rename b into l', c into T' end.
  destruct (inv_ty_cpi HX) as ((_ & _ & _ & HT) & _). destruct (inv_ty_cpi HX') as ((_ & _ & _ & HT') & _).
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  destruct (IH T' lM _ _ compt_M HT HT') as [DT | N]; [left; apply actnf_cpi; assumption | refute].
Qed.

Lemma Dc_actnf_tpi {G Γ Δ Δ0 l1 l2 l3 l4 T T0} : Dc_ctx G Δ Δ0 ->
  Dc_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T0 -> Dc_tynf G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ0 l3 l4 T0).
Proof.
  intros IHc IH X i k k' Hc HX HX'. destruct X; try solve [refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyTPi ?a ?b ?c ?d)) => rename a into Δ', b into l5, c into l6, d into T' end.
  destruct (inv_ty_tpi HX) as ((_ & HΓ & HΔ & W1 & W2 & HT) & _).
  destruct (inv_ty_tpi HX') as ((_ & _ & HΔ' & W5 & W6 & HT') & _).
  destruct (IHc Δ' HΔ HΔ') as [Dc | N]; [| refute].
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (GEq_bind (ctx_glob _ _ _ HΓ) (eqctx_sym_D Ec)
                (lequiv_sym _ _ _ (leqv_lequiv _ _ _ W1 W5 H15))) as HE.
  destruct (IH T' lM _ _ compt_M HT (gconv_ty HE HT')) as [DT | N]; [left; apply actnf_tpi; assumption | refute].
Qed.

Lemma Dc_actne_gvar {G Γ U Δ i' l d d0} : in_gctx (gΨ G) U (gdTy Δ i' l) -> Dc_sub G Γ d d0 Δ ->
  Dc_tyne G Γ (tyGvar U d) (tyGvar U d0).
Proof.
  intros Hin IH X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute].
  match goal with |- Dec (ac_tyne _ _ _ (tyGvar ?a ?b)) => rename a into U', b into d' end.
  destruct (dec_nat_eq U U') as [<- | N]; [| refute].
  destruct (inv_ty_gvar HX) as (Δ0 & i0 & l0 & (Hv & HΓ & Hin0 & Hle & Ht & Hn & He) & _).
  destruct (inv_ty_gvar HX') as (Δ1 & i1 & l1 & (_ & _ & Hin1 & _ & Ht' & Hn' & He') & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <-.
  rewrite Hi in HΓ.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (HΔ & _).
  destruct (IH d' i Hc (lift_ctx HΔ (lle_D_compt _ Hc)) (lsub_wf_prem Hi HΓ Ht Hn He)
              (lsub_wf_prem Hi HΓ Ht' Hn' He')) as [Ds | N]; [left; eapply actne_gvar; eassumption |].
  right; intros D. destruct (ainv_tygvar D) as (Δ2 & i2 & l2 & d2 & E & Hin2 & Ds).
  injection E as <-. pose proof (in_gctx_det Hin Hin2) as E. injection E as <- <- <-. exact (N Ds).
Qed.

Lemma Dc_actne_El {G Γ l l0 ν ν0 W} : ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_tyne G Γ (tyEl l ν) (tyEl l0 ν0).
Proof.
  intros D0 IH X i k k' Hc HX HX'. destruct X; try solve [refute].
  match goal with |- Dec (ac_tyne _ _ _ (tyEl ?a ?b)) => rename a into l', b into ν' end.
  destruct (inv_ty_El HX) as ((_ & _ & Hν) & _). destruct (inv_ty_El HX') as ((_ & _ & Hν') & _).
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  destruct (IH ν' i _ _ _ _ Hc Hν Hν') as [Dν | N]; [left; eapply actne_El; eassumption |].
  right; intros D. destruct (ainv_El D) as (l2 & ν2 & W2 & E & _ & Dν). injection E as <- <-.
  rewrite <- (ac_nee_uniq D0 Dν) in Dν. exact (N Dν).
Qed.

(** ** Local contexts *)

Lemma Dc_acc_nil {G} : Dc_ctx G cnil cnil.
Proof. intros X *; destruct X; try solve [refute]. left; apply acc_nil. Qed.

Lemma Dc_acc_var {G g} : Dc_ctx G (cvar g) (cvar g).
Proof.
  intros X ? ?; destruct X; try solve [refute].
  match goal with |- Dec (ac_ctx _ _ (cvar ?a)) =>
    destruct (dec_nat_eq g a) as [<- | N]; [left; apply acc_var | refute] end.
Qed.

Lemma Dc_acc_ext {G Γ Γ0 A A0 l l0} : Dc_ctx G Γ Γ0 -> Dc_ty G Γ A A0 -> Dc_ctx G (Γ ,, A @ l) (Γ0 ,, A0 @ l0).
Proof.
  intros IHc IHA X H H'. destruct X; try solve [refute].
  match goal with |- Dec (ac_ctx _ _ (cext ?a ?b ?c)) => rename a into Γ', b into A', c into l' end.
  destruct (wfc_ext_inv H) as (HΓ & HA & _). destruct (wfc_ext_inv H') as (HΓ' & HA' & _).
  destruct (IHc Γ' HΓ HΓ') as [Dc | N]; [| refute].
  pose proof (ac_ctx_sound' Dc HΓ HΓ') as Ec.
  destruct (IHA A' lD _ _ compt_D HA (mvD (eqctx_sym_D Ec) HA')) as [DA | N]; [| refute].
  destruct (leqv_dec l l') as [Hl | N]; [left; apply acc_ext; assumption | refute].
Qed.

(** ** Terms *)

Lemma Dc_actm_red {G Γ t t0 T w w0 W} : reds_ty T W -> whnf_ty W -> reds t w -> whnf w ->
  Dc_tmnf G Γ w w0 W -> Dc_tm G Γ t t0 T.
Proof.
  intros HrT HwT Hr Hw IH t' i k Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (tgt_whnf_tm i Hc Ht') as (w' & Hr' & Hw').
  pose proof (red_ty_sound Hc (wf_tm_ty Hi Ht) HrT HwT) as ET.
  assert (EW : [ G ; Γ ⊢[ typeof i ] W ≅ T @ k ]) by (rewrite Hi; exact (eqty_sym _ _ _ _ _ _ ET)).
  pose proof (eqtm_wf_r Hi (red_tm_sound Hc Ht Hr Hw)) as Hw0.
  pose proof (eqtm_wf_r Hi (red_tm_sound Hc Ht' Hr' Hw')) as Hw0'.
  destruct (IH w' i k Hc (wf_conv _ _ _ _ _ _ _ Hw0 EW) (wf_conv _ _ _ _ _ _ _ Hw0' EW)) as [D | N].
  - left. exact (actm_red _ _ _ _ _ _ _ _ HrT HwT Hr Hr' Hw Hw' D).
  - right. intros D. destruct (ainv_tm D) as (W2 & w2 & w3 & HrT2 & HwT2 & Hr2 & Hr3 & Hw2 & Hw3 & D2).
    rewrite <- (reds_ty_whnf_det _ _ _ HrT HrT2 HwT HwT2), <- (reds_whnf_det _ _ _ Hr Hr2 Hw Hw2),
      <- (reds_whnf_det _ _ _ Hr' Hr3 Hw' Hw3) in D2.
    exact (N D2).
Qed.

Lemma Dc_actmnf_code_nat {G Γ l} : Dc_tmnf G Γ tmNat tmNat (tyU l).
Proof. intros x i k1 Hc Hx Hx'; destruct x; try solve [refute]. left; apply actmnf_code_nat. Qed.

Lemma Dc_actmnf_code_U {G Γ l k k0} : Dc_tmnf G Γ (tmU k) (tmU k0) (tyU l).
Proof.
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmU ?a) _) =>
    destruct (leqv_dec k a) as [Hl | N]; [left; exact (actmnf_code_U _ _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s0 t t0} :
  Dc_tm G Γ s s0 (tyU l1) -> Dc_tm G (Γ ,, tyEl l1 s @ l1) t t0 (tyU l2) ->
  Dc_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s0 t0) (tyU l).
Proof.
  intros IHs IHt x i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmPi ?a ?b ?c ?d) _) =>
    rename a into l5, b into l6, c into s', d into t' end.
  destruct (code_pi_prem Hc Hx) as (Hv & W1 & W2 & Hs & Ht).
  destruct (code_pi_prem Hc Hx') as (_ & W5 & W6 & Hs' & Ht').
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15. pose proof (leqv_lequiv _ _ _ W2 W6 H26) as E26.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU15 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l5 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E15)] | rewrite Hi; exact EU15]. }
  destruct (IHs s' i _ Hc Hs Hs1) as [Ds | N]; [| refute].
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l5 s' @ l1 ]) by (apply eqty_El; [exact Hv | exact E15 | exact Es]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl l5 s' ≅ tyEl l1 s @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E15)]).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  assert (Ht1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EEl' (lequiv_sym _ _ _ E15) HΓ1 Ht') |
                                       exact (lequiv_suc _ _ _ E26)] |].
    rewrite Hi. apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E26]. }
  destruct (IHt t' i _ Hc Ht Ht1) as [Dt | N]; [left; apply actmnf_code_pi; assumption | refute].
Qed.

Lemma Dc_actmnf_zero {G Γ} : Dc_tmnf G Γ zero zero tyNat.
Proof. intros x i k1 Hc Hx Hx'; destruct x; try solve [refute]. left; apply actmnf_zero. Qed.

Lemma Dc_actmnf_succ {G Γ t t0} : Dc_tm G Γ t t0 tyNat -> Dc_tmnf G Γ (succ t) (succ t0) tyNat.
Proof.
  intros IH x i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute].
  match goal with |- Dec (ac_tmnf _ _ _ (succ ?a) _) => rename a into t' end.
  destruct (inv_succ Hi Hx) as ((_ & Ht) & _). destruct (inv_succ Hi Hx') as ((_ & Ht') & _).
  destruct (IH t' i lzero Hc Ht Ht') as [D | N]; [left; apply actmnf_succ; exact D | refute].
Qed.

Lemma Dc_actmnf_ne {G Γ ν ν0 W W0} : posty W -> ac_tmnee G Γ ν ν0 W0 -> Dc_nee G Γ ν ν0 W0 ->
  Dc_tmnf G Γ ν ν0 W.
Proof.
  intros Hp D0 IH x i k Hc Hν Hx.
  destruct (IH x i k k _ _ Hc Hν Hx) as [D | N]; [left; exact (actmnf_ne _ _ _ _ _ _ Hp D) |].
  right; intros D. destruct (ainv_nfne_tm Hp (proj1 (ac_tmnee_whne D0)) D) as (W2 & D2).
  rewrite <- (ac_nee_uniq D0 D2) in D2. exact (N D2).
Qed.

Lemma Dc_actmnf_eta {G Γ l l' A B w w0} :
  Dc_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app w0⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  Dc_tmnf G Γ w w0 (tyPi l l' A B).
Proof.
  intros IH x i k Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi (wf_tm_ty Hi Hw)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  destruct (IH _ i l' Hc (pre_eta_body Hi Hv W1 W2 HA HB (lvl_eq_tm' Hk Hw))
              (pre_eta_body Hi Hv W1 W2 HA HB (lvl_eq_tm' Hk Hx))) as [D | N];
    [left; exact (actmnf_eta _ _ _ _ _ _ _ _ D) | right; intros D; exact (N (ainv_eta D))].
Qed.

Lemma Dc_actmnf_ueta {G Γ n l T w w0} :
  Dc_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w0⟨ush n⟩ᵤ (ubvars n)) T ->
  Dc_tmnf G Γ w w0 (tyUPi n l T).
Proof.
  intros IH x i k Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_upi (wf_tm_ty Hi Hw)) as ((-> & HΓ & Hn & W & HT) & Hk).
  destruct (IH _ lM l compt_M (wf_ueta_body W HT (lvl_eq_tm' Hk Hw)) (wf_ueta_body W HT (lvl_eq_tm' Hk Hx)))
    as [D | N]; [left; exact (actmnf_ueta _ _ _ _ _ _ _ D) | right; intros D; exact (N (ainv_ueta D))].
Qed.

Lemma Dc_actmnf_ceta {G Γ l T w w0} :
  Dc_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w0⟪S⟫ (cvar 0)) T -> Dc_tmnf G Γ w w0 (tyCPi l T).
Proof.
  intros IH x i k Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_cpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & W & HT) & Hk).
  destruct (IH _ lM l compt_M (wf_ceta_body W HT (lvl_eq_tm' Hk Hw)) (wf_ceta_body W HT (lvl_eq_tm' Hk Hx)))
    as [D | N]; [left; exact (actmnf_ceta _ _ _ _ _ _ D) | right; intros D; exact (N (ainv_ceta D))].
Qed.

Lemma Dc_actmnf_teta {G Γ Δ l l' T w w0} :
  Dc_tm (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w0⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  Dc_tmnf G Γ w w0 (tyTPi Δ l l' T).
Proof.
  intros IH x i k Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_tpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & HΔ & W1 & W2 & HT) & Hk).
  destruct (IH _ lM l' compt_M (wf_teta_body HΔ W1 W2 HT (lvl_eq_tm' Hk Hw))
              (wf_teta_body HΔ W1 W2 HT (lvl_eq_tm' Hk Hx)))
    as [D | N]; [left; exact (actmnf_teta _ _ _ _ _ _ _ _ D) | right; intros D; exact (N (ainv_teta D))].
Qed.

Lemma Dc_actmnf_boxT {G Γ Δ l T T0} : Dc_tmnf G Γ (boxT T) (boxT T0) (tyCTyp Δ l).
Proof.
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute].
  match goal with |- Dec (ac_tmnf _ _ _ (boxT ?a) _) =>
    destruct (ty_leq_dec T a) as [Hl | N]; [left; exact (actmnf_boxT _ _ _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actmnf_boxt {G Γ Δ A l t t0} : Dc_tmnf G Γ (boxt t) (boxt t0) (tyCTrm Δ A l).
Proof.
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute].
  match goal with |- Dec (ac_tmnf _ _ _ (boxt ?a) _) =>
    destruct (tm_leq_dec t a) as [Hl | N]; [left; exact (actmnf_boxt _ _ _ _ _ _ _ Hl) | refute] end.
Qed.

(** ** Local substitutions

    Pointwise, from the context's deepest entry: an entry's type is
    instantiated by the deeper entries, which must be equal first (as
    [lsub_eq_pt]). *)

Lemma sub_dec_pt {G i Γ} (Hc : compt i) : forall Θ d d', [ G ; Θ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] d : Θ ] -> [ G ; Γ ⊢[ i ] d' : Θ ] ->
  (forall n A k, in_ctx Θ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d] @ k ] ->
     Dec (ac_tm G Γ (llk d n) (llk d' n) A[d])) ->
  Dec (forall n A k, in_ctx Θ n A k -> ac_tm G Γ (llk d n) (llk d' n) A[d]).
Proof.
  pose proof (compt_typeof_self _ Hc) as Hi.
  induction Θ as [| g | Θ0 IH B lB]; intros d d' HΘ Hd Hd' Hpt.
  - left; intros n A k Hin; inversion Hin.
  - left; intros n A k Hin; exfalso; exact (no_in_ctx_var _ _ _ _ Hin).
  - destruct (wfc_ext_inv HΘ) as (HΘ0 & HB & _).
    destruct (IH (ldrop 1 d) (ldrop 1 d') HΘ0 (lsub_wf_drop1 Hd) (lsub_wf_drop1 Hd')) as [Y | N].
    + intros n A k Hin Hr. rewrite !llk_ldrop in *. cbn [Nat.add] in *.
      pose proof (Hpt (S n) _ _ (in_there _ _ _ _ _ _ Hin)) as X.
      rewrite shift_subst_ldrop1 in X. exact (X Hr).
    + assert (E0 : [ G ; Γ ⊢[ i ] ldrop 1 d ≅ ldrop 1 d' : Θ0 ]).
      { apply (lsub_eq_pt Hi Θ0 Γ _ _ HΘ0 (lsub_wf_drop1 Hd) (lsub_wf_drop1 Hd')). intros n A k Hin Hr.
        exact (ac_tm_sound Hc (Y n A k Hin) (lsub_wf_var (lsub_wf_drop1 Hd) Hin) Hr). }
      assert (H0 : [ G ; Γ ⊢[ i ] llk d' 0 : B⟨↑⟩[d] @ lB ]).
      { pose proof (lsub_wf_var Hd' (in_here _ _ _)) as X.
        rewrite shift_subst_ldrop1 in X |- *.
        eapply wf_conv; [exact X |]. rewrite Hi. exact (wf_ty_func Hi HB E0). }
      destruct (Hpt 0 _ _ (in_here _ _ _) H0) as [D0 | N0].
      * left. intros n A k Hin.
        inversion Hin as [Γ1 A1 l1 | Γ1 A1 l1 B1 l1' m Hm]; subst; [exact D0 |].
        pose proof (Y m A1 _ Hm) as X. rewrite !llk_ldrop in X. cbn [Nat.add] in X.
        rewrite shift_subst_ldrop1. exact X.
      * right. intros Hall. exact (N0 (Hall 0 _ _ (in_here _ _ _))).
    + right. intros Hall. apply N. intros n A k Hin. rewrite !llk_ldrop. cbn [Nat.add].
      rewrite <- shift_subst_ldrop1. exact (Hall (S n) _ _ (in_there _ _ _ _ _ _ Hin)).
Qed.

Lemma Dc_acs_pt {G Γ d d0 Θ} :
  (forall n A k, in_ctx Θ n A k -> Dc_tm G Γ (llk d n) (llk d0 n) A[d]) -> Dc_sub G Γ d d0 Θ.
Proof.
  intros IH d' i Hc HΘ Hd Hd'.
  destruct (sub_dec_pt Hc Θ d d' HΘ Hd Hd'
              (fun n A k Hin Hr => IH n A k Hin (llk d' n) i k Hc (lsub_wf_var Hd Hin) Hr)) as [Y | N];
    [left; exact (acs_pt _ _ _ _ _ Y) | right; intros D; exact (N (ainv_sub D))].
Qed.

(** ** Neutral terms *)

Lemma Dc_actmnee_red {G Γ ν ν0 T W} : ac_tmne G Γ ν ν0 T -> Dc_ne G Γ ν ν0 T -> reds_ty T W -> whnf_ty W ->
  Dc_nee G Γ ν ν0 W.
Proof.
  intros D0 IH Hr Hw ν' i k k' A A' Hc Hν Hν'.
  destruct (IH ν' i k k' A A' Hc Hν Hν') as [D | N]; [left; exact (actmnee_red _ _ _ _ _ _ D Hr Hw) |].
  right; intros D. destruct (ainv_nee D) as (T2 & D2 & Hr2 & _).
  rewrite <- (ac_ne_uniq D0 D2) in D2. exact (N D2).
Qed.

Lemma Dc_actmne_var {G Γ n T l} : in_ctx Γ n T l -> Dc_ne G Γ (var n) (var n) T.
Proof.
  intros Hin x i k k' A A' Hc Hν Hx. destruct x; try solve [refute].
  match goal with |- Dec (ac_tmne _ _ _ (var ?a) _) =>
    destruct (dec_nat_eq n a) as [<- | N]; [left; exact (actmne_var _ _ _ _ _ Hin) | refute] end.
Qed.

Lemma Dc_actmne_gvar {G Γ u Δ i' T l d d0} : in_gctx (gΨ G) u (gdTm Δ i' T l) -> Dc_sub G Γ d d0 Δ ->
  Dc_ne G Γ (gvar u d) (gvar u d0) T[d].
Proof.
  intros Hin IH x i k k' X X' Hc Hν Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute].
  match goal with |- Dec (ac_tmne _ _ _ (gvar ?a ?b) _) => rename a into u', b into d' end.
  destruct (dec_nat_eq u u') as [<- | N]; [| refute].
  destruct (inv_gvar Hi Hν) as (Δ0 & i0 & T0 & l0 & (HΓ & Hin0 & Hle & Ht & Hn & He) & _ & _).
  destruct (inv_gvar Hi Hx) as (Δ1 & i1 & T1 & l1 & (_ & Hin1 & _ & Ht' & Hn' & He') & _ & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <- <-.
  pose proof HΓ as HΓi. rewrite Hi in HΓi.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓi) Hin) as (HΔ & _).
  destruct (IH d' i Hc (lift_ctx HΔ (lle_D_compt _ Hc)) (lsub_wf_prem Hi HΓi Ht Hn He)
              (lsub_wf_prem Hi HΓi Ht' Hn' He')) as [Ds | N]; [left; eapply actmne_gvar; eassumption |].
  right; intros D. destruct (ainv_gvar D) as (Δ2 & i2 & T2 & l2 & d2 & E & Hin2 & Ds).
  injection E as <-. pose proof (in_gctx_det Hin Hin2) as E. injection E as <- <- <- <-. exact (N Ds).
Qed.

Lemma Dc_actmne_natrec {G Γ l l0 M M0 s s0 z z0 ν ν0 W} :
  Dc_ty G (Γ ,, tyNat @ lzero) M M0 -> Dc_tm G Γ s s0 M[lsingle zero] ->
  Dc_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z0 M[lsucc] ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (natrec l M s z ν) (natrec l0 M0 s0 z0 ν0) M[lsingle ν].
Proof.
  intros IHM IHs IHz Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute].
  match goal with |- Dec (ac_tmne _ _ _ (natrec ?a ?b ?c ?d ?e) _) =>
    rename a into l', b into M', c into s', d into z', e into ν' end.
  destruct (inv_natrec Hi Hx) as ((Hv & Wl & HM & Hs & Hz & Hν) & _ & _).
  destruct (inv_natrec Hi Hx') as ((_ & Wl' & HM' & Hs' & Hz' & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_natrec D) as (l2 & M2 & s2 & z2 & ν2 & W2 & E & _ & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as E.
  destruct (IHM M' i _ _ Hc HM HM') as [DM | N]; [| refute].
  pose proof (ac_ty_sound Hc DM HM (wft_lconv _ _ _ _ _ _ HM' E)) as EM.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  assert (HN : [ G ; Γ ⊢[ i ] tyNat @ lzero ]) by (apply wft_nat; [exact Hv | rewrite Hi; exact HΓ]).
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HN | exact I]).
  assert (H0 : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; [exact Hv | rewrite Hi; exact HΓ]).
  pose proof (eqty_single Hi EM H0) as EM0.
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E] | rewrite Hi; exact EM0]).
  destruct (IHs s' i l Hc Hs Hs1) as [Ds | N]; [| refute].
  assert (HΓM : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] ]) by (apply wfc_ext; assumption).
  assert (EM' : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' ≅ M @ l' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM) | exact (lequiv_sym _ _ _ E)]).
  pose proof (eqty_subst Hi EM (lsub_wf_lsucc Hi Hv HΓM)) as EMs.
  assert (Hz1 : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (stab_tm Hi EM' (lequiv_sym _ _ _ E) HΓM Hz') | exact E]
                        | rewrite Hi; exact EMs]).
  destruct (IHz z' i l Hc Hz Hz1) as [Dz | N]; [left; eapply actmne_natrec; eassumption | refute].
Qed.

Lemma Dc_actmne_app {G Γ l1 l2 l3 l4 A A0 B Bb ν ν0 s s0 m m' A0' B0} :
  ac_tmnee G Γ ν ν0 (tyPi m m' A0' B0) -> Dc_nee G Γ ν ν0 (tyPi m m' A0' B0) -> Dc_tm G Γ s s0 A0' ->
  Dc_ne G Γ (app ν l1 l2 A B s) (app ν0 l3 l4 A0 Bb s0) B0[lsingle s].
Proof.
  intros Dν0 IHν IHs x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute].
  match goal with |- Dec (ac_tmne _ _ _ (app ?a ?b ?c ?d ?e ?f) _) =>
    rename a into ν', b into l5, c into l6, d into A', e into B', f into s' end.
  destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν & Hs) & _ & _).
  destruct (inv_app Hi Hx') as ((_ & W5 & W6 & HA' & HB' & Hν' & Hs') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_app D) as (l7 & l8 & A2 & B2 & ν2 & s2 & m2 & m2' & A1 & B1 & E & Dν2 & _);
       injection E as <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (pi_inj_c Hc E0) as (Em1 & _ & EA0 & _).
  destruct (pi_inj_c Hc E1) as (Em5 & _ & EA1 & _).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em1) Em5) as E15.
  pose proof (retype Hi Hs (lequiv_refl _ _ W1) (eqty_sym _ _ _ _ _ _ EA0)) as Hs0.
  pose proof (retype Hi Hs' E15 (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EA1) E15)) as Hs1.
  destruct (IHs s' i l1 Hc Hs0 Hs1) as [Ds | N]; [left; eapply actmne_app; eassumption |].
  right; intros D. destruct (ainv_app D) as (l7 & l8 & A2 & B2 & ν2 & s2 & m2 & m2' & A1 & B1 & E & Dν2 & Ds2).
  injection E as <- <- <- <- <- <-. pose proof (ac_nee_uniq Dν0 Dν2) as E. injection E as <- <- <- <-.
  exact (N Ds2).
Qed.

Lemma Dc_actmne_uapp {G Γ n l T ν ν0 ls ls0} :
  ac_tmnee G Γ ν ν0 (tyUPi n l T) -> Dc_nee G Γ ν ν0 (tyUPi n l T) -> length ls = n ->
  Dc_ne G Γ (uapp ν ls) (uapp ν0 ls0) T[uext ls lvar]ᵤ.
Proof.
  intros Dν0 IHν Hn x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute].
  match goal with |- Dec (ac_tmne _ _ _ (uapp ?a ?b) _) => rename a into ν', b into ls' end.
  destruct (inv_uapp Hi Hx) as (n0 & l0 & T0 & (-> & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_uapp Hi Hx') as (n1 & l1 & T1 & (_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (IHν ν' lM _ _ _ _ compt_M Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_uapp D) as (n2 & l2 & T2 & ν2 & ls2 & E & Dν2 & _ & _);
       injection E as <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqvs_dec ls ls') as [Hls | N]; [left; eapply actmne_uapp; eassumption | refute].
Qed.

Lemma Dc_actmne_capp {G Γ l T ν ν0 Δ Δ0} :
  ac_tmnee G Γ ν ν0 (tyCPi l T) -> Dc_nee G Γ ν ν0 (tyCPi l T) -> Dc_ctx G Δ Δ0 ->
  Dc_ne G Γ (capp ν Δ) (capp ν0 Δ0) T⦃gsingle (GCtx Δ)⦄.
Proof.
  intros Dν0 IHν IHc x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute].
  match goal with |- Dec (ac_tmne _ _ _ (capp ?a ?b) _) => rename a into ν', b into Δ' end.
  destruct (inv_capp Hi Hx) as (l0 & T0 & (-> & _ & _ & HΔ & Hν & _) & _ & _).
  destruct (inv_capp Hi Hx') as (l1 & T1 & (_ & _ & _ & HΔ' & Hν' & _) & _ & _).
  destruct (IHν ν' lM _ _ _ _ compt_M Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_capp D) as (l2 & T2 & ν2 & Δ2 & E & Dν2 & _);
       injection E as <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (IHc Δ' HΔ HΔ') as [Dc | N]; [left; eapply actmne_capp; eassumption | refute].
Qed.

Lemma Dc_actmne_tapp {G Γ Δ l l' T ν ν0 A A0} :
  ac_tmnee G Γ ν ν0 (tyTPi Δ l l' T) -> Dc_nee G Γ ν ν0 (tyTPi Δ l l' T) -> Dc_ty G Δ A A0 ->
  Dc_ne G Γ (tapp ν A) (tapp ν0 A0) T⦃gsingle (GTy A)⦄.
Proof.
  intros Dν0 IHν IHA x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute].
  match goal with |- Dec (ac_tmne _ _ _ (tapp ?a ?b) _) => rename a into ν', b into A' end.
  destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T0 & (-> & Hν & HΔ0 & _ & _ & _ & HA & _) & _ & _).
  destruct (inv_tapp Hi Hx') as (Δ1 & l1 & l1' & T1 & (_ & Hν' & HΔ1 & _ & _ & _ & HA' & _) & _ & _).
  destruct (IHν ν' lM _ _ _ _ compt_M Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_tapp D) as (Δ2 & l2 & l2' & T2 & ν2 & A2 & E & Dν2 & _);
       injection E as <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & E1 & _).
  destruct (declM_tpi_inj E0) as (Ec0 & _ & _ & _). destruct (declM_tpi_inj E1) as (Ec1 & _ & _ & _).
  destruct (IHA A' lD _ _ compt_D (mvD Ec0 HA) (mvD Ec1 HA')) as [DA | N];
    [left; eapply actmne_tapp; eassumption |].
  right; intros D. destruct (ainv_tapp D) as (Δ2 & l2 & l2' & T2 & ν2 & A2 & E & Dν2 & DA2).
  injection E as <- <-. pose proof (ac_nee_uniq Dν0 Dν2) as E. injection E as <- <- <- <-. exact (N DA2).
Qed.
