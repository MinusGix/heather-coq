(** * Decidability of algorithmic conversion (08:236; M6_DESIGN.md step 6)

    Induction on a derivation whose left side is the given one (by
    completeness, reflexivity supplies it), for every typed right side.
    The right side is normalized (typed syntax has a whnf) and compared by
    head; a component under a binder is decided once the binder's
    components are, the binder moved to the left side's by soundness. A
    negative answer inverts the algorithm on the left side's head ([ainv_*]);
    neutrals infer a unique type ([ac_infer_uniq]). Decidability is in
    [Prop] (H1). *)
From DeLaM.Typing Require Export StaticCodeEq.
From DeLaM.Validity Require Export AlgComplete.

(** ** Uniqueness of the inferred type *)

Lemma elimT_inj {l1 l2 rb l Δ t l1' l2' rb' l' Δ' t'} :
  elimT l1 l2 rb l Δ t = elimT l1' l2' rb' l' Δ' t' ->
  l1 = l1' /\ l2 = l2' /\ rb = rb' /\ l = l' /\ Δ = Δ' /\ t = t'.
Proof. intros H; injection H; auto 7. Qed.
Lemma elimt_inj {l1 l2 rb l Δ T t l1' l2' rb' l' Δ' T' t'} :
  elimt l1 l2 rb l Δ T t = elimt l1' l2' rb' l' Δ' T' t' ->
  l1 = l1' /\ l2 = l2' /\ rb = rb' /\ l = l' /\ Δ = Δ' /\ T = T' /\ t = t'.
Proof. intros H; injection H; auto 8. Qed.

(** The components' equations, except the recursor block's (left to
    [mkrb_inj_MT]). *)
Ltac inj_small := repeat match goal with H : ?a = _ |- _ =>
  lazymatch a with mkrb _ _ _ => fail | _ => injection H; intros; clear H end end.
(** Inversion on the left term's head, cheaper than [inversion] (whose
    proof terms dominated this file): [destruct] with the left index
    remembered, mismatched heads closed by [discriminate]. The recursors go
    through [elimT_inj]: [injection] would unfold the [mkrb] block. *)
Ltac ne_inv D :=
  let x := fresh "x" in let E := fresh "E" in
  lazymatch type of D with ac_tmne _ _ ?v _ _ => remember v as x eqn:E in D end;
  destruct D; try discriminate E;
  lazymatch type of E with
  | elimT _ _ _ _ _ _ = _ => apply elimT_inj in E; decompose [and] E; clear E; inj_small
  | elimt _ _ _ _ _ _ _ = _ => apply elimt_inj in E; decompose [and] E; clear E; inj_small
  | _ => injection E; intros
  end; subst.

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
      lazymatch J with ac_tmne _ _ _ _ _ => ne_inv D2; try kill_ne; try kill_box
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

(** The head constructor of a term. Related neutrals, and related normal
    forms at a positive type, share it: a mismatch is refuted without
    inverting the (large) judgments. *)
Definition tm_con (t : tm) : nat :=
  match t with
  | var _ => 0 | tmErr => 1 | tmNat => 2 | tmPi _ _ _ _ => 3 | tmU _ => 4 | zero => 5 | succ _ => 6
  | natrec _ _ _ _ _ => 7 | lam _ _ _ _ => 8 | app _ _ _ _ _ _ => 9 | gvar _ _ => 10 | boxT _ => 11
  | boxt _ => 12 | letboxT _ _ _ _ _ _ => 13 | letboxt _ _ _ _ _ _ _ => 14 | tmTy _ => 15 | tmTup _ _ => 16
  | bindU _ => 17 | bindG _ => 18 | bindL _ => 19 | elimT _ _ _ _ _ _ => 20 | elimt _ _ _ _ _ _ _ => 21
  | ulam _ _ _ _ => 22 | uapp _ _ => 23 | clam _ _ _ => 24 | capp _ _ => 25 | tlam _ _ _ _ _ => 26 | tapp _ _ => 27
  | tmSig _ _ _ _ => 28 | tmPair _ _ _ _ _ _ => 29 | tmFst _ _ _ _ _ => 30 | tmSnd _ _ _ _ _ => 31
  | tmUnit _ => 32 | tmTriv _ => 33 | gdef _ _ _ => 34 | srefl _ _ _ => 35 | elimSEmpty _ _ _ _ => 36
  | tmRefl _ _ _ => 37 | tmJ _ _ _ _ _ _ _ _ => 38 | tmId _ _ _ _ => 39
  | tmSEq _ _ _ _ => 40 | tmSEmpty _ => 41 | elimEmpty _ _ _ _ => 42
  | tmInl _ _ _ _ _ => 43 | tmInr _ _ _ _ _ => 44 | tmCase _ _ _ _ _ _ _ _ _ => 45
  | tmEmpty _ => 46 | tmSum _ _ _ _ => 47
  | tmSup _ _ _ _ _ _ => 48 | tmElimW _ _ _ _ _ _ _ _ => 49 | tmW _ _ _ _ => 50
  | tmVec _ _ _ => 51 | tmFin _ => 52
  end.

Lemma ac_tmne_con {G Γ ν ν' T} : ac_tmne G Γ ν ν' T -> tm_con ν = tm_con ν'.
Proof. destruct 1; reflexivity. Qed.

Lemma ac_tmnf_con {G Γ w w' W} : ac_tmnf G Γ w w' W -> posty W -> ~ whne w -> tm_con w = tm_con w'.
Proof.
  destruct 1; intros Hp Hn; try reflexivity;
    try match goal with Hd : ac_tmnee _ _ _ _ _ |- _ => exfalso; exact (Hn (proj1 (ac_tmnee_whne Hd))) end;
    inversion Hp; subst; match goal with H : whne_ty _ |- _ => inversion H end.
Qed.

Lemma ac_tynf_head {G Γ W W'} : ac_tynf G Γ W W' -> ty_head W = ty_head W'.
Proof.
  destruct 1; try reflexivity.
  destruct (ac_tyne_whne H) as [Hn Hn']. rewrite (whne_ty_head _ Hn), (whne_ty_head _ Hn'). reflexivity.
Qed.

Ltac refute_con := right; let D := fresh "D" in intros D;
  let E := fresh "E" in
  first [ pose proof (ac_tmne_con D) as E
        | pose proof (ac_tmnf_con D ltac:(first [apply posty_nat | apply posty_U | apply posty_CTyp | apply posty_CTrm | apply posty_id | apply posty_empty | apply posty_sum | apply posty_W]) ltac:(let Hn := fresh in intros Hn; discriminate (whne_ne_head Hn))) as E
        | pose proof (ac_tynf_head D) as E ];
  cbn in E; discriminate E.


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
Proof. intros X *; destruct X; try solve [refute_con | refute]. left; apply actnf_nat. Qed.

Lemma Dc_actnf_U {G Γ l l0} : Dc_tynf G Γ (tyU l) (tyU l0).
Proof.
  intros X *; destruct X; try solve [refute_con | refute]. intros.
  match goal with |- Dec (ac_tynf _ _ _ (tyU ?l')) =>
    destruct (leqv_dec l l') as [Hl | N]; [left; exact (actnf_U _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actnf_pi {G Γ l1 l2 l3 l4 A A0 B B0} :
  Dc_ty G Γ A A0 -> Dc_ty G (Γ ,, A @ l1) B B0 -> Dc_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A0 B0).
Proof.
  intros IHA IHB X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute_con | refute].
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
  intros IH X i k k' Hc HX HX'. destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyCTyp ?a ?b)) => rename a into Δ', b into l' end.
  destruct (inv_ty_CTyp HX) as ((_ & _ & HΔ & _) & _). destruct (inv_ty_CTyp HX') as ((_ & _ & HΔ' & _) & _).
  destruct (IH Δ' HΔ HΔ') as [Dc | N]; [| refute].
  destruct (leqv_dec l l') as [Hl | N]; [left; apply actnf_CTyp; assumption | refute].
Qed.

Lemma Dc_actnf_CTrm {G Γ Δ Δ0 T T0 l l0} : ac_ctx G Δ Δ0 -> Dc_ctx G Δ Δ0 -> Dc_ty G Δ T T0 ->
  Dc_tynf G Γ (tyCTrm Δ T l) (tyCTrm Δ0 T0 l0).
Proof.
  intros _ IHc IHT X i k k' Hc HX HX'. destruct X; try solve [refute_con | refute].
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
  intros IH X i k k' Hc HX HX'. destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyUPi ?a ?b ?c)) => rename a into n', b into l', c into T' end.
  destruct (dec_nat_eq n n') as [<- | N]; [| refute].
  destruct (inv_ty_upi HX) as ((_ & _ & _ & _ & HT) & _). destruct (inv_ty_upi HX') as ((_ & _ & _ & _ & HT') & _).
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  destruct (IH T' lM _ _ compt_M HT HT') as [DT | N]; [left; apply actnf_upi; assumption | refute].
Qed.

Lemma Dc_actnf_cpi {G Γ l l0 T T0} : Dc_ty (gext G gdCtx) Γ⟪S⟫ T T0 -> Dc_tynf G Γ (tyCPi l T) (tyCPi l0 T0).
Proof.
  intros IH X i k k' Hc HX HX'. destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyCPi ?b ?c)) => rename b into l', c into T' end.
  destruct (inv_ty_cpi HX) as ((_ & _ & _ & HT) & _). destruct (inv_ty_cpi HX') as ((_ & _ & _ & HT') & _).
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  destruct (IH T' lM _ _ compt_M HT HT') as [DT | N]; [left; apply actnf_cpi; assumption | refute].
Qed.

Lemma Dc_actnf_tpi {G Γ Δ Δ0 l1 l2 l3 l4 T T0} : Dc_ctx G Δ Δ0 ->
  Dc_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T0 -> Dc_tynf G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ0 l3 l4 T0).
Proof.
  intros IHc IH X i k k' Hc HX HX'. destruct X; try solve [refute_con | refute].
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
  destruct X; try solve [refute_con | refute].
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
  intros D0 IH X i k k' Hc HX HX'. destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tyne _ _ _ (tyEl ?a ?b)) => rename a into l', b into ν' end.
  destruct (inv_ty_El HX) as ((_ & _ & Hν) & _). destruct (inv_ty_El HX') as ((_ & _ & Hν') & _).
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  destruct (IH ν' i _ _ _ _ Hc Hν Hν') as [Dν | N]; [left; eapply actne_El; eassumption |].
  right; intros D. destruct (ainv_El D) as (l2 & ν2 & W2 & E & _ & Dν). injection E as <- <-.
  rewrite <- (ac_nee_uniq D0 Dν) in Dν. exact (N Dν).
Qed.

(** [Vec] and [Fin] at a neutral length (M14a). *)
Lemma Dc_actne_vec {G Γ l l0 A A0 ν ν0 W} : ac_tmnee G Γ ν ν0 W -> Dc_ty G Γ A A0 -> Dc_nee G Γ ν ν0 W ->
  Dc_tyne G Γ (tyVec l A ν) (tyVec l0 A0 ν0).
Proof.
  intros D0 IHA IH X i k k' Hc HX HX'. destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tyne _ _ _ (tyVec ?a ?b ?c)) => rename a into l', b into A', c into ν' end.
  destruct (inv_ty_vec HX) as ((_ & _ & HA & Hν) & _). destruct (inv_ty_vec HX') as ((_ & _ & HA' & Hν') & _).
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N].
  2: { right; intros D. destruct (ainv_vec D) as (l2 & A2 & ν2 & W2 & E & _ & DA & _).
       injection E as <- <- <-. exact (N DA). }
  destruct (IH ν' i _ _ _ _ Hc Hν Hν') as [Dν | N]; [left; eapply actne_vec; eassumption |].
  right; intros D. destruct (ainv_vec D) as (l2 & A2 & ν2 & W2 & E & _ & _ & Dν). injection E as <- <- <-.
  rewrite <- (ac_nee_uniq D0 Dν) in Dν. exact (N Dν).
Qed.

Lemma Dc_actne_fin {G Γ ν ν0 W} : ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W -> Dc_tyne G Γ (tyFin ν) (tyFin ν0).
Proof.
  intros D0 IH X i k k' Hc HX HX'. destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tyne _ _ _ (tyFin ?a)) => rename a into ν' end.
  destruct (inv_ty_fin HX) as ((_ & Hν) & _). destruct (inv_ty_fin HX') as ((_ & Hν') & _).
  destruct (IH ν' i _ _ _ _ Hc Hν Hν') as [Dν | N]; [left; eapply actne_fin; eassumption |].
  right; intros D. destruct (ainv_fin D) as (ν2 & W2 & E & Dν). injection E as <-.
  rewrite <- (ac_nee_uniq D0 Dν) in Dν. exact (N Dν).
Qed.

(** ** Local contexts *)

Lemma Dc_acc_nil {G} : Dc_ctx G cnil cnil.
Proof. intros X *; destruct X; try solve [refute_con | refute]. left; apply acc_nil. Qed.

Lemma Dc_acc_var {G g} : Dc_ctx G (cvar g) (cvar g).
Proof.
  intros X ? ?; destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_ctx _ _ (cvar ?a)) =>
    destruct (dec_nat_eq g a) as [<- | N]; [left; apply acc_var | refute] end.
Qed.

Lemma Dc_acc_ext {G Γ Γ0 A A0 l l0} : Dc_ctx G Γ Γ0 -> Dc_ty G Γ A A0 -> Dc_ctx G (Γ ,, A @ l) (Γ0 ,, A0 @ l0).
Proof.
  intros IHc IHA X H H'. destruct X; try solve [refute_con | refute].
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
Proof. intros x i k1 Hc Hx Hx'; destruct x; try solve [refute_con]. left; apply actmnf_code_nat. Qed.

Lemma Dc_actmnf_code_U {G Γ l k k0} : Dc_tmnf G Γ (tmU k) (tmU k0) (tyU l).
Proof.
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmU ?a) _) =>
    destruct (leqv_dec k a) as [Hl | N]; [left; exact (actmnf_code_U _ _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s0 t t0} :
  Dc_tm G Γ s s0 (tyU l1) -> Dc_tm G (Γ ,, tyEl l1 s @ l1) t t0 (tyU l2) ->
  Dc_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s0 t0) (tyU l).
Proof.
  intros IHs IHt x i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
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
Proof. intros x i k1 Hc Hx Hx'; destruct x; try solve [refute_con]. left; apply actmnf_zero. Qed.

Lemma Dc_actmnf_succ {G Γ t t0} : Dc_tm G Γ t t0 tyNat -> Dc_tmnf G Γ (succ t) (succ t0) tyNat.
Proof.
  intros IH x i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
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
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (boxT ?a) _) =>
    destruct (ty_leq_dec T a) as [Hl | N]; [left; exact (actmnf_boxT _ _ _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actmnf_boxt {G Γ Δ A l t t0} : Dc_tmnf G Γ (boxt t) (boxt t0) (tyCTrm Δ A l).
Proof.
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute_con].
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
  intros Hin x i k k' A A' Hc Hν Hx. destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (var ?a) _) =>
    destruct (dec_nat_eq n a) as [<- | N]; [left; exact (actmne_var _ _ _ _ _ Hin) | refute] end.
Qed.

Lemma Dc_actmne_gvar {G Γ u Δ i' T l d d0} : in_gctx (gΨ G) u (gdTm Δ i' T l) -> Dc_sub G Γ d d0 Δ ->
  Dc_ne G Γ (gvar u d) (gvar u d0) T[d].
Proof.
  intros Hin IH x i k k' X X' Hc Hν Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
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
  destruct x; try solve [refute_con].
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
  destruct x; try solve [refute_con].
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
  destruct x; try solve [refute_con].
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
  destruct x; try solve [refute_con].
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
  destruct x; try solve [refute_con].
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

Lemma Dc_actmne_letboxT {G Γ l1 l2 l3 l4 Δ Δ0 M M0 t1 t0 ν ν0 W} :
  Dc_ctx G Δ Δ0 -> Dc_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M0 ->
  Dc_tm (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t0 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (letboxT l1 l2 Δ M t1 ν) (letboxT l3 l4 Δ0 M0 t0 ν0) M[lsingle ν].
Proof.
  intros IHc IHM IHt Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (letboxT ?a ?b ?c ?d ?e ?f) _) =>
    rename a into l5, b into l6, c into Δ', d into M', e into t2, f into ν' end.
  destruct (inv_letboxT Hi Hx) as ((-> & W1 & W2 & HΔ & HM & Ht1 & Hν) & _ & _).
  destruct (inv_letboxT Hi Hx') as ((_ & W5 & W6 & HΔ' & HM' & Ht2 & Hν') & _ & _).
  destruct (IHν ν' lM _ _ _ _ compt_M Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_letboxT D) as (l7 & l8 & Δ2 & M2 & t3 & ν2 & W3 & E & _ & _ & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15. pose proof (leqv_lequiv _ _ _ W2 W6 H26) as E26.
  destruct (IHc Δ' HΔ HΔ') as [Dc | N]; [| refute].
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 @ lzero ]) by (apply wft_CTyp; assumption).
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ' l6 @ lzero ]) by (apply eqty_CTyp; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  pose proof (lequiv_refl (gL G) lzero I) as E00.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC) E00 HΓ1 HM') E15) as HM1.
  destruct (IHM M' lM _ _ compt_M HM HM1) as [DM | N]; [| refute].
  pose proof (ac_ty_sound compt_M DM HM HM1) as EM.
  assert (HGD : [ ⊢ gext G (gdTy Δ lC l2) ]) by (apply wfg_ty; [exact HG | exact HΔ | left; reflexivity | exact W2]).
  pose proof (gbind_tm HG HGD (gbind_obj_ty (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) HGD Ec E26)
                eq_refl Ht2) as Ht2a.
  pose proof (letboxT_body_eq HGD HΔ W2 EM) as EMb.
  assert (Ht2b : [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E15] | exact EMb]).
  destruct (IHt t2 lM l1 compt_M Ht1 Ht2b) as [Dt | N]; [left; eapply actmne_letboxT; eassumption | refute].
Qed.

Lemma Dc_actmne_letboxt {G Γ l1 l2 l3 l4 Δ Δ0 T T0 M M0 t1 t0 ν ν0 W} :
  Dc_ctx G Δ Δ0 -> Dc_ty G Δ T T0 -> Dc_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M0 ->
  Dc_tm (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t0 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (letboxt l1 l2 Δ T M t1 ν) (letboxt l3 l4 Δ0 T0 M0 t0 ν0) M[lsingle ν].
Proof.
  intros IHc IHT IHM IHt Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (letboxt ?a ?b ?c ?d ?e ?f ?g) _) =>
    rename a into l5, b into l6, c into Δ', d into T', e into M', f into t2, g into ν' end.
  destruct (inv_letboxt Hi Hx) as ((-> & W1 & W2 & HΔ & HT & HM & Ht1 & Hν) & _ & _).
  destruct (inv_letboxt Hi Hx') as ((_ & W5 & W6 & HΔ' & HT' & HM' & Ht2 & Hν') & _ & _).
  destruct (IHν ν' lM _ _ _ _ compt_M Hν Hν') as [Dν | N];
    [| right; intros D;
       destruct (ainv_letboxt D) as (l7 & l8 & Δ2 & T2 & M2 & t3 & ν2 & W3 & E & _ & _ & _ & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15. pose proof (leqv_lequiv _ _ _ W2 W6 H26) as E26.
  destruct (IHc Δ' HΔ HΔ') as [Dc | N]; [| refute].
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E26)) as HT1.
  destruct (IHT T' lD _ _ compt_D HT HT1) as [DT | N]; [| refute].
  pose proof (ac_ty_sound compt_D DT HT HT1) as ET.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 @ lzero ]) by (apply wft_CTrm; assumption).
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ' T' l6 @ lzero ]) by (apply eqty_CTrm; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  pose proof (lequiv_refl (gL G) lzero I) as E00.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC) E00 HΓ1 HM') E15) as HM1.
  destruct (IHM M' lM _ _ compt_M HM HM1) as [DM | N]; [| refute].
  pose proof (ac_ty_sound compt_M DM HM HM1) as EM.
  assert (HGD : [ ⊢ gext G (gdTm Δ lC T l2) ]) by (apply wfg_tm; [exact HG | exact HT | right; reflexivity | exact W2]).
  pose proof (gbind_tm HG HGD (gbind_obj_tm HGD Ec ET E26) eq_refl Ht2) as Ht2a.
  pose proof (letboxt_body_eq HGD HΔ HT W2 EM) as EMb.
  assert (Ht2b : [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E15] | exact EMb]).
  destruct (IHt t2 lM l1 compt_M Ht1 Ht2b) as [Dt | N]; [left; eapply actmne_letboxt; eassumption | refute].
Qed.

(** ** The recursors *)

Definition elim_rb (t : tm) : tm :=
  match t with elimT _ _ rb _ _ _ => rb | elimt _ _ rb _ _ _ _ => rb | _ => t end.

(** Inversion with both bundles given. *)
Lemma ainv_elimT' {G Γ l1 l2 MT Mt bs l Δ ν l1' l2' MT' Mt' bs' l' Δ' ν' T} : whne ν ->
  ac_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν') T ->
  leqv l1 l1' /\ leqv l2 l2' /\ leqv l l' /\ ac_ctx G Δ Δ' /\
  (ac_ty (recGT G) (recΓT Γ) MT MT' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
   (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt)))) /\
  exists W, ac_tmnee G Γ ν ν' W.
Proof.
  intros Hn D.
  destruct (ainv_elimT Hn D) as (MTa & Mta & bsa & l1a & l2a & MTb & Mtb & bsb & la & Δa & νa & Wa & Erba & Ex
                                 & H1 & H2 & Hl & Dc & DMT & DMt & Db & Dν).
  pose proof (f_equal elim_rb Ex) as Erb. cbn [elim_rb] in Erb.
  pose proof (mkrb_inj_br Erba) as Eba. pose proof (mkrb_inj_br Erb) as Ebb.
  destruct (mkrb_inj_MT Erba) as [E1 E2]; destruct (mkrb_inj_MT Erb) as [E3 E4]; subst.
  lazymatch type of Ex with
  | elimT _ _ _ _ _ _ = _ => apply elimT_inj in Ex
  | elimt _ _ _ _ _ _ _ = _ => apply elimt_inj in Ex end;
  decompose [and] Ex; clear Ex; inj_small; subst.
  refine (conj H1 (conj H2 (conj Hl (conj Dc (conj (conj DMT (conj DMt _)) (ex_intro _ Wa Dν)))))).
  intros j Hj. rewrite (Eba j Hj), (Ebb j Hj). exact (Db j Hj).
Qed.

Lemma ainv_elimT_gvar' {G Γ l1 l2 MT Mt bs l Δ U d l1' l2' MT' Mt' bs' l' Δ' ν' T} :
  ac_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d))) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν') T ->
  leqv l1 l1' /\ leqv l2 l2' /\ leqv l l' /\ ac_ctx G Δ Δ' /\
  (ac_ty (recGT G) (recΓT Γ) MT MT' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
   (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt)))) /\
  exists d', ν' = boxT (tyGvar U d') /\ lsub_leq d d'.
Proof.
  intros D.
  destruct (ainv_elimT_gvar D) as (MTa & Mta & bsa & l1a & l2a & MTb & Mtb & bsb & la & Δa & da & Erba & Ex
                                   & H1 & H2 & Hl & Dc & DMT & DMt & Db & Hd).
  pose proof (f_equal elim_rb Ex) as Erb. cbn [elim_rb] in Erb.
  pose proof (mkrb_inj_br Erba) as Eba. pose proof (mkrb_inj_br Erb) as Ebb.
  destruct (mkrb_inj_MT Erba) as [E1 E2]; destruct (mkrb_inj_MT Erb) as [E3 E4]; subst.
  lazymatch type of Ex with
  | elimT _ _ _ _ _ _ = _ => apply elimT_inj in Ex
  | elimt _ _ _ _ _ _ _ = _ => apply elimt_inj in Ex end;
  decompose [and] Ex; clear Ex; inj_small; subst.
  refine (conj H1 (conj H2 (conj Hl (conj Dc (conj (conj DMT (conj DMt _)) (ex_intro _ da (conj eq_refl Hd))))))).
  intros j Hj. rewrite (Eba j Hj), (Ebb j Hj). exact (Db j Hj).
Qed.

Lemma ainv_elimt' {G Γ l1 l2 MT Mt bs l Δ A ν l1' l2' MT' Mt' bs' l' Δ' A' ν' T} : whne ν ->
  ac_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ A ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' A' ν') T ->
  leqv l1 l1' /\ leqv l2 l2' /\ leqv l l' /\ ac_ctx G Δ Δ' /\ ac_ty G Δ A A' /\
  (ac_ty (recGT G) (recΓT Γ) MT MT' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
   (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt)))) /\
  exists W, ac_tmnee G Γ ν ν' W.
Proof.
  intros Hn D.
  destruct (ainv_elimt Hn D) as (MTa & Mta & bsa & l1a & l2a & MTb & Mtb & bsb & la & Δa & Aa & νa & Wa & Erba & Ex
                                 & H1 & H2 & Hl & Dc & DA & DMT & DMt & Db & Dν).
  pose proof (f_equal elim_rb Ex) as Erb. cbn [elim_rb] in Erb.
  pose proof (mkrb_inj_br Erba) as Eba. pose proof (mkrb_inj_br Erb) as Ebb.
  destruct (mkrb_inj_MT Erba) as [E1 E2]; destruct (mkrb_inj_MT Erb) as [E3 E4]; subst.
  lazymatch type of Ex with
  | elimT _ _ _ _ _ _ = _ => apply elimT_inj in Ex
  | elimt _ _ _ _ _ _ _ = _ => apply elimt_inj in Ex end;
  decompose [and] Ex; clear Ex; inj_small; subst.
  refine (conj H1 (conj H2 (conj Hl (conj Dc (conj DA (conj (conj DMT (conj DMt _)) (ex_intro _ Wa Dν))))))).
  intros j Hj. rewrite (Eba j Hj), (Ebb j Hj). exact (Db j Hj).
Qed.

Lemma ainv_elimt_glob' {G Γ l1 l2 MT Mt bs l Δ A c l1' l2' MT' Mt' bs' l' Δ' A' ν' T} : boxed_global c ->
  ac_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ A (boxt c)) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' A' ν') T ->
  leqv l1 l1' /\ leqv l2 l2' /\ leqv l l' /\ ac_ctx G Δ Δ' /\ ac_ty G Δ A A' /\
  (ac_ty (recGT G) (recΓT Γ) MT MT' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
   (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt)))) /\
  exists c', ν' = boxt c' /\ tm_leq c c'.
Proof.
  intros Hg D.
  destruct (ainv_elimt_glob Hg D) as (MTa & Mta & bsa & l1a & l2a & MTb & Mtb & bsb & la & Δa & Aa & da & Erba & Ex
                                   & H1 & H2 & Hl & Dc & DA & DMT & DMt & Db & Hd).
  pose proof (f_equal elim_rb Ex) as Erb. cbn [elim_rb] in Erb.
  pose proof (mkrb_inj_br Erba) as Eba. pose proof (mkrb_inj_br Erb) as Ebb.
  destruct (mkrb_inj_MT Erba) as [E1 E2]; destruct (mkrb_inj_MT Erb) as [E3 E4]; subst.
  lazymatch type of Ex with
  | elimT _ _ _ _ _ _ = _ => apply elimT_inj in Ex
  | elimt _ _ _ _ _ _ _ = _ => apply elimt_inj in Ex end;
  decompose [and] Ex; clear Ex; inj_small; subst.
  refine (conj H1 (conj H2 (conj Hl (conj Dc (conj DA (conj (conj DMT (conj DMt _))
            (ex_intro _ da (conj eq_refl Hd)))))))).
  intros j Hj. rewrite (Eba j Hj), (Ebb j Hj). exact (Db j Hj).
Qed.

(** The scrutinee of a recursor over a global variable. *)
Lemma dec_boxT_gvar U d ν' : Dec (exists d', ν' = boxT (tyGvar U d') /\ lsub_leq d d').
Proof.
  destruct ν'; try (right; intros (? & E & _); discriminate E).
  match goal with |- Dec (exists _, boxT ?T = _ /\ _) => destruct T end;
    try (right; intros (? & E & _); discriminate E).
  match goal with |- Dec (exists _, boxT (tyGvar ?a ?b) = _ /\ _) =>
    destruct (dec_nat_eq U a) as [<- | N]; [| right; intros (? & E & _); injection E as E; congruence];
    destruct (lsub_leq_dec d b) as [Hd | N]; [left; exists b; split; [reflexivity | exact Hd] |];
    right; intros (? & E & Hd); injection E as <-; exact (N Hd) end.
Qed.

Lemma dec_boxt_glob c ν' : Dec (exists c', ν' = boxt c' /\ tm_leq c c').
Proof.
  destruct ν'; try (right; intros (? & E & _); discriminate E).
  match goal with |- Dec (exists _, boxt ?b = _ /\ _) =>
    destruct (tm_leq_dec c b) as [Hd | N]; [left; exists b; split; [reflexivity | exact Hd] |];
    right; intros (? & E & Hd); injection E as <-; exact (N Hd) end.
Qed.

(** The motives and branches, the right side's moved to the left's binders. *)
Lemma Dc_rec_core {G Γ l1 l2 l1' l2' MT MT0 MT' Mt Mt0 Mt' bs bs0 bs'} :
  Dc_ty (recGT G) (recΓT Γ) MT MT0 -> Dc_ty (recGt G) (recΓt Γ) Mt Mt0 ->
  (forall j, j < nbr -> Dc_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs0 j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  [ G ; Γ ⊢[ lM ] ] -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] -> [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] -> [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                         bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ]) ->
  Dec (ac_ty (recGT G) (recΓT Γ) MT MT' /\ ac_ty (recGt G) (recΓt Γ) Mt Mt' /\
       (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                              (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt)))).
Proof.
  intros IHT IHt IHb HΓ E1 E2 HMT HMT' HMt HMt' Hbc Hbc' Hbs Hbs'.
  pose proof (wft_lconv _ _ _ _ _ _ HMT' (lequiv_ush 1 E1)) as HMT1.
  pose proof (wft_lconv _ _ _ _ _ _ HMt' (lequiv_ush 1 E2)) as HMt1.
  destruct (IHT MT' lM _ _ compt_M HMT HMT1) as [DMT | N]; [| right; tauto].
  destruct (IHt Mt' lM _ _ compt_M HMt HMt1) as [DMt | N]; [| right; tauto].
  pose proof (ac_ty_sound compt_M DMT HMT HMT1) as EMT.
  pose proof (ac_ty_sound compt_M DMt HMt HMt1) as EMt.
  assert (Hd : Dec (forall j, j < nbr -> j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                                                  (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt)))).
  { apply dec_forall_lt. intros j. destruct (Nat.lt_ge_cases j nbr) as [Hj | Hj]; [| left; intros Hj'; lia].
    pose proof (branch_conv j Hj EMT EMt E1 E2 HΓ (Hbc j Hj) (Hbc' j Hj) (Hbs' j Hj)) as Hb1.
    destruct (IHb j Hj (bs' j) lM _ compt_M (Hbs j Hj) Hb1) as [Y | N];
      [left; intros _; exact Y | right; intros Z; exact (N (Z Hj))]. }
  destruct Hd as [Y | N]; [left; split; [exact DMT | split; [exact DMt | intros j Hj; exact (Y j Hj Hj)]] |].
  right; intros (_ & _ & Z). exact (N (fun j Hj _ => Z j Hj)).
Qed.

Lemma Dc_actmne_elimT {G Γ l1 l2 l1b l2b MT MT0 Mt Mt0 bs bs0 l lb Δ Δ0 ν ν0 W} :
  Dc_ctx G Δ Δ0 -> Dc_ty (recGT G) (recΓT Γ) MT MT0 -> Dc_ty (recGt G) (recΓt Γ) Mt Mt0 ->
  (forall j, j < nbr -> Dc_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs0 j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1b l2b (mkrb MT0 Mt0 bs0) lb Δ0 ν0)
    (motT (wrapMT MT) l Δ ν).
Proof.
  intros IHc IHT IHt IHb Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (proj1 (ac_tmnee_whne Dν0)) as Hn.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (elimT ?a ?b ?c ?d ?e ?f) _) =>
    rename a into l3, b into l4, c into rb', d into l', e into Δ', f into ν' end.
  destruct (inv_elimT Hi Hx) as (MTa & Mta & bsa & (Erb & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs & Hν)
                                 & _ & _).
  destruct (mkrb_inj_MT Erb) as [<- <-]. pose proof (mkrb_inj_br Erb) as Eb.
  destruct (inv_elimT Hi Hx') as (MT' & Mt' & bs' & (-> & _ & _ & W3 & W4 & Wl' & HΔ' & HMT' & HMt' & Hbc' & Hbs'
                                                     & Hν') & _ & _).
  assert (Hbs0 : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                                       bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
    by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj)).
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  destruct (IHν ν' lM _ _ _ _ compt_M Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_elimT' Hn D) as (_ & _ & _ & _ & _ & W5 & Dν2);
       rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l1 l3) as [H13 | N]; [| right; intros D; destruct (ainv_elimT' Hn D) as (Z & _); exact (N Z)].
  destruct (leqv_dec l2 l4) as [H24 | N]; [| right; intros D; destruct (ainv_elimT' Hn D) as (_ & Z & _); exact (N Z)].
  destruct (leqv_dec l l') as [Hl | N]; [| right; intros D; destruct (ainv_elimT' Hn D) as (_ & _ & Z & _); exact (N Z)].
  destruct (IHc Δ' HΔ HΔ') as [Dc | N];
    [| right; intros D; destruct (ainv_elimT' Hn D) as (_ & _ & _ & Z & _); exact (N Z)].
  destruct (Dc_rec_core IHT IHt IHb HΓ (leqv_lequiv _ _ _ W1 W3 H13) (leqv_lequiv _ _ _ W2 W4 H24)
              HMT HMT' HMt HMt' Hbc Hbc' Hbs0 Hbs') as [(DMT & DMt & Db) | N];
    [left; eapply actmne_elimT; eassumption |].
  right; intros D; destruct (ainv_elimT' Hn D) as (_ & _ & _ & _ & Z & _); exact (N Z).
Qed.

Lemma Dc_actmne_elimT_gvar {G Γ l1 l2 l1b l2b MT MT0 Mt Mt0 bs bs0 l lb Δ Δ0 U d d0} :
  Dc_ctx G Δ Δ0 -> Dc_ty (recGT G) (recΓT Γ) MT MT0 -> Dc_ty (recGt G) (recΓt Γ) Mt Mt0 ->
  (forall j, j < nbr -> Dc_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs0 j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  Dc_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d)))
    (elimT l1b l2b (mkrb MT0 Mt0 bs0) lb Δ0 (boxT (tyGvar U d0)))
    (motT (wrapMT MT) l Δ (boxT (tyGvar U d))).
Proof.
  intros IHc IHT IHt IHb x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (elimT ?a ?b ?c ?d ?e ?f) _) =>
    rename a into l3, b into l4, c into rb', d into l', e into Δ', f into ν' end.
  destruct (inv_elimT Hi Hx) as (MTa & Mta & bsa & (Erb & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs & Hν)
                                 & _ & _).
  destruct (mkrb_inj_MT Erb) as [<- <-]. pose proof (mkrb_inj_br Erb) as Eb.
  destruct (inv_elimT Hi Hx') as (MT' & Mt' & bs' & (-> & _ & _ & W3 & W4 & Wl' & HΔ' & HMT' & HMt' & Hbc' & Hbs'
                                                     & Hν') & _ & _).
  assert (Hbs0 : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                                       bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
    by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj)).
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  destruct (dec_boxT_gvar U d ν') as [(d' & -> & Hd) | N];
    [| right; intros D; destruct (ainv_elimT_gvar' D) as (_ & _ & _ & _ & _ & Z); exact (N Z)].
  destruct (leqv_dec l1 l3) as [H13 | N]; [| right; intros D; destruct (ainv_elimT_gvar' D) as (Z & _); exact (N Z)].
  destruct (leqv_dec l2 l4) as [H24 | N];
    [| right; intros D; destruct (ainv_elimT_gvar' D) as (_ & Z & _); exact (N Z)].
  destruct (leqv_dec l l') as [Hl | N];
    [| right; intros D; destruct (ainv_elimT_gvar' D) as (_ & _ & Z & _); exact (N Z)].
  destruct (IHc Δ' HΔ HΔ') as [Dc | N];
    [| right; intros D; destruct (ainv_elimT_gvar' D) as (_ & _ & _ & Z & _); exact (N Z)].
  destruct (Dc_rec_core IHT IHt IHb HΓ (leqv_lequiv _ _ _ W1 W3 H13) (leqv_lequiv _ _ _ W2 W4 H24)
              HMT HMT' HMt HMt' Hbc Hbc' Hbs0 Hbs') as [(DMT & DMt & Db) | N];
    [left; eapply actmne_elimT_gvar; eassumption |].
  right; intros D; destruct (ainv_elimT_gvar' D) as (_ & _ & _ & _ & Z & _); exact (N Z).
Qed.

Lemma Dc_actmne_elimt {G Γ l1 l2 l1b l2b MT MT0 Mt Mt0 bs bs0 l lb Δ Δ0 A A0 ν ν0 W} :
  Dc_ctx G Δ Δ0 -> Dc_ty G Δ A A0 -> Dc_ty (recGT G) (recΓT Γ) MT MT0 -> Dc_ty (recGt G) (recΓt Γ) Mt Mt0 ->
  (forall j, j < nbr -> Dc_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs0 j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ A ν) (elimt l1b l2b (mkrb MT0 Mt0 bs0) lb Δ0 A0 ν0)
    (mott (wrapMt Mt) l Δ A ν).
Proof.
  intros IHc IHA IHT IHt IHb Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (proj1 (ac_tmnee_whne Dν0)) as Hn.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (elimt ?a ?b ?c ?d ?e ?f ?g) _) =>
    rename a into l3, b into l4, c into rb', d into l', e into Δ', f into A', g into ν' end.
  destruct (inv_elimt Hi Hx) as (MTa & Mta & bsa & (Erb & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs
                                                    & HA & Hν) & _ & _).
  destruct (mkrb_inj_MT Erb) as [<- <-]. pose proof (mkrb_inj_br Erb) as Eb.
  destruct (inv_elimt Hi Hx') as (MT' & Mt' & bs' & (-> & _ & _ & W3 & W4 & Wl' & HΔ' & HMT' & HMt' & Hbc' & Hbs'
                                                     & HA' & Hν') & _ & _).
  assert (Hbs0 : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                                       bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
    by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj)).
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  destruct (IHν ν' lM _ _ _ _ compt_M Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_elimt' Hn D) as (_ & _ & _ & _ & _ & _ & W5 & Dν2);
       rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l1 l3) as [H13 | N]; [| right; intros D; destruct (ainv_elimt' Hn D) as (Z & _); exact (N Z)].
  destruct (leqv_dec l2 l4) as [H24 | N]; [| right; intros D; destruct (ainv_elimt' Hn D) as (_ & Z & _); exact (N Z)].
  destruct (leqv_dec l l') as [Hl | N]; [| right; intros D; destruct (ainv_elimt' Hn D) as (_ & _ & Z & _); exact (N Z)].
  destruct (IHc Δ' HΔ HΔ') as [Dc | N];
    [| right; intros D; destruct (ainv_elimt' Hn D) as (_ & _ & _ & Z & _); exact (N Z)].
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  destruct (IHA A' lD _ _ compt_D HA (mvD (eqctx_sym_D Ec) HA')) as [DA | N];
    [| right; intros D; destruct (ainv_elimt' Hn D) as (_ & _ & _ & _ & Z & _); exact (N Z)].
  destruct (Dc_rec_core IHT IHt IHb HΓ (leqv_lequiv _ _ _ W1 W3 H13) (leqv_lequiv _ _ _ W2 W4 H24)
              HMT HMT' HMt HMt' Hbc Hbc' Hbs0 Hbs') as [(DMT & DMt & Db) | N];
    [left; eapply actmne_elimt; eassumption |].
  right; intros D; destruct (ainv_elimt' Hn D) as (_ & _ & _ & _ & _ & Z & _); exact (N Z).
Qed.

Lemma Dc_actmne_elimt_glob {G Γ l1 l2 l1b l2b MT MT0 Mt Mt0 bs bs0 l lb Δ Δ0 A A0 c c0} : boxed_global c ->
  Dc_ctx G Δ Δ0 -> Dc_ty G Δ A A0 -> Dc_ty (recGT G) (recΓT Γ) MT MT0 -> Dc_ty (recGt G) (recΓt Γ) Mt Mt0 ->
  (forall j, j < nbr -> Dc_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                          (bs j) (bs0 j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  Dc_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ A (boxt c))
    (elimt l1b l2b (mkrb MT0 Mt0 bs0) lb Δ0 A0 (boxt c0))
    (mott (wrapMt Mt) l Δ A (boxt c)).
Proof.
  intros Hg IHc IHA IHT IHt IHb x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (elimt ?a ?b ?c ?d ?e ?f ?g) _) =>
    rename a into l3, b into l4, c into rb', d into l', e into Δ', f into A', g into ν' end.
  destruct (inv_elimt Hi Hx) as (MTa & Mta & bsa & (Erb & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs
                                                    & HA & Hν) & _ & _).
  destruct (mkrb_inj_MT Erb) as [<- <-]. pose proof (mkrb_inj_br Erb) as Eb.
  destruct (inv_elimt Hi Hx') as (MT' & Mt' & bs' & (-> & _ & _ & W3 & W4 & Wl' & HΔ' & HMT' & HMt' & Hbc' & Hbs'
                                                     & HA' & Hν') & _ & _).
  assert (Hbs0 : forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                                       bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
    by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj)).
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  destruct (dec_boxt_glob c ν') as [(c' & -> & Hd) | N];
    [| right; intros D; destruct (ainv_elimt_glob' Hg D) as (_ & _ & _ & _ & _ & _ & Z); exact (N Z)].
  destruct (leqv_dec l1 l3) as [H13 | N];
    [| right; intros D; destruct (ainv_elimt_glob' Hg D) as (Z & _); exact (N Z)].
  destruct (leqv_dec l2 l4) as [H24 | N];
    [| right; intros D; destruct (ainv_elimt_glob' Hg D) as (_ & Z & _); exact (N Z)].
  destruct (leqv_dec l l') as [Hl | N];
    [| right; intros D; destruct (ainv_elimt_glob' Hg D) as (_ & _ & Z & _); exact (N Z)].
  destruct (IHc Δ' HΔ HΔ') as [Dc | N];
    [| right; intros D; destruct (ainv_elimt_glob' Hg D) as (_ & _ & _ & Z & _); exact (N Z)].
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  destruct (IHA A' lD _ _ compt_D HA (mvD (eqctx_sym_D Ec) HA')) as [DA | N];
    [| right; intros D; destruct (ainv_elimt_glob' Hg D) as (_ & _ & _ & _ & Z & _); exact (N Z)].
  destruct (Dc_rec_core IHT IHt IHb HΓ (leqv_lequiv _ _ _ W1 W3 H13) (leqv_lequiv _ _ _ W2 W4 H24)
              HMT HMT' HMt HMt' Hbc Hbc' Hbs0 Hbs') as [(DMT & DMt & Db) | N];
    [left; eapply actmne_elimt_glob; eassumption |].
  right; intros D; destruct (ainv_elimt_glob' Hg D) as (_ & _ & _ & _ & _ & Z & _); exact (N Z).
Qed.

(** ** Decidability *)

(** ** Dependent pairs (M8) *)

Lemma Dc_actnf_sig {G Γ l1 l2 l3 l4 A A0 B B0} :
  Dc_ty G Γ A A0 -> Dc_ty G (Γ ,, A @ l1) B B0 -> Dc_tynf G Γ (tySig l1 l2 A B) (tySig l3 l4 A0 B0).
Proof.
  intros IHA IHB X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tySig ?a ?b ?c ?d)) =>
    rename a into l5, b into l6, c into A', d into B' end.
  destruct (inv_ty_sig HX) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_sig HX') as ((_ & W5 & W6 & HA' & HB') & _).
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E15)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E15) HΓA HB') as HB1.
  destruct (IHB B' i _ _ Hc HB HB1) as [DB | N]; [left; apply actnf_sig; assumption | refute].
Qed.

Lemma Dc_actmnf_code_sig {G Γ l l1 l2 l3 l4 s s0 t t0} :
  Dc_tm G Γ s s0 (tyU l1) -> Dc_tm G (Γ ,, tyEl l1 s @ l1) t t0 (tyU l2) ->
  Dc_tmnf G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s0 t0) (tyU l).
Proof.
  intros IHs IHt x i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSig ?a ?b ?c ?d) _) =>
    rename a into l5, b into l6, c into s', d into t' end.
  destruct (code_sig_prem Hc Hx) as (Hv & W1 & W2 & Hs & Ht).
  destruct (code_sig_prem Hc Hx') as (_ & W5 & W6 & Hs' & Ht').
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
  destruct (IHt t' i _ Hc Ht Ht1) as [Dt | N]; [left; apply actmnf_code_sig; assumption | refute].
Qed.
Lemma Dc_actmnf_code_W {G Γ l l1 l2 l3 l4 s s0 t t0} :
  Dc_tm G Γ s s0 (tyU l1) -> Dc_tm G (Γ ,, tyEl l1 s @ l1) t t0 (tyU l2) ->
  Dc_tmnf G Γ (tmW l1 l2 s t) (tmW l3 l4 s0 t0) (tyU l).
Proof.
  intros IHs IHt x i k Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmW ?a ?b ?c ?d) _) =>
    rename a into l5, b into l6, c into s', d into t' end.
  destruct (code_W_prem Hc Hx) as (Hv & W1 & W2 & Hs & Ht).
  destruct (code_W_prem Hc Hx') as (_ & W5 & W6 & Hs' & Ht').
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
  destruct (IHt t' i _ Hc Ht Ht1) as [Dt | N]; [left; apply actmnf_code_W; assumption | refute].
Qed.

Lemma Dc_actmnf_sig_eta {G Γ l l' A B w w0} :
  Dc_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w0) A ->
  Dc_tm G Γ (tmSnd l l' A B w) (tmSnd l l' A B w0) B[lsingle (tmFst l l' A B w)] ->
  Dc_tmnf G Γ w w0 (tySig l l' A B).
Proof.
  intros IH1 IH2 x i k Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_sig (wf_tm_ty Hi Hw)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hx) as Hx1.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1) as Hf.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hx1) as Hfx.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hw1) as Hs.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hx1) as Hsx.
  destruct (IH1 _ i l Hc Hf Hfx) as [D1 | N]; [| right; intros D; exact (N (proj1 (ainv_sig_eta D)))].
  pose proof (ac_tm_sound Hc D1 Hf Hfx) as E1.
  pose proof (sig_fam_eq Hi HB (eqty_refl _ _ _ _ _ HB) (eqtm_sym _ _ _ _ _ _ _ E1) Hfx Hf) as EBs.
  assert (Hsx1 : [ G ; Γ ⊢[ i ] tmSnd l l' A B x : B[lsingle (tmFst l l' A B w)] @ l' ])
    by (eapply wf_conv; [exact Hsx | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EBs)]).
  destruct (IH2 _ i l' Hc Hs Hsx1) as [D2 | N];
    [left; apply actmnf_sig_eta; assumption | right; intros D; exact (N (proj2 (ainv_sig_eta D)))].
Qed.

(** The unit type (M8c). *)
Lemma Dc_actnf_unit {G Γ l l0} : Dc_tynf G Γ (tyUnit l) (tyUnit l0).
Proof.
  intros X *; destruct X; try solve [refute_con | refute]. intros.
  match goal with |- Dec (ac_tynf _ _ _ (tyUnit ?l')) =>
    destruct (leqv_dec l l') as [Hl | N]; [left; exact (actnf_unit _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actmnf_code_unit {G Γ l k k0} : Dc_tmnf G Γ (tmUnit k) (tmUnit k0) (tyU l).
Proof.
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmUnit ?a) _) =>
    destruct (leqv_dec k a) as [Hl | N]; [left; exact (actmnf_code_unit _ _ _ _ _ Hl) | refute] end.
Qed.
(** The codes of [Empty] and [+] (M12c). *)
Lemma Dc_actmnf_code_empty {G Γ l k k0} : Dc_tmnf G Γ (tmEmpty k) (tmEmpty k0) (tyU l).
Proof.
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmEmpty ?a) _) =>
    destruct (leqv_dec k a) as [Hl | N]; [left; exact (actmnf_code_empty _ _ _ _ _ Hl) | refute] end.
Qed.
Lemma Dc_actmnf_code_sum {G Γ l l1 l2 l3 l4 s s0 t t0} :
  Dc_tm G Γ s s0 (tyU l1) -> Dc_tm G Γ t t0 (tyU l2) -> Dc_tmnf G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s0 t0) (tyU l).
Proof.
  intros IHs IHt x i m Hc Hx Hx'.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSum ?a ?b ?c ?d) _) =>
    rename a into l5, b into l6, c into s', d into t' end.
  destruct (code_sum_prem Hc Hx) as (W1 & W2 & Hs & Ht). destruct (code_sum_prem Hc Hx') as (W5 & W6 & Hs' & Ht').
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15. pose proof (leqv_lequiv _ _ _ W2 W6 H26) as E26.
  destruct (IHs s' i _ Hc Hs (code_U_conv Hc E15 Hs')) as [Ds | N]; [| refute].
  destruct (IHt t' i _ Hc Ht (code_U_conv Hc E26 Ht')) as [Dt | N]; [left; apply actmnf_code_sum; assumption | refute].
Qed.

(** The codes of [Vec] and [Fin] (M14b). *)
Lemma Dc_actmnf_code_vec {G Γ l k k0 s s0 n n0} :
  Dc_tm G Γ s s0 (tyU k) -> Dc_tm G Γ n n0 tyNat -> Dc_tmnf G Γ (tmVec k s n) (tmVec k0 s0 n0) (tyU l).
Proof.
  intros IHs IHn x i m Hc Hx Hx'.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmVec ?a ?b ?c) _) => rename a into k', b into s', c into n' end.
  destruct (code_vec_prem Hc Hx) as (W1 & Hs & Hn). destruct (code_vec_prem Hc Hx') as (W5 & Hs' & Hn').
  destruct (leqv_dec k k') as [H15 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15.
  destruct (IHs s' i _ Hc Hs (code_U_conv Hc E15 Hs')) as [Ds | N]; [| refute].
  destruct (IHn n' i _ Hc Hn Hn') as [Dn | N]; [left; apply actmnf_code_vec; assumption | refute].
Qed.
Lemma Dc_actmnf_code_fin {G Γ l n n0} : Dc_tm G Γ n n0 tyNat -> Dc_tmnf G Γ (tmFin n) (tmFin n0) (tyU l).
Proof.
  intros IHn x i m Hc Hx Hx'.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmFin ?a) _) => rename a into n' end.
  destruct (IHn n' i _ Hc (code_fin_prem Hc Hx) (code_fin_prem Hc Hx')) as [Dn | N];
    [left; apply actmnf_code_fin; exact Dn | refute].
Qed.

Lemma Dc_actmnf_code_sempty {G Γ l k k0} : Dc_tmnf G Γ (tmSEmpty k) (tmSEmpty k0) (tyU l).
Proof.
  intros x i k1 Hc Hx Hx'; destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSEmpty ?a) _) =>
    destruct (leqv_dec k a) as [Hl | N]; [left; exact (actmnf_code_sempty _ _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actmnf_unit_eta {G Γ l w w0} : Dc_tmnf G Γ w w0 (tyUnit l).
Proof. intros x i k Hc Hw Hx. left; apply actmnf_unit_eta. Qed.

(** Strict equality (M10a). *)
Lemma Dc_actnf_seq {G Γ l l0 A A0 a a0 b b0} :
  Dc_ty G Γ A A0 -> Dc_tm G Γ a a0 A -> Dc_tm G Γ b b0 A -> Dc_tynf G Γ (tySEq l A a b) (tySEq l0 A0 a0 b0).
Proof.
  intros IHA IHa IHb X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tySEq ?a ?b ?c ?d)) =>
    rename a into l5, b into A', c into a', d into b' end.
  destruct (inv_ty_seq HX) as ((_ & W & HA & Ha & Hb) & _).
  destruct (inv_ty_seq HX') as ((_ & W5 & HA' & Ha' & Hb') & _).
  destruct (leqv_dec l l5) as [H15 | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W W5 H15) as E15.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l5 ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E15) | rewrite Hi; exact EA]. }
  destruct (IHa a' i l Hc Ha (F _ Ha')) as [Da | N]; [| refute].
  destruct (IHb b' i l Hc Hb (F _ Hb')) as [Db | N]; [left; apply actnf_seq; assumption | refute].
Qed.

Lemma Dc_actnf_sempty {G Γ l l0} : Dc_tynf G Γ (tySEmpty l) (tySEmpty l0).
Proof.
  intros X *; destruct X; try solve [refute_con | refute]. intros.
  match goal with |- Dec (ac_tynf _ _ _ (tySEmpty ?l')) =>
    destruct (leqv_dec l l') as [Hl | N]; [left; exact (actnf_sempty _ _ _ _ Hl) | refute] end.
Qed.

(** The empty type (M12a). *)
Lemma Dc_actnf_empty {G Γ l l0} : Dc_tynf G Γ (tyEmpty l) (tyEmpty l0).
Proof.
  intros X *; destruct X; try solve [refute_con | refute]. intros.
  match goal with |- Dec (ac_tynf _ _ _ (tyEmpty ?l')) =>
    destruct (leqv_dec l l') as [Hl | N]; [left; exact (actnf_empty _ _ _ _ Hl) | refute] end.
Qed.

Lemma Dc_actmne_elimEmpty {G Γ l1 l2 l3 l4 M M0 ν ν0 W} :
  Dc_ty G (Γ ,, tyEmpty l2 @ l2) M M0 -> ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (elimEmpty l1 l2 M ν) (elimEmpty l3 l4 M0 ν0) M[lsingle ν].
Proof.
  intros IHM Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (elimEmpty ?p1 ?p2 ?p3 ?p4) _) =>
    rename p1 into l5, p2 into l6, p3 into M', p4 into ν' end.
  destruct (inv_elimEmpty Hi Hx) as ((_ & W1 & W2 & HM & Hν) & _ & _).
  destruct (inv_elimEmpty Hi Hx') as ((_ & W5 & W6 & HM' & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_elimEmpty D) as (l7 & l8 & M2 & ν2 & W3 & E & _ & _ & _ & Dν2);
       injection E as <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute].
  destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15. pose proof (leqv_lequiv _ _ _ W2 W6 H26) as E26.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  (* the other motive, in this context *)
  assert (HE : [ G ; Γ ⊢[ i ] tyEmpty l6 ≅ tyEmpty l2 @ l6 ])
    by (apply eqty_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact (lequiv_sym _ _ _ E26)]).
  assert (HΓE : [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_empty; [now apply compt_notV | rewrite Hi; exact HΓ | exact W2] | exact W2]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi HE (lequiv_sym _ _ _ E26) HΓE HM') E15) as HM'1.
  destruct (IHM M' i _ _ Hc HM HM'1) as [DM | N]; [left; eapply actmne_elimEmpty; eassumption | refute].
Qed.

Lemma Dc_actmnf_seq_irr {G Γ l A a b w w0} : Dc_tmnf G Γ w w0 (tySEq l A a b).
Proof. intros x i k Hc Hw Hx. left; apply actmnf_seq_irr. Qed.
Lemma Dc_actmnf_sempty_irr {G Γ l w w0} : Dc_tmnf G Γ w w0 (tySEmpty l).
Proof. intros x i k Hc Hw Hx. left; apply actmnf_sempty_irr. Qed.

(** Neutrality is decidable. *)
Fixpoint is_whne (t : tm) : bool :=
  match t with
  | var _ | gvar _ _ => true
  | natrec _ _ _ _ t | app t _ _ _ _ _ | letboxT _ _ _ _ _ t | letboxt _ _ _ _ _ _ t
  | uapp t _ | capp t _ | tapp t _ | tmFst _ _ _ _ t | tmSnd _ _ _ _ t | elimSEmpty _ _ _ t | elimEmpty _ _ _ t
  | tmJ _ _ _ _ _ _ _ t | tmCase _ _ _ _ _ _ _ _ t
  | tmElimW _ _ _ _ _ _ _ t => is_whne t
  | elimT _ _ _ _ _ t => match t with boxT (tyGvar _ _) => true | _ => is_whne t end
  | elimt _ _ _ _ _ _ t => match t with boxt (gvar _ _) | boxt (gdef _ _ _) => true | _ => is_whne t end
  | _ => false
  end.

Lemma is_whne_sound t : is_whne t = true -> whne t.
Proof.
  induction t; cbn; intros H; try discriminate; try solve [constructor; auto].
  all: match goal with
       | |- whne (elimT _ _ _ _ _ ?s) =>
           destruct s; cbn in H; try solve [constructor; auto];
           match goal with |- whne (elimT _ _ _ _ _ (boxT ?T)) => destruct T; try discriminate;
                             apply whne_elimT_gvar end
       | |- whne (elimt _ _ _ _ _ _ ?s) =>
           destruct s; cbn in H; try solve [constructor; auto];
           match goal with |- whne (elimt _ _ _ _ _ _ (boxt ?c)) => destruct c; try discriminate;
                             first [apply whne_elimt_gvar | apply whne_elimt_gdef] end
       end.
Qed.

Lemma is_whne_complete t : whne t -> is_whne t = true.
Proof. induction 1; cbn; auto; destruct t; auto; inversion H. Qed.

Lemma whne_dec t : Dec (whne t).
Proof.
  destruct (is_whne t) eqn:E; [left; exact (is_whne_sound _ E) |].
  right; intros H; rewrite (is_whne_complete _ H) in E; discriminate.
Qed.

(** The identity type (M11a). *)
Lemma Dc_actnf_id {G Γ l l0 A A0 a a0 b b0} :
  Dc_ty G Γ A A0 -> Dc_tm G Γ a a0 A -> Dc_tm G Γ b b0 A -> Dc_tynf G Γ (tyId l A a b) (tyId l0 A0 a0 b0).
Proof.
  intros IHA IHa IHb X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyId ?a ?b ?c ?d)) =>
    rename a into l5, b into A', c into a', d into b' end.
  destruct (inv_ty_id HX) as ((_ & W & HA & Ha & Hb) & _).
  destruct (inv_ty_id HX') as ((_ & W5 & HA' & Ha' & Hb') & _).
  destruct (leqv_dec l l5) as [H15 | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W W5 H15) as E15.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l5 ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E15) | rewrite Hi; exact EA]. }
  destruct (IHa a' i l Hc Ha (F _ Ha')) as [Da | N]; [| refute].
  destruct (IHb b' i l Hc Hb (F _ Hb')) as [Db | N]; [left; apply actnf_id; assumption | refute].
Qed.

Lemma Dc_actmnf_code_id {G Γ l k k0 s s0 t t0 u u0} :
  Dc_tm G Γ s s0 (tyU k) -> Dc_tm G Γ t t0 (tyEl k s) -> Dc_tm G Γ u u0 (tyEl k s) ->
  Dc_tmnf G Γ (tmId k s t u) (tmId k0 s0 t0 u0) (tyU l).
Proof.
  intros IHs IHt IHu x i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmId ?a ?b ?c ?d) _) =>
    rename a into k', b into s', c into t', d into u' end.
  destruct (code_id_prem Hc Hx) as (W & Hs & Ht & Hu). destruct (code_id_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  destruct (leqv_dec k k') as [Hk0 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  destruct (IHs s' i _ Hc Hs Hs1) as [Ds | N]; [| refute].
  destruct (code_El_conv Hc E (ac_tm_sound Hc Ds Hs Hs1)) as (F & _).
  destruct (IHt t' i _ Hc Ht (F _ Ht')) as [Dt | N]; [| refute].
  destruct (IHu u' i _ Hc Hu (F _ Hu')) as [Du | N]; [left; apply actmnf_code_id; assumption | refute].
Qed.
Lemma Dc_actmnf_code_seq {G Γ l k k0 s s0 t t0 u u0} :
  Dc_tm G Γ s s0 (tyU k) -> Dc_tm G Γ t t0 (tyEl k s) -> Dc_tm G Γ u u0 (tyEl k s) ->
  Dc_tmnf G Γ (tmSEq k s t u) (tmSEq k0 s0 t0 u0) (tyU l).
Proof.
  intros IHs IHt IHu x i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSEq ?a ?b ?c ?d) _) =>
    rename a into k', b into s', c into t', d into u' end.
  destruct (code_seq_prem Hc Hx) as (W & Hs & Ht & Hu). destruct (code_seq_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  destruct (leqv_dec k k') as [Hk0 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  destruct (IHs s' i _ Hc Hs Hs1) as [Ds | N]; [| refute].
  destruct (code_El_conv Hc E (ac_tm_sound Hc Ds Hs Hs1)) as (F & _).
  destruct (IHt t' i _ Hc Ht (F _ Ht')) as [Dt | N]; [| refute].
  destruct (IHu u' i _ Hc Hu (F _ Hu')) as [Du | N]; [left; apply actmnf_code_seq; assumption | refute].
Qed.

Lemma Dc_actmnf_refl {G Γ l A a b k k0 C C0 c c0} :
  Dc_tmnf G Γ (tmRefl k C c) (tmRefl k0 C0 c0) (tyId l A a b).
Proof. intros x i m Hc Hw Hx. destruct x; first [left; apply actmnf_refl | refute]. Qed.

Lemma Dc_actmne_elimSEmpty {G Γ l1 l2 l3 l4 M M0 ν ν0} :
  Dc_ty G Γ M M0 -> whne ν -> Dc_ne G Γ (elimSEmpty l1 l2 M ν) (elimSEmpty l3 l4 M0 ν0) M.
Proof.
  intros IHM Hn x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (elimSEmpty ?a ?b ?c ?d) _) =>
    rename a into l5, b into l6, c into M', d into ν' end.
  destruct (inv_elimSEmpty Hi Hx) as ((_ & _ & _ & HM & _) & _ & _).
  destruct (inv_elimSEmpty Hi Hx') as ((_ & _ & _ & HM' & _) & _ & _).
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  destruct (IHM M' i _ _ Hc HM HM') as [DM | N]; [| refute].
  destruct (whne_dec ν') as [Hn' | N]; [left; apply actmne_elimSEmpty; assumption | refute].
Qed.

Lemma Dc_actmne_J {G Γ l1 l2 l3 l4 A A0 a a0 M M0 c c0 u u0 ν ν0 W} :
  Dc_ty G Γ A A0 -> Dc_tm G Γ a a0 A ->
  Dc_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M0 ->
  Dc_tm G Γ c c0 M[lsingle2 a (tmRefl l1 A a)] -> Dc_tm G Γ u u0 A ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmJ l1 l2 A a M c u ν) (tmJ l3 l4 A0 a0 M0 c0 u0 ν0) M[lsingle2 u ν].
Proof.
  intros IHA IHa IHM IHc IHu Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmJ ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8) _) =>
    rename p1 into l5, p2 into l6, p3 into A', p4 into a', p5 into M', p6 into c', p7 into u', p8 into ν' end.
  destruct (inv_J Hi Hx) as ((_ & W1 & W2 & HA & Ha & HI & HM & Hcc & Hu & He) & _ & _).
  destruct (inv_J Hi Hx') as ((_ & W5 & W6 & HA' & Ha' & HI' & HM' & Hc' & Hu' & He') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc He He') as [Dν | N];
    [| right; intros D; destruct (ainv_J D) as (l7 & l8 & A2 & a2 & M2 & c2 & u2 & ν2 & W3 & E & _ & _ & _ & _ & _
                                                & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute].
  destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15. pose proof (leqv_lequiv _ _ _ W2 W6 H26) as E26.
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  assert (F : forall y, [ G ; Γ ⊢[ i ] y : A' @ l5 ] -> [ G ; Γ ⊢[ i ] y : A @ l1 ]).
  { intros y Hy. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hy E15) | rewrite Hi; exact EA]. }
  pose proof (F _ Ha') as Ha'1.
  destruct (IHa a' i l1 Hc Ha Ha'1) as [Da | N]; [| refute].
  pose proof (ac_tm_sound Hc Da Ha Ha'1) as Ea.
  (* the other motive, in this context *)
  pose proof (J_ctx_conv Hi Hc E15 HA HA' EA Ea) as Hid.
  pose proof (wf_ty_subst Hi HM' Hid) as HM'1. rewrite nf_id_ty in HM'1 by exact (wf_ty_nf HM').
  apply (fun H => wft_lconv _ _ _ _ _ _ H E26) in HM'1.
  destruct (IHM M' i _ _ Hc HM HM'1) as [DM | N]; [| refute].
  pose proof (ac_ty_sound Hc DM HM HM'1) as EM.
  (* the other base case, at this instance *)
  assert (Hr : [ G ; Γ ⊢[ i ] tmRefl l1 A a : tyId l1 A a a @ l1 ]) by (apply wf_idrefl; auto).
  pose proof (pre_idrefl_r Hi Hv E15 HA EA (eqty_wf_r Hi EA) Ea Ha'1) as Hr'.
  assert (Hrr : [ G ; Γ ⊢[ i ] tmRefl l1 A a ≅ tmRefl l5 A' a' : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; auto).
  pose proof (lsub_eq_J Hi Hv W1 HA Ha Ha Ha'1 Ea Hr Hr' Hrr) as Hs.
  assert (HMs : [ G ; Γ ⊢[ i ] M[lsingle2 a (tmRefl l1 A a)] ≅ M'[lsingle2 a' (tmRefl l5 A' a')] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi EM (lsub_eq_l Hs)) | exact (wf_ty_func Hi HM'1 Hs)]. }
  assert (Hc'1 : [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc' E26) | rewrite Hi; exact HMs]. }
  destruct (IHc c' i l2 Hc Hcc Hc'1) as [Dc | N]; [| refute].
  destruct (IHu u' i l1 Hc Hu (F _ Hu')) as [Du | N]; [left; eapply actmne_J; eassumption | refute].
Qed.

(** Well-founded trees (M13a). *)
Lemma Dc_actnf_W {G Γ l1 l2 l3 l4 A A0 B B0} :
  Dc_ty G Γ A A0 -> Dc_ty G (Γ ,, A @ l1) B B0 -> Dc_tynf G Γ (tyW l1 l2 A B) (tyW l3 l4 A0 B0).
Proof.
  intros IHA IHB X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyW ?a ?b ?c ?d)) =>
    rename a into l5, b into l6, c into A', d into B' end.
  destruct (inv_ty_W HX) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_W HX') as ((_ & W5 & W6 & HA' & HB') & _).
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E15)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E15) HΓA HB') as HB1.
  destruct (IHB B' i _ _ Hc HB HB1) as [DB | N]; [left; apply actnf_W; assumption | refute].
Qed.

Lemma Dc_actmnf_sup {G Γ l l' A B k1 k2 k3 k4 C D C0 D0 a a0 f f0} :
  Dc_tm G Γ a a0 A -> Dc_tm G Γ f f0 (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) ->
  Dc_tmnf G Γ (tmSup k1 k2 C D a f) (tmSup k3 k4 C0 D0 a0 f0) (tyW l l' A B).
Proof.
  intros IHa IHf x i m Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSup _ _ _ _ ?e ?g) _) => rename e into a', g into f' end.
  destruct (sup_parts Hc Hw) as (Wl & Wl' & HA & HB & Ha & Hf).
  destruct (sup_parts Hc Hx) as (_ & _ & _ & _ & Ha' & Hf').
  destruct (IHa a' i l Hc Ha Ha') as [Da | N]; [| refute].
  pose proof (fty_conv Hc Wl Wl' HA HB Ha' Ha (ac_tm_sound Hc Da Ha Ha')) as EF.
  assert (Hf'1 : [ G ; Γ ⊢[ i ] f' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ])
    by (eapply wf_conv; [exact Hf' | rewrite Hi; exact EF]).
  destruct (IHf f' i _ Hc Hf Hf'1) as [Df | N]; [left; apply actmnf_sup; assumption | refute].
Qed.

Lemma Dc_actmne_elimW {G Γ l1 l2 l3 l4 l5 l6 A A0 B B0 M M0 c c0 ν ν0 W} :
  Dc_ty G Γ A A0 -> Dc_ty G (Γ ,, A @ l1) B B0 -> Dc_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M0 ->
  Dc_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
    c c0 (wstepty l1 l2 A B M) ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmElimW l1 l2 l3 A B M c ν) (tmElimW l4 l5 l6 A0 B0 M0 c0 ν0) M[lsingle ν].
Proof.
  intros IHA IHB IHM IHc Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmElimW ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8) _) =>
    rename p1 into l7, p2 into l8, p3 into l9, p4 into A', p5 into B', p6 into M', p7 into c', p8 into ν' end.
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimW Hi Hx') as ((_ & W7 & W8 & W9 & HA' & HB' & HM' & HF' & HI' & Hc0' & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_elimW D) as (l10 & l11 & l12 & A2 & B2 & M2 & c2 & ν2 & W0 & E
                                                    & _ & _ & _ & _ & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l1 l7) as [H17 | N]; [| refute].
  destruct (leqv_dec l2 l8) as [H28 | N]; [| refute].
  destruct (leqv_dec l3 l9) as [H39 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W7 H17) as E17. pose proof (leqv_lequiv _ _ _ W2 W8 H28) as E28.
  pose proof (leqv_lequiv _ _ _ W3 W9 H39) as E39.
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E17)) as EA.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA7 : [ G ; Γ ⊢[ i ] A' ≅ A @ l7 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E17)]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EA7 (lequiv_sym _ _ _ E17) HΓA HB') E28) as HB'A.
  destruct (IHB B' i _ _ Hc HB HB'A) as [DB | N]; [| refute].
  pose proof (ac_ty_sound Hc DB HB HB'A) as EB.
  assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
  assert (HL : lequiv (gL G) (lmax l7 l8) (lmax l1 l2)) by (apply lequiv_max; now apply lequiv_sym).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l7 l8 A' B' ≅ tyW l1 l2 A B @ lmax l7 l8 ]).
  { eapply eqty_lconv; [apply eqty_sym, eqty_W; first [assumption | (apply compt_notV; eassumption)] | exact HL]. }
  pose proof (ext_wf Hi HW WL) as HΓW.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' HL HΓW HM') E39) as HM'3.
  destruct (IHM M' i _ _ Hc HM HM'3) as [DM | N]; [| refute].
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  pose proof (elimW_step_left Hc E17 E28 E39 HA HA' EA HB HB' EB HM HM' EM HF HI Hc0') as Hc0'2.
  destruct (IHc c' i l3 Hc Hc0 Hc0'2) as [Dc | N]; [left; eapply actmne_elimW; eassumption | refute].
Qed.

(** Binary sums (M12b). *)
Lemma Dc_actnf_sum {G Γ l1 l2 l3 l4 A A0 B B0} :
  Dc_ty G Γ A A0 -> Dc_ty G Γ B B0 -> Dc_tynf G Γ (tySum l1 l2 A B) (tySum l3 l4 A0 B0).
Proof.
  intros IHA IHB X i k k' Hc HX HX'.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tySum ?a ?b ?c ?d)) =>
    rename a into l5, b into l6, c into A', d into B' end.
  destruct (inv_ty_sum HX) as ((_ & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_sum HX') as ((_ & W5 & W6 & HA' & HB') & _).
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  destruct (IHB B' i _ _ Hc HB HB') as [DB | N]; [left; apply actnf_sum; assumption | refute].
Qed.

Lemma Dc_actmnf_inl {G Γ l l' A B k1 k2 k3 k4 C D C0 D0 a a0} :
  Dc_tm G Γ a a0 A -> Dc_tmnf G Γ (tmInl k1 k2 C D a) (tmInl k3 k4 C0 D0 a0) (tySum l l' A B).
Proof.
  intros IHa x i m Hc Hw Hx.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmInl _ _ _ _ ?e) _) => rename e into a' end.
  destruct (IHa a' i l Hc (inl_payload Hc Hw) (inl_payload Hc Hx)) as [Da | N];
    [left; apply actmnf_inl; exact Da | refute].
Qed.
Lemma Dc_actmnf_inr {G Γ l l' A B k1 k2 k3 k4 C D C0 D0 b b0} :
  Dc_tm G Γ b b0 B -> Dc_tmnf G Γ (tmInr k1 k2 C D b) (tmInr k3 k4 C0 D0 b0) (tySum l l' A B).
Proof.
  intros IHb x i m Hc Hw Hx.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmInr _ _ _ _ ?e) _) => rename e into b' end.
  destruct (IHb b' i l' Hc (inr_payload Hc Hw) (inr_payload Hc Hx)) as [Db | N];
    [left; apply actmnf_inr; exact Db | refute].
Qed.

Lemma Dc_actmne_case {G Γ l1 l2 l3 l4 l5 l6 A A0 B B0 M M0 c1 c10 c2 c20 ν ν0 W} :
  Dc_ty G Γ A A0 -> Dc_ty G Γ B B0 -> Dc_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M0 ->
  Dc_tm G (Γ ,, A @ l1) c1 c10 M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] -> Dc_tm G (Γ ,, B @ l2) c2 c20 M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) (tmCase l4 l5 l6 A0 B0 M0 c10 c20 ν0) M[lsingle ν].
Proof.
  intros IHA IHB IHM IHc1 IHc2 Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmCase ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8 ?p9) _) =>
    rename p1 into l7, p2 into l8, p3 into l9, p4 into A', p5 into B', p6 into M', p7 into c1', p8 into c2',
      p9 into ν' end.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Hν) & _ & _).
  destruct (inv_case Hi Hx') as ((_ & W7 & W8 & W9 & HA' & HB' & HM' & Hc1' & Hc2' & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_case D) as (l10 & l11 & l12 & A2 & B2 & M2 & c12 & c22 & ν2 & W0 & E
                                                   & _ & _ & _ & _ & _ & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  destruct (leqv_dec l1 l7) as [H17 | N]; [| refute].
  destruct (leqv_dec l2 l8) as [H28 | N]; [| refute].
  destruct (leqv_dec l3 l9) as [H39 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W7 H17) as E17. pose proof (leqv_lequiv _ _ _ W2 W8 H28) as E28.
  pose proof (leqv_lequiv _ _ _ W3 W9 H39) as E39.
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  destruct (IHB B' i _ _ Hc HB HB') as [DB | N]; [| refute].
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E17)) as EA.
  pose proof (ac_ty_sound Hc DB HB (wft_lconv _ _ _ _ _ _ HB' E28)) as EB.
  destruct (case_right_left (M := M) (c1' := c1') (c2' := c2') (ν' := ν') Hc E17 E28 E39 HA HB HA' HB' EA EB HM')
    as [HM'3 Hbr].
  destruct (IHM M' i _ _ Hc HM HM'3) as [DM | N]; [| refute].
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  destruct (Hbr HM EM Hc1' Hc2' Hν') as (_ & _ & Hc1'2 & Hc2'2 & _).
  destruct (IHc1 c1' i l3 Hc Hc1 Hc1'2) as [Dc1 | N]; [| refute].
  destruct (IHc2 c2' i l3 Hc Hc2 Hc2'2) as [Dc2 | N]; [left; eapply actmne_case; eassumption | refute].
Qed.

Lemma Dc_actmne_fst {G Γ l1 l2 l3 l4 A A0 B Bb ν ν0 m m' A0' B0} :
  ac_tmnee G Γ ν ν0 (tySig m m' A0' B0) -> Dc_nee G Γ ν ν0 (tySig m m' A0' B0) ->
  Dc_ne G Γ (tmFst l1 l2 A B ν) (tmFst l3 l4 A0 Bb ν0) A0'.
Proof.
  intros Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmFst ?a ?b ?c ?d ?e) _) =>
    rename a into l5, b into l6, c into A', d into B', e into ν' end.
  destruct (inv_fst Hi Hx) as ((_ & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_fst Hi Hx') as ((_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N]; [left; eapply actmne_fst; exact Dν |].
  right; intros D. destruct (ainv_fst D) as (l7 & l8 & A2 & B2 & ν2 & m2 & m2' & A1 & B1 & E & Dν2).
  injection E as <- <- <- <- <-. rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2. exact (N Dν2).
Qed.

Lemma Dc_actmne_snd {G Γ l1 l2 l3 l4 A A0 B Bb ν ν0 m m' A0' B0} :
  ac_tmnee G Γ ν ν0 (tySig m m' A0' B0) -> Dc_nee G Γ ν ν0 (tySig m m' A0' B0) ->
  Dc_ne G Γ (tmSnd l1 l2 A B ν) (tmSnd l3 l4 A0 Bb ν0) B0[lsingle (tmFst m m' A0' B0 ν)].
Proof.
  intros Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmSnd ?a ?b ?c ?d ?e) _) =>
    rename a into l5, b into l6, c into A', d into B', e into ν' end.
  destruct (inv_snd Hi Hx) as ((_ & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_snd Hi Hx') as ((_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N]; [left; eapply actmne_snd; exact Dν |].
  right; intros D. destruct (ainv_snd D) as (l7 & l8 & A2 & B2 & ν2 & m2 & m2' & A1 & B1 & E & Dν2).
  injection E as <- <- <- <- <-. rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2. exact (N Dν2).
Qed.

Theorem ac_dec_all :
  (forall G Γ T T', ac_ty G Γ T T' -> Dc_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> Dc_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> Dc_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> Dc_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> Dc_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> Dc_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> Dc_ne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> Dc_nee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> Dc_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first
    [ solve [eapply Dc_act_red; eassumption] | solve [eapply Dc_actnf_nat] | solve [eapply Dc_actnf_U]
    | solve [eapply Dc_actnf_pi; eassumption] | solve [eapply Dc_actnf_ne; eassumption]
    | solve [eapply Dc_actnf_CTyp; eassumption] | solve [eapply Dc_actnf_CTrm; eassumption]
    | solve [eapply Dc_actnf_upi; eassumption] | solve [eapply Dc_actnf_cpi; eassumption]
    | solve [eapply Dc_actnf_tpi; eassumption]
    | solve [eapply Dc_actne_gvar; eassumption] | solve [eapply Dc_actne_El; eassumption]
    | solve [eapply Dc_actne_vec; eassumption] | solve [eapply Dc_actne_fin; eassumption]
    | solve [eapply Dc_acc_nil] | solve [eapply Dc_acc_var] | solve [eapply Dc_acc_ext; eassumption]
    | solve [eapply Dc_actm_red; eassumption]
    | solve [eapply Dc_actmnf_code_nat] | solve [eapply Dc_actmnf_code_U]
    | solve [eapply Dc_actmnf_code_pi; eassumption] | solve [eapply Dc_actmnf_zero]
    | solve [eapply Dc_actmnf_succ; eassumption] | solve [eapply Dc_actmnf_ne; eassumption]
    | solve [eapply Dc_actmnf_eta; eassumption] | solve [eapply Dc_actmnf_ueta; eassumption]
    | solve [eapply Dc_actmnf_ceta; eassumption] | solve [eapply Dc_actmnf_teta; eassumption]
    | solve [eapply Dc_actmnf_boxT] | solve [eapply Dc_actmnf_boxt]
    | solve [eapply Dc_actmne_var; eassumption] | solve [eapply Dc_actmne_gvar; eassumption]
    | solve [eapply Dc_actmne_natrec; eassumption] | solve [eapply Dc_actmne_app; eassumption]
    | solve [eapply Dc_actmne_letboxT; eassumption] | solve [eapply Dc_actmne_letboxt; eassumption]
    | solve [eapply Dc_actmne_elimT; eassumption] | solve [eapply Dc_actmne_elimT_gvar; eassumption]
    | solve [eapply Dc_actmne_elimt; eassumption] | solve [eapply Dc_actmne_elimt_glob; eassumption]
    | solve [eapply Dc_actmne_uapp; eassumption] | solve [eapply Dc_actmne_capp; eassumption]
    | solve [eapply Dc_actmne_tapp; eassumption] | solve [eapply Dc_actmnee_red; eassumption]
    | solve [eapply Dc_acs_pt; eassumption]
    | solve [eapply Dc_actnf_sig; eassumption] | solve [eapply Dc_actmnf_code_sig; eassumption]
    | solve [eapply Dc_actmnf_sig_eta; eassumption] | solve [eapply Dc_actmne_fst; eassumption]
    | solve [eapply Dc_actmne_snd; eassumption]
    | solve [eapply Dc_actnf_unit] | solve [eapply Dc_actmnf_code_unit] | solve [eapply Dc_actmnf_unit_eta]
    | solve [eapply Dc_actnf_seq; eassumption] | solve [eapply Dc_actnf_sempty]
    | solve [eapply Dc_actmnf_seq_irr] | solve [eapply Dc_actmnf_sempty_irr]
    | solve [eapply Dc_actmne_elimSEmpty; eassumption]
    | solve [eapply Dc_actnf_id; eassumption] | solve [eapply Dc_actmnf_refl]
    | solve [eapply Dc_actmne_J; eassumption] | solve [eapply Dc_actmnf_code_id; eassumption]
    | solve [eapply Dc_actmnf_code_seq; eassumption] | solve [eapply Dc_actmnf_code_sempty; eassumption]
    | solve [eapply Dc_actnf_empty; eassumption] | solve [eapply Dc_actmne_elimEmpty; eassumption]
    | solve [eapply Dc_actnf_sum; eassumption] | solve [eapply Dc_actmnf_inl; eassumption]
    | solve [eapply Dc_actmnf_inr; eassumption] | solve [eapply Dc_actmne_case; eassumption]
    | solve [eapply Dc_actnf_W; eassumption] | solve [eapply Dc_actmnf_sup; eassumption]
    | solve [eapply Dc_actmne_elimW; eassumption]
    | solve [eapply Dc_actmnf_code_empty; eassumption] | solve [eapply Dc_actmnf_code_sum; eassumption]
    | solve [eapply Dc_actmnf_code_vec; eassumption] | solve [eapply Dc_actmnf_code_fin; eassumption]
    | solve [eapply Dc_actmnf_code_W; eassumption] ].
Qed.

(** Algorithmic conversion of well-formed types (typed terms) of the
    computing layers is decidable: completeness supplies the reflexive
    derivation to induct on. *)
Theorem ac_ty_dec {G i Γ T T' k k'} : compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> Dec (ac_ty G Γ T T').
Proof.
  intros Hc HT HT'. exact (proj1 ac_dec_all _ _ _ _ (ac_complete_ty Hc (eqty_refl _ _ _ _ _ HT)) T' i k k' Hc HT HT').
Qed.

Theorem ac_tm_dec {G i Γ t t' T k} : compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec (ac_tm G Γ t t' T).
Proof.
  intros Hc Ht Ht'.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_dec_all)))) _ _ _ _ _
           (ac_complete_tm Hc (eqtm_refl _ _ _ _ _ _ Ht)) t' i k Hc Ht Ht').
Qed.

(** Declarative equality of well-formed types (typed terms) of the
    computing layers is decidable. *)
Theorem decl_eqty_dec {G i Γ T T' k} : compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k ] -> Dec ([ G ; Γ ⊢[ i ] T ≅ T' @ k ]).
Proof.
  intros Hc HT HT'. apply (dec_iff (P := ac_ty G Γ T T')); [| exact (ac_ty_dec Hc HT HT')].
  split; [intros D; exact (ac_ty_sound Hc D HT HT') | exact (ac_complete_ty Hc)].
Qed.

Theorem decl_eqtm_dec {G i Γ t t' T k} : compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec ([ G ; Γ ⊢[ i ] t ≅ t' : T @ k ]).
Proof.
  intros Hc Ht Ht'. apply (dec_iff (P := ac_tm G Γ t t' T)); [| exact (ac_tm_dec Hc Ht Ht')].
  split; [intros D; exact (ac_tm_sound Hc D Ht Ht') | exact (ac_complete_tm Hc)].
Qed.

(** At every layer: below D, equality is [≡ₗ] ([StaticCodeEq]); at D and M,
    by the algorithm. *)
Theorem decl_eqty_dec_any {G i Γ T T' k} :
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k ] -> Dec ([ G ; Γ ⊢[ i ] T ≅ T' @ k ]).
Proof.
  destruct i.
  - apply decl_eqty_dec_static. unfold lle; cbn; lia.
  - apply decl_eqty_dec_static. apply lle_refl.
  - apply decl_eqty_dec, compt_D.
  - apply decl_eqty_dec, compt_M.
Qed.

Theorem decl_eqtm_dec_any {G i Γ t t' T k} :
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec ([ G ; Γ ⊢[ i ] t ≅ t' : T @ k ]).
Proof.
  destruct i.
  - apply decl_eqtm_dec_static. unfold lle; cbn; lia.
  - apply decl_eqtm_dec_static. apply lle_refl.
  - apply decl_eqtm_dec, compt_D.
  - apply decl_eqtm_dec, compt_M.
Qed.
