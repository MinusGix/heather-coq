(** * Decidability of algorithmic conversion: indexed coinductive types (M18b)

    One of the parts [AlgDec] puts together (see [AlgDecDef]). As
    [AlgDecIWf]'s cases: the right signature's components are moved into
    the left contexts as they are compared ([ids_ext]); [corec]'s carrier,
    step and seed are compared at the type's telescope, the right ones
    moved there by [corec_right]. *)
From DeLaM.Validity Require Export AlgDecDef.

Lemma Dc_actnf_M {G Γ l l' li k k' ki X X0 A A0 B B0 C C0 j j0} :
  Dc_ty G Γ X X0 -> Dc_ty G (Γ ,, X @ li) A A0 -> Dc_ty G (Γ ,, X @ li ,, A @ l) B B0 ->
  Dc_tm G (Γ ,, X @ li ,, A @ l ,, B @ l') C C0 X⟨↑⟩⟨↑⟩⟨↑⟩ -> Dc_tm G Γ j j0 X ->
  Dc_tynf G Γ (tyM l l' li X A B C j) (tyM k k' ki X0 A0 B0 C0 j0).
Proof.
  intros IHX IHA IHB IHC IHj Y i q q' Hc HY HY'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct Y; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyM ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8)) =>
    rename p1 into k5, p2 into k5', p3 into ki5, p4 into X', p5 into A', p6 into B', p7 into C', p8 into j' end.
  destruct (inv_ty_M HY) as ((_ & W1 & W2 & W3 & HX & HA & HB & HC & Hj) & _).
  destruct (inv_ty_M HY') as ((_ & W1' & W2' & W3' & HX' & HA' & HB' & HC' & Hj') & _).
  destruct (leqv_dec l k5) as [H1 | Hneg]; [| refute].
  destruct (leqv_dec l' k5') as [H2 | Hneg]; [| refute].
  destruct (leqv_dec li ki5) as [H3 | Hneg]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W1' H1) as E1. pose proof (leqv_lequiv _ _ _ W2 W2' H2) as E2.
  pose proof (leqv_lequiv _ _ _ W3 W3' H3) as E3.
  destruct (IHX X' i _ _ Hc HX HX') as [DX | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DX HX (wft_lconv _ _ _ _ _ _ HX' E3)) as EX.
  assert (Hid0 : [ G ; Γ ⊢[ i ] lshift 0 : Γ ]) by (eapply lsub_wf_id; eauto using ctx_of_wf_ty).
  destruct (ids_ext Hi Hid0 Hid0 HX EX HX' E3) as (I1 & I1r).
  pose proof (wft_lconv _ _ _ _ _ _ (mv_ty Hi I1r HA') E1) as HA'l.
  destruct (IHA A' i _ _ Hc HA HA'l) as [DA | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DA HA HA'l) as EA.
  destruct (ids_ext Hi I1 I1r HA EA HA' E1) as (I2 & I2r).
  pose proof (wft_lconv _ _ _ _ _ _ (mv_ty Hi I2r HB') E2) as HB'l.
  destruct (IHB B' i _ _ Hc HB HB'l) as [DB | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DB HB HB'l) as EB.
  destruct (ids_ext Hi I2 I2r HB EB HB' E2) as (I3 & I3r).
  assert (EX3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] X⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wk3_eqty; [exact Hi | exact (ctx_of_wf_tm Hi HC) | exact EX]).
  assert (HC'l : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact (mv_tm Hi I3r HC') | exact E3] | exact EX3]).
  destruct (IHC C' i li Hc HC HC'l) as [DC | Hneg]; [| refute].
  assert (Hj'l : [ G ; Γ ⊢[ i ] j' : X @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact Hj' | exact E3] | exact EX]).
  destruct (IHj j' i li Hc Hj Hj'l) as [Dj | Hneg]; [left; apply actnf_M; assumption | refute].
Qed.

Lemma Dc_actmnf_corec {G Γ l l' li X A B C j k1 k2 k3 X1 A1 B1 C1 j1 k1' k2' k3' X1' A1' B1' C1' j1'
    kc kc' Y Y' c c' y y'} :
  Dc_ty G (Γ ,, X @ li) Y Y' ->
  Dc_tm G (Γ ,, X @ li ,, Y @ kc) c c' (mStepTy l l' li X A B C kc Y)⟨↑⟩ ->
  Dc_tm G Γ y y' Y[lsingle j] ->
  Dc_tmnf G Γ (tmCorec k1 k2 k3 X1 A1 B1 C1 kc Y c j1 y) (tmCorec k1' k2' k3' X1' A1' B1' C1' kc' Y' c' j1' y')
    (tyM l l' li X A B C j).
Proof.
  intros IHY IHc IHy x i q Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmCorec _ _ _ _ _ _ _ ?p1 ?p2 ?p3 _ ?p4) _) =>
    rename p1 into kc5, p2 into Y5, p3 into c5, p4 into y5 end.
  destruct (corec_parts Hc Hw) as (HE & Wkc & Ej & HY & Hc0 & Hy & _).
  destruct (corec_parts Hc Hx) as (_ & Wkc5 & _ & HY5 & Hc5 & Hy5 & _).
  destruct (leqv_dec kc kc5) as [Hkc | Hneg]; [| refute].
  pose proof (leqv_lequiv _ _ _ Wkc Wkc5 Hkc) as Ekc.
  pose proof HE as (_ & _ & _ & HS & _).
  pose proof (eqtm_wf_l Hi Ej) as Hj.
  destruct (IHY Y5 i _ _ Hc HY HY5) as [DY | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DY HY (wft_lconv _ _ _ _ _ _ HY5 Ekc)) as EY.
  destruct (corec_right Hc HS Hj Ekc Wkc HY EY Hc5 Hy5) as (Hc'l & Hy'l).
  destruct (IHc c5 i _ Hc Hc0 Hc'l) as [Dc | Hneg]; [| refute].
  destruct (IHy y5 i kc Hc Hy Hy'l) as [Dy | Hneg]; [left; apply actmnf_corec; assumption | refute].
Qed.

Lemma Dc_actmne_out {G Γ l l' li k k' ki X X0 A A0 B B0 C C0 j j0 ν ν0 W} :
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmOut l l' li X A B C j ν) (tmOut k k' ki X0 A0 B0 C0 j0 ν0) (mOutTy l l' li X A B C j).
Proof.
  intros Dν0 IHν x i q q' T T' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmOut _ _ _ _ _ _ _ _ ?p) _) => rename p into ν' end.
  destruct (inv_out Hi Hx) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hν) & _).
  destruct (inv_out Hi Hx') as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hν') & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | Hneg]; [left; eapply actmne_out; exact Dν |].
  right; intros D; destruct (ainv_out D) as (k2 & k2' & ki2 & X2 & A2 & B2 & C2 & j2 & ν2 & W0 & E & Dν2).
  injection E as <- <- <- <- <- <- <- <- <-.
  rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (Hneg Dν2).
Qed.
