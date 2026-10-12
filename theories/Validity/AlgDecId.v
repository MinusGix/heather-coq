(** * Decidability of algorithmic conversion: the identity type

    One of the parts [AlgDec] puts together (see [AlgDecDef]). *)
From DeLaM.Validity Require Export AlgDecDef.

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

