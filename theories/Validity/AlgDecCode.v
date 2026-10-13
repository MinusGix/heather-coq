(** * Decidability of algorithmic conversion: pairs, unit, codes, strict equality, Empty and the truncation

    One of the parts [AlgDec] puts together (see [AlgDecDef]). *)
From DeLaM.Validity Require Export AlgDecDef.

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

(** The code of [Wf] (M15b), as [W]'s: the arity at [Nat]. *)
Lemma Dc_actmnf_code_wf {G Γ l k k0 s s0 n n0} :
  Dc_tm G Γ s s0 (tyU k) -> Dc_tm G (Γ ,, tyEl k s @ k) n n0 tyNat ->
  Dc_tmnf G Γ (tmWf k s n) (tmWf k0 s0 n0) (tyU l).
Proof.
  intros IHs IHn x i m Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmWf ?a ?b ?c) _) => rename a into k', b into s', c into n' end.
  destruct (code_wf_prem Hc Hx) as (W1 & Hs & Hn).
  destruct (code_wf_prem Hc Hx') as (W5 & Hs' & Hn').
  pose proof (compt_notV Hc) as Hv.
  destruct (leqv_dec k k') as [H15 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  pose proof (code_U_conv Hc E15 Hs') as Hs1.
  destruct (IHs s' i _ Hc Hs Hs1) as [Ds | N]; [| refute].
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl k s @ k ]) by (apply wft_El; assumption).
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl k s ≅ tyEl k' s' @ k ]) by (apply eqty_El; [exact Hv | exact E15 | exact Es]).
  assert (EEl' : [ G ; Γ ⊢[ i ] tyEl k' s' ≅ tyEl k s @ k' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EEl) | exact (lequiv_sym _ _ _ E15)]).
  assert (HΓ1 : [ G ; Γ ,, tyEl k s @ k ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  pose proof (stab_tm Hi EEl' (lequiv_sym _ _ _ E15) HΓ1 Hn') as Hn1.
  destruct (IHn n' i _ Hc Hn Hn1) as [Dn | N]; [left; apply actmnf_code_wf; assumption | refute].
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
(** The code of [∥·∥] (M16b). *)
Lemma Dc_actmnf_code_sq {G Γ l k k0 s s0} :
  Dc_tm G Γ s s0 (tyU k) -> Dc_tmnf G Γ (tmSqCode k s) (tmSqCode k0 s0) (tyU l).
Proof.
  intros IHs x i m Hc Hx Hx'.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSqCode ?a ?b) _) => rename a into k', b into s' end.
  destruct (code_sq_prem Hc Hx) as (W1 & Hs). destruct (code_sq_prem Hc Hx') as (W5 & Hs').
  destruct (leqv_dec k k') as [H15 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15.
  destruct (IHs s' i _ Hc Hs (code_U_conv Hc E15 Hs')) as [Ds | N]; [left; apply actmnf_code_sq; assumption | refute].
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

Lemma Dc_actmnf_seq_irr {G Γ l A a b w w0} : Dc_tmnf G Γ w w0 (tySEq l A a b).
Proof. intros x i k Hc Hw Hx. left; apply actmnf_seq_irr. Qed.
Lemma Dc_actmnf_sempty_irr {G Γ l w w0} : Dc_tmnf G Γ w w0 (tySEmpty l).
Proof. intros x i k Hc Hw Hx. left; apply actmnf_sempty_irr. Qed.
Lemma Dc_actmnf_empty_irr {G Γ l w w0} : Dc_tmnf G Γ w w0 (tyEmpty l).
Proof. intros x i k Hc Hw Hx. left; apply actmnf_empty_irr. Qed.

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

(** [Empty]'s eliminator (M12a): the scrutinees are not compared. *)
Lemma Dc_actmne_elimEmpty {G Γ l1 l2 l3 l4 M M0 ν ν0} :
  Dc_ty G (Γ ,, tyEmpty l2 @ l2) M M0 -> whne ν ->
  Dc_ne G Γ (elimEmpty l1 l2 M ν) (elimEmpty l3 l4 M0 ν0) M[lsingle ν].
Proof.
  intros IHM Hn x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (elimEmpty ?p1 ?p2 ?p3 ?p4) _) =>
    rename p1 into l5, p2 into l6, p3 into M', p4 into ν' end.
  destruct (inv_elimEmpty Hi Hx) as ((_ & W1 & W2 & HM & Hν) & _ & _).
  destruct (inv_elimEmpty Hi Hx') as ((_ & W5 & W6 & HM' & Hν') & _ & _).
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
  destruct (IHM M' i _ _ Hc HM HM'1) as [DM | N]; [| refute].
  destruct (whne_dec ν') as [Hn' | N]; [left; apply actmne_elimEmpty; assumption | refute].
Qed.

(** Propositional truncation (M16a): as at [Empty], the scrutinees are not
    compared, and neither are the steps. *)
Lemma Dc_actnf_sq {G Γ l l0 A A0} : Dc_ty G Γ A A0 -> Dc_tynf G Γ (tySq l A) (tySq l0 A0).
Proof.
  intros IHA X i k k' Hc HX HX'.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tySq ?a ?b)) => rename a into l', b into A' end.
  destruct (inv_ty_sq HX) as ((_ & _ & HA) & _). destruct (inv_ty_sq HX') as ((_ & _ & HA') & _).
  destruct (leqv_dec l l') as [Hl | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [left; apply actnf_sq; assumption | refute].
Qed.

Lemma Dc_actmnf_sq_irr {G Γ l A w w0} : Dc_tmnf G Γ w w0 (tySq l A).
Proof. intros x i k Hc Hw Hx. left; apply actmnf_sq_irr. Qed.

Lemma Dc_actmne_elimSq {G Γ l1 l2 l3 l4 A A0 M M0 c c0 ν ν0} :
  Dc_ty G Γ A A0 -> Dc_ty G (Γ ,, tySq l1 A @ l1) M M0 -> whne ν ->
  Dc_ne G Γ (tmElimSq l1 l2 A M c ν) (tmElimSq l3 l4 A0 M0 c0 ν0) (tySq l2 M[lsingle ν]).
Proof.
  intros IHA IHM Hn x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmElimSq ?p1 ?p2 ?p3 ?p4 ?p5 ?p6) _) =>
    rename p1 into l5, p2 into l6, p3 into A', p4 into M', p5 into c', p6 into ν' end.
  destruct (inv_elimSq Hi Hx) as ((_ & W1 & W2 & HA & HM & _ & Hν) & _ & _).
  destruct (inv_elimSq Hi Hx') as ((_ & W5 & W6 & HA' & HM' & _ & _) & _ & _).
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute].
  destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15. pose proof (leqv_lequiv _ _ _ W2 W6 H26) as E26.
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  (* the other motive, in this context *)
  assert (HS : [ G ; Γ ⊢[ i ] tySq l5 A' ≅ tySq l1 A @ l5 ]).
  { eapply eqty_lconv; [| exact (lequiv_sym _ _ _ E15)].
    apply eqty_sym, eqty_sq; [(apply compt_notV; exact Hc) | exact E15 | exact HA | exact EA]. }
  assert (HΓS : [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_sq; [(apply compt_notV; exact Hc) | exact W1 | exact HA] | exact W1]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi HS (lequiv_sym _ _ _ E15) HΓS HM') E26) as HM'1.
  destruct (IHM M' i _ _ Hc HM HM'1) as [DM | N]; [| refute].
  destruct (whne_dec ν') as [Hn' | N]; [left; apply actmne_elimSq; assumption | refute].
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

