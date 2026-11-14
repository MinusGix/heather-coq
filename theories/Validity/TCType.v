(** * Decidable type checking: types and contexts (M7_DESIGN.md C1, J3.5)

    One step of the induction on size: well-formedness of a type or a
    context is decidable when every judgment about smaller syntax is
    ([IHsz n]). A type's level is read off its former; each premise is
    decided in the order the rule's presuppositions need, and a failure is
    refuted by inversion. *)
From DeLaM.Validity Require Export TCBase.
From DeLaM.Typing Require Import PresupM.

(** The induction hypothesis: every problem about syntax of size < [n]. *)
Definition IHsz (n : nat) : Prop :=
  (forall T, sz_ty T < n -> TYD T) /\
  (forall t, sz_tm t < n -> CKD t) /\
  (forall t, sz_tm t < n -> synth t -> SYD t) /\
  (forall Γ, sz_ctx Γ < n -> CXD Γ).

Section Step.
Context (n : nat) (IH : IHsz n).

Let ihT T : sz_ty T < n -> TYD T := proj1 IH T.
Let ihC t : sz_tm t < n -> CKD t := proj1 (proj2 IH) t.
Let ihX Γ : sz_ctx Γ < n -> CXD Γ := proj2 (proj2 (proj2 IH)) Γ.

Ltac szl := cbn [sz_ty sz_tm sz_ctx sz_l] in *; lia.

(** The M-only formers: at [i = lM], or refuted by [inv]. *)
Ltac at_M inv :=
  let NM := fresh "NM" in
  match goal with |- Dec (wf_ty _ ?i _ _ _) =>
    destruct (layer_eq_dec i lM) as [-> | NM];
    [| right; let H := fresh "H" in intros H;
       first [ destruct (inv _ _ _ _ _ H) as ((? & _) & _) | destruct (inv _ _ _ _ _ _ H) as ((? & _) & _)
             | destruct (inv _ _ _ _ _ _ _ H) as ((? & _) & _) | destruct (inv _ _ _ _ _ _ _ _ H) as ((? & _) & _) ];
       contradiction]
  end.

Lemma dec_tyErr : TYD tyErr.
Proof using . intros G i Γ k _. right; apply no_ty_err. Qed.

Lemma dec_tyNat : TYD tyNat.
Proof using .
  intros G i Γ k HΓ. destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  destruct (lvl_eq_dec (gL G) k lzero) as [Q | Q].
  - left; exact (wft_lvl Q (wft_nat _ _ _ Hv HΓ)).
  - right; intros H; exact (Q (proj2 (inv_ty_nat H))).
Qed.

Lemma dec_tyU l : TYD (tyU l).
Proof using .
  intros G i Γ k HΓ. destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_U H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k (lsuc l)) as [Q | Q].
  - left; exact (wft_lvl Q (wft_U _ _ _ _ Hv HΓ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_U H))).
Qed.

Lemma dec_tyPi l l' A B : sz_ty (tyPi l l' A B) <= n -> TYD (tyPi l l' A B).
Proof using ihT.
  intros Hsz G i Γ k HΓ. destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_pi H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros H; destruct (inv_ty_pi H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros H; destruct (inv_ty_pi H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B ltac:(szl) G i _ l' HΓA) as [HB | N];
    [| right; intros H; destruct (inv_ty_pi H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k (lmax l l')) as [Q | Q].
  - left; exact (wft_lvl Q (wft_pi _ _ _ _ _ _ _ Hv Hl Hl' HA HB)).
  - right; intros H; exact (Q (proj2 (inv_ty_pi H))).
Qed.

Lemma dec_tyEl l t : sz_ty (tyEl l t) <= n -> TYD (tyEl l t).
Proof using ihC.
  intros Hsz G i Γ k HΓ. destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_El H) as ((_ & X & _) & _); contradiction].
  assert (HU : [ G ; Γ ⊢[ typeof i ] tyU l @ lsuc l ])
    by (apply wft_U; [exact (typeof_notV i) | rewrite typeof_idem; exact HΓ | exact Hl]).
  destruct (ihC t ltac:(szl) G i Γ _ _ HU) as [Ht | N];
    [| right; intros H; destruct (inv_ty_El H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_El _ _ _ _ _ Hv Hl Ht)).
  - right; intros H; exact (Q (proj2 (inv_ty_El H))).
Qed.

Lemma dec_tyGvar U d : sz_ty (tyGvar U d) <= n -> TYD (tyGvar U d).
Proof using ihC.
  intros Hsz G i Γ k HΓ. destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (in_gctx_dec (gΨ G) U) as [(D & Hin) | N];
    [| right; intros H; destruct (inv_ty_gvar H) as (? & ? & ? & (_ & _ & X & _) & _); exact (N _ X)].
  destruct D as [| Δ i' l0 | Δ i' T0 l0 |];
    try (right; intros H; destruct (inv_ty_gvar H) as (? & ? & ? & (_ & _ & X & _) & _);
         discriminate (in_gctx_det Hin X)).
  destruct (gctx_decl_ok _ _ _ HG Hin) as [HΔ _].
  assert (Inv : forall k0, [ G ; Γ ⊢[ i ] tyGvar U d @ k0 ] ->
    lle i' i /\ lsub_tail d Δ Γ /\ dnfl d /\
    (forall m A k1, in_ctx Δ m A k1 -> [ G ; Γ ⊢[ i ] llk d m : A[d] @ k1 ]) /\ lvl_eq (gL G) k0 l0).
  { intros k0 H. destruct (inv_ty_gvar H) as (Δ' & i'' & l0' & (_ & _ & X & Hle & Ht & Hd & He) & Hk).
    pose proof (in_gctx_det Hin X) as E. injection E as <- <- <-. tauto. }
  destruct (lle_dec i' i) as [Hle | N]; [| right; intros H; apply N, (Inv _ H)].
  destruct (lsub_tail_dec d Δ Γ) as [Ht | N]; [| right; intros H; apply N, (Inv _ H)].
  destruct (dnfl_dec d) as [Hd | N]; [| right; intros H; apply N, (Inv _ H)].
  destruct (sub_dec Δ d HΓ HΔ Ht Hd
              (fun m A k1 HA => ihC (llk d m) ltac:(pose proof (sz_llk d m); szl) G i Γ A k1 HA))
    as [He | N]; [| right; intros H; apply N, (Inv _ H)].
  destruct (lvl_eq_dec (gL G) k l0) as [Q | Q].
  - left; exact (wft_lvl Q (wft_gvar _ _ _ _ _ _ _ _ Hv HΓ Hin Hle Ht Hd He)).
  - right; intros H; apply Q, (Inv _ H).
Qed.

Lemma dec_tyCTyp Δ l : sz_ty (tyCTyp Δ l) <= n -> TYD (tyCTyp Δ l).
Proof using ihX.
  intros Hsz G i Γ k HΓ. at_M @inv_ty_CTyp. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; intros H; destruct (inv_ty_CTyp H) as ((_ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_CTyp H) as ((_ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k lzero) as [Q | Q].
  - left; exact (wft_lvl Q (wft_CTyp _ _ _ _ HΓ HΔ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_CTyp H))).
Qed.

Lemma dec_tyCTrm Δ A l : sz_ty (tyCTrm Δ A l) <= n -> TYD (tyCTrm Δ A l).
Proof using ihT ihX.
  intros Hsz G i Γ k HΓ. at_M @inv_ty_CTrm. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; intros H; destruct (inv_ty_CTrm H) as ((_ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_CTrm H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (ihT A ltac:(szl) G lD Δ l HΔ) as [HA | N]; [| right; intros H; destruct (inv_ty_CTrm H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k lzero) as [Q | Q].
  - left; exact (wft_lvl Q (wft_CTrm _ _ _ _ _ HΓ HΔ HA Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_CTrm H))).
Qed.

Lemma dec_tyUPi m l T : sz_ty (tyUPi m l T) <= n -> TYD (tyUPi m l T).
Proof using ihT.
  intros Hsz G i Γ k HΓ. at_M @inv_ty_upi.
  destruct (lt_dec 0 m) as [Hm | N]; [| right; intros H; destruct (inv_ty_upi H) as ((_ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (m + gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_upi H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihT T ltac:(szl) (gctx_uwk m G) lM (Γ⟨ush m⟩ᵤ) l (uwk_ctx m HΓ)) as [HT | N];
    [| right; intros H; destruct (inv_ty_upi H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k lomega) as [Q | Q].
  - left; exact (wft_lvl Q (wft_upi _ _ _ _ _ HΓ Hm Hl HT)).
  - right; intros H; exact (Q (proj2 (inv_ty_upi H))).
Qed.

Lemma dec_tyCPi l T : sz_ty (tyCPi l T) <= n -> TYD (tyCPi l T).
Proof using ihT.
  intros Hsz G i Γ k HΓ. at_M @inv_ty_cpi. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_cpi H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT T ltac:(szl) (gext G gdCtx) lM Γ⟪S⟫ l (ctx_S (wfg_ctx' HG) HΓ)) as [HT | N];
    [| right; intros H; destruct (inv_ty_cpi H) as ((_ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_cpi _ _ _ _ HΓ Hl HT)).
  - right; intros H; exact (Q (proj2 (inv_ty_cpi H))).
Qed.

Lemma dec_tyTPi Δ l l' T : sz_ty (tyTPi Δ l l' T) <= n -> TYD (tyTPi Δ l l' T).
Proof using ihT ihX.
  intros Hsz G i Γ k HΓ. at_M @inv_ty_tpi. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; intros H; destruct (inv_ty_tpi H) as ((_ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_tpi H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros H; destruct (inv_ty_tpi H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihT T ltac:(szl) (gext G (gdTy Δ lD l)) lM Γ⟪S⟫ l' (ctx_S (wfg_ty' HΔ (or_intror eq_refl) Hl) HΓ))
    as [HT | N]; [| right; intros H; destruct (inv_ty_tpi H) as ((_ & _ & _ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l') as [Q | Q].
  - left; exact (wft_lvl Q (wft_tpi _ _ _ _ _ _ HΓ HΔ Hl Hl' HT)).
  - right; intros H; exact (Q (proj2 (inv_ty_tpi H))).
Qed.

Lemma dec_tySig l l' A B : sz_ty (tySig l l' A B) <= n -> TYD (tySig l l' A B).
Proof using ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_sig H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros H; destruct (inv_ty_sig H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros H; destruct (inv_ty_sig H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B ltac:(szl) G i _ l' HΓA) as [HB | N];
    [| right; intros H; destruct (inv_ty_sig H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k (lmax l l')) as [Q | Q].
  - left; exact (wft_lvl Q (wft_sig _ _ _ _ _ _ _ Hc Hl Hl' HA HB)).
  - right; intros H; exact (Q (proj2 (inv_ty_sig H))).
Qed.

Lemma dec_tyUnit l : TYD (tyUnit l).
Proof using .
  intros G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_unit H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_unit _ _ _ _ Hc HΓ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_unit H))).
Qed.

(** Strict equality (M10a; at every layer but V since M10c). *)
Lemma dec_tySEq l A a b : sz_ty (tySEq l A a b) <= n -> TYD (tySEq l A a b).
Proof using ihC ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_seq H) as ((_ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros H; destruct (inv_ty_seq H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihC a ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Ha | N];
    [| right; intros H; destruct (inv_ty_seq H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihC b ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Hb | N];
    [| right; intros H; destruct (inv_ty_seq H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_seq _ _ _ _ _ _ _ Hc Hl HA Ha Hb)).
  - right; intros H; exact (Q (proj2 (inv_ty_seq H))).
Qed.

(** The identity type (M11a; at every layer but V since M11b). *)
Lemma dec_tyId l A a b : sz_ty (tyId l A a b) <= n -> TYD (tyId l A a b).
Proof using ihC ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_id H) as ((_ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros H; destruct (inv_ty_id H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihC a ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Ha | N];
    [| right; intros H; destruct (inv_ty_id H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihC b ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Hb | N];
    [| right; intros H; destruct (inv_ty_id H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_id _ _ _ _ _ _ _ Hc Hl HA Ha Hb)).
  - right; intros H; exact (Q (proj2 (inv_ty_id H))).
Qed.

Lemma dec_tySEmpty l : TYD (tySEmpty l).
Proof using .
  intros G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_sempty H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_sempty _ _ _ _ Hc HΓ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_sempty H))).
Qed.

(** The empty type (M12a; at every layer but V since M12c). *)
Lemma dec_tyEmpty l : TYD (tyEmpty l).
Proof using .
  intros G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_empty H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_empty _ _ _ _ Hc HΓ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_empty H))).
Qed.

(** Binary sums (M12b; at every layer but V since M12c). *)
Lemma dec_tySum l l' A B : sz_ty (tySum l l' A B) <= n -> TYD (tySum l l' A B).
Proof using ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_sum H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N];
    [| right; intros H; destruct (inv_ty_sum H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros H; destruct (inv_ty_sum H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihT B ltac:(szl) G i Γ l' HΓ) as [HB | N];
    [| right; intros H; destruct (inv_ty_sum H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k (lmax l l')) as [Q | Q].
  - left; exact (wft_lvl Q (wft_sum _ _ _ _ _ _ _ Hc Hl Hl' HA HB)).
  - right; intros H; exact (Q (proj2 (inv_ty_sum H))).
Qed.

(** Well-founded trees (M13a): the computing layers only. *)
Lemma dec_tyW l l' A B : sz_ty (tyW l l' A B) <= n -> TYD (tyW l l' A B).
Proof using ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_W H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N];
    [| right; intros H; destruct (inv_ty_W H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros H; destruct (inv_ty_W H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B ltac:(szl) G i _ l' HΓA) as [HB | N];
    [| right; intros H; destruct (inv_ty_W H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k (lmax l l')) as [Q | Q].
  - left; exact (wft_lvl Q (wft_W _ _ _ _ _ _ _ Hc Hl Hl' HA HB)).
  - right; intros H; exact (Q (proj2 (inv_ty_W H))).
Qed.

(** [Vec] and [Fin] (M14a): every layer but V since M14b. *)
Lemma dec_tyVec l A t : sz_ty (tyVec l A t) <= n -> TYD (tyVec l A t).
Proof using ihC ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_vec H) as ((_ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros H; destruct (inv_ty_vec H) as ((_ & _ & X & _) & _); contradiction].
  assert (HN : [ G ; Γ ⊢[ typeof i ] tyNat @ lzero ]) by (apply wft_nat; [exact (typeof_notV i) | rewrite typeof_idem; exact HΓ]).
  destruct (ihC t ltac:(szl) G i Γ _ _ HN) as [Ht | N];
    [| right; intros H; destruct (inv_ty_vec H) as ((_ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_vec _ _ _ _ _ _ Hc Hl HA Ht)).
  - right; intros H; exact (Q (proj2 (inv_ty_vec H))).
Qed.

Lemma dec_tyFin t : sz_ty (tyFin t) <= n -> TYD (tyFin t).
Proof using ihC.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  assert (HN : [ G ; Γ ⊢[ typeof i ] tyNat @ lzero ]) by (apply wft_nat; [exact (typeof_notV i) | rewrite typeof_idem; exact HΓ]).
  destruct (ihC t ltac:(szl) G i Γ _ _ HN) as [Ht | N];
    [| right; intros H; destruct (inv_ty_fin H) as ((_ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k lzero) as [Q | Q].
  - left; exact (wft_lvl Q (wft_fin _ _ _ _ Hc Ht)).
  - right; intros H; exact (Q (proj2 (inv_ty_fin H))).
Qed.

(** Finitary well-founded trees (M15a; every layer but V since M15b). *)
Lemma dec_tyWf l A N : sz_ty (tyWf l A N) <= n -> TYD (tyWf l A N).
Proof using ihC ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N0]; [| right; intros H; destruct (inv_ty_wf H) as ((_ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N0];
    [| right; intros H; destruct (inv_ty_wf H) as ((_ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  assert (HNat : [ G ; Γ ,, A @ l ⊢[ typeof i ] tyNat @ lzero ])
    by (apply wft_nat; [exact (typeof_notV i) | rewrite typeof_idem; exact HΓA]).
  destruct (ihC N ltac:(szl) G i _ _ _ HNat) as [HN | N0];
    [| right; intros H; destruct (inv_ty_wf H) as ((_ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_wf _ _ _ _ _ _ Hc Hl HA HN)).
  - right; intros H; exact (Q (proj2 (inv_ty_wf H))).
Qed.

(** Propositional truncation (M16a; every layer but V since M16b). *)
Lemma dec_tySq l A : sz_ty (tySq l A) <= n -> TYD (tySq l A).
Proof using ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_sq H) as ((_ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros H; destruct (inv_ty_sq H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_sq _ _ _ _ _ Hc Hl HA)).
  - right; intros H; exact (Q (proj2 (inv_ty_sq H))).
Qed.

(** Dependent tuples (M17a; every layer but V since M17c). *)
Lemma dec_tyDVec l t F : sz_ty (tyDVec l t F) <= n -> TYD (tyDVec l t F).
Proof using ihC ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_dvec H) as ((_ & X & _) & _); contradiction].
  assert (HN : [ G ; Γ ⊢[ typeof i ] tyNat @ lzero ]) by (apply wft_nat; [exact (typeof_notV i) | rewrite typeof_idem; exact HΓ]).
  destruct (ihC t ltac:(szl) G i Γ _ _ HN) as [Ht | N];
    [| right; intros H; destruct (inv_ty_dvec H) as ((_ & _ & X & _) & _); contradiction].
  assert (HΓF : [ G ; Γ ,, tyFin t @ lzero ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty (wft_fin _ _ _ _ Hv Ht)) | exact I]).
  destruct (ihT F ltac:(szl) G i _ l HΓF) as [HF | N];
    [| right; intros H; destruct (inv_ty_dvec H) as ((_ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_dvec _ _ _ _ _ _ Hv Hl Ht HF)).
  - right; intros H; exact (Q (proj2 (inv_ty_dvec H))).
Qed.

(** Indexed finitary trees (M17b; every layer but V since M17c). The
    signature is shared with [sup_i]'s and [elim_IWf]'s synthesis
    ([TCSynth]); its contexts are at [typeof i]. *)
Lemma dec_iwf_sig l li X A N Ot C :
  sz_ty X < n -> sz_ty A < n -> sz_tm N < n -> sz_tm Ot < n -> sz_tm C < n ->
  forall G i Γ, i <> lV -> [ G ; Γ ⊢[ typeof i ] ] ->
  IWfSig (G := G) (i := i) Γ l li X A N Ot C \/ ~ IWfSig (G := G) (i := i) Γ l li X A N Ot C.
Proof using ihC ihT.
  intros SX SA SN SO SC G i Γ Hv HΓ.
  destruct (lwf_Dec (gL G) l) as [Hl | Hn]; [| right; intros (H & _); contradiction].
  destruct (lwf_Dec (gL G) li) as [Hli | Hn]; [| right; intros (_ & H & _); contradiction].
  destruct (ihT X SX G i Γ li HΓ) as [HX | Hn]; [| right; intros (_ & _ & H & _); contradiction].
  destruct (ihT A SA G i Γ l HΓ) as [HA | Hn]; [| right; intros (_ & _ & _ & H & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  assert (HNat : [ G ; Γ ,, A @ l ⊢[ typeof i ] tyNat @ lzero ])
    by (apply wft_nat; [exact (typeof_notV i) | rewrite typeof_idem; exact HΓA]).
  destruct (ihC N SN G i _ _ _ HNat) as [HN | Hn]; [| right; intros (_ & _ & _ & _ & H & _); contradiction].
  pose proof (wk1_ty_g G i _ _ _ _ _ HΓA HX) as HX1.
  destruct (ihC Ot SO G i _ _ _ (lift_to_typeof_ty HX1)) as [HO | Hn];
    [| right; intros (_ & _ & _ & _ & _ & H & _); contradiction].
  assert (HF : [ G ; Γ ,, A @ l ⊢[ i ] tyFin N @ lzero ]) by (apply wft_fin; [exact Hv | exact HN]).
  assert (HΓAF : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓA | exact (lift_to_typeof_ty HF) | exact I]).
  pose proof (wk1_ty_g G i _ _ _ _ _ HΓAF HX1) as HX2.
  destruct (ihC C SC G i _ _ _ (lift_to_typeof_ty HX2)) as [HC | Hn];
    [| right; intros (_ & _ & _ & _ & _ & _ & H); contradiction].
  left; unfold IWfSig; auto 8.
Qed.

Lemma dec_tyIWf l li X A N Ot C m : sz_ty (tyIWf l li X A N Ot C m) <= n -> TYD (tyIWf l li X A N Ot C m).
Proof using ihC ihT.
  intros Hsz G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  destruct (dec_iwf_sig l li X A N Ot C ltac:(szl) ltac:(szl) ltac:(szl) ltac:(szl) ltac:(szl) G i Γ Hv HΓ)
    as [HS | Hn];
    [| right; intros H; destruct (inv_ty_iwf H) as ((_ & Hs) & _); apply Hn; unfold IWfSig; tauto].
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  destruct (ihC m ltac:(szl) G i Γ X li (lift_to_typeof_ty HX)) as [Hm | Hn];
    [| right; intros H; destruct (inv_ty_iwf H) as ((_ & _ & _ & _ & _ & _ & _ & _ & Hm) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k (lmax l li)) as [Q | Q].
  - left; eapply wft_lvl; [exact Q | apply wft_iwf; assumption].
  - right; intros H; exact (Q (proj2 (inv_ty_iwf H))).
Qed.
(** Indexed coinductive types (M18b), at the computational layers only;
    the signature is shared with [corec]'s and [out]'s synthesis. *)
Lemma dec_m_sig l l' li X A B C :
  sz_ty X < n -> sz_ty A < n -> sz_ty B < n -> sz_tm C < n ->
  forall G i Γ, compt i -> [ G ; Γ ⊢[ typeof i ] ] ->
  MSig (G := G) (i := i) Γ l l' li X A B C \/ ~ MSig (G := G) (i := i) Γ l l' li X A B C.
Proof using ihC ihT.
  intros SX SA SB SC G i Γ Hc HΓ.
  destruct (lwf_Dec (gL G) l) as [Hl | Hn]; [| right; intros (H & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | Hn]; [| right; intros (_ & H & _); contradiction].
  destruct (lwf_Dec (gL G) li) as [Hli | Hn]; [| right; intros (_ & _ & H & _); contradiction].
  destruct (ihT X SX G i Γ li HΓ) as [HX | Hn]; [| right; intros (_ & _ & _ & H & _); contradiction].
  assert (HΓX : [ G ; Γ ,, X @ li ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HX) | exact Hli]).
  destruct (ihT A SA G i _ l HΓX) as [HA | Hn]; [| right; intros (_ & _ & _ & _ & H & _); contradiction].
  assert (HΓXA : [ G ; Γ ,, X @ li ,, A @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓX | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B SB G i _ l' HΓXA) as [HB | Hn]; [| right; intros (_ & _ & _ & _ & _ & H & _); contradiction].
  assert (HΓXAB : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓXA | exact (lift_to_typeof_ty HB) | exact Hl']).
  pose proof (wk1_ty_g G i _ _ _ _ _ HΓX HX) as HX1.
  pose proof (wk1_ty_g G i _ _ _ _ _ HΓXA HX1) as HX2.
  pose proof (wk1_ty_g G i _ _ _ _ _ HΓXAB HX2) as HX3.
  destruct (ihC C SC G i _ _ _ (lift_to_typeof_ty HX3)) as [HC | Hn];
    [| right; intros (_ & _ & _ & _ & _ & _ & H); contradiction].
  left; unfold MSig; auto 8.
Qed.

Lemma dec_tyM l l' li X A B C j : sz_ty (tyM l l' li X A B C j) <= n -> TYD (tyM l l' li X A B C j).
Proof using ihC ihT.
  intros Hsz G i Γ k HΓ.
  destruct (compt_dec i) as [Hc | Hn]; [| right; intros H; exact (Hn (proj1 (proj1 (inv_ty_M H))))].
  destruct (dec_m_sig l l' li X A B C ltac:(szl) ltac:(szl) ltac:(szl) ltac:(szl) G i Γ Hc HΓ) as [HS | Hn];
    [| right; intros H; destruct (inv_ty_M H) as ((_ & Hs) & _); apply Hn; unfold MSig; tauto].
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  destruct (ihC j ltac:(szl) G i Γ X li (lift_to_typeof_ty HX)) as [Hj | Hn];
    [| right; intros H; destruct (inv_ty_M H) as ((_ & _ & _ & _ & _ & _ & _ & _ & Hj) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k (mlvl l l' li)) as [Q | Q].
  - left; eapply wft_lvl; [exact Q | apply wft_M; assumption].
  - right; intros H; exact (Q (proj2 (inv_ty_M H))).
Qed.


Lemma ty_step T : sz_ty T <= n -> TYD T.
Proof using ihC ihT ihX.
  intros Hsz. destruct T;
    first [ apply dec_tyErr | apply dec_tyNat | apply dec_tyU
          | apply dec_tyPi | apply dec_tyEl | apply dec_tyGvar | apply dec_tyCTyp | apply dec_tyCTrm
          | apply dec_tyUPi | apply dec_tyCPi | apply dec_tyTPi | apply dec_tySig | apply dec_tyUnit
          | apply dec_tySEq | apply dec_tySEmpty | apply dec_tyId | apply dec_tyEmpty | apply dec_tySum
          | apply dec_tyW | apply dec_tyVec | apply dec_tyFin | apply dec_tyWf | apply dec_tySq
          | apply dec_tyDVec | apply dec_tyIWf | apply dec_tyM ];
    assumption.
Qed.

(** ** Contexts *)

Lemma cx_step Γ : sz_ctx Γ <= n -> CXD Γ.
Proof using ihT ihX.
  intros Hsz G i HG. destruct Γ as [| g | Γ A l].
  - left; exact (wfc_nil _ _ HG).
  - destruct (gctx_var_dec G g) as [Y | N]; [left; exact (wfc_var _ _ _ HG Y) | right; intros H; inversion H; contradiction].
  - destruct (ihX Γ ltac:(szl) G i HG) as [HΓ | N]; [| right; intros H; inversion H; contradiction].
    destruct (ihT A ltac:(szl) G i Γ l (lift_ctx_typeof HΓ)) as [HA | N]; [| right; intros H; inversion H; contradiction].
    destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; inversion H; contradiction].
    left; exact (wfc_ext _ _ _ _ _ HΓ HA Hl).
Qed.

End Step.
