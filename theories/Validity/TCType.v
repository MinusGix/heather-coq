(** * Decidable type checking: types and contexts (M7_DESIGN.md C1, J3.5)

    One step of the induction on size: well-formedness of a type or a
    context is decidable when every judgment about smaller syntax is
    ([IHsz n]). A type's level is read off its former; each premise is
    decided in the order the rule's presuppositions need, and a failure is
    refuted by inversion. *)
From DeLaM.Validity Require Export TCBase.

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
Proof. intros G i Γ k _. right; apply no_ty_err. Qed.

Lemma dec_tyNat : TYD tyNat.
Proof.
  intros G i Γ k HΓ. destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  destruct (lvl_eq_dec (gL G) k lzero) as [Q | Q].
  - left; exact (wft_lvl Q (wft_nat _ _ _ Hv HΓ)).
  - right; intros H; exact (Q (proj2 (inv_ty_nat H))).
Qed.

Lemma dec_tyU l : TYD (tyU l).
Proof.
  intros G i Γ k HΓ. destruct (layer_eq_dec i lV) as [-> | Hv]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_U H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k (lsuc l)) as [Q | Q].
  - left; exact (wft_lvl Q (wft_U _ _ _ _ Hv HΓ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_U H))).
Qed.

Lemma dec_tyPi l l' A B : sz_ty (tyPi l l' A B) <= n -> TYD (tyPi l l' A B).
Proof.
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
Proof.
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
Proof.
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
Proof.
  intros Hsz G i Γ k HΓ. at_M @inv_ty_CTyp. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; intros H; destruct (inv_ty_CTyp H) as ((_ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_CTyp H) as ((_ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k lzero) as [Q | Q].
  - left; exact (wft_lvl Q (wft_CTyp _ _ _ _ HΓ HΔ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_CTyp H))).
Qed.

Lemma dec_tyCTrm Δ A l : sz_ty (tyCTrm Δ A l) <= n -> TYD (tyCTrm Δ A l).
Proof.
  intros Hsz G i Γ k HΓ. at_M @inv_ty_CTrm. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; intros H; destruct (inv_ty_CTrm H) as ((_ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_CTrm H) as ((_ & _ & _ & _ & X) & _); contradiction].
  destruct (ihT A ltac:(szl) G lD Δ l HΔ) as [HA | N]; [| right; intros H; destruct (inv_ty_CTrm H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k lzero) as [Q | Q].
  - left; exact (wft_lvl Q (wft_CTrm _ _ _ _ _ HΓ HΔ HA Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_CTrm H))).
Qed.

Lemma dec_tyUPi m l T : sz_ty (tyUPi m l T) <= n -> TYD (tyUPi m l T).
Proof.
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
Proof.
  intros Hsz G i Γ k HΓ. at_M @inv_ty_cpi. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_cpi H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT T ltac:(szl) (gext G gdCtx) lM Γ⟪S⟫ l (ctx_S (wfg_ctx' HG) HΓ)) as [HT | N];
    [| right; intros H; destruct (inv_ty_cpi H) as ((_ & _ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_cpi _ _ _ _ HΓ Hl HT)).
  - right; intros H; exact (Q (proj2 (inv_ty_cpi H))).
Qed.

Lemma dec_tyTPi Δ l l' T : sz_ty (tyTPi Δ l l' T) <= n -> TYD (tyTPi Δ l l' T).
Proof.
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
Proof.
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
Proof.
  intros G i Γ k HΓ.
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; apply no_ty_V |].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_unit H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_unit _ _ _ _ Hc HΓ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_unit H))).
Qed.

(** Strict equality (M10a): the computing layers only. *)
Lemma dec_tySEq l A a b : sz_ty (tySEq l A a b) <= n -> TYD (tySEq l A a b).
Proof.
  intros Hsz G i Γ k HΓ.
  destruct (compt_dec i) as [Hc | N]; [| right; intros H; destruct (inv_ty_seq H) as ((X & _) & _); contradiction].
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

Lemma dec_tySEmpty l : TYD (tySEmpty l).
Proof.
  intros G i Γ k HΓ.
  destruct (compt_dec i) as [Hc | N]; [| right; intros H; destruct (inv_ty_sempty H) as ((X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; destruct (inv_ty_sempty H) as ((_ & _ & X) & _); contradiction].
  destruct (lvl_eq_dec (gL G) k l) as [Q | Q].
  - left; exact (wft_lvl Q (wft_sempty _ _ _ _ Hc HΓ Hl)).
  - right; intros H; exact (Q (proj2 (inv_ty_sempty H))).
Qed.

Lemma ty_step T : sz_ty T <= n -> TYD T.
Proof.
  intros Hsz. destruct T;
    first [ apply dec_tyErr | apply dec_tyNat | apply dec_tyU
          | apply dec_tyPi | apply dec_tyEl | apply dec_tyGvar | apply dec_tyCTyp | apply dec_tyCTrm
          | apply dec_tyUPi | apply dec_tyCPi | apply dec_tyTPi | apply dec_tySig | apply dec_tyUnit
          | apply dec_tySEq | apply dec_tySEmpty ];
    assumption.
Qed.

(** ** Contexts *)

Lemma cx_step Γ : sz_ctx Γ <= n -> CXD Γ.
Proof.
  intros Hsz G i HG. destruct Γ as [| g | Γ A l].
  - left; exact (wfc_nil _ _ HG).
  - destruct (gctx_var_dec G g) as [Y | N]; [left; exact (wfc_var _ _ _ HG Y) | right; intros H; inversion H; contradiction].
  - destruct (ihX Γ ltac:(szl) G i HG) as [HΓ | N]; [| right; intros H; inversion H; contradiction].
    destruct (ihT A ltac:(szl) G i Γ l (lift_ctx_typeof HΓ)) as [HA | N]; [| right; intros H; inversion H; contradiction].
    destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; inversion H; contradiction].
    left; exact (wfc_ext _ _ _ _ _ HΓ HA Hl).
Qed.

End Step.
