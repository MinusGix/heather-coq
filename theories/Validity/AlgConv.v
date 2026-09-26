(** * The conversion lemma for algorithmic conversion (08:94; M6_DESIGN.md H10)

    An algorithmic derivation over [(G, Γ)] at a type [T] also holds over a
    related [(G2, Γ2)] at an equal type [T2]: [GEq G G2] for the global
    context, [Γ ≅ Γ2] in [G2], and [T2 ≅ T] in [(G2, Γ)]. Neutral terms
    infer an equal type. The source syntax is typed in [(G, Γ)], as for
    soundness. All declarative facts about the target live over the source
    local context [Γ]; [Γ2] only appears in the algorithmic conclusion
    (untyped reduction does not look at contexts).

    This file: the plumbing. *)
From DeLaM.Validity Require Export AlgSound.
From DeLaM.Typing Require Export GConv AlgStruct.

(** ** Lookups along an equivalence of contexts *)

Lemma eqctx_lookup {G i Γ Γ2} : typeof i = i -> [ G ⊢[ i ] Γ ≅ Γ2 ] ->
  forall n T l, in_ctx Γ n T l ->
  exists T2 l2, in_ctx Γ2 n T2 l2 /\ lequiv (gL G) l l2 /\ [ G ; Γ ⊢[ i ] T ≅ T2 @ l ].
Proof.
  intros Hi H. induction H as [G i0 HG | G i0 g HG Hg | G i0 Γ Γ' A A' l l' Hc IH HA HAA Hl];
    intros n T l0 Hin; inversion Hin; subst.
  - pose proof (wfc_ext _ _ _ _ _ (ctx_of_wf_ty Hi HA) HA (lequiv_wf_l _ _ _ Hl)) as HΓA.
    exists A'⟨↑⟩, l'. split; [constructor | split; [exact Hl | eapply wk1_eqty; eassumption]].
  - match goal with Hm : in_ctx Γ _ _ _ |- _ => destruct (IH Hi _ _ _ Hm) as (T2 & l2 & Hin2 & El & ET) end.
    pose proof (wfc_ext _ _ _ _ _ (ctx_of_wf_ty Hi HA) HA (lequiv_wf_l _ _ _ Hl)) as HΓA.
    exists T2⟨↑⟩, l2. split; [now constructor | split; [exact El | eapply wk1_eqty; eassumption]].
Qed.

Lemma eqctx_lookup_r {G i Γ Γ2} : typeof i = i -> [ G ⊢[ i ] Γ ≅ Γ2 ] ->
  forall n T2 l2, in_ctx Γ2 n T2 l2 ->
  exists T l, in_ctx Γ n T l /\ lequiv (gL G) l l2 /\ [ G ; Γ ⊢[ i ] T ≅ T2 @ l ].
Proof.
  intros Hi H. induction H as [G i0 HG | G i0 g HG Hg | G i0 Γ Γ' A A' l l' Hc IH HA HAA Hl];
    intros n T2 l2 Hin; inversion Hin; subst.
  - pose proof (wfc_ext _ _ _ _ _ (ctx_of_wf_ty Hi HA) HA (lequiv_wf_l _ _ _ Hl)) as HΓA.
    exists A⟨↑⟩, l. split; [constructor | split; [exact Hl | eapply wk1_eqty; eassumption]].
  - match goal with Hm : in_ctx Γ' _ _ _ |- _ => destruct (IH Hi _ _ _ Hm) as (T & l1 & Hin1 & El & ET) end.
    pose proof (wfc_ext _ _ _ _ _ (ctx_of_wf_ty Hi HA) HA (lequiv_wf_l _ _ _ Hl)) as HΓA.
    exists T⟨↑⟩, l1. split; [now constructor | split; [exact El | eapply wk1_eqty; eassumption]].
Qed.

(** ** Equivalent contexts under the rules' binders *)

(** Extension by the same entries. *)
Lemma eqctx_ext_refl {G i Γ Γ2 A l} : [ G ⊢[ i ] Γ ≅ Γ2 ] -> [ G ; Γ ⊢[ i ] A @ l ] -> lwf (gL G) l ->
  [ G ⊢[ i ] Γ ,, A @ l ≅ Γ2 ,, A @ l ].
Proof. intros Hc HA Hl. apply eqc_ext; [exact Hc | exact HA | apply eqty_refl, HA | exact (lequiv_refl _ _ Hl)]. Qed.

(** Under a new global binding. *)
Lemma eqctx_gext {G i Γ Γ2 D} : [ ⊢ gext G D ] -> [ G ⊢[ i ] Γ ≅ Γ2 ] -> [ gext G D ⊢[ i ] Γ⟪S⟫ ≅ Γ2⟪S⟫ ].
Proof.
  intros Hg H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ H _ (D :: gΨ G)
                        (gwk_step gwk_id) (le_n _) (gwkwf_step _ _ _ _ (gwkwf_id _)) Hg).
Qed.

(** Under fresh levels and fresh global bindings ([wf_wkc]). *)
Lemma eqctx_wkc G i Γ Γ2 nu Ds : [ G ⊢[ i ] Γ ≅ Γ2 ] ->
  [ ⊢ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ] ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ⊢[ i ]
      wkc nu (length Ds) Γ ≅ wkc nu (length Ds) Γ2 ].
Proof.
  intros H HG. pose proof (uwk_eqctx nu H) as X. unfold gctx_uwk in X; cbn [gL gΨ] in X.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ X _ _ _ (le_n _)
                (gwk_stepn_wf Ds _) HG) as Y.
  unfold wkc. rewrite !(proj1 (proj2 (proj2 gren_ext_all)) _ (ush (length Ds)) (gwk_fn (gwk_stepn (length Ds))))
    by (intros; now rewrite gwk_stepn_fn).
  exact Y.
Qed.

(** Extension by the same entries. *)
Lemma eqctx_cexts {G i Γ Γ2} As : [ G ⊢[ i ] Γ ≅ Γ2 ] -> [ G ; cexts Γ As ⊢[ i ] ] ->
  [ G ⊢[ i ] cexts Γ As ≅ cexts Γ2 As ].
Proof.
  revert Γ Γ2; induction As as [| [A l] As IH]; intros Γ Γ2 H HΓ; cbn [cexts] in *; [exact H|].
  apply IH; [| exact HΓ].
  destruct (wfc_ext_inv (wf_cexts_prefix _ _ _ _ HΓ)) as (_ & HA & Hl).
  exact (eqctx_ext_refl H HA Hl).
Qed.

(** The recursors' scopes. *)
Lemma eqctx_recΓT {G Γ Γ2} : [ G ⊢[ lM ] Γ ≅ Γ2 ] -> [ recGT G ⊢[ lM ] recΓT Γ ≅ recΓT Γ2 ].
Proof.
  intros H. pose proof (eqctx_wf_l (i := lM) eq_refl H) as HΓ.
  pose proof (wf_recΓT _ _ HΓ) as HT. unfold recΓT in *.
  destruct (wfc_ext_inv HT) as (_ & HA & Hl). apply eqctx_ext_refl; [| exact HA | exact Hl].
  exact (eqctx_wkc _ _ _ _ 1 (gdCtx :: nil) H (wf_recGT (ctx_glob _ _ _ HΓ))).
Qed.

Lemma eqctx_recΓt {G Γ Γ2} : [ G ⊢[ lM ] Γ ≅ Γ2 ] -> [ recGt G ⊢[ lM ] recΓt Γ ≅ recΓt Γ2 ].
Proof.
  intros H. pose proof (eqctx_wf_l (i := lM) eq_refl H) as HΓ.
  pose proof (wf_recΓt _ _ HΓ) as HT. unfold recΓt in *.
  destruct (wfc_ext_inv HT) as (_ & HA & Hl). apply eqctx_ext_refl; [| exact HA | exact Hl].
  exact (eqctx_wkc _ _ _ _ 1 (_ :: gdCtx :: nil) H (wf_recGt (ctx_glob _ _ _ HΓ))).
Qed.

Lemma eqctx_brΓ {G Γ Γ2 wT wt l1 l2} k : k < 13 -> [ G ⊢[ lM ] Γ ≅ Γ2 ] ->
  [ brG k G ; brΓ k Γ wT wt l1 l2 ⊢[ lM ] ] ->
  [ brG k G ⊢[ lM ] brΓ k Γ wT wt l1 l2 ≅ brΓ k Γ2 wT wt l1 l2 ].
Proof.
  intros Hk H HB. unfold brΓ in *. apply eqctx_cexts; [| exact HB].
  pose proof (eqctx_wf_l (i := lM) eq_refl H) as HΓ.
  pose proof (wf_brG (ctx_glob _ _ _ HΓ) k Hk) as HG.
  rewrite <- (brDecls_len k Hk). exact (eqctx_wkc _ _ _ _ _ (brDecls k) H HG).
Qed.
