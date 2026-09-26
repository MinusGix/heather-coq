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

(** ** Small facts about the relation *)

Lemma GEq_L {G G2} : GEq G G2 -> gL G2 = gL G.
Proof. intros (_ & _ & HL & _); exact HL. Qed.
Lemma GEq_wf2 {G G2} : GEq G G2 -> [ ⊢ G2 ].
Proof. intros (_ & HG2 & _); exact HG2. Qed.
Lemma GEq_lwf {G G2 l} : GEq G G2 -> lwf (gL G) l -> lwf (gL G2) l.
Proof. intros HE; now rewrite (GEq_L HE). Qed.
Lemma GEq_lequiv {G G2 l l'} : GEq G G2 -> lequiv (gL G) l l' -> lequiv (gL G2) l l'.
Proof. intros HE; now rewrite (GEq_L HE). Qed.

Lemma ac_ctx_sound' {G Δ Δ'} : ac_ctx G Δ Δ' -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ].
Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 ac_sound_all))) _ _ _ H). Qed.

(** ** The statements *)

Definition C_ty G Γ T T' : Prop := forall i G2 Γ2 k k', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_ty G2 Γ2 T T'.
Definition C_tynf G Γ T T' : Prop := forall i G2 Γ2 k k', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_tynf G2 Γ2 T T'.
Definition C_tyne G Γ T T' : Prop := forall i G2 Γ2 k k', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_tyne G2 Γ2 T T'.
Definition C_ctx G Δ Δ' : Prop := forall G2, GEq G G2 ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> ac_ctx G2 Δ Δ'.
Definition C_tm G Γ t t' T : Prop := forall i G2 Γ2 T2 k, compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G2 ; Γ ⊢[ i ] T2 ≅ T @ k ] ->
  ac_tm G2 Γ2 t t' T2.
Definition C_tmnf G Γ w w' W : Prop := forall i G2 Γ2 W2 k, compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] w : W @ k ] -> [ G ; Γ ⊢[ i ] w' : W @ k ] -> [ G2 ; Γ ⊢[ i ] W2 ≅ W @ k ] -> whnf_ty W2 ->
  ac_tmnf G2 Γ2 w w' W2.
Definition C_ne G Γ ν ν' T : Prop := forall i G2 Γ2 k k' A A', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  exists T2, ac_tmne G2 Γ2 ν ν' T2 /\ [ G2 ; Γ ⊢[ i ] T2 ≅ T @ k ].
Definition C_nee G Γ ν ν' W : Prop := forall i G2 Γ2 k k' A A', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  exists W2, ac_tmnee G2 Γ2 ν ν' W2 /\ [ G2 ; Γ ⊢[ i ] W2 ≅ W @ k ].
Definition C_sub G Γ d d' Θ : Prop := forall i G2 Γ2 Θ2, compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Θ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] d : Θ ] -> [ G ; Γ ⊢[ i ] d' : Θ ] -> [ G2 ⊢[ lD ] Θ ≅ Θ2 ] ->
  ac_sub G2 Γ2 d d' Θ2.

(** ** Types *)

Lemma C_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  C_tynf G Γ W W' -> C_ty G Γ T T'.
Proof.
  intros Hr Hr' Hw Hw' IH i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT Hr Hw)) as HW.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT' Hr' Hw')) as HW'.
  eapply act_red; [exact Hr | exact Hr' | exact Hw | exact Hw' | exact (IH i G2 Γ2 k k' Hc HE Hctx HW HW')].
Qed.

Lemma C_actnf_nat {G Γ} : C_tynf G Γ tyNat tyNat.
Proof. red; intros; apply actnf_nat. Qed.
Lemma C_actnf_U {G Γ l l'} : leqv l l' -> C_tynf G Γ (tyU l) (tyU l').
Proof. intros Hl; red; intros; now apply actnf_U. Qed.

Lemma C_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> C_ty G (Γ ,, A @ l1) B B' ->
  C_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA IHB i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_pi HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  apply actnf_pi; [exact H13 | exact H24 | exact (IHA i G2 Γ2 l1 l3 Hc HE Hctx HA HA') |].
  apply (IHB i G2 (Γ2 ,, A @ l1) l2 l4 Hc HE); [| exact HB | exact HB1].
  exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
Qed.

Lemma C_actnf_ne {G Γ V V'} : C_tyne G Γ V V' -> C_tynf G Γ V V'.
Proof. intros IH i G2 Γ2 k k' Hc HE Hctx HT HT'. apply actnf_ne. exact (IH i G2 Γ2 k k' Hc HE Hctx HT HT'). Qed.

Lemma C_actnf_CTyp {G Γ Δ Δ' l l'} : C_ctx G Δ Δ' -> leqv l l' -> C_tynf G Γ (tyCTyp Δ l) (tyCTyp Δ' l').
Proof.
  intros IH Hl i G2 Γ2 k k' Hc HE Hctx HT HT'.
  destruct (inv_ty_CTyp HT) as ((_ & _ & HΔ & _) & _). destruct (inv_ty_CTyp HT') as ((_ & _ & HΔ' & _) & _).
  apply actnf_CTyp; [exact (IH G2 HE HΔ HΔ') | exact Hl].
Qed.

Lemma C_actnf_CTrm {G Γ Δ Δ' T T' l l'} : ac_ctx G Δ Δ' -> C_ctx G Δ Δ' -> C_ty G Δ T T' -> leqv l l' ->
  C_tynf G Γ (tyCTrm Δ T l) (tyCTrm Δ' T' l').
Proof.
  intros Dc IHc IHT Hl i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_CTrm HX) as ((_ & _ & HΔ & HT & W) & _).
  destruct (inv_ty_CTrm HX') as ((_ & _ & HΔ' & HT' & W') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E)) as HT1.
  apply actnf_CTrm; [exact (IHc G2 HE HΔ HΔ') | | exact Hl].
  exact (IHT lD G2 Δ l l compt_D HE (eqc_refl _ _ _ (gconv_ctx HE compt_D HΔ)) HT HT1).
Qed.

Lemma C_actnf_upi {G Γ n l l' T T'} : leqv l l' -> C_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  C_tynf G Γ (tyUPi n l T) (tyUPi n l' T').
Proof.
  intros Hl IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_upi HX) as ((-> & _ & _ & _ & HT) & _). destruct (inv_ty_upi HX') as ((_ & _ & _ & _ & HT') & _).
  apply actnf_upi; [exact Hl |].
  exact (IH lM (gctx_uwk n G2) Γ2⟨ush n⟩ᵤ l l' compt_M (GEq_uwk n HE) (uwk_eqctx n Hctx) HT HT').
Qed.

Lemma C_actnf_cpi {G Γ l l' T T'} : leqv l l' -> C_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  C_tynf G Γ (tyCPi l T) (tyCPi l' T').
Proof.
  intros Hl IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_cpi HX) as ((-> & _ & _ & HT) & _). destruct (inv_ty_cpi HX') as ((_ & _ & _ & HT') & _).
  pose proof (GEq_ext_same HE (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT))) as HE1.
  apply actnf_cpi; [exact Hl |].
  exact (IH lM _ Γ2⟪S⟫ l l' compt_M HE1 (eqctx_gext (GEq_wf2 HE1) Hctx) HT HT').
Qed.

Lemma C_actnf_tpi {G Γ Δ Δ' l1 l2 l3 l4 T T'} : ac_ctx G Δ Δ' -> C_ctx G Δ Δ' -> leqv l1 l3 -> leqv l2 l4 ->
  C_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T' -> C_tynf G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ' l3 l4 T').
Proof.
  intros Dc IHc H13 H24 IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_tpi HX) as ((-> & HΓ & HΔ & W1 & W2 & HT) & _).
  destruct (inv_ty_tpi HX') as ((_ & _ & HΔ' & W3 & W4 & HT') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HGD : [ ⊢ gext G (gdTy Δ lD l1) ]) by (apply wfg_ty; auto).
  pose proof (gbind_obj_ty (lle_refl lD) ltac:(discriminate) HGD Ec E13) as Ho.
  pose proof (gbind_ty HG HGD Ho HT') as HT1.
  pose proof (GEq_ext_same HE HGD) as HE1.
  apply actnf_tpi; [exact (IHc G2 HE HΔ HΔ') | exact H13 | exact H24 |].
  exact (IH lM _ Γ2⟪S⟫ l2 l4 compt_M HE1 (eqctx_gext (GEq_wf2 HE1) Hctx) HT HT1).
Qed.

Lemma C_actne_gvar {G Γ U Δ i' l d d'} : in_gctx (gΨ G) U (gdTy Δ i' l) -> C_sub G Γ d d' Δ ->
  C_tyne G Γ (tyGvar U d) (tyGvar U d').
Proof.
  intros Hin IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_gvar HX) as (Δ0 & i0 & l0 & (Hv & HΓ & Hin0 & Hle & Ht & Hn & He) & _).
  destruct (inv_ty_gvar HX') as (Δ1 & i1 & l1 & (_ & _ & Hin1 & _ & Ht' & Hn' & He') & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <-.
  rewrite Hi in HΓ.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (HΔ & _).
  pose proof (lift_ctx HΔ (lle_D_compt _ Hc)) as HΔi.
  destruct HE as (HG & HG2 & HL & Hl). destruct (Hl _ _ Hin) as (D2 & Hin2 & HD2).
  destruct D2 as [| Δ2 i2 l2 | ]; cbn in HD2; try contradiction. destruct HD2 as (-> & _ & _ & HΔΔ).
  eapply actne_gvar; [exact Hin2 |].
  exact (IH i G2 Γ2 Δ2 Hc (conj HG (conj HG2 (conj HL Hl))) Hctx HΔi
           (lsub_wf_prem Hi HΓ Ht Hn He) (lsub_wf_prem Hi HΓ Ht' Hn' He') HΔΔ).
Qed.

Lemma C_actne_El {G Γ l l' ν ν' W} : leqv l l' -> C_nee G Γ ν ν' W -> C_tyne G Γ (tyEl l ν) (tyEl l' ν').
Proof.
  intros Hl IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_El HX) as ((_ & _ & Hν) & _). destruct (inv_ty_El HX') as ((_ & _ & Hν') & _).
  destruct (IH i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν') as (W2 & X & _).
  eapply actne_El; [exact Hl | exact X].
Qed.

(** ** Local contexts (at D) *)

Lemma C_acc_nil {G} : C_ctx G cnil cnil.
Proof. red; intros; apply acc_nil. Qed.
Lemma C_acc_var {G g} : C_ctx G (cvar g) (cvar g).
Proof. red; intros; apply acc_var. Qed.

Lemma C_acc_ext {G Γ Γ' A A' l l'} : ac_ctx G Γ Γ' -> C_ctx G Γ Γ' -> C_ty G Γ A A' -> leqv l l' ->
  C_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof.
  intros Dc IHc IHA Hl G2 HE H H'.
  destruct (wfc_ext_inv H) as (HΓ & HA & W). destruct (wfc_ext_inv H') as (HΓ' & HA' & W').
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ctx_sound' Dc HΓ HΓ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HA' (lequiv_sym _ _ _ E)) as HA1.
  apply acc_ext; [exact (IHc G2 HE HΓ HΓ') | | exact Hl].
  exact (IHA lD G2 Γ l l compt_D HE (eqc_refl _ _ _ (gconv_ctx HE compt_D HΓ)) HA HA1).
Qed.

(** ** Terms *)

(** Normalization of a typed type, with its equation. *)
Lemma tgt_whnf {G i Γ T k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] ->
  exists W, reds_ty T W /\ whnf_ty W /\ [ G ; Γ ⊢[ i ] T ≅ W @ k ].
Proof.
  intros Hc HT. destruct Hc as [-> | ->].
  - destruct (decl_whnf_tyred HT) as (W & HW & Hw).
    exists W; exact (conj (tyred_red _ _ _ _ _ _ HW) (conj Hw (tyred_eq _ _ _ _ _ _ HW))).
  - destruct (declM_whnf_tyred HT) as (W & HW & Hw).
    exists W; exact (conj (tyred_red _ _ _ _ _ _ HW) (conj Hw (tyred_eq _ _ _ _ _ _ HW))).
Qed.

(** A whnf type equal to a positive one is positive. *)
Lemma posty_head W W2 : posty W -> whnf_ty W2 -> ty_head W2 = ty_head W -> posty W2.
Proof.
  intros Hp Hw2 E. destruct Hp;
    try match goal with Hn : whne_ty ?V |- _ => rewrite (whne_ty_head V Hn) in E end;
    destruct W2; cbn in E; try discriminate;
    first [ apply posty_nat | apply posty_U | apply posty_CTyp | apply posty_CTrm
          | apply posty_ne; inversion Hw2; subst; first [assumption | constructor] ].
Qed.

Lemma head_pi W : ty_head W = 3 -> exists m m' A B, W = tyPi m m' A B.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_upi W : ty_head W = 6 -> exists n m T, W = tyUPi n m T.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_cpi W : ty_head W = 7 -> exists m T, W = tyCPi m T.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_tpi W : ty_head W = 8 -> exists Δ m m' T, W = tyTPi Δ m m' T.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.

(** The head of the new type, from its equation with the old. *)
Ltac new_head Hc EW Hw2 W :=
  let E := fresh "Eh" in
  pose proof (decl_head_c Hc EW Hw2 ltac:(auto with whnf)) as E; cbn [ty_head] in E;
  destruct W; cbn [ty_head] in E; try discriminate; clear E.

Lemma C_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> C_tmnf G Γ w w' W -> C_tm G Γ t t' T.
Proof.
  intros HrT HwT Hr Hr' Hw Hw' IH i G2 Γ2 T2 k Hc HE Hctx Ht Ht' ET2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (red_ty_sound Hc (wf_tm_ty Hi Ht) HrT HwT) as ET.
  pose proof (red_tm_sound Hc Ht Hr Hw) as Et. pose proof (red_tm_sound Hc Ht' Hr' Hw') as Et'.
  assert (EW : [ G ; Γ ⊢[ typeof i ] W ≅ T @ k ]) by (rewrite Hi; exact (eqty_sym _ _ _ _ _ _ ET)).
  destruct (tgt_whnf Hc (eqty_wf_l Hi ET2)) as (W2 & HrT2 & HwT2 & ET2W).
  assert (EW2 : [ G2 ; Γ ⊢[ i ] W2 ≅ W @ k ]).
  { eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ ET2W) |].
    eapply eqty_trans; [exact ET2 | exact (gconv_eqty HE Hi ET)]. }
  eapply actm_red; [exact HrT2 | exact HwT2 | exact Hr | exact Hr' | exact Hw | exact Hw' |].
  exact (IH i G2 Γ2 W2 k Hc HE Hctx (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Et) EW)
           (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Et') EW) EW2 HwT2).
Qed.

Lemma C_actmnf_code_nat {G Γ l} : C_tmnf G Γ tmNat tmNat (tyU l).
Proof. red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2. new_head Hc EW Hw2 W2. apply actmnf_code_nat. Qed.

Lemma C_actmnf_code_U {G Γ l k k'} : leqv k k' -> C_tmnf G Γ (tmU k) (tmU k') (tyU l).
Proof.
  intros Hl; red; intros i G2 Γ2 W2 kk Hc HE Hctx Ht Ht' EW Hw2. new_head Hc EW Hw2 W2.
  apply actmnf_code_U; exact Hl.
Qed.

Lemma C_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> C_tm G Γ s s' (tyU l1) -> C_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  C_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs IHt i G2 Γ2 W2 k Hc HE Hctx Hx Hx' EW Hw2. pose proof (compt_typeof_self _ Hc) as Hi.
  new_head Hc EW Hw2 W2.
  destruct (inv_code_pi Hi Hx) as ((Hv & W1 & W2 & Hs & Ht) & _).
  destruct (inv_code_pi Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (Es' : [ G ; Γ ⊢[ i ] s' ≅ s : tyU l3 @ lsuc l3 ]).
  { eapply eqtm_lconv; [| exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13))].
    eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ Es) | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EU1)]. }
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (apply eqty_El; [exact Hv | exact (lequiv_sym _ _ _ E13) | exact Es']).
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  pose proof (stab_tm Hi EEl (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  apply actmnf_code_pi; [exact H13 | exact H24 | |].
  - exact (IHs i G2 Γ2 (tyU l1) (lsuc l1) Hc HE Hctx Hs Hs1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs)))).
  - apply (IHt i G2 (Γ2 ,, tyEl l1 s @ l1) (tyU l2) (lsuc l2) Hc HE); [| exact Ht | exact Ht2 |].
    + exact (eqctx_ext_refl Hctx (gconv_ty HE HEl) (GEq_lwf HE W1)).
    + exact (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht))).
Qed.

Lemma C_actmnf_zero {G Γ} : C_tmnf G Γ zero zero tyNat.
Proof. red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2. new_head Hc EW Hw2 W2. apply actmnf_zero. Qed.

Lemma C_actmnf_succ {G Γ t t'} : C_tm G Γ t t' tyNat -> C_tmnf G Γ (succ t) (succ t') tyNat.
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hx Hx' EW Hw2. pose proof (compt_typeof_self _ Hc) as Hi.
  new_head Hc EW Hw2 W2.
  destruct (inv_succ Hi Hx) as ((Hv & Ht) & _). destruct (inv_succ Hi Hx') as ((_ & Ht') & _).
  apply actmnf_succ.
  exact (IH i G2 Γ2 tyNat lzero Hc HE Hctx Ht Ht' (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht)))).
Qed.

Lemma C_actmnf_ne {G Γ ν ν' W W'} : posty W -> C_nee G Γ ν ν' W' -> C_tmnf G Γ ν ν' W.
Proof.
  intros Hp IH i G2 Γ2 W2 k Hc HE Hctx Hν Hν' EW Hw2.
  pose proof (compt_typeof_self _ Hc) as Hi.
  assert (HwW : whnf_ty W) by (destruct Hp; auto with whnf).
  pose proof (decl_head_c Hc EW Hw2 HwW) as Eh.
  destruct (IH i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν') as (W3 & X & _).
  eapply actmnf_ne; [exact (posty_head _ _ Hp Hw2 Eh) | exact X].
Qed.

Lemma C_actmnf_eta {G Γ l l' A B w w'} :
  C_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  C_tmnf G Γ w w' (tyPi l l' A B).
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (head_pi W2 (decl_head_c Hc EW Hw2 (whnf_tyPi _ _ _ _))) as (m & m' & A2 & B2 & ->).
  destruct (inv_ty_pi (wf_tm_ty Hi Hw)) as ((Hv & W1 & W3 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  destruct (pi_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (Em & Em' & EA & EB).
  assert (Hctx' : [ G2 ⊢[ i ] Γ ,, A @ l ≅ Γ2 ,, A2 @ m ])
    by (apply eqc_ext; [exact Hctx | exact (gconv_ty HE HA) | exact EA | exact (lequiv_sym _ _ _ Em)]).
  pose proof (IH i G2 (Γ2 ,, A2 @ m) B2 l' Hc HE Hctx' (pre_eta_body Hi Hv W1 W3 HA HB Hw1)
                (pre_eta_body Hi Hv W1 W3 HA HB Hw1') (eqty_sym _ _ _ _ _ _ EB)) as X.
  apply actmnf_eta.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_spa_all)))) _ _ _ _ _ X _ _
           (spa_app _ _ _ _ _ _ _ _ _ _ _ (spa_refl _)) (spa_app _ _ _ _ _ _ _ _ _ _ _ (spa_refl _))).
Qed.

Lemma wfg_gext {G D} : [ ⊢ G ] -> decl_ok G D -> decl_layer D -> [ ⊢ gext G D ].
Proof. destruct G; apply wfg_cons. Qed.

Lemma C_actmnf_ueta {G Γ n l T w w'} :
  C_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  C_tmnf G Γ w w' (tyUPi n l T).
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_upi (wf_tm_ty Hi Hw)) as ((-> & HΓ & Hn & W & HT) & Hk).
  destruct (head_upi W2 (decl_head_c Hc EW Hw2 (whnf_tyUPi _ _ _))) as (n2 & m & T2 & ->).
  destruct (declM_upi_inj (eqty_sym _ _ _ _ _ _ EW)) as (-> & _ & ET).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  apply actmnf_ueta.
  exact (IH lM (gctx_uwk n G2) Γ2⟨ush n⟩ᵤ T2 l compt_M (GEq_uwk n HE) (uwk_eqctx n Hctx)
           (wf_ueta_body W HT Hw1) (wf_ueta_body W HT Hw1') (eqty_sym _ _ _ _ _ _ ET)).
Qed.

Lemma C_actmnf_ceta {G Γ l T w w'} :
  C_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T -> C_tmnf G Γ w w' (tyCPi l T).
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_cpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & W & HT) & Hk).
  destruct (head_cpi W2 (decl_head_c Hc EW Hw2 (whnf_tyCPi _ _))) as (m & T2 & ->).
  destruct (declM_cpi_inj (eqty_sym _ _ _ _ _ _ EW)) as (_ & ET).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (GEq_ext_same HE (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT))) as HE1.
  apply actmnf_ceta.
  exact (IH lM _ Γ2⟪S⟫ T2 l compt_M HE1 (eqctx_gext (GEq_wf2 HE1) Hctx)
           (wf_ceta_body W HT Hw1) (wf_ceta_body W HT Hw1') (eqty_sym _ _ _ _ _ _ ET)).
Qed.

Lemma C_actmnf_teta {G Γ Δ l l' T w w'} :
  C_tm (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  C_tmnf G Γ w w' (tyTPi Δ l l' T).
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_tpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & HΔ & W1 & W3 & HT) & Hk).
  destruct (head_tpi W2 (decl_head_c Hc EW Hw2 (whnf_tyTPi _ _ _ _))) as (Δ2 & m & m' & T2 & ->).
  destruct (declM_tpi_inj (eqty_sym _ _ _ _ _ _ EW)) as (HΔΔ & Em & _ & ET).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT)) as HGD.
  pose proof (GEq_ext_same HE HGD) as HE0.
  pose proof (GEq_wf2 HE) as HG2.
  assert (HGD2 : [ ⊢ gext G2 (gdTy Δ2 lD m) ]).
  { apply (wfg_gext HG2); [split; [exact (eqctx_wf_r (i := lD) eq_refl HΔΔ) | exact (lequiv_wf_l _ _ _ Em)]
                         | right; reflexivity]. }
  assert (Hd : gdecl_eq G2 (gdTy Δ lD l) (gdTy Δ2 lD m))
    by exact (conj eq_refl (conj (or_intror eq_refl) (conj (lequiv_sym _ _ _ Em) HΔΔ))).
  pose proof (GEq_ext HE HGD HGD2 Hd) as HE1.
  pose proof (GEq_ext (GEq_refl _ HG2) (GEq_wf2 HE0) HGD2 Hd) as HE2.
  apply actmnf_teta.
  exact (IH lM _ Γ2⟪S⟫ T2 l' compt_M HE1 (eqctx_gext HGD2 Hctx)
           (wf_teta_body HΔ W1 W3 HT Hw1) (wf_teta_body HΔ W1 W3 HT Hw1')
           (eqty_sym _ _ _ _ _ _ (gconv_eqty HE2 eq_refl ET))).
Qed.

Lemma C_actmnf_boxT {G Γ Δ l T T'} : ty_leq T T' -> C_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ l).
Proof.
  intros H; red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2. new_head Hc EW Hw2 W2.
  apply actmnf_boxT; exact H.
Qed.

Lemma C_actmnf_boxt {G Γ Δ A l t t'} : tm_leq t t' -> C_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ A l).
Proof.
  intros H; red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2. new_head Hc EW Hw2 W2.
  apply actmnf_boxt; exact H.
Qed.

(** ** Neutral terms *)

Lemma lvl_eq_G2 {G G2 k l} : GEq G G2 -> lvl_eq (gL G) k l -> lvl_eq (gL G2) k l.
Proof. intros HE; now rewrite (GEq_L HE). Qed.

Lemma gconv_lsub {G G2 i Γ d Θ} : GEq G G2 -> compt i -> [ G ; Γ ⊢[ i ] d : Θ ] -> [ G2 ; Γ ⊢[ i ] d : Θ ].
Proof.
  intros HE Hc [Hx Hn Ht Hv]. pose proof (compt_typeof_self _ Hc) as Hi.
  constructor; [rewrite Hi in Hx |- *; exact (gconv_ctx HE Hc Hx) | exact Hn | exact Ht |].
  intros n T l Hin. exact (gconv_tm HE Hi (Hv _ _ _ Hin)).
Qed.

Lemma ac_ne_sound' {G Γ ν ν' T i k k' A A'} : ac_tmne G Γ ν ν' T -> compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  [ G ; Γ ⊢[ i ] A ≅ T @ k ] /\ [ G ; Γ ⊢[ i ] A' ≅ T @ k' ] /\ [ G ; Γ ⊢[ i ] ν ≅ ν' : A @ k ].
Proof. intros D; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all)))))) _ _ _ _ _ D _ _ _ _ _). Qed.

(** An unchanged inferred type is related to itself in the target. *)
Lemma ne_refl {G Γ ν ν' T i G2 k k' A A'} : ac_tmne G Γ ν ν' T -> compt i -> GEq G G2 ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> [ G2 ; Γ ⊢[ i ] T ≅ T @ k ].
Proof.
  intros D Hc HE Hν Hν'. destruct (ac_ne_sound' D Hc Hν Hν') as (EA & _ & _).
  exact (eqty_refl _ _ _ _ _ (gconv_ty HE (eqty_wf_r (compt_typeof_self _ Hc) EA))).
Qed.

Lemma ac_tmnee_whnf {G Γ ν ν' W} : ac_tmnee G Γ ν ν' W -> whnf_ty W.
Proof. intros H; inversion H; assumption. Qed.

Lemma C_actmnee_red {G Γ ν ν' T W} : ac_tmne G Γ ν ν' T -> C_ne G Γ ν ν' T -> reds_ty T W -> whnf_ty W ->
  C_nee G Γ ν ν' W.
Proof.
  intros D IH Hr Hw i G2 Γ2 k k' A A' Hc HE Hctx Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (IH i G2 Γ2 k k' A A' Hc HE Hctx Hν Hν') as (T2 & X & ET2).
  destruct (ac_ne_sound' D Hc Hν Hν') as (EA & _ & _).
  pose proof (red_ty_sound Hc (eqty_wf_r Hi EA) Hr Hw) as ET.
  destruct (tgt_whnf Hc (eqty_wf_l Hi ET2)) as (W2 & Hr2 & Hw2 & EW2).
  exists W2. split; [exact (actmnee_red _ _ _ _ _ _ X Hr2 Hw2) |].
  eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ EW2) |].
  eapply eqty_trans; [exact ET2 | exact (gconv_eqty HE Hi ET)].
Qed.

Lemma C_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> ac_tm G Γ (llk d n) (llk d' n) A[d]) ->
  (forall n A k, in_ctx Θ n A k -> C_tm G Γ (llk d n) (llk d' n) A[d]) -> C_sub G Γ d d' Θ.
Proof.
  intros D IH i G2 Γ2 Θ2 Hc HE Hctx HΘ Hd Hd' HΘΘ. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all))))))) _ _ _ _ _
                (acs_pt _ _ _ _ _ D) i Hc HΘ Hd Hd') as (_ & _ & Edd).
  apply acs_pt. intros n A2 k2 Hin2.
  destruct (eqctx_lookup_r (i := lD) eq_refl HΘΘ _ _ _ Hin2) as (A & k & Hin & _ & EA).
  apply (IH n A k Hin i G2 Γ2 A2[d] k Hc HE Hctx (lsw_var _ _ _ _ _ Hd _ _ _ Hin)
           (eqtm_wf_r Hi (Edd _ _ _ Hin))).
  exact (eqty_subst Hi (lift_eqty (eqty_sym _ _ _ _ _ _ EA) (lle_D_compt _ Hc)) (gconv_lsub HE Hc Hd)).
Qed.

Lemma C_actmne_var {G Γ n T l} : in_ctx Γ n T l -> C_ne G Γ (var n) (var n) T.
Proof.
  intros Hin i G2 Γ2 k k' X X' Hc HE Hctx Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_var Hi Hν) as (T0 & l0 & (_ & Hin0) & Hk & _).
  destruct (in_ctx_det Hin Hin0) as [<- <-].
  destruct (eqctx_lookup Hi Hctx _ _ _ Hin) as (T2 & l2 & Hin2 & _ & ET).
  exists T2. split; [exact (actmne_var _ _ _ _ _ Hin2) |].
  exact (eqty_sym _ _ _ _ _ _ (lvl_eq_eqty (lvl_eq_G2 HE Hk) ET)).
Qed.

Lemma C_actmne_gvar {G Γ u Δ i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ i' T l) -> C_sub G Γ d d' Δ ->
  C_ne G Γ (gvar u d) (gvar u d') T[d].
Proof.
  intros Hin IH i G2 Γ2 k k' X X' Hc HE Hctx Hν Hν'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_gvar Hi Hν) as (Δ0 & i0 & T0 & l0 & (HΓ & Hin0 & Hle & Ht & Hn & He) & Hk & _).
  destruct (inv_gvar Hi Hν') as (Δ1 & i1 & T1 & l1 & (_ & Hin1 & _ & Ht' & Hn' & He') & _ & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <- <-.
  pose proof HΓ as HΓi. rewrite Hi in HΓi.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓi) Hin) as (HΔ & _).
  pose proof (lift_ctx HΔ (lle_D_compt _ Hc)) as HΔi.
  pose proof (lsub_wf_prem Hi HΓi Ht Hn He) as Hd.
  pose proof HE as (_ & _ & _ & Hl). destruct (Hl _ _ Hin) as (D2 & Hin2 & HD2).
  destruct D2 as [| | Δ2 i2 T2 l2]; cbn in HD2; try contradiction.
  destruct HD2 as (-> & _ & _ & HΔΔ & ET).
  exists T2[d]. split.
  - eapply actmne_gvar; [exact Hin2 |].
    exact (IH i G2 Γ2 Δ2 Hc HE Hctx HΔi Hd (lsub_wf_prem Hi HΓi Ht' Hn' He') HΔΔ).
  - apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
    exact (eqty_subst Hi (lift_eqty (eqty_sym _ _ _ _ _ _ ET) (lle_D_compt _ Hc)) (gconv_lsub HE Hc Hd)).
Qed.

Lemma C_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  ac_ty G (Γ ,, tyNat @ lzero) M M' -> C_ty G (Γ ,, tyNat @ lzero) M M' ->
  ac_tm G Γ s s' M[lsingle zero] -> C_tm G Γ s s' M[lsingle zero] ->
  ac_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> C_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof.
  intros Hl DM IHM Ds IHs Dz IHz Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_natrec Hi Hx) as ((Hv & Wl & HM & Hs & Hz & Hν) & Hk & HX).
  destruct (inv_natrec Hi Hx') as ((_ & Wl' & HM' & Hs' & Hz' & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as E.
  pose proof (ac_ty_sound Hc DM HM (wft_lconv _ _ _ _ _ _ HM' E)) as EM.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  assert (HN : [ G ; Γ ⊢[ i ] tyNat @ lzero ]) by (apply wft_nat; [exact Hv | rewrite Hi; exact HΓ]).
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HN | exact I]).
  assert (H0 : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; [exact Hv | rewrite Hi; exact HΓ]).
  pose proof (eqty_single Hi EM H0) as EM0.
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E] | rewrite Hi; exact EM0]).
  assert (HΓM : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] ]) by (apply wfc_ext; assumption).
  assert (EM' : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' ≅ M @ l' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM) | exact (lequiv_sym _ _ _ E)]).
  pose proof (stab_tm Hi EM' (lequiv_sym _ _ _ E) HΓM Hz') as Hz1.
  pose proof (eqty_subst Hi EM (lsub_wf_lsucc Hi Hv HΓM)) as EMs.
  assert (Hz2 : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hz1 | exact E] | rewrite Hi; exact EMs]).
  assert (HctxN : [ G2 ⊢[ i ] Γ ,, tyNat @ lzero ≅ Γ2 ,, tyNat @ lzero ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HN) I).
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν') as (W2 & Xν & _).
  exists M[lsingle ν]. split.
  - apply (actmne_natrec _ _ _ _ _ _ _ _ _ _ _ _ W2 Hl).
    + exact (IHM i G2 _ l l Hc HE HctxN HM (wft_lconv _ _ _ _ _ _ HM' E)).
    + exact (IHs i G2 Γ2 _ l Hc HE Hctx Hs Hs1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs)))).
    + apply (IHz i G2 _ _ l Hc HE (eqctx_ext_refl HctxN (gconv_ty HE HM) (GEq_lwf HE Wl)) Hz Hz2).
      exact (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hz))).
    + exact Xν.
  - exact (ne_refl (actmne_natrec _ _ _ _ _ _ _ _ _ _ _ _ _ Hl DM Ds Dz Dν) Hc HE Hx Hx').
Qed.

Lemma ac_nee_sound' {G Γ ν ν' W i k k' A A'} : ac_tmnee G Γ ν ν' W -> compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  [ G ; Γ ⊢[ i ] A ≅ W @ k ] /\ [ G ; Γ ⊢[ i ] A' ≅ W @ k' ] /\ [ G ; Γ ⊢[ i ] ν ≅ ν' : A @ k ].
Proof.
  intros D; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all))))))) _ _ _ _ _ D _ _ _ _ _).
Qed.

Lemma C_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> C_nee G Γ ν ν' (tyPi m m' A0 B0) ->
  ac_tm G Γ s s' A0 -> C_tm G Γ s s' A0 ->
  C_ne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof.
  intros Dν IHν Ds IHs i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν & Hs) & Hk & HX).
  destruct (inv_app Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν' & Hs') & Hk' & HX').
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (pi_inj_c Hc E0) as (Em1 & Em2 & EA0 & EB0).
  destruct (pi_inj_c Hc E1) as (Em3 & Em4 & EA1 & EB1).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em1) Em3) as E13.
  assert (EA : [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ]).
  { eapply eqty_trans; [exact EA0 |]. apply eqty_sym.
    eapply eqty_lconv; [exact EA1 | exact E13]. }
  assert (Hs0 : [ G ; Γ ⊢[ i ] s : A0 @ l1 ])
    by (eapply wf_conv; [exact Hs | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA0)]).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : A @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E13] | rewrite Hi; exact EA]).
  assert (Hs1' : [ G ; Γ ⊢[ i ] s' : A0 @ l1 ])
    by (eapply wf_conv; [exact Hs1 | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA0)]).
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν') as (W & Xν & EW).
  destruct (head_pi W (decl_head_c Hc EW (ac_tmnee_whnf Xν) (whnf_tyPi _ _ _ _))) as (n1 & n2 & A2 & B2 & ->).
  destruct (pi_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (_ & En2 & EA2 & EB2).
  pose proof (GEq_lequiv HE Em1) as Em1'. pose proof (GEq_lequiv HE Em2) as Em2'.
  assert (ET : [ G2 ; Γ ⊢[ i ] A2 ≅ A0 @ l1 ])
    by exact (eqty_sym _ _ _ _ _ _ (eqty_lconv _ _ _ _ _ _ _ EA2 (lequiv_sym _ _ _ Em1'))).
  pose proof (IHs i G2 Γ2 A2 l1 Hc HE Hctx Hs0 Hs1' ET) as Xs.
  exists B2[lsingle s]. split; [eapply actmne_app; [exact Xν | exact Xs] |].
  assert (Hs0m : [ G2 ; Γ ⊢[ i ] s : A0 @ m ]) by exact (gconv_tm HE Hi (wf_lconv _ _ _ _ _ _ _ Hs0 Em1)).
  pose proof (eqty_sym _ _ _ _ _ _ (eqty_single Hi EB2 Hs0m)) as EBs.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
  exact (eqty_lconv _ _ _ _ _ _ _ EBs (lequiv_sym _ _ _ Em2')).
Qed.

Lemma C_actmne_uapp {G Γ n l T ν ν' ls ls'} :
  ac_tmnee G Γ ν ν' (tyUPi n l T) -> C_nee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' -> C_ne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros Dν IHν Hn Hls i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_uapp Hi Hx) as (n0 & l0 & T0 & (-> & W0 & HT0 & Hlen & Hw & Hν) & Hk & HX).
  destruct (inv_uapp Hi Hx') as (n1 & l1 & T1 & (_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & _ & _).
  destruct (declM_upi_inj E0) as (-> & El0 & _).
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν') as (W & Xν & EW).
  destruct (head_upi W (decl_head_c compt_M EW (ac_tmnee_whnf Xν) (whnf_tyUPi _ _ _))) as (n2 & m & T2 & ->).
  destruct (declM_upi_inj (eqty_sym _ _ _ _ _ _ EW)) as (-> & _ & ET).
  exists T2[uext ls lvar]ᵤ. split; [eapply actmne_uapp; [exact Xν | exact Hn | exact Hls] |].
  subst n0.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  assert (Hw2 : Forall (lwf (gL G2)) ls) by (rewrite (GEq_L HE); exact Hw).
  pose proof (uinst_eqty (GEq_wf2 HE) (wf_ctx_dnf HΓ) Hw2 (eqty_sym _ _ _ _ _ _ ET)) as I.
  assert (Hok : usub_ok (uext ls lvar) (gL G) (length ls + gL G))
    by (apply usub_ok_uext; [exact Hw | apply usub_ok_id]).
  pose proof (lequiv_lvsubst _ _ _ _ _ Hok El0) as E.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)). exact (eqty_lconv _ _ _ _ _ _ _ I (GEq_lequiv HE E)).
Qed.

Lemma C_actmne_capp {G Γ l T ν ν' Δ Δ'} :
  ac_tmnee G Γ ν ν' (tyCPi l T) -> C_nee G Γ ν ν' (tyCPi l T) -> C_ctx G Δ Δ' ->
  C_ne G Γ (capp ν Δ) (capp ν' Δ') T⦃gsingle (GCtx Δ)⦄.
Proof.
  intros Dν IHν IHc i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_capp Hi Hx) as (l0 & T0 & (-> & W0 & HT0 & HΔ & Hν & _) & Hk & HX).
  destruct (inv_capp Hi Hx') as (l1 & T1 & (_ & W1 & HT1 & HΔ' & Hν' & _) & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & _ & _).
  destruct (declM_cpi_inj E0) as (El0 & _).
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν') as (W & Xν & EW).
  destruct (head_cpi W (decl_head_c compt_M EW (ac_tmnee_whnf Xν) (whnf_tyCPi _ _))) as (m & T2 & ->).
  destruct (declM_cpi_inj (eqty_sym _ _ _ _ _ _ EW)) as (_ & ET).
  exists T2⦃gsingle (GCtx Δ)⦄. split; [eapply actmne_capp; [exact Xν | exact (IHc G2 HE HΔ HΔ')] |].
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  pose proof (inst_c_eqty (gconv_ctx HE compt_M HΓ) (gconv_ctx HE compt_D HΔ) (eqty_sym _ _ _ _ _ _ ET)) as I.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
  exact (eqty_lconv _ _ _ _ _ _ _ I (lequiv_sym _ _ _ (GEq_lequiv HE El0))).
Qed.

Lemma C_actmne_tapp {G Γ Δ l l' T ν ν' A A'} :
  ac_tmnee G Γ ν ν' (tyTPi Δ l l' T) -> C_nee G Γ ν ν' (tyTPi Δ l l' T) -> C_ty G Δ A A' ->
  C_ne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof.
  intros Dν IHν IHA i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T0 & (-> & Hν & HΔ0 & W0 & W0' & HT0 & HA & _) & Hk & HX).
  destruct (inv_tapp Hi Hx') as (Δ1 & l1 & l1' & T1 & (_ & Hν' & HΔ1 & W1 & W1' & HT1 & HA' & _) & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & E1 & _).
  destruct (declM_tpi_inj E0) as (Ec0 & El0 & El0' & _).
  destruct (declM_tpi_inj E1) as (Ec1 & El1 & _ & _).
  pose proof (decl_ty_ctxconv_D Ec0 HA (lequiv_refl _ _ W0)) as HAΔ.
  pose proof (decl_ty_ctxconv_D Ec1 HA' (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ El1) El0)) as HA'Δ.
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν') as (W & Xν & EW).
  destruct (head_tpi W (decl_head_c compt_M EW (ac_tmnee_whnf Xν) (whnf_tyTPi _ _ _ _))) as (Δ2 & m & m' & T2 & ->).
  destruct (declM_tpi_inj (eqty_sym _ _ _ _ _ _ EW)) as (HΔΔ2 & _ & _ & ET).
  exists T2⦃gsingle (GTy A)⦄. split.
  { eapply actmne_tapp; [exact Xν | exact (IHA lD G2 Δ2 l0 l0 compt_D HE HΔΔ2 HAΔ HA'Δ)]. }
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  pose proof (gconv_ty HE (wft_lconv _ _ _ _ _ _ HAΔ El0)) as HAl.
  pose proof (inst_t_eqty (gconv_ctx HE compt_M HΓ) HAl (eqty_sym _ _ _ _ _ _ ET)) as I.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
  exact (eqty_lconv _ _ _ _ _ _ _ I (lequiv_sym _ _ _ (GEq_lequiv HE El0'))).
Qed.
