(** * Conversion of the global context (M6_DESIGN.md H10)

    Two global contexts are related ([GEq G G2]) when they have the same
    level context and their declarations are pointwise equal in [G2]:
    contexts equivalent at P, types equal, levels equivalent. Declarative
    judgments over [G] then hold over [G2], unchanged: substitute each
    global variable by its identity object ([id_obj]), which is typed in
    [G2] by conversion and acts as the identity on typed syntax
    ([equiv_gsubst]). The top-binding case is [gbind] (AlgPrereq). *)
From DeLaM.Typing Require Export CtxConv GStatic.

Definition gdecl_eq (G2 : gctx) (D D2 : gdecl) : Prop :=
  match D, D2 with
  | gdCtx, gdCtx => True
  | gdTy Δ i l, gdTy Δ2 i2 l2 =>
      i2 = i /\ (i = lC \/ i = lD) /\ lequiv (gL G2) l l2 /\ [ G2 ⊢[ lD ] Δ ≅ Δ2 ]
  | gdTm Δ i T l, gdTm Δ2 i2 T2 l2 =>
      i2 = i /\ (i = lV \/ i = lC) /\ lequiv (gL G2) l l2 /\ [ G2 ⊢[ lD ] Δ ≅ Δ2 ] /\
      [ G2 ; Δ ⊢[ lD ] T ≅ T2 @ l ]
  (* a definition only to itself: definitions are never bound by letbox (M9) *)
  | gdDef Δ T l t, gdDef Δ2 T2 l2 t2 => Δ2 = Δ /\ T2 = T /\ l2 = l /\ t2 = t
  | _, _ => False
  end.

Definition GEq (G G2 : gctx) : Prop :=
  [ ⊢ G ] /\ [ ⊢ G2 ] /\ gL G2 = gL G /\
  forall u D, in_gctx (gΨ G) u D -> exists D2, in_gctx (gΨ G2) u D2 /\ gdecl_eq G2 D D2.

(** ** The identity objects *)

Definition gid_obj (Ψ : list gdecl) (u : nat) : gobj :=
  match nth_error Ψ u with Some D => id_obj D u | None => GId u end.

Lemma id_obj_ren D ξ j : id_obj (gdecl_ren D ξ) j = id_obj D j.
Proof. destruct D; reflexivity. Qed.

Lemma gid_obj_in Ψ u D : in_gctx Ψ u D -> gid_obj Ψ u = id_obj D u.
Proof.
  unfold gid_obj. intros H. assert (Hk : exists D0, nth_error Ψ u = Some D0 /\ forall j, id_obj D0 j = id_obj D j).
  { induction H as [Ψ D | Ψ D D' n Hin IH].
    - exists D; split; [reflexivity | intros j; symmetry; apply id_obj_ren].
    - destruct IH as (D0 & HD0 & E). exists D0; split; [exact HD0 | intros j; rewrite E; symmetry; apply id_obj_ren]. }
  destruct Hk as (D0 & -> & E). apply E.
Qed.

Lemma dnfo_id_obj D j : dnfo (id_obj D j).
Proof. destruct D; cbn; auto. Qed.
Lemma dnfo_gid_obj Ψ u : dnfo (gid_obj Ψ u).
Proof. unfold gid_obj. destruct (nth_error Ψ u); [apply dnfo_id_obj | cbn; auto]. Qed.

Lemma gsub_equiv_gid_obj G : gsub_equiv G GId (gid_obj (gΨ G)).
Proof. intros n D Hin. right; left. exists n; split; [reflexivity | exact (gid_obj_in _ _ _ Hin)]. Qed.

(** Typed syntax is unchanged. *)
Section Unchanged.
Context {G : gctx}.

Lemma gid_obj_ctx {i Γ} : [ G ; Γ ⊢[ i ] ] -> Γ⦃gid_obj (gΨ G)⦄ = Γ.
Proof.
  intros H. rewrite <- (proj1 (proj2 equiv_gsubst) _ _ _ H _ _ (gsub_equiv_gid_obj G) (dnfo_gid_obj _)).
  apply gsubst_id_ctx; [exact (wf_ctx_dnf H) | reflexivity].
Qed.
Lemma gid_obj_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> T⦃gid_obj (gΨ G)⦄ = T.
Proof.
  intros H. rewrite <- (proj1 (proj2 (proj2 equiv_gsubst)) _ _ _ _ _ H _ _ (gsub_equiv_gid_obj G) (dnfo_gid_obj _)).
  apply gsubst_id_ty; [exact (wf_ty_dnf H) | reflexivity].
Qed.
Lemma gid_obj_tm {i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> t⦃gid_obj (gΨ G)⦄ = t.
Proof.
  intros H.
  rewrite <- (proj1 (proj2 (proj2 (proj2 equiv_gsubst))) _ _ _ _ _ _ H _ _ (gsub_equiv_gid_obj G) (dnfo_gid_obj _)).
  apply gsubst_id; [exact (wf_tm_dnf H) | reflexivity].
Qed.
End Unchanged.

(** ** The identity objects are typed in the related context *)

Lemma GEq_to {G G2} : GEq G G2 -> gwk_to G (gΨ G2) = G2.
Proof. intros (_ & _ & HL & _). destruct G2 as [L2 Ψ2]; unfold gwk_to; cbn in *. now rewrite HL. Qed.

Lemma lle_refl i : lle i i.
Proof. unfold lle; lia. Qed.

Lemma gconv_sub {G G2} : GEq G G2 -> [ gwk_to G (gΨ G2) ⊢ gid_obj (gΨ G) : G ].
Proof.
  intros HE. rewrite (GEq_to HE). destruct HE as (HG & HG2 & HL & Hl).
  constructor; [exact HG2 | intros; apply dnfo_gid_obj |].
  intros n D Hin. rewrite (gid_obj_in _ _ _ Hin).
  destruct (Hl _ _ Hin) as (D2 & Hin2 & Heq).
  pose proof (gctx_decl_ok _ _ _ HG Hin) as Hok.
  destruct D as [| Δ i l | Δ i T l | Δ T l t], D2 as [| Δ2 i2 l2 | Δ2 i2 T2 l2 | Δ2 T2 l2 t2];
    cbn in Heq; try contradiction;
    cbn [gdecl_gsubst id_obj gobj_wf].
  - destruct G2 as [L2 Ψ2]. exact (in_gctx_ctx_var _ _ _ Hin2).
  - destruct Hok as (HΔ & _). rewrite (gid_obj_ctx HΔ).
    destruct Heq as (-> & Hi & El & Hc).
    pose proof (eqctx_id (i := lD) eq_refl (eqctx_sym_D Hc)) as Hid.
    assert (Ht : typeof i = lD) by (destruct Hi as [-> | ->]; reflexivity).
    eapply wft_lconv; [| exact El].
    eapply wft_gvar; [destruct Hi as [-> | ->]; discriminate | rewrite Ht; exact (eqctx_wf_l (i := lD) eq_refl Hc)
                     | exact Hin2 | apply lle_refl | exact (lsw_tail _ _ _ _ _ Hid) | solve [cbn; auto] |].
    intros m A k HA. exact (var_layer (lsw_var _ _ _ _ _ Hid _ _ _ HA) i Ht).
  - destruct Hok as (HΔ & HT & _). rewrite (gid_obj_ctx HΔ), (gid_obj_ty HT).
    destruct Heq as (-> & Hi & El & Hc & ET).
    pose proof (eqctx_id (i := lD) eq_refl (eqctx_sym_D Hc)) as Hid.
    assert (Ht : typeof i = lD) by (destruct Hi as [-> | ->]; reflexivity).
    pose proof (gctx_decl_ok _ _ _ HG2 Hin2) as (_ & HT2 & _).
    eapply wf_lconv; [| exact El]. eapply wf_conv with (T' := T2); [| rewrite Ht; exact (eqty_lconv _ _ _ _ _ _ _ ET (lequiv_sym _ _ _ El))].
    rewrite <- (nf_id_ty T2) by exact (wf_ty_nf HT2).
    eapply wf_gvar; [rewrite Ht; exact (eqctx_wf_l (i := lD) eq_refl Hc)
                    | exact Hin2 | apply lle_refl | exact (lsw_tail _ _ _ _ _ Hid) | solve [cbn; auto] |].
    intros m A k HA. exact (var_layer (lsw_var _ _ _ _ _ Hid _ _ _ HA) i Ht).
  - destruct Hok as (HΔ & HT & _ & Ht). destruct Heq as (-> & -> & -> & ->).
    rewrite (gid_obj_ctx HΔ), (gid_obj_ty HT), (gid_obj_tm Ht). exact Hin2.
Qed.

(** ** Transfer of the judgments *)

Section Transfer.
Context {G G2 : gctx} (HE : GEq G G2).

Lemma gconv_ctx {i Γ} : compt i -> [ G ; Γ ⊢[ i ] ] -> [ G2 ; Γ ⊢[ i ] ].
Proof.
  intros Hc H. pose proof (proj1 (proj2 gsubstitution) _ _ _ H _ _ (gconv_sub HE) Hc) as X.
  now rewrite (GEq_to HE), (gid_obj_ctx H) in X.
Qed.

Lemma gconv_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G2 ; Γ ⊢[ i ] T @ l ].
Proof.
  intros H. pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ H _ _ (gconv_sub HE)) as X.
  now rewrite (GEq_to HE), (gid_obj_ctx (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H)), (gid_obj_ty H) in X.
Qed.

Lemma gconv_tm {i Γ t T l} : typeof i = i -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G2 ; Γ ⊢[ i ] t : T @ l ].
Proof.
  intros Hi H. pose proof (proj1 (proj2 (proj2 (proj2 gsubstitution))) _ _ _ _ _ _ H _ _ (gconv_sub HE)) as X.
  now rewrite (GEq_to HE), (gid_obj_ctx (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H)),
    (gid_obj_ty (wf_tm_ty Hi H)), (gid_obj_tm H) in X.
Qed.

(** At any layer, given the type's well-formedness (a definition's body at C, M9). *)
Lemma gconv_tm_at {i j Γ t T l} : [ G ; Γ ⊢[ j ] T @ l ] -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G2 ; Γ ⊢[ i ] t : T @ l ].
Proof.
  intros HT H. pose proof (proj1 (proj2 (proj2 (proj2 gsubstitution))) _ _ _ _ _ _ H _ _ (gconv_sub HE)) as X.
  now rewrite (GEq_to HE), (gid_obj_ctx (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H)),
    (gid_obj_ty HT), (gid_obj_tm H) in X.
Qed.

Lemma gconv_eqty {i Γ T T' l} : typeof i = i -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G2 ; Γ ⊢[ i ] T ≅ T' @ l ].
Proof.
  intros Hi H. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gsubstitution)))) _ _ _ _ _ _ H _ _ (gconv_sub HE)) as X.
  pose proof (eqty_wf_l Hi H) as H1. pose proof (eqty_wf_r Hi H) as H2.
  now rewrite (GEq_to HE), (gid_obj_ctx (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H1)),
    (gid_obj_ty H1), (gid_obj_ty H2) in X.
Qed.

Lemma gconv_eqtm {i Γ t t' T l} : typeof i = i -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G2 ; Γ ⊢[ i ] t ≅ t' : T @ l ].
Proof.
  intros Hi H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 gsubstitution))))) _ _ _ _ _ _ _ H _ _ (gconv_sub HE)) as X.
  pose proof (eqtm_wf_l Hi H) as H1. pose proof (eqtm_wf_r Hi H) as H2.
  now rewrite (GEq_to HE), (gid_obj_ctx (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H1)),
    (gid_obj_ty (wf_tm_ty Hi H1)), (gid_obj_tm H1), (gid_obj_tm H2) in X.
Qed.

Lemma gconv_eqctx {i Γ Γ'} : compt i -> [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G2 ⊢[ i ] Γ ≅ Γ' ].
Proof.
  intros Hc H. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gsubstitution))))) _ _ _ _ H _ _ (gconv_sub HE) Hc)
    as X.
  pose proof (compt_typeof_self _ Hc) as Hi.
  now rewrite (GEq_to HE), (gid_obj_ctx (eqctx_wf_l Hi H)), (gid_obj_ctx (eqctx_wf_r Hi H)) in X.
Qed.

End Transfer.

(** ** Closure of the relation under the rules' global extensions *)

Definition decl_layer (D : gdecl) : Prop :=
  match D with
  | gdCtx => True
  | gdTy _ i _ => i = lC \/ i = lD
  | gdTm _ i _ _ => i = lV \/ i = lC
  | gdDef _ _ _ _ => True
  end.

Lemma wfg_cons_inv L Ψ D : [ ⊢ mkG L (D :: Ψ) ] ->
  [ ⊢ mkG L Ψ ] /\ decl_ok (mkG L Ψ) D /\ decl_layer D.
Proof.
  intros H; inversion H; subst; cbn; repeat split; auto;
    first [ match goal with HT : [ _ ; _ ⊢[ _ ] _ @ _ ] |- _ => exact (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HT) end
          | eapply lift_tm; [eassumption | unfold lle; cbn; lia] ].
Qed.

Lemma wfg_cons L Ψ D : [ ⊢ mkG L Ψ ] -> decl_ok (mkG L Ψ) D -> decl_layer D -> [ ⊢ mkG L (D :: Ψ) ].
Proof.
  intros H HD HL; destruct D; cbn in HD, HL.
  - now apply wfg_ctx.
  - destruct HD; now apply wfg_ty.
  - destruct HD as (? & ? & ?); now apply wfg_tm.
  - destruct HD as (? & ? & ? & ?); now apply wfg_def.
Qed.

Lemma gdecl_eq_refl G D : decl_ok G D -> decl_layer D -> gdecl_eq G D D.
Proof.
  intros HD HL; destruct D; cbn in *; auto.
  - destruct HD as (HΔ & Hl). refine (conj eq_refl (conj HL (conj (lequiv_refl _ _ Hl) (eqc_refl _ _ _ HΔ)))).
  - destruct HD as (HΔ & HT & Hl).
    refine (conj eq_refl (conj HL (conj (lequiv_refl _ _ Hl) (conj (eqc_refl _ _ _ HΔ) _)))).
    now apply eqty_refl.
Qed.

Lemma decl_ok_gconv {G G2 D} : GEq G G2 -> decl_ok G D -> decl_ok G2 D.
Proof.
  intros HE HD. pose proof HE as (_ & _ & HL & _). destruct D; cbn in *; auto; rewrite HL.
  - destruct HD as (HΔ & Hl). split; [exact (gconv_ctx HE compt_D HΔ) | exact Hl].
  - destruct HD as (HΔ & HT & Hl). split; [exact (gconv_ctx HE compt_D HΔ) | split; [exact (gconv_ty HE HT) | exact Hl]].
  - destruct HD as (HΔ & HT & Hl & Ht).
    refine (conj (gconv_ctx HE compt_D HΔ) (conj (gconv_ty HE HT) (conj Hl _))).
    exact (gconv_tm_at HE HT Ht).
Qed.

Lemma gdecl_eq_wk1 {L Ψ D0 D D'} : [ ⊢ mkG L (D0 :: Ψ) ] -> gdecl_eq (mkG L Ψ) D D' ->
  gdecl_eq (mkG L (D0 :: Ψ)) (gdecl_ren D S) (gdecl_ren D' S).
Proof.
  intros Hg HD.
  assert (Hw : gwk_wf (gwk_step gwk_id) (D0 :: Ψ) Ψ) by (constructor; constructor).
  destruct D, D'; cbn in *; try contradiction; auto.
  - destruct HD as (-> & Hi & Hl & Hc). refine (conj eq_refl (conj Hi (conj Hl _))).
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ Hc _ _ _ (le_n _) Hw Hg).
  - destruct HD as (-> & Hi & Hl & Hc & HT). refine (conj eq_refl (conj Hi (conj Hl (conj _ _)))).
    + exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ Hc _ _ _ (le_n _) Hw Hg).
    + exact (proj1 (proj2 (proj2 (proj2 (proj2 gweakening)))) _ _ _ _ _ _ HT _ _ _ (le_n _) Hw Hg).
  - destruct HD as (-> & -> & -> & ->); repeat split.
Qed.

Lemma GEq_ext {G G2 D D2} : GEq G G2 -> [ ⊢ gext G D ] -> [ ⊢ gext G2 D2 ] -> gdecl_eq G2 D D2 ->
  GEq (gext G D) (gext G2 D2).
Proof.
  intros HE Hg Hg2 HD. pose proof HE as (_ & _ & HL & Hl).
  destruct G as [L Ψ], G2 as [L2 Ψ2]; cbn in HL; subst L2.
  refine (conj Hg (conj Hg2 (conj eq_refl _))). cbn [gext gΨ].
  intros u X Hin. inversion Hin as [Ψ0 D1 | Ψ0 D1 D1' n Hn]; subst.
  - exists (gdecl_ren D2 S); split; [constructor | exact (gdecl_eq_wk1 Hg2 HD)].
  - destruct (Hl _ _ Hn) as (X2 & Hin2 & HX). exists (gdecl_ren X2 S).
    split; [now constructor | exact (gdecl_eq_wk1 Hg2 HX)].
Qed.

Lemma GEq_ext_same {G G2 D} : GEq G G2 -> [ ⊢ gext G D ] -> GEq (gext G D) (gext G2 D).
Proof.
  intros HE Hg. pose proof HE as (_ & HG2 & HL & _).
  destruct G as [L Ψ]; unfold gext in Hg |- *; cbn [gL gΨ] in *.
  destruct (wfg_cons_inv _ _ _ Hg) as (_ & HD & HLy).
  pose proof (decl_ok_gconv HE HD) as HD2.
  destruct G2 as [L2 Ψ2]; cbn in HL, HD2 |- *.
  apply (GEq_ext (G := mkG L Ψ) (G2 := mkG L2 Ψ2)); [exact HE | exact Hg | apply wfg_cons; assumption |].
  apply gdecl_eq_refl; assumption.
Qed.

Lemma GEq_app {G G2} Ds : GEq G G2 -> [ ⊢ mkG (gL G) (Ds ++ gΨ G) ] ->
  GEq (mkG (gL G) (Ds ++ gΨ G)) (mkG (gL G2) (Ds ++ gΨ G2)).
Proof.
  intros HE. induction Ds as [|D Ds IH]; intros Hg; cbn [List.app] in *.
  - destruct G, G2; exact HE.
  - destruct (wfg_cons_inv _ _ _ Hg) as (Hg' & _ & _).
    exact (GEq_ext_same (G := mkG (gL G) (Ds ++ gΨ G)) (G2 := mkG (gL G2) (Ds ++ gΨ G2)) (IH Hg') Hg).
Qed.

(** Universe weakening. *)

Lemma uwk_eqty n {G i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ gctx_uwk n G ; ucren Γ (ush n) ⊢[ i ] uren_ty T (ush n) ≅ uren_ty T' (ush n) @ lvren l (ush n) ].
Proof.
  intros H. rewrite gctx_uwk_as, uren_ush_ctx, !uren_ush_ty, lvren_ush.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ H _ _ (usub_ok_ush n (gL G))).
Qed.
Lemma uwk_eqctx n {G i Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] ->
  [ gctx_uwk n G ⊢[ i ] ucren Γ (ush n) ≅ ucren Γ' (ush n) ].
Proof.
  intros H. rewrite gctx_uwk_as, !uren_ush_ctx.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ H _ _ (usub_ok_ush n (gL G))).
Qed.

Lemma gdecl_eq_uwk n {G D D2} : gdecl_eq G D D2 ->
  gdecl_eq (gctx_uwk n G) (gdecl_uren D (ush n)) (gdecl_uren D2 (ush n)).
Proof.
  intros HD. destruct D, D2; cbn in *; try contradiction; auto.
  - destruct HD as (-> & Hi & Hl & Hc). refine (conj eq_refl (conj Hi (conj _ (uwk_eqctx n Hc)))).
    rewrite !lvren_ush. exact (lequiv_lvsubst _ _ _ _ _ (usub_ok_ush n (gL G)) Hl).
  - destruct HD as (-> & Hi & Hl & Hc & HT).
    refine (conj eq_refl (conj Hi (conj _ (conj (uwk_eqctx n Hc) (uwk_eqty n HT))))).
    rewrite !lvren_ush. exact (lequiv_lvsubst _ _ _ _ _ (usub_ok_ush n (gL G)) Hl).
  - destruct HD as (-> & -> & -> & ->); repeat split.
Qed.

Lemma GEq_uwk n {G G2} : GEq G G2 -> GEq (gctx_uwk n G) (gctx_uwk n G2).
Proof.
  intros (HG & HG2 & HL & Hl). refine (conj (uwk_glob n _ HG) (conj (uwk_glob n _ HG2) (conj _ _))).
  - cbn. now rewrite HL.
  - intros u D' Hin. unfold gctx_uwk in Hin; cbn [gΨ] in Hin.
    destruct (in_gctx_uren_inv _ _ _ _ Hin) as (D & HD & ->).
    destruct (Hl _ _ HD) as (D2 & Hin2 & HD2). exists (gdecl_uren D2 (ush n)).
    split; [exact (in_gctx_uren _ _ _ _ Hin2) | exact (gdecl_eq_uwk n HD2)].
Qed.

Lemma GEq_recGT {G G2} : GEq G G2 -> [ ⊢ recGT G ] -> GEq (recGT G) (recGT G2).
Proof. intros HE Hg. exact (GEq_ext_same (GEq_uwk 1 HE) Hg). Qed.

Lemma GEq_recGt {G G2} : GEq G G2 -> [ ⊢ recGt G ] -> GEq (recGt G) (recGt G2).
Proof.
  intros HE Hg. unfold recGt in *.
  pose proof (proj1 (wfg_cons_inv _ _ _ Hg)) as Hg1.
  exact (GEq_ext_same (G := gext (gctx_uwk 1 G) gdCtx) (GEq_ext_same (GEq_uwk 1 HE) Hg1) Hg).
Qed.

Lemma GEq_brG {G G2} k : GEq G G2 -> [ ⊢ brG k G ] -> GEq (brG k G) (brG k G2).
Proof. intros HE Hg. exact (GEq_app (brDecls k) (GEq_uwk (br_nu k) HE) Hg). Qed.

Lemma decl_layer_ren D ξ : decl_layer (gdecl_ren D ξ) = decl_layer D.
Proof. destruct D; reflexivity. Qed.

Lemma gctx_decl_layer G n D : [ ⊢ G ] -> in_gctx (gΨ G) n D -> decl_layer D.
Proof.
  destruct G as [L Ψ]; cbn. intros Hg Hin; revert Hg; induction Hin as [Ψ D | Ψ D D' n Hin IH]; intros Hg;
    rewrite decl_layer_ren; destruct (wfg_cons_inv _ _ _ Hg) as (Hg' & _ & HL); auto.
Qed.

Lemma GEq_refl G : [ ⊢ G ] -> GEq G G.
Proof.
  intros HG. refine (conj HG (conj HG (conj eq_refl _))). intros u D Hin. exists D; split; [exact Hin |].
  exact (gdecl_eq_refl _ _ (gctx_decl_ok _ _ _ HG Hin) (gctx_decl_layer _ _ _ HG Hin)).
Qed.
