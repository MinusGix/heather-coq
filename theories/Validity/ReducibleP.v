(** * Reducibility of every judgment at P (M2_DESIGN.md, 5g)

    The identity global substitution is related to itself (the images
    of global variables are the variables themselves), and a well-formed
    context's identity local substitution too.  The fundamental theorems
    at P and at M therefore give reducibility for arbitrary well-formed
    global contexts: M1's restriction to global contexts that bind
    context variables only is gone. *)
From DeLaM.Validity Require Export FundamentalS ModalS.

Definition gid : gsub := fun n => GId n.

Lemma gdecl_gsubst_gid D : dnf_decl D -> gdecl_gsubst D gid = D.
Proof.
  destruct D; cbn [gdecl_gsubst dnf_decl]; intros HD; f_equal; try reflexivity;
    first [apply gsubst_id_ctx | apply gsubst_id_ty]; first [tauto | intros; reflexivity].
Qed.

Lemma gsub_wf_gid {G} : [ ⊢ G ] -> [ G ⊢ gid : G ].
Proof.
  intros HG. constructor; [exact HG | intros n; exact I |].
  intros n D Hin. rewrite gdecl_gsubst_gid by exact (in_gctx_dnf _ _ _ Hin).
  destruct D; cbn.
  - destruct G as [L Ψ]; exact (in_gctx_ctx_var _ _ _ Hin).
  - exists i; split; [apply lle_refl | exact Hin].
  - exists i; split; [apply lle_refl | exact Hin].
Qed.

Section Reducible.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsR : VPLaws (@lr_vp LRM) := vpM_laws EP EM.

Lemma GRel0_gid {G} : GRel0 EP EM G G gid gid.
Proof. intros n D Hin. destruct D; cbn; reflexivity. Qed.

Lemma GSubRel_gid {G} : [ ⊢ G ] -> GSubRel EP EM G G gid gid.
Proof.
  intros HG. constructor; [reflexivity | exact (gsub_wf_gid HG) | exact (gsub_wf_gid HG)
                         | exact GRel0_gid | exact GRel0_gid | exact GRel0_gid].
Qed.

(** Validity with σ at the identities, then at the identity local
    substitution. *)
Section At.
Context {E : GenericEq} {EL : GenericEqLaws} {LP : LRParams} {VL : VPLaws lr_vp} {VN : VPNe}.

Lemma VTyS_red {G Γ T T' l} : [ G ; Γ ⊢g T @ l ] -> [ G ; Γ ⊢g T' @ l ] ->
  @VCtxS EP EM E LP G Γ -> @VTyS EP EM E LP G Γ T T' l -> LRty l G Γ T T'.
Proof.
  intros HT HT' VΓ VT. pose proof (ctx_of_ty HT) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (VΓ _ _ _ (GSubRel_gid HG) _ _ (gwk_ok_id G)) as X.
  pose proof (VT _ _ _ (GSubRel_gid HG) _ _ (gwk_ok_id G)) as Y. cbn [gwa] in X, Y.
  rewrite !gsubst_id_ctx in X, Y by first [exact (wf_ctx_dnf HΓ) | reflexivity].
  rewrite !gsubst_id_ty in Y by first [exact (wf_ty_dnf HT) | exact (wf_ty_dnf HT') | reflexivity].
  pose proof (Y _ _ _ (SubRel_id_rel _ _ X HΓ)) as Z.
  now rewrite (subst_id_ty T _ (wf_ty_nf HT) lshift0_id), (subst_id_ty T' _ (wf_ty_nf HT') lshift0_id) in Z.
Qed.

Lemma VTmS_red {G Γ t t' T l} : [ G ; Γ ⊢g t : T @ l ] -> [ G ; Γ ⊢g t' : T @ l ] ->
  @VCtxS EP EM E LP G Γ -> @VTmS EP EM E LP G Γ t t' T l -> LRtm l G Γ T T t t'.
Proof.
  intros Ht Ht' VΓ Vt. pose proof (ctx_of_tm Ht) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (wf_tm_ty ge_typeof Ht) as HT.
  pose proof (VΓ _ _ _ (GSubRel_gid HG) _ _ (gwk_ok_id G)) as X.
  pose proof (Vt _ _ _ (GSubRel_gid HG) _ _ (gwk_ok_id G)) as Y. cbn [gwa] in X, Y.
  rewrite !gsubst_id_ctx in X, Y by first [exact (wf_ctx_dnf HΓ) | reflexivity].
  rewrite !gsubst_id_ty, !gsubst_id in Y
    by first [exact (wf_ty_dnf HT) | exact (wf_tm_dnf Ht) | exact (wf_tm_dnf Ht') | reflexivity].
  pose proof (Y _ _ _ (SubRel_id_rel _ _ X HΓ)) as Z.
  now rewrite (subst_id_ty T _ (wf_ty_nf HT) lshift0_id), (subst_id t _ (wf_tm_nf Ht) lshift0_id),
    (subst_id t' _ (wf_tm_nf Ht') lshift0_id) in Z.
Qed.

End At.

(** ** At P, at both instances *)

Lemma reducibleP_eqty {G Γ T T' l} : [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] ->
  @LRty EP LR_P l G Γ T T' /\ @LRty EM LR_P l G Γ T T'.
Proof.
  intros H. destruct (proj1 (proj2 (proj2 (proj2 (proj2 (fundamentalS EP EM))))) _ _ _ _ _ _ H eq_refl)
    as ((_ & VP & VM) & TP & TM).
  pose proof (eqty_wf_l (i := lD) eq_refl H) as HT. pose proof (eqty_wf_r (i := lD) eq_refl H) as HT'.
  split.
  - apply (VTyS_red (E := EP)); [| | exact VP | exact TP]; apply (lift_ty (i := lD)); auto using ge_lle_D.
  - apply (VTyS_red (E := EM)); [| | exact VM | exact TM]; apply (lift_ty (i := lD)); auto using ge_lle_D.
Qed.

Lemma reducibleP_eqtm {G Γ t t' T l} : [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ] ->
  @LRtm EP LR_P l G Γ T T t t' /\ @LRtm EM LR_P l G Γ T T t t'.
Proof.
  intros H. destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalS EP EM)))))) _ _ _ _ _ _ _ H eq_refl)
    as ((_ & VP & VM) & _ & _ & TP & TM).
  pose proof (eqtm_wf_l (i := lD) eq_refl H) as Ht. pose proof (eqtm_wf_r (i := lD) eq_refl H) as Ht'.
  split.
  - apply (VTmS_red (E := EP)); [| | exact VP | exact TP]; apply (lift_tm (i := lD)); auto using ge_lle_D.
  - apply (VTmS_red (E := EM)); [| | exact VM | exact TM]; apply (lift_tm (i := lD)); auto using ge_lle_D.
Qed.

End Reducible.
