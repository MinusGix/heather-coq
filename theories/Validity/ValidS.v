(** * Properties of validity with global substitutions

    The PER-like rules at the level of [VTyS]/[VTmS].  Symmetry swaps the
    global substitutions, so it moves to the other side's context with the
    context's validity (and, for terms, converts back with the type's
    validity); transitivity and conversion use a substitution related to
    itself. *)
From DeLaM.Validity Require Export GSubRel.

Section ValidS.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Locally *)

Lemma VTy_wk1 {G Γ A A' B k l} : VTy G Γ A A' l -> VTy G (Γ ,, B @ k) A⟨↑⟩ A'⟨↑⟩ l.
Proof.
  intros H Δ d d' [Hd _]. rewrite !shift_subst_ty. exact (H _ _ _ Hd).
Qed.

Lemma CtxRel_lookup G : forall Γ Γ' n T T' l l', CtxRel G Γ Γ' ->
  in_ctx Γ n T l -> in_ctx Γ' n T' l' -> VTy G Γ T T' l.
Proof.
  induction Γ as [| g | Γ IH A k]; intros Γ' n T T' l l' HΓ Hin Hin'; inversion Hin; subst.
  - destruct Γ' as [| g' | Γ' A' k']; inversion Hin'; subst. cbn [CtxRel] in HΓ.
    destruct HΓ as (_ & _ & HA & _). exact (VTy_wk1 HA).
  - destruct Γ' as [| g' | Γ' A' k']; inversion Hin'; subst. cbn [CtxRel] in HΓ.
    destruct HΓ as (HΓ & _). apply VTy_wk1. eapply IH; eassumption.
Qed.

Lemma VTy_single {G Γ A B B' a a' l l'} :
  VTy G (Γ ,, A @ l) B B' l' -> VTm G Γ a a' A l -> VTy G Γ B[lsingle a] B'[lsingle a'] l'.
Proof.
  intros HB Ha Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  rewrite !single_subst_ty, !lift_single_ty by assumption.
  exact (HB _ _ _ (SubRel_cons Hd (Ha _ _ _ Hd))).
Qed.

Lemma VTyG_single {G Γ A B B' a a' l l'} :
  VTyG G (Γ ,, A @ l) B B' l' -> VTmG G Γ a a' A l -> VTyG G Γ B[lsingle a] B'[lsingle a'] l'.
Proof.
  intros HB Ha G' γ Hγ. pose proof (HB _ _ Hγ) as X. rewrite gwa_cext in X.
  rewrite !gwa_subst_ty, !gwa_lsingle. exact (VTy_single X (Ha _ _ Hγ)).
Qed.

Lemma VTm_single {G Γ A B b b' a a' l l'} :
  VTm G (Γ ,, A @ l) b b' B l' -> VTm G Γ a a' A l ->
  VTm G Γ b[lsingle a] b'[lsingle a'] B[lsingle a] l'.
Proof.
  intros Hb Ha Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTm_trans Ha (VTm_sym Ha)) as Haa.
  rewrite !single_subst_ty, !single_subst, !lift_single_ty, !lift_single_tm by assumption.
  eapply LRtm_irrel_r; [exact (Hb _ _ _ (SubRel_cons Hd (Ha _ _ _ Hd)))|].
  exact (VTm_ty Hb _ _ _ (SubRel_cons Hd (Haa _ _ _ Hd))).
Qed.

Lemma VTmG_single {G Γ A B b b' a a' l l'} :
  VTmG G (Γ ,, A @ l) b b' B l' -> VTmG G Γ a a' A l ->
  VTmG G Γ b[lsingle a] b'[lsingle a'] B[lsingle a] l'.
Proof.
  intros Hb Ha G' γ Hγ. pose proof (Hb _ _ Hγ) as X. rewrite gwa_cext in X.
  rewrite !gwa_subst_ty, !gwa_subst, !gwa_lsingle. exact (VTm_single X (Ha _ _ Hγ)).
Qed.

(** The contractum of [natrec] at a successor. *)
Lemma VTm_single2 {G Γ M z z' t t' q q' l} :
  VTy G (Γ ,, tyNat @ lzero) M M l ->
  VTm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] l ->
  VTm G Γ t t' tyNat lzero -> VTm G Γ q q' M[lsingle t] l ->
  VTm G Γ z[lsingle2 t q] z'[lsingle2 t' q'] M[lsingle (succ t)] l.
Proof.
  intros VM Vz Vt Vq Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTm_trans Vt (VTm_sym Vt)) as Vtt.
  assert (Ht : SubRel G (Γ ,, tyNat @ lzero) Δ (lcons d t[d]) (lcons d' t'[d']))
    by exact (SubRel_cons Hd (Vt _ _ _ Hd)).
  assert (Hq : LRtm l G Δ M[lcons d t[d]] M[lcons d' t'[d']] q[d] q'[d']).
  { pose proof (Vq _ _ _ Hd) as X. rewrite !single_subst_ty, !lift_single_ty in X by assumption.
    eapply LRtm_irrel_r; [exact X | exact (VM _ _ _ Ht)]. }
  pose proof (Vz _ _ _ (SubRel_cons Ht Hq)) as Z.
  rewrite !lsucc_cons2_ty in Z by assumption.
  rewrite !single2_subst, !lift2_single2, !single_subst_ty by assumption. cbn [subst_tm].
  eapply LRtm_irrel_r; [exact Z|].
  pose proof (V_succ Vtt _ _ _ Hd) as Hs. cbn [subst_tm] in Hs.
  pose proof (VM _ _ _ (SubRel_cons (A := tyNat) Hd Hs)) as Y.
  now rewrite <- !lift_single_ty in Y by assumption.
Qed.

Lemma CtxRelG_lookup {G Γ Γ' n T T' l l'} : CtxRelG G Γ Γ' ->
  in_ctx Γ n T l -> in_ctx Γ' n T' l' -> VTyG G Γ T T' l.
Proof.
  intros HΓ Hin Hin' G' γ Hγ.
  exact (CtxRel_lookup _ _ _ _ _ _ _ _ (HΓ _ _ Hγ) (in_ctx_gwa _ _ _ _ _ Hin) (in_ctx_gwa _ _ _ _ _ Hin')).
Qed.

Lemma CtxRel_tl {G Γ Γ' A A' l l'} : CtxRel G (Γ ,, A @ l) (Γ' ,, A' @ l') -> CtxRel G Γ Γ'.
Proof. cbn [CtxRel]. tauto. Qed.
Lemma CtxRelG_tl {G Γ Γ' A A' l l'} : CtxRelG G (Γ ,, A @ l) (Γ' ,, A' @ l') -> CtxRelG G Γ Γ'.
Proof. intros H G' γ Hγ. pose proof (H _ _ Hγ) as X. rewrite !gwa_cext in X. exact (CtxRel_tl X). Qed.

(** ** With global substitutions *)

Section S.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation GValid := (GValid EP EM).
Local Notation VCtxS := (@VCtxS EP EM E LP).
Local Notation VTyS := (@VTyS EP EM E LP).
Local Notation VTmS := (@VTmS EP EM E LP).

Lemma VCtxS_nil {G} : VCtxS G cnil.
Proof. intros G' σ σ' Hσ. exact CtxRelG_nil. Qed.

Lemma VCtxS_var {G g} : gctx_var G g -> VCtxS G (cvar g).
Proof.
  intros Hg G' σ σ' Hσ. pose proof (gsr_rel _ _ _ _ _ _ Hσ _ _ (gctx_var_in _ _ Hg)) as X.
  rewrite !gs_cvar. cbn in X. destruct (σ g), (σ' g); try contradiction. subst. exact CtxRelG_var.
Qed.

Lemma VCtxS_ext {G Γ A l} : GValid G -> VCtxS G Γ -> VTyS G Γ A A l -> lwf (gL G) l ->
  VCtxS G (Γ ,, A @ l).
Proof.
  intros HG HΓ HA Hl G' σ σ' Hσ. rewrite !gs_cext.
  apply CtxRelG_ext; [exact (HΓ _ _ _ Hσ) | | exact (HA _ _ _ Hσ) | exact (HA _ _ _ (GSubRel_sym _ _ HG Hσ))].
  apply lequiv_refl. now rewrite (gsr_L _ _ _ _ _ _ Hσ).
Qed.

Lemma VCtxS_tl {G Γ A l} : VCtxS G (Γ ,, A @ l) -> VCtxS G Γ.
Proof. intros H G' σ σ' Hσ. pose proof (H _ _ _ Hσ) as X. rewrite !gs_cext in X. exact (CtxRelG_tl X). Qed.

(** The type of a variable. *)
Lemma VTyS_lookup {G Γ n T l} : VCtxS G Γ -> in_ctx Γ n T l -> VTyS G Γ T T l.
Proof.
  intros HΓ Hin G' σ σ' Hσ.
  exact (CtxRelG_lookup (HΓ _ _ _ Hσ) (in_ctx_gsubst _ _ _ _ _ Hin) (in_ctx_gsubst _ _ _ _ _ Hin)).
Qed.

(** ** PER and conversion *)

Lemma VTyS_sym {G Γ T T' l} : GValid G -> VCtxS G Γ -> VTyS G Γ T T' l -> VTyS G Γ T' T l.
Proof.
  intros HG HΓ H G' σ σ' Hσ. pose proof (GSubRel_sym _ _ HG Hσ) as Hσ'.
  exact (VTyG_transport (HΓ _ _ _ Hσ') (VTyG_sym (H _ _ _ Hσ'))).
Qed.

Lemma VTyS_trans {G Γ T1 T2 T3 l} : VTyS G Γ T1 T2 l -> VTyS G Γ T2 T3 l -> VTyS G Γ T1 T3 l.
Proof.
  intros H1 H2 G' σ σ' Hσ. exact (VTyG_trans (H1 _ _ _ (GSubRel_refl_l _ _ Hσ)) (H2 _ _ _ Hσ)).
Qed.

Lemma VTmS_sym {G Γ t t' T l} : GValid G -> VCtxS G Γ -> VTyS G Γ T T l ->
  VTmS G Γ t t' T l -> VTmS G Γ t' t T l.
Proof.
  intros HG HΓ HT H G' σ σ' Hσ. pose proof (GSubRel_sym _ _ HG Hσ) as Hσ'.
  pose proof (VTmG_sym (VTmG_transport (HΓ _ _ _ Hσ') (H _ _ _ Hσ'))) as X.
  exact (VTmG_conv X (HT _ _ _ Hσ)).
Qed.

Lemma VTmS_trans {G Γ t1 t2 t3 T l} : VTmS G Γ t1 t2 T l -> VTmS G Γ t2 t3 T l -> VTmS G Γ t1 t3 T l.
Proof.
  intros H1 H2 G' σ σ' Hσ. exact (VTmG_trans (H1 _ _ _ (GSubRel_refl_l _ _ Hσ)) (H2 _ _ _ Hσ)).
Qed.

Lemma VTmS_conv {G Γ t t' T T' l} : VTmS G Γ t t' T' l -> VTyS G Γ T T' l -> VTmS G Γ t t' T l.
Proof.
  intros Ht HT G' σ σ' Hσ. exact (VTmG_conv (Ht _ _ _ Hσ) (HT _ _ _ (GSubRel_refl_l _ _ Hσ))).
Qed.

Lemma VTyS_lconv {G Γ T T' l l'} : VTyS G Γ T T' l' -> lequiv (gL G) l l' -> VTyS G Γ T T' l.
Proof.
  intros H Hl G' σ σ' Hσ. apply (VTyG_lconv (H _ _ _ Hσ)). now rewrite (gsr_L _ _ _ _ _ _ Hσ).
Qed.
Lemma VTmS_lconv {G Γ t t' T l l'} : VTmS G Γ t t' T l' -> lequiv (gL G) l l' -> VTmS G Γ t t' T l.
Proof.
  intros H Hl G' σ σ' Hσ. apply (VTmG_lconv (H _ _ _ Hσ)). now rewrite (gsr_L _ _ _ _ _ _ Hσ).
Qed.

(** Validity of [VTmS] carries that of its type (left, at [σ ≈ σ]). *)
Lemma VTyS_single {G Γ A B B' a a' l l'} :
  VTyS G (Γ ,, A @ l) B B' l' -> VTmS G Γ a a' A l -> VTyS G Γ B[lsingle a] B'[lsingle a'] l'.
Proof.
  intros HB Ha G' σ σ' Hσ. pose proof (HB _ _ _ Hσ) as X. rewrite gs_cext in X.
  rewrite !gs_single_ty. exact (VTyG_single X (Ha _ _ _ Hσ)).
Qed.

Lemma VTmS_single {G Γ A B b b' a a' l l'} :
  VTmS G (Γ ,, A @ l) b b' B l' -> VTmS G Γ a a' A l ->
  VTmS G Γ b[lsingle a] b'[lsingle a'] B[lsingle a] l'.
Proof.
  intros Hb Ha G' σ σ' Hσ. pose proof (Hb _ _ _ Hσ) as X. rewrite gs_cext in X.
  rewrite !gs_single_ty, !gs_single. exact (VTmG_single X (Ha _ _ _ Hσ)).
Qed.

Lemma VTmS_single2 {G Γ M z z' t t' q q' l} :
  VTyS G (Γ ,, tyNat @ lzero) M M l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] l ->
  VTmS G Γ t t' tyNat lzero -> VTmS G Γ q q' M[lsingle t] l ->
  VTmS G Γ z[lsingle2 t q] z'[lsingle2 t' q'] M[lsingle (succ t)] l.
Proof.
  intros VM Vz Vt Vq G' σ σ' Hσ.
  pose proof (VM _ _ _ (GSubRel_refl_l _ _ Hσ)) as XM. pose proof (Vz _ _ _ Hσ) as Xz.
  pose proof (Vt _ _ _ Hσ) as Xt.
  pose proof (Vq _ _ _ Hσ) as Xq.
  rewrite ?gs_cext, ?gs_tyNat, ?gs_lsucc_ty in XM. rewrite ?gs_cext, ?gs_tyNat, ?gs_lsucc_ty in Xz.
  rewrite ?gs_tyNat in Xt. rewrite ?gs_single_ty in Xq. rewrite ?gs_single_ty, ?gs_single2, ?gs_succ.
  intros G'' γ Hγ. pose proof (XM _ _ Hγ) as YM. pose proof (Xz _ _ Hγ) as Yz.
  pose proof (Xt _ _ Hγ) as Yt. pose proof (Xq _ _ Hγ) as Yq.
  rewrite ?gwa_cext, ?gwa_tyNat in YM. rewrite ?gwa_cext, ?gwa_tyNat, ?gwa_subst_ty, ?gwa_lsucc in Yz.
  rewrite ?gwa_tyNat in Yt. rewrite ?gwa_subst_ty, ?gwa_lsingle in Yq.
  rewrite ?gwa_subst, ?gwa_lsingle2, ?gwa_subst_ty, ?gwa_lsingle, ?gwa_succ.
  exact (VTm_single2 YM Yz Yt Yq).
Qed.

(** Decoding a valid code. *)
Lemma VTyS_El {G Γ c c' l} : lwf (gL G) l -> VTmS G Γ c c' (tyU l) (lsuc l) ->
  VTyS G Γ (tyEl l c) (tyEl l c') l.
Proof.
  intros Hl Hc G' σ σ' Hσ. rewrite !gs_tyEl.
  pose proof (Hc _ _ _ Hσ) as X. rewrite gs_tyU in X.
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as HL.
  apply V_ElG; [rewrite HL; exact Hl | rewrite HL; now apply lequiv_refl | exact X].
Qed.

(** Transitivity through the diagonal: a first step validated only at
    substitutions related to themselves (as a rule's M1 lemma is, whose two
    sides share their subterms). *)
Lemma VTyS_trans_diag {G Γ T1 T2 T3 l} :
  (forall G' σ, GSubRel G' G σ σ -> @VTyG E LP G' Γ⦃σ⦄ T1⦃σ⦄ T2⦃σ⦄ l) -> VTyS G Γ T2 T3 l -> VTyS G Γ T1 T3 l.
Proof.
  intros H1 H2 G' σ σ' Hσ. exact (VTyG_trans (H1 _ _ (GSubRel_refl_l _ _ Hσ)) (H2 _ _ _ Hσ)).
Qed.
Lemma VTmS_trans_diag {G Γ t1 t2 t3 T l} :
  (forall G' σ, GSubRel G' G σ σ -> @VTmG E LP G' Γ⦃σ⦄ t1⦃σ⦄ t2⦃σ⦄ T⦃σ⦄ l) -> VTmS G Γ t2 t3 T l ->
  VTmS G Γ t1 t3 T l.
Proof.
  intros H1 H2 G' σ σ' Hσ. exact (VTmG_trans (H1 _ _ (GSubRel_refl_l _ _ Hσ)) (H2 _ _ _ Hσ)).
Qed.

End S.

End ValidS.
