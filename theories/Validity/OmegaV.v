(** * Validity at ω (M4_DESIGN.md F3, F5)

    The validity forms of [Def], [CtxRel] and [GSubRel], at the level ω:
    related local substitutions, global weakenings and related global
    substitutions give types related by [LRω]. Contexts never contain ω,
    so [SubRel], [CtxRel] and [GSubRel] are the finite ones. The PER,
    conversion and level-equivalence lemmas mirror the finite ones. *)
From DeLaM.LogRel Require Export Omega.
From DeLaM.Validity Require Export ValidS GSubRelW.

Section Local.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** The relation, with its canonical term relation *)

Definition LRtyω G Γ T T' := exists R, LRω G Γ T T' R.
Definition LRtmω G Γ T T' t t' := exists R, LRω G Γ T T' R /\ R t t'.

Lemma LRtmω_ty {G Γ T T' t t'} : LRtmω G Γ T T' t t' -> LRtyω G Γ T T'.
Proof. intros (R & H & _); now exists R. Qed.
Lemma LRtmω_inv {G Γ T T' R t t'} : LRω G Γ T T' R -> LRtmω G Γ T T' t t' -> R t t'.
Proof. intros H (R' & H' & Ht). exact (proj2 (LRω_irrel H H' t t') Ht). Qed.

Lemma LRtmω_irrel_r {G Γ T T' T'' t t'} :
  LRtmω G Γ T T' t t' -> LRtyω G Γ T T'' -> LRtmω G Γ T T'' t t'.
Proof.
  intros (R & H & Ht) [R' H']. exists R'; split; [exact H'|]. exact (proj1 (LRω_irrel H H' t t') Ht).
Qed.
Lemma LRtmω_irrel_l {G Γ T T' T'' t t'} :
  LRtmω G Γ T' T t t' -> LRtyω G Γ T'' T -> LRtmω G Γ T'' T t t'.
Proof.
  intros (R & H & Ht) [R' H']. exists R'; split; [exact H'|].
  exact (proj1 (LRω_irrel (LRω_sym H) (LRω_sym H') t' t) Ht).
Qed.

Lemma LRtyω_sym {G Γ T T'} : LRtyω G Γ T T' -> LRtyω G Γ T' T.
Proof. intros [R H]; exists (flipR R); now apply LRω_sym. Qed.
Lemma LRtyω_trans {G Γ T1 T2 T3} : LRtyω G Γ T1 T2 -> LRtyω G Γ T2 T3 -> LRtyω G Γ T1 T3.
Proof. intros [R1 H1] [R2 H2]. exists R1. exact (proj1 (LRω_trans H1 H2)). Qed.
Lemma LRtmω_sym {G Γ T T' t t'} : LRtmω G Γ T T' t t' -> LRtmω G Γ T' T t' t.
Proof. intros (R & H & Ht). exists (flipR R); split; [now apply LRω_sym | exact Ht]. Qed.
Lemma LRtmω_trans {G Γ T1 T2 T3 t1 t2 t3} :
  LRtmω G Γ T1 T2 t1 t2 -> LRtmω G Γ T2 T3 t2 t3 -> LRtmω G Γ T1 T3 t1 t3.
Proof.
  intros (R1 & H1 & Ht1) (R2 & H2 & Ht2). destruct (LRω_trans H1 H2) as [H3 Hc].
  exists R1; split; [exact H3 | exact (Hc _ _ _ Ht1 Ht2)].
Qed.

Lemma LRtyω_leq {G Γ T1 T2 T3} : LRtyω G Γ T1 T2 -> LRtyω G Γ T3 T3 -> ty_leq T2 T3 -> LRtyω G Γ T1 T3.
Proof. intros [R H] [R3 H3] Ex. exists R. exact (proj1 (LRω_leq H H3 Ex)). Qed.
Lemma LRtmω_leq {G Γ T T' t1 t2 t3} :
  LRtmω G Γ T T' t1 t2 -> LRtmω G Γ T' T' t3 t3 -> tm_leq t2 t3 -> LRtmω G Γ T T' t1 t3.
Proof.
  intros (R & H & Ht) (R3 & H3 & Ht3) Ex. exists R; split; [exact H|].
  exact (proj2 (LRω_leq H H3 (ty_leq_refl _)) _ _ _ Ht Ht3 Ex).
Qed.

Lemma LRtmω_kw {G Γ} (ρ : kwk G Γ) {T T' t t'} :
  LRtmω G Γ T T' t t' -> LRtmω (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') (ktm ρ t) (ktm ρ t').
Proof.
  intros (R & H & Ht). destruct (LRω_kwk H ρ) as (R' & H' & HR'). exists R'; split; auto.
Qed.
Lemma LRtyω_kw {G Γ} (ρ : kwk G Γ) {T T'} :
  LRtyω G Γ T T' -> LRtyω (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T').
Proof. intros [R H]. destruct (LRω_kwk H ρ) as (R' & H' & _). now exists R'. Qed.

(** ** Local validity *)

Definition VTyω G Γ T T' := forall Δ d d', SubRel G Γ Δ d d' -> LRtyω G Δ T[d] T'[d'].
Definition VTmω G Γ t t' T :=
  forall Δ d d', SubRel G Γ Δ d d' -> LRtmω G Δ T[d] T[d'] t[d] t'[d'].

Lemma VTyω_sym {G Γ T T'} : VTyω G Γ T T' -> VTyω G Γ T' T.
Proof. intros H Δ d d' Hd. apply LRtyω_sym, H, SubRel_sym, Hd. Qed.
Lemma VTyω_trans {G Γ T1 T2 T3} : VTyω G Γ T1 T2 -> VTyω G Γ T2 T3 -> VTyω G Γ T1 T3.
Proof. intros H1 H2 Δ d d' Hd. eapply LRtyω_trans; [apply H1, Hd | apply H2, (SubRel_refl_r Hd)]. Qed.
Lemma VTyω_refl_l {G Γ T T'} : VTyω G Γ T T' -> VTyω G Γ T T.
Proof. intros H; eapply VTyω_trans; [exact H | now apply VTyω_sym]. Qed.
Lemma VTmω_ty {G Γ t t' T} : VTmω G Γ t t' T -> VTyω G Γ T T.
Proof. intros H Δ d d' Hd. exact (LRtmω_ty (H _ _ _ Hd)). Qed.
Lemma VTmω_sym {G Γ t t' T} : VTmω G Γ t t' T -> VTmω G Γ t' t T.
Proof. intros H Δ d d' Hd. apply LRtmω_sym, H, SubRel_sym, Hd. Qed.
Lemma VTmω_trans {G Γ t1 t2 t3 T} : VTmω G Γ t1 t2 T -> VTmω G Γ t2 t3 T -> VTmω G Γ t1 t3 T.
Proof. intros H1 H2 Δ d d' Hd. eapply LRtmω_trans; [apply H1, (SubRel_refl_l Hd) | apply H2, Hd]. Qed.
Lemma VTmω_conv {G Γ t t' T T'} : VTmω G Γ t t' T' -> VTyω G Γ T T' -> VTmω G Γ t t' T.
Proof.
  intros Ht HT Δ d d' Hd.
  pose proof (Ht _ _ _ Hd) as H1. pose proof (HT _ _ _ (SubRel_refl_l Hd)) as H2.
  pose proof (VTyω_refl_l HT _ _ _ Hd) as H3.
  assert (H4 : LRtmω G Δ T[d] T'[d'] t[d] t'[d']).
  { eapply LRtmω_irrel_l; [exact H1 | eapply LRtyω_trans; [exact H2 | exact (LRtmω_ty H1)]]. }
  exact (LRtmω_irrel_r H4 H3).
Qed.

Lemma VTyω_leq {G Γ T T'} : VTyω G Γ T T -> VTyω G Γ T' T' -> ty_leq T T' -> VTyω G Γ T T'.
Proof.
  intros V V' Ex Δ d d' Hd.
  exact (LRtyω_leq (V _ _ _ Hd) (V' _ _ _ (SubRel_refl_r Hd)) (subst_leq_ty _ _ _ Ex)).
Qed.
Lemma VTmω_leq {G Γ t t' T} : VTmω G Γ t t T -> VTmω G Γ t' t' T -> tm_leq t t' -> VTmω G Γ t t' T.
Proof.
  intros V V' Ex Δ d d' Hd.
  refine (LRtmω_leq (V _ _ _ Hd) (V' _ _ _ (SubRel_refl_r Hd)) _).
  apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl | exact Ex].
Qed.

Lemma VTyω_transport {G Γ Γ' T T'} : CtxRel G Γ Γ' -> VTyω G Γ T T' -> VTyω G Γ' T T'.
Proof. intros HΓ H Δ d d' Hd. exact (H _ _ _ (SubRel_transport _ _ _ _ _ _ HΓ Hd)). Qed.
Lemma VTmω_transport {G Γ Γ' t t' T} : CtxRel G Γ Γ' -> VTmω G Γ t t' T -> VTmω G Γ' t t' T.
Proof. intros HΓ H Δ d d' Hd. exact (H _ _ _ (SubRel_transport _ _ _ _ _ _ HΓ Hd)). Qed.

(** ** Under global weakenings *)

Definition VTyGω G Γ T T' := forall G' γ, gwk_ok γ G' G -> VTyω G' Γ⟦γ⟧ T⟦γ⟧ T'⟦γ⟧.
Definition VTmGω G Γ t t' T := forall G' γ, gwk_ok γ G' G -> VTmω G' Γ⟦γ⟧ t⟦γ⟧ t'⟦γ⟧ T⟦γ⟧.

Lemma VTyGω_sym {G Γ T T'} : VTyGω G Γ T T' -> VTyGω G Γ T' T.
Proof. intros H G' γ Hγ. exact (VTyω_sym (H _ _ Hγ)). Qed.
Lemma VTyGω_trans {G Γ T1 T2 T3} : VTyGω G Γ T1 T2 -> VTyGω G Γ T2 T3 -> VTyGω G Γ T1 T3.
Proof. intros H1 H2 G' γ Hγ. exact (VTyω_trans (H1 _ _ Hγ) (H2 _ _ Hγ)). Qed.
Lemma VTmGω_ty {G Γ t t' T} : VTmGω G Γ t t' T -> VTyGω G Γ T T.
Proof. intros H G' γ Hγ. exact (VTmω_ty (H _ _ Hγ)). Qed.
Lemma VTmGω_sym {G Γ t t' T} : VTmGω G Γ t t' T -> VTmGω G Γ t' t T.
Proof. intros H G' γ Hγ. exact (VTmω_sym (H _ _ Hγ)). Qed.
Lemma VTmGω_trans {G Γ t1 t2 t3 T} : VTmGω G Γ t1 t2 T -> VTmGω G Γ t2 t3 T -> VTmGω G Γ t1 t3 T.
Proof. intros H1 H2 G' γ Hγ. exact (VTmω_trans (H1 _ _ Hγ) (H2 _ _ Hγ)). Qed.
Lemma VTmGω_conv {G Γ t t' T T'} : VTmGω G Γ t t' T' -> VTyGω G Γ T T' -> VTmGω G Γ t t' T.
Proof. intros H1 H2 G' γ Hγ. exact (VTmω_conv (H1 _ _ Hγ) (H2 _ _ Hγ)). Qed.
Lemma VTyGω_leq {G Γ T T'} : VTyGω G Γ T T -> VTyGω G Γ T' T' -> ty_leq T T' -> VTyGω G Γ T T'.
Proof. intros V V' Ex G' γ Hγ. exact (VTyω_leq (V _ _ Hγ) (V' _ _ Hγ) (ty_leq_gwa _ _ _ Ex)). Qed.
Lemma VTmGω_leq {G Γ t t' T} : VTmGω G Γ t t T -> VTmGω G Γ t' t' T -> tm_leq t t' -> VTmGω G Γ t t' T.
Proof. intros V V' Ex G' γ Hγ. exact (VTmω_leq (V _ _ Hγ) (V' _ _ Hγ) (tm_leq_gwa _ _ _ Ex)). Qed.
Lemma VTyGω_transport {G Γ Γ' T T'} : CtxRelG G Γ Γ' -> VTyGω G Γ T T' -> VTyGω G Γ' T T'.
Proof. intros HΓ H G' γ Hγ. exact (VTyω_transport (HΓ _ _ Hγ) (H _ _ Hγ)). Qed.
Lemma VTmGω_transport {G Γ Γ' t t' T} : CtxRelG G Γ Γ' -> VTmGω G Γ t t' T -> VTmGω G Γ' t t' T.
Proof. intros HΓ H G' γ Hγ. exact (VTmω_transport (HΓ _ _ Hγ) (H _ _ Hγ)). Qed.

End Local.

(** ** With related global substitutions *)

Section Global.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.
Context {E : GenericEq} {EL : @GenericEqLaws E} {LP : LRParams} {VL : VPLaws lr_vp}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation GValid := (GValid EP EM).
Local Notation VCtxS := (@VCtxS EP EM E LP).

Definition VTySω (G : gctx) (Γ : ctx) (T T' : ty) : Prop :=
  forall G' σ σ', GSubRel G' G σ σ' -> VTyGω G' Γ⦃σ⦄ T⦃σ⦄ T'⦃σ'⦄.
Definition VTmSω (G : gctx) (Γ : ctx) (t t' : tm) (T : ty) : Prop :=
  forall G' σ σ', GSubRel G' G σ σ' -> VTmGω G' Γ⦃σ⦄ t⦃σ⦄ t'⦃σ'⦄ T⦃σ⦄.

(** Validity with global substitutions, without global weakenings. *)
Lemma VTySω_intro_loc {G Γ T T'} :
  (forall G' σ σ', GSubRel G' G σ σ' -> VTyω G' Γ⦃σ⦄ T⦃σ⦄ T'⦃σ'⦄) -> VTySω G Γ T T'.
Proof.
  intros H G' σ σ' Hσ G'' γ Hγ Θ e e' He.
  pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG.
  rewrite !gwa_gsubst_ctx in He. rewrite !gwa_gsubst_ty.
  exact (H _ _ _ (GSubRel_wk EP EM Hσ Hγ HG) _ _ _ He).
Qed.
Lemma VTmSω_intro_loc {G Γ t t' T} :
  (forall G' σ σ', GSubRel G' G σ σ' -> VTmω G' Γ⦃σ⦄ t⦃σ⦄ t'⦃σ'⦄ T⦃σ⦄) -> VTmSω G Γ t t' T.
Proof.
  intros H G' σ σ' Hσ G'' γ Hγ Θ e e' He.
  pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG.
  rewrite !gwa_gsubst_ctx in He. rewrite !gwa_gsubst_ty, !gwa_gsubst_tm.
  exact (H _ _ _ (GSubRel_wk EP EM Hσ Hγ HG) _ _ _ He).
Qed.

Lemma VTySω_sym {G Γ T T'} : GValid G -> VCtxS G Γ -> VTySω G Γ T T' -> VTySω G Γ T' T.
Proof.
  intros HG HΓ H G' σ σ' Hσ. pose proof (GSubRel_sym _ _ HG Hσ) as Hσ'.
  exact (VTyGω_transport (HΓ _ _ _ Hσ') (VTyGω_sym (H _ _ _ Hσ'))).
Qed.
Lemma VTySω_trans {G Γ T1 T2 T3} : VTySω G Γ T1 T2 -> VTySω G Γ T2 T3 -> VTySω G Γ T1 T3.
Proof. intros H1 H2 G' σ σ' Hσ. exact (VTyGω_trans (H1 _ _ _ (GSubRel_refl_l _ _ Hσ)) (H2 _ _ _ Hσ)). Qed.
Lemma VTmSω_sym {G Γ t t' T} : GValid G -> VCtxS G Γ -> VTySω G Γ T T ->
  VTmSω G Γ t t' T -> VTmSω G Γ t' t T.
Proof.
  intros HG HΓ HT H G' σ σ' Hσ. pose proof (GSubRel_sym _ _ HG Hσ) as Hσ'.
  pose proof (VTmGω_sym (VTmGω_transport (HΓ _ _ _ Hσ') (H _ _ _ Hσ'))) as X.
  exact (VTmGω_conv X (HT _ _ _ Hσ)).
Qed.
Lemma VTmSω_trans {G Γ t1 t2 t3 T} : VTmSω G Γ t1 t2 T -> VTmSω G Γ t2 t3 T -> VTmSω G Γ t1 t3 T.
Proof. intros H1 H2 G' σ σ' Hσ. exact (VTmGω_trans (H1 _ _ _ (GSubRel_refl_l _ _ Hσ)) (H2 _ _ _ Hσ)). Qed.
Lemma VTmSω_conv {G Γ t t' T T'} : VTmSω G Γ t t' T' -> VTySω G Γ T T' -> VTmSω G Γ t t' T.
Proof. intros Ht HT G' σ σ' Hσ. exact (VTmGω_conv (Ht _ _ _ Hσ) (HT _ _ _ (GSubRel_refl_l _ _ Hσ))). Qed.

Lemma VTySω_leq {G Γ T T'} : VCtxS G Γ -> VTySω G Γ T T -> VTySω G Γ T' T' -> ty_leq T T' ->
  VTySω G Γ T T'.
Proof.
  intros HΓ V V' Ex G' σ σ' Hσ. pose proof (V _ _ _ Hσ) as X.
  pose proof (VTyGω_transport (CtxRelG_sym (HΓ _ _ _ Hσ)) (V' _ _ _ (GSubRel_refl_r _ _ Hσ))) as Y.
  refine (VTyGω_trans X (VTyGω_leq (VTyGω_trans (VTyGω_sym X) X) Y _)).
  apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl | exact Ex].
Qed.
Lemma VTmSω_leq {G Γ t t' T} : VCtxS G Γ -> VTySω G Γ T T -> VTmSω G Γ t t T -> VTmSω G Γ t' t' T ->
  tm_leq t t' -> VTmSω G Γ t t' T.
Proof.
  intros HΓ HT V V' Ex G' σ σ' Hσ. pose proof (V _ _ _ Hσ) as X.
  pose proof (VTmGω_transport (CtxRelG_sym (HΓ _ _ _ Hσ)) (V' _ _ _ (GSubRel_refl_r _ _ Hσ))) as Y0.
  pose proof (VTmGω_conv Y0 (HT _ _ _ Hσ)) as Y.
  refine (VTmGω_trans X (VTmGω_leq (VTmGω_trans (VTmGω_sym X) X) Y _)).
  apply (proj1 (proj2 leq_gsubst_all)); [intros; apply gobj_leq_refl | exact Ex].
Qed.

End Global.
