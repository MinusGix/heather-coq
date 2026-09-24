(** * Validity of application *)
From DeLaM.Validity Require Export Red.

Section App.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Syntax *)

Lemma ren_id_tm (t : tm) : nftm t -> t⟨rshift 0⟩ = t.
Proof.
  intros H. rewrite (ren_as_subst _ _ (lshift 0)); [apply subst_id; auto|];
    intros; cbn; f_equal; lia.
Qed.
Lemma ren_lift_id_ty (T : ty) : nfty T -> T⟨rlift (rshift 0)⟩ = T.
Proof.
  intros H. rewrite <- (ren_id_ty T) at 2 by exact H.
  apply ren_ext_ty; intros [|n]; rewrite ?rlk_rlift; cbn; lia.
Qed.
Lemma lift_single_ty (B : ty) d a : LK nftm d -> B[llift d][lsingle a] = B[lcons d a].
Proof.
  intros Hd. apply subst_subst_ty. intros [|n]; rewrite llk_llift; cbn; [reflexivity|].
  change (ren_tm ?x ?r) with x⟨r⟩. symmetry; apply shift_single, Hd.
Qed.

(** ** The Π relation at the identity weakening *)

Lemma PiRel_id {G Δ l1 l2 l3 l4 A B A' B' domR codR t t'} (HΔ : [ G ; Δ ⊢g ]) :
  nfty A -> nfty A' -> nfty B -> nfty B' ->
  PiRel G Δ l1 l2 l3 l4 A B A' B' domR codR t t' ->
  exists w w', [ G ; Δ ⊢g t ⤳* w : tyPi l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Δ ⊢g t' ⤳* w' : tyPi l3 l4 A' B' @ lmax l1 l2 ] /\
    forall a a' (ha : domR (kw_loc wk_id (wkwf_id Δ) HΔ) a a') la lb la' lb' A1 B1 A1' B1',
      lequiv (gL G) la l1 -> lequiv (gL G) lb l2 ->
      lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
      [ G ; Δ ⊢ A ≈ A1 @ l1 ] -> [ G ; Δ ,, A @ l1 ⊢ B ≈ B1 @ l2 ] ->
      [ G ; Δ ⊢ A' ≈ A1' @ l1 ] -> [ G ; Δ ,, A' @ l1 ⊢ B' ≈ B1' @ l2 ] ->
      codR (kw_loc wk_id (wkwf_id Δ) HΔ) a a' ha (app w la lb A1 B1 a) (app w' la' lb' A1' B1' a').
Proof.
  intros NA NA' NB NB' (w & w' & Hw & Hw' & _ & _ & _ & _ & HK).
  exists w, w'. refine (conj Hw (conj Hw' _)).
  intros a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
  pose proof (HK (kw_loc wk_id (wkwf_id Δ) HΔ) a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4) as K.
  unfold kty, ktm, ktyl, kw_loc in K; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in K.
  rewrite (ren_id_tm w), (ren_id_tm w') in K
    by (eapply wf_tm_nf, eqtm_wf_r; [apply ge_typeof | apply tmred_eq; eassumption]).
  rewrite (ren_id_ty A), (ren_id_ty A'), (ren_lift_id_ty B), (ren_lift_id_ty B') in K by assumption.
  now apply K.
Qed.

(** ** Application *)

Section AppV.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' t t' s s' : _}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l')
  (Vt : VTm G Γ t t' (tyPi l l' A B) (lmax l l')) (Vs : VTm G Γ s s' A l).

Lemma V_app : VTm G Γ (app t l l' A B s) (app t' l3 l4 A' B' s') B[lsingle s] l'.
Proof.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (LR_pi_here Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB
                (VTyG_refl_l VA) (VTyG_refl_l VB) _ _ _ Hd) as HP.
  apply VTyG_loc in VA, VB.
  pose proof (VTy_refl_l VA) as VAA. pose proof (VTy_refl_l VB) as VBB.
  pose proof (LRtm_inv HP (Vt _ _ _ Hd)) as HPi.
  (* facts about the domain and the codomain *)
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd' & _).
  destruct (VAA _ _ _ (SubRel_refl_r Hd)) as [RA2 HRA2].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (HAd' & _ & _).
  destruct (VA _ _ _ (SubRel_refl_r Hd)) as [RA3 HRA3].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA3) as (_ & _ & HAA').
  assert (Hlift' : SubRel G (Γ ,, A @ l) (Δ ,, A[d'] @ l) (llift d') (llift d'))
    by (apply SubRel_lift; [exact (SubRel_refl_r Hd) | exact VAA | exact HAd' | exact Hwl]).
  destruct (VB _ _ _ Hlift') as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HBd' & HB'd' & HBB').
  assert (HBd : [ G ; Δ ,, A[d] @ l ⊢g B[llift d] @ l' ]).
  { eapply (wf_ty_subst ge_typeof HB). apply (lsub_wf_lift _ _ ge_typeof); auto.
    exact (SubRel_wf_l _ _ _ _ _ Hd). }
  pose proof (Vs _ _ _ Hd) as Hs. destruct (LRtm_escape Hs) as [Hsd Hs'd].
  pose proof (Vs _ _ _ (SubRel_refl_r Hd)) as Hs2. destruct (LRtm_escape Hs2) as [_ Hs'd'].
  (* the application at the identity weakening *)
  push_subst.
  destruct (PiRel_id HΔ (wf_ty_nf HAd) (wf_ty_nf HAd') (wf_ty_nf HBd) (wf_ty_nf HBd') HPi)
    as (w & w' & Hw & Hw' & K).
  assert (ha : LRrel (lmeasure (lmax l l')) G Δ A[d]⟨wk_id⟩ A[d']⟨wk_id⟩ l s[d] s'[d']).
  { cbn [wk_ren]. rewrite !ren_id_ty by eauto using wf_ty_nf.
    apply (LRtm_stage (l := l)); [rewrite lmeasure_max; lia | exact Hs]. }
  pose proof (K s[d] s'[d'] ha l l' l3 l4 A[d] B[llift d] A'[d'] B'[llift d']) as K1.
  unfold piCod, kty, ktm, ktyl, kw_loc in K1; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in K1.
  rewrite !ren_lift_id_ty in K1 by eauto using wf_ty_nf.
  (* reflexive left annotations *)
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (_ & _ & HAA).
  assert (RAd : [ G ; Δ ⊢ A[d] ≈ A[d] @ l ])
    by (eapply geq_ty_trans; [exact HAA | apply geq_ty_sym, HAA]).
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
    by (apply SubRel_lift; [exact (SubRel_refl_l Hd) | exact VAA | exact HAd | exact Hwl]).
  destruct (VBB _ _ _ Hlift) as [RB0 HRB0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB0) as (_ & _ & RBd).
  pose proof (K1 (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') H3 H4 RAd RBd HAA' HBB') as X.
  apply (LRtm_stage (l := l')) in X; [|rewrite lmeasure_max; lia].
  destruct X as (R & HR & HX).
  (* typed reductions of the two applications *)
  assert (HAA's : [ G ; Δ ⊢g A[d'] ≅ A'[d'] @ l ]) by now apply geq_ty_sound.
  assert (HA'3 : [ G ; Δ ⊢g A'[d'] @ l3 ]) by (eapply lconv_ty; [exact HA'd' | now apply lequiv_sym]).
  assert (HB'3 : [ G ; Δ ,, A'[d'] @ l3 ⊢g B'[llift d'] @ l4 ]).
  { eapply (lconv_ty (l := l')); [|now apply lequiv_sym].
    eapply (stab_ty ge_typeof HAA's (lequiv_sym _ _ _ H3)); [|exact HB'd'].
    apply ext_wf_g; [exact HA'3 | eauto using lequiv_wf_l]. }
  assert (Hs'3 : [ G ; Δ ⊢g s'[d'] : A'[d'] @ l3 ]).
  { eapply (wf_lconv _ _ _ _ _ _ l); [|exact H3].
    eapply wf_conv; [exact Hs'd' | rewrite ge_typeof; now apply eqty_sym]. }
  assert (Hw'3 : [ G ; Δ ⊢g t'[d'] ⤳* w' : tyPi l3 l4 A'[d'] B'[llift d'] @ lmax l3 l4 ]).
  { eapply (tmred_lconv _ _ _ _ (lmax l l')); [|now apply lequiv_max].
    eapply tmred_conv; [apply ge_typeof | exact Hw'|].
    apply eqty_pi; auto using ge_notV, lequiv_sym, geq_ty_sound. }
  assert (Happ' : [ G ; Δ ⊢g app t'[d'] l3 l4 A'[d'] B'[llift d'] s'[d']
                       ⤳* app w' l3 l4 A'[d'] B'[llift d'] s'[d'] : B[llift d'][lsingle s'[d']] @ l' ]).
  { eapply (tmred_lconv _ _ _ _ l4); [|apply lequiv_sym, H4].
    eapply tmred_conv; [apply ge_typeof | apply tmred_app_cong; eauto using lequiv_wf_l |].
    eapply (eqty_lconv _ _ _ _ _ _ l'); [|exact H4].
    apply eqty_sym. exact (eqty_single ge_typeof (geq_ty_sound HBB') Hs'd'). }
  assert (Happ : [ G ; Δ ⊢g app t[d] l l' A[d] B[llift d] s[d]
                      ⤳* app w l l' A[d] B[llift d] s[d] : B[llift d][lsingle s[d]] @ l' ])
    by (apply tmred_app_cong; auto).
  pose proof (LR_red_tm _ _ _ _ _ _ _ _ HR _ _ _ _ HX Happ Happ') as HY.
  (* back to the substituted type [B[s/x]] *)
  rewrite !single_subst_ty by assumption.
  eapply LRtm_irrel_r; [exists R; split; [exact HR | exact HY]|].
  assert (Hss : LRtm l G Δ A[d] A[d'] s[d] s[d'])
    by (eapply LRtm_trans; [exact Hs | apply LRtm_sym; exact (Vs _ _ _ (SubRel_refl_r Hd))]).
  pose proof (VBB _ _ _ (SubRel_cons Hd Hss)) as HBs.
  now rewrite <- !lift_single_ty in HBs by assumption.
Qed.

End AppV.

End App.
