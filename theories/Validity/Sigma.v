(** * Validity of dependent pairs (M8_DESIGN.md I7)

    The Σ type relation is built as Π's ([LR_sig_here], with Π's domain
    and codomain relations [piDom]/[piCod]). A pair of whnfs is related as
    soon as its projections are, in every world and at every choice of
    annotations ([SigRel_of_proj]); the projections of related terms are
    read off at the identity world ([SigRel_id]). The rules follow: pairs
    by β on their projections, projections by anti-reduction to the whnf's,
    β by anti-reduction, η by the projections' β. *)
From DeLaM.Validity Require Export CodePi.

Section Sigma.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Syntax *)

Lemma ktm_subst {G Δ} (ρ : kwk G Δ) (t : tm) d : ktm ρ t[d] = t⟦kw_γ ρ⟧[kwsub ρ d].
Proof using . unfold ktm, kwsub. now rewrite gwa_subst, subst_ren_lren. Qed.

(** A single substitution after a substitution, in the Kripke form. *)
Lemma kw_single_subst_ty {G Δ} (ρ : kwk G Δ) (B : ty) a d :
  (B[lsingle a])⟦kw_γ ρ⟧[kwsub ρ d] = (ktyl ρ B[llift d])[lsingle (ktm ρ a[d])].
Proof using .
  assert (Nk : LK nftm (kwsub ρ d)) by (intros n; unfold kwsub; rewrite llk_lren; apply ren_nf).
  rewrite ktyl_subst_single, ktm_subst, gwa_subst_ty, gwa_lsingle.
  rewrite (single_subst_ty _ Nk), (lift_single_ty _ _ _ Nk). reflexivity.
Qed.

Lemma kw_eqty_l {G Γ} (ρ : kwk G Γ) {A l B B' l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g B ≅ B' @ l' ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktyl ρ B ≅ ktyl ρ B' @ l' ].
Proof using .
  intros HA Hl H. exact (eqty_wkr (kw_wkr_l ρ) (kw_ext ρ HA Hl) (gwa_eqty (kw_gok ρ) (kw_glob ρ) H)).
Qed.

(** ** The Σ type relation *)

Section SigTy.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' : ty}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l').

Let N := lmeasure (lmax l l').

Lemma LR_sig_here Δ d d' : SubRel G Γ Δ d d' ->
  LogRel (lmax l l') G Δ (tySig l l' A B)[d] (tySig l3 l4 A' B')[d'] (lmax l l')
    (SigRel G Δ l l' l3 l4 A[d] B[llift d] A'[d'] B'[llift d']
       (piDom (A := A) (A' := A') (l := l) (l' := l') Δ d d')
       (piCod (A := A) (A' := A') (B := B) (B' := B') (l := l) (l' := l') Δ d d')).
Proof using EL H3 H4 HB Hwl Hwl' VA VB VL VN.
  intros Hd.
  destruct (poly_here (F := tySig) (A := A) (A' := A') (B := B) (B' := B') Hwl Hwl' H3 H4 HB VA VB Δ d d'
              ltac:(intros; apply wft_sig; auto using ge_compt, ge_notV) ltac:(reflexivity) Hd) as (P & Hdom & Hcod).
  exact (LRsig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P Hdom Hcod (releq_refl _)).
Qed.

Lemma V_sig : VTy G Γ (tySig l l' A B) (tySig l3 l4 A' B') (lmax l l').
Proof using EL H3 H4 HB Hwl Hwl' VA VB VL VN. intros Δ d d' Hd. eexists. exact (LR_sig_here _ _ _ Hd). Qed.

(** The codomain at related indices, in every world. *)
Lemma codty_at {Δ d d'} (ρ : kwk G Δ) x x' : SubRel G Γ Δ d d' ->
  LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A[d']) x x' ->
  LRty l' (kw_G ρ) (kw_Δ ρ) (ktyl ρ B[llift d])[lsingle x] (ktyl ρ B'[llift d'])[lsingle x'].
Proof using EL VB VL.
  intros Hd Hx. pose proof (SubRel_kw _ _ _ ρ _ _ Hd) as Hdρ.
  rewrite !kty_subst in Hx.
  pose proof (VB _ _ (kw_gok ρ)) as VBρ. rewrite gwa_cext in VBρ.
  pose proof (VBρ _ _ _ (SubRel_cons Hdρ Hx)) as X.
  now rewrite <- !ktyl_subst_single in X.
Qed.

End SigTy.

(** ** Typed reductions *)

Section Red.
Context {G : gctx} {Γ : ctx}.

Lemma tmred_fst_cong {l l' A B t w} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  [ G ; Γ ⊢g t ⤳* w : tySig l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢g tmFst l l' A B t ⤳* tmFst l l' A B w : A @ l ].
Proof using .
  intros Hl Hl' HA HB [Ht Hr Heq]. split.
  - apply wf_fst; auto using ge_compt, ge_notV.
  - now apply reds_fst.
  - apply eqtm_fst; auto using ge_compt, ge_notV, lequiv_refl, eqty_refl.
Qed.

Lemma tmred_snd_cong {l l' A B t w} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  [ G ; Γ ⊢g t ⤳* w : tySig l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢g tmSnd l l' A B t ⤳* tmSnd l l' A B w : B[lsingle (tmFst l l' A B t)] @ l' ].
Proof using .
  intros Hl Hl' HA HB [Ht Hr Heq]. split.
  - apply wf_snd; auto using ge_compt, ge_notV.
  - now apply reds_snd.
  - apply eqtm_snd; auto using ge_compt, ge_notV, lequiv_refl, eqty_refl.
Qed.

(** β through equivalent annotations on the projection. *)
Lemma tmred_fst_beta {l l' la lb A0 B0 A1 B1 a b} :
  lwf (gL G) l -> lwf (gL G) l' -> lequiv (gL G) la l -> lequiv (gL G) lb l' ->
  [ G ; Γ ⊢g A0 @ l ] -> [ G ; Γ ,, A0 @ l ⊢g B0 @ l' ] ->
  [ G ; Γ ⊢g a : A0 @ l ] -> [ G ; Γ ⊢g b : B0[lsingle a] @ l' ] ->
  [ G ; Γ ⊢g A0 ≅ A1 @ l ] -> [ G ; Γ ,, A0 @ l ⊢g B0 ≅ B1 @ l' ] ->
  [ G ; Γ ⊢g tmFst la lb A1 B1 (tmPair l l' A0 B0 a b) ⤳* a : A0 @ l ].
Proof using .
  intros Hl Hl' H1 H2 HA0 HB0 Ha Hb HA1 HB1.
  assert (HP : [ G ; Γ ⊢g tmPair l l' A0 B0 a b : tySig l l' A0 B0 @ lmax l l' ])
    by (apply wf_pair; auto using ge_compt, ge_notV).
  assert (Eq1 : [ G ; Γ ⊢g tmFst l l' A0 B0 (tmPair l l' A0 B0 a b) ≅ tmFst la lb A1 B1 (tmPair l l' A0 B0 a b)
                    : A0 @ l ])
    by (apply eqtm_fst; auto using ge_compt, ge_notV, lequiv_sym, eqtm_refl).
  assert (Eq2 : [ G ; Γ ⊢g tmFst l l' A0 B0 (tmPair l l' A0 B0 a b) ≅ a : A0 @ l ])
    by (apply eqtm_fst_beta; auto using ge_compt, ge_notV).
  split.
  - exact (eqtm_wf_r ge_typeof Eq1).
  - econstructor; [constructor | constructor].
  - eapply eqtm_trans; [apply eqtm_sym, Eq1 | exact Eq2].
Qed.

Lemma tmred_snd_beta {l l' la lb A0 B0 A1 B1 a b} :
  lwf (gL G) l -> lwf (gL G) l' -> lequiv (gL G) la l -> lequiv (gL G) lb l' ->
  [ G ; Γ ⊢g A0 @ l ] -> [ G ; Γ ,, A0 @ l ⊢g B0 @ l' ] ->
  [ G ; Γ ⊢g a : A0 @ l ] -> [ G ; Γ ⊢g b : B0[lsingle a] @ l' ] ->
  [ G ; Γ ⊢g A0 ≅ A1 @ l ] -> [ G ; Γ ,, A0 @ l ⊢g B0 ≅ B1 @ l' ] ->
  [ G ; Γ ⊢g tmSnd la lb A1 B1 (tmPair l l' A0 B0 a b) ⤳* b : B0[lsingle a] @ l' ].
Proof using .
  intros Hl Hl' H1 H2 HA0 HB0 Ha Hb HA1 HB1.
  pose proof (eqtm_snd_beta _ _ _ _ _ _ _ _ _ ge_compt Hl Hl' HA0 HB0 Ha Hb) as Eq2.
  pose proof (eqtm_wf_l ge_typeof Eq2) as Hlhs.
  assert (HP : [ G ; Γ ⊢g tmPair l l' A0 B0 a b : tySig l l' A0 B0 @ lmax l l' ])
    by (apply wf_pair; auto using ge_compt, ge_notV).
  assert (Eq1 : [ G ; Γ ⊢g tmSnd l l' A0 B0 (tmPair l l' A0 B0 a b) ≅ tmSnd la lb A1 B1 (tmPair l l' A0 B0 a b)
                    : B0[lsingle (tmFst l l' A0 B0 (tmPair l l' A0 B0 a b))] @ l' ])
    by (apply eqtm_snd; auto using ge_compt, ge_notV, lequiv_sym, eqtm_refl).
  assert (EB : [ G ; Γ ⊢g B0[lsingle a] ≅ B0[lsingle (tmFst l l' A0 B0 (tmPair l l' A0 B0 a b))] @ l' ]).
  { apply (wf_ty_func ge_typeof HB0 (d' := lsingle (tmFst l l' A0 B0 (tmPair l l' A0 B0 a b)))).
    apply (lsub_eq_single ge_typeof); auto.
    - apply wf_fst; auto using ge_compt, ge_notV.
    - apply eqtm_sym, eqtm_fst_beta; auto using ge_compt, ge_notV. }
  pose proof (eqtm_conv _ _ _ _ _ _ _ _ Eq1 ltac:(rewrite ge_typeof; exact EB)) as Eq1'.
  split.
  - exact (eqtm_wf_r ge_typeof Eq1').
  - econstructor; [constructor | constructor].
  - eapply eqtm_trans; [apply eqtm_sym, Eq1' | exact Eq2].
Qed.

End Red.

(** ** The Σ relation at the identity weakening *)

Lemma SigRel_id {G Δ l1 l2 l3 l4 A B A' B' domR codR t t'} (HΔ : [ G ; Δ ⊢g ]) :
  nfty A -> nfty A' -> nfty B -> nfty B' ->
  SigRel G Δ l1 l2 l3 l4 A B A' B' domR codR t t' ->
  exists w w', [ G ; Δ ⊢g t ⤳* w : tySig l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Δ ⊢g t' ⤳* w' : tySig l3 l4 A' B' @ lmax l1 l2 ] /\
    forall la lb la' lb' A1 B1 A1' B1',
      lequiv (gL G) la l1 -> lequiv (gL G) lb l2 ->
      lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
      [ G ; Δ ⊢ A ≈ A1 @ l1 ] -> [ G ; Δ ,, A @ l1 ⊢ B ≈ B1 @ l2 ] ->
      [ G ; Δ ⊢ A' ≈ A1' @ l1 ] -> [ G ; Δ ,, A' @ l1 ⊢ B' ≈ B1' @ l2 ] ->
      exists h : domR (kw_loc wk_id (wkwf_id Δ) HΔ) (tmFst la lb A1 B1 w) (tmFst la' lb' A1' B1' w'),
        codR (kw_loc wk_id (wkwf_id Δ) HΔ) _ _ h (tmSnd la lb A1 B1 w) (tmSnd la' lb' A1' B1' w').
Proof using .
  intros NA NA' NB NB' (w & w' & Hw & Hw' & _ & _ & _ & _ & HK).
  exists w, w'. refine (conj Hw (conj Hw' _)).
  intros la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
  pose proof (HK (kw_loc wk_id (wkwf_id Δ) HΔ) la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4) as K.
  unfold kty, ktm, ktyl, kw_loc in K; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk] in K.
  rewrite (ren_id_tm w), (ren_id_tm w') in K
    by (eapply wf_tm_nf, eqtm_wf_r; [apply ge_typeof | apply tmred_eq; eassumption]).
  rewrite (ren_id_ty A), (ren_id_ty A'), (ren_lift_id_ty B), (ren_lift_id_ty B') in K by assumption.
  now apply K.
Qed.

(** The domain and codomain relations at the identity world, as [LRtm]. *)
Lemma piDom_id {G l l' A A' Δ d d' HΔ a a'} : nfty A[d] -> nfty A'[d'] ->
  @piDom E LP G l l' A A' Δ d d' (kw_loc wk_id (wkwf_id Δ) HΔ) a a' ->
  LRtm l G Δ A[d] A'[d'] a a'.
Proof using .
  intros N N' h. unfold piDom, kty, kw_loc in h; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk] in h.
  rewrite !ren_id_ty in h by assumption.
  apply (LRtm_stage (n := lmeasure (lmax l l'))); [rewrite lmeasure_max; lia | exact h].
Qed.

Lemma piCod_id {G l l' A A' B B' Δ d d' HΔ a a' h b b'} : nfty B[llift d] -> nfty B'[llift d'] ->
  @piCod E LP G l l' A A' B B' Δ d d' (kw_loc wk_id (wkwf_id Δ) HΔ) a a' h b b' ->
  LRtm l' G Δ B[llift d][lsingle a] B'[llift d'][lsingle a'] b b'.
Proof using .
  intros N N' c. unfold piCod, ktyl, kw_loc in c; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk] in c.
  rewrite !ren_lift_id_ty in c by assumption.
  apply (LRtm_stage (n := lmeasure (lmax l l'))); [rewrite lmeasure_max; lia | exact c].
Qed.

(** ** Projections *)

Section ProjV.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' : ty} {p p' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l').

(** The common setup: the whnfs of [p[d]] and [p'[d']], and the
    projections' relations at the identity world, at the rule's own
    annotations. *)
Lemma proj_setup {Δ d d'} : SubRel G Γ Δ d d' -> VTm G Γ p p' (tySig l l' A B) (lmax l l') ->
  exists w w',
    [ G ; Δ ⊢g p[d] ⤳* w : tySig l l' A[d] B[llift d] @ lmax l l' ] /\
    [ G ; Δ ⊢g p'[d'] ⤳* w' : tySig l3 l4 A'[d'] B'[llift d'] @ lmax l3 l4 ] /\
    LRtm l G Δ A[d] A[d'] (tmFst l l' A[d] B[llift d] w) (tmFst l3 l4 A'[d'] B'[llift d'] w') /\
    LRtm l' G Δ B[llift d][lsingle (tmFst l l' A[d] B[llift d] w)]
                B[llift d'][lsingle (tmFst l3 l4 A'[d'] B'[llift d'] w')]
                (tmSnd l l' A[d] B[llift d] w) (tmSnd l3 l4 A'[d'] B'[llift d'] w').
Proof using EL H3 H4 HB Hwl Hwl' VA VB VL VN.
  intros Hd Vp. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (LR_sig_here Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB
                (VTyG_refl_l VA) (VTyG_refl_l VB) _ _ _ Hd) as HP.
  pose proof (VTyG_loc VA) as VAl. pose proof (VTyG_loc VB) as VBl.
  pose proof (VTy_refl_l VAl) as VAA. pose proof (VTy_refl_l VBl) as VBB.
  pose proof (LRtm_inv HP (Vp _ _ _ Hd)) as HS.
  destruct (VAl _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd' & HAA).
  destruct (VAA _ _ _ (SubRel_refl_r Hd)) as [RA2 HRA2].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (HAd' & _ & _).
  destruct (VAl _ _ _ (SubRel_refl_r Hd)) as [RA3 HRA3].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA3) as (_ & _ & HAA').
  assert (Hlift' : SubRel G (Γ ,, A @ l) (Δ ,, A[d'] @ l) (llift d') (llift d'))
    by (apply SubRel_lift; [exact (SubRel_refl_r Hd) | exact VAA | exact HAd' | exact Hwl]).
  destruct (VBl _ _ _ Hlift') as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HBd' & HB'd' & HBB').
  assert (HBd : [ G ; Δ ,, A[d] @ l ⊢g B[llift d] @ l' ]).
  { eapply (wf_ty_subst ge_typeof HB). apply (lsub_wf_lift _ _ ge_typeof); auto.
    exact (SubRel_wf_l _ _ _ _ _ Hd). }
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (_ & _ & HAA0).
  assert (RAd : [ G ; Δ ⊢ A[d] ≈ A[d] @ l ])
    by (eapply geq_ty_trans; [exact HAA0 | apply geq_ty_sym, HAA0]).
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
    by (apply SubRel_lift; [exact (SubRel_refl_l Hd) | exact VAA | exact HAd | exact Hwl]).
  destruct (VBB _ _ _ Hlift) as [RB0 HRB0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB0) as (_ & _ & RBd).
  push_subst.
  destruct (SigRel_id HΔ (wf_ty_nf HAd) (wf_ty_nf HAd') (wf_ty_nf HBd) (wf_ty_nf HBd') HS)
    as (w & w' & Hw & Hw' & K).
  destruct (K l l' l3 l4 A[d] B[llift d] A'[d'] B'[llift d']
              (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') H3 H4 RAd RBd HAA' HBB') as (h & c).
  exists w, w'. refine (conj Hw (conj _ (conj (piDom_id (wf_ty_nf HAd) (wf_ty_nf HAd') h)
                                           (piCod_id (wf_ty_nf HBd) (wf_ty_nf HBd') c)))).
  (* the right whnf at its own annotations *)
  eapply (tmred_lconv _ _ _ _ (lmax l l')); [|now apply lequiv_max].
  eapply tmred_conv; [apply ge_typeof | exact Hw'|].
  apply eqty_sig; auto using ge_compt, ge_notV, lequiv_sym, geq_ty_sound.
Qed.

(** The typings of the annotations at both substitutions. *)
Lemma sig_annots {Δ d d'} : SubRel G Γ Δ d d' ->
  [ G ; Δ ⊢g A[d] @ l ] /\ [ G ; Δ ,, A[d] @ l ⊢g B[llift d] @ l' ] /\
  [ G ; Δ ⊢g A[d'] @ l ] /\ [ G ; Δ ,, A[d'] @ l ⊢g B[llift d'] @ l' ] /\
  [ G ; Δ ⊢g A'[d'] @ l3 ] /\ [ G ; Δ ,, A'[d'] @ l3 ⊢g B'[llift d'] @ l4 ] /\
  [ G ; Δ ⊢g A[d'] ≅ A'[d'] @ l ] /\ [ G ; Δ ,, A[d'] @ l ⊢g B[llift d'] ≅ B'[llift d'] @ l' ].
Proof using EL H3 H4 HB Hwl VA VB VL VN.
  intros Hd.
  pose proof (VTyG_loc VA) as VAl. pose proof (VTyG_loc VB) as VBl. pose proof (VTy_refl_l VAl) as VAA.
  destruct (VAl _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & _ & _).
  destruct (VAl _ _ _ (SubRel_refl_r Hd)) as [RA3 HRA3].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA3) as (HAd' & HA'd' & HAA').
  assert (Hlift' : SubRel G (Γ ,, A @ l) (Δ ,, A[d'] @ l) (llift d') (llift d'))
    by (apply SubRel_lift; [exact (SubRel_refl_r Hd) | exact VAA | exact HAd' | exact Hwl]).
  destruct (VBl _ _ _ Hlift') as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HBd' & HB'd' & HBB').
  assert (HBd : [ G ; Δ ,, A[d] @ l ⊢g B[llift d] @ l' ]).
  { eapply (wf_ty_subst ge_typeof HB). apply (lsub_wf_lift _ _ ge_typeof); auto.
    exact (SubRel_wf_l _ _ _ _ _ Hd). }
  pose proof (geq_ty_sound HAA') as HAAs.
  assert (HA'3 : [ G ; Δ ⊢g A'[d'] @ l3 ]) by (eapply lconv_ty; [exact HA'd' | solve [apply lequiv_sym; assumption]]).
  assert (HB'3 : [ G ; Δ ,, A'[d'] @ l3 ⊢g B'[llift d'] @ l4 ]).
  { eapply (lconv_ty (l := l')); [|solve [apply lequiv_sym; assumption]].
    eapply (stab_ty ge_typeof HAAs (lequiv_sym _ _ _ H3)); [|exact HB'd'].
    apply ext_wf_g; [exact HA'3 | eauto using lequiv_wf_l]. }
  repeat split; auto using geq_ty_sound.
Qed.

End ProjV.

Section FstV.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' : ty} {p p' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l')
  (Vp : VTm G Γ p p' (tySig l l' A B) (lmax l l')).

Lemma V_fst : VTm G Γ (tmFst l l' A B p) (tmFst l3 l4 A' B' p') A l.
Proof using EL H3 H4 HB Hwl Hwl' VA VB VL VN Vp.
  intros Δ d d' Hd.
  destruct (proj_setup Hwl Hwl' H3 H4 HB VA VB Hd Vp) as (w & w' & Hw & Hw' & Hf & _).
  destruct (sig_annots Hwl H3 H4 HB VA VB Hd) as (HAd & HBd & HAd' & HBd' & HA'3 & HB'3 & EA & EB).
  push_subst.
  eapply LRtm_red; [exact Hf | apply tmred_fst_cong; assumption |].
  eapply (tmred_lconv _ _ _ _ l3); [|solve [apply lequiv_sym; assumption]].
  eapply tmred_conv; [apply ge_typeof | apply tmred_fst_cong; eauto using lequiv_wf_l |].
  eapply eqty_lconv; [apply eqty_sym, EA | exact H3].
Qed.

End FstV.

Section SndV.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' : ty} {p p' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l')
  (Vp : VTm G Γ p p' (tySig l l' A B) (lmax l l')).

Lemma V_snd : VTm G Γ (tmSnd l l' A B p) (tmSnd l3 l4 A' B' p') B[lsingle (tmFst l l' A B p)] l'.
Proof using EL H3 H4 HB Hwl Hwl' VA VB VL VN Vp.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (proj_setup Hwl Hwl' H3 H4 HB VA VB Hd Vp) as (w & w' & Hw & Hw' & Hf & Hs).
  destruct (sig_annots Hwl H3 H4 HB VA VB Hd) as (HAd & HBd & HAd' & HBd' & HA'3 & HB'3 & EA & EB).
  pose proof (VTy_refl_l (VTyG_loc VB)) as VBB.
  (* the first projections *)
  pose proof (tmred_fst_cong Hwl Hwl' HAd HBd Hw) as Hfp.
  pose proof (tmred_fst_cong (lequiv_wf_l _ _ _ H3) (lequiv_wf_l _ _ _ H4) HA'3 HB'3 Hw') as Hfp'.
  pose proof (LRtm_red_l Hf Hfp) as G1.
  assert (Vpp : VTm G Γ p p (tySig l l' A B) (lmax l l')) by exact (VTm_trans Vp (VTm_sym Vp)).
  pose proof (V_fst Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB
                (VTyG_refl_l VA) (VTyG_refl_l VB) Vpp _ _ _ Hd) as G2.
  rewrite !subst_fst in G2.
  (* the codomain instances *)
  pose proof (LRtm_red_l (LRtm_trans Hf (LRtm_sym Hf)) Hfp) as F0.
  pose proof (VBB _ _ _ (SubRel_cons (SubRel_refl_l Hd) F0)) as T1C1.
  pose proof (VBB _ _ _ (SubRel_cons (SubRel_refl_r Hd) (LRtm_trans (LRtm_sym G1) G2))) as C2T2.
  rewrite <- !lift_single_ty in T1C1, C2T2 by assumption.
  (* the second projections, reduced *)
  destruct T1C1 as [R1 HR1]. destruct (escape_ty _ _ _ _ _ _ _ _ HR1) as (_ & _ & E1).
  assert (Hsp : [ G ; Δ ⊢g tmSnd l l' A[d] B[llift d] p[d] ⤳* tmSnd l l' A[d] B[llift d] w
                  : B[llift d][lsingle (tmFst l l' A[d] B[llift d] w)] @ l' ]).
  { eapply tmred_conv; [apply ge_typeof | apply tmred_snd_cong; assumption |].
    apply geq_ty_sound, E1. }
  assert (Hsp' : [ G ; Δ ⊢g tmSnd l3 l4 A'[d'] B'[llift d'] p'[d'] ⤳* tmSnd l3 l4 A'[d'] B'[llift d'] w'
                   : B[llift d'][lsingle (tmFst l3 l4 A'[d'] B'[llift d'] w')] @ l' ]).
  { eapply (tmred_lconv _ _ _ _ l4); [|solve [apply lequiv_sym; assumption]].
    eapply tmred_conv; [apply ge_typeof | apply tmred_snd_cong; eauto using lequiv_wf_l |].
    eapply (eqty_lconv _ _ _ _ _ _ l'); [|exact H4].
    pose proof (tmred_eq _ _ _ _ _ _ _ Hfp') as Ef.
    assert (CA : forall t, [ G ; Δ ⊢g t : A'[d'] @ l3 ] -> [ G ; Δ ⊢g t : A[d'] @ l ]).
    { intros t Ht. eapply (wf_lconv _ _ _ _ _ _ l3); [|solve [apply lequiv_sym; assumption]].
      eapply wf_conv; [exact Ht | rewrite ge_typeof; eapply eqty_lconv; [exact EA | exact H3]]. }
    assert (Ef' : [ G ; Δ ⊢g tmFst l3 l4 A'[d'] B'[llift d'] p'[d'] ≅ tmFst l3 l4 A'[d'] B'[llift d'] w'
                      : A[d'] @ l ]).
    { eapply (eqtm_lconv _ _ _ _ _ _ _ l3); [|solve [apply lequiv_sym; assumption]].
      eapply eqtm_conv; [exact Ef | rewrite ge_typeof; eapply eqty_lconv; [exact EA | exact H3]]. }
    eapply (eqty_trans _ _ _ _ (B'[llift d'][lsingle (tmFst l3 l4 A'[d'] B'[llift d'] w')])).
    - apply (wf_ty_func ge_typeof (eqty_wf_r ge_typeof EB)).
      apply (lsub_eq_single ge_typeof); [exact (eqtm_wf_l ge_typeof Ef') | exact (eqtm_wf_r ge_typeof Ef')
                                        | exact Ef'].
    - apply eqty_sym. exact (eqty_single ge_typeof EB (eqtm_wf_r ge_typeof Ef')). }
  pose proof (LRtm_red Hs Hsp Hsp') as Y.
  rewrite !single_subst_ty by assumption. push_subst.
  eapply LRtm_conv_r; [eapply LRtm_conv_l; [exact Y | exists R1; exact HR1] | exact C2T2].
Qed.

End SndV.

(** ** Related pairs from related projections *)

Lemma SigRel_of_proj {G l l' A B Δ d d' w w'} (HΔ : [ G ; Δ ⊢g ]) :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Δ ⊢g A[d] @ l ] -> [ G ; Δ ,, A[d] @ l ⊢g B[llift d] @ l' ] ->
  [ G ; Δ ⊢g A[d'] @ l ] -> [ G ; Δ ,, A[d'] @ l ⊢g B[llift d'] @ l' ] ->
  [ G ; Δ ⊢ A[d] ≈ A[d] @ l ] -> [ G ; Δ ,, A[d] @ l ⊢ B[llift d] ≈ B[llift d] @ l' ] ->
  [ G ; Δ ⊢ A[d'] ≈ A[d] @ l ] -> [ G ; Δ ,, A[d'] @ l ⊢ B[llift d'] ≈ B[llift d] @ l' ] ->
  [ G ; Δ ⊢g tySig l l' A[d] B[llift d] ≅ tySig l l' A[d'] B[llift d'] @ lmax l l' ] ->
  [ G ; Δ ⊢g w : tySig l l' A[d] B[llift d] @ lmax l l' ] ->
  [ G ; Δ ⊢g w' : tySig l l' A[d'] B[llift d'] @ lmax l l' ] ->
  whnf w -> whnf w' ->
  (forall (ρ : kwk G Δ) la lb la' lb' A1 B1 A1' B1',
      lequiv (gL G) la l -> lequiv (gL G) lb l' ->
      lequiv (gL G) la' l -> lequiv (gL G) lb' l' ->
      [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A[d] ≈ A1 @ l ] ->
      [ kw_G ρ ; kw_Δ ρ ,, kty ρ A[d] @ l ⊢ ktyl ρ B[llift d] ≈ B1 @ l' ] ->
      [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A[d'] ≈ A1' @ l ] ->
      [ kw_G ρ ; kw_Δ ρ ,, kty ρ A[d'] @ l ⊢ ktyl ρ B[llift d'] ≈ B1' @ l' ] ->
      exists h : @piDom E LP G l l' A A Δ d d' ρ (tmFst la lb A1 B1 (ktm ρ w)) (tmFst la' lb' A1' B1' (ktm ρ w')),
        @piCod E LP G l l' A A B B Δ d d' ρ _ _ h (tmSnd la lb A1 B1 (ktm ρ w)) (tmSnd la' lb' A1' B1' (ktm ρ w'))) ->
  SigRel G Δ l l' l l' A[d] B[llift d] A[d'] B[llift d']
    (@piDom E LP G l l' A A Δ d d') (@piCod E LP G l l' A A B B Δ d d') w w'.
Proof using EL.
  intros Hwl Hwl' HAd HBd HAd' HBd' RA RB RA' RB' ES Hw Hw' Nw Nw' K.
  pose proof (wf_ty_nf HAd) as NA. pose proof (wf_ty_nf HAd') as NA'.
  pose proof (wf_ty_nf HBd) as NB. pose proof (wf_ty_nf HBd') as NB'.
  assert (Nt : nftm w) by exact (wf_tm_nf Hw). assert (Nt' : nftm w') by exact (wf_tm_nf Hw').
  (* at the identity world, the Σ's own annotations *)
  set (ρ0 := kw_loc wk_id (wkwf_id Δ) HΔ).
  assert (Eid : forall T : ty, nfty T -> kty ρ0 T = T)
    by (intros T NT; unfold kty, ρ0, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk]; now apply ren_id_ty).
  assert (Eidl : forall T : ty, nfty T -> ktyl ρ0 T = T)
    by (intros T NT; unfold ktyl, ρ0, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk]; now apply ren_lift_id_ty).
  assert (Eidt : forall t : tm, nftm t -> ktm ρ0 t = t)
    by (intros t Nt0; unfold ktm, ρ0, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk]; now apply ren_id_tm).
  destruct (K ρ0 l l' l l' A[d] B[llift d] A[d] B[llift d]
              (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl'))
    as (h & c).
  1-4: change (kw_G ρ0) with G; change (kw_Δ ρ0) with Δ;
    rewrite ?(Eid _ NA), ?(Eid _ NA'), ?(Eidl _ NB), ?(Eidl _ NB'); assumption.
  pose proof (piDom_id NA NA' h) as Hf. pose proof (piCod_id NB NB' c) as Hs.
  rewrite (Eidt _ Nt), (Eidt _ Nt') in Hf, Hs.
  assert (Hw'l : [ G ; Δ ⊢g w' : tySig l l' A[d] B[llift d] @ lmax l l' ])
    by (eapply wf_conv; [exact Hw' | rewrite ge_typeof; exact ES]).
  assert (GEQ : [ G ; Δ ⊢ w ≈ w' : tySig l l' A[d] B[llift d] @ lmax l l' ])
    by exact (geq_tm_sig_ext Hwl Hwl' HAd HBd Hw Hw'l (LRtm_geq Hf) (LRtm_geq Hs)).
  exists w, w'.
  refine (conj (tmred_refl _ _ _ Hw) (conj (tmred_refl _ _ _ Hw') (conj Nw (conj Nw' (conj GEQ (conj _ K)))))).
  eapply geq_tm_conv; [exact GEQ | exact ES].
Qed.

(** ** Pairs *)

Section PairV.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' : ty} {a a' b b' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l')
  (Va : VTmG G Γ a a' A l) (Vb : VTmG G Γ b b' B[lsingle a] l').

(** A component's validity in a world, as [kty]/[ktm]. *)
Lemma Va_at {Δ d d'} (ρ : kwk G Δ) : SubRel G Γ Δ d d' ->
  LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A[d']) (ktm ρ a[d]) (ktm ρ a'[d']).
Proof using EL VL Va.
  intros Hd. rewrite !kty_subst, !ktm_subst. exact (Va _ _ (kw_gok ρ) _ _ _ (SubRel_kw _ _ _ ρ _ _ Hd)).
Qed.
Lemma Vb_at {Δ d d'} (ρ : kwk G Δ) : SubRel G Γ Δ d d' ->
  LRtm l' (kw_G ρ) (kw_Δ ρ) (ktyl ρ B[llift d])[lsingle (ktm ρ a[d])] (ktyl ρ B[llift d'])[lsingle (ktm ρ a[d'])]
    (ktm ρ b[d]) (ktm ρ b'[d']).
Proof using EL VL Vb.
  intros Hd. rewrite <- !kw_single_subst_ty, !ktm_subst.
  exact (Vb _ _ (kw_gok ρ) _ _ _ (SubRel_kw _ _ _ ρ _ _ Hd)).
Qed.

Lemma V_pair : VTm G Γ (tmPair l l' A B a b) (tmPair l3 l4 A' B' a' b') (tySig l l' A B) (lmax l l').
Proof using EL H3 H4 HB Hwl Hwl' VA VB VL VN Va Vb.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (LR_sig_here Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB
                (VTyG_refl_l VA) (VTyG_refl_l VB) _ _ _ Hd) as HP.
  destruct (sig_annots Hwl H3 H4 HB VA VB Hd) as (HAd & HBd & HAd' & HBd' & HA'3 & HB'3 & EA & EB).
  pose proof (VTyG_loc VA) as VAl. pose proof (VTy_refl_l VAl) as VAA.
  pose proof (VTy_refl_l (VTyG_loc VB)) as VBB.
  pose proof (VTyG_refl_l VB) as VBBG.
  (* reflexive annotations *)
  destruct (VAA _ _ _ (SubRel_refl_l Hd)) as [R1 HR1]. destruct (escape_ty _ _ _ _ _ _ _ _ HR1) as (_ & _ & RA).
  destruct (VAA _ _ _ (SubRel_refl_r Hd)) as [R2 HR2]. destruct (escape_ty _ _ _ _ _ _ _ _ HR2) as (_ & _ & RA').
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
    by (apply SubRel_lift; [exact (SubRel_refl_l Hd) | exact VAA | exact HAd | exact Hwl]).
  assert (Hlift' : SubRel G (Γ ,, A @ l) (Δ ,, A[d'] @ l) (llift d') (llift d'))
    by (apply SubRel_lift; [exact (SubRel_refl_r Hd) | exact VAA | exact HAd' | exact Hwl]).
  destruct (VBB _ _ _ Hlift) as [R3 HR3]. destruct (escape_ty _ _ _ _ _ _ _ _ HR3) as (_ & _ & RB).
  destruct (VBB _ _ _ Hlift') as [R4 HR4]. destruct (escape_ty _ _ _ _ _ _ _ _ HR4) as (_ & _ & RB').
  destruct (escape_ty _ _ _ _ _ _ _ _ HP) as (_ & _ & ESg). rewrite !subst_tySig in ESg.
  pose proof (geq_ty_sound ESg) as ES.
  destruct (VAA _ _ _ Hd) as [R5 HR5]. destruct (escape_ty _ _ _ _ _ _ _ _ HR5) as (_ & _ & EAdd').
  assert (Hlift0 : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact VAA | exact HAd | exact Hwl]).
  destruct (VBB _ _ _ Hlift0) as [R6 HR6]. destruct (escape_ty _ _ _ _ _ _ _ _ HR6) as (_ & _ & EBdd').
  pose proof (geq_ty_sym EAdd') as RA''.
  assert (RB'' : [ G ; Δ ,, A[d'] @ l ⊢ B[llift d'] ≈ B[llift d] @ l' ]).
  { apply geq_ty_sym. eapply geq_ty_ctxconv; [apply geq_ty_sound, EAdd' | apply lequiv_refl, Hwl
                                             | apply ext_wf_g; [exact HAd' | exact Hwl] | exact EBdd']. }
  (* the components *)
  pose proof (VTmG_loc Va _ _ _ Hd) as Ha. pose proof (VTmG_loc Va _ _ _ (SubRel_refl_r Hd)) as Ha1.
  pose proof (VTmG_loc Vb _ _ _ Hd) as Hb. pose proof (VTmG_loc Vb _ _ _ (SubRel_refl_r Hd)) as Hb1.
  rewrite !single_subst_ty in Hb, Hb1 by assumption.
  destruct (LRtm_escape Ha) as [Had _]. destruct (LRtm_escape Ha1) as [Had' Ha'd'].
  destruct (LRtm_escape Hb) as [Hbd _]. destruct (LRtm_escape Hb1) as [_ Hb'd'].
  pose proof (LRtm_geq Ha1) as Eaa'.
  (* the right pair at its annotations *)
  assert (EA3 : [ G ; Δ ⊢g A[d'] ≅ A'[d'] @ l3 ]) by (eapply eqty_lconv; [exact EA | exact H3]).
  assert (Ha'3 : [ G ; Δ ⊢g a'[d'] : A'[d'] @ l3 ]).
  { eapply (wf_lconv _ _ _ _ _ _ l); [|exact H3].
    eapply wf_conv; [exact Ha'd' | rewrite ge_typeof; apply eqty_sym, EA]. }
  assert (EBa : [ G ; Δ ⊢g B[llift d'][lsingle a[d']] ≅ B'[llift d'][lsingle a'[d']] @ l' ]).
  { eapply (eqty_trans _ _ _ _ (B[llift d'][lsingle a'[d']])).
    - apply (wf_ty_func ge_typeof HBd'). apply (lsub_eq_single ge_typeof); auto using geq_tm_sound.
    - exact (eqty_single ge_typeof EB Ha'd'). }
  assert (Hb'4 : [ G ; Δ ⊢g b'[d'] : B'[llift d'][lsingle a'[d']] @ l4 ]).
  { eapply (wf_lconv _ _ _ _ _ _ l'); [|exact H4].
    eapply wf_conv; [exact Hb'd' | rewrite ge_typeof; apply eqty_sym, EBa]. }
  assert (HF : [ G ; Δ ⊢g tmPair l l' A[d] B[llift d] a[d] b[d] : tySig l l' A[d] B[llift d] @ lmax l l' ])
    by (apply wf_pair; auto using ge_compt, ge_notV).
  assert (HF' : [ G ; Δ ⊢g tmPair l3 l4 A'[d'] B'[llift d'] a'[d'] b'[d'] : tySig l l' A[d'] B[llift d'] @ lmax l l' ]).
  { eapply (wf_conv _ _ _ _ _ (tySig l3 l4 A'[d'] B'[llift d'])); [| rewrite ge_typeof; apply eqty_sig;
                        [exact ge_notV | solve [apply lequiv_sym; assumption] | solve [apply lequiv_sym; assumption] | exact HAd' | exact EA | exact EB]].
    eapply (wf_lconv _ _ _ _ _ _ (lmax l3 l4)); [|apply lequiv_max; solve [apply lequiv_sym; assumption]].
    apply wf_pair; eauto using ge_compt, ge_notV, lequiv_wf_l. }
  eapply LRtm_of; [exact HP|]. push_subst.
  apply (SigRel_of_proj HΔ Hwl Hwl' HAd HBd HAd' HBd' RA RB RA'' RB'' ES HF HF' (whnf_pair _ _ _ _ _ _)
           (whnf_pair _ _ _ _ _ _)).
  (* the projections in every world *)
  intros ρ la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
  rewrite !ktm_pair.
  pose proof (Va_at ρ Hd) as Haρ. pose proof (Va_at ρ (SubRel_refl_r Hd)) as Haρ1.
  pose proof (Vb_at ρ Hd) as Hbρ. pose proof (Vb_at ρ (SubRel_refl_r Hd)) as Hbρ1.
  destruct (LRtm_escape Haρ) as [Hadρ _]. destruct (LRtm_escape Haρ1) as [Had'ρ Ha'd'ρ].
  destruct (LRtm_escape Hbρ) as [Hbdρ _]. destruct (LRtm_escape Hbρ1) as [_ Hb'd'ρ].
  apply (kw_lequiv ρ) in Hla, Hlb, Hla', Hlb'.
  pose proof (kw_lwf ρ Hwl) as Hwlρ. pose proof (kw_lwf ρ Hwl') as Hwl'ρ.
  pose proof (kw_lequiv ρ H3) as H3ρ. pose proof (kw_lequiv ρ H4) as H4ρ.
  pose proof (kw_ty ρ HAd) as HAdρ. pose proof (kw_ty_l ρ HAd Hwl HBd) as HBdρ.
  pose proof (kw_ty ρ HAd') as HAd'ρ. pose proof (kw_ty_l ρ HAd' Hwl HBd') as HBd'ρ.
  assert (Hw3 : lwf (gL G) l3) by exact (lequiv_wf_l _ _ _ H3).
  pose proof (kw_ty ρ HA'3) as HA'3ρ. pose proof (kw_ty_l ρ HA'3 Hw3 HB'3) as HB'3ρ.
  pose proof (kw_eqty ρ EA) as EAρ. pose proof (kw_eqty_l ρ HAd' Hwl EB) as EBρ.
  pose proof (kw_ext ρ HA'3 Hw3) as HΔ'3.
  (* the right component's typings at the right annotations *)
  assert (EA3ρ : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A[d'] ≅ kty ρ A'[d'] @ l3 ]) by (eapply eqty_lconv; [exact EAρ | exact H3ρ]).
  assert (Ha'3ρ : [ kw_G ρ ; kw_Δ ρ ⊢g ktm ρ a'[d'] : kty ρ A'[d'] @ l3 ]).
  { eapply (wf_lconv _ _ _ _ _ _ l); [|exact H3ρ].
    eapply wf_conv; [exact Ha'd'ρ | rewrite ge_typeof; apply eqty_sym, EAρ]. }
  assert (EBaρ : [ kw_G ρ ; kw_Δ ρ ⊢g (ktyl ρ B[llift d'])[lsingle (ktm ρ a[d'])]
                    ≅ (ktyl ρ B'[llift d'])[lsingle (ktm ρ a'[d'])] @ l' ]).
  { eapply (eqty_trans _ _ _ _ ((ktyl ρ B[llift d'])[lsingle (ktm ρ a'[d'])])).
    - apply (wf_ty_func ge_typeof HBd'ρ). apply (lsub_eq_single ge_typeof); auto.
      apply geq_tm_sound, (LRtm_geq Haρ1).
    - exact (eqty_single ge_typeof EBρ Ha'd'ρ). }
  assert (Hb'4ρ : [ kw_G ρ ; kw_Δ ρ ⊢g ktm ρ b'[d'] : (ktyl ρ B'[llift d'])[lsingle (ktm ρ a'[d'])] @ l4 ]).
  { eapply (wf_lconv _ _ _ _ _ _ l'); [|exact H4ρ].
    eapply wf_conv; [exact Hb'd'ρ | rewrite ge_typeof; apply eqty_sym, EBaρ]. }
  (* the annotations of the right projections, at the right pair's *)
  assert (EA1' : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A'[d'] ≅ A1' @ l3 ]).
  { eapply eqty_lconv; [|exact H3ρ]. eapply eqty_trans; [apply eqty_sym, EAρ | now apply geq_ty_sound]. }
  assert (EB1' : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A'[d'] @ l3 ⊢g ktyl ρ B'[llift d'] ≅ B1' @ l4 ]).
  { eapply eqty_lconv; [|exact H4ρ].
    eapply (stab_eqty ge_typeof EA3ρ (lequiv_refl _ _ (kw_lwf ρ Hw3)) HΔ'3).
    eapply eqty_lconv with (l' := l'); [| apply lequiv_refl; exact Hwl'ρ].
    eapply (stab_eqty ge_typeof (eqty_refl _ _ _ _ _ HAd'ρ) (lequiv_sym _ _ _ H3ρ));
      [apply ext_wf_g; [eapply lconv_ty; [exact HAd'ρ | solve [apply lequiv_sym; assumption]] | exact (kw_lwf ρ Hw3)] |].
    eapply eqty_trans; [apply eqty_sym, EBρ | now apply geq_ty_sound]. }
  (* the first projections *)
  assert (Rf : [ kw_G ρ ; kw_Δ ρ ⊢g tmFst la lb A1 B1 (tmPair l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ a[d]) (ktm ρ b[d]))
                  ⤳* ktm ρ a[d] : kty ρ A[d] @ l ])
    by (apply tmred_fst_beta; auto using geq_ty_sound).
  assert (Rf' : [ kw_G ρ ; kw_Δ ρ ⊢g tmFst la' lb' A1' B1' (tmPair l3 l4 (kty ρ A'[d']) (ktyl ρ B'[llift d']) (ktm ρ a'[d']) (ktm ρ b'[d']))
                   ⤳* ktm ρ a'[d'] : kty ρ A[d'] @ l ]).
  { eapply (tmred_lconv _ _ _ _ l3); [|solve [apply lequiv_sym; assumption]].
    eapply tmred_conv; [apply ge_typeof | apply tmred_fst_beta; eauto using lequiv_wf_l |].
    - eapply lequiv_trans; [exact Hla' | solve [apply lequiv_sym; assumption]].
    - eapply lequiv_trans; [exact Hlb' | solve [apply lequiv_sym; assumption]].
    - apply eqty_sym, EA3ρ. }
  pose proof (LRtm_red Haρ Rf Rf') as Hfst.
  assert (h : @piDom E LP G l l' A A Δ d d' ρ
                (tmFst la lb A1 B1 (tmPair l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ a[d]) (ktm ρ b[d])))
                (tmFst la' lb' A1' B1' (tmPair l3 l4 (kty ρ A'[d']) (ktyl ρ B'[llift d']) (ktm ρ a'[d']) (ktm ρ b'[d']))))
    by (unfold piDom; apply (LRtm_stage (l := l)); [rewrite lmeasure_max; lia | exact Hfst]).
  exists h. unfold piCod.
  apply (LRtm_stage (l := l')); [rewrite lmeasure_max; lia|].
  (* the second projections *)
  assert (Rs : [ kw_G ρ ; kw_Δ ρ ⊢g tmSnd la lb A1 B1 (tmPair l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ a[d]) (ktm ρ b[d]))
                  ⤳* ktm ρ b[d] : (ktyl ρ B[llift d])[lsingle (ktm ρ a[d])] @ l' ])
    by (apply tmred_snd_beta; auto using geq_ty_sound).
  assert (Rs' : [ kw_G ρ ; kw_Δ ρ ⊢g tmSnd la' lb' A1' B1' (tmPair l3 l4 (kty ρ A'[d']) (ktyl ρ B'[llift d']) (ktm ρ a'[d']) (ktm ρ b'[d']))
                   ⤳* ktm ρ b'[d'] : (ktyl ρ B[llift d'])[lsingle (ktm ρ a[d'])] @ l' ]).
  { eapply (tmred_lconv _ _ _ _ l4); [|solve [apply lequiv_sym; assumption]].
    eapply tmred_conv; [apply ge_typeof | apply tmred_snd_beta; eauto using lequiv_wf_l |].
    - eapply lequiv_trans; [exact Hla' | solve [apply lequiv_sym; assumption]].
    - eapply lequiv_trans; [exact Hlb' | solve [apply lequiv_sym; assumption]].
    - eapply eqty_lconv; [apply eqty_sym, EBaρ | exact H4ρ]. }
  pose proof (LRtm_red Hbρ Rs Rs') as X.
  (* back to the first projections as indices *)
  pose proof (LRtm_red_l (LRtm_trans Haρ (LRtm_sym Haρ)) Rf) as Fl.
  pose proof (LRtm_sym (LRtm_red_l (LRtm_sym Haρ1) Rf')) as Fr.
  eapply LRtm_conv_r; [eapply LRtm_conv_l; [exact X|] |].
  - exact (codty_at VBBG ρ _ _ (SubRel_refl_l Hd) Fl).
  - exact (codty_at VBBG ρ _ _ (SubRel_refl_r Hd) Fr).
Qed.

End PairV.

(** ** β *)

Section BetaV.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {A B : ty} {a b : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTy G Γ A A l) (Va : VTm G Γ a a A l) (Vb : VTm G Γ b b B[lsingle a] l').

Lemma beta_annots {Δ d d'} : SubRel G Γ Δ d d' ->
  [ G ; Δ ⊢g A[d] @ l ] /\ [ G ; Δ ,, A[d] @ l ⊢g B[llift d] @ l' ] /\
  [ G ; Δ ⊢g a[d] : A[d] @ l ] /\ [ G ; Δ ⊢g b[d] : B[llift d][lsingle a[d]] @ l' ].
Proof using EL HB Hwl VA Va Vb.
  intros Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & _ & _).
  assert (Hld : lsub_wf G ge_layer (Δ ,, A[d] @ l) (llift d) (Γ ,, A @ l))
    by (apply (lsub_wf_lift _ _ ge_typeof); auto; exact (SubRel_wf_l _ _ _ _ _ Hd)).
  pose proof (Vb _ _ _ Hd) as Hb. rewrite !single_subst_ty in Hb by assumption.
  refine (conj HAd (conj (wf_ty_subst ge_typeof HB Hld) (conj _ _))).
  - exact (proj1 (LRtm_escape (Va _ _ _ Hd))).
  - exact (proj1 (LRtm_escape Hb)).
Qed.

Lemma V_fst_beta : VTm G Γ (tmFst l l' A B (tmPair l l' A B a b)) a A l.
Proof using EL HB Hwl Hwl' VA Va Vb.
  intros Δ d d' Hd. destruct (beta_annots Hd) as (HAd & HBd & Had & Hbd).
  push_subst. eapply LRtm_red_l; [exact (Va _ _ _ Hd) |].
  apply tmred_fst_beta; auto using lequiv_refl, eqty_refl.
Qed.

Lemma V_snd_beta : VTm G Γ (tmSnd l l' A B (tmPair l l' A B a b)) b B[lsingle a] l'.
Proof using EL HB Hwl Hwl' VA Va Vb.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (beta_annots Hd) as (HAd & HBd & Had & Hbd).
  pose proof (Vb _ _ _ Hd) as Hb.
  push_subst. rewrite !single_subst_ty in Hb |- * by assumption.
  eapply LRtm_red_l; [exact Hb |].
  apply tmred_snd_beta; auto using lequiv_refl, eqty_refl.
Qed.

End BetaV.

(** ** η *)

Section EtaV.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {A B : ty} {p : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (HA : [ G ; Γ ⊢g A @ l ]) (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (Hp : [ G ; Γ ⊢g p : tySig l l' A B @ lmax l l' ])
  (VA : VTyG G Γ A A l) (VB : VTyG G (Γ ,, A @ l) B B l')
  (Vp : VTm G Γ p p (tySig l l' A B) (lmax l l')).

Lemma V_sig_eta : VTm G Γ (tmPair l l' A B (tmFst l l' A B p) (tmSnd l l' A B p)) p
                    (tySig l l' A B) (lmax l l').
Proof using EL HA HB Hp Hwl Hwl' VA VB VL VN Vp.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Hsd.
  destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (LR_sig_here Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB VA VB _ _ _ Hd) as HP.
  pose proof (VTyG_loc VA) as VAl. pose proof (VTyG_loc VB) as VBl.
  destruct (sig_annots Hwl (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB VA VB Hd)
    as (HAd & HBd & HAd' & HBd' & _ & _ & _ & _).
  (* reflexive and cross annotations *)
  destruct (VAl _ _ _ (SubRel_refl_l Hd)) as [R1 HR1]. destruct (escape_ty _ _ _ _ _ _ _ _ HR1) as (_ & _ & RA).
  destruct (VAl _ _ _ Hd) as [R5 HR5]. destruct (escape_ty _ _ _ _ _ _ _ _ HR5) as (_ & _ & EAdd').
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
    by (apply SubRel_lift; [exact (SubRel_refl_l Hd) | exact VAl | exact HAd | exact Hwl]).
  assert (Hlift0 : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact VAl | exact HAd | exact Hwl]).
  destruct (VBl _ _ _ Hlift) as [R3 HR3]. destruct (escape_ty _ _ _ _ _ _ _ _ HR3) as (_ & _ & RB).
  destruct (VBl _ _ _ Hlift0) as [R6 HR6]. destruct (escape_ty _ _ _ _ _ _ _ _ HR6) as (_ & _ & EBdd').
  pose proof (geq_ty_sym EAdd') as RA''.
  assert (RB'' : [ G ; Δ ,, A[d'] @ l ⊢ B[llift d'] ≈ B[llift d] @ l' ]).
  { apply geq_ty_sym. eapply geq_ty_ctxconv; [apply geq_ty_sound, EAdd' | apply lequiv_refl, Hwl
                                             | apply ext_wf_g; [exact HAd' | exact Hwl] | exact EBdd']. }
  destruct (escape_ty _ _ _ _ _ _ _ _ HP) as (_ & _ & ESg). rewrite !subst_tySig in ESg.
  pose proof (geq_ty_sound ESg) as ES.
  (* the relation of [p] *)
  pose proof (LRtm_inv HP (Vp _ _ _ Hd)) as Hpi.
  destruct Hpi as (wd & w' & Hwd & Hw' & Hnfd & Hnf' & _ & _ & Kp).
  (* the η-expansion *)
  pose proof (wf_tm_subst ge_typeof (pre_sig_eta_l ge_notV Hwl Hwl' HA HB Hp) Hsd) as HL.
  push_subst. rewrite subst_pair, subst_fst, subst_snd, subst_tySig in HL.
  set (L := tmPair l l' A[d] B[llift d] (tmFst l l' A[d] B[llift d] p[d]) (tmSnd l l' A[d] B[llift d] p[d])).
  assert (Hw'Σ : [ G ; Δ ⊢g w' : tySig l l' A[d'] B[llift d'] @ lmax l l' ])
    by exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw')).
  pose proof (wf_tm_subst ge_typeof Hp Hsd) as Hpd. rewrite subst_tySig in Hpd.
  assert (X : LRtm (lmax l l') G Δ (tySig l l' A[d] B[llift d]) (tySig l l' A[d'] B[llift d']) L w').
  { eapply LRtm_of; [rewrite <- !subst_tySig; exact HP|].
    apply (SigRel_of_proj HΔ Hwl Hwl' HAd HBd HAd' HBd' RA RB RA'' RB'' ES HL Hw'Σ (whnf_pair _ _ _ _ _ _) Hnf').
    intros ρ la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    pose proof (kw_ty ρ HAd) as HAdρ. pose proof (kw_ty_l ρ HAd Hwl HBd) as HBdρ.
    pose proof (kw_lwf ρ Hwl) as Hwlρ. pose proof (kw_lwf ρ Hwl') as Hwl'ρ.
    assert (RAρ : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A[d] ≈ kty ρ A[d] @ l ]) by exact (kw_geq_ty ρ RA).
    assert (RBρ : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A[d] @ l ⊢ ktyl ρ B[llift d] ≈ ktyl ρ B[llift d] @ l' ])
      by exact (kw_geq_ty_l ρ HAd Hwl RB).
    destruct (Kp ρ l l' la' lb' (kty ρ A[d]) (ktyl ρ B[llift d]) A1' B1'
                (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') Hla' Hlb' RAρ RBρ HA1' HB1') as (h0 & c0).
    unfold piDom in h0. unfold piCod in c0.
    apply (LRtm_stage (l := l)) in h0; [|rewrite lmeasure_max; lia].
    apply (LRtm_stage (l := l')) in c0; [|rewrite lmeasure_max; lia].
    apply (kw_lequiv ρ) in Hla, Hlb.
    pose proof (kw_tm ρ Hpd) as Hpdρ. rewrite kty_tySig in Hpdρ.
    pose proof (kw_tmred ρ Hwd) as Hwdρ. rewrite kty_tySig in Hwdρ.
    (* the left projections, reduced to [wd]'s *)
    assert (Hfp : [ kw_G ρ ; kw_Δ ρ ⊢g tmFst l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ p[d]) :
                    kty ρ A[d] @ l ]) by (apply wf_fst; auto using ge_compt, ge_notV).
    assert (Hsp : [ kw_G ρ ; kw_Δ ρ ⊢g tmSnd l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ p[d]) :
                    (ktyl ρ B[llift d])[lsingle (tmFst l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ p[d]))] @ l' ])
      by (apply wf_snd; auto using ge_compt, ge_notV).
    assert (Rf : [ kw_G ρ ; kw_Δ ρ ⊢g tmFst la lb A1 B1 (ktm ρ L)
                   ⤳* tmFst l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ wd) : kty ρ A[d] @ l ]).
    { subst L. rewrite ktm_pair, ktm_fst, ktm_snd.
      eapply tmred_trans; [apply tmred_fst_beta; auto using geq_ty_sound |].
      apply tmred_fst_cong; auto. }
    pose proof (LRtm_red_l h0 Rf) as Hf1.
    assert (Hn : lmeasure l <= lmeasure (lmax l l')) by (rewrite lmeasure_max; lia).
    exists (proj1 (LRtm_stage Hn) Hf1).
    apply (LRtm_stage (l := l')); [rewrite lmeasure_max; lia|].
    (* the left second projections, reduced *)
    pose proof (tmred_fst_cong Hwlρ Hwl'ρ HAdρ HBdρ Hwdρ) as Rfp.
    assert (EC : [ kw_G ρ ; kw_Δ ρ ⊢g (ktyl ρ B[llift d])[lsingle (tmFst l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ p[d]))]
                    ≅ (ktyl ρ B[llift d])[lsingle (tmFst l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ wd))] @ l' ]).
    { apply (wf_ty_func ge_typeof HBdρ). pose proof (tmred_eq _ _ _ _ _ _ _ Rfp) as Ef.
      apply (lsub_eq_single ge_typeof); [exact Hfp | exact (eqtm_wf_r ge_typeof Ef) | exact Ef]. }
    assert (Rs : [ kw_G ρ ; kw_Δ ρ ⊢g tmSnd la lb A1 B1 (ktm ρ L)
                   ⤳* tmSnd l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ wd)
                   : (ktyl ρ B[llift d])[lsingle (tmFst l l' (kty ρ A[d]) (ktyl ρ B[llift d]) (ktm ρ wd))] @ l' ]).
    { eapply tmred_conv; [apply ge_typeof | | exact EC].
      subst L. rewrite ktm_pair, ktm_fst, ktm_snd.
      eapply tmred_trans; [apply tmred_snd_beta; auto using geq_ty_sound |].
      apply tmred_snd_cong; auto. }
    pose proof (LRtm_red_l c0 Rs) as Y.
    eapply LRtm_conv_l; [exact Y |].
    exact (codty_at (VTyG_refl_l VB) ρ _ _ (SubRel_refl_l Hd)
             (LRtm_red_l (LRtm_trans h0 (LRtm_sym h0)) Rf)). }
  eapply LRtm_red; [exact X | apply tmred_refl, HL | exact Hw'].
Qed.

End EtaV.

(** ** The code of Σ and its decoding *)

(** Decoding a Σ code, with annotations [k1 k2] equivalent to the levels
    [l1 l2] at which the premises are typed. *)
Lemma tyred_El_sig {G Δ la l1 l2 k1 k2 s t} :
  lequiv (gL G) k1 l1 -> lequiv (gL G) k2 l2 ->
  [ G ; Δ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Δ ,, tyEl k1 s @ l1 ⊢g t : tyU l2 @ lsuc l2 ] ->
  lequiv (gL G) la (lmax l1 l2) ->
  [ G ; Δ ⊢g tyEl la (tmSig k1 k2 s t) ⤳* tySig k1 k2 (tyEl k1 s) (tyEl k2 t) @ lmax l1 l2 ].
Proof using .
  intros H1 H2 Hs Ht Hla.
  pose proof (conv_U' Hs (lequiv_sym _ _ _ H1)) as Hs1.
  destruct (El_annot Hs H1) as [HA _].
  assert (HΓ : [ G ; Δ ,, tyEl k1 s @ k1 ⊢g ])
    by (apply ext_wf_g; [eapply lconv_ty; [exact HA | solve [apply lequiv_sym; assumption]] | eauto using lequiv_wf_l]).
  pose proof (stab_tm ge_typeof (eqty_refl _ _ _ _ _ HA) (lequiv_sym _ _ _ H1) HΓ Ht) as Ht1.
  pose proof (conv_U' Ht1 (lequiv_sym _ _ _ H2)) as Ht2.
  assert (Hc : [ G ; Δ ⊢g tmSig k1 k2 s t : tyU (lmax k1 k2) @ lsuc (lmax k1 k2) ])
    by (apply wf_code_sig; eauto using ge_compt, ge_notV, lequiv_wf_l).
  assert (Hm : lequiv (gL G) (lmax l1 l2) (lmax k1 k2)) by (apply lequiv_max; solve [apply lequiv_sym; assumption]).
  destruct (El_annot Hc (lequiv_trans _ _ _ _ Hla Hm)) as [HEl HEq].
  eapply tyred_lconv; [|exact Hm].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  apply eqty_sym, eqty_El_sig; eauto using ge_compt, ge_notV, lequiv_wf_l.
Qed.

Section CodeSigV.
Context {G : gctx} {Γ : ctx} {l1 l2 l3 l4 : lvl} {s s' t t' : tm}
  (Hw1 : lwf (gL G) l1) (Hw2 : lwf (gL G) l2)
  (H13 : lequiv (gL G) l1 l3) (H24 : lequiv (gL G) l2 l4)
  (Hs : [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ])
  (Ht : [ G ; Γ ,, tyEl l1 s @ l1 ⊢g t : tyU l2 @ lsuc l2 ])
  (Vs : VTmG G Γ s s' (tyU l1) (lsuc l1))
  (Vt : VTmG G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2)).

Lemma V_code_sig :
  VTm G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL H13 H24 Hs Ht Hw1 Hw2 VL VN Vs Vt.
  (* facts in [Γ] *)
  destruct (El_annot Hs (lequiv_refl _ _ Hw1)) as [HA _].
  destruct (El_annot Ht (lequiv_refl _ _ Hw2)) as [HB _].
  pose proof (V_ElG Hw1 H13 Vs) as VA. pose proof (V_ElG Hw2 H24 Vt) as VB.
  (* at a pair of related substitutions *)
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Hwd.
  pose proof (wf_ty_subst ge_typeof HA Hwd) as HAd.
  pose proof (wf_tm_subst ge_typeof Hs Hwd) as Hsd.
  pose proof (wf_tm_subst ge_typeof Ht (lsub_wf_lift _ _ ge_typeof _ _ _ _ _ Hwd HAd Hw1)) as Htd.
  rewrite !subst_tyU, !subst_tyEl in *.
  assert (Hlift : SubRel G (Γ ,, tyEl l1 s @ l1) (Δ ,, tyEl l1 s[d] @ l1) (llift d) (llift d'))
    by exact (SubRel_lift Hd (VTy_refl_l (VTyG_loc VA)) HAd Hw1).
  pose proof (VTmG_loc Vt _ _ _ Hlift) as Xt. pose proof (VTmG_loc Vs _ _ _ Hd) as Xs. rewrite !subst_tyU in Xs, Xt.
  (* the right-hand codes, by escape *)
  pose proof (proj2 (LRtm_escape Xs)) as Hs'd'.
  destruct (El_annot Hs'd' (lequiv_sym _ _ _ H13)) as [HA'd' _].
  assert (HAA'd : [ G ; Δ ⊢g tyEl l1 s[d] ≅ tyEl l3 s'[d'] @ l1 ])
    by exact (eqty_El _ _ _ _ _ _ _ ge_notV H13 (geq_tm_sound (LRtm_geq Xs))).
  assert (HΔA' : [ G ; Δ ,, tyEl l3 s'[d'] @ l1 ⊢g ]) by now apply ext_wf_g.
  pose proof (stab_tm ge_typeof HAA'd (lequiv_refl _ _ Hw1) HΔA' (proj2 (LRtm_escape Xt))) as Ht'd'.
  assert (Hgeq : [ G ; Δ ⊢ tmSig l1 l2 s[d] t[llift d] ≈ tmSig l3 l4 s'[d'] t'[llift d']
                     : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ])
    by exact (geq_tm_code_sig H13 H24 Hsd (LRtm_geq Xs) (LRtm_geq Xt)).
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U (lwf_max Hw1 Hw2)).
  exists (tmSig l1 l2 s[d] t[llift d]), (tmSig l3 l4 s'[d'] t'[llift d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmSig _ _ _ _) (conj (whnf_tmSig _ _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  eexists. eapply LR_red_ty;
    [exact (LR_sig_here Hw1 Hw2 (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24) HB VA VB _ _ _ Hd)
    | | ]; push_subst.
  - apply tyred_El_sig; auto using lequiv_refl.
  - apply tyred_El_sig; auto using lequiv_sym.
Qed.

End CodeSigV.

Lemma V_El_sig {G Γ l l' s t} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢g t : tyU l' @ lsuc l' ] ->
  VTmG G Γ s s (tyU l) (lsuc l) -> VTmG G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTy G Γ (tySig l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmSig l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Hs Ht Vs Vt Δ d d' Hd.
  destruct (El_annot Hs (lequiv_refl _ _ Hw)) as [HA _].
  destruct (El_annot Ht (lequiv_refl _ _ Hw')) as [HB _].
  pose proof (V_ElG Hw (lequiv_refl _ _ Hw) Vs) as VA. pose proof (V_ElG Hw' (lequiv_refl _ _ Hw') Vt) as VB.
  pose proof (LR_sig_here Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB _ _ _ Hd) as HP.
  destruct (escape_ty _ _ _ _ _ _ _ _ HP) as (HPd & _ & _).
  pose proof (SubRel_wf_r Hd) as Hwd'.
  pose proof (wf_ty_subst ge_typeof HA Hwd') as HAd'.
  pose proof (wf_tm_subst ge_typeof Hs Hwd') as Hsd'.
  pose proof (wf_tm_subst ge_typeof Ht (lsub_wf_lift _ _ ge_typeof _ _ _ _ _ Hwd' HAd' Hw)) as Htd'.
  rewrite !subst_tyU, !subst_tyEl in *.
  eexists. eapply LR_red_ty; [exact HP | apply tyred_refl, HPd |]. push_subst.
  apply tyred_El_sig; auto using lequiv_refl, lwf_max.
Qed.

End Sigma.
