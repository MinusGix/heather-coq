(** * Validity of [letbox] at layer M (07b)

    A related scrutinee reduces to [box]es of the same code or to related
    neutrals.
    - [box]: [letbox] β-reduces, and the reducts are related by the
      body's validity at the global substitutions extended by the code.
    - neutral: [letbox] is neutral, by the generic law, whose premises
      are the escaped validity of the motive and of the body; the body's
      comes from the substitutions pushed under the new binding with
      [U₀^id] ([GSubRel_up_id]). *)
From DeLaM.Validity Require Export ModalS GSubRelE.

#[local] Existing Instance LR_P.

(** ** Syntax: inversion, typed reduction, the identity instance *)

Lemma letboxT_inv {G Γ l' l Δ M t' t T k} : [ G ; Γ ⊢[ lM ] letboxT l' l Δ M t' t : T @ k ] ->
  lwf (gL G) l' /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\ [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] /\
  [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] /\
  [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] /\
  [ G ; Γ ⊢[ lM ] T ≅ M[lsingle t] @ k ] /\ lequiv (gL G) k l'.
Proof.
  intros H. remember lM as i eqn:Ei. remember (letboxT l' l Δ M t' t) as u eqn:Eu.
  induction H; inversion Eu; subst; try discriminate;
    try match goal with IH : lM = lM -> _ |- _ => destruct (IH eq_refl eq_refl) as (? & ? & ? & ? & ? & ? & ? & ?) end;
    repeat match goal with |- _ /\ _ => split end; try assumption.
  all: first [ solve [apply eqty_refl; apply (wf_tm_ty (i := lM) eq_refl (t := letboxT l' l Δ M t' t));
                      apply wf_letboxT; assumption]
             | solve [apply lequiv_refl; assumption]
             | solve [eapply eqty_trans; [eassumption | assumption]]
             | solve [eapply eqty_lconv; eassumption]
             | solve [eapply lequiv_trans; eassumption] ].
Qed.

Lemma reds_letboxT l' l Δ M t' t t0 : reds t t0 -> reds (letboxT l' l Δ M t' t) (letboxT l' l Δ M t' t0).
Proof. unfold reds; induction 1; [constructor | econstructor; [constructor; eassumption | assumption]]. Qed.

Section LetboxTRed.
Context {G : gctx} {Θ D : ctx} {l1 l2 : lvl} {M : ty} {b : tm}
  (Hl1 : lwf (gL G) l1) (Hl2 : lwf (gL G) l2) (HD : [ G ; D ⊢[ lD ] ])
  (HM : [ G ; Θ ,, tyCTyp D l2 @ lzero ⊢[ lM ] M @ l1 ])
  (Hb : [ gext G (gdTy D lC l2) ; Θ⟪S⟫ ⊢[ lM ] b : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ]).

Lemma wf_letboxT_at {s} : [ G ; Θ ⊢[ lM ] s : tyCTyp D l2 @ lzero ] ->
  [ G ; Θ ⊢[ lM ] letboxT l1 l2 D M b s : M[lsingle s] @ l1 ].
Proof. intros; apply wf_letboxT; assumption. Qed.

Lemma tmred_letboxT_cong {s w} : [ G ; Θ ⊢[ lM ] s ⤳* w : tyCTyp D l2 @ lzero ] ->
  [ G ; Θ ⊢[ lM ] letboxT l1 l2 D M b s ⤳* letboxT l1 l2 D M b w : M[lsingle s] @ l1 ].
Proof.
  intros [Hs Hr Heq]. split.
  - now apply wf_letboxT_at.
  - now apply reds_letboxT.
  - apply eqtm_letboxT; try assumption; try (apply lequiv_refl; assumption).
    + now apply eqc_refl.
    + now apply eqty_refl.
    + now apply eqtm_refl.
Qed.

Lemma tmred_letboxT_beta {T} : [ G ; D ⊢[ lC ] T @ l2 ] ->
  [ G ; Θ ⊢[ lM ] letboxT l1 l2 D M b (boxT T) ⤳* b⦃gsingle (GTy T)⦄ : M[lsingle (boxT T)] @ l1 ].
Proof.
  intros HT. assert (HΘ : [ G ; Θ ⊢[ lM ] ]) by exact (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)).
  split.
  - apply wf_letboxT_at, wf_boxT; assumption.
  - econstructor; [constructor | constructor].
  - apply eqtm_letboxT_beta; assumption.
Qed.

End LetboxTRed.

Lemma wf_gext_ty {G Δ i l} : [ ⊢ G ] -> [ G ; Δ ⊢[ lD ] ] -> i = lC \/ i = lD -> lwf (gL G) l ->
  [ ⊢ gext G (gdTy Δ i l) ].
Proof. destruct G as [L Ψ]; unfold gext; cbn. intros; apply wfg_ty; assumption. Qed.

Lemma gwk_ok_step G D : gwk_ok (gwk_step gwk_id) (gext G D) G.
Proof. split; [reflexivity | constructor; constructor]. Qed.

(** A global shift commutes with a local substitution under a binder. *)
Lemma gshift_llift_ty (M : ty) e : M⟪S⟫[llift (gwk e)] = M[llift e]⟪S⟫.
Proof.
  rewrite gren_subst_ty. apply subst_ext_ty. intros n. rewrite llk_glren, !llk_llift.
  destruct n; [reflexivity |].
  unfold gwk. rewrite llk_glren. change (gren_tm ?x ?ξ) with x⟪ξ⟫. change (ren_tm ?x ?r) with x⟨r⟩.
  symmetry; apply gren_ren.
Qed.

(** The β-reduct of a substituted body is the body under the extended
    substitution. *)
Lemma letbox_reduct (t : tm) σ e o : (forall n, dnfo (σ n)) -> LK dnftm e ->
  (t⦃gup σ⦄[gwk e])⦃gsingle o⦄ = t⦃gcons σ o⦄[e].
Proof.
  intros Hσ He. rewrite gsubst_subst, gup_single_tm by exact Hσ. apply subst_ext. intros n.
  rewrite llk_glsubst. unfold gwk. rewrite llk_glren.
  change (gsubst_tm (gren_tm (llk e n) S) (gsingle o)) with ((llk e n)⟪S⟫⦃gsingle o⦄).
  rewrite (gsubst_gren_tm _ _ _ (fun j => GId j)) by reflexivity.
  apply gsubst_id; [exact (He n) | reflexivity].
Qed.

(** The identity instance of a global type variable, over a context
    convertible to its binding's. *)
Lemma wf_ty_gvar_id {G U Δ Y l} : in_gctx (gΨ G) U (gdTy Δ lC l) -> [ G ⊢[ lD ] Δ ≅ Y ] ->
  [ G ; Y ⊢[ lC ] tyGvar U (lshift 0) @ l ].
Proof.
  intros Hin Hc. destruct (eqctx_id_at Hc (i := lC) eq_refl) as [Hw Hn Ht Hv].
  eapply wft_gvar; [discriminate | exact Hw | exact Hin | apply lle_refl | exact Ht | exact I | exact Hv].
Qed.

(** ** The identity instance is valid *)

Section IdInst.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma gwa_lshift0 γ : (lshift 0)⟦γ⟧ = lshift 0.
Proof. now destruct γ. Qed.

(** The identity substitution is related to itself, at every global
    weakening. *)
Lemma VSubK_id {G X} : [ G ; X ⊢[ lD ] ] -> CtxRelG G X X -> VSubK G X (lshift 0) (lshift 0) X.
Proof.
  intros HX HR G' γ Hγ. rewrite gwa_lshift0.
  pose proof (gwk_ok_to Hγ) as EG.
  apply VSub_intro; [exact (HR _ _ Hγ) | apply tail_id | apply tail_id | intros n; exact I | intros n; exact I |].
  intros n A k Hin Θ d d' Hd. pose proof (ctx_glob _ _ _ (SubRel_ctx Hd)) as HG'.
  pose proof (in_ctx_wf (i := lD) eq_refl (gwa_ctx Hγ HG' HX) Hin) as HA.
  rewrite (subst_id_ty _ _ (wf_ty_nf HA) lshift0_id), lshift0_id. exact (V_var Hin _ _ _ Hd).
Qed.

(** Related substitutions under a global weakening. *)
Lemma SubRel_gwa {G Γ Δ d d' G' γ} : SubRel G Γ Δ d d' -> gwk_ok γ G' G -> [ ⊢ G' ] ->
  SubRel G' Γ⟦γ⟧ Δ⟦γ⟧ d⟦γ⟧ d'⟦γ⟧.
Proof.
  intros H Hγ HG. destruct (SubRel_dnf _ _ _ _ _ H) as [N N'].
  pose (ρ := mkKwk (G := G) (Γ := Δ) G' Δ⟦γ⟧ γ wk_id Hγ (wkwf_id _) (gwa_ctx Hγ HG (SubRel_ctx H))).
  eapply SubRel_ext; [| | exact (SubRel_kw _ _ _ ρ _ _ H)]; intros n;
    rewrite llk_kwsub, llk_gwa; unfold ktm; cbn [kw_r kw_γ ρ];
    apply ren_id_tm, dnftm_nftm, dnf_gwa; auto.
Qed.

End IdInst.

(** ** [letbox] on contextual types *)

Section LetboxT.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_laws' : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation VCtxSP := (@VCtxS EP EM EP LR_P).
Local Notation VCtxSPM := (@VCtxS EP EM EM LR_P).
Local Notation VCtxEqSP := (@VCtxEqS EP LR_P EP EM).
Local Notation VCtxEqSM := (@VCtxEqS EM LR_P EP EM).

(** The body's type. *)
Local Notation Mb M := (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]).

Lemma VS_letboxT {G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 t t0} :
  GValid EP EM G -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M @ l1 ] -> [ G ; Γ ,, tyCTyp Δ' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
  [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t1 : Mb M @ l1 ] ->
  [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : Mb M @ l1 ] ->
  [ gext G (gdTy Δ' lC l4) ; Γ⟪S⟫ ⊢[ lM ] t2 : Mb M' @ l3 ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l2 @ lzero ] -> [ G ; Γ ⊢[ lM ] t0 : tyCTyp Δ l2 @ lzero ] ->
  VCtxSM G Γ -> VCtxSP G Δ -> VCtxSPM G Δ -> VCtxEqSP G Δ Δ' -> VCtxEqSM G Δ Δ' ->
  VTySM G (Γ ,, tyCTyp Δ l2 @ lzero) M M' l1 ->
  VTmSM (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (Mb M) l1 ->
  VTmSM (gext G (gdTy Δ' lC l4)) Γ⟪S⟫ t2 t2 (Mb M') l3 ->
  VTmSM G Γ t t0 (tyCTyp Δ l2) lzero ->
  VTmSM G Γ (letboxT l1 l2 Δ M t1 t) (letboxT l3 l4 Δ' M' t2 t0) M[lsingle t] l1.
Proof.
  intros HG Hl13 Hl24 Hl1 Hl2 HΔ HΔ' HΔΔ' HM HM' Ht1 Ht2 Ht2' Ht Ht0 VΓ VΔP VΔM VEqP VEqM VM Vb Vb' Vt.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  (* global facts *)
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσl. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (GSubRel_sym EP EM HG Hσ) as Hσs.
  assert (EL : gL G' = gL G) by exact (gsr_L _ _ _ _ _ _ Hσ).
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  pose proof (SubRel_refl_r He) as He'.
  (* the contexts *)
  pose proof (gs_ctx EP EM Hσ HΔ) as HD. pose proof (gs_ctx EP EM Hσr HΔ') as HD'.
  pose proof (gs_ctx EP EM Hσr HΔ) as HDr.
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  pose proof (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) He') as He'r.
  pose proof (CtxRelG_escape_P EP EM (VEqP _ _ _ Hσ) HD HD') as [HgDD' HDD'].
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hσ) HD HDr) as [_ HDDr].
  (* the typings of both sides, by inversion *)
  assert (Hw : [ G ; Γ ⊢[ lM ] letboxT l1 l2 Δ M t1 t : M[lsingle t] @ l1 ]) by (apply wf_letboxT; assumption).
  assert (Hw' : [ G ; Γ ⊢[ lM ] letboxT l3 l4 Δ' M' t2 t0 : M'[lsingle t0] @ l3 ]).
  { apply wf_letboxT; try assumption; try exact (lequiv_wf_r _ _ _ Hl13); try exact (lequiv_wf_r _ _ _ Hl24).
    eapply wf_conv; [exact Ht0 | apply eqty_CTyp; [exact (ctx_of_wf_tm (i := lM) eq_refl Ht) | exact (eqctx_sym_D HΔΔ') | exact (lequiv_sym _ _ _ Hl24)]]. }
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (SubRel_wf_l _ _ _ _ _ He'r) as Hew'. rewrite (@gm_layer_M EP EM EMl) in Hew'.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσr Hw') Hew') as X'.
  rewrite gs_letboxT, subst_letboxT in X, X' |- *. rewrite gs_letboxT, subst_letboxT.
  destruct (letboxT_inv X) as (_ & _ & HDw & HM1 & Hb1 & Hs & _ & _).
  destruct (letboxT_inv X') as (_ & _ & HD'w & HM1' & Hb2 & Hs' & _ & _).
  clear X X'.
  rewrite gs_single_ty, !single_subst_ty by assumption.
  (* the scrutinee: related at [□Δ⦃σ⦄] *)
  pose proof (vp_ctx_refl_l EP EM HD (VΔP _ _ _ Hσ) (VΔM _ _ _ Hσ)) as VD.
  assert (Hl2' : lwf (gL G') l2) by (now rewrite EL).
  pose proof (LR_ctyp EP EM HΘ HD HD Hl2' (lequiv_refl _ _ Hl2') VD) as HLc.
  assert (Vss : forall d d', @SubRel EM LRM G' Γ⦃σ⦄ Θ d d' ->
            @LRtm EM LRM lzero G' Θ (tyCTyp Δ⦃σ⦄ l2) (tyCTyp Δ⦃σ⦄ l2) (t⦃σ⦄)[d] (t0⦃σ'⦄)[d']).
  { intros d d' Hd. pose proof (Vt _ _ _ Hσ _ _ (gwk_ok_id G') _ _ _ Hd) as Y; cbn [gwa] in Y.
    rewrite gs_tyCTyp in Y. exact Y. }
  destruct (Vss _ _ He) as (R & HR & Hr).
  pose proof (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ HR HLc _ _) Hr) as (w & w' & Hsw & Hs'w & Hg & Hg' & Hn & Hn').
  (* the scrutinees and their normal forms, related *)
  assert (HLww : @LRtm EM LRM lzero G' Θ (tyCTyp Δ⦃σ⦄ l2) (tyCTyp Δ⦃σ⦄ l2) w w').
  { exists (@CTypRel EM LRM G' Θ Δ⦃σ⦄ Δ⦃σ⦄ l2 l2); split; [exact HLc|].
    exists w, w'. refine (conj _ (conj _ (conj Hg (conj Hg' (conj Hn Hn'))))); apply tmred_refl.
    - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hsw)).
    - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  assert (HLsw' : @LRtm EM LRM lzero G' Θ (tyCTyp Δ⦃σ⦄ l2) (tyCTyp Δ⦃σ⦄ l2) (t⦃σ⦄)[e] w').
  { eapply LRtm_red; [exact HLww | exact Hsw |]. apply tmred_refl.
    exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  pose proof (LRtm_trans HLsw' (LRtm_sym HLww)) as HLsw.
  pose proof (LRtm_trans (LRtm_sym (Vss _ _ He)) HLsw') as HLs'w'.
  pose proof (LRtm_trans (LRtm_sym HLs'w') (LRtm_sym (Vss _ _ He'))) as HLw'x.
  rewrite (@gm_layer_M EP EM EMl) in Hsw, Hs'w.
  (* the motive at related scrutinees *)
  assert (VMat : forall d d' a a', @SubRel EM LRM G' Γ⦃σ⦄ Θ d d' ->
            @LRtm EM LRM lzero G' Θ (tyCTyp Δ⦃σ⦄ l2) (tyCTyp Δ⦃σ⦄ l2) a a' ->
            @LRty EM LRM l1 G' Θ (M⦃σ⦄)[llift d][lsingle a] (M'⦃σ'⦄)[llift d'][lsingle a']).
  { intros d d' a a' Hd Ha. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
    rewrite !lift_single_ty by assumption.
    pose proof (VM _ _ _ Hσ _ _ (gwk_ok_id G')) as Y; cbn [gwa] in Y. rewrite gs_cext, gs_tyCTyp in Y.
    apply Y, SubRel_cons; [exact Hd | exact Ha]. }
  assert (VMat_l : forall d d' a a', @SubRel EM LRM G' Γ⦃σ⦄ Θ d d' ->
            @LRtm EM LRM lzero G' Θ (tyCTyp Δ⦃σ⦄ l2) (tyCTyp Δ⦃σ⦄ l2) a a' ->
            @LRty EM LRM l1 G' Θ (M⦃σ⦄)[llift d][lsingle a] (M⦃σ⦄)[llift d'][lsingle a']).
  { intros d d' a a' Hd Ha. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
    rewrite !lift_single_ty by assumption.
    pose proof (VTy_refl_l (VM _ _ _ Hσ _ _ (gwk_ok_id G'))) as Y; cbn [gwa] in Y. rewrite gs_cext, gs_tyCTyp in Y.
    apply Y, SubRel_cons; [exact Hd | exact Ha]. }
  assert (Hl13' : lequiv (gL G') l1 l3) by (now rewrite EL).
  (* conversion to the goal's types and anti-reduction: what the cases share *)
  assert (Fin : forall u u',
    @LRtm EM LRM l1 G' Θ (M⦃σ⦄)[llift e][lsingle w] (M'⦃σ'⦄)[llift e'][lsingle w'] u u' ->
    [ G' ; Θ ⊢[ lM ] letboxT l1 l2 Δ⦃σ⦄ (M⦃σ⦄)[llift e] (t1⦃gup σ⦄)[gwk e] (t⦃σ⦄)[e] ⤳* u
        : (M⦃σ⦄)[llift e][lsingle (t⦃σ⦄)[e]] @ l1 ] ->
    [ G' ; Θ ⊢[ lM ] letboxT l3 l4 Δ'⦃σ'⦄ (M'⦃σ'⦄)[llift e'] (t2⦃gup σ'⦄)[gwk e'] (t0⦃σ'⦄)[e'] ⤳* u'
        : (M'⦃σ'⦄)[llift e'][lsingle (t0⦃σ'⦄)[e']] @ l3 ] ->
    @LRtm EM LRM l1 G' Θ (M⦃σ⦄)[llift e][lsingle (t⦃σ⦄)[e]] (M⦃σ⦄)[llift e'][lsingle (t⦃σ⦄)[e']]
      (letboxT l1 l2 Δ⦃σ⦄ (M⦃σ⦄)[llift e] (t1⦃gup σ⦄)[gwk e] (t⦃σ⦄)[e])
      (letboxT l3 l4 Δ'⦃σ'⦄ (M'⦃σ'⦄)[llift e'] (t2⦃gup σ'⦄)[gwk e'] (t0⦃σ'⦄)[e'])).
  { intros u u' Z Hu Hu'.
    pose proof (LRtm_conv_l Z (VMat_l _ _ _ _ (SubRel_refl_l He) HLsw)) as Z1.
    pose proof (LRtm_conv_r Z1 (LRty_sym (VMat _ _ _ _ He' (LRtm_sym HLw'x)))) as Z2.
    destruct (VMat _ _ _ _ He' (Vss _ _ He')) as [RT HRT].
    destruct (escape_ty _ _ _ _ _ _ _ _ HRT) as (_ & _ & HTT).
    pose proof (geq_ty_sound HTT) as HTTd. rewrite (@gm_layer_M EP EM EMl) in HTTd.
    eapply LRtm_red; [exact Z2 | rewrite (@gm_layer_M EP EM EMl); exact Hu |].
    rewrite (@gm_layer_M EP EM EMl).
    eapply (tmred_conv _ _ _ _ _ eq_refl); [exact (tmred_lconv _ _ _ _ _ Hu' Hl13') |].
    exact (eqty_sym _ _ _ _ _ _ HTTd). }
  assert (Hl1' : lwf (gL G') l1) by (now rewrite EL).
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  (* the right scrutinee, at the right-hand contextual type *)
  assert (HCC : [ G' ; Θ ⊢[ lM ] tyCTyp Δ⦃σ⦄ l2 ≅ tyCTyp Δ'⦃σ'⦄ l4 @ lzero ])
    by (apply eqty_CTyp; [exact HΘ | exact HDD' | now rewrite EL]).
  pose proof (tmred_conv _ _ _ _ _ eq_refl Hs'w HCC) as Hs'w4.
  destruct Hn as [T1 T1' HV | ν ν' Hνν].
  - (* box: β-reduce, and use the body at the extended substitutions *)
    destruct HV as (HE & HT1 & VT1P & VT1M). subst T1'.
    assert (Hσx : GSubRel G' (gext G (gdTy Δ lC l2)) (gcons σ (GTy T1)) (gcons σ' (GTy T1))).
    { apply (GSubRel_cons EP EM Hσ); cbn [gdecl_gsubst gobj_wf dnfo GObjRel].
      - exact (wf_ty_dnf HT1).
      - exact HT1.
      - exact (ctxconv_ty (i := lC) HDDr eq_refl HT1).
      - exact (conj (fun _ => eq_refl) (conj VT1P VT1M)).
      - exact (conj (fun _ => eq_refl) (conj (VTyG_transport (VΔP _ _ _ Hσ) VT1P)
                                              (VTyG_transport (VΔM _ _ _ Hσ) VT1M))). }
    pose proof (Vb _ _ _ Hσx G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
    rewrite gcons_shift_ctx in Y. specialize (Y _ _ _ He).
    assert (Eb : (boxT (tyGvar 0 (lshift 0)))⦃gcons σ (GTy T1)⦄ = boxT T1).
    { change ((boxT (tyGvar 0 (lshift 0)))⦃gcons σ (GTy T1)⦄) with (boxT T1[lshift 0]).
      now rewrite nf_id_ty by exact (wf_ty_nf HT1). }
    rewrite gs_single_ty, gcons_shift_ty, Eb, !single_subst_ty in Y by assumption.
    cbn [subst Subst_tm subst_tm] in Y.
    pose proof (LRtm_conv_r Y (VMat _ _ _ _ He' HLww)) as Z.
    apply (Fin _ _ Z).
    + rewrite <- letbox_reduct by assumption.
      eapply tmred_trans; [exact (tmred_letboxT_cong Hl1' Hl2' HDw HM1 Hb1 Hsw) |].
      eapply (tmred_conv _ _ _ _ _ eq_refl); [exact (tmred_letboxT_beta Hl1' Hl2' HDw HM1 Hb1 HT1) |].
      destruct (VMat_l _ _ _ _ (SubRel_refl_l He) (LRtm_sym HLsw)) as [RT HRT].
      destruct (escape_ty _ _ _ _ _ _ _ _ HRT) as (_ & _ & HTT).
      pose proof (geq_ty_sound HTT) as HTTd. rewrite (@gm_layer_M EP EM EMl) in HTTd. exact HTTd.
    + rewrite <- letbox_reduct by assumption.
      assert (Hl3' : lwf (gL G') l3) by exact (lequiv_wf_r _ _ _ Hl13').
      assert (Hl4' : lwf (gL G') l4) by (rewrite EL; exact (lequiv_wf_r _ _ _ Hl24)).
      assert (HT1' : [ G' ; Δ'⦃σ'⦄ ⊢[ lC ] T1 @ l4 ]).
      { eapply wft_lconv; [exact (ctxconv_ty (i := lC) HDD' eq_refl HT1) | rewrite EL; exact (lequiv_sym _ _ _ Hl24)]. }
      eapply tmred_trans; [exact (tmred_letboxT_cong Hl3' Hl4' HD'w HM1' Hb2 Hs'w4) |].
      eapply (tmred_conv _ _ _ _ _ eq_refl); [exact (tmred_letboxT_beta Hl3' Hl4' HD'w HM1' Hb2 HT1') |].
      pose proof (LRty_trans (LRty_sym (VMat _ _ _ _ He' HLww)) (VMat _ _ _ _ He' (LRtm_sym HLs'w'))) as [RT HRT].
      destruct (escape_ty _ _ _ _ _ _ _ _ HRT) as (_ & _ & HTT).
      pose proof (geq_ty_sound HTT) as HTTd. rewrite (@gm_layer_M EP EM EMl) in HTTd.
      eapply eqty_lconv; [exact HTTd | exact (lequiv_sym _ _ _ Hl13')].
  - (* neutral: letbox is neutral *)
    assert (Hl3' : lwf (gL G') l3) by exact (lequiv_wf_r _ _ _ Hl13').
    assert (Hl24' : lequiv (gL G') l2 l4) by (now rewrite EL).
    (* the motives, related *)
    pose proof (VS_CTyp EP EM (ctx_of_wf_tm (i := lM) eq_refl Ht) HΔ HΔ Hl2 (lequiv_refl _ _ Hl2) VΔP VΔM) as VC.
    pose proof (VC _ _ _ Hσl _ _ (gwk_ok_id G')) as VCa; cbn [gwa] in VCa. rewrite gs_tyCTyp in VCa.
    assert (HCe : [ G' ; Θ ⊢[ ge_layer ] (tyCTyp Δ⦃σ⦄ l2)[e] @ lzero ])
      by (rewrite (@gm_layer_M EP EM EMl); cbn; apply wft_CTyp; assumption).
    pose proof (SubRel_lift He VCa HCe I) as Hlift. cbn [subst Subst_ty subst_ty] in Hlift.
    pose proof (VM _ _ _ Hσ _ _ (gwk_ok_id G')) as YM; cbn [gwa] in YM. rewrite gs_cext, gs_tyCTyp in YM.
    destruct (YM _ _ _ Hlift) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (_ & _ & HgM).
    (* the bodies, related under the new binding *)
    pose proof (wf_gext_ty (i := lC) HG' HD (or_introl eq_refl) Hl2') as HG1.
    pose proof (gwk_ok_step G' (gdTy Δ⦃σ⦄ lC l2)) as Hγ1.
    pose proof (gwk_ctx Hγ1 HG1 HD) as HDs.
    pose proof (CtxRelG_trans (VΔP _ _ _ Hσ) (CtxRelG_sym (VΔP _ _ _ Hσ))) as XP.
    pose proof (CtxRelG_trans (VΔM _ _ _ Hσ) (CtxRelG_sym (VΔM _ _ _ Hσ))) as XM.
    assert (Hin0 : in_gctx (gΨ (gext G' (gdTy Δ⦃σ⦄ lC l2))) 0 (gdTy Δ⦃σ⦄⟪S⟫ lC l2))
      by exact (ing_here _ (gdTy Δ⦃σ⦄ lC l2)).
    assert (HlC : forall E0 : GenericEq, lle lC (@ge_layer E0))
      by (intros E0; exact (lle_trans lC lD _ ltac:(unfold lle; cbn; lia) ge_lle_D)).
    pose proof (VTyG_gvar_ne (E := EP) (LP := LR_P) (δ := lshift 0) (δ' := lshift 0) Hin0 (HlC EP) I I (VSubK_id HDs (CtxRelG_gwk XP Hγ1)))
      as UP.
    pose proof (VTyG_gvar_ne (E := EM) (LP := LR_P) (δ := lshift 0) (δ' := lshift 0) Hin0 (HlC EM) I I (VSubK_id HDs (CtxRelG_gwk XM Hγ1)))
      as UM.
    assert (Hσu : GSubRel (gext G' (gdTy Δ⦃σ⦄ lC l2)) (gext G (gdTy Δ lC l2))
                    (gsub_up_id (gdTy Δ lC l2) σ) (gsub_up_id (gdTy Δ lC l2) σ')).
    { apply (GSubRel_up_id EP EM (D := gdTy Δ lC l2) Hσ); cbn [gdecl_gsubst gdecl_ren id_obj gobj_wf GObjRel].
      - exact HG1.
      - exact (wf_ty_gvar_id Hin0 (eqc_refl _ _ _ HDs)).
      - exact (wf_ty_gvar_id Hin0 (gwk_eqctx Hγ1 HG1 HDDr)).
      - exact (conj (fun _ => eq_refl) (conj UP UM)).
      - exact (conj (fun _ => eq_refl)
                 (conj (VTyG_transport (CtxRelG_gwk (VΔP _ _ _ Hσ) Hγ1) UP)
                       (VTyG_transport (CtxRelG_gwk (VΔM _ _ _ Hσ) Hγ1) UM))). }
    pose proof (Vb _ _ _ Hσu _ _ (gwk_ok_id _)) as Yb; cbn [gwa] in Yb.
    rewrite <- (gsubst_up_id_tm _ _ σ Ht1), <- (gsubst_up_id_tm _ _ σ' Ht2) in Yb.
    rewrite gs_single_ty in Yb. unfold gsub_up_id in Yb. rewrite gcons_shift_ctx, gcons_shift_ty in Yb.
    rewrite <- gwa_gsubst_ctx, <- gwa_gsubst_ty in Yb.
    change ((boxT (tyGvar 0 (lshift 0)))⦃gcons (gsub_wk σ (gwk_step gwk_id)) (id_obj (gdTy Δ lC l2) 0)⦄)
      with (boxT (tyGvar 0 (lshift 0))) in Yb.
    pose proof (Yb _ _ _ (SubRel_gwa He Hγ1 HG1)) as Yb'.
    assert (Ngwk : LK nftm (gwk e)) by (intros n; apply dnftm_nftm, (lk_dnf_gwk _ De)).
    assert (Hgb : @geq_tm EM (gext G' (gdTy Δ⦃σ⦄ lC l2)) Θ⟪S⟫ (t1⦃gup σ⦄)[gwk e] (t2⦃gup σ'⦄)[gwk e']
                    (Mb (M⦃σ⦄)[llift e]) l1).
    { rewrite <- gshift_llift_ty.
      change (boxT (tyGvar 0 (lshift 0))) with ((boxT (tyGvar 0 (lshift 0)))[gwk e]).
      rewrite <- (single_subst_ty (gwk e) Ngwk). exact (LRtm_geq Yb'). }
    pose proof (gne_tm_letboxT (EP := EP) (EM := EM) Hl13' Hl24' HgDD' HM1 HgM HM1' Hgb Hb2 Hνν) as Hν.
    destruct (VMat _ _ _ _ He HLww) as [Rν HRν].
    destruct (escape_ty _ _ _ _ _ _ _ _ HRν) as (_ & _ & Hgν).
    assert (Hν' := gne_tm_conv Hν (geq_ty_sound Hgν)).
    refine (Fin _ _ (ex_intro _ Rν (conj HRν (LR_neutral _ _ _ _ _ _ _ HRν _ _ Hν Hν'))) _ _).
    + exact (tmred_letboxT_cong Hl1' Hl2' HDw HM1 Hb1 Hsw).
    + assert (Hl4' : lwf (gL G') l4) by exact (lequiv_wf_r _ _ _ Hl24').
      exact (tmred_letboxT_cong Hl3' Hl4' HD'w HM1' Hb2 Hs'w4).
Qed.

End LetboxT.
