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

Lemma letboxt_inv {G Γ l' l Δ A M t' t T k} : [ G ; Γ ⊢[ lM ] letboxt l' l Δ A M t' t : T @ k ] ->
  lwf (gL G) l' /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\ [ G ; Δ ⊢[ lD ] A @ l ] /\
  [ G ; Γ ,, tyCTrm Δ A l @ lzero ⊢[ lM ] M @ l' ] /\
  [ gext G (gdTm Δ lC A l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] /\
  [ G ; Γ ⊢[ lM ] t : tyCTrm Δ A l @ lzero ] /\
  [ G ; Γ ⊢[ lM ] T ≅ M[lsingle t] @ k ] /\ lequiv (gL G) k l'.
Proof.
  intros H. remember lM as i eqn:Ei. remember (letboxt l' l Δ A M t' t) as u eqn:Eu.
  induction H; inversion Eu; subst; try discriminate;
    try match goal with IH : lM = lM -> _ |- _ =>
          destruct (IH eq_refl eq_refl) as (? & ? & ? & ? & ? & ? & ? & ? & ?) end;
    repeat match goal with |- _ /\ _ => split end; try assumption.
  all: first [ solve [apply eqty_refl; apply (wf_tm_ty (i := lM) eq_refl (t := letboxt l' l Δ A M t' t));
                      apply wf_letboxt; assumption]
             | solve [apply lequiv_refl; assumption]
             | solve [eapply eqty_trans; [eassumption | assumption]]
             | solve [eapply eqty_lconv; eassumption]
             | solve [eapply lequiv_trans; eassumption] ].
Qed.

Lemma reds_letboxt l' l Δ A M t' t t0 : reds t t0 -> reds (letboxt l' l Δ A M t' t) (letboxt l' l Δ A M t' t0).
Proof. unfold reds; induction 1; [constructor | econstructor; [constructor; eassumption | assumption]]. Qed.

Section LetboxtRed.
Context {G : gctx} {Θ D : ctx} {A : ty} {l1 l2 : lvl} {M : ty} {b : tm}
  (Hl1 : lwf (gL G) l1) (Hl2 : lwf (gL G) l2) (HD : [ G ; D ⊢[ lD ] ]) (HA : [ G ; D ⊢[ lD ] A @ l2 ])
  (HM : [ G ; Θ ,, tyCTrm D A l2 @ lzero ⊢[ lM ] M @ l1 ])
  (Hb : [ gext G (gdTm D lC A l2) ; Θ⟪S⟫ ⊢[ lM ] b : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ]).

Lemma tmred_letboxt_cong {s w} : [ G ; Θ ⊢[ lM ] s ⤳* w : tyCTrm D A l2 @ lzero ] ->
  [ G ; Θ ⊢[ lM ] letboxt l1 l2 D A M b s ⤳* letboxt l1 l2 D A M b w : M[lsingle s] @ l1 ].
Proof.
  intros [Hs Hr Heq]. split.
  - apply wf_letboxt; assumption.
  - now apply reds_letboxt.
  - apply eqtm_letboxt; try assumption; try (apply lequiv_refl; assumption).
    + now apply eqc_refl.
    + now apply eqty_refl.
    + now apply eqty_refl.
    + now apply eqtm_refl.
Qed.

Lemma tmred_letboxt_beta {t} : [ G ; D ⊢[ lC ] t : A @ l2 ] ->
  [ G ; Θ ⊢[ lM ] letboxt l1 l2 D A M b (boxt t) ⤳* b⦃gsingle (GTm t)⦄ : M[lsingle (boxt t)] @ l1 ].
Proof.
  intros Ht. assert (HΘ : [ G ; Θ ⊢[ lM ] ]) by exact (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)).
  split.
  - apply wf_letboxt, wf_boxt; assumption.
  - econstructor; [constructor | constructor].
  - apply eqtm_letboxt_beta; assumption.
Qed.

End LetboxtRed.

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

Lemma wf_tm_gvar_id {G u Δ A Y l} : in_gctx (gΨ G) u (gdTm Δ lC A l) -> [ G ⊢[ lD ] Δ ≅ Y ] ->
  [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Y ⊢[ lC ] gvar u (lshift 0) : A @ l ].
Proof.
  intros Hin Hc HA. destruct (eqctx_id_at Hc (i := lC) eq_refl) as [Hw Hn Ht Hv].
  pose proof (wf_gvar _ _ _ _ _ _ _ _ _ Hw Hin (lle_refl _) Ht I Hv) as X.
  now rewrite nf_id_ty in X by exact (wf_ty_nf HA).
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
  assert (EL : gL G <= gL G') by exact (gsr_L _ _ _ _ _ _ Hσ).
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  pose proof (SubRel_refl_r He) as He'.
  (* the contexts *)
  pose proof (gs_ctx EP EM Hσ HΔ compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ' compt_D) as HD'.
  pose proof (gs_ctx EP EM Hσr HΔ compt_D) as HDr.
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
  assert (Hl2' : lwf (gL G') l2) by (lup EL).
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
  assert (Hl13' : lequiv (gL G') l1 l3) by (lup EL).
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
  assert (Hl1' : lwf (gL G') l1) by (lup EL).
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  (* the right scrutinee, at the right-hand contextual type *)
  assert (HCC : [ G' ; Θ ⊢[ lM ] tyCTyp Δ⦃σ⦄ l2 ≅ tyCTyp Δ'⦃σ'⦄ l4 @ lzero ])
    by (apply eqty_CTyp; [exact HΘ | exact HDD' | lup EL]).
  pose proof (tmred_conv _ _ _ _ _ eq_refl Hs'w HCC) as Hs'w4.
  destruct Hn as [T1 T1' HV | ν ν' Hνν].
  - (* box: β-reduce, and use the body at the extended substitutions *)
    destruct HV as (HE & HT1 & HT1c & VT1P & VT1M).
    assert (Hσx : GSubRel G' (gext G (gdTy Δ lC l2)) (gcons σ (GTy T1)) (gcons σ' (GTy T1'))).
    { apply (GSubRel_cons2 EP EM Hσ); cbn [gdecl_gsubst gobj_wf dnfo GObjRel].
      - exact (wf_ty_dnf HT1).
      - exact (wf_ty_dnf HT1c).
      - exact HT1.
      - exact (ctxconv_ty (i := lC) HDDr eq_refl HT1c).
      - exact (conj (fun _ => HE) (conj VT1P VT1M)).
      - exact (conj (fun _ => ty_leq_refl _)
                 (conj (VTyG_trans VT1P (VTyG_sym VT1P)) (VTyG_trans VT1M (VTyG_sym VT1M)))).
      - exact (conj (fun _ => ty_leq_refl _)
                 (conj (VTyG_transport (VΔP _ _ _ Hσ) (VTyG_trans (VTyG_sym VT1P) VT1P))
                       (VTyG_transport (VΔM _ _ _ Hσ) (VTyG_trans (VTyG_sym VT1M) VT1M)))). }
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
      assert (Hl4' : lwf (gL G') l4) by (lup EL).
      assert (HT1' : [ G' ; Δ'⦃σ'⦄ ⊢[ lC ] T1' @ l4 ]).
      { eapply wft_lconv; [exact (ctxconv_ty (i := lC) HDD' eq_refl HT1c) | lup EL]. }
      eapply tmred_trans; [exact (tmred_letboxT_cong Hl3' Hl4' HD'w HM1' Hb2 Hs'w4) |].
      eapply (tmred_conv _ _ _ _ _ eq_refl); [exact (tmred_letboxT_beta Hl3' Hl4' HD'w HM1' Hb2 HT1') |].
      pose proof (LRty_trans (LRty_sym (VMat _ _ _ _ He' (LRtm_trans (LRtm_sym HLww) HLww)))
                    (VMat _ _ _ _ He' (LRtm_sym HLs'w'))) as [RT HRT].
      destruct (escape_ty _ _ _ _ _ _ _ _ HRT) as (_ & _ & HTT).
      pose proof (geq_ty_sound HTT) as HTTd. rewrite (@gm_layer_M EP EM EMl) in HTTd.
      eapply eqty_lconv; [exact HTTd | exact (lequiv_sym _ _ _ Hl13')].
  - (* neutral: letbox is neutral *)
    assert (Hl3' : lwf (gL G') l3) by exact (lequiv_wf_r _ _ _ Hl13').
    assert (Hl24' : lequiv (gL G') l2 l4) by (lup EL).
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
      - exact (conj (fun _ => ty_leq_refl _) (conj UP UM)).
      - exact (conj (fun _ => ty_leq_refl _)
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

(** ** [letbox] on contextual terms *)

Section Letboxt.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_laws'' : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation VCtxSP := (@VCtxS EP EM EP LR_P).
Local Notation VCtxSPM := (@VCtxS EP EM EM LR_P).
Local Notation VCtxEqSP := (@VCtxEqS EP LR_P EP EM).
Local Notation VCtxEqSM := (@VCtxEqS EM LR_P EP EM).
Local Notation Mbt M := (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]).

Lemma VS_letboxt {G Γ l1 l2 l3 l4 Δ Δ' A A' M M' t1 t2 t t0} :
  GValid EP EM G -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Δ ⊢[ lD ] A @ l2 ] -> [ G ; Δ' ⊢[ lD ] A' @ l4 ] -> [ G ; Δ ⊢[ lD ] A ≅ A' @ l2 ] ->
  [ G ; Γ ,, tyCTrm Δ A l2 @ lzero ⊢[ lM ] M @ l1 ] -> [ G ; Γ ,, tyCTrm Δ' A' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
  [ gext G (gdTm Δ lC A l2) ; Γ⟪S⟫ ⊢[ lM ] t1 : Mbt M @ l1 ] ->
  [ gext G (gdTm Δ lC A l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : Mbt M @ l1 ] ->
  [ gext G (gdTm Δ' lC A' l4) ; Γ⟪S⟫ ⊢[ lM ] t2 : Mbt M' @ l3 ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTrm Δ A l2 @ lzero ] -> [ G ; Γ ⊢[ lM ] t0 : tyCTrm Δ A l2 @ lzero ] ->
  VCtxSM G Γ -> VCtxSP G Δ -> VCtxSPM G Δ -> VCtxEqSP G Δ Δ' -> VCtxEqSM G Δ Δ' ->
  @VTyS EP EM EP LR_P G Δ A A' l2 -> @VTyS EP EM EM LR_P G Δ A A' l2 ->
  VTySM G (Γ ,, tyCTrm Δ A l2 @ lzero) M M' l1 ->
  VTmSM (gext G (gdTm Δ lC A l2)) Γ⟪S⟫ t1 t2 (Mbt M) l1 ->
  VTmSM (gext G (gdTm Δ' lC A' l4)) Γ⟪S⟫ t2 t2 (Mbt M') l3 ->
  VTmSM G Γ t t0 (tyCTrm Δ A l2) lzero ->
  VTmSM G Γ (letboxt l1 l2 Δ A M t1 t) (letboxt l3 l4 Δ' A' M' t2 t0) M[lsingle t] l1.
Proof.
  intros HG Hl13 Hl24 Hl1 Hl2 HΔ HΔ' HΔΔ' HA HA' HAA' HM HM' Ht1 Ht2 Ht2' Ht Ht0 VΓ VΔP VΔM VEqP VEqM VAP VAM
    VM Vb Vb' Vt.
  pose proof (VTyS_trans EP EM VAP (VTyS_sym EP EM HG VΔP VAP)) as VAAP.
  pose proof (VTyS_trans EP EM VAM (VTyS_sym EP EM HG VΔM VAM)) as VAAM.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  (* global facts *)
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσl. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  pose proof (GSubRel_sym EP EM HG Hσ) as Hσs.
  assert (EL : gL G <= gL G') by exact (gsr_L _ _ _ _ _ _ Hσ).
  pose proof (SubRel_ctx He) as HΘ; rewrite (@gm_layer_M EP EM EMl) in HΘ.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  pose proof (SubRel_refl_r He) as He'.
  (* the contexts *)
  pose proof (gs_ctx EP EM Hσ HΔ compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ' compt_D) as HD'.
  pose proof (gs_ctx EP EM Hσr HΔ compt_D) as HDr.
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  pose proof (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) He') as He'r.
  pose proof (CtxRelG_escape_P EP EM (VEqP _ _ _ Hσ) HD HD') as [HgDD' HDD'].
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hσ) HD HDr) as [_ HDDr].
  (* the typings of both sides, by inversion *)
  assert (Hw : [ G ; Γ ⊢[ lM ] letboxt l1 l2 Δ A M t1 t : M[lsingle t] @ l1 ]) by (apply wf_letboxt; assumption).
  assert (Hw' : [ G ; Γ ⊢[ lM ] letboxt l3 l4 Δ' A' M' t2 t0 : M'[lsingle t0] @ l3 ]).
  { apply wf_letboxt; try assumption; try exact (lequiv_wf_r _ _ _ Hl13); try exact (lequiv_wf_r _ _ _ Hl24).
    eapply wf_conv; [exact Ht0 | apply eqty_CTrm; [exact (ctx_of_wf_tm (i := lM) eq_refl Ht) | exact HΔ'
      | exact (eqctx_sym_D HΔΔ') | exact HA'
      | eapply eqty_lconv; [exact (ctxconv_eqty (i := lD) HΔΔ' eq_refl (eqty_sym _ _ _ _ _ _ HAA'))
                           | exact (lequiv_sym _ _ _ Hl24)]
      | exact (lequiv_sym _ _ _ Hl24)]]. }
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (SubRel_wf_l _ _ _ _ _ He'r) as Hew'. rewrite (@gm_layer_M EP EM EMl) in Hew'.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσr Hw') Hew') as X'.
  rewrite gs_letboxt, subst_letboxt in X, X' |- *. rewrite gs_letboxt, subst_letboxt.
  destruct (letboxt_inv X) as (_ & _ & HDw & HAw & HM1 & Hb1 & Hs & _ & _).
  destruct (letboxt_inv X') as (_ & _ & HD'w & HA'w & HM1' & Hb2 & Hs' & _ & _).
  clear X X'.
  rewrite gs_single_ty, !single_subst_ty by assumption.
  (* the scrutinee: related at [□Δ⦃σ⦄] *)
  pose proof (vp_ctx_refl_l EP EM HD (VΔP _ _ _ Hσ) (VΔM _ _ _ Hσ)) as VD.
  assert (Hl2' : lwf (gL G') l2) by (lup EL).
  assert (VA : vp_ty (vpM EP EM) G' Δ⦃σ⦄ A⦃σ⦄ A⦃σ⦄ l2).
  { refine (conj (eqty_refl _ _ _ _ _ HAw) (conj _ _)).
    - exact (VAAP _ _ _ Hσl). - exact (VAAM _ _ _ Hσl). }
  pose proof (LR_ctrm EP EM HΘ HD HD HAw HAw Hl2' (lequiv_refl _ _ Hl2') VD VA VA) as HLc.
  assert (Vss : forall d d', @SubRel EM LRM G' Γ⦃σ⦄ Θ d d' ->
            @LRtm EM LRM lzero G' Θ (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) (t⦃σ⦄)[d] (t0⦃σ'⦄)[d']).
  { intros d d' Hd. pose proof (Vt _ _ _ Hσ _ _ (gwk_ok_id G') _ _ _ Hd) as Y; cbn [gwa] in Y.
    rewrite gs_tyCTrm in Y. exact Y. }
  destruct (Vss _ _ He) as (R & HR & Hr).
  pose proof (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ HR HLc _ _) Hr) as (w & w' & Hsw & Hs'w & Hg & Hg' & Hn & Hn').
  (* the scrutinees and their normal forms, related *)
  assert (HLww : @LRtm EM LRM lzero G' Θ (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) w w').
  { exists (@CTrmRel EM LRM G' Θ Δ⦃σ⦄ Δ⦃σ⦄ A⦃σ⦄ A⦃σ⦄ l2 l2); split; [exact HLc|].
    exists w, w'. refine (conj _ (conj _ (conj Hg (conj Hg' (conj Hn Hn'))))); apply tmred_refl.
    - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hsw)).
    - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  assert (HLsw' : @LRtm EM LRM lzero G' Θ (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) (t⦃σ⦄)[e] w').
  { eapply LRtm_red; [exact HLww | exact Hsw |]. apply tmred_refl.
    exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs'w)). }
  pose proof (LRtm_trans HLsw' (LRtm_sym HLww)) as HLsw.
  pose proof (LRtm_trans (LRtm_sym (Vss _ _ He)) HLsw') as HLs'w'.
  pose proof (LRtm_trans (LRtm_sym HLs'w') (LRtm_sym (Vss _ _ He'))) as HLw'x.
  rewrite (@gm_layer_M EP EM EMl) in Hsw, Hs'w.
  (* the motive at related scrutinees *)
  assert (VMat : forall d d' a a', @SubRel EM LRM G' Γ⦃σ⦄ Θ d d' ->
            @LRtm EM LRM lzero G' Θ (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) a a' ->
            @LRty EM LRM l1 G' Θ (M⦃σ⦄)[llift d][lsingle a] (M'⦃σ'⦄)[llift d'][lsingle a']).
  { intros d d' a a' Hd Ha. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
    rewrite !lift_single_ty by assumption.
    pose proof (VM _ _ _ Hσ _ _ (gwk_ok_id G')) as Y; cbn [gwa] in Y. rewrite gs_cext, gs_tyCTrm in Y.
    apply Y, SubRel_cons; [exact Hd | exact Ha]. }
  assert (VMat_l : forall d d' a a', @SubRel EM LRM G' Γ⦃σ⦄ Θ d d' ->
            @LRtm EM LRM lzero G' Θ (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2) a a' ->
            @LRty EM LRM l1 G' Θ (M⦃σ⦄)[llift d][lsingle a] (M⦃σ⦄)[llift d'][lsingle a']).
  { intros d d' a a' Hd Ha. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
    rewrite !lift_single_ty by assumption.
    pose proof (VTy_refl_l (VM _ _ _ Hσ _ _ (gwk_ok_id G'))) as Y; cbn [gwa] in Y. rewrite gs_cext, gs_tyCTrm in Y.
    apply Y, SubRel_cons; [exact Hd | exact Ha]. }
  assert (Hl13' : lequiv (gL G') l1 l3) by (lup EL).
  (* conversion to the goal's types and anti-reduction: what the cases share *)
  assert (Fin : forall u u',
    @LRtm EM LRM l1 G' Θ (M⦃σ⦄)[llift e][lsingle w] (M'⦃σ'⦄)[llift e'][lsingle w'] u u' ->
    [ G' ; Θ ⊢[ lM ] letboxt l1 l2 Δ⦃σ⦄ A⦃σ⦄ (M⦃σ⦄)[llift e] (t1⦃gup σ⦄)[gwk e] (t⦃σ⦄)[e] ⤳* u
        : (M⦃σ⦄)[llift e][lsingle (t⦃σ⦄)[e]] @ l1 ] ->
    [ G' ; Θ ⊢[ lM ] letboxt l3 l4 Δ'⦃σ'⦄ A'⦃σ'⦄ (M'⦃σ'⦄)[llift e'] (t2⦃gup σ'⦄)[gwk e'] (t0⦃σ'⦄)[e'] ⤳* u'
        : (M'⦃σ'⦄)[llift e'][lsingle (t0⦃σ'⦄)[e']] @ l3 ] ->
    @LRtm EM LRM l1 G' Θ (M⦃σ⦄)[llift e][lsingle (t⦃σ⦄)[e]] (M⦃σ⦄)[llift e'][lsingle (t⦃σ⦄)[e']]
      (letboxt l1 l2 Δ⦃σ⦄ A⦃σ⦄ (M⦃σ⦄)[llift e] (t1⦃gup σ⦄)[gwk e] (t⦃σ⦄)[e])
      (letboxt l3 l4 Δ'⦃σ'⦄ A'⦃σ'⦄ (M'⦃σ'⦄)[llift e'] (t2⦃gup σ'⦄)[gwk e'] (t0⦃σ'⦄)[e'])).
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
  assert (Hl1' : lwf (gL G') l1) by (lup EL).
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  (* the right scrutinee, at the right-hand contextual type *)
  assert (Hl24' : lequiv (gL G') l2 l4) by (lup EL).
  assert (HA'D : [ G' ; Δ⦃σ⦄ ⊢[ lD ] A'⦃σ'⦄ @ l2 ]).
  { eapply wft_lconv; [exact (ctxconv_ty (i := lD) (eqctx_sym_D HDD') eq_refl HA'w) | exact Hl24']. }
  destruct (VTyG_escape_P EP EM (VΔP _ _ _ Hσ) HD HAw HA'D (VAP _ _ _ Hσ)) as [HgAA' HAA'd].
  assert (HCC : [ G' ; Θ ⊢[ lM ] tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2 ≅ tyCTrm Δ'⦃σ'⦄ A'⦃σ'⦄ l4 @ lzero ])
    by (apply eqty_CTrm; assumption).
  pose proof (tmred_conv _ _ _ _ _ eq_refl Hs'w HCC) as Hs'w4.
  (* the type of the code, related across the substitutions *)
  assert (HAσ'D : [ G' ; Δ⦃σ⦄ ⊢[ lD ] A⦃σ'⦄ @ l2 ])
    by exact (ctxconv_ty (i := lD) (eqctx_sym_D HDDr) eq_refl (gs_ty EP EM Hσr HA)).
  destruct (VTyG_escape_P EP EM (VΔP _ _ _ Hσ) HD HAw HAσ'D (VAAP _ _ _ Hσ)) as [_ HAAr].
  destruct Hn as [c c' HV | ν ν' Hνν].
  - (* box: β-reduce, and use the body at the extended substitutions *)
    destruct HV as (HE & Hc & Hcc & VcP & VcM).
    pose proof (VTmG_trans (VTmG_sym VcP) VcP) as VcPr. pose proof (VTmG_trans (VTmG_sym VcM) VcM) as VcMr.
    assert (Hσx : GSubRel G' (gext G (gdTm Δ lC A l2)) (gcons σ (GTm c)) (gcons σ' (GTm c'))).
    { apply (GSubRel_cons2 EP EM Hσ); cbn [gdecl_gsubst gobj_wf dnfo GObjRel].
      - exact (wf_tm_dnf Hc).
      - exact (wf_tm_dnf Hcc).
      - exact Hc.
      - exact (ctxconv_tm (i := lC) HDDr eq_refl (wf_conv _ _ _ _ _ _ _ Hcc (eqty_sym _ _ _ _ _ _ HAAr))).
      - exact (conj HE (conj VcP VcM)).
      - exact (conj (tm_leq_refl _) (conj (VTmG_trans VcP (VTmG_sym VcP)) (VTmG_trans VcM (VTmG_sym VcM)))).
      - refine (conj (tm_leq_refl _) (conj _ _)).
        + exact (VTmG_conv (VTmG_transport (VΔP _ _ _ Hσ) VcPr) (VTyG_sym (VTyG_transport (VΔP _ _ _ Hσ) (VAAP _ _ _ Hσ)))).
        + exact (VTmG_conv (VTmG_transport (VΔM _ _ _ Hσ) VcMr) (VTyG_sym (VTyG_transport (VΔM _ _ _ Hσ) (VAAM _ _ _ Hσ)))). }
    pose proof (Vb _ _ _ Hσx G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
    rewrite gcons_shift_ctx in Y. specialize (Y _ _ _ He).
    assert (Eb : (boxt (gvar 0 (lshift 0)))⦃gcons σ (GTm c)⦄ = boxt c).
    { change ((boxt (gvar 0 (lshift 0)))⦃gcons σ (GTm c)⦄) with (boxt c[lshift 0]).
      now rewrite nf_id by exact (wf_tm_nf Hc). }
    rewrite gs_single_ty, gcons_shift_ty, Eb, !single_subst_ty in Y by assumption.
    cbn [subst Subst_tm subst_tm] in Y.
    pose proof (LRtm_conv_r Y (VMat _ _ _ _ He' HLww)) as Z.
    apply (Fin _ _ Z).
    + rewrite <- letbox_reduct by assumption.
      eapply tmred_trans; [exact (tmred_letboxt_cong Hl1' Hl2' HDw HAw HM1 Hb1 Hsw) |].
      eapply (tmred_conv _ _ _ _ _ eq_refl); [exact (tmred_letboxt_beta Hl1' Hl2' HDw HAw HM1 Hb1 Hc) |].
      destruct (VMat_l _ _ _ _ (SubRel_refl_l He) (LRtm_sym HLsw)) as [RT HRT].
      destruct (escape_ty _ _ _ _ _ _ _ _ HRT) as (_ & _ & HTT).
      pose proof (geq_ty_sound HTT) as HTTd. rewrite (@gm_layer_M EP EM EMl) in HTTd. exact HTTd.
    + rewrite <- letbox_reduct by assumption.
      assert (Hl3' : lwf (gL G') l3) by exact (lequiv_wf_r _ _ _ Hl13').
      assert (Hl4' : lwf (gL G') l4) by exact (lequiv_wf_r _ _ _ Hl24').
      assert (Hc' : [ G' ; Δ'⦃σ'⦄ ⊢[ lC ] c' : A'⦃σ'⦄ @ l4 ]).
      { eapply wf_lconv; [| exact (lequiv_sym _ _ _ Hl24')].
        exact (ctxconv_tm (i := lC) HDD' eq_refl (wf_conv _ _ _ _ _ _ _ Hcc (eqty_sym _ _ _ _ _ _ HAA'd))). }
      eapply tmred_trans; [exact (tmred_letboxt_cong Hl3' Hl4' HD'w HA'w HM1' Hb2 Hs'w4) |].
      eapply (tmred_conv _ _ _ _ _ eq_refl); [exact (tmred_letboxt_beta Hl3' Hl4' HD'w HA'w HM1' Hb2 Hc') |].
      pose proof (LRty_trans (LRty_sym (VMat _ _ _ _ He' (LRtm_trans (LRtm_sym HLww) HLww)))
                    (VMat _ _ _ _ He' (LRtm_sym HLs'w'))) as [RT HRT].
      destruct (escape_ty _ _ _ _ _ _ _ _ HRT) as (_ & _ & HTT).
      pose proof (geq_ty_sound HTT) as HTTd. rewrite (@gm_layer_M EP EM EMl) in HTTd.
      eapply eqty_lconv; [exact HTTd | exact (lequiv_sym _ _ _ Hl13')].
  - (* neutral: letbox is neutral *)
    assert (Hl3' : lwf (gL G') l3) by exact (lequiv_wf_r _ _ _ Hl13').
    (* the motives, related *)
    pose proof (VS_CTrm EP EM HG (ctx_of_wf_tm (i := lM) eq_refl Ht) HΔ HΔ HA HA Hl2 (lequiv_refl _ _ Hl2)
                  VΔP VΔM VΔP VΔM VAAP VAAM) as VC.
    pose proof (VC _ _ _ Hσl _ _ (gwk_ok_id G')) as VCa; cbn [gwa] in VCa. rewrite gs_tyCTrm in VCa.
    assert (HCe : [ G' ; Θ ⊢[ ge_layer ] (tyCTrm Δ⦃σ⦄ A⦃σ⦄ l2)[e] @ lzero ])
      by (rewrite (@gm_layer_M EP EM EMl); cbn; apply wft_CTrm; assumption).
    pose proof (SubRel_lift He VCa HCe I) as Hlift. cbn [subst Subst_ty subst_ty] in Hlift.
    pose proof (VM _ _ _ Hσ _ _ (gwk_ok_id G')) as YM; cbn [gwa] in YM. rewrite gs_cext, gs_tyCTrm in YM.
    destruct (YM _ _ _ Hlift) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (_ & _ & HgM).
    (* the bodies, related under the new binding *)
    pose proof (wf_gext_ty (i := lC) HG' HD (or_introl eq_refl) Hl2') as HG0.
    assert (HG1 : [ ⊢ gext G' (gdTm Δ⦃σ⦄ lC A⦃σ⦄ l2) ]).
    { destruct G' as [L' Ψ']; unfold gext; cbn in *. apply wfg_tm; auto. }
    pose proof (gwk_ok_step G' (gdTm Δ⦃σ⦄ lC A⦃σ⦄ l2)) as Hγ1.
    pose proof (gwk_ctx Hγ1 HG1 HD) as HDs.
    pose proof (gwk_ty Hγ1 HG1 HAw) as HAs.
    pose proof (CtxRelG_trans (VΔP _ _ _ Hσ) (CtxRelG_sym (VΔP _ _ _ Hσ))) as XP.
    pose proof (CtxRelG_trans (VΔM _ _ _ Hσ) (CtxRelG_sym (VΔM _ _ _ Hσ))) as XM.
    assert (Hin0 : in_gctx (gΨ (gext G' (gdTm Δ⦃σ⦄ lC A⦃σ⦄ l2))) 0 (gdTm Δ⦃σ⦄⟪S⟫ lC A⦃σ⦄⟪S⟫ l2))
      by exact (ing_here _ (gdTm Δ⦃σ⦄ lC A⦃σ⦄ l2)).
    assert (HlC : forall E0 : GenericEq, lle lC (@ge_layer E0))
      by (intros E0; exact (lle_trans lC lD _ ltac:(unfold lle; cbn; lia) ge_lle_D)).
    pose proof (VTmG_gvar_ne (E := EP) (LP := LR_P) (δ := lshift 0) (δ' := lshift 0) Hin0 (HlC EP) I I
                  (VSubK_id HDs (CtxRelG_gwk XP Hγ1)) (VSubK_id HDs (CtxRelG_gwk XP Hγ1))
                  (VTyG_gwk (VAAP _ _ _ Hσl) Hγ1)) as UP.
    pose proof (VTmG_gvar_ne (E := EM) (LP := LR_P) (δ := lshift 0) (δ' := lshift 0) Hin0 (HlC EM) I I
                  (VSubK_id HDs (CtxRelG_gwk XM Hγ1)) (VSubK_id HDs (CtxRelG_gwk XM Hγ1))
                  (VTyG_gwk (VAAM _ _ _ Hσl) Hγ1)) as UM.
    rewrite nf_id_ty in UP, UM by exact (wf_ty_nf HAs).
    pose proof (gwk_eqctx Hγ1 HG1 HDDr) as HDDrs.
    pose proof (gwk_eqty Hγ1 HG1 HAAr) as HAArs.
    assert (Hσu : GSubRel (gext G' (gdTm Δ⦃σ⦄ lC A⦃σ⦄ l2)) (gext G (gdTm Δ lC A l2))
                    (gsub_up_id (gdTm Δ lC A l2) σ) (gsub_up_id (gdTm Δ lC A l2) σ')).
    { apply (GSubRel_up_id EP EM (D := gdTm Δ lC A l2) Hσ); cbn [gdecl_gsubst gdecl_ren id_obj gobj_wf GObjRel].
      - exact HG1.
      - exact (wf_tm_gvar_id Hin0 (eqc_refl _ _ _ HDs) HAs).
      - exact (ctxconv_tm (i := lC) HDDrs eq_refl (wf_conv _ _ _ _ _ _ _ (wf_tm_gvar_id Hin0 (eqc_refl _ _ _ HDs) HAs) (eqty_sym _ _ _ _ _ _ HAArs))).
      - exact (conj (tm_leq_refl _) (conj UP UM)).
      - refine (conj (tm_leq_refl _) (conj _ _)).
        + exact (VTmG_conv (VTmG_transport (CtxRelG_gwk (VΔP _ _ _ Hσ) Hγ1) UP)
                   (VTyG_sym (VTyG_transport (CtxRelG_gwk (VΔP _ _ _ Hσ) Hγ1) (VTyG_gwk (VAAP _ _ _ Hσ) Hγ1)))).
        + exact (VTmG_conv (VTmG_transport (CtxRelG_gwk (VΔM _ _ _ Hσ) Hγ1) UM)
                   (VTyG_sym (VTyG_transport (CtxRelG_gwk (VΔM _ _ _ Hσ) Hγ1) (VTyG_gwk (VAAM _ _ _ Hσ) Hγ1)))). }
    pose proof (Vb _ _ _ Hσu _ _ (gwk_ok_id _)) as Yb; cbn [gwa] in Yb.
    rewrite <- (gsubst_up_id_tm _ _ σ Ht1), <- (gsubst_up_id_tm _ _ σ' Ht2) in Yb.
    rewrite gs_single_ty in Yb. unfold gsub_up_id in Yb. rewrite gcons_shift_ctx, gcons_shift_ty in Yb.
    rewrite <- gwa_gsubst_ctx, <- gwa_gsubst_ty in Yb.
    change ((boxt (gvar 0 (lshift 0)))⦃gcons (gsub_wk σ (gwk_step gwk_id)) (id_obj (gdTm Δ lC A l2) 0)⦄)
      with (boxt (gvar 0 (lshift 0))) in Yb.
    pose proof (Yb _ _ _ (SubRel_gwa He Hγ1 HG1)) as Yb'.
    assert (Ngwk : LK nftm (gwk e)) by (intros n; apply dnftm_nftm, (lk_dnf_gwk _ De)).
    assert (Hgb : @geq_tm EM (gext G' (gdTm Δ⦃σ⦄ lC A⦃σ⦄ l2)) Θ⟪S⟫ (t1⦃gup σ⦄)[gwk e] (t2⦃gup σ'⦄)[gwk e']
                    (Mbt (M⦃σ⦄)[llift e]) l1).
    { rewrite <- gshift_llift_ty.
      change (boxt (gvar 0 (lshift 0))) with ((boxt (gvar 0 (lshift 0)))[gwk e]).
      rewrite <- (single_subst_ty (gwk e) Ngwk). exact (LRtm_geq Yb'). }
    pose proof (gne_tm_letboxt (EP := EP) (EM := EM) Hl13' Hl24' HgDD' HAw HgAA' HM1 HgM HM1' Hgb Hb2 Hνν) as Hν.
    destruct (VMat _ _ _ _ He HLww) as [Rν HRν].
    destruct (escape_ty _ _ _ _ _ _ _ _ HRν) as (_ & _ & Hgν).
    assert (Hν' := gne_tm_conv Hν (geq_ty_sound Hgν)).
    refine (Fin _ _ (ex_intro _ Rν (conj HRν (LR_neutral _ _ _ _ _ _ _ HRν _ _ Hν Hν'))) _ _).
    + exact (tmred_letboxt_cong Hl1' Hl2' HDw HAw HM1 Hb1 Hsw).
    + assert (Hl4' : lwf (gL G') l4) by exact (lequiv_wf_r _ _ _ Hl24').
      exact (tmred_letboxt_cong Hl3' Hl4' HD'w HA'w HM1' Hb2 Hs'w4).
Qed.

End Letboxt.

(** ** The β-rules *)

Section LetboxBeta.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_laws3 : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation VCtxSP := (@VCtxS EP EM EP LR_P).
Local Notation VCtxSPM := (@VCtxS EP EM EM LR_P).

Lemma VS_letboxT_beta {G Γ l' l Δ M t' T} :
  GValid EP EM G -> lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] T @ l ] ->
  [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] ->
  [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] ->
  VCtxSP G Δ -> VCtxSPM G Δ -> @VTyS EP EM EP LR_P G Δ T T l -> @VTyS EP EM EM LR_P G Δ T T l ->
  VTmSM (gext G (gdTy Δ lC l)) Γ⟪S⟫ t' t' (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) l' ->
  VTmSM G Γ (letboxT l' l Δ M t' (boxT T)) t'⦃gsingle (GTy T)⦄ M[lsingle (boxT T)] l'.
Proof.
  intros HG Hl' Hl HΔ HT HM Ht' VΔP VΔM VTP VTM Vb.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσl. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  assert (EL : gL G <= gL G') by exact (gsr_L _ _ _ _ _ _ Hσ).
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  pose proof (gs_ctx EP EM Hσ HΔ compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ compt_D) as HDr.
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hσ) HD HDr) as [_ HDDr].
  (* the code is static: the same under both substitutions *)
  pose proof ((proj1 (proj2 (proj2 static_gsubst))) _ _ _ _ _ HT (lle_refl _) _ _ (GSubRel_agree EP EM Hσ)) as ET.
  pose proof (gs_ty EP EM Hσ HT) as HT1.
  (* the left-hand side's typing, by inversion *)
  assert (Hw : [ G ; Γ ⊢[ lM ] letboxT l' l Δ M t' (boxT T) : M[lsingle (boxT T)] @ l' ]).
  { apply wf_letboxT; try assumption. apply wf_boxT; try assumption.
    exact (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)). }
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  rewrite gs_letboxT, subst_letboxT, gs_boxT in X. cbn [subst Subst_tm subst_tm] in X.
  destruct (letboxT_inv X) as (_ & _ & HDw & HM1 & Hb1 & _ & _ & _). clear X.
  (* the extended substitutions *)
  pose proof (gs_ty EP EM Hσr HT) as HT1r.
  assert (Hσx : GSubRel G' (gext G (gdTy Δ lC l)) (gcons σ (GTy T⦃σ⦄)) (gcons σ' (GTy T⦃σ'⦄))).
  { apply (GSubRel_cons2 EP EM Hσ); cbn [gdecl_gsubst gobj_wf dnfo GObjRel].
    - exact (wf_ty_dnf HT1).
    - exact (wf_ty_dnf HT1r).
    - exact HT1.
    - exact HT1r.
    - exact (conj (fun _ => ET) (conj (VTP _ _ _ Hσ) (VTM _ _ _ Hσ))).
    - exact (conj (fun _ => ty_leq_refl _) (conj (VTP _ _ _ Hσl) (VTM _ _ _ Hσl))).
    - exact (conj (fun _ => ty_leq_refl _) (conj (VTP _ _ _ Hσr) (VTM _ _ _ Hσr))). }
  pose proof (Vb _ _ _ Hσx G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  rewrite gcons_shift_ctx in Y. specialize (Y _ _ _ He).
  assert (Eb : (boxT (tyGvar 0 (lshift 0)))⦃gcons σ (GTy T⦃σ⦄)⦄ = boxT T⦃σ⦄).
  { change ((boxT (tyGvar 0 (lshift 0)))⦃gcons σ (GTy T⦃σ⦄)⦄) with (boxT T⦃σ⦄[lshift 0]).
    now rewrite nf_id_ty by exact (wf_ty_nf HT1). }
  rewrite gs_single_ty, gcons_shift_ty, Eb, !single_subst_ty in Y by assumption.
  cbn [subst Subst_tm subst_tm] in Y.
  (* the goal *)
  rewrite gs_letboxT, subst_letboxT, gs_boxT, gs_single_ty, gs_boxT, !single_subst_ty by assumption.
  cbn [subst Subst_tm subst_tm].
  rewrite (gs_gsingle _ _ _ Nσ'), (gup_single_tm _ _ _ Nσ'). cbn [gosubst].
  change (gsubst_ty T σ') with T⦃σ'⦄.
  assert (Hl'1 : lwf (gL G') l') by (lup EL). assert (Hl1 : lwf (gL G') l) by (lup EL).
  eapply LRtm_red_l; [exact Y |]. rewrite (@gm_layer_M EP EM EMl), <- letbox_reduct by assumption.
  exact (tmred_letboxT_beta Hl'1 Hl1 HDw HM1 Hb1 HT1).
Qed.

Lemma VS_letboxt_beta {G Γ l' l Δ A M t' c} :
  GValid EP EM G -> lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ G ; Δ ⊢[ lC ] c : A @ l ] -> [ G ; Γ ,, tyCTrm Δ A l @ lzero ⊢[ lM ] M @ l' ] ->
  [ gext G (gdTm Δ lC A l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] ->
  VCtxSP G Δ -> VCtxSPM G Δ -> @VTyS EP EM EP LR_P G Δ A A l -> @VTyS EP EM EM LR_P G Δ A A l ->
  @VTmS EP EM EP LR_P G Δ c c A l -> @VTmS EP EM EM LR_P G Δ c c A l ->
  VTmSM (gext G (gdTm Δ lC A l)) Γ⟪S⟫ t' t' (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) l' ->
  VTmSM G Γ (letboxt l' l Δ A M t' (boxt c)) t'⦃gsingle (GTm c)⦄ M[lsingle (boxt c)] l'.
Proof.
  intros HG Hl' Hl HΔ HA Hc HM Ht' VΔP VΔM VAP VAM VcP VcM Vb.
  apply (VTmS_intro_loc EP EM). intros G' σ σ' Hσ Θ e e' He.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (GSubRel_refl_l EP EM Hσ) as Hσl. pose proof (GSubRel_refl_r EP EM Hσ) as Hσr.
  assert (EL : gL G <= gL G') by exact (gsr_L _ _ _ _ _ _ Hσ).
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  pose proof (gs_ctx EP EM Hσ HΔ compt_D) as HD. pose proof (gs_ctx EP EM Hσr HΔ compt_D) as HDr.
  pose proof (CtxRelG_escape_P EP EM (VΔP _ _ _ Hσ) HD HDr) as [_ HDDr].
  pose proof (gs_ty EP EM Hσ HA) as HA1.
  assert (HAσ'D : [ G' ; Δ⦃σ⦄ ⊢[ lD ] A⦃σ'⦄ @ l ])
    by exact (ctxconv_ty (i := lD) (eqctx_sym_D HDDr) eq_refl (gs_ty EP EM Hσr HA)).
  destruct (VTyG_escape_P EP EM (VΔP _ _ _ Hσ) HD HA1 HAσ'D (VAP _ _ _ Hσ)) as [_ HAAr].
  pose proof ((proj1 (proj2 (proj2 (proj2 static_gsubst)))) _ _ _ _ _ _ Hc (lle_refl _) _ _
                (GSubRel_agree EP EM Hσ)) as Ec.
  pose proof (gs_tm EP EM Hσ Hc) as Hc1.
  assert (Hw : [ G ; Γ ⊢[ lM ] letboxt l' l Δ A M t' (boxt c) : M[lsingle (boxt c)] @ l' ]).
  { apply wf_letboxt; try assumption. apply wf_boxt; try assumption.
    exact (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)). }
  pose proof (SubRel_wf_l _ _ _ _ _ He) as Hew. rewrite (@gm_layer_M EP EM EMl) in Hew.
  pose proof (wf_tm_subst (i := lM) eq_refl (gs_tm EP EM Hσ Hw) Hew) as X.
  rewrite gs_letboxt, subst_letboxt, gs_boxt in X. cbn [subst Subst_tm subst_tm] in X.
  destruct (letboxt_inv X) as (_ & _ & HDw & HAw & HM1 & Hb1 & _ & _ & _). clear X.
  pose proof (gs_tm EP EM Hσr Hc) as Hc1r.
  assert (Hσx : GSubRel G' (gext G (gdTm Δ lC A l)) (gcons σ (GTm c⦃σ⦄)) (gcons σ' (GTm c⦃σ'⦄))).
  { apply (GSubRel_cons2 EP EM Hσ); cbn [gdecl_gsubst gobj_wf dnfo GObjRel].
    - exact (wf_tm_dnf Hc1).
    - exact (wf_tm_dnf Hc1r).
    - exact Hc1.
    - exact Hc1r.
    - exact (conj Ec (conj (VcP _ _ _ Hσ) (VcM _ _ _ Hσ))).
    - exact (conj (tm_leq_refl _) (conj (VcP _ _ _ Hσl) (VcM _ _ _ Hσl))).
    - exact (conj (tm_leq_refl _) (conj (VcP _ _ _ Hσr) (VcM _ _ _ Hσr))). }
  pose proof (Vb _ _ _ Hσx G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  rewrite gcons_shift_ctx in Y. specialize (Y _ _ _ He).
  assert (Eb : (boxt (gvar 0 (lshift 0)))⦃gcons σ (GTm c⦃σ⦄)⦄ = boxt c⦃σ⦄).
  { change ((boxt (gvar 0 (lshift 0)))⦃gcons σ (GTm c⦃σ⦄)⦄) with (boxt c⦃σ⦄[lshift 0]).
    now rewrite nf_id by exact (wf_tm_nf Hc1). }
  rewrite gs_single_ty, gcons_shift_ty, Eb, !single_subst_ty in Y by assumption.
  cbn [subst Subst_tm subst_tm] in Y.
  rewrite gs_letboxt, subst_letboxt, gs_boxt, gs_single_ty, gs_boxt, !single_subst_ty by assumption.
  cbn [subst Subst_tm subst_tm].
  rewrite (gs_gsingle _ _ _ Nσ'), (gup_single_tm _ _ _ Nσ'). cbn [gosubst].
  change (gsubst_tm c σ') with c⦃σ'⦄.
  assert (Hl'1 : lwf (gL G') l') by (lup EL). assert (Hl1 : lwf (gL G') l) by (lup EL).
  eapply LRtm_red_l; [exact Y |]. rewrite (@gm_layer_M EP EM EMl), <- letbox_reduct by assumption.
  exact (tmred_letboxt_beta Hl'1 Hl1 HDw HAw HM1 Hb1 Hc1).
Qed.

End LetboxBeta.
