(** * The recursion lemmas on code (M3_DESIGN.md E13)

    The FT case of a recursor, unfolded: related global substitutions
    [σ ≈ σ'] into [G[φ]], related local ones [e ≈ e'] into [Γ[φ]⦃σ⦄],
    and the recursors moved there. This file relates the moved motives'
    instances (from the motives' validity at every [ψ]), the reducts (from
    the branches' validity at [ψ = levels ++ φ], [σ] extended by the
    code's pieces, [e] by the recursive calls), and proves the recursion
    lemmas by induction on the code's C-typing. *)
From DeLaM.Typing Require Export RecPeel.
From DeLaM.Validity Require Export RecObj LetboxS DeclConsequencesP RecExt.

(** ** Pointwise equal substitutions *)

Lemma gext_s_one o σ i : gext_s (o :: nil) σ i = gcons σ o i.
Proof. unfold gext_s; destruct i; cbn; [reflexivity | f_equal; lia]. Qed.

(** ** The motives' instances at convertible scrutinees *)

Lemma motT_eq_scrut {G Γ MT l1 l Δ t t'} :
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t ≅ motT (wrapMT MT) l Δ t' @ l1 ].
Proof.
  destruct G as [L Ψ]. intros HMT Hl HΔ Htt.
  pose proof (eqtm_wf_l (i := lM) eq_refl Htt) as Ht. pose proof (eqtm_wf_r (i := lM) eq_refl Htt) as Ht'.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht)) as Hg.
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ HMT L (usingle l) (usub_ok_single L l Hl)) as X1.
  rewrite (G_us_recGT _ _ _ Hg), lvsubst_ush1_single in X1.
  assert (Hσ : [ mkG L Ψ ⊢ gsingle (GCtx Δ) : mkG L (gdCtx :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) gdCtx); [exact Hg | exact (wf_ctx_dnf HΔ) | exact HΔ]. }
  pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X1 Ψ _ Hσ) as X2.
  unfold gwk_to in X2; cbn [gL] in X2. change (gsubst ?x ?s) with (gcsubst x s) in X2 at 1.
  rewrite (recΓT_inst _ _ _ (wf_ctx_dnf (ctx_of_wf_tm (i := lM) eq_refl Ht))) in X2.
  exact (wf_ty_func (i := lM) eq_refl X2 (lsub_eq_single (i := lM) eq_refl Ht Ht' Htt)).
Qed.

Lemma mott_eq_scrut {G Γ Mt l2 l Δ T t t'} :
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t ≅ mott (wrapMt Mt) l Δ T t' @ l2 ].
Proof.
  destruct G as [L Ψ]. intros HMt Hl HΔ HT Htt.
  pose proof (eqtm_wf_l (i := lM) eq_refl Htt) as Ht. pose proof (eqtm_wf_r (i := lM) eq_refl Htt) as Ht'.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_tm (i := lM) eq_refl Ht)) as Hg.
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ HMt L (usingle l) (usub_ok_single L l Hl)) as X1.
  rewrite (G_us_recGt _ _ _ Hg), lvsubst_ush1_single in X1.
  assert (Hσ0 : [ mkG L Ψ ⊢ gsingle (GCtx Δ) : mkG L (gdCtx :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) gdCtx); [exact Hg | exact (wf_ctx_dnf HΔ) | exact HΔ]. }
  assert (Hg1 : [ ⊢ mkG L (gdTy Δ lD l :: Ψ) ]) by (apply wfg_ty; auto).
  assert (Hσ1 : [ mkG L (gdTy Δ lD l :: Ψ) ⊢ gup (gsingle (GCtx Δ)) : mkG L (gdTy (cvar 0) lD l :: gdCtx :: Ψ) ])
    by exact (gsub_wf_up _ _ _ (gdTy (cvar 0) lD l) Hσ0 Hg1).
  assert (Hσ2 : [ mkG L Ψ ⊢ gsingle (GTy T) : mkG L (gdTy Δ lD l :: Ψ) ]).
  { apply (gsub_wf_single (mkG L Ψ) (gdTy Δ lD l)); [exact Hg | exact (wf_ty_dnf HT) |].
    rewrite gdecl_gsubst_ren_single by exact (wf_ctx_dnf HΔ). exact HT. }
  pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X1 _ _ Hσ1) as X2.
  unfold gwk_to in X2; cbn [gL] in X2.
  pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X2 Ψ _ Hσ2) as X3.
  unfold gwk_to in X3; cbn [gL] in X3.
  change (gsubst (gsubst ?x ?s1) ?s2) with (gcsubst (gcsubst x s1) s2) in X3 at 1.
  rewrite (recΓt_inst _ _ _ _ (wf_ctx_dnf (ctx_of_wf_tm (i := lM) eq_refl Ht)) (wf_ctx_dnf HΔ) (wf_ty_nf HT)) in X3.
  exact (wf_ty_func (i := lM) eq_refl X3 (lsub_eq_single (i := lM) eq_refl Ht Ht' Htt)).
Qed.

(** ** Typed reductions of the recursors *)

Lemma reds_elimT' l1 l2 rb l Δ t t0 : reds t t0 -> reds (elimT l1 l2 rb l Δ t) (elimT l1 l2 rb l Δ t0).
Proof. induction 1; [constructor | econstructor; [apply red_elimT; eassumption | assumption]]. Qed.
Lemma reds_elimt' l1 l2 rb l Δ T t t0 : reds t t0 -> reds (elimt l1 l2 rb l Δ T t) (elimt l1 l2 rb l Δ T t0).
Proof. induction 1; [constructor | econstructor; [apply red_elimt; eassumption | assumption]]. Qed.

Section RecRed.
Context {G : gctx} {Θ : ctx} {l1 l2 : lvl} {MT Mt : ty} {bs : nat -> tm} {l : lvl} {Δ : ctx}
  (Hrb : RBwf G Θ l1 l2 MT Mt bs) (Hl : lwf (gL G) l) (HΔ : [ G ; Δ ⊢[ lD ] ]).

Lemma tmred_elimT_cong {s w} : [ G ; Θ ⊢[ lM ] s ⤳* w : tyCTyp Δ l @ lzero ] ->
  [ G ; Θ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ s ⤳* elimT l1 l2 (mkrb MT Mt bs) l Δ w
      : motT (wrapMT MT) l Δ s @ l1 ].
Proof.
  intros [Hs Hr Heq]. destruct Hrb as (Hl1 & Hl2 & HMT & HMt & Hc & Hb). split.
  - now apply wf_elimT'.
  - now apply reds_elimT'.
  - apply eqtm_elimT; try assumption; try (apply lequiv_refl; assumption).
    + exact (motT_eq_scrut HMT Hl HΔ Heq).
    + now apply eqc_refl.
    + now apply eqty_refl.
    + now apply eqty_refl.
    + intros k Hk; apply eqtm_refl, Hb, Hk.
Qed.

Lemma tmred_elimT_beta {c r} : [ G ; Δ ⊢[ lC ] c @ l ] -> redT l1 l2 (mkrb MT Mt bs) l Δ c = Some r ->
  [ G ; Θ ⊢[ lM ] r : motT (wrapMT MT) l Δ (boxT c) @ l1 ] ->
  [ G ; Θ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT c) ⤳* r : motT (wrapMT MT) l Δ (boxT c) @ l1 ].
Proof.
  intros Hc Hred Hr. pose proof (ctx_of_wf_tm (i := lM) eq_refl Hr) as HΘ.
  assert (Hw : [ G ; Θ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT c) : motT (wrapMT MT) l Δ (boxT c) @ l1 ])
    by (apply wf_elimT'; auto; apply wf_boxT; auto).
  split.
  - exact Hw.
  - econstructor; [apply red_elimT_beta, Hred | constructor].
  - apply eqtm_elimT_beta; assumption.
Qed.

End RecRed.

Section RecRedt.
Context {G : gctx} {Θ : ctx} {l1 l2 : lvl} {MT Mt : ty} {bs : nat -> tm} {l : lvl} {Δ : ctx} {T : ty}
  (Hrb : RBwf G Θ l1 l2 MT Mt bs) (Hl : lwf (gL G) l) (HΔ : [ G ; Δ ⊢[ lD ] ]) (HT : [ G ; Δ ⊢[ lD ] T @ l ]).

Lemma tmred_elimt_cong {s w} : [ G ; Θ ⊢[ lM ] s ⤳* w : tyCTrm Δ T l @ lzero ] ->
  [ G ; Θ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T s ⤳* elimt l1 l2 (mkrb MT Mt bs) l Δ T w
      : mott (wrapMt Mt) l Δ T s @ l2 ].
Proof.
  intros [Hs Hr Heq]. destruct Hrb as (Hl1 & Hl2 & HMT & HMt & Hc & Hb). split.
  - now apply wf_elimt'.
  - now apply reds_elimt'.
  - apply eqtm_elimt; try assumption; try (apply lequiv_refl; assumption).
    + exact (mott_eq_scrut HMt Hl HΔ HT Heq).
    + now apply eqc_refl.
    + now apply eqty_refl.
    + now apply eqty_refl.
    + now apply eqty_refl.
    + intros k Hk; apply eqtm_refl, Hb, Hk.
Qed.

Lemma tmred_elimt_beta {c r} : [ G ; Δ ⊢[ lC ] c : T @ l ] -> redt l1 l2 (mkrb MT Mt bs) l Δ T c = Some r ->
  [ G ; Θ ⊢[ lM ] r : mott (wrapMt Mt) l Δ T (boxt c) @ l2 ] ->
  [ G ; Θ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c) ⤳* r : mott (wrapMt Mt) l Δ T (boxt c) @ l2 ].
Proof.
  intros Hc Hred Hr. pose proof (ctx_of_wf_tm (i := lM) eq_refl Hr) as HΘ.
  assert (Hw : [ G ; Θ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c) : mott (wrapMt Mt) l Δ T (boxt c) @ l2 ])
    by (apply wf_elimt'; auto; apply wf_boxt; auto).
  split.
  - exact Hw.
  - econstructor; [apply red_elimt_beta, Hred | constructor].
  - apply eqtm_elimt_beta; assumption.
Qed.

(** The index is reduced under a boxed [λ]; the instances' equation is a
    premise (the recursion lemma has it semantically). *)
Lemma tmred_elimt_idx {W k k' A b} : [ G ; Δ ⊢[ lD ] T ⤳* W @ l ] ->
  [ G ; Θ ⊢[ lM ] boxt (lam k k' A b) : tyCTrm Δ T l @ lzero ] ->
  [ G ; Θ ⊢[ lM ] mott (wrapMt Mt) l Δ T (boxt (lam k k' A b)) ≅ mott (wrapMt Mt) l Δ W (boxt (lam k k' A b)) @ l2 ] ->
  [ G ; Θ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt (lam k k' A b)) ⤳*
                 elimt l1 l2 (mkrb MT Mt bs) l Δ W (boxt (lam k k' A b)) : mott (wrapMt Mt) l Δ T (boxt (lam k k' A b)) @ l2 ].
Proof.
  intros [HT0 Hr HTW] Hs Hinst. destruct Hrb as (Hl1 & Hl2 & HMT & HMt & Hc & Hb).
  pose proof (eqty_wf_r (i := lD) eq_refl HTW) as HW.
  split.
  - now apply wf_elimt'.
  - clear -Hr. induction Hr as [|T U W0 Hs Hrs IH]; [constructor|].
    econstructor; [apply red_elimt_idx, Hs | exact IH].
  - apply eqtm_elimt; try assumption; try (apply lequiv_refl; assumption).
    + now apply eqc_refl.
    + now apply eqty_refl.
    + now apply eqty_refl.
    + intros k0 Hk; apply eqtm_refl, Hb, Hk.
    + now apply eqtm_refl.
Qed.

End RecRedt.

Section RecS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsRec : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation GObjRel := (GObjRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtmM := (@LRtm EM LRM).

Lemma GSubRel_ext {G' G σ σ' τ τ'} : (forall i, σ i = τ i) -> (forall i, σ' i = τ' i) ->
  GSubRel G' G σ σ' -> GSubRel G' G τ τ'.
Proof. exact (RecExt.GSubRel_ext EP EM). Qed.

(** Extension by a context, one on each side, related at P. *)
Lemma GSubRel_ctx1 {G' G σ σ' Δ Δ'} : GSubRel G' G σ σ' -> [ G' ; Δ ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ ≅ Δ' ] ->
  GSubRel G' (gext G gdCtx) (gext_s (GCtx Δ :: nil) σ) (gext_s (GCtx Δ' :: nil) σ').
Proof.
  intros Hσ HΔ HΔΔ. pose proof (eqctx_wf_r (i := lD) eq_refl HΔΔ) as HΔ'.
  refine (GSubRel_ext (fun i => eq_sym (gext_s_one _ _ i)) (fun i => eq_sym (gext_s_one _ _ i)) _).
  apply (GSubRel_cons2 EP EM Hσ); cbn [gdecl_gsubst dnfo gobj_wf].
  - exact (wf_ctx_dnf HΔ).
  - exact (wf_ctx_dnf HΔ').
  - exact HΔ.
  - exact HΔ'.
  - exact (GObjRel_ctx EP EM HΔΔ).
  - exact (GObjRel_ctx EP EM (eqc_refl _ _ _ HΔ)).
  - exact (GObjRel_ctx EP EM (eqc_refl _ _ _ HΔ')).
Qed.

(** Extension by a context and a P-type over it. *)
Lemma GSubRel_ctx_ty {G' G σ σ' Δ Δ' U U' k} : GSubRel G' G σ σ' -> [ G' ; Δ ⊢[ lD ] ] ->
  [ G' ⊢[ lD ] Δ ≅ Δ' ] -> [ G' ; Δ ⊢[ lD ] U ≅ U' @ k ] -> [ G' ; Δ' ⊢[ lD ] U' @ k ] ->
  GSubRel G' (gext (gext G gdCtx) (gdTy (cvar 0) lD k))
    (gext_s (GCtx Δ :: GTy U :: nil) σ) (gext_s (GCtx Δ' :: GTy U' :: nil) σ').
Proof.
  intros Hσ HΔ HΔΔ HU HU'. pose proof (eqctx_wf_r (i := lD) eq_refl HΔΔ) as HΔ'.
  pose proof (eqty_wf_l (i := lD) eq_refl HU) as HUl.
  refine (GSubRel_ext (fun i => eq_sym (gext_s_app (GCtx Δ :: nil) (GTy U) σ i))
                      (fun i => eq_sym (gext_s_app (GCtx Δ' :: nil) (GTy U') σ' i)) _).
  pose proof (GSubRel_ctx1 Hσ HΔ HΔΔ) as H1.
  assert (Ep : forall o τ, gdecl_gsubst (gdTy (cvar 0) lD k) (gext_s (o :: nil) τ) = gdTy (pctx o) lD k)
    by (intros; reflexivity).
  refine (GSubRel_cons2 EP EM H1 _ _ _ _ _ _ _); rewrite ?Ep; cbn [pctx dnfo gobj_wf].
  - exact (wf_ty_dnf HUl).
  - exact (wf_ty_dnf HU').
  - exact HUl.
  - exact HU'.
  - apply (GObjRel_ty EP EM); [intros Hle; unfold lle in Hle; cbn in Hle; lia | exact HU].
  - apply (GObjRel_ty EP EM); [intros; apply ty_leq_refl | exact (eqty_refl _ _ _ _ _ HUl)].
  - apply (GObjRel_ty EP EM); [intros; apply ty_leq_refl | exact (eqty_refl _ _ _ _ _ HU')].
Qed.

(** ** The motives' instances are related *)

Section Mot.
Variables (G0 : gctx) (Γ0 : ctx) (L' : nat) (φ : nat -> lvl) (MT MT' : ty) (l1 l1' : lvl).
Hypothesis (HMT : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT @ lvren l1 (ush 1) ])
           (HMT' : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT' @ lvren l1' (ush 1) ])
           (Hl1 : lequiv L' (lvsubst l1 φ) (lvsubst l1' φ))
           (Hφ : usub_ok φ L' (gL G0))
           (VMT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
              VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT ψ) (usubst_ty MT' ψ)
                (lvsubst (lvren l1 (ush 1)) ψ))
           (VMT' : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
              VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT' ψ) (usubst_ty MT' ψ)
                (lvsubst (lvren l1' (ush 1)) ψ))
           (VΓ : VCtxSM (G_us G0 L' φ) (ucsubst Γ0 φ)).
Variables (G' : gctx) (σ σ' : gsub) (Θ : ctx) (e e' : lsub).
Hypothesis (Hσ : GSubRel G' (G_us G0 L' φ) σ σ')
           (He : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e e')
           (HEL : gL G' = L').

Lemma MotRel_T {kL kR ΔL ΔR a a'} :
  lwf L' kL -> lequiv L' kL kR -> [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  LRtmM lzero G' Θ (tyCTyp ΔL kL) (tyCTyp ΔL kL) a a' ->
  LRtmM lzero G' Θ (tyCTyp ΔR kR) (tyCTyp ΔR kR) a' a' ->
  LRtyM (lvsubst l1 φ) G' Θ
    (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))])) kL ΔL a)
    (motT (wrapMT ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄[llift (gwk (uwk e'))])) kR ΔR a').
Proof.
  intros HkL Hk HΔL HΔ Ha Ha'.
  pose proof HEL as EL.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  pose proof (proj1 (LRtm_escape Ha)) as Hat. pose proof (proj1 (LRtm_escape Ha')) as Hat'.
  rewrite (motT_inst MT φ σ e kL ΔL a), (motT_inst MT' φ σ' e' kR ΔR a')
    by first [exact (wf_ty_dnf HMT) | exact (wf_ty_dnf HMT') | assumption | exact (wf_ctx_dnf HΔL)
             | exact (wf_ctx_dnf HΔR) | exact (wf_tm_dnf Hat) | exact (wf_tm_dnf Hat')].
  (* left against right, at the left level *)
  assert (HψL : usub_ok (uext (kL :: nil) φ) L' (gL (recGT G0)))
    by (apply (usub_ok_uext (kL :: nil) φ L' (gL G0)); [repeat constructor; exact HkL | exact Hφ]).
  pose proof (VMT _ _ HψL) as X. rewrite G_us_recGT_uext in X.
  pose proof (X _ _ _ (GSubRel_ctx1 Hσ HΔL HΔ) G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  rewrite recΓT_inst' in Y.
  assert (Ha0 : LRtmM lzero G' Θ (tyCTyp ΔL kL)[e] (tyCTyp ΔL kL)[e'] a a') by exact Ha.
  pose proof (Y _ _ _ (SubRel_cons He Ha0)) as Z.
  change (lvsubst (lvren l1 (ush 1)) (uext (kL :: nil) φ)) with
    (lvsubst (lvren l1 (ush (length (kL :: nil)))) (uext (kL :: nil) φ)) in Z.
  rewrite lvren_ush_uext in Z.
  (* the right side at its own level *)
  assert (HψR : usub_ok (uext (kR :: nil) φ) L' (gL (recGT G0))).
  { apply (usub_ok_uext (kR :: nil) φ L' (gL G0)); [repeat constructor | exact Hφ].
    exact (lequiv_wf_r _ _ _ Hk). }
  pose proof (VMT' _ _ HψR) as X'. rewrite G_us_recGT_uext in X'.
  pose proof (X' _ _ _ (GSubRel_ctx1 (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) G' gwk_id
                (gwk_ok_id G')) as Y'; cbn [gwa] in Y'.
  rewrite recΓT_inst' in Y'.
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  pose proof (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) (SubRel_refl_r He)) as He'.
  assert (Ha1 : LRtmM lzero G' Θ (tyCTyp ΔR kR)[e'] (tyCTyp ΔR kR)[e'] a' a') by exact Ha'.
  pose proof (Y' _ _ _ (SubRel_cons He' Ha1)) as Z'.
  change (lvsubst (lvren l1' (ush 1)) (uext (kR :: nil) φ)) with
    (lvsubst (lvren l1' (ush (length (kR :: nil)))) (uext (kR :: nil) φ)) in Z'.
  rewrite lvren_ush_uext in Z'.
  refine (LRty_leq Z (LRty_lconv Z' _) _).
  - rewrite EL; exact Hl1.
  - apply (proj1 leq_subst_all); [apply lsub_leq_refl|].
    apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl|].
    apply (proj1 leq_usubst_all); [| apply ty_leq_refl].
    intros [|i]; unfold uext; cbn; [exact (lequiv_leqv _ _ _ Hk) | apply leqv_refl].
Qed.

End Mot.

Section Mott.
Variables (G0 : gctx) (Γ0 : ctx) (L' : nat) (φ : nat -> lvl) (Mt Mt' : ty) (l2 l2' : lvl).
Hypothesis (HMt : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt @ lvren l2 (ush 1) ])
           (HMt' : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt' @ lvren l2' (ush 1) ])
           (Hl2 : lequiv L' (lvsubst l2 φ) (lvsubst l2' φ))
           (Hφ : usub_ok φ L' (gL G0))
           (VMt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
              VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt ψ) (usubst_ty Mt' ψ)
                (lvsubst (lvren l2 (ush 1)) ψ))
           (VMt' : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
              VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt' ψ) (usubst_ty Mt' ψ)
                (lvsubst (lvren l2' (ush 1)) ψ))
           (VΓ : VCtxSM (G_us G0 L' φ) (ucsubst Γ0 φ)).
Variables (G' : gctx) (σ σ' : gsub) (Θ : ctx) (e e' : lsub).
Hypothesis (Hσ : GSubRel G' (G_us G0 L' φ) σ σ')
           (He : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e e')
           (HEL : gL G' = L').

Lemma MotRel_t {kL kR ΔL ΔR UL UR a a'} :
  lwf L' kL -> lequiv L' kL kR -> [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  [ G' ; ΔL ⊢[ lD ] UL ≅ UR @ kL ] -> [ G' ; ΔR ⊢[ lD ] UR @ kR ] ->
  LRtmM lzero G' Θ (tyCTrm ΔL UL kL) (tyCTrm ΔL UL kL) a a' ->
  LRtmM lzero G' Θ (tyCTrm ΔR UR kR) (tyCTrm ΔR UR kR) a' a' ->
  LRtyM (lvsubst l2 φ) G' Θ
    (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))])) kL ΔL UL a)
    (mott (wrapMt ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄[llift (gwk (gwk (uwk e')))])) kR ΔR UR a').
Proof.
  intros HkL Hk HΔL HΔ HU HUR Ha Ha'.
  pose proof HEL as EL.
  pose proof (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as Nσ.
  pose proof (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)) as Nσ'.
  destruct (SubRel_dnf _ _ _ _ _ He) as [De De'].
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  pose proof (eqty_wf_l (i := lD) eq_refl HU) as HUL.
  pose proof (proj1 (LRtm_escape Ha)) as Hat. pose proof (proj1 (LRtm_escape Ha')) as Hat'.
  rewrite (mott_inst Mt φ σ e kL ΔL UL a), (mott_inst Mt' φ σ' e' kR ΔR UR a')
    by first [exact (wf_ty_dnf HMt) | exact (wf_ty_dnf HMt') | assumption | exact (wf_ctx_dnf HΔL)
             | exact (wf_ctx_dnf HΔR) | exact (wf_ty_dnf HUL) | exact (wf_ty_dnf HUR)
             | exact (wf_tm_dnf Hat) | exact (wf_tm_dnf Hat')].
  assert (HkR : lequiv (gL G') kR kL) by (rewrite EL; apply lequiv_sym, Hk).
  assert (HUR' : [ G' ; ΔR ⊢[ lD ] UR @ kL ]) by (eapply wft_lconv; [exact HUR | rewrite EL; exact Hk]).
  (* left against right, at the left level *)
  assert (HψL : usub_ok (uext (kL :: nil) φ) L' (gL (recGt G0)))
    by (apply (usub_ok_uext (kL :: nil) φ L' (gL G0)); [repeat constructor; exact HkL | exact Hφ]).
  pose proof (VMt _ _ HψL) as X. rewrite G_us_recGt_uext in X.
  pose proof (X _ _ _ (GSubRel_ctx_ty Hσ HΔL HΔ HU HUR') G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  rewrite recΓt_inst' in Y by exact (wf_ty_nf HUL).
  assert (Ha0 : LRtmM lzero G' Θ (tyCTrm ΔL UL kL)[e] (tyCTrm ΔL UL kL)[e'] a a') by exact Ha.
  pose proof (Y _ _ _ (SubRel_cons He Ha0)) as Z.
  change (lvsubst (lvren l2 (ush 1)) (uext (kL :: nil) φ)) with
    (lvsubst (lvren l2 (ush (length (kL :: nil)))) (uext (kL :: nil) φ)) in Z.
  rewrite lvren_ush_uext in Z.
  (* the right side at its own level *)
  assert (HψR : usub_ok (uext (kR :: nil) φ) L' (gL (recGt G0))).
  { apply (usub_ok_uext (kR :: nil) φ L' (gL G0)); [repeat constructor | exact Hφ].
    exact (lequiv_wf_r _ _ _ Hk). }
  pose proof (VMt' _ _ HψR) as X'. rewrite G_us_recGt_uext in X'.
  pose proof (X' _ _ _ (GSubRel_ctx_ty (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
                          (eqty_refl _ _ _ _ _ HUR) HUR) G' gwk_id (gwk_ok_id G')) as Y'; cbn [gwa] in Y'.
  rewrite recΓt_inst' in Y' by exact (wf_ty_nf HUR).
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  pose proof (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) (SubRel_refl_r He)) as He'.
  assert (Ha1 : LRtmM lzero G' Θ (tyCTrm ΔR UR kR)[e'] (tyCTrm ΔR UR kR)[e'] a' a') by exact Ha'.
  pose proof (Y' _ _ _ (SubRel_cons He' Ha1)) as Z'.
  change (lvsubst (lvren l2' (ush 1)) (uext (kR :: nil) φ)) with
    (lvsubst (lvren l2' (ush (length (kR :: nil)))) (uext (kR :: nil) φ)) in Z'.
  rewrite lvren_ush_uext in Z'.
  refine (LRty_leq Z (LRty_lconv Z' _) _).
  - rewrite EL; exact Hl2.
  - apply (proj1 leq_subst_all); [apply lsub_leq_refl|].
    apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl|].
    apply (proj1 leq_usubst_all); [| apply ty_leq_refl].
    intros [|i]; unfold uext; cbn; [exact (lequiv_leqv _ _ _ Hk) | apply leqv_refl].
Qed.

End Mott.

End RecS.


(** ** β reducts of a moved bundle at the type heads *)
Ltac forall_tac := solve [repeat (apply Forall_cons; [first [assumption | exact I]|]); apply Forall_nil].

Section Red.
Variables (MT Mt : ty) (bs : nat -> tm) (φ : nat -> lvl) (σ : gsub) (e : lsub) (l1 l2 : lvl).
Local Notation rb := (mkrb ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))])
                          ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))])
                          (fun k => ((usubst_tm (bs k) (uupn (br_nu k) φ))⦃gbsub k σ⦄)[lliftn (br_nl k) (bsub k e)])).

Lemma redT_nat_inst k Δ : dnftm (bs 0) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redT l1 l2 rb k Δ tyNat = Some (((usubst_tm (bs 0) (uext nil φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof.
  intros Hb Hσ He HΔ. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity.
Qed.

Lemma redT_pi_inst k0 Δ k k' A B : dnftm (bs 1) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A -> dnfty B ->
  dnftm (elimT l1 l2 rb k Δ (boxT A)) -> dnftm (elimT l1 l2 rb k' (cext Δ A k) (boxT B)) ->
  redT l1 l2 rb k0 Δ (tyPi k k' A B) =
  Some (((usubst_tm (bs 1) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: nil) σ⦄)
          [lext (elimT l1 l2 rb k Δ (boxT A) :: elimT l1 l2 rb k' (cext Δ A k) (boxT B) :: nil) e]).
Proof.
  intros Hb Hσ He HΔ HA HB H1 H2. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity.
Qed.

Lemma redT_U_inst k0 Δ k : dnftm (bs 2) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redT l1 l2 rb k0 Δ (tyU k) =
  Some (((usubst_tm (bs 2) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof. intros Hb Hσ He HΔ. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redT_El_inst k0 Δ k t : dnftm (bs 3) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm t ->
  dnftm (elimt l1 l2 rb (lsuc k) Δ (tyU k) (boxt t)) ->
  redT l1 l2 rb k0 Δ (tyEl k t) =
  Some (((usubst_tm (bs 3) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTm t :: nil) σ⦄)
          [lext (elimt l1 l2 rb (lsuc k) Δ (tyU k) (boxt t) :: nil) e]).
Proof. intros Hb Hσ He HΔ Ht H1. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** Term heads. *)
Local Notation rect k Δ T c := (elimt l1 l2 rb k Δ T (boxt c)).
Local Notation recT k Δ c := (elimT l1 l2 rb k Δ (boxT c)).

Lemma redt_var_inst k0 Δ T n : dnftm (bs 4) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty T ->
  redt l1 l2 rb k0 Δ T (var n) =
  Some (((usubst_tm (bs 4) (uext (k0 :: nil) φ))⦃gext_s (GCtx Δ :: GTy T :: GTm (var n) :: nil) σ⦄)[lext nil e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption | exact I]. reflexivity. Qed.

Lemma redt_nat_inst k0 Δ T : dnftm (bs 5) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T tmNat =
  Some (((usubst_tm (bs 5) (uext nil φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_pi_inst k0 Δ T k k' s0 t0 : dnftm (bs 6) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm s0 -> dnftm t0 ->
  dnftm (rect (lsuc k) Δ (tyU k) s0) -> dnftm (rect (lsuc k') (cext Δ (tyEl k s0) k) (tyU k') t0) ->
  redt l1 l2 rb k0 Δ T (tmPi k k' s0 t0) =
  Some (((usubst_tm (bs 6) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTm s0 :: GTm t0 :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s0 :: rect (lsuc k') (cext Δ (tyEl k s0) k) (tyU k') t0 :: nil) e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_U_inst k0 Δ T k : dnftm (bs 7) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T (tmU k) =
  Some (((usubst_tm (bs 7) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_zero_inst k0 Δ T : dnftm (bs 8) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T zero =
  Some (((usubst_tm (bs 8) (uext nil φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_succ_inst k0 Δ T t0 : dnftm (bs 9) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm t0 ->
  dnftm (rect lzero Δ tyNat t0) ->
  redt l1 l2 rb k0 Δ T (succ t0) =
  Some (((usubst_tm (bs 9) (uext nil φ))⦃gext_s (GCtx Δ :: GTm t0 :: nil) σ⦄)[lext (rect lzero Δ tyNat t0 :: nil) e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_natrec_inst k0 Δ T k M s0 z0 t0 : dnftm (bs 10) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty M -> dnftm s0 -> dnftm z0 -> dnftm t0 ->
  dnftm (recT k (cext Δ tyNat lzero) M) -> dnftm (rect k Δ (subst_ty M (lsingle zero)) s0) ->
  dnftm (rect k (cext (cext Δ tyNat lzero) M k) (subst_ty M lsucc) z0) -> dnftm (rect lzero Δ tyNat t0) ->
  redt l1 l2 rb k0 Δ T (natrec k M s0 z0 t0) =
  Some (((usubst_tm (bs 10) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil) σ⦄)
          [lext (recT k (cext Δ tyNat lzero) M :: rect k Δ (subst_ty M (lsingle zero)) s0 ::
                 rect k (cext (cext Δ tyNat lzero) M k) (subst_ty M lsucc) z0 :: rect lzero Δ tyNat t0 :: nil) e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_lam_inst k0 Δ k1 k2 C B k k' A b : dnftm (bs 11) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm b ->
  dnftm (recT k Δ A) -> dnftm (rect k' (cext Δ A k) B b) ->
  redt l1 l2 rb k0 Δ (tyPi k1 k2 C B) (lam k k' A b) =
  Some (((usubst_tm (bs 11) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) σ⦄)
          [lext (recT k Δ A :: rect k' (cext Δ A k) B b :: nil) e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_app_inst k0 Δ T k k' A B f a : dnftm (bs 12) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm f -> dnftm a ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) ->
  dnftm (rect (lmax k k') Δ (tyPi k k' A B) f) -> dnftm (rect k Δ A a) ->
  redt l1 l2 rb k0 Δ T (app f k k' A B a) =
  Some (((usubst_tm (bs 12) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: rect (lmax k k') Δ (tyPi k k' A B) f :: rect k Δ A a :: nil) e]).
Proof. intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

End Red.

Lemma gdnf_gext_s os σ : Forall dnfo os -> gdnf σ -> gdnf (gext_s os σ).
Proof.
  intros Ho Hσ i; unfold gext_s. destruct (Nat.ltb_spec i (length os)); [|apply Hσ].
  rewrite Forall_forall in Ho. apply Ho, nth_In; lia.
Qed.
Lemma lk_dnf_lext xs e : Forall dnftm xs -> LK dnftm e -> LK dnftm (lext xs e).
Proof.
  intros Hx He n. rewrite llk_lext. destruct (Nat.ltb_spec n (length xs)); [|apply He].
  rewrite Forall_forall in Hx. apply Hx, nth_In; lia.
Qed.

Lemma lk_dnf_lcons d a : LK dnftm d -> dnftm a -> LK dnftm (lcons d a).
Proof. intros Hd Ha [|n]; cbn; [exact Ha | apply Hd]. Qed.
Ltac lk_dnf_tac := repeat (apply lk_dnf_lcons; [| eapply wf_tm_dnf; eassumption]); assumption.

Lemma gext_s2 x y σ i : gext_s (x :: y :: nil) σ i = gcons (gcons σ x) y i.
Proof. unfold gext_s; destruct i as [|[|i]]; cbn; auto. f_equal; lia. Qed.
Lemma gext_s3 x y z σ i : gext_s (x :: y :: z :: nil) σ i = gcons (gcons (gcons σ x) y) z i.
Proof. unfold gext_s; destruct i as [|[|[|i]]]; cbn; auto. f_equal; lia. Qed.

Ltac inst_cbn := unfold uext, gext_s, gv, gu; try unfold lsingle; try unfold lsucc;
  cbn [length Nat.ltb Nat.leb Nat.sub nth lvsubst ucsubst usubst_tm usubst_ty ulsubst gcsubst gsubst_tm
       gsubst_ty glsubst pctx pty ptm subst_tm subst_ty lcomp gsubst GSubst_tm GSubst_ty GSubst_ctx subst
       Subst_tm Subst_ty lext fold_left llk lcons'].

Ltac inst_cbn_in H := unfold uext, gext_s, gv, gu in H; try unfold lsingle in H; try unfold lsucc in H;
  cbn [length Nat.ltb Nat.leb Nat.sub nth lvsubst ucsubst usubst_tm usubst_ty ulsubst gcsubst gsubst_tm
       gsubst_ty glsubst pctx pty ptm subst_tm subst_ty lcomp gsubst GSubst_tm GSubst_ty GSubst_ctx subst
       Subst_tm Subst_ty lext fold_left llk lcons'] in H.

Section GS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

(** Images at a C-declaration over a context. *)
Lemma GSubRel_code {G' G σ1 σ2 D o1 o2 Δ1 Δ2 T1 T2 k} :
  GSubRel EP EM G' G σ1 σ2 -> gdecl_gsubst D σ1 = gdTy Δ1 lC k -> gdecl_gsubst D σ2 = gdTy Δ2 lC k ->
  o1 = GTy T1 -> o2 = GTy T2 ->
  [ G' ; Δ1 ⊢[ lC ] T1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] T2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] T1 ≅ T2 @ k ] -> ty_leq T1 T2 ->
  GSubRel EP EM G' (gext G D) (gcons σ1 o1) (gcons σ2 o2).
Proof.
  intros Hσ E1 E2 -> -> H1 H2 H12 E.
  apply (GSubRel_cons2 EP EM Hσ); rewrite ?E1, ?E2; cbn [dnfo gobj_wf].
  - exact (wf_ty_dnf H1).
  - exact (wf_ty_dnf H2).
  - exact H1.
  - exact H2.
  - apply (GObjRel_ty EP EM); [intros; exact E | exact H12].
  - apply (GObjRel_ty EP EM); [intros; apply ty_leq_refl | exact (eqty_refl _ _ _ _ _ (lift_ty (j := lD) H1 ltac:(unfold lle; cbn; lia)))].
  - apply (GObjRel_ty EP EM); [intros; apply ty_leq_refl | exact (eqty_refl _ _ _ _ _ (lift_ty (j := lD) H2 ltac:(unfold lle; cbn; lia)))].
Qed.

Lemma GSubRel_ctx1' {G' G σ σ' Δ Δ'} : GSubRel EP EM G' G σ σ' -> [ G' ; Δ ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ ≅ Δ' ] ->
  GSubRel EP EM G' (gext G gdCtx) (gcons σ (GCtx Δ)) (gcons σ' (GCtx Δ')).
Proof.
  intros Hσ HΔ HΔΔ.
  exact (GSubRel_ext EP EM (fun i => gext_s_one _ _ i) (fun i => gext_s_one _ _ i) (GSubRel_ctx1 EP EM Hσ HΔ HΔΔ)).
Qed.

Lemma GSubRel_code_tm {G' G σ1 σ2 D o1 o2 Δ1 Δ2 A1 A2 t1 t2 k} :
  GSubRel EP EM G' G σ1 σ2 -> gdecl_gsubst D σ1 = gdTm Δ1 lC A1 k -> gdecl_gsubst D σ2 = gdTm Δ2 lC A2 k ->
  o1 = GTm t1 -> o2 = GTm t2 ->
  [ G' ; Δ1 ⊢[ lC ] t1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] t2 : A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : A1 @ k ] ->
  tm_leq t1 t2 -> GSubRel EP EM G' (gext G D) (gcons σ1 o1) (gcons σ2 o2).
Proof.
  intros Hσ E1 E2 -> -> H1 H2 H12 E.
  apply (GSubRel_cons2 EP EM Hσ); rewrite ?E1, ?E2; cbn [dnfo gobj_wf].
  - exact (wf_tm_dnf H1).
  - exact (wf_tm_dnf H2).
  - exact H1.
  - exact H2.
  - exact (GObjRel_tm EP EM E H12).
  - exact (GObjRel_tm EP EM (tm_leq_refl _) (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) H1 ltac:(unfold lle; cbn; lia)))).
  - exact (GObjRel_tm EP EM (tm_leq_refl _) (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) H2 ltac:(unfold lle; cbn; lia)))).
Qed.

Lemma GS_El {G0 L' φ G' σ1 σ2 Δ1 Δ2 t1 t2 k} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] t1 : tyU k @ lsuc k ] -> [ G' ; Δ2 ⊢[ lC ] t2 : tyU k @ lsuc k ] ->
  [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : tyU k @ lsuc k ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG 3 G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTm t1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTm t2 :: nil) σ2).
Proof.
  intros Hσ HΔ1 HΔ Ht1 Ht2 Ht E.
  rewrite (G_us_brG_uext 3 G0 L' φ (k :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s2 _ _ _ i)) (fun i => eq_sym (gext_s2 _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: nil) φ)) (brDecls 3) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (G_us G0 L' φ) gdCtx) (gdTm (cvar 0) lC (tyU k) (lsuc k))).
  refine (GSubRel_code_tm _ _ _ eq_refl eq_refl Ht1 Ht2 Ht E); [exact (GSubRel_ctx1' Hσ HΔ1 HΔ) | reflexivity | reflexivity].
Qed.

(** Images at a declaration of any static layer. *)
Lemma GSubRel_ty_i {G' G σ1 σ2 D o1 o2 Δ1 Δ2 T1 T2 i k} : lle i lD ->
  GSubRel EP EM G' G σ1 σ2 -> gdecl_gsubst D σ1 = gdTy Δ1 i k -> gdecl_gsubst D σ2 = gdTy Δ2 i k ->
  o1 = GTy T1 -> o2 = GTy T2 ->
  [ G' ; Δ1 ⊢[ i ] T1 @ k ] -> [ G' ; Δ2 ⊢[ i ] T2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] T1 ≅ T2 @ k ] ->
  (lle i lC -> ty_leq T1 T2) -> GSubRel EP EM G' (gext G D) (gcons σ1 o1) (gcons σ2 o2).
Proof.
  intros Hi Hσ E1 E2 -> -> H1 H2 H12 E.
  apply (GSubRel_cons2 EP EM Hσ); rewrite ?E1, ?E2; cbn [dnfo gobj_wf].
  - exact (wf_ty_dnf H1).
  - exact (wf_ty_dnf H2).
  - exact H1.
  - exact H2.
  - exact (GObjRel_ty EP EM E H12).
  - apply (GObjRel_ty EP EM); [intros; apply ty_leq_refl | exact (eqty_refl _ _ _ _ _ (lift_ty (j := lD) H1 Hi))].
  - apply (GObjRel_ty EP EM); [intros; apply ty_leq_refl | exact (eqty_refl _ _ _ _ _ (lift_ty (j := lD) H2 Hi))].
Qed.

Lemma GSubRel_tm_i {G' G σ1 σ2 D o1 o2 Δ1 Δ2 A1 A2 t1 t2 i k} : lle i lD ->
  GSubRel EP EM G' G σ1 σ2 -> gdecl_gsubst D σ1 = gdTm Δ1 i A1 k -> gdecl_gsubst D σ2 = gdTm Δ2 i A2 k ->
  o1 = GTm t1 -> o2 = GTm t2 ->
  [ G' ; Δ1 ⊢[ i ] t1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ i ] t2 : A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : A1 @ k ] ->
  tm_leq t1 t2 -> GSubRel EP EM G' (gext G D) (gcons σ1 o1) (gcons σ2 o2).
Proof.
  intros Hi Hσ E1 E2 -> -> H1 H2 H12 E.
  apply (GSubRel_cons2 EP EM Hσ); rewrite ?E1, ?E2; cbn [dnfo gobj_wf].
  - exact (wf_tm_dnf H1).
  - exact (wf_tm_dnf H2).
  - exact H1.
  - exact H2.
  - exact (GObjRel_tm EP EM E H12).
  - exact (GObjRel_tm EP EM (tm_leq_refl _) (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) H1 Hi))).
  - exact (GObjRel_tm EP EM (tm_leq_refl _) (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) H2 Hi))).
Qed.

Lemma GS_pi {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 k1 k2} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k1 ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k1 ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k1 ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ,, A1 @ k1 ⊢[ lC ] B1 @ k2 ] -> [ G' ; Δ2 ,, A2 @ k1 ⊢[ lC ] B2 @ k2 ] ->
  [ G' ; Δ1 ,, A1 @ k1 ⊢[ lD ] B1 ≅ B2 @ k2 ] -> ty_leq B1 B2 ->
  GSubRel EP EM G' (G_us (brG 1 G0) L' (uext (k1 :: k2 :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: nil) σ2).
Proof.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB.
  rewrite (G_us_brG_uext 1 G0 L' φ (k1 :: k2 :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k1 :: k2 :: nil) φ)) (brDecls 1) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k1)) (gdTy (cvar 1 ,, gv 0 @ k1) lC k2)).
  pose proof (dnfty_nfty _ (wf_ty_dnf HA1)) as NA1. pose proof (dnfty_nfty _ (wf_ty_dnf HA2)) as NA2.
  refine (GSubRel_code _ _ _ eq_refl eq_refl HB1 HB2 HB EB).
  - refine (GSubRel_code _ _ _ eq_refl eq_refl HA1 HA2 HA EA); [exact (GSubRel_ctx1' Hσ HΔ1 HΔ) | reflexivity | reflexivity].
  - cbn; unfold gv; cbn. rewrite (subst_id_ty A1); [reflexivity | exact NA1 | intros; cbn; f_equal; lia].
  - cbn; unfold gv; cbn. rewrite (subst_id_ty A2); [reflexivity | exact NA2 | intros; cbn; f_equal; lia].
Qed.

Local Ltac decl_eq := first [ reflexivity
  | cbn; unfold gv, gu; cbn; rewrite ?subst_lshift0_ty, ?subst_lshift0 by (apply dnfty_nfty || apply dnftm_nftm; assumption);
    reflexivity ].
Local Ltac lleC := unfold lle; cbn; lia.

Lemma GS_ctx0 {G0 L' φ G' σ1 σ2 Δ1 Δ2} k ls : brDecls k = gdCtx :: nil -> length ls = br_nu k ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  GSubRel EP EM G' (G_us (brG k G0) L' (uext ls φ)) (gext_s (GCtx Δ1 :: nil) σ1) (gext_s (GCtx Δ2 :: nil) σ2).
Proof.
  intros HD Hn Hσ HΔ1 HΔ. rewrite (G_us_brG_uext k G0 L' φ ls Hn), HD. exact (GSubRel_ctx1 EP EM Hσ HΔ1 HΔ).
Qed.

Lemma GS_var {G0 L' φ G' σ1 σ2 Δ1 Δ2 T1 T2 n k} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lD ] T1 @ k ] -> [ G' ; Δ2 ⊢[ lD ] T2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] T1 ≅ T2 @ k ] ->
  [ G' ; Δ1 ⊢[ lV ] var n : T1 @ k ] -> [ G' ; Δ2 ⊢[ lV ] var n : T2 @ k ] ->
  GSubRel EP EM G' (G_us (brG 4 G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy T1 :: GTm (var n) :: nil) σ1) (gext_s (GCtx Δ2 :: GTy T2 :: GTm (var n) :: nil) σ2).
Proof.
  intros Hσ HΔ1 HΔ HT1 HT2 HT Hv1 Hv2. pose proof (wf_ty_dnf HT1) as N1. pose proof (wf_ty_dnf HT2) as N2.
  rewrite (G_us_brG_uext 4 G0 L' φ (k :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: nil) φ)) (brDecls 4) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lD k)) (gdTm (cvar 1) lV (gv 0) k)).
  refine (GSubRel_tm_i (i := lV) ltac:(lleC) _ _ _ eq_refl eq_refl Hv1 Hv2 _ (tm_leq_refl _)); [| decl_eq | decl_eq |].
  - refine (GSubRel_ty_i (i := lD) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HT1 HT2 HT
             (fun H => ltac:(unfold lle in H; cbn in H; lia))); reflexivity.
  - exact (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hv1 ltac:(lleC))).
Qed.

Lemma GS_succ {G0 L' φ G' σ1 σ2 Δ1 Δ2 t1 t2} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] t1 : tyNat @ lzero ] -> [ G' ; Δ2 ⊢[ lC ] t2 : tyNat @ lzero ] ->
  [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : tyNat @ lzero ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG 9 G0) L' (uext nil φ))
    (gext_s (GCtx Δ1 :: GTm t1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTm t2 :: nil) σ2).
Proof.
  intros Hσ HΔ1 HΔ Ht1 Ht2 Ht E.
  rewrite (G_us_brG_uext 9 G0 L' φ nil eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s2 _ _ _ i)) (fun i => eq_sym (gext_s2 _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext nil φ)) (brDecls 9) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (G_us G0 L' φ) gdCtx) (gdTm (cvar 0) lC tyNat lzero)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl Ht1 Ht2 Ht E); reflexivity.
Qed.

Lemma GS_pi' {G0 L' φ G' σ1 σ2 Δ1 Δ2 s1 s2 t1 t2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] s1 : tyU k @ lsuc k ] -> [ G' ; Δ2 ⊢[ lC ] s2 : tyU k @ lsuc k ] ->
  [ G' ; Δ1 ⊢[ lD ] s1 ≅ s2 : tyU k @ lsuc k ] -> tm_leq s1 s2 ->
  [ G' ; Δ1 ,, tyEl k s1 @ k ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> [ G' ; Δ2 ,, tyEl k s2 @ k ⊢[ lC ] t2 : tyU k' @ lsuc k' ] ->
  [ G' ; Δ1 ,, tyEl k s1 @ k ⊢[ lD ] t1 ≅ t2 : tyU k' @ lsuc k' ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG 6 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTm s1 :: GTm t1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTm s2 :: GTm t2 :: nil) σ2).
Proof.
  intros Hσ HΔ1 HΔ Hs1 Hs2 Hs Es Ht1 Ht2 Ht Et.
  pose proof (wf_tm_dnf Hs1) as N1. pose proof (wf_tm_dnf Hs2) as N2.
  rewrite (G_us_brG_uext 6 G0 L' φ (k :: k' :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 6) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTm (cvar 0) lC (tyU k) (lsuc k)))
       (gdTm (cvar 1 ,, tyEl k (gu 0) @ k) lC (tyU k') (lsuc k'))).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ht1 Ht2 Ht Et); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl Hs1 Hs2 Hs Es); reflexivity.
Qed.

Lemma GS_natrec {G0 L' φ G' σ1 σ2 Δ1 Δ2 M1 M2 s1 s2 z1 z2 t1 t2 k} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ,, tyNat @ lzero ⊢[ lC ] M1 @ k ] -> [ G' ; Δ2 ,, tyNat @ lzero ⊢[ lC ] M2 @ k ] ->
  [ G' ; Δ1 ,, tyNat @ lzero ⊢[ lD ] M1 ≅ M2 @ k ] -> ty_leq M1 M2 ->
  [ G' ; Δ1 ⊢[ lC ] s1 : M1[lsingle zero] @ k ] -> [ G' ; Δ2 ⊢[ lC ] s2 : M2[lsingle zero] @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] s1 ≅ s2 : M1[lsingle zero] @ k ] -> tm_leq s1 s2 ->
  [ G' ; Δ1 ,, tyNat @ lzero ,, M1 @ k ⊢[ lC ] z1 : M1[lsucc] @ k ] ->
  [ G' ; Δ2 ,, tyNat @ lzero ,, M2 @ k ⊢[ lC ] z2 : M2[lsucc] @ k ] ->
  [ G' ; Δ1 ,, tyNat @ lzero ,, M1 @ k ⊢[ lD ] z1 ≅ z2 : M1[lsucc] @ k ] -> tm_leq z1 z2 ->
  [ G' ; Δ1 ⊢[ lC ] t1 : tyNat @ lzero ] -> [ G' ; Δ2 ⊢[ lC ] t2 : tyNat @ lzero ] ->
  [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : tyNat @ lzero ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG 10 G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy M1 :: GTm s1 :: GTm z1 :: GTm t1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy M2 :: GTm s2 :: GTm z2 :: GTm t2 :: nil) σ2).
Proof.
  intros Hσ HΔ1 HΔ HM1 HM2 HM EM1 Hs1 Hs2 Hs Es Hz1 Hz2 Hz Ez Ht1 Ht2 Ht Et.
  pose proof (wf_ty_dnf HM1) as N1. pose proof (wf_ty_dnf HM2) as N2.
  rewrite (G_us_brG_uext 10 G0 L' φ (k :: nil) eq_refl).
  assert (E5 : forall a b c d f τ i, gext_s (a :: b :: c :: d :: f :: nil) τ i =
                                   gcons (gcons (gcons (gcons (gcons τ a) b) c) d) f i).
  { intros; unfold gext_s; destruct i as [|[|[|[|[|i]]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E5 _ _ _ _ _ _ i)) (fun i => eq_sym (E5 _ _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: nil) φ)) (brDecls 10) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0 ,, tyNat @ lzero) lC k))
        (gdTm (cvar 1) lC (tyGvar 0 (lsingle zero)) k))
        (gdTm (cvar 2 ,, tyNat @ lzero ,, gv 1 @ k) lC (tyGvar 1 lsucc) k))
        (gdTm (cvar 3) lC tyNat lzero)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ht1 Ht2 Ht Et); [| reflexivity | reflexivity].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hz1 Hz2 Hz Ez); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hs1 Hs2 Hs Es); [| reflexivity | reflexivity].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HM1 HM2 HM (fun _ => EM1)); [| reflexivity | reflexivity].
  exact (GSubRel_ctx1' Hσ HΔ1 HΔ).
Qed.

Lemma GS_lam {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 b1 b2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] B1 @ k' ] -> [ G' ; Δ2 ,, A2 @ k ⊢[ lD ] B2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] B1 ≅ B2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lC ] b1 : B1 @ k' ] -> [ G' ; Δ2 ,, A2 @ k ⊢[ lC ] b2 : B2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] b1 ≅ b2 : B1 @ k' ] -> tm_leq b1 b2 ->
  GSubRel EP EM G' (G_us (brG 11 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: GTm b1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: GTm b2 :: nil) σ2).
Proof.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB Hb1 Hb2 Hb Eb.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_ty_dnf HB1) as NB1. pose proof (wf_ty_dnf HB2) as NB2.
  rewrite (G_us_brG_uext 11 G0 L' φ (k :: k' :: nil) eq_refl).
  assert (E4 : forall a b c d τ i, gext_s (a :: b :: c :: d :: nil) τ i = gcons (gcons (gcons (gcons τ a) b) c) d i).
  { intros; unfold gext_s; destruct i as [|[|[|[|i]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E4 _ _ _ _ _ i)) (fun i => eq_sym (E4 _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 11) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTy (cvar 1 ,, gv 0 @ k) lD k'))
       (gdTm (cvar 2 ,, gv 1 @ k) lC (gv 0) k')).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hb1 Hb2 Hb Eb); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lD) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB _); [| decl_eq | decl_eq |].
  - refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
  - intros H; unfold lle in H; cbn in H; lia.
Qed.

Lemma GS_app {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 f1 f2 a1 a2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lC ] B1 @ k' ] -> [ G' ; Δ2 ,, A2 @ k ⊢[ lC ] B2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] B1 ≅ B2 @ k' ] -> ty_leq B1 B2 ->
  [ G' ; Δ1 ⊢[ lC ] f1 : tyPi k k' A1 B1 @ lmax k k' ] -> [ G' ; Δ2 ⊢[ lC ] f2 : tyPi k k' A2 B2 @ lmax k k' ] ->
  [ G' ; Δ1 ⊢[ lD ] f1 ≅ f2 : tyPi k k' A1 B1 @ lmax k k' ] -> tm_leq f1 f2 ->
  [ G' ; Δ1 ⊢[ lC ] a1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] a2 : A2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] a1 ≅ a2 : A1 @ k ] -> tm_leq a1 a2 ->
  GSubRel EP EM G' (G_us (brG 12 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: GTm f1 :: GTm a1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: GTm f2 :: GTm a2 :: nil) σ2).
Proof.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB Hf1 Hf2 Hf Ef Ha1 Ha2 Ha Ea.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_ty_dnf HB1) as NB1. pose proof (wf_ty_dnf HB2) as NB2.
  rewrite (G_us_brG_uext 12 G0 L' φ (k :: k' :: nil) eq_refl).
  assert (E5 : forall a b c d f τ i, gext_s (a :: b :: c :: d :: f :: nil) τ i =
                                   gcons (gcons (gcons (gcons (gcons τ a) b) c) d) f i).
  { intros; unfold gext_s; destruct i as [|[|[|[|[|i]]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E5 _ _ _ _ _ _ i)) (fun i => eq_sym (E5 _ _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 12) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTy (cvar 1 ,, gv 0 @ k) lC k'))
       (gdTm (cvar 2) lC (tyPi k k' (gv 1) (gv 0)) (lmax k k'))) (gdTm (cvar 3) lC (gv 2) k)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ha1 Ha2 Ha Ea); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hf1 Hf2 Hf Ef); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

End GS.

Section Rec.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
#[local] Instance LR_M_lawsRec2 : VPLaws (@lr_vp LRM) := vpM_laws EP EM.
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtmM := (@LRtm EM LRM).

Variables (G0 : gctx) (Γ0 : ctx) (L' : nat) (φ : nat -> lvl) (l1 l2 l1' l2' : lvl)
  (MT MT' Mt Mt' : ty) (bs bs' : nat -> tm).
Hypothesis (Hφ : usub_ok φ L' (gL G0))
  (HMT : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT @ lvren l1 (ush 1) ])
  (HMT' : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT' @ lvren l1' (ush 1) ])
  (Hl1 : lequiv L' (lvsubst l1 φ) (lvsubst l1' φ))
  (VMT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT ψ) (usubst_ty MT' ψ)
       (lvsubst (lvren l1 (ush 1)) ψ))
  (VMTl : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT ψ) (usubst_ty MT ψ)
       (lvsubst (lvren l1 (ush 1)) ψ))
  (VMTr : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT' ψ) (usubst_ty MT' ψ)
       (lvsubst (lvren l1' (ush 1)) ψ))
  (HMt : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt @ lvren l2 (ush 1) ])
  (HMt' : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt' @ lvren l2' (ush 1) ])
  (Hl2 : lequiv L' (lvsubst l2 φ) (lvsubst l2' φ))
  (VMt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt ψ) (usubst_ty Mt' ψ)
       (lvsubst (lvren l2 (ush 1)) ψ))
  (VMtl : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt ψ) (usubst_ty Mt ψ)
       (lvsubst (lvren l2 (ush 1)) ψ))
  (VMtr : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt' ψ) (usubst_ty Mt' ψ)
       (lvsubst (lvren l2' (ush 1)) ψ))
  (Hbs : forall k, k < 13 -> [ brG k G0 ; brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                               bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ])
  (Hbs' : forall k, k < 13 -> [ brG k G0 ; brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                               bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ])
  (VBr : forall k, k < 13 -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VTmSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) ψ)
       (usubst_tm (bs k) ψ) (usubst_tm (bs' k) ψ)
       (usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) ψ) (lvsubst (brLv k l1 l2) ψ))
  (VBr' : forall k, k < 13 -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VTmSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2') ψ)
       (usubst_tm (bs' k) ψ) (usubst_tm (bs' k) ψ)
       (usubst_ty (brRes k (wrapMT MT') (wrapMt Mt')) ψ) (lvsubst (brLv k l1' l2') ψ))
  (VΓ : VCtxSM (G_us G0 L' φ) (ucsubst Γ0 φ)).
Variables (G' : gctx) (σ σ' : gsub) (Θ : ctx) (e e' : lsub).
Hypothesis (Hσ : GSubRel G' (G_us G0 L' φ) σ σ')
  (He : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e e').

Local Notation MTL := ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))]).
Local Notation MTR := ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄[llift (gwk (uwk e'))]).
Local Notation MtL := ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))]).
Local Notation MtR := ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄[llift (gwk (gwk (uwk e')))]).
Local Notation bsL := (fun k => ((usubst_tm (bs k) (uupn (br_nu k) φ))⦃gbsub k σ⦄)[lliftn (br_nl k) (bsub k e)]).
Local Notation bsR := (fun k => ((usubst_tm (bs' k) (uupn (br_nu k) φ))⦃gbsub k σ'⦄)[lliftn (br_nl k) (bsub k e')]).

Hypothesis (HrbL : RBwf G' Θ (lvsubst l1 φ) (lvsubst l2 φ) MTL MtL bsL)
  (HrbR : RBwf G' Θ (lvsubst l1' φ) (lvsubst l2' φ) MTR MtR bsR).

(** Facts from the hypotheses. *)
Hypothesis (EL : gL G' = L').
Lemma Nσ : gdnf σ. Proof. exact (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)). Qed.
Lemma Nσ' : gdnf σ'. Proof. exact (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)). Qed.
Lemma De : LK dnftm e. Proof. exact (proj1 (SubRel_dnf _ _ _ _ _ He)). Qed.
Lemma De' : LK dnftm e'. Proof. exact (proj2 (SubRel_dnf _ _ _ _ _ He)). Qed.
Lemma HΘ : [ G' ; Θ ⊢[ lM ] ].
Proof. pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X. Qed.
Lemma He'r : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ') Θ e' e'.
Proof.
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  exact (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) (SubRel_refl_r He)).
Qed.
Lemma He'l : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e' e'.
Proof. exact (SubRel_refl_r He). Qed.

(** Boxed code related from syntax. *)
Lemma box_rel {Δ c c' k} : [ G' ; Δ ⊢[ lD ] ] -> lwf L' k ->
  [ G' ; Δ ⊢[ lC ] c @ k ] -> [ G' ; Δ ⊢[ lC ] c' @ k ] -> ty_leq c c' ->
  LRtmM lzero G' Θ (tyCTyp Δ k) (tyCTyp Δ k) (boxT c) (boxT c').
Proof.
  intros HΔ Hk Hc Hc' E.
  pose proof (static_code_ty (i := lC) ltac:(unfold lle; cbn; lia) Hc Hc' E) as Hcc.
  destruct (VTyG_of_eq EP EM (lift_eqty (j := lD) Hcc ltac:(unfold lle; cbn; lia))) as [VP VM].
  destruct (CtxRelG_of_eq EP EM (eqc_refl _ _ _ HΔ)) as [CP CM].
  apply (LRtm_boxT EP EM HΘ HΔ Hc Hc' E); [rewrite EL; exact Hk | | exact VP | exact VM].
  exact (conj (eqc_refl _ _ _ HΔ) (conj CP CM)).
Qed.

Lemma box_rel_tm {Δ A t t' k} : [ G' ; Δ ⊢[ lD ] A @ k ] -> lwf L' k ->
  [ G' ; Δ ⊢[ lC ] t : A @ k ] -> [ G' ; Δ ⊢[ lC ] t' : A @ k ] -> tm_leq t t' ->
  LRtmM lzero G' Θ (tyCTrm Δ A k) (tyCTrm Δ A k) (boxt t) (boxt t').
Proof.
  intros HA Hk Ht Ht' E. pose proof (ctx_of_wf_ty (i := lD) eq_refl HA) as HΔ.
  pose proof (static_code_tm (i := lC) ltac:(unfold lle; cbn; lia) Ht Ht' E) as Htt.
  destruct (VTmG_of_eq EP EM (lift_eqtm (j := lD) Htt ltac:(unfold lle; cbn; lia))) as [VP VM].
  destruct (VTyG_of_eq EP EM (eqty_refl _ _ _ _ _ HA)) as [AP AM].
  destruct (CtxRelG_of_eq EP EM (eqc_refl _ _ _ HΔ)) as [CP CM].
  apply (LRtm_boxt EP EM HΘ HΔ HA Ht Ht' E); [rewrite EL; exact Hk | | exact AP | exact AM | exact VP | exact VM].
  exact (conj (eqc_refl _ _ _ HΔ) (conj CP CM)).
Qed.

(** ** The common part of a branch case

    Both reducts come from the branches' validity; the right one is
    switched from the left levels to its own by level invariance. *)

Lemma br_core k ls ls' os os' xsL xsR goalL goalR l : k < 13 ->
  length ls = br_nu k -> length ls' = br_nu k -> Forall (lwf L') ls -> Forall (lwf L') ls' ->
  (forall i, leqv (uext ls φ i) (uext ls' φ i)) ->
  GSubRel G' (G_us (brG k G0) L' (uext ls φ)) (gext_s os σ) (gext_s os' σ') ->
  GSubRel G' (G_us (brG k G0) L' (uext ls' φ)) (gext_s os' σ') (gext_s os' σ') ->
  SubRelM G' ((ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) (uext ls φ))⦃gext_s os σ⦄) Θ (lext xsL e) (lext xsR e') ->
  SubRelM G' ((ucsubst (brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2') (uext ls' φ))⦃gext_s os' σ'⦄) Θ
    (lext xsR e') (lext xsR e') ->
  LRtyM l G' Θ goalL (((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e]) ->
  LRtyM l G' Θ (((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls φ))⦃gext_s os σ⦄)[lext xsR e']) goalR ->
  LRtyM l G' Θ goalR (((usubst_ty (brRes k (wrapMT MT') (wrapMt Mt')) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e']) ->
  lequiv (gL G') l (lvsubst (brLv k l1 l2) (uext ls φ)) ->
  lequiv (gL G') l (lvsubst (brLv k l1' l2') (uext ls' φ)) ->
  LRtmM l G' Θ goalL goalR (((usubst_tm (bs k) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e])
    (((usubst_tm (bs' k) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e']).
Proof.
  intros Hk Hn Hn' Hls Hls' Eψ GS1 GS2 SR1 SR2 T1 T2 T3 Hl Hl'.
  assert (Hψ : usub_ok (uext ls φ) L' (gL (brG k G0))).
  { unfold brG, gctx_uwk; cbn [gL]. rewrite <- Hn. exact (usub_ok_uext ls φ L' (gL G0) Hls Hφ). }
  assert (Hψ' : usub_ok (uext ls' φ) L' (gL (brG k G0))).
  { unfold brG, gctx_uwk; cbn [gL]. rewrite <- Hn'. exact (usub_ok_uext ls' φ L' (gL G0) Hls' Hφ). }
  pose proof (VBr k Hk _ _ Hψ _ _ _ GS1 G' gwk_id (gwk_ok_id G') _ _ _ SR1) as Z1; cbn [gwa] in Z1.
  pose proof (VBr' k Hk _ _ Hψ' _ _ _ GS2 G' gwk_id (gwk_ok_id G') _ _ _ SR2) as Z2; cbn [gwa] in Z2.
  pose proof (LRtm_conv_r (LRtm_conv_l (LRtm_lconv Z1 Hl) T1) T2) as W1.
  pose proof (LRtm_conv_r (LRtm_conv_l (LRtm_lconv Z2 Hl') T3) (LRty_sym T3)) as W2.
  refine (LRtm_leq W1 W2 _).
  apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl |].
  apply (proj1 (proj2 leq_gsubst_all)); [intros; apply gobj_leq_refl |].
  apply (proj1 (proj2 leq_usubst_all)); [exact Eψ | apply tm_leq_refl].
Qed.

(** ** Natural numbers *)

Lemma rec_T_nat {ΔL ΔR kL kR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' lzero kL -> lequiv L' lzero kR ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT tyNat)) (motT (wrapMT MTR) kR ΔR (boxT tyNat))
    (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL (boxT tyNat))
    (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR (boxT tyNat)).
Proof.
  intros HΔL HΔ HkL HkR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  pose proof EL as EL'.
  assert (Hw0 : lwf L' lzero) by exact I.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL).
  assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (HN : forall Δ k, [ G' ; Δ ⊢[ lD ] ] -> lequiv L' lzero k -> [ G' ; Δ ⊢[ lC ] tyNat @ k ]).
  { intros Δ k HΔ0 Hk. eapply wft_lconv; [apply wft_nat; [discriminate | exact HΔ0] | rewrite EL; apply lequiv_sym, Hk]. }
  (* the reducts *)
  set (rL := ((usubst_tm (bs 0) (uext nil φ))⦃gext_s (GCtx ΔL :: nil) σ⦄)[lext nil e]).
  set (rR := ((usubst_tm (bs' 0) (uext nil φ))⦃gext_s (GCtx ΔR :: nil) σ'⦄)[lext nil e']).
  assert (HredL : redT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL tyNat = Some rL).
  { apply redT_nat_inst; [exact (wf_tm_dnf (Hbs 0 ltac:(lia))) | exact Nσ | exact De | exact (wf_ctx_dnf HΔL)]. }
  assert (HredR : redT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR tyNat = Some rR).
  { apply redT_nat_inst; [exact (wf_tm_dnf (Hbs' 0 ltac:(lia))) | exact Nσ' | exact De' | exact (wf_ctx_dnf HΔR)]. }
  (* the branch at the extended substitutions *)
  assert (Hψ : usub_ok (uext nil φ) L' (gL (brG 0 G0)))
    by exact (usub_ok_uext nil φ L' (gL G0) (Forall_nil _) Hφ).
  pose proof (VBr 0 ltac:(lia) _ _ Hψ) as X.
  rewrite (G_us_brG_uext 0 G0 L' φ nil eq_refl) in X. cbn [brDecls map gdecl_usubst List.app] in X.
  pose proof (X _ _ _ (GSubRel_ctx1 EP EM Hσ HΔL HΔ) G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  cbn [brΓ brLocs cexts br_nu br_ng br_ar] in Y.
  replace ((ucsubst (wkc 0 1 Γ0) (uext nil φ))⦃gext_s (GCtx ΔL :: nil) σ⦄) with (gcsubst (ucsubst Γ0 φ) σ) in Y
    by (symmetry; exact (wkc_inst 0 1 Γ0 nil (GCtx ΔL :: nil) φ σ eq_refl eq_refl)).
  pose proof (Y _ _ _ He) as Z. clear X Y.
  cbn [brRes br_nu br_ng br_nl br_ar] in Z. unfold brLv in Z. cbn [br_nu br_ar Nat.ltb Nat.leb] in Z.
  change (lvsubst (lvren l1 (ush 0)) (uext nil φ)) with (lvsubst (lvren l1 (ush (length (@nil lvl)))) (uext nil φ)) in Z.
  rewrite lvren_ush_uext in Z.
  change (wkb 0 1 0 (wrapMT MT)) with (wkb (length (@nil lvl)) (length (GCtx ΔL :: nil)) (length (@nil tm)) (wrapMT MT)) in Z.
  change ((?T)[e]) with (T[lext nil e]) in Z at 1.
  change ((?T)[e']) with (T[lext nil e']) in Z at 1.
  rewrite !motT_wkb_inst in Z by first [apply gdnf_gext_s; [repeat constructor; exact (wf_ctx_dnf HΔL) | exact Nσ]
                                       | apply lk_dnf_lext; [constructor | first [exact De | exact De']]].
  assert (Z' : LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) lzero ΔL (boxT tyNat))
                 (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) lzero ΔL (boxT tyNat))
                 rL rR) by exact Z.
  clear Z.
  (* the goal's types *)
  pose proof (box_rel HΔL HwL (HN _ _ HΔL HkL) (HN _ _ HΔL HkL) I) as BL.
  pose proof (box_rel HΔL Hw0 (HN _ _ HΔL (lequiv_refl _ _ Hw0)) (HN _ _ HΔL (lequiv_refl _ _ Hw0)) I) as B0.
  pose proof (box_rel HΔR HwR (HN _ _ HΔR HkR) (HN _ _ HΔR HkR) I) as BR.
  assert (Hwl1 : lwf L' (lvsubst l1 φ)) by (rewrite <- EL; exact (proj1 HrbL)).
  assert (T1 : LRtyM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT tyNat)) (motT (wrapMT MTL) lzero ΔL (boxT tyNat)))
    by exact (MotRel_T EP EM G0 Γ0 L' φ MT MT l1 l1 HMT HMT (lequiv_refl _ _ Hwl1) Hφ VMTl VMTl VΓ G' σ σ Θ e e
                (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL) BL B0).
  assert (T2 : LRtyM (lvsubst l1 φ) G' Θ
                 (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) lzero ΔL (boxT tyNat))
                 (motT (wrapMT MTR) kR ΔR (boxT tyNat)))
    by exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e'
                (Hσ) (He'l) EL Hw0 HkR HΔL HΔ B0 BR).
  pose proof (LRtm_conv_r (LRtm_conv_l Z' T1) T2) as W.
  (* anti-reduction *)
  destruct (LRtm_escape W) as [HrL _]. destruct (LRtm_escape (LRtm_sym W)) as [HrR _].
  rewrite (@gm_layer_M EP EM EMl) in HrL, HrR.
  assert (Hl1' : lequiv (gL G') (lvsubst l1 φ) (lvsubst l1' φ)) by (rewrite EL; exact Hl1).
  pose proof (tmred_elimT_beta HrbL (eq_ind_r (fun L => lwf L kL) HwL EL) HΔL (HN _ _ HΔL HkL) HredL HrL) as R1.
  pose proof (tmred_elimT_beta HrbR (eq_ind_r (fun L => lwf L kR) HwR EL) HΔR (HN _ _ HΔR HkR) HredR
                (wf_lconv _ _ _ _ _ _ _ HrR (lequiv_sym _ _ _ Hl1'))) as R2.
  pose proof (tmred_lconv _ _ _ _ _ R2 Hl1') as R2'.
  rewrite <- (@gm_layer_M EP EM EMl) in R1, R2'.
  exact (LRtm_red W R1 R2').
Qed.



Local Notation recTL k Δ c := (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ (boxT c)).
Local Notation recTR k Δ c := (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ (boxT c)).

Lemma rec_T_pi {ΔL ΔR kL kR k1 k2 k1' k2' A B A' B'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k1 k2) kL -> lequiv L' (lmax k1 k2) kR ->
  lwf L' k1 -> lwf L' k2 -> lwf L' k1' -> lwf L' k2' -> leqv k1 k1' -> leqv k2 k2' ->
  [ G' ; ΔL ⊢[ lC ] A @ k1 ] -> [ G' ; ΔL ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  [ G' ; ΔL ⊢[ lC ] A' @ k1 ] -> [ G' ; ΔL ,, A @ k1 ⊢[ lC ] B' @ k2 ] -> ty_leq A A' -> ty_leq B B' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k1 ΔL (boxT A)) (motT (wrapMT MTR) k1' ΔR (boxT A'))
    (recTL k1 ΔL A) (recTR k1' ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k2 (ΔL ,, A @ k1) (boxT B)) (motT (wrapMT MTR) k2' (ΔR ,, A' @ k1') (boxT B'))
    (recTL k2 (ΔL ,, A @ k1) B) (recTR k2' (ΔR ,, A' @ k1') B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyPi k1 k2 A B)))
    (motT (wrapMT MTR) kR ΔR (boxT (tyPi k1' k2' A' B')))
    (recTL kL ΔL (tyPi k1 k2 A B)) (recTR kR ΔR (tyPi k1' k2' A' B')).
Proof.
  intros HΔL HΔ HkL HkR Hw1 Hw2 Hw1' Hw2' E1 E2 HA HB HA' HB' EA EB IHA IHB.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q1 : lequiv L' k1 k1') by exact (leqv_lequiv _ _ _ Hw1 Hw1' E1).
  assert (Q2 : lequiv L' k2 k2') by exact (leqv_lequiv _ _ _ Hw2 Hw2' E2).
  (* declarative facts about the pieces *)
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD.
  pose proof (lift_eqty (j := lD) (static_code_ty Hl1c HA HA' EA) Hl1c) as HAA.
  pose proof (lift_eqty (j := lD) (static_code_ty Hl1c HB HB' EB) Hl1c) as HBB.
  assert (HΔA : [ G' ⊢[ lD ] ΔL ,, A @ k1 ≅ ΔR ,, A' @ k1' ]).
  { apply eqc_ext; [exact HΔ | exact HAD | exact HAA | rewrite EL; exact Q1]. }
  assert (HΔAk : [ G' ⊢[ lD ] ΔL ,, A @ k1 ≅ ΔR ,, A' @ k1 ]).
  { apply eqc_ext; [exact HΔ | exact HAD | exact HAA | rewrite EL; apply lequiv_refl, Hw1]. }
  assert (HA'R : [ G' ; ΔR ⊢[ lC ] A' @ k1 ]) by exact (ctxconv_ty HΔ (i := lC) eq_refl HA').
  assert (HB'R : [ G' ; ΔR ,, A' @ k1 ⊢[ lC ] B' @ k2 ]) by exact (ctxconv_ty HΔAk (i := lC) eq_refl HB').
  assert (HA'R' : [ G' ; ΔR ⊢[ lC ] A' @ k1' ]) by (eapply wft_lconv; [exact HA'R | rewrite EL; apply lequiv_sym, Q1]).
  assert (HB'R' : [ G' ; ΔR ,, A' @ k1' ⊢[ lC ] B' @ k2' ]).
  { eapply wft_lconv; [| rewrite EL; apply lequiv_sym, Q2].
    refine (ctxconv_ty _ (i := lC) eq_refl HB'R). apply eqc_ext; [apply eqc_refl, HΔR | exact (lift_ty (j := lD) HA'R Hl1c)
      | apply eqty_refl, (lift_ty (j := lD) HA'R Hl1c) | rewrite EL; exact Q1]. }
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  pose proof (wf_ty_dnf HA) as NA. pose proof (wf_ty_dnf HB) as NB.
  pose proof (wf_ty_dnf HA'R) as NA'. pose proof (wf_ty_dnf HB'R') as NB'.
  (* the recursive calls are typed *)
  destruct (LRtm_escape IHA) as [Ha1 _]. destruct (LRtm_escape (LRtm_sym IHA)) as [Ha1' _].
  destruct (LRtm_escape IHB) as [Ha2 _]. destruct (LRtm_escape (LRtm_sym IHB)) as [Ha2' _].
  (* the reducts *)
  set (xsL := recTL k1 ΔL A :: recTL k2 (ΔL ,, A @ k1) B :: nil).
  set (xsR := recTR k1' ΔR A' :: recTR k2' (ΔR ,, A' @ k1') B' :: nil).
  set (rL := ((usubst_tm (bs 1) (uext (k1 :: k2 :: nil) φ))⦃gext_s (GCtx ΔL :: GTy A :: GTy B :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 1) (uext (k1' :: k2' :: nil) φ))⦃gext_s (GCtx ΔR :: GTy A' :: GTy B' :: nil) σ'⦄)[lext xsR e']).
  set (rR0 := ((usubst_tm (bs' 1) (uext (k1 :: k2 :: nil) φ))⦃gext_s (GCtx ΔR :: GTy A' :: GTy B' :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL (tyPi k1 k2 A B) = Some rL).
  { apply redT_pi_inst; first [exact (wf_tm_dnf (Hbs 1 ltac:(lia))) | exact Nσ | exact De | exact (wf_ctx_dnf HΔL)
      | exact (wf_ty_dnf HA) | exact (wf_ty_dnf HB) | exact (wf_tm_dnf Ha1) | exact (wf_tm_dnf Ha2)]. }
  assert (HredR : redT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR (tyPi k1' k2' A' B') = Some rR).
  { apply redT_pi_inst; first [exact (wf_tm_dnf (Hbs' 1 ltac:(lia))) | exact Nσ' | exact De' | exact (wf_ctx_dnf HΔR)
      | exact (wf_ty_dnf HA'R) | exact (wf_ty_dnf HB'R') | exact (wf_tm_dnf Ha1') | exact (wf_tm_dnf Ha2')]. }
  (* the branch, left against right, at the left levels *)
  assert (Hψ : usub_ok (uext (k1 :: k2 :: nil) φ) L' (gL (brG 1 G0)))
    by exact (usub_ok_uext (k1 :: k2 :: nil) φ L' (gL G0) ltac:(repeat constructor; assumption) Hφ).
  pose proof (GS_pi EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB) as GS1.
  pose proof (VBr 1 ltac:(lia) _ _ Hψ _ _ _ GS1 G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst] in Y. rewrite !gs_cext in Y.
  rewrite (wkc_inst' 2 3 Γ0 (k1 :: k2 :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil) φ σ eq_refl eq_refl) in Y.
  rewrite (lvren_ush_uext' l1 2 (k1 :: k2 :: nil) φ eq_refl) in Y.
  (* the recursive calls, at the branch context's entries *)
  assert (Hwl1 : lwf L' (lvsubst l1 φ)) by (rewrite <- EL; exact (proj1 HrbL)).
  assert (HΔLA : [ G' ; ΔL ,, A @ k1 ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔL | exact HAD | rewrite EL; exact Hw1]).
  assert (HΔRA : [ G' ; ΔR ,, A' @ k1' ⊢[ lD ] ]) by exact (eqctx_wf_r (i := lD) eq_refl HΔA).
  assert (X1 : LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k1 ΔL (boxT A))
                 (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k1 ΔL (boxT A))
                 (recTL k1 ΔL A) (recTR k1' ΔR A')).
  { refine (LRtm_conv_r IHA (LRty_sym _)).
    exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw1 Q1 HΔL HΔ (box_rel HΔL Hw1 HA HA' EA) (box_rel HΔR Hw1' HA'R' HA'R' (ty_leq_refl _))). }
  assert (X2 : LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k2 (ΔL ,, A @ k1) (boxT B))
                 (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k2 (ΔL ,, A @ k1) (boxT B))
                 (recTL k2 (ΔL ,, A @ k1) B) (recTR k2' (ΔR ,, A' @ k1') B')).
  { refine (LRtm_conv_r IHB (LRty_sym _)).
    exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw2 Q2 HΔLA HΔA (box_rel HΔLA Hw2 HB HB' EB) (box_rel HΔRA Hw2' HB'R' HB'R' (ty_leq_refl _))). }
  match type of Y with VTm _ ?C _ _ _ _ => assert (SR1 : SubRelM G' C Θ (lext xsL e) (lext xsR e')) end.
  { apply SubRel_cons; [apply SubRel_cons; [exact He |] |].
    - rewrite (motT_wkb_inst' MT 2 3 0 (k1 :: k2 :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil) nil φ σ e e),
              (motT_wkb_inst' MT 2 3 0 (k1 :: k2 :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil) nil φ σ e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De | exact De'].
      inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NA). exact X1.
    - rewrite (motT_wkb_inst' MT 2 3 1 (k1 :: k2 :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil)
                 (recTL k1 ΔL A :: nil) φ σ e),
              (motT_wkb_inst' MT 2 3 1 (k1 :: k2 :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil)
                 (recTR k1' ΔR A' :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ]
                 | intros [|?n]; cbn [llk]; [first [exact (wf_tm_dnf Ha1) | exact (wf_tm_dnf Ha1')]
                                           | first [apply De | apply De']] ].
      inst_cbn. rewrite !subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NB)]. exact X2. }
  pose proof (Y _ _ _ SR1) as Z1. clear Y SR1.
  cbn [brRes] in Z1. unfold brLv in Z1. cbn [br_nu br_ar Nat.ltb Nat.leb] in Z1.
  rewrite (lvren_ush_uext' l1 2 (k1 :: k2 :: nil) φ eq_refl) in Z1.
  rewrite (motT_wkb_inst' MT 2 3 2 (k1 :: k2 :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil) xsL φ σ e),
          (motT_wkb_inst' MT 2 3 2 (k1 :: k2 :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil) xsR φ σ e') in Z1
    by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ]
             | apply lk_dnf_lext; [ try unfold xsL; try unfold xsR;
                                    repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                  | first [exact De | exact De']]].
  fold rL rR0 in Z1. inst_cbn_in Z1.
  rewrite !subst_lshift0_ty in Z1 by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NB)].
  (* the right-hand reduct, at its own levels *)
  assert (HψR : usub_ok (uext (k1' :: k2' :: nil) φ) L' (gL (brG 1 G0)))
    by exact (usub_ok_uext (k1' :: k2' :: nil) φ L' (gL G0) ltac:(repeat constructor; assumption) Hφ).
  pose proof (GS_pi EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R' HA'R'
                (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R' Hl1c)) (ty_leq_refl _) HB'R' HB'R'
                (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HB'R' Hl1c)) (ty_leq_refl _)) as GS2.
  pose proof (VBr' 1 ltac:(lia) _ _ HψR _ _ _ GS2 G' gwk_id (gwk_ok_id G')) as Y2; cbn [gwa] in Y2.
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst] in Y2. rewrite !gs_cext in Y2.
  rewrite (wkc_inst' 2 3 Γ0 (k1' :: k2' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: nil) φ σ' eq_refl eq_refl) in Y2.
  rewrite (lvren_ush_uext' l1' 2 (k1' :: k2' :: nil) φ eq_refl) in Y2.
  assert (Hl1'' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl1g : lequiv (gL G') (lvsubst l1 φ) (lvsubst l1' φ)) by (rewrite EL; exact Hl1).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1'') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1'') as X2r.
  match type of Y2 with VTm _ ?C _ _ _ _ => assert (SR2 : SubRelM G' C Θ (lext xsR e') (lext xsR e')) end.
  { apply SubRel_cons; [apply SubRel_cons; [exact He'r |] |].
    - rewrite (motT_wkb_inst' MT' 2 3 0 (k1' :: k2' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: nil) nil φ σ' e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
      inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NA'). exact X1r.
    - rewrite (motT_wkb_inst' MT' 2 3 1 (k1' :: k2' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: nil)
                 (recTR k1' ΔR A' :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ']
                 | intros [|?n]; cbn [llk]; [exact (wf_tm_dnf Ha1') | apply De'] ].
      inst_cbn. rewrite !subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NB')]. exact X2r. }
  pose proof (Y2 _ _ _ SR2) as Z2. clear Y2 SR2.
  cbn [brRes] in Z2. unfold brLv in Z2. cbn [br_nu br_ar Nat.ltb Nat.leb] in Z2.
  rewrite (lvren_ush_uext' l1' 2 (k1' :: k2' :: nil) φ eq_refl) in Z2.
  rewrite (motT_wkb_inst' MT' 2 3 2 (k1' :: k2' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: nil) xsR φ σ' e') in Z2
    by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ']
             | apply lk_dnf_lext; [ try unfold xsR;
                                    repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                  | exact De']].
  fold rR in Z2. inst_cbn_in Z2.
  rewrite !subst_lshift0_ty in Z2 by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NB')].
  (* the codes' typings *)
  assert (Hn : lC <> lV) by discriminate.
  assert (Q12 : lequiv L' (lmax k1 k2) (lmax k1' k2')) by (apply lequiv_max; assumption).
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tyPi k1 k2 A B @ lmax k1 k2 ]) by (apply wft_pi; rewrite ?EL; assumption).
  assert (HcL : [ G' ; ΔL ⊢[ lC ] tyPi k1 k2 A B @ kL ]) by (eapply wft_lconv; [exact HcL0 | rewrite EL; apply lequiv_sym, HkL]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyPi k1' k2' A' B' @ lmax k1' k2' ]) by (apply wft_pi; rewrite ?EL; assumption).
  assert (HcR : [ G' ; ΔR ⊢[ lC ] tyPi k1' k2' A' B' @ kR ]).
  { eapply wft_lconv; [exact HcR0 | rewrite EL; eapply lequiv_trans; [apply lequiv_sym, HkR | exact Q12]]. }
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyPi k1' k2' A' B' @ lmax k1 k2 ]).
  { eapply wft_lconv; [| rewrite EL; exact Q12]. refine (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0). }
  assert (Ec : ty_leq (tyPi k1 k2 A B) (tyPi k1' k2' A' B')) by (cbn; auto).
  assert (Hw12 : lwf L' (lmax k1 k2)) by (cbn; auto).
  assert (Hw12' : lwf L' (lmax k1' k2')) by (cbn; auto).
  pose proof (box_rel HΔL (lequiv_wf_r _ _ _ HkL) HcL HcL (ty_leq_refl _)) as BL.
  pose proof (box_rel HΔL Hw12 HcL0 HcL0 (ty_leq_refl _)) as B0.
  pose proof (box_rel HΔL Hw12 HcL0 HcRL Ec) as B0'.
  pose proof (box_rel HΔR (lequiv_wf_r _ _ _ HkR) HcR HcR (ty_leq_refl _)) as BR.
  pose proof (box_rel HΔR Hw12' HcR0 HcR0 (ty_leq_refl _)) as BR0.
  (* the types *)
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT l1 l1 HMT HMT (lequiv_refl _ _ Hwl1) Hφ VMTl VMTl VΓ G' σ σ Θ e e
                (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL (lequiv_wf_r _ _ _ HkL) (lequiv_sym _ _ _ HkL) HΔL
                (eqc_refl _ _ _ HΔL) BL B0) as T1.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
                Hw12 HkR HΔL HΔ B0' BR) as T2.
  assert (Hwl1' : lwf L' (lvsubst l1' φ)) by exact (lequiv_wf_r _ _ _ Hl1).
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT' MT' l1' l1' HMT' HMT' (lequiv_refl _ _ Hwl1') Hφ VMTr VMTr VΓ G' σ' σ' Θ e' e'
                (GSubRel_refl_r EP EM Hσ) He'r EL (lequiv_wf_r _ _ _ HkR)
                (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Q12) HΔR (eqc_refl _ _ _ HΔR) BR BR0) as T3.
  pose proof (LRty_lconv T3 Hl1g) as T3'.
  pose proof (LRtm_conv_r (LRtm_conv_l Z1 T1) T2) as W1.
  pose proof (LRtm_conv_r (LRtm_conv_l (LRtm_lconv Z2 Hl1g) T3') (LRty_sym T3')) as W2.
  assert (Eleq : tm_leq rR0 rR).
  { unfold rR0, rR. apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl |].
    apply (proj1 (proj2 leq_gsubst_all)); [intros; apply gobj_leq_refl |].
    apply (proj1 (proj2 leq_usubst_all)); [| apply tm_leq_refl].
    intros [|[|i]]; unfold uext; cbn; [exact E2 | exact E1 | apply leqv_refl]. }
  pose proof (LRtm_leq W1 W2 Eleq) as W.
  (* anti-reduction *)
  destruct (LRtm_escape W) as [HrL _]. destruct (LRtm_escape (LRtm_sym W)) as [HrR _].
  rewrite (@gm_layer_M EP EM EMl) in HrL, HrR.
  pose proof (tmred_elimT_beta HrbL (eq_ind_r (fun L => lwf L kL) (lequiv_wf_r _ _ _ HkL) EL) HΔL HcL HredL HrL) as R1.
  pose proof (tmred_elimT_beta HrbR (eq_ind_r (fun L => lwf L kR) (lequiv_wf_r _ _ _ HkR) EL) HΔR HcR HredR
                (wf_lconv _ _ _ _ _ _ _ HrR (lequiv_sym _ _ _ Hl1g))) as R2.
  pose proof (tmred_lconv _ _ _ _ _ R2 Hl1g) as R2'.
  rewrite <- (@gm_layer_M EP EM EMl) in R1, R2'.
  exact (LRtm_red W R1 R2').
Qed.


(** ** Universes *)

Lemma rec_T_U {ΔL ΔR kL kR k k'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc k) kL -> lequiv L' (lsuc k) kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyU k))) (motT (wrapMT MTR) kR ΔR (boxT (tyU k')))
    (recTL kL ΔL (tyU k)) (recTR kR ΔR (tyU k')).
Proof.
  intros HΔL HΔ HkL HkR Hw Hw' E.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (Hwl1 : lwf L' (lvsubst l1 φ)) by (rewrite <- EL; exact (proj1 HrbL)).
  assert (Hwl1' : lwf L' (lvsubst l1' φ)) by exact (lequiv_wf_r _ _ _ Hl1).
  assert (Hl1g : lequiv (gL G') (lvsubst l1 φ) (lvsubst l1' φ)) by (rewrite EL; exact Hl1).
  set (rL := ((usubst_tm (bs 2) (uext (k :: nil) φ))⦃gext_s (GCtx ΔL :: nil) σ⦄)[lext nil e]).
  set (rR := ((usubst_tm (bs' 2) (uext (k' :: nil) φ))⦃gext_s (GCtx ΔR :: nil) σ'⦄)[lext nil e']).
  set (rR0 := ((usubst_tm (bs' 2) (uext (k :: nil) φ))⦃gext_s (GCtx ΔR :: nil) σ'⦄)[lext nil e']).
  assert (HredL : redT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL (tyU k) = Some rL)
    by (apply redT_U_inst; first [exact (wf_tm_dnf (Hbs 2 ltac:(lia))) | exact Nσ | exact De | exact NΔL]).
  assert (HredR : redT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR (tyU k') = Some rR)
    by (apply redT_U_inst; first [exact (wf_tm_dnf (Hbs' 2 ltac:(lia))) | exact Nσ' | exact De' | exact NΔR]).
  (* left against right, at the left level *)
  assert (Hψ : usub_ok (uext (k :: nil) φ) L' (gL (brG 2 G0)))
    by exact (usub_ok_uext (k :: nil) φ L' (gL G0) ltac:(repeat constructor; assumption) Hφ).
  assert (GS1 : GSubRel G' (G_us (brG 2 G0) L' (uext (k :: nil) φ)) (gext_s (GCtx ΔL :: nil) σ)
                  (gext_s (GCtx ΔR :: nil) σ')).
  { rewrite (G_us_brG_uext 2 G0 L' φ (k :: nil) eq_refl). exact (GSubRel_ctx1 EP EM Hσ HΔL HΔ). }
  pose proof (VBr 2 ltac:(lia) _ _ Hψ _ _ _ GS1 G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar] in Y.
  rewrite (wkc_inst' 1 1 Γ0 (k :: nil) (GCtx ΔL :: nil) φ σ eq_refl eq_refl) in Y.
  pose proof (Y _ _ _ He) as Z1. clear Y.
  cbn [brRes] in Z1. unfold brLv in Z1. cbn [br_nu br_ar Nat.ltb Nat.leb] in Z1.
  rewrite (lvren_ush_uext' l1 1 (k :: nil) φ eq_refl) in Z1.
  change ((?T)[e]) with (T[lext nil e]) in Z1 at 1. change ((?T)[e']) with (T[lext nil e']) in Z1 at 1.
  rewrite (motT_wkb_inst' MT 1 1 0 (k :: nil) (GCtx ΔL :: nil) nil φ σ e (lext nil e)),
          (motT_wkb_inst' MT 1 1 0 (k :: nil) (GCtx ΔL :: nil) nil φ σ e' (lext nil e')) in Z1
    by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De | exact De'].
  fold rL rR0 in Z1. inst_cbn_in Z1.
  (* the right-hand reduct at its own level *)
  assert (HψR : usub_ok (uext (k' :: nil) φ) L' (gL (brG 2 G0)))
    by exact (usub_ok_uext (k' :: nil) φ L' (gL G0) ltac:(repeat constructor; assumption) Hφ).
  assert (GS2 : GSubRel G' (G_us (brG 2 G0) L' (uext (k' :: nil) φ)) (gext_s (GCtx ΔR :: nil) σ')
                  (gext_s (GCtx ΔR :: nil) σ')).
  { rewrite (G_us_brG_uext 2 G0 L' φ (k' :: nil) eq_refl).
    exact (GSubRel_ctx1 EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)). }
  pose proof (VBr' 2 ltac:(lia) _ _ HψR _ _ _ GS2 G' gwk_id (gwk_ok_id G')) as Y2; cbn [gwa] in Y2.
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar] in Y2.
  rewrite (wkc_inst' 1 1 Γ0 (k' :: nil) (GCtx ΔR :: nil) φ σ' eq_refl eq_refl) in Y2.
  pose proof (Y2 _ _ _ He'r) as Z2. clear Y2.
  cbn [brRes] in Z2. unfold brLv in Z2. cbn [br_nu br_ar Nat.ltb Nat.leb] in Z2.
  rewrite (lvren_ush_uext' l1' 1 (k' :: nil) φ eq_refl) in Z2.
  change ((?T)[e']) with (T[lext nil e']) in Z2.
  rewrite !(motT_wkb_inst' MT' 1 1 0 (k' :: nil) (GCtx ΔR :: nil) nil φ σ' e' (lext nil e')) in Z2
    by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
  fold rR in Z2. inst_cbn_in Z2.
  (* the codes *)
  assert (Hn : lC <> lV) by discriminate.
  assert (HUL : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> lequiv L' (lsuc j) j' -> [ G' ; Δ ⊢[ lC ] tyU j @ j' ]).
  { intros Δ j j' HΔ0 Hj Hjj. eapply wft_lconv; [apply wft_U; [exact Hn | exact HΔ0 | rewrite EL; exact Hj]
                                                | rewrite EL; apply lequiv_sym, Hjj]. }
  assert (Qs : lequiv L' (lsuc k) (lsuc k')) by (apply lequiv_suc, Q).
  assert (Hws : lwf L' (lsuc k)) by exact Hw. assert (Hws' : lwf L' (lsuc k')) by exact Hw'.
  pose proof (HUL _ _ _ HΔL Hw HkL) as HcL.
  pose proof (HUL _ _ _ HΔL Hw (lequiv_refl _ _ Hws)) as HcL0.
  pose proof (HUL _ _ _ HΔL Hw' (lequiv_sym _ _ _ Qs)) as HcRL.
  pose proof (HUL _ _ _ HΔR Hw' (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Qs) HkR)) as HcR.
  pose proof (HUL _ _ _ HΔR Hw' (lequiv_refl _ _ Hws')) as HcR0.
  pose proof (box_rel HΔL (lequiv_wf_r _ _ _ HkL) HcL HcL (ty_leq_refl _)) as BL.
  pose proof (box_rel HΔL Hws HcL0 HcL0 (ty_leq_refl _)) as B0.
  pose proof (box_rel HΔL Hws HcL0 HcRL E) as B0'.
  pose proof (box_rel HΔR (lequiv_wf_r _ _ _ HkR) HcR HcR (ty_leq_refl _)) as BR.
  pose proof (box_rel HΔR Hws' HcR0 HcR0 (ty_leq_refl _)) as BR0.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT l1 l1 HMT HMT (lequiv_refl _ _ Hwl1) Hφ VMTl VMTl VΓ G' σ σ Θ e e
                (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL (lequiv_wf_r _ _ _ HkL) (lequiv_sym _ _ _ HkL) HΔL
                (eqc_refl _ _ _ HΔL) BL B0) as T1.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
                Hws HkR HΔL HΔ B0' BR) as T2.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT' MT' l1' l1' HMT' HMT' (lequiv_refl _ _ Hwl1') Hφ VMTr VMTr VΓ G' σ' σ' Θ e' e'
                (GSubRel_refl_r EP EM Hσ) He'r EL (lequiv_wf_r _ _ _ HkR)
                (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Qs) HΔR (eqc_refl _ _ _ HΔR) BR BR0) as T3.
  pose proof (LRty_lconv T3 Hl1g) as T3'.
  pose proof (LRtm_conv_r (LRtm_conv_l Z1 T1) T2) as W1.
  pose proof (LRtm_conv_r (LRtm_conv_l (LRtm_lconv Z2 Hl1g) T3') (LRty_sym T3')) as W2.
  assert (Eleq : tm_leq rR0 rR).
  { unfold rR0, rR. apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl |].
    apply (proj1 (proj2 leq_gsubst_all)); [intros; apply gobj_leq_refl |].
    apply (proj1 (proj2 leq_usubst_all)); [| apply tm_leq_refl].
    intros [|i]; unfold uext; cbn; [exact E | apply leqv_refl]. }
  pose proof (LRtm_leq W1 W2 Eleq) as W.
  destruct (LRtm_escape W) as [HrL _]. destruct (LRtm_escape (LRtm_sym W)) as [HrR _].
  rewrite (@gm_layer_M EP EM EMl) in HrL, HrR.
  pose proof (tmred_elimT_beta HrbL (eq_ind_r (fun L => lwf L kL) (lequiv_wf_r _ _ _ HkL) EL) HΔL HcL HredL HrL) as R1.
  pose proof (tmred_elimT_beta HrbR (eq_ind_r (fun L => lwf L kR) (lequiv_wf_r _ _ _ HkR) EL) HΔR HcR HredR
                (wf_lconv _ _ _ _ _ _ _ HrR (lequiv_sym _ _ _ Hl1g))) as R2.
  pose proof (tmred_lconv _ _ _ _ _ R2 Hl1g) as R2'.
  rewrite <- (@gm_layer_M EP EM EMl) in R1, R2'.
  exact (LRtm_red W R1 R2').
Qed.

(** ** Decodings of codes *)

Local Notation rectL k Δ T c := (elimt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ T (boxt c)).
Local Notation rectR k Δ T c := (elimt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ T (boxt c)).

Lemma rec_T_El {ΔL ΔR kL kR k k' t t'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  [ G' ; ΔL ⊢[ lC ] t : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] t' : tyU k @ lsuc k ] -> tm_leq t t' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt t))
    (mott (wrapMt MtR) (lsuc k') ΔR (tyU k') (boxt t'))
    (rectL (lsuc k) ΔL (tyU k) t) (rectR (lsuc k') ΔR (tyU k') t') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyEl k t))) (motT (wrapMT MTR) kR ΔR (boxT (tyEl k' t')))
    (recTL kL ΔL (tyEl k t)) (recTR kR ΔR (tyEl k' t')).
Proof.
  intros HΔL HΔ HkL HkR Hw Hw' E Ht Ht' Et IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Hn : lC <> lV) by discriminate.
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (Qs : lequiv L' (lsuc k) (lsuc k')) by (apply lequiv_suc, Q).
  assert (Hwl1 : lwf L' (lvsubst l1 φ)) by (rewrite <- EL; exact (proj1 HrbL)).
  assert (Hwl1' : lwf L' (lvsubst l1' φ)) by exact (lequiv_wf_r _ _ _ Hl1).
  assert (Hl1g : lequiv (gL G') (lvsubst l1 φ) (lvsubst l1' φ)) by (rewrite EL; exact Hl1).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  (* the pieces *)
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Ht Ht' Et) Hl1c) as Htt.
  assert (HU : forall Δ j, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> [ G' ; Δ ⊢[ lD ] tyU j @ lsuc j ])
    by (intros; apply wft_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HUU : [ G' ; ΔL ⊢[ lD ] tyU k ≅ tyU k' @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q]).
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyU k @ lsuc k ]) by exact (ctxconv_tm HΔ (i := lC) eq_refl Ht').
  assert (Ht'R' : [ G' ; ΔR ⊢[ lC ] t' : tyU k' @ lsuc k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht'R | rewrite EL; apply lequiv_sym, Qs] |].
    apply eqty_U; [discriminate | exact HΔR | rewrite EL; apply lequiv_sym, Q]. }
  pose proof (wf_tm_dnf Ht) as Nt. pose proof (wf_tm_dnf Ht'R') as Nt'.
  destruct (LRtm_escape IHt) as [Ha _]. destruct (LRtm_escape (LRtm_sym IHt)) as [Ha' _].
  (* the reducts *)
  set (xsL := rectL (lsuc k) ΔL (tyU k) t :: nil). set (xsR := rectR (lsuc k') ΔR (tyU k') t' :: nil).
  set (rL := ((usubst_tm (bs 3) (uext (k :: nil) φ))⦃gext_s (GCtx ΔL :: GTm t :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 3) (uext (k' :: nil) φ))⦃gext_s (GCtx ΔR :: GTm t' :: nil) σ'⦄)[lext xsR e']).
  set (rR0 := ((usubst_tm (bs' 3) (uext (k :: nil) φ))⦃gext_s (GCtx ΔR :: GTm t' :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL (tyEl k t) = Some rL).
  { apply redT_El_inst; first [exact (wf_tm_dnf (Hbs 3 ltac:(lia))) | exact Nσ | exact De | exact NΔL
                              | exact Nt | exact (wf_tm_dnf Ha)]. }
  assert (HredR : redT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR (tyEl k' t') = Some rR).
  { apply redT_El_inst; first [exact (wf_tm_dnf (Hbs' 3 ltac:(lia))) | exact Nσ' | exact De' | exact NΔR
                              | exact Nt' | exact (wf_tm_dnf Ha')]. }
  (* the recursive call at the branch context's entry *)
  pose proof (box_rel_tm (HU _ _ HΔL Hw) Hw Ht Ht' Et) as Bt.
  pose proof (box_rel_tm (HU _ _ HΔR Hw') Hw' Ht'R' Ht'R' (tm_leq_refl _)) as Bt'.
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (X1 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt t))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))]))
                    (lsuc k) ΔL (tyU k) (boxt t))
                 (rectL (lsuc k) ΔL (tyU k) t) (rectR (lsuc k') ΔR (tyU k') t')).
  { refine (LRtm_conv_r IHt (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             (kL := lsuc k) (kR := lsuc k') Hw Qs HΔL HΔ HUU (HU _ _ HΔR Hw') Bt Bt'). }
  (* left against right, at the left level *)
  assert (Hψ : usub_ok (uext (k :: nil) φ) L' (gL (brG 3 G0)))
    by exact (usub_ok_uext (k :: nil) φ L' (gL G0) ltac:(repeat constructor; assumption) Hφ).
  pose proof (GS_El EP EM Hσ HΔL HΔ Ht Ht'R Htt Et) as GS1.
  pose proof (VBr 3 ltac:(lia) _ _ Hψ _ _ _ GS1 G' gwk_id (gwk_ok_id G')) as Y; cbn [gwa] in Y.
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst] in Y. rewrite !gs_cext in Y.
  rewrite (wkc_inst' 1 2 Γ0 (k :: nil) (GCtx ΔL :: GTm t :: nil) φ σ eq_refl eq_refl) in Y.
  rewrite (lvren_ush_uext' l2 1 (k :: nil) φ eq_refl) in Y.
  match type of Y with VTm _ ?C _ _ _ _ => assert (SR1 : SubRelM G' C Θ (lext xsL e) (lext xsR e')) end.
  { apply SubRel_cons; [exact He |].
    rewrite (mott_wkb_inst' Mt 1 2 0 (k :: nil) (GCtx ΔL :: GTm t :: nil) nil φ σ e e),
            (mott_wkb_inst' Mt 1 2 0 (k :: nil) (GCtx ΔL :: GTm t :: nil) nil φ σ e' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De | exact De'].
    inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt). exact X1. }
  pose proof (Y _ _ _ SR1) as Z1. clear Y SR1.
  cbn [brRes] in Z1. unfold brLv in Z1. cbn [br_nu br_ar Nat.ltb Nat.leb] in Z1.
  rewrite (lvren_ush_uext' l1 1 (k :: nil) φ eq_refl) in Z1.
  rewrite (motT_wkb_inst' MT 1 2 1 (k :: nil) (GCtx ΔL :: GTm t :: nil) xsL φ σ e),
          (motT_wkb_inst' MT 1 2 1 (k :: nil) (GCtx ΔL :: GTm t :: nil) xsR φ σ e') in Z1
    by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ]
             | apply lk_dnf_lext; [ try unfold xsL; try unfold xsR;
                                    repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                  | first [exact De | exact De']]].
  fold rL rR0 in Z1. inst_cbn_in Z1. rewrite !subst_lshift0 in Z1 by exact (dnftm_nftm _ Nt).
  (* the right-hand reduct at its own level *)
  assert (HψR : usub_ok (uext (k' :: nil) φ) L' (gL (brG 3 G0)))
    by exact (usub_ok_uext (k' :: nil) φ L' (gL G0) ltac:(repeat constructor; assumption) Hφ).
  assert (Ht'Rs : [ G' ; ΔR ⊢[ lD ] t' ≅ t' : tyU k' @ lsuc k' ])
    by exact (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R' Hl1c)).
  pose proof (GS_El EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Ht'R' Ht'R' Ht'Rs (tm_leq_refl _)) as GS2.
  pose proof (VBr' 3 ltac:(lia) _ _ HψR _ _ _ GS2 G' gwk_id (gwk_ok_id G')) as Y2; cbn [gwa] in Y2.
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst] in Y2. rewrite !gs_cext in Y2.
  rewrite (wkc_inst' 1 2 Γ0 (k' :: nil) (GCtx ΔR :: GTm t' :: nil) φ σ' eq_refl eq_refl) in Y2.
  rewrite (lvren_ush_uext' l2' 1 (k' :: nil) φ eq_refl) in Y2.
  assert (Hl2'' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2'') as X1r.
  match type of Y2 with VTm _ ?C _ _ _ _ => assert (SR2 : SubRelM G' C Θ (lext xsR e') (lext xsR e')) end.
  { apply SubRel_cons; [exact He'r |].
    rewrite (mott_wkb_inst' Mt' 1 2 0 (k' :: nil) (GCtx ΔR :: GTm t' :: nil) nil φ σ' e' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
    inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt'). exact X1r. }
  pose proof (Y2 _ _ _ SR2) as Z2. clear Y2 SR2.
  cbn [brRes] in Z2. unfold brLv in Z2. cbn [br_nu br_ar Nat.ltb Nat.leb] in Z2.
  rewrite (lvren_ush_uext' l1' 1 (k' :: nil) φ eq_refl) in Z2.
  rewrite (motT_wkb_inst' MT' 1 2 1 (k' :: nil) (GCtx ΔR :: GTm t' :: nil) xsR φ σ' e') in Z2
    by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ']
             | apply lk_dnf_lext; [ try unfold xsR;
                                    repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                  | exact De']].
  fold rR in Z2. inst_cbn_in Z2. rewrite !subst_lshift0 in Z2 by exact (dnftm_nftm _ Nt').
  (* the codes *)
  assert (HEl : forall Δ j j' u, lwf L' j -> [ G' ; Δ ⊢[ lC ] u : tyU j @ lsuc j ] -> lequiv L' j j' ->
                  [ G' ; Δ ⊢[ lC ] tyEl j u @ j' ]).
  { intros Δ j j' u Hj Hu Hjj. eapply wft_lconv; [apply wft_El; [exact Hn | rewrite EL; exact Hj | exact Hu]
                                                 | rewrite EL; apply lequiv_sym, Hjj]. }
  pose proof (HEl _ _ _ _ Hw Ht HkL) as HcL.
  pose proof (HEl _ _ _ _ Hw Ht (lequiv_refl _ _ Hw)) as HcL0.
  assert (Ht'L' : [ G' ; ΔL ⊢[ lC ] t' : tyU k' @ lsuc k' ]) by exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl Ht'R').
  pose proof (HEl _ _ _ _ Hw' Ht'L' (lequiv_sym _ _ _ Q)) as HcRL.
  pose proof (HEl _ _ _ _ Hw' Ht'R' (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkR)) as HcR.
  pose proof (HEl _ _ _ _ Hw' Ht'R' (lequiv_refl _ _ Hw')) as HcR0.
  assert (Ec : ty_leq (tyEl k t) (tyEl k' t')) by (cbn; auto).
  pose proof (box_rel HΔL (lequiv_wf_r _ _ _ HkL) HcL HcL (ty_leq_refl _)) as BL.
  pose proof (box_rel HΔL Hw HcL0 HcL0 (ty_leq_refl _)) as B0.
  pose proof (box_rel HΔL Hw HcL0 HcRL Ec) as B0'.
  pose proof (box_rel HΔR (lequiv_wf_r _ _ _ HkR) HcR HcR (ty_leq_refl _)) as BR.
  pose proof (box_rel HΔR Hw' HcR0 HcR0 (ty_leq_refl _)) as BR0.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT l1 l1 HMT HMT (lequiv_refl _ _ Hwl1) Hφ VMTl VMTl VΓ G' σ σ Θ e e
                (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL (lequiv_wf_r _ _ _ HkL) (lequiv_sym _ _ _ HkL) HΔL
                (eqc_refl _ _ _ HΔL) BL B0) as T1.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
                Hw HkR HΔL HΔ B0' BR) as T2.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT' MT' l1' l1' HMT' HMT' (lequiv_refl _ _ Hwl1') Hφ VMTr VMTr VΓ G' σ' σ' Θ e' e'
                (GSubRel_refl_r EP EM Hσ) He'r EL (lequiv_wf_r _ _ _ HkR)
                (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Q) HΔR (eqc_refl _ _ _ HΔR) BR BR0) as T3.
  pose proof (LRty_lconv T3 Hl1g) as T3'.
  pose proof (LRtm_conv_r (LRtm_conv_l Z1 T1) T2) as W1.
  pose proof (LRtm_conv_r (LRtm_conv_l (LRtm_lconv Z2 Hl1g) T3') (LRty_sym T3')) as W2.
  assert (Eleq : tm_leq rR0 rR).
  { unfold rR0, rR. apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl |].
    apply (proj1 (proj2 leq_gsubst_all)); [intros; apply gobj_leq_refl |].
    apply (proj1 (proj2 leq_usubst_all)); [| apply tm_leq_refl].
    intros [|i]; unfold uext; cbn; [exact E | apply leqv_refl]. }
  pose proof (LRtm_leq W1 W2 Eleq) as W.
  destruct (LRtm_escape W) as [HrL _]. destruct (LRtm_escape (LRtm_sym W)) as [HrR _].
  rewrite (@gm_layer_M EP EM EMl) in HrL, HrR.
  pose proof (tmred_elimT_beta HrbL (eq_ind_r (fun L => lwf L kL) (lequiv_wf_r _ _ _ HkL) EL) HΔL HcL HredL HrL) as R1.
  pose proof (tmred_elimT_beta HrbR (eq_ind_r (fun L => lwf L kR) (lequiv_wf_r _ _ _ HkR) EL) HΔR HcR HredR
                (wf_lconv _ _ _ _ _ _ _ HrR (lequiv_sym _ _ _ Hl1g))) as R2.
  pose proof (tmred_lconv _ _ _ _ _ R2 Hl1g) as R2'.
  rewrite <- (@gm_layer_M EP EM EMl) in R1, R2'.
  exact (LRtm_red W R1 R2').
Qed.

(** ** The term heads *)

(** Anti-reduction for a term head, from the related reducts. *)
Lemma rec_t_fin {ΔL ΔR kL kR TL TR cL cR rL rR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ; ΔR ⊢[ lD ] ] ->
  lwf L' kL -> lwf L' kR -> [ G' ; ΔL ⊢[ lD ] TL @ kL ] -> [ G' ; ΔR ⊢[ lD ] TR @ kR ] ->
  [ G' ; ΔL ⊢[ lC ] cL : TL @ kL ] -> [ G' ; ΔR ⊢[ lC ] cR : TR @ kR ] ->
  redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL cL = Some rL ->
  redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR cR = Some rR ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt cL)) (mott (wrapMt MtR) kR ΔR TR (boxt cR)) rL rR ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt cL)) (mott (wrapMt MtR) kR ΔR TR (boxt cR))
    (rectL kL ΔL TL cL) (rectR kR ΔR TR cR).
Proof.
  intros HΔL HΔR HkL HkR HTL HTR HcL HcR HredL HredR W.
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  destruct (LRtm_escape W) as [HrL _]. destruct (LRtm_escape (LRtm_sym W)) as [HrR _].
  rewrite (@gm_layer_M EP EM EMl) in HrL, HrR.
  pose proof (tmred_elimt_beta HrbL (eq_ind_r (fun L => lwf L kL) HkL EL) HΔL HTL HcL HredL HrL) as R1.
  pose proof (tmred_elimt_beta HrbR (eq_ind_r (fun L => lwf L kR) HkR EL) HΔR HTR HcR HredR
                (wf_lconv _ _ _ _ _ _ _ HrR (lequiv_sym _ _ _ Hl2g))) as R2.
  pose proof (tmred_lconv _ _ _ _ _ R2 Hl2g) as R2'.
  rewrite <- (@gm_layer_M EP EM EMl) in R1, R2'.
  exact (LRtm_red W R1 R2').
Qed.

Lemma rec_t_nat {ΔL ΔR kL kR TL TR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc lzero) kL -> lequiv L' (lsuc lzero) kR ->
  [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TL @ lsuc lzero ] -> [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TR @ lsuc lzero ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt tmNat)) (mott (wrapMt MtR) kR ΔR TR (boxt tmNat))
    (rectL kL ΔL TL tmNat) (rectR kR ΔR TR tmNat).
Proof.
  intros HΔL HΔ HkL HkR HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hn : lC <> lV) by discriminate.
  assert (Hw0 : lwf L' (lsuc lzero)) by exact I.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (HkLg : lequiv (gL G') (lsuc lzero) kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') (lsuc lzero) kR) by (rewrite EL; exact HkR).
  (* the index types *)
  assert (HU0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU lzero @ lsuc lzero ])
    by (intros; apply wft_U; [discriminate | assumption | exact I]).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | rewrite EL; apply lequiv_sym, HkL]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | rewrite EL; apply lequiv_sym, HkR]. }
  assert (HcN : forall Δ T k, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU lzero ≅ T @ lsuc lzero ] ->
                  lequiv L' (lsuc lzero) k -> [ G' ; Δ ⊢[ lC ] tmNat : T @ k ]).
  { intros Δ T k HΔ0 HT Hk. eapply wf_lconv; [| rewrite EL; apply lequiv_sym, Hk].
    eapply wf_conv; [apply wf_code_nat; [exact Hn | exact HΔ0] | apply eqty_sym, HT]. }
  pose proof (HcN _ _ _ HΔL HTL HkL) as HcL.
  pose proof (HcN _ _ _ HΔR (ctxconv_eqty HΔ (i := lD) eq_refl HTR) HkR) as HcR.
  pose proof (HcN _ _ _ HΔL (eqty_refl _ _ _ _ _ (HU0 _ HΔL)) (lequiv_refl _ _ Hw0)) as HcL0.
  pose proof (HcN _ _ _ HΔR (eqty_refl _ _ _ _ _ (HU0 _ HΔR)) (lequiv_refl _ _ Hw0)) as HcR0.
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm (HU0 _ HΔL) Hw0 HcL0 HcL0 (tm_leq_refl _)) as B0.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  pose proof (box_rel_tm (HU0 _ HΔR) Hw0 HcR0 HcR0 (tm_leq_refl _)) as BR0.
  (* the reducts *)
  set (rL := ((usubst_tm (bs 5) (uext nil φ))⦃gext_s (GCtx ΔL :: nil) σ⦄)[lext nil e]).
  set (rR := ((usubst_tm (bs' 5) (uext nil φ))⦃gext_s (GCtx ΔR :: nil) σ'⦄)[lext nil e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL tmNat = Some rL)
    by (apply redt_nat_inst; first [exact (wf_tm_dnf (Hbs 5 ltac:(lia))) | exact Nσ | exact De | exact NΔL]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR tmNat = Some rR)
    by (apply redt_nat_inst; first [exact (wf_tm_dnf (Hbs' 5 ltac:(lia))) | exact Nσ' | exact De' | exact NΔR]).
  refine (rec_t_fin HΔL HΔR HwL HwR HTLk HTRk HcL HcR HredL HredR _).
  (* the branch *)
  refine (br_core 5 nil nil (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil _ _ _ ltac:(lia) eq_refl eq_refl
            (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            (GS_ctx0 EP EM 5 nil eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 5 nil eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) _ _ _ _ _ _ _).
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar]. rewrite (wkc_inst' 0 1 Γ0 nil (GCtx ΔL :: nil) φ σ eq_refl eq_refl). exact He.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar]. rewrite (wkc_inst' 0 1 Γ0 nil (GCtx ΔR :: nil) φ σ' eq_refl eq_refl). exact He'r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 0 1 0 nil (GCtx ΔL :: nil) nil φ σ e (lext nil e))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De].
    inst_cbn.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) (lequiv_sym _ _ _ HkLg))
             (HU0 _ HΔL) BL B0).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 0 1 0 nil (GCtx ΔL :: nil) nil φ σ e' (lext nil e'))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De'].
    inst_cbn.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw0 HkR HΔL HΔ HTR HTRk B0 BR).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 0 1 0 nil (GCtx ΔR :: nil) nil φ σ' e' (lext nil e'))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
    inst_cbn.
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                          (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) (lequiv_refl _ _ Hw0)) HΔR (eqc_refl _ _ _ HΔR)
                          _ (HU0 _ HΔR) BR BR0) Hl2g).
    exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (ctxconv_eqty HΔ (i := lD) eq_refl HTR)) (lequiv_sym _ _ _ HkRg)).
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 0 nil φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 0 nil φ eq_refl). exact Hl2g.
Qed.

Lemma rec_t_zero {ΔL ΔR kL kR TL TR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lzero) kL -> lequiv L' (lzero) kR ->
  [ G' ; ΔL ⊢[ lD ] tyNat ≅ TL @ lzero ] -> [ G' ; ΔL ⊢[ lD ] tyNat ≅ TR @ lzero ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt zero)) (mott (wrapMt MtR) kR ΔR TR (boxt zero))
    (rectL kL ΔL TL zero) (rectR kR ΔR TR zero).
Proof.
  intros HΔL HΔ HkL HkR HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hn : lC <> lV) by discriminate.
  assert (Hw0 : lwf L' (lzero)) by exact I.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (HkLg : lequiv (gL G') (lzero) kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') (lzero) kR) by (rewrite EL; exact HkR).
  (* the index types *)
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | rewrite EL; apply lequiv_sym, HkL]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | rewrite EL; apply lequiv_sym, HkR]. }
  assert (HcN : forall Δ T k, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat ≅ T @ lzero ] ->
                  lequiv L' (lzero) k -> [ G' ; Δ ⊢[ lC ] zero : T @ k ]).
  { intros Δ T k HΔ0 HT Hk. eapply wf_lconv; [| rewrite EL; apply lequiv_sym, Hk].
    eapply wf_conv; [apply wf_zero; [exact Hn | exact HΔ0] | apply eqty_sym, HT]. }
  pose proof (HcN _ _ _ HΔL HTL HkL) as HcL.
  pose proof (HcN _ _ _ HΔR (ctxconv_eqty HΔ (i := lD) eq_refl HTR) HkR) as HcR.
  pose proof (HcN _ _ _ HΔL (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) (lequiv_refl _ _ Hw0)) as HcL0.
  pose proof (HcN _ _ _ HΔR (eqty_refl _ _ _ _ _ (HN0 _ HΔR)) (lequiv_refl _ _ Hw0)) as HcR0.
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm (HN0 _ HΔL) Hw0 HcL0 HcL0 (tm_leq_refl _)) as B0.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  pose proof (box_rel_tm (HN0 _ HΔR) Hw0 HcR0 HcR0 (tm_leq_refl _)) as BR0.
  (* the reducts *)
  set (rL := ((usubst_tm (bs 8) (uext nil φ))⦃gext_s (GCtx ΔL :: nil) σ⦄)[lext nil e]).
  set (rR := ((usubst_tm (bs' 8) (uext nil φ))⦃gext_s (GCtx ΔR :: nil) σ'⦄)[lext nil e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL zero = Some rL)
    by (apply redt_zero_inst; first [exact (wf_tm_dnf (Hbs 8 ltac:(lia))) | exact Nσ | exact De | exact NΔL]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR zero = Some rR)
    by (apply redt_zero_inst; first [exact (wf_tm_dnf (Hbs' 8 ltac:(lia))) | exact Nσ' | exact De' | exact NΔR]).
  refine (rec_t_fin HΔL HΔR HwL HwR HTLk HTRk HcL HcR HredL HredR _).
  (* the branch *)
  refine (br_core 8 nil nil (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil _ _ _ ltac:(lia) eq_refl eq_refl
            (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            (GS_ctx0 EP EM 8 nil eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 8 nil eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) _ _ _ _ _ _ _).
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar]. rewrite (wkc_inst' 0 1 Γ0 nil (GCtx ΔL :: nil) φ σ eq_refl eq_refl). exact He.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar]. rewrite (wkc_inst' 0 1 Γ0 nil (GCtx ΔR :: nil) φ σ' eq_refl eq_refl). exact He'r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 0 1 0 nil (GCtx ΔL :: nil) nil φ σ e (lext nil e))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De].
    inst_cbn.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) (lequiv_sym _ _ _ HkLg))
             (HN0 _ HΔL) BL B0).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 0 1 0 nil (GCtx ΔL :: nil) nil φ σ e' (lext nil e'))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De'].
    inst_cbn.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw0 HkR HΔL HΔ HTR HTRk B0 BR).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 0 1 0 nil (GCtx ΔR :: nil) nil φ σ' e' (lext nil e'))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
    inst_cbn.
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                          (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) (lequiv_refl _ _ Hw0)) HΔR (eqc_refl _ _ _ HΔR)
                          _ (HN0 _ HΔR) BR BR0) Hl2g).
    exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (ctxconv_eqty HΔ (i := lD) eq_refl HTR)) (lequiv_sym _ _ _ HkRg)).
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 0 nil φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 0 nil φ eq_refl). exact Hl2g.
Qed.

Lemma rec_t_U {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lsuc j)) kL -> lequiv L' (lsuc (lsuc j)) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lsuc j) ≅ TL @ lsuc (lsuc j) ] -> [ G' ; ΔL ⊢[ lD ] tyU (lsuc j) ≅ TR @ lsuc (lsuc j) ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmU j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmU j')))
    (rectL kL ΔL TL (tmU j)) (rectR kR ΔR TR (tmU j')).
Proof.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hn : lC <> lV) by discriminate.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q2 : lequiv L' (lsuc (lsuc j)) (lsuc (lsuc j'))) by (do 2 apply lequiv_suc; exact Q).
  assert (Hw0 : lwf L' (lsuc (lsuc j))) by exact Hj. assert (Hw0' : lwf L' (lsuc (lsuc j'))) by exact Hj'.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (HkLg : lequiv (gL G') (lsuc (lsuc j)) kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') (lsuc (lsuc j)) kR) by (rewrite EL; exact HkR).
  assert (HU : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lD ] tyU (lsuc i) @ lsuc (lsuc i) ])
    by (intros; apply wft_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU (lsuc j) ≅ tyU (lsuc j') @ lsuc (lsuc j) ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; apply lequiv_suc, Q]).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  (* the codes *)
  assert (HcU : forall Δ i T k, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lD ] tyU (lsuc i) ≅ T @ lsuc (lsuc i) ] ->
                  lequiv L' (lsuc (lsuc i)) k -> [ G' ; Δ ⊢[ lC ] tmU i : T @ k ]).
  { intros Δ i T k HΔ0 Hi HT Hk. eapply wf_lconv; [| rewrite EL; apply lequiv_sym, Hk].
    eapply wf_conv; [apply wf_code_U; [exact Hn | exact HΔ0 | rewrite EL; exact Hi] | apply eqty_sym, HT]. }
  pose proof (HcU _ _ _ _ HΔL Hj HTL HkL) as HcL.
  assert (HTRR : [ G' ; ΔR ⊢[ lD ] tyU (lsuc j') ≅ TR @ lsuc (lsuc j') ]).
  { eapply eqty_lconv; [eapply eqty_trans; [apply eqty_sym, (HUU _ HΔR) | exact (ctxconv_eqty HΔ (i := lD) eq_refl HTR)]
                       | rewrite EL; apply lequiv_sym, Q2]. }
  pose proof (HcU _ _ _ _ HΔR Hj' HTRR (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q2) HkR)) as HcR.
  pose proof (HcU _ _ _ _ HΔL Hj (eqty_refl _ _ _ _ _ (HU _ _ HΔL Hj)) (lequiv_refl _ _ Hw0)) as HcL0.
  pose proof (HcU _ _ _ _ HΔL Hj' (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (HUU _ HΔL))
                                    ltac:(rewrite EL; apply lequiv_sym, Q2)) (lequiv_sym _ _ _ Q2)) as HcRL.
  pose proof (HcU _ _ _ _ HΔR Hj' (eqty_refl _ _ _ _ _ (HU _ _ HΔR Hj')) (lequiv_refl _ _ Hw0')) as HcR0.
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm (HU _ _ HΔL Hj) Hw0 HcL0 HcL0 (tm_leq_refl _)) as B0.
  pose proof (box_rel_tm (HU _ _ HΔL Hj) Hw0 HcL0 HcRL E) as B0'.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  pose proof (box_rel_tm (HU _ _ HΔR Hj') Hw0' HcR0 HcR0 (tm_leq_refl _)) as BR0.
  (* the reducts *)
  set (rL := ((usubst_tm (bs 7) (uext (j :: nil) φ))⦃gext_s (GCtx ΔL :: nil) σ⦄)[lext nil e]).
  set (rR := ((usubst_tm (bs' 7) (uext (j' :: nil) φ))⦃gext_s (GCtx ΔR :: nil) σ'⦄)[lext nil e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL (tmU j) = Some rL)
    by (apply redt_U_inst; first [exact (wf_tm_dnf (Hbs 7 ltac:(lia))) | exact Nσ | exact De | exact NΔL]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR (tmU j') = Some rR)
    by (apply redt_U_inst; first [exact (wf_tm_dnf (Hbs' 7 ltac:(lia))) | exact Nσ' | exact De' | exact NΔR]).
  refine (rec_t_fin HΔL HΔR HwL HwR HTLk HTRk HcL HcR HredL HredR _).
  refine (br_core 7 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil _ _ _ ltac:(lia) eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption) _
            (GS_ctx0 EP EM 7 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 7 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) _ _ _ _ _ _ _).
  - intros [|i]; unfold uext; cbn; [exact E | apply leqv_refl].
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar].
    rewrite (wkc_inst' 1 1 Γ0 (j :: nil) (GCtx ΔL :: nil) φ σ eq_refl eq_refl). exact He.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar].
    rewrite (wkc_inst' 1 1 Γ0 (j' :: nil) (GCtx ΔR :: nil) φ σ' eq_refl eq_refl). exact He'r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 1 1 0 (j :: nil) (GCtx ΔL :: nil) nil φ σ e (lext nil e))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De].
    inst_cbn.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) (lequiv_sym _ _ _ HkLg))
             (HU _ _ HΔL Hj) BL B0).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 1 1 0 (j :: nil) (GCtx ΔL :: nil) nil φ σ e' (lext nil e'))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De'].
    inst_cbn.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw0 HkR HΔL HΔ HTR HTRk B0' BR).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 1 1 0 (j' :: nil) (GCtx ΔR :: nil) nil φ σ' e' (lext nil e'))
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
    inst_cbn.
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                          (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Q2) HΔR (eqc_refl _ _ _ HΔR)
                          _ (HU _ _ HΔR Hj') BR BR0) Hl2g).
    eapply eqty_lconv; [apply eqty_sym, HTRR |]. rewrite EL; eapply lequiv_trans; [apply lequiv_sym, HkR | exact Q2].
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 1 (j :: nil) φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 1 (j' :: nil) φ eq_refl). exact Hl2g.
Qed.

Lemma rec_t_succ {ΔL ΔR kL kR TL TR t t'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' lzero kL -> lequiv L' lzero kR ->
  [ G' ; ΔL ⊢[ lD ] tyNat ≅ TL @ lzero ] -> [ G' ; ΔL ⊢[ lD ] tyNat ≅ TR @ lzero ] ->
  [ G' ; ΔL ⊢[ lC ] t : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] t' : tyNat @ lzero ] -> tm_leq t t' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt t)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt t'))
    (rectL lzero ΔL tyNat t) (rectR lzero ΔR tyNat t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (succ t))) (mott (wrapMt MtR) kR ΔR TR (boxt (succ t')))
    (rectL kL ΔL TL (succ t)) (rectR kR ΔR TR (succ t')).
Proof.
  intros HΔL HΔ HkL HkR HTL HTR Ht Ht' Et IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Hw0 : lwf L' lzero) by exact I.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HkLg : lequiv (gL G') lzero kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') lzero kR) by (rewrite EL; exact HkR).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  (* the codes *)
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Ht Ht' Et) Hl1c) as Htt.
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyNat @ lzero ]) by exact (ctxconv_tm HΔ (i := lC) eq_refl Ht').
  pose proof (wf_tm_dnf Ht) as Nt. pose proof (wf_tm_dnf Ht'R) as Nt'.
  assert (HcS : forall Δ T k u, [ G' ; Δ ⊢[ lC ] u : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lD ] tyNat ≅ T @ lzero ] ->
                  lequiv L' lzero k -> [ G' ; Δ ⊢[ lC ] succ u : T @ k ]).
  { intros Δ T k u Hu HT Hk. eapply wf_lconv; [| rewrite EL; apply lequiv_sym, Hk].
    eapply wf_conv; [apply wf_succ; [exact Hn | exact Hu] | apply eqty_sym, HT]. }
  pose proof (HcS _ _ _ _ Ht HTL HkL) as HcL.
  pose proof (HcS _ _ _ _ Ht'R (ctxconv_eqty HΔ (i := lD) eq_refl HTR) HkR) as HcR.
  pose proof (HcS _ _ _ _ Ht (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) (lequiv_refl _ _ Hw0)) as HcL0.
  pose proof (HcS _ _ _ _ Ht' (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) (lequiv_refl _ _ Hw0)) as HcRL.
  pose proof (HcS _ _ _ _ Ht'R (eqty_refl _ _ _ _ _ (HN0 _ HΔR)) (lequiv_refl _ _ Hw0)) as HcR0.
  assert (Es : tm_leq (succ t) (succ t')) by exact Et.
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm (HN0 _ HΔL) Hw0 HcL0 HcL0 (tm_leq_refl _)) as B0.
  pose proof (box_rel_tm (HN0 _ HΔL) Hw0 HcL0 HcRL Es) as B0'.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  pose proof (box_rel_tm (HN0 _ HΔR) Hw0 HcR0 HcR0 (tm_leq_refl _)) as BR0.
  (* the recursive call *)
  destruct (LRtm_escape IHt) as [Ha _]. destruct (LRtm_escape (LRtm_sym IHt)) as [Ha' _].
  assert (X1 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt t))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) lzero ΔL tyNat (boxt t))
                 (rectL lzero ΔL tyNat t) (rectR lzero ΔR tyNat t')).
  { refine (LRtm_conv_r IHt (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw0 (lequiv_refl _ _ Hw0) HΔL HΔ (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) (HN0 _ HΔR)
             (box_rel_tm (HN0 _ HΔL) Hw0 Ht Ht' Et) (box_rel_tm (HN0 _ HΔR) Hw0 Ht'R Ht'R (tm_leq_refl _))). }
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X1r.
  (* the reducts *)
  set (xsL := rectL lzero ΔL tyNat t :: nil). set (xsR := rectR lzero ΔR tyNat t' :: nil).
  set (rL := ((usubst_tm (bs 9) (uext nil φ))⦃gext_s (GCtx ΔL :: GTm t :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 9) (uext nil φ))⦃gext_s (GCtx ΔR :: GTm t' :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL (succ t) = Some rL)
    by (apply redt_succ_inst; first [exact (wf_tm_dnf (Hbs 9 ltac:(lia))) | exact Nσ | exact De | exact NΔL
                                    | exact Nt | exact (wf_tm_dnf Ha)]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR (succ t') = Some rR)
    by (apply redt_succ_inst; first [exact (wf_tm_dnf (Hbs' 9 ltac:(lia))) | exact Nσ' | exact De' | exact NΔR
                                    | exact Nt' | exact (wf_tm_dnf Ha')]).
  refine (rec_t_fin HΔL HΔR HwL HwR HTLk HTRk HcL HcR HredL HredR _).
  refine (br_core 9 nil nil (GCtx ΔL :: GTm t :: nil) (GCtx ΔR :: GTm t' :: nil) xsL xsR _ _ _ ltac:(lia) eq_refl eq_refl
            (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            (GS_succ EP EM Hσ HΔL HΔ Ht Ht'R Htt Et)
            (GS_succ EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Ht'R Ht'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 0 2 Γ0 nil (GCtx ΔL :: GTm t :: nil) φ σ eq_refl eq_refl).
    rewrite (lvren_ush_uext' l2 0 nil φ eq_refl).
    apply SubRel_cons; [exact He |].
    rewrite (mott_wkb_inst' Mt 0 2 0 nil (GCtx ΔL :: GTm t :: nil) nil φ σ e e),
            (mott_wkb_inst' Mt 0 2 0 nil (GCtx ΔL :: GTm t :: nil) nil φ σ e' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De | exact De'].
    inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt). exact X1.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 0 2 Γ0 nil (GCtx ΔR :: GTm t' :: nil) φ σ' eq_refl eq_refl).
    rewrite (lvren_ush_uext' l2' 0 nil φ eq_refl).
    apply SubRel_cons; [exact He'r |].
    rewrite (mott_wkb_inst' Mt' 0 2 0 nil (GCtx ΔR :: GTm t' :: nil) nil φ σ' e' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
    inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt'). exact X1r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 0 2 1 nil (GCtx ΔL :: GTm t :: nil) xsL φ σ e)
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ]
               | apply lk_dnf_lext; [ unfold xsL; repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                    | exact De]].
    inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) (lequiv_sym _ _ _ HkLg)) (HN0 _ HΔL) BL B0).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 0 2 1 nil (GCtx ΔL :: GTm t :: nil) xsR φ σ e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ]
               | apply lk_dnf_lext; [ unfold xsR; repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                    | exact De']].
    inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw0 HkR HΔL HΔ HTR HTRk B0' BR).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 0 2 1 nil (GCtx ΔR :: GTm t' :: nil) xsR φ σ' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ']
               | apply lk_dnf_lext; [ unfold xsR; repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                    | exact De']].
    inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt').
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR (lequiv_sym _ _ _ HkR)
                          HΔR (eqc_refl _ _ _ HΔR) _ (HN0 _ HΔR) BR BR0) Hl2g).
    exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (ctxconv_eqty HΔ (i := lD) eq_refl HTR)) (lequiv_sym _ _ _ HkRg)).
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 0 nil φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 0 nil φ eq_refl). exact Hl2g.
Qed.

Lemma rec_t_pi {ΔL ΔR kL kR TL TR k k' k1 k1' s0 t0 s1 t1} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lmax k k')) kL -> lequiv L' (lsuc (lmax k k')) kR ->
  lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TL @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TR @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lC ] s0 : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s1 : tyU k @ lsuc k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lC ] t0 : tyU k' @ lsuc k' ] ->
  [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> tm_leq t0 t1 ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s1))
    (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') (boxt t0))
    (mott (wrapMt MtR) (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') (boxt t1))
    (rectL (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') t0) (rectR (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') t1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmPi k k' s0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmPi k1 k1' s1 t1)))
    (rectL kL ΔL TL (tmPi k k' s0 t0)) (rectR kR ΔR TR (tmPi k1 k1' s1 t1)).
Proof.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR Hs Hs' Es Ht Ht' Et IHs IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qms : lequiv L' (lsuc (lmax k k')) (lsuc (lmax k1 k1'))) by (apply lequiv_suc, Qm).
  assert (Hwm : lwf L' (lsuc (lmax k k'))) by (cbn; auto). assert (Hwm1 : lwf L' (lsuc (lmax k1 k1'))) by (cbn; auto).
  assert (Hwm0 : lwf L' (lmax k k')) by (cbn; auto). assert (Hwm10 : lwf L' (lmax k1 k1')) by (cbn; auto).
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HkLg : lequiv (gL G') (lsuc (lmax k k')) kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') (lsuc (lmax k k')) kR) by (rewrite EL; exact HkR).
  assert (HU : forall Δ j, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> [ G' ; Δ ⊢[ lD ] tyU j @ lsuc j ])
    by (intros; apply wft_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  (* the pieces *)
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Hs Hs' Es) Hl1c) as Hss.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Ht Ht' Et) Hl1c) as Htt.
  pose proof (lift_tm (j := lD) Hs Hl1c) as HsD.
  assert (HElL : [ G' ; ΔL ⊢[ lD ] tyEl k s0 @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact HsD]).
  assert (HΔLE : [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔL | exact HElL | rewrite EL; exact Hw]).
  assert (CE : [ G' ⊢[ lD ] ΔL ,, tyEl k s0 @ k ≅ ΔR ,, tyEl k s1 @ k ]).
  { apply eqc_ext; [exact HΔ | exact HElL | apply eqty_El; [discriminate | rewrite EL; apply lequiv_refl, Hw | exact Hss]
                   | rewrite EL; apply lequiv_refl, Hw]. }
  assert (CE1 : [ G' ⊢[ lD ] ΔL ,, tyEl k s0 @ k ≅ ΔR ,, tyEl k1 s1 @ k1 ]).
  { apply eqc_ext; [exact HΔ | exact HElL | apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss]
                   | rewrite EL; exact Q]. }
  assert (CEL : [ G' ⊢[ lD ] ΔL ,, tyEl k s0 @ k ≅ ΔL ,, tyEl k1 s1 @ k1 ]).
  { apply eqc_ext; [apply eqc_refl, HΔL | exact HElL | apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss]
                   | rewrite EL; exact Q]. }
  pose proof (eqctx_wf_r (i := lD) eq_refl CE1) as HΔRE1.
  assert (Hs'R : [ G' ; ΔR ⊢[ lC ] s1 : tyU k @ lsuc k ]) by exact (ctxconv_tm HΔ (i := lC) eq_refl Hs').
  assert (HsU : forall Δ u, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lC ] u : tyU k @ lsuc k ] -> [ G' ; Δ ⊢[ lC ] u : tyU k1 @ lsuc k1 ]).
  { intros Δ u HΔ0 Hu. eapply wf_conv; [eapply wf_lconv; [exact Hu | rewrite EL; apply lequiv_suc, lequiv_sym, Q] |].
    apply HUU; [exact HΔ0 | apply lequiv_sym, Q]. }
  pose proof (HsU _ _ HΔR Hs'R) as Hs'R1. pose proof (HsU _ _ HΔL Hs') as Hs'L1.
  assert (HtU : forall Δ u, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lC ] u : tyU k' @ lsuc k' ] -> [ G' ; Δ ⊢[ lC ] u : tyU k1' @ lsuc k1' ]).
  { intros Δ u HΔ0 Hu. eapply wf_conv; [eapply wf_lconv; [exact Hu | rewrite EL; apply lequiv_suc, lequiv_sym, Q'] |].
    apply HUU; [exact HΔ0 | apply lequiv_sym, Q']. }
  assert (Ht'R : [ G' ; ΔR ,, tyEl k s1 @ k ⊢[ lC ] t1 : tyU k' @ lsuc k' ]) by exact (ctxconv_tm CE (i := lC) eq_refl Ht').
  pose proof (HtU _ _ HΔRE1 (ctxconv_tm CE1 (i := lC) eq_refl Ht')) as Ht'R1.
  pose proof (HtU _ _ (eqctx_wf_r (i := lD) eq_refl CEL) (ctxconv_tm CEL (i := lC) eq_refl Ht')) as Ht'L1.
  pose proof (wf_tm_dnf Hs) as Ns. pose proof (wf_tm_dnf Hs'R) as Ns'. pose proof (wf_tm_dnf Ht) as Nt. pose proof (wf_tm_dnf Ht'R) as Nt'.
  (* the codes *)
  assert (HcP : forall Δ T j j' u v kk, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> lwf L' j' ->
     [ G' ; Δ ⊢[ lC ] u : tyU j @ lsuc j ] -> [ G' ; Δ ,, tyEl j u @ j ⊢[ lC ] v : tyU j' @ lsuc j' ] ->
     [ G' ; Δ ⊢[ lD ] tyU (lmax j j') ≅ T @ lsuc (lmax j j') ] -> lequiv L' (lsuc (lmax j j')) kk ->
     [ G' ; Δ ⊢[ lC ] tmPi j j' u v : T @ kk ]).
  { intros Δ T j j' u v kk HΔ0 Hj Hj' Hu Hv HT Hkk. eapply wf_lconv; [| rewrite EL; apply lequiv_sym, Hkk].
    eapply wf_conv; [apply wf_code_pi; [exact Hn | rewrite EL; exact Hj | rewrite EL; exact Hj' | exact Hu | exact Hv]
                    | apply eqty_sym, HT]. }
  assert (HUm : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU (lmax k k') ≅ tyU (lmax k1 k1') @ lsuc (lmax k k') ])
    by (intros; apply HUU; [assumption | exact Qm]).
  pose proof (HcP _ _ _ _ _ _ _ HΔL Hw Hw' Hs Ht HTL HkL) as HcL.
  pose proof (HcP _ _ _ _ _ _ _ HΔL Hw Hw' Hs Ht (eqty_refl _ _ _ _ _ (HU _ _ HΔL Hwm0)) (lequiv_refl _ _ Hwm)) as HcL0.
  pose proof (HcP _ _ _ _ _ _ _ HΔL Hw1 Hw1' Hs'L1 Ht'L1
                (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (HUm _ HΔL)) ltac:(rewrite EL; apply lequiv_suc, lequiv_sym, Qm))
                (lequiv_sym _ _ _ Qms)) as HcRL.
  assert (HTRR : [ G' ; ΔR ⊢[ lD ] tyU (lmax k1 k1') ≅ TR @ lsuc (lmax k1 k1') ]).
  { eapply eqty_lconv; [eapply eqty_trans; [apply eqty_sym, (HUm _ HΔR) | exact (ctxconv_eqty HΔ (i := lD) eq_refl HTR)]
                       | rewrite EL; apply lequiv_suc, lequiv_sym, Qm]. }
  pose proof (HcP _ _ _ _ _ _ _ HΔR Hw1 Hw1' Hs'R1 Ht'R1 HTRR (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Qms) HkR)) as HcR.
  pose proof (HcP _ _ _ _ _ _ _ HΔR Hw1 Hw1' Hs'R1 Ht'R1 (eqty_refl _ _ _ _ _ (HU _ _ HΔR Hwm10)) (lequiv_refl _ _ Hwm1)) as HcR0.
  assert (Ec : tm_leq (tmPi k k' s0 t0) (tmPi k1 k1' s1 t1)) by (cbn; auto).
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm (HU _ _ HΔL Hwm0) Hwm HcL0 HcL0 (tm_leq_refl _)) as B0.
  pose proof (box_rel_tm (HU _ _ HΔL Hwm0) Hwm HcL0 HcRL Ec) as B0'.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  pose proof (box_rel_tm (HU _ _ HΔR Hwm10) Hwm1 HcR0 HcR0 (tm_leq_refl _)) as BR0.
  (* the recursive calls *)
  destruct (LRtm_escape IHs) as [Ha1 _]. destruct (LRtm_escape (LRtm_sym IHs)) as [Ha1' _].
  destruct (LRtm_escape IHt) as [Ha2 _]. destruct (LRtm_escape (LRtm_sym IHt)) as [Ha2' _].
  assert (X1 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) (lsuc k) ΔL (tyU k) (boxt s0))
                 (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1)).
  { refine (LRtm_conv_r IHs (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             (kL := lsuc k) (kR := lsuc k1) Hw (lequiv_suc _ _ _ Q) HΔL HΔ (HUU _ _ _ HΔL Q) (HU _ _ HΔR Hw1)
             (box_rel_tm (HU _ _ HΔL Hw) Hw Hs Hs' Es) (box_rel_tm (HU _ _ HΔR Hw1) Hw1 Hs'R1 Hs'R1 (tm_leq_refl _))). }
  assert (X2 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') (boxt t0))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))]))
                    (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') (boxt t0))
                 (rectL (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') t0) (rectR (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') t1)).
  { refine (LRtm_conv_r IHt (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             (kL := lsuc k') (kR := lsuc k1') Hw' (lequiv_suc _ _ _ Q') HΔLE CE1 (HUU _ _ _ HΔLE Q') (HU _ _ HΔRE1 Hw1')
             (box_rel_tm (HU _ _ HΔLE Hw') Hw' Ht Ht' Et) (box_rel_tm (HU _ _ HΔRE1 Hw1') Hw1' Ht'R1 Ht'R1 (tm_leq_refl _))). }
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r.
  (* the reducts *)
  set (xsL := rectL (lsuc k) ΔL (tyU k) s0 :: rectL (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') t0 :: nil).
  set (xsR := rectR (lsuc k1) ΔR (tyU k1) s1 :: rectR (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') t1 :: nil).
  set (rL := ((usubst_tm (bs 6) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx ΔL :: GTm s0 :: GTm t0 :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 6) (uext (k1 :: k1' :: nil) φ))⦃gext_s (GCtx ΔR :: GTm s1 :: GTm t1 :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL (tmPi k k' s0 t0) = Some rL)
    by (apply redt_pi_inst; first [exact (wf_tm_dnf (Hbs 6 ltac:(lia))) | exact Nσ | exact De | exact NΔL
                                  | exact Ns | exact Nt | exact (wf_tm_dnf Ha1) | exact (wf_tm_dnf Ha2)]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR (tmPi k1 k1' s1 t1) = Some rR)
    by (apply redt_pi_inst; first [exact (wf_tm_dnf (Hbs' 6 ltac:(lia))) | exact Nσ' | exact De' | exact NΔR
                                  | exact Ns' | exact Nt' | exact (wf_tm_dnf Ha1') | exact (wf_tm_dnf Ha2')]).
  refine (rec_t_fin HΔL HΔR HwL HwR HTLk HTRk HcL HcR HredL HredR _).
  refine (br_core 6 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil)
            (GCtx ΔR :: GTm s1 :: GTm t1 :: nil) xsL xsR _ _ _ ltac:(lia) eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption) _
            (GS_pi' EP EM Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et)
            (GS_pi' EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hs'R1 Hs'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _) Ht'R1 Ht'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - intros [|[|i]]; unfold uext; cbn; [exact E' | exact E | apply leqv_refl].
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 2 3 Γ0 (k :: k' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil) φ σ eq_refl eq_refl).
    rewrite (lvren_ush_uext' l2 2 (k :: k' :: nil) φ eq_refl).
    apply SubRel_cons; [apply SubRel_cons; [exact He |] |].
    + rewrite (mott_wkb_inst' Mt 2 3 0 (k :: k' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil) nil φ σ e e),
              (mott_wkb_inst' Mt 2 3 0 (k :: k' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil) nil φ σ e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De | exact De'].
      inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Ns). exact X1.
    + rewrite (mott_wkb_inst' Mt 2 3 1 (k :: k' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil)
                 (rectL (lsuc k) ΔL (tyU k) s0 :: nil) φ σ e),
              (mott_wkb_inst' Mt 2 3 1 (k :: k' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil)
                 (rectR (lsuc k1) ΔR (tyU k1) s1 :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ]
                 | intros [|?n]; cbn [llk]; [first [exact (wf_tm_dnf Ha1) | exact (wf_tm_dnf Ha1')]
                                           | first [apply De | apply De']] ].
      inst_cbn. rewrite !subst_lshift0 by first [exact (dnftm_nftm _ Ns) | exact (dnftm_nftm _ Nt)]. exact X2.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 2 3 Γ0 (k1 :: k1' :: nil) (GCtx ΔR :: GTm s1 :: GTm t1 :: nil) φ σ' eq_refl eq_refl).
    rewrite (lvren_ush_uext' l2' 2 (k1 :: k1' :: nil) φ eq_refl).
    apply SubRel_cons; [apply SubRel_cons; [exact He'r |] |].
    + rewrite (mott_wkb_inst' Mt' 2 3 0 (k1 :: k1' :: nil) (GCtx ΔR :: GTm s1 :: GTm t1 :: nil) nil φ σ' e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
      inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Ns'). exact X1r.
    + rewrite (mott_wkb_inst' Mt' 2 3 1 (k1 :: k1' :: nil) (GCtx ΔR :: GTm s1 :: GTm t1 :: nil)
                 (rectR (lsuc k1) ΔR (tyU k1) s1 :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ']
                 | intros [|?n]; cbn [llk]; [exact (wf_tm_dnf Ha1') | apply De'] ].
      inst_cbn. rewrite !subst_lshift0 by first [exact (dnftm_nftm _ Ns') | exact (dnftm_nftm _ Nt')]. exact X2r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 2 3 2 (k :: k' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil) xsL φ σ e)
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ]
               | apply lk_dnf_lext; [ unfold xsL; repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                    | exact De]].
    inst_cbn. rewrite !subst_lshift0 by first [exact (dnftm_nftm _ Ns) | exact (dnftm_nftm _ Nt)].
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) (lequiv_sym _ _ _ HkLg)) (HU _ _ HΔL Hwm0) BL B0).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 2 3 2 (k :: k' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil) xsR φ σ e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ]
               | apply lk_dnf_lext; [ unfold xsR; repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                    | exact De']].
    inst_cbn. rewrite !subst_lshift0 by first [exact (dnftm_nftm _ Ns) | exact (dnftm_nftm _ Nt)].
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hwm HkR HΔL HΔ HTR HTRk B0' BR).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 2 3 2 (k1 :: k1' :: nil) (GCtx ΔR :: GTm s1 :: GTm t1 :: nil) xsR φ σ' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ']
               | apply lk_dnf_lext; [ unfold xsR; repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                                    | exact De']].
    inst_cbn. rewrite !subst_lshift0 by first [exact (dnftm_nftm _ Ns') | exact (dnftm_nftm _ Nt')].
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                          (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Qms) HΔR (eqc_refl _ _ _ HΔR)
                          _ (HU _ _ HΔR Hwm10) BR BR0) Hl2g).
    eapply eqty_lconv; [apply eqty_sym, HTRR |]. rewrite EL; eapply lequiv_trans; [apply lequiv_sym, HkR | exact Qms].
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 2 (k :: k' :: nil) φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 2 (k1 :: k1' :: nil) φ eq_refl). exact Hl2g.
Qed.

Lemma rec_t_natrec {ΔL ΔR kL kR TL TR k k1 M M' s0 s1 z0 z1 t0 t1} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle t0] ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle t0] ≅ TR @ k ] ->
  [ G' ; ΔL ,, tyNat @ lzero ⊢[ lC ] M @ k ] -> [ G' ; ΔL ,, tyNat @ lzero ⊢[ lC ] M' @ k ] -> ty_leq M M' ->
  [ G' ; ΔL ⊢[ lC ] s0 : M[lsingle zero] @ k ] -> [ G' ; ΔL ⊢[ lC ] s1 : M[lsingle zero] @ k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z0 : M[lsucc] @ k ] ->
  [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z1 : M[lsucc] @ k ] -> tm_leq z0 z1 ->
  [ G' ; ΔL ⊢[ lC ] t0 : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] t1 : tyNat @ lzero ] -> tm_leq t0 t1 ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k (ΔL ,, tyNat @ lzero) (boxT M))
    (motT (wrapMT MTR) k1 (ΔR ,, tyNat @ lzero) (boxT M'))
    (recTL k (ΔL ,, tyNat @ lzero) M) (recTR k1 (ΔR ,, tyNat @ lzero) M') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (M[lsingle zero]) (boxt s0))
    (mott (wrapMt MtR) k1 ΔR (M'[lsingle zero]) (boxt s1))
    (rectL k ΔL (M[lsingle zero]) s0) (rectR k1 ΔR (M'[lsingle zero]) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) (boxt z0))
    (mott (wrapMt MtR) k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) (boxt z1))
    (rectL k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) z0) (rectR k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) z1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt t0))
    (mott (wrapMt MtR) lzero ΔR tyNat (boxt t1))
    (rectL lzero ΔL tyNat t0) (rectR lzero ΔR tyNat t1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (natrec k M s0 z0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (natrec k1 M' s1 z1 t1)))
    (rectL kL ΔL TL (natrec k M s0 z0 t0)) (rectR kR ΔR TR (natrec k1 M' s1 z1 t1)).
Proof.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR HM HM' EMM Hs Hs' Es Hz Hz' Ez Ht Ht' Et IHM IHs IHz IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hw0 : lwf L' lzero) by exact I.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl1 : lwf L' (lvsubst l1 φ)) by (rewrite <- EL; exact (proj1 HrbL)).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HkLg : lequiv (gL G') k kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') k kR) by (rewrite EL; exact HkR).
  (* contexts *)
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  assert (HNe : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ,, tyNat @ lzero ⊢[ lD ] ])
    by (intros; apply wfc_ext; [assumption | apply HN0; assumption | exact I]).
  assert (CN : [ G' ⊢[ lD ] ΔL ,, tyNat @ lzero ≅ ΔR ,, tyNat @ lzero ]).
  { apply eqc_ext; [exact HΔ | exact (HN0 _ HΔL) | apply eqty_refl, HN0, HΔL | apply lequiv_refl; exact I]. }
  pose proof (HNe _ HΔL) as HΔLN. pose proof (HNe _ HΔR) as HΔRN.
  pose proof (lift_ty (j := lD) HM Hl1c) as HMD.
  pose proof (lift_eqty (j := lD) (static_code_ty Hl1c HM HM' EMM) Hl1c) as HMM.
  assert (CNM : [ G' ⊢[ lD ] ΔL ,, tyNat @ lzero ,, M @ k ≅ ΔR ,, tyNat @ lzero ,, M' @ k1 ])
    by (apply eqc_ext; [exact CN | exact HMD | exact HMM | exact Qg]).
  assert (CNMk : [ G' ⊢[ lD ] ΔL ,, tyNat @ lzero ,, M @ k ≅ ΔR ,, tyNat @ lzero ,, M' @ k ])
    by (apply eqc_ext; [exact CN | exact HMD | exact HMM | apply lequiv_refl; rewrite EL; exact Hw]).
  assert (HΔLNM : [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔLN | exact HMD | rewrite EL; exact Hw]).
  pose proof (eqctx_wf_r (i := lD) eq_refl CNM) as HΔRNM.
  pose proof (eqctx_wf_r (i := lD) eq_refl CNMk) as HΔRNMk.
  (* the motive's instances *)
  assert (Hz0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] zero : tyNat @ lzero ])
    by (intros; apply wf_zero; [discriminate | assumption]).
  assert (HM0 : [ G' ; ΔL ⊢[ lD ] M[lsingle zero] ≅ M'[lsingle zero] @ k ])
    by exact (eqty_single (i := lD) eq_refl HMM (Hz0 _ HΔL)).
  assert (HMs : [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lD ] M[lsucc] ≅ M'[lsucc] @ k ])
    by exact (eqty_subst (i := lD) eq_refl HMM (lsub_wf_lsucc (i := lD) eq_refl ltac:(discriminate) HΔLNM)).
  pose proof (lift_tm (j := lD) Ht Hl1c) as HtD. pose proof (lift_tm (j := lD) Ht' Hl1c) as Ht'D.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Ht Ht' Et) Hl1c) as Htt.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Hs Hs' Es) Hl1c) as Hss.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Hz Hz' Ez) Hl1c) as Hzz.
  assert (HMtt : [ G' ; ΔL ⊢[ lD ] M[lsingle t0] ≅ M'[lsingle t1] @ k ])
    by exact (eqty_subst_single_D HMM (lift_ty (j := lD) HM' Hl1c) Htt HtD Ht'D).
  (* the right pieces *)
  assert (HM'R : [ G' ; ΔR ,, tyNat @ lzero ⊢[ lC ] M' @ k ]) by exact (ctxconv_ty CN (i := lC) eq_refl HM').
  assert (HM'R1 : [ G' ; ΔR ,, tyNat @ lzero ⊢[ lC ] M' @ k1 ]) by (eapply wft_lconv; [exact HM'R | apply lequiv_sym, Qg]).
  assert (Hs'L2 : [ G' ; ΔL ⊢[ lC ] s1 : M'[lsingle zero] @ k ]) by (eapply wf_conv; [exact Hs' | apply eqty_sym, HM0]).
  assert (Hs'R : [ G' ; ΔR ⊢[ lC ] s1 : M'[lsingle zero] @ k ]) by exact (ctxconv_tm HΔ (i := lC) eq_refl Hs'L2).
  assert (Hs'R1 : [ G' ; ΔR ⊢[ lC ] s1 : M'[lsingle zero] @ k1 ]) by (eapply wf_lconv; [exact Hs'R | apply lequiv_sym, Qg]).
  assert (Hz'L2 : [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z1 : M'[lsucc] @ k ])
    by (eapply wf_conv; [exact Hz' | apply eqty_sym, HMs]).
  assert (Hz'R : [ G' ; ΔR ,, tyNat @ lzero ,, M' @ k ⊢[ lC ] z1 : M'[lsucc] @ k ])
    by exact (ctxconv_tm CNMk (i := lC) eq_refl Hz'L2).
  assert (Hz'R1 : [ G' ; ΔR ,, tyNat @ lzero ,, M' @ k1 ⊢[ lC ] z1 : M'[lsucc] @ k1 ])
    by (eapply wf_lconv; [exact (ctxconv_tm CNM (i := lC) eq_refl Hz'L2) | apply lequiv_sym, Qg]).
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t1 : tyNat @ lzero ]) by exact (ctxconv_tm HΔ (i := lC) eq_refl Ht').
  pose proof (wf_ty_dnf HM) as NM. pose proof (wf_ty_dnf HM'R) as NM'.
  pose proof (wf_tm_dnf Hs) as Ns. pose proof (wf_tm_dnf Hs'R) as Ns'.
  pose proof (wf_tm_dnf Hz) as Nz. pose proof (wf_tm_dnf Hz'R) as Nz'.
  pose proof (wf_tm_dnf Ht) as Nt. pose proof (wf_tm_dnf Ht'R) as Nt'.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] natrec k M s0 z0 t0 : M[lsingle t0] @ k ])
    by (apply wf_natrec; [exact Hn | rewrite EL; exact Hw | exact HM | exact Hs | exact Hz | exact Ht]).
  assert (HcL : [ G' ; ΔL ⊢[ lC ] natrec k M s0 z0 t0 : TL @ kL ])
    by (eapply wf_lconv; [eapply wf_conv; [exact HcL0 | apply eqty_sym, HTL] | apply lequiv_sym, HkLg]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] natrec k1 M' s1 z1 t1 : M'[lsingle t1] @ k1 ])
    by (apply wf_natrec; [exact Hn | rewrite EL; exact Hw1 | exact HM'R1 | exact Hs'R1 | exact Hz'R1 | exact Ht'R]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] natrec k1 M' s1 z1 t1 : M[lsingle t0] @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg] | exact HMtt]. }
  assert (HTRM : [ G' ; ΔR ⊢[ lD ] TR ≅ M'[lsingle t1] @ k ])
    by exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTR) HMtt)).
  assert (HcR : [ G' ; ΔR ⊢[ lC ] natrec k1 M' s1 z1 t1 : TR @ kR ]).
  { eapply wf_lconv; [eapply wf_conv; [eapply wf_lconv; [exact HcR0 | exact Qg] | exact HTRM] | apply lequiv_sym, HkRg]. }
  pose proof (eqty_wf_l (i := lD) eq_refl HMtt) as HT0L.
  pose proof (wf_tm_ty (i := lD) eq_refl (lift_tm (j := lD) HcR0 Hl1c)) as HT0R.
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (Ec : tm_leq (natrec k M s0 z0 t0) (natrec k1 M' s1 z1 t1)) by (cbn; repeat split; assumption).
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm HT0L Hw HcL0 HcL0 (tm_leq_refl _)) as B0.
  pose proof (box_rel_tm HT0L Hw HcL0 HcRL Ec) as B0'.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  pose proof (box_rel_tm HT0R Hw1 HcR0 HcR0 (tm_leq_refl _)) as BR0.
  (* the recursive calls *)
  destruct (LRtm_escape IHM) as [Ha1 _]. destruct (LRtm_escape (LRtm_sym IHM)) as [Ha1' _].
  destruct (LRtm_escape IHs) as [Ha2 _]. destruct (LRtm_escape (LRtm_sym IHs)) as [Ha2' _].
  destruct (LRtm_escape IHz) as [Ha3 _]. destruct (LRtm_escape (LRtm_sym IHz)) as [Ha3' _].
  destruct (LRtm_escape IHt) as [Ha4 _]. destruct (LRtm_escape (LRtm_sym IHt)) as [Ha4' _].
  assert (HM'0 : [ G' ; ΔR ⊢[ lD ] M'[lsingle zero] @ k1 ])
    by exact (wf_ty_single (i := lD) eq_refl (lift_ty (j := lD) HM'R1 Hl1c) (Hz0 _ HΔR)).
  assert (HM's : [ G' ; ΔR ,, tyNat @ lzero ,, M' @ k1 ⊢[ lD ] M'[lsucc] @ k1 ])
    by exact (wf_ty_subst (i := lD) eq_refl (lift_ty (j := lD) HM'R1 Hl1c) (lsub_wf_lsucc (i := lD) eq_refl ltac:(discriminate) HΔRNM)).
  assert (X1 : LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k (ΔL ,, tyNat @ lzero) (boxT M))
                 (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k (ΔL ,, tyNat @ lzero) (boxT M))
                 (recTL k (ΔL ,, tyNat @ lzero) M) (recTR k1 (ΔR ,, tyNat @ lzero) M')).
  { refine (LRtm_conv_r IHM (LRty_sym _)).
    exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw Q HΔLN CN (box_rel HΔLN Hw HM HM' EMM) (box_rel HΔRN Hw1 HM'R1 HM'R1 (ty_leq_refl _))). }
  assert (X2 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (M[lsingle zero]) (boxt s0))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) k ΔL (M[lsingle zero]) (boxt s0))
                 (rectL k ΔL (M[lsingle zero]) s0) (rectR k1 ΔR (M'[lsingle zero]) s1)).
  { refine (LRtm_conv_r IHs (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             (kL := k) (kR := k1) Hw Q HΔL HΔ HM0 HM'0
             (box_rel_tm (eqty_wf_l (i := lD) eq_refl HM0) Hw Hs Hs' Es) (box_rel_tm HM'0 Hw1 Hs'R1 Hs'R1 (tm_leq_refl _))). }
  assert (X3 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) (boxt z0))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))]))
                    k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) (boxt z0))
                 (rectL k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) z0) (rectR k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) z1)).
  { refine (LRtm_conv_r IHz (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             (kL := k) (kR := k1) Hw Q HΔLNM CNM HMs HM's
             (box_rel_tm (eqty_wf_l (i := lD) eq_refl HMs) Hw Hz Hz' Ez) (box_rel_tm HM's Hw1 Hz'R1 Hz'R1 (tm_leq_refl _))). }
  assert (X4 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt t0))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) lzero ΔL tyNat (boxt t0))
                 (rectL lzero ΔL tyNat t0) (rectR lzero ΔR tyNat t1)).
  { refine (LRtm_conv_r IHt (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw0 (lequiv_refl _ _ Hw0) HΔL HΔ (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) (HN0 _ HΔR)
             (box_rel_tm (HN0 _ HΔL) Hw0 Ht Ht' Et) (box_rel_tm (HN0 _ HΔR) Hw0 Ht'R Ht'R (tm_leq_refl _))). }
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHz) IHz) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X4r.
  (* the reducts *)
  set (xsL := recTL k (ΔL ,, tyNat @ lzero) M :: rectL k ΔL (M[lsingle zero]) s0 ::
              rectL k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) z0 :: rectL lzero ΔL tyNat t0 :: nil).
  set (xsR := recTR k1 (ΔR ,, tyNat @ lzero) M' :: rectR k1 ΔR (M'[lsingle zero]) s1 ::
              rectR k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) z1 :: rectR lzero ΔR tyNat t1 :: nil).
  set (rL := ((usubst_tm (bs 10) (uext (k :: nil) φ))⦃gext_s (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 10) (uext (k1 :: nil) φ))⦃gext_s (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL (natrec k M s0 z0 t0) = Some rL)
    by (apply redt_natrec_inst; first [exact (wf_tm_dnf (Hbs 10 ltac:(lia))) | exact Nσ | exact De | assumption
                                      | exact (wf_tm_dnf Ha1) | exact (wf_tm_dnf Ha2) | exact (wf_tm_dnf Ha3) | exact (wf_tm_dnf Ha4)]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR (natrec k1 M' s1 z1 t1) = Some rR)
    by (apply redt_natrec_inst; first [exact (wf_tm_dnf (Hbs' 10 ltac:(lia))) | exact Nσ' | exact De' | assumption
                                      | exact (wf_tm_dnf Ha1') | exact (wf_tm_dnf Ha2') | exact (wf_tm_dnf Ha3') | exact (wf_tm_dnf Ha4')]).
  refine (rec_t_fin HΔL HΔR HwL HwR HTLk HTRk HcL HcR HredL HredR _).
  pose proof De as De0. pose proof De' as De0'.
  refine (br_core 10 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
            (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil) xsL xsR _ _ _ ltac:(lia) eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption) _
            (GS_natrec EP EM Hσ HΔL HΔ HM HM'R HMM EMM Hs Hs'R Hss Es Hz Hz'R Hzz Ez Ht Ht'R Htt Et)
            (GS_natrec EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HM'R1 HM'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HM'R1 Hl1c)) (ty_leq_refl _)
               Hs'R1 Hs'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _)
               Hz'R1 Hz'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hz'R1 Hl1c)) (tm_leq_refl _)
               Ht'R Ht'R (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - intros [|i]; unfold uext; cbn; [exact E | apply leqv_refl].
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 1 5 Γ0 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil) φ σ eq_refl eq_refl).
    rewrite (lvren_ush_uext' l1 1 (k :: nil) φ eq_refl), (lvren_ush_uext' l2 1 (k :: nil) φ eq_refl).
    apply SubRel_cons; [apply SubRel_cons; [apply SubRel_cons; [apply SubRel_cons; [exact He |] |] |] |].
    + rewrite (motT_wkb_inst' MT 1 5 0 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil) nil φ σ e e),
              (motT_wkb_inst' MT 1 5 0 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil) nil φ σ e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NM). exact X1.
    + rewrite (mott_wkb_inst' Mt 1 5 1 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
                 (recTL k (ΔL ,, tyNat @ lzero) M :: nil) φ σ e),
              (mott_wkb_inst' Mt 1 5 1 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
                 (recTR k1 (ΔR ,, tyNat @ lzero) M' :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Ns). exact X2.
    + rewrite (mott_wkb_inst' Mt 1 5 2 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
                 (recTL k (ΔL ,, tyNat @ lzero) M :: rectL k ΔL (M[lsingle zero]) s0 :: nil) φ σ e),
              (mott_wkb_inst' Mt 1 5 2 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
                 (recTR k1 (ΔR ,, tyNat @ lzero) M' :: rectR k1 ΔR (M'[lsingle zero]) s1 :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NM). rewrite !subst_lshift0 by exact (dnftm_nftm _ Nz).
      exact X3.
    + rewrite (mott_wkb_inst' Mt 1 5 3 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
                 (recTL k (ΔL ,, tyNat @ lzero) M :: rectL k ΔL (M[lsingle zero]) s0 ::
                  rectL k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) z0 :: nil) φ σ e),
              (mott_wkb_inst' Mt 1 5 3 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
                 (recTR k1 (ΔR ,, tyNat @ lzero) M' :: rectR k1 ΔR (M'[lsingle zero]) s1 ::
                  rectR k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) z1 :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt). exact X4.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 1 5 Γ0 (k1 :: nil) (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil) φ σ' eq_refl eq_refl).
    rewrite (lvren_ush_uext' l1' 1 (k1 :: nil) φ eq_refl), (lvren_ush_uext' l2' 1 (k1 :: nil) φ eq_refl).
    apply SubRel_cons; [apply SubRel_cons; [apply SubRel_cons; [apply SubRel_cons; [exact He'r |] |] |] |].
    + rewrite (motT_wkb_inst' MT' 1 5 0 (k1 :: nil) (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil) nil φ σ' e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NM'). exact X1r.
    + rewrite (mott_wkb_inst' Mt' 1 5 1 (k1 :: nil) (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil)
                 (recTR k1 (ΔR ,, tyNat @ lzero) M' :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Ns'). exact X2r.
    + rewrite (mott_wkb_inst' Mt' 1 5 2 (k1 :: nil) (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil)
                 (recTR k1 (ΔR ,, tyNat @ lzero) M' :: rectR k1 ΔR (M'[lsingle zero]) s1 :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NM'). rewrite !subst_lshift0 by exact (dnftm_nftm _ Nz').
      exact X3r.
    + rewrite (mott_wkb_inst' Mt' 1 5 3 (k1 :: nil) (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil)
                 (recTR k1 (ΔR ,, tyNat @ lzero) M' :: rectR k1 ΔR (M'[lsingle zero]) s1 ::
                  rectR k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) z1 :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite !subst_lshift0 by exact (dnftm_nftm _ Nt'). exact X4r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 1 5 4 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil) xsL φ σ e)
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | unfold xsL; lk_dnf_tac].
    inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NM).
    rewrite !subst_lshift0 by first [exact (dnftm_nftm _ Ns) | exact (dnftm_nftm _ Nz) | exact (dnftm_nftm _ Nt)].
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) (lequiv_sym _ _ _ HkLg)) HT0L BL B0).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 1 5 4 (k :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil) xsR φ σ e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | unfold xsR; lk_dnf_tac].
    inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NM).
    rewrite !subst_lshift0 by first [exact (dnftm_nftm _ Ns) | exact (dnftm_nftm _ Nz) | exact (dnftm_nftm _ Nt)].
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw HkR HΔL HΔ HTR HTRk B0' BR).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 1 5 4 (k1 :: nil) (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil) xsR φ σ' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | unfold xsR; lk_dnf_tac].
    inst_cbn. rewrite !subst_lshift0_ty by exact (dnfty_nfty _ NM').
    rewrite !subst_lshift0 by first [exact (dnftm_nftm _ Ns') | exact (dnftm_nftm _ Nz') | exact (dnftm_nftm _ Nt')].
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                          (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Q) HΔR (eqc_refl _ _ _ HΔR)
                          _ HT0R BR BR0) Hl2g).
    eapply eqty_lconv; [exact HTRM | apply lequiv_sym, HkRg].
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 1 (k :: nil) φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 1 (k1 :: nil) φ eq_refl). exact Hl2g.
Qed.

Lemma rec_t_app {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' f f' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k' kL -> lequiv L' k' kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ TL @ k' ] -> [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ TR @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] f : tyPi k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] f' : tyPi k k' A B @ lmax k k' ] -> tm_leq f f' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tyPi k k' A B) (boxt f))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tyPi k1 k1' A' B') (boxt f'))
    (rectL (lmax k k') ΔL (tyPi k k' A B) f) (rectR (lmax k1 k1') ΔR (tyPi k1 k1' A' B') f') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (app f k k' A B a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (app f' k1 k1' A' B' a')))
    (rectL kL ΔL TL (app f k k' A B a)) (rectR kR ΔR TR (app f' k1 k1' A' B' a')).
Proof.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Hf Hf' Ef Ha Ha' Ea IHA IHB IHf IHa.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto). assert (Hwm1 : lwf L' (lmax k1 k1')) by (cbn; auto).
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl1 : lwf L' (lvsubst l1 φ)) by (rewrite <- EL; exact (proj1 HrbL)).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HkLg : lequiv (gL G') k' kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') k' kR) by (rewrite EL; exact HkR).
  (* declarative facts about the pieces *)
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (lift_ty (j := lD) HB Hl1c) as HBD.
  pose proof (lift_eqty (j := lD) (static_code_ty Hl1c HA HA' EA) Hl1c) as HAA.
  pose proof (lift_eqty (j := lD) (static_code_ty Hl1c HB HB' EB) Hl1c) as HBB.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Hf Hf' Ef) Hl1c) as Hff.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Ha Ha' Ea) Hl1c) as Haa.
  pose proof (lift_tm (j := lD) Ha Hl1c) as HaD. pose proof (lift_tm (j := lD) Ha' Hl1c) as Ha'D.
  assert (HΔLA : [ G' ; ΔL ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔL | exact HAD | rewrite EL; exact Hw]).
  assert (CA : [ G' ⊢[ lD ] ΔL ,, A @ k ≅ ΔR ,, A' @ k ]).
  { apply eqc_ext; [exact HΔ | exact HAD | exact HAA | apply lequiv_refl; rewrite EL; exact Hw]. }
  assert (CA1 : [ G' ⊢[ lD ] ΔL ,, A @ k ≅ ΔR ,, A' @ k1 ]) by (apply eqc_ext; [exact HΔ | exact HAD | exact HAA | exact Qg]).
  pose proof (eqctx_wf_r (i := lD) eq_refl CA1) as HΔRA1.
  assert (HPP : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B ≅ tyPi k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact Qg | exact Qg' | exact HAD | exact HAA | exact HBB]).
  assert (HPPk : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B ≅ tyPi k k' A' B' @ lmax k k' ])
    by (apply eqty_pi; [discriminate | apply lequiv_refl; rewrite EL; exact Hw | apply lequiv_refl; rewrite EL; exact Hw'
                       | exact HAD | exact HAA | exact HBB]).
  pose proof (eqty_wf_l (i := lD) eq_refl HPP) as HPD.
  assert (HBa : [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ B'[lsingle a'] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty (j := lD) HB' Hl1c) Haa HaD Ha'D).
  (* the right pieces, in the right context: at the left levels and at their own *)
  assert (HA'R : [ G' ; ΔR ⊢[ lC ] A' @ k ]) by exact (ctxconv_ty HΔ (i := lC) eq_refl HA').
  assert (HA'R1 : [ G' ; ΔR ⊢[ lC ] A' @ k1 ]) by (eapply wft_lconv; [exact HA'R | apply lequiv_sym, Qg]).
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D.
  assert (HB'R : [ G' ; ΔR ,, A' @ k ⊢[ lC ] B' @ k' ]) by exact (ctxconv_ty CA (i := lC) eq_refl HB').
  assert (HB'R1 : [ G' ; ΔR ,, A' @ k1 ⊢[ lC ] B' @ k1' ])
    by (eapply wft_lconv; [exact (ctxconv_ty CA1 (i := lC) eq_refl HB') | apply lequiv_sym, Qg']).
  pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  assert (Hf'L2 : [ G' ; ΔL ⊢[ lC ] f' : tyPi k k' A' B' @ lmax k k' ]) by (eapply wf_conv; [exact Hf' | apply eqty_sym, HPPk]).
  assert (Hf'R : [ G' ; ΔR ⊢[ lC ] f' : tyPi k k' A' B' @ lmax k k' ]) by exact (ctxconv_tm HΔ (i := lC) eq_refl Hf'L2).
  assert (Hf'R1 : [ G' ; ΔR ⊢[ lC ] f' : tyPi k1 k1' A' B' @ lmax k1 k1' ]).
  { eapply wf_lconv; [| apply lequiv_sym, Qmg]. eapply wf_conv; [exact Hf'R |].
    eapply eqty_lconv; [| exact Qmg].
    apply eqty_pi; [discriminate | apply lequiv_sym, Qg | apply lequiv_sym, Qg' | exact HA'R1D
                   | apply eqty_refl, HA'R1D | apply eqty_refl, HB'R1D]. }
  pose proof (wf_tm_ty (i := lD) eq_refl (lift_tm (j := lD) Hf'R1 Hl1c)) as HPR1.
  assert (Ha'L2 : [ G' ; ΔL ⊢[ lC ] a' : A' @ k ]) by (eapply wf_conv; [exact Ha' | apply eqty_sym, HAA]).
  assert (Ha'R : [ G' ; ΔR ⊢[ lC ] a' : A' @ k ]) by exact (ctxconv_tm HΔ (i := lC) eq_refl Ha'L2).
  assert (Ha'R1 : [ G' ; ΔR ⊢[ lC ] a' : A' @ k1 ]) by (eapply wf_lconv; [exact Ha'R | apply lequiv_sym, Qg]).
  pose proof (wf_ty_dnf HA) as NA. pose proof (wf_ty_dnf HA'R) as NA'.
  pose proof (wf_ty_dnf HB) as NB. pose proof (wf_ty_dnf HB'R) as NB'.
  pose proof (wf_tm_dnf Hf) as Nf. pose proof (wf_tm_dnf Hf'R) as Nf'.
  pose proof (wf_tm_dnf Ha) as Na. pose proof (wf_tm_dnf Ha'R) as Na'.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] app f k k' A B a : B[lsingle a] @ k' ])
    by (apply wf_app; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Hf | exact Ha]).
  assert (HcL : [ G' ; ΔL ⊢[ lC ] app f k k' A B a : TL @ kL ])
    by (eapply wf_lconv; [eapply wf_conv; [exact HcL0 | apply eqty_sym, HTL] | apply lequiv_sym, HkLg]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] app f' k1 k1' A' B' a' : B'[lsingle a'] @ k1' ])
    by (apply wf_app; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1 | exact Hf'R1 | exact Ha'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] app f' k1 k1' A' B' a' : B[lsingle a] @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg'] | exact HBa]. }
  assert (HTRM : [ G' ; ΔR ⊢[ lD ] TR ≅ B'[lsingle a'] @ k' ])
    by exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTR) HBa)).
  assert (HcR : [ G' ; ΔR ⊢[ lC ] app f' k1 k1' A' B' a' : TR @ kR ]).
  { eapply wf_lconv; [eapply wf_conv; [eapply wf_lconv; [exact HcR0 | exact Qg'] | exact HTRM] | apply lequiv_sym, HkRg]. }
  pose proof (eqty_wf_l (i := lD) eq_refl HBa) as HT0L.
  pose proof (wf_tm_ty (i := lD) eq_refl (lift_tm (j := lD) HcR0 Hl1c)) as HT0R.
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (Ec : tm_leq (app f k k' A B a) (app f' k1 k1' A' B' a')) by (cbn; repeat split; assumption).
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm HT0L Hw' HcL0 HcL0 (tm_leq_refl _)) as B0.
  pose proof (box_rel_tm HT0L Hw' HcL0 HcRL Ec) as B0'.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  pose proof (box_rel_tm HT0R Hw1' HcR0 HcR0 (tm_leq_refl _)) as BR0.
  (* the recursive calls *)
  destruct (LRtm_escape IHA) as [Ha1 _]. destruct (LRtm_escape (LRtm_sym IHA)) as [Ha1' _].
  destruct (LRtm_escape IHB) as [Ha2 _]. destruct (LRtm_escape (LRtm_sym IHB)) as [Ha2' _].
  destruct (LRtm_escape IHf) as [Ha3 _]. destruct (LRtm_escape (LRtm_sym IHf)) as [Ha3' _].
  destruct (LRtm_escape IHa) as [Ha4 _]. destruct (LRtm_escape (LRtm_sym IHa)) as [Ha4' _].
  assert (X1 : LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A))
                 (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k ΔL (boxT A))
                 (recTL k ΔL A) (recTR k1 ΔR A')).
  { refine (LRtm_conv_r IHA (LRty_sym _)).
    exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw Q HΔL HΔ (box_rel HΔL Hw HA HA' EA) (box_rel HΔR Hw1 HA'R1 HA'R1 (ty_leq_refl _))). }
  assert (X2 : LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B))
                 (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k' (ΔL ,, A @ k) (boxT B))
                 (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B')).
  { refine (LRtm_conv_r IHB (LRty_sym _)).
    exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw' Q' HΔLA CA1 (box_rel HΔLA Hw' HB HB' EB) (box_rel HΔRA1 Hw1' HB'R1 HB'R1 (ty_leq_refl _))). }
  assert (X3 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tyPi k k' A B) (boxt f))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))]))
                    (lmax k k') ΔL (tyPi k k' A B) (boxt f))
                 (rectL (lmax k k') ΔL (tyPi k k' A B) f) (rectR (lmax k1 k1') ΔR (tyPi k1 k1' A' B') f')).
  { refine (LRtm_conv_r IHf (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             (kL := lmax k k') (kR := lmax k1 k1') Hwm Qm HΔL HΔ HPP HPR1
             (box_rel_tm HPD Hwm Hf Hf' Ef) (box_rel_tm HPR1 Hwm1 Hf'R1 Hf'R1 (tm_leq_refl _))). }
  assert (X4 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) k ΔL A (boxt a))
                 (rectL k ΔL A a) (rectR k1 ΔR A' a')).
  { refine (LRtm_conv_r IHa (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             (kL := k) (kR := k1) Hw Q HΔL HΔ HAA HA'R1D
             (box_rel_tm HAD Hw Ha Ha' Ea) (box_rel_tm HA'R1D Hw1 Ha'R1 Ha'R1 (tm_leq_refl _))). }
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHf) IHf) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X4r.
  (* the reducts *)
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL (lmax k k') ΔL (tyPi k k' A B) f :: rectL k ΔL A a :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tyPi k1 k1' A' B') f' :: rectR k1 ΔR A' a' :: nil).
  set (rL := ((usubst_tm (bs 12) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 12) (uext (k1 :: k1' :: nil) φ))⦃gext_s (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL (app f k k' A B a) = Some rL)
    by (apply redt_app_inst; first [exact (wf_tm_dnf (Hbs 12 ltac:(lia))) | exact Nσ | exact De | assumption
                                   | exact (wf_tm_dnf Ha1) | exact (wf_tm_dnf Ha2) | exact (wf_tm_dnf Ha3) | exact (wf_tm_dnf Ha4)]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR (app f' k1 k1' A' B' a') = Some rR)
    by (apply redt_app_inst; first [exact (wf_tm_dnf (Hbs' 12 ltac:(lia))) | exact Nσ' | exact De' | assumption
                                   | exact (wf_tm_dnf Ha1') | exact (wf_tm_dnf Ha2') | exact (wf_tm_dnf Ha3') | exact (wf_tm_dnf Ha4')]).
  refine (rec_t_fin HΔL HΔR HwL HwR HTLk HTRk HcL HcR HredL HredR _).
  pose proof De as De0. pose proof De' as De0'.
  refine (br_core 12 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) xsL xsR _ _ _ ltac:(lia) eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption) _
            (GS_app EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Hf Hf'R Hff Ef Ha Ha'R Haa Ea)
            (GS_app EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Hf'R1 Hf'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hf'R1 Hl1c)) (tm_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - intros [|[|i]]; unfold uext; cbn; [exact E' | exact E | apply leqv_refl].
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 2 5 Γ0 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) φ σ eq_refl eq_refl).
    rewrite (lvren_ush_uext' l1 2 (k :: k' :: nil) φ eq_refl), (lvren_ush_uext' l2 2 (k :: k' :: nil) φ eq_refl).
    apply SubRel_cons; [apply SubRel_cons; [apply SubRel_cons; [apply SubRel_cons; [exact He |] |] |] |].
    + rewrite (motT_wkb_inst' MT 2 5 0 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) nil φ σ e e),
              (motT_wkb_inst' MT 2 5 0 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) nil φ σ e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NB)]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf) | exact (dnftm_nftm _ Na)]. exact X1.
    + rewrite (motT_wkb_inst' MT 2 5 1 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (recTL k ΔL A :: nil) φ σ e),
              (motT_wkb_inst' MT 2 5 1 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (recTR k1 ΔR A' :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NB)]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf) | exact (dnftm_nftm _ Na)]. exact X2.
    + rewrite (mott_wkb_inst' Mt 2 5 2 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: nil) φ σ e),
              (mott_wkb_inst' Mt 2 5 2 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NB)]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf) | exact (dnftm_nftm _ Na)]. exact X3.
    + rewrite (mott_wkb_inst' Mt 2 5 3 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL (lmax k k') ΔL (tyPi k k' A B) f :: nil) φ σ e),
              (mott_wkb_inst' Mt 2 5 3 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tyPi k1 k1' A' B') f' :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NB)]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf) | exact (dnftm_nftm _ Na)]. exact X4.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 2 5 Γ0 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) φ σ' eq_refl eq_refl).
    rewrite (lvren_ush_uext' l1' 2 (k1 :: k1' :: nil) φ eq_refl), (lvren_ush_uext' l2' 2 (k1 :: k1' :: nil) φ eq_refl).
    apply SubRel_cons; [apply SubRel_cons; [apply SubRel_cons; [apply SubRel_cons; [exact He'r |] |] |] |].
    + rewrite (motT_wkb_inst' MT' 2 5 0 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) nil φ σ' e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NB')]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf') | exact (dnftm_nftm _ Na')]. exact X1r.
    + rewrite (motT_wkb_inst' MT' 2 5 1 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) (recTR k1 ΔR A' :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NB')]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf') | exact (dnftm_nftm _ Na')]. exact X2r.
    + rewrite (mott_wkb_inst' Mt' 2 5 2 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) (recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NB')]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf') | exact (dnftm_nftm _ Na')]. exact X3r.
    + rewrite (mott_wkb_inst' Mt' 2 5 3 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) (recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tyPi k1 k1' A' B') f' :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NB')]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf') | exact (dnftm_nftm _ Na')]. exact X4r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 2 5 4 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) xsL φ σ e)
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | unfold xsL; lk_dnf_tac].
    inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NB)]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf) | exact (dnftm_nftm _ Na)].
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) (lequiv_sym _ _ _ HkLg)) HT0L BL B0).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 2 5 4 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil) xsR φ σ e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | unfold xsR; lk_dnf_tac].
    inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NB)]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf) | exact (dnftm_nftm _ Na)].
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw' HkR HΔL HΔ HTR HTRk B0' BR).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 2 5 4 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) xsR φ σ' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | unfold xsR; lk_dnf_tac].
    inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NB')]. rewrite ?subst_lshift0 by first [exact (dnftm_nftm _ Nf') | exact (dnftm_nftm _ Na')].
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                          (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Q') HΔR (eqc_refl _ _ _ HΔR)
                          _ HT0R BR BR0) Hl2g).
    eapply eqty_lconv; [exact HTRM | apply lequiv_sym, HkRg].
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 2 (k :: k' :: nil) φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 2 (k1 :: k1' :: nil) φ eq_refl). exact Hl2g.
Qed.

Lemma rec_t_var {ΔL ΔR kL kR TL TR k T0 n} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] -> lequiv L' k kL -> lequiv L' k kR ->
  [ G' ; ΔL ⊢[ lD ] T0 ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] T0 ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lV ] var n : T0 @ k ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (var n)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (var n)))
    (rectL kL ΔL TL (var n)) (rectR kR ΔR TR (var n)).
Proof.
  intros HΔL HΔ HkL HkR HTL HTR Hv.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (HkLg : lequiv (gL G') k kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') k kR) by (rewrite EL; exact HkR).
  assert (QLR : lequiv L' kL kR) by exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkL) HkR).
  assert (QLRg : lequiv (gL G') kL kR) by (rewrite EL; exact QLR).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (HTRkL : [ G' ; ΔR ⊢[ lD ] TR @ kL ]) by (eapply wft_lconv; [exact HTRk | exact QLRg]).
  assert (HTLR : [ G' ; ΔL ⊢[ lD ] TL ≅ TR @ kL ]).
  { eapply eqty_lconv; [exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) HTR) | apply lequiv_sym, HkLg]. }
  assert (HvL : [ G' ; ΔL ⊢[ lV ] var n : TL @ kL ])
    by (eapply wf_lconv; [eapply wf_conv; [exact Hv | apply eqty_sym, HTL] | apply lequiv_sym, HkLg]).
  assert (HvR : [ G' ; ΔR ⊢[ lV ] var n : TR @ kR ]).
  { refine (ctxconv_tm HΔ (i := lV) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact Hv | apply eqty_sym, HTR] | apply lequiv_sym, HkRg]. }
  assert (HvRL : [ G' ; ΔR ⊢[ lV ] var n : TR @ kL ]) by (eapply wf_lconv; [exact HvR | exact QLRg]).
  assert (Hlv : lle lV lC) by (unfold lle; cbn; lia).
  pose proof (lift_tm (j := lC) HvL Hlv) as HcL. pose proof (lift_tm (j := lC) HvR Hlv) as HcR.
  pose proof (wf_ty_dnf HTLk) as NTL. pose proof (wf_ty_dnf HTRk) as NTR. pose proof (wf_tm_dnf HvL) as Nv.
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  set (osL := GCtx ΔL :: GTy TL :: GTm (var n) :: nil). set (osR := GCtx ΔR :: GTy TR :: GTm (var n) :: nil).
  set (rL := ((usubst_tm (bs 4) (uext (kL :: nil) φ))⦃gext_s osL σ⦄)[lext nil e]).
  set (rR := ((usubst_tm (bs' 4) (uext (kR :: nil) φ))⦃gext_s osR σ'⦄)[lext nil e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL (var n) = Some rL)
    by (apply redt_var_inst; first [exact (wf_tm_dnf (Hbs 4 ltac:(lia))) | exact Nσ | exact De | assumption]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR (var n) = Some rR)
    by (apply redt_var_inst; first [exact (wf_tm_dnf (Hbs' 4 ltac:(lia))) | exact Nσ' | exact De' | assumption]).
  refine (rec_t_fin HΔL HΔR HwL HwR HTLk HTRk HcL HcR HredL HredR _).
  refine (br_core 4 (kL :: nil) (kR :: nil) osL osR nil nil _ _ _ ltac:(lia) eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption) _
            (GS_var EP EM Hσ HΔL HΔ HTLk HTRkL HTLR HvL HvRL)
            (GS_var EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HTRk HTRk (eqty_refl _ _ _ _ _ HTRk) HvR HvR)
            _ _ _ _ _ _ _).
  - intros [|i]; unfold uext; cbn; [exact (lequiv_leqv _ _ _ QLR) | apply leqv_refl].
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst].
    rewrite (wkc_inst' 1 3 Γ0 (kL :: nil) osL φ σ eq_refl eq_refl). exact He.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst].
    rewrite (wkc_inst' 1 3 Γ0 (kR :: nil) osR φ σ' eq_refl eq_refl). exact He'r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 1 3 0 (kL :: nil) osL nil φ σ e e)
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De].
    unfold osL; inst_cbn. rewrite ?subst_lshift0_ty by exact (dnfty_nfty _ NTL). rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nv). rewrite ?Nat.add_0_r.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_refl _ _ HwL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_refl _ _ _ _ _ HTLk) HTLk BL BL).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 1 3 0 (kL :: nil) osL nil φ σ e' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | exact De'].
    unfold osL; inst_cbn. rewrite ?subst_lshift0_ty by exact (dnfty_nfty _ NTL). rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nv). rewrite ?Nat.add_0_r.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             HwL QLR HΔL HΔ HTLR HTRk BL BR).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 1 3 0 (kR :: nil) osR nil φ σ' e' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | exact De'].
    unfold osR; inst_cbn. rewrite ?subst_lshift0_ty by exact (dnfty_nfty _ NTR). rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nv). rewrite ?Nat.add_0_r.
    exact (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR (lequiv_refl _ _ HwR) HΔR (eqc_refl _ _ _ HΔR)
                          (eqty_refl _ _ _ _ _ HTRk) HTRk BR BR) Hl2g).
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 1 (kL :: nil) φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 1 (kR :: nil) φ eq_refl). exact Hl2g.
Qed.

(** ** λ: the index is first reduced to its Π whnf *)
Lemma LRty_eqM {l T T'} : LRtyM l G' Θ T T' -> [ G' ; Θ ⊢[ lM ] T ≅ T' @ l ].
Proof.
  intros [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & H).
  pose proof (geq_ty_sound H) as H'. rewrite (@gm_layer_M EP EM EMl) in H'. exact H'.
Qed.

Lemma rec_t_fin_lam {ΔL ΔR kL kR TL TR WL WR k k' A b k1 k1' A' b' rL rR} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ; ΔR ⊢[ lD ] ] -> lwf L' kL -> lwf L' kR ->
  [ G' ; ΔL ⊢[ lD ] TL @ kL ] -> [ G' ; ΔR ⊢[ lD ] TR @ kR ] ->
  [ G' ; ΔL ⊢[ lC ] lam k k' A b : TL @ kL ] -> [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : TR @ kR ] ->
  [ G' ; ΔL ⊢[ lD ] TL ⤳* WL @ kL ] -> [ G' ; ΔR ⊢[ lD ] TR ⤳* WR @ kR ] ->
  redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL WL (lam k k' A b) = Some rL ->
  redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR WR (lam k1 k1' A' b') = Some rR ->
  LRtyM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (lam k k' A b)))
    (mott (wrapMt MtL) kL ΔL WL (boxt (lam k k' A b))) ->
  LRtyM (lvsubst l2' φ) G' Θ (mott (wrapMt MtR) kR ΔR TR (boxt (lam k1 k1' A' b')))
    (mott (wrapMt MtR) kR ΔR WR (boxt (lam k1 k1' A' b'))) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (lam k k' A b)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (lam k1 k1' A' b'))) rL rR ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (lam k k' A b)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (lam k1 k1' A' b')))
    (rectL kL ΔL TL (lam k k' A b)) (rectR kR ΔR TR (lam k1 k1' A' b')).
Proof.
  intros HΔL HΔR HkL HkR HTL HTR HcL HcR HWL HWR HredL HredR ML MR W.
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (HkLg : lwf (gL G') kL) by (rewrite EL; exact HkL). assert (HkRg : lwf (gL G') kR) by (rewrite EL; exact HkR).
  destruct (LRtm_escape W) as [HrL _]. destruct (LRtm_escape (LRtm_sym W)) as [HrR _].
  rewrite (@gm_layer_M EP EM EMl) in HrL, HrR.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl HrL) as HΘ0.
  pose proof (LRty_eqM ML) as EqL. pose proof (LRty_eqM MR) as EqR.
  pose proof (eqty_wf_r (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWL)) as HWL0.
  pose proof (eqty_wf_r (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWR)) as HWR0.
  assert (HcLW : [ G' ; ΔL ⊢[ lC ] lam k k' A b : WL @ kL ])
    by (eapply wf_conv; [exact HcL | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HWL)]).
  assert (HcRW : [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : WR @ kR ])
    by (eapply wf_conv; [exact HcR | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HWR)]).
  pose proof (tmred_elimt_idx HrbL HkLg HΔL HWL (wf_boxt _ _ _ _ _ _ HΘ0 HkLg HΔL HTL HcL) EqL) as R1a.
  pose proof (tmred_elimt_beta HrbL HkLg HΔL HWL0 HcLW HredL
                ltac:(eapply wf_conv; [exact HrL | apply eqty_sym, EqL])) as R1b.
  pose proof (tmred_trans _ _ _ _ _ R1a (tmred_conv _ _ _ _ _ eq_refl R1b (eqty_sym _ _ _ _ _ _ EqL))) as R1.
  pose proof (wf_lconv _ _ _ _ _ _ _ HrR (lequiv_sym _ _ _ Hl2g)) as HrR'.
  pose proof (tmred_elimt_idx HrbR HkRg HΔR HWR (wf_boxt _ _ _ _ _ _ HΘ0 HkRg HΔR HTR HcR) EqR) as R2a.
  pose proof (tmred_elimt_beta HrbR HkRg HΔR HWR0 HcRW HredR
                ltac:(eapply wf_conv; [exact HrR' | apply eqty_sym, EqR])) as R2b.
  pose proof (tmred_trans _ _ _ _ _ R2a (tmred_conv _ _ _ _ _ eq_refl R2b (eqty_sym _ _ _ _ _ _ EqR))) as R2.
  pose proof (tmred_lconv _ _ _ _ _ R2 Hl2g) as R2'.
  rewrite <- (@gm_layer_M EP EM EMl) in R1, R2'.
  exact (LRtm_red W R1 R2').
Qed.

Lemma rec_t_lam {ΔL ΔR kL kR TL TR k k' k1 k1' A A' B0 b b'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] b : B0 @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] b' : B0 @ k' ] -> tm_leq b b' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  (forall BL BR, [ G' ; ΔL ,, A @ k ⊢[ lD ] B0 ≅ BL @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lD ] B0 ≅ BR @ k' ] ->
     LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' (ΔL ,, A @ k) BL (boxt b))
       (mott (wrapMt MtR) k1' (ΔR ,, A' @ k1) BR (boxt b'))
       (rectL k' (ΔL ,, A @ k) BL b) (rectR k1' (ΔR ,, A' @ k1) BR b')) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (lam k k' A b)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (lam k1 k1' A' b')))
    (rectL kL ΔL TL (lam k k' A b)) (rectR kR ΔR TR (lam k1 k1' A' b')).
Proof.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA Hb Hb' Eb IHA IHb.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  pose proof (wf_ctx_dnf HΔL) as NΔL. pose proof (wf_ctx_dnf HΔR) as NΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto). assert (Hwm1 : lwf L' (lmax k1 k1')) by (cbn; auto).
  assert (Hkg : lequiv (gL G') k k) by (apply lequiv_refl; rewrite EL; exact Hw).
  assert (Hkg' : lequiv (gL G') k' k') by (apply lequiv_refl; rewrite EL; exact Hw').
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HkLg : lequiv (gL G') (lmax k k') kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') (lmax k k') kR) by (rewrite EL; exact HkR).
  (* the domain *)
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD.
  pose proof (lift_eqty (j := lD) (static_code_ty Hl1c HA HA' EA) Hl1c) as HAA.
  assert (HΔLA : [ G' ; ΔL ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔL | exact HAD | rewrite EL; exact Hw]).
  assert (CA : [ G' ⊢[ lD ] ΔL ,, A @ k ≅ ΔR ,, A' @ k ]) by (apply eqc_ext; [exact HΔ | exact HAD | exact HAA | exact Hkg]).
  assert (CA1 : [ G' ⊢[ lD ] ΔL ,, A @ k ≅ ΔR ,, A' @ k1 ]) by (apply eqc_ext; [exact HΔ | exact HAD | exact HAA | exact Qg]).
  pose proof (eqctx_wf_r (i := lD) eq_refl CA1) as HΔRA1.
  assert (HA'R : [ G' ; ΔR ⊢[ lC ] A' @ k ]) by exact (ctxconv_ty HΔ (i := lC) eq_refl HA').
  assert (HA'R1 : [ G' ; ΔR ⊢[ lC ] A' @ k1 ]) by (eapply wft_lconv; [exact HA'R | apply lequiv_sym, Qg]).
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D.
  (* the indices' Π whnfs *)
  destruct (decl_pi_red HTL) as (c1 & c2 & CL & BL & HWL).
  destruct (decl_pi_red (ctxconv_eqty HΔ (i := lD) eq_refl HTR)) as (c3 & c4 & CR & BR & HWR).
  assert (EqL : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ tyPi c1 c2 CL BL @ lmax k k' ])
    by exact (eqty_trans _ _ _ _ _ _ _ HTL (tyred_eq _ _ _ _ _ _ HWL)).
  assert (EqR : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ tyPi c3 c4 CR BR @ lmax k k' ])
    by exact (eqty_trans _ _ _ _ _ _ _ HTR (ctxconv_eqty (eqctx_sym_D HΔ) (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWR))).
  destruct (decl_pi_inj EqL) as (_ & _ & _ & HB0BL). destruct (decl_pi_inj EqR) as (_ & _ & _ & HB0BR).
  pose proof (eqty_wf_r (i := lD) eq_refl HB0BL) as HBLD. pose proof (eqty_wf_r (i := lD) eq_refl HB0BR) as HBRD.
  assert (HBLBR : [ G' ; ΔL ,, A @ k ⊢[ lD ] BL ≅ BR @ k' ])
    by exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HB0BL) HB0BR).
  pose proof (ctxconv_ty CA (i := lD) eq_refl HBRD) as HBRk.
  assert (HBR1 : [ G' ; ΔR ,, A' @ k1 ⊢[ lD ] BR @ k1' ])
    by (eapply wft_lconv; [exact (ctxconv_ty CA1 (i := lD) eq_refl HBRD) | apply lequiv_sym, Qg']).
  (* the body at the whnfs' codomains *)
  assert (HbL : [ G' ; ΔL ,, A @ k ⊢[ lC ] b : BL @ k' ]) by (eapply wf_conv; [exact Hb | apply eqty_sym, HB0BL]).
  assert (Hb'L : [ G' ; ΔL ,, A @ k ⊢[ lC ] b' : BL @ k' ]) by (eapply wf_conv; [exact Hb' | apply eqty_sym, HB0BL]).
  assert (Hb'R : [ G' ; ΔR ,, A' @ k ⊢[ lC ] b' : BR @ k' ]).
  { refine (ctxconv_tm CA (i := lC) eq_refl _). eapply wf_conv; [exact Hb' | apply eqty_sym, HB0BR]. }
  assert (Hb'R1 : [ G' ; ΔR ,, A' @ k1 ⊢[ lC ] b' : BR @ k1' ]).
  { eapply wf_lconv; [| apply lequiv_sym, Qg']. refine (ctxconv_tm CA1 (i := lC) eq_refl _).
    eapply wf_conv; [exact Hb' | apply eqty_sym, HB0BR]. }
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c HbL Hb'L Eb) Hl1c) as Hbb.
  pose proof (wf_ty_dnf HA) as NA. pose proof (wf_ty_dnf HA'R) as NA'.
  pose proof (wf_ty_dnf HBLD) as NBL. pose proof (wf_ty_dnf HBRk) as NBR.
  pose proof (wf_tm_dnf Hb) as Nb. pose proof (wf_tm_dnf Hb'R) as Nb'.
  (* the codes *)
  assert (HΠ' : [ G' ; ΔL ⊢[ lD ] tyPi k k' A BL @ lmax k k' ])
    by (apply wft_pi; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBLD]).
  assert (HΠΠ' : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ tyPi k k' A BL @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact Hkg | exact Hkg' | exact HAD | apply eqty_refl, HAD | exact HB0BL]).
  assert (HΠ'R : [ G' ; ΔL ⊢[ lD ] tyPi k k' A BL ≅ tyPi k1 k1' A' BR @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact Qg | exact Qg' | exact HAD | exact HAA | exact HBLBR]).
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] lam k k' A b : tyPi k k' A BL @ lmax k k' ])
    by (apply wf_lam; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HbL]).
  assert (HcL : [ G' ; ΔL ⊢[ lC ] lam k k' A b : TL @ kL ]).
  { eapply wf_lconv; [eapply wf_conv; [exact HcL0 |] | apply lequiv_sym, HkLg].
    exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) HΠΠ'). }
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : tyPi k1 k1' A' BR @ lmax k1 k1' ])
    by (apply wf_lam; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact Hb'R1]).
  pose proof (wf_tm_ty (i := lD) eq_refl (lift_tm (j := lD) HcR0 Hl1c)) as HΠR.
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] lam k1 k1' A' b' : tyPi k k' A BL @ lmax k k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qmg] | exact HΠ'R]. }
  assert (HTRΠ : [ G' ; ΔR ⊢[ lD ] TR ≅ tyPi k1 k1' A' BR @ lmax k k' ]).
  { refine (ctxconv_eqty HΔ (i := lD) eq_refl _).
    exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTR) (eqty_trans _ _ _ _ _ _ _ HΠΠ' HΠ'R)). }
  assert (HcR : [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : TR @ kR ]).
  { eapply wf_lconv; [eapply wf_conv; [eapply wf_lconv; [exact HcR0 | exact Qmg] | exact HTRΠ] | apply lequiv_sym, HkRg]. }
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (Ec : tm_leq (lam k k' A b) (lam k1 k1' A' b')) by (cbn; repeat split; assumption).
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL0.
  pose proof (box_rel_tm HΠ' Hwm HcL0 HcL0 (tm_leq_refl _)) as BΠ.
  pose proof (box_rel_tm HΠ' Hwm HcL0 HcRL Ec) as BΠ'.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR0.
  pose proof (box_rel_tm HΠR Hwm1 HcR0 HcR0 (tm_leq_refl _)) as BRR.
  (* the index reductions *)
  pose proof (tyred_lconv _ _ _ _ HWL (lequiv_sym _ _ _ HkLg)) as HWLk.
  pose proof (tyred_lconv _ _ _ _ HWR (lequiv_sym _ _ _ HkRg)) as HWRk.
  pose proof (eqty_wf_r (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWLk)) as HWL0.
  pose proof (eqty_wf_r (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWRk)) as HWR0.
  assert (HcLW : [ G' ; ΔL ⊢[ lC ] lam k k' A b : tyPi c1 c2 CL BL @ kL ])
    by (eapply wf_conv; [exact HcL | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HWLk)]).
  assert (HcRW : [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : tyPi c3 c4 CR BR @ kR ])
    by (eapply wf_conv; [exact HcR | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HWRk)]).
  pose proof (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_refl _ _ HwL) HΔL (eqc_refl _ _ _ HΔL)
             (tyred_eq _ _ _ _ _ _ HWLk) HWL0 BL0 (box_rel_tm HWL0 HwL HcLW HcLW (tm_leq_refl _))) as ML.
  pose proof (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
             G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR (lequiv_refl _ _ HwR) HΔR (eqc_refl _ _ _ HΔR)
             (tyred_eq _ _ _ _ _ _ HWRk) HWR0 BR0 (box_rel_tm HWR0 HwR HcRW HcRW (tm_leq_refl _))) as MR.
  (* the recursive calls *)
  pose proof (IHb BL BR HB0BL HB0BR) as IHb'.
  destruct (LRtm_escape IHA) as [Ha1 _]. destruct (LRtm_escape (LRtm_sym IHA)) as [Ha1' _].
  destruct (LRtm_escape IHb') as [Ha2 _]. destruct (LRtm_escape (LRtm_sym IHb')) as [Ha2' _].
  assert (X1 : LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k ΔL (boxT A))
                 (recTL k ΔL A) (recTR k1 ΔR A')).
  { refine (LRtm_conv_r IHA (LRty_sym _)).
    exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw Q HΔL HΔ (box_rel HΔL Hw HA HA' EA) (box_rel HΔR Hw1 HA'R1 HA'R1 (ty_leq_refl _))). }
  assert (X2 : LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' (ΔL ,, A @ k) BL (boxt b))
                 (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) k' (ΔL ,, A @ k) BL (boxt b)) (rectL k' (ΔL ,, A @ k) BL b) (rectR k1' (ΔR ,, A' @ k1) BR b')).
  { refine (LRtm_conv_r IHb' (LRty_sym _)).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             (kL := k') (kR := k1') Hw' Q' HΔLA CA1 HBLBR HBR1
             (box_rel_tm HBLD Hw' HbL Hb'L Eb) (box_rel_tm HBR1 Hw1' Hb'R1 Hb'R1 (tm_leq_refl _))). }
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHb') IHb') Hl2g') as X2r.
  (* the reducts *)
  set (xsL := recTL k ΔL A :: rectL k' (ΔL ,, A @ k) BL b :: nil). set (xsR := recTR k1 ΔR A' :: rectR k1' (ΔR ,, A' @ k1) BR b' :: nil).
  set (rL := ((usubst_tm (bs 11) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 11) (uext (k1 :: k1' :: nil) φ))⦃gext_s (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL (tyPi c1 c2 CL BL) (lam k k' A b) = Some rL)
    by (apply redt_lam_inst; first [exact (wf_tm_dnf (Hbs 11 ltac:(lia))) | exact Nσ | exact De | assumption
                                   | exact (wf_tm_dnf Ha1) | exact (wf_tm_dnf Ha2)]).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR (tyPi c3 c4 CR BR) (lam k1 k1' A' b') = Some rR)
    by (apply redt_lam_inst; first [exact (wf_tm_dnf (Hbs' 11 ltac:(lia))) | exact Nσ' | exact De' | assumption
                                   | exact (wf_tm_dnf Ha1') | exact (wf_tm_dnf Ha2')]).
  refine (rec_t_fin_lam HΔL HΔR HwL HwR HTLk HTRk HcL HcR HWLk HWRk HredL HredR ML MR _).
  pose proof De as De0. pose proof De' as De0'.
  refine (br_core 11 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) xsL xsR _ _ _ ltac:(lia) eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption) _
            (GS_lam EP EM Hσ HΔL HΔ HA HA'R HAA EA HBLD HBRk HBLBR HbL Hb'R Hbb Eb)
            (GS_lam EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HBR1 HBR1 (eqty_refl _ _ _ _ _ HBR1)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - intros [|[|i]]; unfold uext; cbn; [exact E' | exact E | apply leqv_refl].
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 2 4 Γ0 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) φ σ eq_refl eq_refl).
    rewrite (lvren_ush_uext' l1 2 (k :: k' :: nil) φ eq_refl), (lvren_ush_uext' l2 2 (k :: k' :: nil) φ eq_refl).
    apply SubRel_cons; [apply SubRel_cons; [exact He |] |].
    + rewrite (motT_wkb_inst' MT 2 4 0 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) nil φ σ e e),
              (motT_wkb_inst' MT 2 4 0 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) nil φ σ e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NBL)]. rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nb). exact X1.
    + rewrite (mott_wkb_inst' Mt 2 4 1 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) (recTL k ΔL A :: nil) φ σ e),
              (mott_wkb_inst' Mt 2 4 1 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) (recTR k1 ΔR A' :: nil) φ σ e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NBL)]. rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nb). exact X2.
  - cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst]. rewrite !gs_cext.
    rewrite (wkc_inst' 2 4 Γ0 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) φ σ' eq_refl eq_refl).
    rewrite (lvren_ush_uext' l1' 2 (k1 :: k1' :: nil) φ eq_refl), (lvren_ush_uext' l2' 2 (k1 :: k1' :: nil) φ eq_refl).
    apply SubRel_cons; [apply SubRel_cons; [exact He'r |] |].
    + rewrite (motT_wkb_inst' MT' 2 4 0 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) nil φ σ' e' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NBR)]. rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nb'). exact X1r.
    + rewrite (mott_wkb_inst' Mt' 2 4 1 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) (recTR k1 ΔR A' :: nil) φ σ' e')
        by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | lk_dnf_tac].
      inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NBR)]. rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nb'). exact X2r.
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 2 4 2 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) xsL φ σ e)
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | unfold xsL; lk_dnf_tac].
    inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NBL)]. rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nb).
    refine (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             _ HΠ' BL0 BΠ).
    eapply eqty_lconv; [exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) HΠΠ') | apply lequiv_sym, HkLg].
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt 2 4 2 (k :: k' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) xsR φ σ e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ] | unfold xsR; lk_dnf_tac].
    inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA) | exact (dnfty_nfty _ NBL)]. rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nb).
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hwm HkR HΔL HΔ (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HΠΠ') HTR) HTRk BΠ' BR0).
  - cbn [brRes]. rewrite (mott_wkb_inst' Mt' 2 4 2 (k1 :: k1' :: nil) (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) xsR φ σ' e')
      by first [reflexivity | apply gdnf_gext_s; [forall_tac | exact Nσ'] | unfold xsR; lk_dnf_tac].
    inst_cbn. rewrite ?subst_lshift0_ty by first [exact (dnfty_nfty _ NA') | exact (dnfty_nfty _ NBR)]. rewrite ?subst_lshift0 by exact (dnftm_nftm _ Nb').
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                          (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Qm) HΔR (eqc_refl _ _ _ HΔR)
                          _ HΠR BR0 BRR) Hl2g).
    eapply eqty_lconv; [exact HTRΠ | apply lequiv_sym, HkRg].
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2 2 (k :: k' :: nil) φ eq_refl). apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; cbn [br_nu br_ar Nat.ltb Nat.leb].
    rewrite (lvren_ush_uext' l2' 2 (k1 :: k1' :: nil) φ eq_refl). exact Hl2g.
Qed.


(** ** Neutral scrutinees: the motives and branches under their binders
    (M3_DESIGN.md E13, E14) *)

#[local] Instance LR_M_permRec : VPPerm (@lr_vp LRM) := vpM_perm EP EM.

Hypothesis (HG0 : [ ⊢ G_us G0 L' φ ]) (HΓ0 : [ G_us G0 L' φ ; ucsubst Γ0 φ ⊢[ lM ] ])
  (VΓT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) -> VCtxSM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ))
  (VΓt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) -> VCtxSM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ))
  (VΓbr : forall k, k < 13 -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VCtxSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) ψ)).

Lemma EP_MT : @geq_ty EM (recGT G') (recΓT Θ) MTL MTR (lvren (lvsubst l1 φ) (ush 1)).
Proof.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (VMT (S L') (uup φ) (usub_ok_uup _ _ _ Hφ)) as V.
  pose proof (VΓT (S L') (uup φ) (usub_ok_uup _ _ _ Hφ)) as VC.
  unfold G_us in V, VC. rewrite recGT_usubst, recΓT_usubst in V, VC. rewrite lvren_ush1_usubst in V.
  pose proof (GSubRel_uwkn EP EM (n := 1) HG0 Hσ) as X1.
  assert (HGr : [ ⊢ recGT G' ]) by exact (wf_recGT HG').
  pose proof (GSubRel_gup EP EM (D := gdCtx) X1 HGr eq_refl) as X2.
  change (guwkn 1 σ) with (guwk σ) in X2. change (guwkn 1 σ') with (guwk σ') in X2.
  pose proof (V _ _ _ X2 _ gwk_id (gwk_ok_id _)) as V'. cbn [gwa] in V'.
  pose proof (VC _ _ _ (GSubRel_refl_l EP EM X2) _ gwk_id (gwk_ok_id _)) as C. cbn [gwa] in C.
  rewrite (recΓT_gsubst _ _ Nσ) in V', C.
  pose proof (wf_ctx_lwf (gs_ctx EP EM Hσ HΓ0 compt_M)) as WΓ1.
  pose proof (SubRel_uwkn (n := 1) HG' WΓ1 He) as H1.
  pose proof (SubRel_gwkn (D := gdCtx) (Ds := nil) H1 HGr) as H2.
  pose proof (SubRel_cexts ((tyCTyp (cvar 0) (lvar 0), lzero) :: nil) _ _ _ _ H2 C
                ltac:(repeat constructor)) as H3.
  destruct (V' _ _ _ H3) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & Hg).
  exact Hg.
Qed.

Lemma EP_Mt : @geq_ty EM (recGt G') (recΓt Θ) MtL MtR (lvren (lvsubst l2 φ) (ush 1)).
Proof.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (VMt (S L') (uup φ) (usub_ok_uup _ _ _ Hφ)) as V.
  pose proof (VΓt (S L') (uup φ) (usub_ok_uup _ _ _ Hφ)) as VC.
  unfold G_us in V, VC. rewrite recGt_usubst, recΓt_usubst in V, VC. rewrite lvren_ush1_usubst in V.
  pose proof (GSubRel_uwkn EP EM (n := 1) HG0 Hσ) as X1.
  assert (HGr : [ ⊢ recGT G' ]) by exact (wf_recGT HG').
  assert (HGr' : [ ⊢ recGt G' ]) by exact (wf_recGt HG').
  pose proof (GSubRel_gup EP EM (D := gdCtx) X1 HGr eq_refl) as X2.
  pose proof (GSubRel_gup EP EM (D := gdTy (cvar 0) lD (lvar 0)) X2 HGr' eq_refl) as X3.
  change (guwkn 1 σ) with (guwk σ) in X3. change (guwkn 1 σ') with (guwk σ') in X3.
  pose proof (V _ _ _ X3 _ gwk_id (gwk_ok_id _)) as V'. cbn [gwa] in V'.
  pose proof (VC _ _ _ (GSubRel_refl_l EP EM X3) _ gwk_id (gwk_ok_id _)) as C. cbn [gwa] in C.
  rewrite (recΓt_gsubst _ _ Nσ) in V', C.
  pose proof (wf_ctx_lwf (gs_ctx EP EM Hσ HΓ0 compt_M)) as WΓ1.
  pose proof (SubRel_uwkn (n := 1) HG' WΓ1 He) as H1.
  pose proof (SubRel_gwkn (D := gdTy (cvar 0) lD (lvar 0)) (Ds := gdCtx :: nil) H1 HGr') as H2.
  pose proof (SubRel_cexts ((tyCTrm (cvar 1) (gv 0) (lvar 0), lzero) :: nil) _ _ _ _ H2 C
                ltac:(repeat constructor)) as H3.
  destruct (V' _ _ _ H3) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & Hg).
  exact Hg.
Qed.


Lemma EP_br k : k < 13 ->
  @geq_tm EM (brG k G') (brΓ k Θ (wrapMT MTL) (wrapMt MtL) (lvsubst l1 φ) (lvsubst l2 φ)) (bsL k) (bsR k)
    (brRes k (wrapMT MTL) (wrapMt MtL)) (brLv k (lvsubst l1 φ) (lvsubst l2 φ)).
Proof.
  intros Hk.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (usub_ok_uupn (br_nu k) _ _ _ Hφ) as Hψ.
  pose proof (VBr k Hk _ _ Hψ) as V. pose proof (VΓbr k Hk _ _ Hψ) as VC.
  unfold G_us in V, VC. rewrite (brG_usubst k G0 L' φ Hk) in V, VC.
  rewrite (brΓ_usubst k Γ0 _ _ l1 l2 φ Hk) in V, VC.
  rewrite (brRes_usubst k _ _ φ Hk), brLv_usubst in V.
  rewrite wrapMT_usubst, wrapMt_usubst in V, VC.
  (* the global substitution: [nu] fresh levels, then the branch's bindings *)
  pose proof (GSubRel_uwkn EP EM (n := br_nu k) HG0 Hσ) as X1.
  pose proof (GSubRel_gupn EP EM (brDecls k) X1 (closed_brDecls k Hk) (wf_brG HG' k Hk)) as X2.
  rewrite (brDecls_len k Hk) in X2.
  change (gupn (br_ng k) (guwkn (br_nu k) σ)) with (gbsub k σ) in X2.
  change (gupn (br_ng k) (guwkn (br_nu k) σ')) with (gbsub k σ') in X2.
  pose proof (V _ _ _ X2 _ gwk_id (gwk_ok_id _)) as V'. cbn [gwa] in V'.
  pose proof (VC _ _ _ (GSubRel_refl_l EP EM X2) _ gwk_id (gwk_ok_id _)) as C. cbn [gwa] in C.
  rewrite (brΓ_gsubst _ _ _ _ _ _ _ Hk Nσ), (brRes_gsubst _ _ _ _ Hk Nσ) in V'.
  rewrite (brΓ_gsubst _ _ _ _ _ _ _ Hk Nσ) in C.
  rewrite ?wrapMT_gsubst, ?wrapMt_gsubst in V', C.
  (* the local substitution: its fresh levels and bindings, then the recursive calls *)
  pose proof (wf_ctx_lwf (gs_ctx EP EM Hσ HΓ0 compt_M)) as WΓ1.
  pose proof (SubRel_uwkn (n := br_nu k) HG' WΓ1 He) as H1.
  destruct (brDecls_cons k Hk) as (D1 & Ds & ED).
  assert (HGb : [ ⊢ mkG (gL (gctx_uwk (br_nu k) G')) ((D1 :: Ds) ++ gΨ (gctx_uwk (br_nu k) G')) ]).
  { rewrite <- ED. exact (wf_brG HG' k Hk). }
  pose proof (SubRel_gwkn H1 HGb) as H2. rewrite <- ED, (brDecls_len k Hk) in H2.
  change (gwkn (br_ng k) (uwkn (br_nu k) e)) with (bsub k e) in H2.
  change (gwkn (br_ng k) (uwkn (br_nu k) e')) with (bsub k e') in H2.
  unfold brΓ in C.
  pose proof (SubRel_cexts _ _ _ _ _ H2 C (brLocs_lwf k _ _ _ _ _ Hk
                (lwf_lvren _ _ _ _ (uren_ok_ush _ _) (proj1 HrbL))
                (lwf_lvren _ _ _ _ (uren_ok_ush _ _) (proj1 (proj2 HrbL))))) as H3.
  rewrite (brLocs_subst _ _ _ _ _ _ Hk De), (brLocs_len _ _ _ _ _ Hk) in H3.
  pose proof (V' _ _ _ H3) as Y. rewrite (brRes_subst _ _ _ _ Hk De) in Y.
  exact (LRtm_geq Y).
Qed.

End Rec.
