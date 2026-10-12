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
Proof using Hl Hrb HΔ.
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
Proof using Hl Hrb HΔ.
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
Proof using HT Hl Hrb HΔ.
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
Proof using HT Hl Hrb HΔ.
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
Proof using Hl Hrb HΔ.
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
Proof using . exact (RecExt.GSubRel_ext EP EM). Qed.

(** Extension by a context, one on each side, related at P. *)
Lemma GSubRel_ctx1 {G' G σ σ' Δ Δ'} : GSubRel G' G σ σ' -> [ G' ; Δ ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ ≅ Δ' ] ->
  GSubRel G' (gext G gdCtx) (gext_s (GCtx Δ :: nil) σ) (gext_s (GCtx Δ' :: nil) σ').
Proof using ELM ELP.
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
Proof using ELM ELP.
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
Proof using ELM ELP HEL HMT HMT' He Hl1 Hσ Hφ VMT VMT' VΓ.
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
Proof using ELM ELP HEL HMt HMt' He Hl2 Hσ Hφ VMt VMt' VΓ.
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
(** Normal forms of payloads and calls, read off a typing or a relation
    in the context. *)
Ltac dnf_any :=
  cbn [dnfo];
  first [ assumption | exact I
        | match goal with
          | |- dnfctx ?Δ => match goal with H : [ _ ; Δ ⊢[ _ ] ] |- _ => exact (wf_ctx_dnf H) end
          | |- dnfty ?A => match goal with H : [ _ ; _ ⊢[ _ ] A @ _ ] |- _ => exact (wf_ty_dnf H) end
          | |- dnftm ?x => match goal with
                           | H : [ _ ; _ ⊢[ _ ] x : _ @ _ ] |- _ => exact (wf_tm_dnf H)
                           | H : @LRtm _ _ _ _ _ _ _ x _ |- _ => exact (wf_tm_dnf (proj1 (LRtm_escape H)))
                           | H : @LRtm _ _ _ _ _ _ _ _ x |- _ => exact (wf_tm_dnf (proj1 (LRtm_escape (LRtm_sym H))))
                           end
          end
        (* a call, up to the unfolding of the recursor's bundle *)
        | solve [ eapply wf_tm_dnf, proj1, LRtm_escape; eassumption
                | eapply wf_tm_dnf, proj1, LRtm_escape, LRtm_sym; eassumption ] ].
Ltac forall_tac := solve [repeat (apply Forall_cons; [dnf_any|]); apply Forall_nil].

Section Red.
Variables (MT Mt : ty) (bs : nat -> tm) (φ : nat -> lvl) (σ : gsub) (e : lsub) (l1 l2 : lvl).
Local Notation rb := (mkrb ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))])
                          ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))])
                          (fun k => ((usubst_tm (bs k) (uupn (br_nu k) φ))⦃gbsub k σ⦄)[lliftn (br_nl k) (bsub k e)])).

Lemma redT_nat_inst k Δ : dnftm (bs 0) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redT l1 l2 rb k Δ tyNat = Some (((usubst_tm (bs 0) (uext nil φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using .
  intros Hb Hσ He HΔ. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity.
Qed.

Lemma redT_pi_inst k0 Δ k k' A B : dnftm (bs 1) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A -> dnfty B ->
  dnftm (elimT l1 l2 rb k Δ (boxT A)) -> dnftm (elimT l1 l2 rb k' (cext Δ A k) (boxT B)) ->
  redT l1 l2 rb k0 Δ (tyPi k k' A B) =
  Some (((usubst_tm (bs 1) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: nil) σ⦄)
          [lext (elimT l1 l2 rb k Δ (boxT A) :: elimT l1 l2 rb k' (cext Δ A k) (boxT B) :: nil) e]).
Proof using .
  intros Hb Hσ He HΔ HA HB H1 H2. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity.
Qed.

Lemma redT_U_inst k0 Δ k : dnftm (bs 2) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redT l1 l2 rb k0 Δ (tyU k) =
  Some (((usubst_tm (bs 2) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros Hb Hσ He HΔ. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redT_El_inst k0 Δ k t : dnftm (bs 3) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm t ->
  dnftm (elimt l1 l2 rb (lsuc k) Δ (tyU k) (boxt t)) ->
  redT l1 l2 rb k0 Δ (tyEl k t) =
  Some (((usubst_tm (bs 3) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTm t :: nil) σ⦄)
          [lext (elimt l1 l2 rb (lsuc k) Δ (tyU k) (boxt t) :: nil) e]).
Proof using . intros Hb Hσ He HΔ Ht H1. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** Term heads. *)
Local Notation rect k Δ T c := (elimt l1 l2 rb k Δ T (boxt c)).
Local Notation recT k Δ c := (elimT l1 l2 rb k Δ (boxT c)).

Lemma redt_var_inst k0 Δ T n : dnftm (bs 4) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty T ->
  redt l1 l2 rb k0 Δ T (var n) =
  Some (((usubst_tm (bs 4) (uext (k0 :: nil) φ))⦃gext_s (GCtx Δ :: GTy T :: GTm (var n) :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption | exact I]. reflexivity. Qed.

Lemma redt_nat_inst k0 Δ T : dnftm (bs 5) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T tmNat =
  Some (((usubst_tm (bs 5) (uext nil φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_pi_inst k0 Δ T k k' s0 t0 : dnftm (bs 6) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm s0 -> dnftm t0 ->
  dnftm (rect (lsuc k) Δ (tyU k) s0) -> dnftm (rect (lsuc k') (cext Δ (tyEl k s0) k) (tyU k') t0) ->
  redt l1 l2 rb k0 Δ T (tmPi k k' s0 t0) =
  Some (((usubst_tm (bs 6) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTm s0 :: GTm t0 :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s0 :: rect (lsuc k') (cext Δ (tyEl k s0) k) (tyU k') t0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_U_inst k0 Δ T k : dnftm (bs 7) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T (tmU k) =
  Some (((usubst_tm (bs 7) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_zero_inst k0 Δ T : dnftm (bs 8) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T zero =
  Some (((usubst_tm (bs 8) (uext nil φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_succ_inst k0 Δ T t0 : dnftm (bs 9) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm t0 ->
  dnftm (rect lzero Δ tyNat t0) ->
  redt l1 l2 rb k0 Δ T (succ t0) =
  Some (((usubst_tm (bs 9) (uext nil φ))⦃gext_s (GCtx Δ :: GTm t0 :: nil) σ⦄)[lext (rect lzero Δ tyNat t0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_natrec_inst k0 Δ T k M s0 z0 t0 : dnftm (bs 10) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty M -> dnftm s0 -> dnftm z0 -> dnftm t0 ->
  dnftm (recT k (cext Δ tyNat lzero) M) -> dnftm (rect k Δ (subst_ty M (lsingle zero)) s0) ->
  dnftm (rect k (cext (cext Δ tyNat lzero) M k) (subst_ty M lsucc) z0) -> dnftm (rect lzero Δ tyNat t0) ->
  redt l1 l2 rb k0 Δ T (natrec k M s0 z0 t0) =
  Some (((usubst_tm (bs 10) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil) σ⦄)
          [lext (recT k (cext Δ tyNat lzero) M :: rect k Δ (subst_ty M (lsingle zero)) s0 ::
                 rect k (cext (cext Δ tyNat lzero) M k) (subst_ty M lsucc) z0 :: rect lzero Δ tyNat t0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_lam_inst k0 Δ k1 k2 C B k k' A b : dnftm (bs 11) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm b ->
  dnftm (recT k Δ A) -> dnftm (rect k' (cext Δ A k) B b) ->
  redt l1 l2 rb k0 Δ (tyPi k1 k2 C B) (lam k k' A b) =
  Some (((usubst_tm (bs 11) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) σ⦄)
          [lext (recT k Δ A :: rect k' (cext Δ A k) B b :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_app_inst k0 Δ T k k' A B f a : dnftm (bs 12) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm f -> dnftm a ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) ->
  dnftm (rect (lmax k k') Δ (tyPi k k' A B) f) -> dnftm (rect k Δ A a) ->
  redt l1 l2 rb k0 Δ T (app f k k' A B a) =
  Some (((usubst_tm (bs 12) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: rect (lmax k k') Δ (tyPi k k' A B) f :: rect k Δ A a :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** Heather's extension branches (M8d). *)
Lemma redT_sig_inst k0 Δ k k' A B : dnftm (bs 13) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A -> dnfty B ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) ->
  redT l1 l2 rb k0 Δ (tySig k k' A B) =
  Some (((usubst_tm (bs 13) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redT_unit_inst k0 Δ k : dnftm (bs 14) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redT l1 l2 rb k0 Δ (tyUnit k) =
  Some (((usubst_tm (bs 14) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codesig_inst k0 Δ T k k' s0 t0 : dnftm (bs 15) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm s0 -> dnftm t0 ->
  dnftm (rect (lsuc k) Δ (tyU k) s0) -> dnftm (rect (lsuc k') (cext Δ (tyEl k s0) k) (tyU k') t0) ->
  redt l1 l2 rb k0 Δ T (tmSig k k' s0 t0) =
  Some (((usubst_tm (bs 15) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTm s0 :: GTm t0 :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s0 :: rect (lsuc k') (cext Δ (tyEl k s0) k) (tyU k') t0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_pair_inst k0 Δ T k k' A B a b : dnftm (bs 16) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm a -> dnftm b ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) ->
  dnftm (rect k Δ A a) -> dnftm (rect k' Δ (subst_ty B (lsingle a)) b) ->
  redt l1 l2 rb k0 Δ T (tmPair k k' A B a b) =
  Some (((usubst_tm (bs 16) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm b :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: rect k Δ A a :: rect k' Δ (subst_ty B (lsingle a)) b :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_fst_inst k0 Δ T k k' A B p : dnftm (bs 17) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm p ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) -> dnftm (rect (lmax k k') Δ (tySig k k' A B) p) ->
  redt l1 l2 rb k0 Δ T (tmFst k k' A B p) =
  Some (((usubst_tm (bs 17) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm p :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: rect (lmax k k') Δ (tySig k k' A B) p :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_snd_inst k0 Δ T k k' A B p : dnftm (bs 18) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm p ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) -> dnftm (rect (lmax k k') Δ (tySig k k' A B) p) ->
  redt l1 l2 rb k0 Δ T (tmSnd k k' A B p) =
  Some (((usubst_tm (bs 18) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm p :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: rect (lmax k k') Δ (tySig k k' A B) p :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codeunit_inst k0 Δ T k : dnftm (bs 19) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T (tmUnit k) =
  Some (((usubst_tm (bs 19) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_triv_inst k0 Δ T k : dnftm (bs 20) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T (tmTriv k) =
  Some (((usubst_tm (bs 20) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redT_id_inst k0 Δ k A a b : dnftm (bs 21) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnftm a -> dnftm b ->
  dnftm (recT k Δ A) -> dnftm (rect k Δ A a) -> dnftm (rect k Δ A b) ->
  redT l1 l2 rb k0 Δ (tyId k A a b) =
  Some (((usubst_tm (bs 21) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil) σ⦄)
          [lext (recT k Δ A :: rect k Δ A a :: rect k Δ A b :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codeid_inst k0 Δ T k s0 t0 u0 : dnftm (bs 22) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnftm s0 -> dnftm t0 -> dnftm u0 ->
  dnftm (rect (lsuc k) Δ (tyU k) s0) -> dnftm (rect k Δ (tyEl k s0) t0) -> dnftm (rect k Δ (tyEl k s0) u0) ->
  redt l1 l2 rb k0 Δ T (tmId k s0 t0 u0) =
  Some (((usubst_tm (bs 22) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTm s0 :: GTm t0 :: GTm u0 :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s0 :: rect k Δ (tyEl k s0) t0 :: rect k Δ (tyEl k s0) u0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_refl_inst k0 Δ T k A a : dnftm (bs 23) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnftm a -> dnftm (recT k Δ A) -> dnftm (rect k Δ A a) ->
  redt l1 l2 rb k0 Δ T (tmRefl k A a) =
  Some (((usubst_tm (bs 23) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTm a :: nil) σ⦄)
          [lext (recT k Δ A :: rect k Δ A a :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_J_inst k0 Δ T k k' A a M c u e0 : dnftm (bs 24) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnftm a -> dnfty M -> dnftm c -> dnftm u -> dnftm e0 ->
  dnftm (recT k Δ A) -> dnftm (rect k Δ A a) ->
  dnftm (recT k' (cext (cext Δ A k) (tyId k A⟨↑⟩ a⟨↑⟩ (var 0)) k) M) ->
  dnftm (rect k' Δ (subst_ty M (lsingle2 a (tmRefl k A a))) c) ->
  dnftm (rect k Δ A u) -> dnftm (rect k Δ (tyId k A a u) e0) ->
  redt l1 l2 rb k0 Δ T (tmJ k k' A a M c u e0) =
  Some (((usubst_tm (bs 24) (uext (k :: k' :: nil) φ))
           ⦃gext_s (GCtx Δ :: GTy A :: GTm a :: GTy M :: GTm c :: GTm u :: GTm e0 :: nil) σ⦄)
          [lext (recT k Δ A :: rect k Δ A a :: recT k' (cext (cext Δ A k) (tyId k A⟨↑⟩ a⟨↑⟩ (var 0)) k) M
                 :: rect k' Δ (subst_ty M (lsingle2 a (tmRefl k A a))) c
                 :: rect k Δ A u :: rect k Δ (tyId k A a u) e0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** Strict equality (M10c), as the identity type and the unit type. *)
Lemma redT_seq_inst k0 Δ k A a b : dnftm (bs 25) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnftm a -> dnftm b ->
  dnftm (recT k Δ A) -> dnftm (rect k Δ A a) -> dnftm (rect k Δ A b) ->
  redT l1 l2 rb k0 Δ (tySEq k A a b) =
  Some (((usubst_tm (bs 25) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil) σ⦄)
          [lext (recT k Δ A :: rect k Δ A a :: rect k Δ A b :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codeseq_inst k0 Δ T k s0 t0 u0 : dnftm (bs 26) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnftm s0 -> dnftm t0 -> dnftm u0 ->
  dnftm (rect (lsuc k) Δ (tyU k) s0) -> dnftm (rect k Δ (tyEl k s0) t0) -> dnftm (rect k Δ (tyEl k s0) u0) ->
  redt l1 l2 rb k0 Δ T (tmSEq k s0 t0 u0) =
  Some (((usubst_tm (bs 26) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTm s0 :: GTm t0 :: GTm u0 :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s0 :: rect k Δ (tyEl k s0) t0 :: rect k Δ (tyEl k s0) u0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redT_sempty_inst k0 Δ k : dnftm (bs 27) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redT l1 l2 rb k0 Δ (tySEmpty k) =
  Some (((usubst_tm (bs 27) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codesempty_inst k0 Δ T k : dnftm (bs 28) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T (tmSEmpty k) =
  Some (((usubst_tm (bs 28) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_srefl_inst k0 Δ T k A a : dnftm (bs 29) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnftm a -> dnftm (recT k Δ A) -> dnftm (rect k Δ A a) ->
  redt l1 l2 rb k0 Δ T (srefl k A a) =
  Some (((usubst_tm (bs 29) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTm a :: nil) σ⦄)
          [lext (recT k Δ A :: rect k Δ A a :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** The motive's level first, as the branch binds it. *)
Lemma redt_elimSEmpty_inst k0 Δ T k k' M e0 : dnftm (bs 30) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty M -> dnftm e0 -> dnftm (recT k' Δ M) -> dnftm (rect k Δ (tySEmpty k) e0) ->
  redt l1 l2 rb k0 Δ T (elimSEmpty k k' M e0) =
  Some (((usubst_tm (bs 30) (uext (k' :: k :: nil) φ))⦃gext_s (GCtx Δ :: GTy M :: GTm e0 :: nil) σ⦄)
          [lext (recT k' Δ M :: rect k Δ (tySEmpty k) e0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** The empty type and binary sums (M12c). *)
Lemma redT_empty_inst k0 Δ k : dnftm (bs 31) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redT l1 l2 rb k0 Δ (tyEmpty k) =
  Some (((usubst_tm (bs 31) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codeempty_inst k0 Δ T k : dnftm (bs 32) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  redt l1 l2 rb k0 Δ T (tmEmpty k) =
  Some (((usubst_tm (bs 32) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext nil e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_elimEmpty_inst k0 Δ T k k' M t : dnftm (bs 33) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty M -> dnftm t -> dnftm (recT k (cext Δ (tyEmpty k') k') M) -> dnftm (rect k' Δ (tyEmpty k') t) ->
  redt l1 l2 rb k0 Δ T (elimEmpty k k' M t) =
  Some (((usubst_tm (bs 33) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy M :: GTm t :: nil) σ⦄)
          [lext (recT k (cext Δ (tyEmpty k') k') M :: rect k' Δ (tyEmpty k') t :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redT_sum_inst k0 Δ k k' A B : dnftm (bs 34) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A -> dnfty B ->
  dnftm (recT k Δ A) -> dnftm (recT k' Δ B) ->
  redT l1 l2 rb k0 Δ (tySum k k' A B) =
  Some (((usubst_tm (bs 34) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' Δ B :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codesum_inst k0 Δ T k k' s0 t0 : dnftm (bs 35) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm s0 -> dnftm t0 ->
  dnftm (rect (lsuc k) Δ (tyU k) s0) -> dnftm (rect (lsuc k') Δ (tyU k') t0) ->
  redt l1 l2 rb k0 Δ T (tmSum k k' s0 t0) =
  Some (((usubst_tm (bs 35) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTm s0 :: GTm t0 :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s0 :: rect (lsuc k') Δ (tyU k') t0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_inl_inst k0 Δ T k k' A B a : dnftm (bs 36) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm a -> dnftm (recT k Δ A) -> dnftm (recT k' Δ B) -> dnftm (rect k Δ A a) ->
  redt l1 l2 rb k0 Δ T (tmInl k k' A B a) =
  Some (((usubst_tm (bs 36) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm a :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' Δ B :: rect k Δ A a :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_inr_inst k0 Δ T k k' A B b : dnftm (bs 37) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm b -> dnftm (recT k Δ A) -> dnftm (recT k' Δ B) -> dnftm (rect k' Δ B b) ->
  redt l1 l2 rb k0 Δ T (tmInr k k' A B b) =
  Some (((usubst_tm (bs 37) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' Δ B :: rect k' Δ B b :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_case_inst k0 Δ T k k' k'' A B M c1 c2 t : dnftm (bs 38) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnfty M -> dnftm c1 -> dnftm c2 -> dnftm t ->
  dnftm (recT k Δ A) -> dnftm (recT k' Δ B) -> dnftm (recT k'' (cext Δ (tySum k k' A B) (lmax k k')) M) ->
  dnftm (rect k'' (cext Δ A k) (subst_ty M⟨rlift ↑⟩ (lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0)))) c1) ->
  dnftm (rect k'' (cext Δ B k') (subst_ty M⟨rlift ↑⟩ (lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0)))) c2) ->
  dnftm (rect (lmax k k') Δ (tySum k k' A B) t) ->
  redt l1 l2 rb k0 Δ T (tmCase k k' k'' A B M c1 c2 t) =
  Some (((usubst_tm (bs 38) (uext (k :: k' :: k'' :: nil) φ))
           ⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTy M :: GTm c1 :: GTm c2 :: GTm t :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' Δ B :: recT k'' (cext Δ (tySum k k' A B) (lmax k k')) M
                 :: rect k'' (cext Δ A k) (subst_ty M⟨rlift ↑⟩ (lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0)))) c1
                 :: rect k'' (cext Δ B k') (subst_ty M⟨rlift ↑⟩ (lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0)))) c2
                 :: rect (lmax k k') Δ (tySum k k' A B) t :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** W (M13b). *)
Lemma redT_W_inst k0 Δ k k' A B : dnftm (bs 39) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A -> dnfty B ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) ->
  redT l1 l2 rb k0 Δ (tyW k k' A B) =
  Some (((usubst_tm (bs 39) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codeW_inst k0 Δ T k k' s0 t0 : dnftm (bs 40) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm s0 -> dnftm t0 ->
  dnftm (rect (lsuc k) Δ (tyU k) s0) -> dnftm (rect (lsuc k') (cext Δ (tyEl k s0) k) (tyU k') t0) ->
  redt l1 l2 rb k0 Δ T (tmW k k' s0 t0) =
  Some (((usubst_tm (bs 40) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTm s0 :: GTm t0 :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s0 :: rect (lsuc k') (cext Δ (tyEl k s0) k) (tyU k') t0 :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_sup_inst k0 Δ T k k' A B a f : dnftm (bs 41) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnftm a -> dnftm f ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) -> dnftm (rect k Δ A a) ->
  dnftm (rect (lmax k' (lmax k k')) Δ (tyPi k' (lmax k k') (subst_ty B (lsingle a)) (tyW k k' A B)⟨↑⟩) f) ->
  redt l1 l2 rb k0 Δ T (tmSup k k' A B a f) =
  Some (((usubst_tm (bs 41) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm f :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: rect k Δ A a
                 :: rect (lmax k' (lmax k k')) Δ (tyPi k' (lmax k k') (subst_ty B (lsingle a)) (tyW k k' A B)⟨↑⟩) f :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_elimW_inst k0 Δ T k k' k'' A B M c t : dnftm (bs 42) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty B -> dnfty M -> dnftm c -> dnftm t ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ A k) B) -> dnftm (recT k'' (cext Δ (tyW k k' A B) (lmax k k')) M) ->
  dnftm (rect k'' (cext (cext (cext Δ A k) (wfty k k' A B) (lmax k' (lmax k k'))) (wihty k k' k'' A B M) (lmax k' k''))
            (wstepty k k' A B M) c) ->
  dnftm (rect (lmax k k') Δ (tyW k k' A B) t) ->
  redt l1 l2 rb k0 Δ T (tmElimW k k' k'' A B M c t) =
  Some (((usubst_tm (bs 42) (uext (k :: k' :: k'' :: nil) φ))
           ⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTy M :: GTm c :: GTm t :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ A k) B :: recT k'' (cext Δ (tyW k k' A B) (lmax k k')) M
                 :: rect k'' (cext (cext (cext Δ A k) (wfty k k' A B) (lmax k' (lmax k k'))) (wihty k k' k'' A B M) (lmax k' k''))
                      (wstepty k k' A B M) c
                 :: rect (lmax k k') Δ (tyW k k' A B) t :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** Vec and Fin (M14b): the length's call is a term call at [Nat]. *)
Lemma redT_vec_inst k0 Δ k A n : dnftm (bs 43) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A -> dnftm n ->
  dnftm (recT k Δ A) -> dnftm (rect lzero Δ tyNat n) ->
  redT l1 l2 rb k0 Δ (tyVec k A n) =
  Some (((usubst_tm (bs 43) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTm n :: nil) σ⦄)
          [lext (recT k Δ A :: rect lzero Δ tyNat n :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codevec_inst k0 Δ T k s0 n : dnftm (bs 44) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm s0 -> dnftm n ->
  dnftm (rect (lsuc k) Δ (tyU k) s0) -> dnftm (rect lzero Δ tyNat n) ->
  redt l1 l2 rb k0 Δ T (tmVec k s0 n) =
  Some (((usubst_tm (bs 44) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTm s0 :: GTm n :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s0 :: rect lzero Δ tyNat n :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redT_fin_inst k0 Δ n : dnftm (bs 45) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm n ->
  dnftm (rect lzero Δ tyNat n) ->
  redT l1 l2 rb k0 Δ (tyFin n) =
  Some (((usubst_tm (bs 45) (uext nil φ))⦃gext_s (GCtx Δ :: GTm n :: nil) σ⦄)[lext (rect lzero Δ tyNat n :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codefin_inst k0 Δ T n : dnftm (bs 46) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm n ->
  dnftm (rect lzero Δ tyNat n) ->
  redt l1 l2 rb k0 Δ T (tmFin n) =
  Some (((usubst_tm (bs 46) (uext nil φ))⦃gext_s (GCtx Δ :: GTm n :: nil) σ⦄)[lext (rect lzero Δ tyNat n :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

(** Finitary well-founded trees (M15b): the arity's call is a term call at
    [Nat] under the shape. *)
Lemma redT_wf_inst k0 Δ k A N : dnftm (bs 47) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A -> dnftm N ->
  dnftm (recT k Δ A) -> dnftm (rect lzero (cext Δ A k) tyNat N) ->
  redT l1 l2 rb k0 Δ (tyWf k A N) =
  Some (((usubst_tm (bs 47) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTm N :: nil) σ⦄)
          [lext (recT k Δ A :: rect lzero (cext Δ A k) tyNat N :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codewf_inst k0 Δ T k s n : dnftm (bs 48) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm s -> dnftm n ->
  dnftm (rect (lsuc k) Δ (tyU k) s) -> dnftm (rect lzero (cext Δ (tyEl k s) k) tyNat n) ->
  redt l1 l2 rb k0 Δ T (tmWf k s n) =
  Some (((usubst_tm (bs 48) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTm s :: GTm n :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s :: rect lzero (cext Δ (tyEl k s) k) tyNat n :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_supf_inst k0 Δ T k A N a cs : dnftm (bs 49) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnftm N -> dnftm a -> dnftm cs ->
  dnftm (recT k Δ A) -> dnftm (rect lzero (cext Δ A k) tyNat N) -> dnftm (rect k Δ A a) ->
  dnftm (rect k Δ (tyVec k (tyWf k A N) (subst_tm N (lsingle a))) cs) ->
  redt l1 l2 rb k0 Δ T (tmSupf k A N a cs) =
  Some (((usubst_tm (bs 49) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTm N :: GTm a :: GTm cs :: nil) σ⦄)
          [lext (recT k Δ A :: rect lzero (cext Δ A k) tyNat N :: rect k Δ A a
                 :: rect k Δ (tyVec k (tyWf k A N) (subst_tm N (lsingle a))) cs :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_elimWf_inst k0 Δ T k k' A N M c t : dnftm (bs 50) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnftm N -> dnfty M -> dnftm c -> dnftm t ->
  dnftm (recT k Δ A) -> dnftm (rect lzero (cext Δ A k) tyNat N) -> dnftm (recT k' (cext Δ (tyWf k A N) k) M) ->
  dnftm (rect k' (cext (cext (cext Δ A k) (wfcsty k A N) k) (wfihty k k' A N M) (lmax lzero k'))
            (wfstepty k A N M) c) ->
  dnftm (rect k Δ (tyWf k A N) t) ->
  redt l1 l2 rb k0 Δ T (tmElimWf k k' A N M c t) =
  Some (((usubst_tm (bs 50) (uext (k :: k' :: nil) φ))
           ⦃gext_s (GCtx Δ :: GTy A :: GTm N :: GTy M :: GTm c :: GTm t :: nil) σ⦄)
          [lext (recT k Δ A :: rect lzero (cext Δ A k) tyNat N :: recT k' (cext Δ (tyWf k A N) k) M
                 :: rect k' (cext (cext (cext Δ A k) (wfcsty k A N) k) (wfihty k k' A N M) (lmax lzero k'))
                      (wfstepty k A N M) c
                 :: rect k Δ (tyWf k A N) t :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

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
  cbn [length Nat.ltb Nat.leb Nat.sub nth lvsubst ucsubst usubst_tm usubst_ty ulsubst gcsubst gsubst_tm gsubst_ty glsubst pctx pty ptm subst_tm subst_ty lcomp gsubst GSubst_tm GSubst_ty GSubst_ctx subst Subst_tm Subst_ty lext fold_left llk lcons'].

Ltac inst_cbn_in H := unfold uext, gext_s, gv, gu in H; try unfold lsingle in H; try unfold lsucc in H;
  cbn [length Nat.ltb Nat.leb Nat.sub nth lvsubst ucsubst usubst_tm usubst_ty ulsubst gcsubst gsubst_tm gsubst_ty glsubst pctx pty ptm subst_tm subst_ty lcomp gsubst GSubst_tm GSubst_ty GSubst_ctx subst Subst_tm Subst_ty lext fold_left llk lcons'] in H.

Lemma subst_liftshift_ty (T : ty) : T[lcons (lshift 2) (var 0)] = T⟨rlift ↑⟩.
Proof. rewrite ren_as_r2l_ty. reflexivity. Qed.

(** A normaliser for [elimW]'s step telescope (M13b): renamings as
    substitutions, substitutions fused, the composite computed. *)
Lemma rs_ty_raw (T : ty) r : ren_ty T r = subst_ty T (r2l r).
Proof. exact (ren_as_r2l_ty T r). Qed.
Lemma rs_tm_raw (t : tm) r : ren_tm t r = subst_tm t (r2l r).
Proof. exact (ren_as_r2l t r). Qed.
Lemma ss_ty_raw (T : ty) d d' : subst_ty (subst_ty T d) d' = subst_ty T (lcomp d d').
Proof. exact (subst_subst_ty T d d' (lcomp d d') (fun n => llk_lcomp d d' n)). Qed.
Lemma ss_tm_raw (t : tm) d d' : subst_tm (subst_tm t d) d' = subst_tm t (lcomp d d').
Proof. exact (subst_subst t d d' (lcomp d d') (fun n => llk_lcomp d d' n)). Qed.
Ltac snorm := repeat progress (
  cbn [ren Ren_ty Ren_tm Ren_lsub subst Subst_ty Subst_tm Subst_lsub ren_ty ren_tm lren r2l rdrop rshift1 rlift rup
       lcons' rlk subst_ty subst_tm lcomp lnorm ldrop llift llk lsingle Nat.eqb Nat.add];
  rewrite ?rs_ty_raw, ?rs_tm_raw, ?ss_ty_raw, ?ss_tm_raw).

(** [elimW]'s telescope under universe and global substitution (M13b), in
    the raw forms [cbn] exposes in the calls' scopes. *)
Lemma gss_ty_raw (T : ty) d σ : gsubst_ty (subst_ty T d) σ = subst_ty (gsubst_ty T σ) (glsubst d σ).
Proof. exact (gsubst_subst_ty T d σ). Qed.
Lemma grs_ty_raw (T : ty) r σ : gsubst_ty (ren_ty T r) σ = ren_ty (gsubst_ty T σ) r.
Proof. exact (gsubst_ren_ty T r σ). Qed.
Lemma grs_tm_raw (t : tm) r σ : gsubst_tm (ren_tm t r) σ = ren_tm (gsubst_tm t σ) r.
Proof. exact (gsubst_ren t r σ). Qed.
Ltac tel_push := repeat progress (
  cbn [usubst_ty usubst_tm lvsubst ulsubst gsubst_ty gsubst_tm glsubst lsingle lcons'];
  rewrite ?usubst_ren_ty', ?usubst_ren', ?usubst_subst_ty', ?gss_ty_raw, ?grs_ty_raw, ?grs_tm_raw).
Lemma us_wfty l l' (A B : ty) φ :
  usubst_ty (wfty l l' A B) φ = wfty (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma us_wihty l l' l'' (A B M : ty) φ :
  usubst_ty (wihty l l' l'' A B M) φ
  = wihty (lvsubst l φ) (lvsubst l' φ) (lvsubst l'' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_ty M φ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma us_wstepty l l' (A B M : ty) φ :
  usubst_ty (wstepty l l' A B M) φ = wstepty (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_ty M φ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma gs_wfty l l' (A B : ty) σ : gsubst_ty (wfty l l' A B) σ = wfty l l' (gsubst_ty A σ) (gsubst_ty B σ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma gs_wihty l l' l'' (A B M : ty) σ :
  gsubst_ty (wihty l l' l'' A B M) σ = wihty l l' l'' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_ty M σ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma gs_wstepty l l' (A B M : ty) σ :
  gsubst_ty (wstepty l l' A B M) σ = wstepty l l' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_ty M σ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.

(** [elim_Wf]'s step telescope (M15b), likewise. *)
Lemma us_wfcsty l (A : ty) (N : tm) φ :
  usubst_ty (wfcsty l A N) φ = wfcsty (lvsubst l φ) (usubst_ty A φ) (usubst_tm N φ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma us_wfihty l l' (A : ty) (N : tm) (M : ty) φ :
  usubst_ty (wfihty l l' A N M) φ
  = wfihty (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_tm N φ) (usubst_ty M φ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma us_wfstepty l (A : ty) (N : tm) (M : ty) φ :
  usubst_ty (wfstepty l A N M) φ = wfstepty (lvsubst l φ) (usubst_ty A φ) (usubst_tm N φ) (usubst_ty M φ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma gs_wfcsty l (A : ty) (N : tm) σ : gsubst_ty (wfcsty l A N) σ = wfcsty l (gsubst_ty A σ) (gsubst_tm N σ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma gs_wfihty l l' (A : ty) (N : tm) (M : ty) σ :
  gsubst_ty (wfihty l l' A N M) σ = wfihty l l' (gsubst_ty A σ) (gsubst_tm N σ) (gsubst_ty M σ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.
Lemma gs_wfstepty l (A : ty) (N : tm) (M : ty) σ :
  gsubst_ty (wfstepty l A N M) σ = wfstepty l (gsubst_ty A σ) (gsubst_tm N σ) (gsubst_ty M σ).
Proof. tel_push. rewrite ?usubst_tmNth, ?gs_tmNth_raw; tel_push. reflexivity. Qed.

Lemma uc_ext Γ T l φ : ucsubst (Γ ,, T @ l) φ = ucsubst Γ φ ,, usubst_ty T φ @ lvsubst l φ.
Proof. reflexivity. Qed.
Lemma gc_ext Γ T l σ : gcsubst (Γ ,, T @ l) σ = gcsubst Γ σ ,, gsubst_ty T σ @ l.
Proof. reflexivity. Qed.

Lemma eqc_ext_inv {G i Γ Γ' A A' l l'} : [ G ⊢[ i ] Γ ,, A @ l ≅ Γ' ,, A' @ l' ] ->
  [ G ⊢[ i ] Γ ≅ Γ' ] /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] /\ lequiv (gL G) l l'.
Proof. intros H; inversion H; subst; refine (conj _ (conj _ (conj _ _))); assumption. Qed.

Section GS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

(** Images at a C-declaration over a context. *)
Lemma GSubRel_code {G' G σ1 σ2 D o1 o2 Δ1 Δ2 T1 T2 k} :
  GSubRel EP EM G' G σ1 σ2 -> gdecl_gsubst D σ1 = gdTy Δ1 lC k -> gdecl_gsubst D σ2 = gdTy Δ2 lC k ->
  o1 = GTy T1 -> o2 = GTy T2 ->
  [ G' ; Δ1 ⊢[ lC ] T1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] T2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] T1 ≅ T2 @ k ] -> ty_leq T1 T2 ->
  GSubRel EP EM G' (gext G D) (gcons σ1 o1) (gcons σ2 o2).
Proof using ELM ELP.
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
Proof using ELM ELP.
  intros Hσ HΔ HΔΔ.
  exact (GSubRel_ext EP EM (fun i => gext_s_one _ _ i) (fun i => gext_s_one _ _ i) (GSubRel_ctx1 EP EM Hσ HΔ HΔΔ)).
Qed.

Lemma GSubRel_code_tm {G' G σ1 σ2 D o1 o2 Δ1 Δ2 A1 A2 t1 t2 k} :
  GSubRel EP EM G' G σ1 σ2 -> gdecl_gsubst D σ1 = gdTm Δ1 lC A1 k -> gdecl_gsubst D σ2 = gdTm Δ2 lC A2 k ->
  o1 = GTm t1 -> o2 = GTm t2 ->
  [ G' ; Δ1 ⊢[ lC ] t1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] t2 : A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : A1 @ k ] ->
  tm_leq t1 t2 -> GSubRel EP EM G' (gext G D) (gcons σ1 o1) (gcons σ2 o2).
Proof using ELM ELP.
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
Proof using ELM ELP.
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
Proof using ELM ELP.
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
Proof using ELM ELP.
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

(** For [Π] (branch 1) and [Σ] (branch 13), which share their scope. *)
Lemma GS_pi {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 k1 k2} kb : brDecls kb = brDecls 1 -> br_nu kb = 2 ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k1 ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k1 ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k1 ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ,, A1 @ k1 ⊢[ lC ] B1 @ k2 ] -> [ G' ; Δ2 ,, A2 @ k1 ⊢[ lC ] B2 @ k2 ] ->
  [ G' ; Δ1 ,, A1 @ k1 ⊢[ lD ] B1 ≅ B2 @ k2 ] -> ty_leq B1 B2 ->
  GSubRel EP EM G' (G_us (brG kb G0) L' (uext (k1 :: k2 :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: nil) σ2).
Proof using ELM ELP.
  intros HD Hnu Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB.
  rewrite (G_us_brG_uext kb G0 L' φ (k1 :: k2 :: nil) (eq_sym Hnu)), HD.
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
    rewrite ?subst_lshift1_ty, ?subst_lshift1; reflexivity ].
Local Ltac lleC := unfold lle; cbn; lia.
(** [sup]'s children's type (M13b): the shifted [W] under the position binder. *)
Local Ltac elimW_decl_eq := cbn; unfold gv, gu; snorm;
  rewrite ?subst_lshift0_ty, ?subst_lshift0 by (apply dnfty_nfty || apply dnftm_nftm; assumption); snorm; reflexivity.
Local Ltac sup_decl_eq := cbn; unfold gv, gu; cbn;
  rewrite ?subst_lshift0_ty, ?subst_lshift0 by (apply dnfty_nfty || apply dnftm_nftm; assumption);
  rewrite ?subst_lshift1_ty, ?subst_lshift1, ?subst_liftshift_ty; reflexivity.

Lemma GS_ctx0 {G0 L' φ G' σ1 σ2 Δ1 Δ2} k ls : brDecls k = gdCtx :: nil -> length ls = br_nu k ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  GSubRel EP EM G' (G_us (brG k G0) L' (uext ls φ)) (gext_s (GCtx Δ1 :: nil) σ1) (gext_s (GCtx Δ2 :: nil) σ2).
Proof using ELM ELP.
  intros HD Hn Hσ HΔ1 HΔ. rewrite (G_us_brG_uext k G0 L' φ ls Hn), HD. exact (GSubRel_ctx1 EP EM Hσ HΔ1 HΔ).
Qed.

Lemma GS_var {G0 L' φ G' σ1 σ2 Δ1 Δ2 T1 T2 n k} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lD ] T1 @ k ] -> [ G' ; Δ2 ⊢[ lD ] T2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] T1 ≅ T2 @ k ] ->
  [ G' ; Δ1 ⊢[ lV ] var n : T1 @ k ] -> [ G' ; Δ2 ⊢[ lV ] var n : T2 @ k ] ->
  GSubRel EP EM G' (G_us (brG 4 G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy T1 :: GTm (var n) :: nil) σ1) (gext_s (GCtx Δ2 :: GTy T2 :: GTm (var n) :: nil) σ2).
Proof using ELM ELP.
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
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ Ht1 Ht2 Ht E.
  rewrite (G_us_brG_uext 9 G0 L' φ nil eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s2 _ _ _ i)) (fun i => eq_sym (gext_s2 _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext nil φ)) (brDecls 9) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (G_us G0 L' φ) gdCtx) (gdTm (cvar 0) lC tyNat lzero)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl Ht1 Ht2 Ht E); reflexivity.
Qed.

(** For the codes of [Π] (branch 6) and [Σ] (branch 15). *)
Lemma GS_pi' {G0 L' φ G' σ1 σ2 Δ1 Δ2 s1 s2 t1 t2 k k'} kb : brDecls kb = brDecls 6 -> br_nu kb = 2 ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] s1 : tyU k @ lsuc k ] -> [ G' ; Δ2 ⊢[ lC ] s2 : tyU k @ lsuc k ] ->
  [ G' ; Δ1 ⊢[ lD ] s1 ≅ s2 : tyU k @ lsuc k ] -> tm_leq s1 s2 ->
  [ G' ; Δ1 ,, tyEl k s1 @ k ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> [ G' ; Δ2 ,, tyEl k s2 @ k ⊢[ lC ] t2 : tyU k' @ lsuc k' ] ->
  [ G' ; Δ1 ,, tyEl k s1 @ k ⊢[ lD ] t1 ≅ t2 : tyU k' @ lsuc k' ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG kb G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTm s1 :: GTm t1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTm s2 :: GTm t2 :: nil) σ2).
Proof using ELM ELP.
  intros HD Hnu Hσ HΔ1 HΔ Hs1 Hs2 Hs Es Ht1 Ht2 Ht Et.
  pose proof (wf_tm_dnf Hs1) as N1. pose proof (wf_tm_dnf Hs2) as N2.
  rewrite (G_us_brG_uext kb G0 L' φ (k :: k' :: nil) (eq_sym Hnu)), HD.
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
Proof using ELM ELP.
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
Proof using ELM ELP.
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
Proof using ELM ELP.
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

Lemma GS_pair {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 a1 a2 b1 b2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lC ] B1 @ k' ] -> [ G' ; Δ2 ,, A2 @ k ⊢[ lC ] B2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] B1 ≅ B2 @ k' ] -> ty_leq B1 B2 ->
  [ G' ; Δ1 ⊢[ lC ] a1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] a2 : A2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] a1 ≅ a2 : A1 @ k ] -> tm_leq a1 a2 ->
  [ G' ; Δ1 ⊢[ lC ] b1 : B1[lsingle a1] @ k' ] -> [ G' ; Δ2 ⊢[ lC ] b2 : B2[lsingle a2] @ k' ] ->
  [ G' ; Δ1 ⊢[ lD ] b1 ≅ b2 : B1[lsingle a1] @ k' ] -> tm_leq b1 b2 ->
  GSubRel EP EM G' (G_us (brG 16 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: GTm a1 :: GTm b1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: GTm a2 :: GTm b2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB Ha1 Ha2 Ha Ea Hb1 Hb2 Hb Eb.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_ty_dnf HB1) as NB1. pose proof (wf_ty_dnf HB2) as NB2.
  pose proof (wf_tm_dnf Ha1) as Na1. pose proof (wf_tm_dnf Ha2) as Na2.
  rewrite (G_us_brG_uext 16 G0 L' φ (k :: k' :: nil) eq_refl).
  assert (E5 : forall a b c d f τ i, gext_s (a :: b :: c :: d :: f :: nil) τ i =
                                   gcons (gcons (gcons (gcons (gcons τ a) b) c) d) f i).
  { intros; unfold gext_s; destruct i as [|[|[|[|[|i]]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E5 _ _ _ _ _ _ i)) (fun i => eq_sym (E5 _ _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 16) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTy (cvar 1 ,, gv 0 @ k) lC k'))
       (gdTm (cvar 2) lC (gv 1) k)) (gdTm (cvar 3) lC (tyGvar 1 (lsingle (gu 0))) k')).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hb1 Hb2 Hb Eb); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ha1 Ha2 Ha Ea); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For the projections (branches 17 and 18, which share their scope). *)
Lemma GS_fst {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 p1 p2 k k'} kb : brDecls kb = brDecls 17 -> br_nu kb = 2 ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lC ] B1 @ k' ] -> [ G' ; Δ2 ,, A2 @ k ⊢[ lC ] B2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] B1 ≅ B2 @ k' ] -> ty_leq B1 B2 ->
  [ G' ; Δ1 ⊢[ lC ] p1 : tySig k k' A1 B1 @ lmax k k' ] -> [ G' ; Δ2 ⊢[ lC ] p2 : tySig k k' A2 B2 @ lmax k k' ] ->
  [ G' ; Δ1 ⊢[ lD ] p1 ≅ p2 : tySig k k' A1 B1 @ lmax k k' ] -> tm_leq p1 p2 ->
  GSubRel EP EM G' (G_us (brG kb G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: GTm p1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: GTm p2 :: nil) σ2).
Proof using ELM ELP.
  intros HD Hnu Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB Hp1 Hp2 Hp Ep.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_ty_dnf HB1) as NB1. pose proof (wf_ty_dnf HB2) as NB2.
  rewrite (G_us_brG_uext kb G0 L' φ (k :: k' :: nil) (eq_sym Hnu)), HD.
  assert (E4 : forall a b c d τ i, gext_s (a :: b :: c :: d :: nil) τ i = gcons (gcons (gcons (gcons τ a) b) c) d i).
  { intros; unfold gext_s; destruct i as [|[|[|[|i]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E4 _ _ _ _ _ i)) (fun i => eq_sym (E4 _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 17) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTy (cvar 1 ,, gv 0 @ k) lC k'))
       (gdTm (cvar 2) lC (tySig k k' (gv 1) (gv 0)) (lmax k k'))).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hp1 Hp2 Hp Ep); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [Id] (branch 21), its code (22) and [refl] (23), and for [sEq]'s
    (25, 26, 29), which share their scopes. *)
Lemma GS_id {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 a1 a2 b1 b2 k} kb : brDecls kb = brDecls 21 -> br_nu kb = 1 ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ⊢[ lC ] a1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] a2 : A2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] a1 ≅ a2 : A1 @ k ] -> tm_leq a1 a2 ->
  [ G' ; Δ1 ⊢[ lC ] b1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] b2 : A2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] b1 ≅ b2 : A1 @ k ] -> tm_leq b1 b2 ->
  GSubRel EP EM G' (G_us (brG kb G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTm a1 :: GTm b1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTm a2 :: GTm b2 :: nil) σ2).
Proof using ELM ELP.
  intros HD Hnu Hσ HΔ1 HΔ HA1 HA2 HA EA Ha1 Ha2 Ha Ea Hb1 Hb2 Hb Eb.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  rewrite (G_us_brG_uext kb G0 L' φ (k :: nil) (eq_sym Hnu)), HD.
  assert (E4 : forall a b c d τ i, gext_s (a :: b :: c :: d :: nil) τ i = gcons (gcons (gcons (gcons τ a) b) c) d i).
  { intros; unfold gext_s; destruct i as [|[|[|[|i]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E4 _ _ _ _ _ i)) (fun i => eq_sym (E4 _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: nil) φ)) (brDecls 21) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTm (cvar 1) lC (gv 0) k))
       (gdTm (cvar 2) lC (gv 1) k)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hb1 Hb2 Hb Eb); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ha1 Ha2 Ha Ea); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

Lemma GS_codeid {G0 L' φ G' σ1 σ2 Δ1 Δ2 s1 s2 t1 t2 u1 u2 k} kb : brDecls kb = brDecls 22 -> br_nu kb = 1 ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] s1 : tyU k @ lsuc k ] -> [ G' ; Δ2 ⊢[ lC ] s2 : tyU k @ lsuc k ] ->
  [ G' ; Δ1 ⊢[ lD ] s1 ≅ s2 : tyU k @ lsuc k ] -> tm_leq s1 s2 ->
  [ G' ; Δ1 ⊢[ lC ] t1 : tyEl k s1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] t2 : tyEl k s2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : tyEl k s1 @ k ] -> tm_leq t1 t2 ->
  [ G' ; Δ1 ⊢[ lC ] u1 : tyEl k s1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] u2 : tyEl k s2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] u1 ≅ u2 : tyEl k s1 @ k ] -> tm_leq u1 u2 ->
  GSubRel EP EM G' (G_us (brG kb G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTm s1 :: GTm t1 :: GTm u1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTm s2 :: GTm t2 :: GTm u2 :: nil) σ2).
Proof using ELM ELP.
  intros HD Hnu Hσ HΔ1 HΔ Hs1 Hs2 Hs Es Ht1 Ht2 Ht Et Hu1 Hu2 Hu Eu.
  pose proof (wf_tm_dnf Hs1) as Ns1. pose proof (wf_tm_dnf Hs2) as Ns2.
  rewrite (G_us_brG_uext kb G0 L' φ (k :: nil) (eq_sym Hnu)), HD.
  assert (E4 : forall a b c d τ i, gext_s (a :: b :: c :: d :: nil) τ i = gcons (gcons (gcons (gcons τ a) b) c) d i).
  { intros; unfold gext_s; destruct i as [|[|[|[|i]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E4 _ _ _ _ _ i)) (fun i => eq_sym (E4 _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: nil) φ)) (brDecls 22) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTm (cvar 0) lC (tyU k) (lsuc k)))
       (gdTm (cvar 1) lC (tyEl k (gu 0)) k)) (gdTm (cvar 2) lC (tyEl k (gu 1)) k)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hu1 Hu2 Hu Eu); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ht1 Ht2 Ht Et); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl Hs1 Hs2 Hs Es); reflexivity.
Qed.

Lemma GS_refl {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 a1 a2 k} kb : brDecls kb = brDecls 23 -> br_nu kb = 1 ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ⊢[ lC ] a1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] a2 : A2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] a1 ≅ a2 : A1 @ k ] -> tm_leq a1 a2 ->
  GSubRel EP EM G' (G_us (brG kb G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTm a1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTm a2 :: nil) σ2).
Proof using ELM ELP.
  intros HD Hnu Hσ HΔ1 HΔ HA1 HA2 HA EA Ha1 Ha2 Ha Ea.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  rewrite (G_us_brG_uext kb G0 L' φ (k :: nil) (eq_sym Hnu)), HD.
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: nil) φ)) (brDecls 23) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTm (cvar 1) lC (gv 0) k)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ha1 Ha2 Ha Ea); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [sEmpty]'s eliminator (branch 30): the motive's level first. *)
Lemma GS_elimSEmpty {G0 L' φ G' σ1 σ2 Δ1 Δ2 M1 M2 e1 e2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] M1 @ k' ] -> [ G' ; Δ2 ⊢[ lC ] M2 @ k' ] -> [ G' ; Δ1 ⊢[ lD ] M1 ≅ M2 @ k' ] -> ty_leq M1 M2 ->
  [ G' ; Δ1 ⊢[ lC ] e1 : tySEmpty k @ k ] -> [ G' ; Δ2 ⊢[ lC ] e2 : tySEmpty k @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] e1 ≅ e2 : tySEmpty k @ k ] -> tm_leq e1 e2 ->
  GSubRel EP EM G' (G_us (brG 30 G0) L' (uext (k' :: k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy M1 :: GTm e1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy M2 :: GTm e2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HM1 HM2 HM EM1 He1 He2 He Ee.
  pose proof (wf_ty_dnf HM1) as NM1. pose proof (wf_ty_dnf HM2) as NM2.
  rewrite (G_us_brG_uext 30 G0 L' φ (k' :: k :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k' :: k :: nil) φ)) (brDecls 30) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k')) (gdTm (cvar 1) lC (tySEmpty k) k)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl He1 He2 He Ee); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HM1 HM2 HM (fun _ => EM1)); reflexivity.
Qed.

(** For [J] (branch 24). *)
Lemma GS_J {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 a1 a2 M1 M2 c1 c2 u1 u2 e1 e2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ⊢[ lC ] a1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] a2 : A2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] a1 ≅ a2 : A1 @ k ] -> tm_leq a1 a2 ->
  [ G' ; Δ1 ,, A1 @ k ,, tyId k A1⟨↑⟩ a1⟨↑⟩ (var 0) @ k ⊢[ lC ] M1 @ k' ] ->
  [ G' ; Δ2 ,, A2 @ k ,, tyId k A2⟨↑⟩ a2⟨↑⟩ (var 0) @ k ⊢[ lC ] M2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ,, tyId k A1⟨↑⟩ a1⟨↑⟩ (var 0) @ k ⊢[ lD ] M1 ≅ M2 @ k' ] -> ty_leq M1 M2 ->
  [ G' ; Δ1 ⊢[ lC ] c1 : M1[lsingle2 a1 (tmRefl k A1 a1)] @ k' ] ->
  [ G' ; Δ2 ⊢[ lC ] c2 : M2[lsingle2 a2 (tmRefl k A2 a2)] @ k' ] ->
  [ G' ; Δ1 ⊢[ lD ] c1 ≅ c2 : M1[lsingle2 a1 (tmRefl k A1 a1)] @ k' ] -> tm_leq c1 c2 ->
  [ G' ; Δ1 ⊢[ lC ] u1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] u2 : A2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] u1 ≅ u2 : A1 @ k ] -> tm_leq u1 u2 ->
  [ G' ; Δ1 ⊢[ lC ] e1 : tyId k A1 a1 u1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] e2 : tyId k A2 a2 u2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] e1 ≅ e2 : tyId k A1 a1 u1 @ k ] -> tm_leq e1 e2 ->
  GSubRel EP EM G' (G_us (brG 24 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTm a1 :: GTy M1 :: GTm c1 :: GTm u1 :: GTm e1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTm a2 :: GTy M2 :: GTm c2 :: GTm u2 :: GTm e2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA Ha1 Ha2 Ha Ea HM1 HM2 HM EM1 Hc1 Hc2 Hc Ec Hu1 Hu2 Hu Eu He1 He2 He Ee.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_tm_dnf Ha1) as Na1. pose proof (wf_tm_dnf Ha2) as Na2.
  pose proof (wf_ty_dnf HM1) as NM1. pose proof (wf_ty_dnf HM2) as NM2.
  pose proof (wf_tm_dnf Hu1) as Nu1. pose proof (wf_tm_dnf Hu2) as Nu2.
  rewrite (G_us_brG_uext 24 G0 L' φ (k :: k' :: nil) eq_refl).
  assert (E7 : forall a b c d f g h τ i, gext_s (a :: b :: c :: d :: f :: g :: h :: nil) τ i =
                 gcons (gcons (gcons (gcons (gcons (gcons (gcons τ a) b) c) d) f) g) h i).
  { intros; unfold gext_s; destruct i as [|[|[|[|[|[|[|i]]]]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E7 _ _ _ _ _ _ _ _ i)) (fun i => eq_sym (E7 _ _ _ _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 24) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k))
       (gdTm (cvar 1) lC (gv 0) k))
       (gdTy (cvar 2 ,, gv 1 @ k ,, tyId k (gv 1)⟨↑⟩ (gu 0)⟨↑⟩ (var 0) @ k) lC k'))
       (gdTm (cvar 3) lC (tyGvar 0 (lsingle2 (gu 1) (tmRefl k (gv 2) (gu 1)))) k'))
       (gdTm (cvar 4) lC (gv 3) k))
       (gdTm (cvar 5) lC (tyId k (gv 4) (gu 3) (gu 0)) k)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl He1 He2 He Ee); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hu1 Hu2 Hu Eu); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hc1 Hc2 Hc Ec); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HM1 HM2 HM (fun _ => EM1)); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ha1 Ha2 Ha Ea); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [Empty]'s eliminator (branch 33): the motive over the scrutinee. *)
Lemma GS_elimEmpty {G0 L' φ G' σ1 σ2 Δ1 Δ2 M1 M2 t1 t2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ,, tyEmpty k' @ k' ⊢[ lC ] M1 @ k ] -> [ G' ; Δ2 ,, tyEmpty k' @ k' ⊢[ lC ] M2 @ k ] ->
  [ G' ; Δ1 ,, tyEmpty k' @ k' ⊢[ lD ] M1 ≅ M2 @ k ] -> ty_leq M1 M2 ->
  [ G' ; Δ1 ⊢[ lC ] t1 : tyEmpty k' @ k' ] -> [ G' ; Δ2 ⊢[ lC ] t2 : tyEmpty k' @ k' ] ->
  [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : tyEmpty k' @ k' ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG 33 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy M1 :: GTm t1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy M2 :: GTm t2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HM1 HM2 HM EM1 Ht1 Ht2 Ht Et.
  rewrite (G_us_brG_uext 33 G0 L' φ (k :: k' :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 33) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0 ,, tyEmpty k' @ k') lC k)) (gdTm (cvar 1) lC (tyEmpty k') k')).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ht1 Ht2 Ht Et); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HM1 HM2 HM (fun _ => EM1)); reflexivity.
Qed.

(** For [+] (branch 34): two types over the context. *)
Lemma GS_sum {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ⊢[ lC ] B1 @ k' ] -> [ G' ; Δ2 ⊢[ lC ] B2 @ k' ] -> [ G' ; Δ1 ⊢[ lD ] B1 ≅ B2 @ k' ] -> ty_leq B1 B2 ->
  GSubRel EP EM G' (G_us (brG 34 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB.
  rewrite (G_us_brG_uext 34 G0 L' φ (k :: k' :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 34) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTy (cvar 1) lC k')).
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [+]'s code (branch 35). *)
Lemma GS_codesum {G0 L' φ G' σ1 σ2 Δ1 Δ2 s1 s2 t1 t2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] s1 : tyU k @ lsuc k ] -> [ G' ; Δ2 ⊢[ lC ] s2 : tyU k @ lsuc k ] ->
  [ G' ; Δ1 ⊢[ lD ] s1 ≅ s2 : tyU k @ lsuc k ] -> tm_leq s1 s2 ->
  [ G' ; Δ1 ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> [ G' ; Δ2 ⊢[ lC ] t2 : tyU k' @ lsuc k' ] ->
  [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : tyU k' @ lsuc k' ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG 35 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTm s1 :: GTm t1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTm s2 :: GTm t2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ Hs1 Hs2 Hs Es Ht1 Ht2 Ht Et.
  rewrite (G_us_brG_uext 35 G0 L' φ (k :: k' :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 35) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTm (cvar 0) lC (tyU k) (lsuc k))) (gdTm (cvar 1) lC (tyU k') (lsuc k'))).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ht1 Ht2 Ht Et); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl Hs1 Hs2 Hs Es); reflexivity.
Qed.

(** For the injections (branches 36 and 37): the payload's type is the
    first or the second summand. *)
Lemma GS_inj {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 C1 a1 a2 k k' kc} kb (U : nat) :
  kb = 36 /\ U = 1 /\ C1 = A1 /\ kc = k \/ kb = 37 /\ U = 0 /\ C1 = B1 /\ kc = k' ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ⊢[ lC ] B1 @ k' ] -> [ G' ; Δ2 ⊢[ lC ] B2 @ k' ] -> [ G' ; Δ1 ⊢[ lD ] B1 ≅ B2 @ k' ] -> ty_leq B1 B2 ->
  [ G' ; Δ1 ⊢[ lC ] a1 : C1 @ kc ] -> [ G' ; Δ2 ⊢[ lC ] a2 : (if Nat.eqb U 1 then A2 else B2) @ kc ] ->
  [ G' ; Δ1 ⊢[ lD ] a1 ≅ a2 : C1 @ kc ] -> tm_leq a1 a2 ->
  GSubRel EP EM G' (G_us (brG kb G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: GTm a1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: GTm a2 :: nil) σ2).
Proof using ELM ELP.
  intros Hkb Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB Ha1 Ha2 Ha Ea.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_ty_dnf HB1) as NB1. pose proof (wf_ty_dnf HB2) as NB2.
  assert (E4 : forall a b c d τ i, gext_s (a :: b :: c :: d :: nil) τ i = gcons (gcons (gcons (gcons τ a) b) c) d i).
  { intros; unfold gext_s; destruct i as [|[|[|[|i]]]]; cbn; auto. f_equal; lia. }
  destruct Hkb as [(-> & -> & -> & ->) | (-> & -> & -> & ->)]; cbn [Nat.eqb] in Ha2.
  - rewrite (G_us_brG_uext 36 G0 L' φ (k :: k' :: nil) eq_refl).
    refine (GSubRel_ext EP EM (fun i => eq_sym (E4 _ _ _ _ _ i)) (fun i => eq_sym (E4 _ _ _ _ _ i)) _).
    change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 36) ++ gΨ (G_us G0 L' φ))) with
      (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTy (cvar 1) lC k'))
         (gdTm (cvar 2) lC (gv 1) k)).
    refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ha1 Ha2 Ha Ea); [| decl_eq | decl_eq].
    refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
    refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
  - rewrite (G_us_brG_uext 37 G0 L' φ (k :: k' :: nil) eq_refl).
    refine (GSubRel_ext EP EM (fun i => eq_sym (E4 _ _ _ _ _ i)) (fun i => eq_sym (E4 _ _ _ _ _ i)) _).
    change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 37) ++ gΨ (G_us G0 L' φ))) with
      (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTy (cvar 1) lC k'))
         (gdTm (cvar 2) lC (gv 0) k')).
    refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ha1 Ha2 Ha Ea); [| decl_eq | decl_eq].
    refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
    refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [case] (branch 38): the branches' types in the substituted form of
    their scopes' declarations. *)
Lemma GS_case {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 M1 M2 c1 c1' c2 c2' t1 t2 k k' k''} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ⊢[ lC ] B1 @ k' ] -> [ G' ; Δ2 ⊢[ lC ] B2 @ k' ] -> [ G' ; Δ1 ⊢[ lD ] B1 ≅ B2 @ k' ] -> ty_leq B1 B2 ->
  [ G' ; Δ1 ,, tySum k k' A1 B1 @ lmax k k' ⊢[ lC ] M1 @ k'' ] ->
  [ G' ; Δ2 ,, tySum k k' A2 B2 @ lmax k k' ⊢[ lC ] M2 @ k'' ] ->
  [ G' ; Δ1 ,, tySum k k' A1 B1 @ lmax k k' ⊢[ lD ] M1 ≅ M2 @ k'' ] -> ty_leq M1 M2 ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lC ] c1 : M1⟨rlift ↑⟩[lsingle (tmInl k k' A1⟨↑⟩ B1⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; Δ2 ,, A2 @ k ⊢[ lC ] c1' : M2⟨rlift ↑⟩[lsingle (tmInl k k' A2⟨↑⟩ B2⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] c1 ≅ c1' : M1⟨rlift ↑⟩[lsingle (tmInl k k' A1⟨↑⟩ B1⟨↑⟩ (var 0))] @ k'' ] ->
  tm_leq c1 c1' ->
  [ G' ; Δ1 ,, B1 @ k' ⊢[ lC ] c2 : M1⟨rlift ↑⟩[lsingle (tmInr k k' A1⟨↑⟩ B1⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; Δ2 ,, B2 @ k' ⊢[ lC ] c2' : M2⟨rlift ↑⟩[lsingle (tmInr k k' A2⟨↑⟩ B2⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; Δ1 ,, B1 @ k' ⊢[ lD ] c2 ≅ c2' : M1⟨rlift ↑⟩[lsingle (tmInr k k' A1⟨↑⟩ B1⟨↑⟩ (var 0))] @ k'' ] ->
  tm_leq c2 c2' ->
  [ G' ; Δ1 ⊢[ lC ] t1 : tySum k k' A1 B1 @ lmax k k' ] -> [ G' ; Δ2 ⊢[ lC ] t2 : tySum k k' A2 B2 @ lmax k k' ] ->
  [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : tySum k k' A1 B1 @ lmax k k' ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG 38 G0) L' (uext (k :: k' :: k'' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: GTy M1 :: GTm c1 :: GTm c2 :: GTm t1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: GTy M2 :: GTm c1' :: GTm c2' :: GTm t2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB HM1 HM2 HM EM1 Hc1 Hc1' Hc1e Ec1 Hc2 Hc2' Hc2e Ec2 Ht1 Ht2 Ht Et.
  rewrite liftshift_single_ty in Hc1, Hc1', Hc1e, Hc2, Hc2', Hc2e.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_ty_dnf HB1) as NB1. pose proof (wf_ty_dnf HB2) as NB2.
  pose proof (wf_ty_dnf HM1) as NM1. pose proof (wf_ty_dnf HM2) as NM2.
  rewrite (G_us_brG_uext 38 G0 L' φ (k :: k' :: k'' :: nil) eq_refl).
  assert (E7 : forall a b c d f g h τ i, gext_s (a :: b :: c :: d :: f :: g :: h :: nil) τ i =
                 gcons (gcons (gcons (gcons (gcons (gcons (gcons τ a) b) c) d) f) g) h i).
  { intros; unfold gext_s; destruct i as [|[|[|[|[|[|[|i]]]]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E7 _ _ _ _ _ _ _ _ i)) (fun i => eq_sym (E7 _ _ _ _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: k'' :: nil) φ)) (brDecls 38) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k))
       (gdTy (cvar 1) lC k'))
       (gdTy (cvar 2 ,, tySum k k' (gv 1) (gv 0) @ lmax k k') lC k''))
       (gdTm (cvar 3 ,, gv 2 @ k) lC (tyGvar 0 (lcons (lshift 1) (tmInl k k' (gv 2)⟨↑⟩ (gv 1)⟨↑⟩ (var 0)))) k''))
       (gdTm (cvar 4 ,, gv 2 @ k') lC (tyGvar 1 (lcons (lshift 1) (tmInr k k' (gv 3)⟨↑⟩ (gv 2)⟨↑⟩ (var 0)))) k''))
       (gdTm (cvar 5) lC (tySum k k' (gv 4) (gv 3)) (lmax k k'))).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ht1 Ht2 Ht Et); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hc2 Hc2' Hc2e Ec2); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hc1 Hc1' Hc1e Ec1); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HM1 HM2 HM (fun _ => EM1)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [sup] (branch 41): the children's type over the shape. *)
Lemma GS_sup {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 a1 a2 f1 f2 k k'} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lC ] B1 @ k' ] -> [ G' ; Δ2 ,, A2 @ k ⊢[ lC ] B2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] B1 ≅ B2 @ k' ] -> ty_leq B1 B2 ->
  [ G' ; Δ1 ⊢[ lC ] a1 : A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] a2 : A2 @ k ] ->
  [ G' ; Δ1 ⊢[ lD ] a1 ≅ a2 : A1 @ k ] -> tm_leq a1 a2 ->
  [ G' ; Δ1 ⊢[ lC ] f1 : tyPi k' (lmax k k') B1[lsingle a1] (tyW k k' A1 B1)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  [ G' ; Δ2 ⊢[ lC ] f2 : tyPi k' (lmax k k') B2[lsingle a2] (tyW k k' A2 B2)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  [ G' ; Δ1 ⊢[ lD ] f1 ≅ f2 : tyPi k' (lmax k k') B1[lsingle a1] (tyW k k' A1 B1)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  tm_leq f1 f2 ->
  GSubRel EP EM G' (G_us (brG 41 G0) L' (uext (k :: k' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: GTm a1 :: GTm f1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: GTm a2 :: GTm f2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB Ha1 Ha2 Ha Ea Hf1 Hf2 Hf Ef.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_ty_dnf HB1) as NB1. pose proof (wf_ty_dnf HB2) as NB2.
  pose proof (wf_tm_dnf Ha1) as Na1. pose proof (wf_tm_dnf Ha2) as Na2.
  rewrite (G_us_brG_uext 41 G0 L' φ (k :: k' :: nil) eq_refl).
  assert (E5 : forall a b c d f τ i, gext_s (a :: b :: c :: d :: f :: nil) τ i =
                                   gcons (gcons (gcons (gcons (gcons τ a) b) c) d) f i).
  { intros; unfold gext_s; destruct i as [|[|[|[|[|i]]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E5 _ _ _ _ _ _ i)) (fun i => eq_sym (E5 _ _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) φ)) (brDecls 41) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTy (cvar 1 ,, gv 0 @ k) lC k'))
       (gdTm (cvar 2) lC (gv 1) k))
       (gdTm (cvar 3) lC (tyPi k' (lmax k k') (tyGvar 1 (lsingle (gu 0))) (tyW k k' (gv 2) (gv 1))⟨↑⟩) (lmax k' (lmax k k')))).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hf1 Hf2 Hf Ef); [| sup_decl_eq | sup_decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ha1 Ha2 Ha Ea); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [elimW] (branch 42): the step's telescope in its notation form. *)
Lemma GS_elimW {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 B1 B2 M1 M2 c1 c2 t1 t2 k k' k''} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lC ] B1 @ k' ] -> [ G' ; Δ2 ,, A2 @ k ⊢[ lC ] B2 @ k' ] ->
  [ G' ; Δ1 ,, A1 @ k ⊢[ lD ] B1 ≅ B2 @ k' ] -> ty_leq B1 B2 ->
  [ G' ; Δ1 ,, tyW k k' A1 B1 @ lmax k k' ⊢[ lC ] M1 @ k'' ] ->
  [ G' ; Δ2 ,, tyW k k' A2 B2 @ lmax k k' ⊢[ lC ] M2 @ k'' ] ->
  [ G' ; Δ1 ,, tyW k k' A1 B1 @ lmax k k' ⊢[ lD ] M1 ≅ M2 @ k'' ] -> ty_leq M1 M2 ->
  [ G' ; Δ1 ,, A1 @ k ,, wfty k k' A1 B1 @ lmax k' (lmax k k') ,, wihty k k' k'' A1 B1 M1 @ lmax k' k''
      ⊢[ lC ] c1 : wstepty k k' A1 B1 M1 @ k'' ] ->
  [ G' ; Δ2 ,, A2 @ k ,, wfty k k' A2 B2 @ lmax k' (lmax k k') ,, wihty k k' k'' A2 B2 M2 @ lmax k' k''
      ⊢[ lC ] c2 : wstepty k k' A2 B2 M2 @ k'' ] ->
  [ G' ; Δ1 ,, A1 @ k ,, wfty k k' A1 B1 @ lmax k' (lmax k k') ,, wihty k k' k'' A1 B1 M1 @ lmax k' k''
      ⊢[ lD ] c1 ≅ c2 : wstepty k k' A1 B1 M1 @ k'' ] ->
  tm_leq c1 c2 ->
  [ G' ; Δ1 ⊢[ lC ] t1 : tyW k k' A1 B1 @ lmax k k' ] -> [ G' ; Δ2 ⊢[ lC ] t2 : tyW k k' A2 B2 @ lmax k k' ] ->
  [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : tyW k k' A1 B1 @ lmax k k' ] -> tm_leq t1 t2 ->
  GSubRel EP EM G' (G_us (brG 42 G0) L' (uext (k :: k' :: k'' :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTy B1 :: GTy M1 :: GTm c1 :: GTm t1 :: nil) σ1)
    (gext_s (GCtx Δ2 :: GTy A2 :: GTy B2 :: GTy M2 :: GTm c2 :: GTm t2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA HB1 HB2 HB EB HM1 HM2 HM EM1 Hc1 Hc2 Hc Ec Ht1 Ht2 Ht Et.
  pose proof (wf_ty_dnf HA1) as NA1. pose proof (wf_ty_dnf HA2) as NA2.
  pose proof (wf_ty_dnf HB1) as NB1. pose proof (wf_ty_dnf HB2) as NB2.
  pose proof (wf_ty_dnf HM1) as NM1. pose proof (wf_ty_dnf HM2) as NM2.
  rewrite (G_us_brG_uext 42 G0 L' φ (k :: k' :: k'' :: nil) eq_refl).
  assert (E6 : forall a b c d f g τ i, gext_s (a :: b :: c :: d :: f :: g :: nil) τ i =
                 gcons (gcons (gcons (gcons (gcons (gcons τ a) b) c) d) f) g i).
  { intros; unfold gext_s; destruct i as [|[|[|[|[|[|i]]]]]]; cbn; auto. f_equal; lia. }
  refine (GSubRel_ext EP EM (fun i => eq_sym (E6 _ _ _ _ _ _ _ i)) (fun i => eq_sym (E6 _ _ _ _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: k' :: k'' :: nil) φ)) (brDecls 42) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k))
       (gdTy (cvar 1 ,, gv 0 @ k) lC k'))
       (gdTy (cvar 2 ,, tyW k k' (gv 1) (gv 0) @ lmax k k') lC k''))
       (gdTm (cvar 3 ,, gv 2 @ k ,, wfty k k' (gv 2) (gv 1) @ lmax k' (lmax k k')
               ,, wihty k k' k'' (gv 2) (gv 1) (gv 0) @ lmax k' k'') lC (wstepty k k' (gv 2) (gv 1) (gv 0)) k''))
       (gdTm (cvar 4) lC (tyW k k' (gv 3) (gv 2)) (lmax k k'))).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Ht1 Ht2 Ht Et); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hc1 Hc2 Hc Ec); [| elimW_decl_eq | elimW_decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HM1 HM2 HM (fun _ => EM1)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl HB1 HB2 HB (fun _ => EB)); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [Vec] (branch 43): its element type and its length. *)
Lemma GS_vec {G0 L' φ G' σ1 σ2 Δ1 Δ2 A1 A2 n1 n2 k} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] A1 @ k ] -> [ G' ; Δ2 ⊢[ lC ] A2 @ k ] -> [ G' ; Δ1 ⊢[ lD ] A1 ≅ A2 @ k ] -> ty_leq A1 A2 ->
  [ G' ; Δ1 ⊢[ lC ] n1 : tyNat @ lzero ] -> [ G' ; Δ2 ⊢[ lC ] n2 : tyNat @ lzero ] ->
  [ G' ; Δ1 ⊢[ lD ] n1 ≅ n2 : tyNat @ lzero ] -> tm_leq n1 n2 ->
  GSubRel EP EM G' (G_us (brG 43 G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTy A1 :: GTm n1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTy A2 :: GTm n2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ HA1 HA2 HA EA Hn1 Hn2 Hn En.
  rewrite (G_us_brG_uext 43 G0 L' φ (k :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: nil) φ)) (brDecls 43) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTy (cvar 0) lC k)) (gdTm (cvar 1) lC tyNat lzero)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hn1 Hn2 Hn En); [| decl_eq | decl_eq].
  refine (GSubRel_ty_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl HA1 HA2 HA (fun _ => EA)); reflexivity.
Qed.

(** For [Vec]'s code (branch 44). *)
Lemma GS_codevec {G0 L' φ G' σ1 σ2 Δ1 Δ2 s1 s2 n1 n2 k} :
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] s1 : tyU k @ lsuc k ] -> [ G' ; Δ2 ⊢[ lC ] s2 : tyU k @ lsuc k ] ->
  [ G' ; Δ1 ⊢[ lD ] s1 ≅ s2 : tyU k @ lsuc k ] -> tm_leq s1 s2 ->
  [ G' ; Δ1 ⊢[ lC ] n1 : tyNat @ lzero ] -> [ G' ; Δ2 ⊢[ lC ] n2 : tyNat @ lzero ] ->
  [ G' ; Δ1 ⊢[ lD ] n1 ≅ n2 : tyNat @ lzero ] -> tm_leq n1 n2 ->
  GSubRel EP EM G' (G_us (brG 44 G0) L' (uext (k :: nil) φ))
    (gext_s (GCtx Δ1 :: GTm s1 :: GTm n1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTm s2 :: GTm n2 :: nil) σ2).
Proof using ELM ELP.
  intros Hσ HΔ1 HΔ Hs1 Hs2 Hs Es Hn1 Hn2 Hn En.
  rewrite (G_us_brG_uext 44 G0 L' φ (k :: nil) eq_refl).
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s3 _ _ _ _ i)) (fun i => eq_sym (gext_s3 _ _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext (k :: nil) φ)) (brDecls 44) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (gext (G_us G0 L' φ) gdCtx) (gdTm (cvar 0) lC (tyU k) (lsuc k))) (gdTm (cvar 1) lC tyNat lzero)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) _ _ _ eq_refl eq_refl Hn1 Hn2 Hn En); [| decl_eq | decl_eq].
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl Hs1 Hs2 Hs Es); reflexivity.
Qed.

(** For [Fin] and its code (branches 45 and 46): the scope of [succ]'s. *)
Lemma GS_fin {G0 L' φ G' σ1 σ2 Δ1 Δ2 n1 n2} kb : brDecls kb = brDecls 9 -> br_nu kb = 0 ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 -> [ G' ; Δ1 ⊢[ lD ] ] -> [ G' ⊢[ lD ] Δ1 ≅ Δ2 ] ->
  [ G' ; Δ1 ⊢[ lC ] n1 : tyNat @ lzero ] -> [ G' ; Δ2 ⊢[ lC ] n2 : tyNat @ lzero ] ->
  [ G' ; Δ1 ⊢[ lD ] n1 ≅ n2 : tyNat @ lzero ] -> tm_leq n1 n2 ->
  GSubRel EP EM G' (G_us (brG kb G0) L' (uext nil φ))
    (gext_s (GCtx Δ1 :: GTm n1 :: nil) σ1) (gext_s (GCtx Δ2 :: GTm n2 :: nil) σ2).
Proof using ELM ELP.
  intros HD Hnu Hσ HΔ1 HΔ Hn1 Hn2 Hn En.
  rewrite (G_us_brG_uext kb G0 L' φ nil (eq_sym Hnu)), HD.
  refine (GSubRel_ext EP EM (fun i => eq_sym (gext_s2 _ _ _ i)) (fun i => eq_sym (gext_s2 _ _ _ i)) _).
  change (mkG L' (map (fun D => gdecl_usubst D (uext nil φ)) (brDecls 9) ++ gΨ (G_us G0 L' φ))) with
    (gext (gext (G_us G0 L' φ) gdCtx) (gdTm (cvar 0) lC tyNat lzero)).
  refine (GSubRel_tm_i (i := lC) ltac:(lleC) (GSubRel_ctx1' Hσ HΔ1 HΔ) _ _ eq_refl eq_refl Hn1 Hn2 Hn En); reflexivity.
Qed.

(** ** A branch's global payloads, generically (M15b step 0)

    [GSone G' D1 D2 o1 o2]: the payloads [o1], [o2] fit the two images
    [D1], [D2] of one scope declaration (a context, or a type or term at
    C) and are related. [GSall] folds it over a scope's declarations,
    oldest first, extending the substitutions as it goes; [GS_br] turns
    it into the scope's [GSubRel], for any branch whose declarations are
    of those kinds (all of them but [J]'s and [case]'s motives, whose
    entries need conversions). [gs_solve] proves [GSall] from the
    payloads' typings in context. *)
Definition GSone G' (D1 D2 : gdecl) (o1 o2 : gobj) : Prop :=
  match D1, D2, o1, o2 with
  | gdCtx, gdCtx, GCtx Δ1, GCtx Δ2 => [ G' ; Δ1 ⊢[ lD ] ] /\ [ G' ⊢[ lD ] Δ1 ≅ Δ2 ]
  | gdTy Δ1 lC k1, gdTy Δ2 lC k2, GTy T1, GTy T2 =>
      k1 = k2 /\ [ G' ; Δ1 ⊢[ lC ] T1 @ k1 ] /\ [ G' ; Δ2 ⊢[ lC ] T2 @ k1 ] /\
      [ G' ; Δ1 ⊢[ lD ] T1 ≅ T2 @ k1 ] /\ ty_leq T1 T2
  | gdTm Δ1 lC A1 k1, gdTm Δ2 lC A2 k2, GTm t1, GTm t2 =>
      k1 = k2 /\ [ G' ; Δ1 ⊢[ lC ] t1 : A1 @ k1 ] /\ [ G' ; Δ2 ⊢[ lC ] t2 : A2 @ k1 ] /\
      [ G' ; Δ1 ⊢[ lD ] t1 ≅ t2 : A1 @ k1 ] /\ tm_leq t1 t2
  | _, _, _, _ => False
  end.

Fixpoint GSall G' (σ1 σ2 : gsub) (ds : list gdecl) (os1 os2 : list gobj) : Prop :=
  match ds, os1, os2 with
  | nil, nil, nil => True
  | D :: ds, o1 :: os1, o2 :: os2 =>
      GSone G' (gdecl_gsubst D σ1) (gdecl_gsubst D σ2) o1 o2 /\ GSall G' (gcons σ1 o1) (gcons σ2 o2) ds os1 os2
  | _, _, _ => False
  end.

Lemma gext_s_cons o os σ i : gext_s (o :: os) σ i = gext_s os (gcons σ o) i.
Proof using .
  unfold gext_s; cbn [length].
  destruct (Nat.ltb_spec i (length os)), (Nat.ltb_spec i (S (length os))); try lia.
  - replace (S (length os) - S i) with (S (length os - S i)) by lia. reflexivity.
  - replace (i - length os) with 0 by lia. replace (S (length os) - S i) with 0 by lia. reflexivity.
  - replace (i - length os) with (S (i - S (length os))) by lia. reflexivity.
Qed.

Lemma GSone_rel {G' L Ψ σ1 σ2 D o1 o2} : GSubRel EP EM G' (mkG L Ψ) σ1 σ2 ->
  GSone G' (gdecl_gsubst D σ1) (gdecl_gsubst D σ2) o1 o2 ->
  GSubRel EP EM G' (mkG L (D :: Ψ)) (gcons σ1 o1) (gcons σ2 o2).
Proof using ELM ELP.
  intros Hσ H. change (mkG L (D :: Ψ)) with (gext (mkG L Ψ) D).
  destruct (gdecl_gsubst D σ1) eqn:E1; destruct (gdecl_gsubst D σ2) eqn:E2; destruct o1, o2;
    repeat match goal with i : layer |- _ => destruct i end; cbn [GSone] in H; try contradiction.
  - destruct H as [HΔ1 HΔ]. destruct D; cbn in E1; try discriminate E1. exact (GSubRel_ctx1' Hσ HΔ1 HΔ).
  - destruct H as (<- & H1 & H2 & H12 & E).
    exact (GSubRel_ty_i (i := lC) ltac:(unfold lle; cbn; lia) Hσ E1 E2 eq_refl eq_refl H1 H2 H12 (fun _ => E)).
  - destruct H as (<- & H1 & H2 & H12 & E).
    exact (GSubRel_tm_i (i := lC) ltac:(unfold lle; cbn; lia) Hσ E1 E2 eq_refl eq_refl H1 H2 H12 E).
Qed.

Lemma GSall_rel G' L : forall ds os1 os2 Ψ σ1 σ2, GSubRel EP EM G' (mkG L Ψ) σ1 σ2 -> GSall G' σ1 σ2 ds os1 os2 ->
  GSubRel EP EM G' (mkG L (rev ds ++ Ψ)) (gext_s os1 σ1) (gext_s os2 σ2).
Proof using ELM ELP.
  induction ds as [|D ds IH]; intros [|o1 os1] [|o2 os2] Ψ σ1 σ2 Hσ H; try contradiction.
  - exact (GSubRel_ext EP EM (fun i => f_equal σ1 (eq_sym (Nat.sub_0_r i)))
             (fun i => f_equal σ2 (eq_sym (Nat.sub_0_r i))) Hσ).
  - destruct H as [H1 H2]. pose proof (IH _ _ _ _ _ (GSone_rel Hσ H1) H2) as X.
    cbn [rev]. rewrite <- app_assoc.
    exact (GSubRel_ext EP EM (fun i => eq_sym (gext_s_cons _ _ _ i)) (fun i => eq_sym (gext_s_cons _ _ _ i)) X).
Qed.

Lemma GS_br {G0 L' φ G' σ1 σ2 os1 os2} k ls : length ls = br_nu k ->
  GSubRel EP EM G' (G_us G0 L' φ) σ1 σ2 ->
  GSall G' σ1 σ2 (rev (map (fun D => gdecl_usubst D (uext ls φ)) (brDecls k))) os1 os2 ->
  GSubRel EP EM G' (G_us (brG k G0) L' (uext ls φ)) (gext_s os1 σ1) (gext_s os2 σ2).
Proof using ELM ELP.
  intros Hn Hσ H. rewrite (G_us_brG_uext k G0 L' φ ls Hn).
  pose proof (GSall_rel G' L' _ _ _ (gΨ (G_us G0 L' φ)) _ _ Hσ H) as X. rewrite rev_involutive in X. exact X.
Qed.

End GS.

(** [J]'s motive context's last type, at any layer (M11b). *)
Lemma wf_Jid_g {G i Γ l A a} : i <> lV -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢[ typeof i ] ] ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ].
Proof.
  intros Hv Hl HΓA HA Ha. apply wft_id; [exact Hv | exact Hl | apply wk1_ty_g; assumption
                                        | apply wk1_tm_g; assumption | apply var0_wf_g; assumption].
Qed.

(** Typing payloads' normal forms, and scope images computed as [sr_ctx]
    computes the calls' scopes (shared with [RecReduct]). *)
Ltac lsh0 :=
  repeat first [ rewrite subst_lshift0 by (apply dnftm_nftm; dnf_any)
               | rewrite subst_lshift0_ty by (apply dnfty_nfty; dnf_any) ].
Ltac gs_dnf :=
  repeat match goal with
  | H : [ _ ; _ ⊢[ lC ] ?T @ _ ] |- _ =>
      lazymatch goal with _ : dnfty T |- _ => fail | _ => pose proof (wf_ty_dnf H) end
  | H : [ _ ; _ ⊢[ lC ] ?t : _ @ _ ] |- _ =>
      lazymatch goal with _ : dnftm t |- _ => fail | _ => pose proof (wf_tm_dnf H) end
  end.
Ltac gs_norm :=
  cbn [gsubst GSubst_ctx GSubst_ty GSubst_tm gcons]; rewrite ?uc_ext, ?gc_ext;
  rewrite ?us_wfcsty, ?us_wfihty, ?us_wfstepty, ?gs_wfcsty, ?gs_wfihty, ?gs_wfstepty,
          ?us_wfty, ?us_wihty, ?us_wstepty, ?gs_wfty, ?gs_wihty, ?gs_wstepty;
  inst_cbn; cbn [gcons pctx pty ptm]; lsh0.

(** ** The recursion lemmas' hypotheses, bundled

    The section below quantifies over the recursors' data and these
    hypotheses. They are one class (an argument [R] of every lemma that
    uses one), not section hypotheses, so that the section can be
    reopened in other files (RecS*.v), which then build in parallel: each
    reopening declares the same data, [Context {R : RecHyps ...}], and
    the hypotheses as [Let]s of their fields, and a lemma from another
    file finds its [R] by instance resolution. *)
Definition LR_M_lawsRec2 (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}
  {EMl : GenericEqM EP EM} : VPLaws (@lr_vp (LR_M EP EM)) := vpM_laws EP EM.
Definition LR_M_permRec (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}
  {EMl : GenericEqM EP EM} : VPPerm (@lr_vp (LR_M EP EM)) := vpM_perm EP EM.

Module RecH.
Section RecH.
Context {EP EM : GenericEq} {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtmM := (@LRtm EM LRM).
#[local] Existing Instance LR_M_lawsRec2.

Context {G0 : gctx} {Γ0 : ctx} {L' : nat} {φ : nat -> lvl} {l1 l2 l1' l2' : lvl}
  {MT MT' Mt Mt' : ty} {bs bs' : nat -> tm}.
Context {G' : gctx} {σ σ' : gsub} {Θ : ctx} {e e' : lsub}.

Local Notation MTL := ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))]).
Local Notation MTR := ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄[llift (gwk (uwk e'))]).
Local Notation MtL := ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))]).
Local Notation MtR := ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄[llift (gwk (gwk (uwk e')))]).
Local Notation bsL := (fun k => ((usubst_tm (bs k) (uupn (br_nu k) φ))⦃gbsub k σ⦄)[lliftn (br_nl k) (bsub k e)]).
Local Notation bsR := (fun k => ((usubst_tm (bs' k) (uupn (br_nu k) φ))⦃gbsub k σ'⦄)[lliftn (br_nl k) (bsub k e')]).

Class RecHyps : Prop := {
  Hφ : usub_ok φ L' (gL G0) ;
  HMT : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT @ lvren l1 (ush 1) ] ;
  HMT' : [ recGT G0 ; recΓT Γ0 ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ;
  Hl1 : lequiv L' (lvsubst l1 φ) (lvsubst l1' φ) ;
  VMT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT ψ) (usubst_ty MT' ψ)
       (lvsubst (lvren l1 (ush 1)) ψ) ;
  VMTl : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT ψ) (usubst_ty MT ψ)
       (lvsubst (lvren l1 (ush 1)) ψ) ;
  VMTr : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) ->
     VTySM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) (usubst_ty MT' ψ) (usubst_ty MT' ψ)
       (lvsubst (lvren l1' (ush 1)) ψ) ;
  HMt : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ;
  HMt' : [ recGt G0 ; recΓt Γ0 ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ;
  Hl2 : lequiv L' (lvsubst l2 φ) (lvsubst l2' φ) ;
  VMt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt ψ) (usubst_ty Mt' ψ)
       (lvsubst (lvren l2 (ush 1)) ψ) ;
  VMtl : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt ψ) (usubst_ty Mt ψ)
       (lvsubst (lvren l2 (ush 1)) ψ) ;
  VMtr : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) ->
     VTySM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) (usubst_ty Mt' ψ) (usubst_ty Mt' ψ)
       (lvsubst (lvren l2' (ush 1)) ψ) ;
  Hbs : forall k, k < nbr -> [ brG k G0 ; brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                               bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ] ;
  Hbs' : forall k, k < nbr -> [ brG k G0 ; brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                               bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ] ;
  VBr : forall k, k < nbr -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VTmSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) ψ)
       (usubst_tm (bs k) ψ) (usubst_tm (bs' k) ψ)
       (usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) ψ) (lvsubst (brLv k l1 l2) ψ) ;
  VBr' : forall k, k < nbr -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VTmSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2') ψ)
       (usubst_tm (bs' k) ψ) (usubst_tm (bs' k) ψ)
       (usubst_ty (brRes k (wrapMT MT') (wrapMt Mt')) ψ) (lvsubst (brLv k l1' l2') ψ) ;
  VΓ : VCtxSM (G_us G0 L' φ) (ucsubst Γ0 φ) ;
  Hσ : GSubRel G' (G_us G0 L' φ) σ σ' ;
  He : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e e' ;
  HrbL : RBwf G' Θ (lvsubst l1 φ) (lvsubst l2 φ) MTL MtL bsL ;
  HrbR : RBwf G' Θ (lvsubst l1' φ) (lvsubst l2' φ) MTR MtR bsR ;
  EL : gL G' = L' ;
  HG0 : [ ⊢ G_us G0 L' φ ] ;
  HΓ0 : [ G_us G0 L' φ ; ucsubst Γ0 φ ⊢[ lM ] ] ;
  VΓT : forall L'' ψ, usub_ok ψ L'' (gL (recGT G0)) -> VCtxSM (G_us (recGT G0) L'' ψ) (ucsubst (recΓT Γ0) ψ) ;
  VΓt : forall L'' ψ, usub_ok ψ L'' (gL (recGt G0)) -> VCtxSM (G_us (recGt G0) L'' ψ) (ucsubst (recΓt Γ0) ψ) ;
  VΓbr : forall k, k < nbr -> forall L'' ψ, usub_ok ψ L'' (gL (brG k G0)) ->
     VCtxSM (G_us (brG k G0) L'' ψ) (ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) ψ)
}.
End RecH.
End RecH.

Section Rec.
Context {EP EM : GenericEq} {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtmM := (@LRtm EM LRM).
#[local] Existing Instance LR_M_lawsRec2.

Context {G0 : gctx} {Γ0 : ctx} {L' : nat} {φ : nat -> lvl} {l1 l2 l1' l2' : lvl}
  {MT MT' Mt Mt' : ty} {bs bs' : nat -> tm}.
Context {G' : gctx} {σ σ' : gsub} {Θ : ctx} {e e' : lsub}.
Context {RH : @RecH.RecHyps EP EM G0 Γ0 L' φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' G' σ σ' Θ e e'}.

Let Hφ := @RecH.Hφ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HMT := @RecH.HMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HMT' := @RecH.HMT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hl1 := @RecH.Hl1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMT := @RecH.VMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMTl := @RecH.VMTl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMTr := @RecH.VMTr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HMt := @RecH.HMt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HMt' := @RecH.HMt' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hl2 := @RecH.Hl2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMt := @RecH.VMt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMtl := @RecH.VMtl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMtr := @RecH.VMtr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hbs := @RecH.Hbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hbs' := @RecH.Hbs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VBr := @RecH.VBr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VBr' := @RecH.VBr' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VΓ := @RecH.VΓ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hσ := @RecH.Hσ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let He := @RecH.He _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HrbL := @RecH.HrbL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HrbR := @RecH.HrbR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let EL := @RecH.EL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HG0 := @RecH.HG0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HΓ0 := @RecH.HΓ0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VΓT := @RecH.VΓT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VΓt := @RecH.VΓt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VΓbr := @RecH.VΓbr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.

Local Notation MTL := ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))]).
Local Notation MTR := ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄[llift (gwk (uwk e'))]).
Local Notation MtL := ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))]).
Local Notation MtR := ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄[llift (gwk (gwk (uwk e')))]).
Local Notation bsL := (fun k => ((usubst_tm (bs k) (uupn (br_nu k) φ))⦃gbsub k σ⦄)[lliftn (br_nl k) (bsub k e)]).
Local Notation bsR := (fun k => ((usubst_tm (bs' k) (uupn (br_nu k) φ))⦃gbsub k σ'⦄)[lliftn (br_nl k) (bsub k e')]).

(** Facts from the hypotheses. *)
Lemma Nσ : gdnf σ. Proof using Hσ. exact (gsw_dnf _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)). Qed.
Lemma Nσ' : gdnf σ'. Proof using Hσ. exact (gsw_dnf _ _ _ (gsr_wf_r _ _ _ _ _ _ Hσ)). Qed.
Lemma De : LK dnftm e. Proof using ELM He. exact (proj1 (SubRel_dnf _ _ _ _ _ He)). Qed.
Lemma De' : LK dnftm e'. Proof using ELM He. exact (proj2 (SubRel_dnf _ _ _ _ _ He)). Qed.
Lemma HΘ : [ G' ; Θ ⊢[ lM ] ].
Proof using EMl He. pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X. Qed.
Lemma He'r : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ') Θ e' e'.
Proof using ELM ELP He Hσ VΓ.
  pose proof (VΓ _ _ _ Hσ _ _ (gwk_ok_id G')) as XΓ; cbn [gwa] in XΓ.
  exact (SubRel_transport _ _ _ _ _ _ (CtxRel_sym _ _ _ XΓ) (SubRel_refl_r He)).
Qed.
Lemma He'l : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e' e'.
Proof using ELM ELP He. exact (SubRel_refl_r He). Qed.

(** Boxed code related from syntax. *)
Lemma box_rel {Δ c c' k} : [ G' ; Δ ⊢[ lD ] ] -> lwf L' k ->
  [ G' ; Δ ⊢[ lC ] c @ k ] -> [ G' ; Δ ⊢[ lC ] c' @ k ] -> ty_leq c c' ->
  LRtmM lzero G' Θ (tyCTyp Δ k) (tyCTyp Δ k) (boxT c) (boxT c').
Proof using EL ELM ELP EMl He.
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
Proof using EL ELM ELP EMl He.
  intros HA Hk Ht Ht' E. pose proof (ctx_of_wf_ty (i := lD) eq_refl HA) as HΔ.
  pose proof (static_code_tm (i := lC) ltac:(unfold lle; cbn; lia) Ht Ht' E) as Htt.
  destruct (VTmG_of_eq EP EM (lift_eqtm (j := lD) Htt ltac:(unfold lle; cbn; lia))) as [VP VM].
  destruct (VTyG_of_eq EP EM (eqty_refl _ _ _ _ _ HA)) as [AP AM].
  destruct (CtxRelG_of_eq EP EM (eqc_refl _ _ _ HΔ)) as [CP CM].
  apply (LRtm_boxt EP EM HΘ HΔ HA Ht Ht' E); [rewrite EL; exact Hk | | exact AP | exact AM | exact VP | exact VM].
  exact (conj (eqc_refl _ _ _ HΔ) (conj CP CM)).
Qed.

(** Pointwise equivalent payload levels. *)
Lemma uext_leqv {ls ls' φ0} : Forall2 leqv ls ls' -> forall i, leqv (uext ls φ0 i) (uext ls' φ0 i).
Proof using .
  intros H i. unfold uext. rewrite (Forall2_length H).
  destruct (i <? length ls'); [| apply leqv_refl].
  generalize (length ls' - S i) as n. clear i.
  induction H as [| a a' ls ls' Ha H IH]; intros [|n]; cbn; auto using leqv_refl.
Qed.

(** ** Instantiating the branch scopes (M8_DESIGN.md J2, S2)

    [wkb_rw] rewrites one motive instance [M(wkb nu ng j w)] under the
    branch payloads into the instantiated motive, reading the recursive
    calls' prefix off the local substitution. [res_eq] proves a result
    instance equation, [sr_ctx] opens a branch context's relation into its
    ambient part and its calls. *)
Ltac lext_base d := lazymatch d with lcons ?d' _ => lext_base d' | lext _ ?e => e | _ => d end.
Ltac lext_split d e :=
  lazymatch d with
  | lcons ?d' ?a => let xs := lext_split d' e in eval cbn [List.app] in (xs ++ a :: nil)
  | lext ?xs _ => xs
  | _ => constr:(@nil tm)
  end.
Ltac wkb_side :=
  first [ reflexivity
        | apply gdnf_gext_s; [forall_tac | first [exact Nσ | exact Nσ']]
        | apply lk_dnf_lext;
          [ repeat (apply Forall_cons; [dnf_any |]); apply Forall_nil
          | first [exact De | exact De'] ]
        | repeat (apply lk_dnf_lcons; [| dnf_any]); first [exact De | exact De'] ].
Ltac wkb_rw :=
  match goal with
  | |- context [ ((usubst_ty (motT (wkb ?nu ?ng ?nl ?w) ?lv ?g ?c) (uext ?ls ?φ0))⦃gext_s ?os ?σ0⦄)[?d] ] =>
      let e0 := lext_base d in let xs := lext_split d e0 in
      rewrite (motT_wkb_inst' _ nu ng nl ls os xs φ0 σ0 e0 d lv g c) by wkb_side
  | |- context [ ((usubst_ty (mott (wkb ?nu ?ng ?nl ?w) ?lv ?g ?U ?c) (uext ?ls ?φ0))⦃gext_s ?os ?σ0⦄)[?d] ] =>
      let e0 := lext_base d in let xs := lext_split d e0 in
      rewrite (mott_wkb_inst' _ nu ng nl ls os xs φ0 σ0 e0 d lv g U c) by wkb_side
  end.
Ltac res_eq := cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar]; wkb_rw; inst_cbn; lsh0;
  rewrite ?Nat.add_0_r; reflexivity.
Ltac sr_ctx :=
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst mkLocs call_ty call_lv br_calls]; rewrite ?gs_cext;
  rewrite wkc_inst' by reflexivity; rewrite ?lvren_ush_uext' by reflexivity;
  repeat apply SubRel_cons; [first [exact He | exact He'r] | ..];
  repeat wkb_rw; inst_cbn; lsh0.

(** The typing reduct's side conditions: normal forms of the payloads and
    of the calls, read off their typings and relations. *)
Ltac inst_side k :=
  first [ exact Nσ | exact Nσ' | exact De | exact De'
        | exact (wf_tm_dnf (Hbs k ltac:(lia))) | exact (wf_tm_dnf (Hbs' k ltac:(lia))) | dnf_any ].

(** [GS_br]'s side, from the payloads' typings in context: each scope
    declaration's image is computed as [sr_ctx] computes the calls'
    scopes (the telescopes kept in notation form), then matched up to
    conversion; the right payloads against themselves by reflexivity. *)
Ltac gs_leaf :=
  first
  [ lazymatch goal with |- ?x = ?x => reflexivity end
  | apply ty_leq_refl | apply tm_leq_refl | assumption
  | gs_norm;
    first [ assumption | solve [apply eqc_refl; assumption]
          | solve [apply eqty_refl; eapply lift_ty; [eassumption | unfold lle; cbn; lia]]
          | solve [apply eqtm_refl; eapply lift_tm; [eassumption | unfold lle; cbn; lia]] ] ].
Ltac gs_solve :=
  gs_dnf; cbn [rev List.app map brDecls GSall gdecl_usubst gdecl_gsubst uext lvsubst Nat.ltb Nat.leb length nth Nat.sub GSone];
  repeat split; gs_leaf.

(** ** The common part of a branch case

    Both reducts come from the branches' validity; the right one is
    switched from the left levels to its own by level invariance. *)

Lemma br_core k ls ls' os os' xsL xsR goalL goalR l : k < nbr ->
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
Proof using ELM ELP Hφ VBr VBr'.
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

Local Notation recTL k Δ c := (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ (boxT c)).
Local Notation recTR k Δ c := (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ (boxT c)).

(** ** A type branch, generically (M8_DESIGN.md J2, S2)

    As [rec_t_br], at the type heads: the codes are types, the result
    motive is [M_Typ], the branch level is [l₁]. *)
Lemma rec_T_br k ls ls' os os' xsL xsR {ΔL ΔR kL kR k0 k0R cL cR} :
  k < nbr -> br_isT k = true ->
  length ls = br_nu k -> length ls' = br_nu k -> Forall (lwf L') ls -> Forall (lwf L') ls' ->
  (forall i, leqv (uext ls φ i) (uext ls' φ i)) ->
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k0 kL -> lequiv L' k0 kR -> lequiv L' k0 k0R ->
  [ G' ; ΔL ⊢[ lC ] cL @ k0 ] -> [ G' ; ΔL ⊢[ lC ] cR @ k0 ] -> [ G' ; ΔR ⊢[ lC ] cR @ k0R ] -> ty_leq cL cR ->
  GSubRel G' (G_us (brG k G0) L' (uext ls φ)) (gext_s os σ) (gext_s os' σ') ->
  GSubRel G' (G_us (brG k G0) L' (uext ls' φ)) (gext_s os' σ') (gext_s os' σ') ->
  SubRelM G' ((ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) (uext ls φ))⦃gext_s os σ⦄) Θ (lext xsL e) (lext xsR e') ->
  SubRelM G' ((ucsubst (brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2') (uext ls' φ))⦃gext_s os' σ'⦄) Θ
    (lext xsR e') (lext xsR e') ->
  ((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e] =
    motT (wrapMT MTL) k0 ΔL (boxT cL) ->
  ((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls φ))⦃gext_s os σ⦄)[lext xsR e'] =
    motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k0 ΔL (boxT cL) ->
  ((usubst_ty (brRes k (wrapMT MT') (wrapMt Mt')) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e'] =
    motT (wrapMT MTR) k0R ΔR (boxT cR) ->
  redT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL cL =
    Some (((usubst_tm (bs k) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e]) ->
  redT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR cR =
    Some (((usubst_tm (bs' k) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e']) ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT cL)) (motT (wrapMT MTR) kR ΔR (boxT cR))
    (recTL kL ΔL cL) (recTR kR ΔR cR).
Proof using EL ELM ELP EMl HMT HMT' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hk HkT Hn Hn' Hls Hls' Eψ HΔL HΔ HkL HkR Hk0R HcL0 HcRL HcR0 Ec GS1 GS2 SR1 SR2
    EhL EhL' EhR HredL HredR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  assert (Hw0 : lwf L' k0) by exact (lequiv_wf_l _ _ _ HkL).
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hw0R : lwf L' k0R) by exact (lequiv_wf_r _ _ _ Hk0R).
  assert (Hwl1 : lwf L' (lvsubst l1 φ)) by (rewrite <- EL; exact (proj1 HrbL)).
  assert (Hwl1' : lwf L' (lvsubst l1' φ)) by exact (lequiv_wf_r _ _ _ Hl1).
  assert (Hl1g : lequiv (gL G') (lvsubst l1 φ) (lvsubst l1' φ)) by (rewrite EL; exact Hl1).
  (* the codes at the goal's levels *)
  assert (HcL : [ G' ; ΔL ⊢[ lC ] cL @ kL ]) by (eapply wft_lconv; [exact HcL0 | rewrite EL; apply lequiv_sym, HkL]).
  assert (HcR : [ G' ; ΔR ⊢[ lC ] cR @ kR ]).
  { eapply wft_lconv; [exact HcR0 | rewrite EL; eapply lequiv_trans; [apply lequiv_sym, HkR | exact Hk0R]]. }
  pose proof (box_rel HΔL HwL HcL HcL (ty_leq_refl _)) as BL.
  pose proof (box_rel HΔL Hw0 HcL0 HcL0 (ty_leq_refl _)) as B0.
  pose proof (box_rel HΔL Hw0 HcL0 HcRL Ec) as B0'.
  pose proof (box_rel HΔR HwR HcR HcR (ty_leq_refl _)) as BR.
  pose proof (box_rel HΔR Hw0R HcR0 HcR0 (ty_leq_refl _)) as BR0.
  assert (W : LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT cL)) (motT (wrapMT MTR) kR ΔR (boxT cR))
                (((usubst_tm (bs k) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e])
                (((usubst_tm (bs' k) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e'])).
  { refine (br_core k ls ls' os os' xsL xsR _ _ _ Hk Hn Hn' Hls Hls' Eψ GS1 GS2 SR1 SR2 _ _ _ _ _).
    - rewrite EhL.
      exact (MotRel_T EP EM G0 Γ0 L' φ MT MT l1 l1 HMT HMT (lequiv_refl _ _ Hwl1) Hφ VMTl VMTl VΓ G' σ σ Θ e e
               (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL
               (eqc_refl _ _ _ HΔL) BL B0).
    - rewrite EhL'.
      exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
               Hw0 HkR HΔL HΔ B0' BR).
    - rewrite EhR.
      exact (LRty_lconv (MotRel_T EP EM G0 Γ0 L' φ MT' MT' l1' l1' HMT' HMT' (lequiv_refl _ _ Hwl1') Hφ VMTr VMTr VΓ
                           G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                           (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Hk0R) HΔR (eqc_refl _ _ _ HΔR) BR BR0) Hl1g).
    - unfold brLv; rewrite HkT. rewrite (lvren_ush_uext' l1 (br_nu k) ls φ Hn).
      apply lequiv_refl; rewrite EL; exact Hwl1.
    - unfold brLv; rewrite HkT. rewrite (lvren_ush_uext' l1' (br_nu k) ls' φ Hn'). exact Hl1g. }
  (* anti-reduction *)
  destruct (LRtm_escape W) as [HrL _]. destruct (LRtm_escape (LRtm_sym W)) as [HrR _].
  rewrite (@gm_layer_M EP EM EMl) in HrL, HrR.
  pose proof (tmred_elimT_beta HrbL (eq_ind_r (fun L => lwf L kL) HwL EL) HΔL HcL HredL HrL) as R1.
  pose proof (tmred_elimT_beta HrbR (eq_ind_r (fun L => lwf L kR) HwR EL) HΔR HcR HredR
                (wf_lconv _ _ _ _ _ _ _ HrR (lequiv_sym _ _ _ Hl1g))) as R2.
  pose proof (tmred_lconv _ _ _ _ _ R2 Hl1g) as R2'.
  rewrite <- (@gm_layer_M EP EM EMl) in R1, R2'.
  exact (LRtm_red W R1 R2').
Qed.

(** ** Natural numbers *)

Lemma rec_T_nat {ΔL ΔR kL kR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' lzero kL -> lequiv L' lzero kR ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT tyNat)) (motT (wrapMT MTR) kR ΔR (boxT tyNat))
    (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL (boxT tyNat))
    (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR (boxT tyNat)).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HN : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lC ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  refine (rec_T_br 0 nil nil (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' lzero I) (HN _ HΔL) (HN _ HΔL) (HN _ HΔR) I
            (GS_ctx0 EP EM 0 nil eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 0 nil eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) _ _ _ _ _ _ _).
  - sr_ctx.
  - sr_ctx.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_nat_inst; inst_side 0.
  - apply redT_nat_inst; inst_side 0.
Qed.





(** ** A sub-code and its recursive call

    Each branch relates its sub-codes' calls on the two sides from the
    induction hypotheses (M8_DESIGN.md L4): the right sub-code in the
    right context at both level annotations, and the call with the left
    motive on both sides ([MotRel_T]/[MotRel_t]), which is what [sr_ctx]
    reads. *)

Lemma Tcall {ΔL ΔR k k1 A A'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] -> lwf L' k -> lequiv L' k k1 ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  [ G' ; ΔL ⊢[ lD ] A ≅ A' @ k ] /\ [ G' ; ΔR ⊢[ lC ] A' @ k ] /\ [ G' ; ΔR ⊢[ lC ] A' @ k1 ] /\
  [ G' ⊢[ lD ] ΔL ,, A @ k ≅ ΔR ,, A' @ k ] /\ [ G' ⊢[ lD ] ΔL ,, A @ k ≅ ΔR ,, A' @ k1 ] /\
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A))
    (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k ΔL (boxT A))
    (recTL k ΔL A) (recTR k1 ΔR A').
Proof using EL ELM ELP EMl HMT HMT' He Hl1 Hσ Hφ VMT VMTr VΓ.
  intros HΔL HΔ Hw Q HA HA' EA IHA.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof (lequiv_wf_r _ _ _ Q) as Hw1.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD.
  pose proof (lift_eqty (j := lD) (static_code_ty Hl1c HA HA' EA) Hl1c) as HAA.
  assert (HA'R : [ G' ; ΔR ⊢[ lC ] A' @ k ]) by exact (ctxconv_ty HΔ (i := lC) eq_refl HA').
  assert (HA'R1 : [ G' ; ΔR ⊢[ lC ] A' @ k1 ]) by (eapply wft_lconv; [exact HA'R | apply lequiv_sym, Qg]).
  refine (conj HAA (conj HA'R (conj HA'R1 (conj _ (conj _ _))))).
  - apply eqc_ext; [exact HΔ | exact HAD | exact HAA | apply lequiv_refl; rewrite EL; exact Hw].
  - apply eqc_ext; [exact HΔ | exact HAD | exact HAA | exact Qg].
  - refine (LRtm_conv_r IHA (LRty_sym _)).
    exact (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw Q HΔL HΔ (box_rel HΔL Hw HA HA' EA) (box_rel HΔR Hw1 HA'R1 HA'R1 (ty_leq_refl _))).
Qed.

(** A binder type ([Π], branch 1; [Σ], branch 13): its former [F], formation
    rule and reduct instance. *)
Ltac rec_T_bind kb F wftF inst ΔL ΔR k1 k2 k1' k2' A B A' B' :=
  intros HΔL HΔ HkL HkR Hw1 Hw2 Hw1' Hw2' E1 E2 HA HB HA' HB' EA EB IHA IHB;
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR;
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia);
  assert (Q1 : lequiv L' k1 k1') by exact (leqv_lequiv _ _ _ Hw1 Hw1' E1);
  assert (Q2 : lequiv L' k2 k2') by exact (leqv_lequiv _ _ _ Hw2 Hw2' E2);
  assert (Hl1'' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1));
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw1 Q1 HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1);
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw2 Q2 HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2);
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1'') as X1r;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1'') as X2r;
  (* the codes *)
  assert (Q12 : lequiv L' (lmax k1 k2) (lmax k1' k2')) by (apply lequiv_max; assumption);
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] F k1 k2 A B @ lmax k1 k2 ]) by (apply wftF; [discriminate | ..]; rewrite ?EL; assumption);
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] F k1' k2' A' B' @ lmax k1' k2' ]) by (apply wftF; [discriminate | ..]; rewrite ?EL; assumption);
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] F k1' k2' A' B' @ lmax k1 k2 ])
    by (eapply wft_lconv; [refine (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Q12]);
  refine (rec_T_br kb (k1 :: k2 :: nil) (k1' :: k2' :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: nil)
            (recTL k1 ΔL A :: recTL k2 (ΔL ,, A @ k1) B :: nil) (recTR k1' ΔR A' :: recTR k2' (ΔR ,, A' @ k1') B' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E1 (Forall2_cons _ _ E2 (Forall2_nil _))))
            HΔL HΔ HkL HkR Q12 HcL0 HcRL HcR0 (conj E1 (conj E2 (conj EA EB)))
            (GS_pi EP EM kb eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB)
            (GS_pi EP EM kb eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _) HB'R1 HB'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HB'R1 Hl1c)) (ty_leq_refl _)) _ _ _ _ _ _ _);
  [ sr_ctx; [exact X1 | exact X2] | sr_ctx; [exact X1r | exact X2r] | res_eq | res_eq | res_eq
  | apply inst; inst_side kb | apply inst; inst_side kb ].

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
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  rec_T_bind 1 tyPi wft_pi redT_pi_inst ΔL ΔR k1 k2 k1' k2' A B A' B'.
Qed.

Lemma rec_T_sig {ΔL ΔR kL kR k1 k2 k1' k2' A B A' B'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k1 k2) kL -> lequiv L' (lmax k1 k2) kR ->
  lwf L' k1 -> lwf L' k2 -> lwf L' k1' -> lwf L' k2' -> leqv k1 k1' -> leqv k2 k2' ->
  [ G' ; ΔL ⊢[ lC ] A @ k1 ] -> [ G' ; ΔL ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  [ G' ; ΔL ⊢[ lC ] A' @ k1 ] -> [ G' ; ΔL ,, A @ k1 ⊢[ lC ] B' @ k2 ] -> ty_leq A A' -> ty_leq B B' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k1 ΔL (boxT A)) (motT (wrapMT MTR) k1' ΔR (boxT A'))
    (recTL k1 ΔL A) (recTR k1' ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k2 (ΔL ,, A @ k1) (boxT B)) (motT (wrapMT MTR) k2' (ΔR ,, A' @ k1') (boxT B'))
    (recTL k2 (ΔL ,, A @ k1) B) (recTR k2' (ΔR ,, A' @ k1') B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tySig k1 k2 A B)))
    (motT (wrapMT MTR) kR ΔR (boxT (tySig k1' k2' A' B')))
    (recTL kL ΔL (tySig k1 k2 A B)) (recTR kR ΔR (tySig k1' k2' A' B')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  rec_T_bind 13 tySig wft_sig redT_sig_inst ΔL ΔR k1 k2 k1' k2' A B A' B'.
Qed.

Lemma rec_T_W {ΔL ΔR kL kR k1 k2 k1' k2' A B A' B'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k1 k2) kL -> lequiv L' (lmax k1 k2) kR ->
  lwf L' k1 -> lwf L' k2 -> lwf L' k1' -> lwf L' k2' -> leqv k1 k1' -> leqv k2 k2' ->
  [ G' ; ΔL ⊢[ lC ] A @ k1 ] -> [ G' ; ΔL ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  [ G' ; ΔL ⊢[ lC ] A' @ k1 ] -> [ G' ; ΔL ,, A @ k1 ⊢[ lC ] B' @ k2 ] -> ty_leq A A' -> ty_leq B B' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k1 ΔL (boxT A)) (motT (wrapMT MTR) k1' ΔR (boxT A'))
    (recTL k1 ΔL A) (recTR k1' ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k2 (ΔL ,, A @ k1) (boxT B)) (motT (wrapMT MTR) k2' (ΔR ,, A' @ k1') (boxT B'))
    (recTL k2 (ΔL ,, A @ k1) B) (recTR k2' (ΔR ,, A' @ k1') B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyW k1 k2 A B)))
    (motT (wrapMT MTR) kR ΔR (boxT (tyW k1' k2' A' B')))
    (recTL kL ΔL (tyW k1 k2 A B)) (recTR kR ΔR (tyW k1' k2' A' B')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  rec_T_bind 39 tyW wft_W redT_W_inst ΔL ΔR k1 k2 k1' k2' A B A' B'.
Qed.



(** ** Universes *)

Lemma rec_T_U {ΔL ΔR kL kR k k'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc k) kL -> lequiv L' (lsuc k) kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyU k))) (motT (wrapMT MTR) kR ΔR (boxT (tyU k')))
    (recTL kL ΔL (tyU k)) (recTR kR ΔR (tyU k')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' E.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (HU : forall Δ j, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> [ G' ; Δ ⊢[ lC ] tyU j @ lsuc j ])
    by (intros; apply wft_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyU k' @ lsuc k ])
    by (eapply wft_lconv; [exact (HU _ _ HΔL Hw') | rewrite EL; apply lequiv_suc, Q]).
  refine (rec_T_br 2 (k :: nil) (k' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) (HU _ _ HΔL Hw) HcRL (HU _ _ HΔR Hw') E
            (GS_ctx0 EP EM 2 (k :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 2 (k' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  - sr_ctx.
  - sr_ctx.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_U_inst; inst_side 2.
  - apply redT_U_inst; inst_side 2.
Qed.

Lemma rec_T_unit {ΔL ΔR kL kR k k'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyUnit k))) (motT (wrapMT MTR) kR ΔR (boxT (tyUnit k')))
    (recTL kL ΔL (tyUnit k)) (recTR kR ΔR (tyUnit k')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' E.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (HU : forall Δ j, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> [ G' ; Δ ⊢[ lC ] tyUnit j @ j ])
    by (intros; apply wft_unit; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyUnit k' @ k ])
    by (eapply wft_lconv; [exact (HU _ _ HΔL Hw') | rewrite EL; exact Q]).
  refine (rec_T_br 14 (k :: nil) (k' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q (HU _ _ HΔL Hw) HcRL (HU _ _ HΔR Hw') E
            (GS_ctx0 EP EM 14 (k :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 14 (k' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redT_unit_inst; inst_side 14.
  - apply redT_unit_inst; inst_side 14.
Qed.


(** ** Decodings of codes *)

Local Notation rectL k Δ T c := (elimt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ T (boxt c)).
Local Notation rectR k Δ T c := (elimt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ T (boxt c)).

Lemma tcall {ΔL ΔR k k1 T T' t t'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] -> lwf L' k -> lequiv L' k k1 ->
  [ G' ; ΔL ⊢[ lD ] T ≅ T' @ k ] ->
  [ G' ; ΔL ⊢[ lC ] t : T @ k ] -> [ G' ; ΔL ⊢[ lC ] t' : T @ k ] -> tm_leq t t' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL T (boxt t)) (mott (wrapMt MtR) k1 ΔR T' (boxt t'))
    (rectL k ΔL T t) (rectR k1 ΔR T' t') ->
  [ G' ; ΔL ⊢[ lD ] t ≅ t' : T @ k ] /\ [ G' ; ΔR ⊢[ lC ] t' : T' @ k ] /\ [ G' ; ΔR ⊢[ lC ] t' : T' @ k1 ] /\
  [ G' ; ΔR ⊢[ lD ] T' @ k1 ] /\
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL T (boxt t))
    (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) k ΔL T (boxt t))
    (rectL k ΔL T t) (rectR k1 ΔR T' t').
Proof using EL ELM ELP EMl HMt HMt' He Hl2 Hσ Hφ VMt VMtr VΓ.
  intros HΔL HΔ Hw Q HTT Ht Ht' Et IHt.
  pose proof (lequiv_wf_r _ _ _ Q) as Hw1.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  pose proof (eqty_wf_l (i := lD) eq_refl HTT) as HTD.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c Ht Ht' Et) Hl1c) as Htt.
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : T' @ k ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _). eapply wf_conv; [exact Ht' | apply eqty_sym, HTT]. }
  assert (Ht'R1 : [ G' ; ΔR ⊢[ lC ] t' : T' @ k1 ]) by (eapply wf_lconv; [exact Ht'R | apply lequiv_sym, Qg]).
  pose proof (wf_tm_ty (i := lD) eq_refl (lift_tm (j := lD) Ht'R1 Hl1c)) as HT'R1.
  refine (conj Htt (conj Ht'R (conj Ht'R1 (conj HT'R1 _)))).
  refine (LRtm_conv_r IHt (LRty_sym _)).
  exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
           (kL := k) (kR := k1) Hw Q HΔL HΔ HTT HT'R1
           (box_rel_tm HTD Hw Ht Ht' Et) (box_rel_tm HT'R1 Hw1 Ht'R1 Ht'R1 (tm_leq_refl _))).
Qed.

Lemma rec_T_El {ΔL ΔR kL kR k k' t t'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  [ G' ; ΔL ⊢[ lC ] t : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] t' : tyU k @ lsuc k ] -> tm_leq t t' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt t))
    (mott (wrapMt MtR) (lsuc k') ΔR (tyU k') (boxt t'))
    (rectL (lsuc k) ΔL (tyU k) t) (rectR (lsuc k') ΔR (tyU k') t') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyEl k t))) (motT (wrapMT MTR) kR ΔR (boxT (tyEl k' t')))
    (recTL kL ΔL (tyEl k t)) (recTR kR ΔR (tyEl k' t')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' E Ht Ht' Et IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (Hl2'' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HUU : [ G' ; ΔL ⊢[ lD ] tyU k ≅ tyU k' @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q]).
  (* the code and its call *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) HUU Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X1).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Ht') as Ht'R.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2'') as X1r.
  (* the codes *)
  assert (HEl : forall Δ j j' u, lwf L' j -> [ G' ; Δ ⊢[ lC ] u : tyU j @ lsuc j ] -> lequiv L' j j' ->
                  [ G' ; Δ ⊢[ lC ] tyEl j u @ j' ]).
  { intros Δ j j' u Hj Hu Hjj. eapply wft_lconv; [apply wft_El; [discriminate | rewrite EL; exact Hj | exact Hu]
                                                 | rewrite EL; apply lequiv_sym, Hjj]. }
  pose proof (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl Ht'R1) as Ht'L1.
  refine (rec_T_br 3 (k :: nil) (k' :: nil) (GCtx ΔL :: GTm t :: nil) (GCtx ΔR :: GTm t' :: nil)
            (rectL (lsuc k) ΔL (tyU k) t :: nil) (rectR (lsuc k') ΔR (tyU k') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q (HEl _ _ _ _ Hw Ht (lequiv_refl _ _ Hw)) (HEl _ _ _ _ Hw' Ht'L1 (lequiv_sym _ _ _ Q))
            (HEl _ _ _ _ Hw' Ht'R1 (lequiv_refl _ _ Hw')) (conj E Et)
            (GS_El EP EM Hσ HΔL HΔ Ht Ht'R Htt Et)
            (GS_El EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Ht'R1 Ht'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx. exact X1.
  - sr_ctx. exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_El_inst; inst_side 3.
  - apply redT_El_inst; inst_side 3.
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
Proof using EL ELM ELP EMl Hl2 HrbL HrbR.
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

(** ** A term branch, generically (M8_DESIGN.md J2, S2)

    Everything about a term branch but its recursive calls and the
    instantiation of its result: the codes' typings at the index types,
    the result motives related three times, the branch levels, the
    branches' validity ([br_core]) and anti-reduction ([rec_t_fin]). The
    branch supplies the payloads, the relations of its global payloads
    ([GS1], [GS2]) and of its recursive calls ([SR1], [SR2]), its reducts,
    and its result's three instances ([EhL], [EhL'], [EhR]). The left code
    [cL] is typed at the canonical index [T0 @ k0] in [ΔL]; the right one
    at its own canonical index [T0R @ k0R] in [ΔR]. *)
Lemma rec_t_br_core k ls ls' os os' xsL xsR {ΔL ΔR kL kR TL TR k0 k0R T0 T0R cL cR} :
  k < nbr -> br_isT k = false ->
  length ls = br_nu k -> length ls' = br_nu k -> Forall (lwf L') ls -> Forall (lwf L') ls' ->
  (forall i, leqv (uext ls φ i) (uext ls' φ i)) ->
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k0 kL -> lequiv L' k0 kR -> lequiv L' k0 k0R ->
  [ G' ; ΔL ⊢[ lD ] T0 ≅ TL @ k0 ] -> [ G' ; ΔL ⊢[ lD ] T0 ≅ TR @ k0 ] -> [ G' ; ΔR ⊢[ lD ] T0 ≅ T0R @ k0 ] ->
  [ G' ; ΔL ⊢[ lC ] cL : T0 @ k0 ] -> [ G' ; ΔL ⊢[ lC ] cR : T0 @ k0 ] -> [ G' ; ΔR ⊢[ lC ] cR : T0R @ k0R ] ->
  tm_leq cL cR ->
  GSubRel G' (G_us (brG k G0) L' (uext ls φ)) (gext_s os σ) (gext_s os' σ') ->
  GSubRel G' (G_us (brG k G0) L' (uext ls' φ)) (gext_s os' σ') (gext_s os' σ') ->
  SubRelM G' ((ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) (uext ls φ))⦃gext_s os σ⦄) Θ (lext xsL e) (lext xsR e') ->
  SubRelM G' ((ucsubst (brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2') (uext ls' φ))⦃gext_s os' σ'⦄) Θ
    (lext xsR e') (lext xsR e') ->
  ((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e] =
    mott (wrapMt MtL) k0 ΔL T0 (boxt cL) ->
  ((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls φ))⦃gext_s os σ⦄)[lext xsR e'] =
    mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) k0 ΔL T0 (boxt cL) ->
  ((usubst_ty (brRes k (wrapMT MT') (wrapMt Mt')) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e'] =
    mott (wrapMt MtR) k0R ΔR T0R (boxt cR) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt cL)) (mott (wrapMt MtR) kR ΔR TR (boxt cR))
    (((usubst_tm (bs k) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e])
    (((usubst_tm (bs' k) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e']).
Proof using EL ELM ELP EMl HMt HMt' He Hl2 HrbL Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hk HkT Hn Hn' Hls Hls' Eψ HΔL HΔ HkL HkR Hk0R HTL HTR H0R HcL0 HcRL HcR0 Ec GS1 GS2 SR1 SR2
    EhL EhL' EhR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  assert (Hw0 : lwf L' k0) by exact (lequiv_wf_l _ _ _ HkL).
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hw0R : lwf L' k0R) by exact (lequiv_wf_r _ _ _ Hk0R).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (HkLg : lequiv (gL G') k0 kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') k0 kR) by (rewrite EL; exact HkR).
  assert (Hk0Rg : lequiv (gL G') k0 k0R) by (rewrite EL; exact Hk0R).
  (* the index types *)
  pose proof (eqty_wf_l (i := lD) eq_refl HTL) as HT0.
  pose proof (eqty_wf_r (i := lD) eq_refl H0R) as HT0R0.
  assert (HT0R : [ G' ; ΔR ⊢[ lD ] T0R @ k0R ]) by (eapply wft_lconv; [exact HT0R0 | apply lequiv_sym, Hk0Rg]).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  pose proof (ctxconv_eqty HΔ (i := lD) eq_refl HTR) as HTRΔ.
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  (* the codes at the goal's index types *)
  assert (HcL : [ G' ; ΔL ⊢[ lC ] cL : TL @ kL ]).
  { eapply wf_lconv; [| apply lequiv_sym, HkLg]. eapply wf_conv; [exact HcL0 | apply eqty_sym, HTL]. }
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl HcRL) as HcRΔ.
  assert (HcR : [ G' ; ΔR ⊢[ lC ] cR : TR @ kR ]).
  { eapply wf_lconv; [| apply lequiv_sym, HkRg]. eapply wf_conv; [exact HcRΔ | apply eqty_sym, HTRΔ]. }
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL.
  pose proof (box_rel_tm HT0 Hw0 HcL0 HcL0 (tm_leq_refl _)) as B0.
  pose proof (box_rel_tm HT0 Hw0 HcL0 HcRL Ec) as B0'.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR.
  pose proof (box_rel_tm HT0R Hw0R HcR0 HcR0 (tm_leq_refl _)) as BR0.
  refine (br_core k ls ls' os os' xsL xsR _ _ _ Hk Hn Hn' Hls Hls' Eψ GS1 GS2 SR1 SR2 _ _ _ _ _).
  - rewrite EhL.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_sym _ _ _ HkL) HΔL (eqc_refl _ _ _ HΔL)
             (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) (lequiv_sym _ _ _ HkLg)) HT0 BL B0).
  - rewrite EhL'.
    exact (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e' e' Hσ He'l EL
             Hw0 HkR HΔL HΔ HTR HTRk B0' BR).
  - rewrite EhR.
    refine (LRty_lconv (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
                          G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR
                          (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkR) Hk0R) HΔR (eqc_refl _ _ _ HΔR)
                          _ HT0R BR BR0) Hl2g).
    eapply eqty_trans; [exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTRΔ) (lequiv_sym _ _ _ HkRg)) |].
    exact (eqty_lconv _ _ _ _ _ _ _ H0R (lequiv_sym _ _ _ HkRg)).
  - unfold brLv; rewrite HkT. rewrite (lvren_ush_uext' l2 (br_nu k) ls φ Hn).
    apply lequiv_refl; rewrite EL; exact Hwl2.
  - unfold brLv; rewrite HkT. rewrite (lvren_ush_uext' l2' (br_nu k) ls' φ Hn'). exact Hl2g.
Qed.

Lemma rec_t_br k ls ls' os os' xsL xsR {ΔL ΔR kL kR TL TR k0 k0R T0 T0R cL cR} :
  k < nbr -> br_isT k = false ->
  length ls = br_nu k -> length ls' = br_nu k -> Forall (lwf L') ls -> Forall (lwf L') ls' ->
  (forall i, leqv (uext ls φ i) (uext ls' φ i)) ->
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k0 kL -> lequiv L' k0 kR -> lequiv L' k0 k0R ->
  [ G' ; ΔL ⊢[ lD ] T0 ≅ TL @ k0 ] -> [ G' ; ΔL ⊢[ lD ] T0 ≅ TR @ k0 ] -> [ G' ; ΔR ⊢[ lD ] T0 ≅ T0R @ k0 ] ->
  [ G' ; ΔL ⊢[ lC ] cL : T0 @ k0 ] -> [ G' ; ΔL ⊢[ lC ] cR : T0 @ k0 ] -> [ G' ; ΔR ⊢[ lC ] cR : T0R @ k0R ] ->
  tm_leq cL cR ->
  GSubRel G' (G_us (brG k G0) L' (uext ls φ)) (gext_s os σ) (gext_s os' σ') ->
  GSubRel G' (G_us (brG k G0) L' (uext ls' φ)) (gext_s os' σ') (gext_s os' σ') ->
  SubRelM G' ((ucsubst (brΓ k Γ0 (wrapMT MT) (wrapMt Mt) l1 l2) (uext ls φ))⦃gext_s os σ⦄) Θ (lext xsL e) (lext xsR e') ->
  SubRelM G' ((ucsubst (brΓ k Γ0 (wrapMT MT') (wrapMt Mt') l1' l2') (uext ls' φ))⦃gext_s os' σ'⦄) Θ
    (lext xsR e') (lext xsR e') ->
  ((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e] =
    mott (wrapMt MtL) k0 ΔL T0 (boxt cL) ->
  ((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls φ))⦃gext_s os σ⦄)[lext xsR e'] =
    mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) k0 ΔL T0 (boxt cL) ->
  ((usubst_ty (brRes k (wrapMT MT') (wrapMt Mt')) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e'] =
    mott (wrapMt MtR) k0R ΔR T0R (boxt cR) ->
  redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL cL =
    Some (((usubst_tm (bs k) (uext ls φ))⦃gext_s os σ⦄)[lext xsL e]) ->
  redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR cR =
    Some (((usubst_tm (bs' k) (uext ls' φ))⦃gext_s os' σ'⦄)[lext xsR e']) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt cL)) (mott (wrapMt MtR) kR ΔR TR (boxt cR))
    (rectL kL ΔL TL cL) (rectR kR ΔR TR cR).
Proof using EL ELM ELP EMl HMt HMt' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hk HkT Hn Hn' Hls Hls' Eψ HΔL HΔ HkL HkR Hk0R HTL HTR H0R HcL0 HcRL HcR0 Ec GS1 GS2 SR1 SR2
    EhL EhL' EhR HredL HredR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HkLg : lequiv (gL G') k0 kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') k0 kR) by (rewrite EL; exact HkR).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  pose proof (ctxconv_eqty HΔ (i := lD) eq_refl HTR) as HTRΔ.
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (HcL : [ G' ; ΔL ⊢[ lC ] cL : TL @ kL ]).
  { eapply wf_lconv; [| apply lequiv_sym, HkLg]. eapply wf_conv; [exact HcL0 | apply eqty_sym, HTL]. }
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl HcRL) as HcRΔ.
  assert (HcR : [ G' ; ΔR ⊢[ lC ] cR : TR @ kR ]).
  { eapply wf_lconv; [| apply lequiv_sym, HkRg]. eapply wf_conv; [exact HcRΔ | apply eqty_sym, HTRΔ]. }
  refine (rec_t_fin HΔL HΔR (lequiv_wf_r _ _ _ HkL) (lequiv_wf_r _ _ _ HkR) HTLk HTRk HcL HcR HredL HredR _).
  exact (rec_t_br_core k ls ls' os os' xsL xsR Hk HkT Hn Hn' Hls Hls' Eψ HΔL HΔ HkL HkR Hk0R HTL HTR H0R
           HcL0 HcRL HcR0 Ec GS1 GS2 SR1 SR2 EhL EhL' EhR).
Qed.

Lemma rec_t_nat {ΔL ΔR kL kR TL TR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc lzero) kL -> lequiv L' (lsuc lzero) kR ->
  [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TL @ lsuc lzero ] -> [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TR @ lsuc lzero ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt tmNat)) (mott (wrapMt MtR) kR ΔR TR (boxt tmNat))
    (rectL kL ΔL TL tmNat) (rectR kR ΔR TR tmNat).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hc : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lC ] tmNat : tyU lzero @ lsuc lzero ])
    by (intros; apply wf_code_nat; [discriminate | assumption]).
  assert (HU0 : [ G' ; ΔR ⊢[ lD ] tyU lzero @ lsuc lzero ]) by (apply wft_U; [discriminate | assumption | exact I]).
  refine (rec_t_br 5 nil nil (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' (lsuc lzero) I) HTL HTR (eqty_refl _ _ _ _ _ HU0)
            (Hc _ HΔL) (Hc _ HΔL) (Hc _ HΔR) I
            (GS_ctx0 EP EM 5 nil eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 5 nil eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_nat_inst; inst_side 5.
  - apply redt_nat_inst; inst_side 5.
Qed.


Lemma rec_t_zero {ΔL ΔR kL kR TL TR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lzero) kL -> lequiv L' (lzero) kR ->
  [ G' ; ΔL ⊢[ lD ] tyNat ≅ TL @ lzero ] -> [ G' ; ΔL ⊢[ lD ] tyNat ≅ TR @ lzero ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt zero)) (mott (wrapMt MtR) kR ΔR TR (boxt zero))
    (rectL kL ΔL TL zero) (rectR kR ΔR TR zero).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hc : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lC ] zero : tyNat @ lzero ])
    by (intros; apply wf_zero; [discriminate | assumption]).
  assert (HN0 : [ G' ; ΔR ⊢[ lD ] tyNat @ lzero ]) by (apply wft_nat; [discriminate | assumption]).
  refine (rec_t_br 8 nil nil (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' lzero I) HTL HTR (eqty_refl _ _ _ _ _ HN0)
            (Hc _ HΔL) (Hc _ HΔL) (Hc _ HΔR) I
            (GS_ctx0 EP EM 8 nil eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 8 nil eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_zero_inst; inst_side 8.
  - apply redt_zero_inst; inst_side 8.
Qed.


Lemma rec_t_U {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lsuc j)) kL -> lequiv L' (lsuc (lsuc j)) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lsuc j) ≅ TL @ lsuc (lsuc j) ] -> [ G' ; ΔL ⊢[ lD ] tyU (lsuc j) ≅ TR @ lsuc (lsuc j) ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmU j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmU j')))
    (rectL kL ΔL TL (tmU j)) (rectR kR ΔR TR (tmU j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q2 : lequiv L' (lsuc (lsuc j)) (lsuc (lsuc j'))) by (do 2 apply lequiv_suc; exact Q).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU (lsuc j) ≅ tyU (lsuc j') @ lsuc (lsuc j) ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; apply lequiv_suc, Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmU i : tyU (lsuc i) @ lsuc (lsuc i) ])
    by (intros; apply wf_code_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmU j' : tyU (lsuc j) @ lsuc (lsuc j) ]).
  { eapply wf_lconv; [| rewrite EL; exact Q2].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q2]. }
  refine (rec_t_br 7 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q2 HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 7 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 7 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_U_inst; inst_side 7.
  - apply redt_U_inst; inst_side 7.
Qed.

(** The unit code and the unit element: branches without calls, like [U]. *)
Lemma rec_t_codeunit {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc j) kL -> lequiv L' (lsuc j) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU j ≅ TL @ lsuc j ] -> [ G' ; ΔL ⊢[ lD ] tyU j ≅ TR @ lsuc j ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmUnit j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmUnit j')))
    (rectL kL ΔL TL (tmUnit j)) (rectR kR ΔR TR (tmUnit j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q1 : lequiv L' (lsuc j) (lsuc j')) by (apply lequiv_suc; exact Q).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; exact Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmUnit i : tyU i @ lsuc i ])
    by (intros; apply wf_code_unit; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmUnit j' : tyU j @ lsuc j ]).
  { eapply wf_lconv; [| rewrite EL; exact Q1].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q1]. }
  refine (rec_t_br 19 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q1 HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 19 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 19 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_codeunit_inst; inst_side 19.
  - apply redt_codeunit_inst; inst_side 19.
Qed.

Lemma rec_t_triv {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' j kL -> lequiv L' j kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyUnit j ≅ TL @ j ] -> [ G' ; ΔL ⊢[ lD ] tyUnit j ≅ TR @ j ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmTriv j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmTriv j')))
    (rectL kL ΔL TL (tmTriv j)) (rectR kR ΔR TR (tmTriv j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyUnit j ≅ tyUnit j' @ j ])
    by (intros; apply eqty_unit; [discriminate | assumption | rewrite EL; exact Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmTriv i : tyUnit i @ i ])
    by (intros; apply wf_triv; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmTriv j' : tyUnit j @ j ]).
  { eapply wf_lconv; [| rewrite EL; exact Q].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q]. }
  refine (rec_t_br 20 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 20 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 20 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_triv_inst; inst_side 20.
  - apply redt_triv_inst; inst_side 20.
Qed.


Lemma rec_t_succ {ΔL ΔR kL kR TL TR t t'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' lzero kL -> lequiv L' lzero kR ->
  [ G' ; ΔL ⊢[ lD ] tyNat ≅ TL @ lzero ] -> [ G' ; ΔL ⊢[ lD ] tyNat ≅ TR @ lzero ] ->
  [ G' ; ΔL ⊢[ lC ] t : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] t' : tyNat @ lzero ] -> tm_leq t t' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt t)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt t'))
    (rectL lzero ΔL tyNat t) (rectR lzero ΔR tyNat t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (succ t))) (mott (wrapMt MtR) kR ΔR TR (boxt (succ t')))
    (rectL kL ΔL TL (succ t)) (rectR kR ΔR TR (succ t')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR Ht Ht' Et IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  (* the code and its call *)
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Ht Ht' Et IHt)
    as (Htt & Ht'R & _ & _ & X1).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X1r.
  assert (HcS : forall Δ u, [ G' ; Δ ⊢[ lC ] u : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lC ] succ u : tyNat @ lzero ])
    by (intros; apply wf_succ; [discriminate | assumption]).
  refine (rec_t_br 9 nil nil (GCtx ΔL :: GTm t :: nil) (GCtx ΔR :: GTm t' :: nil)
            (rectL lzero ΔL tyNat t :: nil) (rectR lzero ΔR tyNat t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' lzero I) HTL HTR (eqty_refl _ _ _ _ _ (HN0 _ HΔR))
            (HcS _ _ Ht) (HcS _ _ Ht') (HcS _ _ Ht'R) Et
            (GS_succ EP EM Hσ HΔL HΔ Ht Ht'R Htt Et)
            (GS_succ EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Ht'R Ht'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx. exact X1.
  - sr_ctx. exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_succ_inst; inst_side 9.
  - apply redt_succ_inst; inst_side 9.
Qed.

(** A binder code ([Π], branch 6; [Σ], branch 15): its former [F], typing
    rule and reduct instance. *)
Ltac rec_t_bind kb F wfF inst ΔL ΔR k k' k1 k1' s0 t0 s1 t1 :=
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR Hs Hs' Es Ht Ht' Et IHs IHt;
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR;
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia);
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E);
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E');
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption);
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2));
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]);
  (* the domain code and its call *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) (HUU _ _ _ HΔL Q) Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1);
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R;
  (* the codomain code under the domain's decoding, and its call *)
  assert (HElL : [ G' ; ΔL ⊢[ lD ] tyEl k s0 @ k ])
    by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm (j := lD) Hs Hl1c)]);
  assert (CE : [ G' ⊢[ lD ] ΔL ,, tyEl k s0 @ k ≅ ΔR ,, tyEl k s1 @ k ])
    by (apply eqc_ext; [exact HΔ | exact HElL | apply eqty_El; [discriminate | rewrite EL; apply lequiv_refl, Hw | exact Hss]
                       | rewrite EL; apply lequiv_refl, Hw]);
  assert (CE1 : [ G' ⊢[ lD ] ΔL ,, tyEl k s0 @ k ≅ ΔR ,, tyEl k1 s1 @ k1 ])
    by (apply eqc_ext; [exact HΔ | exact HElL | apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss]
                       | rewrite EL; exact Q]);
  pose proof (eqctx_wf_l (i := lD) eq_refl CE) as HΔLE;
  destruct (tcall (k := lsuc k') HΔLE CE1 Hw' (lequiv_suc _ _ _ Q') (HUU _ _ _ HΔLE Q') Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X2);
  pose proof (ctxconv_tm CE (i := lC) eq_refl Ht') as Ht'R;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r;
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] F k k' s0 t0 : tyU (lmax k k') @ lsuc (lmax k k') ])
    by (apply wfF; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact Hs | exact Ht]);
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] F k1 k1' s1 t1 : tyU (lmax k1 k1') @ lsuc (lmax k1 k1') ])
    by (apply wfF; [discriminate | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact Hs'R1 | exact Ht'R1]);
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] F k1 k1' s1 t1 : tyU (lmax k k') @ lsuc (lmax k k') ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Qm] | exact (HUU _ _ _ HΔL Qm)]);
  refine (rec_t_br kb (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil)
            (GCtx ΔR :: GTm s1 :: GTm t1 :: nil)
            (rectL (lsuc k) ΔL (tyU k) s0 :: rectL (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') t0 :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s1 :: rectR (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') t1 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Qm) HTL HTR (HUU _ _ _ HΔR Qm) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_pi' EP EM kb eq_refl eq_refl Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et)
            (GS_pi' EP EM kb eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hs'R1 Hs'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _) Ht'R1 Ht'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _);
  [ sr_ctx; [exact X1 | exact X2] | sr_ctx; [exact X1r | exact X2r] | res_eq | res_eq | res_eq
  | apply inst; inst_side kb | apply inst; inst_side kb ].

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
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  rec_t_bind 6 tmPi wf_code_pi redt_pi_inst ΔL ΔR k k' k1 k1' s0 t0 s1 t1.
Qed.

Lemma rec_t_codesig {ΔL ΔR kL kR TL TR k k' k1 k1' s0 t0 s1 t1} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
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
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSig k k' s0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSig k1 k1' s1 t1)))
    (rectL kL ΔL TL (tmSig k k' s0 t0)) (rectR kR ΔR TR (tmSig k1 k1' s1 t1)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  rec_t_bind 15 tmSig wf_code_sig redt_codesig_inst ΔL ΔR k k' k1 k1' s0 t0 s1 t1.
Qed.

Lemma rec_t_codeW {ΔL ΔR kL kR TL TR k k' k1 k1' s0 t0 s1 t1} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
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
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmW k k' s0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmW k1 k1' s1 t1)))
    (rectL kL ΔL TL (tmW k k' s0 t0)) (rectR kR ΔR TR (tmW k1 k1' s1 t1)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  rec_t_bind 40 tmW wf_code_W redt_codeW_inst ΔL ΔR k k' k1 k1' s0 t0 s1 t1.
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
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR HM HM' EMM Hs Hs' Es Hz Hz' Ez Ht Ht' Et IHM IHs IHz IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  assert (CN : [ G' ⊢[ lD ] ΔL ,, tyNat @ lzero ≅ ΔR ,, tyNat @ lzero ]).
  { apply eqc_ext; [exact HΔ | exact (HN0 _ HΔL) | apply eqty_refl, HN0, HΔL | apply lequiv_refl; exact I]. }
  (* the motive and its call *)
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CN) CN Hw Q HM HM' EMM IHM) as (HMM & HM'R & HM'R1 & CNMk & CNM & X1).
  pose proof (eqctx_wf_l (i := lD) eq_refl CNM) as HΔLNM.
  (* the motive's instances *)
  assert (HM0 : [ G' ; ΔL ⊢[ lD ] M[lsingle zero] ≅ M'[lsingle zero] @ k ])
    by exact (eqty_single (i := lD) eq_refl HMM (wf_zero _ lD _ ltac:(discriminate) HΔL)).
  assert (HMs : [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lD ] M[lsucc] ≅ M'[lsucc] @ k ])
    by exact (eqty_subst (i := lD) eq_refl HMM (lsub_wf_lsucc (i := lD) eq_refl ltac:(discriminate) HΔLNM)).
  (* the cases and the scrutinee, and their calls *)
  destruct (tcall HΔL HΔ Hw Q HM0 Hs Hs' Es IHs) as (Hss & Hs'R & Hs'R1 & _ & X2).
  destruct (tcall HΔLNM CNM Hw Q HMs Hz Hz' Ez IHz) as (Hzz & _ & Hz'R1 & _ & X3).
  assert (Hz'R : [ G' ; ΔR ,, tyNat @ lzero ,, M' @ k ⊢[ lC ] z1 : M'[lsucc] @ k ]).
  { refine (ctxconv_tm CNMk (i := lC) eq_refl _). eapply wf_conv; [exact Hz' | apply eqty_sym, HMs]. }
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Ht Ht' Et IHt)
    as (Htt & Ht'R & _ & _ & X4).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHz) IHz) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X4r.
  assert (HMtt : [ G' ; ΔL ⊢[ lD ] M[lsingle t0] ≅ M'[lsingle t1] @ k ])
    by exact (eqty_subst_single_D HMM (lift_ty (j := lD) HM' Hl1c) Htt (lift_tm (j := lD) Ht Hl1c) (lift_tm (j := lD) Ht' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] natrec k M s0 z0 t0 : M[lsingle t0] @ k ])
    by (apply wf_natrec; [exact Hn | rewrite EL; exact Hw | exact HM | exact Hs | exact Hz | exact Ht]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] natrec k1 M' s1 z1 t1 : M'[lsingle t1] @ k1 ])
    by (apply wf_natrec; [exact Hn | rewrite EL; exact Hw1 | exact HM'R1 | exact Hs'R1 | exact Hz'R1 | exact Ht'R]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] natrec k1 M' s1 z1 t1 : M[lsingle t0] @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg] | exact HMtt]. }
  set (xsL := recTL k (ΔL ,, tyNat @ lzero) M :: rectL k ΔL (M[lsingle zero]) s0 ::
              rectL k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) z0 :: rectL lzero ΔL tyNat t0 :: nil).
  set (xsR := recTR k1 (ΔR ,, tyNat @ lzero) M' :: rectR k1 ΔR (M'[lsingle zero]) s1 ::
              rectR k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) z1 :: rectR lzero ΔR tyNat t1 :: nil).
  refine (rec_t_br 10 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
            (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HMtt) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_natrec EP EM Hσ HΔL HΔ HM HM'R HMM EMM Hs Hs'R Hss Es Hz Hz'R Hzz Ez Ht Ht'R Htt Et)
            (GS_natrec EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HM'R1 HM'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HM'R1 Hl1c)) (ty_leq_refl _)
               Hs'R1 Hs'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _)
               Hz'R1 Hz'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hz'R1 Hl1c)) (tm_leq_refl _)
               Ht'R Ht'R (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_natrec_inst; inst_side 10.
  - apply redt_natrec_inst; inst_side 10.
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
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Hf Hf' Ef Ha Ha' Ea IHA IHB IHf IHa.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2).
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R.
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  assert (HPP : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B ≅ tyPi k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact HBB]).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  (* the function and the argument, and their calls *)
  destruct (tcall HΔL HΔ Hwm Qm HPP Hf Hf' Ef IHf) as (Hff & Hf'R0 & Hf'R1 & _ & X3).
  assert (Hf'R : [ G' ; ΔR ⊢[ lC ] f' : tyPi k k' A' B' @ lmax k k' ]).
  { pose proof (lift_ty (j := lD) HA'R Hl1c) as HA'RD.
    eapply wf_conv; [exact Hf'R0 |].
    apply eqty_pi; [discriminate | exact Qg | exact Qg' | exact HA'RD | apply eqty_refl, HA'RD
                   | apply eqty_refl, (lift_ty (j := lD) HB'R Hl1c)]. }
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X4).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHf) IHf) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X4r.
  assert (HBa : [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ B'[lsingle a'] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty (j := lD) HB' Hl1c) Haa (lift_tm (j := lD) Ha Hl1c) (lift_tm (j := lD) Ha' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] app f k k' A B a : B[lsingle a] @ k' ])
    by (apply wf_app; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Hf | exact Ha]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] app f' k1 k1' A' B' a' : B'[lsingle a'] @ k1' ])
    by (apply wf_app; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1 | exact Hf'R1 | exact Ha'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] app f' k1 k1' A' B' a' : B[lsingle a] @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg'] | exact HBa]. }
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL (lmax k k') ΔL (tyPi k k' A B) f :: rectL k ΔL A a :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tyPi k1 k1' A' B') f' :: rectR k1 ΔR A' a' :: nil).
  refine (rec_t_br 12 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HBa) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_app EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Hf Hf'R Hff Ef Ha Ha'R Haa Ea)
            (GS_app EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Hf'R1 Hf'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hf'R1 Hl1c)) (tm_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_app_inst; inst_side 12.
  - apply redt_app_inst; inst_side 12.
Qed.

(** ** The Σ eliminations and introduction (M8d) *)

Lemma rec_t_pair {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' a a' b b'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tySig k k' A B ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tySig k k' A B ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ⊢[ lC ] b : B[lsingle a] @ k' ] -> [ G' ; ΔL ⊢[ lC ] b' : B[lsingle a] @ k' ] -> tm_leq b b' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' ΔL (B[lsingle a]) (boxt b)) (mott (wrapMt MtR) k1' ΔR (B'[lsingle a']) (boxt b'))
    (rectL k' ΔL (B[lsingle a]) b) (rectR k1' ΔR (B'[lsingle a']) b') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmPair k k' A B a b)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmPair k1 k1' A' B' a' b')))
    (rectL kL ΔL TL (tmPair k k' A B a b)) (rectR kR ΔR TR (tmPair k1 k1' A' B' a' b')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Ha Ha' Ea Hb Hb' Eb IHA IHB IHa IHb.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2).
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R.
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  assert (HPP : [ G' ; ΔL ⊢[ lD ] tySig k k' A B ≅ tySig k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sig; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact HBB]).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  (* the components and their calls *)
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X3).
  assert (HBa : [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ B'[lsingle a'] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty (j := lD) HB' Hl1c) Haa (lift_tm (j := lD) Ha Hl1c) (lift_tm (j := lD) Ha' Hl1c)).
  destruct (tcall HΔL HΔ Hw' Q' HBa Hb Hb' Eb IHb) as (Hbb & Hb'R & Hb'R1 & _ & X4).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHb) IHb) Hl2g') as X4r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmPair k k' A B a b : tySig k k' A B @ lmax k k' ])
    by (apply wf_pair; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Ha | exact Hb]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmPair k1 k1' A' B' a' b' : tySig k1 k1' A' B' @ lmax k1 k1' ])
    by (apply wf_pair; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1
                       | exact Ha'R1 | exact Hb'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmPair k1 k1' A' B' a' b' : tySig k k' A B @ lmax k k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qmg] | exact HPP]. }
  assert (Ec : tm_leq (tmPair k k' A B a b) (tmPair k1 k1' A' B' a' b')) by (cbn; repeat split; assumption).
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL k ΔL A a :: rectL k' ΔL (B[lsingle a]) b :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR k1 ΔR A' a' :: rectR k1' ΔR (B'[lsingle a']) b' :: nil).
  refine (rec_t_br 16 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm a :: GTm b :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm a' :: GTm b' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HPP) HcL0 HcRL HcR0 Ec
            (GS_pair EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Ha Ha'R Haa Ea Hb Hb'R Hbb Eb)
            (GS_pair EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_pair_inst; inst_side 16.
  - apply redt_pair_inst; inst_side 16.
Qed.

(** [W]'s scopes (M13b): the shifted [W] under a binder, computed. *)
Ltac W_cbn := cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1]; inst_cbn;
  rewrite ?subst_lshift1_ty, ?subst_lshift1, ?subst_liftshift_ty; lsh0.
(** [elimW]'s step scope (M13b): its telescope kept in notation form. *)
Ltac sr_ctx_W :=
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst mkLocs call_ty call_lv br_calls]; rewrite ?gs_cext;
  rewrite wkc_inst' by reflexivity; rewrite ?lvren_ush_uext' by reflexivity;
  repeat apply SubRel_cons; [first [exact He | exact He'r] | ..];
  repeat wkb_rw; cbn [gsubst GSubst_ctx GSubst_ty GSubst_tm]; rewrite ?uc_ext, ?gc_ext;
  rewrite ?us_wfty, ?us_wihty, ?us_wstepty, ?gs_wfty, ?gs_wihty, ?gs_wstepty; inst_cbn; lsh0.
(** [elimWf]'s step scope (M15b), likewise. *)
Ltac sr_ctx_Wf :=
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst mkLocs call_ty call_lv br_calls]; rewrite ?gs_cext;
  rewrite wkc_inst' by reflexivity; rewrite ?lvren_ush_uext' by reflexivity;
  repeat apply SubRel_cons; [first [exact He | exact He'r] | ..];
  repeat wkb_rw; cbn [gsubst GSubst_ctx GSubst_ty GSubst_tm]; rewrite ?uc_ext, ?gc_ext;
  rewrite ?us_wfcsty, ?us_wfihty, ?us_wfstepty, ?gs_wfcsty, ?gs_wfihty, ?gs_wfstepty; inst_cbn; lsh0.

(** [sup] (branch 41): the children's call at their [Π] type over the shape. *)
Lemma rec_t_sup {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' a a' f f'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ⊢[ lC ] f : tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lC ] f' : tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩ @ lmax k' (lmax k k') ] -> tm_leq f f' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ
    (mott (wrapMt MtL) (lmax k' (lmax k k')) ΔL (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) (boxt f))
    (mott (wrapMt MtR) (lmax k1' (lmax k1 k1')) ΔR (tyPi k1' (lmax k1 k1') B'[lsingle a'] (tyW k1 k1' A' B')⟨↑⟩) (boxt f'))
    (rectL (lmax k' (lmax k k')) ΔL (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) f)
    (rectR (lmax k1' (lmax k1 k1')) ΔR (tyPi k1' (lmax k1 k1') B'[lsingle a'] (tyW k1 k1' A' B')⟨↑⟩) f') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSup k k' A B a f)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSup k1 k1' A' B' a' f')))
    (rectL kL ΔL TL (tmSup k k' A B a f)) (rectR kR ΔR TR (tmSup k1 k1' A' B' a' f')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Ha Ha' Ea Hf Hf' Ef IHA IHB IHa IHf.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Qf : lequiv L' (lmax k' (lmax k k')) (lmax k1' (lmax k1 k1'))) by (apply lequiv_max; assumption).
  assert (Hwf : lwf L' (lmax k' (lmax k k'))) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2).
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R.
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  assert (HWW : [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ tyW k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_W; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact HBB]).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  (* the components and their calls *)
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X3).
  pose proof (@W_sup_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qg Qg' (lift_ty (j := lD) HA Hl1c) HAA
                (lift_ty (j := lD) HB Hl1c) HBB Haa (lift_tm (j := lD) Ha Hl1c) (lift_tm (j := lD) Ha' Hl1c)) as HFF.
  destruct (tcall HΔL HΔ Hwf Qf HFF Hf Hf' Ef IHf) as (Hff & _ & Hf'R1 & _ & X4).
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  pose proof (@W_sup_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qk Qk' (lift_ty (j := lD) HA Hl1c) HAA
                (lift_ty (j := lD) HB Hl1c) HBB Haa (lift_tm (j := lD) Ha Hl1c) (lift_tm (j := lD) Ha' Hl1c)) as HFF0.
  assert (Hf'R : [ G' ; ΔR ⊢[ lC ] f' : tyPi k' (lmax k k') B'[lsingle a'] (tyW k k' A' B')⟨↑⟩ @ lmax k' (lmax k k') ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Hf') |].
    exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HFF0)). }
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHf) IHf) Hl2g') as X4r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmSup k k' A B a f : tyW k k' A B @ lmax k k' ])
    by (apply wf_sup; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Ha | exact Hf]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSup k1 k1' A' B' a' f' : tyW k1 k1' A' B' @ lmax k1 k1' ])
    by (apply wf_sup; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1
                      | exact Ha'R1 | exact Hf'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSup k1 k1' A' B' a' f' : tyW k k' A B @ lmax k k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qmg] | exact HWW]. }
  assert (Ec : tm_leq (tmSup k k' A B a f) (tmSup k1 k1' A' B' a' f')) by (cbn; repeat split; assumption).
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL k ΔL A a
                :: rectL (lmax k' (lmax k k')) ΔL (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) f :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR k1 ΔR A' a'
                :: rectR (lmax k1' (lmax k1 k1')) ΔR (tyPi k1' (lmax k1 k1') B'[lsingle a'] (tyW k1 k1' A' B')⟨↑⟩) f' :: nil).
  refine (rec_t_br 41 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm a :: GTm f :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm a' :: GTm f' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HWW) HcL0 HcRL HcR0 Ec
            (GS_sup EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Ha Ha'R Haa Ea Hf Hf'R Hff Ef)
            (GS_sup EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               Hf'R1 Hf'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hf'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; W_cbn; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; W_cbn; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_sup_inst; inst_side 41.
  - apply redt_sup_inst; inst_side 41.
Qed.

(** The projections' common part: the pieces, the pair's call, and the
    first projections on both sides. *)
Ltac rec_t_proj_pre ΔL ΔR k k' k1 k1' A B A' B' p p' :=
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Hp Hp' Ep IHA IHB IHp;
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR;
  assert (Hn : lC <> lV) by discriminate;
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia);
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E);
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E');
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q);
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q');
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption);
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm);
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto);
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1));
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2));
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1);
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2);
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R;
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D;
  pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D;
  assert (HPP : [ G' ; ΔL ⊢[ lD ] tySig k k' A B ≅ tySig k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sig; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact HBB]);
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r;
  destruct (tcall HΔL HΔ Hwm Qm HPP Hp Hp' Ep IHp) as (Hpp & Hp'R0 & Hp'R1 & _ & X3);
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHp) IHp) Hl2g') as X3r;
  assert (Hp'R : [ G' ; ΔR ⊢[ lC ] p' : tySig k k' A' B' @ lmax k k' ])
    by (eapply wf_conv; [exact Hp'R0 |];
        apply eqty_sig; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA'R Hl1c)
                        | apply eqty_refl, (lift_ty (j := lD) HA'R Hl1c) | apply eqty_refl, (lift_ty (j := lD) HB'R Hl1c)]);
  assert (HfL0 : [ G' ; ΔL ⊢[ lC ] tmFst k k' A B p : A @ k ])
    by (apply wf_fst; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Hp]);
  assert (HfR0 : [ G' ; ΔR ⊢[ lC ] tmFst k1 k1' A' B' p' : A' @ k1 ])
    by (apply wf_fst; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1 | exact Hp'R1]);
  assert (HfRL : [ G' ; ΔL ⊢[ lC ] tmFst k1 k1' A' B' p' : A @ k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HfR0) | exact Qg] | exact HAA]);
  assert (Ef : tm_leq (tmFst k k' A B p) (tmFst k1 k1' A' B' p')) by (cbn; repeat split; assumption).

Lemma rec_t_fst {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' p p'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] A ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] A ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] p' : tySig k k' A B @ lmax k k' ] -> tm_leq p p' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tySig k k' A B) (boxt p))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tySig k1 k1' A' B') (boxt p'))
    (rectL (lmax k k') ΔL (tySig k k' A B) p) (rectR (lmax k1 k1') ΔR (tySig k1 k1' A' B') p') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmFst k k' A B p)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmFst k1 k1' A' B' p')))
    (rectL kL ΔL TL (tmFst k k' A B p)) (rectR kR ΔR TR (tmFst k1 k1' A' B' p')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  rec_t_proj_pre ΔL ΔR k k' k1 k1' A B A' B' p p'.
  pose proof HfL0 as HcL0. pose proof HfR0 as HcR0. pose proof HfRL as HcRL. pose proof Ef as Ec.
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL (lmax k k') ΔL (tySig k k' A B) p :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tySig k1 k1' A' B') p' :: nil).
  refine (rec_t_br 17 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm p :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm p' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HAA) HcL0 HcRL HcR0 Ec
            (GS_fst EP EM 17 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Hp Hp'R Hpp Ep)
            (GS_fst EP EM 17 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Hp'R1 Hp'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hp'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_fst_inst; inst_side 17.
  - apply redt_fst_inst; inst_side 17.
Qed.

Lemma rec_t_snd {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' p p'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k' kL -> lequiv L' k' kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] B[lsingle (tmFst k k' A B p)] ≅ TL @ k' ] -> [ G' ; ΔL ⊢[ lD ] B[lsingle (tmFst k k' A B p)] ≅ TR @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] p' : tySig k k' A B @ lmax k k' ] -> tm_leq p p' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tySig k k' A B) (boxt p))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tySig k1 k1' A' B') (boxt p'))
    (rectL (lmax k k') ΔL (tySig k k' A B) p) (rectR (lmax k1 k1') ΔR (tySig k1 k1' A' B') p') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSnd k k' A B p)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSnd k1 k1' A' B' p')))
    (rectL kL ΔL TL (tmSnd k k' A B p)) (rectR kR ΔR TR (tmSnd k1 k1' A' B' p')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  rec_t_proj_pre ΔL ΔR k k' k1 k1' A B A' B' p p'.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c HfL0 HfRL Ef) Hl1c) as Hff.
  assert (HBf : [ G' ; ΔL ⊢[ lD ] B[lsingle (tmFst k k' A B p)] ≅ B'[lsingle (tmFst k1 k1' A' B' p')] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty (j := lD) HB' Hl1c) Hff (lift_tm (j := lD) HfL0 Hl1c)
                (lift_tm (j := lD) HfRL Hl1c)).
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmSnd k k' A B p : B[lsingle (tmFst k k' A B p)] @ k' ])
    by (apply wf_snd; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Hp]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSnd k1 k1' A' B' p' : B'[lsingle (tmFst k1 k1' A' B' p')] @ k1' ])
    by (apply wf_snd; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1 | exact Hp'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSnd k1 k1' A' B' p' : B[lsingle (tmFst k k' A B p)] @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg'] | exact HBf]. }
  assert (Ec : tm_leq (tmSnd k k' A B p) (tmSnd k1 k1' A' B' p')) by (cbn; repeat split; assumption).
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL (lmax k k') ΔL (tySig k k' A B) p :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tySig k1 k1' A' B') p' :: nil).
  refine (rec_t_br 18 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm p :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm p' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HBf) HcL0 HcRL HcR0 Ec
            (GS_fst EP EM 18 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Hp Hp'R Hpp Ep)
            (GS_fst EP EM 18 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Hp'R1 Hp'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hp'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_snd_inst; inst_side 18.
  - apply redt_snd_inst; inst_side 18.
Qed.

(** ** The identity type (M11b) *)

Lemma rec_T_id {ΔL ΔR kL kR k k1 A A' a a' b b'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ⊢[ lC ] b : A @ k ] -> [ G' ; ΔL ⊢[ lC ] b' : A @ k ] -> tm_leq b b' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt b)) (mott (wrapMt MtR) k1 ΔR A' (boxt b'))
    (rectL k ΔL A b) (rectR k1 ΔR A' b') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyId k A a b)))
    (motT (wrapMT MTR) kR ΔR (boxT (tyId k1 A' a' b')))
    (recTL kL ΔL (tyId k A a b)) (recTR kR ΔR (tyId k1 A' a' b')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HA HA' EA Ha Ha' Ea Hb Hb' Eb IHA IHa IHb.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X2).
  destruct (tcall HΔL HΔ Hw Q HAA Hb Hb' Eb IHb) as (Hbb & Hb'R & Hb'R1 & _ & X3).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHb) IHb) Hl2g') as X3r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tyId k A a b @ k ])
    by (apply wft_id; [exact Hn | rewrite EL; exact Hw | exact HA | exact Ha | exact Hb]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyId k1 A' a' b' @ k1 ])
    by (apply wft_id; [exact Hn | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1 | exact Hb'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyId k1 A' a' b' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]).
  assert (Ec : ty_leq (tyId k A a b) (tyId k1 A' a' b')) by (cbn; repeat split; assumption).
  refine (rec_T_br 21 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm a :: GTm b :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: GTm b' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: rectL k ΔL A b :: nil)
            (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: rectR k1 ΔR A' b' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HcL0 HcRL HcR0 Ec
            (GS_id EP EM 21 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea Hb Hb'R Hbb Eb)
            (GS_id EP EM 21 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_id_inst; inst_side 21.
  - apply redT_id_inst; inst_side 21.
Qed.

Lemma rec_t_codeid {ΔL ΔR kL kR TL TR k k1 s s' t t' u u'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc k) kL -> lequiv L' (lsuc k) kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tyU k ≅ TL @ lsuc k ] -> [ G' ; ΔL ⊢[ lD ] tyU k ≅ TR @ lsuc k ] ->
  [ G' ; ΔL ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s' : tyU k @ lsuc k ] -> tm_leq s s' ->
  [ G' ; ΔL ⊢[ lC ] t : tyEl k s @ k ] -> [ G' ; ΔL ⊢[ lC ] t' : tyEl k s @ k ] -> tm_leq t t' ->
  [ G' ; ΔL ⊢[ lC ] u : tyEl k s @ k ] -> [ G' ; ΔL ⊢[ lC ] u' : tyEl k s @ k ] -> tm_leq u u' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s'))
    (rectL (lsuc k) ΔL (tyU k) s) (rectR (lsuc k1) ΔR (tyU k1) s') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tyEl k s) (boxt t)) (mott (wrapMt MtR) k1 ΔR (tyEl k1 s') (boxt t'))
    (rectL k ΔL (tyEl k s) t) (rectR k1 ΔR (tyEl k1 s') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tyEl k s) (boxt u)) (mott (wrapMt MtR) k1 ΔR (tyEl k1 s') (boxt u'))
    (rectL k ΔL (tyEl k s) u) (rectR k1 ΔR (tyEl k1 s') u') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmId k s t u)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmId k1 s' t' u')))
    (rectL kL ΔL TL (tmId k s t u)) (rectR kR ΔR TR (tmId k1 s' t' u')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR Hs Hs' Es Ht Ht' Et Hu Hu' Eu IHs IHt IHu.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HUU : [ G' ; ΔL ⊢[ lD ] tyU k ≅ tyU k1 @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | exact Qg]).
  (* the pieces and their calls *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) HUU Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1).
  assert (HEl : [ G' ; ΔL ⊢[ lD ] tyEl k s ≅ tyEl k1 s' @ k ])
    by (apply eqty_El; [discriminate | exact Qg | exact Hss]).
  destruct (tcall HΔL HΔ Hw Q HEl Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X2).
  destruct (tcall HΔL HΔ Hw Q HEl Hu Hu' Eu IHu) as (Huu & _ & Hu'R1 & _ & X3).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHu) IHu) Hl2g') as X3r.
  (* the right pieces at the left level *)
  assert (HEl' : [ G' ; ΔL ⊢[ lD ] tyEl k s' ≅ tyEl k s @ k ]).
  { apply eqty_El; [discriminate | rewrite EL; exact (lequiv_refl _ _ Hw) | apply eqtm_sym; exact Hss]. }
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R.
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyEl k s' @ k ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Ht') | exact (ctxconv_eqty HΔ (i := lD) eq_refl HEl')]. }
  assert (Hu'R : [ G' ; ΔR ⊢[ lC ] u' : tyEl k s' @ k ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Hu') | exact (ctxconv_eqty HΔ (i := lD) eq_refl HEl')]. }
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmId k s t u : tyU k @ lsuc k ])
    by (apply wf_code_id; [exact Hn | rewrite EL; exact Hw | exact Hs | exact Ht | exact Hu]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmId k1 s' t' u' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_id; [exact Hn | rewrite EL; exact Hw1 | exact Hs'R1 | exact Ht'R1 | exact Hu'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmId k1 s' t' u' : tyU k @ lsuc k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                      | exact (lequiv_suc _ _ _ Qg)] | exact HUU]. }
  assert (Ec : tm_leq (tmId k s t u) (tmId k1 s' t' u')) by (cbn; repeat split; assumption).
  refine (rec_t_br 22 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTm s :: GTm t :: GTm u :: nil)
            (GCtx ΔR :: GTm s' :: GTm t' :: GTm u' :: nil)
            (rectL (lsuc k) ΔL (tyU k) s :: rectL k ΔL (tyEl k s) t :: rectL k ΔL (tyEl k s) u :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s' :: rectR k1 ΔR (tyEl k1 s') t' :: rectR k1 ΔR (tyEl k1 s') u' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HUU) HcL0 HcRL HcR0 Ec
            (GS_codeid EP EM 22 eq_refl eq_refl Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et Hu Hu'R Huu Eu)
            (GS_codeid EP EM 22 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               Hs'R1 Hs'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)
               Hu'R1 Hu'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hu'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codeid_inst; inst_side 22.
  - apply redt_codeid_inst; inst_side 22.
Qed.

Lemma rec_t_refl {ΔL ΔR kL kR TL TR k k1 A A' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tyId k A a a ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] tyId k A a a ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmRefl k A a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmRefl k1 A' a')))
    (rectL kL ΔL TL (tmRefl k A a)) (rectR kR ΔR TR (tmRefl k1 A' a')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR HA HA' EA Ha Ha' Ea IHA IHa.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X2r.
  assert (HII : [ G' ; ΔL ⊢[ lD ] tyId k A a a ≅ tyId k1 A' a' a' @ k ])
    by (apply eqty_id; [discriminate | exact Qg | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact Haa | exact Haa]).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmRefl k A a : tyId k A a a @ k ])
    by (apply wf_idrefl; [exact Hn | rewrite EL; exact Hw | exact HA | exact Ha]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmRefl k1 A' a' : tyId k1 A' a' a' @ k1 ])
    by (apply wf_idrefl; [exact Hn | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmRefl k1 A' a' : tyId k A a a @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                    | exact HII]. }
  assert (Ec : tm_leq (tmRefl k A a) (tmRefl k1 A' a')) by (cbn; repeat split; assumption).
  refine (rec_t_br 23 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm a :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: nil) (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HII) HcL0 HcRL HcR0 Ec
            (GS_refl EP EM 23 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea)
            (GS_refl EP EM 23 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_refl_inst; inst_side 23.
  - apply redt_refl_inst; inst_side 23.
Qed.


(** ** Strict equality (M10c), as the identity type and the unit type *)

Lemma rec_T_seq {ΔL ΔR kL kR k k1 A A' a a' b b'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ⊢[ lC ] b : A @ k ] -> [ G' ; ΔL ⊢[ lC ] b' : A @ k ] -> tm_leq b b' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt b)) (mott (wrapMt MtR) k1 ΔR A' (boxt b'))
    (rectL k ΔL A b) (rectR k1 ΔR A' b') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tySEq k A a b)))
    (motT (wrapMT MTR) kR ΔR (boxT (tySEq k1 A' a' b')))
    (recTL kL ΔL (tySEq k A a b)) (recTR kR ΔR (tySEq k1 A' a' b')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HA HA' EA Ha Ha' Ea Hb Hb' Eb IHA IHa IHb.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X2).
  destruct (tcall HΔL HΔ Hw Q HAA Hb Hb' Eb IHb) as (Hbb & Hb'R & Hb'R1 & _ & X3).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHb) IHb) Hl2g') as X3r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tySEq k A a b @ k ])
    by (apply wft_seq; [exact Hn | rewrite EL; exact Hw | exact HA | exact Ha | exact Hb]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tySEq k1 A' a' b' @ k1 ])
    by (apply wft_seq; [exact Hn | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1 | exact Hb'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tySEq k1 A' a' b' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]).
  assert (Ec : ty_leq (tySEq k A a b) (tySEq k1 A' a' b')) by (cbn; repeat split; assumption).
  refine (rec_T_br 25 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm a :: GTm b :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: GTm b' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: rectL k ΔL A b :: nil)
            (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: rectR k1 ΔR A' b' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HcL0 HcRL HcR0 Ec
            (GS_id EP EM 25 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea Hb Hb'R Hbb Eb)
            (GS_id EP EM 25 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_seq_inst; inst_side 25.
  - apply redT_seq_inst; inst_side 25.
Qed.

Lemma rec_t_codeseq {ΔL ΔR kL kR TL TR k k1 s s' t t' u u'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc k) kL -> lequiv L' (lsuc k) kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tyU k ≅ TL @ lsuc k ] -> [ G' ; ΔL ⊢[ lD ] tyU k ≅ TR @ lsuc k ] ->
  [ G' ; ΔL ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s' : tyU k @ lsuc k ] -> tm_leq s s' ->
  [ G' ; ΔL ⊢[ lC ] t : tyEl k s @ k ] -> [ G' ; ΔL ⊢[ lC ] t' : tyEl k s @ k ] -> tm_leq t t' ->
  [ G' ; ΔL ⊢[ lC ] u : tyEl k s @ k ] -> [ G' ; ΔL ⊢[ lC ] u' : tyEl k s @ k ] -> tm_leq u u' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s'))
    (rectL (lsuc k) ΔL (tyU k) s) (rectR (lsuc k1) ΔR (tyU k1) s') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tyEl k s) (boxt t)) (mott (wrapMt MtR) k1 ΔR (tyEl k1 s') (boxt t'))
    (rectL k ΔL (tyEl k s) t) (rectR k1 ΔR (tyEl k1 s') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tyEl k s) (boxt u)) (mott (wrapMt MtR) k1 ΔR (tyEl k1 s') (boxt u'))
    (rectL k ΔL (tyEl k s) u) (rectR k1 ΔR (tyEl k1 s') u') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSEq k s t u)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSEq k1 s' t' u')))
    (rectL kL ΔL TL (tmSEq k s t u)) (rectR kR ΔR TR (tmSEq k1 s' t' u')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR Hs Hs' Es Ht Ht' Et Hu Hu' Eu IHs IHt IHu.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HUU : [ G' ; ΔL ⊢[ lD ] tyU k ≅ tyU k1 @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | exact Qg]).
  (* the pieces and their calls *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) HUU Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1).
  assert (HEl : [ G' ; ΔL ⊢[ lD ] tyEl k s ≅ tyEl k1 s' @ k ])
    by (apply eqty_El; [discriminate | exact Qg | exact Hss]).
  destruct (tcall HΔL HΔ Hw Q HEl Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X2).
  destruct (tcall HΔL HΔ Hw Q HEl Hu Hu' Eu IHu) as (Huu & _ & Hu'R1 & _ & X3).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHu) IHu) Hl2g') as X3r.
  (* the right pieces at the left level *)
  assert (HEl' : [ G' ; ΔL ⊢[ lD ] tyEl k s' ≅ tyEl k s @ k ]).
  { apply eqty_El; [discriminate | rewrite EL; exact (lequiv_refl _ _ Hw) | apply eqtm_sym; exact Hss]. }
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R.
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyEl k s' @ k ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Ht') | exact (ctxconv_eqty HΔ (i := lD) eq_refl HEl')]. }
  assert (Hu'R : [ G' ; ΔR ⊢[ lC ] u' : tyEl k s' @ k ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Hu') | exact (ctxconv_eqty HΔ (i := lD) eq_refl HEl')]. }
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmSEq k s t u : tyU k @ lsuc k ])
    by (apply wf_code_seq; [exact Hn | rewrite EL; exact Hw | exact Hs | exact Ht | exact Hu]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSEq k1 s' t' u' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_seq; [exact Hn | rewrite EL; exact Hw1 | exact Hs'R1 | exact Ht'R1 | exact Hu'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSEq k1 s' t' u' : tyU k @ lsuc k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                      | exact (lequiv_suc _ _ _ Qg)] | exact HUU]. }
  assert (Ec : tm_leq (tmSEq k s t u) (tmSEq k1 s' t' u')) by (cbn; repeat split; assumption).
  refine (rec_t_br 26 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTm s :: GTm t :: GTm u :: nil)
            (GCtx ΔR :: GTm s' :: GTm t' :: GTm u' :: nil)
            (rectL (lsuc k) ΔL (tyU k) s :: rectL k ΔL (tyEl k s) t :: rectL k ΔL (tyEl k s) u :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s' :: rectR k1 ΔR (tyEl k1 s') t' :: rectR k1 ΔR (tyEl k1 s') u' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HUU) HcL0 HcRL HcR0 Ec
            (GS_codeid EP EM 26 eq_refl eq_refl Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et Hu Hu'R Huu Eu)
            (GS_codeid EP EM 26 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               Hs'R1 Hs'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)
               Hu'R1 Hu'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hu'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codeseq_inst; inst_side 26.
  - apply redt_codeseq_inst; inst_side 26.
Qed.

Lemma rec_t_srefl {ΔL ΔR kL kR TL TR k k1 A A' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tySEq k A a a ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] tySEq k A a a ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (srefl k A a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (srefl k1 A' a')))
    (rectL kL ΔL TL (srefl k A a)) (rectR kR ΔR TR (srefl k1 A' a')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR HA HA' EA Ha Ha' Ea IHA IHa.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X2r.
  assert (HII : [ G' ; ΔL ⊢[ lD ] tySEq k A a a ≅ tySEq k1 A' a' a' @ k ])
    by (apply eqty_seq; [discriminate | exact Qg | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact Haa | exact Haa]).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] srefl k A a : tySEq k A a a @ k ])
    by (apply wf_srefl; [exact Hn | rewrite EL; exact Hw | exact HA | exact Ha]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] srefl k1 A' a' : tySEq k1 A' a' a' @ k1 ])
    by (apply wf_srefl; [exact Hn | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] srefl k1 A' a' : tySEq k A a a @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                    | exact HII]. }
  assert (Ec : tm_leq (srefl k A a) (srefl k1 A' a')) by (cbn; repeat split; assumption).
  refine (rec_t_br 29 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm a :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: nil) (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HII) HcL0 HcRL HcR0 Ec
            (GS_refl EP EM 29 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea)
            (GS_refl EP EM 29 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_srefl_inst; inst_side 29.
  - apply redt_srefl_inst; inst_side 29.
Qed.

Lemma rec_T_sempty {ΔL ΔR kL kR k k'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tySEmpty k))) (motT (wrapMT MTR) kR ΔR (boxT (tySEmpty k')))
    (recTL kL ΔL (tySEmpty k)) (recTR kR ΔR (tySEmpty k')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' E.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (HU : forall Δ j, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> [ G' ; Δ ⊢[ lC ] tySEmpty j @ j ])
    by (intros; apply wft_sempty; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tySEmpty k' @ k ])
    by (eapply wft_lconv; [exact (HU _ _ HΔL Hw') | rewrite EL; exact Q]).
  refine (rec_T_br 27 (k :: nil) (k' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q (HU _ _ HΔL Hw) HcRL (HU _ _ HΔR Hw') E
            (GS_ctx0 EP EM 27 (k :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 27 (k' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redT_sempty_inst; inst_side 27.
  - apply redT_sempty_inst; inst_side 27.
Qed.

Lemma rec_t_codesempty {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc j) kL -> lequiv L' (lsuc j) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU j ≅ TL @ lsuc j ] -> [ G' ; ΔL ⊢[ lD ] tyU j ≅ TR @ lsuc j ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSEmpty j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmSEmpty j')))
    (rectL kL ΔL TL (tmSEmpty j)) (rectR kR ΔR TR (tmSEmpty j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q1 : lequiv L' (lsuc j) (lsuc j')) by (apply lequiv_suc; exact Q).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; exact Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmSEmpty i : tyU i @ lsuc i ])
    by (intros; apply wf_code_sempty; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSEmpty j' : tyU j @ lsuc j ]).
  { eapply wf_lconv; [| rewrite EL; exact Q1].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q1]. }
  refine (rec_t_br 28 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q1 HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 28 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 28 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_codesempty_inst; inst_side 28.
  - apply redt_codesempty_inst; inst_side 28.
Qed.

(** [sEmpty]'s eliminator: the motive's call at the motive's level, the
    scrutinee's at [sEmpty]'s. *)
Lemma rec_t_elimSEmpty {ΔL ΔR kL kR TL TR k k' k1 k1' M M' e0 e0'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k' kL -> lequiv L' k' kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] M ≅ TL @ k' ] -> [ G' ; ΔL ⊢[ lD ] M ≅ TR @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] M @ k' ] -> [ G' ; ΔL ⊢[ lC ] M' @ k' ] -> ty_leq M M' ->
  [ G' ; ΔL ⊢[ lC ] e0 : tySEmpty k @ k ] -> [ G' ; ΔL ⊢[ lC ] e0' : tySEmpty k @ k ] -> tm_leq e0 e0' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT M)) (motT (wrapMT MTR) k1' ΔR (boxT M'))
    (recTL k' ΔL M) (recTR k1' ΔR M') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tySEmpty k) (boxt e0))
    (mott (wrapMt MtR) k1 ΔR (tySEmpty k1) (boxt e0'))
    (rectL k ΔL (tySEmpty k) e0) (rectR k1 ΔR (tySEmpty k1) e0') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (elimSEmpty k k' M e0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (elimSEmpty k1 k1' M' e0')))
    (rectL kL ΔL TL (elimSEmpty k k' M e0)) (rectR kR ΔR TR (elimSEmpty k1 k1' M' e0')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HM HM' EM1 He0 He0' Ee IHM IHe.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the motive and the scrutinee, and their calls *)
  destruct (Tcall HΔL HΔ Hw' Q' HM HM' EM1 IHM) as (HMM & HM'R & HM'R1 & _ & _ & X1).
  assert (HSE : [ G' ; ΔL ⊢[ lD ] tySEmpty k ≅ tySEmpty k1 @ k ])
    by (apply eqty_sempty; [discriminate | exact HΔL | exact Qg]).
  destruct (tcall HΔL HΔ Hw Q HSE He0 He0' Ee IHe) as (Hee & He'R0 & He'R1 & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHe) IHe) Hl2g') as X2r.
  (* the right scrutinee at the left level's [sEmpty] *)
  assert (He'R : [ G' ; ΔR ⊢[ lC ] e0' : tySEmpty k @ k ]).
  { eapply wf_conv; [exact He'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl HSE)]. }
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] elimSEmpty k k' M e0 : M @ k' ])
    by (apply wf_elimSEmpty; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HM | exact He0]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] elimSEmpty k1 k1' M' e0' : M' @ k1' ])
    by (apply wf_elimSEmpty; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HM'R1 | exact He'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] elimSEmpty k1 k1' M' e0' : M @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg']
                    | exact HMM]. }
  assert (Ec : tm_leq (elimSEmpty k k' M e0) (elimSEmpty k1 k1' M' e0')) by (cbn; repeat split; assumption).
  refine (rec_t_br 30 (k' :: k :: nil) (k1' :: k1 :: nil) (GCtx ΔL :: GTy M :: GTm e0 :: nil)
            (GCtx ΔR :: GTy M' :: GTm e0' :: nil)
            (recTL k' ΔL M :: rectL k ΔL (tySEmpty k) e0 :: nil)
            (recTR k1' ΔR M' :: rectR k1 ΔR (tySEmpty k1) e0' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E' (Forall2_cons _ _ E (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HMM) HcL0 HcRL HcR0 Ec
            (GS_elimSEmpty EP EM Hσ HΔL HΔ HM HM'R HMM EM1 He0 He'R Hee Ee)
            (GS_elimSEmpty EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HM'R1 Hl1c)) (ty_leq_refl _)
               He'R1 He'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) He'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_elimSEmpty_inst; inst_side 30.
  - apply redt_elimSEmpty_inst; inst_side 30.
Qed.

(** [J]'s motive context shifts its carrier and point: the shifts are
    computed before the global substitution reaches them. *)
Ltac J_cbn := try unfold lsingle2; cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1]; inst_cbn;
  rewrite ?subst_lshift1_ty, ?subst_lshift1; lsh0.
Ltac J_res := cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar]; wkb_rw; J_cbn; rewrite ?Nat.add_0_r; reflexivity.

Lemma rec_t_J {ΔL ΔR kL kR TL TR k k' k1 k1' A A' a a' M M' c c' u u' e0 e0'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k' kL -> lequiv L' k' kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle2 u e0] ≅ TL @ k' ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle2 u e0] ≅ TR @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ] ->
  [ G' ; ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lC ] M @ k' ] ->
  [ G' ; ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lC ] M' @ k' ] -> ty_leq M M' ->
  [ G' ; ΔL ⊢[ lC ] c : M[lsingle2 a (tmRefl k A a)] @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] c' : M[lsingle2 a (tmRefl k A a)] @ k' ] -> tm_leq c c' ->
  [ G' ; ΔL ⊢[ lC ] u : A @ k ] -> [ G' ; ΔL ⊢[ lC ] u' : A @ k ] -> tm_leq u u' ->
  [ G' ; ΔL ⊢[ lC ] e0 : tyId k A a u @ k ] -> [ G' ; ΔL ⊢[ lC ] e0' : tyId k A a u @ k ] -> tm_leq e0 e0' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) (boxT M))
    (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1 ,, tyId k1 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ k1) (boxT M'))
    (recTL k' (ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) M)
    (recTR k1' (ΔR ,, A' @ k1 ,, tyId k1 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ k1) M') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' ΔL (M[lsingle2 a (tmRefl k A a)]) (boxt c))
    (mott (wrapMt MtR) k1' ΔR (M'[lsingle2 a' (tmRefl k1 A' a')]) (boxt c'))
    (rectL k' ΔL (M[lsingle2 a (tmRefl k A a)]) c) (rectR k1' ΔR (M'[lsingle2 a' (tmRefl k1 A' a')]) c') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt u)) (mott (wrapMt MtR) k1 ΔR A' (boxt u'))
    (rectL k ΔL A u) (rectR k1 ΔR A' u') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tyId k A a u) (boxt e0))
    (mott (wrapMt MtR) k1 ΔR (tyId k1 A' a' u') (boxt e0'))
    (rectL k ΔL (tyId k A a u) e0) (rectR k1 ΔR (tyId k1 A' a' u') e0') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmJ k k' A a M c u e0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmJ k1 k1' A' a' M' c' u' e0')))
    (rectL kL ΔL TL (tmJ k k' A a M c u e0)) (rectR kR ΔR TR (tmJ k1 k1' A' a' M' c' u' e0')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA Ha Ha' Ea HI HM HM' EM1 Hc Hc' Ec Hu Hu' Eu
    He0 He0' Ee IHA IHa IHM IHc IHu IHe.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the carrier and the point *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X2).
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (lift_ty (j := lD) HA' Hl1c) as HA'D.
  pose proof (lift_tm (j := lD) Ha Hl1c) as HaD. pose proof (lift_tm (j := lD) Ha' Hl1c) as Ha'D.
  (* the motive, over the right context at both levels *)
  pose proof (J_ctx_eq' (i := lD) eq_refl ltac:(discriminate) Qg HΔ HAD HAA Haa) as CM1.
  pose proof (J_ctx_eq' (i := lD) eq_refl ltac:(discriminate) Qk HΔ HAD HAA Haa) as CM.
  pose proof (eqctx_wf_l (i := lD) eq_refl CM) as HΔM.
  destruct (Tcall HΔM CM1 Hw' Q' HM HM' EM1 IHM) as (HMM & _ & HM'R1 & _ & _ & X3).
  pose proof (ctxconv_ty CM (i := lC) eq_refl HM') as HM'R.
  (* the endpoint and the path *)
  destruct (tcall HΔL HΔ Hw Q HAA Hu Hu' Eu IHu) as (Huu & Hu'R & Hu'R1 & _ & X5).
  assert (HId1 : [ G' ; ΔL ⊢[ lD ] tyId k A a u ≅ tyId k1 A' a' u' @ k ])
    by (apply eqty_id; [discriminate | exact Qg | exact HAD | exact HAA | exact Haa | exact Huu]).
  destruct (tcall HΔL HΔ Hw Q HId1 He0 He0' Ee IHe) as (Hee & _ & He'R1 & _ & X6).
  (* the motive's instances *)
  pose proof (lift_ty (j := lD) HM' Hl1c) as HM'D.
  pose proof (lift_tm (j := lD) Hu Hl1c) as HuD. pose proof (lift_tm (j := lD) Hu' Hl1c) as Hu'D.
  pose proof (lift_tm (j := lD) He0 Hl1c) as HeD. pose proof (lift_tm (j := lD) He0' Hl1c) as He'D.
  destruct (J_facts_D (l3 := k1) Qg HAD HAA HA'D HaD Haa Ha'D HMM HM'D HuD Huu Hu'D HeD Hee He'D)
    as (_ & Hc1 & Hr1 & _).
  destruct (J_facts_D (l3 := k) Qk HAD HAA HA'D HaD Haa Ha'D HMM HM'D HuD Huu Hu'D HeD Hee He'D)
    as (_ & Hc0 & _ & HI0).
  destruct (tcall HΔL HΔ Hw' Q' Hc1 Hc Hc' Ec IHc) as (Hcc & _ & Hc'R1 & _ & X4).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHc) IHc) Hl2g') as X4r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHu) IHu) Hl2g') as X5r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHe) IHe) Hl2g') as X6r.
  (* the right pieces at the left levels *)
  assert (Hc'R : [ G' ; ΔR ⊢[ lC ] c' : M'[lsingle2 a' (tmRefl k A' a')] @ k' ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Hc')
                    | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ Hc0))]. }
  assert (He'R : [ G' ; ΔR ⊢[ lC ] e0' : tyId k A' a' u' @ k ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl He0')
                    | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HI0))]. }
  (* the codes *)
  assert (HI' : [ G' ; ΔR ,, A' @ k1 ⊢[ lC ] tyId k1 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ k1 ]).
  { apply wf_Jid_g; [exact Hn | rewrite EL; exact Hw1 | | exact HA'R1 | exact Ha'R1].
    apply wfc_ext; [exact HΔR | exact (lift_ty (j := lD) HA'R1 Hl1c) | rewrite EL; exact Hw1]. }
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmJ k k' A a M c u e0 : M[lsingle2 u e0] @ k' ])
    by (apply wf_J; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact Ha | exact HI
                    | exact HM | exact Hc | exact Hu | exact He0]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmJ k1 k1' A' a' M' c' u' e0' : M'[lsingle2 u' e0'] @ k1' ])
    by (apply wf_J; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact Ha'R1 | exact HI'
                    | exact HM'R1 | exact Hc'R1 | exact Hu'R1 | exact He'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmJ k1 k1' A' a' M' c' u' e0' : M[lsingle2 u e0] @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg']
                    | exact Hr1]. }
  assert (Ecc : tm_leq (tmJ k k' A a M c u e0) (tmJ k1 k1' A' a' M' c' u' e0')) by (cbn; repeat split; assumption).
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HM'R1 Hl1c) as HM'R1D.
  refine (rec_t_br 24 (k :: k' :: nil) (k1 :: k1' :: nil)
            (GCtx ΔL :: GTy A :: GTm a :: GTy M :: GTm c :: GTm u :: GTm e0 :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: GTy M' :: GTm c' :: GTm u' :: GTm e0' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: recTL k' (ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) M
             :: rectL k' ΔL (M[lsingle2 a (tmRefl k A a)]) c :: rectL k ΔL A u :: rectL k ΔL (tyId k A a u) e0 :: nil)
            (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: recTR k1' (ΔR ,, A' @ k1 ,, tyId k1 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ k1) M'
             :: rectR k1' ΔR (M'[lsingle2 a' (tmRefl k1 A' a')]) c' :: rectR k1 ΔR A' u'
             :: rectR k1 ΔR (tyId k1 A' a' u') e0' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) HcL0 HcRL HcR0 Ecc
            (GS_J EP EM Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea HM HM'R HMM EM1 Hc Hc'R Hcc Ec Hu Hu'R Huu Eu
               He0 He'R Hee Ee)
            (GS_J EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HA'R1 HA'R1 (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ HM'R1D) (ty_leq_refl _)
               Hc'R1 Hc'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hc'R1 Hl1c)) (tm_leq_refl _)
               Hu'R1 Hu'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hu'R1 Hl1c)) (tm_leq_refl _)
               He'R1 He'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) He'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; J_cbn; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6].
  - sr_ctx; J_cbn; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_J_inst; inst_side 24.
  - apply redt_J_inst; inst_side 24.
Qed.

(** ** The empty type and binary sums (M12c) *)

Lemma rec_T_empty {ΔL ΔR kL kR k k'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyEmpty k))) (motT (wrapMT MTR) kR ΔR (boxT (tyEmpty k')))
    (recTL kL ΔL (tyEmpty k)) (recTR kR ΔR (tyEmpty k')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' E.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (HU : forall Δ j, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> [ G' ; Δ ⊢[ lC ] tyEmpty j @ j ])
    by (intros; apply wft_empty; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyEmpty k' @ k ])
    by (eapply wft_lconv; [exact (HU _ _ HΔL Hw') | rewrite EL; exact Q]).
  refine (rec_T_br 31 (k :: nil) (k' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q (HU _ _ HΔL Hw) HcRL (HU _ _ HΔR Hw') E
            (GS_ctx0 EP EM 31 (k :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 31 (k' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redT_empty_inst; inst_side 31.
  - apply redT_empty_inst; inst_side 31.
Qed.

Lemma rec_t_codeempty {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc j) kL -> lequiv L' (lsuc j) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU j ≅ TL @ lsuc j ] -> [ G' ; ΔL ⊢[ lD ] tyU j ≅ TR @ lsuc j ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmEmpty j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmEmpty j')))
    (rectL kL ΔL TL (tmEmpty j)) (rectR kR ΔR TR (tmEmpty j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q1 : lequiv L' (lsuc j) (lsuc j')) by (apply lequiv_suc; exact Q).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; exact Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmEmpty i : tyU i @ lsuc i ])
    by (intros; apply wf_code_empty; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmEmpty j' : tyU j @ lsuc j ]).
  { eapply wf_lconv; [| rewrite EL; exact Q1].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q1]. }
  refine (rec_t_br 32 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q1 HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 32 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 32 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_codeempty_inst; inst_side 32.
  - apply redt_codeempty_inst; inst_side 32.
Qed.

(** [Empty]'s eliminator: the motive's call over the scrutinee, the
    scrutinee's at [Empty]'s level. *)
Lemma rec_t_elimEmpty {ΔL ΔR kL kR TL TR k k' k1 k1' M M' t t'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TR @ k ] ->
  [ G' ; ΔL ,, tyEmpty k' @ k' ⊢[ lC ] M @ k ] -> [ G' ; ΔL ,, tyEmpty k' @ k' ⊢[ lC ] M' @ k ] -> ty_leq M M' ->
  [ G' ; ΔL ⊢[ lC ] t : tyEmpty k' @ k' ] -> [ G' ; ΔL ⊢[ lC ] t' : tyEmpty k' @ k' ] -> tm_leq t t' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k (ΔL ,, tyEmpty k' @ k') (boxT M))
    (motT (wrapMT MTR) k1 (ΔR ,, tyEmpty k1' @ k1') (boxT M'))
    (recTL k (ΔL ,, tyEmpty k' @ k') M) (recTR k1 (ΔR ,, tyEmpty k1' @ k1') M') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' ΔL (tyEmpty k') (boxt t))
    (mott (wrapMt MtR) k1' ΔR (tyEmpty k1') (boxt t'))
    (rectL k' ΔL (tyEmpty k') t) (rectR k1' ΔR (tyEmpty k1') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (elimEmpty k k' M t)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (elimEmpty k1 k1' M' t')))
    (rectL kL ΔL TL (elimEmpty k k' M t)) (rectR kR ΔR TR (elimEmpty k1 k1' M' t')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HM HM' EM1 Ht Ht' Et IHM IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the scrutinee's type, and the motive's context *)
  assert (HED : [ G' ; ΔL ⊢[ lD ] tyEmpty k' @ k' ])
    by (apply wft_empty; [discriminate | exact HΔL | rewrite EL; exact Hw']).
  assert (HEE : forall j, lequiv L' k' j -> [ G' ; ΔL ⊢[ lD ] tyEmpty k' ≅ tyEmpty j @ k' ])
    by (intros; apply eqty_empty; [discriminate | exact HΔL | rewrite EL; assumption]).
  assert (CE : [ G' ⊢[ lD ] ΔL ,, tyEmpty k' @ k' ≅ ΔR ,, tyEmpty k' @ k' ])
    by (apply eqc_ext; [exact HΔ | exact HED | exact (HEE _ (lequiv_refl _ _ Hw')) | rewrite EL; exact (lequiv_refl _ _ Hw')]).
  assert (CE1 : [ G' ⊢[ lD ] ΔL ,, tyEmpty k' @ k' ≅ ΔR ,, tyEmpty k1' @ k1' ])
    by (apply eqc_ext; [exact HΔ | exact HED | exact (HEE _ Q') | exact Qg']).
  pose proof (eqctx_wf_l (i := lD) eq_refl CE) as HΔE.
  (* the motive and the scrutinee, and their calls *)
  destruct (Tcall HΔE CE1 Hw Q HM HM' EM1 IHM) as (HMM & _ & HM'R1 & _ & _ & X1).
  pose proof (ctxconv_ty CE (i := lC) eq_refl HM') as HM'R.
  destruct (tcall HΔL HΔ Hw' Q' (HEE _ Q') Ht Ht' Et IHt) as (Htt & Ht'R0 & Ht'R1 & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r.
  (* the right scrutinee at the left level's [Empty] *)
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyEmpty k' @ k' ]).
  { eapply wf_conv; [exact Ht'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (HEE _ Q'))]. }
  (* the result types *)
  assert (Hr1 : [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k ])
    by exact (eqty_subst_single_D HMM (lift_ty (j := lD) HM' Hl1c) Htt (lift_tm (j := lD) Ht Hl1c)
                (lift_tm (j := lD) Ht' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] elimEmpty k k' M t : M[lsingle t] @ k ])
    by (apply wf_elimEmpty; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HM | exact Ht]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] elimEmpty k1 k1' M' t' : M'[lsingle t'] @ k1 ])
    by (apply wf_elimEmpty; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HM'R1 | exact Ht'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] elimEmpty k1 k1' M' t' : M[lsingle t] @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                    | exact Hr1]. }
  assert (Ec : tm_leq (elimEmpty k k' M t) (elimEmpty k1 k1' M' t')) by (cbn; repeat split; assumption).
  refine (rec_t_br 33 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy M :: GTm t :: nil)
            (GCtx ΔR :: GTy M' :: GTm t' :: nil)
            (recTL k (ΔL ,, tyEmpty k' @ k') M :: rectL k' ΔL (tyEmpty k') t :: nil)
            (recTR k1 (ΔR ,, tyEmpty k1' @ k1') M' :: rectR k1' ΔR (tyEmpty k1') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) HcL0 HcRL HcR0 Ec
            (GS_elimEmpty EP EM Hσ HΔL HΔ HM HM'R HMM EM1 Ht Ht'R Htt Et)
            (GS_elimEmpty EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HM'R1 Hl1c)) (ty_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_elimEmpty_inst; inst_side 33.
  - apply redt_elimEmpty_inst; inst_side 33.
Qed.

Lemma rec_T_sum {ΔL ΔR kL kR k k' k1 k1' A B A' B'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR ->
  lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] B @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] A' @ k ] -> [ G' ; ΔL ⊢[ lC ] B' @ k' ] -> ty_leq A A' -> ty_leq B B' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT B)) (motT (wrapMT MTR) k1' ΔR (boxT B'))
    (recTL k' ΔL B) (recTR k1' ΔR B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tySum k k' A B)))
    (motT (wrapMT MTR) kR ΔR (boxT (tySum k1 k1' A' B')))
    (recTL kL ΔL (tySum k k' A B)) (recTR kR ΔR (tySum k1 k1' A' B')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HA HB HA' HB' EA EB IHA IHB.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  (* the summands and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (Tcall HΔL HΔ Hw' Q' HB HB' EB IHB) as (HBB & HB'R & HB'R1 & _ & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tySum k k' A B @ lmax k k' ])
    by (apply wft_sum; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tySum k1 k1' A' B' @ lmax k1 k1' ])
    by (apply wft_sum; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tySum k1 k1' A' B' @ lmax k k' ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Qm]).
  assert (Ec : ty_leq (tySum k k' A B) (tySum k1 k1' A' B')) by (cbn; repeat split; assumption).
  refine (rec_T_br 34 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: nil)
            (recTL k ΔL A :: recTL k' ΔL B :: nil) (recTR k1 ΔR A' :: recTR k1' ΔR B' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm HcL0 HcRL HcR0 Ec
            (GS_sum EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB)
            (GS_sum EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _) HB'R1 HB'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HB'R1 Hl1c)) (ty_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_sum_inst; inst_side 34.
  - apply redT_sum_inst; inst_side 34.
Qed.

Lemma rec_t_codesum {ΔL ΔR kL kR TL TR k k' k1 k1' s0 t0 s1 t1} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lmax k k')) kL -> lequiv L' (lsuc (lmax k k')) kR ->
  lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TL @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TR @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lC ] s0 : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s1 : tyU k @ lsuc k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ⊢[ lC ] t0 : tyU k' @ lsuc k' ] -> [ G' ; ΔL ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> tm_leq t0 t1 ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s1))
    (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k') ΔL (tyU k') (boxt t0))
    (mott (wrapMt MtR) (lsuc k1') ΔR (tyU k1') (boxt t1))
    (rectL (lsuc k') ΔL (tyU k') t0) (rectR (lsuc k1') ΔR (tyU k1') t1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSum k k' s0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSum k1 k1' s1 t1)))
    (rectL kL ΔL TL (tmSum k k' s0 t0)) (rectR kR ΔR TR (tmSum k1 k1' s1 t1)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR Hs Hs' Es Ht Ht' Et IHs IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  (* the summands' codes and their calls *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) (HUU _ _ _ HΔL Q) Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1).
  destruct (tcall (k := lsuc k') HΔL HΔ Hw' (lequiv_suc _ _ _ Q') (HUU _ _ _ HΔL Q') Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X2).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R.
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Ht') as Ht'R.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmSum k k' s0 t0 : tyU (lmax k k') @ lsuc (lmax k k') ])
    by (apply wf_code_sum; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact Hs | exact Ht]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSum k1 k1' s1 t1 : tyU (lmax k1 k1') @ lsuc (lmax k1 k1') ])
    by (apply wf_code_sum; [discriminate | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact Hs'R1 | exact Ht'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSum k1 k1' s1 t1 : tyU (lmax k k') @ lsuc (lmax k k') ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Qm] | exact (HUU _ _ _ HΔL Qm)]).
  refine (rec_t_br 35 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil)
            (GCtx ΔR :: GTm s1 :: GTm t1 :: nil)
            (rectL (lsuc k) ΔL (tyU k) s0 :: rectL (lsuc k') ΔL (tyU k') t0 :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s1 :: rectR (lsuc k1') ΔR (tyU k1') t1 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Qm) HTL HTR (HUU _ _ _ HΔR Qm) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_codesum EP EM Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et)
            (GS_codesum EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hs'R1 Hs'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _) Ht'R1 Ht'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codesum_inst; inst_side 35.
  - apply redt_codesum_inst; inst_side 35.
Qed.

(** The injections: both summands' calls and the payload's. *)
Ltac rec_t_inj kb inj wf_inj inst U ΔL ΔR k k' k1 k1' A B A' B' a a' :=
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Ha Ha' Ea IHA IHB IHa;
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR;
  assert (Hn : lC <> lV) by discriminate; assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia);
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E);
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E');
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q); assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q');
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption);
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm);
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1));
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2));
  (* the summands and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1);
  destruct (Tcall HΔL HΔ Hw' Q' HB HB' EB IHB) as (HBB & HB'R & HB'R1 & _ & _ & X2);
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D; pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D;
  assert (HSS : [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ tySum k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sum; [discriminate | exact Qg | exact Qg' | exact HAA | exact HBB]);
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r;
  (* the payload and its call *)
  let TC := lazymatch U with
             | 1 => constr:(tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa)
             | _ => constr:(tcall HΔL HΔ Hw' Q' HBB Ha Ha' Ea IHa)
             end in
  destruct TC as (Haa & Ha'R & Ha'R1 & _ & X3);
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X3r;
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] inj k k' A B a : tySum k k' A B @ lmax k k' ])
    by (apply wf_inj; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Ha]);
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] inj k1 k1' A' B' a' : tySum k1 k1' A' B' @ lmax k1 k1' ])
    by (apply wf_inj; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1
                      | exact Ha'R1]);
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] inj k1 k1' A' B' a' : tySum k k' A B @ lmax k k' ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qmg]
                        | exact HSS]);
  assert (Ec : tm_leq (inj k k' A B a) (inj k1 k1' A' B' a')) by (cbn; repeat split; assumption);
  let xL := lazymatch U with 1 => constr:(rectL k ΔL A a) | _ => constr:(rectL k' ΔL B a) end in
  let xR := lazymatch U with 1 => constr:(rectR k1 ΔR A' a') | _ => constr:(rectR k1' ΔR B' a') end in
  let Hkb := lazymatch U with
             | 1 => uconstr:(or_introl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))
             | _ => uconstr:(or_intror (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))
             end in
  refine (rec_t_br kb (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm a :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm a' :: nil)
            (recTL k ΔL A :: recTL k' ΔL B :: xL :: nil) (recTR k1 ΔR A' :: recTR k1' ΔR B' :: xR :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HSS) HcL0 HcRL HcR0 Ec
            (GS_inj EP EM kb U Hkb Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB
               Ha Ha'R Haa Ea)
            (GS_inj EP EM kb U Hkb (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HA'R1 HA'R1 (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _)
               HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _);
  [ sr_ctx; [exact X1 | exact X2 | exact X3] | sr_ctx; [exact X1r | exact X2r | exact X3r] | res_eq | res_eq | res_eq
  | apply inst; inst_side kb | apply inst; inst_side kb ].

Lemma rec_t_inl {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT B)) (motT (wrapMT MTR) k1' ΔR (boxT B'))
    (recTL k' ΔL B) (recTR k1' ΔR B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmInl k k' A B a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmInl k1 k1' A' B' a')))
    (rectL kL ΔL TL (tmInl k k' A B a)) (rectR kR ΔR TR (tmInl k1 k1' A' B' a')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  rec_t_inj 36 tmInl wf_inl redt_inl_inst (1) ΔL ΔR k k' k1 k1' A B A' B' a a'.
Qed.

Lemma rec_t_inr {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] a : B @ k' ] -> [ G' ; ΔL ⊢[ lC ] a' : B @ k' ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT B)) (motT (wrapMT MTR) k1' ΔR (boxT B'))
    (recTL k' ΔL B) (recTR k1' ΔR B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' ΔL B (boxt a)) (mott (wrapMt MtR) k1' ΔR B' (boxt a'))
    (rectL k' ΔL B a) (rectR k1' ΔR B' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmInr k k' A B a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmInr k1 k1' A' B' a')))
    (rectL kL ΔL TL (tmInr k k' A B a)) (rectR kR ΔR TR (tmInr k1 k1' A' B' a')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  rec_t_inj 37 tmInr wf_inr redt_inr_inst (0) ΔL ΔR k k' k1 k1' A B A' B' a a'.
Qed.

(** [case]: the summands', the motive's (over the sum), the branches' (over
    their summands, at the motive's instances) and the scrutinee's calls.
    The branch scopes declare the branch types in their substituted form
    ([liftshift_cons_ty']); the calls carry the typing rule's. *)
Lemma rec_t_case {ΔL ΔR kL kR TL TR k k' k'' k1 k1' k1'' A A' B B' M M' c1 c1' c2 c2' t t'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k'' kL -> lequiv L' k'' kR -> lwf L' k -> lwf L' k' -> lwf L' k'' -> lwf L' k1 -> lwf L' k1' -> lwf L' k1'' ->
  leqv k k1 -> leqv k' k1' -> leqv k'' k1'' ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TL @ k'' ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TR @ k'' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ,, tySum k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G' ; ΔL ,, tySum k k' A B @ lmax k k' ⊢[ lC ] M' @ k'' ] -> ty_leq M M' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] c1 : M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] c1' : M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] -> tm_leq c1 c1' ->
  [ G' ; ΔL ,, B @ k' ⊢[ lC ] c2 : M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; ΔL ,, B @ k' ⊢[ lC ] c2' : M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] -> tm_leq c2 c2' ->
  [ G' ; ΔL ⊢[ lC ] t : tySum k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] t' : tySum k k' A B @ lmax k k' ] ->
  tm_leq t t' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT B)) (motT (wrapMT MTR) k1' ΔR (boxT B'))
    (recTL k' ΔL B) (recTR k1' ΔR B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k'' (ΔL ,, tySum k k' A B @ lmax k k') (boxT M))
    (motT (wrapMT MTR) k1'' (ΔR ,, tySum k1 k1' A' B' @ lmax k1 k1') (boxT M'))
    (recTL k'' (ΔL ,, tySum k k' A B @ lmax k k') M) (recTR k1'' (ΔR ,, tySum k1 k1' A' B' @ lmax k1 k1') M') ->
  LRtmM (lvsubst l2 φ) G' Θ
    (mott (wrapMt MtL) k'' (ΔL ,, A @ k) (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) (boxt c1))
    (mott (wrapMt MtR) k1'' (ΔR ,, A' @ k1) (M'⟨rlift ↑⟩[lsingle (tmInl k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) (boxt c1'))
    (rectL k'' (ΔL ,, A @ k) (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) c1)
    (rectR k1'' (ΔR ,, A' @ k1) (M'⟨rlift ↑⟩[lsingle (tmInl k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) c1') ->
  LRtmM (lvsubst l2 φ) G' Θ
    (mott (wrapMt MtL) k'' (ΔL ,, B @ k') (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) (boxt c2))
    (mott (wrapMt MtR) k1'' (ΔR ,, B' @ k1') (M'⟨rlift ↑⟩[lsingle (tmInr k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) (boxt c2'))
    (rectL k'' (ΔL ,, B @ k') (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) c2)
    (rectR k1'' (ΔR ,, B' @ k1') (M'⟨rlift ↑⟩[lsingle (tmInr k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) c2') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tySum k k' A B) (boxt t))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tySum k1 k1' A' B') (boxt t'))
    (rectL (lmax k k') ΔL (tySum k k' A B) t) (rectR (lmax k1 k1') ΔR (tySum k1 k1' A' B') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmCase k k' k'' A B M c1 c2 t)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmCase k1 k1' k1'' A' B' M' c1' c2' t')))
    (rectL kL ΔL TL (tmCase k k' k'' A B M c1 c2 t)) (rectR kR ΔR TR (tmCase k1 k1' k1'' A' B' M' c1' c2' t')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw'' Hw1 Hw1' Hw1'' E E' E'' HTL HTR HA HA' EA HB HB' EB HM HM' EM1
    Hc1 Hc1' Ec1 Hc2 Hc2' Ec2 Ht Ht' Et IHA IHB IHM IHc1 IHc2 IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Q'' : lequiv L' k'' k1'') by exact (leqv_lequiv _ _ _ Hw'' Hw1'' E'').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qg'' : lequiv (gL G') k'' k1'') by (rewrite EL; exact Q'').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the summands and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall HΔL HΔ Hw' Q' HB HB' EB IHB) as (HBB & HB'R & HB'R1 & CB & CB1 & X2).
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (lift_ty (j := lD) HA' Hl1c) as HA'D.
  pose proof (lift_ty (j := lD) HB Hl1c) as HBD. pose proof (lift_ty (j := lD) HB' Hl1c) as HB'D.
  (* the sum, and the motive over it *)
  assert (HSD : [ G' ; ΔL ⊢[ lD ] tySum k k' A B @ lmax k k' ])
    by (apply wft_sum; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBD]).
  assert (HSS : [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ tySum k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sum; [discriminate | exact Qg | exact Qg' | exact HAA | exact HBB]).
  assert (HSS0 : [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ tySum k k' A' B' @ lmax k k' ])
    by (apply eqty_sum; [discriminate | exact Qk | exact Qk' | exact HAA | exact HBB]).
  assert (CS : [ G' ⊢[ lD ] ΔL ,, tySum k k' A B @ lmax k k' ≅ ΔR ,, tySum k k' A' B' @ lmax k k' ])
    by (apply eqc_ext; [exact HΔ | exact HSD | exact HSS0 | rewrite EL; exact (lequiv_refl _ _ Hwm)]).
  assert (CS1 : [ G' ⊢[ lD ] ΔL ,, tySum k k' A B @ lmax k k' ≅ ΔR ,, tySum k1 k1' A' B' @ lmax k1 k1' ])
    by (apply eqc_ext; [exact HΔ | exact HSD | exact HSS | exact Qmg]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CS) as HΔS.
  destruct (Tcall HΔS CS1 Hw'' Q'' HM HM' EM1 IHM) as (HMM & _ & HM'R1 & _ & _ & X3).
  pose proof (ctxconv_ty CS (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty (j := lD) HM Hl1c) as HMD. pose proof (lift_ty (j := lD) HM' Hl1c) as HM'D.
  (* the branches' types *)
  destruct (case_facts_D Qg Qg' HAD HAA HA'D HBD HBB HB'D HMD HMM HM'D) as (_ & CAf & CBf & EC1 & EC2).
  destruct (case_facts_D Qk Qk' HAD HAA HA'D HBD HBB HB'D HMD HMM HM'D) as (_ & CAf0 & CBf0 & EC10 & EC20).
  pose proof (ctxconv_eqty (eqctx_sym_D CAf) (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ EC1)) as HC1.
  pose proof (ctxconv_eqty (eqctx_sym_D CBf) (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ EC2)) as HC2.
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA. pose proof (eqctx_wf_l (i := lD) eq_refl CB) as HΔB.
  destruct (tcall HΔA CA1 Hw'' Q'' HC1 Hc1 Hc1' Ec1 IHc1) as (Hcc1 & _ & Hc1'R1 & _ & X4).
  destruct (tcall HΔB CB1 Hw'' Q'' HC2 Hc2 Hc2' Ec2 IHc2) as (Hcc2 & _ & Hc2'R1 & _ & X5).
  (* the scrutinee and its call *)
  destruct (tcall HΔL HΔ Hwm Qm HSS Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X6).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHc1) IHc1) Hl2g') as X4r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHc2) IHc2) Hl2g') as X5r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X6r.
  (* the right pieces at the left levels *)
  assert (Hc1'R : [ G' ; ΔR ,, A' @ k ⊢[ lC ] c1' : M'⟨rlift ↑⟩[lsingle (tmInl k k' A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ k'' ]).
  { eapply wf_conv; [exact (ctxconv_tm CA (i := lC) eq_refl Hc1') |].
    exact (ctxconv_eqty CA (i := lD) eq_refl (ctxconv_eqty (eqctx_sym_D CAf0) (i := lD) eq_refl EC10)). }
  assert (Hc2'R : [ G' ; ΔR ,, B' @ k' ⊢[ lC ] c2' : M'⟨rlift ↑⟩[lsingle (tmInr k k' A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ k'' ]).
  { eapply wf_conv; [exact (ctxconv_tm CB (i := lC) eq_refl Hc2') |].
    exact (ctxconv_eqty CB (i := lD) eq_refl (ctxconv_eqty (eqctx_sym_D CBf0) (i := lD) eq_refl EC20)). }
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tySum k k' A' B' @ lmax k k' ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Ht') |].
    exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HSS0)). }
  (* the result types *)
  assert (Hr1 : [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k'' ])
    by exact (eqty_subst_single_D HMM HM'D Htt (lift_tm (j := lD) Ht Hl1c) (lift_tm (j := lD) Ht' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmCase k k' k'' A B M c1 c2 t : M[lsingle t] @ k'' ])
    by (apply wf_case; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | rewrite EL; exact Hw''
                       | exact HA | exact HB | exact HM | exact Hc1 | exact Hc2 | exact Ht]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmCase k1 k1' k1'' A' B' M' c1' c2' t' : M'[lsingle t'] @ k1'' ])
    by (apply wf_case; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | rewrite EL; exact Hw1''
                       | exact HA'R1 | exact HB'R1 | exact HM'R1 | exact Hc1'R1 | exact Hc2'R1 | exact Ht'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmCase k1 k1' k1'' A' B' M' c1' c2' t' : M[lsingle t] @ k'' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg'']
                    | exact Hr1]. }
  assert (Ecc : tm_leq (tmCase k k' k'' A B M c1 c2 t) (tmCase k1 k1' k1'' A' B' M' c1' c2' t'))
    by (cbn; repeat split; assumption).
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  pose proof (lift_ty (j := lD) HM'R1 Hl1c) as HM'R1D.
  refine (rec_t_br 38 (k :: k' :: k'' :: nil) (k1 :: k1' :: k1'' :: nil)
            (GCtx ΔL :: GTy A :: GTy B :: GTy M :: GTm c1 :: GTm c2 :: GTm t :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTy M' :: GTm c1' :: GTm c2' :: GTm t' :: nil)
            (recTL k ΔL A :: recTL k' ΔL B :: recTL k'' (ΔL ,, tySum k k' A B @ lmax k k') M
             :: rectL k'' (ΔL ,, A @ k) (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) c1
             :: rectL k'' (ΔL ,, B @ k') (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) c2
             :: rectL (lmax k k') ΔL (tySum k k' A B) t :: nil)
            (recTR k1 ΔR A' :: recTR k1' ΔR B' :: recTR k1'' (ΔR ,, tySum k1 k1' A' B' @ lmax k1 k1') M'
             :: rectR k1'' (ΔR ,, A' @ k1) (M'⟨rlift ↑⟩[lsingle (tmInl k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) c1'
             :: rectR k1'' (ΔR ,, B' @ k1') (M'⟨rlift ↑⟩[lsingle (tmInr k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) c2'
             :: rectR (lmax k1 k1') ΔR (tySum k1 k1' A' B') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_cons _ _ E'' (Forall2_nil _)))))
            HΔL HΔ HkL HkR Q'' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) HcL0 HcRL HcR0 Ecc
            (GS_case EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB HM HM'R HMM EM1
               Hc1 Hc1'R Hcc1 Ec1 Hc2 Hc2'R Hcc2 Ec2 Ht Ht'R Htt Et)
            (GS_case EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HA'R1 HA'R1 (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _)
               HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ HM'R1D) (ty_leq_refl _)
               Hc1'R1 Hc1'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hc1'R1 Hl1c)) (tm_leq_refl _)
               Hc2'R1 Hc2'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hc2'R1 Hl1c)) (tm_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; J_cbn; rewrite ?liftshift_cons_ty'; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6].
  - sr_ctx; J_cbn; rewrite ?liftshift_cons_ty'; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_case_inst; inst_side 38.
  - apply redt_case_inst; inst_side 38.
Qed.

(** [elimW] (branch 42), as [case]: the step's telescope over the shape,
    read off [W_facts] at both sides' levels. *)
Lemma rec_t_elimW {ΔL ΔR kL kR TL TR k k' k'' k1 k1' k1'' A A' B B' M M' c c' t t'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k'' kL -> lequiv L' k'' kR -> lwf L' k -> lwf L' k' -> lwf L' k'' -> lwf L' k1 -> lwf L' k1' -> lwf L' k1'' ->
  leqv k k1 -> leqv k' k1' -> leqv k'' k1'' ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TL @ k'' ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TR @ k'' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ,, tyW k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G' ; ΔL ,, tyW k k' A B @ lmax k k' ⊢[ lC ] M' @ k'' ] -> ty_leq M M' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] wfty k k' A B @ lmax k' (lmax k k') ] ->
  [ G' ; ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ⊢[ lC ] wihty k k' k'' A B M @ lmax k' k'' ] ->
  [ G' ; ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
      ⊢[ lC ] c : wstepty k k' A B M @ k'' ] ->
  [ G' ; ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
      ⊢[ lC ] c' : wstepty k k' A B M @ k'' ] -> tm_leq c c' ->
  [ G' ; ΔL ⊢[ lC ] t : tyW k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] t' : tyW k k' A B @ lmax k k' ] ->
  tm_leq t t' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k'' (ΔL ,, tyW k k' A B @ lmax k k') (boxT M))
    (motT (wrapMT MTR) k1'' (ΔR ,, tyW k1 k1' A' B' @ lmax k1 k1') (boxT M'))
    (recTL k'' (ΔL ,, tyW k k' A B @ lmax k k') M) (recTR k1'' (ΔR ,, tyW k1 k1' A' B' @ lmax k1 k1') M') ->
  LRtmM (lvsubst l2 φ) G' Θ
    (mott (wrapMt MtL) k'' (ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
       (wstepty k k' A B M) (boxt c))
    (mott (wrapMt MtR) k1'' (ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1')
                              ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'')
       (wstepty k1 k1' A' B' M') (boxt c'))
    (rectL k'' (ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
       (wstepty k k' A B M) c)
    (rectR k1'' (ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1')
                 ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'')
       (wstepty k1 k1' A' B' M') c') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tyW k k' A B) (boxt t))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tyW k1 k1' A' B') (boxt t'))
    (rectL (lmax k k') ΔL (tyW k k' A B) t) (rectR (lmax k1 k1') ΔR (tyW k1 k1' A' B') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmElimW k k' k'' A B M c t)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmElimW k1 k1' k1'' A' B' M' c' t')))
    (rectL kL ΔL TL (tmElimW k k' k'' A B M c t)) (rectR kR ΔR TR (tmElimW k1 k1' k1'' A' B' M' c' t')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw'' Hw1 Hw1' Hw1'' E E' E'' HTL HTR HA HA' EA HB HB' EB HM HM' EM1 HF HI
    Hc Hc' Ec Ht Ht' Et IHA IHB IHM IHc IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Q'' : lequiv L' k'' k1'') by exact (leqv_lequiv _ _ _ Hw'' Hw1'' E'').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qg'' : lequiv (gL G') k'' k1'') by (rewrite EL; exact Q'').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  assert (Qk'' : lequiv (gL G') k'' k'') by (rewrite EL; exact (lequiv_refl _ _ Hw'')).
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the shape, the positions and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2).
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R.
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (lift_ty (j := lD) HA' Hl1c) as HA'D.
  pose proof (lift_ty (j := lD) HB Hl1c) as HBD. pose proof (lift_ty (j := lD) HB' Hl1c) as HB'D.
  (* the tree type, and the motive over it *)
  assert (HWD : [ G' ; ΔL ⊢[ lD ] tyW k k' A B @ lmax k k' ])
    by (apply wft_W; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBD]).
  assert (HWW : [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ tyW k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_W; [discriminate | exact Qg | exact Qg' | exact HAD | exact HAA | exact HBB]).
  assert (HWW0 : [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ tyW k k' A' B' @ lmax k k' ])
    by (apply eqty_W; [discriminate | exact Qk | exact Qk' | exact HAD | exact HAA | exact HBB]).
  assert (CW : [ G' ⊢[ lD ] ΔL ,, tyW k k' A B @ lmax k k' ≅ ΔR ,, tyW k k' A' B' @ lmax k k' ])
    by (apply eqc_ext; [exact HΔ | exact HWD | exact HWW0 | rewrite EL; exact (lequiv_refl _ _ Hwm)]).
  assert (CW1 : [ G' ⊢[ lD ] ΔL ,, tyW k k' A B @ lmax k k' ≅ ΔR ,, tyW k1 k1' A' B' @ lmax k1 k1' ])
    by (apply eqc_ext; [exact HΔ | exact HWD | exact HWW | exact Qmg]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CW) as HΔW.
  destruct (Tcall HΔW CW1 Hw'' Q'' HM HM' EM1 IHM) as (HMM & _ & HM'R1 & _ & _ & X3).
  pose proof (ctxconv_ty CW (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty (j := lD) HM Hl1c) as HMD. pose proof (lift_ty (j := lD) HM' Hl1c) as HM'D.
  pose proof (lift_ty (j := lD) HF Hl1c) as HFD. pose proof (lift_ty (j := lD) HI Hl1c) as HID.
  (* the step's telescope, at the right levels and at the left ones *)
  destruct (@W_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ _ _ Qg Qg' Qg''
              HAA HAD HA'D HBB HBD HB'D HMM HMD HM'D HFD HID) as (_ & _ & CS1L & ES1).
  destruct (@W_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ _ _ Qk Qk' Qk''
              HAA HAD HA'D HBB HBD HB'D HMM HMD HM'D HFD HID) as (_ & _ & CS0L & ES0).
  destruct (eqc_ext_inv CS1L) as (CS1a & _ & EI1 & QI1). destruct (eqc_ext_inv CS1a) as (_ & _ & EF1 & QF1).
  destruct (eqc_ext_inv CS0L) as (CS0a & _ & EI0 & QI0). destruct (eqc_ext_inv CS0a) as (_ & _ & EF0 & QF0).
  pose proof (eqctx_wf_l (i := lD) eq_refl CS1a) as HΔAF.
  assert (CS1 : [ G' ⊢[ lD ] ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
                  ≅ ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1') ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'' ])
    by (apply eqc_ext; [apply eqc_ext; [exact CA1 | exact HFD | exact EF1 | exact QF1] | exact HID | exact EI1 | exact QI1]).
  assert (CS0 : [ G' ⊢[ lD ] ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
                  ≅ ΔR ,, A' @ k ,, wfty k k' A' B' @ lmax k' (lmax k k') ,, wihty k k' k'' A' B' M' @ lmax k' k'' ])
    by (apply eqc_ext; [apply eqc_ext; [exact CA | exact HFD | exact EF0 | exact QF0] | exact HID | exact EI0 | exact QI0]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CS1) as HΔS.
  (* the step and the scrutinee, and their calls *)
  destruct (tcall HΔS CS1 Hw'' Q'' ES1 Hc Hc' Ec IHc) as (Hcc & _ & Hc'R1 & _ & X4).
  destruct (tcall HΔL HΔ Hwm Qm HWW Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X5).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHc) IHc) Hl2g') as X4r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X5r.
  (* the right pieces at the left levels *)
  assert (Hc'R : [ G' ; ΔR ,, A' @ k ,, wfty k k' A' B' @ lmax k' (lmax k k') ,, wihty k k' k'' A' B' M' @ lmax k' k''
                   ⊢[ lC ] c' : wstepty k k' A' B' M' @ k'' ]).
  { eapply wf_conv; [exact (ctxconv_tm CS0 (i := lC) eq_refl Hc') |].
    exact (ctxconv_eqty CS0 (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ ES0)). }
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyW k k' A' B' @ lmax k k' ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Ht') |].
    exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HWW0)). }
  (* the result types *)
  assert (Hr1 : [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k'' ])
    by exact (eqty_subst_single_D HMM HM'D Htt (lift_tm (j := lD) Ht Hl1c) (lift_tm (j := lD) Ht' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmElimW k k' k'' A B M c t : M[lsingle t] @ k'' ])
    by (apply wf_elimW; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | rewrite EL; exact Hw''
                        | exact HA | exact HB | exact HM | exact HF | exact HI | exact Hc | exact Ht]).
  pose proof (@sc_elimW_q G' lC Hl1c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Qg Qg' Qg''
                HA HA' (static_code_ty Hl1c HA HA' EA) HB HB' (static_code_ty Hl1c HB HB' EB)
                HM HM' (static_code_ty Hl1c HM HM' EM1) HF HI Hc' Ht Ht' (static_code_tm Hl1c Ht Ht' Et)) as HcRL.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmElimW k1 k1' k1'' A' B' M' c' t' : M'[lsingle t'] @ k1'' ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact HcRL | apply eqty_sym, Hr1] | apply lequiv_sym, Qg'']. }
  assert (Ecc : tm_leq (tmElimW k k' k'' A B M c t) (tmElimW k1 k1' k1'' A' B' M' c' t'))
    by (cbn; repeat split; assumption).
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  pose proof (lift_ty (j := lD) HM'R1 Hl1c) as HM'R1D.
  refine (rec_t_br 42 (k :: k' :: k'' :: nil) (k1 :: k1' :: k1'' :: nil)
            (GCtx ΔL :: GTy A :: GTy B :: GTy M :: GTm c :: GTm t :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTy M' :: GTm c' :: GTm t' :: nil)
            (recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: recTL k'' (ΔL ,, tyW k k' A B @ lmax k k') M
             :: rectL k'' (ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
                  (wstepty k k' A B M) c
             :: rectL (lmax k k') ΔL (tyW k k' A B) t :: nil)
            (recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: recTR k1'' (ΔR ,, tyW k1 k1' A' B' @ lmax k1 k1') M'
             :: rectR k1'' (ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1')
                            ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'') (wstepty k1 k1' A' B' M') c'
             :: rectR (lmax k1 k1') ΔR (tyW k1 k1' A' B') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_cons _ _ E'' (Forall2_nil _)))))
            HΔL HΔ HkL HkR Q'' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) HcL0 HcRL HcR0 Ecc
            (GS_elimW EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB HM HM'R HMM EM1 Hc Hc'R Hcc Ec Ht Ht'R Htt Et)
            (GS_elimW EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HA'R1 HA'R1 (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _)
               HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ HM'R1D) (ty_leq_refl _)
               Hc'R1 Hc'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hc'R1 Hl1c)) (tm_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx_W; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5].
  - sr_ctx_W; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_elimW_inst; inst_side 42.
  - apply redt_elimW_inst; inst_side 42.
Qed.

(** Length-indexed tuples and finite indices (M14b): the length's call is a
    term call at [Nat], as [succ]'s. *)
Lemma rec_T_vec {ΔL ΔR kL kR k k1 A A' n n'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] n' : tyNat @ lzero ] -> tm_leq n n' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt n)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt n'))
    (rectL lzero ΔL tyNat n) (rectR lzero ΔR tyNat n') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyVec k A n)))
    (motT (wrapMT MTR) kR ΔR (boxT (tyVec k1 A' n')))
    (recTL kL ΔL (tyVec k A n)) (recTR kR ΔR (tyVec k1 A' n')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HA HA' EA Hn Hn' En IHA IHn.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hv : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  (* the element type, the length, and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Hn Hn' En IHn)
    as (Hnn & Hn'R & _ & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHn) IHn) Hl2g') as X2r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tyVec k A n @ k ])
    by (apply wft_vec; [exact Hv | rewrite EL; exact Hw | exact HA | exact Hn]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyVec k1 A' n' @ k1 ])
    by (apply wft_vec; [exact Hv | rewrite EL; exact Hw1 | exact HA'R1 | exact Hn'R]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyVec k1 A' n' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Q]).
  assert (Ec : ty_leq (tyVec k A n) (tyVec k1 A' n')) by (cbn; repeat split; assumption).
  refine (rec_T_br 43 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm n :: nil)
            (GCtx ΔR :: GTy A' :: GTm n' :: nil)
            (recTL k ΔL A :: rectL lzero ΔL tyNat n :: nil) (recTR k1 ΔR A' :: rectR lzero ΔR tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HcL0 HcRL HcR0 Ec
            (GS_vec EP EM Hσ HΔL HΔ HA HA'R HAA EA Hn Hn'R Hnn En)
            (GS_vec EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _) Hn'R Hn'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hn'R Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_vec_inst; inst_side 43.
  - apply redT_vec_inst; inst_side 43.
Qed.

Lemma rec_t_codevec {ΔL ΔR kL kR TL TR k k1 s0 s1 n n'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc k) kL -> lequiv L' (lsuc k) kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tyU k ≅ TL @ lsuc k ] -> [ G' ; ΔL ⊢[ lD ] tyU k ≅ TR @ lsuc k ] ->
  [ G' ; ΔL ⊢[ lC ] s0 : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s1 : tyU k @ lsuc k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] n' : tyNat @ lzero ] -> tm_leq n n' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s1))
    (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt n)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt n'))
    (rectL lzero ΔL tyNat n) (rectR lzero ΔR tyNat n') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmVec k s0 n)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmVec k1 s1 n')))
    (rectL kL ΔL TL (tmVec k s0 n)) (rectR kR ΔR TR (tmVec k1 s1 n')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR Hs Hs' Es Hn Hn' En IHs IHn.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  (* the element code, the length, and their calls *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) (HUU _ _ _ HΔL Q) Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1).
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Hn Hn' En IHn)
    as (Hnn & Hn'R & _ & _ & X2).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHn) IHn) Hl2g') as X2r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmVec k s0 n : tyU k @ lsuc k ])
    by (apply wf_code_vec; [discriminate | rewrite EL; exact Hw | exact Hs | exact Hn]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmVec k1 s1 n' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_vec; [discriminate | rewrite EL; exact Hw1 | exact Hs'R1 | exact Hn'R]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmVec k1 s1 n' : tyU k @ lsuc k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Q] | exact (HUU _ _ _ HΔL Q)]).
  refine (rec_t_br 44 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTm s0 :: GTm n :: nil)
            (GCtx ΔR :: GTm s1 :: GTm n' :: nil)
            (rectL (lsuc k) ΔL (tyU k) s0 :: rectL lzero ΔL tyNat n :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s1 :: rectR lzero ΔR tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (HUU _ _ _ HΔR Q) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_codevec EP EM Hσ HΔL HΔ Hs Hs'R Hss Es Hn Hn'R Hnn En)
            (GS_codevec EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hs'R1 Hs'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _) Hn'R Hn'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hn'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codevec_inst; inst_side 44.
  - apply redt_codevec_inst; inst_side 44.
Qed.

Lemma rec_T_fin {ΔL ΔR kL kR n n'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' lzero kL -> lequiv L' lzero kR ->
  [ G' ; ΔL ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] n' : tyNat @ lzero ] -> tm_leq n n' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt n)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt n'))
    (rectL lzero ΔL tyNat n) (rectR lzero ΔR tyNat n') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyFin n))) (motT (wrapMT MTR) kR ΔR (boxT (tyFin n')))
    (recTL kL ΔL (tyFin n)) (recTR kR ΔR (tyFin n')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hn Hn' En IHn.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Hn Hn' En IHn)
    as (Hnn & Hn'R & _ & _ & X1).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHn) IHn) Hl2g') as X1r.
  assert (HcF : forall Δ u, [ G' ; Δ ⊢[ lC ] u : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lC ] tyFin u @ lzero ])
    by (intros; apply wft_fin; [discriminate | assumption]).
  refine (rec_T_br 45 nil nil (GCtx ΔL :: GTm n :: nil) (GCtx ΔR :: GTm n' :: nil)
            (rectL lzero ΔL tyNat n :: nil) (rectR lzero ΔR tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' lzero I) (HcF _ _ Hn) (HcF _ _ Hn') (HcF _ _ Hn'R) En
            (GS_fin EP EM 45 eq_refl eq_refl Hσ HΔL HΔ Hn Hn'R Hnn En)
            (GS_fin EP EM 45 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hn'R Hn'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hn'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx. exact X1.
  - sr_ctx. exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_fin_inst; inst_side 45.
  - apply redT_fin_inst; inst_side 45.
Qed.

Lemma rec_t_codefin {ΔL ΔR kL kR TL TR n n'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc lzero) kL -> lequiv L' (lsuc lzero) kR ->
  [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TL @ lsuc lzero ] -> [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TR @ lsuc lzero ] ->
  [ G' ; ΔL ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] n' : tyNat @ lzero ] -> tm_leq n n' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt n)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt n'))
    (rectL lzero ΔL tyNat n) (rectR lzero ΔR tyNat n') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmFin n))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmFin n')))
    (rectL kL ΔL TL (tmFin n)) (rectR kR ΔR TR (tmFin n')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR Hn Hn' En IHn.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Hn Hn' En IHn)
    as (Hnn & Hn'R & _ & _ & X1).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHn) IHn) Hl2g') as X1r.
  assert (HcF : forall Δ u, [ G' ; Δ ⊢[ lC ] u : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lC ] tmFin u : tyU lzero @ lsuc lzero ])
    by (intros; apply wf_code_fin; [discriminate | assumption]).
  assert (HU0 : [ G' ; ΔR ⊢[ lD ] tyU lzero @ lsuc lzero ]) by (apply wft_U; [discriminate | assumption | exact I]).
  refine (rec_t_br 46 nil nil (GCtx ΔL :: GTm n :: nil) (GCtx ΔR :: GTm n' :: nil)
            (rectL lzero ΔL tyNat n :: nil) (rectR lzero ΔR tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' (lsuc lzero) I) HTL HTR (eqty_refl _ _ _ _ _ HU0)
            (HcF _ _ Hn) (HcF _ _ Hn') (HcF _ _ Hn'R) En
            (GS_fin EP EM 46 eq_refl eq_refl Hσ HΔL HΔ Hn Hn'R Hnn En)
            (GS_fin EP EM 46 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hn'R Hn'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hn'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx. exact X1.
  - sr_ctx. exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codefin_inst; inst_side 46.
  - apply redt_codefin_inst; inst_side 46.
Qed.

Lemma rec_t_var {ΔL ΔR kL kR TL TR k T0 n} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] -> lequiv L' k kL -> lequiv L' k kR ->
  [ G' ; ΔL ⊢[ lD ] T0 ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] T0 ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lV ] var n : T0 @ k ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (var n)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (var n)))
    (rectL kL ΔL TL (var n)) (rectR kR ΔR TR (var n)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR Hv.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL).
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
  (* the branch: its index is the recursor's own *)
  refine (rec_t_br 4 (kL :: nil) (kR :: nil) (GCtx ΔL :: GTy TL :: GTm (var n) :: nil)
            (GCtx ΔR :: GTy TR :: GTm (var n) :: nil) nil nil ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; exact (lequiv_wf_r _ _ _ HkR))
            (uext_leqv (Forall2_cons _ _ (lequiv_leqv _ _ _ QLR) (Forall2_nil _)))
            HΔL HΔ (lequiv_refl _ _ HwL) QLR QLR (eqty_refl _ _ _ _ _ HTLk) HTLR
            (ctxconv_eqty HΔ (i := lD) eq_refl HTLR) HcL HcL HcR (tm_leq_refl _)
            (GS_var EP EM Hσ HΔL HΔ HTLk HTRkL HTLR HvL HvRL)
            (GS_var EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HTRk HTRk (eqty_refl _ _ _ _ _ HTRk) HvR HvR)
            _ _ _ _ _ _ _).
  - sr_ctx.
  - sr_ctx.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_var_inst; inst_side 4.
  - apply redt_var_inst; inst_side 4.
Qed.

(** ** λ: the index is first reduced to its Π whnf *)
Lemma LRty_eqM {l T T'} : LRtyM l G' Θ T T' -> [ G' ; Θ ⊢[ lM ] T ≅ T' @ l ].
Proof using ELM EMl.
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
Proof using EL ELM ELP EMl Hl2 HrbL HrbR.
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
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA Hb Hb' Eb IHA IHb.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
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
  (* the domain and its call *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔLA.
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
pose proof (wf_ty_dnf HA'R) as NA'.
pose proof (wf_tm_dnf Hb'R) as Nb'.
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
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR0.
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
  destruct (tcall HΔLA CA1 Hw' Q' HBLBR HbL Hb'L Eb IHb') as (_ & _ & _ & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHb') IHb') Hl2g') as X2r.
  (* the reducts *)
  set (xsL := recTL k ΔL A :: rectL k' (ΔL ,, A @ k) BL b :: nil). set (xsR := recTR k1 ΔR A' :: rectR k1' (ΔR ,, A' @ k1) BR b' :: nil).
  set (rL := ((usubst_tm (bs 11) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 11) (uext (k1 :: k1' :: nil) φ))⦃gext_s (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL (tyPi c1 c2 CL BL) (lam k k' A b) = Some rL)
    by (apply redt_lam_inst; inst_side 11).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR (tyPi c3 c4 CR BR) (lam k1 k1' A' b') = Some rR)
    by (apply redt_lam_inst; inst_side 11).
  refine (rec_t_fin_lam HΔL HΔR HwL HwR HTLk HTRk HcL HcR HWLk HWRk HredL HredR ML MR _).
  refine (rec_t_br_core 11 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil)
            (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HΠΠ') HTL)
            (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HΠΠ') HTR) (ctxconv_eqty HΔ (i := lD) eq_refl HΠ'R)
            HcL0 HcRL HcR0 Ec
            (GS_lam EP EM Hσ HΔL HΔ HA HA'R HAA EA HBLD HBRk HBLBR HbL Hb'R Hbb Eb)
            (GS_lam EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HBR1 HBR1 (eqty_refl _ _ _ _ _ HBR1)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
Qed.


(** ** Neutral scrutinees: the motives and branches under their binders
    (M3_DESIGN.md E13, E14) *)

#[local] Existing Instance LR_M_permRec.

Lemma EP_MT : @geq_ty EM (recGT G') (recΓT Θ) MTL MTR (lvren (lvsubst l1 φ) (ush 1)).
Proof using ELM ELP EMl HG0 He HΓ0 Hσ Hφ VMT VΓT.
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
Proof using ELM ELP EMl HG0 He HΓ0 Hσ Hφ VMt VΓt.
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


Lemma EP_br k : k < nbr ->
  @geq_tm EM (brG k G') (brΓ k Θ (wrapMT MTL) (wrapMt MtL) (lvsubst l1 φ) (lvsubst l2 φ)) (bsL k) (bsR k)
    (brRes k (wrapMT MTL) (wrapMt MtL)) (brLv k (lvsubst l1 φ) (lvsubst l2 φ)).
Proof using ELM ELP EMl HG0 He HrbL HΓ0 Hσ Hφ VBr VΓbr.
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


Lemma EP_all {kL kR ΔL ΔR} : lequiv (gL G') kL kR -> @geq_ctx EP G' ΔL ΔR ->
  ElimPrem EP EM G' Θ (lvsubst l1 φ) (lvsubst l2 φ) (lvsubst l1' φ) (lvsubst l2' φ) MTL MTR MtL MtR bsL bsR
    kL kR ΔL ΔR.
Proof using EL ELM ELP EMl HG0 He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VΓT VΓbr VΓt.
  intros Hk HΔ.
  destruct HrbL as (_ & _ & HMTL & HMtL & HbcL & HbL). destruct HrbR as (_ & _ & HMTR & HMtR & HbcR & HbR).
  constructor; first [ assumption | rewrite EL; assumption | exact EP_MT | exact EP_Mt | exact EP_br ].
Qed.

(** The neutral recursion on types. *)
Lemma rec_T_ne {ΔL ΔR kL kR ν ν'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lwf L' kL -> lequiv L' kL kR -> @geq_ctx EP G' ΔL ΔR ->
  @CtxRelG EP LR_P G' ΔL ΔR -> @CtxRelG EM LR_P G' ΔL ΔR ->
  @gne_tm EM G' Θ ν ν' (tyCTyp ΔL kL) lzero ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL ν) (motT (wrapMT MTR) kR ΔR ν')
    (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL ν)
    (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR ν').
Proof using EL ELM ELP EMl HG0 HMT HMT' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMTr VMt VΓ VΓT VΓbr VΓt.
  intros HΔL HΔ Hw Hk HgΔ CP CM Hν.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HΘ : [ G' ; Θ ⊢[ lM ] ]) by (pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X).
  assert (Hwg : lwf (gL G') kL) by (rewrite EL; exact Hw).
  assert (Hkg : lequiv (gL G') kL kR) by (rewrite EL; exact Hk).
  assert (HwR : lwf (gL G') kR) by exact (lequiv_wf_r _ _ _ Hkg).
  pose proof (CtxRelG_trans CP (CtxRelG_sym CP)) as CPL. pose proof (CtxRelG_trans CM (CtxRelG_sym CM)) as CML.
  pose proof (CtxRelG_trans (CtxRelG_sym CP) CP) as CPR. pose proof (CtxRelG_trans (CtxRelG_sym CM) CM) as CMR.
  pose proof (LR_ctyp EP EM HΘ HΔL HΔL Hwg (lequiv_refl _ _ Hwg) (conj (eqc_refl _ _ _ HΔL) (conj CPL CML))) as LL.
  pose proof (LR_ctyp EP EM HΘ HΔR HΔR HwR (lequiv_refl _ _ HwR) (conj (eqc_refl _ _ _ HΔR) (conj CPR CMR))) as LR0.
  assert (HCC : [ G' ; Θ ⊢[ lM ] tyCTyp ΔL kL ≅ tyCTyp ΔR kR @ lzero ]) by (apply eqty_CTyp; assumption).
  assert (Hν'R : @gne_tm EM G' Θ ν' ν' (tyCTyp ΔR kR) lzero).
  { apply (gne_tm_conv (gne_tm_refl_r Hν)). rewrite (@gm_layer_M EP EM EMl). exact HCC. }
  assert (BL : LRtmM lzero G' Θ (tyCTyp ΔL kL) (tyCTyp ΔL kL) ν ν')
    by (exists (@CTypRel EM LRM G' Θ ΔL ΔL kL kL); exact (conj LL (LR_neutral _ _ _ _ _ _ _ LL _ _ Hν Hν))).
  assert (BR : LRtmM lzero G' Θ (tyCTyp ΔR kR) (tyCTyp ΔR kR) ν' ν')
    by (exists (@CTypRel EM LRM G' Θ ΔR ΔR kR kR); exact (conj LR0 (LR_neutral _ _ _ _ _ _ _ LR0 _ _ Hν'R Hν'R))).
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e e' Hσ He EL
                (kL := kL) (kR := kR) Hw Hk HΔL HΔ BL BR) as Mot.
  pose proof (LRty_eqM Mot) as Meq.
  pose proof (gne_tm_elimT (EP := EP) (EM := EM) Meq (EP_all Hkg HgΔ) Hν) as Hne.
  destruct Mot as [R HR].
  exists R. split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR _ _ Hne).
  apply (gne_tm_conv Hne). rewrite (@gm_layer_M EP EM EMl). exact Meq.
Qed.

(** The neutral recursion on terms. *)
Lemma rec_t_ne {ΔL ΔR kL kR TL TR ν ν'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lwf L' kL -> lequiv L' kL kR -> @geq_ctx EP G' ΔL ΔR ->
  @CtxRelG EP LR_P G' ΔL ΔR -> @CtxRelG EM LR_P G' ΔL ΔR ->
  [ G' ; ΔL ⊢[ lD ] TL @ kL ] -> [ G' ; ΔL ⊢[ lD ] TL ≅ TR @ kL ] ->
  @VTyG EP LR_P G' ΔL TL TR kL -> @VTyG EM LR_P G' ΔL TL TR kL ->
  @gne_tm EM G' Θ ν ν' (tyCTrm ΔL TL kL) lzero ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL ν) (mott (wrapMt MtR) kR ΔR TR ν')
    (elimt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL ν)
    (elimt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR ν').
Proof using EL ELM ELP EMl HG0 HMt HMt' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VMtr VΓ VΓT VΓbr VΓt.
  intros HΔL HΔ Hw Hk HgΔ CP CM HTL HTT VP VM Hν.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HΘ : [ G' ; Θ ⊢[ lM ] ]) by (pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X).
  assert (Hwg : lwf (gL G') kL) by (rewrite EL; exact Hw).
  assert (Hkg : lequiv (gL G') kL kR) by (rewrite EL; exact Hk).
  assert (HwR : lwf (gL G') kR) by exact (lequiv_wf_r _ _ _ Hkg).
  pose proof (eqty_wf_r (i := lD) eq_refl HTT) as HTRL.
  assert (HTR : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTRL) | exact (lequiv_sym _ _ _ Hkg)]. }
  pose proof (CtxRelG_trans CP (CtxRelG_sym CP)) as CPL. pose proof (CtxRelG_trans CM (CtxRelG_sym CM)) as CML.
  pose proof (CtxRelG_trans (CtxRelG_sym CP) CP) as CPR. pose proof (CtxRelG_trans (CtxRelG_sym CM) CM) as CMR.
  destruct (VTyG_escape_P EP EM CPL HΔL HTL HTRL VP) as [HgT _].
  (* the contextual types, each related to itself *)
  assert (VPL : @VTyG EP LR_P G' ΔL TL TL kL) by exact (VTyG_trans VP (VTyG_sym VP)).
  assert (VML : @VTyG EM LR_P G' ΔL TL TL kL) by exact (VTyG_trans VM (VTyG_sym VM)).
  assert (VPR : @VTyG EP LR_P G' ΔR TR TR kR).
  { eapply VTyG_lconv; [exact (VTyG_transport CP (VTyG_trans (VTyG_sym VP) VP)) | exact (lequiv_sym _ _ _ Hkg)]. }
  assert (VMR : @VTyG EM LR_P G' ΔR TR TR kR).
  { eapply VTyG_lconv; [exact (VTyG_transport CM (VTyG_trans (VTyG_sym VM) VM)) | exact (lequiv_sym _ _ _ Hkg)]. }
  pose proof (LR_ctrm EP EM HΘ HΔL HΔL HTL HTL Hwg (lequiv_refl _ _ Hwg) (conj (eqc_refl _ _ _ HΔL) (conj CPL CML))
                (conj (eqty_refl _ _ _ _ _ HTL) (conj VPL VML)) (conj (eqty_refl _ _ _ _ _ HTL) (conj VPL VML))) as LL.
  pose proof (LR_ctrm EP EM HΘ HΔR HΔR HTR HTR HwR (lequiv_refl _ _ HwR) (conj (eqc_refl _ _ _ HΔR) (conj CPR CMR))
                (conj (eqty_refl _ _ _ _ _ HTR) (conj VPR VMR)) (conj (eqty_refl _ _ _ _ _ HTR) (conj VPR VMR))) as LR0.
  assert (HCC : [ G' ; Θ ⊢[ lM ] tyCTrm ΔL TL kL ≅ tyCTrm ΔR TR kR @ lzero ]) by (apply eqty_CTrm; assumption).
  assert (Hν'R : @gne_tm EM G' Θ ν' ν' (tyCTrm ΔR TR kR) lzero).
  { apply (gne_tm_conv (gne_tm_refl_r Hν)). rewrite (@gm_layer_M EP EM EMl). exact HCC. }
  assert (BL : LRtmM lzero G' Θ (tyCTrm ΔL TL kL) (tyCTrm ΔL TL kL) ν ν')
    by (exists (@CTrmRel EM LRM G' Θ ΔL ΔL TL TL kL kL); exact (conj LL (LR_neutral _ _ _ _ _ _ _ LL _ _ Hν Hν))).
  assert (BR : LRtmM lzero G' Θ (tyCTrm ΔR TR kR) (tyCTrm ΔR TR kR) ν' ν')
    by (exists (@CTrmRel EM LRM G' Θ ΔR ΔR TR TR kR kR); exact (conj LR0 (LR_neutral _ _ _ _ _ _ _ LR0 _ _ Hν'R Hν'R))).
  pose proof (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e e' Hσ He EL
                (kL := kL) (kR := kR) Hw Hk HΔL HΔ HTT HTR BL BR) as Mot.
  pose proof (LRty_eqM Mot) as Meq.
  pose proof (gne_tm_elimt (EP := EP) (EM := EM) Meq (EP_all Hkg HgΔ) HTL HTR HgT Hν) as Hne.
  destruct Mot as [R HR].
  exists R. split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR _ _ Hne).
  apply (gne_tm_conv Hne). rewrite (@gm_layer_M EP EM EMl). exact Meq.
Qed.


(** Boxed global variables: the recursions are neutral. *)
Lemma rec_T_gvar {ΔL ΔR kL kR k U d d'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR ->
  [ G' ; ΔL ⊢[ lC ] tyGvar U d @ k ] -> [ G' ; ΔL ⊢[ lC ] tyGvar U d' @ k ] ->
  ty_leq (tyGvar U d) (tyGvar U d') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyGvar U d)))
    (motT (wrapMT MTR) kR ΔR (boxT (tyGvar U d')))
    (recTL kL ΔL (tyGvar U d)) (recTR kR ΔR (tyGvar U d')).
Proof using EL ELM ELP EMl HG0 HMT HMT' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMTr VMt VΓ VΓT VΓbr VΓt.
  intros HΔL HΔ HkL HkR Hc Hc' Ec.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HΘ : [ G' ; Θ ⊢[ lM ] ]) by (pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X).
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Q : lequiv L' kL kR) by exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkL) HkR).
  assert (Qg : lequiv (gL G') kL kR) by (rewrite EL; exact Q).
  assert (HkLg : lequiv (gL G') k kL) by (rewrite EL; exact HkL). assert (HkRg : lequiv (gL G') k kR) by (rewrite EL; exact HkR).
  assert (HcL : [ G' ; ΔL ⊢[ lC ] tyGvar U d @ kL ]) by (eapply wft_lconv; [exact Hc | apply lequiv_sym, HkLg]).
  assert (Hc'L : [ G' ; ΔL ⊢[ lC ] tyGvar U d' @ kL ]) by (eapply wft_lconv; [exact Hc' | apply lequiv_sym, HkLg]).
  assert (Hc'R : [ G' ; ΔR ⊢[ lC ] tyGvar U d' @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lC) eq_refl Hc') | apply lequiv_sym, HkRg]. }
  pose proof (box_rel HΔL HwL HcL Hc'L Ec) as BLR. pose proof (box_rel HΔR HwR Hc'R Hc'R (ty_leq_refl _)) as BRR.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e e' Hσ He EL
                (kL := kL) (kR := kR) HwL Q HΔL HΔ BLR BRR) as Mot.
  pose proof (LRty_eqM Mot) as Meq.
  destruct (CtxRelG_of_eq EP EM HΔ) as [CP _].
  destruct (CtxRelG_escape_P EP EM CP HΔL HΔR) as [HgΔ _].
  pose proof (geq_tm_sound (LRtm_geq BLR)) as Hbox. rewrite (@gm_layer_M EP EM EMl) in Hbox.
  pose proof (gne_tm_elimT_gvar (EP := EP) (EM := EM) Meq (EP_all Qg HgΔ) Hbox) as Hne.
  destruct Mot as [R HR]. exists R. split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR _ _ Hne).
  apply (gne_tm_conv Hne). rewrite (@gm_layer_M EP EM EMl). exact (LRty_eqM (ex_intro _ R HR)).
Qed.

Lemma rec_t_glob {ΔL ΔR kL kR k T0 TL TR c c'} : boxed_global c -> boxed_global c' -> [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR ->
  [ G' ; ΔL ⊢[ lD ] T0 ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] T0 ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lC ] c : T0 @ k ] -> [ G' ; ΔL ⊢[ lC ] c' : T0 @ k ] ->
  tm_leq c c' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt c))
    (mott (wrapMt MtR) kR ΔR TR (boxt c'))
    (rectL kL ΔL TL c) (rectR kR ΔR TR c').
Proof using EL ELM ELP EMl HG0 HMt HMt' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VMtr VΓ VΓT VΓbr VΓt.
  intros Hg Hg' HΔL HΔ HkL HkR HTL HTR Hc Hc' Ec.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HΘ : [ G' ; Θ ⊢[ lM ] ]) by (pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X).
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Q : lequiv L' kL kR) by exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkL) HkR).
  assert (Qg : lequiv (gL G') kL kR) by (rewrite EL; exact Q).
  assert (HkLg : lequiv (gL G') k kL) by (rewrite EL; exact HkL). assert (HkRg : lequiv (gL G') k kR) by (rewrite EL; exact HkR).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (HTLR : [ G' ; ΔL ⊢[ lD ] TL ≅ TR @ kL ]).
  { eapply eqty_lconv; [exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) HTR) | apply lequiv_sym, HkLg]. }
  assert (HcL : [ G' ; ΔL ⊢[ lC ] c : TL @ kL ])
    by (eapply wf_lconv; [eapply wf_conv; [exact Hc | apply eqty_sym, HTL] | apply lequiv_sym, HkLg]).
  assert (Hc'L : [ G' ; ΔL ⊢[ lC ] c' : TL @ kL ])
    by (eapply wf_lconv; [eapply wf_conv; [exact Hc' | apply eqty_sym, HTL] | apply lequiv_sym, HkLg]).
  assert (Hc'R : [ G' ; ΔR ⊢[ lC ] c' : TR @ kR ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact Hc' | apply eqty_sym, HTR] | apply lequiv_sym, HkRg]. }
  pose proof (box_rel_tm HTLk HwL HcL Hc'L Ec) as BLR.
  pose proof (box_rel_tm HTRk HwR Hc'R Hc'R (tm_leq_refl _)) as BRR.
  pose proof (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e e' Hσ He EL
                (kL := kL) (kR := kR) HwL Q HΔL HΔ HTLR HTRk BLR BRR) as Mot.
  pose proof (LRty_eqM Mot) as Meq.
  destruct (CtxRelG_of_eq EP EM HΔ) as [CP _]. destruct (CtxRelG_of_eq EP EM (eqc_refl _ _ _ HΔL)) as [CPL _].
  destruct (CtxRelG_escape_P EP EM CP HΔL HΔR) as [HgΔ _].
  destruct (VTyG_of_eq EP EM HTLR) as [VP _].
  destruct (VTyG_escape_P EP EM CPL HΔL HTLk (eqty_wf_r (i := lD) eq_refl HTLR) VP) as [HgT _].
  pose proof (geq_tm_sound (LRtm_geq BLR)) as Hbox. rewrite (@gm_layer_M EP EM EMl) in Hbox.
  pose proof (gne_tm_elimt_glob (EP := EP) (EM := EM) Hg Hg' Meq (EP_all Qg HgΔ) HTLk HTRk HgT Hbox) as Hne.
  destruct Mot as [R HR]. exists R. split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR _ _ Hne).
  apply (gne_tm_conv Hne). rewrite (@gm_layer_M EP EM EMl). exact (LRty_eqM (ex_intro _ R HR)).
Qed.


(** ** The recursion lemmas proper (M3_DESIGN.md E13)

    By induction on the left code's C-typing at [G']: for every context
    [ΔR] equal to its context, every right code [≡ₗ]-related to it (with
    well-formed levels, hence typed by the static code lemma), and every
    pair of index types (terms) or levels equivalent to its own, the two
    recursions are related at the motives' instances. *)

Definition RT Δ c k := [ G' ; Δ ⊢[ lC ] c @ k ] ->
  forall ΔR kL kR c', [ G' ⊢[ lD ] Δ ≅ ΔR ] -> lequiv L' k kL -> lequiv L' k kR ->
  ty_leq c c' -> ty_lwf L' c' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL Δ (boxT c)) (motT (wrapMT MTR) kR ΔR (boxT c'))
    (recTL kL Δ c) (recTR kR ΔR c').
Definition Rt Δ c T k := [ G' ; Δ ⊢[ lC ] c : T @ k ] ->
  forall ΔR kL kR TL TR c', [ G' ⊢[ lD ] Δ ≅ ΔR ] -> lequiv L' k kL -> lequiv L' k kR ->
  [ G' ; Δ ⊢[ lD ] T ≅ TL @ k ] -> [ G' ; Δ ⊢[ lD ] T ≅ TR @ k ] ->
  tm_leq c c' -> tm_lwf L' c' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL Δ TL (boxt c)) (mott (wrapMt MtR) kR ΔR TR (boxt c'))
    (rectL kL Δ TL c) (rectR kR ΔR TR c').

Lemma HCD : lle lC lD. Proof using EL. unfold lle; cbn; lia. Qed.

Lemma scr_ty {Δ c c' k} : [ G' ; Δ ⊢[ lC ] c @ k ] -> ty_leq c c' -> ty_lwf L' c' ->
  [ G' ; Δ ⊢[ lC ] c' @ k ] /\ [ G' ; Δ ⊢[ lD ] c ≅ c' @ k ].
Proof using EL.
  intros H E W. rewrite <- EL in W.
  destruct (proj1 (proj2 (proj2 static_code)) _ _ _ _ _ H HCD _ E W) as [H1 H2].
  exact (conj H1 (lift_eqty H2 HCD)).
Qed.
Lemma scr_tm {Δ c c' T k} : [ G' ; Δ ⊢[ lC ] c : T @ k ] -> tm_leq c c' -> tm_lwf L' c' ->
  [ G' ; Δ ⊢[ lC ] c' : T @ k ] /\ [ G' ; Δ ⊢[ lD ] c ≅ c' : T @ k ].
Proof using EL.
  intros H E W. rewrite <- EL in W.
  destruct (proj1 (proj2 (proj2 (proj2 static_code))) _ _ _ _ _ _ H HCD _ E W) as [H1 H2].
  exact (conj H1 (lift_eqtm H2 HCD)).
Qed.

Lemma ceq_ext {Δ ΔR A A' k k'} : [ G' ⊢[ lD ] Δ ≅ ΔR ] -> [ G' ; Δ ⊢[ lD ] A @ k ] ->
  [ G' ; Δ ⊢[ lD ] A ≅ A' @ k ] -> lequiv L' k k' -> [ G' ⊢[ lD ] Δ ,, A @ k ≅ ΔR ,, A' @ k' ].
Proof using EL. intros; apply eqc_ext; [assumption | assumption | assumption | rewrite EL; assumption]. Qed.

Lemma eq_self_l {Δ T T' k} : [ G' ; Δ ⊢[ lD ] T ≅ T' @ k ] -> [ G' ; Δ ⊢[ lD ] T ≅ T @ k ].
Proof using . intros H; exact (eqty_trans _ _ _ _ _ _ _ H (eqty_sym _ _ _ _ _ _ H)). Qed.

(** ** One recursive call, generically (M15b step 0)

    From a component's hypothesis ([RT]/[Rt]) and its [≤]-related right
    side: the right side's typings, the conversion, the call related at
    the related contexts in [Tcall]/[tcall]'s form, and the right call
    related to itself at the right level (the hand-written branches'
    [X r] lines). *)
Lemma RTcall {ΔL ΔR k k1 A A'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] -> lwf L' k -> lwf L' k1 ->
  leqv k k1 -> [ G' ; ΔL ⊢[ lC ] A @ k ] -> ty_leq A A' -> ty_lwf L' A' -> RT ΔL A k ->
  [ G' ; ΔL ⊢[ lC ] A' @ k ] /\ [ G' ; ΔL ⊢[ lD ] A ≅ A' @ k ] /\ [ G' ; ΔR ⊢[ lC ] A' @ k ] /\
  [ G' ; ΔR ⊢[ lC ] A' @ k1 ] /\
  [ G' ⊢[ lD ] ΔL ,, A @ k ≅ ΔR ,, A' @ k ] /\ [ G' ⊢[ lD ] ΔL ,, A @ k ≅ ΔR ,, A' @ k1 ] /\
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A))
    (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e'))])) k ΔL (boxT A))
    (recTL k ΔL A) (recTR k1 ΔR A') /\
  LRtmM (lvsubst l1' φ) G' Θ (motT (wrapMT MTR) k1 ΔR (boxT A')) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTR k1 ΔR A') (recTR k1 ΔR A').
Proof using EL ELM ELP EMl HMT HMT' He Hl1 Hσ Hφ VMT VMTr VΓ.
  intros HΔL HΔ Hw Hw1 E HA EA WA IHA.
  destruct (scr_ty HA EA WA) as [HA' _]. pose proof (lq Hw Hw1 E) as Q.
  pose proof (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q EA WA) as X.
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA X) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  refine (conj HA' (conj HAA (conj HA'R (conj HA'R1 (conj CA (conj CA1 (conj X1 _))))))).
  refine (LRtm_lconv (LRtm_trans (LRtm_sym X) X) _). rewrite EL; exact (lequiv_sym _ _ _ Hl1).
Qed.

Lemma Rtcall {ΔL ΔR k k1 T T' t t'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] -> lwf L' k -> lwf L' k1 ->
  leqv k k1 -> [ G' ; ΔL ⊢[ lD ] T ≅ T' @ k ] ->
  [ G' ; ΔL ⊢[ lC ] t : T @ k ] -> tm_leq t t' -> tm_lwf L' t' -> Rt ΔL t T k ->
  [ G' ; ΔL ⊢[ lC ] t' : T @ k ] /\ [ G' ; ΔL ⊢[ lD ] t ≅ t' : T @ k ] /\ [ G' ; ΔR ⊢[ lC ] t' : T @ k ] /\
  [ G' ; ΔR ⊢[ lC ] t' : T' @ k1 ] /\
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL T (boxt t))
    (mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e')))])) k ΔL T (boxt t))
    (rectL k ΔL T t) (rectR k1 ΔR T' t') /\
  LRtmM (lvsubst l2' φ) G' Θ (mott (wrapMt MtR) k1 ΔR T' (boxt t')) (mott (wrapMt MtR) k1 ΔR T' (boxt t'))
    (rectR k1 ΔR T' t') (rectR k1 ΔR T' t').
Proof using EL ELM ELP EMl HMt HMt' He Hl2 Hσ Hφ VMt VMtr VΓ.
  intros HΔL HΔ Hw Hw1 E HTT Ht Et Wt IHt.
  destruct (scr_tm Ht Et Wt) as [Ht' _]. pose proof (lq Hw Hw1 E) as Q.
  pose proof (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HTT) HTT Et Wt) as X.
  destruct (tcall HΔL HΔ Hw Q HTT Ht Ht' Et X) as (Htt & _ & Ht'R1 & _ & X1).
  refine (conj Ht' (conj Htt (conj (ctxconv_tm HΔ (i := lC) eq_refl Ht') (conj Ht'R1 (conj X1 _))))).
  refine (LRtm_lconv (LRtm_trans (LRtm_sym X) X) _). rewrite EL; exact (lequiv_sym _ _ _ Hl2).
Qed.

(** The mismatched formers are closed by conversion before [cbn], which
    then runs on the one that survives (as [leq_cases], [LevelEq.v]). *)
Ltac leq_inv := match goal with
  | E : ty_leq _ ?c, W : ty_lwf _ ?c |- _ =>
      is_var c; destruct c; try exact (False_ind _ E); cbn in E, W; try contradiction
  | E : tm_leq _ ?c, W : tm_lwf _ ?c |- _ =>
      is_var c; destruct c; try exact (False_ind _ E); cbn in E, W; try contradiction
  end; repeat match goal with H : _ /\ _ |- _ => destruct H end.

Lemma RT_nat {Δ} : RT Δ tyNat lzero.
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  exact (rec_T_nat HΔL HΔ HkL HkR).
Qed.

Lemma RT_U {Δ k} : RT Δ (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_T_U HΔL HΔ HkL HkR Hw W E).
Qed.

Lemma RT_lconv {Δ c k k'} : lequiv (gL G') k k' -> [ G' ; Δ ⊢[ lC ] c @ k' ] -> RT Δ c k' -> RT Δ c k.
Proof using EL.
  intros Q Hc' IH _ ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Q.
  exact (IH Hc' ΔR kL kR c' HΔ (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkL)
           (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkR) E W).
Qed.

Lemma RT_gvar {Δ U d k} : RT Δ (tyGvar U d) k.
Proof using EL ELM ELP EMl HG0 HMT HMT' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMTr VMt VΓ VΓT VΓbr VΓt.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  destruct (scr_ty Hc E W) as [Hc' _]. pose proof E as E0; revert E0. leq_inv. match goal with H : U = ?x |- _ => subst x end. intros E0.
  exact (rec_T_gvar HΔL HΔ HkL HkR Hc Hc' E0).
Qed.

Lemma RT_pi {Δ k1 k2 A B} : lwf (gL G') k1 -> lwf (gL G') k2 ->
  [ G' ; Δ ⊢[ lC ] A @ k1 ] -> [ G' ; Δ ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  RT Δ A k1 -> RT (Δ ,, A @ k1) B k2 -> RT Δ (tyPi k1 k2 A B) (lmax k1 k2).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hw1 Hw2 HA HB IHA IHB Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw1, Hw2.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  refine (rec_T_pi HΔL HΔ HkL HkR Hw1 Hw2 _ _ _ _ HA HB HA' HB' _ _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw1) (lq Hw1 _ _) _ _); eassumption.
  - refine (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA (lq Hw1 _ _)) (lequiv_refl _ _ Hw2) (lq Hw2 _ _) _ _);
      eassumption.
Qed.

Lemma RT_El {Δ k t} : lwf (gL G') k -> [ G' ; Δ ⊢[ lC ] t : tyU k @ lsuc k ] ->
  Rt Δ t (tyU k) (lsuc k) -> RT Δ (tyEl k t) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtr VΓ.
  intros Hw Ht IH Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_T_El HΔL HΔ HkL HkR Hw _ _ Ht Ht' _ _); try eassumption.
  refine (IH Ht _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
  - apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
  - apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
Qed.

Lemma Rt_conv {Δ t T T' k} : [ G' ; Δ ⊢[ lD ] T ≅ T' @ k ] -> [ G' ; Δ ⊢[ lC ] t : T' @ k ] ->
  Rt Δ t T' k -> Rt Δ t T k.
Proof using .
  intros HT Ht IH _ ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W.
  apply (IH Ht); try assumption;
    [exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HT) HTL) | exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HT) HTR)].
Qed.

Lemma Rt_lconv {Δ t T k k'} : lequiv (gL G') k k' -> [ G' ; Δ ⊢[ lC ] t : T @ k' ] -> Rt Δ t T k' -> Rt Δ t T k.
Proof using EL.
  intros Q Ht IH _ ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof Q as Qg. rewrite EL in Q.
  exact (IH Ht ΔR kL kR TL TR c' HΔ (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkL)
           (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkR)
           (eqty_lconv _ _ _ _ _ _ _ HTL (lequiv_sym _ _ _ Qg)) (eqty_lconv _ _ _ _ _ _ _ HTR (lequiv_sym _ _ _ Qg)) E W).
Qed.

Lemma Rt_var {Δ n T k} : in_ctx Δ n T k -> Rt Δ (var n) T k.
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hin Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv. match goal with H : n = ?x |- _ => subst x end.
  refine (rec_t_var HΔL HΔ HkL HkR HTL HTR _).
  apply wf_var; assumption.
Qed.

Lemma Rt_gvar {Δ u d T k} : Rt Δ (gvar u d) T k.
Proof using EL ELM ELP EMl HG0 HMt HMt' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VMtr VΓ VΓT VΓbr VΓt.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  destruct (scr_tm Hc E W) as [Hc' _]. pose proof E as E0; revert E0. leq_inv. match goal with H : u = ?x |- _ => subst x end. intros E0.
  refine (rec_t_glob _ _ HΔL HΔ HkL HkR HTL HTR Hc Hc' E0); exact I.
Qed.

(** A defined global is code the recursor does not enter (M9). *)
Lemma Rt_gdef {Δ u b d T k} : Rt Δ (gdef u b d) T k.
Proof using EL ELM ELP EMl HG0 HMt HMt' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VMtr VΓ VΓT VΓbr VΓt.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  destruct (scr_tm Hc E W) as [Hc' _].
  refine (rec_t_glob _ _ HΔL HΔ HkL HkR HTL HTR Hc Hc' E); [exact I | exact (boxed_global_leq (gdef u b d) c' I E)].
Qed.

Lemma Rt_nat {Δ} : Rt Δ tmNat (tyU lzero) (lsuc lzero).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  exact (rec_t_nat HΔL HΔ HkL HkR HTL HTR).
Qed.
Lemma Rt_zero {Δ} : Rt Δ zero tyNat lzero.
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  exact (rec_t_zero HΔL HΔ HkL HkR HTL HTR).
Qed.
Lemma Rt_U {Δ j} : Rt Δ (tmU j) (tyU (lsuc j)) (lsuc (lsuc j)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_t_U HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_succ {Δ t} : [ G' ; Δ ⊢[ lC ] t : tyNat @ lzero ] -> Rt Δ t tyNat lzero -> Rt Δ (succ t) tyNat lzero.
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Ht IH Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  destruct (scr_tm Ht E W) as [Ht' _].
  refine (rec_t_succ HΔL HΔ HkL HkR HTL HTR Ht Ht' E _).
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  exact (IH Ht _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN E W).
Qed.

Lemma Rt_pi {Δ k k' s t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) t (tyU k') (lsuc k') ->
  Rt Δ (tmPi k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hw' Hs Ht IHs IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (sc_ctx_tm HCD Ht) as HΔLs. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_pi HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR Hs Hs' _ Ht Ht' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
    refine (IHt Ht _ _ _ _ _ _ (ceq_ext HΔ HEl _ Q) (lequiv_refl L' (lsuc k') Hw') (lequiv_lsuc' _ _ _ Q') _ _ _ _);
      try eassumption.
    + apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss].
    + apply eqty_refl, wft_U; [discriminate | exact HΔLs | rewrite EL; exact Hw'].
    + apply eqty_U; [discriminate | exact HΔLs | rewrite EL; exact Q'].
Qed.

Lemma Rt_lam {Δ k k' A B b} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] b : B @ k' ] ->
  RT Δ A k -> Rt (Δ ,, A @ k) b B k' -> Rt Δ (lam k k' A b) (tyPi k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA Hb IHA IHb Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_lam HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ Hb Hb' _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - intros BL BR HBL HBR.
    exact (IHb Hb _ _ _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q' HBL HBR
             ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_app {Δ k k' A B f a} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ⊢[ lC ] f : tyPi k k' A B @ lmax k k' ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ f (tyPi k k' A B) (lmax k k') -> Rt Δ a A k ->
  Rt Δ (app f k k' A B a) (B[lsingle a]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Hf Ha IHA IHB IHf IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Hf ltac:(eassumption) ltac:(eassumption)) as [Hf' _].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (X : [ G' ; Δ ⊢[ lD ] tyPi k k' A B ≅ tyPi k1 k1' A' B' @ lmax k k' ]).
  { apply eqty_pi; [discriminate | rewrite EL; exact Q | rewrite EL; exact Q' | exact (lift_ty HA HCD) | exact HAA | exact HBB]. }
  refine (rec_t_app HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Hf Hf' _ Ha Ha' _ _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHf Hf _ _ _ _ _ _ HΔ (lequiv_refl L' (lmax k k') (conj Hw Hw')) (lequiv_lmax' _ _ _ _ _ Q Q')
             (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_natrec {Δ k M s z t} : lwf (gL G') k ->
  [ G' ; Δ ,, tyNat @ lzero ⊢[ lC ] M @ k ] -> [ G' ; Δ ⊢[ lC ] s : M[lsingle zero] @ k ] ->
  [ G' ; Δ ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z : M[lsucc] @ k ] -> [ G' ; Δ ⊢[ lC ] t : tyNat @ lzero ] ->
  RT (Δ ,, tyNat @ lzero) M k -> Rt Δ s (M[lsingle zero]) k ->
  Rt (Δ ,, tyNat @ lzero ,, M @ k) z (M[lsucc]) k -> Rt Δ t tyNat lzero ->
  Rt Δ (natrec k M s z t) (M[lsingle t]) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw HM Hs Hz Ht IHM IHs IHz IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq M ?x |- _ => rename x into M' end.
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' HMM].
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' _].
  destruct (scr_tm Hz ltac:(eassumption) ltac:(eassumption)) as [Hz' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HN0 : [ G' ; Δ ⊢[ lD ] tyNat @ lzero ]) by (apply wft_nat; [discriminate | exact HΔL]).
  assert (CN : [ G' ⊢[ lD ] Δ ,, tyNat @ lzero ≅ ΔR ,, tyNat @ lzero ])
    by (apply ceq_ext; [exact HΔ | exact HN0 | apply eqty_refl, HN0 | apply lequiv_refl; exact I]).
  pose proof (lift_ty HM HCD) as HMD.
  assert (CNM : [ G' ⊢[ lD ] Δ ,, tyNat @ lzero ,, M @ k ≅ ΔR ,, tyNat @ lzero ,, M' @ k1 ])
    by (apply ceq_ext; [exact CN | exact HMD | exact HMM | exact Q]).
  pose proof (sc_ctx_tm HCD Hz) as HΔLNM.
  assert (HM0 : [ G' ; Δ ⊢[ lD ] M[lsingle zero] ≅ M'[lsingle zero] @ k ])
    by exact (eqty_single (i := lD) eq_refl HMM (wf_zero _ lD _ ltac:(discriminate) HΔL)).
  assert (HMs : [ G' ; Δ ,, tyNat @ lzero ,, M @ k ⊢[ lD ] M[lsucc] ≅ M'[lsucc] @ k ])
    by exact (eqty_subst (i := lD) eq_refl HMM (lsub_wf_lsucc (i := lD) eq_refl ltac:(discriminate) HΔLNM)).
  assert (HNN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, HN0).
  refine (rec_t_natrec HΔL HΔ HkL HkR Hw _ _ HTL HTR HM HM' _ Hs Hs' _ Hz Hz' _ Ht Ht' _ _ _ _ _); try eassumption.
  - exact (IHM HM _ _ _ _ CN (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HM0) HM0 ltac:(eassumption) ltac:(eassumption)).
  - exact (IHz Hz _ _ _ _ _ _ CNM (lequiv_refl _ _ Hw) Q (eq_self_l HMs) HMs ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HNN HNN
             ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma RT_sig {Δ k1 k2 A B} : lwf (gL G') k1 -> lwf (gL G') k2 ->
  [ G' ; Δ ⊢[ lC ] A @ k1 ] -> [ G' ; Δ ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  RT Δ A k1 -> RT (Δ ,, A @ k1) B k2 -> RT Δ (tySig k1 k2 A B) (lmax k1 k2).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hw1 Hw2 HA HB IHA IHB Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw1, Hw2.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  refine (rec_T_sig HΔL HΔ HkL HkR Hw1 Hw2 _ _ _ _ HA HB HA' HB' _ _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw1) (lq Hw1 _ _) _ _); eassumption.
  - refine (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA (lq Hw1 _ _)) (lequiv_refl _ _ Hw2) (lq Hw2 _ _) _ _);
      eassumption.
Qed.

Lemma RT_W {Δ k1 k2 A B} : lwf (gL G') k1 -> lwf (gL G') k2 ->
  [ G' ; Δ ⊢[ lC ] A @ k1 ] -> [ G' ; Δ ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  RT Δ A k1 -> RT (Δ ,, A @ k1) B k2 -> RT Δ (tyW k1 k2 A B) (lmax k1 k2).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hw1 Hw2 HA HB IHA IHB Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw1, Hw2.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  refine (rec_T_W HΔL HΔ HkL HkR Hw1 Hw2 _ _ _ _ HA HB HA' HB' _ _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw1) (lq Hw1 _ _) _ _); eassumption.
  - refine (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA (lq Hw1 _ _)) (lequiv_refl _ _ Hw2) (lq Hw2 _ _) _ _);
      eassumption.
Qed.

Lemma RT_unit {Δ k} : RT Δ (tyUnit k) k.
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw. leq_inv.
  exact (rec_T_unit HΔL HΔ HkL HkR Hw W E).
Qed.

Lemma Rt_codesig {Δ k k' s t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) t (tyU k') (lsuc k') ->
  Rt Δ (tmSig k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hw' Hs Ht IHs IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (sc_ctx_tm HCD Ht) as HΔLs. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_codesig HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR Hs Hs' _ Ht Ht' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
    refine (IHt Ht _ _ _ _ _ _ (ceq_ext HΔ HEl _ Q) (lequiv_refl L' (lsuc k') Hw') (lequiv_lsuc' _ _ _ Q') _ _ _ _);
      try eassumption.
    + apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss].
    + apply eqty_refl, wft_U; [discriminate | exact HΔLs | rewrite EL; exact Hw'].
    + apply eqty_U; [discriminate | exact HΔLs | rewrite EL; exact Q'].
Qed.

Lemma Rt_codeW {Δ k k' s t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) t (tyU k') (lsuc k') ->
  Rt Δ (tmW k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hw' Hs Ht IHs IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (sc_ctx_tm HCD Ht) as HΔLs. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_codeW HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR Hs Hs' _ Ht Ht' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
    refine (IHt Ht _ _ _ _ _ _ (ceq_ext HΔ HEl _ Q) (lequiv_refl L' (lsuc k') Hw') (lequiv_lsuc' _ _ _ Q') _ _ _ _);
      try eassumption.
    + apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss].
    + apply eqty_refl, wft_U; [discriminate | exact HΔLs | rewrite EL; exact Hw'].
    + apply eqty_U; [discriminate | exact HΔLs | rewrite EL; exact Q'].
Qed.

Lemma Rt_codeunit {Δ j} : Rt Δ (tmUnit j) (tyU j) (lsuc j).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_t_codeunit HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_triv {Δ j} : Rt Δ (tmTriv j) (tyUnit j) j.
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw. leq_inv.
  exact (rec_t_triv HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_pair {Δ k k' A B a b} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ⊢[ lC ] a : A @ k ] -> [ G' ; Δ ⊢[ lC ] b : B[lsingle a] @ k' ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ a A k -> Rt Δ b (B[lsingle a]) k' ->
  Rt Δ (tmPair k k' A B a b) (tySig k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Ha Hb IHA IHB IHa IHb Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  match goal with H : tm_leq a ?x |- _ => rename x into a' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' Haa].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (X : [ G' ; Δ ⊢[ lD ] B[lsingle a] ≅ B'[lsingle a'] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty HB' HCD) Haa (lift_tm Ha HCD) (lift_tm Ha' HCD)).
  refine (rec_t_pair HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Ha Ha' _ Hb Hb' _ _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHb Hb _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_fst {Δ k k' A B p} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ p (tySig k k' A B) (lmax k k') ->
  Rt Δ (tmFst k k' A B p) A k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Hp IHA IHB IHp Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Hp ltac:(eassumption) ltac:(eassumption)) as [Hp' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (X : [ G' ; Δ ⊢[ lD ] tySig k k' A B ≅ tySig k1 k1' A' B' @ lmax k k' ]).
  { apply eqty_sig; [discriminate | rewrite EL; exact Q | rewrite EL; exact Q' | exact (lift_ty HA HCD) | exact HAA | exact HBB]. }
  refine (rec_t_fst HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Hp Hp' _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHp Hp _ _ _ _ _ _ HΔ (lequiv_refl L' (lmax k k') (conj Hw Hw')) (lequiv_lmax' _ _ _ _ _ Q Q')
             (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_snd {Δ k k' A B p} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ p (tySig k k' A B) (lmax k k') ->
  Rt Δ (tmSnd k k' A B p) (B[lsingle (tmFst k k' A B p)]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Hp IHA IHB IHp Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Hp ltac:(eassumption) ltac:(eassumption)) as [Hp' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (X : [ G' ; Δ ⊢[ lD ] tySig k k' A B ≅ tySig k1 k1' A' B' @ lmax k k' ]).
  { apply eqty_sig; [discriminate | rewrite EL; exact Q | rewrite EL; exact Q' | exact (lift_ty HA HCD) | exact HAA | exact HBB]. }
  refine (rec_t_snd HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Hp Hp' _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHp Hp _ _ _ _ _ _ HΔ (lequiv_refl L' (lmax k k') (conj Hw Hw')) (lequiv_lmax' _ _ _ _ _ Q Q')
             (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma RT_id {Δ k A a b} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] -> [ G' ; Δ ⊢[ lC ] b : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ b A k -> RT Δ (tyId k A a b) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha Hb IHA IHa IHb Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_T_id HΔL HΔ HkL HkR Hw _ _ HA HA' _ Ha Ha' _ Hb Hb' _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHb Hb _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_codeid {Δ k s t u} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G' ; Δ ⊢[ lC ] t : tyEl k s @ k ] -> [ G' ; Δ ⊢[ lC ] u : tyEl k s @ k ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ t (tyEl k s) k -> Rt Δ u (tyEl k s) k ->
  Rt Δ (tmId k s t u) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hs Ht Hu IHs IHt IHu Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : tm_leq s ?x |- _ => rename x into s' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  destruct (scr_tm Hu ltac:(eassumption) ltac:(eassumption)) as [Hu' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HUU : [ G' ; Δ ⊢[ lD ] tyU k ≅ tyU k1 @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q]).
  assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s ≅ tyEl k1 s' @ k ])
    by (apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss]).
  refine (rec_t_codeid HΔL HΔ HkL HkR Hw _ _ HTL HTR Hs Hs' _ Ht Ht' _ Hu Hu' _ _ _ _); try eassumption.
  - exact (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_suc _ _ _ Q) (eq_self_l HUU) HUU
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HEl) HEl ltac:(eassumption) ltac:(eassumption)).
  - exact (IHu Hu _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HEl) HEl ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_refl {Δ k A a} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ (tmRefl k A a) (tyId k A a a) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha IHA IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_t_refl HΔL HΔ HkL HkR Hw _ _ HTL HTR HA HA' _ Ha Ha' _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_J {Δ k k' A a M c u e0} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ] ->
  [ G' ; Δ ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lC ] M @ k' ] ->
  [ G' ; Δ ⊢[ lC ] c : M[lsingle2 a (tmRefl k A a)] @ k' ] ->
  [ G' ; Δ ⊢[ lC ] u : A @ k ] -> [ G' ; Δ ⊢[ lC ] e0 : tyId k A a u @ k ] ->
  RT Δ A k -> Rt Δ a A k -> RT (Δ ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) M k' ->
  Rt Δ c (M[lsingle2 a (tmRefl k A a)]) k' -> Rt Δ u A k -> Rt Δ e0 (tyId k A a u) k ->
  Rt Δ (tmJ k k' A a M c u e0) (M[lsingle2 u e0]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA Ha HI HM Hc Hu He0 IHA IHa IHM IHc IHu IHe Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : tm_leq a ?x |- _ => rename x into a' end.
  match goal with H : ty_leq M ?x |- _ => rename x into M' end.
  match goal with H : tm_leq u ?x |- _ => rename x into u' end.
  match goal with H : tm_leq e0 ?x |- _ => rename x into e0' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' Haa].
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' HMM].
  destruct (scr_tm Hc ltac:(eassumption) ltac:(eassumption)) as [Hc' _].
  destruct (scr_tm Hu ltac:(eassumption) ltac:(eassumption)) as [Hu' Huu].
  destruct (scr_tm He0 ltac:(eassumption) ltac:(eassumption)) as [He0' Hee].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  pose proof (J_ctx_eq' (i := lD) eq_refl ltac:(discriminate) Qg HΔ (lift_ty HA HCD) HAA Haa) as CM1.
  destruct (J_facts_D (l3 := k1) Qg (lift_ty HA HCD) HAA (lift_ty HA' HCD) (lift_tm Ha HCD) Haa (lift_tm Ha' HCD)
              HMM (lift_ty HM' HCD) (lift_tm Hu HCD) Huu (lift_tm Hu' HCD) (lift_tm He0 HCD) Hee (lift_tm He0' HCD))
    as (_ & Hc1 & _ & HId1).
  refine (rec_t_J HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ Ha Ha' _ HI HM HM' _ Hc Hc' _ Hu Hu' _ He0 He0' _
            _ _ _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHM HM _ _ _ _ CM1 (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHc Hc _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' (eq_self_l Hc1) Hc1 ltac:(eassumption) ltac:(eassumption)).
  - exact (IHu Hu _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHe He0 _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HId1) HId1 ltac:(eassumption) ltac:(eassumption)).
Qed.

(** Strict equality (M10c). *)
Lemma RT_seq {Δ k A a b} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] -> [ G' ; Δ ⊢[ lC ] b : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ b A k -> RT Δ (tySEq k A a b) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha Hb IHA IHa IHb Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_T_seq HΔL HΔ HkL HkR Hw _ _ HA HA' _ Ha Ha' _ Hb Hb' _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHb Hb _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_codeseq {Δ k s t u} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G' ; Δ ⊢[ lC ] t : tyEl k s @ k ] -> [ G' ; Δ ⊢[ lC ] u : tyEl k s @ k ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ t (tyEl k s) k -> Rt Δ u (tyEl k s) k ->
  Rt Δ (tmSEq k s t u) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hs Ht Hu IHs IHt IHu Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : tm_leq s ?x |- _ => rename x into s' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  destruct (scr_tm Hu ltac:(eassumption) ltac:(eassumption)) as [Hu' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HUU : [ G' ; Δ ⊢[ lD ] tyU k ≅ tyU k1 @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q]).
  assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s ≅ tyEl k1 s' @ k ])
    by (apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss]).
  refine (rec_t_codeseq HΔL HΔ HkL HkR Hw _ _ HTL HTR Hs Hs' _ Ht Ht' _ Hu Hu' _ _ _ _); try eassumption.
  - exact (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_suc _ _ _ Q) (eq_self_l HUU) HUU
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HEl) HEl ltac:(eassumption) ltac:(eassumption)).
  - exact (IHu Hu _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HEl) HEl ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_srefl {Δ k A a} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ (srefl k A a) (tySEq k A a a) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha IHA IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_t_srefl HΔL HΔ HkL HkR Hw _ _ HTL HTR HA HA' _ Ha Ha' _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma RT_sempty {Δ k} : RT Δ (tySEmpty k) k.
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw. leq_inv.
  exact (rec_T_sempty HΔL HΔ HkL HkR Hw W E).
Qed.

Lemma Rt_codesempty {Δ j} : Rt Δ (tmSEmpty j) (tyU j) (lsuc j).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_t_codesempty HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_elimSEmpty {Δ k k' M e0} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] M @ k' ] -> [ G' ; Δ ⊢[ lC ] e0 : tySEmpty k @ k ] ->
  RT Δ M k' -> Rt Δ e0 (tySEmpty k) k -> Rt Δ (elimSEmpty k k' M e0) M k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HM He0 IHM IHe Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq M ?x |- _ => rename x into M' end.
  match goal with H : tm_leq e0 ?x |- _ => rename x into e0' end.
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' _].
  destruct (scr_tm He0 ltac:(eassumption) ltac:(eassumption)) as [He0' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (HSE : [ G' ; Δ ⊢[ lD ] tySEmpty k ≅ tySEmpty k1 @ k ])
    by (apply eqty_sempty; [discriminate | exact HΔL | rewrite EL; exact Q]).
  refine (rec_t_elimSEmpty HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HM HM' _ He0 He0' _ _ _); try eassumption.
  - exact (IHM HM _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHe He0 _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HSE) HSE ltac:(eassumption) ltac:(eassumption)).
Qed.

(** The empty type and binary sums (M12c). *)
Lemma RT_empty {Δ k} : RT Δ (tyEmpty k) k.
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw. leq_inv.
  exact (rec_T_empty HΔL HΔ HkL HkR Hw W E).
Qed.

Lemma Rt_codeempty {Δ j} : Rt Δ (tmEmpty j) (tyU j) (lsuc j).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_t_codeempty HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_elimEmpty {Δ k k' M t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ,, tyEmpty k' @ k' ⊢[ lC ] M @ k ] -> [ G' ; Δ ⊢[ lC ] t : tyEmpty k' @ k' ] ->
  RT (Δ ,, tyEmpty k' @ k') M k -> Rt Δ t (tyEmpty k') k' -> Rt Δ (elimEmpty k k' M t) (M[lsingle t]) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HM Ht IHM IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (HED : [ G' ; Δ ⊢[ lD ] tyEmpty k' @ k' ])
    by (apply wft_empty; [discriminate | exact HΔL | rewrite EL; exact Hw']).
  assert (HEE : [ G' ; Δ ⊢[ lD ] tyEmpty k' ≅ tyEmpty k1' @ k' ])
    by (apply eqty_empty; [discriminate | exact HΔL | rewrite EL; exact Q']).
  refine (rec_t_elimEmpty HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HM HM' _ Ht Ht' _ _ _); try eassumption.
  - exact (IHM HM _ _ _ _ (ceq_ext HΔ HED HEE Q') (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' (eq_self_l HEE) HEE ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma RT_sum {Δ k k' A B} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] B @ k' ] ->
  RT Δ A k -> RT Δ B k' -> RT Δ (tySum k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hw Hw' HA HB IHA IHB Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' _].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' _].
  refine (rec_T_sum HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HA HB HA' HB' _ _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) (lq Hw _ _) _ _); eassumption.
  - refine (IHB HB _ _ _ _ HΔ (lequiv_refl _ _ Hw') (lq Hw' _ _) _ _); eassumption.
Qed.

Lemma Rt_codesum {Δ k k' s t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ t (tyU k') (lsuc k') ->
  Rt Δ (tmSum k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hw' Hs Ht IHs IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_codesum HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR Hs Hs' _ Ht Ht' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - refine (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k') Hw') (lequiv_lsuc' _ _ _ Q') _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw'].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q'].
Qed.

Lemma Rt_inl {Δ k k' A B a} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] B @ k' ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> RT Δ B k' -> Rt Δ a A k -> Rt Δ (tmInl k k' A B a) (tySum k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Ha IHA IHB IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' _].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_inl HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Ha Ha' _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_inr {Δ k k' A B b} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] B @ k' ] -> [ G' ; Δ ⊢[ lC ] b : B @ k' ] ->
  RT Δ A k -> RT Δ B k' -> Rt Δ b B k' -> Rt Δ (tmInr k k' A B b) (tySum k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Hb IHA IHB IHb Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' _].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_inr HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Hb Hb' _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHb Hb _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' (eq_self_l HBB) HBB ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_case {Δ k k' k'' A B M c1 c2 t} : lwf (gL G') k -> lwf (gL G') k' -> lwf (gL G') k'' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ,, tySum k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] c1 : M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; Δ ,, B @ k' ⊢[ lC ] c2 : M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; Δ ⊢[ lC ] t : tySum k k' A B @ lmax k k' ] ->
  RT Δ A k -> RT Δ B k' -> RT (Δ ,, tySum k k' A B @ lmax k k') M k'' ->
  Rt (Δ ,, A @ k) c1 (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) k'' ->
  Rt (Δ ,, B @ k') c2 (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) k'' ->
  Rt Δ t (tySum k k' A B) (lmax k k') ->
  Rt Δ (tmCase k k' k'' A B M c1 c2 t) (M[lsingle t]) k''.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' Hw'' HA HB HM Hc1 Hc2 Ht IHA IHB IHM IHc1 IHc2 IHt Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw', Hw''.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : leqv k'' ?x |- _ => rename x into k1'' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' HMM].
  destruct (scr_tm Hc1 ltac:(eassumption) ltac:(eassumption)) as [Hc1' _].
  destruct (scr_tm Hc2 ltac:(eassumption) ltac:(eassumption)) as [Hc2' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Q'' : lequiv L' k'' k1'') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_ty HB HCD) as HBD.
  assert (HSD : [ G' ; Δ ⊢[ lD ] tySum k k' A B @ lmax k k' ])
    by (apply wft_sum; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBD]).
  assert (HSS : [ G' ; Δ ⊢[ lD ] tySum k k' A B ≅ tySum k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sum; [discriminate | exact Qg | exact Qg' | exact HAA | exact HBB]).
  destruct (case_facts_D Qg Qg' HAD HAA (lift_ty HA' HCD) HBD HBB (lift_ty HB' HCD) (lift_ty HM HCD) HMM (lift_ty HM' HCD))
    as (_ & CAf & CBf & EC1 & EC2).
  pose proof (ctxconv_eqty (eqctx_sym_D CAf) (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ EC1)) as HC1.
  pose proof (ctxconv_eqty (eqctx_sym_D CBf) (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ EC2)) as HC2.
  refine (rec_t_case HΔL HΔ HkL HkR Hw Hw' Hw'' _ _ _ _ _ _ HTL HTR HA HA' _ HB HB' _ HM HM' _ Hc1 Hc1' _
            Hc2 Hc2' _ Ht Ht' _ _ _ _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHM HM _ _ _ _ (ceq_ext HΔ HSD HSS Qm) (lequiv_refl _ _ Hw'') Q'' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHc1 Hc1 _ _ _ _ _ _ (ceq_ext HΔ HAD HAA Q) (lequiv_refl _ _ Hw'') Q'' (eq_self_l HC1) HC1
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHc2 Hc2 _ _ _ _ _ _ (ceq_ext HΔ HBD HBB Q') (lequiv_refl _ _ Hw'') Q'' (eq_self_l HC2) HC2
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hwm) Qm (eq_self_l HSS) HSS
             ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_sup {Δ k k' A B a f} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G' ; Δ ⊢[ lC ] f : tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ a A k ->
  Rt Δ f (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) (lmax k' (lmax k k')) ->
  Rt Δ (tmSup k k' A B a f) (tyW k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Ha Hf IHA IHB IHa IHf Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  match goal with H : tm_leq a ?x |- _ => rename x into a' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' Haa].
  destruct (scr_tm Hf ltac:(eassumption) ltac:(eassumption)) as [Hf' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qf : lequiv L' (lmax k' (lmax k k')) (lmax k1' (lmax k1 k1'))) by (repeat apply lequiv_max; assumption).
  assert (Hwf : lwf L' (lmax k' (lmax k k'))) by (cbn; auto).
  pose proof (@W_sup_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qg Qg' (lift_ty HA HCD) HAA
                (lift_ty HB HCD) HBB Haa (lift_tm Ha HCD) (lift_tm Ha' HCD)) as X.
  refine (rec_t_sup HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Ha Ha' _ Hf Hf' _ _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHf Hf _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hwf) Qf (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_elimW {Δ k k' k'' A B M c t} : lwf (gL G') k -> lwf (gL G') k' -> lwf (gL G') k'' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ,, tyW k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] wfty k k' A B @ lmax k' (lmax k k') ] ->
  [ G' ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ⊢[ lC ] wihty k k' k'' A B M @ lmax k' k'' ] ->
  [ G' ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
      ⊢[ lC ] c : wstepty k k' A B M @ k'' ] ->
  [ G' ; Δ ⊢[ lC ] t : tyW k k' A B @ lmax k k' ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> RT (Δ ,, tyW k k' A B @ lmax k k') M k'' ->
  Rt (Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
    c (wstepty k k' A B M) k'' ->
  Rt Δ t (tyW k k' A B) (lmax k k') ->
  Rt Δ (tmElimW k k' k'' A B M c t) (M[lsingle t]) k''.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' Hw'' HA HB HM HF HI Hc Ht IHA IHB IHM IHc IHt Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw', Hw''.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : leqv k'' ?x |- _ => rename x into k1'' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  match goal with H : ty_leq M ?x |- _ => rename x into M' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' HMM].
  destruct (scr_tm Hc ltac:(eassumption) ltac:(eassumption)) as [Hc' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Q'' : lequiv L' k'' k1'') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qg'' : lequiv (gL G') k'' k1'') by (rewrite EL; exact Q'').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_ty HB HCD) as HBD.
  assert (HWD : [ G' ; Δ ⊢[ lD ] tyW k k' A B @ lmax k k' ])
    by (apply wft_W; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBD]).
  assert (HWW : [ G' ; Δ ⊢[ lD ] tyW k k' A B ≅ tyW k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_W; [discriminate | exact Qg | exact Qg' | exact HAD | exact HAA | exact HBB]).
  destruct (@W_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ _ _ Qg Qg' Qg''
              HAA HAD (lift_ty HA' HCD) HBB HBD (lift_ty HB' HCD) HMM (lift_ty HM HCD) (lift_ty HM' HCD)
              (lift_ty HF HCD) (lift_ty HI HCD)) as (_ & _ & CS1L & ES1).
  destruct (eqc_ext_inv CS1L) as (CS1a & _ & EI1 & QI1). destruct (eqc_ext_inv CS1a) as (_ & _ & EF1 & QF1).
  assert (CS1 : [ G' ⊢[ lD ] Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
                  ≅ ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1') ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'' ])
    by (apply eqc_ext; [apply eqc_ext; [exact (ceq_ext HΔ HAD HAA Q) | exact (lift_ty HF HCD) | exact EF1 | exact QF1]
                       | exact (lift_ty HI HCD) | exact EI1 | exact QI1]).
  refine (rec_t_elimW HΔL HΔ HkL HkR Hw Hw' Hw'' _ _ _ _ _ _ HTL HTR HA HA' _ HB HB' _ HM HM' _ HF HI Hc Hc' _
            Ht Ht' _ _ _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ HAD HAA Q) (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHM HM _ _ _ _ (ceq_ext HΔ HWD HWW Qm) (lequiv_refl _ _ Hw'') Q'' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHc Hc _ _ _ _ _ _ CS1 (lequiv_refl _ _ Hw'') Q'' (eq_self_l ES1) ES1 ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hwm) Qm (eq_self_l HWW) HWW ltac:(eassumption) ltac:(eassumption)).
Qed.

(** Length-indexed tuples and finite indices, with their codes (M14b). *)
Lemma RT_vec {Δ k A n} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] ->
  RT Δ A k -> Rt Δ n tyNat lzero -> RT Δ (tyVec k A n) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Hn IHA IHn Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' _].
  destruct (scr_tm Hn ltac:(eassumption) ltac:(eassumption)) as [Hn' _].
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  refine (rec_T_vec HΔL HΔ HkL HkR Hw _ _ HA HA' _ Hn Hn' _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) (lq Hw _ _) _ _); eassumption.
  - refine (IHn Hn _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN _ _); eassumption.
Qed.

Lemma Rt_codevec {Δ k s n} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ n tyNat lzero -> Rt Δ (tmVec k s n) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hs Hn IHs IHn Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' _].
  destruct (scr_tm Hn ltac:(eassumption) ltac:(eassumption)) as [Hn' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  refine (rec_t_codevec HΔL HΔ HkL HkR Hw _ _ HTL HTR Hs Hs' _ Hn Hn' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - refine (IHn Hn _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN _ _); eassumption.
Qed.

Lemma RT_fin {Δ n} : [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> Rt Δ n tyNat lzero -> RT Δ (tyFin n) lzero.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hn IHn Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_tm Hn E W) as [Hn' _].
  refine (rec_T_fin HΔL HΔ HkL HkR Hn Hn' E _).
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  exact (IHn Hn _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN E W).
Qed.

Lemma Rt_codefin {Δ n} : [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> Rt Δ n tyNat lzero ->
  Rt Δ (tmFin n) (tyU lzero) (lsuc lzero).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hn IHn Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  destruct (scr_tm Hn E W) as [Hn' _].
  refine (rec_t_codefin HΔL HΔ HkL HkR HTL HTR Hn Hn' E _).
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  exact (IHn Hn _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN E W).
Qed.

(** Finitary well-founded trees (M15b step 0): each branch in one lemma,
    its calls through [RTcall]/[Rtcall] and its payloads through [GS_br]. *)
Lemma RT_wf {Δ k A N} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] ->
  RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> RT Δ (tyWf k A N) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtr VΓ.
  intros Hw HA HN IHA IHN Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA)
    as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X2 & X2r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyWf k1 A' N' @ k1 ])
    by (apply wft_wf; [discriminate | rewrite EL; exact Hw1 | exact HA'R1 | exact HN'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tyWf k1 A' N' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Q]).
  refine (rec_T_br 47 (k :: nil) (k1 :: nil) (GCtx Δ :: GTy A :: GTm N :: nil) (GCtx ΔR :: GTy A' :: GTm N' :: nil)
            (recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: nil)
            (recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR Q Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 47 (k :: nil) eq_refl Hσ _) (GS_br EP EM 47 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_wf_inst; inst_side 47.
  - apply redT_wf_inst; inst_side 47.
Qed.

Lemma Rt_codewf {Δ k s n} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] n : tyNat @ lzero ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) n tyNat lzero -> Rt Δ (tmWf k s n) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hs Hn IHs IHn Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : tm_leq s ?x |- _ => rename x into s', H into Es end.
  match goal with H : tm_leq n ?x |- _ => rename x into n', H into En end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  destruct (Rtcall (k := lsuc k) (k1 := lsuc k1) HΔL HΔ Hw Hw1 (leqv_lsuc _ _ Ek) (HUU _ _ _ HΔL Q) Hs Es ltac:(assumption) IHs)
    as (Hs' & Hss & Hs'R & Hs'R1 & X1 & X1r).
  assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
  assert (CE : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ≅ ΔR ,, tyEl k s' @ k ])
    by (apply ceq_ext; [exact HΔ | exact HEl | apply eqty_El; [discriminate | rewrite EL; apply lequiv_refl, Hw | exact Hss]
                       | apply lequiv_refl, Hw]).
  assert (CE1 : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ≅ ΔR ,, tyEl k1 s' @ k1 ])
    by (apply ceq_ext; [exact HΔ | exact HEl | apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss] | exact Q]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CE) as HΔE.
  assert (HNat : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔE]).
  destruct (Rtcall (k := lzero) (k1 := lzero) (T' := tyNat) HΔE CE1 I I (leqv_refl _) HNat Hn En ltac:(assumption) IHn)
    as (Hn' & Hnn & _ & Hn'R1 & X2 & X2r).
  pose proof (ctxconv_tm CE (i := lC) eq_refl Hn') as Hn'R.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmWf k1 s' n' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_wf; [discriminate | rewrite EL; exact Hw1 | exact Hs'R1 | exact Hn'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmWf k1 s' n' : tyU k @ lsuc k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Q] | exact (HUU _ _ _ HΔL Q)]).
  refine (rec_t_br 48 (k :: nil) (k1 :: nil) (GCtx Δ :: GTm s :: GTm n :: nil) (GCtx ΔR :: GTm s' :: GTm n' :: nil)
            (rectL (lsuc k) Δ (tyU k) s :: rectL lzero (Δ ,, tyEl k s @ k) tyNat n :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s' :: rectR lzero (ΔR ,, tyEl k1 s' @ k1) tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (HUU _ _ _ HΔR Q) Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 48 (k :: nil) eq_refl Hσ _) (GS_br EP EM 48 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codewf_inst; inst_side 48.
  - apply redt_codewf_inst; inst_side 48.
Qed.

Lemma Rt_supf {Δ k A N a cs} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G' ; Δ ⊢[ lC ] cs : tyVec k (tyWf k A N) N[lsingle a] @ k ] ->
  RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> Rt Δ a A k -> Rt Δ cs (tyVec k (tyWf k A N) N[lsingle a]) k ->
  Rt Δ (tmSupf k A N a cs) (tyWf k A N) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw HA HN Ha Hcs IHA IHN IHa IHcs Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : tm_leq a ?x |- _ => rename x into a', H into Ea end.
  match goal with H : tm_leq cs ?x |- _ => rename x into cs', H into Ecs end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  (* the shape, the arity, the label, and their calls *)
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA) as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X2 & X2r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  destruct (Rtcall HΔL HΔ Hw Hw1 Ek HAA Ha Ea ltac:(assumption) IHa) as (Ha' & Haa & Ha'R0 & Ha'R1 & X3 & X3r).
  assert (Ha'R : [ G' ; ΔR ⊢[ lC ] a' : A' @ k ])
    by (eapply wf_conv; [exact Ha'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HAA))]).
  (* the children, at their vector type *)
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_tm HN HCD) as HND.
  pose proof (@Wf_cs_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ Qg HAD HAA HND HNN Haa
                (lift_tm Ha HCD) (lift_tm Ha' HCD)) as HCC.
  pose proof (@Wf_cs_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ Qk HAD HAA HND HNN Haa
                (lift_tm Ha HCD) (lift_tm Ha' HCD)) as HCC0.
  destruct (Rtcall (k1 := k1) HΔL HΔ Hw Hw1 Ek HCC Hcs Ecs ltac:(assumption) IHcs) as (Hcs' & Hcss & Hcs'R0 & Hcs'R1 & X4 & X4r).
  assert (Hcs'R : [ G' ; ΔR ⊢[ lC ] cs' : tyVec k (tyWf k A' N') N'[lsingle a'] @ k ])
    by (eapply wf_conv; [exact Hcs'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HCC0))]).
  (* the codes *)
  assert (HWW : [ G' ; Δ ⊢[ lD ] tyWf k A N ≅ tyWf k1 A' N' @ k ])
    by (apply eqty_wf; [discriminate | exact Qg | exact HAD | exact HAA | exact HNN]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSupf k1 A' N' a' cs' : tyWf k1 A' N' @ k1 ])
    by (apply wf_supf; [discriminate | rewrite EL; exact Hw1 | exact HA'R1 | exact HN'R1 | exact Ha'R1 | exact Hcs'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmSupf k1 A' N' a' cs' : tyWf k A N @ k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                        | exact HWW]).
  refine (rec_t_br 49 (k :: nil) (k1 :: nil) (GCtx Δ :: GTy A :: GTm N :: GTm a :: GTm cs :: nil)
            (GCtx ΔR :: GTy A' :: GTm N' :: GTm a' :: GTm cs' :: nil)
            (recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: rectL k Δ A a
               :: rectL k Δ (tyVec k (tyWf k A N) N[lsingle a]) cs :: nil)
            (recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N' :: rectR k1 ΔR A' a'
               :: rectR k1 ΔR (tyVec k1 (tyWf k1 A' N') N'[lsingle a']) cs' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HWW) Hc HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 49 (k :: nil) eq_refl Hσ _) (GS_br EP EM 49 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_supf_inst; inst_side 49.
  - apply redt_supf_inst; inst_side 49.
Qed.

Lemma Rt_elimWf {Δ k k' A N M c t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] ->
  [ G' ; Δ ,, tyWf k A N @ k ⊢[ lC ] M @ k' ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] wfcsty k A N @ k ] ->
  [ G' ; Δ ,, A @ k ,, wfcsty k A N @ k ⊢[ lC ] wfihty k k' A N M @ lmax lzero k' ] ->
  [ G' ; Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k' ⊢[ lC ] c : wfstepty k A N M @ k' ] ->
  [ G' ; Δ ⊢[ lC ] t : tyWf k A N @ k ] ->
  RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> RT (Δ ,, tyWf k A N @ k) M k' ->
  Rt (Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k') c (wfstepty k A N M) k' ->
  Rt Δ t (tyWf k A N) k ->
  Rt Δ (tmElimWf k k' A N M c t) (M[lsingle t]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HN HM HCs HI Hc Ht IHA IHN IHM IHc IHt Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv k' ?x |- _ => rename x into k1', H into Ek' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : ty_leq M ?x |- _ => rename x into M', H into EM1 end.
  match goal with H : tm_leq c ?x |- _ => rename x into c', H into Ec end.
  match goal with H : tm_leq t ?x |- _ => rename x into t', H into Et end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' k1' |- _ => rename H into Hw1' end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  (* the shape, the arity and their calls *)
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA) as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X2 & X2r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_ty HA' HCD) as HA'D.
  pose proof (lift_tm HN HCD) as HND. pose proof (lift_tm HN' HCD) as HN'D.
  (* the tree type, and the motive over it *)
  assert (HWD : [ G' ; Δ ⊢[ lD ] tyWf k A N @ k ]) by (apply wft_wf; [discriminate | rewrite EL; exact Hw | exact HAD | exact HND]).
  assert (HWW : [ G' ; Δ ⊢[ lD ] tyWf k A N ≅ tyWf k1 A' N' @ k ])
    by (apply eqty_wf; [discriminate | exact Qg | exact HAD | exact HAA | exact HNN]).
  assert (HWW0 : [ G' ; Δ ⊢[ lD ] tyWf k A N ≅ tyWf k A' N' @ k ])
    by (apply eqty_wf; [discriminate | exact Qk | exact HAD | exact HAA | exact HNN]).
  pose proof (ceq_ext HΔ HWD HWW0 (lequiv_refl _ _ Hw)) as CW. pose proof (ceq_ext HΔ HWD HWW Q) as CW1.
  destruct (RTcall (eqctx_wf_l (i := lD) eq_refl CW) CW1 Hw' Hw1' Ek' HM EM1 ltac:(assumption) IHM)
    as (HM' & HMM & _ & HM'R1 & _ & _ & X3 & X3r).
  pose proof (ctxconv_ty CW (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty HM HCD) as HMD. pose proof (lift_ty HM' HCD) as HM'D.
  (* the step's telescope, at the right levels and at the left ones *)
  destruct (@Wf_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qg Qg'
              HAA HAD HA'D HNN HND HN'D HMM HMD (lift_ty HI HCD)) as (_ & _ & CS1L & ES1).
  destruct (@Wf_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qk Qk'
              HAA HAD HA'D HNN HND HN'D HMM HMD (lift_ty HI HCD)) as (_ & _ & CS0L & ES0).
  destruct (eqc_ext_inv CS1L) as (CS1a & _ & EI1 & QI1). destruct (eqc_ext_inv CS1a) as (_ & _ & EF1 & QF1).
  destruct (eqc_ext_inv CS0L) as (CS0a & _ & EI0 & QI0). destruct (eqc_ext_inv CS0a) as (_ & _ & EF0 & QF0).
  assert (CS1 : [ G' ⊢[ lD ] Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k'
                  ≅ ΔR ,, A' @ k1 ,, wfcsty k1 A' N' @ k1 ,, wfihty k1 k1' A' N' M' @ lmax lzero k1' ])
    by (apply eqc_ext; [apply eqc_ext; [exact CA1 | exact (lift_ty HCs HCD) | exact EF1 | exact QF1]
                       | exact (lift_ty HI HCD) | exact EI1 | exact QI1]).
  assert (CS0 : [ G' ⊢[ lD ] Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k'
                  ≅ ΔR ,, A' @ k ,, wfcsty k A' N' @ k ,, wfihty k k' A' N' M' @ lmax lzero k' ])
    by (apply eqc_ext; [apply eqc_ext; [exact CA | exact (lift_ty HCs HCD) | exact EF0 | exact QF0]
                       | exact (lift_ty HI HCD) | exact EI0 | exact QI0]).
  (* the step and the scrutinee, and their calls *)
  destruct (Rtcall (eqctx_wf_l (i := lD) eq_refl CS1) CS1 Hw' Hw1' Ek' ES1 Hc Ec ltac:(assumption) IHc)
    as (Hc' & Hcc & _ & Hc'R1 & X4 & X4r).
  assert (Hc'R : [ G' ; ΔR ,, A' @ k ,, wfcsty k A' N' @ k ,, wfihty k k' A' N' M' @ lmax lzero k'
                   ⊢[ lC ] c' : wfstepty k A' N' M' @ k' ]).
  { eapply wf_conv; [exact (ctxconv_tm CS0 (i := lC) eq_refl Hc') |].
    exact (ctxconv_eqty CS0 (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ ES0)). }
  destruct (Rtcall HΔL HΔ Hw Hw1 Ek HWW Ht Et ltac:(assumption) IHt) as (Ht' & Htt & Ht'R0 & Ht'R1 & X5 & X5r).
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyWf k A' N' @ k ])
    by (eapply wf_conv; [exact Ht'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HWW0))]).
  (* the codes *)
  assert (Hr1 : [ G' ; Δ ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k' ])
    by exact (eqty_subst_single_D HMM HM'D Htt (lift_tm Ht HCD) (lift_tm Ht' HCD)).
  pose proof (@sc_elimWf_q G' lC HCD _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(discriminate) Qg Qg'
                HA HA' (static_code_ty HCD HA HA' EA) HN HN' (static_code_tm HCD HN HN' EN)
                HM HM' (static_code_ty HCD HM HM' EM1) HI Hc' Ht Ht'
                (static_code_tm HCD Ht Ht' Et)) as HcRL.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmElimWf k1 k1' A' N' M' c' t' : M'[lsingle t'] @ k1' ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact HcRL | apply eqty_sym, Hr1] | apply lequiv_sym, Qg']. }
  refine (rec_t_br 50 (k :: k' :: nil) (k1 :: k1' :: nil)
            (GCtx Δ :: GTy A :: GTm N :: GTy M :: GTm c :: GTm t :: nil)
            (GCtx ΔR :: GTy A' :: GTm N' :: GTy M' :: GTm c' :: GTm t' :: nil)
            (recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: recTL k' (Δ ,, tyWf k A N @ k) M
             :: rectL k' (Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k') (wfstepty k A N M) c
             :: rectL k Δ (tyWf k A N) t :: nil)
            (recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N' :: recTR k1' (ΔR ,, tyWf k1 A' N' @ k1) M'
             :: rectR k1' (ΔR ,, A' @ k1 ,, wfcsty k1 A' N' @ k1 ,, wfihty k1 k1' A' N' M' @ lmax lzero k1')
                  (wfstepty k1 A' N' M') c'
             :: rectR k1 ΔR (tyWf k1 A' N') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Ek' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) Hc0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 50 (k :: k' :: nil) eq_refl Hσ _)
            (GS_br EP EM 50 (k1 :: k1' :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx_Wf; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5].
  - sr_ctx_Wf; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_elimWf_inst; inst_side 50.
  - apply redt_elimWf_inst; inst_side 50.
Qed.

Theorem rec_code :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> i = lC -> G = G' -> RT Γ T l) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> i = lC -> G = G' -> Rt Γ t T l) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof using EL ELM ELP EMl HG0 HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ VΓT VΓbr VΓt.
  apply typing_mut; intros; try exact I;
    (* the rules at M do not type code *)
    match goal with Ei : ?i = lC, EG : ?G = G' |- _ => first [discriminate Ei | subst i G] end;
    repeat match goal with IH : lC = lC -> G' = G' -> _ |- _ => specialize (IH eq_refl eq_refl) end;
    cbn [typeof] in *;
    (* the rules of the computing layers do not type code (M8_DESIGN.md I1) *)
    try match goal with c : compt lC |- _ => destruct c; discriminate end.
  all: first
    [ solve [apply RT_nat | apply RT_U | apply RT_gvar | apply Rt_nat | apply Rt_zero | apply Rt_U | apply Rt_gvar | apply Rt_gdef]
    | solve [eapply Rt_var; eassumption]
    | solve [eapply RT_pi; eassumption] | solve [eapply RT_El; eassumption] | solve [eapply RT_lconv; eassumption]
    | solve [eapply Rt_succ; eassumption] | solve [eapply Rt_pi; eassumption] | solve [eapply Rt_natrec; eassumption]
    | solve [eapply Rt_lam; eassumption] | solve [eapply Rt_app; eassumption]
    | solve [eapply Rt_conv; eassumption] | solve [eapply Rt_lconv; eassumption]
    | solve [apply RT_unit | apply Rt_codeunit | apply Rt_triv]
    | solve [eapply RT_sig; eassumption] | solve [eapply Rt_codesig; eassumption] | solve [eapply Rt_pair; eassumption]
    | solve [eapply Rt_fst; eassumption] | solve [eapply Rt_snd; eassumption]
    | solve [eapply RT_id; eassumption] | solve [eapply Rt_codeid; eassumption]
    | solve [eapply Rt_refl; eassumption] | solve [eapply Rt_J; eassumption]
    (* strict equality (M10c) *)
    | solve [eapply RT_seq; eassumption] | solve [eapply Rt_codeseq; eassumption]
    | solve [eapply Rt_srefl; eassumption] | solve [apply RT_sempty | apply Rt_codesempty]
    | solve [eapply Rt_elimSEmpty; eassumption]
    (* the empty type and binary sums (M12c) *)
    | solve [apply RT_empty | apply Rt_codeempty] | solve [eapply Rt_elimEmpty; eassumption]
    | solve [eapply RT_sum; eassumption] | solve [eapply Rt_codesum; eassumption]
    | solve [eapply Rt_inl; eassumption] | solve [eapply Rt_inr; eassumption]
    | solve [eapply Rt_case; eassumption]
    (* well-founded trees (M13b) *)
    | solve [eapply RT_W; eassumption] | solve [eapply Rt_codeW; eassumption]
    | solve [eapply Rt_sup; eassumption] | solve [eapply Rt_elimW; eassumption]
    (* length-indexed tuples and finite indices (M14b) *)
    | solve [eapply RT_vec; eassumption] | solve [eapply Rt_codevec; eassumption]
    | solve [eapply RT_fin; eassumption] | solve [eapply Rt_codefin; eassumption]
    (* finitary well-founded trees (M15b) *)
    | solve [eapply RT_wf; eassumption] | solve [eapply Rt_codewf; eassumption]
    | solve [eapply Rt_supf; eassumption] | solve [eapply Rt_elimWf; eassumption] ].
Qed.

(** The recursion lemmas, for a code typed at C in the left context. *)
Lemma rec_T {ΔL ΔR kL kR k c c'} : [ G' ; ΔL ⊢[ lC ] c @ k ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> ty_leq c c' -> ty_lwf L' c' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT c)) (motT (wrapMT MTR) kR ΔR (boxT c'))
    (recTL kL ΔL c) (recTR kR ΔR c').
Proof using EL ELM ELP EMl HG0 HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ VΓT VΓbr VΓt. intros Hc. exact (proj1 (proj2 (proj2 rec_code)) _ _ _ _ _ Hc eq_refl eq_refl Hc ΔR kL kR c'). Qed.

Lemma rec_t {ΔL ΔR kL kR k T TL TR c c'} : [ G' ; ΔL ⊢[ lC ] c : T @ k ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> [ G' ; ΔL ⊢[ lD ] T ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] T ≅ TR @ k ] ->
  tm_leq c c' -> tm_lwf L' c' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt c)) (mott (wrapMt MtR) kR ΔR TR (boxt c'))
    (rectL kL ΔL TL c) (rectR kR ΔR TR c').
Proof using EL ELM ELP EMl HG0 HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ VΓT VΓbr VΓt. intros Hc. exact (proj1 (proj2 (proj2 (proj2 rec_code))) _ _ _ _ _ _ Hc eq_refl eq_refl Hc ΔR kL kR TL TR c'). Qed.

End Rec.
