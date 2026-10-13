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

(** Propositional truncation (M16b): the step's call is at the motive at
    the squash of the payload, under [∥·∥]. *)
Lemma redT_sq_inst k0 Δ k A : dnftm (bs 51) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A ->
  dnftm (recT k Δ A) ->
  redT l1 l2 rb k0 Δ (tySq k A) =
  Some (((usubst_tm (bs 51) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: nil) σ⦄)[lext (recT k Δ A :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_codesq_inst k0 Δ T k s : dnftm (bs 52) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm s ->
  dnftm (rect (lsuc k) Δ (tyU k) s) ->
  redt l1 l2 rb k0 Δ T (tmSqCode k s) =
  Some (((usubst_tm (bs 52) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTm s :: nil) σ⦄)
          [lext (rect (lsuc k) Δ (tyU k) s :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_sq_inst k0 Δ T k A a : dnftm (bs 53) -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty A -> dnftm a ->
  dnftm (recT k Δ A) -> dnftm (rect k Δ A a) ->
  redt l1 l2 rb k0 Δ T (tmSq k A a) =
  Some (((usubst_tm (bs 53) (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy A :: GTm a :: nil) σ⦄)
          [lext (recT k Δ A :: rect k Δ A a :: nil) e]).
Proof using . intros. rewrite <- branch_inst by first [forall_tac | assumption]. reflexivity. Qed.

Lemma redt_elimSq_inst k0 Δ T k k' A M c t : dnftm (bs 54) -> gdnf σ -> LK dnftm e -> dnfctx Δ ->
  dnfty A -> dnfty M -> dnftm c -> dnftm t ->
  dnftm (recT k Δ A) -> dnftm (recT k' (cext Δ (tySq k A) k) M) ->
  dnftm (rect k' (cext Δ A k) (tySq k' (subst_ty M⟨rlift ↑⟩ (lsingle (tmSq k A⟨↑⟩ (var 0))))) c) ->
  dnftm (rect k Δ (tySq k A) t) ->
  redt l1 l2 rb k0 Δ T (tmElimSq k k' A M c t) =
  Some (((usubst_tm (bs 54) (uext (k :: k' :: nil) φ))
           ⦃gext_s (GCtx Δ :: GTy A :: GTy M :: GTm c :: GTm t :: nil) σ⦄)
          [lext (recT k Δ A :: recT k' (cext Δ (tySq k A) k) M
                 :: rect k' (cext Δ A k) (tySq k' (subst_ty M⟨rlift ↑⟩ (lsingle (tmSq k A⟨↑⟩ (var 0))))) c
                 :: rect k Δ (tySq k A) t :: nil) e]).
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

End Rec.

(** ** Tactics shared by the per-former files

    Defined outside the section so that the files reopening it see
    them: the hypotheses they name are the fields' projections
    ([RecH.He]), found by instance resolution, as are the facts. *)
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
  repeat apply SubRel_cons; [first [exact RecH.He | exact He'r] | ..];
  repeat wkb_rw; inst_cbn; lsh0.

(** The typing reduct's side conditions: normal forms of the payloads and
    of the calls, read off their typings and relations. *)
Ltac inst_side k :=
  first [ exact Nσ | exact Nσ' | exact De | exact De'
        | exact (wf_tm_dnf (RecH.Hbs k ltac:(lia))) | exact (wf_tm_dnf (RecH.Hbs' k ltac:(lia))) | dnf_any ].

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

(** [W]'s scopes (M13b): the shifted [W] under a binder, computed. *)
Ltac W_cbn := cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1]; inst_cbn;
  rewrite ?subst_lshift1_ty, ?subst_lshift1, ?subst_liftshift_ty; lsh0.
(** [elimW]'s step scope (M13b): its telescope kept in notation form. *)
Ltac sr_ctx_W :=
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst mkLocs call_ty call_lv br_calls]; rewrite ?gs_cext;
  rewrite wkc_inst' by reflexivity; rewrite ?lvren_ush_uext' by reflexivity;
  repeat apply SubRel_cons; [first [exact RecH.He | exact He'r] | ..];
  repeat wkb_rw; cbn [gsubst GSubst_ctx GSubst_ty GSubst_tm]; rewrite ?uc_ext, ?gc_ext;
  rewrite ?us_wfty, ?us_wihty, ?us_wstepty, ?gs_wfty, ?gs_wihty, ?gs_wstepty; inst_cbn; lsh0.
(** [elimWf]'s step scope (M15b), likewise. *)
Ltac sr_ctx_Wf :=
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst mkLocs call_ty call_lv br_calls]; rewrite ?gs_cext;
  rewrite wkc_inst' by reflexivity; rewrite ?lvren_ush_uext' by reflexivity;
  repeat apply SubRel_cons; [first [exact RecH.He | exact He'r] | ..];
  repeat wkb_rw; cbn [gsubst GSubst_ctx GSubst_ty GSubst_tm]; rewrite ?uc_ext, ?gc_ext;
  rewrite ?us_wfcsty, ?us_wfihty, ?us_wfstepty, ?gs_wfcsty, ?gs_wfihty, ?gs_wfstepty; inst_cbn; lsh0.

(** [J]'s motive context shifts its carrier and point: the shifts are
    computed before the global substitution reaches them. *)
Ltac J_cbn := try unfold lsingle2; cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1]; inst_cbn;
  rewrite ?subst_lshift1_ty, ?subst_lshift1; lsh0.
Ltac J_res := cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar]; wkb_rw; J_cbn; rewrite ?Nat.add_0_r; reflexivity.

(** The mismatched formers are closed by conversion before [cbn], which
    then runs on the one that survives (as [leq_cases], [LevelEq.v]). *)
Ltac leq_inv := match goal with
  | E : ty_leq _ ?c, W : ty_lwf _ ?c |- _ =>
      is_var c; destruct c; try exact (False_ind _ E); cbn in E, W; try contradiction
  | E : tm_leq _ ?c, W : tm_lwf _ ?c |- _ =>
      is_var c; destruct c; try exact (False_ind _ E); cbn in E, W; try contradiction
  end; repeat match goal with H : _ /\ _ |- _ => destruct H end.

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

Local Notation recTL k Δ c := (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ (boxT c)).
Local Notation recTR k Δ c := (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ (boxT c)).
Local Notation rectL k Δ T c := (elimt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ T (boxt c)).
Local Notation rectR k Δ T c := (elimt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ T (boxt c)).

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

End Rec.

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

Local Notation recTL k Δ c := (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ (boxT c)).
Local Notation recTR k Δ c := (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ (boxT c)).
Local Notation rectL k Δ T c := (elimt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ T (boxt c)).
Local Notation rectR k Δ T c := (elimt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ T (boxt c)).
#[local] Existing Instance LR_M_permRec.

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

End Rec.
