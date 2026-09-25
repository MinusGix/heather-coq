(** * The recursion lemmas on code (M3_DESIGN.md E13)

    The FT case of a recursor, unfolded: related global substitutions
    [σ ≈ σ'] into [G[φ]], related local ones [e ≈ e'] into [Γ[φ]⦃σ⦄],
    and the recursors moved there. This file relates the moved motives'
    instances (from the motives' validity at every [ψ]), the reducts (from
    the branches' validity at [ψ = levels ++ φ], [σ] extended by the
    code's pieces, [e] by the recursive calls), and proves the recursion
    lemmas by induction on the code's C-typing. *)
From DeLaM.Typing Require Export RecPeel.
From DeLaM.Validity Require Export RecObj LetboxS.

(** ** Pointwise equal substitutions *)

Lemma gdecl_gsubst_ext D σ τ : (forall i, σ i = τ i) -> gdecl_gsubst D σ = gdecl_gsubst D τ.
Proof.
  intros H; destruct D; cbn [gdecl_gsubst]; f_equal.
  all: first [ reflexivity | exact (proj1 (proj2 (proj2 gsubst_ext_all)) _ _ _ H)
             | exact (proj1 gsubst_ext_all _ _ _ H) ].
Qed.

Lemma gsub_wf_ext {G' G σ τ} : (forall i, σ i = τ i) -> [ G' ⊢ σ : G ] -> [ G' ⊢ τ : G ].
Proof.
  intros H [Hg Hn Hv]. constructor; [exact Hg | intros i; rewrite <- H; apply Hn |].
  intros n D Hin. rewrite <- H, <- (gdecl_gsubst_ext D σ τ H). exact (Hv _ _ Hin).
Qed.

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

Lemma GRel0_ext {G' G σ σ' τ τ'} : (forall i, σ i = τ i) -> (forall i, σ' i = τ' i) ->
  GRel0 EP EM G' G σ σ' -> GRel0 EP EM G' G τ τ'.
Proof.
  intros H H' R n D Hin. rewrite <- H, <- H', <- (gdecl_gsubst_ext D σ τ H). exact (R _ _ Hin).
Qed.

Lemma GSubRel_ext {G' G σ σ' τ τ'} : (forall i, σ i = τ i) -> (forall i, σ' i = τ' i) ->
  GSubRel G' G σ σ' -> GSubRel G' G τ τ'.
Proof.
  intros H H' [HL Hl Hr R Rl Rr]. constructor; [exact HL | exact (gsub_wf_ext H Hl) | exact (gsub_wf_ext H' Hr)
    | exact (GRel0_ext H H' R) | exact (GRel0_ext H H Rl) | exact (GRel0_ext H' H' Rr)].
Qed.

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
           (He : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e e').

Lemma MotRel_T {kL kR ΔL ΔR a a'} :
  lwf L' kL -> lequiv L' kL kR -> [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  LRtmM lzero G' Θ (tyCTyp ΔL kL) (tyCTyp ΔL kL) a a' ->
  LRtmM lzero G' Θ (tyCTyp ΔR kR) (tyCTyp ΔR kR) a' a' ->
  LRtyM (lvsubst l1 φ) G' Θ
    (motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))])) kL ΔL a)
    (motT (wrapMT ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄[llift (gwk (uwk e'))])) kR ΔR a').
Proof.
  intros HkL Hk HΔL HΔ Ha Ha'.
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as EL; cbn in EL.
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
           (He : SubRelM G' (gcsubst (ucsubst Γ0 φ) σ) Θ e e').

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
  pose proof (gsr_L _ _ _ _ _ _ Hσ) as EL; cbn in EL.
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
