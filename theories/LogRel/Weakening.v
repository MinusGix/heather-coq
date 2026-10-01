(** * Weakening of the logical relation (ch. 7, Weakening)

    A related pair of types stays related in every weakened context, and
    the term relation is preserved.  The Π case needs no induction
    hypothesis: its premises are already Kripke, and the weakened relation
    is the original one at composite weakenings.  The universe case uses
    weakening one stage down. *)
From DeLaM.LogRel Require Export Transitivity.

Section Weakening.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Term relations *)

Section KwRel.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma NatRel_kw : forall t t', NatRel G Γ t t' -> NatRel (kw_G ρ) (kw_Δ ρ) (ktm ρ t) (ktm ρ t').
Proof.
  apply (NatRel_mut G Γ (fun t t' _ => NatRel (kw_G ρ) (kw_Δ ρ) (ktm ρ t) (ktm ρ t'))
                        (fun t t' _ => NatNf (kw_G ρ) (kw_Δ ρ) (ktm ρ t) (ktm ρ t'))).
  - intros t t' w w' Hw Hw' Heq _ IH.
    pose proof (kw_tmred ρ Hw) as Hw1. pose proof (kw_tmred ρ Hw') as Hw1'.
    pose proof (kw_geq_tm ρ Heq) as Heq1. rewrite kty_tyNat in Hw1, Hw1', Heq1.
    econstructor; [exact Hw1 | exact Hw1' | exact Heq1 | exact IH].
  - rewrite ktm_zero; constructor.
  - intros; rewrite !ktm_succ; now constructor.
  - intros ν ν' H; constructor. pose proof (kw_gne_tm ρ H) as X. now rewrite kty_tyNat in X.
Qed.

Lemma NeRel_kw V V' l t t' : NeRel G Γ V V' l t t' ->
  NeRel (kw_G ρ) (kw_Δ ρ) (kty ρ V) (kty ρ V') l (ktm ρ t) (ktm ρ t').
Proof.
  intros (ν & ν' & H1 & H2 & H3 & H4). exists (ktm ρ ν), (ktm ρ ν').
  exact (conj (kw_tmred ρ H1) (conj (kw_tmred ρ H2) (conj (kw_gne_tm ρ H3) (kw_gne_tm ρ H4)))).
Qed.

Lemma whnf_kw t : whnf t -> whnf (ktm ρ t).
Proof. intros; apply whnf_ren, whnf_gwa; assumption. Qed.
Lemma whne_ty_kw V : whne_ty V -> whne_ty (kty ρ V).
Proof. intros; apply whne_ty_ren, whne_ty_gwa; assumption. Qed.

(** The shared type-level data of a binder former, weakened; [F] commutes
    with the weakening as [Π] and [Σ] do. *)
Lemma poly_kw {F T T' l l1 l2 l3 l4 A B A' B'} :
  (forall k k' C D, kty ρ (F k k' C D) = F k k' (kty ρ C) (ktyl ρ D)) ->
  PolyFacts G Γ F T T' l l1 l2 l3 l4 A B A' B' ->
  PolyFacts (kw_G ρ) (kw_Δ ρ) F (kty ρ T) (kty ρ T') l l1 l2 l3 l4
    (kty ρ A) (ktyl ρ B) (kty ρ A') (ktyl ρ B').
Proof.
  intros HF [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
  pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'. rewrite HF in X, X'.
  split.
  - exact (kw_lequiv ρ Hl).
  - exact (kw_lequiv ρ Hl3).
  - exact (kw_lequiv ρ Hl4).
  - exact (kw_lwf ρ Hw1).
  - exact (kw_lwf ρ Hw2).
  - exact X.
  - exact X'.
  - exact (kw_ty ρ HA).
  - exact (kw_ty ρ HA').
  - exact (kw_ty_l ρ HA Hw1 HB).
  - exact (kw_ty_l ρ HA' Hw1 HB').
  - exact (kw_geq_ty ρ HAA).
  - exact (kw_geq_ty_l ρ HA Hw1 HBB).
Qed.

End KwRel.

(** ** Well-founded trees (M13a): weakening re-associates the data

    A weakened child sits at [(ρ ∘ ρ2) ∘ ρ3] where the weakened relation
    reads [ρ ∘ (ρ2 ∘ ρ3)]; the two give equivalent relations, by
    irrelevance at the type-level derivations ([HdA], [HcA]). *)
Lemma WNf_kw {G Γ l1 l2 A B} {domR : DomRel G Γ} {codR : CodRel G Γ domR} {w w'} :
  WNf G Γ l1 l2 A B domR codR w w' -> forall ρ : kwk G Γ,
  (forall ρ2 ρ3, releq (domR (kw_comp (kw_comp ρ ρ2) ρ3)) (domR (kw_comp ρ (kw_comp ρ2 ρ3)))) ->
  (forall ρ2 ρ3 x y h h', releq (codR (kw_comp (kw_comp ρ ρ2) ρ3) x y h)
                                (codR (kw_comp ρ (kw_comp ρ2 ρ3)) x y h')) ->
  WNf (kw_G ρ) (kw_Δ ρ) l1 l2 (kty ρ A) (ktyl ρ B)
    (fun ρ' => domR (kw_comp ρ ρ')) (fun ρ' x x' h => codR (kw_comp ρ ρ') x x' h) (ktm ρ w) (ktm ρ w').
Proof.
  destruct 1 as [G Γ l1 l2 A B domR codR k1 k2 k1' k2' C D C' D' a a' f f' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha Hwf Hf
                | G Γ l1 l2 A B domR codR ν ν' Hν];
    intros ρ HdA HcA.
  - pose proof (lequiv_wf_r _ _ _ Hk1) as W1. pose proof (lequiv_wf_r _ _ _ Hk2) as W2.
    pose proof (eqty_wf_l ge_typeof (geq_ty_sound HC)) as HA.
    rewrite !ktm_sup. apply wnf_sup; [apply (kw_lequiv ρ); assumption .. | | | | | | |].
    + exact (kw_geq_ty ρ HC).
    + exact (kw_geq_ty ρ HC').
    + exact (kw_geq_ty_l ρ HA W1 HD).
    + exact (kw_geq_ty_l ρ HA W1 HD').
    + intros ρ2. cbn beta. rewrite <- !ktm_comp. exact (Ha (kw_comp ρ ρ2)).
    + intros ρ2. rewrite <- !ktm_comp, <- !ktyl_comp, <- !kty_comp. exact (Hwf (kw_comp ρ ρ2)).
    + intros ρ2. cbn beta. rewrite <- !ktm_comp, <- !ktyl_comp, <- !kty_comp.
      intros ha b b' Hbb la lb A1 B1 la' lb' A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
      pose proof (Hf (kw_comp ρ ρ2) ha b b' Hbb la lb A1 B1 la' lb' A1' B1'
                    (kw_lequiv_shrink ρ H1 W2) (kw_lequiv_shrink ρ H2 WL)
                    (kw_lequiv_shrink ρ H3 W2) (kw_lequiv_shrink ρ H4 WL) HA1 HB1 HA1' HB1') as X.
      eapply WRel_dir; [exact X | intros ρ3; apply HdA | intros ρ3 x y h h'; apply HcA].
  - apply wnf_ne. pose proof (kw_gne_tm ρ Hν) as W. rewrite kty_tyW in W. exact W.
Qed.

Lemma WRel_kw {G Γ l1 l2 A B} {domR : DomRel G Γ} {codR : CodRel G Γ domR} (ρ : kwk G Γ) :
  (forall ρ2 ρ3, releq (domR (kw_comp (kw_comp ρ ρ2) ρ3)) (domR (kw_comp ρ (kw_comp ρ2 ρ3)))) ->
  (forall ρ2 ρ3 x y h h', releq (codR (kw_comp (kw_comp ρ ρ2) ρ3) x y h)
                                (codR (kw_comp ρ (kw_comp ρ2 ρ3)) x y h')) ->
  forall t t', WRel G Γ l1 l2 A B domR codR t t' ->
  WRel (kw_G ρ) (kw_Δ ρ) l1 l2 (kty ρ A) (ktyl ρ B)
    (fun ρ' => domR (kw_comp ρ ρ')) (fun ρ' x x' h => codR (kw_comp ρ ρ') x x' h) (ktm ρ t) (ktm ρ t').
Proof.
  intros HdA HcA t t' H. destruct (WRel_inv H) as (w & w' & Hw & Hw' & Heq & Hn).
  pose proof (kw_tmred ρ Hw) as Y. pose proof (kw_tmred ρ Hw') as Y'. pose proof (kw_geq_tm ρ Heq) as Z.
  rewrite kty_tyW in Y, Y', Z.
  econstructor; [exact Y | exact Y' | exact Z | exact (WNf_kw Hn ρ HdA HcA)].
Qed.

(** ** Meta-functions: the domain of [TΠ] at composite worlds *)

Lemma vp_ty_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) {Δ A A' l} :
  vp_ty lr_vp (kw_G ρ') Δ⟦kw_γ ρ⟧⟦kw_γ ρ'⟧ A A' l ->
  vp_ty lr_vp (kw_G (kw_comp ρ ρ')) Δ⟦kw_γ (kw_comp ρ ρ')⟧ A A' l.
Proof. cbn. rewrite gwa_comp_ctx. exact id. Qed.

Lemma wf_gext_ty_inv {G Δ i l} : [ ⊢ gext G (gdTy Δ i l) ] -> [ G ; Δ ⊢[ lD ] ] /\ lwf (gL G) l.
Proof. intros H; inversion H; subst; auto. Qed.

(** The extended global context of a world. *)
Lemma kw_glob_ctx {G Γ} (ρ : kwk G Γ) : [ ⊢ gext (kw_G ρ) gdCtx ].
Proof. apply wfg_ctx, kw_glob. Qed.
Lemma kw_glob_ty {G Γ} (ρ : kwk G Γ) {Δ l} : [ ⊢ gext G (gdTy Δ lD l) ] ->
  [ ⊢ gext (kw_G ρ) (gdTy Δ⟦kw_γ ρ⟧ lD l) ].
Proof.
  intros H. destruct (wf_gext_ty_inv H) as [HΔ Hl].
  apply wfg_ty; [apply kw_glob | exact (gwa_ctx (kw_gok ρ) (kw_glob ρ) HΔ) | right; reflexivity | exact (kw_lwf ρ Hl)].
Qed.

Lemma kw_body_ty_c {G Γ} (ρ : kwk G Γ) {T l} : [ gext G gdCtx ; Γ⟪S⟫ ⊢g T @ l ] ->
  [ gext (kw_G ρ) gdCtx ; (kw_Δ ρ)⟪S⟫ ⊢g kbody ρ T @ l ].
Proof.
  intros H. pose proof (kw_body_ty ρ (D := gdCtx) (T := T) (l := l)) as X. rewrite gdecl_gwa_ctx in X.
  exact (X (kw_glob_ctx ρ) H).
Qed.
Lemma kw_body_ty_t {G Γ} (ρ : kwk G Γ) {Δ l1 T l} : [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢g T @ l ] ->
  [ gext (kw_G ρ) (gdTy Δ⟦kw_γ ρ⟧ lD l1) ; (kw_Δ ρ)⟪S⟫ ⊢g kbody ρ T @ l ].
Proof.
  intros H. pose proof (kw_body_ty ρ (D := gdTy Δ lD l1) (T := T) (l := l)) as X. rewrite gdecl_gwa_ty in X.
  exact (X (kw_glob_ty ρ (ctx_glob _ _ _ (ctx_of_ty H))) H).
Qed.

(** ** The statement *)

Definition Pwk n := forall G Γ T T' l R,
  LR n (LRbelow n) G Γ T T' l R -> forall ρ : kwk G Γ,
  exists R', LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l R' /\
    forall t t', R t t' -> R' (ktm ρ t) (ktm ρ t').

Lemma URel_kw n G Γ (ρ : kwk G Γ) l1 t t' :
  Pwk (lmeasure l1) -> lmeasure l1 < n -> lwf (gL G) l1 ->
  URel (LRbelow n) G Γ l1 t t' -> URel (LRbelow n) (kw_G ρ) (kw_Δ ρ) l1 (ktm ρ t) (ktm ρ t').
Proof.
  intros Hwk Hn Hl1 (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & HK).
  exists (ktm ρ w), (ktm ρ w').
  pose proof (kw_tmred ρ Hw) as Hw1. pose proof (kw_tmred ρ Hw') as Hw1'.
  pose proof (kw_geq_tm ρ Heq) as Heq1. rewrite kty_tyU in Hw1, Hw1', Heq1.
  refine (conj Hw1 (conj Hw1' (conj (whnf_kw ρ _ Hnf) (conj (whnf_kw ρ _ Hnf') (conj Heq1 _))))).
  intros la lb Hla Hlb. apply (kw_lequiv_shrink ρ) in Hla, Hlb; [| exact Hl1 ..].
  destruct (HK la lb Hla Hlb) as [R0 H0].
  rewrite LRbelow_spec in H0 |- * by exact Hn.
  destruct (Hwk _ _ _ _ _ _ H0 ρ) as (R1 & H1 & _).
  rewrite !kty_tyEl in H1. now exists R1.
Qed.

(** ** Weakening *)

Lemma LR_kwk_step n : (forall m, m < n -> Pwk m) -> Pwk n.
Proof.
  (* by induction: the identity type's carrier relation is at [Γ] only (M11a) *)
  intros IHn G Γ T T' l R H.
  induction H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd _ codAd _ HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd _ HR
                | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd _ HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd _ codAd _ HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb
                    HRA IHRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd _ codAd _ HR]; intros ρ.
  - exists (NatRel (kw_G ρ) (kw_Δ ρ)). split.
    + pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
      rewrite kty_tyNat in X, X'.
      eapply LRnat; [exact (kw_lequiv ρ Hl) | exact X | exact X' | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. exact (NatRel_kw ρ _ _ Ht).
  - exists (URel (LRbelow n) (kw_G ρ) (kw_Δ ρ) l1). split.
    + pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
      rewrite kty_tyU in X, X'.
      eapply LRU; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hl2) | exact Hn | exact X | exact X'
                  | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. eapply URel_kw; eauto using lequiv_wf_r; try apply IHn; lia.
  - exists (NeRel (kw_G ρ) (kw_Δ ρ) (kty ρ V) (kty ρ V') l). split.
    + eapply LRne; [exact (kw_tyred ρ HT) | exact (kw_tyred ρ HT') | exact (kw_gne_ty ρ HV)
                   | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. exact (NeRel_kw ρ _ _ _ _ _ Ht).
  - set (domR' := fun ρ' : kwk (kw_G ρ) (kw_Δ ρ) => domR (kw_comp ρ ρ')).
    set (codR' := fun (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' (ha : domR' ρ' a a') =>
                    codR (kw_comp ρ ρ') a a' ha).
    pose proof (poly_kw ρ (kty_tyPi ρ) P) as P'.
    destruct P as [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
    exists (PiRel (kw_G ρ) (kw_Δ ρ) l1 l2 l3 l4 (kty ρ A) (ktyl ρ B) (kty ρ A') (ktyl ρ B')
              domR' codR'). split.
    + eapply (LRpi n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l l1 l2 l3 l4
                (kty ρ A) (ktyl ρ B) (kty ρ A') (ktyl ρ B') domR' codR').
      * exact P'.
      * intros ρ'. subst domR'; cbn beta.
        rewrite <- !kty_comp. exact (domAd (kw_comp ρ ρ')).
      * intros ρ' a a' ha. subst codR'; cbn beta.
        rewrite <- !ktyl_comp. exact (codAd (kw_comp ρ ρ') a a' ha).
      * apply releq_refl.
    + intros t t' Ht. apply HR in Ht.
      destruct Ht as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
      pose proof (kw_tmred ρ Hw) as Y. pose proof (kw_tmred ρ Hw') as Y'.
      pose proof (kw_geq_tm ρ Heq) as Z. pose proof (kw_geq_tm ρ Heq') as Z'.
      rewrite kty_tyPi in Y, Y', Z, Z'.
      exists (ktm ρ w), (ktm ρ w').
      refine (conj Y (conj Y' (conj (whnf_kw ρ _ Hnf) (conj (whnf_kw ρ _ Hnf') (conj Z (conj Z' _)))))).
      intros ρ' a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      subst codR'; cbn beta. rewrite <- !ktm_comp.
      rewrite <- kty_comp in HA1, HA1'. rewrite <- ktyl_comp, <- kty_comp in HB1, HB1'.
      apply (kw_lequiv_shrink ρ) in H1, H3; [| exact Hw1 ..].
      apply (kw_lequiv_shrink ρ) in H2, H4; [| exact Hw2 ..].
      exact (HK (kw_comp ρ ρ') a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1').
  - destruct (ModRel_kwk ρ HM) as (R' & HM' & HR'). exists R'.
    split; [now apply LRmod | exact HR'].
  - (* CΠ: the instances at composite worlds *)
    set (instR' := fun (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) Δ Δ' (h : vp_ctx lr_vp (kw_G ρ') Δ Δ') =>
                     instR (kw_comp ρ ρ') Δ Δ' h).
    pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
    rewrite kty_tyCPi in X, X'.
    exists (CPiRel (kw_G ρ) (kw_Δ ρ) l1 l2 (kbody ρ T1) (kbody ρ T1') instR'). split.
    + eapply (LRcpi n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l l1 l2
                (kbody ρ T1) (kbody ρ T1') instR').
      * exact Hj.
      * exact (kw_lequiv ρ Hl).
      * exact (kw_lequiv ρ Hl2).
      * exact (kw_lwf ρ Hw1).
      * exact X.
      * exact X'.
      * exact (kw_body_ty_c ρ HT1).
      * exact (kw_body_ty_c ρ HT1').
      * pose proof (kw_geq_ty ρ Hgeq) as Y. rewrite !kty_tyCPi in Y. exact Y.
      * intros ρ' Δ Δ' h. subst instR'; cbn beta.
        rewrite <- !kbody_comp. exact (instAd (kw_comp ρ ρ') Δ Δ' h).
      * apply releq_refl.
    + intros t t' Ht. apply HR in Ht.
      destruct Ht as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
      pose proof (kw_tmred ρ Hw) as Y. pose proof (kw_tmred ρ Hw') as Y'.
      pose proof (kw_geq_tm ρ Heq) as Z. pose proof (kw_geq_tm ρ Heq') as Z'.
      rewrite kty_tyCPi in Y, Y', Z, Z'.
      exists (ktm ρ w), (ktm ρ w').
      refine (conj Y (conj Y' (conj (whnf_kw ρ _ Hnf) (conj (whnf_kw ρ _ Hnf') (conj Z (conj Z' _)))))).
      intros ρ' Δ Δ' h. subst instR'; cbn beta. rewrite <- !ktm_comp.
      exact (HK (kw_comp ρ ρ') Δ Δ' h).
  - (* TΠ: likewise, the domain moved along the composite *)
    set (instR' := fun (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) A A'
                     (h : vp_ty lr_vp (kw_G ρ') Δ1⟦kw_γ ρ⟧⟦kw_γ ρ'⟧ A A' l1) =>
                     instR (kw_comp ρ ρ') A A' (vp_ty_comp ρ ρ' h)).
    pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
    rewrite kty_tyTPi in X, X'.
    exists (TPiRel (kw_G ρ) (kw_Δ ρ) Δ1⟦kw_γ ρ⟧ Δ1'⟦kw_γ ρ⟧ l1 l2 l3 l4 (kbody ρ T1) (kbody ρ T1') instR').
    split.
    + eapply (LRtpi n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l Δ1⟦kw_γ ρ⟧ Δ1'⟦kw_γ ρ⟧
                l1 l2 l3 l4 (kbody ρ T1) (kbody ρ T1') instR').
      * exact Hj.
      * exact (kw_lequiv ρ Hl).
      * exact (kw_lequiv ρ Hl3).
      * exact (kw_lequiv ρ Hl4).
      * exact (kw_lwf ρ Hw1).
      * exact (kw_lwf ρ Hw2).
      * exact X.
      * exact X'.
      * exact (vpl_ctx_gwk (kw_gok ρ) (kw_glob ρ) HΔ).
      * exact (kw_body_ty_t ρ HT1).
      * exact (kw_body_ty_t ρ HT1').
      * pose proof (kw_geq_ty ρ Hgeq) as Y. rewrite !kty_tyTPi in Y. exact Y.
      * intros ρ' A A' h. subst instR'; cbn beta.
        rewrite <- !kbody_comp. exact (instAd (kw_comp ρ ρ') A A' (vp_ty_comp ρ ρ' h)).
      * apply releq_refl.
    + intros t t' Ht. apply HR in Ht.
      destruct Ht as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
      pose proof (kw_tmred ρ Hw) as Y. pose proof (kw_tmred ρ Hw') as Y'.
      pose proof (kw_geq_tm ρ Heq) as Z. pose proof (kw_geq_tm ρ Heq') as Z'.
      rewrite kty_tyTPi in Y, Y', Z, Z'.
      exists (ktm ρ w), (ktm ρ w').
      refine (conj Y (conj Y' (conj (whnf_kw ρ _ Hnf) (conj (whnf_kw ρ _ Hnf') (conj Z (conj Z' _)))))).
      intros ρ' A A' h. subst instR'; cbn beta. rewrite <- !ktm_comp.
      exact (HK (kw_comp ρ ρ') A A' (vp_ty_comp ρ ρ' h)).
  - set (domR' := fun ρ' : kwk (kw_G ρ) (kw_Δ ρ) => domR (kw_comp ρ ρ')).
    set (codR' := fun (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' (ha : domR' ρ' a a') =>
                    codR (kw_comp ρ ρ') a a' ha).
    pose proof (poly_kw ρ (kty_tySig ρ) P) as P'.
    destruct P as [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
    exists (SigRel (kw_G ρ) (kw_Δ ρ) l1 l2 l3 l4 (kty ρ A) (ktyl ρ B) (kty ρ A') (ktyl ρ B')
              domR' codR'). split.
    + eapply (LRsig n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l l1 l2 l3 l4
                (kty ρ A) (ktyl ρ B) (kty ρ A') (ktyl ρ B') domR' codR').
      * exact P'.
      * intros ρ'. subst domR'; cbn beta.
        rewrite <- !kty_comp. exact (domAd (kw_comp ρ ρ')).
      * intros ρ' a a' ha. subst codR'; cbn beta.
        rewrite <- !ktyl_comp. exact (codAd (kw_comp ρ ρ') a a' ha).
      * apply releq_refl.
    + intros t t' Ht. apply HR in Ht.
      destruct Ht as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
      pose proof (kw_tmred ρ Hw) as Y. pose proof (kw_tmred ρ Hw') as Y'.
      pose proof (kw_geq_tm ρ Heq) as Z. pose proof (kw_geq_tm ρ Heq') as Z'.
      rewrite kty_tySig in Y, Y', Z, Z'.
      exists (ktm ρ w), (ktm ρ w').
      refine (conj Y (conj Y' (conj (whnf_kw ρ _ Hnf) (conj (whnf_kw ρ _ Hnf') (conj Z (conj Z' _)))))).
      intros ρ' la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      subst domR' codR'; cbn beta. rewrite <- !ktm_comp.
      rewrite <- kty_comp in HA1, HA1'. rewrite <- ktyl_comp, <- kty_comp in HB1, HB1'.
      apply (kw_lequiv_shrink ρ) in H1, H3; [| exact Hw1 ..].
      apply (kw_lequiv_shrink ρ) in H2, H4; [| exact Hw2 ..].
      exact (HK (kw_comp ρ ρ') la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1').
  - exists (UnitRel (kw_G ρ) (kw_Δ ρ) l1). split.
    + pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
      rewrite kty_tyUnit in X, X'.
      eapply LRunit; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hl2) | exact (kw_lwf ρ Hw) | exact X | exact X'
                     | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. destruct Ht as (w & w' & Hr & Hr' & Hn & Hn').
      pose proof (kw_tmred ρ Hr) as Y. pose proof (kw_tmred ρ Hr') as Y'.
      rewrite kty_tyUnit in Y, Y'. exists (ktm ρ w), (ktm ρ w').
      exact (conj Y (conj Y' (conj (whnf_kw ρ _ Hn) (whnf_kw ρ _ Hn')))).
  - (* sEq *)
    exists (SEqRel (kw_G ρ) (kw_Δ ρ) (tySEq s1 (kty ρ SA) (ktm ρ sa) (ktm ρ sb)) s1). split.
    + pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
      rewrite kty_tySEq in X, X'.
      eapply LRseq; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hl2) | exact (kw_lwf ρ Hw) | exact X | exact X'
                    | exact (kw_ty ρ HSA) | exact (kw_geq_ty ρ HSAA) | exact (kw_geq_tm ρ Hsaa)
                    | exact (kw_geq_tm ρ Hsbb) | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. destruct Ht as (w & w' & Hr & Hr' & Hn & Hn').
      pose proof (kw_tmred ρ Hr) as Y. pose proof (kw_tmred ρ Hr') as Y'.
      rewrite kty_tySEq in Y, Y'. exists (ktm ρ w), (ktm ρ w').
      exact (conj Y (conj Y' (conj (whnf_kw ρ _ Hn) (whnf_kw ρ _ Hn')))).
  - (* sEmpty *)
    exists (SEmptyRel (kw_G ρ) (kw_Δ ρ) s1). split.
    + pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
      rewrite kty_tySEmpty in X, X'.
      eapply LRsempty; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hl2) | exact (kw_lwf ρ Hw) | exact X | exact X'
                       | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. destruct Ht as (w & w' & Hr & Hr' & Hn & Hn').
      pose proof (kw_tmred ρ Hr) as Y. pose proof (kw_tmred ρ Hr') as Y'.
      pose proof (kw_gne_tm ρ Hn) as Z. pose proof (kw_gne_tm ρ Hn') as Z'.
      rewrite kty_tySEmpty in Y, Y', Z, Z'. exists (ktm ρ w), (ktm ρ w').
      exact (conj Y (conj Y' (conj Z Z'))).
  - (* Id: weaken the carrier's derivation *)
    destruct (IHRA ρ) as (RA' & HRA' & Hmap).
    destruct (LR_tm_per _ _ _ _ _ _ _ HRA') as [Hs' Ht'].
    exists (IdRel (kw_G ρ) (kw_Δ ρ) s1 (kty ρ IA) (ktm ρ ia) (ktm ρ ib) RA'). split.
    + pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
      rewrite kty_tyId in X, X'.
      eapply LRid; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hl2) | exact (kw_lwf ρ Hw) | exact X | exact X'
                   | exact (kw_ty ρ HIA) | exact (kw_geq_ty ρ HIAA) | exact (kw_geq_tm ρ Hiaa)
                   | exact (kw_geq_tm ρ Hibb) | exact HRA' | exact (Hmap _ _ Hra) | exact (Hmap _ _ Hrb)
                   | exact Hs' | exact Ht' | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. destruct Ht as (w & w' & Hr & Hr' & Heq & Hn).
      pose proof (kw_tmred ρ Hr) as Y. pose proof (kw_tmred ρ Hr') as Y'.
      pose proof (kw_geq_tm ρ Heq) as Z.
      rewrite kty_tyId in Y, Y', Z. exists (ktm ρ w), (ktm ρ w').
      refine (conj Y (conj Y' (conj Z _))).
      destruct Hn as [k k' C C' c c' Hk Hk' HC HC' H1 H2 H3 H4 | ν ν' Hν].
      * rewrite !ktm_refl. apply idnf_refl; auto using kw_lequiv.
        -- exact (kw_geq_ty ρ HC).
        -- exact (kw_geq_ty ρ HC').
      * apply idnf_ne. pose proof (kw_gne_tm ρ Hν) as W. rewrite kty_tyId in W. exact W.
  - (* Empty *)
    exists (EmptyRel (kw_G ρ) (kw_Δ ρ) s1). split.
    + pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
      rewrite kty_tyEmpty in X, X'.
      eapply LRempty; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hl2) | exact (kw_lwf ρ Hw) | exact X | exact X'
                      | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. destruct Ht as (w & w' & Hr & Hr' & Hn).
      pose proof (kw_tmred ρ Hr) as Y. pose proof (kw_tmred ρ Hr') as Y'.
      pose proof (kw_gne_tm ρ Hn) as Z.
      rewrite kty_tyEmpty in Y, Y', Z. exists (ktm ρ w), (ktm ρ w').
      exact (conj Y (conj Y' Z)).
  - (* +: weaken both summands' derivations *)
    destruct (IHRA ρ) as (RA' & HRA' & HmapA).
    destruct (IHRB ρ) as (RB' & HRB' & HmapB).
    destruct (LR_tm_per _ _ _ _ _ _ _ HRA') as [HsA' HtA'].
    destruct (LR_tm_per _ _ _ _ _ _ _ HRB') as [HsB' HtB'].
    exists (SumRel (kw_G ρ) (kw_Δ ρ) u1 u2 (kty ρ UA) (kty ρ UB) RA' RB'). split.
    + pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
      rewrite kty_tySum in X, X'.
      eapply LRsum; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hl3) | exact (kw_lequiv ρ Hl4)
                    | exact (kw_lwf ρ Hw1) | exact (kw_lwf ρ Hw2) | exact X | exact X'
                    | exact (kw_ty ρ HUA) | exact (kw_geq_ty ρ HUAA) | exact (kw_ty ρ HUB)
                    | exact (kw_geq_ty ρ HUBB) | exact HRA' | exact HRB'
                    | exact HsA' | exact HtA' | exact HsB' | exact HtB' | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. destruct Ht as (w & w' & Hr & Hr' & Heq & Hn).
      pose proof (kw_tmred ρ Hr) as Y. pose proof (kw_tmred ρ Hr') as Y'.
      pose proof (kw_geq_tm ρ Heq) as Z.
      rewrite kty_tySum in Y, Y', Z. exists (ktm ρ w), (ktm ρ w').
      refine (conj Y (conj Y' (conj Z _))).
      destruct Hn as [k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha
                     | k1 k2 k1' k2' C D C' D' b b' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Hb | ν ν' Hν].
      * rewrite !ktm_inl.
        apply sumnf_inl; [apply (kw_lequiv ρ); assumption .. | exact (kw_geq_ty ρ HC) | exact (kw_geq_ty ρ HC')
                         | exact (kw_geq_ty ρ HD) | exact (kw_geq_ty ρ HD') | exact (HmapA _ _ Ha)].
      * rewrite !ktm_inr.
        apply sumnf_inr; [apply (kw_lequiv ρ); assumption .. | exact (kw_geq_ty ρ HC) | exact (kw_geq_ty ρ HC')
                         | exact (kw_geq_ty ρ HD) | exact (kw_geq_ty ρ HD') | exact (HmapB _ _ Hb)].
      * apply sumnf_ne. pose proof (kw_gne_tm ρ Hν) as W. rewrite kty_tySum in W. exact W.
  - (* W: the data at composite worlds, as Π's *)
    set (domR' := fun ρ' : kwk (kw_G ρ) (kw_Δ ρ) => domR (kw_comp ρ ρ')).
    set (codR' := fun (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' (ha : domR' ρ' a a') =>
                    codR (kw_comp ρ ρ') a a' ha).
    pose proof (poly_kw ρ (kty_tyW ρ) P) as P'.
    exists (WRel (kw_G ρ) (kw_Δ ρ) l1 l2 (kty ρ A) (ktyl ρ B) domR' codR'). split.
    + eapply (LRw n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l l1 l2 l3 l4
                (kty ρ A) (ktyl ρ B) (kty ρ A') (ktyl ρ B') domR' codR').
      * exact P'.
      * intros ρ'. subst domR'; cbn beta.
        rewrite <- !kty_comp. exact (domAd (kw_comp ρ ρ')).
      * intros ρ' a a' ha. subst codR'; cbn beta.
        rewrite <- !ktyl_comp. exact (codAd (kw_comp ρ ρ') a a' ha).
      * apply releq_refl.
    + intros t t' Ht. apply HR in Ht. subst domR' codR'.
      apply (WRel_kw ρ); [| | exact Ht].
      * intros ρ2 ρ3.
        pose proof (domAd (kw_comp (kw_comp ρ ρ2) ρ3)) as D1.
        pose proof (domAd (kw_comp ρ (kw_comp ρ2 ρ3))) as D2.
        repeat rewrite kty_comp in D1. repeat rewrite kty_comp in D2.
        exact (LR_irrel _ _ _ _ _ _ _ _ _ _ D1 D2).
      * intros ρ2 ρ3 x y h h'.
        pose proof (codAd (kw_comp (kw_comp ρ ρ2) ρ3) x y h) as D1.
        pose proof (codAd (kw_comp ρ (kw_comp ρ2 ρ3)) x y h') as D2.
        repeat rewrite ktyl_comp in D1. repeat rewrite ktyl_comp in D2.
        exact (LR_irrel _ _ _ _ _ _ _ _ _ _ D1 D2).
Qed.

Theorem LR_kwk n : Pwk n.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_kwk_step, IHn.
Qed.

(** Purely local weakening (M1's statement). *)
Corollary LR_wk n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> forall Δ (ρ : wk), ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] ->
  exists R', LR n (LRbelow n) G Δ T⟨ρ⟩ T'⟨ρ⟩ l R' /\ forall t t', R t t' -> R' t⟨ρ⟩ t'⟨ρ⟩.
Proof. intros H Δ ρ Hρ HΔ. exact (LR_kwk n _ _ _ _ _ _ H (kw_loc ρ Hρ HΔ)). Qed.

End Weakening.
