(** * Reflection of neutrals (ch. 7, Reflexivity of Neutral)

    Neutral terms that are generically equal at both related types are
    related.  By induction on the derivation; the universe case builds a
    neutral derivation one stage down, the Π case applies the neutral
    congruence law for application. *)
From DeLaM.LogRel Require Export Weakening.

(** ** The meta-functions' neutral applications at related arguments
    (M5_DESIGN.md G3)

    The laws ([gne_tm_capp], [gne_tm_tapp]) compare the arguments by the
    generic equivalence at P, which the relation only sees through its
    parameters. The class states the applications at parameter-related
    arguments; it holds vacuously at [j = P], and at [j = M] by escape of
    the payload (Payload.v). *)
Class VPNe `{E : GenericEq} `{LP : LRParams} := {
  vpn_capp {G Γ l T ν ν' Δ Δ'} : lr_j = jM -> lwf (gL G) l ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢g T @ l ] -> vp_ctx lr_vp G Δ Δ' ->
    [ G ; Γ ⊢g T⦃gsingle (GCtx Δ)⦄ ≅ T⦃gsingle (GCtx Δ')⦄ @ l ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyCPi l T @ l ] ->
    [ G ; Γ ⊢ capp ν Δ ~ capp ν' Δ' : T⦃gsingle (GCtx Δ)⦄ @ l ] ;
  vpn_tapp {G Γ Δ l l' T ν ν' A A'} : lr_j = jM -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢g T @ l' ] -> vp_ctx lr_vp G Δ Δ -> vp_ty lr_vp G Δ A A' l ->
    [ G ; Γ ⊢g T⦃gsingle (GTy A)⦄ ≅ T⦃gsingle (GTy A')⦄ @ l' ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyTPi Δ l l' T @ l' ] ->
    [ G ; Γ ⊢ tapp ν A ~ tapp ν' A' : T⦃gsingle (GTy A)⦄ @ l' ]
}.

#[export] Instance VPNe_P `{E : GenericEq} : @VPNe E LR_P.
Proof. constructor; intros; discriminate. Qed.

Section Neutral.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Helpers *)

Lemma gne_tm_typed_l {G Γ ν ν' T l} : [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢g ν : T @ l ].
Proof. intros H; exact (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq H))). Qed.
Lemma gne_tm_typed_r {G Γ ν ν' T l} : [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢g ν' : T @ l ].
Proof. intros H; exact (eqtm_wf_r ge_typeof (geq_tm_sound (gne_tm_geq H))). Qed.

(** Convert a neutral equality along [T ⤳* W] (and a level equivalence). *)
Lemma gne_tm_red {G Γ ν ν' T W l l'} :
  [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> lequiv (gL G) l' l ->
  [ G ; Γ ⊢ ν ~ ν' : W @ l' ].
Proof.
  intros Hν HT Hl. eapply gne_tm_lconv; [|exact Hl]. eapply gne_tm_conv; [exact Hν | apply HT].
Qed.

Lemma gne_tmred_refl {G Γ ν ν' T l} : [ G ; Γ ⊢ ν ~ ν' : T @ l ] ->
  [ G ; Γ ⊢g ν ⤳* ν : T @ l ] /\ [ G ; Γ ⊢g ν' ⤳* ν' : T @ l ].
Proof. intros H; split; apply tmred_refl; eauto using gne_tm_typed_l, gne_tm_typed_r. Qed.

(** ** Contextual types *)

Lemma ModRel_neutral {G Γ T T' l R} : ModRel G Γ T T' l R -> forall ν ν',
  [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢ ν ~ ν' : T' @ l ] -> R ν ν'.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros ν ν' Hν Hν'; apply HR;
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as H1;
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as H2;
    destruct (gne_tmred_refl H1) as [R1 _]; destruct (gne_tmred_refl H2) as [_ R2];
    exists ν, ν'; refine (conj R1 (conj R2 (conj (gne_tm_geq H1) (conj (gne_tm_geq H2) (conj _ _)))));
    constructor; assumption.
Qed.

(** ** Reflection *)

Theorem LR_neutral n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> forall ν ν',
  [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢ ν ~ ν' : T' @ l ] -> R ν ν'.
Proof.
  induction 1 as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd IHdom arAd HR
                 | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                     HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                     widxAd IHwidx Hwisym Hwistr wdomAd IHwdom warAd wotAd wchAd wixAd HR];
    intros ν ν' Hν Hν'; first [exact (ModRel_neutral HM _ _ Hν Hν') | apply HR].
  - (* Nat *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HN.
    destruct (gne_tmred_refl HN) as [H1 H2].
    econstructor; [exact H1 | exact H2 | now apply gne_tm_geq | now constructor].
  - (* U *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HU.
    destruct (gne_tmred_refl HU) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HU) _))))).
    1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
    intros la lb Hla Hlb. rewrite LRbelow_spec by exact Hn.
    assert (HUa : [ G ; Γ ⊢ ν ~ ν' : tyU la @ lsuc la ]).
    { eapply gne_tm_lconv; [|apply lequiv_suc, Hla].
      eapply gne_tm_conv; [exact HU|].
      apply eqty_U; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, gne_tm_typed_l, HU
                    | now apply lequiv_sym]. }
    assert (HEl : [ G ; Γ ⊢ tyEl la ν ~ tyEl lb ν' @ l1 ]).
    { eapply gne_ty_lconv; [|apply lequiv_sym, Hla].
      apply gne_ty_El; [eapply lequiv_trans; [exact Hla | now apply lequiv_sym] | exact HUa]. }
    pose proof (eqty_wf_l ge_typeof (geq_ty_sound (gne_ty_geq HEl))) as Hw.
    pose proof (eqty_wf_r ge_typeof (geq_ty_sound (gne_ty_geq HEl))) as Hw'.
    eexists. eapply LRne; [apply tyred_refl, Hw | apply tyred_refl, Hw' | exact HEl | apply releq_refl].
  - (* neutral *)
    destruct (gne_tmred_refl Hν) as [H1 _]. destruct (gne_tmred_refl Hν') as [_ H2].
    exists ν, ν'. refine (conj _ (conj _ (conj _ _))).
    + eapply tmred_conv; [apply ge_typeof | exact H1 | apply HT].
    + eapply tmred_conv; [apply ge_typeof | exact H2 | apply HT'].
    + eapply gne_tm_conv; [exact Hν | apply HT].
    + eapply gne_tm_conv; [exact Hν' | apply HT'].
  - (* Π *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    destruct (gne_tmred_refl HP) as [H1 _]. destruct (gne_tmred_refl HP') as [_ H2].
    exists ν, ν'.
    refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HP) (conj (gne_tm_geq HP') _)))))).
    1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
    intros ρ a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    apply (kw_lequiv ρ) in Hla, Hlb, Hla', Hlb'.
    pose proof (kw_lwf ρ Hw1) as Hw1'.
    (* facts in the weakened context *)
    assert (HAr : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A @ l1 ]) by exact (kw_ty ρ HA).
    assert (HA'r : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A' @ l1 ]) by exact (kw_ty ρ HA').
    assert (HΔA : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢g ]) by exact (kw_ext ρ HA Hw1).
    assert (EA : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A' @ l1 ]) by exact (kw_geq_ty ρ HAA).
    assert (EB : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ ktyl ρ B' @ l2 ])
      by exact (kw_geq_ty_l ρ HA Hw1 HBB).
    assert (HA1w : [ kw_G ρ ; kw_Δ ρ ⊢g A1 @ la ]).
    { eapply lconv_ty; [exact (eqty_wf_r ge_typeof (geq_ty_sound HA1)) | now apply lequiv_sym]. }
    assert (HΔA1 : [ kw_G ρ ; kw_Δ ρ ,, A1 @ la ⊢g ]) by (apply ext_wf_g; eauto using lequiv_wf_l).
    destruct (escape_tm _ _ _ _ _ _ _ _ (domAd ρ) a a' ha) as (Ha & Ha' & Haa).
    (* the two annotations agree *)
    assert (EA1 : [ kw_G ρ ; kw_Δ ρ ⊢ A1 ≈ A1' @ la ]).
    { eapply geq_ty_lconv; [|exact Hla].
      eapply geq_ty_trans; [apply geq_ty_sym, HA1 | eapply geq_ty_trans; [exact EA | exact HA1']]. }
    assert (EB1 : [ kw_G ρ ; kw_Δ ρ ,, A1 @ la ⊢ B1 ≈ B1' @ lb ]).
    { eapply geq_ty_lconv; [|exact Hlb].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, HA1 | now apply lequiv_sym | exact HΔA1 |].
      eapply geq_ty_trans; [apply geq_ty_sym, HB1 | eapply geq_ty_trans; [exact EB |]].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, geq_ty_sym, EA | apply lequiv_refl, Hw1'
                             | exact HΔA | exact HB1']. }
    assert (Hνr : [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ ν ~ ktm ρ ν' : tyPi la lb A1 B1 @ lmax la lb ]).
    { eapply (gne_tm_lconv (l' := lmax l1 l2)); [|now apply lequiv_max].
      pose proof (kw_gne_tm ρ HP) as Y. rewrite kty_tyPi in Y.
      eapply gne_tm_conv; [exact Y|].
      apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym. }
    assert (Haa1 : [ kw_G ρ ; kw_Δ ρ ⊢ a ≈ a' : A1 @ la ]).
    { eapply geq_tm_conv_l; [exact Haa | | exact Hla].
      eapply eqty_lconv; [apply geq_ty_sound, HA1 | exact Hla]. }
    pose proof (gne_tm_app (lequiv_trans _ _ _ _ Hla (lequiv_sym _ _ _ Hla'))
                  (lequiv_trans _ _ _ _ Hlb (lequiv_sym _ _ _ Hlb')) HA1w EA1 EB1 Hνr Haa1) as X.
    assert (X1 : [ kw_G ρ ; kw_Δ ρ ⊢ app (ktm ρ ν) la lb A1 B1 a ~ app (ktm ρ ν') la' lb' A1' B1' a'
                     : (ktyl ρ B)[lsingle a] @ l2 ]).
    { eapply gne_tm_conv; [eapply gne_tm_lconv; [exact X | now apply lequiv_sym]|].
      apply (eqty_single ge_typeof (geq_ty_sound (geq_ty_sym HB1)) Ha). }
    apply (IHcod ρ a a' ha); [exact X1|].
    eapply gne_tm_conv; [exact X1|].
    destruct (escape_ty _ _ _ _ _ _ _ _ (codAd ρ a a' ha)) as (_ & _ & Hc).
    now apply geq_ty_sound.
  - (* CΠ: the neutral application at every world and related contexts *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    destruct (gne_tmred_refl HP) as [H1 _]. destruct (gne_tmred_refl HP') as [_ H2].
    exists ν, ν'.
    refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HP) (conj (gne_tm_geq HP') _)))))).
    1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
    intros ρ Δ Δ' h.
    pose proof (vpl_ctx_trans (vpl_ctx_sym h) h) as h'.
    destruct (escape_ty _ _ _ _ _ _ _ _ (instAd ρ Δ Δ' h)) as (_ & _ & E1).
    destruct (escape_ty _ _ _ _ _ _ _ _ (instAd ρ Δ' Δ' h')) as (_ & _ & E2).
    assert (Einst : [ kw_G ρ ; kw_Δ ρ ⊢g (kbody ρ T1)⦃gsingle (GCtx Δ)⦄ ≅ (kbody ρ T1)⦃gsingle (GCtx Δ')⦄ @ l1 ])
      by (apply geq_ty_sound; eapply geq_ty_trans; [exact E1 | apply geq_ty_sym, E2]).
    assert (Hνr : [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ ν ~ ktm ρ ν' : tyCPi l1 (kbody ρ T1) @ l1 ])
      by (pose proof (kw_gne_tm ρ HP) as Y; rewrite kty_tyCPi in Y; exact Y).
    pose proof (vpn_capp Hj (kw_lwf ρ Hw1) (kw_body_ty_c ρ HT1) h Einst Hνr) as X.
    apply (IHinst ρ Δ Δ' h); [exact X|].
    eapply gne_tm_conv; [exact X | apply geq_ty_sound, E1].
  - (* TΠ *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    destruct (gne_tmred_refl HP) as [H1 _]. destruct (gne_tmred_refl HP') as [_ H2].
    exists ν, ν'.
    refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HP) (conj (gne_tm_geq HP') _)))))).
    1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
    intros ρ A A' h.
    pose proof (vpl_ty_trans (vpl_ty_sym h) h) as h'.
    pose proof (vpl_ctx_gwk (kw_gok ρ) (kw_glob ρ) HΔ) as HΔr.
    destruct (escape_ty _ _ _ _ _ _ _ _ (instAd ρ A A' h)) as (_ & _ & E1).
    destruct (escape_ty _ _ _ _ _ _ _ _ (instAd ρ A' A' h')) as (_ & _ & E2).
    assert (Einst : [ kw_G ρ ; kw_Δ ρ ⊢g (kbody ρ T1)⦃gsingle (GTy A)⦄ ≅ (kbody ρ T1)⦃gsingle (GTy A')⦄ @ l2 ])
      by (apply geq_ty_sound; eapply geq_ty_trans; [exact E1 | apply geq_ty_sym, E2]).
    assert (Hνr : [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ ν ~ ktm ρ ν' : tyTPi Δ1⟦kw_γ ρ⟧ l1 l2 (kbody ρ T1) @ l2 ])
      by (pose proof (kw_gne_tm ρ HP) as Y; rewrite kty_tyTPi in Y; exact Y).
    pose proof (vpn_tapp Hj (kw_lwf ρ Hw1) (kw_lwf ρ Hw2) (kw_body_ty_t ρ HT1)
                  (vpl_ctx_trans HΔr (vpl_ctx_sym HΔr)) h Einst Hνr) as X.
    apply (IHinst ρ A A' h); [exact X|].
    eapply gne_tm_conv; [exact X | apply geq_ty_sound, E1].
  - (* Σ: the neutral projections *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    destruct (gne_tmred_refl HP) as [H1 _]. destruct (gne_tmred_refl HP') as [_ H2].
    exists ν, ν'.
    refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HP) (conj (gne_tm_geq HP') _)))))).
    1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
    intros ρ la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    apply (kw_lequiv ρ) in Hla, Hlb, Hla', Hlb'.
    pose proof (kw_lwf ρ Hw1) as Hw1'.
    assert (HAr : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A @ l1 ]) by exact (kw_ty ρ HA).
    assert (HΔA : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢g ]) by exact (kw_ext ρ HA Hw1).
    assert (EA : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A' @ l1 ]) by exact (kw_geq_ty ρ HAA).
    assert (EB : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ ktyl ρ B' @ l2 ])
      by exact (kw_geq_ty_l ρ HA Hw1 HBB).
    assert (HA1w : [ kw_G ρ ; kw_Δ ρ ⊢g A1 @ la ]).
    { eapply lconv_ty; [exact (eqty_wf_r ge_typeof (geq_ty_sound HA1)) | now apply lequiv_sym]. }
    assert (HΔA1 : [ kw_G ρ ; kw_Δ ρ ,, A1 @ la ⊢g ]) by (apply ext_wf_g; eauto using lequiv_wf_l).
    assert (EA1 : [ kw_G ρ ; kw_Δ ρ ⊢ A1 ≈ A1' @ la ]).
    { eapply geq_ty_lconv; [|exact Hla].
      eapply geq_ty_trans; [apply geq_ty_sym, HA1 | eapply geq_ty_trans; [exact EA | exact HA1']]. }
    assert (EB1 : [ kw_G ρ ; kw_Δ ρ ,, A1 @ la ⊢ B1 ≈ B1' @ lb ]).
    { eapply geq_ty_lconv; [|exact Hlb].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, HA1 | now apply lequiv_sym | exact HΔA1 |].
      eapply geq_ty_trans; [apply geq_ty_sym, HB1 | eapply geq_ty_trans; [exact EB |]].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, geq_ty_sym, EA | apply lequiv_refl, Hw1'
                             | exact HΔA | exact HB1']. }
    assert (Hνr : [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ ν ~ ktm ρ ν' : tySig la lb A1 B1 @ lmax la lb ]).
    { eapply (gne_tm_lconv (l' := lmax l1 l2)); [|now apply lequiv_max].
      pose proof (kw_gne_tm ρ HP) as Y. rewrite kty_tySig in Y.
      eapply gne_tm_conv; [exact Y|].
      apply geq_ty_sound, geq_ty_sig; auto using lequiv_sym. }
    pose proof (lequiv_trans _ _ _ _ Hla (lequiv_sym _ _ _ Hla')) as Qa.
    pose proof (lequiv_trans _ _ _ _ Hlb (lequiv_sym _ _ _ Hlb')) as Qb.
    (* the first projections, at both domains *)
    assert (F1 : [ kw_G ρ ; kw_Δ ρ ⊢ tmFst la lb A1 B1 (ktm ρ ν) ~ tmFst la' lb' A1' B1' (ktm ρ ν')
                     : kty ρ A @ l1 ]).
    { eapply gne_tm_conv; [eapply gne_tm_lconv; [exact (gne_tm_fst Qa Qb HA1w EA1 EB1 Hνr)
                                                | now apply lequiv_sym]|].
      apply geq_ty_sound, geq_ty_sym, HA1. }
    assert (F2 : [ kw_G ρ ; kw_Δ ρ ⊢ tmFst la lb A1 B1 (ktm ρ ν) ~ tmFst la' lb' A1' B1' (ktm ρ ν')
                     : kty ρ A' @ l1 ]) by (eapply gne_tm_conv; [exact F1 | apply geq_ty_sound, EA]).
    pose proof (IHdom ρ _ _ F1 F2) as h. exists h.
    destruct (escape_tm _ _ _ _ _ _ _ _ (domAd ρ) _ _ h) as (Ha & _ & _).
    (* the second projections, at the codomain instances *)
    assert (X1 : [ kw_G ρ ; kw_Δ ρ ⊢ tmSnd la lb A1 B1 (ktm ρ ν) ~ tmSnd la' lb' A1' B1' (ktm ρ ν')
                     : (ktyl ρ B)[lsingle (tmFst la lb A1 B1 (ktm ρ ν))] @ l2 ]).
    { eapply gne_tm_conv; [eapply gne_tm_lconv; [exact (gne_tm_snd Qa Qb HA1w EA1 EB1 Hνr)
                                                | now apply lequiv_sym]|].
      apply (eqty_single ge_typeof (geq_ty_sound (geq_ty_sym HB1)) Ha). }
    apply (IHcod ρ _ _ h); [exact X1|].
    eapply gne_tm_conv; [exact X1|].
    destruct (escape_ty _ _ _ _ _ _ _ _ (codAd ρ _ _ h)) as (_ & _ & Hc).
    now apply geq_ty_sound.
  - (* Unit: typed neutrals are related *)
    assert (EU : [ G ; Γ ⊢g T ≅ tyUnit l1 @ l ]) by apply HT.
    assert (EU' : [ G ; Γ ⊢g T' ≅ tyUnit l2 @ l ]) by apply HT'.
    pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    pose proof (lequiv_trans _ _ _ _ Hl2 Hl') as Hl2'.
    assert (X1 : [ G ; Γ ⊢g ν : tyUnit l1 @ l1 ]).
    { eapply conv_tm; [exact (gne_tm_typed_l Hν) | eapply eqty_lconv; [apply eqty_sym, EU | exact Hl'] | exact Hl']. }
    assert (X2 : [ G ; Γ ⊢g ν' : tyUnit l1 @ l1 ]).
    { apply (unit_conv Hl2).
      eapply conv_tm; [exact (gne_tm_typed_r Hν') | eapply eqty_lconv; [apply eqty_sym, EU' | exact Hl2'] | exact Hl2']. }
    exists ν, ν'. refine (conj (tmred_refl _ _ _ X1) (conj (tmred_refl _ _ _ X2) (conj _ _))).
    + constructor; exact (gne_tm_whne_l Hν).
    + constructor; exact (gne_tm_whne_r Hν').
  - (* sEq: typed neutrals are related *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj _ _))).
    + constructor; exact (gne_tm_whne_l Hν).
    + constructor; exact (gne_tm_whne_r Hν').
  - (* sEmpty: each side a neutral related to itself *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj _ _))).
    + exact (gne_tm_trans HP (gne_tm_sym HP)).
    + exact (gne_tm_trans (gne_tm_sym HP) HP).
  - (* Id: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj (gne_tm_geq HP) _))).
    now apply idnf_ne.
  - (* Empty: each side a neutral related to itself, as at sEmpty *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj _ _))).
    + exact (gne_tm_trans HP (gne_tm_sym HP)).
    + exact (gne_tm_trans (gne_tm_sym HP) HP).
  - (* +: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj (gne_tm_geq HP) _))).
    now apply sumnf_ne.
  - (* W: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    econstructor; [exact H1 | exact H2 | exact (gne_tm_geq HP) | now apply wnf_ne].
  - (* Wf: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    econstructor; [exact H1 | exact H2 | exact (gne_tm_geq HP) | now apply wfnf_ne].
  - (* ∥·∥: each side a neutral related to itself, as at Empty *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    split; [exists ν | exists ν']; split; [exact H1 | | exact H2 |]; apply sqnf_ne.
    + exact (gne_tm_trans HP (gne_tm_sym HP)).
    + exact (gne_tm_trans (gne_tm_sym HP) HP).
  - (* IWf: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    econstructor; [exact H1 | exact H2 | exact (gne_tm_geq HP) | now apply iwfnf_ne].
Qed.

End Neutral.
