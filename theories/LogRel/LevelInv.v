(** * Level invariance of the relation (M3_DESIGN.md E6')

    The relation does not see level annotations beyond their equivalence:
    if [T1] and [T2] are related, and [T3] is [≡ₗ]-related to [T2] and
    related to itself, then [T1] and [T3] are related, with the same term
    relation; likewise for terms. Weak-head normal forms of [≡ₗ]-related
    syntax are [≡ₗ]-related (LevelRed.v), so the shapes agree; the
    generic laws [g*_leq] relate the normal forms themselves. The proof
    follows transitivity (Transitivity.v), with the second derivation
    replaced by the self-relation of [T3]. *)
From DeLaM.Syntax Require Export LevelRed LevelEqInv.
From DeLaM.LogRel Require Export Transitivity.
From DeLaM.LogRel Require Import IWfAux MAux.

(** ** Kripke weakenings respect [≡ₗ] *)

Lemma ty_leq_gwa (T T' : ty) γ : ty_leq T T' -> ty_leq T⟦γ⟧ T'⟦γ⟧.
Proof. destruct γ; cbn; auto; apply (proj1 leq_gren_all). Qed.
Lemma tm_leq_gwa (t t' : tm) γ : tm_leq t t' -> tm_leq t⟦γ⟧ t'⟦γ⟧.
Proof. destruct γ; cbn; auto; apply (proj1 (proj2 leq_gren_all)). Qed.

Section LevelInv.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma kty_leq {G Γ} (ρ : kwk G Γ) T T' : ty_leq T T' -> ty_leq (kty ρ T) (kty ρ T').
Proof using . intros H; unfold kty; apply (proj1 leq_ren_all), ty_leq_gwa, H. Qed.
Lemma ktm_leq {G Γ} (ρ : kwk G Γ) t t' : tm_leq t t' -> tm_leq (ktm ρ t) (ktm ρ t').
Proof using . intros H; unfold ktm; apply (proj1 (proj2 leq_ren_all)), tm_leq_gwa, H. Qed.
Lemma ktyl_leq {G Γ} (ρ : kwk G Γ) T T' : ty_leq T T' -> ty_leq (ktyl ρ T) (ktyl ρ T').
Proof using . intros H; unfold ktyl; apply (proj1 leq_ren_all), ty_leq_gwa, H. Qed.
Lemma subst_leq_ty (T T' : ty) d : ty_leq T T' -> ty_leq T[d] T'[d].
Proof using . intros H; apply (proj1 leq_subst_all); [apply lsub_leq_refl | exact H]. Qed.
Lemma ktml_leq {G Γ} (ρ : kwk G Γ) t t' : tm_leq t t' -> tm_leq (ktml ρ t) (ktml ρ t').
Proof using . intros H; unfold ktml; apply (proj1 (proj2 leq_ren_all)), tm_leq_gwa, H. Qed.
Lemma subst_leq_tm (t t' : tm) d : tm_leq t t' -> tm_leq t[d] t'[d].
Proof using . intros H; apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl | exact H]. Qed.
Lemma kbody_leq {G Γ} (ρ : kwk G Γ) T T' : ty_leq T T' -> ty_leq (kbody ρ T) (kbody ρ T').
Proof using . intros H; unfold kbody; apply (proj1 leq_ren_all), ty_leq_gwa, H. Qed.
Lemma gsingle_leq_ty (T T' : ty) o : ty_leq T T' -> ty_leq T⦃gsingle o⦄ T'⦃gsingle o⦄.
Proof using . intros H; apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl | exact H]. Qed.

(** ** Normal forms of related syntax *)

Lemma tyred_leq {G Γ T T' W W' l l'} : ty_leq T T' ->
  [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g T' ⤳* W' @ l' ] -> whnf_ty W -> whnf_ty W' -> ty_leq W W'.
Proof using . intros Ex [_ H _] [_ H' _]; exact (reds_ty_whnf_leq _ _ _ _ Ex H H'). Qed.
Lemma tmred_leq {G Γ t t' w w' T T' l l'} : tm_leq t t' ->
  [ G ; Γ ⊢g t ⤳* w : T @ l ] -> [ G ; Γ ⊢g t' ⤳* w' : T' @ l' ] -> whnf w -> whnf w' -> tm_leq w w'.
Proof using . intros Ex [_ H _] [_ H' _]; exact (reds_whnf_leq _ _ _ _ Ex H H'). Qed.

(** The left type of a related pair has a weak-head normal form. *)
Lemma LR_whnf_l {n rec G Γ T T' l R} : LR n rec G Γ T T' l R ->
  exists W, [ G ; Γ ⊢g T ⤳* W @ l ] /\ whnf_ty W.
Proof using EL.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR].
  all: first
    [ solve [eexists; split; [exact HT | first [exact (whnf_ty_ne _ (gne_ty_whne_l HV)) | solve [eauto with whnf]]]]
    | match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end;
      (eexists; split; [eassumption | eauto with whnf]) ].
Qed.

(** ** Generic helpers *)

Lemma gne_ty_refl_r {G Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Γ ⊢ V' ~ V' @ l ].
Proof using EL. intros H; eapply gne_ty_trans; [apply gne_ty_sym, H | exact H]. Qed.
Lemma gne_ty_refl_l {G Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Γ ⊢ V ~ V @ l ].
Proof using EL. intros H; eapply gne_ty_trans; [exact H | apply gne_ty_sym, H]. Qed.
Lemma gne_tm_refl_r {G Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Γ ⊢ t' ~ t' : T @ l ].
Proof using EL. intros H; eapply gne_tm_trans; [apply gne_tm_sym, H | exact H]. Qed.
Lemma gne_tm_refl_l {G Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Γ ⊢ t ~ t : T @ l ].
Proof using EL. intros H; eapply gne_tm_trans; [exact H | apply gne_tm_sym, H]. Qed.
Lemma geq_tm_refl_r {G Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢ t' ≈ t' : T @ l ].
Proof using EL. intros H; eapply geq_tm_trans; [apply geq_tm_sym, H | exact H]. Qed.
Lemma geq_tm_refl_l {G Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢ t ≈ t : T @ l ].
Proof using EL. intros H; eapply geq_tm_trans; [exact H | apply geq_tm_sym, H]. Qed.
Lemma geq_ty_refl_l {G Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Γ ⊢ T ≈ T @ l ].
Proof using EL. intros H; eapply geq_ty_trans; [exact H | apply geq_ty_sym, H]. Qed.

(** Composition with an [≡ₗ]-related right-hand side. *)
Lemma gne_tm_leq_r {G Γ t1 t2 t3 T l} : [ G ; Γ ⊢ t1 ~ t2 : T @ l ] -> [ G ; Γ ⊢ t3 ~ t3 : T @ l ] ->
  tm_leq t2 t3 -> [ G ; Γ ⊢ t1 ~ t3 : T @ l ].
Proof using EL. intros H H3 Et; eapply gne_tm_trans; [exact H | exact (gne_tm_leq (gne_tm_refl_r H) H3 Et)]. Qed.
Lemma geq_tm_leq_r {G Γ t1 t2 t3 T l} : [ G ; Γ ⊢ t1 ≈ t2 : T @ l ] -> [ G ; Γ ⊢ t3 ≈ t3 : T @ l ] ->
  tm_leq t2 t3 -> [ G ; Γ ⊢ t1 ≈ t3 : T @ l ].
Proof using EL. intros H H3 Et; eapply geq_tm_trans; [exact H | exact (geq_tm_leq (geq_tm_refl_r H) H3 Et)]. Qed.
Lemma gne_ty_leq_r {G Γ V1 V2 V3 l} : [ G ; Γ ⊢ V1 ~ V2 @ l ] -> [ G ; Γ ⊢ V3 ~ V3 @ l ] ->
  ty_leq V2 V3 -> [ G ; Γ ⊢ V1 ~ V3 @ l ].
Proof using EL. intros H H3 Et; eapply gne_ty_trans; [exact H | exact (gne_ty_leq (gne_ty_refl_r H) H3 Et)]. Qed.
Lemma geq_ty_leq_r {G Γ T1 T2 T3 l} : [ G ; Γ ⊢ T1 ≈ T2 @ l ] -> [ G ; Γ ⊢ T3 ≈ T3 @ l ] ->
  ty_leq T2 T3 -> [ G ; Γ ⊢ T1 ≈ T3 @ l ].
Proof using EL. intros H H3 Et; eapply geq_ty_trans; [exact H | exact (geq_ty_leq (geq_ty_refl_r H) H3 Et)]. Qed.

(** ** Natural numbers *)

Lemma NatRel_leq G Γ :
  forall t1 t2, NatRel G Γ t1 t2 -> forall t3, NatRel G Γ t3 t3 -> tm_leq t2 t3 -> NatRel G Γ t1 t3.
Proof using EL.
  apply (NatRel_mut G Γ
           (fun t1 t2 _ => forall t3, NatRel G Γ t3 t3 -> tm_leq t2 t3 -> NatRel G Γ t1 t3)
           (fun w1 w2 _ => forall w3, NatNf G Γ w3 w3 -> tm_leq w2 w3 -> NatNf G Γ w1 w3)).
  - intros t1 t2 w1 w2 Hw1 Hw2 Heq Hnf IH t3 H3 Et.
    inversion H3 as [? ? w3 w3' Hw3 Hw3' Heq3 Hnf3]; subst.
    assert (w3' = w3) as ->
      by (eapply tmred_whnf_det; [exact Hw3' | exact Hw3 | exact (NatNf_whnf_r Hnf3) | exact (NatNf_whnf_l Hnf3)]).
    assert (Ew : tm_leq w2 w3)
      by exact (tmred_leq Et Hw2 Hw3 (NatNf_whnf_r Hnf) (NatNf_whnf_l Hnf3)).
    econstructor; [exact Hw1 | exact Hw3 | exact (geq_tm_leq_r Heq Heq3 Ew) | exact (IH _ Hnf3 Ew)].
  - intros w3 H3 Ew; destruct w3; cbn in Ew; try contradiction; constructor.
  - intros t t' Ht IH w3 H3 Ew; destruct w3; cbn in Ew; try contradiction.
    inversion H3 as [| ? ? H33 | ? ? Hn]; subst.
    + constructor; exact (IH _ H33 Ew).
    + apply gne_tm_whne_l in Hn; inversion Hn.
  - intros ν ν' Hν w3 H3 Ew.
    pose proof (whne_leq _ _ Ew (gne_tm_whne_r Hν)) as Hn3.
    inversion H3 as [| | ? ? H33]; subst; try solve [inversion Hn3].
    constructor. exact (gne_tm_leq_r Hν H33 Ew).
Qed.

(** ** Neutrals *)

Lemma NeRel_leq {G Γ V1 V2 V3 V3' l t1 t2 t3} :
  [ G ; Γ ⊢g V3 ≅ V2 @ l ] -> [ G ; Γ ⊢g V3 ≅ V1 @ l ] -> [ G ; Γ ⊢g V3' ≅ V3 @ l ] ->
  NeRel G Γ V1 V2 l t1 t2 -> NeRel G Γ V3 V3' l t3 t3 -> tm_leq t2 t3 -> NeRel G Γ V1 V2 l t1 t3.
Proof using EL.
  intros E32 E31 E33 (ν1 & ν2 & Hν1 & Hν2 & H12 & H12') (ν3 & ν3' & Hν3 & Hν3' & H33 & H33') Et.
  assert (ν3' = ν3) as ->
    by (eapply tmred_whnf_det; [exact Hν3' | exact Hν3 | exact (whnf_ne _ (gne_tm_whne_r H33))
                               | exact (whnf_ne _ (gne_tm_whne_l H33))]).
  assert (Eν : tm_leq ν2 ν3)
    by exact (tmred_leq Et Hν2 Hν3 (whnf_ne _ (gne_tm_whne_r H12)) (whnf_ne _ (gne_tm_whne_l H33))).
  exists ν1, ν3. refine (conj Hν1 (conj _ (conj _ _))).
  - eapply tmred_conv; [apply ge_typeof | exact Hν3 | exact E32].
  - exact (gne_tm_leq_r H12 (gne_tm_conv H33 E31) Eν).
  - exact (gne_tm_leq_r H12' (gne_tm_conv H33 E32) Eν).
Qed.

(** ** Contextual types: a diagonal bridge, composed by transitivity *)

Lemma CTypNf_leq {G Γ Δ k w2 w3} : CTypNf G Γ Δ k w2 w2 -> CTypNf G Γ Δ k w3 w3 -> tm_leq w2 w3 ->
  CTypNf G Γ Δ k w2 w3.
Proof using EL VL.
  intros H2 H3 Ew. inversion H2 as [T2 ? H2' | ν ? Hν]; subst.
  - destruct w3; cbn in Ew; try contradiction.
    inversion H3 as [? ? H3' | ? ? Hn]; subst.
    + constructor; exact (vpl_tyc_leq H2' H3' Ew).
    + apply gne_tm_whne_l in Hn; inversion Hn.
  - pose proof (whne_leq _ _ Ew (gne_tm_whne_r Hν)) as Hn3.
    inversion H3 as [? ? H3' | ? ? H3']; subst; [inversion Hn3|].
    constructor; exact (gne_tm_leq Hν H3' Ew).
Qed.

Lemma CTrmNf_leq {G Γ Δ A k w2 w3} : CTrmNf G Γ Δ A k w2 w2 -> CTrmNf G Γ Δ A k w3 w3 -> tm_leq w2 w3 ->
  CTrmNf G Γ Δ A k w2 w3.
Proof using EL VL.
  intros H2 H3 Ew. inversion H2 as [t2 ? H2' | ν ? Hν]; subst.
  - destruct w3; cbn in Ew; try contradiction.
    inversion H3 as [? ? H3' | ? ? Hn]; subst.
    + constructor; exact (vpl_tmc_leq H2' H3' Ew).
    + apply gne_tm_whne_l in Hn; inversion Hn.
  - pose proof (whne_leq _ _ Ew (gne_tm_whne_r Hν)) as Hn3.
    inversion H3 as [? ? H3' | ? ? H3']; subst; [inversion Hn3|].
    constructor; exact (gne_tm_leq Hν H3' Ew).
Qed.

Ltac mod_agree' :=
  match goal with
  | H1 : tyred ?G ?i ?Γ ?T ?W1 ?l, H2 : tyred ?G ?i ?Γ ?T ?W2 ?l' |- _ =>
      let Heq := fresh "Heq" in
      assert (Heq : W1 = W2) by (eapply tyred_whnf_det; [exact H1 | exact H2 | eauto with whnf | eauto with whnf]);
      clear H2; first [discriminate Heq | injection Heq; intros; subst]
  end.

(** A diagonal [ModRel]: both reducts coincide. *)
Lemma ModRel_diag' {G Γ T T' l R} : ModRel G Γ T T' l R -> T = T' ->
  (exists Δ k, lequiv (gL G) l lzero /\ lwf (gL G) k /\ [ G ; Γ ⊢g T ⤳* tyCTyp Δ k @ l ] /\
     vp_ctx lr_vp G Δ Δ /\ [ G ; Γ ⊢ tyCTyp Δ k ≈ tyCTyp Δ k @ lzero ] /\
     releq R (CTypRel G Γ Δ Δ k k)) \/
  (exists Δ A k, lequiv (gL G) l lzero /\ lwf (gL G) k /\ [ G ; Γ ⊢g T ⤳* tyCTrm Δ A k @ l ] /\
     vp_ctx lr_vp G Δ Δ /\ vp_ty lr_vp G Δ A A k /\ [ G ; Γ ⊢ tyCTrm Δ A k ≈ tyCTrm Δ A k @ lzero ] /\
     releq R (CTrmRel G Γ Δ Δ A A k k)).
Proof using .
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros <-; mod_agree'.
  - left; do 2 eexists; split; [exact Hl | split; [| split; [exact HT |]]];
      [eapply lequiv_wf_l; eassumption | eauto].
  - right; do 3 eexists; split; [exact Hl | split; [| split; [exact HT |]]];
      [eapply lequiv_wf_l; eassumption | eauto].
Qed.

Lemma ModRel_bridge {G Γ T2 T3 l R2 R3} : ModRel G Γ T2 T2 l R2 -> ModRel G Γ T3 T3 l R3 -> ty_leq T2 T3 ->
  ModRel G Γ T2 T3 l R2 /\ (forall t2 t3, R2 t2 t2 -> R3 t3 t3 -> tm_leq t2 t3 -> R2 t2 t3).
Proof using EL VL.
  intros M2 M3 ET.
  destruct (ModRel_diag' M2 eq_refl) as [(Δ & k & Hl & Hwk & HT2 & HΔ & Hgeq & HR)
                                        | (Δ & A & k & Hl & Hwk & HT2 & HΔ & HA & Hgeq & HR)];
    destruct (ModRel_diag' M3 eq_refl) as [(Δ3 & k3 & Hl3 & Hwk3 & HT3 & HΔ3 & Hgeq3 & HR3)
                                          | (Δ3 & A3 & k3 & Hl3 & Hwk3 & HT3 & HΔ3 & HB & Hgeq3 & HR3)];
    pose proof (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) ltac:(eauto with whnf)) as EW; cbn in EW;
    try contradiction.
  - destruct EW as [EΔ Ek].
    pose proof (leqv_lequiv _ _ _ Hwk Hwk3 Ek) as Hkk.
    assert (HΔΔ : vp_ctx lr_vp G Δ Δ3) by exact (vpl_ctx_leq HΔ HΔ3 EΔ).
    assert (HC : [ G ; Γ ⊢ tyCTyp Δ k ≈ tyCTyp Δ3 k3 @ lzero ])
      by (apply geq_ty_leq; [exact Hgeq | exact Hgeq3 | cbn; auto]).
    pose proof (geq_ty_sound HC) as HCd.
    split.
    + eapply (MRctyp _ _ _ _ _ Δ Δ3 k k3); try eassumption.
      intros t t'; rewrite (HR t t'); split.
      * apply CTypRel_conv_r; assumption.
      * apply CTypRel_conv_r; [now apply vpl_ctx_sym | solve [apply lequiv_sym; assumption] | now apply eqty_sym].
    + intros t2 t3 H2 H3 Et. apply HR in H2. apply HR3 in H3. apply HR.
      destruct H2 as (w2 & w2' & Hw2 & Hw2' & E2 & _ & N2 & _).
      destruct H3 as (w3 & w3' & Hw3 & Hw3' & E3 & _ & N3 & _).
      assert (w2' = w2) as -> by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | exact (CTypNf_whnf_r N2)
                                                          | exact (CTypNf_whnf_l N2)]).
      assert (w3' = w3) as -> by (eapply tmred_whnf_det; [exact Hw3' | exact Hw3 | exact (CTypNf_whnf_r N3)
                                                          | exact (CTypNf_whnf_l N3)]).
      assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2 Hw3 (CTypNf_whnf_l N2) (CTypNf_whnf_l N3)).
      pose proof (eqty_sym _ _ _ _ _ _ HCd) as HCd'.
      pose proof (CTypNf_conv (vpl_ctx_sym HΔΔ) (lequiv_sym _ _ _ Hkk) HCd' N3) as N3'.
      pose proof (geq_tm_conv E3 HCd') as E3'.
      pose proof (geq_tm_leq E2 E3' Ew) as E23.
      pose proof (CTypNf_leq N2 N3' Ew) as N23.
      exists w2, w3. refine (conj Hw2 (conj _ (conj E23 (conj E23 (conj N23 N23))))).
      eapply tmred_conv; [apply ge_typeof | exact Hw3 | exact HCd'].
  - destruct EW as (EΔ & EA & Ek).
    pose proof (leqv_lequiv _ _ _ Hwk Hwk3 Ek) as Hkk.
    assert (HΔΔ : vp_ctx lr_vp G Δ Δ3) by exact (vpl_ctx_leq HΔ HΔ3 EΔ).
    (* [A3] at [Δ] and [k] *)
    assert (HB0 : vp_ty lr_vp G Δ A3 A3 k).
    { eapply vpl_ty_lconv; [apply lequiv_sym, Hkk|]. eapply vpl_ty_ctx; [apply vpl_ctx_sym, HΔΔ | exact HB]. }
    assert (HAA : vp_ty lr_vp G Δ A A3 k) by exact (vpl_ty_leq HA HB0 EA).
    assert (HAA' : vp_ty lr_vp G Δ3 A3 A k3).
    { eapply vpl_ty_lconv; [exact Hkk|]. eapply vpl_ty_ctx; [exact HΔΔ | now apply vpl_ty_sym]. }
    assert (HC : [ G ; Γ ⊢ tyCTrm Δ A k ≈ tyCTrm Δ3 A3 k3 @ lzero ])
      by (apply geq_ty_leq; [exact Hgeq | exact Hgeq3 | cbn; auto]).
    pose proof (geq_ty_sound HC) as HCd.
    split.
    + eapply (MRctrm _ _ _ _ _ Δ Δ3 A A3 k k3); try eassumption.
      intros t t'; rewrite (HR t t'); split.
      * apply CTrmRel_conv_r; assumption.
      * apply CTrmRel_conv_r; [now apply vpl_ctx_sym | | solve [apply lequiv_sym; assumption] | now apply eqty_sym].
        exact HAA'.
    + intros t2 t3 H2 H3 Et. apply HR in H2. apply HR3 in H3. apply HR.
      destruct H2 as (w2 & w2' & Hw2 & Hw2' & E2 & _ & N2 & _).
      destruct H3 as (w3 & w3' & Hw3 & Hw3' & E3 & _ & N3 & _).
      assert (w2' = w2) as -> by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | exact (CTrmNf_whnf_r N2)
                                                          | exact (CTrmNf_whnf_l N2)]).
      assert (w3' = w3) as -> by (eapply tmred_whnf_det; [exact Hw3' | exact Hw3 | exact (CTrmNf_whnf_r N3)
                                                          | exact (CTrmNf_whnf_l N3)]).
      assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2 Hw3 (CTrmNf_whnf_l N2) (CTrmNf_whnf_l N3)).
      pose proof (eqty_sym _ _ _ _ _ _ HCd) as HCd'.
      pose proof (CTrmNf_conv (vpl_ctx_sym HΔΔ) HAA' (lequiv_sym _ _ _ Hkk) HCd' N3) as N3'.
      pose proof (geq_tm_conv E3 HCd') as E3'.
      pose proof (geq_tm_leq E2 E3' Ew) as E23.
      pose proof (CTrmNf_leq N2 N3' Ew) as N23.
      exists w2, w3. refine (conj Hw2 (conj _ (conj E23 (conj E23 (conj N23 N23))))).
      eapply tmred_conv; [apply ge_typeof | exact Hw3 | exact HCd'].
Qed.

(** ** The statement *)

(** A pair's right-hand terms are related by the right type's
    self-relation. *)
Lemma LR_cross {n G Γ T1 T3 T4 l R R3 t t'} :
  LR n (LRbelow n) G Γ T1 T3 l R -> LR n (LRbelow n) G Γ T3 T4 l R3 -> R t t' -> R3 t' t'.
Proof using EL VL.
  intros H13 H34 Ht. pose proof (LR_sym _ _ _ _ _ _ _ H13) as H31.
  exact (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ H31 H34 t' t') (LR_tm_refl_l _ _ _ _ _ _ _ t' t H31 Ht)).
Qed.

Definition Pleq n := forall G Γ T1 T2 l R,
  LR n (LRbelow n) G Γ T1 T2 l R -> forall T3 R3,
  LR n (LRbelow n) G Γ T3 T3 l R3 -> ty_leq T2 T3 ->
  LR n (LRbelow n) G Γ T1 T3 l R /\
  (forall t1 t2 t3, R t1 t2 -> R3 t3 t3 -> tm_leq t2 t3 -> R t1 t3).

(** ** The universe *)

Lemma URel_leq n G Γ l1 l3 t1 t2 t3 :
  Pleq (lmeasure l1) -> lmeasure l1 < n -> lequiv (gL G) l3 l1 ->
  URel (LRbelow n) G Γ l1 t1 t2 -> URel (LRbelow n) G Γ l3 t3 t3 -> tm_leq t2 t3 ->
  URel (LRbelow n) G Γ l1 t1 t3.
Proof using EL.
  intros Hinv Hn Hl (w1 & w2 & Hw1 & Hw2 & Hnf1 & Hnf2 & Heq1 & HK1)
    (w3 & w3' & Hw3 & Hw3' & Hnf3 & Hnf3' & Heq3 & HK3) Et.
  assert (w3' = w3) as -> by (eapply tmred_whnf_det; eauto).
  assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2 Hw3 Hnf2 Hnf3).
  assert (Hm : lmeasure l3 = lmeasure l1) by (eapply lequiv_measure; eauto).
  exists w1, w3. refine (conj Hw1 (conj (tmred_U_conv Hw3 Hl) (conj Hnf1 (conj Hnf3 (conj _ _))))).
  - exact (geq_tm_leq_r Heq1 (geq_U_conv (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ Hw1)) Heq3 Hl) Ew).
  - intros la lb Hla Hlb.
    destruct (HK1 la lb Hla Hlb) as [R1 H1].
    destruct (HK3 lb lb) as [R3 H3]; [eapply lequiv_trans; [eassumption | apply lequiv_sym, Hl] ..|].
    rewrite LRbelow_spec in H1 by exact Hn. rewrite LRbelow_spec in H3 by lia.
    unfold LogRel in *. rewrite Hm in H3.
    exists R1. rewrite LRbelow_spec by exact Hn.
    refine (proj1 (Hinv _ _ _ _ _ _ H1 _ _ (LR_lconv _ _ _ _ _ _ _ _ _ H3 (lequiv_sym _ _ _ Hl)) _)).
    cbn; split; [apply leqv_refl | exact Ew].
Qed.

(** ** The identity type (M11a) *)

Lemma IdRel_leq {G Γ s1 s3 IA A3 ia ib a3 b3 RA RA3 t1 t2 t3} :
  lequiv (gL G) s3 s1 -> [ G ; Γ ⊢g tyId s3 A3 a3 b3 ≅ tyId s1 IA ia ib @ s3 ] ->
  [ G ; Γ ⊢ IA ≈ A3 @ s1 ] ->
  (forall x y z, RA x y -> RA3 z z -> tm_leq y z -> RA x z) ->
  (forall x y, RA3 x y -> RA3 y x) -> (forall x y z, RA3 x y -> RA3 y z -> RA3 x z) ->
  IdRel G Γ s1 IA ia ib RA t1 t2 -> IdRel G Γ s3 A3 a3 b3 RA3 t3 t3 -> tm_leq t2 t3 ->
  IdRel G Γ s1 IA ia ib RA t1 t3.
Proof using EL.
  intros Hl31 HV EA Hc Hs3 Ht3 (w1 & w2 & Hr1 & Hr2 & Heq12 & Hn12) (w3 & w3' & Hr3 & Hr3' & Heq33 & Hn33) Et.
  assert (w3' = w3) as ->
    by (eapply tmred_whnf_det; [exact Hr3' | exact Hr3 | exact (IdNf_whnf_r Hn33) | exact (IdNf_whnf_l Hn33)]).
  assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hr2 Hr3 (IdNf_whnf_r Hn12) (IdNf_whnf_l Hn33)).
  pose proof (lequiv_sym _ _ _ Hl31) as Hl13.
  assert (Hr3c : [ G ; Γ ⊢g t3 ⤳* w3 : tyId s1 IA ia ib @ s1 ]).
  { eapply tmred_lconv; [| exact Hl13]. eapply tmred_conv; [apply ge_typeof | exact Hr3 | exact HV]. }
  assert (Heq33c : [ G ; Γ ⊢ w3 ≈ w3 : tyId s1 IA ia ib @ s1 ]).
  { eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq33 | exact HV] | exact Hl13]. }
  exists w1, w3. refine (conj Hr1 (conj Hr3c (conj (geq_tm_leq_r Heq12 Heq33c Ew) _))).
  assert (R3 : forall x y, RA3 x y -> RA3 y y) by (intros x y H; exact (Ht3 _ _ _ (Hs3 _ _ H) H)).
  destruct Hn12 as [k1 k2 C1 C2 c1 c2 Hk1 Hk2 HC1 HC2 H1 H2 H3 H4 | ν1 ν2 Hν12].
  - destruct (tm_leq_refl_inv Ew) as (k3 & C3 & c3 & -> & Ek & EC & Ec).
    inversion Hn33 as [k3' k3'' C3' C3'' c3' c3'' Hk3 _ HC3 _ G1 _ G3 _ | ν3 ν3' Hν3]; subst.
    + apply idnf_refl.
      * exact Hk1.
      * eapply lequiv_trans; [exact Hk3 | exact Hl31].
      * exact HC1.
      * eapply geq_ty_leq_r; [exact HC2 | | exact EC].
        eapply geq_ty_lconv; [exact (geq_ty_refl_r HC3) | exact Hl13].
      * exact H1.
      * exact (Hc _ _ _ H2 (R3 _ _ G1) Ec).
      * exact H3.
      * exact (Hc _ _ _ H4 (R3 _ _ G3) Ec).
    + exfalso. pose proof (gne_tm_whne_l Hν3) as Hw. inversion Hw.
  - inversion Hn33 as [k3 k3' C3 C3' c3 c3' _ _ _ _ _ _ _ _ | ν3 ν3' Hν3]; subst.
    + exfalso. pose proof (gne_tm_whne_r Hν12) as Hw.
      destruct ν2; cbn in Ew; try contradiction. inversion Hw.
    + apply idnf_ne. eapply gne_tm_leq_r; [exact Hν12 | | exact Ew].
      eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν3 | exact HV] | exact Hl13].
Qed.

(** ** Binary sums (M12b) *)

Lemma SumRel_leq {G Γ u1 u2 u5 u6 A1 B1 A3 B3 RA RB RA3 RB3 t1 t2 t3} :
  lequiv (gL G) u5 u1 -> lequiv (gL G) u6 u2 ->
  [ G ; Γ ⊢g tySum u5 u6 A3 B3 ≅ tySum u1 u2 A1 B1 @ lmax u5 u6 ] ->
  (forall x y z, RA x y -> RA3 z z -> tm_leq y z -> RA x z) ->
  (forall x y z, RB x y -> RB3 z z -> tm_leq y z -> RB x z) ->
  (forall x y, RA3 x y -> RA3 y x) -> (forall x y z, RA3 x y -> RA3 y z -> RA3 x z) ->
  (forall x y, RB3 x y -> RB3 y x) -> (forall x y z, RB3 x y -> RB3 y z -> RB3 x z) ->
  SumRel G Γ u1 u2 A1 B1 RA RB t1 t2 -> SumRel G Γ u5 u6 A3 B3 RA3 RB3 t3 t3 -> tm_leq t2 t3 ->
  SumRel G Γ u1 u2 A1 B1 RA RB t1 t3.
Proof using EL.
  intros Hl5 Hl6 HV HcA HcB HsA3 HtA3 HsB3 HtB3 (w1 & w2 & Hr1 & Hr2 & Heq12 & Hn12)
    (w3 & w3' & Hr3 & Hr3' & Heq33 & Hn33) Et.
  assert (w3' = w3) as ->
    by (eapply tmred_whnf_det; [exact Hr3' | exact Hr3 | exact (SumNf_whnf_r Hn33) | exact (SumNf_whnf_l Hn33)]).
  assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hr2 Hr3 (SumNf_whnf_r Hn12) (SumNf_whnf_l Hn33)).
  pose proof (lequiv_sym _ _ _ Hl5) as Hl15. pose proof (lequiv_sym _ _ _ Hl6) as Hl26.
  assert (Hm : lequiv (gL G) (lmax u1 u2) (lmax u5 u6)) by now apply lequiv_max.
  assert (Hr3c : [ G ; Γ ⊢g t3 ⤳* w3 : tySum u1 u2 A1 B1 @ lmax u1 u2 ]).
  { eapply tmred_lconv; [| exact Hm]. eapply tmred_conv; [apply ge_typeof | exact Hr3 | exact HV]. }
  assert (Heq33c : [ G ; Γ ⊢ w3 ≈ w3 : tySum u1 u2 A1 B1 @ lmax u1 u2 ]).
  { eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq33 | exact HV] | exact Hm]. }
  exists w1, w3. refine (conj Hr1 (conj Hr3c (conj (geq_tm_leq_r Heq12 Heq33c Ew) _))).
  assert (RA3r : forall x y, RA3 x y -> RA3 y y) by (intros x y H; exact (HtA3 _ _ _ (HsA3 _ _ H) H)).
  assert (RB3r : forall x y, RB3 x y -> RB3 y y) by (intros x y H; exact (HtB3 _ _ _ (HsB3 _ _ H) H)).
  destruct Hn12 as [k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha
                   | k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha | ν1 ν2 Hν12].
  - destruct (tm_leq_inl_inv Ew) as (j1 & j2 & P & Q & c & -> & Ej1 & Ej2 & EP & EQ & Ec).
    inversion Hn33 as [i1 i2 i1' i2' P1 Q1 P2 Q2 c1 c2 Hi1 Hi2 Hi1' Hi2' HP1 HP2 HQ1 HQ2 Hc | | ν3 ν3' Hν3];
      subst.
    + apply sumnf_inl;
        [ exact Hk1 | exact Hk2
        | eapply lequiv_trans; [eassumption | exact Hl5] | eapply lequiv_trans; [eassumption | exact Hl6]
        | exact HC
        | eapply geq_ty_leq_r; [exact HC' | eapply geq_ty_lconv; [eapply geq_ty_refl_r; eassumption | exact Hl15]
                               | exact EP]
        | exact HD
        | eapply geq_ty_leq_r; [exact HD' | eapply geq_ty_lconv; [eapply geq_ty_refl_r; eassumption | exact Hl26]
                               | exact EQ]
        | eapply HcA; [exact Ha | eapply RA3r; eassumption | exact Ec] ].
    + exfalso. pose proof (gne_tm_whne_l Hν3) as Hw. inversion Hw.
  - destruct (tm_leq_inr_inv Ew) as (j1 & j2 & P & Q & c & -> & Ej1 & Ej2 & EP & EQ & Ec).
    inversion Hn33 as [| i1 i2 i1' i2' P1 Q1 P2 Q2 c1 c2 Hi1 Hi2 Hi1' Hi2' HP1 HP2 HQ1 HQ2 Hc | ν3 ν3' Hν3];
      subst.
    + apply sumnf_inr;
        [ exact Hk1 | exact Hk2
        | eapply lequiv_trans; [eassumption | exact Hl5] | eapply lequiv_trans; [eassumption | exact Hl6]
        | exact HC
        | eapply geq_ty_leq_r; [exact HC' | eapply geq_ty_lconv; [eapply geq_ty_refl_r; eassumption | exact Hl15]
                               | exact EP]
        | exact HD
        | eapply geq_ty_leq_r; [exact HD' | eapply geq_ty_lconv; [eapply geq_ty_refl_r; eassumption | exact Hl26]
                               | exact EQ]
        | eapply HcB; [exact Ha | eapply RB3r; eassumption | exact Ec] ].
    + exfalso. pose proof (gne_tm_whne_l Hν3) as Hw. inversion Hw.
  - inversion Hn33 as [| | ν3 ν3' Hν3]; subst.
    1-2: exfalso; pose proof (gne_tm_whne_r Hν12) as Hw;
      destruct ν2; cbn in Ew; try contradiction; inversion Hw.
    apply sumnf_ne. eapply gne_tm_leq_r; [exact Hν12 | | exact Ew].
    eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν3 | exact HV] | exact Hm].
Qed.

(** [WhRel] along [≤ₗ]. *)
Lemma WhRel_leq {G Γ T l t1 t2 t3} : WhRel G Γ T l t1 t2 -> WhRel G Γ T l t3 t3 -> tm_leq t2 t3 ->
  WhRel G Γ T l t1 t3.
Proof using EL.
  intros (w1 & w2 & H1 & H2 & N1 & N2 & E12) (w3 & w3' & H3 & H3' & N3 & N3' & E33) Et.
  assert (w3' = w3) as -> by (eapply tmred_whnf_det; [exact H3' | exact H3 | exact N3' | exact N3]).
  exists w1, w3. refine (conj H1 (conj H3 (conj N1 (conj N3 _)))).
  exact (geq_tm_leq_r E12 E33 (tmred_leq Et H2 H3 N2 N3)).
Qed.

(** ** Well-founded trees (M13a)

    As [WRel_trans]: the shapes by [Dl] (the domain's level invariance);
    at the children, the middle tree's are taken at the right position,
    which the domain's codomain irrelevance ([Ci]) allows, and the third
    tree's at the right position too, related to itself by [C13]. *)
Lemma WRel_leq :
  forall G Γ l1 l2 A1 B1 (d1 : DomRel G Γ) (c1 : CodRel G Γ d1) t1 t2,
  WRel G Γ l1 l2 A1 B1 d1 c1 t1 t2 ->
  forall l3 l4 A3 B3 (d3 : DomRel G Γ) (c3 : CodRel G Γ d3) t3,
  WRel G Γ l3 l4 A3 B3 d3 c3 t3 t3 -> tm_leq t2 t3 ->
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
  [ G ; Γ ⊢g A1 @ l1 ] -> [ G ; Γ ⊢ A1 ≈ A3 @ l1 ] -> [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B3 @ l2 ] ->
  (forall (ρ : kwk G Γ) x y (h : d1 ρ x y),
      [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle x] ≈ (ktyl ρ B3)[lsingle y] @ l2 ]) ->
  (forall ρ x y z, d1 ρ x y -> d3 ρ z z -> tm_leq y z -> d1 ρ x z) ->
  (forall ρ x y z (h : d1 ρ x y) (h' : d1 ρ x z) u v, c1 ρ x z h' u v -> c1 ρ x y h u v) ->
  (forall ρ x y (h : d1 ρ x y) (h3 : d3 ρ y y) u v, c1 ρ x y h u v -> c3 ρ y y h3 v v) ->
  WRel G Γ l1 l2 A1 B1 d1 c1 t1 t3.
Proof using EL.
  apply (WRel_mut
    (fun G Γ l1 l2 A1 B1 d1 c1 t1 t2 _ =>
      forall l3 l4 A3 B3 (d3 : DomRel G Γ) (c3 : CodRel G Γ d3) t3,
      WRel G Γ l3 l4 A3 B3 d3 c3 t3 t3 -> tm_leq t2 t3 ->
      lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
      [ G ; Γ ⊢g A1 @ l1 ] -> [ G ; Γ ⊢ A1 ≈ A3 @ l1 ] -> [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B3 @ l2 ] ->
      (forall (ρ : kwk G Γ) x y (h : d1 ρ x y),
          [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle x] ≈ (ktyl ρ B3)[lsingle y] @ l2 ]) ->
      (forall ρ x y z, d1 ρ x y -> d3 ρ z z -> tm_leq y z -> d1 ρ x z) ->
      (forall ρ x y z (h : d1 ρ x y) (h' : d1 ρ x z) u v, c1 ρ x z h' u v -> c1 ρ x y h u v) ->
      (forall ρ x y (h : d1 ρ x y) (h3 : d3 ρ y y) u v, c1 ρ x y h u v -> c3 ρ y y h3 v v) ->
      WRel G Γ l1 l2 A1 B1 d1 c1 t1 t3)
    (fun G Γ l1 l2 A1 B1 d1 c1 w1 w2 _ =>
      forall l3 l4 A3 B3 (d3 : DomRel G Γ) (c3 : CodRel G Γ d3) w3,
      WNf G Γ l3 l4 A3 B3 d3 c3 w3 w3 -> tm_leq w2 w3 ->
      lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
      [ G ; Γ ⊢g A1 @ l1 ] -> [ G ; Γ ⊢ A1 ≈ A3 @ l1 ] -> [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B3 @ l2 ] ->
      (forall (ρ : kwk G Γ) x y (h : d1 ρ x y),
          [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle x] ≈ (ktyl ρ B3)[lsingle y] @ l2 ]) ->
      (forall ρ x y z, d1 ρ x y -> d3 ρ z z -> tm_leq y z -> d1 ρ x z) ->
      (forall ρ x y z (h : d1 ρ x y) (h' : d1 ρ x z) u v, c1 ρ x z h' u v -> c1 ρ x y h u v) ->
      (forall ρ x y (h : d1 ρ x y) (h3 : d3 ρ y y) u v, c1 ρ x y h u v -> c3 ρ y y h3 v v) ->
      WNf G Γ l1 l2 A1 B1 d1 c1 w1 w3)).
  - intros G Γ l1 l2 A1 B1 d1 c1 t1 t2 w1 w2 Hw1 Hw2 Heq Hn IH l3 l4 A3 B3 d3 c3 t3 H3 Et Hl3 Hl4
      HA1 HA13 HB13 HC Dl Ci C13.
    destruct (WRel_inv H3) as (w3 & w3' & Hw3 & Hw3' & Heq3 & Hn3).
    assert (w3' = w3) as ->
      by (eapply tmred_whnf_det; [exact Hw3' | exact Hw3 | exact (WNf_whnf_r Hn3) | exact (WNf_whnf_l Hn3)]).
    assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2 Hw3 (WNf_whnf_r Hn) (WNf_whnf_l Hn3)).
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HV : [ G ; Γ ⊢g tyW l3 l4 A3 B3 ≅ tyW l1 l2 A1 B1 @ lmax l3 l4 ]).
    { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_W; auto using lequiv_sym | exact Hm]. }
    econstructor; [exact Hw1 | | |].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw3 | exact HV] | apply lequiv_sym, Hm].
    + eapply geq_tm_leq_r; [exact Heq | | exact Ew].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq3 | exact HV] | apply lequiv_sym, Hm].
    + exact (IH l3 l4 A3 B3 d3 c3 w3 Hn3 Ew Hl3 Hl4 HA1 HA13 HB13 HC Dl Ci C13).
  - intros G Γ l1 l2 A1 B1 d1 c1 k1 k2 k1' k2' C D C' D' a a' f f' Hk1 Hk2 Hk1' Hk2' HC0 HC0' HD HD' Ha Hwf Hf IH
      l3 l4 A3 B3 d3 c3 w3 H3 Ew Hl3 Hl4 HA1 HA13 HB13 HC Dl Ci C13.
    destruct (tm_leq_sup_inv Ew) as (j1 & j2 & E0 & F0 & a3 & f3 & -> & _ & _ & _ & _ & Ea & Ef).
    destruct (WNf_sup_inv H3) as (i1 & i2 & E' & F' & a3' & f3' & Heq3 & Hj1 & Hj2 & _ & _
                                  & HE & _ & HF & _ & Ha3 & Hwf3 & Hf3).
    injection Heq3 as <- <- <- <- <- <-.
    pose proof (lequiv_wf_l _ _ _ Hl3) as W3. pose proof (lequiv_wf_l _ _ _ Hl4) as W4.
    pose proof (lequiv_wf_r _ _ _ Hl3) as W1. pose proof (lequiv_wf_r _ _ _ Hl4) as W2.
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    (* not the [forall ρ] premises: a failing [eauto] under the last one's
       binders cost 16 s *)
    apply wnf_sup; lazymatch goal with
      | |- forall _ : kwk _ _, _ => idtac | _ => eauto using lequiv_trans end.
    + eapply geq_ty_trans; [exact HA13 | eapply geq_ty_lconv; [exact HE | apply lequiv_sym, Hl3]].
    + (* [B3 ≈ F] under [A3], moved under [A1] *)
      eapply geq_ty_trans; [exact HB13|].
      eapply geq_ty_ctxconv; [| exact Hl3 | apply ext_wf_g; [exact HA1 | exact W1] |].
      * eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA13 | exact Hl3].
      * eapply geq_ty_lconv; [exact HF | apply lequiv_sym, Hl4].
    + intros ρ. exact (Dl ρ _ _ _ (Ha ρ) (Ha3 ρ) (ktm_leq ρ _ _ Ea)).
    + (* the children's functions, the third ones' type converted *)
      intros ρ.
      pose proof (W_fty_eq (kw_lequiv ρ (lequiv_sym _ _ _ Hl3)) (kw_lequiv ρ (lequiv_sym _ _ _ Hl4)) (kw_ty ρ HA1)
                    (kw_geq_ty ρ HA13) (kw_geq_ty_l ρ HA1 W1 HB13)
                    (HC ρ _ _ (Dl ρ _ _ _ (Ha ρ) (Ha3 ρ) (ktm_leq ρ _ _ Ea)))) as EP.
      assert (Qm : lequiv (gL (kw_G ρ)) (lmax l4 (lmax l3 l4)) (lmax l2 (lmax l1 l2)))
        by (apply lequiv_max; [|apply lequiv_max]; apply (kw_lequiv ρ); assumption).
      eapply WhRel_leq; [exact (Hwf ρ) | | exact (ktm_leq ρ _ _ Ef)].
      eapply WhRel_conv; [exact (Hwf3 ρ) | eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, EP | exact Qm] |].
      apply lequiv_sym, Qm.
    + intros ρ h13 b b3 Hbb la lb A1x B1x la3 lb3 A1x3 B1x3 H1 H2' H3' H4 HA1x HB1x HA1x3 HB1x3.
      pose proof (Ha ρ) as h12. pose proof (Ha3 ρ) as h33.
      pose proof (Ci ρ _ _ _ h12 h13 b b3 Hbb) as Hbb12.
      pose proof (C13 ρ _ _ h13 h33 b b3 Hbb) as Hb33.
      pose proof (kw_lwf ρ W1) as V1. pose proof (kw_lwf ρ W2) as V2.
      pose proof (kw_lequiv ρ Hl3) as Q3. pose proof (kw_lequiv ρ Hl4) as Q4.
      assert (Qm : lequiv (gL (kw_G ρ)) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
      pose proof (HC ρ _ _ h13) as EC. pose proof (geq_ty_sound EC) as EC'.
      pose proof (eqty_wf_l ge_typeof EC') as HB1a. pose proof (eqty_wf_r ge_typeof EC') as HB3a.
      assert (EW : [ kw_G ρ ; kw_Δ ρ ⊢ tyW l1 l2 (kty ρ A1) (ktyl ρ B1) ≈ tyW l3 l4 (kty ρ A3) (ktyl ρ B3) @ lmax l1 l2 ]).
      { pose proof (kw_geq_ty ρ (geq_ty_W (lequiv_sym _ _ _ Hl3) (lequiv_sym _ _ _ Hl4) HA1 HA13 HB13)) as X.
        now rewrite !kty_tyW in X. }
      assert (HΔ1 : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B1)[lsingle (ktm ρ a)] @ l2 ⊢g ])
        by (apply ext_wf_g; [exact HB1a | exact V2]).
      assert (HΔ3 : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B3)[lsingle (ktm ρ a3)] @ l4 ⊢g ])
        by (apply ext_wf_g; [eapply lconv_ty; [exact HB3a | solve [apply lequiv_sym; assumption]] | exact (kw_lwf ρ W4)]).
      assert (EW1 : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B1)[lsingle (ktm ρ a)] @ l2
                      ⊢ (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ ≈ (tyW l3 l4 (kty ρ A3) (ktyl ρ B3))⟨↑⟩ @ lmax l1 l2 ])
        by exact (geq_ty_wk (wkr_shift1 _ _ _) HΔ1 EW).
      (* the right annotations, moved to the third tree's context *)
      assert (MB : forall X, [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B1)[lsingle (ktm ρ a)] @ l2
                               ⊢ (tyW l1 l2 (kty ρ A1) (ktyl ρ B1))⟨↑⟩ ≈ X @ lmax l1 l2 ] ->
                     [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B3)[lsingle (ktm ρ a3)] @ l4
                               ⊢ (tyW l3 l4 (kty ρ A3) (ktyl ρ B3))⟨↑⟩ ≈ X @ lmax l3 l4 ]).
      { intros X HX. eapply geq_ty_lconv; [|exact Qm].
        eapply geq_ty_ctxconv; [| apply lequiv_sym, Q4 | exact HΔ3 |].
        - exact EC'.
        - eapply geq_ty_trans; [apply geq_ty_sym, EW1 | exact HX]. }
      assert (MA : forall X, [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B1)[lsingle (ktm ρ a)] ≈ X @ l2 ] ->
                     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B3)[lsingle (ktm ρ a3)] ≈ X @ l4 ]).
      { intros X HX. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, EC | exact HX] | exact Q4]. }
      assert (P3 : lequiv (gL G) la3 l4) by exact (lequiv_trans _ _ _ _ H3' (lequiv_sym _ _ _ Hl4)).
      assert (Pm : lequiv (gL G) lb3 (lmax l3 l4)) by exact (lequiv_trans _ _ _ _ H4 (lequiv_sym _ _ _ Hm)).
      (* the third trees' children, at the right annotations on both sides *)
      pose proof (Hf3 ρ h33 b3 b3 Hb33 la3 lb3 A1x3 B1x3 la3 lb3 A1x3 B1x3 P3 Pm P3 Pm
                    (MA _ HA1x3) (MB _ HB1x3) (MA _ HA1x3) (MB _ HB1x3)) as X3.
      refine (IH ρ h12 b b3 Hbb12 la lb A1x B1x la3 lb3 A1x3 B1x3 H1 H2' H3' H4 HA1x HB1x HA1x3 HB1x3
                l3 l4 (kty ρ A3) (ktyl ρ B3) _ _ _ X3 _ Q3 Q4 (kw_ty ρ HA1) (kw_geq_ty ρ HA13)
                (kw_geq_ty_l ρ HA1 W1 HB13) _ _ _ _).
      * cbn; repeat split; auto using ktm_leq, leqv_refl, ty_leq_refl, tm_leq_refl.
      * intros ρ' x y h. rewrite <- !ktyl_comp. exact (HC (kw_comp ρ ρ') x y h).
      * intros ρ' x y z. exact (Dl (kw_comp ρ ρ') x y z).
      * intros ρ' x y z h h'. exact (Ci (kw_comp ρ ρ') x y z h h').
      * intros ρ' x y h h3. exact (C13 (kw_comp ρ ρ') x y h h3).
  - intros G Γ l1 l2 A1 B1 d1 c1 ν ν' Hν l3 l4 A3 B3 d3 c3 w3 H3 Ew Hl3 Hl4 HA1 HA13 HB13 HC Dl Ci C13.
    pose proof (WNf_ne_inv (whne_leq _ _ Ew (gne_tm_whne_r Hν)) H3) as Hν3.
    assert (Hm : lequiv (gL G) (lmax l3 l4) (lmax l1 l2)) by now apply lequiv_max.
    assert (HV : [ G ; Γ ⊢g tyW l3 l4 A3 B3 ≅ tyW l1 l2 A1 B1 @ lmax l3 l4 ]).
    { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_W; auto using lequiv_sym | exact Hm]. }
    apply wnf_ne. eapply gne_tm_leq_r; [exact Hν | | exact Ew].
    eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν3 | exact HV] | apply lequiv_sym, Hm].
Qed.

(** ** Finitary trees (M15a)

    As [WfRel_trans_all], the third tree related to itself: the shapes by
    [Dl]; a spine along a third length [NatRel]-related to the left one,
    its children taken at the third annotations on both sides. *)
Section WfLeq.

Definition WfLeqHyps G Γ l1 A1 N1 (d1 : DomRel G Γ) l3 A3 N3 (d3 : DomRel G Γ) :=
  WfFlipHyps G Γ l1 A1 N1 d1 l3 A3 N3 /\
  (forall ρ x y z, d1 ρ x y -> d3 ρ z z -> tm_leq y z -> d1 ρ x z).

Lemma WfLeqHyps_kw {G Γ l1 A1 N1 d1 l3 A3 N3 d3} (ρ : kwk G Γ) :
  WfLeqHyps G Γ l1 A1 N1 d1 l3 A3 N3 d3 ->
  WfLeqHyps (kw_G ρ) (kw_Δ ρ) l1 (kty ρ A1) (ktml ρ N1) (fun ρ' => d1 (kw_comp ρ ρ'))
    l3 (kty ρ A3) (ktml ρ N3) (fun ρ' => d3 (kw_comp ρ ρ')).
Proof using EL.
  intros [Hy Dl]. split; [exact (WfFlipHyps_kw ρ Hy)|].
  intros ρ' x y z. exact (Dl (kw_comp ρ ρ') x y z).
Qed.

Lemma WfRel_leq_all :
  (forall G Γ l1 A1 N1 d1 t1 t2, WfRel G Γ l1 A1 N1 d1 t1 t2 ->
     forall l3 A3 N3 d3 t3, WfLeqHyps G Γ l1 A1 N1 d1 l3 A3 N3 d3 ->
     WfRel G Γ l3 A3 N3 d3 t3 t3 -> tm_leq t2 t3 -> WfRel G Γ l1 A1 N1 d1 t1 t3) /\
  (forall G Γ l1 A1 N1 d1 t1 t2, WfNf G Γ l1 A1 N1 d1 t1 t2 ->
     forall l3 A3 N3 d3 t3, WfLeqHyps G Γ l1 A1 N1 d1 l3 A3 N3 d3 ->
     WfNf G Γ l3 A3 N3 d3 t3 t3 -> tm_leq t2 t3 -> WfNf G Γ l1 A1 N1 d1 t1 t3) /\
  (forall G Γ l1 A1 N1 d1 k1 cs1 cs2, VecSp G Γ l1 A1 N1 d1 k1 cs1 cs2 ->
     forall l3 A3 N3 d3 k3 cs3, WfLeqHyps G Γ l1 A1 N1 d1 l3 A3 N3 d3 ->
     NatRel G Γ k1 k3 -> VecSp G Γ l3 A3 N3 d3 k3 cs3 cs3 -> tm_leq cs2 cs3 ->
     VecSp G Γ l1 A1 N1 d1 k1 cs1 cs3).
Proof using EL.
  apply WfRel_comb.
  - intros G Γ l1 A1 N1 d1 t1 t2 w1 w2 Hw1 Hw2 Heq Hn IH l3 A3 N3 d3 t3 Hy H3 Et.
    destruct (WfFlip_data (proj1 Hy)) as (W1 & W3 & HWf1 & HWf3 & EWg & EW).
    pose proof (proj1 (proj1 Hy)) as Hl.
    destruct (WfRel_inv H3) as (w3 & w3' & Hw3 & Hw3' & Heq3 & Hn3).
    assert (w3' = w3) as ->
      by (eapply tmred_whnf_det; [exact Hw3' | exact Hw3 | exact (WfNf_whnf_r Hn3) | exact (WfNf_whnf_l Hn3)]).
    assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2 Hw3 (WfNf_whnf_r Hn) (WfNf_whnf_l Hn3)).
    assert (HV : [ G ; Γ ⊢g tyWf l3 A3 N3 ≅ tyWf l1 A1 N1 @ l3 ]) by (eapply eqty_lconv; [apply eqty_sym, EW | exact Hl]).
    econstructor; [exact Hw1 | | |].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw3 | exact HV] | apply lequiv_sym, Hl].
    + eapply geq_tm_leq_r; [exact Heq | | exact Ew].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq3 | exact HV] | apply lequiv_sym, Hl].
    + exact (IH l3 A3 N3 d3 w3 Hy Hn3 Ew).
  - intros G Γ l1 A1 N1 d1 k k' C C' M M' a a' cs cs' Hk Hk' HAC HAC' HNM HNM' Ha Hcs IH l3 A3 N3 d3 t3 Hy H3 Ew.
    destruct (tm_leq_supf_inv Ew) as (j3 & C3 & M3 & a3 & cs3 & -> & _ & _ & _ & Ea & Ecs).
    destruct (WfNf_sup_inv H3) as (j3' & C3' & M3' & a3' & cs3' & Heq3 & Hj3 & _ & HE & _ & HF & _ & Ha3 & Hcs3).
    injection Heq3 as <- <- <- <- <-.
    destruct Hy as [Hy0 Dl]. pose proof Hy0 as (Hl & HA1 & HA13 & HN13 & HC).
    pose proof (lequiv_wf_r _ _ _ Hl) as W1.
    apply wfnf_sup.
    + exact Hk.
    + exact (lequiv_trans _ _ _ _ Hj3 Hl).
    + exact HAC.
    + eapply geq_ty_trans; [exact HA13 | eapply geq_ty_lconv; [exact HE | apply lequiv_sym, Hl]].
    + exact HNM.
    + eapply geq_tm_trans; [exact HN13|].
      eapply geq_tm_ctxconv; [| exact Hl | apply ext_wf_g; [exact HA1 | exact W1] | exact HF].
      eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA13 | exact Hl].
    + intros ρ. exact (Dl ρ _ _ _ (Ha ρ) (Ha3 ρ) (ktm_leq ρ _ _ Ea)).
    + intros ρ.
      exact (IH ρ l3 (kty ρ A3) (ktml ρ N3) _ _ _ (WfLeqHyps_kw ρ (conj Hy0 Dl))
               (HC ρ _ _ (Dl ρ _ _ _ (Ha ρ) (Ha3 ρ) (ktm_leq ρ _ _ Ea))) (Hcs3 ρ) (ktm_leq ρ _ _ Ecs)).
  - intros G Γ l1 A1 N1 d1 ν ν' Hν l3 A3 N3 d3 t3 Hy H3 Ew.
    destruct (WfFlip_data (proj1 Hy)) as (W1 & W3 & HWf1 & HWf3 & EWg & EW).
    pose proof (proj1 (proj1 Hy)) as Hl.
    pose proof (WfNf_ne_inv (whne_leq _ _ Ew (gne_tm_whne_r Hν)) H3) as Hν3.
    assert (HV : [ G ; Γ ⊢g tyWf l3 A3 N3 ≅ tyWf l1 A1 N1 @ l3 ]) by (eapply eqty_lconv; [apply eqty_sym, EW | exact Hl]).
    apply wfnf_ne. eapply gne_tm_leq_r; [exact Hν | | exact Ew].
    eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν3 | exact HV] | apply lequiv_sym, Hl].
  - intros G Γ l1 A1 N1 d1 k1 cs1 cs2 Hk Hu l3 A3 N3 d3 k3 cs3 Hy Hkk H3 Ecs.
    pose proof (VecSp_zero_inv H3 (NatRel_inv_zero Hkk Hk)) as Hu3.
    pose proof (proj1 (proj1 Hy)) as Hl.
    apply vsp_zero; [exact Hk|].
    destruct Hu as (w1 & _ & Hr1 & _ & Hf1 & _). destruct Hu3 as (w3 & _ & Hr3 & _ & Hf3 & _).
    exists w1, w3. exact (conj Hr1 (conj (unit_tmred_conv Hl Hr3) (conj Hf1 Hf3))).
  - intros G Γ l1 A1 N1 d1 k1 m1 cs1 cs2 w1 w2 Hk Hcs1 Hcs2 Hwh1 Hwh2 Heq Hfst IHfst Hsnd IHsnd
      l3 A3 N3 d3 k3 cs3 Hy Hkk H3 Ecs.
    destruct (WfFlip_data (proj1 Hy)) as (W1 & W3 & HWf1 & HWf3 & EWg & EW).
    pose proof (proj1 (proj1 Hy)) as Hl.
    destruct (NatRel_inv_succ Hkk Hk) as (m3 & Hk3 & Hmm).
    destruct (VecSp_succ_inv H3 Hk3) as (w3 & w3' & Hcs3 & Hcs3' & Hwh3 & Hwh3' & Heq3 & Hfst3 & Hsnd3).
    assert (w3' = w3) as -> by (eapply tmred_whnf_det; [exact Hcs3' | exact Hcs3 | exact Hwh3' | exact Hwh3]).
    assert (Ew : tm_leq w2 w3) by exact (tmred_leq Ecs Hcs2 Hcs3 Hwh2 Hwh3).
    pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
    pose proof (sigvec_eq (lequiv_sym _ _ _ Hl) W1 HWf1 EW Em) as ES.
    assert (Hml : lequiv (gL G) (lmax l3 l3) (lmax l1 l1)) by now apply lequiv_max.
    assert (HV : [ G ; Γ ⊢g tySig l3 l3 (tyWf l3 A3 N3) (tyVec l3 (tyWf l3 A3 N3)⟨↑⟩ m3⟨↑⟩)
                   ≅ tySig l1 l1 (tyWf l1 A1 N1) (tyVec l1 (tyWf l1 A1 N1)⟨↑⟩ m1⟨↑⟩) @ lmax l3 l3 ])
      by (eapply eqty_lconv; [apply eqty_sym, ES | exact Hml]).
    assert (HΓ1 : [ G ; Γ ,, tyWf l1 A1 N1 @ l1 ⊢g ]) by now apply ext_wf_g.
    assert (HΓ3 : [ G ; Γ ,, tyWf l3 A3 N3 @ l3 ⊢g ]) by now apply ext_wf_g.
    assert (VV : [ G ; Γ ,, tyWf l1 A1 N1 @ l1 ⊢ tyVec l1 (tyWf l1 A1 N1)⟨↑⟩ m1⟨↑⟩
                                              ≈ tyVec l3 (tyWf l3 A3 N3)⟨↑⟩ m3⟨↑⟩ @ l1 ])
      by exact (geq_ty_wk (wkr_shift1 _ _ _) HΓ1 (geq_vec_nat m1 m3 Hmm l1 l3 _ _ (lequiv_sym _ _ _ Hl) HWf1 EWg)).
    assert (MA : forall X, [ G ; Γ ⊢ tyWf l1 A1 N1 ≈ X @ l1 ] -> [ G ; Γ ⊢ tyWf l3 A3 N3 ≈ X @ l3 ]).
    { intros X HX. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, EWg | exact HX] | exact Hl]. }
    assert (MB : forall X, [ G ; Γ ,, tyWf l1 A1 N1 @ l1 ⊢ tyVec l1 (tyWf l1 A1 N1)⟨↑⟩ m1⟨↑⟩ ≈ X @ l1 ] ->
                   [ G ; Γ ,, tyWf l3 A3 N3 @ l3 ⊢ tyVec l3 (tyWf l3 A3 N3)⟨↑⟩ m3⟨↑⟩ ≈ X @ l3 ]).
    { intros X HX. eapply geq_ty_lconv; [|exact Hl].
      eapply geq_ty_ctxconv; [exact EW | apply lequiv_sym, Hl | exact HΓ3 |].
      eapply geq_ty_trans; [apply geq_ty_sym, VV | exact HX]. }
    pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    apply (vsp_succ G Γ l1 A1 N1 d1 k1 m1 cs1 cs3 w1 w3).
    + exact Hk.
    + exact Hcs1.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs3 | exact HV] | apply lequiv_sym, Hml].
    + exact Hwh1.
    + exact Hwh3.
    + eapply geq_tm_leq_r; [exact Heq | | exact Ew].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq3 | exact HV] | apply lequiv_sym, Hml].
    + intros la lb A1x B1x la3 lb3 A1x3 B1x3 H1 H2 H3' H4 HA1x HB1x HA1x3 HB1x3.
      assert (P3 : lequiv (gL G) la3 l3) by exact (lequiv_trans _ _ _ _ H3' Hl').
      assert (P4 : lequiv (gL G) lb3 l3) by exact (lequiv_trans _ _ _ _ H4 Hl').
      pose proof (Hfst3 la3 lb3 A1x3 B1x3 la3 lb3 A1x3 B1x3 P3 P4 P3 P4
                    (MA _ HA1x3) (MB _ HB1x3) (MA _ HA1x3) (MB _ HB1x3)) as X3.
      refine (IHfst la lb A1x B1x la3 lb3 A1x3 B1x3 H1 H2 H3' H4 HA1x HB1x HA1x3 HB1x3 l3 A3 N3 d3 _ Hy X3 _).
      cbn; repeat split; auto using leqv_refl, ty_leq_refl, tm_leq_refl.
    + intros la lb A1x B1x la3 lb3 A1x3 B1x3 H1 H2 H3' H4 HA1x HB1x HA1x3 HB1x3.
      assert (P3 : lequiv (gL G) la3 l3) by exact (lequiv_trans _ _ _ _ H3' Hl').
      assert (P4 : lequiv (gL G) lb3 l3) by exact (lequiv_trans _ _ _ _ H4 Hl').
      pose proof (Hsnd3 la3 lb3 A1x3 B1x3 la3 lb3 A1x3 B1x3 P3 P4 P3 P4
                    (MA _ HA1x3) (MB _ HB1x3) (MA _ HA1x3) (MB _ HB1x3)) as X3.
      refine (IHsnd la lb A1x B1x la3 lb3 A1x3 B1x3 H1 H2 H3' H4 HA1x HB1x HA1x3 HB1x3 l3 A3 N3 d3 _ _ Hy Hmm X3 _).
      cbn; repeat split; auto using leqv_refl, ty_leq_refl, tm_leq_refl.
  - intros G Γ l1 A1 N1 d1 k1 ν1 cs1 cs2 Hk Hν1 Hne l3 A3 N3 d3 k3 cs3 Hy Hkk H3 Ecs.
    destruct (WfFlip_data (proj1 Hy)) as (W1 & W3 & HWf1 & HWf3 & EWg & EW).
    pose proof (proj1 (proj1 Hy)) as Hl.
    destruct (NatRel_inv_ne Hkk Hk (gne_tm_whne_l Hν1)) as (ν3 & Hk3 & Hνν).
    pose proof (VecSp_ne_inv H3 Hk3 (gne_tm_whne_r Hνν)) as Hne3.
    apply (vsp_ne G Γ l1 A1 N1 d1 k1 ν1 cs1 cs3); [exact Hk | exact Hν1 |].
    pose proof (geq_ty_sound (gne_ty_geq (gne_ty_vec (lequiv_sym _ _ _ Hl) HWf1 EWg Hνν))) as EV.
    assert (EV' : [ G ; Γ ⊢g tyVec l3 (tyWf l3 A3 N3) ν3 ≅ tyVec l1 (tyWf l1 A1 N1) ν1 @ l3 ])
      by (eapply eqty_lconv; [apply eqty_sym, EV | exact Hl]).
    pose proof (NeRel_conv2 EV' EV' Hne3) as Hne3'.
    apply (NeRel_lconv _ _ _ _ _ _ (lequiv_sym _ _ _ Hl)) in Hne3'.
    pose proof (eqty_wf_l ge_typeof EV) as HV1.
    eapply NeRel_leq; [apply eqty_refl, HV1 | apply eqty_refl, HV1 | apply eqty_refl, HV1 | exact Hne | exact Hne3' | exact Ecs].
Qed.

End WfLeq.

(** ** Indexed finitary trees (M17b)

    As [IWfRel_trans_all], the third tree related to itself. A child
    position along the third length is split by [PosRel_leq_split] into one
    along the second length, [≡ₗ]-below it. *)
Section IWfLeq.

Lemma ktmll_leq {G Γ} (ρ : kwk G Γ) t t' : tm_leq t t' -> tm_leq (ktmll ρ t) (ktmll ρ t').
Proof using . intros H; unfold ktmll; apply (proj1 (proj2 leq_ren_all)), tm_leq_gwa, H. Qed.

Lemma PosRel_refl_r {G Γ k k' p p'} : PosRel G Γ k k' p p' -> PosRel G Γ k' k' p' p'.
Proof using EL.
  induction 1 as [k k' m m' Hk Hk' Hm | k k' m m' p p' Hk Hk' Hp IH | k k' p p' Ek Hp].
  - apply pos_hd; auto. exact (NatRel_trans _ _ _ _ (NatRel_sym _ _ _ _ Hm) _ Hm).
  - eapply pos_tl; eauto.
  - apply pos_ne; [exact (eqtm_refl _ _ _ _ _ _ (eqtm_wf_r ge_typeof Ek)) |].
    eapply gne_tm_conv; [eapply gne_tm_trans; [apply gne_tm_sym, Hp | exact Hp] |].
    apply eqty_fin; [exact ge_notV | exact Ek].
Qed.

Lemma PosRel_leq_split {G Γ k1 k3 p p'} : PosRel G Γ k1 k3 p p' -> forall k2, NatRel G Γ k1 k2 ->
  tm_leq k2 k3 -> exists p'', PosRel G Γ k1 k2 p p'' /\ tm_leq p'' p'.
Proof using EL.
  induction 1 as [k1 k3 m1 m3 Hk1 Hk3 Hm | k1 k3 m1 m3 p p' Hk1 Hk3 Hp IH | k1 k3 p p' Ek Hp];
    intros k2 Hk12 E23;
    [destruct (NatRel_inv_succ Hk12 Hk1) as (m2 & Hk2 & Hm12);
     pose proof (tmred_leq E23 Hk2 Hk3 (whnf_succ _) (whnf_succ _)) as Es; cbn in Es ..|].
  3: { exists p'. split; [apply pos_ne; [exact (geq_tm_sound (NatRel_geq Hk12)) | exact Hp] | apply tm_leq_refl]. }
  - exists (posHd m2). split; [constructor; auto|].
    unfold posHd; cbn; repeat split; auto using leqv_refl, ty_leq_refl, tm_leq_refl.
  - destruct (IH m2 Hm12 Es) as (p'' & Hp1 & Ep).
    exists (posTl m2 p''). split; [econstructor; eauto|].
    unfold posTl; cbn; repeat split; auto using leqv_refl, ty_leq_refl, tm_leq_refl.
Qed.

Definition IWfLeqHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 (ix1 dm1 : DomRel G Γ) l3 li3 X3 A3 N3 Ot3 C3
    (dm3 : DomRel G Γ) :=
  IWfFlipHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l3 li3 X3 A3 N3 Ot3 C3 /\
  (forall ρ x y z, dm1 ρ x y -> dm3 ρ z z -> tm_leq y z -> dm1 ρ x z).

Lemma IWfLeqHyps_kw {G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l3 li3 X3 A3 N3 Ot3 C3 dm3} (ρ : kwk G Γ) :
  IWfLeqHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l3 li3 X3 A3 N3 Ot3 C3 dm3 ->
  IWfLeqHyps (kw_G ρ) (kw_Δ ρ) l1 li1 (kty ρ X1) (kty ρ A1) (ktml ρ N1) (ktml ρ Ot1) (ktmll ρ C1)
    (fun ρ' => ix1 (kw_comp ρ ρ')) (fun ρ' => dm1 (kw_comp ρ ρ'))
    l3 li3 (kty ρ X3) (kty ρ A3) (ktml ρ N3) (ktml ρ Ot3) (ktmll ρ C3) (fun ρ' => dm3 (kw_comp ρ ρ')).
Proof using EL.
  intros [Hy Dl]. split; [exact (IWfFlipHyps_kw ρ Hy)|].
  intros ρ' x y z. exact (Dl (kw_comp ρ ρ') x y z).
Qed.

Lemma IWfRel_leq_all :
  (forall G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2, IWfRel G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2 ->
     forall l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 m3 t3,
     IWfLeqHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l3 li3 X3 A3 N3 Ot3 C3 dm3 ->
     [ G ; Γ ⊢g tyIWf l1 li1 X1 A1 N1 Ot1 C1 m1 ≅ tyIWf l3 li3 X3 A3 N3 Ot3 C3 m3 @ lmax l1 li1 ] ->
     IWfRel G Γ l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 m3 t3 t3 -> tm_leq t2 t3 ->
     IWfRel G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t3) /\
  (forall G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2, IWfNf G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2 ->
     forall l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 m3 t3,
     IWfLeqHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l3 li3 X3 A3 N3 Ot3 C3 dm3 ->
     [ G ; Γ ⊢g tyIWf l1 li1 X1 A1 N1 Ot1 C1 m1 ≅ tyIWf l3 li3 X3 A3 N3 Ot3 C3 m3 @ lmax l1 li1 ] ->
     IWfNf G Γ l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 m3 t3 t3 -> tm_leq t2 t3 ->
     IWfNf G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t3) /\
  (forall G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 cs1 cs2,
     DVecISp G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 cs1 cs2 ->
     forall l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 c3 k3 cs3,
     IWfLeqHyps G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 l3 li3 X3 A3 N3 Ot3 C3 dm3 ->
     NatRel G Γ k1 k3 ->
     [ G ; Γ ,, tyFin k1 @ lzero ⊢g iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1 ≅ iwfFamT l3 li3 X3 A3 N3 Ot3 C3 c3
         @ lmax l1 li1 ] ->
     (forall (ρ : kwk G Γ) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k1) (ktm ρ k3) p p' ->
        ix1 ρ (ktml ρ c1)[lsingle p] (ktml ρ c3)[lsingle p']) ->
     DVecISp G Γ l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 c3 k3 cs3 cs3 -> tm_leq cs2 cs3 ->
     DVecISp G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 cs1 cs3).
Proof using EL.
  apply IWfRel_comb.
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 t1 t2 w1 w2 Hw1 Hw2 Heq Hn IH
      l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 m3 t3 Hy ET H3 Et.
    pose proof (IWfFlip_lv (proj1 Hy)) as Hml.
    destruct (IWfRel_inv H3) as (w3 & w3' & Hw3 & Hw3' & Heq3 & Hn3).
    assert (w3' = w3) as ->
      by (eapply tmred_whnf_det; [exact Hw3' | exact Hw3 | exact (IWfNf_whnf_r Hn3) | exact (IWfNf_whnf_l Hn3)]).
    assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2 Hw3 (IWfNf_whnf_r Hn) (IWfNf_whnf_l Hn3)).
    assert (HV : [ G ; Γ ⊢g tyIWf l3 li3 X3 A3 N3 Ot3 C3 m3 ≅ tyIWf l1 li1 X1 A1 N1 Ot1 C1 m1 @ lmax l3 li3 ])
      by (eapply eqty_lconv; [apply eqty_sym, ET | exact Hml]).
    econstructor; [exact Hw1 | | |].
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw3 | exact HV] | apply lequiv_sym, Hml].
    + eapply geq_tm_leq_r; [exact Heq | | exact Ew].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq3 | exact HV] | apply lequiv_sym, Hml].
    + exact (IH l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 m3 w3 Hy ET Hn3 Ew).
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 k ki k' ki' Xa Aa Na Oa Ca Xb Ab Nb Ob Cb a a' cs cs'
      E1 E2 Hd Ho Hcs IH l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 m3 t3 Hy ET H3 Ew.
    destruct (tm_leq_supi_inv Ew) as (k3 & ki3 & Xc & Ac & Nc & Oc & Cc & a3 & cs3 & -> & _ & _ & _ & _ & _ & _ & _
                                      & Ea & Ecs).
    destruct (IWfNf_sup_inv H3) as (k'' & ki'' & Xd & Ad & Nd & Od & Cd & a'' & cs'' & Heq3 & E3 & _ & Hd3 & _ & Hcs3).
    injection Heq3 as <- <- <- <- <- <- <- <- <-.
    destruct Hy as [Hy0 Dl]. pose proof Hy0 as (HE & _ & _ & Hesc & Har & _ & Hch & _).
    assert (Hd13 : forall ρ : kwk G Γ, dm1 ρ (ktm ρ a) (ktm ρ a3))
      by (intros ρ; exact (Dl ρ _ _ _ (Hd ρ) (Hd3 ρ) (ktm_leq ρ _ _ Ea))).
    apply iwfnf_sup.
    + exact E1.
    + exact (IWfEq_trans ge_typeof ge_notV HE E3).
    + exact Hd13.
    + exact Ho.
    + intros ρ. destruct (Hesc ρ _ _ (Hd13 ρ)) as (Ha & Ha' & Haa).
      refine (IH ρ l3 li3 (kty ρ X3) (kty ρ A3) (ktml ρ N3) (ktml ρ Ot3) (ktmll ρ C3)
               (fun ρ' => ix3 (kw_comp ρ ρ')) (fun ρ' => dm3 (kw_comp ρ ρ'))
               (ktmll ρ C3)[llift (lsingle (ktm ρ a3))] (ktml ρ N3)[lsingle (ktm ρ a3)] (ktm ρ cs3)
               (IWfLeqHyps_kw ρ (conj Hy0 Dl)) (Har ρ _ _ (Hd13 ρ))
               (IWf_fam_eq ge_typeof ge_notV (IWfEq_kw ρ HE) Ha Ha' Haa) _ (Hcs3 ρ) (ktm_leq ρ _ _ Ecs)).
      intros ρ' p p' Hp. rewrite !ktml_comp_child. rewrite !ktm_comp_single in Hp.
      exact (Hch _ _ _ (Hd13 (kw_comp ρ ρ')) p p' Hp).
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 m1 ν ν' Hν l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 m3 t3 Hy ET H3 Ew.
    pose proof (IWfFlip_lv (proj1 Hy)) as Hml.
    pose proof (IWfNf_ne_inv (whne_leq _ _ Ew (gne_tm_whne_r Hν)) H3) as Hν3.
    assert (HV : [ G ; Γ ⊢g tyIWf l3 li3 X3 A3 N3 Ot3 C3 m3 ≅ tyIWf l1 li1 X1 A1 N1 Ot1 C1 m1 @ lmax l3 li3 ])
      by (eapply eqty_lconv; [apply eqty_sym, ET | exact Hml]).
    apply iwfnf_ne. eapply gne_tm_leq_r; [exact Hν | | exact Ew].
    eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν3 | exact HV] | apply lequiv_sym, Hml].
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 cs1 cs2 Hk Hu l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 c3 k3 cs3
      Hy Hkk _ _ H3 Ecs.
    pose proof (DVecISp_zero_inv H3 (NatRel_inv_zero Hkk Hk)) as Hu3.
    apply visp_zero; [exact Hk|].
    destruct Hu as (w1 & _ & Hr1 & _ & Hf1 & _). destruct Hu3 as (w3 & _ & Hr3 & _ & Hf3 & _).
    exists w1, w3. exact (conj Hr1 (conj (unit_tmred_conv (IWfFlip_lv (proj1 Hy)) Hr3) (conj Hf1 Hf3))).
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 m1 cs1 cs2 w1 w2 Hk Hcs1 Hcs2 Hwh1 Hwh2 Heq
      Hfst IHfst Hsnd IHsnd l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 c3 k3 cs3 Hy Hkk HF HP H3 Ecs.
    pose proof (proj1 Hy) as Hy0. pose proof Hy0 as (HE & _).
    pose proof HE as (Hll & Hlli & (Wl & Wli & HX & HA & HN & HO & HC) & _ & _ & _ & _ & _
                      & HX' & HA' & HN' & HO' & HC').
    pose proof (IWfFlip_lv Hy0) as Hml. pose proof (lequiv_sym _ _ _ Hml) as Hml'.
    assert (HL : lwf (gL G) (lmax l1 li1)) by (split; assumption).
    assert (HL3 : lwf (gL G) (lmax l3 li3)) by exact (lequiv_wf_l _ _ _ Hml).
    assert (Hml2 : lequiv (gL G) (lmax (lmax l3 li3) (lmax l3 li3)) (lmax (lmax l1 li1) (lmax l1 li1)))
      by now apply lequiv_max.
    destruct (NatRel_inv_succ Hkk Hk) as (m3 & Hk3 & Hmm).
    destruct (DVecISp_succ_inv H3 Hk3) as (w3 & w3' & Hcs3 & Hcs3' & Hwh3 & Hwh3' & Heq3 & Hfst3 & Hsnd3).
    assert (w3' = w3) as -> by (eapply tmred_whnf_det; [exact Hcs3' | exact Hcs3 | exact Hwh3' | exact Hwh3]).
    assert (Ew : tm_leq w2 w3) by exact (tmred_leq Ecs Hcs2 Hcs3 Hwh2 Hwh3).
    pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
    pose proof (eqtm_wf_l ge_typeof Em) as Hm1. pose proof (eqtm_wf_r ge_typeof Em) as Hm3.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hk) as Ek.
    assert (HF1 : [ G ; Γ ,, tyFin (succ m1) @ lzero ⊢g iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1
                    ≅ iwfFamT l3 li3 X3 A3 N3 Ot3 C3 c3 @ lmax l1 li1 ]).
    { refine (stab_eqty ge_typeof _ (lequiv_refl (gL G) lzero I) _ HF).
      - apply eqty_fin; [exact ge_notV | exact Ek].
      - apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV |].
        exact (eqtm_wf_r ge_typeof Ek). }
    pose proof (eqty_wf_l ge_typeof HF1) as HF1w.
    pose proof (dvecHd_eqty ge_typeof ge_notV ge_compt Hm1 Hm3 Em HF1w HF1) as EH.
    assert (ETf : [ G ; Γ ⊢g tyIWf l1 li1 X1 A1 N1 Ot1 C1 c1[lsingle (posHd m1)]
                    ≅ tyIWf l3 li3 X3 A3 N3 Ot3 C3 c3[lsingle (posHd m3)] @ lmax l1 li1 ]).
    { pose proof EH as Y. rewrite !iwfFamT_single in Y by eauto using wf_ty_nf, wf_tm_nf. exact Y. }
    assert (ETs : [ G ; Γ ,, tyFin m1 @ lzero ⊢g iwfFamT l1 li1 X1 A1 N1 Ot1 C1 (posMv m1 c1)
                    ≅ iwfFamT l3 li3 X3 A3 N3 Ot3 C3 (posMv m3 c3) @ lmax l1 li1 ]).
    { rewrite <- !iwfFamT_mv. exact (dvecMv_eqty ge_typeof ge_notV ge_compt Hm1 Hm3 Em HF1w HF1). }
    set (F1 := iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1) in *. set (F3 := iwfFamT l3 li3 X3 A3 N3 Ot3 C3 c3) in *.
    pose proof (dvec_sig_eqty ge_typeof ge_notV ge_compt Hml' HL Hm1 Hm3 Em HF1w HF1) as ES.
    assert (HV : [ G ; Γ ⊢g tySig (lmax l3 li3) (lmax l3 li3) (dvecHd m3 F3) (dvecTl (lmax l3 li3) m3 F3)
                   ≅ tySig (lmax l1 li1) (lmax l1 li1) (dvecHd m1 F1) (dvecTl (lmax l1 li1) m1 F1)
                   @ lmax (lmax l3 li3) (lmax l3 li3) ])
      by (eapply eqty_lconv; [apply eqty_sym, ES | exact Hml2]).
    assert (HH : [ G ; Γ ⊢g dvecHd m1 F1 @ lmax l1 li1 ])
      by exact (wf_ty_single ge_typeof HF1w (fin_inl_wf ge_typeof ge_notV ge_compt Hm1)).
    assert (HH3 : [ G ; Γ ⊢g dvecHd m3 F3 @ lmax l3 li3 ])
      by (eapply wft_lconv; [exact (eqty_wf_r ge_typeof EH) | exact Hml]).
    assert (HΓ1 : [ G ; Γ ,, dvecHd m1 F1 @ lmax l1 li1 ⊢g ]) by (apply ext_wf_g; [exact HH | exact HL]).
    assert (HΓ3 : [ G ; Γ ,, dvecHd m3 F3 @ lmax l3 li3 ⊢g ]) by (apply ext_wf_g; [exact HH3 | exact HL3]).
    pose proof Hy0 as (_ & _ & _ & _ & _ & _ & _ & HGy & Hiey).
    destruct (iwf_succ_geq HE HGy Hk Hk3 Hmm HF (fun ρ p p' Hp => Hiey ρ _ _ (HP ρ p p' Hp))) as [GH GT].
    assert (MA : forall Y, [ G ; Γ ⊢ dvecHd m1 F1 ≈ Y @ lmax l1 li1 ] -> [ G ; Γ ⊢ dvecHd m3 F3 ≈ Y @ lmax l3 li3 ]).
    { intros Y HY. eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, GH | exact HY] | exact Hml]. }
    assert (MB : forall Y, [ G ; Γ ,, dvecHd m1 F1 @ lmax l1 li1 ⊢ dvecTl (lmax l1 li1) m1 F1 ≈ Y @ lmax l1 li1 ] ->
                  [ G ; Γ ,, dvecHd m3 F3 @ lmax l3 li3 ⊢ dvecTl (lmax l3 li3) m3 F3 ≈ Y @ lmax l3 li3 ]).
    { intros Y HY. eapply geq_ty_lconv; [| exact Hml].
      eapply geq_ty_trans; [apply geq_ty_sym, (GT _ _ HΓ3) |].
      exact (geq_ty_ctxconv EH Hml' HΓ3 HY). }
    apply (visp_succ G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 m1 cs1 cs3 w1 w3).
    + exact Hk.
    + exact Hcs1.
    + eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hcs3 | exact HV] | apply lequiv_sym, Hml2].
    + exact Hwh1.
    + exact Hwh3.
    + eapply geq_tm_leq_r; [exact Heq | | exact Ew].
      eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Heq3 | exact HV] | apply lequiv_sym, Hml2].
    + intros la lb Ax Bx la3 lb3 Ax3 Bx3 H1 H2 H3' H4 HAx HBx HAx3 HBx3.
      assert (P3 : lequiv (gL G) la3 (lmax l3 li3)) by exact (lequiv_trans _ _ _ _ H3' Hml').
      assert (P4 : lequiv (gL G) lb3 (lmax l3 li3)) by exact (lequiv_trans _ _ _ _ H4 Hml').
      pose proof (Hfst3 la3 lb3 Ax3 Bx3 la3 lb3 Ax3 Bx3 P3 P4 P3 P4
                    (MA _ HAx3) (MB _ HBx3) (MA _ HAx3) (MB _ HBx3)) as Y3.
      refine (IHfst la lb Ax Bx la3 lb3 Ax3 Bx3 H1 H2 H3' H4 HAx HBx HAx3 HBx3
                l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 _ _ Hy ETf Y3 _).
      cbn; repeat split; auto using leqv_refl, ty_leq_refl, tm_leq_refl.
    + intros la lb Ax Bx la3 lb3 Ax3 Bx3 H1 H2 H3' H4 HAx HBx HAx3 HBx3.
      assert (P3 : lequiv (gL G) la3 (lmax l3 li3)) by exact (lequiv_trans _ _ _ _ H3' Hml').
      assert (P4 : lequiv (gL G) lb3 (lmax l3 li3)) by exact (lequiv_trans _ _ _ _ H4 Hml').
      pose proof (Hsnd3 la3 lb3 Ax3 Bx3 la3 lb3 Ax3 Bx3 P3 P4 P3 P4
                    (MA _ HAx3) (MB _ HBx3) (MA _ HAx3) (MB _ HBx3)) as Y3.
      refine (IHsnd la lb Ax Bx la3 lb3 Ax3 Bx3 H1 H2 H3' H4 HAx HBx HAx3 HBx3
                l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 _ _ _ Hy Hmm ETs _ Y3 _).
      * intros ρ p p' Hp. rewrite !ktml_posMv_single by eauto using wf_tm_nf. apply HP.
        apply pos_tl; [exact (kw_tmred_succ Hk ρ) | exact (kw_tmred_succ Hk3 ρ) | exact Hp].
      * cbn; repeat split; auto using leqv_refl, ty_leq_refl, tm_leq_refl.
  - intros G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 ν1 cs1 cs2 Hk Hν1 Hne
      l3 li3 X3 A3 N3 Ot3 C3 ix3 dm3 c3 k3 cs3 Hy Hkk HF _ H3 Ecs.
    pose proof (IWfFlip_lv (proj1 Hy)) as Hml. pose proof (lequiv_sym _ _ _ Hml) as Hml'.
    destruct (NatRel_inv_ne Hkk Hk (gne_tm_whne_l Hν1)) as (ν3 & Hk3 & Hνν).
    pose proof (DVecISp_ne_inv H3 Hk3 (gne_tm_whne_r Hνν)) as Hne3.
    apply (visp_ne G Γ l1 li1 X1 A1 N1 Ot1 C1 ix1 dm1 c1 k1 ν1 cs1 cs3); [exact Hk | exact Hν1 |].
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Eν.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hk) as Ek.
    assert (HFν : [ G ; Γ ,, tyFin ν1 @ lzero ⊢g iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1
                    ≅ iwfFamT l3 li3 X3 A3 N3 Ot3 C3 c3 @ lmax l1 li1 ]).
    { refine (stab_eqty ge_typeof _ (lequiv_refl (gL G) lzero I) _ HF).
      - apply eqty_fin; [exact ge_notV | exact Ek].
      - apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV |].
        exact (eqtm_wf_r ge_typeof Ek). }
    assert (EV : [ G ; Γ ⊢g tyDVec (lmax l1 li1) ν1 (iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1)
                    ≅ tyDVec (lmax l3 li3) ν3 (iwfFamT l3 li3 X3 A3 N3 Ot3 C3 c3) @ lmax l1 li1 ]).
    { apply eqty_dvec; [exact (compt_notV _ ge_compt) | exact Hml' | exact (eqtm_wf_l ge_typeof Eν) | exact Eν
                       | exact (eqty_wf_l ge_typeof HFν) | exact HFν]. }
    assert (EV' : [ G ; Γ ⊢g tyDVec (lmax l3 li3) ν3 (iwfFamT l3 li3 X3 A3 N3 Ot3 C3 c3)
                     ≅ tyDVec (lmax l1 li1) ν1 (iwfFamT l1 li1 X1 A1 N1 Ot1 C1 c1) @ lmax l3 li3 ])
      by (eapply eqty_lconv; [apply eqty_sym, EV | exact Hml]).
    pose proof (NeRel_conv2 EV' EV' Hne3) as Hne3'.
    apply (NeRel_lconv _ _ _ _ _ _ (lequiv_sym _ _ _ Hml)) in Hne3'.
    pose proof (eqty_wf_l ge_typeof EV) as HV1.
    eapply NeRel_leq; [apply eqty_refl, HV1 | apply eqty_refl, HV1 | apply eqty_refl, HV1
                      | exact Hne | exact Hne3' | exact Ecs].
Qed.

End IWfLeq.

(** ** [Π]'s and [Σ]'s relations with an [≡ₗ]-related right-hand side,
    given their components' (M18b: [M]'s observations; the [Π] and [Σ]
    cases below are these with the induction hypotheses). The third
    pair's annotations are the first pair's right ones. *)
Section BinLeq.
Context {G : gctx} {Γ : ctx} {l1 l2 l3 l4 k3 k4 : lvl} {A1 B1 A2 B2 A3 B3 : ty}
  {domR1 : DomRel G Γ} {codR1 : CodRel G Γ domR1} {domR3 : DomRel G Γ} {codR3 : CodRel G Γ domR3}
  (Q31 : lequiv (gL G) l3 l1) (Q42 : lequiv (gL G) l4 l2)
  (Q13 : lequiv (gL G) l1 k3) (Q24 : lequiv (gL G) l2 k4) (Hw1 : lwf (gL G) l1)
  (HA1 : [ G ; Γ ⊢g A1 @ l1 ]) (HA2 : [ G ; Γ ⊢g A2 @ l1 ]) (HA3 : [ G ; Γ ⊢g A3 @ k3 ])
  (HA12 : [ G ; Γ ⊢ A1 ≈ A2 @ l1 ]) (HA13 : [ G ; Γ ⊢ A1 ≈ A3 @ l1 ])
  (HB12 : [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B2 @ l2 ]) (HB13 : [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B3 @ l2 ]).

(** The second pair's components against the third's. *)
Lemma bin_leq_23 : [ G ; Γ ⊢ A2 ≈ A3 @ l1 ] /\ [ G ; Γ ,, A2 @ l1 ⊢ B2 ≈ B3 @ l2 ].
Proof using EL HA12 HA13 HA2 HB12 HB13 Hw1.
  split; [exact (geq_ty_trans (geq_ty_sym HA12) HA13)|].
  eapply geq_ty_ctxconv; [apply geq_ty_sound, HA12 | now apply lequiv_refl
                         | apply ext_wf_g; [exact HA2 | exact Hw1] | exact (geq_ty_trans (geq_ty_sym HB12) HB13)].
Qed.

Lemma bin_leq_ann (ρ : kwk G Γ) A5 B5 :
  [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A2 ≈ A5 @ l1 ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l1 ⊢ ktyl ρ B2 ≈ B5 @ l2 ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A3 ≈ A5 @ k3 ] /\ [ kw_G ρ ; kw_Δ ρ ,, kty ρ A3 @ k3 ⊢ ktyl ρ B3 ≈ B5 @ k4 ].
Proof using EL HA12 HA13 HA2 HA3 HB12 HB13 Hw1 Q13 Q24.
  intros HA5 HB5. destruct bin_leq_23 as [HA23 HB23].
  pose proof (kw_lequiv ρ Q13) as Q13'. pose proof (kw_lequiv ρ Q24) as Q24'.
  assert (HΔ3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A3 @ k3 ⊢g ]) by exact (kw_ext ρ HA3 (lequiv_wf_r _ _ _ Q13)).
  assert (E23 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A2 ≈ kty ρ A3 @ l1 ]) by exact (kw_geq_ty ρ HA23).
  split.
  - eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, E23 | exact HA5] |]. apply lequiv_sym, Q13'.
  - assert (F : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l1 ⊢ ktyl ρ B3 ≈ B5 @ l2 ]).
    { eapply geq_ty_trans; [apply geq_ty_sym, (kw_geq_ty_l ρ HA2 Hw1 HB23) | exact HB5]. }
    eapply geq_ty_lconv; [|apply lequiv_sym, Q24'].
    eapply geq_ty_ctxconv; [apply geq_ty_sound, E23 | exact Q13' | exact HΔ3 | exact F].
Qed.

Lemma PiRel_leq
  (H13 : forall ρ a a', domR1 ρ a a' -> domR3 ρ a' a')
  (Lcod : forall ρ a a' (ha : domR1 ρ a a') (h3 : domR3 ρ a' a') u v w,
     codR1 ρ a a' ha u v -> codR3 ρ a' a' h3 w w -> tm_leq v w -> codR1 ρ a a' ha u w) t1 t2 t3 :
  PiRel G Γ l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 t1 t2 ->
  PiRel G Γ k3 k4 k3 k4 A3 B3 A3 B3 domR3 codR3 t3 t3 -> tm_leq t2 t3 ->
  PiRel G Γ l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 t1 t3.
Proof using EL HA1 HA12 HA13 HA2 HA3 HB12 HB13 Hw1 Q13 Q24 Q31 Q42.
  intros H12 H33 Et.
  pose proof (geq_ty_sound (geq_ty_pi Q13 Q24 HA1 HA13 HB13)) as HP13.
  pose proof (geq_ty_sound (geq_ty_trans (geq_ty_sym (geq_ty_pi (lequiv_sym _ _ _ Q31) (lequiv_sym _ _ _ Q42) HA1 HA12 HB12))
                              (geq_ty_pi Q13 Q24 HA1 HA13 HB13))) as HP23.
  destruct H12 as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
  destruct H33 as (w3 & w3' & Hw3r & Hw3r' & Hnf3 & Hnf3' & Heq3 & _ & HK3).
  assert (w3' = w3) as -> by (eapply tmred_whnf_det; eauto).
  assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2r Hw3r Hnf2 Hnf3).
  assert (Hm : lequiv (gL G) (lmax l1 l2) (lmax k3 k4)) by now apply lequiv_max.
  exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
  - eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Hm] |].
    apply eqty_sym, HP23.
  - exact (geq_tm_leq_r Heq1 (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP13) Hm) Ew).
  - exact (geq_tm_leq_r Heq1' (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP23) Hm) Ew).
  - intros ρ a a' ha la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5.
    pose proof (HK1 ρ a a' ha la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5) as X1.
    destruct (bin_leq_ann ρ A5 B5 HA5 HB5) as [HA35 HB35].
    assert (Hla3 : lequiv (gL G) la' k3) by (eapply lequiv_trans; [exact Hla' | exact Q13]).
    assert (Hlb3 : lequiv (gL G) lb' k4) by (eapply lequiv_trans; [exact Hlb' | exact Q24]).
    pose proof (HK3 ρ a' a' (H13 ρ a a' ha) la' lb' la' lb' A5 B5 A5 B5 Hla3 Hlb3 Hla3 Hlb3
                  HA35 HB35 HA35 HB35) as X3.
    refine (Lcod ρ a a' ha _ _ _ _ X1 X3 _).
    cbn; repeat split; auto using ktm_leq, leqv_refl, ty_leq_refl, tm_leq_refl.
Qed.

Lemma SigRel_leq
  (Ldom : forall ρ x y z, domR1 ρ x y -> domR3 ρ z z -> tm_leq y z -> domR1 ρ x z)
  (Lcod : forall ρ x y z (h1 : domR1 ρ x y) (h3 : domR3 ρ z z) (h : domR1 ρ x z) u v w,
     codR1 ρ x y h1 u v -> codR3 ρ z z h3 w w -> tm_leq y z -> tm_leq v w -> codR1 ρ x z h u w) t1 t2 t3 :
  SigRel G Γ l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 t1 t2 ->
  SigRel G Γ k3 k4 k3 k4 A3 B3 A3 B3 domR3 codR3 t3 t3 -> tm_leq t2 t3 ->
  SigRel G Γ l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 t1 t3.
Proof using EL HA1 HA12 HA13 HA2 HA3 HB12 HB13 Hw1 Q13 Q24 Q31 Q42.
  intros H12 H33 Et.
  pose proof (geq_ty_sound (geq_ty_sig Q13 Q24 HA1 HA13 HB13)) as HP13.
  pose proof (geq_ty_sound (geq_ty_trans (geq_ty_sym (geq_ty_sig (lequiv_sym _ _ _ Q31) (lequiv_sym _ _ _ Q42) HA1 HA12 HB12))
                              (geq_ty_sig Q13 Q24 HA1 HA13 HB13))) as HP23.
  destruct H12 as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
  destruct H33 as (w3 & w3' & Hw3r & Hw3r' & Hnf3 & Hnf3' & Heq3 & _ & HK3).
  assert (w3' = w3) as -> by (eapply tmred_whnf_det; eauto).
  assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2r Hw3r Hnf2 Hnf3).
  assert (Hm : lequiv (gL G) (lmax l1 l2) (lmax k3 k4)) by now apply lequiv_max.
  exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
  - eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Hm] |].
    apply eqty_sym, HP23.
  - exact (geq_tm_leq_r Heq1 (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP13) Hm) Ew).
  - exact (geq_tm_leq_r Heq1' (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP23) Hm) Ew).
  - intros ρ la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5.
    destruct (HK1 ρ la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5) as [h1 C1].
    destruct (bin_leq_ann ρ A5 B5 HA5 HB5) as [HA35 HB35].
    assert (Hla3 : lequiv (gL G) la' k3) by (eapply lequiv_trans; [exact Hla' | exact Q13]).
    assert (Hlb3 : lequiv (gL G) lb' k4) by (eapply lequiv_trans; [exact Hlb' | exact Q24]).
    destruct (HK3 ρ la' lb' la' lb' A5 B5 A5 B5 Hla3 Hlb3 Hla3 Hlb3 HA35 HB35 HA35 HB35) as [h3 C3].
    assert (Ef : tm_leq (tmFst la' lb' A5 B5 (ktm ρ w2)) (tmFst la' lb' A5 B5 (ktm ρ w3)))
      by (cbn; repeat split; auto using ktm_leq, leqv_refl, ty_leq_refl).
    assert (Es : tm_leq (tmSnd la' lb' A5 B5 (ktm ρ w2)) (tmSnd la' lb' A5 B5 (ktm ρ w3)))
      by (cbn; repeat split; auto using ktm_leq, leqv_refl, ty_leq_refl).
    pose proof (Ldom ρ _ _ _ h1 h3 Ef) as h. exists h.
    exact (Lcod ρ _ _ _ h1 h3 h _ _ _ C1 C3 Ef Es).
Qed.

End BinLeq.

(** ** [M]'s relation with an [≡ₗ]-related right-hand side (M18b)

    As [MRn_trans] (Transitivity.v), the second pair replaced by the
    third signature's self-relation: [out]'s observations by
    [SigRel_leq] at the second's annotations, the children's functions by
    [PiRel_leq], whose codomain is the induction hypothesis on the
    children, and then moved from the second's right shape to the third's
    by irrelevance. The equalities come from the first signature against
    the third ([σ1] against [σ3], at the first pair's relations), which
    [LR_leq_step] builds from the induction hypotheses. *)
Section MLeq.

Lemma ktyll_leq {G Γ} (ρ : kwk G Γ) T T' : ty_leq T T' -> ty_leq (ktyll ρ T) (ktyll ρ T').
Proof using . intros H; unfold ktyll; apply (proj1 leq_ren_all), ty_leq_gwa, H. Qed.
Lemma ktmlll_leq {G Γ} (ρ : kwk G Γ) t t' : tm_leq t t' -> tm_leq (ktmlll ρ t) (ktmlll ρ t').
Proof using . intros H; unfold ktmlll; apply (proj1 (proj2 leq_ren_all)), tm_leq_gwa, H. Qed.

(** The first signature against the third, from the first pair's and the
    third's self-equality: the third's moved to the first's contexts
    entry by entry. *)
Lemma MGeq_leq {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3} :
  MGeq G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' -> MGeq G Γ s1 s2 si X3 A3 B3 C3 s1 s2 si X3 A3 B3 C3 ->
  lequiv (gL G) l1 s1 -> lequiv (gL G) l2 s2 -> lequiv (gL G) li si ->
  ty_leq X' X3 -> ty_leq A' A3 -> ty_leq B' B3 -> tm_leq C' C3 ->
  MGeq G Γ l1 l2 li X A B C s1 s2 si X3 A3 B3 C3.
Proof using EL.
  intros (_ & _ & _ & HS & HXX & HAA & HBB & HCC) (_ & _ & _ & HS3 & HXX3 & HAA3 & HBB3 & HCC3) Q1 Q2 Qi EX EA EB EC.
  pose proof HS as (W1 & W2 & Wi & HX & HA & HB & HC).
  pose proof HS3 as (V1 & V2 & Vi & HX3 & HA3 & HB3 & HC3).
  pose proof (lequiv_sym _ _ _ Q1) as Q1'. pose proof (lequiv_sym _ _ _ Q2) as Q2'.
  pose proof (lequiv_sym _ _ _ Qi) as Qi'.
  pose proof (eqc_refl _ _ _ (ctx_of_ty HX)) as P0.
  assert (GX : [ G ; Γ ⊢ X ≈ X3 @ li ]) by exact (geq_ty_leq_r HXX (geq_ty_lconv HXX3 Qi) EX).
  assert (P1 : [ G ⊢[ ge_layer ] Γ ,, X3 @ si ≅ Γ ,, X @ li ])
    by exact (eqc_ext _ _ _ _ _ _ _ _ P0 HX3
                (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (geq_ty_sound GX)) Qi') Qi').
  assert (P1' : [ G ⊢[ ge_layer ] Γ ,, X @ li ≅ Γ ,, X3 @ si ])
    by exact (eqc_ext _ _ _ _ _ _ _ _ P0 HX (geq_ty_sound GX) Qi).
  assert (GA : [ G ; Γ ,, X @ li ⊢ A ≈ A3 @ l1 ])
    by exact (geq_ty_leq_r HAA (geq_ty_lconv (geq_ty_ctxeq P1 HAA3) Q1) EA).
  assert (P2 : [ G ⊢[ ge_layer ] Γ ,, X3 @ si ,, A3 @ s1 ≅ Γ ,, X @ li ,, A @ l1 ]).
  { refine (eqc_ext _ _ _ _ _ _ _ _ P1 HA3 _ Q1').
    exact (eqty_lconv _ _ _ _ _ _ _ (geq_ty_sound (geq_ty_ctxeq P1' (geq_ty_sym GA))) Q1'). }
  assert (P2' : [ G ⊢[ ge_layer ] Γ ,, X @ li ,, A @ l1 ≅ Γ ,, X3 @ si ,, A3 @ s1 ])
    by exact (eqc_ext _ _ _ _ _ _ _ _ P1' HA (geq_ty_sound GA) Q1).
  assert (GB : [ G ; Γ ,, X @ li ,, A @ l1 ⊢ B ≈ B3 @ l2 ])
    by exact (geq_ty_leq_r HBB (geq_ty_lconv (geq_ty_ctxeq P2 HBB3) Q2) EB).
  assert (P3 : [ G ⊢[ ge_layer ] Γ ,, X3 @ si ,, A3 @ s1 ,, B3 @ s2 ≅ Γ ,, X @ li ,, A @ l1 ,, B @ l2 ]).
  { refine (eqc_ext _ _ _ _ _ _ _ _ P2 HB3 _ Q2').
    exact (eqty_lconv _ _ _ _ _ _ _ (geq_ty_sound (geq_ty_ctxeq P2' (geq_ty_sym GB))) Q2'). }
  assert (EX3 : [ G ; Γ ,, X @ li ,, A @ l1 ,, B @ l2 ⊢g X3⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wk3_eqty; [exact ge_typeof | exact (ctx_of_wf_tm ge_typeof HC)
                         | exact (eqty_sym _ _ _ _ _ _ (geq_ty_sound GX))]).
  refine (conj Q1 (conj Q2 (conj Qi (conj HS (conj GX (conj GA (conj GB _))))))).
  exact (geq_tm_leq_r HCC (geq_tm_conv (geq_tm_lconv (geq_tm_ctxeq P3 HCC3) Qi) EX3) EC).
Qed.

(** The hypotheses: the first signature against the second and against
    the third (at the same relations), the third against itself, the
    indices, [≡ₗ] of the second's index and child index to the third's,
    and what the relations' irrelevance and level invariance give (the
    induction hypotheses at [LRm]'s premises). *)
Definition MLeqHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3
    (I1 I3 : DomRel G Γ) (S1 S3 : MShRel G Γ) (P1 P3 : MPosRel G Γ) (m m' m3 : tm) : Prop :=
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' I1 S1 P1 /\
  MSide G Γ l1 l2 li X A B C s1 s2 si X3 A3 B3 C3 I1 S1 P1 /\
  MSide G Γ s1 s2 si X3 A3 B3 C3 s1 s2 si X3 A3 B3 C3 I3 S3 P3 /\
  nftm m /\ nftm m' /\ nftm m3 /\
  (forall ρ, I1 ρ (ktm ρ m) (ktm ρ m')) /\ (forall ρ, I1 ρ (ktm ρ m) (ktm ρ m3)) /\
  (forall ρ, I3 ρ (ktm ρ m3) (ktm ρ m3)) /\
  tm_leq m' m3 /\ tm_leq C' C3 /\
  MShIrr I1 S1 /\ MPosIrr I1 S1 P1 /\
  (forall ρ x y z a b c, I1 ρ x y -> I3 ρ z z -> tm_leq y z -> S1 ρ x y a b -> S3 ρ z z c c -> tm_leq b c ->
     S1 ρ x y a c) /\
  (forall ρ x y z a b c p q, I1 ρ x y -> I3 ρ z z -> tm_leq y z -> S1 ρ x y a b -> S3 ρ z z c c ->
     tm_leq b c -> P1 ρ x y a b p q -> P3 ρ z z c c q q) /\
  (forall ρ x y z a b c p q r, I1 ρ x y -> I3 ρ z z -> tm_leq y z -> S1 ρ x y a b -> S3 ρ z z c c ->
     tm_leq b c -> P1 ρ x y a b p q -> P3 ρ z z c c r r -> tm_leq q r -> P1 ρ x y a b p r).

Lemma MLeqHyps_kw {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3
    I1 I3 S1 S3 P1 P3 m m' m3} (ρ : kwk G Γ) :
  MLeqHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3 I1 I3 S1 S3 P1 P3 m m' m3 ->
  MLeqHyps (kw_G ρ) (kw_Δ ρ) l1 l2 li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C)
    r1 r2 ri (kty ρ X') (ktyl ρ A') (ktyll ρ B') (ktmlll ρ C')
    s1 s2 si (kty ρ X3) (ktyl ρ A3) (ktyll ρ B3) (ktmlll ρ C3)
    (fun ρ' => I1 (kw_comp ρ ρ')) (fun ρ' => I3 (kw_comp ρ ρ')) (fun ρ' => S1 (kw_comp ρ ρ'))
    (fun ρ' => S3 (kw_comp ρ ρ')) (fun ρ' => P1 (kw_comp ρ ρ')) (fun ρ' => P3 (kw_comp ρ ρ'))
    (ktm ρ m) (ktm ρ m') (ktm ρ m3).
Proof using EL.
  intros (HM1 & HM13 & HM3 & _ & _ & _ & I1m & I13m & I3m & Em & EC & Si & Pi & Sl & P13 & Pl).
  refine (conj (MSide_kw ρ HM1) (conj (MSide_kw ρ HM13) (conj (MSide_kw ρ HM3) (conj _ (conj _ (conj _
            (conj (MIdx_kw ρ I1m) (conj (MIdx_kw ρ I13m) (conj (MIdx_kw ρ I3m) _))))))))).
  1-3: kw_nf.
  refine (conj (ktm_leq ρ _ _ Em) (conj (ktmlll_leq ρ _ _ EC)
            (conj (MShIrr_kw ρ Si) (conj (MPosIrr_kw ρ Pi) (conj _ (conj _ _)))))).
  - intros ρ'. exact (Sl _).
  - intros ρ'. exact (P13 _).
  - intros ρ'. exact (Pl _).
Qed.

(** The hypotheses at a child: the first pair's at the second's shape
    and position, the composite's at the third's shape, the third's at its
    shape and the second's position. *)
Lemma MLeqHyps_child {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3
    I1 I3 S1 S3 P1 P3 m m' m3} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a b c p p' :
  MLeqHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3 I1 I3 S1 S3 P1 P3 m m' m3 ->
  S1 ρ (ktm ρ m) (ktm ρ m') a b -> S1 ρ (ktm ρ m) (ktm ρ m3) a c -> S3 ρ (ktm ρ m3) (ktm ρ m3) c c ->
  tm_leq b c ->
  P1 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' b) p p' ->
  P1 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m3) (ktm ρ' a) (ktm ρ' c) p p' ->
  P3 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m3) (ktm (kw_comp ρ ρ') m3) (ktm ρ' c) (ktm ρ' c) p' p' ->
  MLeqHyps (kw_G ρ') (kw_Δ ρ')
    l1 l2 li (kty (kw_comp ρ ρ') X) (ktyl (kw_comp ρ ρ') A) (ktyll (kw_comp ρ ρ') B) (ktmlll (kw_comp ρ ρ') C)
    r1 r2 ri (kty (kw_comp ρ ρ') X') (ktyl (kw_comp ρ ρ') A') (ktyll (kw_comp ρ ρ') B') (ktmlll (kw_comp ρ ρ') C')
    s1 s2 si (kty (kw_comp ρ ρ') X3) (ktyl (kw_comp ρ ρ') A3) (ktyll (kw_comp ρ ρ') B3)
      (ktmlll (kw_comp ρ ρ') C3)
    (fun ρ'' => I1 (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => I3 (kw_comp (kw_comp ρ ρ') ρ''))
    (fun ρ'' => S1 (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => S3 (kw_comp (kw_comp ρ ρ') ρ''))
    (fun ρ'' => P1 (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => P3 (kw_comp (kw_comp ρ ρ') ρ''))
    (ktmlll (kw_comp ρ ρ') C)[lsingle3 (ktm (kw_comp ρ ρ') m) (ktm ρ' a) p]
    (ktmlll (kw_comp ρ ρ') C')[lsingle3 (ktm (kw_comp ρ ρ') m') (ktm ρ' b) p']
    (ktmlll (kw_comp ρ ρ') C3)[lsingle3 (ktm (kw_comp ρ ρ') m3) (ktm ρ' c) p'].
Proof using EL.
  intros (HM1 & HM13 & HM3 & Nm & Nm' & Nm3 & I1m & I13m & I3m & Em & EC & Si & Pi & Sl & P13 & Pl)
    h1 h13 h3 Eb hp hp13 hp3.
  destruct (MSide_child ρ ρ' a b p p' HM1 Nm Nm' I1m h1 hp) as (N1 & N2 & J1).
  destruct (MSide_child ρ ρ' a c p p' HM13 Nm Nm3 I13m h13 hp13) as (_ & N3 & J13).
  destruct (MSide_child ρ ρ' c c p' p' HM3 Nm3 Nm3 I3m h3 hp3) as (_ & _ & J3).
  refine (conj (MSide_kw (kw_comp ρ ρ') HM1) (conj (MSide_kw (kw_comp ρ ρ') HM13)
            (conj (MSide_kw (kw_comp ρ ρ') HM3) (conj N1 (conj N2 (conj N3 (conj J1 (conj J13 (conj J3 _))))))))).
  refine (conj _ (conj (ktmlll_leq _ _ _ EC) (conj (MShIrr_kw (kw_comp ρ ρ') Si) (conj (MPosIrr_kw (kw_comp ρ ρ') Pi) (conj _ (conj _ _)))))).
  - apply (proj1 (proj2 leq_subst_all)); [| exact (ktmlll_leq _ _ _ EC)].
    unfold lsingle3, lsingle2; cbn; repeat split; auto using ktm_leq, tm_leq_refl.
  - intros ρ''. exact (Sl _).
  - intros ρ''. exact (P13 _).
  - intros ρ''. exact (Pl _).
Qed.

(** One instance at a depth. *)
Definition MLeqAt n := forall G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3
    I1 I3 S1 S3 P1 P3 m m' m3,
  MLeqHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3 I1 I3 S1 S3 P1 P3 m m' m3 ->
  forall t1 t2 t3,
    MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' t1 t2 ->
    MRn n G Γ s1 s2 si X3 A3 B3 C3 s1 s2 si X3 A3 B3 C3 S3 P3 m3 m3 t3 t3 -> tm_leq t2 t3 ->
    MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' t1 t3.

Lemma MPi_leq n (IH : MLeqAt n) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3
    I1 I3 S1 S3 P1 P3 m m' m3}
    (H : MLeqHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3 I1 I3 S1 S3 P1 P3 m m' m3)
    (ρ : kwk G Γ) a b c (h1 : S1 ρ (ktm ρ m) (ktm ρ m') a b) (h3 : S3 ρ (ktm ρ m3) (ktm ρ m3) c c)
    (h : S1 ρ (ktm ρ m) (ktm ρ m') a c) (Eb : tm_leq b c) u v w :
  MKidRel n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' ρ a b u v ->
  MKidRel n G Γ s1 s2 si X3 A3 B3 C3 s1 s2 si X3 A3 B3 C3 S3 P3 m3 m3 ρ c c w w -> tm_leq v w ->
  MKidRel n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' ρ a c u w.
Proof using EL.
  pose proof H as (HM1 & HM13 & HM3 & Nm & Nm' & Nm3 & I1m & I13m & I3m & Em & EC & Si & Pi & Sl & P13 & Pl).
  pose proof (ms_geq HM1) as HG1. pose proof (ms_geq HM13) as HG13.
  pose proof HG1 as (Hr1 & Hr2 & Hri & (W1 & W2 & Wi & _) & _).
  pose proof HG13 as (Hs1 & Hs2 & Hsi & _).
  assert (Hm : lequiv (gL G) (mlvl l1 l2 li) (mlvl r1 r2 ri)) by (apply lequiv_mlvl; assumption).
  assert (Hm3 : lequiv (gL G) (mlvl l1 l2 li) (mlvl s1 s2 si)) by (apply lequiv_mlvl; assumption).
  assert (h13 : S1 ρ (ktm ρ m) (ktm ρ m3) a c) by exact (proj1 (Si ρ _ _ _ (I1m ρ) (I13m ρ) a c) h).
  unfold MKidRel. rewrite !kw_B_single, !kw_mKid. rewrite !mKid_single by kw_nf.
  intros Y1 Y3 Ev.
  (* the families at the three shapes *)
  pose proof (ms_gBa HM1 ρ _ _ a b (I1m ρ) h1) as GB1.
  pose proof (ms_gBa HM1 ρ _ _ a c (I1m ρ) h) as GB1'.
  pose proof (ms_gBa HM13 ρ _ _ a c (I13m ρ) h13) as GB13.
  pose proof (geq_ty_sound GB1) as DB1. pose proof (geq_ty_sound GB1') as DB1'.
  pose proof (geq_ty_sound GB13) as DB13.
  pose proof (eqty_wf_l ge_typeof DB1) as HB.
  pose proof (eqty_wf_r ge_typeof DB1) as HBb. pose proof (eqty_wf_r ge_typeof DB1') as HBc.
  pose proof (eqty_wf_r ge_typeof DB13) as HB3.
  pose proof (ext_wf_g HB (kw_lwf ρ W2)) as HΔB.
  pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG1) HΔB) (ms_gCa HM1 ρ _ _ a b (I1m ρ) h1)) as K1.
  pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG1) HΔB) (ms_gCa HM1 ρ _ _ a c (I1m ρ) h)) as K1'.
  pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG13) HΔB) (ms_gCa HM13 ρ _ _ a c (I13m ρ) h13)) as K13.
  (* the shapes in the positions' worlds *)
  assert (Sab : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
             S1 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' b)).
  { intros ρ'. rewrite !(ktm_comp ρ ρ'). exact (ms_shmon HM1 ρ ρ' _ _ _ _ (I1m ρ) h1). }
  assert (Sac : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
             S1 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' c)).
  { intros ρ'. rewrite !(ktm_comp ρ ρ'). exact (ms_shmon HM1 ρ ρ' _ _ _ _ (I1m ρ) h). }
  assert (Sac3 : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
             S1 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m3) (ktm ρ' a) (ktm ρ' c)).
  { intros ρ'. rewrite !(ktm_comp ρ ρ'). exact (ms_shmon HM13 ρ ρ' _ _ _ _ (I13m ρ) h13). }
  assert (Scc : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
             S3 (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m3) (ktm (kw_comp ρ ρ') m3) (ktm ρ' c) (ktm ρ' c)).
  { intros ρ'. rewrite !(ktm_comp ρ ρ'). exact (ms_shmon HM3 ρ ρ' _ _ _ _ (I3m ρ) h3). }
  (* at the second's shape [b], then at the third's [c] by irrelevance *)
  refine (PiRel_dir (kw_lwf ρ W2) HB HBb HBc GB1 GB1' K1 K1' _ _ _ u w
            (PiRel_leq (kw_lequiv ρ (lequiv_sym _ _ _ Hr2)) (kw_lequiv ρ (lequiv_sym _ _ _ Hm))
               (kw_lequiv ρ Hs2) (kw_lequiv ρ Hm3) (kw_lwf ρ W2) HB HBb (lconv_ty HB3 (kw_lequiv ρ Hs2))
               GB1 GB13 K1 K13 _ _ u v w Y1 Y3 Ev)).
  - eapply (eqty_trans _ _ _ _ (tyPi l2 (mlvl l1 l2 li) (ktyll ρ B)[lsingle2 (ktm ρ m) a]
        (tyM l1 l2 li (kty ρ X)⟨↑⟩ (ktyl ρ A)⟨rlift ↑⟩ (ktyll ρ B)⟨rlift (rlift ↑)⟩
           (ktmlll ρ C)⟨rlift (rlift (rlift ↑))⟩ (ktmlll ρ C)[llift (lsingle2 (ktm ρ m) a)])));
      [apply eqty_sym|]; apply geq_ty_sound, geq_ty_pi;
      first [ exact HB | exact GB1 | exact GB1' | exact K1 | exact K1'
            | apply kw_lequiv; assumption | apply lequiv_mlvl; apply kw_lequiv; assumption ].
  - intros ρ'. exact (Pi _ _ _ _ _ _ _ (I1m _) (I1m _) (Sab ρ') (Sac ρ')).
  - intros ρ' p p' hp hp'.
    destruct (MSide_child ρ ρ' a b p p' HM1 Nm Nm' I1m h1 hp) as (N1 & N2 & J1).
    destruct (MSide_child ρ ρ' a c p p' HM1 Nm Nm' I1m h hp') as (_ & N3 & J3).
    exact (MRn_irrel n (MIrrHyps_self (MSide_kw (kw_comp ρ ρ') HM1) (MShIrr_kw _ Si) (MPosIrr_kw _ Pi)
                         N1 N2 N3 J1 J3)).
  - intros ρ' p p' hp.
    exact (P13 _ _ _ _ _ _ _ p p' (I1m _) (I3m _) (ktm_leq _ _ _ Em) (Sab ρ') (Scc ρ') (ktm_leq _ _ _ Eb) hp).
  - (* the children: the induction hypothesis *)
    intros ρ' p p' hp hp3 x y z Z1 Z3 Ez.
    pose proof (proj1 (Pi _ _ _ _ _ _ _ (I1m _) (I13m _) (Sab ρ') (Sac3 ρ') p p') hp) as hp13.
    exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (MLeqHyps_child ρ ρ' a b c p p' H h1 h13 h3 Eb hp hp13 hp3) x y z Z1 Z3 Ez).
Qed.

(** The observations, given the children's: the second's annotations
    serve the third. *)
Lemma MObs_leq n (IH : MLeqAt n) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3
    I1 I3 S1 S3 P1 P3 m m' m3} :
  MLeqHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3 I1 I3 S1 S3 P1 P3 m m' m3 ->
  forall t1 t2 t3,
    MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' t1 t2 ->
    MObs (MRn n) G Γ s1 s2 si X3 A3 B3 C3 s1 s2 si X3 A3 B3 C3 S3 P3 m3 m3 t3 t3 -> tm_leq t2 t3 ->
    MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S1 P1 m m' t1 t3.
Proof using EL.
  intros H t1 t2 t3 H12 H33 Et.
  pose proof H as (HM1 & HM13 & HM3 & Nm & Nm' & Nm3 & I1m & I13m & I3m & Em & EC & Si & Pi & Sl & P13 & Pl).
  pose proof (ms_geq HM1) as HG1; pose proof (ms_geq HM13) as HG13.
  destruct (MSide_root HM1 Nm Nm' I1m) as (Em1 & EA1 & EB1 & EC1).
  destruct (MSide_root HM13 Nm Nm3 I13m) as (Em13 & EA13 & EB13 & EC13).
  pose proof HG1 as (Hr1 & Hr2 & Hri & (W1 & W2 & Wi & _) & _).
  pose proof HG13 as (Hs1 & Hs2 & Hsi & _ & HXX13 & _).
  assert (Hm : lequiv (gL G) (mlvl l1 l2 li) (mlvl r1 r2 ri)) by (apply lequiv_mlvl; assumption).
  assert (Hm3 : lequiv (gL G) (mlvl l1 l2 li) (mlvl s1 s2 si)) by (apply lequiv_mlvl; assumption).
  intros k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann'.
  (* the second's annotations, at the third signature *)
  assert (Ann3 : MAnn G Γ s1 s2 si X3 A3 B3 C3 m3 k1' k2' ki' X1' A1' B1' C1' j1').
  { refine (MAnn_conv (MEq_trans ge_typeof ge_notV (MEq_sym ge_typeof ge_notV (MEq_of_MGeq HG13))
                         (MEq_of_MGeq HG1)) _ Ann').
    eapply eqtm_lconv; [| exact (lequiv_sym _ _ _ Hsi)].
    eapply eqtm_conv; [| rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ (geq_ty_sound HXX13))].
    exact (geq_tm_sound (geq_tm_trans (geq_tm_sym Em13) Em1)). }
  specialize (H12 k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann').
  specialize (H33 k1' k2' ki' X1' A1' B1' C1' j1' k1' k2' ki' X1' A1' B1' C1' j1' Ann3 Ann3).
  pose proof (geq_ty_sound EA1) as DA1. pose proof (geq_ty_sound EA13) as DA13.
  refine (SigRel_leq (lequiv_sym _ _ _ Hr1) (lequiv_sym _ _ _ Hm) Hs1 Hm3 W1
            (eqty_wf_l ge_typeof DA1) (eqty_wf_r ge_typeof DA1) (lconv_ty (eqty_wf_r ge_typeof DA13) Hs1)
            EA1 EA13 (M_outB_geq HG1 EB1 EC1) (M_outB_geq HG13 EB13 EC13) _ _ _ _ _ H12 H33 _).
  - intros ρ x y z hxy hz Ey. exact (Sl ρ _ _ _ x y z (I1m ρ) (I3m ρ) (ktm_leq ρ _ _ Em) hxy hz Ey).
  - intros ρ x y z hxy hz h u v w Y1 Y3 Ey Ev. exact (MPi_leq n IH H ρ x y z hxy hz h Ey u v w Y1 Y3 Ev).
  - cbn; repeat split; auto using leqv_refl, ty_leq_refl, tm_leq_refl.
Qed.

Lemma MRn_leq n : MLeqAt n.
Proof using EL.
  induction n as [|n IH]; intros G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X3 A3 B3 C3
    I1 I3 S1 S3 P1 P3 m m' m3 H t1 t2 t3 H12 H33 Et.
  all: pose proof H as (HM1 & HM13 & _ & Nm & Nm' & Nm3 & I1m & I13m & _).
  all: pose proof (ms_geq HM1) as HG1; pose proof (ms_geq HM13) as HG13.
  all: destruct (MSide_root HM1 Nm Nm' I1m) as (Em1 & _).
  all: destruct (MSide_root HM13 Nm Nm3 I13m) as (Em13 & _).
  all: pose proof HG13 as (Hs1 & Hs2 & Hsi & _).
  all: assert (Hm3 : lequiv (gL G) (mlvl l1 l2 li) (mlvl s1 s2 si)) by (apply lequiv_mlvl; assumption).
  all: pose proof (geq_ty_sound (MGeq_M HG1 Em1)) as D12.
  all: pose proof (geq_ty_sound (MGeq_M HG13 Em13)) as D13.
  all: assert (D32 : [ G ; Γ ⊢g tyM s1 s2 si X3 A3 B3 C3 m3 ≅ tyM r1 r2 ri X' A' B' C' m' @ mlvl l1 l2 li ])
         by (eapply eqty_trans; [apply eqty_sym, D13 | exact D12]).
  all: destruct H12 as [(w1 & w2 & R1 & R2 & Wh1 & Wh2 & E1 & E1') H12].
  all: destruct H33 as [(w3 & w3' & R3 & R3' & Wh3 & Wh3' & E3 & _) H33].
  all: assert (w3' = w3) as -> by (eapply tmred_whnf_det; eauto).
  all: assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et R2 R3 Wh2 Wh3).
  all: split;
    [ exists w1, w3; refine (conj R1 (conj _ (conj Wh1 (conj Wh3 (conj _ _)))));
      [ eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact R3 | exact Hm3] | exact D32]
      | exact (geq_tm_leq_r E1 (geq_tm_conv_l E3 (eqty_sym _ _ _ _ _ _ D13) Hm3) Ew)
      | exact (geq_tm_leq_r E1' (geq_tm_conv_l E3 D32 Hm3) Ew) ] |].
  1: exact Logic.I.
  intros ρ. exact (MObs_leq n IH (MLeqHyps_kw ρ H) _ _ _ (H12 ρ) (H33 ρ) (ktm_leq ρ _ _ Et)).
Qed.

End MLeq.

(** ** Level invariance *)

Lemma LR_leq_step n : (forall m, m < n -> Pleq m) -> Pleq n.
Proof using EL VL.
  intros IHn G Γ T1 T2 l R H.
  induction H as [G Γ T1 T2 l R Hl HT1 HT2 HR
                 | G Γ T1 T2 l l1 l2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l V1 V2 R HT1 HT2 HV HR
                 | G Γ T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HA1 HA2 HB1 HB2 HA12 HB12] domAd1 IHdom codAd1 IHcod HR
                 | G Γ T1 T2 l R Hj HM
                 | G Γ T1 T2 l l1 l2 U1 U2 instR R Hj Hl Hl2 Hw1 HT1 HT2 HU1 HU2 Hgeq instAd IHinst HR
                 | G Γ T1 T2 l Δ1 Δ2 l1 l2 l3 l4 U1 U2 instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HΔ HU1 HU2
                     Hgeq instAd IHinst HR
                 | G Γ T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HA1 HA2 HB1 HB2 HA12 HB12] domAd1 IHdom codAd1 IHcod HR
                 | G Γ T1 T2 l l1 l2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hn HT1 HT2 HSA HSAA Hsaa Hsbb HR
                 | G Γ T1 T2 l s1 s2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hn HT1 HT2 HIA HIAA Hiaa Hibb
                     HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T1 T2 l s1 s2 R Hl Hl2 Hn HT1 HT2 HR
                 | G Γ T1 T2 l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T1 T2 l l1 l2 l3 l4 A1 B1 A2 B2 domR1 codR1 R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT1 HT2 HA1 HA2 HB1 HB2 HA12 HB12] domAd1 IHdom codAd1 IHcod HR
                 | G Γ T1 T2 l l1 l2 A1 A2 N1 N2 domR1 R Hl Hl2 Hw HT1 HT2 HA1 HA2 HN1t HN2t HA12 HN12
                     domAd1 IHdom arAd1 HR
                 | G Γ T1 T2 l l1 l2 A A' RQ R Hl Hl2 Hw HT1 HT2 HA HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T1 T2 l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                     HT1 HT2 HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                     widxAd IHwidx Hwisym Hwistr wdomAd IHwdom warAd wotAd wchAd wixAd HR
                 | G Γ T1 T2 l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                     Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT1 HT2 HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                     HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros T3 R3 H3 ET; destruct (LR_whnf_l H3) as (W3 & HT3 & Hnw3).
  - (* Nat *)
    pose proof (ty_leq_nat_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as ->.
    destruct (LR_inv_nat H3 HT3) as (_ & _ & HR3).
    split; [eapply LRnat; eauto|].
    intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
    eapply NatRel_leq; eauto.
  - (* U *)
    destruct (ty_leq_U_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as (l3 & -> & E3).
    destruct (LR_inv_U H3 HT3) as (l4 & _ & Hl4 & _ & _ & HR3).
    assert (Q : lequiv (gL G) l2 l3)
      by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) (lequiv_wf_r _ _ _ Hl4) E3).
    assert (Hl31 : lequiv (gL G) l3 l1) by (eapply lequiv_trans; [apply lequiv_sym, Q | exact Hl2]).
    split; [eapply (LRU n (LRbelow n) G Γ T1 T3 l l1 l3); eauto|].
    intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
    eapply URel_leq; eauto; try apply IHn; lia.
  - (* neutral *)
    pose proof (tyred_leq ET HT2 HT3 (whnf_ty_ne _ (gne_ty_whne_r HV)) Hnw3) as EW.
    pose proof (whne_ty_leq _ _ EW (gne_ty_whne_r HV)) as Hn3.
    destruct (LR_inv_ne H3 HT3 Hn3) as (V3 & _ & HV33 & HR3).
    pose proof (gne_ty_leq_r HV (gne_ty_refl_l HV33) EW) as HV13.
    assert (E23 : [ G ; Γ ⊢g V2 ≅ W3 @ l ])
      by exact (geq_ty_sound (gne_ty_geq (gne_ty_leq (gne_ty_refl_r HV) (gne_ty_refl_l HV33) EW))).
    split.
    + eapply LRne; [exact HT1 | exact HT3 | exact HV13 |].
      eapply releq_trans; [exact HR|]. intros t t'; split; apply NeRel_conv; [exact E23 | apply eqty_sym, E23].
    + intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
      eapply NeRel_leq; [apply eqty_sym, E23 | | | exact H12 | exact H33 | exact Et].
      * apply eqty_sym, geq_ty_sound, gne_ty_geq, HV13.
      * apply eqty_sym, geq_ty_sound, gne_ty_geq, HV33.
  - (* Π *)
    destruct (ty_leq_pi_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (k3 & k4 & A3 & B3 & -> & E3 & E4 & EA & EB).
    destruct (LR_inv_pi H3 HT3) as (k3' & k4' & A3' & B3' & domR3 & codR3 &
      [_ _ _ Hwk3 Hwk4 _ HT3' HA3 _ HB3 _ HA33 HB33] & domAd3 & codAd3 & HR3).
    assert (Heq : tyPi k3' k4' A3' B3' = tyPi k3 k4 A3 B3)
      by (eapply tyred_whnf_det; [exact HT3' | exact HT3 | eauto with whnf | eauto with whnf]).
    injection Heq as -> -> -> ->. clear HT3'.
    assert (HΓ : [ G ; Γ ⊢g ]) by exact (ctx_of_ty HA1).
    (* levels *)
    assert (Q3 : lequiv (gL G) l3 k3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl3) Hwk3 E3).
    assert (Q4 : lequiv (gL G) l4 k4) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl4) Hwk4 E4).
    assert (Q13 : lequiv (gL G) l1 k3) by (eapply lequiv_trans; [apply lequiv_sym, Hl3 | exact Q3]).
    assert (Q24 : lequiv (gL G) l2 k4) by (eapply lequiv_trans; [apply lequiv_sym, Hl4 | exact Q4]).
    (* the domains *)
    assert (Hdom3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A1) (kty ρ A3) l1 (domR1 ρ))
      by (intros ρ; exact (proj1 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13))
                                     (kty_leq ρ _ _ EA)))).
    assert (Hrefl : forall ρ a a', domR1 ρ a a' -> domR1 ρ a' a').
    { intros ρ a a' ha. exact (LR_tm_refl_l _ _ _ _ _ _ _ a' a (LR_sym _ _ _ _ _ _ _ (domAd1 ρ)) ha). }
    assert (H13 : forall ρ a a', domR1 ρ a a' -> domR3 ρ a' a').
    { intros ρ a a' ha.
      pose proof (LR_irrel _ _ _ _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ (Hdom3 ρ))
                    (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13)) a' a') as X.
      exact (proj1 X (Hrefl ρ a a' ha)). }
    assert (Hcodirr : forall ρ a a1 a2 (h1 : domR1 ρ a a1) (h2 : domR1 ρ a a2),
               releq (codR1 ρ a a1 h1) (codR1 ρ a a2 h2))
      by (intros; eapply LR_irrel; [apply codAd1 | apply codAd1]).
    assert (Hcod3 : forall ρ a a' (ha : domR1 ρ a a'),
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ B3)[lsingle a'] (ktyl ρ B3)[lsingle a'] l2
                  (codR3 ρ a' a' (H13 ρ a a' ha)))
      by (intros; exact (LR_lconv _ _ _ _ _ _ _ _ _ (codAd3 _ _ _ _) (kw_lequiv ρ Q24))).
    assert (Ecod : forall (ρ : kwk G Γ) a', ty_leq (ktyl ρ B2)[lsingle a'] (ktyl ρ B3)[lsingle a'])
      by (intros; apply subst_leq_ty, ktyl_leq, EB).
    (* generic and declarative facts *)
    assert (HA3' : [ G ; Γ ⊢g A3 @ l1 ]) by exact (lconv_ty HA3 (lequiv_sym _ _ _ Q13)).
    assert (HA23 : [ G ; Γ ⊢ A2 ≈ A3 @ l1 ])
      by exact (geq_ty_leq (geq_ty_refl_r HA12) (geq_ty_lconv HA33 Q13) EA).
    assert (HA13 : [ G ; Γ ⊢ A1 ≈ A3 @ l1 ]) by exact (geq_ty_trans HA12 HA23).
    assert (HB33' : [ G ; Γ ,, A1 @ l1 ⊢ B3 ≈ B3 @ l2 ]).
    { eapply geq_ty_lconv; [|exact Q24].
      eapply geq_ty_ctxconv; [| apply lequiv_sym, Q13 | apply ext_wf_g; [exact HA1 | exact Hw1] | exact HB33].
      eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA13 | apply lequiv_sym, Q13]. }
    assert (HB23 : [ G ; Γ ,, A1 @ l1 ⊢ B2 ≈ B3 @ l2 ])
      by exact (geq_ty_leq (geq_ty_refl_r HB12) HB33' EB).
    assert (HB13 : [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B3 @ l2 ]) by exact (geq_ty_trans HB12 HB23).
    assert (HP12 : [ G ; Γ ⊢ tyPi l1 l2 A1 B1 ≈ tyPi l3 l4 A2 B2 @ lmax l1 l2 ])
      by (apply geq_ty_pi; auto using lequiv_sym).
    assert (HP13 : [ G ; Γ ⊢ tyPi l1 l2 A1 B1 ≈ tyPi k3 k4 A3 B3 @ lmax l1 l2 ])
      by (apply geq_ty_pi; auto).
    pose proof (geq_ty_sound (geq_ty_trans (geq_ty_sym HP12) HP13)) as HP23d.
    pose proof (geq_ty_sound HP13) as HP13d.
    assert (HR13 : releq R (PiRel G Γ l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1)).
    { assert (Hd : forall ρ, releq (domR1 ρ) (domR1 ρ)) by (intros; apply releq_refl).
      assert (Hc : forall ρ a a' (ha ha' : domR1 ρ a a'), releq (codR1 ρ a a' ha) (codR1 ρ a a' ha'))
        by (intros; apply Hcodirr).
      eapply releq_trans; [exact HR|]. intros t t'; split.
      - exact (PiRel_dir Hw1 HA1 HA2 HA3' HA12 HA13 HB12 HB13 HP23d Hd Hc t t').
      - exact (PiRel_dir Hw1 HA1 HA3' HA2 HA13 HA12 HB13 HB12 (eqty_sym _ _ _ _ _ _ HP23d) Hd Hc t t'). }
    split.
    + apply (LRpi n (LRbelow n) G Γ T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1 R); [split|..].
      * exact Hl.
      * apply lequiv_sym, Q13.
      * apply lequiv_sym, Q24.
      * exact Hw1.
      * exact Hw2.
      * exact HT1.
      * exact HT3.
      * exact HA1.
      * exact HA3'.
      * exact HB1.
      * eapply (lconv_ty (l := k4)); [|apply lequiv_sym, Q24].
        eapply ctx_lvl_ty; [exact HA3 | apply lequiv_sym, Q13 | exact HB3].
      * exact HA13.
      * exact HB13.
      * exact Hdom3.
      * intros ρ a a' ha. exact (proj1 (IHcod ρ a a' ha _ _ (Hcod3 ρ a a' ha) (Ecod ρ a'))).
      * exact HR13.
    + (* terms *)
      intros t1 t2 t3 H12' H33' Et. apply HR. apply HR in H12'. apply HR3 in H33'.
      refine (PiRel_leq Hl3 Hl4 Q13 Q24 Hw1 HA1 HA2 HA3 HA12 HA13 HB12 HB13 H13 _ _ _ _ H12' H33' Et).
      intros ρ a a' ha h3 u v w X1 X3 Ev.
      exact (proj2 (IHcod ρ a a' ha _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (codAd3 ρ a' a' h3) (kw_lequiv ρ Q24))
                      (Ecod ρ a')) _ _ _ X1 X3 Ev).
  - (* contextual types *)
    assert (HM3 : ModRel G Γ T3 T3 l R3).
    { destruct (ModRel_red_r HM) as [(Δ & k & HT2) | (Δ & A & k & HT2)];
        pose proof (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3) as EW;
        destruct W3; cbn in EW; try contradiction.
      - exact (proj2 (LR_inv_CTyp H3 HT3)).
      - exact (proj2 (LR_inv_CTrm H3 HT3)). }
    destruct (ModRel_trans (ModRel_sym HM) HM) as [HM22 Hc22].
    destruct (ModRel_bridge HM22 HM3 ET) as [HM23 Hb].
    destruct (ModRel_trans HM HM23) as [HM13 Hc13].
    split; [apply LRmod; [exact Hj | exact HM13]|].
    intros t1 t2 t3 H12 H33 Et.
    exact (Hc13 t1 t2 t3 H12 (Hb t2 t3 (Hc22 t2 t1 t2 H12 H12) H33 Et)).
  - (* CΠ *)
    destruct (ty_leq_cpi_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as (k3 & U3 & -> & E3 & EU).
    destruct (LR_inv_cpi H3 HT3) as (m3 & U3' & instR3 & _ & _ & _ & Hwk3 & HT3' & HU3 & _ & Hgeq3 &
      instAd3 & HR3).
    assert (Heq : tyCPi m3 U3' = tyCPi k3 U3)
      by (eapply tyred_whnf_det; [exact HT3' | exact HT3 | eauto with whnf | eauto with whnf]).
    injection Heq as -> ->. clear HT3'.
    assert (Q3 : lequiv (gL G) l2 k3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hwk3 E3).
    assert (Q13 : lequiv (gL G) l1 k3) by (eapply lequiv_trans; [apply lequiv_sym, Hl2 | exact Q3]).
    assert (Hdiag : forall (ρ : kwk G Γ) Δ Δ', vp_ctx lr_vp (kw_G ρ) Δ Δ' -> vp_ctx lr_vp (kw_G ρ) Δ' Δ')
      by (intros ρ Δ Δ' h; exact (vpl_ctx_trans (vpl_ctx_sym h) h)).
    assert (Hinst3 : forall ρ Δ Δ' (h : vp_ctx lr_vp (kw_G ρ) Δ Δ'),
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kbody ρ U3)⦃gsingle (GCtx Δ')⦄ (kbody ρ U3)⦃gsingle (GCtx Δ')⦄
                  l1 (instR3 ρ Δ' Δ' (Hdiag ρ Δ Δ' h)))
      by (intros; exact (LR_lconv _ _ _ _ _ _ _ _ _ (instAd3 _ _ _ _) (kw_lequiv ρ Q13))).
    assert (Einst : forall (ρ : kwk G Γ) Δ', ty_leq (kbody ρ U2)⦃gsingle (GCtx Δ')⦄ (kbody ρ U3)⦃gsingle (GCtx Δ')⦄)
      by (intros; apply gsingle_leq_ty, kbody_leq, EU).
    assert (HP23 : [ G ; Γ ⊢ tyCPi l2 U2 ≈ tyCPi k3 U3 @ l1 ])
      by (apply geq_ty_leq; [exact (geq_ty_refl_r Hgeq) | exact (geq_ty_lconv Hgeq3 Q13) | cbn; auto]).
    pose proof (geq_ty_sound HP23) as HP23d.
    pose proof (geq_ty_sound (geq_ty_trans Hgeq HP23)) as HP13d.
    assert (HR13 : releq R (CPiRel G Γ l1 k3 U1 U3 instR)).
    { eapply releq_trans; [exact HR|]. intros t t'; split.
      - apply (CPiRel_dir HP23d); intros; apply releq_refl.
      - apply (CPiRel_dir (eqty_sym _ _ _ _ _ _ HP23d)); intros; apply releq_refl. }
    split.
    + apply (LRcpi n (LRbelow n) G Γ T1 T3 l l1 k3 U1 U3 instR R).
      * exact Hj.
      * exact Hl.
      * apply lequiv_sym, Q13.
      * exact Hw1.
      * exact HT1.
      * exact HT3.
      * exact HU1.
      * exact (lconv_ty HU3 (lequiv_sym _ _ _ Q13)).
      * exact (geq_ty_trans Hgeq HP23).
      * intros ρ Δ Δ' h. exact (proj1 (IHinst ρ Δ Δ' h _ _ (Hinst3 ρ Δ Δ' h) (Einst ρ Δ'))).
      * exact HR13.
    + intros t1 t2 t3 H12' H33' Et. apply HR. apply HR in H12'. apply HR3 in H33'.
      destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
      destruct H33' as (w3 & w3' & Hw3r & Hw3r' & Hnf3 & Hnf3' & Heq3 & _ & HK3).
      assert (w3' = w3) as -> by (eapply tmred_whnf_det; eauto).
      assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2r Hw3r Hnf2 Hnf3).
      exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
      * eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Q13] |].
        apply eqty_sym, HP23d.
      * exact (geq_tm_leq_r Heq1 (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP13d) Q13) Ew).
      * exact (geq_tm_leq_r Heq1' (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP23d) Q13) Ew).
      * intros ρ Δ Δ' h.
        refine (proj2 (IHinst ρ Δ Δ' h _ _ (Hinst3 ρ Δ Δ' h) (Einst ρ Δ')) _ _ _ (HK1 ρ Δ Δ' h)
                  (HK3 ρ Δ' Δ' (Hdiag ρ Δ Δ' h)) _).
        cbn; split; [apply ktm_leq, Ew | apply (proj1 (proj2 (proj2 leq_refl_all)))].
  - (* TΠ *)
    destruct (ty_leq_tpi_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (Δ3 & k3 & k4 & U3 & -> & EΔ & E3 & E4 & EU).
    destruct (LR_inv_tpi H3 HT3) as (Δ3' & m3 & m4 & U3' & instR3 & _ & _ & _ & _ & Hwk3 & Hwk4 & HT3' &
      HΔ33 & HU3 & _ & Hgeq3 & instAd3 & HR3).
    assert (Heq : tyTPi Δ3' m3 m4 U3' = tyTPi Δ3 k3 k4 U3)
      by (eapply tyred_whnf_det; [exact HT3' | exact HT3 | eauto with whnf | eauto with whnf]).
    injection Heq as -> -> -> ->. clear HT3'.
    assert (Q3 : lequiv (gL G) l3 k3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl3) Hwk3 E3).
    assert (Q4 : lequiv (gL G) l4 k4) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl4) Hwk4 E4).
    assert (Q13 : lequiv (gL G) l1 k3) by (eapply lequiv_trans; [apply lequiv_sym, Hl3 | exact Q3]).
    assert (Q24 : lequiv (gL G) l2 k4) by (eapply lequiv_trans; [apply lequiv_sym, Hl4 | exact Q4]).
    assert (HΔ23 : vp_ctx lr_vp G Δ2 Δ3)
      by exact (vpl_ctx_leq (vpl_ctx_trans (vpl_ctx_sym HΔ) HΔ) HΔ33 EΔ).
    pose proof (vpl_ctx_trans HΔ HΔ23) as HΔ13.
    assert (Hdiag : forall (ρ : kwk G Γ) A A', vp_ty lr_vp (kw_G ρ) Δ1⟦kw_γ ρ⟧ A A' l1 ->
                      vp_ty lr_vp (kw_G ρ) Δ3⟦kw_γ ρ⟧ A' A' k3)
      by (intros ρ A A' h;
          exact (vpl_ty_lconv (kw_lequiv ρ Q13)
                   (vpl_ty_ctx (vpl_ctx_gwk (kw_gok ρ) (kw_glob ρ) HΔ13) (vpl_ty_trans (vpl_ty_sym h) h)))).
    assert (Hinst3 : forall ρ A A' (h : vp_ty lr_vp (kw_G ρ) Δ1⟦kw_γ ρ⟧ A A' l1),
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kbody ρ U3)⦃gsingle (GTy A')⦄ (kbody ρ U3)⦃gsingle (GTy A')⦄
                  l2 (instR3 ρ A' A' (Hdiag ρ A A' h)))
      by (intros; exact (LR_lconv _ _ _ _ _ _ _ _ _ (instAd3 _ _ _ _) (kw_lequiv ρ Q24))).
    assert (Einst : forall (ρ : kwk G Γ) A', ty_leq (kbody ρ U2)⦃gsingle (GTy A')⦄ (kbody ρ U3)⦃gsingle (GTy A')⦄)
      by (intros; apply gsingle_leq_ty, kbody_leq, EU).
    assert (HP23 : [ G ; Γ ⊢ tyTPi Δ2 l3 l4 U2 ≈ tyTPi Δ3 k3 k4 U3 @ l2 ])
      by (apply geq_ty_leq; [exact (geq_ty_refl_r Hgeq) | exact (geq_ty_lconv Hgeq3 Q24) | cbn; auto]).
    pose proof (geq_ty_sound HP23) as HP23d.
    pose proof (geq_ty_sound (geq_ty_trans Hgeq HP23)) as HP13d.
    assert (HR13 : releq R (TPiRel G Γ Δ1 Δ3 l1 l2 k3 k4 U1 U3 instR)).
    { eapply releq_trans; [exact HR|]. intros t t'; split.
      - apply (TPiRel_dir HP23d); intros; apply releq_refl.
      - apply (TPiRel_dir (eqty_sym _ _ _ _ _ _ HP23d)); intros; apply releq_refl. }
    split.
    + apply (LRtpi n (LRbelow n) G Γ T1 T3 l Δ1 Δ3 l1 l2 k3 k4 U1 U3 instR R).
      * exact Hj.
      * exact Hl.
      * apply lequiv_sym, Q13.
      * apply lequiv_sym, Q24.
      * exact Hw1.
      * exact Hw2.
      * exact HT1.
      * exact HT3.
      * exact HΔ13.
      * exact HU1.
      * exact HU3.
      * exact (geq_ty_trans Hgeq HP23).
      * intros ρ A A' h. exact (proj1 (IHinst ρ A A' h _ _ (Hinst3 ρ A A' h) (Einst ρ A'))).
      * exact HR13.
    + intros t1 t2 t3 H12' H33' Et. apply HR. apply HR in H12'. apply HR3 in H33'.
      destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
      destruct H33' as (w3 & w3' & Hw3r & Hw3r' & Hnf3 & Hnf3' & Heq3 & _ & HK3).
      assert (w3' = w3) as -> by (eapply tmred_whnf_det; eauto).
      assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2r Hw3r Hnf2 Hnf3).
      exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
      * eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Q24] |].
        apply eqty_sym, HP23d.
      * exact (geq_tm_leq_r Heq1 (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP13d) Q24) Ew).
      * exact (geq_tm_leq_r Heq1' (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP23d) Q24) Ew).
      * intros ρ A A' h.
        refine (proj2 (IHinst ρ A A' h _ _ (Hinst3 ρ A A' h) (Einst ρ A')) _ _ _ (HK1 ρ A A' h)
                  (HK3 ρ A' A' (Hdiag ρ A A' h)) _).
        cbn; split; [apply ktm_leq, Ew | apply (proj1 leq_refl_all)].
  - (* Σ *)
    destruct (ty_leq_sig_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (k3 & k4 & A3 & B3 & -> & E3 & E4 & EA & EB).
    destruct (LR_inv_sig H3 HT3) as (k3' & k4' & A3' & B3' & domR3 & codR3 &
      [_ _ _ Hwk3 Hwk4 _ HT3' HA3 _ HB3 _ HA33 HB33] & domAd3 & codAd3 & HR3).
    assert (Heq : tySig k3' k4' A3' B3' = tySig k3 k4 A3 B3)
      by (eapply tyred_whnf_det; [exact HT3' | exact HT3 | eauto with whnf | eauto with whnf]).
    injection Heq as -> -> -> ->. clear HT3'.
    assert (HΓ : [ G ; Γ ⊢g ]) by exact (ctx_of_ty HA1).
    (* levels *)
    assert (Q3 : lequiv (gL G) l3 k3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl3) Hwk3 E3).
    assert (Q4 : lequiv (gL G) l4 k4) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl4) Hwk4 E4).
    assert (Q13 : lequiv (gL G) l1 k3) by (eapply lequiv_trans; [apply lequiv_sym, Hl3 | exact Q3]).
    assert (Q24 : lequiv (gL G) l2 k4) by (eapply lequiv_trans; [apply lequiv_sym, Hl4 | exact Q4]).
    (* the domains *)
    assert (Hdom3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A1) (kty ρ A3) l1 (domR1 ρ))
      by (intros ρ; exact (proj1 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13))
                                     (kty_leq ρ _ _ EA)))).
    assert (Hrefl : forall ρ a a', domR1 ρ a a' -> domR1 ρ a' a').
    { intros ρ a a' ha. exact (LR_tm_refl_l _ _ _ _ _ _ _ a' a (LR_sym _ _ _ _ _ _ _ (domAd1 ρ)) ha). }
    assert (H13 : forall ρ a a', domR1 ρ a a' -> domR3 ρ a' a').
    { intros ρ a a' ha.
      pose proof (LR_irrel _ _ _ _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ (Hdom3 ρ))
                    (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13)) a' a') as X.
      exact (proj1 X (Hrefl ρ a a' ha)). }
    assert (Hcodirr : forall ρ a a1 a2 (h1 : domR1 ρ a a1) (h2 : domR1 ρ a a2),
               releq (codR1 ρ a a1 h1) (codR1 ρ a a2 h2))
      by (intros; eapply LR_irrel; [apply codAd1 | apply codAd1]).
    assert (Hcod3 : forall ρ a a' (ha : domR1 ρ a a'),
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ B3)[lsingle a'] (ktyl ρ B3)[lsingle a'] l2
                  (codR3 ρ a' a' (H13 ρ a a' ha)))
      by (intros; exact (LR_lconv _ _ _ _ _ _ _ _ _ (codAd3 _ _ _ _) (kw_lequiv ρ Q24))).
    assert (Ecod : forall (ρ : kwk G Γ) a', ty_leq (ktyl ρ B2)[lsingle a'] (ktyl ρ B3)[lsingle a'])
      by (intros; apply subst_leq_ty, ktyl_leq, EB).
    (* generic and declarative facts *)
    assert (HA3' : [ G ; Γ ⊢g A3 @ l1 ]) by exact (lconv_ty HA3 (lequiv_sym _ _ _ Q13)).
    assert (HA23 : [ G ; Γ ⊢ A2 ≈ A3 @ l1 ])
      by exact (geq_ty_leq (geq_ty_refl_r HA12) (geq_ty_lconv HA33 Q13) EA).
    assert (HA13 : [ G ; Γ ⊢ A1 ≈ A3 @ l1 ]) by exact (geq_ty_trans HA12 HA23).
    assert (HB33' : [ G ; Γ ,, A1 @ l1 ⊢ B3 ≈ B3 @ l2 ]).
    { eapply geq_ty_lconv; [|exact Q24].
      eapply geq_ty_ctxconv; [| apply lequiv_sym, Q13 | apply ext_wf_g; [exact HA1 | exact Hw1] | exact HB33].
      eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA13 | apply lequiv_sym, Q13]. }
    assert (HB23 : [ G ; Γ ,, A1 @ l1 ⊢ B2 ≈ B3 @ l2 ])
      by exact (geq_ty_leq (geq_ty_refl_r HB12) HB33' EB).
    assert (HB13 : [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B3 @ l2 ]) by exact (geq_ty_trans HB12 HB23).
    assert (HP12 : [ G ; Γ ⊢ tySig l1 l2 A1 B1 ≈ tySig l3 l4 A2 B2 @ lmax l1 l2 ])
      by (apply geq_ty_sig; auto using lequiv_sym).
    assert (HP13 : [ G ; Γ ⊢ tySig l1 l2 A1 B1 ≈ tySig k3 k4 A3 B3 @ lmax l1 l2 ])
      by (apply geq_ty_sig; auto).
    pose proof (geq_ty_sound (geq_ty_trans (geq_ty_sym HP12) HP13)) as HP23d.
    pose proof (geq_ty_sound HP13) as HP13d.
    assert (HR13 : releq R (SigRel G Γ l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1)).
    { assert (Hd : forall ρ, releq (domR1 ρ) (domR1 ρ)) by (intros; apply releq_refl).
      assert (Hc : forall ρ a a' (ha ha' : domR1 ρ a a'), releq (codR1 ρ a a' ha) (codR1 ρ a a' ha'))
        by (intros; apply Hcodirr).
      eapply releq_trans; [exact HR|]. intros t t'; split.
      - exact (SigRel_dir Hw1 HA1 HA2 HA3' HA12 HA13 HB12 HB13 HP23d Hd Hc t t').
      - exact (SigRel_dir Hw1 HA1 HA3' HA2 HA13 HA12 HB13 HB12 (eqty_sym _ _ _ _ _ _ HP23d) Hd Hc t t'). }
    split.
    + apply (LRsig n (LRbelow n) G Γ T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1 R); [split|..].
      * exact Hl.
      * apply lequiv_sym, Q13.
      * apply lequiv_sym, Q24.
      * exact Hw1.
      * exact Hw2.
      * exact HT1.
      * exact HT3.
      * exact HA1.
      * exact HA3'.
      * exact HB1.
      * eapply (lconv_ty (l := k4)); [|apply lequiv_sym, Q24].
        eapply ctx_lvl_ty; [exact HA3 | apply lequiv_sym, Q13 | exact HB3].
      * exact HA13.
      * exact HB13.
      * exact Hdom3.
      * intros ρ a a' ha. exact (proj1 (IHcod ρ a a' ha _ _ (Hcod3 ρ a a' ha) (Ecod ρ a'))).
      * exact HR13.
    + (* terms *)
      intros t1 t2 t3 H12' H33' Et. apply HR. apply HR in H12'. apply HR3 in H33'.
      refine (SigRel_leq Hl3 Hl4 Q13 Q24 Hw1 HA1 HA2 HA3 HA12 HA13 HB12 HB13 _ _ _ _ _ H12' H33' Et).
      * intros ρ x y z h1 h3 Ey.
        exact (proj2 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13))
                        (kty_leq ρ _ _ EA)) _ _ _ h1 h3 Ey).
      * intros ρ x y z h1 h3 h u v w C1 C3 Ey Ev.
        assert (Ec : ty_leq (ktyl ρ B2)[lsingle y] (ktyl ρ B3)[lsingle z])
          by (apply (proj1 leq_subst_all); [cbn; auto | apply ktyl_leq, EB]).
        pose proof (proj2 (IHcod ρ _ _ h1 _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (codAd3 ρ _ _ h3) (kw_lequiv ρ Q24)) Ec)
                      _ _ _ C1 C3 Ev) as X.
        exact (proj1 (Hcodirr ρ _ _ _ h1 h _ _) X).
  - (* Unit *)
    destruct (ty_leq_unit_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as (l3 & -> & E3).
    destruct (LR_inv_unit H3 HT3) as (l4 & _ & Hl4 & Hw3 & _ & HR3).
    assert (Q : lequiv (gL G) l2 l3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hw3 E3).
    assert (Hl31 : lequiv (gL G) l3 l1) by (eapply lequiv_trans; [apply lequiv_sym, Q | exact Hl2]).
    split; [eapply (LRunit n (LRbelow n) G Γ T1 T3 l l1 l3); eauto|].
    intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
    destruct H12 as (w1 & _ & Hr1 & _ & Hf1 & _). destruct H33 as (w3 & _ & Hr3 & _ & Hf3 & _).
    exists w1, w3. exact (conj Hr1 (conj (unit_tmred_conv Hl31 Hr3) (conj Hf1 Hf3))).
  - (* sEq *)
    destruct (ty_leq_seq_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (s3 & A3 & a3 & b3 & -> & E3 & EA & Ea & Eb).
    destruct (LR_inv_seq H3 HT3) as (s4 & A4 & a4 & b4 & _ & Hl4 & Hw3 & _ & HA3 & HA34 & Ha34 & Hb34 & HR3).
    assert (Q : lequiv (gL G) s2 s3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hw3 E3).
    assert (Hl31 : lequiv (gL G) s3 s1) by (eapply lequiv_trans; [apply lequiv_sym, Q | exact Hl2]).
    assert (Hl13 : lequiv (gL G) s1 s3) by solve [apply lequiv_sym; assumption].
    assert (EA13 : [ G ; Γ ⊢ SA ≈ A3 @ s1 ]).
    { eapply geq_ty_leq_r; [exact HSAA | eapply geq_ty_lconv; [exact (geq_ty_refl_l HA34) | exact Hl13]
                           | exact EA]. }
    assert (DA31 : [ G ; Γ ⊢g A3 ≅ SA @ s1 ]) by (apply eqty_sym, geq_ty_sound, EA13).
    assert (Ea13 : [ G ; Γ ⊢ sa ≈ a3 : SA @ s1 ]).
    { eapply geq_tm_leq_r; [exact Hsaa | | exact Ea].
      eapply geq_tm_conv; [eapply geq_tm_lconv; [exact (geq_tm_refl_l Ha34) | exact Hl13] | exact DA31]. }
    assert (Eb13 : [ G ; Γ ⊢ sb ≈ b3 : SA @ s1 ]).
    { eapply geq_tm_leq_r; [exact Hsbb | | exact Eb].
      eapply geq_tm_conv; [eapply geq_tm_lconv; [exact (geq_tm_refl_l Hb34) | exact Hl13] | exact DA31]. }
    split; [eapply (LRseq n (LRbelow n) G Γ T1 T3 l s1 s3 SA A3 sa a3 sb b3); eauto|].
    intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
    assert (HV : [ G ; Γ ⊢g tySEq s3 A3 a3 b3 ≅ tySEq s1 SA sa sb @ s3 ]).
    { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_seq; eauto | exact Hl31]. }
    apply (SEqRel_conv HV Hl31) in H33.
    destruct H12 as (w1 & _ & Hr1 & _ & Hf1 & _). destruct H33 as (w3 & _ & Hr3 & _ & Hf3 & _).
    exists w1, w3. auto.
  - (* sEmpty *)
    destruct (ty_leq_sempty_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as (s3 & -> & E3).
    destruct (LR_inv_sempty H3 HT3) as (s4 & _ & Hl4 & Hw3 & _ & HR3).
    assert (Q : lequiv (gL G) s2 s3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hw3 E3).
    assert (Hl31 : lequiv (gL G) s3 s1) by (eapply lequiv_trans; [apply lequiv_sym, Q | exact Hl2]).
    split; [eapply (LRsempty n (LRbelow n) G Γ T1 T3 l s1 s3); eauto|].
    intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
    apply (SEmptyRel_lconv Hl31) in H33.
    destruct H12 as (w1 & _ & Hr1 & _ & Hf1 & _). destruct H33 as (w3 & _ & Hr3 & _ & Hf3 & _).
    exists w1, w3. auto.
  - (* Id: the carriers by their induction hypothesis *)
    destruct (ty_leq_id_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (s3 & A3 & a3 & b3 & -> & E3 & EA & Ea & Eb).
    destruct (LR_inv_id H3 HT3) as (s4 & A4 & a4 & b4 & RA3 & _ & Hl4 & Hw3 & _ & HA3 & HA34 & Ha34 & Hb34
                                    & HRA3 & Hra3 & Hrb3 & Hps3 & Hpt3 & HR3).
    assert (Q : lequiv (gL G) s2 s3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hw3 E3).
    assert (Hl31 : lequiv (gL G) s3 s1) by (eapply lequiv_trans; [apply lequiv_sym, Q | exact Hl2]).
    assert (Hl13 : lequiv (gL G) s1 s3) by solve [apply lequiv_sym; assumption].
    assert (EA13 : [ G ; Γ ⊢ IA ≈ A3 @ s1 ]).
    { eapply geq_ty_leq_r; [exact HIAA | eapply geq_ty_lconv; [exact (geq_ty_refl_l HA34) | exact Hl13]
                           | exact EA]. }
    assert (DA31 : [ G ; Γ ⊢g A3 ≅ IA @ s1 ]) by (apply eqty_sym, geq_ty_sound, EA13).
    assert (Ea13 : [ G ; Γ ⊢ ia ≈ a3 : IA @ s1 ]).
    { eapply geq_tm_leq_r; [exact Hiaa | | exact Ea].
      eapply geq_tm_conv; [eapply geq_tm_lconv; [exact (geq_tm_refl_l Ha34) | exact Hl13] | exact DA31]. }
    assert (Eb13 : [ G ; Γ ⊢ ib ≈ b3 : IA @ s1 ]).
    { eapply geq_tm_leq_r; [exact Hibb | | exact Eb].
      eapply geq_tm_conv; [eapply geq_tm_lconv; [exact (geq_tm_refl_l Hb34) | exact Hl13] | exact DA31]. }
    assert (HRA33 : LR n (LRbelow n) G Γ A3 A3 s1 RA3)
      by exact (LR_lconv _ _ _ _ _ _ _ _ _ (LR_refl_l _ _ _ _ _ _ _ HRA3) Hl13).
    destruct (IHRA _ _ HRA33 EA) as [HRA13 Hc].
    assert (Rf3 : forall x y, RA3 x y -> RA3 x x) by (intros x y H; exact (Hpt3 _ _ _ H (Hps3 _ _ H))).
    split.
    + pose proof (Hc _ _ _ Hra (Rf3 _ _ Hra3) Ea) as Ha3.
      pose proof (Hc _ _ _ Hrb (Rf3 _ _ Hrb3) Eb) as Hb3.
      eapply (LRid n (LRbelow n) G Γ T1 T3 l s1 s3 IA A3 ia a3 ib b3 RA); eauto.
    + intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
      assert (HV : [ G ; Γ ⊢g tyId s3 A3 a3 b3 ≅ tyId s1 IA ia ib @ s3 ]).
      { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_id; eauto | exact Hl31]. }
      exact (IdRel_leq Hl31 HV EA13 Hc Hps3 Hpt3 H12 H33 Et).
  - (* Empty: self-related neutrals, as at sEmpty *)
    destruct (ty_leq_empty_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as (s3 & -> & E3).
    destruct (LR_inv_empty H3 HT3) as (s4 & _ & Hl4 & Hw3 & _ & HR3).
    assert (Q : lequiv (gL G) s2 s3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hw3 E3).
    assert (Hl31 : lequiv (gL G) s3 s1) by (eapply lequiv_trans; [apply lequiv_sym, Q | exact Hl2]).
    split; [eapply (LRempty n (LRbelow n) G Γ T1 T3 l s1 s3); eauto|].
    intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
    apply (EmptyRel_lconv Hl31) in H33.
    destruct H12 as (w1 & _ & Hr1 & _ & Hf1 & _). destruct H33 as (w3 & _ & Hr3 & _ & Hf3 & _).
    exists w1, w3. auto.
  - (* +: the summands by their induction hypotheses *)
    destruct (ty_leq_sum_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (u5 & u6 & A3 & B3 & -> & E5 & E6 & EA & EB).
    destruct (LR_inv_sum H3 HT3) as (u7 & u8 & A4 & B4 & RA3 & RB3 & _ & _ & _ & Hw5 & Hw6 & _
                                    & _ & HA34 & _ & HB34 & HRA3 & HRB3 & HsA3 & HtA3 & HsB3 & HtB3 & HR3).
    assert (Q5 : lequiv (gL G) u3 u5) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl3) Hw5 E5).
    assert (Q6 : lequiv (gL G) u4 u6) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl4) Hw6 E6).
    assert (Hl51 : lequiv (gL G) u5 u1) by (eapply lequiv_trans; [apply lequiv_sym, Q5 | exact Hl3]).
    assert (Hl62 : lequiv (gL G) u6 u2) by (eapply lequiv_trans; [apply lequiv_sym, Q6 | exact Hl4]).
    pose proof (lequiv_sym _ _ _ Hl51) as Hl15. pose proof (lequiv_sym _ _ _ Hl62) as Hl26.
    assert (EA13 : [ G ; Γ ⊢ UA ≈ A3 @ u1 ]).
    { eapply geq_ty_leq_r; [exact HUAA | eapply geq_ty_lconv; [exact (geq_ty_refl_l HA34) | exact Hl15]
                           | exact EA]. }
    assert (EB13 : [ G ; Γ ⊢ UB ≈ B3 @ u2 ]).
    { eapply geq_ty_leq_r; [exact HUBB | eapply geq_ty_lconv; [exact (geq_ty_refl_l HB34) | exact Hl26]
                           | exact EB]. }
    destruct (IHRA _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (LR_refl_l _ _ _ _ _ _ _ HRA3) Hl15) EA) as [HRA13 HcA].
    destruct (IHRB _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (LR_refl_l _ _ _ _ _ _ _ HRB3) Hl26) EB) as [HRB13 HcB].
    split.
    + eapply (LRsum n (LRbelow n) G Γ T1 T3 l u1 u2 u5 u6 UA A3 UB B3 RA RB); eauto.
    + intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
      assert (HV : [ G ; Γ ⊢g tySum u5 u6 A3 B3 ≅ tySum u1 u2 UA UB @ lmax u5 u6 ]).
      { eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, geq_ty_sum; eauto | now apply lequiv_max]. }
      exact (SumRel_leq Hl51 Hl62 HV HcA HcB HsA3 HtA3 HsB3 HtB3 H12 H33 Et).
  - (* W: the type-level data as Σ's; the terms by [WRel_leq] *)
    destruct (ty_leq_W_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (k3 & k4 & A3 & B3 & -> & E3 & E4 & EA & EB).
    destruct (LR_inv_W H3 HT3) as (k3' & k4' & A3' & B3' & domR3 & codR3 &
      [_ _ _ Hwk3 Hwk4 _ HT3' HA3 _ HB3 _ HA33 HB33] & domAd3 & codAd3 & HR3).
    assert (Heq : tyW k3' k4' A3' B3' = tyW k3 k4 A3 B3)
      by (eapply tyred_whnf_det; [exact HT3' | exact HT3 | eauto with whnf | eauto with whnf]).
    injection Heq as -> -> -> ->. clear HT3'.
    assert (HΓ : [ G ; Γ ⊢g ]) by exact (ctx_of_ty HA1).
    (* levels *)
    assert (Q3 : lequiv (gL G) l3 k3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl3) Hwk3 E3).
    assert (Q4 : lequiv (gL G) l4 k4) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl4) Hwk4 E4).
    assert (Q13 : lequiv (gL G) l1 k3) by (eapply lequiv_trans; [apply lequiv_sym, Hl3 | exact Q3]).
    assert (Q24 : lequiv (gL G) l2 k4) by (eapply lequiv_trans; [apply lequiv_sym, Hl4 | exact Q4]).
    (* the domains *)
    assert (Hdom3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A1) (kty ρ A3) l1 (domR1 ρ))
      by (intros ρ; exact (proj1 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13))
                                     (kty_leq ρ _ _ EA)))).
    assert (Hrefl : forall ρ a a', domR1 ρ a a' -> domR1 ρ a' a').
    { intros ρ a a' ha. exact (LR_tm_refl_l _ _ _ _ _ _ _ a' a (LR_sym _ _ _ _ _ _ _ (domAd1 ρ)) ha). }
    assert (H13 : forall ρ a a', domR1 ρ a a' -> domR3 ρ a' a').
    { intros ρ a a' ha.
      pose proof (LR_irrel _ _ _ _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ (Hdom3 ρ))
                    (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13)) a' a') as X.
      exact (proj1 X (Hrefl ρ a a' ha)). }
    assert (Hcodirr : forall ρ a a1 a2 (h1 : domR1 ρ a a1) (h2 : domR1 ρ a a2),
               releq (codR1 ρ a a1 h1) (codR1 ρ a a2 h2))
      by (intros; eapply LR_irrel; [apply codAd1 | apply codAd1]).
    assert (Hcod3 : forall ρ a a' (ha : domR1 ρ a a'),
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ B3)[lsingle a'] (ktyl ρ B3)[lsingle a'] l2
                  (codR3 ρ a' a' (H13 ρ a a' ha)))
      by (intros; exact (LR_lconv _ _ _ _ _ _ _ _ _ (codAd3 _ _ _ _) (kw_lequiv ρ Q24))).
    assert (Ecod : forall (ρ : kwk G Γ) a', ty_leq (ktyl ρ B2)[lsingle a'] (ktyl ρ B3)[lsingle a'])
      by (intros; apply subst_leq_ty, ktyl_leq, EB).
    (* generic and declarative facts *)
    assert (HA3' : [ G ; Γ ⊢g A3 @ l1 ]) by exact (lconv_ty HA3 (lequiv_sym _ _ _ Q13)).
    assert (HA23 : [ G ; Γ ⊢ A2 ≈ A3 @ l1 ])
      by exact (geq_ty_leq (geq_ty_refl_r HA12) (geq_ty_lconv HA33 Q13) EA).
    assert (HA13 : [ G ; Γ ⊢ A1 ≈ A3 @ l1 ]) by exact (geq_ty_trans HA12 HA23).
    assert (HB33' : [ G ; Γ ,, A1 @ l1 ⊢ B3 ≈ B3 @ l2 ]).
    { eapply geq_ty_lconv; [|exact Q24].
      eapply geq_ty_ctxconv; [| apply lequiv_sym, Q13 | apply ext_wf_g; [exact HA1 | exact Hw1] | exact HB33].
      eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA13 | apply lequiv_sym, Q13]. }
    assert (HB23 : [ G ; Γ ,, A1 @ l1 ⊢ B2 ≈ B3 @ l2 ])
      by exact (geq_ty_leq (geq_ty_refl_r HB12) HB33' EB).
    assert (HB13 : [ G ; Γ ,, A1 @ l1 ⊢ B1 ≈ B3 @ l2 ]) by exact (geq_ty_trans HB12 HB23).
    split.
    + apply (LRw n (LRbelow n) G Γ T1 T3 l l1 l2 k3 k4 A1 B1 A3 B3 domR1 codR1 R); [split|..].
      * exact Hl.
      * apply lequiv_sym, Q13.
      * apply lequiv_sym, Q24.
      * exact Hw1.
      * exact Hw2.
      * exact HT1.
      * exact HT3.
      * exact HA1.
      * exact HA3'.
      * exact HB1.
      * eapply (lconv_ty (l := k4)); [|apply lequiv_sym, Q24].
        eapply ctx_lvl_ty; [exact HA3 | apply lequiv_sym, Q13 | exact HB3].
      * exact HA13.
      * exact HB13.
      * exact Hdom3.
      * intros ρ a a' ha. exact (proj1 (IHcod ρ a a' ha _ _ (Hcod3 ρ a a' ha) (Ecod ρ a'))).
      * exact HR.
    + intros t1 t2 t3 H12' H33' Et. apply HR. apply HR in H12'. apply HR3 in H33'.
      refine (WRel_leq _ _ _ _ _ _ _ _ _ _ H12' _ _ _ _ _ _ _ H33' Et (lequiv_sym _ _ _ Q13)
                (lequiv_sym _ _ _ Q24) HA1 HA13 HB13 _ _ _ _).
      * intros ρ x y h.
        pose proof (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (codAd1 ρ x y h)))) as E12.
        pose proof (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (Hcod3 ρ x y h)))) as E33.
        exact (geq_ty_leq_r E12 E33 (Ecod ρ y)).
      * intros ρ x y z h1 h3 Ex.
        exact (proj2 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13)) (kty_leq ρ _ _ EA))
                 x y z h1 h3 Ex).
      * intros ρ x y z h h' u v Huv. exact (proj1 (Hcodirr ρ x z y h' h u v) Huv).
      * intros ρ x y h h3 u v Huv.
        pose proof (LR_lconv _ _ _ _ _ _ _ _ _ (codAd3 ρ y y h3) (kw_lequiv ρ Q24)) as C3.
        pose proof (proj1 (IHcod ρ x y h _ _ C3 (Ecod ρ y))) as C13.
        pose proof (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ C13 C3 u v) Huv) as X.
        destruct (LR_tm_per _ _ _ _ _ _ _ C3) as [Hs Ht]. exact (Ht _ _ _ (Hs _ _ X) X).
  - (* Wf: the type-level data as W's domain; the terms by [WfRel_leq_all] *)
    destruct (ty_leq_wf_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as (k3 & A3 & N3 & -> & E3 & EA & EN).
    destruct (LR_inv_wf H3 HT3) as (k3' & A3' & N3' & domR3 & _ & _ & Hwk3 & _ & HT3' & HA3 & _ & HN3t & _
                                    & HA33 & HN33 & domAd3 & arAd3 & HR3).
    assert (Heq : tyWf k3' A3' N3' = tyWf k3 A3 N3)
      by (eapply tyred_whnf_det; [exact HT3' | exact HT3 | eauto with whnf | eauto with whnf]).
    injection Heq as -> -> ->. clear HT3'.
    assert (Q : lequiv (gL G) l2 k3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hwk3 E3).
    assert (Q13 : lequiv (gL G) l1 k3) by (eapply lequiv_trans; [apply lequiv_sym, Hl2 | exact Q]).
    assert (Hdom3' : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A3) (kty ρ A3) l1 (domR3 ρ))
      by (intros ρ; exact (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13))).
    assert (Hdom3 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A1) (kty ρ A3) l1 (domR1 ρ))
      by (intros ρ; exact (proj1 (IHdom ρ _ _ (Hdom3' ρ) (kty_leq ρ _ _ EA)))).
    assert (Hrefl : forall ρ a a', domR1 ρ a a' -> domR1 ρ a' a').
    { intros ρ a a' ha. exact (LR_tm_refl_l _ _ _ _ _ _ _ a' a (LR_sym _ _ _ _ _ _ _ (domAd1 ρ)) ha). }
    assert (H13 : forall ρ a a', domR1 ρ a a' -> domR3 ρ a' a').
    { intros ρ a a' ha.
      pose proof (LR_irrel _ _ _ _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ (Hdom3 ρ)) (Hdom3' ρ) a' a') as X.
      exact (proj1 X (Hrefl ρ a a' ha)). }
    assert (Dl : forall ρ x y z, domR1 ρ x y -> domR3 ρ z z -> tm_leq y z -> domR1 ρ x z)
      by (intros ρ; exact (proj2 (IHdom ρ _ _ (Hdom3' ρ) (kty_leq ρ _ _ EA)))).
    assert (Har : forall (ρ : kwk G Γ) a a', domR1 ρ a a' ->
               NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N1)[lsingle a] (ktml ρ N3)[lsingle a']).
    { intros ρ a a' ha.
      exact (NatRel_leq _ _ _ _ (arAd1 ρ a a' ha) _ (arAd3 ρ a' a' (H13 ρ a a' ha))
               (subst_leq_tm _ _ _ (ktml_leq ρ _ _ EN))). }
    (* generic and declarative facts *)
    assert (HA3' : [ G ; Γ ⊢g A3 @ l1 ]) by exact (lconv_ty HA3 (lequiv_sym _ _ _ Q13)).
    assert (HA23 : [ G ; Γ ⊢ A2 ≈ A3 @ l1 ])
      by exact (geq_ty_leq (geq_ty_refl_r HA12) (geq_ty_lconv HA33 Q13) EA).
    assert (HA13 : [ G ; Γ ⊢ A1 ≈ A3 @ l1 ]) by exact (geq_ty_trans HA12 HA23).
    assert (HN33' : [ G ; Γ ,, A1 @ l1 ⊢ N3 ≈ N3 : tyNat @ lzero ]).
    { eapply geq_tm_ctxconv; [| apply lequiv_sym, Q13 | apply ext_wf_g; [exact HA1 | exact Hw] | exact HN33].
      eapply eqty_lconv; [apply eqty_sym, geq_ty_sound, HA13 | apply lequiv_sym, Q13]. }
    assert (HN23 : [ G ; Γ ,, A1 @ l1 ⊢ N2 ≈ N3 : tyNat @ lzero ])
      by exact (geq_tm_leq (geq_tm_refl_r HN12) HN33' EN).
    assert (HN13 : [ G ; Γ ,, A1 @ l1 ⊢ N1 ≈ N3 : tyNat @ lzero ]) by exact (geq_tm_trans HN12 HN23).
    split.
    + apply (LRwf n (LRbelow n) G Γ T1 T3 l l1 k3 A1 A3 N1 N3 domR1 R).
      * exact Hl.
      * apply lequiv_sym, Q13.
      * exact Hw.
      * exact HT1.
      * exact HT3.
      * exact HA1.
      * exact HA3'.
      * exact HN1t.
      * exact (ctx_lvl_tm HA3 (lequiv_sym _ _ _ Q13) HN3t).
      * exact HA13.
      * exact HN13.
      * exact Hdom3.
      * exact Har.
      * exact HR.
    + intros t1 t2 t3 H12' H33' Et. apply HR. apply HR in H12'. apply HR3 in H33'.
      exact (proj1 WfRel_leq_all _ _ _ _ _ _ _ _ H12' k3 A3 N3 domR3 t3
               (conj (conj (lequiv_sym _ _ _ Q13) (conj HA1 (conj HA13 (conj HN13 Har)))) Dl) H33' Et).
  - (* ∥·∥: the carrier by its induction hypothesis; the terms are each good alone *)
    destruct (ty_leq_sq_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as (s3 & A3 & -> & E3 & EA).
    destruct (LR_inv_sq H3 HT3) as (s4 & A4 & RA3 & _ & _ & Hw3 & HT3' & _ & HA3 & HA34 & HRA3 & _ & _ & HR3).
    assert (Q : lequiv (gL G) l2 s3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hw3 E3).
    assert (Hl31 : lequiv (gL G) s3 l1) by (eapply lequiv_trans; [apply lequiv_sym, Q | exact Hl2]).
    pose proof (lequiv_sym _ _ _ Hl31) as Hl13.
    assert (EA13 : [ G ; Γ ⊢ A ≈ A3 @ l1 ]).
    { eapply geq_ty_leq_r; [exact HAA | eapply geq_ty_lconv; [exact (geq_ty_refl_l HA34) | exact Hl13]
                           | exact EA]. }
    assert (HRA33 : LR n (LRbelow n) G Γ A3 A3 l1 RA3)
      by exact (LR_lconv _ _ _ _ _ _ _ _ _ (LR_refl_l _ _ _ _ _ _ _ HRA3) Hl13).
    destruct (IHRQ _ _ HRA33 EA) as [HRQ13 _].
    assert (Hfl : releq (flipR RQ) RA3)
      by exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ HRQ13) HRA33).
    split.
    + eapply (LRsq n (LRbelow n) G Γ T1 T3 l l1 s3 A A3 RQ); eauto.
    + intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
      apply (SqRel_conv (RA' := RQ) Hl31 HA3 (geq_ty_lconv (geq_ty_sym EA13) Hl31)) in H33.
      * exact (conj (proj1 H12) (proj1 H33)).
      * intros a; split; intros X; [exact (proj2 (Hfl a a) X) | exact (proj1 (Hfl a a) X)].
  - (* IWf: the type-level data as Wf's; the terms by [IWfRel_leq_all] *)
    destruct (ty_leq_iwf_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (l3 & li3 & X3 & A3 & N3 & O3 & C3 & m3 & -> & E3 & Ei3 & EX & EA & EN & EO & EC & Em).
    destruct (LR_inv_iwf H3 HT3) as (k3' & ki3' & X3' & A3' & N3' & O3' & C3' & m3' & idxR3 & domR3 & _ & _ & _
                                     & Hwl3 & Hwli3 & _ & HT3' & HX3 & _ & HA3 & _ & HN3 & _ & HO3 & _ & HC3 & _
                                     & Hm3 & _ & HXX33 & HAA33 & HNN33 & HOO33 & HCC33 & Hmm33
                                     & idxAd3 & _ & _ & domAd3 & arAd3 & otAd3 & chAd3 & ixAd3 & HR3).
    assert (Heq : tyIWf k3' ki3' X3' A3' N3' O3' C3' m3' = tyIWf l3 li3 X3 A3 N3 O3 C3 m3)
      by (eapply tyred_whnf_det; [exact HT3' | exact HT3 | eauto with whnf | eauto with whnf]).
    injection Heq as -> -> -> -> -> -> -> ->. clear HT3'.
    assert (Q : lequiv (gL G) wl2 l3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hwl3 E3).
    assert (Qi : lequiv (gL G) wli2 li3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hwli2) Hwli3 Ei3).
    assert (Q13 : lequiv (gL G) wl1 l3) by (eapply lequiv_trans; [apply lequiv_sym, Hl2 | exact Q]).
    assert (Qi13 : lequiv (gL G) wli1 li3) by (eapply lequiv_trans; [apply lequiv_sym, Hwli2 | exact Qi]).
    pose proof (lequiv_sym _ _ _ Q13) as Q31. pose proof (lequiv_sym _ _ _ Qi13) as Qi31.
    (* the index and shape relations, by their induction hypotheses *)
    assert (Hidx3' : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ X3) (kty ρ X3) wli1 (idxR3 ρ))
      by (intros ρ; exact (LR_lconv _ _ _ _ _ _ _ _ _ (idxAd3 ρ) (kw_lequiv ρ Qi13))).
    assert (Hidx13 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ wX) (kty ρ X3) wli1 (widxR ρ))
      by (intros ρ; exact (proj1 (IHwidx ρ _ _ (Hidx3' ρ) (kty_leq ρ _ _ EX)))).
    assert (Il : forall ρ x y z, widxR ρ x y -> idxR3 ρ z z -> tm_leq y z -> widxR ρ x z)
      by (intros ρ; exact (proj2 (IHwidx ρ _ _ (Hidx3' ρ) (kty_leq ρ _ _ EX)))).
    assert (Hdom3' : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A3) (kty ρ A3) wl1 (domR3 ρ))
      by (intros ρ; exact (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13))).
    assert (Hdom13 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ wA) (kty ρ A3) wl1 (wdomR ρ))
      by (intros ρ; exact (proj1 (IHwdom ρ _ _ (Hdom3' ρ) (kty_leq ρ _ _ EA)))).
    assert (Hrefl : forall ρ a a', wdomR ρ a a' -> wdomR ρ a' a').
    { intros ρ a a' ha. exact (LR_tm_refl_l _ _ _ _ _ _ _ a' a (LR_sym _ _ _ _ _ _ _ (wdomAd ρ)) ha). }
    assert (H13 : forall ρ a a', wdomR ρ a a' -> domR3 ρ a' a').
    { intros ρ a a' ha.
      pose proof (LR_irrel _ _ _ _ _ _ _ _ _ _ (LR_sym _ _ _ _ _ _ _ (Hdom13 ρ)) (Hdom3' ρ) a' a') as Y.
      exact (proj1 Y (Hrefl ρ a a' ha)). }
    assert (Dl : forall ρ x y z, wdomR ρ x y -> domR3 ρ z z -> tm_leq y z -> wdomR ρ x z)
      by (intros ρ; exact (proj2 (IHwdom ρ _ _ (Hdom3' ρ) (kty_leq ρ _ _ EA)))).
    assert (Har13 : forall (ρ : kwk G Γ) a a', wdomR ρ a a' ->
               NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ wN)[lsingle a] (ktml ρ N3)[lsingle a']).
    { intros ρ a a' ha.
      exact (NatRel_leq _ _ _ _ (warAd ρ a a' ha) _ (arAd3 ρ a' a' (H13 ρ a a' ha))
               (subst_leq_tm _ _ _ (ktml_leq ρ _ _ EN))). }
    assert (Hot13 : forall (ρ : kwk G Γ) a a', wdomR ρ a a' -> widxR ρ (ktml ρ wO)[lsingle a] (ktml ρ O3)[lsingle a']).
    { intros ρ a a' ha.
      exact (Il ρ _ _ _ (wotAd ρ a a' ha) (otAd3 ρ a' a' (H13 ρ a a' ha)) (subst_leq_tm _ _ _ (ktml_leq ρ _ _ EO))). }
    assert (Hch13 : forall (ρ : kwk G Γ) a a', wdomR ρ a a' -> forall p p',
               PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ wN)[lsingle a] (ktml ρ N3)[lsingle a'] p p' ->
               widxR ρ (ktmll ρ wC)[lsingle2 a p] (ktmll ρ C3)[lsingle2 a' p']).
    { intros ρ a a' ha p p' Hp.
      destruct (PosRel_leq_split Hp _ (warAd ρ a a' ha) (subst_leq_tm _ _ _ (ktml_leq ρ _ _ EN)))
        as (p'' & Hp1 & Ep).
      refine (Il ρ _ _ _ (wchAd ρ a a' ha p p'' Hp1) (chAd3 ρ a' a' (H13 ρ a a' ha) p' p' (PosRel_refl_r Hp)) _).
      apply (proj1 (proj2 leq_subst_all)); [| exact (ktmll_leq ρ _ _ EC)].
      unfold lsingle2; cbn; repeat split; auto using tm_leq_refl. }
    assert (Hix13 : forall ρ : kwk G Γ, widxR ρ (ktm ρ wm) (ktm ρ m3))
      by (intros ρ; exact (Il ρ _ _ _ (wixAd ρ) (ixAd3 ρ) (ktm_leq ρ _ _ Em))).
    (* generic and declarative facts *)
    assert (HX31 : [ G ; Γ ⊢g X3 @ wli1 ]) by exact (lconv_ty HX3 Qi31).
    assert (HA31 : [ G ; Γ ⊢g A3 @ wl1 ]) by exact (lconv_ty HA3 Q31).
    assert (HXX13 : [ G ; Γ ⊢ wX ≈ X3 @ wli1 ])
      by exact (geq_ty_trans HwXX (geq_ty_leq (geq_ty_refl_r HwXX) (geq_ty_lconv HXX33 Qi13) EX)).
    assert (HAA13 : [ G ; Γ ⊢ wA ≈ A3 @ wl1 ])
      by exact (geq_ty_trans HwAA (geq_ty_leq (geq_ty_refl_r HwAA) (geq_ty_lconv HAA33 Q13) EA)).
    assert (EA31 : [ G ; Γ ⊢g A3 ≅ wA @ l3 ]) by exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (geq_ty_sound HAA13)) Q31).
    assert (EXd31 : [ G ; Γ ⊢g X3 ≅ wX @ li3 ]) by exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (geq_ty_sound HXX13)) Qi31).
    assert (HΓA : [ G ; Γ ,, wA @ wl1 ⊢g ]) by exact (ext_wf_g HwA Hw).
    assert (HNN13 : [ G ; Γ ,, wA @ wl1 ⊢ wN ≈ N3 : tyNat @ lzero ])
      by exact (geq_tm_trans HwNN (geq_tm_leq (geq_tm_refl_r HwNN) (geq_tm_ctxconv EA31 Q31 HΓA HNN33) EN)).
    pose proof (geq_tm_sound HNN13) as ENd.
    assert (EX1 : [ G ; Γ ,, wA @ wl1 ⊢g X3⟨↑⟩ ≅ wX⟨↑⟩ @ li3 ])
      by exact (wk1_eqty G ge_layer ge_typeof _ _ _ _ _ _ HΓA EXd31).
    assert (HOO13 : [ G ; Γ ,, wA @ wl1 ⊢ wO ≈ O3 : wX⟨↑⟩ @ wli1 ]).
    { eapply geq_tm_trans; [exact HwOO|]. eapply geq_tm_leq; [exact (geq_tm_refl_r HwOO) | | exact EO].
      eapply geq_tm_lconv; [| exact Qi13]. eapply geq_tm_conv; [| exact EX1].
      exact (geq_tm_ctxconv EA31 Q31 HΓA HOO33). }
    assert (HΓAN : [ G ; Γ ,, wA @ wl1 ,, tyFin wN @ lzero ⊢g ])
      by (apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact HwN] | exact I]).
    assert (HΓAN' : [ G ; Γ ,, wA @ wl1 ,, tyFin N3 @ lzero ⊢g ])
      by (apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact (eqtm_wf_r ge_typeof ENd)] | exact I]).
    assert (EX2 : [ G ; Γ ,, wA @ wl1 ,, tyFin wN @ lzero ⊢g X3⟨↑⟩⟨↑⟩ ≅ wX⟨↑⟩⟨↑⟩ @ li3 ])
      by exact (wk1_eqty G ge_layer ge_typeof _ _ _ _ _ _ HΓAN EX1).
    assert (HCC13 : [ G ; Γ ,, wA @ wl1 ,, tyFin wN @ lzero ⊢ wC ≈ C3 : wX⟨↑⟩⟨↑⟩ @ wli1 ]).
    { eapply geq_tm_trans; [exact HwCC|]. eapply geq_tm_leq; [exact (geq_tm_refl_r HwCC) | | exact EC].
      eapply geq_tm_lconv; [| exact Qi13]. eapply geq_tm_conv; [| exact EX2].
      eapply geq_tm_ctxconv; [| exact (lequiv_refl (gL G) lzero I) | exact HΓAN |].
      { apply eqty_fin; [exact ge_notV | apply eqtm_sym, ENd]. }
      exact (geq_tm_ctxconv2 EA31 Q31 HΓAN' HCC33). }
    assert (Hmm13 : [ G ; Γ ⊢ wm ≈ m3 : wX @ wli1 ])
      by exact (geq_tm_trans Hwmm (geq_tm_leq (geq_tm_refl_r Hwmm) (geq_tm_lconv (geq_tm_conv Hmm33 EXd31) Qi13) Em)).
    assert (HN31 : [ G ; Γ ,, A3 @ wl1 ⊢g N3 : tyNat @ lzero ]) by exact (ctx_lvl_tm HA3 Q31 HN3).
    assert (HΓAN3 : [ G ; Γ ,, A3 @ wl1 ,, tyFin N3 @ lzero ⊢g ])
      by (apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact HN31] | exact I]).
    split.
    + eapply (LRiwf n (LRbelow n) G Γ T1 T3 l wl1 wli1 l3 li3 wX X3 wA A3 wN N3 wO O3 wC C3 wm m3 widxR wdomR R).
      * exact Hl.
      * exact Q31.
      * exact Qi31.
      * exact Hw.
      * exact Hwwi.
      * exact HT1.
      * exact HT3.
      * exact HwX.
      * exact HX31.
      * exact HwA.
      * exact HA31.
      * exact HwN.
      * exact HN31.
      * exact HwO.
      * eapply wf_lconv; [exact (ctx_lvl_tm HA3 Q31 HO3) | exact Qi13].
      * exact HwC.
      * eapply wf_lconv; [| exact Qi13].
        exact (mv_tm ge_typeof (stab2_lsub ge_typeof (eqty_refl _ _ _ _ _ HA3) Q31 HΓAN3) HC3).
      * exact Hwm.
      * eapply wf_lconv; [exact Hm3 | exact Qi13].
      * exact HXX13.
      * exact HAA13.
      * exact HNN13.
      * exact HOO13.
      * exact HCC13.
      * exact Hmm13.
      * exact Hidx13.
      * exact Hwisym.
      * exact Hwistr.
      * exact Hdom13.
      * exact Har13.
      * exact Hot13.
      * exact Hch13.
      * exact Hix13.
      * exact HR.
    + assert (HE : IWfEq (G := G) (i := ge_layer) Γ wl1 wli1 l3 li3 wX X3 wA A3 wN N3 wO O3 wC C3).
      { apply IWfEq_intro; [exact Q13 | exact Qi13 | exact (geq_ty_sound HXX13) | exact (geq_ty_sound HAA13)
          | exact ENd | exact (geq_tm_sound HOO13) | exact (geq_tm_sound HCC13)
          | exact Hw | exact Hwwi | exact HwX | exact HwA | exact HwN | exact HwO | exact HwC
          | exact HX31 | exact HA31 | exact (eqtm_wf_r ge_typeof ENd)
          | exact (eqtm_wf_r ge_typeof (geq_tm_sound HOO13)) | exact (eqtm_wf_r ge_typeof (geq_tm_sound HCC13))]. }
      assert (Hy : IWfFlipHyps G Γ wl1 wli1 wX wA wN wO wC widxR wdomR l3 li3 X3 A3 N3 O3 C3).
      { refine (conj HE (conj Hwisym (conj Hwistr (conj _ (conj Har13 (conj Hot13 (conj Hch13
                  (conj (conj HXX13 (conj HAA13 (conj HNN13 (conj HOO13 HCC13)))) _)))))))).
        - intros ρ a a' h.
          destruct (escape_tm _ _ _ _ _ _ _ _ (wdomAd ρ) a a' h) as (Ha & Ha' & Haa).
          exact (conj Ha (conj Ha' (geq_tm_sound Haa))).
        - intros ρ x y h. exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (widxAd ρ) x y h))). }
      intros t1 t2 t3 H12' H33' Et. apply HR. apply HR in H12'. apply HR3 in H33'.
      exact (proj1 IWfRel_leq_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12' l3 li3 X3 A3 N3 O3 C3 idxR3 domR3 m3 t3
               (conj Hy Dl) (IWf_ty_eq ge_typeof ge_notV HE (geq_tm_sound Hmm13)) H33' Et).
  - (* M: the composite pair's premises from the induction hypotheses at
       the third's index, shapes and positions; the terms by [MRn_leq] *)
    destruct (ty_leq_M_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3))
      as (s1 & s2 & si & X3 & A3 & B3 & C3 & m3 & -> & E1 & E2 & Ei & EX & EA & EB & EC & Em).
    destruct (LR_inv_M H3 HT3) as (s1' & s2' & si' & X3' & A3' & B3' & C3' & m3' & idxR3 & shR3 & posR3 & _
                                   & Hs1s & Hs2s & Hsis & Ws1 & Ws2 & Wsi & _ & HT3' & HX3 & _ & HA3 & _
                                   & HB3 & _ & HC3 & _ & Hm3 & _ & HXX33 & HAA33 & HBB33 & HCC33 & Hmm33
                                   & idxAd3 & shAd3 & posAd3 & chAd3 & gB3 & gC3 & gCa3 & imon3 & shmon3
                                   & posmon3 & ixAd3 & HR3).
    assert (Heq : tyM s1' s2' si' X3' A3' B3' C3' m3' = tyM s1 s2 si X3 A3 B3 C3 m3)
      by (eapply tyred_whnf_det; [exact HT3' | exact HT3 | eauto with whnf | eauto with whnf]).
    injection Heq as -> -> -> -> -> -> -> ->. clear HT3'.
    (* levels *)
    assert (Q1 : lequiv (gL G) mr1 s1) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hmr1) Ws1 E1).
    assert (Q2 : lequiv (gL G) mr2 s2) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hmr2) Ws2 E2).
    assert (Qi : lequiv (gL G) mri si) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hmri) Wsi Ei).
    assert (Q13 : lequiv (gL G) ml1 s1) by (eapply lequiv_trans; [apply lequiv_sym, Hmr1 | exact Q1]).
    assert (Q23 : lequiv (gL G) ml2 s2) by (eapply lequiv_trans; [apply lequiv_sym, Hmr2 | exact Q2]).
    assert (Qi3 : lequiv (gL G) mli si) by (eapply lequiv_trans; [apply lequiv_sym, Hmri | exact Qi]).
    pose proof (lequiv_sym _ _ _ Q13) as Q31. pose proof (lequiv_sym _ _ _ Q23) as Q32.
    pose proof (lequiv_sym _ _ _ Qi3) as Qi31.
    (* the two sides given *)
    pose proof (MSide_of_LR Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HmX HmA HmB HmC HmXX HmAA HmBB HmCC
                  midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon) as HM1.
    pose proof (MSide_of_LR Hs1s Hs2s Hsis Ws1 Ws2 Wsi HX3 HA3 HB3 HC3 HXX33 HAA33 HBB33 HCC33
                  idxAd3 shAd3 posAd3 chAd3 gB3 gC3 gCa3 imon3 shmon3 posmon3) as HM3.
    pose proof (wf_tm_nf Hmm) as Nm. pose proof (wf_tm_nf Hmm') as Nm'. pose proof (wf_tm_nf Hm3) as Nm3.
    (* the signature *)
    pose proof (MGeq_leq (ms_geq HM1) (ms_geq HM3) Q13 Q23 Qi3 EX EA EB EC) as HG13.
    pose proof HG13 as (_ & _ & _ & _ & GX & GA & GB & GC).
    pose proof (MSig_lconv ge_typeof ge_notV (conj Ws1 (conj Ws2 (conj Wsi (conj HX3 (conj HA3 (conj HB3 HC3))))))
                  Q31 Q32 Qi31) as (_ & _ & _ & H3X & H3A & H3B & H3C).
    assert (EXd31 : [ G ; Γ ⊢g X3 ≅ mX @ si ])
      by exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (geq_ty_sound GX)) Qi31).
    assert (Hmm13 : [ G ; Γ ⊢ mm ≈ m3 : mX @ mli ])
      by exact (geq_tm_leq_r Hmmm (geq_tm_lconv (geq_tm_conv Hmm33 EXd31) Qi3) Em).
    (* the index *)
    assert (Hidx3' : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ X3) (kty ρ X3) mli (idxR3 ρ))
      by (intros ρ; exact (LR_lconv _ _ _ _ _ _ _ _ _ (idxAd3 ρ) (kw_lequiv ρ Qi3))).
    assert (Hidx13 : forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ mX) (kty ρ X3) mli (midxR ρ))
      by (intros ρ; exact (proj1 (IHmidx ρ _ _ (Hidx3' ρ) (kty_leq ρ _ _ EX)))).
    assert (Il : forall ρ x y z, midxR ρ x y -> idxR3 ρ z z -> tm_leq y z -> midxR ρ x z)
      by (intros ρ; exact (proj2 (IHmidx ρ _ _ (Hidx3' ρ) (kty_leq ρ _ _ EX)))).
    assert (Ii3 : forall ρ x x', midxR ρ x x' -> idxR3 ρ x' x')
      by (intros ρ x x' h; exact (LR_cross (Hidx13 ρ) (Hidx3' ρ) h)).
    assert (Ix13 : forall ρ, midxR ρ (ktm ρ mm) (ktm ρ m3))
      by (intros ρ; exact (Il ρ _ _ _ (mixAd ρ) (ixAd3 ρ) (ktm_leq ρ _ _ Em))).
    (* the shapes *)
    assert (Sh3' : forall ρ z, idxR3 ρ z z ->
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ A3)[lsingle z] (ktyl ρ A3)[lsingle z] ml1 (shR3 ρ z z))
      by (intros ρ z h; exact (LR_lconv _ _ _ _ _ _ _ _ _ (shAd3 ρ z z h) (kw_lequiv ρ Q13))).
    assert (EAz : forall (ρ : kwk G Γ) y z, tm_leq y z -> ty_leq (ktyl ρ mA')[lsingle y] (ktyl ρ A3)[lsingle z])
      by (intros; apply (proj1 leq_subst_all); [cbn; auto | apply ktyl_leq, EA]).
    assert (Sh13 : forall ρ x x', midxR ρ x x' ->
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ mA)[lsingle x] (ktyl ρ A3)[lsingle x'] ml1 (mshR ρ x x'))
      by (intros ρ x x' h;
          exact (proj1 (IHmsh ρ x x' h _ _ (Sh3' ρ x' (Ii3 ρ x x' h)) (EAz ρ x' x' (tm_leq_refl x'))))).
    assert (Sl : forall ρ x y z a b c, midxR ρ x y -> idxR3 ρ z z -> tm_leq y z -> mshR ρ x y a b ->
                   shR3 ρ z z c c -> tm_leq b c -> mshR ρ x y a c)
      by (intros ρ x y z a b c h hz Ey ha hc Eb;
          exact (proj2 (IHmsh ρ x y h _ _ (Sh3' ρ z hz) (EAz ρ y z Ey)) a b c ha hc Eb)).
    assert (Si3 : forall ρ x x' a a', midxR ρ x x' -> mshR ρ x x' a a' -> shR3 ρ x' x' a' a')
      by (intros ρ x x' a a' h ha; exact (LR_cross (Sh13 ρ x x' h) (Sh3' ρ x' (Ii3 ρ x x' h)) ha)).
    assert (Shirr : MShIrr midxR mshR)
      by (intros ρ x y y' h h'; eapply LR_irrel; [exact (mshAd ρ x y h) | exact (mshAd ρ x y' h')]).
    (* the positions *)
    assert (Pos3' : forall ρ z c, idxR3 ρ z z -> shR3 ρ z z c c ->
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyll ρ B3)[lsingle2 z c] (ktyll ρ B3)[lsingle2 z c] ml2
                 (posR3 ρ z z c c))
      by (intros ρ z c hz hc; exact (LR_lconv _ _ _ _ _ _ _ _ _ (posAd3 ρ z z c c hz hc) (kw_lequiv ρ Q23))).
    assert (EBz : forall (ρ : kwk G Γ) y z b c, tm_leq y z -> tm_leq b c ->
               ty_leq (ktyll ρ mB')[lsingle2 y b] (ktyll ρ B3)[lsingle2 z c])
      by (intros; apply (proj1 leq_subst_all); [unfold lsingle2; cbn; repeat split; auto | apply ktyll_leq, EB]).
    assert (Pos13 : forall ρ x x' a a', midxR ρ x x' -> mshR ρ x x' a a' ->
               LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyll ρ mB)[lsingle2 x a] (ktyll ρ B3)[lsingle2 x' a'] ml2
                 (mposR ρ x x' a a'))
      by (intros ρ x x' a a' h ha;
          exact (proj1 (IHmpos ρ x x' a a' h ha _ _ (Pos3' ρ x' a' (Ii3 ρ x x' h) (Si3 ρ x x' a a' h ha))
                          (EBz ρ x' x' a' a' (tm_leq_refl x') (tm_leq_refl a'))))).
    assert (Pl : forall ρ x y z a b c p q r, midxR ρ x y -> idxR3 ρ z z -> tm_leq y z -> mshR ρ x y a b ->
                   shR3 ρ z z c c -> tm_leq b c -> mposR ρ x y a b p q -> posR3 ρ z z c c r r -> tm_leq q r ->
                   mposR ρ x y a b p r)
      by (intros ρ x y z a b c p q r h hz Ey ha hc Eb;
          exact (proj2 (IHmpos ρ x y a b h ha _ _ (Pos3' ρ z c hz hc) (EBz ρ y z b c Ey Eb)) p q r)).
    assert (P13 : forall ρ x y z a b c p q, midxR ρ x y -> idxR3 ρ z z -> tm_leq y z -> mshR ρ x y a b ->
                    shR3 ρ z z c c -> tm_leq b c -> mposR ρ x y a b p q -> posR3 ρ z z c c q q)
      by (intros ρ x y z a b c p q h hz Ey ha hc Eb hp;
          exact (LR_cross (proj1 (IHmpos ρ x y a b h ha _ _ (Pos3' ρ z c hz hc) (EBz ρ y z b c Ey Eb)))
                   (Pos3' ρ z c hz hc) hp)).
    assert (Pirr : MPosIrr midxR mshR mposR)
      by (intros ρ x y y' a b b' h h' ha ha';
          eapply LR_irrel; [exact (mposAd ρ x y a b h ha) | exact (mposAd ρ x y' a b' h' ha')]).
    (* the child index *)
    assert (Ch13 : forall ρ x x' a a' p p', midxR ρ x x' -> mshR ρ x x' a a' -> mposR ρ x x' a a' p p' ->
               midxR ρ (ktmlll ρ mC)[lsingle3 x a p] (ktmlll ρ C3)[lsingle3 x' a' p']).
    { intros ρ x x' a a' p p' h ha hp.
      pose proof (Ii3 ρ x x' h) as hx. pose proof (Si3 ρ x x' a a' h ha) as hc.
      refine (Il ρ _ _ _ (mchAd ρ x x' a a' p p' h ha hp)
                (chAd3 ρ x' x' a' a' p' p' hx hc
                   (P13 ρ x x' x' a a' a' p p' h hx (tm_leq_refl x') ha hc (tm_leq_refl a') hp)) _).
      apply (proj1 (proj2 leq_subst_all)); [unfold lsingle3, lsingle2; cbn; repeat split; auto using tm_leq_refl
                                           | apply ktmlll_leq, EC]. }
    (* the families, generically: the third's self-equalities moved to the first's contexts *)
    assert (EA31 : forall ρ x x', midxR ρ x x' ->
               [ kw_G ρ ; kw_Δ ρ ⊢g (ktyl ρ A3)[lsingle x'] ≅ (ktyl ρ mA)[lsingle x] @ s1 ])
      by (intros ρ x x' h; exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (geq_ty_sound
             (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (Sh13 ρ x x' h)))))) (kw_lequiv ρ Q31))).
    assert (EX3ρ : forall ρ : kwk G Γ, [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ X3 ≅ kty ρ mX @ mli ])
      by (intros ρ; exact (kw_eqty ρ (eqty_sym _ _ _ _ _ _ (geq_ty_sound GX)))).
    assert (gB13 : forall ρ x x', midxR ρ x x' ->
               [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ mA)[lsingle x] @ ml1
                   ⊢ (ktyll ρ mB)[llift (lsingle x)] ≈ (ktyll ρ B3)[llift (lsingle x')] @ ml2 ]).
    { intros ρ x x' h.
      pose proof (escape_ty _ _ _ _ _ _ _ _ (Sh13 ρ x x' h)) as (HAx & _ & _).
      refine (geq_ty_leq_r (mgB ρ x x' h) _ (subst_leq_ty _ _ _ (ktyll_leq ρ _ _ EB))).
      eapply geq_ty_lconv; [| exact (kw_lequiv ρ Q23)].
      eapply geq_ty_ctxconv; [exact (EA31 ρ x x' h) | exact (kw_lequiv ρ Q31)
                             | exact (ext_wf_g HAx (kw_lwf ρ Hmw1)) | exact (gB3 ρ x' x' (Ii3 ρ x x' h))]. }
    assert (gC13 : forall ρ x x', midxR ρ x x' ->
               [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ mA)[lsingle x] @ ml1 ,, (ktyll ρ mB)[llift (lsingle x)] @ ml2
                   ⊢ (ktmlll ρ mC)[llift (llift (lsingle x))] ≈ (ktmlll ρ C3)[llift (llift (lsingle x'))]
                   : (kty ρ mX)⟨↑⟩⟨↑⟩ @ mli ]).
    { intros ρ x x' h.
      pose proof (EA31 ρ x x' h) as DA.
      pose proof (ext_wf_g (eqty_wf_l ge_typeof DA) (kw_lwf ρ Ws1)) as HΓA3.
      assert (DB : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A3)[lsingle x'] @ s1
                     ⊢g (ktyll ρ B3)[llift (lsingle x')] ≅ (ktyll ρ mB)[llift (lsingle x)] @ s2 ]).
      { eapply eqty_lconv; [| exact (kw_lequiv ρ Q32)]. apply geq_ty_sound.
        eapply geq_ty_ctxconv;
          [ exact (geq_ty_sound (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (Sh13 ρ x x' h)))))
          | exact (kw_lequiv ρ Q13) | exact HΓA3 |].
        exact (geq_ty_sym (gB13 ρ x x' h)). }
      pose proof (ctx2_conv ge_typeof DA (kw_lequiv ρ Q31) DB (kw_lequiv ρ Q32)) as Q.
      pose proof (mgC ρ x x' h) as GC1.
      pose proof (ctx_of_eqtm ge_typeof (geq_tm_sound GC1)) as HΓ2. pose proof (ctx_pre HΓ2) as HΓ1.
      pose proof (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ2
                    (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ1 (EX3ρ ρ))) as EX2.
      refine (geq_tm_leq_r GC1 _ (subst_leq_tm _ _ _ (ktmlll_leq ρ _ _ EC))).
      eapply geq_tm_conv; [| exact EX2]. eapply geq_tm_lconv; [| exact (kw_lequiv ρ Qi3)].
      exact (geq_tm_ctxeq Q (gC3 ρ x' x' (Ii3 ρ x x' h))). }
    assert (gCa13 : forall ρ x x' a a', midxR ρ x x' -> mshR ρ x x' a a' ->
               [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ mB)[lsingle2 x a] @ ml2
                   ⊢ (ktmlll ρ mC)[llift (lsingle2 x a)] ≈ (ktmlll ρ C3)[llift (lsingle2 x' a')] : (kty ρ mX)⟨↑⟩ @ mli ]).
    { intros ρ x x' a a' h ha.
      pose proof (escape_ty _ _ _ _ _ _ _ _ (Pos13 ρ x x' a a' h ha)) as (HBx & _ & EBx).
      pose proof (mgCa ρ x x' a a' h ha) as GC1.
      pose proof (ctx_of_eqtm ge_typeof (geq_tm_sound GC1)) as HΓ1.
      pose proof (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ1 (EX3ρ ρ)) as EX1.
      refine (geq_tm_leq_r GC1 _ (subst_leq_tm _ _ _ (ktmlll_leq ρ _ _ EC))).
      eapply geq_tm_conv; [| exact EX1]. eapply geq_tm_lconv; [| exact (kw_lequiv ρ Qi3)].
      eapply geq_tm_ctxconv;
        [ exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (geq_ty_sound EBx)) (kw_lequiv ρ Q32))
        | exact (kw_lequiv ρ Q32) | exact HΓ1 | exact (gCa3 ρ x' x' a' a' (Ii3 ρ x x' h) (Si3 ρ x x' a a' h ha)) ]. }
    (* the composite side, and the relation at it *)
    pose proof (MSide_of_LR Q31 Q32 Qi31 Hmw1 Hmw2 Hmwi HmX HmA HmB HmC GX GA GB GC
                  Hidx13 Sh13 Pos13 Ch13 gB13 gC13 gCa13 mimon mshmon mposmon) as HM13.
    assert (HI : MIrrHyps G Γ ml1 ml2 mli mX mA mB mC mr1 mr2 mri mX' mA' mB' mC' s1 s2 si X3 A3 B3 C3
                   midxR midxR mshR mshR mposR mposR mm mm' m3).
    { refine (conj HM1 (conj HM13 (conj Shirr (conj _ (conj Nm (conj Nm' (conj Nm3 (conj mixAd Ix13)))))))).
      intros ρ x x' x'' a a' h h' ha. exact (Pirr ρ x x' x'' a a' a' h h' ha (proj1 (Shirr ρ x x' x'' h h' a a') ha)). }
    split.
    + eapply (LRm n (LRbelow n) G Γ T1 T3 l ml1 ml2 mli s1 s2 si mX X3 mA A3 mB B3 mC C3 mm m3 midxR mshR mposR R).
      * exact Hl.
      * exact Q31.
      * exact Q32.
      * exact Qi31.
      * exact Hmw1.
      * exact Hmw2.
      * exact Hmwi.
      * exact HT1.
      * exact HT3.
      * exact HmX.
      * exact H3X.
      * exact HmA.
      * exact H3A.
      * exact HmB.
      * exact H3B.
      * exact HmC.
      * exact H3C.
      * exact Hmm.
      * eapply wf_lconv; [exact Hm3 | exact Qi3].
      * exact GX.
      * exact GA.
      * exact GB.
      * exact GC.
      * exact Hmm13.
      * exact Hidx13.
      * exact Sh13.
      * exact Pos13.
      * exact Ch13.
      * exact gB13.
      * exact gC13.
      * exact gCa13.
      * exact mimon.
      * exact mshmon.
      * exact mposmon.
      * exact Ix13.
      * eapply releq_trans; [exact HR | exact (MR_irrel HI)].
    + assert (HL : MLeqHyps G Γ ml1 ml2 mli mX mA mB mC mr1 mr2 mri mX' mA' mB' mC' s1 s2 si X3 A3 B3 C3
                     midxR idxR3 mshR shR3 mposR posR3 mm mm' m3)
        by exact (conj HM1 (conj HM13 (conj HM3 (conj Nm (conj Nm' (conj Nm3 (conj mixAd (conj Ix13 (conj ixAd3
                    (conj Em (conj EC (conj Shirr (conj Pirr (conj Sl (conj P13 Pl))))))))))))))).
      intros t1 t2 t3 Y1 Y3 Et. apply HR. apply HR in Y1. apply HR3 in Y3. intros k.
      exact (MRn_leq k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL t1 t2 t3 (Y1 k) (Y3 k) Et).
Qed.

Theorem LR_leq n : Pleq n.
Proof using EL VL.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_leq_step, IHn.
Qed.

(** Named forms, at a level's stage. *)
Corollary LogRel_leq_ty {l0 G Γ T1 T2 T3 l R R3} :
  LogRel l0 G Γ T1 T2 l R -> LogRel l0 G Γ T3 T3 l R3 -> ty_leq T2 T3 -> LogRel l0 G Γ T1 T3 l R.
Proof using EL VL. intros H H3 Ex; exact (proj1 (LR_leq _ _ _ _ _ _ _ H _ _ H3 Ex)). Qed.
Corollary LogRel_leq_tm {l0 G Γ T1 T2 l R T3 R3 t1 t2 t3} :
  LogRel l0 G Γ T1 T2 l R -> LogRel l0 G Γ T3 T3 l R3 -> ty_leq T2 T3 ->
  R t1 t2 -> R3 t3 t3 -> tm_leq t2 t3 -> R t1 t3.
Proof using EL VL. intros H H3 Ex; exact (proj2 (LR_leq _ _ _ _ _ _ _ H _ _ H3 Ex) t1 t2 t3). Qed.

End LevelInv.
