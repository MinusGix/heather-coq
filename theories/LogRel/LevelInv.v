(** * Level invariance of the relation (M3_DESIGN.md E6')

    The relation does not see level annotations beyond their equivalence:
    if [T1] and [T2] are related, and [T3] is [≡ₗ]-related to [T2] and
    related to itself, then [T1] and [T3] are related, with the same term
    relation; likewise for terms. Weak-head normal forms of [≡ₗ]-related
    syntax are [≡ₗ]-related (LevelRed.v), so the shapes agree; the
    generic laws [g*_leq] relate the normal forms themselves. The proof
    follows transitivity (Transitivity.v), with the second derivation
    replaced by the self-relation of [T3]. *)
From DeLaM.Syntax Require Export LevelRed.
From DeLaM.LogRel Require Export Reduction.

(** ** Kripke weakenings respect [≡ₗ] *)

Lemma ty_leq_gwa (T T' : ty) γ : ty_leq T T' -> ty_leq T⟦γ⟧ T'⟦γ⟧.
Proof. destruct γ; cbn; auto; apply (proj1 leq_gren_all). Qed.
Lemma tm_leq_gwa (t t' : tm) γ : tm_leq t t' -> tm_leq t⟦γ⟧ t'⟦γ⟧.
Proof. destruct γ; cbn; auto; apply (proj1 (proj2 leq_gren_all)). Qed.

Section LevelInv.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma kty_leq {G Γ} (ρ : kwk G Γ) T T' : ty_leq T T' -> ty_leq (kty ρ T) (kty ρ T').
Proof. intros H; unfold kty; apply (proj1 leq_ren_all), ty_leq_gwa, H. Qed.
Lemma ktm_leq {G Γ} (ρ : kwk G Γ) t t' : tm_leq t t' -> tm_leq (ktm ρ t) (ktm ρ t').
Proof. intros H; unfold ktm; apply (proj1 (proj2 leq_ren_all)), tm_leq_gwa, H. Qed.
Lemma ktyl_leq {G Γ} (ρ : kwk G Γ) T T' : ty_leq T T' -> ty_leq (ktyl ρ T) (ktyl ρ T').
Proof. intros H; unfold ktyl; apply (proj1 leq_ren_all), ty_leq_gwa, H. Qed.
Lemma subst_leq_ty (T T' : ty) d : ty_leq T T' -> ty_leq T[d] T'[d].
Proof. intros H; apply (proj1 leq_subst_all); [apply lsub_leq_refl | exact H]. Qed.
Lemma kbody_leq {G Γ} (ρ : kwk G Γ) T T' : ty_leq T T' -> ty_leq (kbody ρ T) (kbody ρ T').
Proof. intros H; unfold kbody; apply (proj1 leq_ren_all), ty_leq_gwa, H. Qed.
Lemma gsingle_leq_ty (T T' : ty) o : ty_leq T T' -> ty_leq T⦃gsingle o⦄ T'⦃gsingle o⦄.
Proof. intros H; apply (proj1 leq_gsubst_all); [intros; apply gobj_leq_refl | exact H]. Qed.

(** ** Normal forms of related syntax *)

Lemma tyred_leq {G Γ T T' W W' l l'} : ty_leq T T' ->
  [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g T' ⤳* W' @ l' ] -> whnf_ty W -> whnf_ty W' -> ty_leq W W'.
Proof. intros Ex [_ H _] [_ H' _]; exact (reds_ty_whnf_leq _ _ _ _ Ex H H'). Qed.
Lemma tmred_leq {G Γ t t' w w' T T' l l'} : tm_leq t t' ->
  [ G ; Γ ⊢g t ⤳* w : T @ l ] -> [ G ; Γ ⊢g t' ⤳* w' : T' @ l' ] -> whnf w -> whnf w' -> tm_leq w w'.
Proof. intros Ex [_ H _] [_ H' _]; exact (reds_whnf_leq _ _ _ _ Ex H H'). Qed.

(** The left type of a related pair has a weak-head normal form. *)
Lemma LR_whnf_l {n rec G Γ T T' l R} : LR n rec G Γ T T' l R ->
  exists W, [ G ; Γ ⊢g T ⤳* W @ l ] /\ whnf_ty W.
Proof.
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
                    HRA HRB Hpa Hta Hpb Htb HR].
  all: first
    [ solve [eexists; split; [exact HT | first [exact (whnf_ty_ne _ (gne_ty_whne_l HV)) | solve [eauto with whnf]]]]
    | match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end;
      (eexists; split; [eassumption | eauto with whnf]) ].
Qed.

(** ** Generic helpers *)

Lemma gne_ty_refl_r {G Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Γ ⊢ V' ~ V' @ l ].
Proof. intros H; eapply gne_ty_trans; [apply gne_ty_sym, H | exact H]. Qed.
Lemma gne_ty_refl_l {G Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Γ ⊢ V ~ V @ l ].
Proof. intros H; eapply gne_ty_trans; [exact H | apply gne_ty_sym, H]. Qed.
Lemma gne_tm_refl_r {G Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Γ ⊢ t' ~ t' : T @ l ].
Proof. intros H; eapply gne_tm_trans; [apply gne_tm_sym, H | exact H]. Qed.
Lemma gne_tm_refl_l {G Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Γ ⊢ t ~ t : T @ l ].
Proof. intros H; eapply gne_tm_trans; [exact H | apply gne_tm_sym, H]. Qed.
Lemma geq_tm_refl_r {G Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢ t' ≈ t' : T @ l ].
Proof. intros H; eapply geq_tm_trans; [apply geq_tm_sym, H | exact H]. Qed.
Lemma geq_tm_refl_l {G Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢ t ≈ t : T @ l ].
Proof. intros H; eapply geq_tm_trans; [exact H | apply geq_tm_sym, H]. Qed.
Lemma geq_ty_refl_l {G Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Γ ⊢ T ≈ T @ l ].
Proof. intros H; eapply geq_ty_trans; [exact H | apply geq_ty_sym, H]. Qed.

(** Composition with an [≡ₗ]-related right-hand side. *)
Lemma gne_tm_leq_r {G Γ t1 t2 t3 T l} : [ G ; Γ ⊢ t1 ~ t2 : T @ l ] -> [ G ; Γ ⊢ t3 ~ t3 : T @ l ] ->
  tm_leq t2 t3 -> [ G ; Γ ⊢ t1 ~ t3 : T @ l ].
Proof. intros H H3 Et; eapply gne_tm_trans; [exact H | exact (gne_tm_leq (gne_tm_refl_r H) H3 Et)]. Qed.
Lemma geq_tm_leq_r {G Γ t1 t2 t3 T l} : [ G ; Γ ⊢ t1 ≈ t2 : T @ l ] -> [ G ; Γ ⊢ t3 ≈ t3 : T @ l ] ->
  tm_leq t2 t3 -> [ G ; Γ ⊢ t1 ≈ t3 : T @ l ].
Proof. intros H H3 Et; eapply geq_tm_trans; [exact H | exact (geq_tm_leq (geq_tm_refl_r H) H3 Et)]. Qed.
Lemma gne_ty_leq_r {G Γ V1 V2 V3 l} : [ G ; Γ ⊢ V1 ~ V2 @ l ] -> [ G ; Γ ⊢ V3 ~ V3 @ l ] ->
  ty_leq V2 V3 -> [ G ; Γ ⊢ V1 ~ V3 @ l ].
Proof. intros H H3 Et; eapply gne_ty_trans; [exact H | exact (gne_ty_leq (gne_ty_refl_r H) H3 Et)]. Qed.
Lemma geq_ty_leq_r {G Γ T1 T2 T3 l} : [ G ; Γ ⊢ T1 ≈ T2 @ l ] -> [ G ; Γ ⊢ T3 ≈ T3 @ l ] ->
  ty_leq T2 T3 -> [ G ; Γ ⊢ T1 ≈ T3 @ l ].
Proof. intros H H3 Et; eapply geq_ty_trans; [exact H | exact (geq_ty_leq (geq_ty_refl_r H) H3 Et)]. Qed.

(** ** Natural numbers *)

Lemma NatRel_leq G Γ :
  forall t1 t2, NatRel G Γ t1 t2 -> forall t3, NatRel G Γ t3 t3 -> tm_leq t2 t3 -> NatRel G Γ t1 t3.
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
      * apply CTypRel_conv_r; [now apply vpl_ctx_sym | now apply lequiv_sym | now apply eqty_sym].
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
      * apply CTrmRel_conv_r; [now apply vpl_ctx_sym | | now apply lequiv_sym | now apply eqty_sym].
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

Definition Pleq n := forall G Γ T1 T2 l R,
  LR n (LRbelow n) G Γ T1 T2 l R -> forall T3 R3,
  LR n (LRbelow n) G Γ T3 T3 l R3 -> ty_leq T2 T3 ->
  LR n (LRbelow n) G Γ T1 T3 l R /\
  (forall t1 t2 t3, R t1 t2 -> R3 t3 t3 -> tm_leq t2 t3 -> R t1 t3).

Lemma ty_leq_pi_inv {l3 l4 A2 B2 W} : ty_leq (tyPi l3 l4 A2 B2) W ->
  exists k3 k4 A3 B3, W = tyPi k3 k4 A3 B3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq A2 A3 /\ ty_leq B2 B3.
Proof. destruct W; cbn; try contradiction; intros; do 4 eexists; intuition eauto. Qed.
Lemma ty_leq_sig_inv {l3 l4 A2 B2 W} : ty_leq (tySig l3 l4 A2 B2) W ->
  exists k3 k4 A3 B3, W = tySig k3 k4 A3 B3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq A2 A3 /\ ty_leq B2 B3.
Proof. destruct W; cbn; try contradiction; intros; do 4 eexists; intuition eauto. Qed.
Lemma ty_leq_U_inv {l2 W} : ty_leq (tyU l2) W -> exists l3, W = tyU l3 /\ leqv l2 l3.
Proof. destruct W; cbn; try contradiction; eauto. Qed.
Lemma ty_leq_unit_inv {l2 W} : ty_leq (tyUnit l2) W -> exists l3, W = tyUnit l3 /\ leqv l2 l3.
Proof. destruct W; cbn; try contradiction; eauto. Qed.
Lemma ty_leq_seq_inv {l2 A2 a2 b2 W} : ty_leq (tySEq l2 A2 a2 b2) W ->
  exists l3 A3 a3 b3, W = tySEq l3 A3 a3 b3 /\ leqv l2 l3 /\ ty_leq A2 A3 /\ tm_leq a2 a3 /\ tm_leq b2 b3.
Proof. destruct W; cbn; try contradiction; intros; do 4 eexists; intuition eauto. Qed.
Lemma ty_leq_id_inv {l2 A2 a2 b2 W} : ty_leq (tyId l2 A2 a2 b2) W ->
  exists l3 A3 a3 b3, W = tyId l3 A3 a3 b3 /\ leqv l2 l3 /\ ty_leq A2 A3 /\ tm_leq a2 a3 /\ tm_leq b2 b3.
Proof. destruct W; cbn; try contradiction; intros; do 4 eexists; intuition eauto. Qed.
Lemma tm_leq_refl_inv {l C c w} : tm_leq (tmRefl l C c) w ->
  exists l' C' c', w = tmRefl l' C' c' /\ leqv l l' /\ ty_leq C C' /\ tm_leq c c'.
Proof. destruct w; cbn; try contradiction; intros; do 3 eexists; intuition eauto. Qed.
Lemma ty_leq_sempty_inv {l2 W} : ty_leq (tySEmpty l2) W -> exists l3, W = tySEmpty l3 /\ leqv l2 l3.
Proof. destruct W; cbn; try contradiction; eauto. Qed.
Lemma ty_leq_empty_inv {l2 W} : ty_leq (tyEmpty l2) W -> exists l3, W = tyEmpty l3 /\ leqv l2 l3.
Proof. destruct W; cbn; try contradiction; eauto. Qed.
Lemma ty_leq_sum_inv {l3 l4 A2 B2 W} : ty_leq (tySum l3 l4 A2 B2) W ->
  exists k3 k4 A3 B3, W = tySum k3 k4 A3 B3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq A2 A3 /\ ty_leq B2 B3.
Proof. destruct W; cbn; try contradiction; intros; do 4 eexists; intuition eauto. Qed.
Lemma tm_leq_inl_inv {l l' C D c w} : tm_leq (tmInl l l' C D c) w ->
  exists k k' C' D' c', w = tmInl k k' C' D' c' /\ leqv l k /\ leqv l' k' /\ ty_leq C C' /\ ty_leq D D' /\ tm_leq c c'.
Proof. destruct w; cbn; try contradiction; intros; do 5 eexists; intuition eauto. Qed.
Lemma tm_leq_inr_inv {l l' C D c w} : tm_leq (tmInr l l' C D c) w ->
  exists k k' C' D' c', w = tmInr k k' C' D' c' /\ leqv l k /\ leqv l' k' /\ ty_leq C C' /\ ty_leq D D' /\ tm_leq c c'.
Proof. destruct w; cbn; try contradiction; intros; do 5 eexists; intuition eauto. Qed.
Lemma ty_leq_nat_inv {W} : ty_leq tyNat W -> W = tyNat.
Proof. destruct W; cbn; try contradiction; auto. Qed.
Lemma ty_leq_cpi_inv {l2 U2 W} : ty_leq (tyCPi l2 U2) W ->
  exists k U3, W = tyCPi k U3 /\ leqv l2 k /\ ty_leq U2 U3.
Proof. destruct W; cbn; try contradiction; intros; do 2 eexists; intuition eauto. Qed.
Lemma ty_leq_tpi_inv {Δ2 l3 l4 U2 W} : ty_leq (tyTPi Δ2 l3 l4 U2) W ->
  exists Δ3 k3 k4 U3, W = tyTPi Δ3 k3 k4 U3 /\ ctx_leq Δ2 Δ3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq U2 U3.
Proof. destruct W; cbn; try contradiction; intros; do 4 eexists; intuition eauto. Qed.

(** ** The universe *)

Lemma URel_leq n G Γ l1 l3 t1 t2 t3 :
  Pleq (lmeasure l1) -> lmeasure l1 < n -> lequiv (gL G) l3 l1 ->
  URel (LRbelow n) G Γ l1 t1 t2 -> URel (LRbelow n) G Γ l3 t3 t3 -> tm_leq t2 t3 ->
  URel (LRbelow n) G Γ l1 t1 t3.
Proof.
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
Proof.
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
Proof.
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

(** ** Level invariance *)

Lemma LR_leq_step n : (forall m, m < n -> Pleq m) -> Pleq n.
Proof.
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
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR];
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
      destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
      destruct H33' as (w3 & w3' & Hw3r & Hw3r' & Hnf3 & Hnf3' & Heq3 & _ & HK3).
      assert (w3' = w3) as -> by (eapply tmred_whnf_det; eauto).
      assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2r Hw3r Hnf2 Hnf3).
      assert (Hm : lequiv (gL G) (lmax l1 l2) (lmax k3 k4)) by now apply lequiv_max.
      exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
      * eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Hm] |].
        apply eqty_sym, HP23d.
      * exact (geq_tm_leq_r Heq1 (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP13d) Hm) Ew).
      * exact (geq_tm_leq_r Heq1' (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP23d) Hm) Ew).
      * intros ρ a a' ha la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5.
        pose proof (HK1 ρ a a' ha la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5) as X1.
        pose proof (kw_lequiv ρ Q13) as Q13'. pose proof (kw_lequiv ρ Q24) as Q24'.
        assert (HΔ3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A3 @ k3 ⊢g ]) by exact (kw_ext ρ HA3 Hwk3).
        assert (E23 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A2 ≈ kty ρ A3 @ l1 ]) by exact (kw_geq_ty ρ HA23).
        assert (HA35 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A3 ≈ A5 @ k3 ]).
        { eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, E23 | exact HA5] |].
          apply lequiv_sym, Q13'. }
        assert (HB35 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A3 @ k3 ⊢ ktyl ρ B3 ≈ B5 @ k4 ]).
        { assert (F0 : [ G ; Γ ,, A2 @ l1 ⊢ B2 ≈ B3 @ l2 ]).
          { eapply geq_ty_ctxconv; [apply geq_ty_sound, HA12 | now apply lequiv_refl
                                   | apply ext_wf_g; [exact HA2 | exact Hw1] | exact HB23]. }
          assert (F : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l1 ⊢ ktyl ρ B3 ≈ B5 @ l2 ]).
          { eapply geq_ty_trans; [apply geq_ty_sym, (kw_geq_ty_l ρ HA2 Hw1 F0) | exact HB5]. }
          eapply geq_ty_lconv; [|apply lequiv_sym, Q24'].
          eapply geq_ty_ctxconv; [apply geq_ty_sound, E23 | exact Q13' | exact HΔ3 | exact F]. }
        assert (Hla3 : lequiv (gL G) la' k3) by (eapply lequiv_trans; [exact Hla' | exact Q13]).
        assert (Hlb3 : lequiv (gL G) lb' k4) by (eapply lequiv_trans; [exact Hlb' | exact Q24]).
        pose proof (HK3 ρ a' a' (H13 ρ a a' ha) la' lb' la' lb' A5 B5 A5 B5 Hla3 Hlb3 Hla3 Hlb3
                      HA35 HB35 HA35 HB35) as X3.
        refine (proj2 (IHcod ρ a a' ha _ _ (Hcod3 ρ a a' ha) (Ecod ρ a')) _ _ _ X1 X3 _).
        cbn; repeat split; auto using ktm_leq, leqv_refl, ty_leq_refl, tm_leq_refl.
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
      destruct H12' as (w1 & w2 & Hw1r & Hw2r & Hnf1 & Hnf2 & Heq1 & Heq1' & HK1).
      destruct H33' as (w3 & w3' & Hw3r & Hw3r' & Hnf3 & Hnf3' & Heq3 & _ & HK3).
      assert (w3' = w3) as -> by (eapply tmred_whnf_det; eauto).
      assert (Ew : tm_leq w2 w3) by exact (tmred_leq Et Hw2r Hw3r Hnf2 Hnf3).
      assert (Hm : lequiv (gL G) (lmax l1 l2) (lmax k3 k4)) by now apply lequiv_max.
      exists w1, w3. refine (conj Hw1r (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
      * eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hw3r | exact Hm] |].
        apply eqty_sym, HP23d.
      * exact (geq_tm_leq_r Heq1 (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP13d) Hm) Ew).
      * exact (geq_tm_leq_r Heq1' (geq_tm_conv_l Heq3 (eqty_sym _ _ _ _ _ _ HP23d) Hm) Ew).
      * intros ρ la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5.
        destruct (HK1 ρ la lb la' lb' A4 B4 A5 B5 Hla Hlb Hla' Hlb' HA4 HB4 HA5 HB5) as [h1 C1].
        pose proof (kw_lequiv ρ Q13) as Q13'. pose proof (kw_lequiv ρ Q24) as Q24'.
        assert (HΔ3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A3 @ k3 ⊢g ]) by exact (kw_ext ρ HA3 Hwk3).
        assert (E23 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A2 ≈ kty ρ A3 @ l1 ]) by exact (kw_geq_ty ρ HA23).
        assert (HA35 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A3 ≈ A5 @ k3 ]).
        { eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, E23 | exact HA5] |].
          apply lequiv_sym, Q13'. }
        assert (HB35 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A3 @ k3 ⊢ ktyl ρ B3 ≈ B5 @ k4 ]).
        { assert (F0 : [ G ; Γ ,, A2 @ l1 ⊢ B2 ≈ B3 @ l2 ]).
          { eapply geq_ty_ctxconv; [apply geq_ty_sound, HA12 | now apply lequiv_refl
                                   | apply ext_wf_g; [exact HA2 | exact Hw1] | exact HB23]. }
          assert (F : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A2 @ l1 ⊢ ktyl ρ B3 ≈ B5 @ l2 ]).
          { eapply geq_ty_trans; [apply geq_ty_sym, (kw_geq_ty_l ρ HA2 Hw1 F0) | exact HB5]. }
          eapply geq_ty_lconv; [|apply lequiv_sym, Q24'].
          eapply geq_ty_ctxconv; [apply geq_ty_sound, E23 | exact Q13' | exact HΔ3 | exact F]. }
        assert (Hla3 : lequiv (gL G) la' k3) by (eapply lequiv_trans; [exact Hla' | exact Q13]).
        assert (Hlb3 : lequiv (gL G) lb' k4) by (eapply lequiv_trans; [exact Hlb' | exact Q24]).
        destruct (HK3 ρ la' lb' la' lb' A5 B5 A5 B5 Hla3 Hlb3 Hla3 Hlb3 HA35 HB35 HA35 HB35) as [h3 C3].
        assert (Ef : tm_leq (tmFst la' lb' A5 B5 (ktm ρ w2)) (tmFst la' lb' A5 B5 (ktm ρ w3)))
          by (cbn; repeat split; auto using ktm_leq, leqv_refl, ty_leq_refl).
        assert (Es : tm_leq (tmSnd la' lb' A5 B5 (ktm ρ w2)) (tmSnd la' lb' A5 B5 (ktm ρ w3)))
          by (cbn; repeat split; auto using ktm_leq, leqv_refl, ty_leq_refl).
        pose proof (proj2 (IHdom ρ _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (domAd3 ρ) (kw_lequiv ρ Q13))
                           (kty_leq ρ _ _ EA)) _ _ _ h1 h3 Ef) as h.
        exists h.
        assert (Ec : ty_leq (ktyl ρ B2)[lsingle (tmFst la' lb' A5 B5 (ktm ρ w2))]
                            (ktyl ρ B3)[lsingle (tmFst la' lb' A5 B5 (ktm ρ w3))])
          by (apply (proj1 leq_subst_all); [cbn; auto | apply ktyl_leq, EB]).
        pose proof (proj2 (IHcod ρ _ _ h1 _ _ (LR_lconv _ _ _ _ _ _ _ _ _ (codAd3 ρ _ _ h3) Q24') Ec)
                      _ _ _ C1 C3 Es) as X.
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
    assert (Hl13 : lequiv (gL G) s1 s3) by now apply lequiv_sym.
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
    assert (Hl13 : lequiv (gL G) s1 s3) by now apply lequiv_sym.
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
  - (* Empty: related neutrals, as NeRel *)
    destruct (ty_leq_empty_inv (tyred_leq ET HT2 HT3 ltac:(eauto with whnf) Hnw3)) as (s3 & -> & E3).
    destruct (LR_inv_empty H3 HT3) as (s4 & _ & Hl4 & Hw3 & _ & HR3).
    assert (Q : lequiv (gL G) s2 s3) by exact (leqv_lequiv _ _ _ (lequiv_wf_l _ _ _ Hl2) Hw3 E3).
    assert (Hl31 : lequiv (gL G) s3 s1) by (eapply lequiv_trans; [apply lequiv_sym, Q | exact Hl2]).
    split; [eapply (LRempty n (LRbelow n) G Γ T1 T3 l s1 s3); eauto|].
    intros t1 t2 t3 H12 H33 Et. apply HR. apply HR in H12. apply HR3 in H33.
    apply (EmptyRel_lconv Hl31) in H33.
    destruct H12 as (ν1 & ν2 & Hν1 & Hν2 & H12). destruct H33 as (ν3 & ν3' & Hν3 & Hν3' & H33).
    assert (ν3' = ν3) as ->
      by (eapply tmred_whnf_det; [exact Hν3' | exact Hν3 | exact (whnf_ne _ (gne_tm_whne_r H33))
                                 | exact (whnf_ne _ (gne_tm_whne_l H33))]).
    assert (Eν : tm_leq ν2 ν3)
      by exact (tmred_leq Et Hν2 Hν3 (whnf_ne _ (gne_tm_whne_r H12)) (whnf_ne _ (gne_tm_whne_l H33))).
    exists ν1, ν3. exact (conj Hν1 (conj Hν3 (gne_tm_leq_r H12 H33 Eν))).
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
Qed.

Theorem LR_leq n : Pleq n.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_leq_step, IHn.
Qed.

(** Named forms, at a level's stage. *)
Corollary LogRel_leq_ty {l0 G Γ T1 T2 T3 l R R3} :
  LogRel l0 G Γ T1 T2 l R -> LogRel l0 G Γ T3 T3 l R3 -> ty_leq T2 T3 -> LogRel l0 G Γ T1 T3 l R.
Proof. intros H H3 Ex; exact (proj1 (LR_leq _ _ _ _ _ _ _ H _ _ H3 Ex)). Qed.
Corollary LogRel_leq_tm {l0 G Γ T1 T2 l R T3 R3 t1 t2 t3} :
  LogRel l0 G Γ T1 T2 l R -> LogRel l0 G Γ T3 T3 l R3 -> ty_leq T2 T3 ->
  R t1 t2 -> R3 t3 t3 -> tm_leq t2 t3 -> R t1 t3.
Proof. intros H H3 Ex; exact (proj2 (LR_leq _ _ _ _ _ _ _ H _ _ H3 Ex) t1 t2 t3). Qed.

End LevelInv.
