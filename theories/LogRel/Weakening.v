(** * Weakening of the logical relation (ch. 7, Weakening)

    A related pair of types stays related in every weakened context, and
    the term relation is preserved.  The Π case needs no induction
    hypothesis: its premises are already Kripke, and the weakened relation
    is the original one at composite weakenings.  The universe case uses
    weakening one stage down. *)
From DeLaM.LogRel Require Export Transitivity.

Section Weakening.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Composition of weakenings on syntax *)

Lemma ren_wk_comp_ty (T : ty) (ρ ρ' : wk) : T⟨ρ⟩⟨ρ'⟩ = T⟨wk_comp ρ' ρ⟩.
Proof. apply ren_ren_ty; intros; now rewrite rlk_wk_comp. Qed.
Lemma ren_wk_comp (t : tm) (ρ ρ' : wk) : t⟨ρ⟩⟨ρ'⟩ = t⟨wk_comp ρ' ρ⟩.
Proof. apply ren_ren; intros; now rewrite rlk_wk_comp. Qed.
Lemma ren_wk_comp_lift_ty (T : ty) (ρ ρ' : wk) :
  T⟨rlift ρ⟩⟨rlift ρ'⟩ = T⟨rlift (wk_comp ρ' ρ)⟩.
Proof.
  apply ren_ren_ty; intros [|n]; rewrite !rlk_rlift; auto. now rewrite rlk_wk_comp.
Qed.

(** ** Declarative/generic weakening at the instance's layer *)

Lemma tyred_wk' {G Γ Δ} {ρ : wk} {T W l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Δ ⊢g T⟨ρ⟩ ⤳* W⟨ρ⟩ @ l ].
Proof. intros Hρ HΔ H; eapply tyred_wk; eauto using ge_typeof, wk_wf_wkr. Qed.
Lemma tmred_wk' {G Γ Δ} {ρ : wk} {t w T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g t ⤳* w : T @ l ] ->
  [ G ; Δ ⊢g t⟨ρ⟩ ⤳* w⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof. intros Hρ HΔ H; eapply tmred_wk; eauto using ge_typeof, wk_wf_wkr. Qed.
Lemma geq_tm_wk' {G Γ Δ} {ρ : wk} {t t' T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Δ ⊢ t⟨ρ⟩ ≈ t'⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof. intros Hρ; apply geq_tm_wk, wk_wf_wkr, Hρ. Qed.
Lemma gne_tm_wk' {G Γ Δ} {ρ : wk} {t t' T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Δ ⊢ t⟨ρ⟩ ~ t'⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof. intros Hρ; apply gne_tm_wk, wk_wf_wkr, Hρ. Qed.
Lemma gne_ty_wk' {G Γ Δ} {ρ : wk} {V V' l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Δ ⊢ V⟨ρ⟩ ~ V'⟨ρ⟩ @ l ].
Proof. intros Hρ; apply gne_ty_wk, wk_wf_wkr, Hρ. Qed.

(** ** Term relations *)

Lemma NatRel_wk G Γ Δ (ρ : wk) : ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] ->
  forall t t', NatRel G Γ t t' -> NatRel G Δ t⟨ρ⟩ t'⟨ρ⟩.
Proof.
  intros Hρ HΔ.
  apply (NatRel_mut G Γ (fun t t' _ => NatRel G Δ t⟨ρ⟩ t'⟨ρ⟩)
                        (fun t t' _ => NatNf G Δ t⟨ρ⟩ t'⟨ρ⟩)).
  - intros t t' w w' Hw Hw' Heq _ IH.
    econstructor; [exact (tmred_wk' Hρ HΔ Hw) | exact (tmred_wk' Hρ HΔ Hw')
                  | exact (geq_tm_wk' Hρ HΔ Heq) | exact IH].
  - constructor.
  - intros; now constructor.
  - intros ν ν' H; constructor; exact (gne_tm_wk' Hρ HΔ H).
Qed.

Lemma NeRel_wk G Γ Δ (ρ : wk) V V' l t t' : ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] ->
  NeRel G Γ V V' l t t' -> NeRel G Δ V⟨ρ⟩ V'⟨ρ⟩ l t⟨ρ⟩ t'⟨ρ⟩.
Proof.
  intros Hρ HΔ (ν & ν' & H1 & H2 & H3 & H4). exists ν⟨ρ⟩, ν'⟨ρ⟩.
  refine (conj (tmred_wk' Hρ HΔ H1) (conj (tmred_wk' Hρ HΔ H2)
            (conj (gne_tm_wk' Hρ HΔ H3) (gne_tm_wk' Hρ HΔ H4)))).
Qed.

(** ** The statement *)

Definition Pwk n := forall G Γ T T' l R,
  LR n (LRbelow n) G Γ T T' l R -> forall Δ (ρ : wk), ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] ->
  exists R', LR n (LRbelow n) G Δ T⟨ρ⟩ T'⟨ρ⟩ l R' /\ forall t t', R t t' -> R' t⟨ρ⟩ t'⟨ρ⟩.

Lemma URel_wk n G Γ Δ (ρ : wk) l1 t t' :
  Pwk (lmeasure l1) -> lmeasure l1 < n -> ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] ->
  URel (LRbelow n) G Γ l1 t t' -> URel (LRbelow n) G Δ l1 t⟨ρ⟩ t'⟨ρ⟩.
Proof.
  intros Hwk Hn Hρ HΔ (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & HK).
  exists w⟨ρ⟩, w'⟨ρ⟩.
  refine (conj (tmred_wk' Hρ HΔ Hw) (conj (tmred_wk' Hρ HΔ Hw') (conj (whnf_ren _ _ Hnf)
            (conj (whnf_ren _ _ Hnf') (conj (geq_tm_wk' Hρ HΔ Heq) _))))).
  intros la lb Hla Hlb. destruct (HK la lb Hla Hlb) as [R0 H0].
  rewrite LRbelow_spec in H0 |- * by exact Hn.
  destruct (Hwk _ _ _ _ _ _ H0 Δ ρ Hρ HΔ) as (R1 & H1 & _).
  now exists R1.
Qed.

(** ** Weakening *)

Lemma LR_wk_step n : (forall m, m < n -> Pwk m) -> Pwk n.
Proof.
  intros IHn G Γ T T' l R H Δ ρ Hρ HΔ.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HAA HBB domAd codAd HR].
  - exists (NatRel G Δ). split.
    + eapply LRnat; [exact Hl | exact (tyred_wk' Hρ HΔ HT) | exact (tyred_wk' Hρ HΔ HT')
                    | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. exact (NatRel_wk _ _ _ _ Hρ HΔ _ _ Ht).
  - exists (URel (LRbelow n) G Δ l1). split.
    + eapply LRU; [exact Hl | exact Hl2 | exact Hn | exact (tyred_wk' Hρ HΔ HT)
                  | exact (tyred_wk' Hρ HΔ HT') | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. eapply URel_wk; eauto; try apply IHn; lia.
  - exists (NeRel G Δ V⟨ρ⟩ V'⟨ρ⟩ l). split.
    + eapply LRne; [exact (tyred_wk' Hρ HΔ HT) | exact (tyred_wk' Hρ HΔ HT')
                   | exact (gne_ty_wk' Hρ HΔ HV) | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. exact (NeRel_wk _ _ _ _ _ _ _ _ _ Hρ HΔ Ht).
  - set (domR' := fun Δ' (ρ' : wk) (Hρ' : ρ' : Δ' ≤ Δ) HΔ' =>
                    domR Δ' (wk_comp ρ' ρ) (wk_comp_wf _ _ _ _ _ Hρ' Hρ) HΔ').
    set (codR' := fun Δ' (ρ' : wk) (Hρ' : ρ' : Δ' ≤ Δ) HΔ' a a' (ha : domR' Δ' ρ' Hρ' HΔ' a a') =>
                    codR Δ' (wk_comp ρ' ρ) (wk_comp_wf _ _ _ _ _ Hρ' Hρ) HΔ' a a' ha).
    assert (HAr : [ G ; Δ ⊢g A⟨ρ⟩ @ l1 ]) by exact (wf_ty_wk Hρ HΔ HA).
    assert (HA'r : [ G ; Δ ⊢g A'⟨ρ⟩ @ l1 ]) by exact (wf_ty_wk Hρ HΔ HA').
    assert (HΔA : [ G ; Δ ,, A⟨ρ⟩ @ l1 ⊢g ]) by now apply ext_wf_g.
    assert (HΔA' : [ G ; Δ ,, A'⟨ρ⟩ @ l1 ⊢g ]) by now apply ext_wf_g.
    exists (PiRel G Δ l1 l2 l3 l4 A⟨ρ⟩ B⟨rlift ρ⟩ A'⟨ρ⟩ B'⟨rlift ρ⟩ domR' codR'). split.
    + eapply (LRpi n (LRbelow n) G Δ T⟨ρ⟩ T'⟨ρ⟩ l l1 l2 l3 l4 A⟨ρ⟩ B⟨rlift ρ⟩ A'⟨ρ⟩ B'⟨rlift ρ⟩
                domR' codR').
      all: try eassumption.
      * exact (tyred_wk' Hρ HΔ HT).
      * exact (tyred_wk' Hρ HΔ HT').
      * exact (wf_ty_wkr (wkr_lift Hρ) HΔA HB).
      * exact (wf_ty_wkr (wkr_lift Hρ) HΔA' HB').
      * exact (geq_ty_wk' Hρ HΔ HAA).
      * exact (geq_ty_wk (wkr_lift Hρ) HΔA HBB).
      * intros Δ' ρ' Hρ' HΔ'. subst domR'; cbn.
        rewrite !ren_wk_comp_ty. apply domAd.
      * intros Δ' ρ' Hρ' HΔ' a a' ha. subst codR'; cbn.
        rewrite !ren_wk_comp_lift_ty. apply codAd.
      * apply releq_refl.
    + intros t t' Ht. apply HR in Ht.
      destruct Ht as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
      exists w⟨ρ⟩, w'⟨ρ⟩.
      refine (conj (tmred_wk' Hρ HΔ Hw) (conj (tmred_wk' Hρ HΔ Hw') (conj (whnf_ren _ _ Hnf)
                (conj (whnf_ren _ _ Hnf') (conj (geq_tm_wk' Hρ HΔ Heq)
                (conj (geq_tm_wk' Hρ HΔ Heq') _)))))).
      intros Δ' ρ' Hρ' HΔ' a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      subst codR'; cbn. rewrite !ren_wk_comp.
      rewrite ren_wk_comp_ty in HA1, HA1'. rewrite ren_wk_comp_lift_ty, ren_wk_comp_ty in HB1, HB1'.
      apply HK; assumption.
Qed.

Theorem LR_wk n : Pwk n.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_wk_step, IHn.
Qed.

End Weakening.
