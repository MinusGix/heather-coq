(** * Weakening of the logical relation (ch. 7, Weakening)

    A related pair of types stays related in every weakened context, and
    the term relation is preserved.  The Π case needs no induction
    hypothesis: its premises are already Kripke, and the weakened relation
    is the original one at composite weakenings.  The universe case uses
    weakening one stage down. *)
From DeLaM.LogRel Require Export Transitivity.

Section Weakening.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

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

End KwRel.

(** ** The statement *)

Definition Pwk n := forall G Γ T T' l R,
  LR n (LRbelow n) G Γ T T' l R -> forall ρ : kwk G Γ,
  exists R', LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l R' /\
    forall t t', R t t' -> R' (ktm ρ t) (ktm ρ t').

Lemma URel_kw n G Γ (ρ : kwk G Γ) l1 t t' :
  Pwk (lmeasure l1) -> lmeasure l1 < n ->
  URel (LRbelow n) G Γ l1 t t' -> URel (LRbelow n) (kw_G ρ) (kw_Δ ρ) l1 (ktm ρ t) (ktm ρ t').
Proof.
  intros Hwk Hn (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & HK).
  exists (ktm ρ w), (ktm ρ w').
  pose proof (kw_tmred ρ Hw) as Hw1. pose proof (kw_tmred ρ Hw') as Hw1'.
  pose proof (kw_geq_tm ρ Heq) as Heq1. rewrite kty_tyU in Hw1, Hw1', Heq1.
  refine (conj Hw1 (conj Hw1' (conj (whnf_kw ρ _ Hnf) (conj (whnf_kw ρ _ Hnf') (conj Heq1 _))))).
  intros la lb Hla Hlb. rewrite kw_gL in Hla, Hlb.
  destruct (HK la lb Hla Hlb) as [R0 H0].
  rewrite LRbelow_spec in H0 |- * by exact Hn.
  destruct (Hwk _ _ _ _ _ _ H0 ρ) as (R1 & H1 & _).
  rewrite !kty_tyEl in H1. now exists R1.
Qed.

(** ** Weakening *)

Lemma LR_kwk_step n : (forall m, m < n -> Pwk m) -> Pwk n.
Proof.
  intros IHn G Γ T T' l R H ρ.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HAA HBB domAd codAd HR].
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
    + intros t t' Ht. apply HR in Ht. eapply URel_kw; eauto; try apply IHn; lia.
  - exists (NeRel (kw_G ρ) (kw_Δ ρ) (kty ρ V) (kty ρ V') l). split.
    + eapply LRne; [exact (kw_tyred ρ HT) | exact (kw_tyred ρ HT') | exact (kw_gne_ty ρ HV)
                   | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. exact (NeRel_kw ρ _ _ _ _ _ Ht).
  - set (domR' := fun ρ' : kwk (kw_G ρ) (kw_Δ ρ) => domR (kw_comp ρ ρ')).
    set (codR' := fun (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' (ha : domR' ρ' a a') =>
                    codR (kw_comp ρ ρ') a a' ha).
    pose proof (kw_tyred ρ HT) as X. pose proof (kw_tyred ρ HT') as X'.
    rewrite kty_tyPi in X, X'.
    exists (PiRel (kw_G ρ) (kw_Δ ρ) l1 l2 l3 l4 (kty ρ A) (ktyl ρ B) (kty ρ A') (ktyl ρ B')
              domR' codR'). split.
    + eapply (LRpi n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l l1 l2 l3 l4
                (kty ρ A) (ktyl ρ B) (kty ρ A') (ktyl ρ B') domR' codR').
      * exact (kw_lequiv ρ Hl).
      * exact (kw_lequiv ρ Hl3).
      * exact (kw_lequiv ρ Hl4).
      * exact (kw_lwf ρ Hw1).
      * exact (kw_lwf ρ Hw2).
      * exact X.
      * exact X'.
      * exact (kw_ty ρ HA).
      * exact (kw_ty ρ HA').
      * exact (kw_ty_l ρ HA Hw1 HB).
      * exact (kw_ty_l ρ HA' Hw1 HB').
      * exact (kw_geq_ty ρ HAA).
      * exact (kw_geq_ty_l ρ HA Hw1 HBB).
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
      rewrite kw_gL in H1, H2, H3, H4.
      exact (HK (kw_comp ρ ρ') a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1').
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
