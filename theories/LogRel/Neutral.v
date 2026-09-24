(** * Reflection of neutrals (ch. 7, Reflexivity of Neutral)

    Neutral terms that are generically equal at both related types are
    related.  By induction on the derivation; the universe case builds a
    neutral derivation one stage down, the Π case applies the neutral
    congruence law for application. *)
From DeLaM.LogRel Require Export Weakening.

Section Neutral.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

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

(** ** Reflection *)

Theorem LR_neutral n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> forall ν ν',
  [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢ ν ~ ν' : T' @ l ] -> R ν ν'.
Proof.
  induction 1 as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                     HA HA' HB HB' HAA HBB domAd IHdom codAd IHcod HR];
    intros ν ν' Hν Hν'; apply HR.
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
    intros Δ ρ Hρ HΔ a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    (* facts in the weakened context *)
    assert (HAr : [ G ; Δ ⊢g A⟨ρ⟩ @ l1 ]) by exact (wf_ty_wk Hρ HΔ HA).
    assert (HA'r : [ G ; Δ ⊢g A'⟨ρ⟩ @ l1 ]) by exact (wf_ty_wk Hρ HΔ HA').
    assert (HΔA : [ G ; Δ ,, A⟨ρ⟩ @ l1 ⊢g ]) by now apply ext_wf_g.
    assert (EA : [ G ; Δ ⊢ A⟨ρ⟩ ≈ A'⟨ρ⟩ @ l1 ]) by exact (geq_ty_wk' Hρ HΔ HAA).
    assert (EB : [ G ; Δ ,, A⟨ρ⟩ @ l1 ⊢ B⟨rlift ρ⟩ ≈ B'⟨rlift ρ⟩ @ l2 ])
      by exact (geq_ty_wk (wkr_lift Hρ) HΔA HBB).
    assert (HA1w : [ G ; Δ ⊢g A1 @ la ]).
    { eapply lconv_ty; [exact (eqty_wf_r ge_typeof (geq_ty_sound HA1)) | now apply lequiv_sym]. }
    assert (HΔA1 : [ G ; Δ ,, A1 @ la ⊢g ]) by (apply ext_wf_g; eauto using lequiv_wf_l).
    destruct (escape_tm _ _ _ _ _ _ _ _ (domAd Δ ρ Hρ HΔ) a a' ha) as (Ha & Ha' & Haa).
    (* the two annotations agree *)
    assert (EA1 : [ G ; Δ ⊢ A1 ≈ A1' @ la ]).
    { eapply geq_ty_lconv; [|exact Hla].
      eapply geq_ty_trans; [apply geq_ty_sym, HA1 | eapply geq_ty_trans; [exact EA | exact HA1']]. }
    assert (EB1 : [ G ; Δ ,, A1 @ la ⊢ B1 ≈ B1' @ lb ]).
    { eapply geq_ty_lconv; [|exact Hlb].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, HA1 | now apply lequiv_sym | exact HΔA1 |].
      eapply geq_ty_trans; [apply geq_ty_sym, HB1 | eapply geq_ty_trans; [exact EB |]].
      eapply geq_ty_ctxconv; [apply geq_ty_sound, geq_ty_sym, EA | apply lequiv_refl, Hw1
                             | exact HΔA | exact HB1']. }
    assert (Hνr : [ G ; Δ ⊢ ν⟨ρ⟩ ~ ν'⟨ρ⟩ : tyPi la lb A1 B1 @ lmax la lb ]).
    { eapply (gne_tm_lconv (l' := lmax l1 l2)); [|now apply lequiv_max].
      eapply gne_tm_conv; [exact (gne_tm_wk' Hρ HΔ HP)|].
      apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym. }
    assert (Haa1 : [ G ; Δ ⊢ a ≈ a' : A1 @ la ]).
    { eapply geq_tm_conv_l; [exact Haa | | exact Hla].
      eapply eqty_lconv; [apply geq_ty_sound, HA1 | exact Hla]. }
    pose proof (gne_tm_app (lequiv_trans _ _ _ _ Hla (lequiv_sym _ _ _ Hla'))
                  (lequiv_trans _ _ _ _ Hlb (lequiv_sym _ _ _ Hlb')) HA1w EA1 EB1 Hνr Haa1) as X.
    assert (X1 : [ G ; Δ ⊢ app ν⟨ρ⟩ la lb A1 B1 a ~ app ν'⟨ρ⟩ la' lb' A1' B1' a'
                     : B⟨rlift ρ⟩[lsingle a] @ l2 ]).
    { eapply gne_tm_conv; [eapply gne_tm_lconv; [exact X | now apply lequiv_sym]|].
      apply (eqty_single ge_typeof (geq_ty_sound (geq_ty_sym HB1)) Ha). }
    apply (IHcod Δ ρ Hρ HΔ a a' ha); [exact X1|].
    eapply gne_tm_conv; [exact X1|].
    destruct (escape_ty _ _ _ _ _ _ _ _ (codAd Δ ρ Hρ HΔ a a' ha)) as (_ & _ & Hc).
    now apply geq_ty_sound.
Qed.

End Neutral.
