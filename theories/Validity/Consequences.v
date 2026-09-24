(** * Consequences of the fundamental theorem *)
From DeLaM.Validity Require Export Fundamental.

Section Consequences.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** The identity substitution is related to itself *)

Lemma SubRel_id {G} : forall Γ, [ G ; Γ ⊢g ] -> SubRel G Γ Γ (lshift 0) (lshift 0).
Proof.
  induction Γ as [| g | Γ IH A l]; intros HΓ; cbn [SubRel].
  1-2: refine (conj HΓ (conj _ _)); intros n; cbn; constructor.
  inversion HΓ as [| | ? ? ? ? ? HΓ0 HA Hl]; subst.
  assert (Hw : wk_step wk_id : (Γ ,, A @ l) ≤ Γ) by (constructor; constructor).
  assert (Hsh : SubRel G Γ (Γ ,, A @ l) (lshift 1) (lshift 1)).
  { eapply SubRel_ext; [| | exact (SubRel_wk _ _ _ _ _ _ _ Hw HΓ (IH HΓ0))];
      intros n; rewrite llk_lren; cbn; f_equal; lia. }
  cbn [ldrop llk]. split; [exact Hsh|].
  assert (E1 : A[lshift 1] = A⟨↑⟩) by (symmetry; apply ren_as_subst_ty; reflexivity).
  change (LRtm l G (Γ ,, A @ l) A[lshift 1] A[lshift 1] (var 0) (var 0)). rewrite E1. apply var0_LRtm; [|exact HΓ].
  pose proof (proj1 (proj2 (proj2 fundamental)) _ _ _ _ _ HA eq_refl _ _ _ Hsh) as X.
  now rewrite E1 in X.
Qed.

(** ** Reducibility of every judgment *)

Lemma reducible_eqty {G Γ T T' l} : [ G ; Γ ⊢g T ≅ T' @ l ] -> LRty l G Γ T T'.
Proof.
  intros H. pose proof (ctx_of_ty (eqty_wf_l ge_typeof H)) as HΓ.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 fundamental)))) _ _ _ _ _ _ H eq_refl
                _ _ _ (SubRel_id _ HΓ)) as X.
  rewrite !nf_id_ty in X; [exact X | exact (wf_ty_nf (eqty_wf_r ge_typeof H))
                          | exact (wf_ty_nf (eqty_wf_l ge_typeof H))].
Qed.

Lemma reducible_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] -> LRty l G Γ T T.
Proof. intros H; apply reducible_eqty, eqty_refl, H. Qed.

Lemma reducible_eqtm {G Γ t t' T l} : [ G ; Γ ⊢g t ≅ t' : T @ l ] -> LRtm l G Γ T T t t'.
Proof.
  intros H. pose proof (ctx_of_tm (eqtm_wf_l ge_typeof H)) as HΓ.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 fundamental)))) _ _ _ _ _ _ _ H eq_refl
                _ _ _ (SubRel_id _ HΓ)) as X.
  pose proof (wf_ty_nf (eqtm_wf_ty ge_typeof H)) as NT.
  rewrite !nf_id_ty, !nf_id in X by first [exact NT | exact (wf_tm_nf (eqtm_wf_l ge_typeof H))
                                         | exact (wf_tm_nf (eqtm_wf_r ge_typeof H))].
  exact X.
Qed.

Lemma reducible_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] -> LRtm l G Γ T T t t.
Proof. intros H; apply reducible_eqtm, eqtm_refl, H. Qed.

(** ** Canonicity of natural numbers: every typed natural reduces to a
    related normal form ([zero], a successor, or a neutral). *)

Lemma nat_canonicity {G Γ t} : [ G ; Γ ⊢g t : tyNat @ lzero ] -> NatRel G Γ t t.
Proof. intros H; exact (proj1 LRtm_nat (reducible_tm H)). Qed.

(** ** Injectivity of type formers *)

Lemma pi_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢g tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ].
Proof.
  intros H. destruct (reducible_eqty H) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_pi HR (tyred_refl _ _ HP))
    as (m3 & m4 & C' & D' & domR & codR & _ & H3 & H4 & _ & _ & HT' & _ & _ & _ & _ & HAA & HBB & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tyPi _ _ _ _) (whnf_tyPi _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

Lemma U_inj {G Γ l l' k} : [ G ; Γ ⊢g tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof.
  intros H. destruct (reducible_eqty H) as [R HR].
  destruct (LR_inv_U HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (l2 & _ & Hl2 & _ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                (whnf_tyU _) (whnf_tyU _)) as Heq.
  now injection Heq as <-.
Qed.

(** ** Weak-head normalization *)

Lemma tmred_back {G Γ t w T W l l'} :
  [ G ; Γ ⊢g t ⤳* w : W @ l' ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : T @ l ].
Proof.
  intros Ht HT Hl. eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Ht | exact Hl] |].
  apply eqty_sym, (tyred_eq _ _ _ _ _ _ HT).
Qed.

Lemma LR_whnf_ty n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> exists W, [ G ; Γ ⊢g T ⤳* W @ l ] /\ whnf_ty W.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HAA HBB domAd codAd HR];
    eexists; split; eauto using whnf_ty, gne_ty_whne_l.
Qed.

Lemma LR_whnf_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t', R t t' ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HAA HBB domAd codAd HR];
    intros t t' Ht; apply HR in Ht.
  - destruct Ht as [t t' w w' Hw _ _ Hnf]. exists w; split; [exact (tmred_back Hw HT Hl)|].
    destruct Hnf; eauto using whnf, gne_tm_whne_l.
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (ν & ν' & Hν & _ & Hne & _). exists ν; split.
    + eapply tmred_conv; [apply ge_typeof | exact Hν | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HT)].
    + eauto using whnf, gne_tm_whne_l.
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
Qed.

Theorem whnf_normalization_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] ->
  exists W, [ G ; Γ ⊢g T ⤳* W @ l ] /\ whnf_ty W.
Proof. intros H. destruct (reducible_ty H) as [R HR]. exact (LR_whnf_ty _ _ _ _ _ _ _ _ HR). Qed.

Theorem whnf_normalization_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof.
  intros H. destruct (reducible_tm H) as (R & HR & Ht).
  exact (LR_whnf_tm _ _ _ _ _ _ _ _ HR _ _ Ht).
Qed.

(** ** Closed canonicity

    M1 has no typing rule for global variables, so a typed neutral needs a
    local variable at its head: there are no closed neutrals. *)

Lemma no_closed_neutral {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> Γ = cnil -> ~ whne t.
Proof.
  induction 1; intros -> Hne; inversion Hne; subst;
    match goal with
    | H : in_ctx cnil _ _ _ |- _ => inversion H
    | IH : cnil = cnil -> ~ whne ?x, H : whne ?x |- _ => exact (IH eq_refl H)
    end.
Qed.

Fixpoint numeral (n : nat) : tm := match n with 0 => zero | S n => succ (numeral n) end.

Theorem closed_nat_canonicity {G t} : [ G ; cnil ⊢g t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢g t ≅ numeral n : tyNat @ lzero ].
Proof.
  intros H. pose proof (nat_canonicity H) as Hn.
  refine (NatRel_mut G cnil (fun t _ _ => exists n, [ G ; cnil ⊢g t ≅ numeral n : tyNat @ lzero ])
            (fun w _ _ => exists n, [ G ; cnil ⊢g w ≅ numeral n : tyNat @ lzero ]) _ _ _ _ t t Hn).
  - intros t0 t0' w w' Hw _ _ _ (n & Hwn). exists n.
    eapply eqtm_trans; [exact (tmred_eq _ _ _ _ _ _ _ Hw) | exact Hwn].
  - exists 0. apply eqtm_refl, wf_zero; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, H].
  - intros t0 t0' _ (n & Hn'). exists (S n). cbn. apply eqtm_succ; [exact ge_notV | exact Hn'].
  - intros ν ν' Hνν. exfalso.
    exact (no_closed_neutral (gne_tm_typed_l Hνν) eq_refl (gne_tm_whne_l Hνν)).
Qed.

(** ** Discrimination of type formers *)

Lemma nat_not_pi {G Γ k l l' A B} : ~ [ G ; Γ ⊢g tyNat ≅ tyPi l l' A B @ k ].
Proof.
  intros H. destruct (reducible_eqty H) as [R HR].
  destruct (LR_inv_nat HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (_ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                whnf_tyNat (whnf_tyPi _ _ _ _)) as Heq. discriminate.
Qed.

Lemma nat_not_U {G Γ k l} : ~ [ G ; Γ ⊢g tyNat ≅ tyU l @ k ].
Proof.
  intros H. destruct (reducible_eqty H) as [R HR].
  destruct (LR_inv_nat HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (_ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                whnf_tyNat (whnf_tyU _)) as Heq. discriminate.
Qed.

Lemma U_not_pi {G Γ k l l1 l2 A B} : ~ [ G ; Γ ⊢g tyU l ≅ tyPi l1 l2 A B @ k ].
Proof.
  intros H. destruct (reducible_eqty H) as [R HR].
  destruct (LR_inv_U HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (l2' & _ & _ & _ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                (whnf_tyU _) (whnf_tyPi _ _ _ _)) as Heq. discriminate.
Qed.

End Consequences.
