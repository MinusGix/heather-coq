(** * Consequences of reducibility

    Canonicity, injectivity and discrimination of type formers, and
    weak-head normalization follow from the reducibility of every
    judgment, which the fundamental theorems give ([Reducible]).  Closed
    canonicity also needs a global context without type or term
    bindings, since global variables are closed neutrals. *)
From DeLaM.Validity Require Export Fundamental.

Section Consequences.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}
  (red_eqty : forall G Γ T T' l, [ G ; Γ ⊢g T ≅ T' @ l ] -> LRty l G Γ T T')
  (red_eqtm : forall G Γ t t' T l, [ G ; Γ ⊢g t ≅ t' : T @ l ] -> LRtm l G Γ T T t t').

Lemma reducible_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] -> LRty l G Γ T T.
Proof. intros H; apply red_eqty, eqty_refl, H. Qed.

Lemma reducible_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] -> LRtm l G Γ T T t t.
Proof. intros H; apply red_eqtm, eqtm_refl, H. Qed.

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
  intros H. destruct (red_eqty _ _ _ _ _ H) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_pi HR (tyred_refl _ _ HP))
    as (m3 & m4 & C' & D' & domR & codR & _ & H3 & H4 & _ & _ & HT' & _ & _ & _ & _ & HAA & HBB & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tyPi _ _ _ _) (whnf_tyPi _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

Lemma U_inj {G Γ l l' k} : [ G ; Γ ⊢g tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof.
  intros H. destruct (red_eqty _ _ _ _ _ H) as [R HR].
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
                    HA HA' HB HB' HAA HBB domAd codAd HR
                | G Γ T T' l R Hj HM];
    try match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end;
    eexists; split; eauto using whnf_ty, gne_ty_whne_l.
Qed.

Lemma ModRel_whnf_tm {G Γ T T' l R} : ModRel G Γ T T' l R -> forall t t', R t t' ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros t t' Ht; apply HR in Ht; destruct Ht as (w & w' & Hw & _ & _ & _ & Hn & _);
    exists w; (split; [exact (tmred_back Hw HT Hl) |]).
  - exact (CTypNf_whnf_l Hn).
  - exact (CTrmNf_whnf_l Hn).
Qed.

Lemma LR_whnf_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t', R t t' ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HAA HBB domAd codAd HR
                | G Γ T T' l R Hj HM];
    intros t t' Ht; first [exact (ModRel_whnf_tm HM _ _ Ht) | apply HR in Ht].
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

    With no term bindings in the global context, a typed neutral needs a
    local variable at its head: there are no closed neutrals. *)

(** Global contexts binding context variables only. *)
Definition ctx_only (G : gctx) : Prop := forall n D, in_gctx (gΨ G) n D -> D = gdCtx.

Lemma no_closed_neutral {G i Γ t T l} :
  [ G ; Γ ⊢[ i ] t : T @ l ] -> Γ = cnil -> ctx_only G -> ~ whne t.
Proof.
  induction 1; intros -> HG Hne; inversion Hne; subst;
    match goal with
    | H : in_ctx cnil _ _ _ |- _ => inversion H
    | Hin : in_gctx _ _ (gdTm _ _ _ _) |- _ => discriminate (HG _ _ Hin)
    | IH : cnil = cnil -> ctx_only _ -> ~ whne ?x, H : whne ?x |- _ => exact (IH eq_refl HG H)
    end.
Qed.

Fixpoint numeral (n : nat) : tm := match n with 0 => zero | S n => succ (numeral n) end.

Theorem closed_nat_canonicity {G t} : ctx_only G -> [ G ; cnil ⊢g t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢g t ≅ numeral n : tyNat @ lzero ].
Proof.
  intros HG H. pose proof (nat_canonicity H) as Hn.
  refine (NatRel_mut G cnil (fun t _ _ => exists n, [ G ; cnil ⊢g t ≅ numeral n : tyNat @ lzero ])
            (fun w _ _ => exists n, [ G ; cnil ⊢g w ≅ numeral n : tyNat @ lzero ]) _ _ _ _ t t Hn).
  - intros t0 t0' w w' Hw _ _ _ (n & Hwn). exists n.
    eapply eqtm_trans; [exact (tmred_eq _ _ _ _ _ _ _ Hw) | exact Hwn].
  - exists 0. apply eqtm_refl, wf_zero; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, H].
  - intros t0 t0' _ (n & Hn'). exists (S n). cbn. apply eqtm_succ; [exact ge_notV | exact Hn'].
  - intros ν ν' Hνν. exfalso.
    exact (no_closed_neutral (gne_tm_typed_l Hνν) eq_refl HG (gne_tm_whne_l Hνν)).
Qed.

(** ** Discrimination of type formers *)

Lemma nat_not_pi {G Γ k l l' A B} : ~ [ G ; Γ ⊢g tyNat ≅ tyPi l l' A B @ k ].
Proof.
  intros H. destruct (red_eqty _ _ _ _ _ H) as [R HR].
  destruct (LR_inv_nat HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (_ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                whnf_tyNat (whnf_tyPi _ _ _ _)) as Heq. discriminate.
Qed.

Lemma nat_not_U {G Γ k l} : ~ [ G ; Γ ⊢g tyNat ≅ tyU l @ k ].
Proof.
  intros H. destruct (red_eqty _ _ _ _ _ H) as [R HR].
  destruct (LR_inv_nat HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (_ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                whnf_tyNat (whnf_tyU _)) as Heq. discriminate.
Qed.

Lemma U_not_pi {G Γ k l l1 l2 A B} : ~ [ G ; Γ ⊢g tyU l ≅ tyPi l1 l2 A B @ k ].
Proof.
  intros H. destruct (red_eqty _ _ _ _ _ H) as [R HR].
  destruct (LR_inv_U HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (l2' & _ & _ & _ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                (whnf_tyU _) (whnf_tyPi _ _ _ _)) as Heq. discriminate.
Qed.

End Consequences.
