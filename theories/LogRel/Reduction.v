(** * Closure under typed weak-head expansion (ch. 7, Weak Head Expansion)

    Types (and terms) that reduce to related ones are related, with the
    same term relation. *)
From DeLaM.LogRel Require Export Neutral.

Section Reduction.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma tmred_along {G Γ t u T W l l'} :
  [ G ; Γ ⊢g t ⤳* u : T @ l ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> lequiv (gL G) l' l ->
  [ G ; Γ ⊢g t ⤳* u : W @ l' ].
Proof.
  intros Ht HT Hl. eapply tmred_lconv; [|exact Hl].
  eapply tmred_conv; [apply ge_typeof | exact Ht | apply HT].
Qed.

Lemma ModRel_red_ty {G Γ T T' l R T1 T1'} : ModRel G Γ T T' l R ->
  [ G ; Γ ⊢g T1 ⤳* T @ l ] -> [ G ; Γ ⊢g T1' ⤳* T' @ l ] -> ModRel G Γ T1 T1' l R.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR]; intros H1 H1'.
  - exact (MRctyp _ _ _ _ _ _ _ _ _ _ Hl Hk (tyred_trans _ _ _ _ H1 HT) (tyred_trans _ _ _ _ H1' HT')
             HΔ Hgeq HR).
  - exact (MRctrm _ _ _ _ _ _ _ _ _ _ _ _ Hl Hk (tyred_trans _ _ _ _ H1 HT)
             (tyred_trans _ _ _ _ H1' HT') HΔ HA HA' Hgeq HR).
Qed.

Lemma ModRel_red_tm {G Γ T T' l R} : ModRel G Γ T T' l R -> forall t t' t1 t1', R t t' ->
  [ G ; Γ ⊢g t1 ⤳* t : T @ l ] -> [ G ; Γ ⊢g t1' ⤳* t' : T' @ l ] -> R t1 t1'.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros t t' t1 t1' Htt H1 H1'; apply HR; apply HR in Htt;
    destruct Htt as (w & w' & Hw & Hw' & Htt);
    exists w, w'; refine (conj _ (conj _ Htt)).
  all: eapply tmred_trans; [|eassumption].
  all: eapply tmred_along; [eassumption | eassumption | now apply lequiv_sym].
Qed.

Theorem LR_red_ty n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall T1 T1',
  [ G ; Γ ⊢g T1 ⤳* T @ l ] -> [ G ; Γ ⊢g T1' ⤳* T' @ l ] -> LR n rec G Γ T1 T1' l R.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l l1 l2 U1 U1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 U1 U1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros T1 T1' H1 H1'.
  - eapply LRnat; eauto using tyred_trans.
  - eapply LRU with (l1 := l1) (l2 := l2); eauto using tyred_trans.
  - eapply LRne with (V := V) (V' := V'); eauto using tyred_trans.
  - eapply (LRpi n rec G Γ T1 T1' l l1 l2 l3 l4 A B A' B' domR codR); [split|..]; eauto using tyred_trans.
  - apply LRmod; [exact Hj | exact (ModRel_red_ty HM H1 H1')].
  - eapply (LRcpi n rec G Γ T1 T1' l l1 l2 U1 U1' instR); eauto using tyred_trans.
  - eapply (LRtpi n rec G Γ T1 T1' l Δ1 Δ1' l1 l2 l3 l4 U1 U1' instR); eauto using tyred_trans.
  - eapply (LRsig n rec G Γ T1 T1' l l1 l2 l3 l4 A B A' B' domR codR); [split|..]; eauto using tyred_trans.
  - eapply (LRunit n rec G Γ T1 T1' l l1 l2); eauto using tyred_trans.
  - eapply (LRseq n rec G Γ T1 T1' l s1 s2); eauto using tyred_trans.
  - eapply (LRsempty n rec G Γ T1 T1' l s1 s2); eauto using tyred_trans.
  - eapply (LRid n rec G Γ T1 T1' l s1 s2); eauto using tyred_trans.
  - eapply (LRempty n rec G Γ T1 T1' l s1 s2); eauto using tyred_trans.
Qed.

Theorem LR_red_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t' t1 t1', R t t' ->
  [ G ; Γ ⊢g t1 ⤳* t : T @ l ] -> [ G ; Γ ⊢g t1' ⤳* t' : T' @ l ] -> R t1 t1'.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros t t' t1 t1' Htt H1 H1';
    first [exact (ModRel_red_tm HM _ _ _ _ Htt H1 H1') | apply HR; apply HR in Htt].
  - inversion Htt as [? ? w w' Hw Hw' Heq Hnf]; subst.
    econstructor; [| |exact Heq|exact Hnf].
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | now apply lequiv_sym].
  - destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq HK))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hw']. eapply (tmred_lconv _ _ _ _ l); [|now apply lequiv_sym].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv.
      * apply eqty_U; [exact ge_notV | rewrite ge_typeof; eapply tyred_ctx, HT | exact Hl2].
      * eapply lequiv_trans; [exact Hl | apply lequiv_suc, lequiv_sym, Hl2].
  - destruct Htt as (ν & ν' & Hν & Hν' & Hn & Hn').
    exists ν, ν'. refine (conj _ (conj _ (conj Hn Hn'))).
    + eapply tmred_trans; [|exact Hν]. eapply tmred_conv; [apply ge_typeof | exact H1 | apply HT].
    + eapply tmred_trans; [|exact Hν']. eapply tmred_conv; [apply ge_typeof | exact H1' | apply HT'].
  - destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq (conj Heq' HK)))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | now apply lequiv_sym].
  - (* CΠ *)
    destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq (conj Heq' HK)))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | now apply lequiv_sym].
  - (* TΠ *)
    destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq (conj Heq' HK)))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | now apply lequiv_sym].
  - (* Σ *)
    destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq (conj Heq' HK)))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | now apply lequiv_sym].
  - (* Unit *)
    destruct Htt as (w & w' & Hr & Hr' & Hn & Hn'). exists w, w'.
    refine (conj _ (conj _ (conj Hn Hn'))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hr']. apply (unit_tmred_conv Hl2).
      eapply tmred_along; [exact H1' | exact HT' | eapply lequiv_trans; [exact Hl2 | now apply lequiv_sym]].
  - (* sEq: the right side at the left's type *)
    destruct Htt as (w & w' & Hr & Hr' & Hn & Hn'). exists w, w'.
    refine (conj _ (conj _ (conj Hn Hn'))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|now apply lequiv_sym].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_seq; auto using lequiv_sym.
  - (* sEmpty *)
    destruct Htt as (w & w' & Hr & Hr' & Hn & Hn'). exists w, w'.
    refine (conj _ (conj _ (conj Hn Hn'))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hr']. apply (sempty_tmred_conv Hl2).
      eapply tmred_along; [exact H1' | exact HT' | eapply lequiv_trans; [exact Hl2 | now apply lequiv_sym]].
  - (* Id: the right side at the left's type, as for sEq *)
    destruct Htt as (w & w' & Hr & Hr' & Heq & Hn). exists w, w'.
    refine (conj _ (conj _ (conj Heq Hn))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|now apply lequiv_sym].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_id; auto using lequiv_sym.
  - (* Empty *)
    destruct Htt as (w & w' & Hr & Hr' & Hn). exists w, w'.
    refine (conj _ (conj _ Hn)).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
    + eapply tmred_trans; [|exact Hr']. apply (empty_tmred_conv Hl2).
      eapply tmred_along; [exact H1' | exact HT' | eapply lequiv_trans; [exact Hl2 | now apply lequiv_sym]].
Qed.

End Reduction.
