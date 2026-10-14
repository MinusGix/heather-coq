(** * Consequences of reducibility

    Canonicity, injectivity and discrimination of type formers, and
    weak-head normalization follow from the reducibility of every
    judgment, which the fundamental theorems give ([Reducible]).  Closed
    canonicity also needs a global context without type or term
    bindings, since global variables are closed neutrals. *)
From DeLaM.Validity Require Export Fundamental.

(** The head of a type, neutral types sharing one. *)
Definition ty_head (T : ty) : nat :=
  match T with
  | tyGvar _ _ | tyEl _ _ | tyVec _ _ _ | tyFin _ | tyDVec _ _ _ => 0 | tyNat => 1 | tyU _ => 2 | tyPi _ _ _ _ => 3
  | tyCTyp _ _ => 4 | tyCTrm _ _ _ => 5 | tyUPi _ _ _ => 6 | tyCPi _ _ => 7 | tyTPi _ _ _ _ => 8
  | tyErr => 9 | tySig _ _ _ _ => 10 | tyUnit _ => 11 | tySEq _ _ _ _ => 12 | tySEmpty _ => 13
  | tyId _ _ _ _ => 14 | tyEmpty _ => 15 | tySum _ _ _ _ => 16 | tyW _ _ _ _ => 17 | tyWf _ _ _ => 18
  | tySq _ _ => 19 | tyIWf _ _ _ _ _ _ _ _ => 20
  end.

Lemma whne_ty_head V : whne_ty V -> ty_head V = 0.
Proof. destruct 1; reflexivity. Qed.

Section Consequences.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}
  (red_eqty : forall G Γ T T' l, [ G ; Γ ⊢g T ≅ T' @ l ] -> lwf (gL G) l -> LRty l G Γ T T')
  (red_eqtm : forall G Γ t t' T l, [ G ; Γ ⊢g t ≅ t' : T @ l ] -> lwf (gL G) l -> LRtm l G Γ T T t t').

(** The relation is at well-formed levels: at ω (M4), the consequences
    come from the relation at ω instead ([DeclConsequences]). *)

Lemma reducible_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] -> lwf (gL G) l -> LRty l G Γ T T.
Proof using red_eqty. intros H Hl; apply red_eqty; [apply eqty_refl, H | exact Hl]. Qed.

Lemma reducible_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] -> lwf (gL G) l -> LRtm l G Γ T T t t.
Proof using red_eqtm. intros H Hl; apply red_eqtm; [apply eqtm_refl, H | exact Hl]. Qed.

(** ** Canonicity of natural numbers: every typed natural reduces to a
    related normal form ([zero], a successor, or a neutral). *)

Lemma nat_canonicity {G Γ t} : [ G ; Γ ⊢g t : tyNat @ lzero ] -> NatRel G Γ t t.
Proof using EL VL red_eqtm. intros H; exact (proj1 LRtm_nat (reducible_tm H I)). Qed.

(** ** Injectivity of type formers *)

Lemma pi_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢g tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_pi HR (tyred_refl _ _ HP))
    as (m3 & m4 & C' & D' & domR & codR & [_ H3 H4 _ _ _ HT' _ _ _ _ HAA HBB] & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tyPi _ _ _ _) (whnf_tyPi _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

Lemma sig_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢g tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_sig HR (tyred_refl _ _ HP))
    as (m3 & m4 & C' & D' & domR & codR & [_ H3 H4 _ _ _ HT' _ _ _ _ HAA HBB] & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tySig _ _ _ _) (whnf_tySig _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

Lemma unit_inj {G Γ l l1 l2} :
  [ G ; Γ ⊢g tyUnit l1 ≅ tyUnit l2 @ l ] -> lwf (gL G) l -> lequiv (gL G) l2 l1.
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_unit HR (tyred_refl _ _ HP)) as (m2 & _ & H2 & _ & HT' & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tyUnit _) (whnf_tyUnit _)) as Heq.
  injection Heq as <-. exact H2.
Qed.

(** Strict equality (M10a): the components, and the level. *)
Lemma seq_inj {G Γ l l1 l2 A A' a a' b b'} :
  [ G ; Γ ⊢g tySEq l1 A a b ≅ tySEq l2 A' a' b' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ⊢ a ≈ a' : A @ l1 ] /\ [ G ; Γ ⊢ b ≈ b' : A @ l1 ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_seq HR (tyred_refl _ _ HP)) as (m2 & C' & c' & d' & _ & H2 & _ & HT' & _ & HAA & Haa & Hbb & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tySEq _ _ _ _) (whnf_tySEq _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

(** The identity type (M11a): the components, and the level. *)
Lemma id_inj {G Γ l l1 l2 A A' a a' b b'} :
  [ G ; Γ ⊢g tyId l1 A a b ≅ tyId l2 A' a' b' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ⊢ a ≈ a' : A @ l1 ] /\ [ G ; Γ ⊢ b ≈ b' : A @ l1 ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_id HR (tyred_refl _ _ HP))
    as (m2 & C' & c' & d' & RA & _ & H2 & _ & HT' & _ & HAA & Haa & Hbb & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tyId _ _ _ _) (whnf_tyId _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

(** Binary sums (M12b): the summands, and the levels. *)
Lemma sum_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢g tySum l1 l2 A B ≅ tySum l3 l4 A' B' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\ [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ⊢ B ≈ B' @ l2 ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_sum HR (tyred_refl _ _ HP))
    as (m3 & m4 & C' & D' & RA & RB & _ & H3 & H4 & _ & _ & HT' & _ & HAA & _ & HBB & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tySum _ _ _ _) (whnf_tySum _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

(** Well-founded trees (M13a): as Π's. *)
Lemma W_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢g tyW l1 l2 A B ≅ tyW l3 l4 A' B' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_W HR (tyred_refl _ _ HP))
    as (m3 & m4 & C' & D' & domR & codR & [_ H3 H4 _ _ _ HT' _ _ _ _ HAA HBB] & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tyW _ _ _ _) (whnf_tyW _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

(** Finitary well-founded trees (M15a): the shapes and the arities. *)
Lemma Wf_inj {G Γ l l1 l2 A A' N N'} :
  [ G ; Γ ⊢g tyWf l1 A N ≅ tyWf l2 A' N' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢ N ≈ N' : tyNat @ lzero ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_wf HR (tyred_refl _ _ HP))
    as (m2 & C' & M' & domR & _ & H2 & _ & _ & HT' & _ & _ & _ & _ & HAA & HNN & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tyWf _ _ _) (whnf_tyWf _ _ _)) as Heq.
  injection Heq as <- <- <-. auto.
Qed.

(** Propositional truncation (M16a): the carriers, and the levels. *)
Lemma sq_inj {G Γ l l1 l2 A A'} :
  [ G ; Γ ⊢g tySq l1 A ≅ tySq l2 A' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢ A ≈ A' @ l1 ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_sq HR (tyred_refl _ _ HP)) as (m2 & C' & RC & _ & H2 & _ & _ & HT' & _ & HAA & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tySq _ _) (whnf_tySq _ _)) as Heq.
  injection Heq as <- <-. auto.
Qed.

Lemma sempty_inj {G Γ l l1 l2} :
  [ G ; Γ ⊢g tySEmpty l1 ≅ tySEmpty l2 @ l ] -> lwf (gL G) l -> lequiv (gL G) l2 l1.
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_sempty HR (tyred_refl _ _ HP)) as (m2 & _ & H2 & _ & HT' & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tySEmpty _) (whnf_tySEmpty _)) as Heq.
  injection Heq as <-. exact H2.
Qed.

(** A type convertible to a [Π] reduces to one. *)
Lemma pi_red {G Γ l l1 l2 A B T} : [ G ; Γ ⊢g tyPi l1 l2 A B ≅ T @ l ] -> lwf (gL G) l ->
  exists l3 l4 C D, [ G ; Γ ⊢g T ⤳* tyPi l3 l4 C D @ l ].
Proof using EL red_eqty.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_pi HR (tyred_refl _ _ HP)) as (m3 & m4 & C' & D' & _ & _ & [_ _ _ _ _ _ HT' _ _ _ _ _ _] & _).
  eauto.
Qed.

Lemma U_inj {G Γ l l' k} : [ G ; Γ ⊢g tyU l ≅ tyU l' @ k ] -> lwf (gL G) k -> lequiv (gL G) l' l.
Proof using EL red_eqty.
  intros H Hk. destruct (red_eqty _ _ _ _ _ H Hk) as [R HR].
  destruct (LR_inv_U HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (l2 & _ & Hl2 & _ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                (whnf_tyU _) (whnf_tyU _)) as Heq.
  now injection Heq as <-.
Qed.

(** ** Weak-head normalization *)

Lemma tmred_back {G Γ t w T W l l'} :
  [ G ; Γ ⊢g t ⤳* w : W @ l' ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : T @ l ].
Proof using .
  intros Ht HT Hl. eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Ht | exact Hl] |].
  apply eqty_sym, (tyred_eq _ _ _ _ _ _ HT).
Qed.

Lemma LR_whnf_ty n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> exists W, [ G ; Γ ⊢g T ⤳* W @ l ] /\ whnf_ty W.
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
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR];
    try match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end;
    eexists; split; eauto using whnf_ty, gne_ty_whne_l.
Qed.

Lemma ModRel_whnf_tm {G Γ T T' l R} : ModRel G Γ T T' l R -> forall t t', R t t' ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof using EL.
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
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR];
    intros t t' Ht; first [exact (ModRel_whnf_tm HM _ _ Ht) | apply HR in Ht].
  - destruct Ht as [t t' w w' Hw _ _ Hnf]. exists w; split; [exact (tmred_back Hw HT Hl)|].
    destruct Hnf; eauto using whnf, gne_tm_whne_l.
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (ν & ν' & Hν & _ & Hne & _). exists ν; split.
    + eapply tmred_conv; [apply ge_typeof | exact Hν | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HT)].
    + eauto using whnf, gne_tm_whne_l.
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (w & w' & Hr & _ & Hwh & _). exists w; split; [exact (tmred_back Hr HT Hl) | exact Hwh].
  - destruct Ht as (w & w' & Hr & _ & Hwh & _). exists w; split; [exact (tmred_back Hr HT Hl) | exact Hwh].
  - destruct Ht as (ν & ν' & Hν & _ & Hne & _). exists ν; split; [exact (tmred_back Hν HT Hl) |].
    eauto using whnf, gne_tm_whne_l.
  - destruct Ht as (w & w' & Hr & _ & _ & Hnf). exists w; split; [exact (tmred_back Hr HT Hl) |].
    exact (IdNf_whnf_l Hnf).
  - destruct Ht as (ν & ν' & Hν & _ & Hne & _). exists ν; split; [exact (tmred_back Hν HT Hl) |].
    eauto using whnf, gne_tm_whne_l.
  - destruct Ht as (w & w' & Hr & _ & _ & Hnf). exists w; split; [exact (tmred_back Hr HT Hl) |].
    exact (SumNf_whnf_l Hnf).
  - destruct (WRel_inv Ht) as (w & w' & Hr & _ & _ & Hnf). exists w; split; [exact (tmred_back Hr HT Hl) |].
    exact (WNf_whnf_l Hnf).
  - destruct (WfRel_inv Ht) as (w & w' & Hr & _ & _ & Hnf). exists w; split; [exact (tmred_back Hr HT Hl) |].
    exact (WfNf_whnf_l Hnf).
  - destruct Ht as [(w & Hr & Hnf) _]. exists w; split; [exact (tmred_back Hr HT Hl) |].
    destruct Hnf; eauto using whnf, gne_tm_whne_l.
  - destruct (IWfRel_inv Ht) as (w & w' & Hr & _ & _ & Hnf). exists w; split; [exact (tmred_back Hr HT Hl) |].
    exact (IWfNf_whnf_l Hnf).
Qed.

Theorem whnf_normalization_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] -> lwf (gL G) l ->
  exists W, [ G ; Γ ⊢g T ⤳* W @ l ] /\ whnf_ty W.
Proof using EL red_eqty. intros H Hl. destruct (reducible_ty H Hl) as [R HR]. exact (LR_whnf_ty _ _ _ _ _ _ _ _ HR). Qed.

Theorem whnf_normalization_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] -> lwf (gL G) l ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof using EL red_eqtm.
  intros H Hl. destruct (reducible_tm H Hl) as (R & HR & Ht).
  exact (LR_whnf_tm _ _ _ _ _ _ _ _ HR _ _ Ht).
Qed.

(** ** Closed canonicity

    With no term bindings in the global context, a typed neutral needs a
    local variable at its head: there are no closed neutrals. *)

(** Global contexts binding context variables only. *)
Definition ctx_only (G : gctx) : Prop := forall n D, in_gctx (gΨ G) n D -> D = gdCtx.

(** Boxed global variables mention a type or term binding. *)
Lemma tyGvar_decl {G i Γ U d l} : [ G ; Γ ⊢[ i ] tyGvar U d @ l ] ->
  exists Δ i' l', in_gctx (gΨ G) U (gdTy Δ i' l').
Proof using .
  intros H; remember (tyGvar U d) as T eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as -> ->; eauto.
Qed.
Lemma gvar_decl {G i Γ u d A l} : [ G ; Γ ⊢[ i ] gvar u d : A @ l ] ->
  exists Δ i' T l', in_gctx (gΨ G) u (gdTm Δ i' T l').
Proof using .
  intros H; remember (gvar u d) as t eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as -> ->; eauto.
Qed.
Lemma gdef_decl {G i Γ u b d A l} : [ G ; Γ ⊢[ i ] gdef u b d : A @ l ] ->
  exists Δ T l' t0, in_gctx (gΨ G) u (gdDef Δ T l' t0).
Proof using .
  intros H; remember (gdef u b d) as t eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as -> -> ->; eauto.
Qed.
Lemma boxT_inv {G i Γ T A l} : [ G ; Γ ⊢[ i ] boxT T : A @ l ] -> exists Δ l', [ G ; Δ ⊢[ lC ] T @ l' ].
Proof using .
  intros H; remember (boxT T) as t eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as ->; eauto.
Qed.
Lemma boxt_inv {G i Γ t A l} : [ G ; Γ ⊢[ i ] boxt t : A @ l ] -> exists Δ T l', [ G ; Δ ⊢[ lC ] t : T @ l' ].
Proof using .
  intros H; remember (boxt t) as x eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as ->; eauto.
Qed.

Lemma no_closed_neutral {G i Γ t T l} :
  [ G ; Γ ⊢[ i ] t : T @ l ] -> Γ = cnil -> ctx_only G -> ~ whne t.
Proof using .
  induction 1; intros -> HG Hne; inversion Hne; subst;
    match goal with
    | H : in_ctx cnil _ _ _ |- _ => inversion H
    | Hin : in_gctx _ _ (gdTm _ _ _ _) |- _ => discriminate (HG _ _ Hin)
    | IH : cnil = cnil -> ctx_only _ -> ~ whne ?x, H : whne ?x |- _ => exact (IH eq_refl HG H)
    (* recursors on boxed global variables *)
    | H : wf_tm _ _ _ (boxT (tyGvar _ _)) _ _ |- _ =>
        destruct (boxT_inv H) as (? & ? & HT); destruct (tyGvar_decl HT) as (? & ? & ? & Hin);
        discriminate (HG _ _ Hin)
    | H : wf_tm _ _ _ (boxt (gvar _ _)) _ _ |- _ =>
        destruct (boxt_inv H) as (? & ? & ? & Ht); destruct (gvar_decl Ht) as (? & ? & ? & ? & Hin);
        discriminate (HG _ _ Hin)
    | H : wf_tm _ _ _ (boxt (gdef _ _ _)) _ _ |- _ =>
        destruct (boxt_inv H) as (? & ? & ? & Ht); destruct (gdef_decl Ht) as (? & ? & ? & ? & Hin);
        discriminate (HG _ _ Hin)
    end.
Qed.

(** With definitions (M9): at D there are no boxes and no recursors, so a
    global context of context variables and definitions has no closed
    neutrals either. The argument stops at M: [elim(box(u^δ))] with [u]
    defined is neutral ([whne_elimt_gdef]; Heather's rules keep it stuck,
    M9_DESIGN.md step 4), and closed when [δ] is. *)
Definition no_opaque (G : gctx) : Prop :=
  forall n D, in_gctx (gΨ G) n D -> D = gdCtx \/ exists Δ T l t, D = gdDef Δ T l t.

Lemma no_closed_neutral_D {G i Γ t T l} :
  [ G ; Γ ⊢[ i ] t : T @ l ] -> Γ = cnil -> i = lD -> no_opaque G -> ~ whne t.
Proof using .
  induction 1; intros -> Ei HG Hne; try discriminate Ei; subst; inversion Hne; subst;
    match goal with
    | H : in_ctx cnil _ _ _ |- _ => inversion H
    | Hin : in_gctx _ _ (gdTm _ _ _ _) |- _ =>
        destruct (HG _ _ Hin) as [Q | (? & ? & ? & ? & Q)]; discriminate Q
    | IH : cnil = cnil -> ?j = lD -> no_opaque _ -> ~ whne ?x, H : whne ?x |- _ => exact (IH eq_refl eq_refl HG H)
    end.
Qed.

(** The global contexts closed canonicity holds in, at layer [i]. *)
Definition closed_ok (i : layer) (G : gctx) : Prop := ctx_only G \/ (i = lD /\ no_opaque G).

Lemma no_closed_neutral_ok {G i t T l} : closed_ok i G -> [ G ; cnil ⊢[ i ] t : T @ l ] -> ~ whne t.
Proof using .
  intros [HG | (Ei & HG)] Ht; [exact (no_closed_neutral Ht eq_refl HG) | exact (no_closed_neutral_D Ht eq_refl Ei HG)].
Qed.

Lemma closed_ok_no_opaque {i G} : closed_ok i G -> no_opaque G.
Proof using . intros [HG | (_ & HG)] n D Hin; [left; exact (HG _ _ Hin) | exact (HG _ _ Hin)]. Qed.

Lemma no_opaque_tyGvar {G U Δ i' l} : no_opaque G -> ~ in_gctx (gΨ G) U (gdTy Δ i' l).
Proof using . intros HG Hin. destruct (HG _ _ Hin) as [Q | (? & ? & ? & ? & Q)]; discriminate Q. Qed.
Lemma no_opaque_gvar {G u Δ i' T l} : no_opaque G -> ~ in_gctx (gΨ G) u (gdTm Δ i' T l).
Proof using . intros HG Hin. destruct (HG _ _ Hin) as [Q | (? & ? & ? & ? & Q)]; discriminate Q. Qed.

Lemma closed_ok_tyGvar {G i U Δ i' l} : closed_ok i G -> ~ in_gctx (gΨ G) U (gdTy Δ i' l).
Proof using . intros HG; exact (no_opaque_tyGvar (closed_ok_no_opaque HG)). Qed.
Lemma closed_ok_gvar {G i u Δ i' T l} : closed_ok i G -> ~ in_gctx (gΨ G) u (gdTm Δ i' T l).
Proof using . intros HG; exact (no_opaque_gvar (closed_ok_no_opaque HG)). Qed.

(** At M, [closed_ok] is [ctx_only] (DefStuck.v: with a definition, M has
    closed neutrals). *)
Lemma closed_ok_M_ctx_only {G} : closed_ok lM G -> ctx_only G.
Proof using . intros [H | (Ei & _)]; [exact H | discriminate Ei]. Qed.

Fixpoint numeral (n : nat) : tm := match n with 0 => zero | S n => succ (numeral n) end.

Theorem closed_nat_canonicity {G t} : closed_ok ge_layer G -> [ G ; cnil ⊢g t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢g t ≅ numeral n : tyNat @ lzero ].
Proof using EL VL red_eqtm.
  intros HG H. pose proof (nat_canonicity H) as Hn.
  refine (NatRel_mut G cnil (fun t _ _ => exists n, [ G ; cnil ⊢g t ≅ numeral n : tyNat @ lzero ])
            (fun w _ _ => exists n, [ G ; cnil ⊢g w ≅ numeral n : tyNat @ lzero ]) _ _ _ _ t t Hn).
  - intros t0 t0' w w' Hw _ _ _ (n & Hwn). exists n.
    eapply eqtm_trans; [exact (tmred_eq _ _ _ _ _ _ _ Hw) | exact Hwn].
  - exists 0. apply eqtm_refl, wf_zero; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, H].
  - intros t0 t0' _ (n & Hn'). exists (S n). cbn. apply eqtm_succ; [exact ge_notV | exact Hn'].
  - intros ν ν' Hνν. exfalso.
    exact (no_closed_neutral_ok HG (gne_tm_typed_l Hνν) (gne_tm_whne_l Hνν)).
Qed.

(** ** Discrimination of type formers *)

Lemma nat_not_pi {G Γ k l l' A B} : lwf (gL G) k -> ~ [ G ; Γ ⊢g tyNat ≅ tyPi l l' A B @ k ].
Proof using EL red_eqty.
  intros Hk H. destruct (red_eqty _ _ _ _ _ H Hk) as [R HR].
  destruct (LR_inv_nat HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (_ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                whnf_tyNat (whnf_tyPi _ _ _ _)) as Heq. discriminate.
Qed.

Lemma nat_not_U {G Γ k l} : lwf (gL G) k -> ~ [ G ; Γ ⊢g tyNat ≅ tyU l @ k ].
Proof using EL red_eqty.
  intros Hk H. destruct (red_eqty _ _ _ _ _ H Hk) as [R HR].
  destruct (LR_inv_nat HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (_ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                whnf_tyNat (whnf_tyU _)) as Heq. discriminate.
Qed.

Lemma U_not_pi {G Γ k l l1 l2 A B} : lwf (gL G) k -> ~ [ G ; Γ ⊢g tyU l ≅ tyPi l1 l2 A B @ k ].
Proof using EL red_eqty.
  intros Hk H. destruct (red_eqty _ _ _ _ _ H Hk) as [R HR].
  destruct (LR_inv_U HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (l2' & _ & _ & _ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                (whnf_tyU _) (whnf_tyPi _ _ _ _)) as Heq. discriminate.
Qed.

(** ** Discrimination, uniformly: convertible whnf types have the same head *)

Lemma LR_head n rec G Γ T T' l R : LR n rec G Γ T T' l R ->
  exists W W', ([ G ; Γ ⊢g T ⤳* W @ l ]) /\ ([ G ; Γ ⊢g T' ⤳* W' @ l ]) /\
    whnf_ty W /\ whnf_ty W' /\ ty_head W = ty_head W'.
Proof using EL.
  destruct 1; open_poly; try match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end;
  match goal with |- exists _ _, [ _ ; _ ⊢g ?a ⤳* _ @ _ ] /\ [ _ ; _ ⊢g ?b ⤳* _ @ _ ] /\ _ =>
    match goal with HT : [ _ ; _ ⊢g a ⤳* ?X @ _ ], HT' : [ _ ; _ ⊢g b ⤳* ?X' @ _ ] |- _ =>
      exists X, X'; refine (conj HT (conj HT' _)) end end;
  first [ match goal with Hn : [ _ ; _ ⊢ _ ~ _ @ _ ] |- _ =>
            pose proof (gne_ty_whne_l Hn); pose proof (gne_ty_whne_r Hn) end;
          refine (conj _ (conj _ _)); [apply whnf_ty_ne; assumption | apply whnf_ty_ne; assumption |];
          rewrite !whne_ty_head by assumption; reflexivity
        | refine (conj _ (conj _ eq_refl)); eauto using whnf_ty ].
Qed.

Lemma eqty_head {G Γ W W' l} : [ G ; Γ ⊢g W ≅ W' @ l ] -> lwf (gL G) l -> whnf_ty W -> whnf_ty W' ->
  ty_head W = ty_head W'.
Proof using EL red_eqty.
  intros H Hl Hw Hw'. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  destruct (LR_head _ _ _ _ _ _ _ _ HR) as (X & X' & HX & HX' & Hx & Hx' & Eh).
  rewrite <- (tyred_whnf_det _ _ _ _ _ _ _ _ HX (tyred_refl _ _ (eqty_wf_l ge_typeof H)) Hx Hw).
  rewrite <- (tyred_whnf_det _ _ _ _ _ _ _ _ HX' (tyred_refl _ _ (eqty_wf_r ge_typeof H)) Hx' Hw').
  exact Eh.
Qed.

End Consequences.
