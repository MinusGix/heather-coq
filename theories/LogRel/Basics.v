(** * Structural lemmas: stages and level conversion *)
From DeLaM.LogRel Require Export Escape.

Section Basics.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Measures of levels *)

Lemma lequiv_measure_eq L l l' : lequiv L l l' -> lmeasure l = lmeasure l'.
Proof using . apply lequiv_measure. Qed.

Lemma lmeasure_max l1 l2 : lmeasure (lmax l1 l2) = Nat.max (lmeasure l1) (lmeasure l2).
Proof using . reflexivity. Qed.
Lemma lmeasure_suc l : lmeasure (lsuc l) = S (lmeasure l).
Proof using . reflexivity. Qed.

(** ** The universe relation only depends on [rec] at its level *)

Lemma URel_ext rec rec' G Γ l0 : rec l0 = rec' l0 -> URel rec G Γ l0 = URel rec' G Γ l0.
Proof using . intros Hr. unfold URel. now rewrite Hr. Qed.

Lemma URel_below n m G Γ l0 : lmeasure l0 < n -> lmeasure l0 < m ->
  URel (LRbelow n) G Γ l0 = URel (LRbelow m) G Γ l0.
Proof using . intros Hn Hm. apply URel_ext. now rewrite !LRbelow_spec. Qed.

(** ** Cumulativity of stages *)

Theorem cumul_up n m G Γ T T' l R :
  n <= m -> LR n (LRbelow n) G Γ T T' l R -> LR m (LRbelow m) G Γ T T' l R.
Proof using .
  intros Hnm H; induction H; open_poly.
  - eapply LRnat; eauto.
  - match goal with HR : releq _ (URel _ _ _ _) |- _ => rewrite (URel_below n m) in HR by lia end.
    eapply LRU with (l1 := l1) (l2 := l2); eauto; lia.
  - eapply LRne; eauto.
  - eapply LRpi; [split|..]; eauto.
  - eapply LRmod; eauto.
  - eapply LRcpi with (l1 := l1) (l2 := l2) (T1 := T1) (T1' := T1') (instR := instR); eassumption.
  - eapply LRtpi with (Δ1 := Δ1) (Δ1' := Δ1') (l1 := l1) (l2 := l2) (l3 := l3) (l4 := l4)
      (T1 := T1) (T1' := T1') (instR := instR); eassumption.
  - eapply LRsig; [split|..]; eauto.
  - eapply LRunit; eauto.
  - eapply LRseq; eauto.
  - eapply LRsempty; eauto.
  - eapply LRid; eauto.
  - eapply LRempty; eauto.
  - eapply (LRsum _ _ _ _ _ _ _ l1 l2 l3 l4 A A' B B' RA RB); eauto.
  - eapply LRw; [split|..]; eauto.
  - eapply LRwf; eauto.
  - eapply LRsq; eauto.
  - eapply LRiwf; eauto.
  - eapply LRm; eauto.
Qed.

Theorem cumul_down n m G Γ T T' l R :
  lmeasure l <= n -> LR m (LRbelow m) G Γ T T' l R -> LR n (LRbelow n) G Γ T T' l R.
Proof using .
  intros Hl H; revert Hl; induction H; intros Hle; open_poly.
  - eapply LRnat; eauto.
  - assert (lmeasure l1 < n).
    { match goal with Hs : lequiv _ l (lsuc l1) |- _ =>
        rewrite (lequiv_measure_eq _ _ _ Hs), lmeasure_suc in Hle end. lia. }
    match goal with HR : releq _ (URel _ _ _ _) |- _ => rewrite (URel_below m n) in HR by lia end.
    eapply LRU with (l1 := l1) (l2 := l2); eauto.
  - eapply LRne; eauto.
  - match goal with Hs : lequiv _ l (lmax l1 l2) |- _ =>
      rewrite (lequiv_measure_eq _ _ _ Hs), lmeasure_max in Hle end.
    eapply LRpi; [split|..]; eauto.
    all: intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; lia end.
  - eapply LRmod; eauto.
  - match goal with Hs : lequiv _ l l1 |- _ => rewrite (lequiv_measure_eq _ _ _ Hs) in Hle end.
    eapply LRcpi with (l1 := l1) (l2 := l2) (T1 := T1) (T1' := T1') (instR := instR); try eassumption.
    intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; lia end.
  - match goal with Hs : lequiv _ l l2 |- _ => rewrite (lequiv_measure_eq _ _ _ Hs) in Hle end.
    eapply LRtpi with (Δ1 := Δ1) (Δ1' := Δ1') (l1 := l1) (l2 := l2) (l3 := l3) (l4 := l4)
      (T1 := T1) (T1' := T1') (instR := instR); try eassumption.
    intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; lia end.
  - match goal with Hs : lequiv _ l (lmax l1 l2) |- _ =>
      rewrite (lequiv_measure_eq _ _ _ Hs), lmeasure_max in Hle end.
    eapply LRsig; [split|..]; eauto.
    all: intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; lia end.
  - eapply LRunit; eauto.
  - eapply LRseq; eauto.
  - eapply LRsempty; eauto.
  - match goal with Hs : lequiv _ l l1 |- _ => rewrite (lequiv_measure_eq _ _ _ Hs) in Hle end.
    eapply LRid; eauto.
  - eapply LRempty; eauto.
  - match goal with Hs : lequiv _ l (lmax l1 l2) |- _ =>
      rewrite (lequiv_measure_eq _ _ _ Hs), lmeasure_max in Hle end.
    eapply (LRsum _ _ _ _ _ _ _ l1 l2 l3 l4 A A' B B' RA RB); try eassumption.
    all: match goal with IH : lmeasure ?a <= _ -> LR _ _ _ _ _ _ ?a _ |- LR _ _ _ _ _ _ ?a _ =>
           apply IH; lia end.
  - match goal with Hs : lequiv _ l (lmax l1 l2) |- _ =>
      rewrite (lequiv_measure_eq _ _ _ Hs), lmeasure_max in Hle end.
    eapply LRw; [split|..]; eauto.
    all: intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; lia end.
  - match goal with Hs : lequiv _ l l1 |- _ => rewrite (lequiv_measure_eq _ _ _ Hs) in Hle end.
    eapply LRwf; eauto.
    all: intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; lia end.
  - match goal with Hs : lequiv _ l l1 |- _ => rewrite (lequiv_measure_eq _ _ _ Hs) in Hle end.
    eapply LRsq; eauto.
  - match goal with Hs : lequiv _ l (lmax l1 li1) |- _ =>
      rewrite (lequiv_measure_eq _ _ _ Hs), lmeasure_max in Hle end.
    eapply LRiwf; eauto.
    all: intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; lia end.
  - match goal with Hs : lequiv _ l (mlvl l1 l2 li) |- _ =>
      rewrite (lequiv_measure_eq _ _ _ Hs), !lmeasure_max in Hle end.
    eapply LRm; eauto.
    all: intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; [eassumption .. | lia] end.
Qed.

(** A type at level [l] is related identically at every stage above
    [lmeasure l]. *)
Corollary LogRel_stage n G Γ T T' l R :
  lmeasure l <= n -> LogRel l G Γ T T' l R <-> LR n (LRbelow n) G Γ T T' l R.
Proof using .
  intros Hn; split; intros H.
  - eapply cumul_up; [exact Hn | exact H].
  - eapply cumul_down; [lia | exact H].
Qed.

(** ** Level conversion *)


Lemma NeRel_lconv G Γ V V' l l' :
  lequiv (gL G) l' l -> releq (NeRel G Γ V V' l) (NeRel G Γ V V' l').
Proof using EL.
  intros Hl t t'; unfold NeRel; split; intros (ν & ν' & H1 & H2 & H3 & H4);
    exists ν, ν'; refine (conj _ (conj _ (conj _ _)));
    eauto using tmred_lconv, gne_tm_lconv, lequiv_sym.
Qed.

(** ** Saturation: the term relation matters only up to [releq] *)

Lemma releq_refl R : releq R R.
Proof using . intros ??; reflexivity. Qed.
Lemma releq_sym R R' : releq R R' -> releq R' R.
Proof using . intros H ??; symmetry; apply H. Qed.
Lemma releq_trans R R' R'' : releq R R' -> releq R' R'' -> releq R R''.
Proof using . intros H H' ??; etransitivity; [apply H | apply H']. Qed.

Lemma ModRel_releq G Γ T T' l R R' : ModRel G Γ T T' l R -> releq R R' -> ModRel G Γ T T' l R'.
Proof using .
  destruct 1; intros HR'.
  - eapply MRctyp; eauto using releq_trans, releq_sym.
  - eapply MRctrm; eauto using releq_trans, releq_sym.
Qed.

Lemma ModRel_lconv G Γ T T' l l' R :
  ModRel G Γ T T' l R -> lequiv (gL G) l' l -> ModRel G Γ T T' l' R.
Proof using .
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR]; intros Hl'.
  - exact (MRctyp _ _ _ _ _ _ _ _ _ _ (lequiv_trans _ _ _ _ Hl' Hl) Hk
             (tyred_lconv _ _ _ _ HT Hl') (tyred_lconv _ _ _ _ HT' Hl') HΔ Hgeq HR).
  - exact (MRctrm _ _ _ _ _ _ _ _ _ _ _ _ (lequiv_trans _ _ _ _ Hl' Hl) Hk
             (tyred_lconv _ _ _ _ HT Hl') (tyred_lconv _ _ _ _ HT' Hl') HΔ HA HA' Hgeq HR).
Qed.

Lemma LR_releq n rec G Γ T T' l R R' :
  LR n rec G Γ T T' l R -> releq R R' -> LR n rec G Γ T T' l R'.
Proof using .
  destruct 1; intros HR'.
  - eapply LRnat; eauto using releq_trans, releq_sym.
  - eapply LRU; eauto using releq_trans, releq_sym.
  - eapply LRne; eauto using releq_trans, releq_sym.
  - eapply LRpi; eauto using releq_trans, releq_sym.
  - eapply LRmod; eauto using ModRel_releq.
  - eapply LRcpi with (l1 := l1) (l2 := l2) (T1 := T1) (T1' := T1') (instR := instR);
      eauto using releq_trans, releq_sym.
  - eapply LRtpi with (Δ1 := Δ1) (Δ1' := Δ1') (l1 := l1) (l2 := l2) (l3 := l3) (l4 := l4)
      (T1 := T1) (T1' := T1') (instR := instR); eauto using releq_trans, releq_sym.
  - eapply LRsig; eauto using releq_trans, releq_sym.
  - eapply LRunit; eauto using releq_trans, releq_sym.
  - eapply LRseq; eauto using releq_trans, releq_sym.
  - eapply LRsempty; eauto using releq_trans, releq_sym.
  - eapply LRid; eauto using releq_trans, releq_sym.
  - eapply LRempty; eauto using releq_trans, releq_sym.
  - eapply (LRsum _ _ _ _ _ _ _ l1 l2 l3 l4 A A' B B' RA RB); eauto using releq_trans, releq_sym.
  - eapply LRw; eauto using releq_trans, releq_sym.
  - eapply LRwf; eauto using releq_trans, releq_sym.
  - eapply LRsq; eauto using releq_trans, releq_sym.
  - eapply LRiwf; eauto using releq_trans, releq_sym.
  - eapply LRm; eauto using releq_trans, releq_sym.
Qed.

Theorem LR_lconv n rec G Γ T T' l l' R :
  LR n rec G Γ T T' l R -> lequiv (gL G) l' l -> LR n rec G Γ T T' l' R.
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
                | G Γ T T' l l1 l2 A A' a a' b b' R Hl Hl2 Hw HT HT' HA HAA Haa Hbb HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l l1 l2 A A' a a' b b' RA R Hl Hl2 Hw HT HT' HA HAA Haa Hbb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l l1 l2 A A' RA R Hl Hl2 Hw HT HT' HA HAA HRA Hps Hpt HR
                | G Γ T T' l l1 li1 l2 li2 X X' A A' N N' Ot Ot' C C' m m' idxR domR R Hl Hl2 Hli2 Hw Hwi
                    HT HT' HX HX' HA HA' HN HN' HO HO' HC HC' Hmt Hmt' HXX HAA HNN HOO HCC Hmm
                    idxAd Hisym Histr domAd arAd otAd chAd ixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros Hl'.
  - eapply LRnat; eauto using lequiv_trans, tyred_lconv.
  - eapply (LRU n rec G Γ T T' l' l1 l2); eauto using lequiv_trans, tyred_lconv.
  - eapply LRne; eauto using tyred_lconv, gne_ty_lconv.
    eapply releq_trans; [exact HR | now apply NeRel_lconv].
  - eapply (LRpi n rec G Γ T T' l' l1 l2 l3 l4 A B A' B' domR codR); [split|..];
      eauto using lequiv_trans, tyred_lconv.
  - apply LRmod; [exact Hj | exact (ModRel_lconv _ _ _ _ _ _ _ HM Hl')].
  - eapply (LRcpi n rec G Γ T T' l' l1 l2 T1 T1' instR); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRtpi n rec G Γ T T' l' Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRsig n rec G Γ T T' l' l1 l2 l3 l4 A B A' B' domR codR); [split|..];
      eauto using lequiv_trans, tyred_lconv.
  - eapply (LRunit n rec G Γ T T' l' l1 l2); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRseq n rec G Γ T T' l' l1 l2); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRsempty n rec G Γ T T' l' l1 l2); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRid n rec G Γ T T' l' l1 l2); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRempty n rec G Γ T T' l' l1 l2); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRsum n rec G Γ T T' l' u1 u2 u3 u4); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRw n rec G Γ T T' l' l1 l2 l3 l4 A B A' B' domR codR); [split|..];
      eauto using lequiv_trans, tyred_lconv.
  - eapply (LRwf n rec G Γ T T' l' l1 l2 A A' N N' domR); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRsq n rec G Γ T T' l' l1 l2 A A' RA); eauto using lequiv_trans, tyred_lconv.
  - eapply (LRiwf n rec G Γ T T' l' l1 li1 l2 li2 X X' A A' N N' Ot Ot' C C' m m' idxR domR);
      eauto using lequiv_trans, tyred_lconv.
  - eapply (LRm n rec G Γ T T' l' ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR);
      eauto using lequiv_trans, tyred_lconv.
Qed.

End Basics.
