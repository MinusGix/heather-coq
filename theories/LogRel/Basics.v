(** * Structural lemmas: stages and level conversion *)
From DeLaM.LogRel Require Export Escape.

Section Basics.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Measures of levels *)

Lemma lequiv_measure_eq L l l' : lequiv L l l' -> lmeasure l = lmeasure l'.
Proof. apply lequiv_measure. Qed.

Lemma lmeasure_max l1 l2 : lmeasure (lmax l1 l2) = Nat.max (lmeasure l1) (lmeasure l2).
Proof. reflexivity. Qed.
Lemma lmeasure_suc l : lmeasure (lsuc l) = S (lmeasure l).
Proof. reflexivity. Qed.

(** ** The universe relation only depends on [rec] at its level *)

Lemma URel_ext rec rec' G Γ l0 : rec l0 = rec' l0 -> URel rec G Γ l0 = URel rec' G Γ l0.
Proof. intros Hr. unfold URel. now rewrite Hr. Qed.

Lemma URel_below n m G Γ l0 : lmeasure l0 < n -> lmeasure l0 < m ->
  URel (LRbelow n) G Γ l0 = URel (LRbelow m) G Γ l0.
Proof. intros Hn Hm. apply URel_ext. now rewrite !LRbelow_spec. Qed.

(** ** Cumulativity of stages *)

Theorem cumul_up n m G Γ T T' l R :
  n <= m -> LR n (LRbelow n) G Γ T T' l R -> LR m (LRbelow m) G Γ T T' l R.
Proof.
  intros Hnm H; induction H.
  - eapply LRnat; eauto.
  - match goal with HR : releq _ (URel _ _ _ _) |- _ => rewrite (URel_below n m) in HR by lia end.
    eapply LRU with (l1 := l1) (l2 := l2); eauto; lia.
  - eapply LRne; eauto.
  - eapply LRpi; eauto.
Qed.

Theorem cumul_down n m G Γ T T' l R :
  lmeasure l <= n -> LR m (LRbelow m) G Γ T T' l R -> LR n (LRbelow n) G Γ T T' l R.
Proof.
  intros Hl H; revert Hl; induction H; intros Hle.
  - eapply LRnat; eauto.
  - assert (lmeasure l1 < n).
    { match goal with Hs : lequiv _ l (lsuc l1) |- _ =>
        rewrite (lequiv_measure_eq _ _ _ Hs), lmeasure_suc in Hle end. lia. }
    match goal with HR : releq _ (URel _ _ _ _) |- _ => rewrite (URel_below m n) in HR by lia end.
    eapply LRU with (l1 := l1) (l2 := l2); eauto.
  - eapply LRne; eauto.
  - match goal with Hs : lequiv _ l (lmax l1 l2) |- _ =>
      rewrite (lequiv_measure_eq _ _ _ Hs), lmeasure_max in Hle end.
    eapply LRpi; eauto.
    all: intros; match goal with IH : _ |- LR _ _ _ _ _ _ _ _ => eapply IH; lia end.
Qed.

(** A type at level [l] is related identically at every stage above
    [lmeasure l]. *)
Corollary LogRel_stage n G Γ T T' l R :
  lmeasure l <= n -> LogRel l G Γ T T' l R <-> LR n (LRbelow n) G Γ T T' l R.
Proof.
  intros Hn; split; intros H.
  - eapply cumul_up; [exact Hn | exact H].
  - eapply cumul_down; [lia | exact H].
Qed.

(** ** Level conversion *)


Lemma NeRel_lconv G Γ V V' l l' :
  lequiv (gL G) l' l -> releq (NeRel G Γ V V' l) (NeRel G Γ V V' l').
Proof.
  intros Hl t t'; unfold NeRel; split; intros (ν & ν' & H1 & H2 & H3 & H4);
    exists ν, ν'; refine (conj _ (conj _ (conj _ _)));
    eauto using tmred_lconv, gne_tm_lconv, lequiv_sym.
Qed.

(** ** Saturation: the term relation matters only up to [releq] *)

Lemma releq_refl R : releq R R.
Proof. intros ??; reflexivity. Qed.
Lemma releq_sym R R' : releq R R' -> releq R' R.
Proof. intros H ??; symmetry; apply H. Qed.
Lemma releq_trans R R' R'' : releq R R' -> releq R' R'' -> releq R R''.
Proof. intros H H' ??; etransitivity; [apply H | apply H']. Qed.

Lemma LR_releq n rec G Γ T T' l R R' :
  LR n rec G Γ T T' l R -> releq R R' -> LR n rec G Γ T T' l R'.
Proof.
  destruct 1; intros HR'.
  - eapply LRnat; eauto using releq_trans, releq_sym.
  - eapply LRU; eauto using releq_trans, releq_sym.
  - eapply LRne; eauto using releq_trans, releq_sym.
  - eapply LRpi; eauto using releq_trans, releq_sym.
Qed.

Theorem LR_lconv n rec G Γ T T' l l' R :
  LR n rec G Γ T T' l R -> lequiv (gL G) l' l -> LR n rec G Γ T T' l' R.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HAA HBB domAd codAd HR];
    intros Hl'.
  - eapply LRnat; eauto using lequiv_trans, tyred_lconv.
  - eapply (LRU n rec G Γ T T' l' l1 l2); eauto using lequiv_trans, tyred_lconv.
  - eapply LRne; eauto using tyred_lconv, gne_ty_lconv.
    eapply releq_trans; [exact HR | now apply NeRel_lconv].
  - eapply (LRpi n rec G Γ T T' l' l1 l2 l3 l4 A B A' B' domR codR);
      eauto using lequiv_trans, tyred_lconv.
Qed.

End Basics.
