(** * Presupposition of the equations at V and C (M7_DESIGN.md C3 K4)

    [Presupposition] covers the layers with [typeof i = i] (D, M). Below,
    a judgment lifts to D, which gives its presuppositions there (InvAny),
    but not at its own layer. Here: at [i ≤ C], both sides of an equation
    are typed at [i]. The paper's [box] congruences take only the code's
    equation at C (04:1383); O's take both sides typed at C.

    The proof is O's presupposition argument at a layer whose contexts
    live at D: a congruence's right-hand side moves to the right-hand
    context by context conversion along an equivalence at D (CtxConv), and
    its type back by an equation at D. No β rule applies at [i ≤ C]. *)
From DeLaM.Typing Require Export InvAny.
From DeLaM.Typing Require Import StaticCodeEq.

Section Cases.
Context {G : gctx} {i : layer} (Hle : lle i lC).

Let Hd : typeof i = lD := lle_D_typeof i (lle_C_D Hle).
Let HiD : lle i lD := lle_C_D Hle.

Lemma ctxD_of_ty {Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ lD ] ].
Proof. intros H; rewrite <- Hd; exact (ctx_of_ty_any H). Qed.
Lemma ctxD_of_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] ].
Proof. intros H; rewrite <- Hd; exact (ctx_of_tm_any H). Qed.
Lemma tyD_of_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] T @ l ].
Proof. intros H; rewrite <- Hd; exact (wf_tm_ty_any H). Qed.

(** The extended contexts of a congruence are equivalent at D. *)
Lemma extc {Γ A A' l l'} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> lequiv (gL G) l l' ->
  [ G ⊢[ lD ] Γ ,, A @ l ≅ Γ ,, A' @ l' ].
Proof.
  intros HA HAA Hl. apply eqc_ext; [apply eqc_refl, (ctxD_of_ty HA) | exact (lift_ty HA HiD)
                                   | exact (lift_eqty HAA HiD) | exact Hl].
Qed.

Lemma conv_at {Γ t T T' l} : [ G ; Γ ⊢[ i ] t : T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] t : T @ l ].
Proof. intros; eapply wf_conv; [eassumption | now rewrite Hd]. Qed.

Lemma convU_at {Γ t l l'} : [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] t : tyU l' @ lsuc l' ].
Proof.
  intros Ht Hl. eapply wf_lconv; [|apply lequiv_suc, lequiv_sym, Hl].
  apply (conv_at Ht). eapply eqty_lconv; [|apply lequiv_suc, Hl].
  apply eqty_U; [discriminate | exact (ctxD_of_tm Ht) | now apply lequiv_sym].
Qed.

Lemma pc_pi {Γ l1 l2 l3 l4 A A' B B'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyPi l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢[ i ] tyPi l3 l4 A' B' @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HB HB'. split; [apply wft_pi; eauto using lequiv_wf_l|].
  eapply wft_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply wft_pi; eauto using lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | now apply lequiv_sym].
  - eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | now apply lequiv_sym].
Qed.

Lemma pc_El {Γ l l' t t'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] t' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] tyEl l t @ l ] /\ [ G ; Γ ⊢[ i ] tyEl l' t' @ l ].
Proof.
  intros Hv Hl Ht Ht'. split; [apply wft_El; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|exact Hl]. apply wft_El; eauto using lequiv_wf_r. exact (convU_at Ht' Hl).
Qed.

Lemma pc_U {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tyU l' @ lsuc l ].
Proof.
  intros Hv HΓ Hl. split; [apply wft_U; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|apply lequiv_suc, Hl]. apply wft_U; eauto using lequiv_wf_r.
Qed.

Lemma pc_codeU {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmU l : tyU (lsuc l) @ lsuc (lsuc l) ] /\
  [ G ; Γ ⊢[ i ] tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ].
Proof.
  intros Hv HΓ Hl. split; [apply wf_code_U; eauto using lequiv_wf_l|].
  apply (convU_at (l := lsuc l')); [apply wf_code_U; eauto using lequiv_wf_r|].
  apply lequiv_suc, lequiv_sym, Hl.
Qed.

Lemma pc_codepi {Γ l1 l2 l3 l4 s s' t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmPi l1 l2 s t : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmPi l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof.
  intros Hv H13 H24 Hs Hss Hs' Ht Ht'. split; [apply wf_code_pi; eauto using lequiv_wf_l|].
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; eauto using lequiv_wf_l).
  assert (HEE : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; auto).
  apply (convU_at (l := lmax l3 l4)); [|apply lequiv_sym, lequiv_max; assumption].
  apply wf_code_pi; eauto using lequiv_wf_r.
  - exact (convU_at Hs' H13).
  - exact (convU_at (ctxconv_tm (extc HEl HEE H13) Hd Ht') H24).
Qed.

Lemma pc_natrec {Γ l l' M M' s s' z z' t t'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] -> [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M ≅ M' @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' @ l ] ->
  [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] -> [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] t' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] natrec l M s z t : M[lsingle t] @ l ] /\
  [ G ; Γ ⊢[ i ] natrec l' M' s' z' t' : M[lsingle t] @ l ].
Proof.
  intros Hv Hl HM HMM HM' Hs Hs' Hz Hz' Htt Ht Ht'.
  split; [apply wf_natrec; eauto using lequiv_wf_l|].
  pose proof (lift_eqty HMM HiD) as HMMd. pose proof (lift_ty HM HiD) as HMd.
  pose proof (lift_tm Ht HiD) as Htd. pose proof (lift_tm Ht' HiD) as Htd'.
  pose proof (ctxD_of_tm Ht) as HΓ.
  assert (Hzd : [ G ; Γ ⊢[ lD ] zero : tyNat @ lzero ]) by (apply wf_zero; [discriminate | exact HΓ]).
  pose proof (ctxconv_tm (extc HM HMM Hl) Hd Hz') as Hz1.
  pose proof (ctxD_of_tm Hz1) as HΓM.
  eapply wf_lconv with (l' := l'); [|exact Hl].
  eapply conv_at.
  - apply wf_natrec; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HM' | now apply lequiv_sym].
    + eapply wf_lconv; [|apply lequiv_sym, Hl]. apply (conv_at Hs').
      apply eqty_sym. exact (eqty_single (i := lD) eq_refl HMMd Hzd).
    + eapply wf_lconv; [|apply lequiv_sym, Hl]. apply (conv_at Hz1).
      apply eqty_sym. eapply (eqty_subst (i := lD) eq_refl HMMd).
      exact (lsub_wf_lsucc (i := lD) eq_refl ltac:(discriminate) HΓM).
  - eapply eqty_lconv; [|apply lequiv_sym, Hl].
    eapply eqty_trans.
    + apply (wf_ty_func (i := lD) eq_refl HMd (d' := lsingle t')).
      exact (lsub_eq_single (i := lD) eq_refl Htd Htd' (lift_eqtm Htt HiD)).
    + exact (eqty_single (i := lD) eq_refl HMMd Htd').
Qed.

Lemma pc_lam {Γ l1 l2 l3 l4 A A' B t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] t : B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] t' : B @ l2 ] ->
  [ G ; Γ ⊢[ i ] lam l1 l2 A t : tyPi l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] lam l3 l4 A' t' : tyPi l1 l2 A B @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' Ht Ht'. split; [apply wf_lam; eauto using lequiv_wf_l|].
  eapply wf_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply (conv_at (T' := tyPi l3 l4 A' B)).
  - apply wf_lam; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | now apply lequiv_sym].
    + eapply wf_lconv; [exact (ctxconv_tm (extc HA HAA H13) Hd Ht') | now apply lequiv_sym].
  - eapply eqty_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
    apply eqty_pi; [discriminate | assumption | assumption | exact (lift_ty HA HiD)
                   | exact (lift_eqty HAA HiD) |].
    apply eqty_refl. exact (tyD_of_tm Ht).
Qed.

Lemma pc_app {Γ l1 l2 l3 l4 A A' B B' t t' s s'} : i <> lV ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] t : tyPi l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] t' : tyPi l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] s ≅ s' : A @ l1 ] -> [ G ; Γ ⊢[ i ] s : A @ l1 ] -> [ G ; Γ ⊢[ i ] s' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] app t l1 l2 A B s : B[lsingle s] @ l2 ] /\
  [ G ; Γ ⊢[ i ] app t' l3 l4 A' B' s' : B[lsingle s] @ l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HBB HB HB' Ht Ht' Hss Hs Hs'.
  split; [apply wf_app; eauto using lequiv_wf_l|].
  pose proof (lift_eqty HAA HiD) as HAAd. pose proof (lift_eqty HBB HiD) as HBBd.
  pose proof (lift_tm Hs HiD) as Hsd. pose proof (lift_tm Hs' HiD) as Hsd'.
  assert (HPi : [ G ; Γ ⊢[ lD ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ])
    by (apply eqty_pi; [discriminate | assumption | assumption | exact (lift_ty HA HiD) | exact HAAd | exact HBBd]).
  eapply wf_lconv with (l' := l4); [|exact H24].
  apply (conv_at (T' := B'[lsingle s'])).
  - apply wf_app; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | now apply lequiv_sym].
    + eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | now apply lequiv_sym].
    + eapply wf_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
      apply (conv_at Ht'). now apply eqty_sym.
    + eapply wf_lconv with (l' := l1); [|now apply lequiv_sym].
      apply (conv_at Hs'). now apply eqty_sym.
  - eapply eqty_lconv; [|apply lequiv_sym, H24].
    eapply eqty_trans.
    + apply (wf_ty_func (i := lD) eq_refl (lift_ty HB HiD) (d' := lsingle s')).
      exact (lsub_eq_single (i := lD) eq_refl Hsd Hsd' (lift_eqtm Hss HiD)).
    + exact (eqty_single (i := lD) eq_refl HBBd Hsd').
Qed.

(** Dependent pairs and the unit type, code since M8d. *)
Lemma pc_sig {Γ l1 l2 l3 l4 A A' B B'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tySig l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢[ i ] tySig l3 l4 A' B' @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HB HB'. split; [apply wft_sig; eauto using lequiv_wf_l|].
  eapply wft_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply wft_sig; eauto using lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | now apply lequiv_sym].
  - eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | now apply lequiv_sym].
Qed.

Lemma pc_codesig {Γ l1 l2 l3 l4 s s' t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSig l1 l2 s t : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmSig l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof.
  intros Hv H13 H24 Hs Hss Hs' Ht Ht'. split; [apply wf_code_sig; eauto using lequiv_wf_l|].
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; eauto using lequiv_wf_l).
  assert (HEE : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; auto).
  apply (convU_at (l := lmax l3 l4)); [|apply lequiv_sym, lequiv_max; assumption].
  apply wf_code_sig; eauto using lequiv_wf_r.
  - exact (convU_at Hs' H13).
  - exact (convU_at (ctxconv_tm (extc HEl HEE H13) Hd Ht') H24).
Qed.

(** The Σ types of a congruence, related at D. *)
Lemma sig_eqD {Γ l1 l2 l3 l4 A A' B B'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ lD ] tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ lmax l1 l2 ].
Proof.
  intros H13 H24 HA HAA HBB.
  apply eqty_sig; [discriminate | assumption | assumption | exact (lift_ty HA HiD)
                  | exact (lift_eqty HAA HiD) | exact (lift_eqty HBB HiD)].
Qed.

Lemma pc_pair {Γ l1 l2 l3 l4 A A' B B' a a' b b'} : i <> lV ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] b : B[lsingle a] @ l2 ] -> [ G ; Γ ⊢[ i ] b' : B[lsingle a] @ l2 ] ->
  [ G ; Γ ⊢[ i ] tmPair l1 l2 A B a b : tySig l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmPair l3 l4 A' B' a' b' : tySig l1 l2 A B @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HBB HB HB' Haa Ha Ha' Hb Hb'.
  split; [apply wf_pair; eauto using lequiv_wf_l|].
  pose proof (lift_eqty HBB HiD) as HBBd.
  pose proof (lift_tm Ha HiD) as Had. pose proof (lift_tm Ha' HiD) as Had'.
  eapply wf_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply (conv_at (T' := tySig l3 l4 A' B')).
  - apply wf_pair; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | now apply lequiv_sym].
    + eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | now apply lequiv_sym].
    + eapply wf_lconv with (l' := l1); [|now apply lequiv_sym].
      apply (conv_at Ha'). apply eqty_sym, (lift_eqty HAA HiD).
    + eapply wf_lconv with (l' := l2); [|now apply lequiv_sym].
      apply (conv_at Hb'). apply eqty_sym. eapply eqty_trans.
      * apply (wf_ty_func (i := lD) eq_refl (lift_ty HB HiD) (d' := lsingle a')).
        exact (lsub_eq_single (i := lD) eq_refl Had Had' (lift_eqtm Haa HiD)).
      * exact (eqty_single (i := lD) eq_refl HBBd Had').
  - eapply eqty_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
    exact (sig_eqD H13 H24 HA HAA HBB).
Qed.

Lemma pc_fst {Γ l1 l2 l3 l4 A A' B B' p p'} : i <> lV ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] p : tySig l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmFst l1 l2 A B p : A @ l1 ] /\ [ G ; Γ ⊢[ i ] tmFst l3 l4 A' B' p' : A @ l1 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HBB HB HB' Hp Hp'.
  split; [apply wf_fst; eauto using lequiv_wf_l|].
  eapply wf_lconv with (l' := l3); [|exact H13].
  apply (conv_at (T' := A')).
  - apply wf_fst; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | now apply lequiv_sym].
    + eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | now apply lequiv_sym].
    + eapply wf_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
      apply (conv_at Hp'). exact (eqty_sym _ _ _ _ _ _ (sig_eqD H13 H24 HA HAA HBB)).
  - eapply eqty_lconv; [exact (lift_eqty HAA HiD) | now apply lequiv_sym].
Qed.

Lemma pc_snd {Γ l1 l2 l3 l4 A A' B B' p p'} : i <> lV ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] p ≅ p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] p : tySig l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmSnd l1 l2 A B p : B[lsingle (tmFst l1 l2 A B p)] @ l2 ] /\
  [ G ; Γ ⊢[ i ] tmSnd l3 l4 A' B' p' : B[lsingle (tmFst l1 l2 A B p)] @ l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HBB HB HB' Hpp Hp Hp'.
  split; [apply wf_snd; eauto using lequiv_wf_l|].
  pose proof (lift_eqty HBB HiD) as HBBd.
  destruct (pc_fst Hv H13 H24 HA HAA HA' HBB HB HB' Hp Hp') as [Hf Hf'].
  pose proof (lift_tm Hf HiD) as Hfd. pose proof (lift_tm Hf' HiD) as Hfd'.
  assert (Eff : [ G ; Γ ⊢[ lD ] tmFst l1 l2 A B p ≅ tmFst l3 l4 A' B' p' : A @ l1 ]).
  { apply eqtm_fst; [discriminate | assumption | assumption | exact (lift_ty HA HiD)
                    | exact (lift_eqty HAA HiD) | exact HBBd | exact (lift_eqtm Hpp HiD)]. }
  eapply wf_lconv with (l' := l4); [|exact H24].
  apply (conv_at (T' := B'[lsingle (tmFst l3 l4 A' B' p')])).
  - apply wf_snd; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | now apply lequiv_sym].
    + eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | now apply lequiv_sym].
    + eapply wf_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
      apply (conv_at Hp'). exact (eqty_sym _ _ _ _ _ _ (sig_eqD H13 H24 HA HAA HBB)).
  - eapply eqty_lconv; [|apply lequiv_sym, H24].
    eapply eqty_trans.
    + apply (wf_ty_func (i := lD) eq_refl (lift_ty HB HiD) (d' := lsingle (tmFst l3 l4 A' B' p'))).
      exact (lsub_eq_single (i := lD) eq_refl Hfd Hfd' Eff).
    + exact (eqty_single (i := lD) eq_refl HBBd Hfd').
Qed.

Lemma pc_unit {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tyUnit l @ l ] /\ [ G ; Γ ⊢[ i ] tyUnit l' @ l ].
Proof.
  intros Hv HΓ Hl. split; [apply wft_unit; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|exact Hl]. apply wft_unit; eauto using lequiv_wf_r.
Qed.

Lemma pc_codeunit {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmUnit l : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmUnit l' : tyU l @ lsuc l ].
Proof.
  intros Hv HΓ Hl. split; [apply wf_code_unit; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [apply wf_code_unit; eauto using lequiv_wf_r | now apply lequiv_sym].
Qed.

Lemma pc_triv {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmTriv l : tyUnit l @ l ] /\ [ G ; Γ ⊢[ i ] tmTriv l' : tyUnit l @ l ].
Proof.
  intros Hv HΓ Hl. split; [apply wf_triv; eauto using lequiv_wf_l|].
  eapply wf_lconv with (l' := l'); [|exact Hl].
  apply (conv_at (T' := tyUnit l')); [apply wf_triv; eauto using lequiv_wf_r|].
  rewrite Hd in HΓ. eapply eqty_lconv; [apply eqty_unit; [discriminate | exact HΓ | exact Hl] | now apply lequiv_sym].
Qed.

Lemma pc_gvar {Γ u Δ i' T l d d'} : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] gvar u d : T[d] @ l ] /\ [ G ; Γ ⊢[ i ] gvar u d' : T[d] @ l ].
Proof.
  intros HΓ Hin Hi' Ht Hn Ht' Hn' He He' Hee. split; [eapply wf_gvar; eassumption|].
  pose proof HΓ as HΓD; rewrite Hd in HΓD.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓD) Hin) as (_ & HT & _).
  assert (Hdd : [ G ; Γ ⊢[ lD ] d : Δ ]).
  { apply (lsub_wf_prem (i := lD) eq_refl); auto.
    intros n A k H; exact (lift_tm (He _ _ _ H) HiD). }
  assert (Hdd' : [ G ; Γ ⊢[ lD ] d' : Δ ]).
  { apply (lsub_wf_prem (i := lD) eq_refl); auto.
    intros n A k H; exact (lift_tm (He' _ _ _ H) HiD). }
  apply (conv_at (T' := T[d'])); [eapply wf_gvar; eassumption|].
  exact (proj1 (proj2 (proj2 functionality_all)) _ _ _ _ _ HT _ _ _
           (conj Hdd (conj Hdd' (fun n A k H => lift_eqtm (Hee _ _ _ H) HiD)))).
Qed.

(** Defined globals (M9): as [gvar], with the two carried bodies. *)
Lemma pc_gdef {Γ u Δ T l t0 t t' d d'} : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t -> tm_leq t0 t' -> lle lC i ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Δ ⊢[ i ] t : T @ l ] -> [ G ; Δ ⊢[ i ] t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] gdef u t d : T[d] @ l ] /\ [ G ; Γ ⊢[ i ] gdef u t' d' : T[d] @ l ].
Proof.
  intros HΓ Hin Hl Hl' Hi' Ht Hn Ht' Hn' He He' Hee Hb Hb'. split; [eapply wf_gdef; eassumption|].
  pose proof HΓ as HΓD; rewrite Hd in HΓD.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓD) Hin) as (_ & HT & _).
  assert (Hdd : [ G ; Γ ⊢[ lD ] d : Δ ]).
  { apply (lsub_wf_prem (i := lD) eq_refl); auto.
    intros n A k H; exact (lift_tm (He _ _ _ H) HiD). }
  assert (Hdd' : [ G ; Γ ⊢[ lD ] d' : Δ ]).
  { apply (lsub_wf_prem (i := lD) eq_refl); auto.
    intros n A k H; exact (lift_tm (He' _ _ _ H) HiD). }
  apply (conv_at (T' := T[d'])); [eapply wf_gdef; eassumption|].
  exact (proj1 (proj2 (proj2 functionality_all)) _ _ _ _ _ HT _ _ _
           (conj Hdd (conj Hdd' (fun n A k H => lift_eqtm (Hee _ _ _ H) HiD)))).
Qed.


(** The identity type (every layer but V since M11b): the right-hand
    sides by Static Code's constructions, at level-equivalent annotations. *)
Lemma pc_id {Γ l l' A A' a a' b b'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] b : A @ l ] -> [ G ; Γ ⊢[ i ] b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyId l A a b @ l ] /\ [ G ; Γ ⊢[ i ] tyId l' A' a' b' @ l ].
Proof.
  intros Hv Hl HA HAA HA' Ha Ha' Hb Hb'.
  split; [apply wft_id; eauto using lequiv_wf_l | exact (sc_id_q HiD Hv Hl HA' HAA Ha' Hb')].
Qed.

Lemma pc_idrefl {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmRefl l A a : tyId l A a a @ l ] /\ [ G ; Γ ⊢[ i ] tmRefl l' A' a' : tyId l A a a @ l ].
Proof.
  intros Hv Hl HA HAA HA' Haa Ha Ha'.
  split; [apply wf_idrefl; eauto using lequiv_wf_l | exact (sc_idrefl_q HiD Hv Hl HA HA' HAA Ha' Haa)].
Qed.

Lemma pc_code_id {Γ l l' s s' t t' u u'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] u : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmId l s t u : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmId l' s' t' u' : tyU l @ lsuc l ].
Proof.
  intros Hv Hl Hs Hss Hs' Ht Ht' Hu Hu'.
  split; [apply wf_code_id; eauto using lequiv_wf_l | exact (sc_code_id_q HiD Hv Hl Hs' Hss Ht' Hu')].
Qed.

Lemma pc_J {Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' e e'} : i <> lV ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ] ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ⊢[ i ] c : M[lsingle2 a (tmRefl l1 A a)] @ l2 ] ->
  [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ] ->
  [ G ; Γ ⊢[ i ] u ≅ u' : A @ l1 ] -> [ G ; Γ ⊢[ i ] u : A @ l1 ] -> [ G ; Γ ⊢[ i ] u' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] e ≅ e' : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ i ] e : tyId l1 A a u @ l1 ] -> [ G ; Γ ⊢[ i ] e' : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmJ l1 l2 A a M c u e : M[lsingle2 u e] @ l2 ] /\
  [ G ; Γ ⊢[ i ] tmJ l3 l4 A' a' M' c' u' e' : M[lsingle2 u e] @ l2 ].
Proof.
  intros Hv H13 H24 HId HA HAA HA' Haa Ha Ha' HMM HM HM' Hc Hc' Huu Hu Hu' Hee He He'.
  split; [apply wf_J; eauto using lequiv_wf_l |].
  exact (sc_J_q HiD Hv H13 H24 HA HA' HAA Ha Ha' Haa HM' HMM Hc' Hu Hu' Huu He He' Hee).
Qed.

(** Strict equality (every layer but V since M10c), as the identity type. *)
Lemma pc_seq {Γ l l' A A' a a' b b'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] b : A @ l ] -> [ G ; Γ ⊢[ i ] b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tySEq l A a b @ l ] /\ [ G ; Γ ⊢[ i ] tySEq l' A' a' b' @ l ].
Proof.
  intros Hv Hl HA HAA HA' Ha Ha' Hb Hb'.
  split; [apply wft_seq; eauto using lequiv_wf_l | exact (sc_seq_q HiD Hv Hl HA' HAA Ha' Hb')].
Qed.

Lemma pc_sempty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tySEmpty l @ l ] /\ [ G ; Γ ⊢[ i ] tySEmpty l' @ l ].
Proof.
  intros Hv HΓ Hl. split; [apply wft_sempty; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|exact Hl]. apply wft_sempty; eauto using lequiv_wf_r.
Qed.

Lemma pc_srefl {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] srefl l A a : tySEq l A a a @ l ] /\ [ G ; Γ ⊢[ i ] srefl l' A' a' : tySEq l A a a @ l ].
Proof.
  intros Hv Hl HA HAA HA' Haa Ha Ha'.
  split; [apply wf_srefl; eauto using lequiv_wf_l | exact (sc_srefl_q HiD Hv Hl HA HA' HAA Ha' Haa)].
Qed.

Lemma pc_elimSEmpty {Γ l1 l2 l3 l4 M M' e e'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] M @ l2 ] -> [ G ; Γ ⊢[ i ] M ≅ M' @ l2 ] -> [ G ; Γ ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ⊢[ i ] e : tySEmpty l1 @ l1 ] -> [ G ; Γ ⊢[ i ] e' : tySEmpty l1 @ l1 ] ->
  [ G ; Γ ⊢[ i ] elimSEmpty l1 l2 M e : M @ l2 ] /\ [ G ; Γ ⊢[ i ] elimSEmpty l3 l4 M' e' : M @ l2 ].
Proof.
  intros Hv H13 H24 HM HMM HM' He He'.
  split; [apply wf_elimSEmpty; eauto using lequiv_wf_l | exact (sc_elimSEmpty_q HiD Hv H13 H24 HM' HMM He')].
Qed.

Lemma pc_code_seq {Γ l l' s s' t t' u u'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] u : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmSEq l s t u : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmSEq l' s' t' u' : tyU l @ lsuc l ].
Proof.
  intros Hv Hl Hs Hss Hs' Ht Ht' Hu Hu'.
  split; [apply wf_code_seq; eauto using lequiv_wf_l | exact (sc_code_seq_q HiD Hv Hl Hs' Hss Ht' Hu')].
Qed.

Lemma pc_code_sempty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmSEmpty l : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmSEmpty l' : tyU l @ lsuc l ].
Proof.
  intros Hv HΓ Hl. split; [apply wf_code_sempty; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [apply wf_code_sempty; eauto using lequiv_wf_r | now apply lequiv_sym].
Qed.


(** The empty type and binary sums (every layer but V since M12c). *)
Lemma pc_empty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tyEmpty l @ l ] /\ [ G ; Γ ⊢[ i ] tyEmpty l' @ l ].
Proof.
  intros Hv HΓ Hl. split; [apply wft_empty; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|exact Hl]. apply wft_empty; eauto using lequiv_wf_r.
Qed.

Lemma pc_elimEmpty {Γ l1 l2 l3 l4 M M' t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M @ l1 ] -> [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M ≅ M' @ l1 ] ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M' @ l1 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ i ] t : tyEmpty l2 @ l2 ] -> [ G ; Γ ⊢[ i ] t' : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ i ] elimEmpty l1 l2 M t : M[lsingle t] @ l1 ] /\
  [ G ; Γ ⊢[ i ] elimEmpty l3 l4 M' t' : M[lsingle t] @ l1 ].
Proof.
  intros Hv H13 H24 HM HMM HM' Htt Ht Ht'.
  split; [apply wf_elimEmpty; eauto using lequiv_wf_l | exact (sc_elimEmpty_q HiD Hv H13 H24 HM' HMM Ht Ht' Htt)].
Qed.

Lemma pc_sum {Γ l1 l2 l3 l4 A A' B B'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tySum l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢[ i ] tySum l3 l4 A' B' @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HA' HB HB'.
  split; [apply wft_sum; eauto using lequiv_wf_l | exact (sc_sum_q Hv H13 H24 HA' HB')].
Qed.

Lemma pc_inl {Γ l1 l2 l3 l4 A A' B B' a a'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmInl l1 l2 A B a : tySum l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmInl l3 l4 A' B' a' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HB HBB HB' Ha Ha'.
  split; [apply wf_inl; eauto using lequiv_wf_l | exact (sc_inl_q HiD Hv H13 H24 HA' HAA HB' HBB Ha')].
Qed.

Lemma pc_inr {Γ l1 l2 l3 l4 A A' B B' b b'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] b : B @ l2 ] -> [ G ; Γ ⊢[ i ] b' : B @ l2 ] ->
  [ G ; Γ ⊢[ i ] tmInr l1 l2 A B b : tySum l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmInr l3 l4 A' B' b' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HB HBB HB' Hb Hb'.
  split; [apply wf_inr; eauto using lequiv_wf_l | exact (sc_inr_q HiD Hv H13 H24 HA' HAA HB' HBB Hb')].
Qed.

Lemma pc_case {Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' t t'} : i <> lV ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c1 : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] c1' : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ,, B @ l2 ⊢[ i ] c2 : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] -> [ G ; Γ ,, B @ l2 ⊢[ i ] c2' : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t : tySum l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] t' : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmCase l1 l2 l3 A B M c1 c2 t : M[lsingle t] @ l3 ] /\
  [ G ; Γ ⊢[ i ] tmCase l4 l5 l6 A' B' M' c1' c2' t' : M[lsingle t] @ l3 ].
Proof.
  intros Hv H14 H25 H36 HA HAA HA' HB HBB HB' HM HMM HM' Hc1 Hc1' Hc2 Hc2' Htt Ht Ht'.
  split; [apply wf_case; eauto using lequiv_wf_l |].
  exact (sc_case_q HiD Hv H14 H25 H36 HA HA' HAA HB HB' HBB HM HM' HMM Hc1' Hc2' Ht Ht' Htt).
Qed.

Lemma pc_code_empty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmEmpty l : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmEmpty l' : tyU l @ lsuc l ].
Proof.
  intros Hv HΓ Hl. split; [apply wf_code_empty; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [apply wf_code_empty; eauto using lequiv_wf_r | now apply lequiv_sym].
Qed.

Lemma pc_code_sum {Γ l1 l2 l3 l4 s s' t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] t : tyU l2 @ lsuc l2 ] -> [ G ; Γ ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSum l1 l2 s t : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmSum l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof.
  intros Hv H13 H24 Hs Hs' Ht Ht'.
  split; [apply wf_code_sum; eauto using lequiv_wf_l | exact (sc_code_sum_q HiD Hv H13 H24 Hs' Ht')].
Qed.

(** Well-founded trees and their code (every layer but V since M13b). *)
Lemma pc_W {Γ l1 l2 l3 l4 A A' B B'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢[ i ] tyW l3 l4 A' B' @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HB HB'.
  split; [apply wft_W; eauto using lequiv_wf_l | exact (sc_W_q HiD Hv H13 H24 HA HA' HAA HB')].
Qed.

Lemma pc_sup {Γ l1 l2 l3 l4 A A' B B' a a' f f'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] f : tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩ @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ⊢[ i ] f' : tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩ @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ⊢[ i ] tmSup l1 l2 A B a f : tyW l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmSup l3 l4 A' B' a' f' : tyW l1 l2 A B @ lmax l1 l2 ].
Proof.
  intros Hv H13 H24 HA HAA HA' HB HBB HB' Haa Ha Ha' Hf Hf'.
  split; [apply wf_sup; eauto using lequiv_wf_l |].
  exact (sc_sup_q HiD Hv H13 H24 HA HA' HAA HB HB' HBB Ha Ha' Haa Hf').
Qed.

Lemma pc_elimW {Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c c' t t'} : i <> lV ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] wihty l1 l2 l3 A B M @ lmax l2 l3 ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ⊢[ i ] c : wstepty l1 l2 A B M @ l3 ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ⊢[ i ] c' : wstepty l1 l2 A B M @ l3 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t : tyW l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] t' : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmElimW l1 l2 l3 A B M c t : M[lsingle t] @ l3 ] /\
  [ G ; Γ ⊢[ i ] tmElimW l4 l5 l6 A' B' M' c' t' : M[lsingle t] @ l3 ].
Proof.
  intros Hv H14 H25 H36 HA HAA HA' HB HBB HB' HM HMM HM' HF HI Hc Hc' Htt Ht Ht'.
  split; [apply wf_elimW; eauto using lequiv_wf_l |].
  exact (sc_elimW_q HiD Hv H14 H25 H36 HA HA' HAA HB HB' HBB HM HM' HMM HF HI Hc' Ht Ht' Htt).
Qed.

Lemma pc_codeW {Γ l1 l2 l3 l4 s s' t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmW l1 l2 s t : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmW l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof.
  intros Hv H13 H24 Hs Hss Hs' Ht Ht'. split; [apply wf_code_W; eauto using lequiv_wf_l|].
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; eauto using lequiv_wf_l).
  assert (HEE : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; auto).
  apply (convU_at (l := lmax l3 l4)); [|apply lequiv_sym, lequiv_max; assumption].
  apply wf_code_W; eauto using lequiv_wf_r.
  - exact (convU_at Hs' H13).
  - exact (convU_at (ctxconv_tm (extc HEl HEE H13) Hd Ht') H24).
Qed.

(** Length-indexed tuples and finite indices, with their codes (every
    layer but V since M14b). *)
Lemma pc_vec {Γ l l' A A' n n'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyVec l A n @ l ] /\ [ G ; Γ ⊢[ i ] tyVec l' A' n' @ l ].
Proof.
  intros Hv Hl HA HA' Hn Hn'. split; [apply wft_vec; eauto using lequiv_wf_l|].
  eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_vec; eauto using lequiv_wf_r. eapply wft_lconv; [exact HA' | now apply lequiv_sym].
Qed.

Lemma pc_fin {Γ n n'} : i <> lV ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyFin n @ lzero ] /\ [ G ; Γ ⊢[ i ] tyFin n' @ lzero ].
Proof. intros Hv Hn Hn'. split; apply wft_fin; assumption. Qed.

Lemma pc_code_vec {Γ l l' s s' n n'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmVec l s n : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmVec l' s' n' : tyU l @ lsuc l ].
Proof.
  intros Hv Hl Hs Hs' Hn Hn'. split; [apply wf_code_vec; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [|now apply lequiv_sym].
  apply wf_code_vec; eauto using lequiv_wf_r. exact (convU_at Hs' Hl).
Qed.

Lemma pc_code_fin {Γ n n'} : i <> lV ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmFin n : tyU lzero @ lsuc lzero ] /\ [ G ; Γ ⊢[ i ] tmFin n' : tyU lzero @ lsuc lzero ].
Proof. intros Hv Hn Hn'. split; apply wf_code_fin; assumption. Qed.

End Cases.

Theorem presupposition_C :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> True) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> True) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> lle i lC ->
     [ G ; Γ ⊢[ i ] T @ l ] /\ [ G ; Γ ⊢[ i ] T' @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> lle i lC ->
     [ G ; Γ ⊢[ i ] t : T @ l ] /\ [ G ; Γ ⊢[ i ] t' : T @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    (* the computing and M-only rules do not apply below D *)
    try match goal with
        | Hc : compt ?i, Hle : lle ?i lC |- _ => exfalso; exact (lle_C_not_compt Hle Hc)
        | Hle : lle lM lC |- _ => exfalso; exact (lle_C_not_M Hle eq_refl)
        end;
    repeat match goal with IH : lle ?j lC -> _, Hle : lle ?j lC |- _ => specialize (IH Hle) end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try solve [split; auto].
  all: try solve [split; eapply wf_conv; eassumption].
  all: try solve [split; eapply wft_lconv; eassumption].
  all: try solve [split; eapply wf_lconv; eassumption].
  all: try solve [split; apply wf_succ; assumption].
  all: try solve [split; first [eapply wft_gvar | eapply wf_gvar]; eassumption].
  all: first [ solve [eapply pc_pi; eassumption] | solve [eapply pc_El; eassumption]
             | solve [eapply pc_U; eassumption] | solve [eapply pc_codeU; eassumption]
             | solve [eapply pc_codepi; eassumption] | solve [eapply pc_natrec; eassumption]
             | solve [eapply pc_lam; eassumption] | solve [eapply pc_app; eassumption]
             | solve [eapply pc_gvar; eassumption] | solve [eapply pc_gdef; eassumption]
             | solve [eapply pc_sig; eassumption] | solve [eapply pc_codesig; eassumption]
             | solve [eapply pc_pair; eassumption] | solve [eapply pc_fst; eassumption]
             | solve [eapply pc_snd; eassumption] | solve [eapply pc_unit; eassumption]
             | solve [eapply pc_codeunit; eassumption] | solve [eapply pc_triv; eassumption]
             | solve [eapply pc_id; eassumption] | solve [eapply pc_idrefl; eassumption]
             | solve [eapply pc_code_id; eassumption] | solve [eapply pc_J; eassumption]
             | solve [eapply pc_seq; eassumption] | solve [eapply pc_sempty; eassumption]
             | solve [eapply pc_srefl; eassumption] | solve [eapply pc_elimSEmpty; eassumption]
             | solve [eapply pc_code_seq; eassumption] | solve [eapply pc_code_sempty; eassumption]
             (* the empty type and binary sums, with their codes (M12c) *)
             | solve [eapply pc_empty; eassumption] | solve [eapply pc_elimEmpty; eassumption]
             | solve [eapply pc_sum; eassumption] | solve [eapply pc_inl; eassumption]
             | solve [eapply pc_inr; eassumption] | solve [eapply pc_case; eassumption]
             | solve [eapply pc_code_empty; eassumption] | solve [eapply pc_code_sum; eassumption]
             (* well-founded trees and their code (M13b) *)
             | solve [eapply pc_W; eassumption] | solve [eapply pc_sup; eassumption]
             | solve [eapply pc_elimW; eassumption] | solve [eapply pc_codeW; eassumption]
             (* length-indexed tuples and finite indices, with their codes (M14b) *)
             | solve [eapply pc_vec; eassumption] | solve [eapply pc_fin; eassumption]
             | solve [eapply pc_code_vec; eassumption] | solve [eapply pc_code_fin; eassumption] ].
Qed.

Lemma eqty_wf_C {G i Γ T T' l} : lle i lC -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] T @ l ] /\ [ G ; Γ ⊢[ i ] T' @ l ].
Proof. intros Hle H; exact (proj1 (proj2 (proj2 (proj2 (proj2 presupposition_C)))) _ _ _ _ _ _ H Hle). Qed.
Lemma eqtm_wf_C {G i Γ t t' T l} : lle i lC -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] t : T @ l ] /\ [ G ; Γ ⊢[ i ] t' : T @ l ].
Proof.
  intros Hle H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 presupposition_C))))) _ _ _ _ _ _ _ H Hle).
Qed.
