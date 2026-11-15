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
Proof using Hd. intros H; rewrite <- Hd; exact (ctx_of_ty_any H). Qed.
Lemma ctxD_of_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] ].
Proof using Hd. intros H; rewrite <- Hd; exact (ctx_of_tm_any H). Qed.
Lemma tyD_of_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] T @ l ].
Proof using Hd. intros H; rewrite <- Hd; exact (wf_tm_ty_any H). Qed.

(** The extended contexts of a congruence are equivalent at D. *)
Lemma extc {Γ A A' l l'} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> lequiv (gL G) l l' ->
  [ G ⊢[ lD ] Γ ,, A @ l ≅ Γ ,, A' @ l' ].
Proof using Hd HiD.
  intros HA HAA Hl. apply eqc_ext; [apply eqc_refl, (ctxD_of_ty HA) | exact (lift_ty HA HiD)
                                   | exact (lift_eqty HAA HiD) | exact Hl].
Qed.

Lemma conv_at {Γ t T T' l} : [ G ; Γ ⊢[ i ] t : T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] t : T @ l ].
Proof using Hd. intros; eapply wf_conv; [eassumption | now rewrite Hd]. Qed.

Lemma convU_at {Γ t l l'} : [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] t : tyU l' @ lsuc l' ].
Proof using Hd.
  intros Ht Hl. eapply wf_lconv; [|apply lequiv_suc, lequiv_sym, Hl].
  apply (conv_at Ht). eapply eqty_lconv; [|apply lequiv_suc, Hl].
  apply eqty_U; [discriminate | exact (ctxD_of_tm Ht) | solve [apply lequiv_sym; assumption]].
Qed.

Lemma pc_pi {Γ l1 l2 l3 l4 A A' B B'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyPi l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢[ i ] tyPi l3 l4 A' B' @ lmax l1 l2 ].
Proof using Hd HiD.
  intros Hv H13 H24 HA HAA HA' HB HB'. split; [apply wft_pi; eauto using lequiv_wf_l|].
  eapply wft_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply wft_pi; eauto using lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | solve [apply lequiv_sym; assumption]].
  - eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | solve [apply lequiv_sym; assumption]].
Qed.

Lemma pc_El {Γ l l' t t'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] t' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] tyEl l t @ l ] /\ [ G ; Γ ⊢[ i ] tyEl l' t' @ l ].
Proof using Hd.
  intros Hv Hl Ht Ht'. split; [apply wft_El; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|exact Hl]. apply wft_El; eauto using lequiv_wf_r. exact (convU_at Ht' Hl).
Qed.

Lemma pc_U {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tyU l' @ lsuc l ].
Proof using .
  intros Hv HΓ Hl. split; [apply wft_U; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|apply lequiv_suc, Hl]. apply wft_U; eauto using lequiv_wf_r.
Qed.

Lemma pc_codeU {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmU l : tyU (lsuc l) @ lsuc (lsuc l) ] /\
  [ G ; Γ ⊢[ i ] tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ].
Proof using Hd.
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
Proof using Hd HiD.
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
Proof using Hd HiD.
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
    + eapply wft_lconv; [exact HM' | solve [apply lequiv_sym; assumption]].
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
Proof using Hd HiD.
  intros Hv H13 H24 HA HAA HA' Ht Ht'. split; [apply wf_lam; eauto using lequiv_wf_l|].
  eapply wf_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply (conv_at (T' := tyPi l3 l4 A' B)).
  - apply wf_lam; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | solve [apply lequiv_sym; assumption]].
    + eapply wf_lconv; [exact (ctxconv_tm (extc HA HAA H13) Hd Ht') | solve [apply lequiv_sym; assumption]].
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
Proof using Hd HiD.
  intros Hv H13 H24 HA HAA HA' HBB HB HB' Ht Ht' Hss Hs Hs'.
  split; [apply wf_app; eauto using lequiv_wf_l|].
  pose proof (lift_eqty HAA HiD) as HAAd. pose proof (lift_eqty HBB HiD) as HBBd.
  pose proof (lift_tm Hs HiD) as Hsd. pose proof (lift_tm Hs' HiD) as Hsd'.
  assert (HPi : [ G ; Γ ⊢[ lD ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ])
    by (apply eqty_pi; [discriminate | assumption | assumption | exact (lift_ty HA HiD) | exact HAAd | exact HBBd]).
  eapply wf_lconv with (l' := l4); [|exact H24].
  apply (conv_at (T' := B'[lsingle s'])).
  - apply wf_app; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | solve [apply lequiv_sym; assumption]].
    + eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | solve [apply lequiv_sym; assumption]].
    + eapply wf_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
      apply (conv_at Ht'). now apply eqty_sym.
    + eapply wf_lconv with (l' := l1); [|solve [apply lequiv_sym; assumption]].
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
Proof using Hd HiD.
  intros Hv H13 H24 HA HAA HA' HB HB'. split; [apply wft_sig; eauto using lequiv_wf_l|].
  eapply wft_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply wft_sig; eauto using lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | solve [apply lequiv_sym; assumption]].
  - eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | solve [apply lequiv_sym; assumption]].
Qed.

Lemma pc_codesig {Γ l1 l2 l3 l4 s s' t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSig l1 l2 s t : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmSig l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using Hd HiD.
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
Proof using HiD.
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
Proof using Hd HiD.
  intros Hv H13 H24 HA HAA HA' HBB HB HB' Haa Ha Ha' Hb Hb'.
  split; [apply wf_pair; eauto using lequiv_wf_l|].
  pose proof (lift_eqty HBB HiD) as HBBd.
  pose proof (lift_tm Ha HiD) as Had. pose proof (lift_tm Ha' HiD) as Had'.
  eapply wf_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply (conv_at (T' := tySig l3 l4 A' B')).
  - apply wf_pair; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | solve [apply lequiv_sym; assumption]].
    + eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | solve [apply lequiv_sym; assumption]].
    + eapply wf_lconv with (l' := l1); [|solve [apply lequiv_sym; assumption]].
      apply (conv_at Ha'). apply eqty_sym, (lift_eqty HAA HiD).
    + eapply wf_lconv with (l' := l2); [|solve [apply lequiv_sym; assumption]].
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
Proof using Hd HiD.
  intros Hv H13 H24 HA HAA HA' HBB HB HB' Hp Hp'.
  split; [apply wf_fst; eauto using lequiv_wf_l|].
  eapply wf_lconv with (l' := l3); [|exact H13].
  apply (conv_at (T' := A')).
  - apply wf_fst; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | solve [apply lequiv_sym; assumption]].
    + eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | solve [apply lequiv_sym; assumption]].
    + eapply wf_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
      apply (conv_at Hp'). exact (eqty_sym _ _ _ _ _ _ (sig_eqD H13 H24 HA HAA HBB)).
  - eapply eqty_lconv; [exact (lift_eqty HAA HiD) | solve [apply lequiv_sym; assumption]].
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
Proof using Hd HiD.
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
    + eapply wft_lconv; [exact HA' | solve [apply lequiv_sym; assumption]].
    + eapply wft_lconv; [exact (ctxconv_ty (extc HA HAA H13) Hd HB') | solve [apply lequiv_sym; assumption]].
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
Proof using .
  intros Hv HΓ Hl. split; [apply wft_unit; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|exact Hl]. apply wft_unit; eauto using lequiv_wf_r.
Qed.

Lemma pc_codeunit {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmUnit l : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmUnit l' : tyU l @ lsuc l ].
Proof using Hd.
  intros Hv HΓ Hl. split; [apply wf_code_unit; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [apply wf_code_unit; eauto using lequiv_wf_r | solve [apply lequiv_sym; assumption]].
Qed.

Lemma pc_triv {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmTriv l : tyUnit l @ l ] /\ [ G ; Γ ⊢[ i ] tmTriv l' : tyUnit l @ l ].
Proof using Hd.
  intros Hv HΓ Hl. split; [apply wf_triv; eauto using lequiv_wf_l|].
  eapply wf_lconv with (l' := l'); [|exact Hl].
  apply (conv_at (T' := tyUnit l')); [apply wf_triv; eauto using lequiv_wf_r|].
  rewrite Hd in HΓ. eapply eqty_lconv; [apply eqty_unit; [discriminate | exact HΓ | exact Hl] | solve [apply lequiv_sym; assumption]].
Qed.

Lemma pc_gvar {Γ u Δ i' T l d d'} : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] gvar u d : T[d] @ l ] /\ [ G ; Γ ⊢[ i ] gvar u d' : T[d] @ l ].
Proof using Hd HiD.
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
Proof using Hd HiD.
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
Proof using HiD.
  intros Hv Hl HA HAA HA' Ha Ha' Hb Hb'.
  split; [apply wft_id; eauto using lequiv_wf_l | exact (sc_id_q HiD Hv Hl HA' HAA Ha' Hb')].
Qed.

Lemma pc_idrefl {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmRefl l A a : tyId l A a a @ l ] /\ [ G ; Γ ⊢[ i ] tmRefl l' A' a' : tyId l A a a @ l ].
Proof using HiD.
  intros Hv Hl HA HAA HA' Haa Ha Ha'.
  split; [apply wf_idrefl; eauto using lequiv_wf_l | exact (sc_idrefl_q HiD Hv Hl HA HA' HAA Ha' Haa)].
Qed.

Lemma pc_code_id {Γ l l' s s' t t' u u'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] u : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmId l s t u : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmId l' s' t' u' : tyU l @ lsuc l ].
Proof using HiD.
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
Proof using HiD.
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
Proof using HiD.
  intros Hv Hl HA HAA HA' Ha Ha' Hb Hb'.
  split; [apply wft_seq; eauto using lequiv_wf_l | exact (sc_seq_q HiD Hv Hl HA' HAA Ha' Hb')].
Qed.

Lemma pc_sempty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tySEmpty l @ l ] /\ [ G ; Γ ⊢[ i ] tySEmpty l' @ l ].
Proof using .
  intros Hv HΓ Hl. split; [apply wft_sempty; eauto using lequiv_wf_l|].
  eapply wft_lconv; [|exact Hl]. apply wft_sempty; eauto using lequiv_wf_r.
Qed.

Lemma pc_srefl {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] srefl l A a : tySEq l A a a @ l ] /\ [ G ; Γ ⊢[ i ] srefl l' A' a' : tySEq l A a a @ l ].
Proof using HiD.
  intros Hv Hl HA HAA HA' Haa Ha Ha'.
  split; [apply wf_srefl; eauto using lequiv_wf_l | exact (sc_srefl_q HiD Hv Hl HA HA' HAA Ha' Haa)].
Qed.

Lemma pc_elimSEmpty {Γ l1 l2 l3 l4 M M' e e'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] M @ l2 ] -> [ G ; Γ ⊢[ i ] M ≅ M' @ l2 ] -> [ G ; Γ ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ⊢[ i ] e : tySEmpty l1 @ l1 ] -> [ G ; Γ ⊢[ i ] e' : tySEmpty l1 @ l1 ] ->
  [ G ; Γ ⊢[ i ] elimSEmpty l1 l2 M e : M @ l2 ] /\ [ G ; Γ ⊢[ i ] elimSEmpty l3 l4 M' e' : M @ l2 ].
Proof using HiD.
  intros Hv H13 H24 HM HMM HM' He He'.
  split; [apply wf_elimSEmpty; eauto using lequiv_wf_l | exact (sc_elimSEmpty_q HiD Hv H13 H24 HM' HMM He')].
Qed.

Lemma pc_code_seq {Γ l l' s s' t t' u u'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] u : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmSEq l s t u : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmSEq l' s' t' u' : tyU l @ lsuc l ].
Proof using HiD.
  intros Hv Hl Hs Hss Hs' Ht Ht' Hu Hu'.
  split; [apply wf_code_seq; eauto using lequiv_wf_l | exact (sc_code_seq_q HiD Hv Hl Hs' Hss Ht' Hu')].
Qed.

Lemma pc_code_sempty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmSEmpty l : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmSEmpty l' : tyU l @ lsuc l ].
Proof using Hd.
  intros Hv HΓ Hl. split; [apply wf_code_sempty; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [apply wf_code_sempty; eauto using lequiv_wf_r | solve [apply lequiv_sym; assumption]].
Qed.


(** The empty type and binary sums (every layer but V since M12c). *)
Lemma pc_empty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tyEmpty l @ l ] /\ [ G ; Γ ⊢[ i ] tyEmpty l' @ l ].
Proof using .
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
Proof using HiD.
  intros Hv H13 H24 HM HMM HM' Htt Ht Ht'.
  split; [apply wf_elimEmpty; eauto using lequiv_wf_l | exact (sc_elimEmpty_q HiD Hv H13 H24 HM' HMM Ht Ht' Htt)].
Qed.

Lemma pc_sum {Γ l1 l2 l3 l4 A A' B B'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tySum l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢[ i ] tySum l3 l4 A' B' @ lmax l1 l2 ].
Proof using .
  intros Hv H13 H24 HA HA' HB HB'.
  split; [apply wft_sum; eauto using lequiv_wf_l | exact (sc_sum_q Hv H13 H24 HA' HB')].
Qed.

Lemma pc_inl {Γ l1 l2 l3 l4 A A' B B' a a'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmInl l1 l2 A B a : tySum l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmInl l3 l4 A' B' a' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using HiD.
  intros Hv H13 H24 HA HAA HA' HB HBB HB' Ha Ha'.
  split; [apply wf_inl; eauto using lequiv_wf_l | exact (sc_inl_q HiD Hv H13 H24 HA' HAA HB' HBB Ha')].
Qed.

Lemma pc_inr {Γ l1 l2 l3 l4 A A' B B' b b'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] b : B @ l2 ] -> [ G ; Γ ⊢[ i ] b' : B @ l2 ] ->
  [ G ; Γ ⊢[ i ] tmInr l1 l2 A B b : tySum l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmInr l3 l4 A' B' b' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using HiD.
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
Proof using HiD.
  intros Hv H14 H25 H36 HA HAA HA' HB HBB HB' HM HMM HM' Hc1 Hc1' Hc2 Hc2' Htt Ht Ht'.
  split; [apply wf_case; eauto using lequiv_wf_l |].
  exact (sc_case_q HiD Hv H14 H25 H36 HA HA' HAA HB HB' HBB HM HM' HMM Hc1' Hc2' Ht Ht' Htt).
Qed.

Lemma pc_code_empty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] tmEmpty l : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmEmpty l' : tyU l @ lsuc l ].
Proof using Hd.
  intros Hv HΓ Hl. split; [apply wf_code_empty; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [apply wf_code_empty; eauto using lequiv_wf_r | solve [apply lequiv_sym; assumption]].
Qed.

Lemma pc_code_sum {Γ l1 l2 l3 l4 s s' t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] t : tyU l2 @ lsuc l2 ] -> [ G ; Γ ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSum l1 l2 s t : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmSum l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using HiD.
  intros Hv H13 H24 Hs Hs' Ht Ht'.
  split; [apply wf_code_sum; eauto using lequiv_wf_l | exact (sc_code_sum_q HiD Hv H13 H24 Hs' Ht')].
Qed.

(** Well-founded trees and their code (every layer but V since M13b). *)
Lemma pc_W {Γ l1 l2 l3 l4 A A' B B'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢[ i ] tyW l3 l4 A' B' @ lmax l1 l2 ].
Proof using HiD.
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
Proof using HiD.
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
Proof using HiD.
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
Proof using Hd HiD.
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
Proof using .
  intros Hv Hl HA HA' Hn Hn'. split; [apply wft_vec; eauto using lequiv_wf_l|].
  eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_vec; eauto using lequiv_wf_r. eapply wft_lconv; [exact HA' | solve [apply lequiv_sym; assumption]].
Qed.

Lemma pc_fin {Γ n n'} : i <> lV ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyFin n @ lzero ] /\ [ G ; Γ ⊢[ i ] tyFin n' @ lzero ].
Proof using . intros Hv Hn Hn'. split; apply wft_fin; assumption. Qed.

Lemma pc_code_vec {Γ l l' s s' n n'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmVec l s n : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmVec l' s' n' : tyU l @ lsuc l ].
Proof using Hd.
  intros Hv Hl Hs Hs' Hn Hn'. split; [apply wf_code_vec; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [|solve [apply lequiv_sym; assumption]].
  apply wf_code_vec; eauto using lequiv_wf_r. exact (convU_at Hs' Hl).
Qed.

Lemma pc_code_sq {Γ l l' s s'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] tmSqCode l s : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmSqCode l' s' : tyU l @ lsuc l ].
Proof using Hd.
  intros Hv Hl Hs Hs'. split; [apply wf_code_sq; eauto using lequiv_wf_l|].
  apply (convU_at (l := l')); [|solve [apply lequiv_sym; assumption]].
  apply wf_code_sq; eauto using lequiv_wf_r. exact (convU_at Hs' Hl).
Qed.

(** Propositional truncation (every layer but V since M16b). *)
Lemma pc_tySq {Γ l l' A A'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] tySq l A @ l ] /\ [ G ; Γ ⊢[ i ] tySq l' A' @ l ].
Proof using .
  intros Hv Q HA HA'. split; [apply wft_sq; eauto using lequiv_wf_l |].
  eapply wft_lconv; [| exact Q].
  apply wft_sq; [exact Hv | eauto using lequiv_wf_r | eapply wft_lconv; [exact HA' | exact (lequiv_sym _ _ _ Q)]].
Qed.

Lemma pc_sq {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmSq l A a : tySq l A @ l ] /\ [ G ; Γ ⊢[ i ] tmSq l' A' a' : tySq l A @ l ].
Proof using HiD.
  intros Hv Q HA HAA HA' Ha Ha'.
  split; [apply wf_sq; eauto using lequiv_wf_l | exact (sc_sq_q HiD Hv Q HA' HAA Ha')].
Qed.

Lemma pc_elimSq {Γ l1 l2 l3 l4 A A' M M' c c' t t'} : i <> lV ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M @ l2 ] -> [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c' : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tySq l1 A @ l1 ] ->
  [ G ; Γ ⊢[ i ] t : tySq l1 A @ l1 ] -> [ G ; Γ ⊢[ i ] t' : tySq l1 A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmElimSq l1 l2 A M c t : tySq l2 M[lsingle t] @ l2 ] /\
  [ G ; Γ ⊢[ i ] tmElimSq l3 l4 A' M' c' t' : tySq l2 M[lsingle t] @ l2 ].
Proof using HiD.
  intros Hv H13 H24 HA HAA HA' HM HMM HM' Hc Hc' Htt Ht Ht'.
  split; [apply wf_elimSq; eauto using lequiv_wf_l |].
  exact (sc_elimSq_q HiD Hv H13 H24 HA HA' HAA HM HM' HMM Hc' Ht Ht' Htt).
Qed.

Lemma pc_code_fin {Γ n n'} : i <> lV ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmFin n : tyU lzero @ lsuc lzero ] /\ [ G ; Γ ⊢[ i ] tmFin n' : tyU lzero @ lsuc lzero ].
Proof using . intros Hv Hn Hn'. split; apply wf_code_fin; assumption. Qed.

(** Finitary well-founded trees and their code (every layer but V since
    M15b): the right telescope of [elim_Wf] from [static_code]'s, at the
    [≡ₗ]-related syntax [static_code_eq] gives. *)
Lemma pc_wf {Γ l l' A A' N N'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyWf l A N @ l ] /\ [ G ; Γ ⊢[ i ] tyWf l' A' N' @ l ].
Proof using HiD.
  intros Hv Hl HA HAA HA' HN HN'.
  split; [apply wft_wf; eauto using lequiv_wf_l | exact (sc_wf_q HiD Hv Hl HA HA' HAA HN')].
Qed.

Lemma pc_supf {Γ l l' A A' N N' a a' cs cs'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] tmSupf l A N a cs : tyWf l A N @ l ] /\ [ G ; Γ ⊢[ i ] tmSupf l' A' N' a' cs' : tyWf l A N @ l ].
Proof using HiD.
  intros Hv Hl HA HAA HA' HN HNN HN' Haa Ha Ha' Hcs Hcs'.
  split; [apply wf_supf; eauto using lequiv_wf_l |].
  exact (sc_supf_q HiD Hv Hl HA HA' HAA HN HN' HNN Ha Ha' Haa Hcs').
Qed.

Lemma pc_elimWf {Γ l1 l2 l3 l4 A A' N N' M M' c c' t t'} : i <> lV ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] -> [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l1 A N @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ] wfihty l1 l2 A N M @ lmax lzero l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ⊢[ i ] c : wfstepty l1 A N M @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ⊢[ i ] c' : wfstepty l1 A N M @ l2 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyWf l1 A N @ l1 ] ->
  [ G ; Γ ⊢[ i ] t : tyWf l1 A N @ l1 ] -> [ G ; Γ ⊢[ i ] t' : tyWf l1 A N @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmElimWf l1 l2 A N M c t : M[lsingle t] @ l2 ] /\
  [ G ; Γ ⊢[ i ] tmElimWf l3 l4 A' N' M' c' t' : M[lsingle t] @ l2 ].
Proof using HiD.
  intros Hv H13 H24 HA HAA HA' HN HNN HN' HM HMM HM' HC HI Hc Hc' Htt Ht Ht'.
  split; [apply wf_elimWf; eauto using lequiv_wf_l |].
  exact (sc_elimWf_q HiD Hv H13 H24 HA HA' HAA HN HN' HNN HM HM' HMM HI Hc' Ht Ht' Htt).
Qed.

Lemma pc_codewf {Γ l l' s s' n n'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmWf l s n : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmWf l' s' n' : tyU l @ lsuc l ].
Proof using Hd HiD.
  intros Hv Hl Hs Hss Hs' Hn Hn'. split; [apply wf_code_wf; eauto using lequiv_wf_l|].
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l s @ l ]) by (apply wft_El; eauto using lequiv_wf_l).
  assert (HEE : [ G ; Γ ⊢[ i ] tyEl l s ≅ tyEl l' s' @ l ]) by (apply eqty_El; auto).
  apply (convU_at (l := l')); [|solve [apply lequiv_sym; assumption]].
  apply wf_code_wf; eauto using lequiv_wf_r.
  - exact (convU_at Hs' Hl).
  - exact (ctxconv_tm (extc HEl HEE Hl) Hd Hn').
Qed.

(** Dependent tuples and indexed W-types (M17c), along [StaticCode]'s
    [_q] forms. *)
Lemma pc_dvec {Γ l l' n n' F F'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F @ l ] -> [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F ≅ F' @ l ] ->
  [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F' @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec l n F @ l ] /\ [ G ; Γ ⊢[ i ] tyDVec l' n' F' @ l ].
Proof using Hd HiD.
  intros Hv Hl Hn Hnn Hn' HF HFF HF'. split; [apply wft_dvec; eauto using lequiv_wf_l |].
  assert (HF0 : [ G ; Γ ⊢[ i ] tyFin n @ lzero ]) by (apply wft_fin; assumption).
  assert (HFF0 : [ G ; Γ ⊢[ i ] tyFin n ≅ tyFin n' @ lzero ]) by (apply eqty_fin; assumption).
  eapply wft_lconv; [| exact Hl]. apply wft_dvec; [exact Hv | exact (lequiv_wf_r _ _ _ Hl) | exact Hn' |].
  eapply wft_lconv; [| apply lequiv_sym, Hl].
  exact (ctxconv_ty (extc HF0 HFF0 (lequiv_refl (gL G) lzero I)) Hd HF').
Qed.

Lemma pc_iwf {Γ l li k ki X X' A A' N N' Ot Ot' C C' m m'} : i <> lV ->
  lequiv (gL G) l k -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ⊢[ i ] X' @ li ] ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C' : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWf l li X A N Ot C m @ lmax l li ] /\
  [ G ; Γ ⊢[ i ] tyIWf k ki X' A' N' Ot' C' m' @ lmax l li ].
Proof using HiD.
  intros Hv Q1 Q2 HX HXX HX' HA HAA HA' HN HNN HN' HO HO' HC HC' Hm Hm'.
  split; [apply wft_iwf; eauto using lequiv_wf_l |].
  exact (sc_iwf_q HiD Hv Q1 Q2 HX' HXX HA HA' HAA HN HN' HNN HO' HC' Hm').
Qed.

Lemma pc_supi {Γ l li k ki X X' A A' N N' Ot Ot' C C' a a' cs cs'} : i <> lV ->
  lequiv (gL G) l k -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ⊢[ i ] X' @ li ] ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C' : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] cs' : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] tmSupi l li X A N Ot C a cs : tyIWf l li X A N Ot C Ot[lsingle a] @ lmax l li ] /\
  [ G ; Γ ⊢[ i ] tmSupi k ki X' A' N' Ot' C' a' cs' : tyIWf l li X A N Ot C Ot[lsingle a] @ lmax l li ].
Proof using HiD.
  intros Hv Q1 Q2 HX HXX HX' HA HAA HA' HN HNN HN' HO HOO HO' HC HCC HC' Haa Ha Ha' Hcs Hcs'.
  split; [apply wf_supi; eauto using lequiv_wf_l |].
  exact (sc_supi_q HiD Hv Q1 Q2 HX HX' HXX HA HA' HAA HN HN' HNN HO HO' HOO HC HC' HCC Ha Ha' Haa Hcs').
Qed.

Lemma pc_elimIWf {Γ l li l' k ki k' X X' A A' N N' Ot Ot' C C' M M' c c' m m' t t'} : i <> lV ->
  lequiv (gL G) l k -> lequiv (gL G) li ki -> lequiv (gL G) l' k' ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ⊢[ i ] X' @ li ] ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C' : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwfmotty l li X A N Ot C @ lmax l li ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M' @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwfcsty l li X A N Ot C @ lmax l li ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ]
      iwfihty l li l' X A N Ot C M ≅ iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c : iwfstepty l li X A N Ot C M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c' : iwfstepty l li X A N Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] -> [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyIWf l li X A N Ot C m @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] t : tyIWf l li X A N Ot C m @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] t' : tyIWf l li X A N Ot C m @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] tmElimIWf l li l' X A N Ot C M c m t : M[lsingle2 m t] @ l' ] /\
  [ G ; Γ ⊢[ i ] tmElimIWf k ki k' X' A' N' Ot' C' M' c' m' t' : M[lsingle2 m t] @ l' ].
Proof using HiD.
  intros Hv Q1 Q2 Q3 HX HXX HX' HA HAA HA' HN HNN HN' HO HOO HO' HC HCC HC' HMot HM HMM HM' HCs HI EI HI'
    Hc Hc' Hmm Hm Hm' Htt Ht Ht'.
  split; [apply wf_elimIWf; eauto using lequiv_wf_l |].
  exact (sc_elimIWf_q HiD Hv Q1 Q2 Q3 HX HX' HXX HA HA' HAA HN HN' HNN HO HO' HOO HC HC' HCC HM HM' HMM
           HI HI' EI Hc' Hm Hm' Hmm Ht Ht' Htt).
Qed.

(** Infinitary indexed families (M19a), as [IWf]'s. *)
Lemma pc_iwi {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' m m'} : i <> lV ->
  lequiv (gL G) l k -> lequiv (gL G) lp kp -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ⊢[ i ] X' @ li ] ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D @ lp ] -> [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D ≅ D' @ lp ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D' @ lp ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] /\
  [ G ; Γ ⊢[ i ] tyIWi k kp ki X' A' N' D' Ot' C' m' @ iwiL l lp li ].
Proof using HiD.
  intros Hv Q1 Qp Q2 HX HXX HX' HA HAA HA' HN HNN HN' HD HDD HD' HO HOO HO' HC HCC HC' Hm Hm'.
  split; [apply wft_iwi; eauto using lequiv_wf_l |].
  exact (sc_iwi_q HiD Hv Q1 Qp Q2 HX' HXX HA HA' HAA HN HN' HNN HD HD' HDD HO' HC' Hm').
Qed.

Lemma pc_supii {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' a a' cs cs'} : i <> lV ->
  lequiv (gL G) l k -> lequiv (gL G) lp kp -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ⊢[ i ] X' @ li ] ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D @ lp ] -> [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D ≅ D' @ lp ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D' @ lp ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] cs' : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] tmSupii l lp li X A N D Ot C a cs : tyIWi l lp li X A N D Ot C Ot[lsingle a] @ iwiL l lp li ] /\
  [ G ; Γ ⊢[ i ] tmSupii k kp ki X' A' N' D' Ot' C' a' cs' : tyIWi l lp li X A N D Ot C Ot[lsingle a] @ iwiL l lp li ].
Proof using HiD.
  intros Hv Q1 Qp Q2 HX HXX HX' HA HAA HA' HN HNN HN' HD HDD HD' HO HOO HO' HC HCC HC' Haa Ha Ha' Hcs Hcs'.
  split; [apply wf_supii; eauto using lequiv_wf_l |].
  exact (sc_supii_q HiD Hv Q1 Qp Q2 HX HX' HXX HA HA' HAA HN HN' HNN HD HD' HDD HO HO' HOO HC HC' HCC Ha Ha' Haa Hcs').
Qed.

Lemma pc_elimIWi {Γ l lp li l' k kp ki k' X X' A A' N N' D D' Ot Ot' C C' M M' c c' m m' t t'} : i <> lV ->
  lequiv (gL G) l k -> lequiv (gL G) lp kp -> lequiv (gL G) li ki -> lequiv (gL G) l' k' ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ⊢[ i ] X' @ li ] ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D @ lp ] -> [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D ≅ D' @ lp ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D' @ lp ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwimotty l lp li X A N D Ot C @ iwiL l lp li ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M' @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwicsty l lp li X A N D Ot C @ iwiL l lp li ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] 
      iwiihty l lp li l' X A N D Ot C M ≅ iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l')
      ⊢[ i ] c : iwistepty l lp li X A N D Ot C M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l')
      ⊢[ i ] c' : iwistepty l lp li X A N D Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] -> [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] t : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] t' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] tmElimIWi l lp li l' X A N D Ot C M c m t : M[lsingle2 m t] @ l' ] /\
  [ G ; Γ ⊢[ i ] tmElimIWi k kp ki k' X' A' N' D' Ot' C' M' c' m' t' : M[lsingle2 m t] @ l' ].
Proof using HiD.
  intros Hv Q1 Qp Q2 Q3 HX HXX HX' HA HAA HA' HN HNN HN' HD HDD HD' HO HOO HO' HC HCC HC' HMot HM HMM HM' HCs HI EI HI'
    Hc Hc' Hmm Hm Hm' Htt Ht Ht'.
  split; [apply wf_elimIWi; eauto using lequiv_wf_l |].
  exact (sc_elimIWi_q HiD Hv Q1 Qp Q2 Q3 HX HX' HXX HA HA' HAA HN HN' HNN HD HD' HDD HO HO' HOO HC HC' HCC
           HM HM' HMM HI HI' EI Hc' Hm Hm' Hmm Ht Ht' Htt).
Qed.

(** The codes of [DVec] and [IWf] (M17c), along [StaticCode]'s [_q] forms. *)
Lemma pc_code_dvec {Γ l l' n n' f f'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] f : tyU l @ lsuc l ] ->
  [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] f' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] tmDVec l n f : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmDVec l' n' f' : tyU l @ lsuc l ].
Proof using HiD.
  intros Hv Hl Hn Hnn Hn' Hf Hf'. split; [apply wf_code_dvec; eauto using lequiv_wf_l |].
  exact (sc_code_dvec_q HiD Hv Hl Hn Hn' Hnn Hf').
Qed.

Lemma pc_code_iwf {Γ l li k ki x x' s s' n n' o o' c c' m m'} : i <> lV ->
  lequiv (gL G) l k -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] x : tyU li @ lsuc li ] -> [ G ; Γ ⊢[ i ] x ≅ x' : tyU li @ lsuc li ] ->
  [ G ; Γ ⊢[ i ] x' : tyU li @ lsuc li ] ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] o : tyEl li x⟨↑⟩ @ li ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] o' : tyEl li x⟨↑⟩ @ li ] ->
  [ G ; Γ ,, tyEl l s @ l ,, tyFin n @ lzero ⊢[ i ] c : tyEl li x⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, tyEl l s @ l ,, tyFin n @ lzero ⊢[ i ] c' : tyEl li x⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] m : tyEl li x @ li ] -> [ G ; Γ ⊢[ i ] m' : tyEl li x @ li ] ->
  [ G ; Γ ⊢[ i ] tmIWf l li x s n o c m : tyU (lmax l li) @ lsuc (lmax l li) ] /\
  [ G ; Γ ⊢[ i ] tmIWf k ki x' s' n' o' c' m' : tyU (lmax l li) @ lsuc (lmax l li) ].
Proof using HiD.
  intros Hv Q1 Q2 Hx Hxx Hx' Hs Hss Hs' Hn Hnn Hn' Ho Ho' Hc Hc' Hm Hm'.
  split; [apply wf_code_iwf; eauto using lequiv_wf_l |].
  exact (sc_code_iwf_q HiD Hv Q1 Q2 Hx' Hxx Hs Hs' Hss Hn Hn' Hnn Ho' Hc' Hm').
Qed.

Lemma pc_code_iwi {Γ l lp li k kp ki x x' s s' n n' d d' o o' c c' m m'} : i <> lV ->
  lequiv (gL G) l k -> lequiv (gL G) lp kp -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] x : tyU li @ lsuc li ] -> [ G ; Γ ⊢[ i ] x ≅ x' : tyU li @ lsuc li ] ->
  [ G ; Γ ⊢[ i ] x' : tyU li @ lsuc li ] ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyEl l s @ l ,, tyFin n @ lzero ⊢[ i ] d : tyU lp @ lsuc lp ] ->
  [ G ; Γ ,, tyEl l s @ l ,, tyFin n @ lzero ⊢[ i ] d ≅ d' : tyU lp @ lsuc lp ] ->
  [ G ; Γ ,, tyEl l s @ l ,, tyFin n @ lzero ⊢[ i ] d' : tyU lp @ lsuc lp ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] o : tyEl li x⟨↑⟩ @ li ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] o' : tyEl li x⟨↑⟩ @ li ] ->
  [ G ; Γ ,, tyEl l s @ l ,, tyFin n @ lzero ,, tyEl lp d @ lp ⊢[ i ] c : tyEl li x⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, tyEl l s @ l ,, tyFin n @ lzero ,, tyEl lp d @ lp ⊢[ i ] c' : tyEl li x⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] m : tyEl li x @ li ] -> [ G ; Γ ⊢[ i ] m' : tyEl li x @ li ] ->
  [ G ; Γ ⊢[ i ] tmIWi l lp li x s n d o c m : tyU (iwiL l lp li) @ lsuc (iwiL l lp li) ] /\
  [ G ; Γ ⊢[ i ] tmIWi k kp ki x' s' n' d' o' c' m' : tyU (iwiL l lp li) @ lsuc (iwiL l lp li) ].
Proof using HiD.
  intros Hv Q1 Q3 Q2 Hx Hxx Hx' Hs Hss Hs' Hn Hnn Hn' HdD HddD HdD' Ho Ho' Hc Hc' Hm Hm'.
  split; [apply wf_code_iwi; eauto using lequiv_wf_l |].
  exact (sc_code_iwi_q HiD Hv Q1 Q3 Q2 Hx' Hxx Hs Hs' Hss Hn Hn' Hnn HdD HdD' HddD Ho' Hc' Hm').
Qed.

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
  apply typing_mut; intros.
  par: (
    (try exact I;
    (* the computing and M-only rules do not apply below D *)
    try match goal with
        | Hc : compt ?i, Hle : lle ?i lC |- _ => exfalso; exact (lle_C_not_compt Hle Hc)
        | Hle : lle lM lC |- _ => exfalso; exact (lle_C_not_M Hle eq_refl)
        end;
    repeat match goal with IH : lle ?j lC -> _, Hle : lle ?j lC |- _ => specialize (IH Hle) end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end);
    (try solve [split; auto]);
    (try solve [split; eapply wf_conv; eassumption]);
    (try solve [split; eapply wft_lconv; eassumption]);
    (try solve [split; eapply wf_lconv; eassumption]);
    (try solve [split; apply wf_succ; assumption]);
    (try solve [split; first [eapply wft_gvar | eapply wf_gvar]; eassumption]);
    (first [ solve [eapply pc_pi; eassumption] | solve [eapply pc_El; eassumption]
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
             | solve [eapply pc_code_vec; eassumption] | solve [eapply pc_code_fin; eassumption]
             (* finitary well-founded trees and their code (M15b) *)
             | solve [eapply pc_wf; eassumption] | solve [eapply pc_supf; eassumption]
             | solve [eapply pc_elimWf; eassumption] | solve [eapply pc_codewf; eassumption]
             (* the code of ∥·∥ (M16b) *)
             | solve [eapply pc_code_sq; eassumption]
             (* propositional truncation at C (M16b) *)
             | solve [eapply pc_tySq; eassumption] | solve [eapply pc_sq; eassumption]
             | solve [eapply pc_elimSq; eassumption]
             (* dependent tuples and indexed W-types, with their codes (M17c) *)
             | solve [eapply pc_dvec; eassumption] | solve [eapply pc_iwf; eassumption]
             | solve [eapply pc_supi; eassumption] | solve [eapply pc_elimIWf; eassumption]
             | solve [eapply pc_code_dvec; eassumption] | solve [eapply pc_code_iwf; eassumption]
             (* infinitary indexed families (M19a) *)
             | solve [eapply pc_iwi; eassumption] | solve [eapply pc_supii; eassumption]
             | solve [eapply pc_elimIWi; eassumption]
             (* the code of IWi (M19c) *)
             | solve [eapply pc_code_iwi; eassumption] ])).
Qed.

Lemma eqty_wf_C {G i Γ T T' l} : lle i lC -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] T @ l ] /\ [ G ; Γ ⊢[ i ] T' @ l ].
Proof. intros Hle H; exact (proj1 (proj2 (proj2 (proj2 (proj2 presupposition_C)))) _ _ _ _ _ _ H Hle). Qed.
Lemma eqtm_wf_C {G i Γ t t' T l} : lle i lC -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] t : T @ l ] /\ [ G ; Γ ⊢[ i ] t' : T @ l ].
Proof.
  intros Hle H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 presupposition_C))))) _ _ _ _ _ _ _ H Hle).
Qed.
