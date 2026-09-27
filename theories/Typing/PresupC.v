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
             | solve [eapply pc_gvar; eassumption] ].
Qed.

Lemma eqty_wf_C {G i Γ T T' l} : lle i lC -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] T @ l ] /\ [ G ; Γ ⊢[ i ] T' @ l ].
Proof. intros Hle H; exact (proj1 (proj2 (proj2 (proj2 (proj2 presupposition_C)))) _ _ _ _ _ _ H Hle). Qed.
Lemma eqtm_wf_C {G i Γ t t' T l} : lle i lC -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] t : T @ l ] /\ [ G ; Γ ⊢[ i ] t' : T @ l ].
Proof.
  intros Hle H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 presupposition_C))))) _ _ _ _ _ _ _ H Hle).
Qed.
