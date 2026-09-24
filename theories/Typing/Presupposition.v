(** * Presupposition (syntactic validity, ch. 5)

    Every judgment's components are well formed: the type of a typed term,
    both sides of a type equality, both sides of a term equality (and its
    type).  For layers with [typeof i = i]. *)
From DeLaM.Typing Require Export Functionality.

Section Aux.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).

(** ** Context lookups are well formed *)

Lemma in_ctx_wf {Γ n T l} : [ G ; Γ ⊢[ i ] ] -> in_ctx Γ n T l -> [ G ; Γ ⊢[ i ] T @ l ].
Proof.
  intros HΓ Hin; induction Hin as [Γ A l|Γ A l B l' n Hin IH]; inversion HΓ; subst.
  - apply wk1_ty; auto.
  - apply wk1_ty; auto.
Qed.

(** ** Some typed substitutions *)

Lemma lsub_wf_single2 {Γ M t q l} :
  [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] q : M[lsingle t] @ l ] ->
  [ G ; Γ ⊢[ i ] lsingle2 t q : Γ ,, tyNat @ lzero ,, M @ l ].
Proof.
  intros HΓ Ht Hq.
  refine (conj HΓ (conj (lk_lsingle2 _ _ (wf_tm_nf Ht) (wf_tm_nf Hq)) _)).
  intros n T l' Hin.
  inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst; cbn.
  - rewrite (ren_subst_ty _ _ _ (lsingle t)); [exact Hq|].
    intros k; rewrite rlk_shift1; reflexivity.
  - inversion Hm as [Γ1 A1 l2|Γ1 A1 l2 T1 l3 m' Hm']; subst; cbn.
    + exact Ht.
    + rewrite shift2_single2_ty by eauto using in_ctx_nf. rewrite Nat.add_0_r.
      apply wf_var; [now rewrite Hi | exact Hm'].
Qed.

Lemma lsub_wf_lsucc {Γ M l} :
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] lsucc : Γ ,, tyNat @ lzero ].
Proof.
  intros HΓ. refine (conj HΓ (conj lk_lsucc _)).
  intros n T l' Hin.
  inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst; cbn.
  - apply wf_succ; auto. apply wf_var; [now rewrite Hi | ].
    change tyNat with tyNat⟨↑⟩⟨↑⟩ at 2. do 2 constructor.
  - replace (m + 2) with (S (S m)) by lia.
    unfold lsucc; rewrite shift_cons2_ty, <- shift2_as_ty.
    apply wf_var; [now rewrite Hi | do 2 constructor; exact Hm].
Qed.

Lemma lsub_eq_single {Γ A t t' l} :
  [ G ; Γ ⊢[ i ] t : A @ l ] -> [ G ; Γ ⊢[ i ] t' : A @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : A @ l ] ->
  [ G ; Γ ⊢[ i ] lsingle t ≅ lsingle t' : Γ ,, A @ l ].
Proof.
  intros Ht Ht' Heq. pose proof (ctx_of_wf_tm Hi Ht) as HΓ.
  refine (conj (lsub_wf_single G i Hi _ _ _ _ HΓ Ht) (conj (lsub_wf_single G i Hi _ _ _ _ HΓ Ht') _)).
  intros n T l' Hin.
  inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst; cbn.
  - rewrite shift_single_ty by exact (wf_tm_nf_ty Ht). exact Heq.
  - rewrite shift_single_ty by eauto using in_ctx_nf. rewrite Nat.add_0_r.
    apply eqtm_refl, wf_var; [now rewrite Hi | exact Hm].
Qed.

(** ** Conversions of types and levels *)

Lemma conv_tm' {Γ t T T' l} :
  [ G ; Γ ⊢[ i ] t : T' @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] t : T @ l ].
Proof. intros; eapply wf_conv; [eassumption | now rewrite Hi]. Qed.

Lemma conv_U {Γ t l l'} :
  [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] t : tyU l' @ lsuc l' ].
Proof.
  intros Ht Hl. pose proof (ctx_of_wf_tm Hi Ht).
  eapply wf_lconv; [|apply lequiv_suc, lequiv_sym, Hl].
  eapply conv_tm'; [exact Ht|]. eapply eqty_lconv; [|apply lequiv_suc, Hl].
  apply eqty_U; [exact Hv | now rewrite Hi | now apply lequiv_sym].
Qed.

Lemma ext_wf {Γ A l} : [ G ; Γ ⊢[ i ] A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢[ i ] ].
Proof. intros; apply wfc_ext; auto; exact (ctx_of_wf_ty Hi ltac:(eassumption)). Qed.

(** ** Right-hand sides of congruences *)

Lemma pre_pi_r {Γ l1 l2 l3 l4 A A' B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyPi l3 l4 A' B' @ lmax l1 l2 ].
Proof.
  intros H13 H24 HA HA' HB.
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  eapply wft_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply wft_pi; try solve [eauto using lequiv_wf_r].
  eapply wft_lconv; [|apply lequiv_sym; exact H24].
  eapply (stab_ty Hi HA H13); [apply ext_wf; eauto using lequiv_wf_r | exact HB].
Qed.

Lemma pre_El_r {Γ l l' t'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] t' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] tyEl l' t' @ l ].
Proof.
  intros Hl Ht. eapply wft_lconv; [|exact Hl].
  apply wft_El; try solve [eauto using lequiv_wf_r]. now apply (conv_U Ht).
Qed.

Lemma pre_codeU_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ].
Proof.
  intros HΓ Hl. eapply wf_lconv with (l' := lsuc (lsuc l')); [|now apply lequiv_suc, lequiv_suc].
  eapply conv_tm'; [apply wf_code_U; eauto using lequiv_wf_r; now rewrite Hi|].
  eapply eqty_lconv; [|apply lequiv_suc, lequiv_suc, lequiv_sym, Hl].
  apply eqty_U; [exact Hv | now rewrite Hi | now apply lequiv_suc].
Qed.

Lemma pre_codepi_r {Γ l1 l2 l3 l4 s s' t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmPi l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof.
  intros H13 H24 Hs Hs' Ht. pose proof (ctx_of_wf_tm Hi Hs') as HΓ.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; auto).
  assert (Hs3 : [ G ; Γ ⊢[ i ] s' : tyU l3 @ lsuc l3 ]) by exact (conv_U Hs' H13).
  eapply wf_lconv with (l' := lsuc (lmax l3 l4)); [|apply lequiv_suc, lequiv_max; eassumption].
  eapply conv_tm'.
  - apply wf_code_pi; try solve [eauto using lequiv_wf_r].
    apply (conv_U (l := l2)); [|exact H24].
    eapply (stab_tm Hi HEl H13); [|exact Ht].
    apply ext_wf; [apply wft_El; eauto using lequiv_wf_r | eauto using lequiv_wf_r].
  - eapply eqty_lconv; [|apply lequiv_suc, lequiv_max; apply lequiv_sym; eassumption].
    apply eqty_U; [exact Hv | now rewrite Hi | apply lequiv_max; eassumption].
Qed.

Lemma pre_U_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tyU l' @ lsuc l ].
Proof.
  intros HΓ Hl. eapply wft_lconv with (l' := lsuc l'); [|now apply lequiv_suc].
  apply wft_U; eauto using lequiv_wf_r. now rewrite Hi.
Qed.

Lemma wf_ty_func {Γ T l Δ d d'} :
  [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T[d'] @ l ].
Proof. intros; eapply functionality; eauto. Qed.

Lemma pre_natrec_r {Γ l l' M M' s' z' t t'} :
  lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M ≅ M' @ l ] -> [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' @ l ] ->
  [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] t' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] natrec l' M' s' z' t' : M[lsingle t] @ l ].
Proof.
  intros Hl HM HMM HM' Hs' Hz' Htt Ht Ht'.
  pose proof (ctx_of_wf_tm Hi Ht) as HΓ.
  assert (HM'l : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' @ l' ])
    by (eapply wft_lconv; [exact HM' | now apply lequiv_sym]).
  assert (HΓM : [ G ; Γ ,, tyNat @ lzero ,, M' @ l' ⊢[ i ] ])
    by (apply ext_wf; eauto using lequiv_wf_r).
  assert (Hz : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ])
    by (apply wf_zero; [exact Hv | now rewrite Hi]).
  eapply wf_lconv with (l' := l'); [|exact Hl].
  eapply (conv_tm' (T' := M'[lsingle t'])).
  - apply wf_natrec; eauto using lequiv_wf_r.
    + eapply wf_lconv; [|apply lequiv_sym, Hl].
      eapply conv_tm'; [exact Hs'|]. apply eqty_sym. exact (eqty_single Hi HMM Hz).
    + eapply wf_lconv; [|apply lequiv_sym, Hl].
      eapply conv_tm'; [exact (stab_tm Hi HMM Hl HΓM Hz')|].
      apply eqty_sym. eapply (eqty_subst Hi HMM). now apply lsub_wf_lsucc.
  - eapply eqty_lconv; [|apply lequiv_sym, Hl].
    eapply eqty_trans.
    + apply (wf_ty_func HM (d' := lsingle t')). now apply lsub_eq_single.
    + exact (eqty_single Hi HMM Ht').
Qed.

Lemma pre_lam_r {Γ l1 l2 l3 l4 A A' B t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] t' : B @ l2 ] ->
  [ G ; Γ ⊢[ i ] lam l3 l4 A' t' : tyPi l1 l2 A B @ lmax l1 l2 ].
Proof.
  intros H13 H24 HA HAA HA' HB Ht'.
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓ' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply ext_wf; eauto using lequiv_wf_r).
  eapply wf_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  eapply (conv_tm' (T' := tyPi l3 l4 A' B)).
  - apply wf_lam; eauto using lequiv_wf_r.
    eapply wf_lconv; [exact (stab_tm Hi HAA H13 HΓ' Ht') | now apply lequiv_sym].
  - eapply eqty_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
    apply eqty_pi; auto using eqty_refl.
Qed.

Lemma pre_app_r {Γ l1 l2 l3 l4 A A' B B' t' s s'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] t' : tyPi l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] s ≅ s' : A @ l1 ] -> [ G ; Γ ⊢[ i ] s : A @ l1 ] -> [ G ; Γ ⊢[ i ] s' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] app t' l3 l4 A' B' s' : B[lsingle s] @ l2 ].
Proof.
  intros H13 H24 HA HAA HA' HB HBB HB' Ht' Hss Hs Hs'.
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓ' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply ext_wf; eauto using lequiv_wf_r).
  assert (HPi : [ G ; Γ ⊢[ i ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ])
    by (apply eqty_pi; auto).
  eapply wf_lconv with (l' := l4); [|exact H24].
  eapply (conv_tm' (T' := B'[lsingle s'])).
  - apply wf_app; eauto using lequiv_wf_r.
    + eapply wft_lconv; [exact (stab_ty Hi HAA H13 HΓ' HB') | now apply lequiv_sym].
    + eapply wf_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
      eapply conv_tm'; [exact Ht'|]. now apply eqty_sym.
    + eapply wf_lconv with (l' := l1); [|now apply lequiv_sym].
      eapply conv_tm'; [exact Hs'|]. now apply eqty_sym.
  - eapply eqty_lconv; [|apply lequiv_sym, H24].
    eapply eqty_trans.
    + apply (wf_ty_func HB (d' := lsingle s')). now apply lsub_eq_single.
    + exact (eqty_single Hi HBB Hs').
Qed.

Lemma pre_natrec_succ {Γ l M s z t} :
  lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] -> [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] ->
  [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] z[lsingle2 t (natrec l M s z t)] : M[lsingle (succ t)] @ l ].
Proof.
  intros Hl HM Hs Hz Ht. rewrite <- lsucc_single2_ty with (q := natrec l M s z t).
  eapply (wf_tm_subst Hi Hz). apply lsub_wf_single2; auto.
  - exact (ctx_of_wf_tm Hi Ht).
  - apply wf_natrec; auto.
Qed.

Lemma pre_eta_body {Γ l l' A B t} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0) : B @ l' ].
Proof.
  intros Hl Hl' HA HB Ht.
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HA1 : [ G ; Γ ,, A @ l ⊢[ i ] A⟨↑⟩ @ l ]) by (apply wk1_ty; auto).
  assert (HΓAA : [ G ; Γ ,, A @ l ,, A⟨↑⟩ @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  rewrite <- (liftshift_single_var_ty B) at 2 by exact (wf_ty_nf HB).
  apply wf_app; auto.
  - eapply weakening_r; eauto. apply wkr_up, wkr_shift1.
  - exact (wk1_tm G i Hi _ _ _ _ _ _ HΓA Ht).
  - now apply var0_wf.
Qed.

Lemma pre_eta_l {Γ l l' A B t} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] lam l l' A (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) : tyPi l l' A B @ lmax l l' ].
Proof. intros; apply wf_lam; auto using pre_eta_body. Qed.

End Aux.

#[export] Hint Resolve wft_nat wft_pi wft_U wft_El wf_code_nat wf_code_U wf_code_pi wf_zero
  wf_succ wf_natrec wf_lam wf_app wfc_ext in_ctx_wf wf_ty_single wf_tm_single
  ctx_of_wf_ty ctx_of_wf_tm ctx_of_eqty ctx_of_eqtm lequiv_wf_l lequiv_wf_r compt_notV : presup.
#[export] Hint Extern 1 (lwf _ _) =>
  solve [cbn; intuition eauto using lequiv_wf_l, lequiv_wf_r] : presup.
#[export] Hint Extern 1 =>
  match goal with Hi : typeof ?i = ?i |- context [typeof ?i] => rewrite Hi end : presup.

Theorem presupposition :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> True) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> typeof i = i ->
     [ G ; Γ ⊢[ i ] T @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> typeof i = i ->
     [ G ; Γ ⊢[ i ] T @ l ] /\ [ G ; Γ ⊢[ i ] T' @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> typeof i = i ->
     [ G ; Γ ⊢[ i ] t : T @ l ] /\ [ G ; Γ ⊢[ i ] t' : T @ l ] /\ [ G ; Γ ⊢[ i ] T @ l ]).
Proof.
  apply typing_mut; intros; try exact I;
    match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end;
    repeat match goal with IH : ?i = ?i -> _ |- _ => specialize (IH eq_refl) end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try match goal with c : compt ?i |- _ => pose proof (compt_notV _ c) end.
  all: repeat split.
  all: try solve [eauto 4 with presup].
  (* level and type conversions *)
  all: try solve [eapply wft_lconv; eassumption].
  all: try solve [eapply wf_lconv; eassumption].
  all: try solve [eapply conv_tm'; eassumption].
  (* right-hand sides of congruences *)
  all: first [ solve [eapply pre_pi_r; eassumption] | solve [eapply pre_U_r; eauto with presup]
             | solve [eapply pre_El_r; eassumption] | solve [eapply pre_codeU_r; eauto with presup]
             | solve [eapply pre_codepi_r; eassumption]
             | solve [eapply pre_natrec_r; eassumption]
             | solve [eapply pre_lam_r; eassumption] | solve [eapply pre_app_r; eassumption]
             | solve [eapply pre_natrec_succ; eassumption]
             | solve [eapply pre_eta_l; eassumption]
             | solve [eapply wf_natrec; eauto 4 with presup] ].
Qed.

Section Named.
Context {G : gctx} {i : layer} (Hi : typeof i = i).

Let P4 := proj1 (proj2 (proj2 (proj2 presupposition))).
Let P5 := proj1 (proj2 (proj2 (proj2 (proj2 presupposition)))).
Let P6 := proj2 (proj2 (proj2 (proj2 (proj2 presupposition)))).

Lemma wf_tm_ty {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] T @ l ].
Proof. intros H; exact (P4 _ _ _ _ _ _ H Hi). Qed.
Lemma eqty_wf_l {Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T @ l ].
Proof. intros H; exact (proj1 (P5 _ _ _ _ _ _ H Hi)). Qed.
Lemma eqty_wf_r {Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T' @ l ].
Proof. intros H; exact (proj2 (P5 _ _ _ _ _ _ H Hi)). Qed.
Lemma eqtm_wf_l {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t : T @ l ].
Proof. intros H; exact (proj1 (P6 _ _ _ _ _ _ _ H Hi)). Qed.
Lemma eqtm_wf_r {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t' : T @ l ].
Proof. intros H; exact (proj1 (proj2 (P6 _ _ _ _ _ _ _ H Hi))). Qed.
Lemma eqtm_wf_ty {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] T @ l ].
Proof. intros H; exact (proj2 (proj2 (P6 _ _ _ _ _ _ _ H Hi))). Qed.

End Named.
