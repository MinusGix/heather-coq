(** * Presupposition (syntactic validity, ch. 5)

    Every judgment's components are well formed: the type of a typed term,
    both sides of a type equality, both sides of a term equality (and its
    type).  For layers with [typeof i = i]. *)
From DeLaM.Typing Require Export MInst.

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
  constructor; [rewrite Hi; exact HΓ | apply lk_dnf_lsingle2; eauto using wf_tm_dnf
               | split; auto; intros n; cbn; f_equal; lia |].
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
  intros HΓ. constructor; [rewrite Hi; exact HΓ | apply lk_dnf_lsucc
                          | split; auto; intros n; cbn; f_equal; lia |].
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

(** ** Global variables *)

Lemma lle_D_i : lle lD i.
Proof. destruct i; cbn in Hi, Hv; try congruence; unfold lle; cbn; lia. Qed.

Lemma lsub_wf_prem {Γ Δ d} :
  [ G ; Γ ⊢[ i ] ] -> lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] d : Δ ].
Proof. intros HΓ Ht Hd He; constructor; [rewrite Hi; exact HΓ | intros n; apply dnfl_llk; exact Hd | exact Ht | exact He]. Qed.

Lemma pre_gvar_ty {Γ u Δ i' T l d} :
  [ G ; Γ ⊢[ i ] ] -> in_gctx (gΨ G) u (gdTm Δ i' T l) -> [ G ; Γ ⊢[ i ] d : Δ ] ->
  [ G ; Γ ⊢[ i ] T[d] @ l ].
Proof.
  intros HΓ Hin Hd. destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (_ & HT & _).
  exact (wf_ty_subst_g (lift_ty HT lle_D_i) Hd).
Qed.

Lemma pre_gvar_r {Γ u Δ i' T l d d'} :
  [ G ; Γ ⊢[ i ] ] -> in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i ->
  [ G ; Γ ⊢[ i ] d : Δ ] -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] gvar u d' : T[d] @ l ].
Proof.
  intros HΓ Hin Hi' Hd Ht' Hn' Hv' He.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (_ & HT & _).
  pose proof (lsub_wf_prem HΓ Ht' Hn' Hv') as Hd'.
  eapply conv_tm'.
  - eapply wf_gvar; [rewrite Hi; exact HΓ | exact Hin | exact Hi' | exact Ht' | exact Hn' | exact Hv'].
  - exact (proj1 (proj2 (proj2 functionality_all)) _ _ _ _ _ (lift_ty HT lle_D_i) _ _ _
             (conj Hd (conj Hd' He))).
Qed.

(** Defined globals (M9): as [gvar], their declaration at a definition. *)
Lemma pre_gdef_ty {Γ u Δ T l t d} :
  [ G ; Γ ⊢[ i ] ] -> in_gctx (gΨ G) u (gdDef Δ T l t) -> [ G ; Γ ⊢[ i ] d : Δ ] ->
  [ G ; Γ ⊢[ i ] T[d] @ l ].
Proof.
  intros HΓ Hin Hd. destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (_ & HT & _).
  exact (wf_ty_subst_g (lift_ty HT lle_D_i) Hd).
Qed.

Lemma pre_gdef_r {Γ u Δ T l t0 t' d d'} :
  [ G ; Γ ⊢[ i ] ] -> in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t' -> lle lC i ->
  [ G ; Γ ⊢[ i ] d : Δ ] -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Δ ⊢[ i ] t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] gdef u t' d' : T[d] @ l ].
Proof.
  intros HΓ Hin Hle Hi' Hd Ht' Hn' Hv' He Hb.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (_ & HT & _).
  pose proof (lsub_wf_prem HΓ Ht' Hn' Hv') as Hd'.
  eapply conv_tm'.
  - eapply wf_gdef; [rewrite Hi; exact HΓ | exact Hin | exact Hle | exact Hi' | exact Ht' | exact Hn' | exact Hv' | exact Hb].
  - exact (proj1 (proj2 (proj2 functionality_all)) _ _ _ _ _ (lift_ty HT lle_D_i) _ _ _
             (conj Hd (conj Hd' He))).
Qed.

(** ** Context conversion *)

Lemma ctx_conv_ext {Γ Γ' A A' l l'} :
  [ G ; Γ' ⊢[ i ] lshift 0 : Γ ] -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ' ,, A' @ l' ⊢[ i ] ] /\ [ G ; Γ' ,, A' @ l' ⊢[ i ] lshift 0 : Γ ,, A @ l ].
Proof.
  intros Hid HA HAA HA' Hl.
  assert (HΓ' : [ G ; Γ' ⊢[ i ] ]) by (rewrite <- Hi; exact (lsub_wf_ctx Hid)).
  pose proof (wf_ty_subst Hi HA' Hid) as HA'1. rewrite nf_id_ty in HA'1 by exact (wf_ty_nf HA').
  pose proof (eqty_subst Hi HAA Hid) as HAA1.
  rewrite !nf_id_ty in HAA1 by first [exact (wf_ty_nf HA) | exact (wf_ty_nf HA')].
  assert (HA'l : [ G ; Γ' ⊢[ i ] A' @ l' ]) by (eapply wft_lconv; [exact HA'1 | now apply lequiv_sym]).
  assert (HΓ'A : [ G ; Γ' ,, A' @ l' ⊢[ i ] ]) by (apply wfc_ext; eauto using lequiv_wf_r).
  split; [exact HΓ'A|].
  destruct (lsub_wf_tail Hid) as [Ht Hlen].
  assert (Hc : clen Γ = clen Γ') by (specialize (Hlen 0); cbn in Hlen; injection Hlen; lia).
  constructor; [rewrite Hi; exact HΓ'A | apply lk_dnf_lshift | split; [exact Ht|] |].
  - intros n; cbn; f_equal; lia.
  - intros n T k Hin. rewrite nf_id_ty by eauto using in_ctx_nf. cbn; rewrite Nat.add_0_r.
    inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst.
    + eapply wf_conv; [eapply wf_lconv; [apply var0_wf; auto | exact Hl]|].
      rewrite Hi. apply wk1_eqty; auto.
    + pose proof (lsub_wf_var Hid Hm) as Hv'. rewrite nf_id_ty in Hv' by eauto using in_ctx_nf.
      cbn in Hv'; rewrite Nat.add_0_r in Hv'.
      pose proof (wk1_tm G i Hi _ _ _ _ _ _ HΓ'A Hv') as X. cbn in X. rewrite Nat.add_1_r in X. exact X.
Qed.

(** ** Dependent pairs (M8). Their rules are gated to the computing layers,
    which are exactly the layers with [typeof i = i]. *)

Lemma compt_self : compt i.
Proof. destruct i; cbn in Hi, Hv; try congruence; unfold compt; auto. Qed.

(** The unit type (M8c), gated like Σ. *)
Lemma pre_unit_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tyUnit l' @ l ].
Proof.
  intros HΓ Hl. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_unit; rewrite ?Hi; eauto using lequiv_wf_r, compt_self.
Qed.

Lemma pre_triv_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tmTriv l' : tyUnit l @ l ].
Proof.
  intros HΓ Hl. eapply wf_lconv with (l' := l'); [|exact Hl].
  eapply conv_tm'; [apply wf_triv; rewrite ?Hi; eauto using lequiv_wf_r|].
  eapply eqty_lconv; [|apply lequiv_sym, Hl].
  apply eqty_unit; rewrite ?Hi; eauto using lequiv_sym.
Qed.

Lemma pre_El_unit {Γ l} :
  [ G ; Γ ⊢[ i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] tyEl l (tmUnit l) @ l ].
Proof. intros HΓ Hl. apply wft_El; auto. apply wf_code_unit; rewrite ?Hi; auto using compt_self. Qed.

Lemma pre_codeunit_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tmUnit l' : tyU l @ lsuc l ].
Proof.
  intros HΓ Hl. apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_unit; rewrite ?Hi; eauto using lequiv_wf_r, compt_self.
Qed.

(** Strict equality (M10a), gated like Σ. *)
Lemma pre_seq_r {Γ l l' A A' a' b'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tySEq l' A' a' b' @ l ].
Proof.
  intros Hl HAA HA' Ha Hb. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_seq; eauto using compt_self, lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Ha | apply eqty_sym, HAA] | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Hb | apply eqty_sym, HAA] | now apply lequiv_sym].
Qed.

Lemma pre_sempty_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tySEmpty l' @ l ].
Proof.
  intros HΓ Hl. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_sempty; rewrite ?Hi; eauto using lequiv_wf_r, compt_self.
Qed.

Lemma pre_srefl_r {Γ l l' A A' a a'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] srefl l' A' a' : tySEq l A a a @ l ].
Proof.
  intros Hl HA HAA HA' Haa Ha'. eapply conv_tm'.
  - eapply wf_lconv; [|exact Hl]. apply wf_srefl; eauto using compt_self, lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | now apply lequiv_sym].
    + eapply wf_lconv; [eapply conv_tm'; [exact Ha' | apply eqty_sym, HAA] | now apply lequiv_sym].
  - apply eqty_seq; auto using compt_self.
Qed.

Lemma pre_elimSEmpty_r {Γ l1 l2 l3 l4 M M' e'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] M ≅ M' @ l2 ] -> [ G ; Γ ⊢[ i ] M' @ l2 ] -> [ G ; Γ ⊢[ i ] e' : tySEmpty l1 @ l1 ] ->
  [ G ; Γ ⊢[ i ] elimSEmpty l3 l4 M' e' : M @ l2 ].
Proof.
  intros H13 H24 HMM HM' He. eapply conv_tm'; [|exact HMM].
  eapply wf_lconv; [|exact H24]. apply wf_elimSEmpty; eauto using compt_self, lequiv_wf_r.
  - eapply wft_lconv; [exact HM' | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact He|] | now apply lequiv_sym].
    apply eqty_sym, eqty_sempty; [exact compt_self | rewrite Hi; exact (ctx_of_wf_tm Hi He) | exact H13].
Qed.

Lemma pre_sig_r {Γ l1 l2 l3 l4 A A' B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tySig l3 l4 A' B' @ lmax l1 l2 ].
Proof.
  intros H13 H24 HA HA' HB.
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  eapply wft_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply wft_sig; try solve [eauto using lequiv_wf_r, compt_self].
  eapply wft_lconv; [|apply lequiv_sym; exact H24].
  eapply (stab_ty Hi HA H13); [apply ext_wf; eauto using lequiv_wf_r | exact HB].
Qed.

Lemma pre_codesig_r {Γ l1 l2 l3 l4 s s' t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSig l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof.
  intros H13 H24 Hs Hs' Ht. pose proof (ctx_of_wf_tm Hi Hs') as HΓ.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; auto).
  assert (Hs3 : [ G ; Γ ⊢[ i ] s' : tyU l3 @ lsuc l3 ]) by exact (conv_U Hs' H13).
  eapply wf_lconv with (l' := lsuc (lmax l3 l4)); [|apply lequiv_suc, lequiv_max; eassumption].
  eapply conv_tm'.
  - apply wf_code_sig; try solve [eauto using lequiv_wf_r, compt_self].
    apply (conv_U (l := l2)); [|exact H24].
    eapply (stab_tm Hi HEl H13); [|exact Ht].
    apply ext_wf; [apply wft_El; eauto using lequiv_wf_r | eauto using lequiv_wf_r].
  - eapply eqty_lconv; [|apply lequiv_suc, lequiv_max; apply lequiv_sym; eassumption].
    apply eqty_U; [exact Hv | now rewrite Hi | apply lequiv_max; eassumption].
Qed.

(** [B[a] ≅ B'[a']] from [B ≅ B'] and [a ≅ a']. *)
Lemma sig_fam_eq {Γ l1 l2 A B B' a a'} :
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] B[lsingle a] ≅ B'[lsingle a'] @ l2 ].
Proof.
  intros HB HBB Haa Ha Ha'. eapply eqty_trans.
  - apply (wf_ty_func HB (d' := lsingle a')). now apply lsub_eq_single.
  - exact (eqty_single Hi HBB Ha').
Qed.

(** The Σ congruences' common setup: the right family in its own context,
    and the Σ types equal. *)
Lemma sig_r_setup {Γ l1 l2 l3 l4 A A' B B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] A' @ l3 ] /\ [ G ; Γ ,, A' @ l3 ⊢[ i ] B' @ l4 ] /\
  [ G ; Γ ⊢[ i ] tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ lmax l3 l4 ].
Proof.
  intros H13 H24 HA HAA HA' HBB HB'.
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓ' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply ext_wf; eauto using lequiv_wf_r).
  refine (conj HA3 (conj _ _)).
  - eapply wft_lconv; [exact (stab_ty Hi HAA H13 HΓ' HB') | now apply lequiv_sym].
  - eapply eqty_lconv; [|apply lequiv_max; apply lequiv_sym; eassumption].
    apply eqty_sig; auto using compt_self.
Qed.

Lemma pre_pair_r {Γ l1 l2 l3 l4 A A' B B' a a' b'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] b' : B[lsingle a] @ l2 ] ->
  [ G ; Γ ⊢[ i ] tmPair l3 l4 A' B' a' b' : tySig l1 l2 A B @ lmax l1 l2 ].
Proof.
  intros H13 H24 HA HAA HA' HB HBB HB' Haa Ha Ha' Hb'.
  destruct (sig_r_setup H13 H24 HA HAA HA' HBB HB') as (HA3 & HB4 & HSig).
  eapply wf_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  eapply conv_tm'; [|exact HSig].
  apply wf_pair; eauto using lequiv_wf_r, compt_self.
  - eapply wf_lconv with (l' := l1); [|now apply lequiv_sym].
    eapply conv_tm'; [exact Ha'|]. now apply eqty_sym.
  - eapply wf_lconv with (l' := l2); [|now apply lequiv_sym].
    eapply conv_tm'; [exact Hb'|]. apply eqty_sym. exact (sig_fam_eq HB HBB Haa Ha Ha').
Qed.

Lemma pre_fst_r {Γ l1 l2 l3 l4 A A' B B' p'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmFst l3 l4 A' B' p' : A @ l1 ].
Proof.
  intros H13 H24 HA HAA HA' HBB HB' Hp'.
  destruct (sig_r_setup H13 H24 HA HAA HA' HBB HB') as (HA3 & HB4 & HSig).
  eapply wf_lconv with (l' := l3); [|exact H13].
  eapply (conv_tm' (T' := A')).
  - apply wf_fst; eauto using lequiv_wf_r, compt_self.
    eapply wf_lconv with (l' := lmax l1 l2); [|apply lequiv_max; apply lequiv_sym; eassumption].
    eapply conv_tm'; [exact Hp'|]. eapply eqty_lconv; [apply eqty_sym, HSig | now apply lequiv_max].
  - eapply eqty_lconv; [exact HAA | now apply lequiv_sym].
Qed.

Lemma pre_snd_r {Γ l1 l2 l3 l4 A A' B B' p p'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] p ≅ p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] p : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmSnd l3 l4 A' B' p' : B[lsingle (tmFst l1 l2 A B p)] @ l2 ].
Proof.
  intros H13 H24 HA HAA HA' HB HBB HB' Hpp Hp Hp'.
  destruct (sig_r_setup H13 H24 HA HAA HA' HBB HB') as (HA3 & HB4 & HSig).
  assert (Hf : [ G ; Γ ⊢[ i ] tmFst l1 l2 A B p ≅ tmFst l3 l4 A' B' p' : A @ l1 ])
    by (apply eqtm_fst; auto using compt_self).
  assert (Hf1 : [ G ; Γ ⊢[ i ] tmFst l1 l2 A B p : A @ l1 ])
    by (apply wf_fst; eauto using lequiv_wf_l, compt_self).
  pose proof (pre_fst_r H13 H24 HA HAA HA' HBB HB' Hp') as Hf2.
  eapply wf_lconv with (l' := l4); [|exact H24].
  eapply conv_tm'.
  - apply wf_snd; eauto using lequiv_wf_r, compt_self.
    eapply wf_lconv with (l' := lmax l1 l2); [|apply lequiv_max; apply lequiv_sym; eassumption].
    eapply conv_tm'; [exact Hp'|]. eapply eqty_lconv; [apply eqty_sym, HSig | now apply lequiv_max].
  - eapply eqty_lconv with (l' := l2); [exact (sig_fam_eq HB HBB Hf Hf1 Hf2) | now apply lequiv_sym].
Qed.

Lemma pre_snd_beta_l {Γ l l' A B a b} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] b : B[lsingle a] @ l' ] ->
  [ G ; Γ ⊢[ i ] tmSnd l l' A B (tmPair l l' A B a b) : B[lsingle a] @ l' ].
Proof.
  intros Hl Hl' HA HB Ha Hb.
  assert (Hp : [ G ; Γ ⊢[ i ] tmPair l l' A B a b : tySig l l' A B @ lmax l l' ])
    by (apply wf_pair; auto using compt_self).
  assert (Hf : [ G ; Γ ⊢[ i ] tmFst l l' A B (tmPair l l' A B a b) : A @ l ])
    by (apply wf_fst; auto using compt_self).
  eapply conv_tm'; [apply wf_snd; auto using compt_self|].
  apply (wf_ty_func HB (d' := lsingle (tmFst l l' A B (tmPair l l' A B a b)))).
  apply lsub_eq_single; auto. apply eqtm_sym, eqtm_fst_beta; auto using compt_self.
Qed.

Lemma pre_sig_eta_l {Γ l l' A B p} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] tmPair l l' A B (tmFst l l' A B p) (tmSnd l l' A B p) : tySig l l' A B @ lmax l l' ].
Proof.
  intros Hl Hl' HA HB Hp.
  apply wf_pair; auto using compt_self; [apply wf_fst | apply wf_snd]; auto using compt_self.
Qed.

Lemma pre_snd_ty {Γ l l' A B p} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] B[lsingle (tmFst l l' A B p)] @ l' ].
Proof. intros; eapply (wf_ty_single Hi); [eassumption | apply wf_fst; auto using compt_self]. Qed.

End Aux.

(** ** Contextual types and letbox (layer M) *)

Lemma lM_notV : lM <> lV.
Proof. discriminate. Qed.

Lemma ctx_of_ext {G i Γ A l} : [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] ].
Proof. inversion 1; auto. Qed.

Lemma pre_CTrm_r {G Γ Δ Δ' T' l l'} :
  [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] lshift 0 : Δ ] ->
  [ G ; Δ ⊢[ lD ] T' @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ lM ] tyCTrm Δ' T' l' @ lzero ].
Proof.
  intros HΓ HΔ' Hid HT' Hl. apply wft_CTrm; eauto using lequiv_wf_r.
  pose proof (wf_ty_subst (i := lD) eq_refl HT' Hid) as X. rewrite nf_id_ty in X by exact (wf_ty_nf HT').
  eapply wft_lconv; [exact X | now apply lequiv_sym].
Qed.

Lemma pre_letbox_ty {G Γ l1 l2 A M M' t t0} :
  [ G ; Γ ,, A @ l2 ⊢[ lM ] M ≅ M' @ l1 ] -> [ G ; Γ ,, A @ l2 ⊢[ lM ] M' @ l1 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : A @ l2 ] -> [ G ; Γ ⊢[ lM ] t : A @ l2 ] -> [ G ; Γ ⊢[ lM ] t0 : A @ l2 ] ->
  [ G ; Γ ⊢[ lM ] M[lsingle t] ≅ M'[lsingle t0] @ l1 ].
Proof.
  intros HMM HM' Htt Ht Ht0. eapply eqty_trans.
  - exact (eqty_single (i := lM) eq_refl HMM Ht).
  - apply (wf_ty_func (i := lM) eq_refl HM' (d' := lsingle t0)).
    now apply (lsub_eq_single (i := lM) eq_refl).
Qed.

Lemma pre_letboxT_r {G Γ l1 l2 l3 l4 Δ Δ' M M' t2 t t0} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
  [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M' @ l1 ] ->
  [ G ; Γ ,, tyCTyp Δ' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
  [ gext G (gdTy Δ' lC l4) ; Γ⟪S⟫ ⊢[ lM ] t2 : M'⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l3 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTyp Δ l2 @ lzero ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l2 @ lzero ] -> [ G ; Γ ⊢[ lM ] t0 : tyCTyp Δ l2 @ lzero ] ->
  [ G ; Γ ⊢[ lM ] letboxT l3 l4 Δ' M' t2 t0 : M[lsingle t] @ l1 ].
Proof.
  intros H13 H24 HΔ' Hc HMM HM' HM'3 Ht2 Htt Ht Ht0.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ' l4 @ lzero ]) by (apply eqty_CTyp; auto).
  eapply wf_lconv with (l' := l3); [|exact H13].
  eapply (conv_tm' (i := lM) eq_refl (T' := M'[lsingle t0])).
  - apply wf_letboxT; eauto using lequiv_wf_r.
    eapply (conv_tm' (i := lM) eq_refl); [exact Ht0 | now apply eqty_sym].
  - eapply eqty_lconv; [exact (pre_letbox_ty HMM HM' Htt Ht Ht0) | now apply lequiv_sym].
Qed.

Lemma pre_letboxt_r {G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t2 t t0} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢[ lD ] T @ l2 ] -> [ G ; Δ' ⊢[ lD ] T' @ l4 ] ->
  [ G ; Δ ⊢[ lD ] T ≅ T' @ l2 ] ->
  [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
  [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M' @ l1 ] ->
  [ G ; Γ ,, tyCTrm Δ' T' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
  [ gext G (gdTm Δ' lC T' l4) ; Γ⟪S⟫ ⊢[ lM ] t2 : M'⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l3 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTrm Δ T l2 @ lzero ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l2 @ lzero ] -> [ G ; Γ ⊢[ lM ] t0 : tyCTrm Δ T l2 @ lzero ] ->
  [ G ; Γ ⊢[ lM ] letboxt l3 l4 Δ' T' M' t2 t0 : M[lsingle t] @ l1 ].
Proof.
  intros H13 H24 HΔ HΔ' Hc HT HT' HTT HMM HM' HM'3 Ht2 Htt Ht Ht0.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ' T' l4 @ lzero ]) by (apply eqty_CTrm; auto).
  eapply wf_lconv with (l' := l3); [|exact H13].
  eapply (conv_tm' (i := lM) eq_refl (T' := M'[lsingle t0])).
  - apply wf_letboxt; eauto using lequiv_wf_r.
    eapply (conv_tm' (i := lM) eq_refl); [exact Ht0 | now apply eqty_sym].
  - eapply eqty_lconv; [exact (pre_letbox_ty HMM HM' Htt Ht Ht0) | now apply lequiv_sym].
Qed.

(** letbox β: the contractum is typed by the global substitution lemma. *)
Lemma pre_letbox_beta_r {G Γ D o t' M b b' l'} :
  [ G ; Γ ⊢[ lM ] ] -> dnfo o -> gobj_wf G o (gdecl_gsubst (gdecl_ren D S) (gsingle o)) ->
  b⦃gsingle o⦄ = b' -> dnfty M ->
  [ gext G D ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle b] @ l' ] ->
  [ G ; Γ ⊢[ lM ] t'⦃gsingle o⦄ : M[lsingle b'] @ l' ].
Proof.
  intros HΓ Ho Hwf Hb HM Ht'.
  pose proof (gsub_wf_single G D o (ctx_glob _ _ _ HΓ) Ho Hwf) as Hσ.
  pose proof (proj1 (proj2 (proj2 (proj2 gsubstitution))) _ _ _ _ _ _ Ht' (gΨ G) _ Hσ) as X.
  unfold gwk_to in X; cbn in X.
  rewrite (gsubst_gren_ctx _ _ _ (fun j => GId j)), gsubst_id_ctx in X
    by first [reflexivity | exact (wf_ctx_dnf HΓ) | auto].
  rewrite gs_single_ty, Hb, (gsubst_gren_ty _ _ _ (fun j => GId j)), gsubst_id_ty in X
    by first [reflexivity | auto].
  exact X.
Qed.

Lemma pre_letboxT_beta_r {G Γ l' l Δ M t' T} :
  [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] T @ l ] ->
  [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] ->
  [ G ; Γ ⊢[ lM ] t'⦃gsingle (GTy T)⦄ : M[lsingle (boxT T)] @ l' ].
Proof.
  intros HM HΔ HT Ht'.
  eapply pre_letbox_beta_r; [ | | | | exact (wf_ty_dnf HM) | exact Ht'].
  - exact (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)).
  - exact (wf_ty_dnf HT).
  - rewrite gdecl_gsubst_ren_single by exact (wf_ctx_dnf HΔ). exact HT.
  - cbn. change (subst_ty T (glsubst (lshift 0) (gsingle (GTy T)))) with T[lshift 0].
    now rewrite nf_id_ty by exact (wf_ty_nf HT).
Qed.

Lemma pre_letboxt_beta_r {G Γ l' l Δ T M t' t} :
  [ G ; Γ ,, tyCTrm Δ T l @ lzero ⊢[ lM ] M @ l' ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] ->
  [ G ; Δ ⊢[ lC ] t : T @ l ] ->
  [ gext G (gdTm Δ lC T l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] ->
  [ G ; Γ ⊢[ lM ] t'⦃gsingle (GTm t)⦄ : M[lsingle (boxt t)] @ l' ].
Proof.
  intros HM HΔ HT Ht Ht'.
  eapply pre_letbox_beta_r; [ | | | | exact (wf_ty_dnf HM) | exact Ht'].
  - exact (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)).
  - exact (wf_tm_dnf Ht).
  - rewrite gdecl_gsubst_ren_single by (cbn; split; [exact (wf_ctx_dnf HΔ) | exact (wf_ty_dnf HT)]).
    exact Ht.
  - cbn. change (subst_tm t (glsubst (lshift 0) (gsingle (GTm t)))) with t[lshift 0].
    now rewrite nf_id by exact (wf_tm_nf Ht).
Qed.

Lemma typeof_self_notV i : typeof i = i -> i <> lV.
Proof. destruct i; cbn; congruence. Qed.

Lemma ctx_of_tm_M {G Γ t T l} : [ G ; Γ ⊢[ lM ] t : T @ l ] -> [ G ; Γ ⊢[ lM ] ].
Proof. exact (ctx_of_wf_tm (i := lM) eq_refl). Qed.
Lemma ctx_of_ty_M {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] ].
Proof. exact (ctx_of_wf_ty (i := lM) eq_refl). Qed.
Lemma ctx_of_eqtm_M {G Γ t t' T l} : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ lM ] ].
Proof. exact (ctx_of_eqtm (i := lM) eq_refl). Qed.

(** ** The recursors (layer M): the congruences' right-hand sides, typed at
    their own data and converted along the instance equation (E10). *)

Lemma pre_elimT_r {G Γ l1 l2 l1' l2' MT MT' Mt' bs' l l' Δ Δ' t t'} :
  [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t ≅ motT (wrapMT MT') l' Δ' t' @ l1 ] ->
  [ G ; Γ ⊢[ lM ] motT (wrapMT MT') l' Δ' t' @ l1 ] ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> lequiv (gL G) l l' ->
  [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                         bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]) ->
  [ G ; Γ ⊢[ lM ] t' : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' t' : motT (wrapMT MT) l Δ t @ l1 ].
Proof.
  intros HM HM' H1 H2 H3 HΔ' HΔΔ HMT' HMt' Hc Hb Ht'.
  eapply wf_conv; [| exact HM]. eapply wf_lconv; [| exact H1].
  apply wf_elimT; eauto using lequiv_wf_r.
  - eapply wft_lconv; [exact HM' | now apply lequiv_sym].
  - eapply wf_conv; [exact Ht' |]. apply eqty_sym, eqty_CTyp; [exact (ctx_of_tm_M Ht') | exact HΔΔ | exact H3].
Qed.

Lemma pre_elimt_r {G Γ l1 l2 l1' l2' MT' Mt Mt' bs' l l' Δ Δ' T T' t t'} :
  [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t ≅ mott (wrapMt Mt') l' Δ' T' t' @ l2 ] ->
  [ G ; Γ ⊢[ lM ] mott (wrapMt Mt') l' Δ' T' t' @ l2 ] ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ' ⊢[ lD ] T' @ l' ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                         bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]) ->
  [ G ; Γ ⊢[ lM ] t' : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' t' : mott (wrapMt Mt) l Δ T t @ l2 ].
Proof.
  intros HM HM' H1 H2 H3 HΔ HΔ' HΔΔ HT HT' HTT HMT' HMt' Hc Hb Ht'.
  eapply wf_conv; [| exact HM]. eapply wf_lconv; [| exact H2].
  apply wf_elimt; eauto using lequiv_wf_r.
  - eapply wft_lconv; [exact HM' | now apply lequiv_sym].
  - eapply wf_conv; [exact Ht' |]. apply eqty_sym, eqty_CTrm; [exact (ctx_of_tm_M Ht') | assumption ..].
Qed.

Lemma ctx_conv_ext1 {G i} (Hi : typeof i = i) {Γ Γ' A A' l l'} :
  [ G ; Γ' ⊢[ i ] lshift 0 : Γ ] -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l l' -> [ G ; Γ' ,, A' @ l' ⊢[ i ] ].
Proof. intros H1 H2 H3 H4 H5; exact (proj1 (ctx_conv_ext Hi H1 H2 H3 H4 H5)). Qed.
Lemma ctx_conv_ext2 {G i} (Hi : typeof i = i) {Γ Γ' A A' l l'} :
  [ G ; Γ' ⊢[ i ] lshift 0 : Γ ] -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l l' -> [ G ; Γ' ,, A' @ l' ⊢[ i ] lshift 0 : Γ ,, A @ l ].
Proof. intros H1 H2 H3 H4 H5; exact (proj2 (ctx_conv_ext Hi H1 H2 H3 H4 H5)). Qed.

#[export] Hint Resolve wft_nat wft_pi wft_U wft_El wf_code_nat wf_code_U wf_code_pi wf_zero
  wf_succ wf_natrec wf_lam wf_app wfc_ext in_ctx_wf wf_ty_single wf_tm_single
  wft_sig wf_code_sig wf_pair wf_fst wf_snd wft_seq wf_srefl wf_elimSEmpty
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
     [ G ; Γ ⊢[ i ] t : T @ l ] /\ [ G ; Γ ⊢[ i ] t' : T @ l ] /\ [ G ; Γ ⊢[ i ] T @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> typeof i = i ->
     [ G ; Γ ⊢[ i ] ] /\ [ G ; Γ' ⊢[ i ] ] /\ [ G ; Γ' ⊢[ i ] lshift 0 : Γ ]).
Proof.
  apply typing_mut; intros; try exact I;
    match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end;
    repeat match goal with IH : ?i = ?i -> _ |- _ => specialize (IH eq_refl) end;
    repeat match goal with IH : typeof ?j = ?j -> _ |- _ => specialize (IH eq_refl) end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try match goal with c : compt ?i |- _ => pose proof (compt_notV _ c) end.
  all: repeat match goal with |- _ /\ _ => split end.
  all: try solve [eauto 4 with presup].
  (* level and type conversions *)
  all: try solve [eapply wft_lconv; eassumption].
  all: try solve [eapply wf_lconv; eassumption].
  all: try solve [eapply conv_tm'; eassumption].
  (* contexts *)
  all: try solve [apply wfc_nil; auto | apply wfc_var; auto].
  all: try solve [eapply lsub_wf_id; eauto using wfc_nil, wfc_var].
  all: try solve [eapply ext_wf; eauto].
  all: try solve [match goal with
                  | Hid : lsub_wf _ _ ?Γ' _ ?Γ, HAA : eq_ty _ _ ?Γ ?A ?A' ?l, HA : wf_ty _ _ ?Γ ?A ?l,
                    HA' : wf_ty _ _ ?Γ ?A' ?l, Hl : lequiv _ ?l ?l', Hi : typeof ?i = ?i
                    |- _ => first [exact (ctx_conv_ext1 Hi Hid HA HAA HA' Hl)
                                 | exact (ctx_conv_ext2 Hi Hid HA HAA HA' Hl)]
                  end].
  (* global variables *)
  all: try solve [first [eapply wft_gvar | eapply wf_gvar | eapply wf_gdef]; eauto;
                  match goal with Hi : typeof ?i = ?i |- _ => rewrite Hi end; eauto].
  all: try solve [eapply pre_gvar_ty; eauto using typeof_self_notV;
                  eapply lsub_wf_prem; eauto using typeof_self_notV].
  all: try solve [eapply pre_gdef_ty; eauto using typeof_self_notV;
                  eapply lsub_wf_prem; eauto using typeof_self_notV].
  all: try solve [eapply pre_gvar_r; eauto using typeof_self_notV, lsub_wf_prem].
  (* defined globals (M9): the other instance, and δ's reduct *)
  all: try solve [eapply pre_gdef_r; eauto using typeof_self_notV, lsub_wf_prem].
  all: try solve [eapply wf_gdef; eauto using compt_lle_C;
                  match goal with Hi : typeof ?i = ?i |- _ => rewrite Hi end; eauto].
  all: try solve [eapply wf_tm_subst_g; [eassumption | eapply lsub_wf_prem; eauto using typeof_self_notV]].
  (* contextual types, box, letbox *)
  all: try solve [eapply wft_CTyp; eauto using lequiv_wf_l, lequiv_wf_r, ctx_of_tm_M, ctx_of_eqtm_M].
  all: try solve [eapply wft_CTrm; eauto using lequiv_wf_l, lequiv_wf_r, ctx_of_tm_M, ctx_of_eqtm_M].
  all: try solve [eapply pre_CTrm_r; eauto].
  all: try solve [eapply (wf_ty_single (i := lM) eq_refl); [eassumption|];
                  first [eapply wf_boxT | eapply wf_boxt]; eauto using ctx_of_ext, ctx_of_ty_M].
  all: try solve [first [eapply wf_boxT | eapply wf_boxt]; eauto].
  all: try solve [first [eapply wf_letboxT | eapply wf_letboxt]; eauto using lequiv_wf_l, lequiv_wf_r;
                  first [eapply wf_boxT | eapply wf_boxt]; eauto using ctx_of_ext, ctx_of_ty_M].
  all: try solve [eapply pre_letboxT_r; eauto].
  all: try solve [match goal with |- wf_tm _ _ _ (letboxt _ _ ?D' ?T' _ _ _) _ _ =>
                    match goal with Hc : eq_ctx _ _ ?D ?D', HTT : eq_ty _ _ ?D ?T ?T' _ |- _ =>
                      eapply (pre_letboxt_r (Δ := D) (T := T)); eauto end end].
  all: try solve [eapply pre_letboxT_beta_r; eauto].
  all: try solve [eapply pre_letboxt_beta_r; eauto].
  (* the recursors *)
  all: try solve [first [eapply wf_elimT | eapply wf_elimt]; eauto using lequiv_wf_l;
                  (* the branches, from the branch equations *)
                  intros ?k ?Hk; match goal with IH : forall k, k < nbr -> _ = _ -> _ /\ _ |- _ =>
                    exact (proj1 (IH k Hk eq_refl)) end].
  all: try solve [first [eapply pre_elimT_r | eapply pre_elimt_r]; eassumption].
  (* universe polymorphism (UInst) *)
  all: try solve [first [ solve [eapply wft_upi; eauto using lequiv_wf_l]
                        | solve [eapply pre_upi_r; eauto] | solve [eapply pre_ulam_r; eauto]
                        | solve [eapply wf_ulam; eauto using lequiv_wf_l]
                        | solve [eapply wf_uapp; eauto using lequivs_lwf_l] | solve [eapply pre_uapp_r; eauto]
                        | solve [eapply pre_ubeta_l; eauto] | solve [eapply pre_ubeta_r; eauto]
                        | solve [eapply pre_ueta_l; eauto] ]].
  all: try solve [eapply pre_uapp_l; eauto using lequivs_lwf_l; eapply wf_ulam; eassumption].
  (* meta-functions (MInst) *)
  all: try solve [first
         [ solve [eapply wft_cpi; eauto using lequiv_wf_l] | solve [eapply wft_tpi; eauto using lequiv_wf_l]
         | solve [eapply wf_clam; eauto using lequiv_wf_l] | solve [eapply wf_tlam; eauto using lequiv_wf_l]
         | solve [eapply wf_capp; eauto] | solve [eapply wf_tapp; eauto]
         | solve [eapply pre_cpi_r; eauto] | solve [eapply pre_tpi_r; eauto]
         | solve [eapply pre_clam_r; eauto] | solve [eapply pre_tlam_r; eauto]
         | solve [eapply pre_capp_r; eauto] | solve [eapply pre_tapp_r; eauto]
         | solve [eapply pre_cbeta_l; eauto] | solve [eapply pre_tbeta_l; eauto]
         | solve [eapply pre_ceta_l; eauto] | solve [eapply pre_teta_l; eauto]
         | solve [eapply inst_c_ty; eauto] | solve [eapply inst_c_tm; eauto]
         | solve [eapply inst_t_ty; eauto] | solve [eapply inst_t_tm; eauto] ]].
  (* right-hand sides of congruences *)
  all: first [ solve [eapply pre_pi_r; eassumption] | solve [eapply pre_U_r; eauto with presup]
             | solve [eapply pre_El_r; eassumption] | solve [eapply pre_codeU_r; eauto with presup]
             | solve [eapply pre_codepi_r; eassumption]
             | solve [eapply pre_natrec_r; eassumption]
             | solve [eapply pre_lam_r; eassumption] | solve [eapply pre_app_r; eassumption]
             | solve [eapply pre_natrec_succ; eassumption]
             | solve [eapply pre_eta_l; eassumption]
             | solve [eapply wf_natrec; eauto 4 with presup]
             (* dependent pairs (M8) *)
             | solve [eapply pre_sig_r; eassumption] | solve [eapply pre_codesig_r; eassumption]
             | solve [eapply pre_pair_r; eassumption] | solve [eapply pre_fst_r; eassumption]
             | solve [eapply pre_snd_r; eassumption] | solve [eapply pre_snd_beta_l; eassumption]
             | solve [eapply pre_sig_eta_l; eassumption] | solve [eapply pre_snd_ty; eassumption]
             | solve [eapply wf_ty_single; [eassumption|]; eapply wf_fst; eassumption]
             | solve [eapply wft_El; eauto with presup; eapply wf_code_sig; eassumption]
             (* the unit type (M8c) *)
             | solve [eapply pre_unit_r; eauto using lequiv_refl, lequiv_wf_l]
             | solve [eapply pre_El_unit; eassumption]
             | solve [eapply pre_codeunit_r; eauto using lequiv_refl, lequiv_wf_l]
             | solve [eapply pre_triv_r; eauto using lequiv_refl, lequiv_wf_l]
             (* strict equality (M10a) *)
             | solve [eapply pre_seq_r; eassumption]
             | solve [eapply pre_sempty_r; eauto using lequiv_refl, lequiv_wf_l]
             | solve [eapply pre_srefl_r; eassumption]
             | solve [eapply pre_elimSEmpty_r; eassumption] ].
Qed.

Section Named.
Context {G : gctx} {i : layer} (Hi : typeof i = i).

Let P4 := proj1 (proj2 (proj2 (proj2 presupposition))).
Let P5 := proj1 (proj2 (proj2 (proj2 (proj2 presupposition)))).
Let P6 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 presupposition))))).
Let P7 := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 presupposition))))).

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

Lemma eqctx_wf_l {Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G ; Γ ⊢[ i ] ].
Proof. intros H; exact (proj1 (P7 _ _ _ _ H Hi)). Qed.
Lemma eqctx_wf_r {Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G ; Γ' ⊢[ i ] ].
Proof. intros H; exact (proj1 (proj2 (P7 _ _ _ _ H Hi))). Qed.
(** Context conversion: the identity substitution between equivalent contexts. *)
Lemma eqctx_id {Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G ; Γ' ⊢[ i ] lshift 0 : Γ ].
Proof. intros H; exact (proj2 (proj2 (P7 _ _ _ _ H Hi))). Qed.

End Named.
