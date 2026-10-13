(** * Presupposition: the per-former lemmas

    The lemmas of [presupposition]'s cases that need only the local
    substitution metatheory ([Functionality]): split off [Presupposition]
    so that they build beside the global substitution lemmas instead of
    after them. The global variables' cases, which need [GSubstitution],
    stay in [Presupposition]. *)
From DeLaM.Typing Require Export Functionality.

(** ** Equations of the [elim_W] telescope (M13a) *)

Ltac rsimp := repeat first [ rewrite llk_r2l | rewrite llk_lcomp | rewrite llk_llift | rewrite llk_lren
                           | progress rlk_simpl | progress cbn [llk lsingle lsingle2 lsingle3] ].

Lemma W_E2 (B : ty) : (B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)] = B⟨↑⟩⟨↑⟩.
Proof.
  rewrite !ren_ren_comp_ty, (ren_as_r2l_ty B (rcomp ↑ ↑)). apply ren_subst_ty.
  intros [|n]; rewrite llk_r2l; rlk_simpl; cbn; [reflexivity | f_equal; lia].
Qed.

Lemma W_E3 (T : ty) : T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ = T⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩.
Proof. rewrite !ren_ren_comp_ty. apply ren_ext_ty; intros n; rlk_simpl; lia. Qed.

Lemma W_E8 (T : ty) : (T⟨↑⟩⟨rlift ↑⟩)[lsingle (var 0)] = T⟨↑⟩.
Proof.
  rewrite !ren_ren_comp_ty, (ren_as_r2l_ty T ↑). apply ren_subst_ty.
  intros n; rewrite llk_r2l; rlk_simpl; cbn; f_equal; lia.
Qed.

(** The children's type at a shape [a]. *)
Lemma W_shift2_llift_single (T : ty) a : (T⟨↑⟩⟨↑⟩)[llift (lsingle a)] = T⟨↑⟩.
Proof.
  rewrite ren_ren_comp_ty, (ren_subst_ty _ _ _ (lshift 1)).
  - symmetry; apply ren_as_subst_ty. intros n; cbn; f_equal; lia.
  - intros n; rlk_simpl; rewrite llk_llift; cbn. f_equal; lia.
Qed.

Lemma W_E5 l l' (A B : ty) a :
  (wfty l l' A B)[lsingle a] = tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩.
Proof. rewrite subst_tyPi, W_shift2_llift_single. reflexivity. Qed.

Lemma subst_comp_ty (T : ty) d1 d2 : T[d1][d2] = T[lcomp d1 d2].
Proof. apply subst_subst_ty; intros; apply llk_lcomp. Qed.
Lemma subst_comp (t : tm) d1 d2 : t[d1][d2] = t[lcomp d1 d2].
Proof. apply subst_subst; intros; apply llk_lcomp. Qed.

(** Pointwise comparison of substitutions built from the usual pieces. *)
Ltac pw := repeat first
  [ progress (rewrite ?llk_lcomp, ?llk_r2l, ?llk_llift, ?llk_lren)
  | progress rlk_simpl
  | progress cbn [llk lsingle lsingle2 lsingle3 ren_tm subst_tm rlk Nat.add]
  | progress push_ren | progress push_subst ];
  try reflexivity; try (f_equal; lia).

Lemma W_E4b (B : ty) a f : (B⟨↑⟩⟨↑⟩)[llift (lsingle2 a f)] = (B[lsingle a])⟨↑⟩.
Proof.
  rewrite ren_ren_comp_ty, (ren_subst_ty _ _ _ (lren (lsingle a) ↑)), (subst_ren_ty _ _ (lren (lsingle a) ↑));
    auto; intros [|n]; pw.
Qed.
Lemma W_E4c (T : ty) a f :
  (T⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[llift (llift (lsingle2 a f))] = T⟨↑⟩⟨rlift ↑⟩.
Proof.
  rewrite !ren_ren_comp_ty, (ren_subst_ty _ _ _ (r2l (rcomp ↑ (rlift ↑)))), <- ren_as_r2l_ty; auto.
  intros n; pw.
Qed.

Lemma W_E4 l l' l'' (A B M : ty) a f :
  (wihty l l' l'' A B M)[lsingle2 a f] =
  tyPi l' l'' B[lsingle a] M⟨rlift ↑⟩[lsingle (app f⟨↑⟩ l' (lmax l l') B[lsingle a]⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨rlift ↑⟩ (var 0))].
Proof.
  rewrite subst_tyPi. f_equal.
  - apply ren_subst_ty. intros [|n]; pw.
  - set (u0 := app f⟨↑⟩ l' (lmax l l') B[lsingle a]⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨rlift ↑⟩ (var 0)).
    set (u := app (var 1) l' (lmax l l') B⟨↑⟩⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 0)).
    assert (Eu : u[llift (lsingle2 a f)] = u0).
    { subst u u0. rewrite subst_app, subst_var, W_E4b, W_E4c. pw. }
    rewrite subst_comp_ty, !ren_ren_comp_ty.
    rewrite (ren_subst_ty M _ _ (lcons (lshift 1) u0)), (ren_subst_ty M (rlift ↑) _ (lcons (lshift 1) u0)); auto.
    all: intros [|n]; pw.
    rewrite <- Eu. reflexivity.
Qed.

(** The synthesized induction hypothesis's body and codomain, in
    [Γ, y : B[a/x]]: [wIH] is [λ^{l', l''}(B[a/x]). wbody], at
    [Π^{l', l''}(B[a/x]). wcod] ([W_E4]). *)
Notation wbody l l' l'' A B M c a f :=
  (tmElimW l l' l'' A⟨↑⟩ B⟨rlift ↑⟩ M⟨rlift ↑⟩ c⟨rlift (rlift (rlift ↑))⟩
     (app f⟨↑⟩ l' (lmax l l') B[lsingle a]⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨rlift ↑⟩ (var 0))).
Notation wcod l l' A B M a f :=
  (M⟨rlift ↑⟩[lsingle (app f⟨↑⟩ l' (lmax l l') B[lsingle a]⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨rlift ↑⟩ (var 0))]).

Lemma W_shift3_single3_ty (A : ty) a f h : nfty A -> (A⟨↑⟩⟨↑⟩⟨↑⟩)[lsingle3 a f h] = A.
Proof.
  intros NA. rewrite !ren_ren_comp_ty, (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; [exact NA | intros; cbn; f_equal; lia].
  - intros n; pw.
Qed.
Lemma W_lift3_llift3_ty (B : ty) a f h : nfty B -> (B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[llift (lsingle3 a f h)] = B.
Proof.
  intros NB. rewrite !ren_ren_comp_ty, (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; [exact NB | intros; cbn; f_equal; lia].
  - intros [|n]; pw.
Qed.

(** The step's type at [β]: the motive at the [sup]. *)
Lemma W_E6 l l' (A B M : ty) a f h : nfty A -> nfty B ->
  (wstepty l l' A B M)[lsingle3 a f h] = M[lsingle (tmSup l l' A B a f)].
Proof.
  intros NA NB.
  set (s := tmSup l l' A⟨↑⟩⟨↑⟩⟨↑⟩ B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1)).
  assert (Es : s[lsingle3 a f h] = tmSup l l' A B a f).
  { subst s. rewrite subst_sup, W_shift3_single3_ty, W_lift3_llift3_ty by assumption. pw. }
  rewrite subst_comp_ty, !ren_ren_comp_ty, (ren_subst_ty M _ _ (lsingle (tmSup l l' A B a f))); auto.
  intros [|n]; pw. first [exact Es | exact (eq_sym Es)].
Qed.

Lemma shift4_single0_ty (T : ty) : (T⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 0)] = T⟨↑⟩⟨↑⟩⟨↑⟩.
Proof.
  rewrite !ren_ren_comp_ty, (ren_as_r2l_ty T (rcomp ↑ (rcomp ↑ ↑))).
  apply ren_subst_ty. intros n; rewrite llk_r2l; rlk_simpl; cbn. f_equal. lia.
Qed.

Section Aux.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).

(** ** Context lookups are well formed *)

Lemma in_ctx_wf {Γ n T l} : [ G ; Γ ⊢[ i ] ] -> in_ctx Γ n T l -> [ G ; Γ ⊢[ i ] T @ l ].
Proof using Hi.
  intros HΓ Hin; induction Hin as [Γ A l|Γ A l B l' n Hin IH]; inversion HΓ; subst.
  - apply wk1_ty; auto.
  - apply wk1_ty; auto.
Qed.

(** ** Some typed substitutions *)

Lemma lsub_wf_single2 {Γ M t q l} :
  [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] q : M[lsingle t] @ l ] ->
  [ G ; Γ ⊢[ i ] lsingle2 t q : Γ ,, tyNat @ lzero ,, M @ l ].
Proof using Hi.
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
Proof using Hi Hv.
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

(** One local more, the last entry given by [f] (M12b: [case]'s branches
    see the motive at the injection of their variable). *)
Lemma lsub_wf_up1 {Γ A B f l l'} : [ G ; Γ ,, A @ l ⊢[ i ] ] -> dnftm f ->
  [ G ; Γ ,, A @ l ⊢[ i ] f : B⟨↑⟩ @ l' ] -> [ G ; Γ ,, A @ l ⊢[ i ] lcons (lshift 1) f : Γ ,, B @ l' ].
Proof using Hi.
  intros HΓ Hf Hft. constructor; [rewrite Hi; exact HΓ | intros [|n]; cbn; [exact Hf | exact I]
                                 | split; auto; intros n; cbn; f_equal; lia |].
  intros n T l0 Hin.
  inversion Hin as [Γ0 A0 l1|Γ0 A0 l1 T0 l2 m Hm]; subst; cbn.
  - rewrite shift_cons1_ty, <- shift1_as_ty. exact Hft.
  - rewrite shift_cons1_ty, <- shift1_as_ty. replace (m + 1) with (S m) by lia.
    apply wf_var; [now rewrite Hi | constructor; exact Hm].
Qed.

Lemma lsub_eq_up1 {Γ A B f f' l l'} : [ G ; Γ ,, A @ l ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] f : B⟨↑⟩ @ l' ] -> [ G ; Γ ,, A @ l ⊢[ i ] f' : B⟨↑⟩ @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] f ≅ f' : B⟨↑⟩ @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] lcons (lshift 1) f ≅ lcons (lshift 1) f' : Γ ,, B @ l' ].
Proof using Hi.
  intros HΓ Hf Hf' Hff.
  refine (conj (lsub_wf_up1 HΓ (wf_tm_dnf Hf) Hf) (conj (lsub_wf_up1 HΓ (wf_tm_dnf Hf') Hf') _)).
  intros n T l0 Hin.
  inversion Hin as [Γ0 A0 l1|Γ0 A0 l1 T0 l2 m Hm]; subst; cbn.
  - rewrite shift_cons1_ty, <- shift1_as_ty. exact Hff.
  - rewrite shift_cons1_ty, <- shift1_as_ty. replace (m + 1) with (S m) by lia.
    apply eqtm_refl, wf_var; [now rewrite Hi | constructor; exact Hm].
Qed.


Lemma lsub_eq_single {Γ A t t' l} :
  [ G ; Γ ⊢[ i ] t : A @ l ] -> [ G ; Γ ⊢[ i ] t' : A @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : A @ l ] ->
  [ G ; Γ ⊢[ i ] lsingle t ≅ lsingle t' : Γ ,, A @ l ].
Proof using Hi.
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
Proof using Hi. intros; eapply wf_conv; [eassumption | now rewrite Hi]. Qed.

Lemma conv_U {Γ t l l'} :
  [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] t : tyU l' @ lsuc l' ].
Proof using Hi Hv.
  intros Ht Hl. pose proof (ctx_of_wf_tm Hi Ht).
  eapply wf_lconv; [|apply lequiv_suc, lequiv_sym, Hl].
  eapply conv_tm'; [exact Ht|]. eapply eqty_lconv; [|apply lequiv_suc, Hl].
  apply eqty_U; [exact Hv | now rewrite Hi | now apply lequiv_sym].
Qed.

Lemma ext_wf {Γ A l} : [ G ; Γ ⊢[ i ] A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢[ i ] ].
Proof using Hi. intros; apply wfc_ext; auto; exact (ctx_of_wf_ty Hi ltac:(eassumption)). Qed.

(** ** Right-hand sides of congruences *)

Lemma pre_pi_r {Γ l1 l2 l3 l4 A A' B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyPi l3 l4 A' B' @ lmax l1 l2 ].
Proof using Hi Hv.
  intros H13 H24 HA HA' HB.
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  eapply wft_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply wft_pi; try solve [eauto using lequiv_wf_r].
  eapply wft_lconv; [|apply lequiv_sym; exact H24].
  eapply (stab_ty Hi HA H13); [apply ext_wf; eauto using lequiv_wf_r | exact HB].
Qed.

Lemma pre_El_r {Γ l l' t'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] t' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] tyEl l' t' @ l ].
Proof using Hi Hv.
  intros Hl Ht. eapply wft_lconv; [|exact Hl].
  apply wft_El; try solve [eauto using lequiv_wf_r]. now apply (conv_U Ht).
Qed.

Lemma pre_codeU_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ].
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi Hv.
  intros HΓ Hl. eapply wft_lconv with (l' := lsuc l'); [|now apply lequiv_suc].
  apply wft_U; eauto using lequiv_wf_r. now rewrite Hi.
Qed.

Lemma wf_ty_func {Γ T l Δ d d'} :
  [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T[d'] @ l ].
Proof using Hi. intros; eapply functionality; eauto. Qed.

(** The branch types of two [case]s, along equal motives and injections. *)
Lemma case_branch_eq {Γ X B M M' f f' lx lb k} : [ G ; Γ ,, X @ lx ⊢[ i ] ] ->
  [ G ; Γ ,, B @ lb ⊢[ i ] M @ k ] -> [ G ; Γ ,, B @ lb ⊢[ i ] M ≅ M' @ k ] ->
  [ G ; Γ ,, B @ lb ⊢[ i ] M' @ k ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] f : B⟨↑⟩ @ lb ] -> [ G ; Γ ,, X @ lx ⊢[ i ] f' : B⟨↑⟩ @ lb ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] f ≅ f' : B⟨↑⟩ @ lb ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] M⟨rlift ↑⟩[lsingle f] ≅ M'⟨rlift ↑⟩[lsingle f'] @ k ].
Proof using Hi.
  intros HΓ HM HMM HM' Hf Hf' Hff. rewrite !liftshift_single_ty.
  pose proof (lsub_eq_up1 HΓ Hf Hf' Hff) as E.
  eapply eqty_trans; [exact (eqty_subst Hi HMM (lsub_eq_l E)) | exact (wf_ty_func HM' E)].
Qed.

Lemma pre_natrec_r {Γ l l' M M' s' z' t t'} :
  lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M ≅ M' @ l ] -> [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' @ l ] ->
  [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] t' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] natrec l' M' s' z' t' : M[lsingle t] @ l ].
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi Hv. intros; apply wf_lam; auto using pre_eta_body. Qed.

(** ** Global variables *)

Lemma lle_D_i : lle lD i.
Proof using Hi Hv. destruct i; cbn in Hi, Hv; try congruence; unfold lle; cbn; lia. Qed.

Lemma lsub_wf_prem {Γ Δ d} :
  [ G ; Γ ⊢[ i ] ] -> lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] d : Δ ].
Proof using Hi. intros HΓ Ht Hd He; constructor; [rewrite Hi; exact HΓ | intros n; apply dnfl_llk; exact Hd | exact Ht | exact He]. Qed.

(** ** Context conversion *)

Lemma ctx_conv_ext {Γ Γ' A A' l l'} :
  [ G ; Γ' ⊢[ i ] lshift 0 : Γ ] -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ' ,, A' @ l' ⊢[ i ] ] /\ [ G ; Γ' ,, A' @ l' ⊢[ i ] lshift 0 : Γ ,, A @ l ].
Proof using Hi.
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
Proof using Hi Hv. destruct i; cbn in Hi, Hv; try congruence; unfold compt; auto. Qed.

(** The unit type (M8c), gated like Σ. *)
Lemma pre_unit_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tyUnit l' @ l ].
Proof using Hi Hv.
  intros HΓ Hl. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_unit; rewrite ?Hi; eauto using lequiv_wf_r, compt_self.
Qed.

Lemma pre_triv_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tmTriv l' : tyUnit l @ l ].
Proof using Hi Hv.
  intros HΓ Hl. eapply wf_lconv with (l' := l'); [|exact Hl].
  eapply conv_tm'; [apply wf_triv; rewrite ?Hi; eauto using lequiv_wf_r|].
  eapply eqty_lconv; [|apply lequiv_sym, Hl].
  apply eqty_unit; rewrite ?Hi; eauto using lequiv_sym.
Qed.

Lemma pre_El_unit {Γ l} :
  [ G ; Γ ⊢[ i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] tyEl l (tmUnit l) @ l ].
Proof using Hi Hv. intros HΓ Hl. apply wft_El; auto. apply wf_code_unit; rewrite ?Hi; auto using compt_self. Qed.

Lemma pre_codeunit_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tmUnit l' : tyU l @ lsuc l ].
Proof using Hi Hv.
  intros HΓ Hl. apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_unit; rewrite ?Hi; eauto using lequiv_wf_r, compt_self.
Qed.

(** Strict equality (M10a), gated like Σ. *)
Lemma pre_seq_r {Γ l l' A A' a' b'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tySEq l' A' a' b' @ l ].
Proof using Hi Hv.
  intros Hl HAA HA' Ha Hb. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_seq; eauto using compt_self, lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Ha | apply eqty_sym, HAA] | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Hb | apply eqty_sym, HAA] | now apply lequiv_sym].
Qed.

Lemma pre_sempty_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tySEmpty l' @ l ].
Proof using Hi Hv.
  intros HΓ Hl. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_sempty; rewrite ?Hi; eauto using lequiv_wf_r, compt_self.
Qed.

Lemma pre_srefl_r {Γ l l' A A' a a'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] srefl l' A' a' : tySEq l A a a @ l ].
Proof using Hi Hv.
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
Proof using Hi Hv.
  intros H13 H24 HMM HM' He. eapply conv_tm'; [|exact HMM].
  eapply wf_lconv; [|exact H24]. apply wf_elimSEmpty; eauto using compt_self, lequiv_wf_r.
  - eapply wft_lconv; [exact HM' | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact He|] | now apply lequiv_sym].
    apply eqty_sym, eqty_sempty; [exact Hv | rewrite Hi; exact (ctx_of_wf_tm Hi He) | exact H13].
Qed.

(** The identity type (M11a), gated like Σ. *)
Lemma pre_id_r {Γ l l' A A' a' b'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyId l' A' a' b' @ l ].
Proof using Hi Hv.
  intros Hl HAA HA' Ha Hb. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_id; eauto using Hv, lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Ha | apply eqty_sym, HAA] | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Hb | apply eqty_sym, HAA] | now apply lequiv_sym].
Qed.

Lemma pre_idrefl_r {Γ l l' A A' a a'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmRefl l' A' a' : tyId l A a a @ l ].
Proof using Hi Hv.
  intros Hl HA HAA HA' Haa Ha'. eapply conv_tm'.
  - eapply wf_lconv; [|exact Hl]. apply wf_idrefl; eauto using Hv, lequiv_wf_r.
    + eapply wft_lconv; [exact HA' | now apply lequiv_sym].
    + eapply wf_lconv; [eapply conv_tm'; [exact Ha' | apply eqty_sym, HAA] | now apply lequiv_sym].
  - apply eqty_id; auto using Hv.
Qed.

(** The identity type's code (M11b). *)
Lemma pre_codeid_r {Γ l l' s s' t' u'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmId l' s' t' u' : tyU l @ lsuc l ].
Proof using Hi Hv.
  intros Hl Hs Hs' Ht Hu.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l s ≅ tyEl l' s' @ l ]) by (apply eqty_El; auto).
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] x : tyEl l' s' @ l' ]).
  { intros x Hx. eapply wf_lconv with (l' := l); [|now apply lequiv_sym].
    eapply conv_tm'; [exact Hx | apply eqty_sym, HEl]. }
  apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_id; [exact Hv | eauto using lequiv_wf_r | exact (conv_U Hs' Hl) | apply F, Ht | apply F, Hu].
Qed.

(** The empty type (M12a), gated like [sEmpty]. *)
Lemma pre_empty_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tyEmpty l' @ l ].
Proof using Hi Hv.
  intros HΓ Hl. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_empty; rewrite ?Hi; eauto using lequiv_wf_r, Hv.
Qed.

(** Length-indexed tuples and finite indices (M14a). *)
Lemma pre_vec_r {Γ l l' A' n'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] tyVec l' A' n' @ l ].
Proof using Hv.
  intros Hl HA Hn. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_vec; eauto using lequiv_wf_r. eapply wft_lconv; [exact HA | now apply lequiv_sym].
Qed.

Lemma pre_vec_zero {Γ l A} : compt i -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ⊢[ i ] tyVec l A zero @ l ] /\ [ G ; Γ ⊢[ i ] tyUnit l @ l ].
Proof using Hi Hv.
  intros Hc Hl HA. pose proof (ctx_of_wf_ty Hi HA) as HΓ. split.
  - apply wft_vec; auto. apply wf_zero; [exact Hv | now rewrite Hi].
  - apply wft_unit; [exact Hv | now rewrite Hi | exact Hl].
Qed.

Lemma pre_vec_succ {Γ l A n} : compt i -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyVec l A (succ n) @ l ] /\ [ G ; Γ ⊢[ i ] tySig l l A (tyVec l A⟨↑⟩ n⟨↑⟩) @ l ].
Proof using Hi Hv.
  intros Hc Hl HA Hn. pose proof (ext_wf HA Hl) as HΓA. split.
  - apply wft_vec; auto. apply wf_succ; [exact Hv | exact Hn].
  - eapply wft_lconv; [|apply lequiv_sym, lmax_idem, Hl].
    apply wft_sig; auto. apply wft_vec; auto.
    + apply wk1_ty; auto.
    + exact (wk1_tm G i Hi _ _ _ _ _ _ HΓA Hn).
Qed.

Lemma pre_fin_zero {Γ} : compt i -> [ G ; Γ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] tyFin zero @ lzero ] /\ [ G ; Γ ⊢[ i ] tyEmpty lzero @ lzero ].
Proof using Hi Hv.
  intros Hc HΓ. split.
  - apply wft_fin; auto. apply wf_zero; [exact Hv | now rewrite Hi].
  - apply wft_empty; [exact Hv | now rewrite Hi | exact I].
Qed.

Lemma pre_fin_succ {Γ n} : compt i -> [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyFin (succ n) @ lzero ] /\
  [ G ; Γ ⊢[ i ] tySum lzero lzero (tyUnit lzero) (tyFin n) @ lzero ].
Proof using Hi Hv.
  intros Hc Hn. pose proof (ctx_of_wf_tm Hi Hn) as HΓ. split.
  - apply wft_fin; auto. apply wf_succ; [exact Hv | exact Hn].
  - eapply wft_lconv; [|apply lequiv_sym, lmax_idem; exact I].
    apply wft_sum; auto; try exact I.
    + apply wft_unit; [exact Hv | now rewrite Hi | exact I].
    + apply wft_fin; auto.
Qed.

Lemma pre_elimEmpty_r {Γ l1 l2 l3 l4 M M' t t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M @ l1 ] ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M ≅ M' @ l1 ] -> [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M' @ l1 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ i ] t : tyEmpty l2 @ l2 ] -> [ G ; Γ ⊢[ i ] t' : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ i ] elimEmpty l3 l4 M' t' : M[lsingle t] @ l1 ].
Proof using Hi Hv.
  intros H13 H24 HM HMM HM' Htt Ht Ht'.
  pose proof (ctx_of_wf_tm Hi Ht) as HΓ.
  assert (HE : [ G ; Γ ⊢[ i ] tyEmpty l2 ≅ tyEmpty l4 @ l2 ])
    by (apply eqty_empty; [exact Hv | rewrite Hi; exact HΓ | exact H24]).
  assert (HE4 : [ G ; Γ ⊢[ i ] tyEmpty l4 @ l4 ]) by (apply wft_empty; rewrite ?Hi; eauto using lequiv_wf_r, Hv).
  assert (HΓ4 : [ G ; Γ ,, tyEmpty l4 @ l4 ⊢[ i ] ]) by (apply ext_wf; eauto using lequiv_wf_r).
  assert (HM'4 : [ G ; Γ ,, tyEmpty l4 @ l4 ⊢[ i ] M' @ l3 ])
    by (eapply wft_lconv; [exact (stab_ty Hi HE H24 HΓ4 HM') | now apply lequiv_sym]).
  assert (Ht'4 : [ G ; Γ ⊢[ i ] t' : tyEmpty l4 @ l4 ])
    by (eapply wf_lconv; [eapply conv_tm'; [exact Ht' | apply eqty_sym, HE] | now apply lequiv_sym]).
  eapply wf_lconv with (l' := l3); [|exact H13].
  eapply (conv_tm' (T' := M'[lsingle t'])).
  - apply wf_elimEmpty; eauto using lequiv_wf_r, Hv.
  - eapply eqty_lconv; [|apply lequiv_sym, H13].
    eapply eqty_trans.
    + apply (wf_ty_func HM (d' := lsingle t')). now apply lsub_eq_single.
    + exact (eqty_single Hi HMM Ht').
Qed.

(** Binary sums (M12b), gated like [Empty]. *)
Lemma pre_sum_r {Γ l1 l2 l3 l4 A A' B B'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tySum l3 l4 A' B' @ lmax l1 l2 ].
Proof using Hv.
  intros H13 H24 HAA HA' HBB HB'. eapply wft_lconv with (l' := lmax l3 l4); [| apply lequiv_max; assumption].
  apply wft_sum; eauto using Hv, lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | now apply lequiv_sym].
  - eapply wft_lconv; [exact HB' | now apply lequiv_sym].
Qed.

(** The injections' right-hand sides: at the primed annotations, then
    converted to the left's sum type. *)
Lemma pre_inj_conv {Γ l1 l2 l3 l4 A A' B B' x} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] x : tySum l3 l4 A' B' @ lmax l3 l4 ] -> [ G ; Γ ⊢[ i ] x : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using Hi Hv.
  intros H13 H24 HAA HBB Hx. eapply wf_lconv with (l' := lmax l3 l4); [| apply lequiv_max; assumption].
  eapply conv_tm'; [exact Hx|]. eapply eqty_lconv; [apply eqty_sum; auto using Hv |].
  apply lequiv_sym, lequiv_max; assumption.
Qed.

Lemma pre_inl_r {Γ l1 l2 l3 l4 A A' B B' a'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmInl l3 l4 A' B' a' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using Hi Hv.
  intros H13 H24 HAA HA' HBB HB' Ha. apply (pre_inj_conv H13 H24 HAA HBB).
  apply wf_inl; eauto using Hv, lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | now apply lequiv_sym].
  - eapply wft_lconv; [exact HB' | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Ha | apply eqty_sym, HAA] | now apply lequiv_sym].
Qed.

Lemma pre_inr_r {Γ l1 l2 l3 l4 A A' B B' b'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] -> [ G ; Γ ⊢[ i ] b' : B @ l2 ] ->
  [ G ; Γ ⊢[ i ] tmInr l3 l4 A' B' b' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using Hi Hv.
  intros H13 H24 HAA HA' HBB HB' Hb. apply (pre_inj_conv H13 H24 HAA HBB).
  apply wf_inr; eauto using Hv, lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | now apply lequiv_sym].
  - eapply wft_lconv; [exact HB' | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Hb | apply eqty_sym, HBB] | now apply lequiv_sym].
Qed.

(** A [case] branch, moved to the primed carrier's context and the primed
    motive at the primed injection. [inj] is either injection. *)
(** β's right-hand side, at the motive's instance at the injection. *)
Lemma case_inl_single (M : ty) l l' A B a : nfty A -> nfty B ->
  M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))][lsingle a] = M[lsingle (tmInl l l' A B a)].
Proof using . intros NA NB. rewrite liftshift_single_ty, up1_single_ty, subst_inl, !shift_single_ty by assumption. reflexivity. Qed.
Lemma case_inr_single (M : ty) l l' A B b : nfty A -> nfty B ->
  M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))][lsingle b] = M[lsingle (tmInr l l' A B b)].
Proof using . intros NA NB. rewrite liftshift_single_ty, up1_single_ty, subst_inr, !shift_single_ty by assumption. reflexivity. Qed.

Lemma pre_case_inl_rhs {Γ l l' l'' A B M c1 a} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] c1 : M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] c1[lsingle a] : M[lsingle (tmInl l l' A B a)] @ l'' ].
Proof using Hi.
  intros HA HB Hc Ha. rewrite <- (case_inl_single M l l' A B a (wf_ty_nf HA) (wf_ty_nf HB)).
  exact (wf_tm_single Hi Hc Ha).
Qed.
Lemma pre_case_inr_rhs {Γ l l' l'' A B M c2 b} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, B @ l' ⊢[ i ] c2 : M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
  [ G ; Γ ⊢[ i ] b : B @ l' ] -> [ G ; Γ ⊢[ i ] c2[lsingle b] : M[lsingle (tmInr l l' A B b)] @ l'' ].
Proof using Hi.
  intros HA HB Hc Hb. rewrite <- (case_inr_single M l l' A B b (wf_ty_nf HA) (wf_ty_nf HB)).
  exact (wf_tm_single Hi Hc Hb).
Qed.

(** The codes of [Vec] and [Fin] (M14b). *)
Lemma pre_codevec_r {Γ l l' s' n'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmVec l' s' n' : tyU l @ lsuc l ].
Proof using Hi Hv.
  intros Hl Hs Hn. apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_vec; eauto using lequiv_wf_r. exact (conv_U Hs Hl).
Qed.

(** The code of [∥·∥] (M16b), as [Vec]'s. *)
Lemma pre_codesq_r {Γ l l' s'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] tmSqCode l' s' : tyU l @ lsuc l ].
Proof using Hi Hv.
  intros Hl Hs. apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_sq; eauto using lequiv_wf_r. exact (conv_U Hs Hl).
Qed.

(** The code of [Wf] (M15b), as [W]'s: the arity under the shape's binder. *)
Lemma pre_codewf_r {Γ l l' s s' n'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmWf l' s' n' : tyU l @ lsuc l ].
Proof using Hi Hv.
  intros Hl Hs Hs' Hn. pose proof (ctx_of_wf_tm Hi Hs') as HΓ.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l s ≅ tyEl l' s' @ l ]) by (apply eqty_El; auto).
  pose proof (conv_U Hs' Hl) as Hs3.
  apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_wf; [exact Hv | eauto using lequiv_wf_r | exact Hs3 |].
  eapply (stab_tm Hi HEl Hl); [|exact Hn].
  apply ext_wf; [apply wft_El; eauto using lequiv_wf_r | eauto using lequiv_wf_r].
Qed.

(** The codes of [Empty] and [+] (M12c). *)
Lemma pre_El_empty {Γ l} :
  [ G ; Γ ⊢[ i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] tyEl l (tmEmpty l) @ l ].
Proof using Hi Hv. intros HΓ Hl. apply wft_El; auto. apply wf_code_empty; rewrite ?Hi; auto using Hv. Qed.

Lemma pre_codeempty_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tmEmpty l' : tyU l @ lsuc l ].
Proof using Hi Hv.
  intros HΓ Hl. apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_empty; rewrite ?Hi; eauto using lequiv_wf_r, Hv.
Qed.

Lemma pre_codesum_r {Γ l1 l2 l3 l4 s' t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSum l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using Hi Hv.
  intros H13 H24 Hs' Ht'. pose proof (ctx_of_wf_tm Hi Hs') as HΓ.
  eapply wf_lconv with (l' := lsuc (lmax l3 l4)); [|apply lequiv_suc, lequiv_max; eassumption].
  eapply conv_tm'.
  - apply wf_code_sum; [exact Hv | eauto using lequiv_wf_r | eauto using lequiv_wf_r
                       | exact (conv_U Hs' H13) | exact (conv_U Ht' H24)].
  - eapply eqty_lconv; [|apply lequiv_suc, lequiv_max; apply lequiv_sym; eassumption].
    apply eqty_U; [exact Hv | now rewrite Hi | apply lequiv_max; eassumption].
Qed.

Lemma case_branch_r {Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' X X' lx lx' c}
  (inj : lvl -> lvl -> ty -> ty -> tm -> tm) :
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 -> lequiv (gL G) lx lx' ->
  [ G ; Γ ⊢[ i ] X @ lx ] -> [ G ; Γ ⊢[ i ] X ≅ X' @ lx ] -> [ G ; Γ ⊢[ i ] X' @ lx ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] ->
  (forall Y ly, [ G ; Γ ,, Y @ ly ⊢[ i ] ] -> [ G ; Γ ,, Y @ ly ⊢[ i ] var 0 : X⟨↑⟩ @ lx ] ->
     [ G ; Γ ,, Y @ ly ⊢[ i ] inj l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0) : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ] /\
     [ G ; Γ ,, Y @ ly ⊢[ i ] inj l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0) : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ] /\
     [ G ; Γ ,, Y @ ly ⊢[ i ] inj l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0) ≅ inj l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0)
         : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ]) ->
  [ G ; Γ ,, X @ lx ⊢[ i ] c : M⟨rlift ↑⟩[lsingle (inj l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ,, X' @ lx' ⊢[ i ] c : M'⟨rlift ↑⟩[lsingle (inj l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ l6 ].
Proof using Hi.
  intros H14 H25 H36 Hlx HX HXX HX' HM HMM HM' F Hc.
  assert (HX'l : [ G ; Γ ⊢[ i ] X' @ lx' ]) by (eapply wft_lconv; [exact HX' | now apply lequiv_sym]).
  assert (HΓX' : [ G ; Γ ,, X' @ lx' ⊢[ i ] ]) by (apply ext_wf; [exact HX'l | exact (lequiv_wf_r _ _ _ Hlx)]).
  pose proof (stab_tm Hi HXX Hlx HΓX' Hc) as Hc'.
  assert (Hv0 : [ G ; Γ ,, X' @ lx' ⊢[ i ] var 0 : X⟨↑⟩ @ lx ]).
  { eapply wf_lconv; [eapply conv_tm'; [apply var0_wf; [exact Hi | exact HΓX'] |] | exact Hlx].
    eapply eqty_lconv; [apply wk1_eqty; [exact Hi | exact HΓX' | exact HXX] | now apply lequiv_sym]. }
  destruct (F _ _ HΓX' Hv0) as (Hf & Hf' & Hff).
  pose proof (case_branch_eq HΓX' HM HMM HM' Hf Hf' Hff) as EB.
  eapply wf_lconv; [eapply conv_tm'; [exact Hc' | apply eqty_sym, EB] | exact (lequiv_sym _ _ _ H36)].
Qed.

Lemma pre_case_r {Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1' c2' t t'} :
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c1' : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ,, B @ l2 ⊢[ i ] c2' : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t : tySum l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] t' : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmCase l4 l5 l6 A' B' M' c1' c2' t' : M[lsingle t] @ l3 ].
Proof using Hi Hv.
  intros H14 H25 H36 HAA HA HA' HBB HB HB' HM HMM HM' Hc1 Hc2 Htt Ht Ht'.
  pose proof (ctx_of_wf_tm Hi Ht) as HΓ.
  pose proof (lequiv_wf_l _ _ _ H14) as W1. pose proof (lequiv_wf_l _ _ _ H25) as W2.
  pose proof (lequiv_wf_r _ _ _ H14) as W4. pose proof (lequiv_wf_r _ _ _ H25) as W5.
  assert (H45 : lequiv (gL G) (lmax l1 l2) (lmax l4 l5)) by (apply lequiv_max; assumption).
  assert (HA'4 : [ G ; Γ ⊢[ i ] A' @ l4 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HB'5 : [ G ; Γ ⊢[ i ] B' @ l5 ]) by (eapply wft_lconv; [exact HB' | now apply lequiv_sym]).
  assert (ESS : [ G ; Γ ⊢[ i ] tySum l1 l2 A B ≅ tySum l4 l5 A' B' @ lmax l1 l2 ])
    by (apply eqty_sum; auto using Hv).
  assert (HΓS' : [ G ; Γ ,, tySum l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] ])
    by (apply ext_wf; [apply wft_sum; auto using Hv | exact (conj W4 W5)]).
  assert (HM'6 : [ G ; Γ ,, tySum l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' @ l6 ])
    by (eapply wft_lconv; [exact (stab_ty Hi ESS H45 HΓS' HM') | now apply lequiv_sym]).
  (* the branches' injections, left and primed, at the left sum type *)
  assert (Finl : forall Y ly, [ G ; Γ ,, Y @ ly ⊢[ i ] ] -> [ G ; Γ ,, Y @ ly ⊢[ i ] var 0 : A⟨↑⟩ @ l1 ] ->
     [ G ; Γ ,, Y @ ly ⊢[ i ] tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0) : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ] /\
     [ G ; Γ ,, Y @ ly ⊢[ i ] tmInl l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0) : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ] /\
     [ G ; Γ ,, Y @ ly ⊢[ i ] tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0) ≅ tmInl l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0)
         : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ]).
  { intros Y ly HΓY Hv0. refine (conj _ (conj _ _)).
    - apply wf_inl; auto using Hv; apply wk1_ty; assumption.
    - apply pre_inl_r; auto; first [apply wk1_eqty | apply wk1_ty]; assumption.
    - apply eqtm_inl; auto using Hv; [apply wk1_eqty; assumption .. | apply eqtm_refl, Hv0]. }
  assert (Finr : forall Y ly, [ G ; Γ ,, Y @ ly ⊢[ i ] ] -> [ G ; Γ ,, Y @ ly ⊢[ i ] var 0 : B⟨↑⟩ @ l2 ] ->
     [ G ; Γ ,, Y @ ly ⊢[ i ] tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0) : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ] /\
     [ G ; Γ ,, Y @ ly ⊢[ i ] tmInr l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0) : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ] /\
     [ G ; Γ ,, Y @ ly ⊢[ i ] tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0) ≅ tmInr l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0)
         : (tySum l1 l2 A B)⟨↑⟩ @ lmax l1 l2 ]).
  { intros Y ly HΓY Hv0. refine (conj _ (conj _ _)).
    - apply wf_inr; auto using Hv; apply wk1_ty; assumption.
    - apply pre_inr_r; auto; first [apply wk1_eqty | apply wk1_ty]; assumption.
    - apply eqtm_inr; auto using Hv; [apply wk1_eqty; assumption .. | apply eqtm_refl, Hv0]. }
  eapply wf_lconv with (l' := l6); [| exact H36].
  eapply (conv_tm' (T' := M'[lsingle t'])).
  - apply wf_case; auto using Hv.
    + exact (lequiv_wf_r _ _ _ H36).
    + exact (case_branch_r tmInl H14 H25 H36 H14 HA HAA HA' HM HMM HM' Finl Hc1).
    + exact (case_branch_r tmInr H14 H25 H36 H25 HB HBB HB' HM HMM HM' Finr Hc2).
    + eapply wf_lconv; [eapply conv_tm'; [exact Ht' | apply eqty_sym, ESS] | now apply lequiv_sym].
  - eapply eqty_lconv; [|apply lequiv_sym, H36].
    eapply eqty_trans.
    + apply (wf_ty_func HM (d' := lsingle t')). now apply lsub_eq_single.
    + exact (eqty_single Hi HMM Ht').
Qed.


(** Propositional truncation (M16a; every layer but V since M16b). *)
Lemma pre_tySq_r {Γ l l' A'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] tySq l' A' @ l ].
Proof using Hv.
  intros Hl HA'. eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_sq; [exact Hv | exact (lequiv_wf_r _ _ _ Hl) |].
  eapply wft_lconv; [exact HA' | now apply lequiv_sym].
Qed.

Lemma pre_sq_r {Γ l l' A A' a'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] tmSq l' A' a' : tySq l A @ l ].
Proof using Hi Hv.
  intros Hl HAA HA HA' Ha.
  assert (HA'l : [ G ; Γ ⊢[ i ] A' @ l' ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (Ha' : [ G ; Γ ⊢[ i ] a' : A' @ l' ])
    by (eapply wf_lconv; [eapply conv_tm'; [exact Ha | apply eqty_sym, HAA] | now apply lequiv_sym]).
  assert (Hs : [ G ; Γ ⊢[ i ] tmSq l' A' a' : tySq l' A' @ l' ])
    by (apply wf_sq; [exact Hv | exact (lequiv_wf_r _ _ _ Hl) | exact HA'l | exact Ha']).
  eapply wf_lconv with (l' := l'); [|exact Hl].
  eapply conv_tm'; [exact Hs |].
  eapply eqty_lconv; [apply eqty_sq; [exact Hv | exact Hl | exact HA | exact HAA] | apply lequiv_sym, Hl].
Qed.

(** The step, moved to the primed carrier's context and the primed motive
    at the primed [squash], as [case_branch_r]. *)
Lemma sq_branch_r {Γ l1 l2 l3 l4 A A' M M' c} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M @ l2 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ] ->
  [ G ; Γ ,, A' @ l3 ⊢[ i ] c : tySq l4 M'⟨rlift ↑⟩[lsingle (tmSq l3 A'⟨↑⟩ (var 0))] @ l4 ].
Proof using Hi Hv.
  intros H13 H24 HA HAA HA' HM HMM HM' Hc.
  assert (HA'l : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply ext_wf; [exact HA'l | exact (lequiv_wf_r _ _ _ H13)]).
  pose proof (stab_tm Hi HAA H13 HΓA' Hc) as Hc'.
  assert (Hv0 : [ G ; Γ ,, A' @ l3 ⊢[ i ] var 0 : A⟨↑⟩ @ l1 ]).
  { eapply wf_lconv; [eapply conv_tm'; [apply var0_wf; [exact Hi | exact HΓA'] |] | exact H13].
    eapply eqty_lconv; [apply wk1_eqty; [exact Hi | exact HΓA' | exact HAA] | now apply lequiv_sym]. }
  assert (HwA : [ G ; Γ ,, A' @ l3 ⊢[ i ] A⟨↑⟩ @ l1 ]) by (apply wk1_ty; assumption).
  assert (HwA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] A'⟨↑⟩ @ l1 ]) by (apply wk1_ty; assumption).
  assert (HwAA : [ G ; Γ ,, A' @ l3 ⊢[ i ] A⟨↑⟩ ≅ A'⟨↑⟩ @ l1 ]) by (apply wk1_eqty; assumption).
  assert (Hf : [ G ; Γ ,, A' @ l3 ⊢[ i ] tmSq l1 A⟨↑⟩ (var 0) : (tySq l1 A)⟨↑⟩ @ l1 ])
    by (apply wf_sq; [exact Hv | exact (lequiv_wf_l _ _ _ H13) | exact HwA | exact Hv0]).
  assert (Hf' : [ G ; Γ ,, A' @ l3 ⊢[ i ] tmSq l3 A'⟨↑⟩ (var 0) : (tySq l1 A)⟨↑⟩ @ l1 ])
    by exact (pre_sq_r H13 HwAA HwA HwA' Hv0).
  assert (Hff : [ G ; Γ ,, A' @ l3 ⊢[ i ] tmSq l1 A⟨↑⟩ (var 0) ≅ tmSq l3 A'⟨↑⟩ (var 0) : (tySq l1 A)⟨↑⟩ @ l1 ])
    by (apply eqtm_sq; [exact Hv | exact H13 | exact HwA | exact HwAA | apply eqtm_refl, Hv0]).
  pose proof (case_branch_eq HΓA' HM HMM HM' Hf Hf' Hff) as EB.
  assert (HX : [ G ; Γ ,, A' @ l3 ⊢[ i ] M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ]).
  { rewrite liftshift_single_ty. exact (wf_ty_subst Hi HM (lsub_wf_up1 HΓA' (wf_tm_dnf Hf) Hf)). }
  eapply wf_lconv; [eapply conv_tm'; [exact Hc' |] | exact (lequiv_sym _ _ _ H24)].
  apply eqty_sym, eqty_sq; [exact Hv | exact H24 | exact HX | exact EB].
Qed.

Lemma pre_elimSq_r {Γ l1 l2 l3 l4 A A' M M' c' t t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M @ l2 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c' : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tySq l1 A @ l1 ] ->
  [ G ; Γ ⊢[ i ] t : tySq l1 A @ l1 ] -> [ G ; Γ ⊢[ i ] t' : tySq l1 A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmElimSq l3 l4 A' M' c' t' : tySq l2 M[lsingle t] @ l2 ].
Proof using Hi Hv.
  intros H13 H24 HAA HA HA' HM HMM HM' Hc Htt Ht Ht'.
  pose proof (lequiv_wf_r _ _ _ H13) as W3. pose proof (lequiv_wf_r _ _ _ H24) as W4.
  assert (HA'3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (ESS : [ G ; Γ ⊢[ i ] tySq l1 A ≅ tySq l3 A' @ l1 ])
    by (apply eqty_sq; [exact Hv | exact H13 | exact HA | exact HAA]).
  assert (HΓS' : [ G ; Γ ,, tySq l3 A' @ l3 ⊢[ i ] ])
    by (apply ext_wf; [apply wft_sq; [exact Hv | exact W3 | exact HA'3] | exact W3]).
  assert (HM'4 : [ G ; Γ ,, tySq l3 A' @ l3 ⊢[ i ] M' @ l4 ])
    by (eapply wft_lconv; [exact (stab_ty Hi ESS H13 HΓS' HM') | now apply lequiv_sym]).
  assert (HMt : [ G ; Γ ⊢[ i ] M[lsingle t] ≅ M'[lsingle t'] @ l2 ]).
  { eapply eqty_trans.
    - apply (wf_ty_func HM (d' := lsingle t')). now apply lsub_eq_single.
    - exact (eqty_single Hi HMM Ht'). }
  assert (HMs : [ G ; Γ ⊢[ i ] M[lsingle t] @ l2 ]) by exact (wf_ty_single Hi HM Ht).
  assert (Ht'3 : [ G ; Γ ⊢[ i ] t' : tySq l3 A' @ l3 ])
    by (eapply wf_lconv; [eapply conv_tm'; [exact Ht' | apply eqty_sym, ESS] | now apply lequiv_sym]).
  eapply wf_lconv with (l' := l4); [| exact H24].
  eapply (conv_tm' (T' := tySq l4 M'[lsingle t'])).
  - apply wf_elimSq; [exact Hv | exact W3 | exact W4 | exact HA'3 | exact HM'4
                     | exact (sq_branch_r H13 H24 HA HAA HA' HM HMM HM' Hc) | exact Ht'3].
  - eapply eqty_lconv; [|apply lequiv_sym, H24].
    apply eqty_sq; [exact Hv | exact H24 | exact HMs | exact HMt].
Qed.

(** β's right-hand side, at the motive's instance at the [squash]. *)
Lemma sq_single (M : ty) l A a : nfty A ->
  M⟨rlift ↑⟩[lsingle (tmSq l A⟨↑⟩ (var 0))][lsingle a] = M[lsingle (tmSq l A a)].
Proof using . intros NA. rewrite liftshift_single_ty, up1_single_ty, subst_sq, shift_single_ty by assumption. reflexivity. Qed.

Lemma pre_elimSq_sq_rhs {Γ l l' A M c a} : [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] c : tySq l' M⟨rlift ↑⟩[lsingle (tmSq l A⟨↑⟩ (var 0))] @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] c[lsingle a] : tySq l' M[lsingle (tmSq l A a)] @ l' ].
Proof using Hi.
  intros HA Hc Ha. rewrite <- (sq_single M l A a (wf_ty_nf HA)).
  exact (wf_tm_single Hi Hc Ha).
Qed.


(** Strict equality's codes (M10c). *)
Lemma pre_codeseq_r {Γ l l' s s' t' u'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmSEq l' s' t' u' : tyU l @ lsuc l ].
Proof using Hi Hv.
  intros Hl Hs Hs' Ht Hu.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l s ≅ tyEl l' s' @ l ]) by (apply eqty_El; auto).
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] x : tyEl l' s' @ l' ]).
  { intros x Hx. eapply wf_lconv with (l' := l); [|now apply lequiv_sym].
    eapply conv_tm'; [exact Hx | apply eqty_sym, HEl]. }
  apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_seq; [exact Hv | eauto using lequiv_wf_r | exact (conv_U Hs' Hl) | apply F, Ht | apply F, Hu].
Qed.

Lemma pre_El_sempty {Γ l} :
  [ G ; Γ ⊢[ i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] tyEl l (tmSEmpty l) @ l ].
Proof using Hi Hv. intros HΓ Hl. apply wft_El; auto. apply wf_code_sempty; rewrite ?Hi; auto using compt_self. Qed.

Lemma pre_codesempty_r {Γ l l'} :
  [ G ; Γ ⊢[ i ] ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] tmSEmpty l' : tyU l @ lsuc l ].
Proof using Hi Hv.
  intros HΓ Hl. apply (conv_U (l := l')); [|now apply lequiv_sym].
  apply wf_code_sempty; rewrite ?Hi; eauto using lequiv_wf_r, compt_self.
Qed.

(** Two single substitutions at once, for [J]'s motive. *)
Lemma lsub_wf_single2' {Γ A B t q l l'} :
  [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] t : A @ l ] -> [ G ; Γ ⊢[ i ] q : B[lsingle t] @ l' ] ->
  [ G ; Γ ⊢[ i ] lsingle2 t q : Γ ,, A @ l ,, B @ l' ].
Proof using Hi.
  intros HΓ Ht Hq.
  constructor; [rewrite Hi; exact HΓ | apply lk_dnf_lsingle2; eauto using wf_tm_dnf
               | split; auto; intros n; cbn; f_equal; lia |].
  intros n T l0 Hin.
  inversion Hin as [Γ0 A0 l1|Γ0 A0 l1 T0 l2 m Hm]; subst; cbn.
  - rewrite (ren_subst_ty _ _ _ (lsingle t)); [exact Hq|].
    intros k; rewrite rlk_shift1; reflexivity.
  - inversion Hm as [Γ1 A1 l3|Γ1 A1 l3 T1 l4 m' Hm']; subst; cbn.
    + rewrite shift2_single2_ty by exact (wf_tm_nf_ty Ht). exact Ht.
    + rewrite shift2_single2_ty by eauto using in_ctx_nf. rewrite Nat.add_0_r.
      apply wf_var; [now rewrite Hi | exact Hm'].
Qed.

Lemma lsub_eq_single2 {Γ A B t t' q q' l l'} :
  [ G ; Γ ⊢[ i ] t : A @ l ] -> [ G ; Γ ⊢[ i ] t' : A @ l ] -> [ G ; Γ ⊢[ i ] t ≅ t' : A @ l ] ->
  [ G ; Γ ⊢[ i ] q : B[lsingle t] @ l' ] -> [ G ; Γ ⊢[ i ] q' : B[lsingle t'] @ l' ] ->
  [ G ; Γ ⊢[ i ] q ≅ q' : B[lsingle t] @ l' ] ->
  [ G ; Γ ⊢[ i ] lsingle2 t q ≅ lsingle2 t' q' : Γ ,, A @ l ,, B @ l' ].
Proof using Hi.
  intros Ht Ht' Htt Hq Hq' Hqq. pose proof (ctx_of_wf_tm Hi Ht) as HΓ.
  refine (conj (lsub_wf_single2' HΓ Ht Hq) (conj (lsub_wf_single2' HΓ Ht' Hq') _)).
  intros n T l0 Hin.
  inversion Hin as [Γ0 A0 l1|Γ0 A0 l1 T0 l2 m Hm]; subst; cbn.
  - rewrite (ren_subst_ty _ _ _ (lsingle t)); [exact Hqq|].
    intros k; rewrite rlk_shift1; reflexivity.
  - inversion Hm as [Γ1 A1 l3|Γ1 A1 l3 T1 l4 m' Hm']; subst; cbn.
    + rewrite shift2_single2_ty by exact (wf_tm_nf_ty Ht). exact Htt.
    + rewrite shift2_single2_ty by eauto using in_ctx_nf. rewrite Nat.add_0_r.
      apply eqtm_refl, wf_var; [now rewrite Hi | exact Hm'].
Qed.

(** [J]'s motive context entry, instantiated at the right endpoint. *)
Lemma Jty_single l A a u : nfty A -> nftm a ->
  (tyId l A⟨↑⟩ a⟨↑⟩ (var 0))[lsingle u] = tyId l A a u.
Proof using . intros HA Ha. rewrite subst_tyId, shift_single_ty, shift_single; auto. Qed.

Lemma lsub_wf_J {Γ l A a u e} :
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] u : A @ l ] -> [ G ; Γ ⊢[ i ] e : tyId l A a u @ l ] ->
  [ G ; Γ ⊢[ i ] lsingle2 u e : Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ].
Proof using Hi.
  intros Ha Hu He. apply lsub_wf_single2'; [exact (ctx_of_wf_tm Hi Hu) | exact Hu |].
  rewrite Jty_single by first [exact (wf_tm_nf_ty Ha) | exact (wf_tm_nf Ha)]. exact He.
Qed.

Lemma pre_J_ty {Γ l l' A a M u e} :
  [ G ; Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] u : A @ l ] -> [ G ; Γ ⊢[ i ] e : tyId l A a u @ l ] ->
  [ G ; Γ ⊢[ i ] M[lsingle2 u e] @ l' ].
Proof using Hi. intros HM Ha Hu He. eapply wf_ty_subst; [exact Hi | exact HM | exact (lsub_wf_J Ha Hu He)]. Qed.

Lemma lsub_eq_J {Γ l A a u u' e e'} : lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] u : A @ l ] -> [ G ; Γ ⊢[ i ] u' : A @ l ] -> [ G ; Γ ⊢[ i ] u ≅ u' : A @ l ] ->
  [ G ; Γ ⊢[ i ] e : tyId l A a u @ l ] -> [ G ; Γ ⊢[ i ] e' : tyId l A a u @ l ] ->
  [ G ; Γ ⊢[ i ] e ≅ e' : tyId l A a u @ l ] ->
  [ G ; Γ ⊢[ i ] lsingle2 u e ≅ lsingle2 u' e' : Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ].
Proof using Hi Hv.
  intros Hl HA Ha Hu Hu' Huu He He' Hee.
  assert (Hn : nfty A /\ nftm a) by (split; [exact (wf_tm_nf_ty Ha) | exact (wf_tm_nf Ha)]).
  apply lsub_eq_single2; auto; rewrite !Jty_single by tauto; auto.
  eapply conv_tm'; [exact He'|].
  apply eqty_id; [exact Hv | now apply lequiv_refl | exact HA | now apply eqty_refl
                 | now apply eqtm_refl | now apply eqtm_sym].
Qed.

Lemma pre_J_r {Γ l1 l2 l3 l4 A A' a a' M M' c' u u' e e'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  (* first: it fixes [A] and [a] for [eassumption] *)
  [ G ; Γ ,, A @ l1 ⊢[ i ] tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ] ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ] ->
  [ G ; Γ ⊢[ i ] u : A @ l1 ] -> [ G ; Γ ⊢[ i ] u ≅ u' : A @ l1 ] -> [ G ; Γ ⊢[ i ] u' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] e : tyId l1 A a u @ l1 ] -> [ G ; Γ ⊢[ i ] e ≅ e' : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ i ] e' : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmJ l3 l4 A' a' M' c' u' e' : M[lsingle2 u e] @ l2 ].
Proof using Hi Hv.
  intros H13 H24 HId HA HAA HA' Ha Haa Ha' HMM HM' Hc' Hu Huu Hu' He Hee He'.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (Hl1 : lwf (gL G) l1) by eauto using lequiv_wf_l.
  assert (Hl3 : lwf (gL G) l3) by eauto using lequiv_wf_r.
  assert (H31 : lequiv (gL G) l3 l1) by now apply lequiv_sym.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (Ha'A' : [ G ; Γ ⊢[ i ] a' : A' @ l1 ]) by (eapply conv_tm'; [exact Ha' | apply eqty_sym, HAA]).
  destruct (ctx_conv_ext (lsub_wf_id G i Hi Γ HΓ) HA HAA HA' H13) as [HΓA' Hid1].
  (* [Id'] in the old context, and [Id ≅ Id'] there *)
  assert (HAw : [ G ; Γ ,, A @ l1 ⊢[ i ] A⟨↑⟩ @ l1 ]) by (apply wk1_ty; auto).
  assert (HAAw : [ G ; Γ ,, A @ l1 ⊢[ i ] A⟨↑⟩ ≅ A'⟨↑⟩ @ l1 ]) by (apply wk1_eqty; auto).
  assert (Hv0 : [ G ; Γ ,, A @ l1 ⊢[ i ] var 0 : A⟨↑⟩ @ l1 ]) by (apply var0_wf; auto).
  assert (HId' : [ G ; Γ ,, A @ l1 ⊢[ i ] tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l1 ]).
  { eapply wft_lconv with (l' := l3); [|exact H13].
    apply wft_id; auto using Hv.
    - eapply wft_lconv; [apply wk1_ty; eauto | exact H31].
    - eapply wf_lconv; [apply wk1_tm with (T := A'); eauto | exact H31].
    - eapply wf_lconv; [eapply conv_tm'; [exact Hv0 | apply eqty_sym, HAAw] | exact H31]. }
  assert (HIdId' : [ G ; Γ ,, A @ l1 ⊢[ i ] tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) ≅ tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l1 ]).
  { apply eqty_id; auto using Hv.
    - apply wk1_eqtm with (T := A); auto.
    - apply eqtm_refl; exact Hv0. }
  destruct (ctx_conv_ext Hid1 HId HIdId' HId' H13) as [HΓ2 Hid2].
  (* the motive, in the new context *)
  assert (HM'2 : [ G ; Γ ,, A' @ l3 ,, tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3 ⊢[ i ] M' @ l4 ]).
  { pose proof (wf_ty_subst Hi HM' Hid2) as X. rewrite nf_id_ty in X by exact (wf_ty_nf HM').
    eapply wft_lconv; [exact X | now apply lequiv_sym]. }
  (* the [Id] premise, in the new context *)
  assert (HId'' : [ G ; Γ ,, A' @ l3 ⊢[ i ] tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3 ]).
  { assert (HA'3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | exact H31]).
    apply wft_id; auto using Hv.
    - apply wk1_ty; auto.
    - apply wk1_tm with (T := A'); auto. eapply wf_lconv; [exact Ha'A' | exact H31].
    - apply var0_wf; auto. }
  (* the two instances of the motive *)
  assert (Hr : [ G ; Γ ⊢[ i ] tmRefl l1 A a : tyId l1 A a a @ l1 ])
    by (apply wf_idrefl; auto using Hv).
  assert (Hr' : [ G ; Γ ⊢[ i ] tmRefl l3 A' a' : tyId l1 A a a @ l1 ])
    by exact (pre_idrefl_r H13 HA HAA HA' Haa Ha').
  assert (Hrr : [ G ; Γ ⊢[ i ] tmRefl l1 A a ≅ tmRefl l3 A' a' : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; auto using Hv).
  assert (Hs : [ G ; Γ ⊢[ i ] lsingle2 a (tmRefl l1 A a) ≅ lsingle2 a' (tmRefl l3 A' a')
                 : Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ]).
  { apply lsub_eq_J; auto. }
  assert (Hs2 : [ G ; Γ ⊢[ i ] lsingle2 u e ≅ lsingle2 u' e'
                 : Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ]).
  { apply lsub_eq_J; auto. }
  assert (HMs : [ G ; Γ ⊢[ i ] M[lsingle2 a (tmRefl l1 A a)] ≅ M'[lsingle2 a' (tmRefl l3 A' a')] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi HMM (lsub_eq_l Hs)) | exact (wf_ty_func HM' Hs)]. }
  assert (HMs2 : [ G ; Γ ⊢[ i ] M[lsingle2 u e] ≅ M'[lsingle2 u' e'] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi HMM (lsub_eq_l Hs2)) | exact (wf_ty_func HM' Hs2)]. }
  (* [J] at the primed instance *)
  eapply wf_lconv with (l' := l4); [|exact H24].
  eapply conv_tm'; [|eapply eqty_lconv; [exact HMs2 | now apply lequiv_sym]].
  apply wf_J; eauto using Hv, lequiv_wf_r.
  - eapply wft_lconv; [exact HA' | exact H31].
  - eapply wf_lconv; [exact Ha'A' | exact H31].
  - eapply wf_lconv with (l' := l2); [|now apply lequiv_sym].
    eapply conv_tm'; [exact Hc' | apply eqty_sym, HMs].
  - eapply wf_lconv; [eapply conv_tm'; [exact Hu' | apply eqty_sym, HAA] | exact H31].
  - eapply wf_lconv; [|exact H31]. eapply conv_tm'; [exact He'|].
    apply eqty_sym, eqty_id; auto using Hv.
Qed.


Lemma pre_sig_r {Γ l1 l2 l3 l4 A A' B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tySig l3 l4 A' B' @ lmax l1 l2 ].
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi.
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
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hi Hv.
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
Proof using Hv.
  intros Hl Hl' HA HB Hp.
  apply wf_pair; auto using compt_self; [apply wf_fst | apply wf_snd]; auto using compt_self.
Qed.

Lemma pre_snd_ty {Γ l l' A B p} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] B[lsingle (tmFst l l' A B p)] @ l' ].
Proof using Hi Hv. intros; eapply (wf_ty_single Hi); [eassumption | apply wf_fst; auto using compt_self]. Qed.

(** ** Well-founded trees (M13a): the step telescope *)

Lemma wk_under_ty {Γ X Y T lx ly k} : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] T @ k ] -> [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] T⟨rlift ↑⟩ @ k ].
Proof using Hi. intros HΔ HT. eapply weakening_r; eauto. apply wkr_up, wkr_shift1. Qed.
Lemma wk_under_eqty {Γ X Y T T' lx ly k} : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] T ≅ T' @ k ] -> [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] T⟨rlift ↑⟩ ≅ T'⟨rlift ↑⟩ @ k ].
Proof using Hi. intros HΔ HT. eapply weakening_r; eauto. apply wkr_up, wkr_shift1. Qed.

(** ** Dependent tuples (M17a) *)

(** The canonical indices of [Fin (succ m)]. *)
Lemma fin_inl_wf {Γ m} : compt i -> [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin m) (tmTriv lzero) : tyFin (succ m) @ lzero ].
Proof using Hi Hv.
  intros Hc Hm. pose proof (ctx_of_wf_tm Hi Hm) as HΓ.
  eapply wf_conv; [| rewrite Hi; apply eqty_fin_succ; assumption].
  eapply wf_lconv; [| apply lequiv_sym, lmax_idem; exact I].
  apply wf_inl; try exact I; auto using wft_fin.
  - apply wft_unit; [exact Hv | now rewrite Hi | exact I].
  - apply wf_triv; [exact Hv | now rewrite Hi | exact I].
Qed.

Lemma fin_inr_wf {Γ m b} : compt i -> [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] b : tyFin m @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmInr lzero lzero (tyUnit lzero) (tyFin m) b : tyFin (succ m) @ lzero ].
Proof using Hi Hv.
  intros Hc Hm Hb. pose proof (ctx_of_wf_tm Hi Hm) as HΓ.
  eapply wf_conv; [| rewrite Hi; apply eqty_fin_succ; assumption].
  eapply wf_lconv; [| apply lequiv_sym, lmax_idem; exact I].
  apply wf_inr; try exact I; auto using wft_fin.
  apply wft_unit; [exact Hv | now rewrite Hi | exact I].
Qed.

Lemma pre_dvec_r {Γ l l' n n' F' } : compt i -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] n ≅ n' : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F' @ l ] -> [ G ; Γ ⊢[ i ] tyDVec l' n' F' @ l ].
Proof using Hi Hv.
  intros Hc Hl Hnn Hn' HF'.
  assert (HF2 : [ G ; Γ ,, tyFin n' @ lzero ⊢[ i ] F' @ l ]).
  { eapply (stab_ty Hi (eqty_fin _ _ _ _ _ Hv Hnn)); [apply lequiv_refl; exact I | |exact HF'].
    apply ext_wf; [now apply wft_fin | exact I]. }
  eapply wft_lconv with (l' := l'); [|exact Hl].
  apply wft_dvec; eauto using lequiv_wf_r. eapply wft_lconv; [exact HF2 | now apply lequiv_sym].
Qed.

Lemma pre_dvec_zero {Γ l F} : compt i -> lwf (gL G) l -> [ G ; Γ ,, tyFin zero @ lzero ⊢[ i ] F @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec l zero F @ l ] /\ [ G ; Γ ⊢[ i ] tyUnit l @ l ].
Proof using Hi Hv.
  intros Hc Hl HF. pose proof (ctx_of_wf_ty Hi HF) as HΓF.
  assert (HΓ : [ G ; Γ ⊢[ i ] ]) by (inversion HΓF; assumption). split.
  - apply wft_dvec; auto. apply wf_zero; [exact Hv | now rewrite Hi].
  - apply wft_unit; [exact Hv | now rewrite Hi | exact Hl].
Qed.

Lemma pre_dvec_succ {Γ l n F} : compt i -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin (succ n) @ lzero ⊢[ i ] F @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec l (succ n) F @ l ] /\
  [ G ; Γ ⊢[ i ] tySig l l (dvecHd n F) (dvecTl l n F) @ l ].
Proof using Hi Hv.
  intros Hc Hl Hn HF. split.
  - apply wft_dvec; auto. apply wf_succ; [exact Hv | exact Hn].
  - assert (HH : [ G ; Γ ⊢[ i ] dvecHd n F @ l ]) by exact (wf_ty_single Hi HF (fin_inl_wf Hc Hn)).
    pose proof (ext_wf HH Hl) as HΓH.
    assert (Hn1 : [ G ; Γ ,, dvecHd n F @ l ⊢[ i ] n⟨↑⟩ : tyNat @ lzero ])
      by exact (wk1_tm G i Hi _ _ _ _ _ _ HΓH Hn).
    assert (HΔ : [ G ; Γ ,, dvecHd n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] ])
      by (apply ext_wf; [now apply wft_fin | exact I]).
    assert (Hn2 : [ G ; Γ ,, dvecHd n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] n⟨↑⟩⟨↑⟩ : tyNat @ lzero ])
      by exact (wk1_tm G i Hi _ _ _ _ _ _ HΔ Hn1).
    assert (HF1 : [ G ; Γ ,, dvecHd n F @ l ,, tyFin (succ n⟨↑⟩) @ lzero ⊢[ i ] F⟨rlift ↑⟩ @ l ]).
    { apply (wk_under_ty (X := tyFin (succ n))); [|exact HF].
      apply ext_wf; [apply wft_fin; [exact Hv | now apply wf_succ] | exact I]. }
    assert (HF2 : [ G ; Γ ,, dvecHd n F @ l ,, tyFin n⟨↑⟩ @ lzero ,, tyFin (succ n⟨↑⟩⟨↑⟩) @ lzero
                    ⊢[ i ] F⟨rlift ↑⟩⟨rlift ↑⟩ @ l ]).
    { apply (wk_under_ty (X := tyFin (succ n⟨↑⟩))); [|exact HF1].
      apply ext_wf; [apply wft_fin; [exact Hv | now apply wf_succ] | exact I]. }
    assert (Hinr : [ G ; Γ ,, dvecHd n F @ l ,, tyFin n⟨↑⟩ @ lzero
                     ⊢[ i ] tmInr lzero lzero (tyUnit lzero) (tyFin n⟨↑⟩⟨↑⟩) (var 0) : tyFin (succ n⟨↑⟩⟨↑⟩) @ lzero ])
      by (apply fin_inr_wf; [exact Hc | exact Hn2 | exact (var0_wf G i Hi _ _ _ HΔ)]).
    eapply wft_lconv; [|apply lequiv_sym, lmax_idem, Hl].
    apply wft_sig; auto. apply wft_dvec; auto. exact (wf_ty_single Hi HF2 Hinr).
Qed.

Lemma lwf_max {l l'} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) (lmax l l').
Proof using . intros; cbn; split; assumption. Qed.

(** The children's type, over any shape context [Γ, X]. *)
Lemma W_fty_wf {Γ X lx l l' A B} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ] -> [ G ; Γ ,, X @ lx ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] wfty l l' A B @ lmax l' (lmax l l') ].
Proof using Hi Hv.
  intros Hl Hl' HW HB. pose proof (ctx_of_wf_ty Hi HB) as HΓX.
  apply wft_pi; auto using lwf_max.
  eapply wk1_ty; eauto; [apply ext_wf; eauto|]. eapply wk1_ty; eauto.
Qed.

(** The children applied to the position, at [W] weakened past [a], [f]
    and the position. *)
Lemma W_u_wf {Γ X lx F lf l l' A B} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ] -> [ G ; Γ ,, X @ lx ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] ] -> [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfty l l' A B @ lf ] ->
  lequiv (gL G) lf (lmax l' (lmax l l')) ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, B⟨↑⟩ @ l' ⊢[ i ]
      app (var 1) l' (lmax l l') B⟨↑⟩⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 0)
      : (tyW l l' A B)⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax l l' ].
Proof using Hi Hv.
  intros Hl Hl' HW HB HΓXF HF Hlf. pose proof (ctx_of_wf_ty Hi HB) as HΓX.
  assert (HB1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] B⟨↑⟩ @ l' ]) by (eapply wk1_ty; eauto).
  assert (HΔ : [ G ; Γ ,, X @ lx ,, F @ lf ,, B⟨↑⟩ @ l' ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HB2 : [ G ; Γ ,, X @ lx ,, F @ lf ,, B⟨↑⟩ @ l' ⊢[ i ] B⟨↑⟩⟨↑⟩ @ l' ]) by (eapply wk1_ty; eauto).
  assert (HΔB : [ G ; Γ ,, X @ lx ,, F @ lf ,, B⟨↑⟩ @ l' ,, B⟨↑⟩⟨↑⟩ @ l' ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HW2 : [ G ; Γ ,, X @ lx ,, B @ l' ⊢[ i ] (tyW l l' A B)⟨↑⟩⟨↑⟩ @ lmax l l' ])
    by (eapply wk1_ty; eauto; [apply ext_wf; eauto | eapply wk1_ty; eauto]).
  pose proof (wk_under_ty HΔ HW2) as HW3.
  pose proof (wk_under_ty HΔB HW3) as HW4.
  rewrite <- shift4_single0_ty. apply wf_app; auto using lwf_max.
  - eapply wf_conv; [eapply wf_lconv; [apply wf_var; [now rewrite Hi | do 2 constructor] | apply lequiv_sym, Hlf]|].
    rewrite Hi. eapply eqty_lconv; [|apply lequiv_sym, Hlf].
    apply eqty_sym. match goal with |- eq_ty _ _ _ _ ?T _ => change T with ((wfty l l' A B)⟨↑⟩⟨↑⟩) end.
    eapply wk1_eqty; eauto. eapply wk1_eqty; eauto.
  - apply wf_var; [now rewrite Hi | constructor].
Qed.

(** The induction hypothesis's type. *)
Lemma W_ih_wf {Γ X lx F lf l l' l'' A B M} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ] -> [ G ; Γ ,, X @ lx ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] ] -> [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfty l l' A B @ lf ] ->
  lequiv (gL G) lf (lmax l' (lmax l l')) ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] wihty l l' l'' A B M @ lmax l' l'' ].
Proof using Hi Hv.
  intros Hl Hl' Hl'' HW HB HM HΓXF HF Hlf. pose proof (ctx_of_wf_ty Hi HB) as HΓX.
  assert (HL : lwf (gL G) (lmax l l')) by auto using lwf_max.
  assert (HB1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] B⟨↑⟩ @ l' ]) by (eapply wk1_ty; eauto).
  assert (HΔ : [ G ; Γ ,, X @ lx ,, F @ lf ,, B⟨↑⟩ @ l' ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (W1 : [ G ; Γ ,, X @ lx ⊢[ i ] (tyW l l' A B)⟨↑⟩ @ lmax l l' ]) by (eapply wk1_ty; eauto).
  assert (W2 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] (tyW l l' A B)⟨↑⟩⟨↑⟩ @ lmax l l' ]) by (eapply wk1_ty; eauto).
  assert (W3 : [ G ; Γ ,, X @ lx ,, F @ lf ,, B⟨↑⟩ @ l' ⊢[ i ] (tyW l l' A B)⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax l l' ])
    by (eapply wk1_ty; eauto).
  pose proof (wk_under_ty (ext_wf W1 HL) HM) as HM1.
  pose proof (wk_under_ty (ext_wf W2 HL) HM1) as HM2.
  pose proof (wk_under_ty (ext_wf W3 HL) HM2) as HM3.
  apply wft_pi; auto using lwf_max.
  eapply (wf_ty_single Hi HM3). exact (W_u_wf Hl Hl' HW HB HΓXF HF Hlf).
Qed.

Lemma ctx_pre {Γ A l} : [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] ].
Proof using . inversion 1; auto. Qed.
Lemma eqty_sym' {Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T' ≅ T @ l ].
Proof using . apply eqty_sym. Qed.
Lemma eqty_refl' {Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T @ l ].
Proof using . apply eqty_refl. Qed.

(** Weakening past three locals, and under one past three. *)
Lemma wk3_ty {Γ X Y Z lx ly lz T k} : [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩ @ k ].
Proof using Hi.
  intros H HT. pose proof (ctx_pre H) as H2. pose proof (ctx_pre H2) as H1.
  eapply wk1_ty; eauto. eapply wk1_ty; eauto. eapply wk1_ty; eauto.
Qed.
Lemma wk3_eqty {Γ X Y Z lx ly lz T T' k} : [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] T ≅ T' @ k ] -> [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩ ≅ T'⟨↑⟩⟨↑⟩⟨↑⟩ @ k ].
Proof using Hi.
  intros H HT. pose proof (ctx_pre H) as H2. pose proof (ctx_pre H2) as H1.
  eapply wk1_eqty; eauto. eapply wk1_eqty; eauto. eapply wk1_eqty; eauto.
Qed.
Lemma wk_under3_ty {Γ X Y Z X0 lx ly lz l0 T k} : [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] X0 @ l0 ] -> lwf (gL G) l0 -> [ G ; Γ ,, X0 @ l0 ⊢[ i ] T @ k ] ->
  [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ,, X0⟨↑⟩⟨↑⟩⟨↑⟩ @ l0 ⊢[ i ] T⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ k ].
Proof using Hi.
  intros H HX Hl HT. pose proof (ctx_pre H) as H2. pose proof (ctx_pre H2) as H1.
  apply wk_under_ty; [apply ext_wf; [exact (wk3_ty H HX) | exact Hl]|].
  apply wk_under_ty; [apply ext_wf; [eapply wk1_ty; eauto; eapply wk1_ty; eauto | exact Hl]|].
  apply wk_under_ty; [apply ext_wf; [eapply wk1_ty; eauto | exact Hl]|]. exact HT.
Qed.
Lemma wk_under3_eqty {Γ X Y Z X0 lx ly lz l0 T T' k} : [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] X0 @ l0 ] -> lwf (gL G) l0 -> [ G ; Γ ,, X0 @ l0 ⊢[ i ] T ≅ T' @ k ] ->
  [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ,, X0⟨↑⟩⟨↑⟩⟨↑⟩ @ l0
      ⊢[ i ] T⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ ≅ T'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ k ].
Proof using Hi.
  intros H HX Hl HT. pose proof (ctx_pre H) as H2. pose proof (ctx_pre H2) as H1.
  apply wk_under_eqty; [apply ext_wf; [exact (wk3_ty H HX) | exact Hl]|].
  apply wk_under_eqty; [apply ext_wf; [eapply wk1_ty; eauto; eapply wk1_ty; eauto | exact Hl]|].
  apply wk_under_eqty; [apply ext_wf; [eapply wk1_ty; eauto | exact Hl]|]. exact HT.
Qed.

(** The children, two locals further: at the [Π] the telescope spells. *)
Lemma W_var1_wf {Γ X lx F lf Y ly l l' A B} :
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] ] -> [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfty l l' A B @ lf ] ->
  lequiv (gL G) lf (lmax l' (lmax l l')) ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ]
      var 1 : tyPi l' (lmax l l') B⟨↑⟩⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ lmax l' (lmax l l') ].
Proof using Hi.
  intros HΔ HF Hlf. pose proof (ctx_pre HΔ) as H2.
  eapply wf_conv; [eapply wf_lconv; [apply wf_var; [now rewrite Hi | do 2 constructor] | apply lequiv_sym, Hlf]|].
  rewrite Hi. eapply eqty_lconv; [|apply lequiv_sym, Hlf].
  apply eqty_sym. match goal with |- eq_ty _ _ _ _ ?T _ => change T with ((wfty l l' A B)⟨↑⟩⟨↑⟩) end.
  eapply wk1_eqty; eauto. eapply wk1_eqty; eauto.
Qed.

(** [sup] of the step's shape and children, at [W] weakened past the telescope. *)
Lemma W_sup_step_wf {Γ X lx F lf Y ly l l' A B} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] X ≅ A @ l ] -> lequiv (gL G) lx l ->
  [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfty l l' A B @ lf ] -> lequiv (gL G) lf (lmax l' (lmax l l')) ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ]
      tmSup l l' A⟨↑⟩⟨↑⟩⟨↑⟩ B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1) : (tyW l l' A B)⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax l l' ].
Proof using Hi Hv.
  intros Hl Hl' HA HB HΔ HXA Hlx HF Hlf.
  apply wf_sup; auto using compt_self.
  - exact (wk3_ty HΔ HA).
  - exact (wk_under3_ty HΔ HA Hl HB).
  - eapply wf_lconv; [eapply wf_conv; [apply wf_var; [now rewrite Hi | do 3 constructor] |] | apply lequiv_sym, Hlx].
    rewrite Hi. eapply eqty_lconv; [apply (wk3_eqty HΔ); apply eqty_sym, HXA | exact Hlx].
  - rewrite W_E2. change (tyW l l' A⟨↑⟩⟨↑⟩⟨↑⟩ B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)⟨↑⟩ with ((tyW l l' A B)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩).
    rewrite W_E3. exact (W_var1_wf HΔ HF Hlf).
Qed.

Lemma W_var1_step {Γ X lx F lf Y ly l l' A B} :
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] ] -> [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfty l l' A B @ lf ] ->
  lequiv (gL G) lf (lmax l' (lmax l l')) ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] var 1
      : tyPi l' (lmax l l') (B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)]
          (tyW l l' A⟨↑⟩⟨↑⟩⟨↑⟩ B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)⟨↑⟩ @ lmax l' (lmax l l') ].
Proof using Hi.
  intros HΔ HF Hlf. rewrite W_E2.
  change (tyW l l' A⟨↑⟩⟨↑⟩⟨↑⟩ B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)⟨↑⟩ with ((tyW l l' A B)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩).
  rewrite W_E3. exact (W_var1_wf HΔ HF Hlf).
Qed.

Lemma pre_W_r {Γ l1 l2 l3 l4 A A' B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyW l3 l4 A' B' @ lmax l1 l2 ].
Proof using Hi Hv.
  intros H13 H24 HA HA' HB.
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  eapply wft_lconv with (l' := lmax l3 l4); [|now apply lequiv_max].
  apply wft_W; try solve [eauto using lequiv_wf_r, compt_self].
  eapply wft_lconv; [|apply lequiv_sym; exact H24].
  eapply (stab_ty Hi HA H13); [apply ext_wf; eauto using lequiv_wf_r | exact HB].
Qed.

(** The code of [W] (M13b), as [Σ]'s. *)
Lemma pre_codeW_r {Γ l1 l2 l3 l4 s s' t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmW l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using Hi Hv.
  intros H13 H24 Hs Hs' Ht. pose proof (ctx_of_wf_tm Hi Hs') as HΓ.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; auto).
  assert (Hs3 : [ G ; Γ ⊢[ i ] s' : tyU l3 @ lsuc l3 ]) by exact (conv_U Hs' H13).
  eapply wf_lconv with (l' := lsuc (lmax l3 l4)); [|apply lequiv_suc, lequiv_max; eassumption].
  eapply conv_tm'.
  - apply wf_code_W; try solve [eauto using lequiv_wf_r, compt_self].
    apply (conv_U (l := l2)); [|exact H24].
    eapply (stab_tm Hi HEl H13); [|exact Ht].
    apply ext_wf; [apply wft_El; eauto using lequiv_wf_r | eauto using lequiv_wf_r].
  - eapply eqty_lconv; [|apply lequiv_suc, lequiv_max; apply lequiv_sym; eassumption].
    apply eqty_U; [exact Hv | now rewrite Hi | apply lequiv_max; eassumption].
Qed.

Lemma pre_sup_r {Γ l1 l2 l3 l4 A A' B B' a a' f'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] f' : tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩ @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ⊢[ i ] tmSup l3 l4 A' B' a' f' : tyW l1 l2 A B @ lmax l1 l2 ].
Proof using Hi Hv.
  intros H13 H24 HA HAA HA' HB HBB HB' Haa Ha Ha' Hf'.
  pose proof (lequiv_wf_l _ _ _ H13) as W1. pose proof (lequiv_wf_l _ _ _ H24) as W2.
  pose proof (lequiv_wf_r _ _ _ H13) as W3. pose proof (lequiv_wf_r _ _ _ H24) as W4.
  assert (HL : lequiv (gL G) (lmax l1 l2) (lmax l3 l4)) by (apply lequiv_max; assumption).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l3 l4 A' B' @ lmax l1 l2 ])
    by (apply eqty_W; auto using compt_self).
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HBa : [ G ; Γ ⊢[ i ] B[lsingle a] @ l2 ]) by exact (wf_ty_single Hi HB Ha).
  assert (EBa : [ G ; Γ ⊢[ i ] B[lsingle a] ≅ B'[lsingle a'] @ l2 ]).
  { eapply eqty_trans; [apply (wf_ty_func HB (d' := lsingle a')); now apply lsub_eq_single |].
    exact (eqty_single Hi HBB Ha'). }
  eapply wf_lconv with (l' := lmax l3 l4); [| exact HL].
  eapply (conv_tm' (T' := tyW l3 l4 A' B')); [| eapply eqty_lconv; [exact EW | now apply lequiv_sym]].
  apply wf_sup; auto using compt_self.
  - eapply wft_lconv; [exact (stab_ty Hi HAA H13 HΓA' HB') | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Ha' | apply eqty_sym, HAA] | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Hf'|] | apply lequiv_sym, lequiv_max; [exact H24 | exact HL]].
    apply eqty_sym, eqty_pi; auto using lequiv_max.
    eapply wk1_eqty; eauto. apply ext_wf; auto.
Qed.

(** The induction hypothesis's type, along equal components. *)
Lemma W_ih_eq {Γ l1 l2 l3 l4 l5 l6 A A' B B' M M'} :
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' @ lmax l4 l5 ] ->
  [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l4 l5 A' B' @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ]
      wihty l1 l2 l3 A B M ≅ wihty l4 l5 l6 A' B' M' @ lmax l2 l3 ].
Proof using Hi Hv.
  intros H14 H25 H36 HA HB HBB HB' HM HMM HW' EW HF EF.
  pose proof (lequiv_wf_l _ _ _ H14) as W1. pose proof (lequiv_wf_l _ _ _ H25) as W2.
  pose proof (lequiv_wf_l _ _ _ H36) as W3.
  pose proof (lequiv_wf_r _ _ _ H14) as W4. pose proof (lequiv_wf_r _ _ _ H25) as W5.
  assert (HL : lequiv (gL G) (lmax l1 l2) (lmax l4 l5)) by (apply lequiv_max; assumption).
  assert (WL : lwf (gL G) (lmax l1 l2)) by auto using lwf_max.
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; auto using compt_self).
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HΓAF : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] ])
    by (apply ext_wf; auto using lwf_max).
  assert (HB1 : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] B⟨↑⟩ @ l2 ])
    by (eapply wk1_ty; eauto).
  assert (EB1 : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] B⟨↑⟩ ≅ B'⟨↑⟩ @ l2 ])
    by (eapply wk1_eqty; eauto).
  set (Δ := Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, B⟨↑⟩ @ l2).
  assert (HΔ : [ G ; Δ ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HB2 : [ G ; Δ ⊢[ i ] B⟨↑⟩⟨↑⟩ @ l2 ]) by (eapply wk1_ty; eauto).
  assert (EB2 : [ G ; Δ ⊢[ i ] B⟨↑⟩⟨↑⟩ ≅ B'⟨↑⟩⟨↑⟩ @ l2 ]) by (eapply wk1_eqty; eauto).
  assert (HΔB : [ G ; Δ ,, B⟨↑⟩⟨↑⟩ @ l2 ⊢[ i ] ]) by (apply ext_wf; auto).
  (* the children's applications *)
  assert (RF : [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ])
    by (apply eqty_refl; exact HF).
  assert (Hu := W_u_wf W1 W2 HW HB HΓAF RF (lequiv_refl _ _ (lwf_max W2 WL))).
  assert (HB'5 : [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l5 ]) by (eapply wft_lconv; [exact HB' | now apply lequiv_sym]).
  assert (HΓAFB' : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, B'⟨↑⟩ @ l5 ⊢[ i ] ])
    by (apply ext_wf; [eapply wk1_ty; eauto | exact W5]).
  pose proof (W_u_wf W4 W5 HW' HB'5 HΓAF EF ltac:(apply lequiv_max; [exact H25 | exact HL])) as Hu'0.
  assert (Hu' : [ G ; Δ ⊢[ i ] app (var 1) l5 (lmax l4 l5) B'⟨↑⟩⟨↑⟩ (tyW l4 l5 A' B')⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 0)
                    : (tyW l1 l2 A B)⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax l1 l2 ]).
  { assert (EB1' : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] B'⟨↑⟩ ≅ B⟨↑⟩ @ l5 ])
      by (eapply eqty_lconv; [exact (eqty_sym' EB1) | exact (lequiv_sym _ _ _ H25)]).
    pose proof (stab_tm Hi EB1' (lequiv_sym _ _ _ H25) HΔ Hu'0) as X.
    eapply wf_lconv; [eapply conv_tm'; [exact X|] | exact HL].
    eapply eqty_lconv; [| apply lequiv_sym, HL]. apply (wk3_eqty HΔ), EW. }
  assert (EW2 : [ G ; Γ ,, A @ l1 ,, B @ l2 ⊢[ i ] (tyW l1 l2 A B)⟨↑⟩⟨↑⟩ ≅ (tyW l4 l5 A' B')⟨↑⟩⟨↑⟩ @ lmax l1 l2 ])
    by (eapply wk1_eqty; [ | | eapply wk1_eqty]; eauto; apply ext_wf; auto).
  pose proof (wk_under_eqty HΔ EW2) as EW3. pose proof (wk_under_eqty HΔB EW3) as EW4.
  assert (Huu : [ G ; Δ ⊢[ i ] app (var 1) l2 (lmax l1 l2) B⟨↑⟩⟨↑⟩ (tyW l1 l2 A B)⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 0)
                    ≅ app (var 1) l5 (lmax l4 l5) B'⟨↑⟩⟨↑⟩ (tyW l4 l5 A' B')⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 0)
                    : (tyW l1 l2 A B)⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax l1 l2 ]).
  { rewrite <- shift4_single0_ty. apply eqtm_app; auto.
    - apply eqtm_refl, (W_var1_wf HΔ RF), lequiv_refl, lwf_max; assumption.
    - apply eqtm_refl, wf_var; [now rewrite Hi | constructor]. }
  pose proof (wk_under3_ty HΔ HW WL HM) as HM3.
  pose proof (wk_under3_eqty HΔ HW WL HMM) as HMM3.
  apply eqty_pi; auto.
  eapply eqty_trans; [eapply (wf_ty_func HM3); eapply lsub_eq_single; [exact Hu | exact Hu' | exact Huu] |].
  exact (eqty_single Hi HMM3 Hu').
Qed.

(** The step's type, along equal components, in the left telescope. *)
Lemma W_step_eq {Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' I li} :
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l4 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, A' @ l4 ⊢[ i ] B' @ l5 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l4 l5 A' B' @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, I @ li ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, I @ li ⊢[ i ]
      wstepty l1 l2 A B M ≅ wstepty l4 l5 A' B' M' @ l3 ].
Proof using Hi Hv.
  intros H14 H25 H36 HA HAA HA'4 HB HBB HB'5 HM HMM EW HF EF HΘ.
  pose proof (lequiv_wf_l _ _ _ H14) as W1. pose proof (lequiv_wf_l _ _ _ H25) as W2.
  pose proof (lequiv_wf_r _ _ _ H14) as W4. pose proof (lequiv_wf_r _ _ _ H25) as W5.
  assert (HL : lequiv (gL G) (lmax l1 l2) (lmax l4 l5)) by (apply lequiv_max; assumption).
  assert (WL : lwf (gL G) (lmax l1 l2)) by auto using lwf_max.
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; auto using compt_self).
  assert (RF : [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ])
    by (apply eqty_refl; exact HF).
  assert (RL : lequiv (gL G) (lmax l2 (lmax l1 l2)) (lmax l2 (lmax l1 l2))) by (apply lequiv_refl, lwf_max; auto).
  assert (HAA4 : [ G ; Γ ⊢[ i ] A ≅ A' @ l4 ]) by (eapply eqty_lconv; [exact HAA | exact (lequiv_sym _ _ _ H14)]).
  pose proof (W_sup_step_wf W1 W2 HA HB HΘ (eqty_refl' HA) (lequiv_refl _ _ W1) RF RL) as Hs.
  pose proof (W_sup_step_wf W4 W5 HA'4 HB'5 HΘ HAA4 H14 EF ltac:(apply lequiv_max; [exact H25 | exact HL])) as Hs'0.
  assert (Hs' : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, I @ li ⊢[ i ]
                  tmSup l4 l5 A'⟨↑⟩⟨↑⟩⟨↑⟩ B'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1) : (tyW l1 l2 A B)⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax l1 l2 ]).
  { eapply wf_lconv; [eapply conv_tm'; [exact Hs'0 |] | exact HL].
    eapply eqty_lconv; [exact (wk3_eqty HΘ EW) | exact (lequiv_sym _ _ _ HL)]. }
  assert (Hss : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, I @ li ⊢[ i ]
                  tmSup l1 l2 A⟨↑⟩⟨↑⟩⟨↑⟩ B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1)
                  ≅ tmSup l4 l5 A'⟨↑⟩⟨↑⟩⟨↑⟩ B'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1) : (tyW l1 l2 A B)⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax l1 l2 ]).
  { apply eqtm_sup; auto using compt_self.
    - exact (wk3_ty HΘ HA).
    - exact (wk3_eqty HΘ HAA).
    - exact (wk_under3_ty HΘ HA W1 HB).
    - exact (wk_under3_eqty HΘ HA W1 HBB).
    - apply eqtm_refl, wf_var; [now rewrite Hi | do 3 constructor].
    - apply eqtm_refl, (W_var1_step HΘ RF RL). }
  pose proof (wk_under3_ty HΘ HW WL HM) as HM3.
  pose proof (wk_under3_eqty HΘ HW WL HMM) as HMM3.
  eapply eqty_trans; [eapply (wf_ty_func HM3); eapply lsub_eq_single; [exact Hs | exact Hs' | exact Hss] |].
  exact (eqty_single Hi HMM3 Hs').
Qed.

(** [elim_W]'s congruence, right-hand side: the primed telescope is formed,
    the step moved into it along the identity, and the type converted. *)
Lemma pre_elimW_r {Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c' t t'} :
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] wihty l1 l2 l3 A B M @ lmax l2 l3 ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ⊢[ i ] c' : wstepty l1 l2 A B M @ l3 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t : tyW l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] t' : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmElimW l4 l5 l6 A' B' M' c' t' : M[lsingle t] @ l3 ].
Proof using Hi Hv.
  intros H14 H25 H36 HAA HA HA' HBB HB HB' HMM HM HM' HF HI Hc Htt Ht Ht'.
  pose proof (ctx_of_wf_tm Hi Ht) as HΓ.
  pose proof (lequiv_wf_l _ _ _ H14) as W1. pose proof (lequiv_wf_l _ _ _ H25) as W2.
  pose proof (lequiv_wf_l _ _ _ H36) as W3.
  pose proof (lequiv_wf_r _ _ _ H14) as W4. pose proof (lequiv_wf_r _ _ _ H25) as W5.
  pose proof (lequiv_wf_r _ _ _ H36) as W6.
  assert (HL : lequiv (gL G) (lmax l1 l2) (lmax l4 l5)) by (apply lequiv_max; assumption).
  assert (WL : lwf (gL G) (lmax l1 l2)) by auto using lwf_max.
  assert (WL' : lwf (gL G) (lmax l4 l5)) by auto using lwf_max.
  assert (HLF : lequiv (gL G) (lmax l2 (lmax l1 l2)) (lmax l5 (lmax l4 l5))) by (apply lequiv_max; assumption).
  assert (HLI : lequiv (gL G) (lmax l2 l3) (lmax l5 l6)) by (apply lequiv_max; assumption).
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ])
    by (apply eqty_W; auto using compt_self).
  assert (HW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' @ lmax l4 l5 ])
    by (eapply wft_lconv; [exact (pre_W_r H14 H25 HAA HA' HB') | exact (lequiv_sym _ _ _ HL)]).
  assert (HA'4 : [ G ; Γ ⊢[ i ] A' @ l4 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓA' : [ G ; Γ ,, A' @ l4 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HB'5 : [ G ; Γ ,, A' @ l4 ⊢[ i ] B' @ l5 ])
    by (eapply wft_lconv; [exact (stab_ty Hi HAA H14 HΓA' HB') | now apply lequiv_sym]).
  assert (HB'5A : [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l5 ]) by (eapply wft_lconv; [exact HB' | now apply lequiv_sym]).
  assert (HΓW' : [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HM'6 : [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' @ l6 ])
    by (eapply wft_lconv; [exact (stab_ty Hi EW HL HΓW' HM') | now apply lequiv_sym]).
  (* the primed telescope *)
  pose proof (W_fty_wf (X := A') (lx := l4) W4 W5 HW' HB'5) as HF'.
  assert (HΓA'F' : [ G ; Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ⊢[ i ] ])
    by (apply ext_wf; auto using lwf_max).
  assert (HI' : [ G ; Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ⊢[ i ] wihty l4 l5 l6 A' B' M' @ lmax l5 l6 ])
    by exact (W_ih_wf W4 W5 W6 HW' HB'5 HM'6 HΓA'F' (eqty_refl' HF') (lequiv_refl _ _ (lwf_max W5 WL'))).
  (* the left telescope's equations with the primed one *)
  assert (EW2 : [ G ; Γ ,, A @ l1 ,, B @ l2 ⊢[ i ] (tyW l1 l2 A B)⟨↑⟩⟨↑⟩ ≅ (tyW l4 l5 A' B')⟨↑⟩⟨↑⟩ @ lmax l1 l2 ])
    by (eapply wk1_eqty; [ | | eapply wk1_eqty]; eauto; apply ext_wf; auto).
  assert (EF : [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l4 l5 A' B' @ lmax l2 (lmax l1 l2) ])
    by (apply eqty_pi; auto).
  assert (HF'A : [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l4 l5 A' B' @ lmax l2 (lmax l1 l2) ])
    by (eapply wft_lconv; [exact (W_fty_wf W4 W5 HW' HB'5A) | exact HLF]).
  assert (HΓAF : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] ]) by (apply ext_wf; auto using lwf_max).
  assert (HI'A : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] wihty l4 l5 l6 A' B' M' @ lmax l2 l3 ])
    by (eapply wft_lconv; [exact (W_ih_wf W4 W5 W6 HW' HB'5A HM'6 HΓAF EF HLF) | exact HLI]).
  pose proof (W_ih_eq H14 H25 H36 HA HB HBB HB' HM HMM HW' EW HF EF) as EI.
  (* the identity from the primed telescope to the left one *)
  assert (Hid0 : [ G ; Γ ⊢[ i ] lshift 0 : Γ ]) by (eapply lsub_wf_id; eauto).
  pose proof (proj2 (ctx_conv_ext Hid0 HA HAA HA' H14)) as Hid1.
  pose proof (proj2 (ctx_conv_ext Hid1 HF EF HF'A HLF)) as Hid2.
  pose proof (proj2 (ctx_conv_ext Hid2 HI EI HI'A HLI)) as Hid3.
  assert (HΘ : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3 ⊢[ i ] ])
    by (apply ext_wf; auto using lwf_max).
  pose proof (W_step_eq H14 H25 H36 HA HAA HA'4 HB HBB HB'5 HM HMM EW HF EF HΘ) as ES.
  assert (Hc' : [ G ; Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ,, wihty l4 l5 l6 A' B' M' @ lmax l5 l6
                  ⊢[ i ] c' : wstepty l4 l5 A' B' M' @ l6 ]).
  { pose proof (wf_tm_subst Hi Hc Hid3) as X.
    pose proof (eqty_subst Hi ES Hid3) as Y.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ ES) as [N1 N2].
    rewrite nf_id in X by exact (wf_tm_nf Hc).
    rewrite (nf_id_ty (wstepty l1 l2 A B M)) in X, Y by exact N1.
    rewrite (nf_id_ty (wstepty l4 l5 A' B' M')) in Y by exact N2.
    eapply wf_lconv; [eapply conv_tm'; [exact X | exact (eqty_sym' Y)] | exact (lequiv_sym _ _ _ H36)]. }
  assert (Ht'W : [ G ; Γ ⊢[ i ] t' : tyW l4 l5 A' B' @ lmax l4 l5 ])
    by (eapply wf_lconv; [eapply conv_tm'; [exact Ht' | exact (eqty_sym' EW)] | exact (lequiv_sym _ _ _ HL)]).
  eapply wf_lconv with (l' := l6); [| exact H36].
  eapply (conv_tm' (T' := M'[lsingle t'])).
  - apply wf_elimW; auto using compt_self.
  - eapply eqty_lconv; [|apply lequiv_sym, H36].
    eapply eqty_trans.
    + apply (wf_ty_func HM (d' := lsingle t')). now apply lsub_eq_single.
    + exact (eqty_single Hi HMM Ht').
Qed.

(** The children's types of [sup], along equal components (M13b). *)
Lemma W_sup_feq {Γ l1 l2 l3 l4 A A' B B' a a'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩
      ≅ tyPi l4 (lmax l3 l4) B'[lsingle a'] (tyW l3 l4 A' B')⟨↑⟩ @ lmax l2 (lmax l1 l2) ].
Proof using Hi Hv.
  intros H13 H24 HA HAA HB HBB Haa Ha Ha'.
  pose proof (lequiv_wf_l _ _ _ H13) as W1. pose proof (lequiv_wf_l _ _ _ H24) as W2.
  assert (HL : lequiv (gL G) (lmax l1 l2) (lmax l3 l4)) by (apply lequiv_max; assumption).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l3 l4 A' B' @ lmax l1 l2 ])
    by (apply eqty_W; auto using compt_self).
  assert (HBa : [ G ; Γ ⊢[ i ] B[lsingle a] @ l2 ]) by exact (wf_ty_single Hi HB Ha).
  assert (EBa : [ G ; Γ ⊢[ i ] B[lsingle a] ≅ B'[lsingle a'] @ l2 ]).
  { eapply eqty_trans; [apply (wf_ty_func HB (d' := lsingle a')); now apply lsub_eq_single |].
    exact (eqty_single Hi HBB Ha'). }
  apply eqty_pi; auto using lequiv_max.
  eapply wk1_eqty; eauto. apply ext_wf; auto.
Qed.

(** [elim_W]'s facts for a congruence (M13b): the scrutinee's types, the
    motive's contexts, the step's contexts and the step's types. *)
Lemma W_facts {Γ l1 l2 l3 l4 l5 l6 A A' B B' M M'} :
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] wihty l1 l2 l3 A B M @ lmax l2 l3 ] ->
  [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ] /\
  [ G ⊢[ i ] Γ ,, tyW l1 l2 A B @ lmax l1 l2 ≅ Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ] /\
  [ G ⊢[ i ] Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ≅ Γ ,, A' @ l4 ,, wfty l4 l5 A' B' @ lmax l5 (lmax l4 l5) ,, wihty l4 l5 l6 A' B' M' @ lmax l5 l6 ] /\
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3 ⊢[ i ]
      wstepty l1 l2 A B M ≅ wstepty l4 l5 A' B' M' @ l3 ].
Proof using Hi Hv.
  intros H14 H25 H36 HAA HA HA' HBB HB HB' HMM HM HM' HF HI.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (lequiv_wf_l _ _ _ H14) as W1. pose proof (lequiv_wf_l _ _ _ H25) as W2.
  pose proof (lequiv_wf_l _ _ _ H36) as W3.
  pose proof (lequiv_wf_r _ _ _ H14) as W4. pose proof (lequiv_wf_r _ _ _ H25) as W5.
  pose proof (lequiv_wf_r _ _ _ H36) as W6.
  assert (HL : lequiv (gL G) (lmax l1 l2) (lmax l4 l5)) by (apply lequiv_max; assumption).
  assert (WL : lwf (gL G) (lmax l1 l2)) by auto using lwf_max.
  assert (WL' : lwf (gL G) (lmax l4 l5)) by auto using lwf_max.
  assert (HLF : lequiv (gL G) (lmax l2 (lmax l1 l2)) (lmax l5 (lmax l4 l5))) by (apply lequiv_max; assumption).
  assert (HLI : lequiv (gL G) (lmax l2 l3) (lmax l5 l6)) by (apply lequiv_max; assumption).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l4 l5 A' B' @ lmax l1 l2 ])
    by (apply eqty_W; auto using compt_self).
  assert (HW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' @ lmax l4 l5 ])
    by (eapply wft_lconv; [exact (pre_W_r H14 H25 HAA HA' HB') | exact (lequiv_sym _ _ _ HL)]).
  assert (HA'4 : [ G ; Γ ⊢[ i ] A' @ l4 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓA' : [ G ; Γ ,, A' @ l4 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HB'5 : [ G ; Γ ,, A' @ l4 ⊢[ i ] B' @ l5 ])
    by (eapply wft_lconv; [exact (stab_ty Hi HAA H14 HΓA' HB') | now apply lequiv_sym]).
  assert (HB'5A : [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l5 ]) by (eapply wft_lconv; [exact HB' | now apply lequiv_sym]).
  assert (HΓW' : [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HM'6 : [ G ; Γ ,, tyW l4 l5 A' B' @ lmax l4 l5 ⊢[ i ] M' @ l6 ])
    by (eapply wft_lconv; [exact (stab_ty Hi EW HL HΓW' HM') | now apply lequiv_sym]).
  assert (EW2 : [ G ; Γ ,, A @ l1 ,, B @ l2 ⊢[ i ] (tyW l1 l2 A B)⟨↑⟩⟨↑⟩ ≅ (tyW l4 l5 A' B')⟨↑⟩⟨↑⟩ @ lmax l1 l2 ])
    by (eapply wk1_eqty; [ | | eapply wk1_eqty]; eauto; apply ext_wf; auto).
  assert (EF : [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B ≅ wfty l4 l5 A' B' @ lmax l2 (lmax l1 l2) ])
    by (apply eqty_pi; auto).
  pose proof (W_ih_eq H14 H25 H36 HA HB HBB HB' HM HMM HW' EW HF EF) as EI.
  assert (HΘ : [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3 ⊢[ i ] ])
    by (apply ext_wf; [exact HI | apply lwf_max; assumption]).
  pose proof (W_step_eq H14 H25 H36 HA HAA HA'4 HB HBB HB'5 HM HMM EW HF EF HΘ) as ES.
  refine (conj EW (conj _ (conj _ ES))).
  - apply eqc_ext; [apply eqc_refl; exact HΓ | exact HW | exact EW | exact HL].
  - apply eqc_ext; [apply eqc_ext; [apply eqc_ext; [apply eqc_refl; exact HΓ | exact HA | exact HAA | exact H14]
                                  | exact HF | exact EF | exact HLF]
                  | exact HI | exact EI | exact HLI].
Qed.

(** A substitution extended by one more entry. *)
Lemma lsub_wf_cons {Δ d Γ X l h} : [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] h : X[d] @ l ] ->
  [ G ; Δ ⊢[ i ] lcons d h : Γ ,, X @ l ].
Proof using .
  intros [HΔ Hn [Ht Hl] Hv'] Hh. constructor; [exact HΔ | intros [|n]; cbn; [exact (wf_tm_dnf Hh) | apply Hn] | split |].
  - exact Ht.
  - intros n; cbn [clen]. replace (S (clen Γ) + n) with (S (clen Γ + n)) by lia. cbn. apply Hl.
  - intros n T k Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst; cbn.
    + rewrite (ren_subst_ty _ _ _ d); [exact Hh | intros; rewrite rlk_shift1; reflexivity].
    + rewrite (ren_subst_ty _ _ _ d); [exact (Hv' _ _ _ Hm) | intros; rewrite rlk_shift1; reflexivity].
Qed.

(** The telescope weakened past one local, under its binders. *)
Lemma W_fty_ren l l' (A B : ty) : (wfty l l' A B)⟨rlift ↑⟩ = wfty l l' A⟨↑⟩ B⟨rlift ↑⟩.
Proof using . wk_eqW. Qed.
Lemma W_ihty_ren l l' l'' (A B M : ty) :
  (wihty l l' l'' A B M)⟨rlift (rlift ↑)⟩ = wihty l l' l'' A⟨↑⟩ B⟨rlift ↑⟩ M⟨rlift ↑⟩.
Proof using . wk_eqW. Qed.
Lemma W_step_ren l l' (A B M : ty) :
  (wstepty l l' A B M)⟨rlift (rlift (rlift ↑))⟩ = wstepty l l' A⟨↑⟩ B⟨rlift ↑⟩ M⟨rlift ↑⟩.
Proof using . wk_eqW. Qed.

(** The synthesized induction hypothesis is typed at the [ih] entry's
    instance. *)
Lemma W_IH_body_wf {Γ l l' l'' A B M c a f} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l''
      ⊢[ i ] c : wstepty l l' A B M @ l'' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] f : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ] ->
  [ G ; Γ ,, B[lsingle a] @ l' ⊢[ i ] wbody l l' l'' A B M c a f : wcod l l' A B M a f @ l'' ].
Proof using Hi Hv.
  intros Hl Hl' Hl'' HA HB HM Hc Ha Hf. 
  assert (WL : lwf (gL G) (lmax l l')) by auto using lwf_max.
  assert (HW : [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ]) by (apply wft_W; auto using compt_self).
  assert (HBa : [ G ; Γ ⊢[ i ] B[lsingle a] @ l' ]) by exact (wf_ty_single Hi HB Ha).
  assert (HΓ1 : [ G ; Γ ,, B[lsingle a] @ l' ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HW1 : [ G ; Γ ,, B[lsingle a] @ l' ⊢[ i ] (tyW l l' A B)⟨↑⟩ @ lmax l l' ]) by (eapply wk1_ty; eauto).
  assert (HA1 : [ G ; Γ ,, B[lsingle a] @ l' ⊢[ i ] A⟨↑⟩ @ l ]) by (eapply wk1_ty; eauto).
  assert (HΓ1A : [ G ; Γ ,, B[lsingle a] @ l' ,, A⟨↑⟩ @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HB1 : [ G ; Γ ,, B[lsingle a] @ l' ,, A⟨↑⟩ @ l ⊢[ i ] B⟨rlift ↑⟩ @ l' ]) by exact (wk_under_ty HΓ1A HB).
  assert (HM1 : [ G ; Γ ,, B[lsingle a] @ l' ,, (tyW l l' A B)⟨↑⟩ @ lmax l l' ⊢[ i ] M⟨rlift ↑⟩ @ l'' ])
    by exact (wk_under_ty (ext_wf HW1 WL) HM).
  pose proof (W_fty_wf Hl Hl' HW1 HB1) as HF1.
  assert (HΓ1AF : [ G ; Γ ,, B[lsingle a] @ l' ,, A⟨↑⟩ @ l ,, wfty l l' A⟨↑⟩ B⟨rlift ↑⟩ @ lmax l' (lmax l l') ⊢[ i ] ])
    by (apply ext_wf; auto using lwf_max).
  pose proof (W_ih_wf Hl Hl' Hl'' HW1 HB1 HM1 HΓ1AF (eqty_refl' HF1) (lequiv_refl _ _ (lwf_max Hl' WL))) as HI1.
  apply wf_elimW; auto using compt_self.
  - (* the step, weakened under the telescope *)
    rewrite <- W_step_ren. eapply weakening_r; eauto.
    + repeat (eapply wkr_up'; [ | first [reflexivity | symmetry; first [apply W_fty_ren | apply W_ihty_ren]]]).
      apply wkr_shift1.
    + apply ext_wf; auto using lwf_max.
  - (* the scrutinee: the children at the position *)
    eapply wf_tm_retype; [apply wf_app; auto | exact (W_E8 (tyW l l' A B))].
    + eapply wk1_ty; eauto.
    + apply wk_under_ty; [apply ext_wf; [eapply wk1_ty; eauto | exact Hl'] | exact HW1].
    + exact (wk1_tm G i Hi _ _ _ _ _ _ HΓ1 Hf).
    + apply wf_var; [now rewrite Hi | constructor].
Qed.

Lemma W_IH_wf {Γ l l' l'' A B M c a f} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l''
      ⊢[ i ] c : wstepty l l' A B M @ l'' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] f : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ] ->
  [ G ; Γ ⊢[ i ] wIH l l' l'' A B M c a f : (wihty l l' l'' A B M)[lsingle2 a f] @ lmax l' l'' ].
Proof using Hi Hv.
  intros Hl Hl' Hl'' HA HB HM Hc Ha Hf. rewrite W_E4. unfold wIH.
  apply wf_lam; auto; [exact (wf_ty_single Hi HB Ha) |].
  exact (W_IH_body_wf Hl Hl' Hl'' HA HB HM Hc Ha Hf).
Qed.

(** ... and respects equal pieces (the validity of [elim_W]'s β, M13a). *)
Lemma W_IH_body_eq {Γ l l' l'' l4 l5 l6 A A' B B' M M' c c' a a' f f'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  lequiv (gL G) l l4 -> lequiv (gL G) l' l5 -> lequiv (gL G) l'' l6 ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] -> [ G ; Γ ,, A @ l ⊢[ i ] B ≅ B' @ l' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M ≅ M' @ l'' ] ->
  [ G ; Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l''
      ⊢[ i ] c ≅ c' : wstepty l l' A B M @ l'' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] f ≅ f' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ] ->
  [ G ; Γ ,, B[lsingle a] @ l' ⊢[ i ] wbody l l' l'' A B M c a f ≅ wbody l4 l5 l6 A' B' M' c' a' f'
      : wcod l l' A B M a f @ l'' ].
Proof using Hi Hv.
  intros Hl Hl' Hl'' H14 H25 H36 HA HAA HB HBB HM HMM Hcc Ha Ha' Haa Hff.
  assert (WL : lwf (gL G) (lmax l l')) by auto using lwf_max.
  assert (HW : [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ]) by (apply wft_W; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyW l l' A B ≅ tyW l4 l5 A' B' @ lmax l l' ])
    by (apply eqty_W; auto using compt_self).
  assert (HBa : [ G ; Γ ⊢[ i ] B[lsingle a] @ l' ]) by exact (wf_ty_single Hi HB Ha).
  assert (EBa : [ G ; Γ ⊢[ i ] B[lsingle a] ≅ B'[lsingle a'] @ l' ]).
  { eapply eqty_trans; [apply (wf_ty_func HB (d' := lsingle a')); now apply lsub_eq_single|].
    exact (eqty_single Hi HBB Ha'). }
  assert (HΓ1 : [ G ; Γ ,, B[lsingle a] @ l' ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HW1 : [ G ; Γ ,, B[lsingle a] @ l' ⊢[ i ] (tyW l l' A B)⟨↑⟩ @ lmax l l' ]) by (eapply wk1_ty; eauto).
  assert (HA1 : [ G ; Γ ,, B[lsingle a] @ l' ⊢[ i ] A⟨↑⟩ @ l ]) by (eapply wk1_ty; eauto).
  assert (HΓ1A : [ G ; Γ ,, B[lsingle a] @ l' ,, A⟨↑⟩ @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HB1 : [ G ; Γ ,, B[lsingle a] @ l' ,, A⟨↑⟩ @ l ⊢[ i ] B⟨rlift ↑⟩ @ l' ]) by exact (wk_under_ty HΓ1A HB).
  assert (HΓ1W : [ G ; Γ ,, B[lsingle a] @ l' ,, (tyW l l' A B)⟨↑⟩ @ lmax l l' ⊢[ i ] ]) by exact (ext_wf HW1 WL).
  assert (HM1 : [ G ; Γ ,, B[lsingle a] @ l' ,, (tyW l l' A B)⟨↑⟩ @ lmax l l' ⊢[ i ] M⟨rlift ↑⟩ @ l'' ])
    by exact (wk_under_ty HΓ1W HM).
  pose proof (W_fty_wf Hl Hl' HW1 HB1) as HF1.
  assert (HΓ1AF : [ G ; Γ ,, B[lsingle a] @ l' ,, A⟨↑⟩ @ l ,, wfty l l' A⟨↑⟩ B⟨rlift ↑⟩ @ lmax l' (lmax l l') ⊢[ i ] ])
    by (apply ext_wf; auto using lwf_max).
  pose proof (W_ih_wf Hl Hl' Hl'' HW1 HB1 HM1 HΓ1AF (eqty_refl' HF1) (lequiv_refl _ _ (lwf_max Hl' WL))) as HI1.
  apply eqtm_elimW; auto using compt_self.
  - eapply wk1_eqty; eauto.
  - exact (wk_under_eqty HΓ1A HBB).
  - exact (wk_under_eqty HΓ1W HMM).
  - (* the steps, weakened under the telescope *)
    rewrite <- W_step_ren. eapply weakening_r; eauto.
    + repeat (eapply wkr_up'; [ | first [reflexivity | symmetry; first [apply W_fty_ren | apply W_ihty_ren]]]).
      apply wkr_shift1.
    + apply ext_wf; auto using lwf_max.
  - (* the scrutinees: the children at the position *)
    eapply eq_tm_retype; [apply eqtm_app; auto | exact (W_E8 (tyW l l' A B))].
    + now apply lequiv_max.
    + eapply wk1_ty; eauto.
    + eapply wk1_eqty; eauto.
    + apply wk_under_eqty; [apply ext_wf; [eapply wk1_ty; eauto | exact Hl'] | eapply wk1_eqty; eauto].
    + exact (wk1_eqtm G i Hi _ _ _ _ _ _ _ HΓ1 Hff).
    + apply eqtm_refl, wf_var; [now rewrite Hi | constructor].
Qed.

Lemma W_IH_eq {Γ l l' l'' l4 l5 l6 A A' B B' M M' c c' a a' f f'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  lequiv (gL G) l l4 -> lequiv (gL G) l' l5 -> lequiv (gL G) l'' l6 ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] -> [ G ; Γ ,, A @ l ⊢[ i ] B ≅ B' @ l' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M ≅ M' @ l'' ] ->
  [ G ; Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l''
      ⊢[ i ] c ≅ c' : wstepty l l' A B M @ l'' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] f ≅ f' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ] ->
  [ G ; Γ ⊢[ i ] wIH l l' l'' A B M c a f ≅ wIH l4 l5 l6 A' B' M' c' a' f'
      : (wihty l l' l'' A B M)[lsingle2 a f] @ lmax l' l'' ].
Proof using Hi Hv.
  intros Hl Hl' Hl'' H14 H25 H36 HA HAA HB HBB HM HMM Hcc Ha Ha' Haa Hff.
  rewrite W_E4. unfold wIH.
  apply eqtm_lam; auto; [exact (wf_ty_single Hi HB Ha) | |].
  - eapply eqty_trans; [apply (wf_ty_func HB (d' := lsingle a')); now apply lsub_eq_single|].
    exact (eqty_single Hi HBB Ha').
  - exact (W_IH_body_eq Hl Hl' Hl'' H14 H25 H36 HA HAA HB HBB HM HMM Hcc Ha Ha' Haa Hff).
Qed.

Lemma pre_elimW_beta {Γ l l' l'' A B M c a f} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l''
      ⊢[ i ] c : wstepty l l' A B M @ l'' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] f : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ] ->
  [ G ; Γ ⊢[ i ] c[lsingle3 a f (wIH l l' l'' A B M c a f)] : M[lsingle (tmSup l l' A B a f)] @ l'' ].
Proof using Hi Hv.
  intros Hl Hl' Hl'' HA HB HM Hc Ha Hf.
  pose proof (ctx_of_wf_tm Hi Ha) as HΓ.
  rewrite <- (W_E6 l l' A B M a f (wIH l l' l'' A B M c a f) (wf_ty_nf HA) (wf_ty_nf HB)).
  eapply (wf_tm_subst Hi Hc). unfold lsingle3, lsingle2.
  apply lsub_wf_cons; [apply lsub_wf_cons; [apply lsub_wf_cons |] |].
  - eapply lsub_wf_id; eauto.
  - rewrite nf_id_ty by exact (wf_ty_nf HA). exact Ha.
  - change (lcons (lshift 0) a) with (lsingle a). rewrite W_E5. exact Hf.
  - change (lcons (lcons (lshift 0) a) f) with (lsingle2 a f). exact (W_IH_wf Hl Hl' Hl'' HA HB HM Hc Ha Hf).
Qed.

Ltac teq_core := repeat first [ rewrite ren_as_r2l_ty | rewrite ren_as_r2l ];
  repeat first [ rewrite subst_comp_ty | rewrite subst_comp ];
  first [ apply subst_ext_ty | apply subst_ext
        | apply subst_id_ty; [assumption|] | apply subst_id; [assumption|]
        | symmetry; apply subst_id_ty; [assumption|] | symmetry; apply subst_id; [assumption|] ];
  intros [|[|[|[|[|[|[|[|?n]]]]]]]]; unfold lsucc; pw;
  try solve [apply ren_as_r2l | symmetry; apply ren_as_r2l].

(** ** The [nth] schema (M15a) *)

Lemma nth_E0 l (T : ty) : nfty T ->
  (nthMot l T)[lsingle zero] = tyPi l l (tyVec l T zero) (tyPi lzero l (tyFin zero) T⟨↑⟩⟨↑⟩).
Proof using . intros NT. unfold nthMot. push_subst. f_equal; [f_equal|f_equal]; teq_core. Qed.
Lemma nth_ES l (T : ty) :
  (nthMot l T)[lsucc] = tyPi l l (tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1))) (tyPi lzero l (tyFin (succ (var 2))) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩).
Proof using . unfold nthMot. push_subst. f_equal; [f_equal|f_equal]; teq_core. Qed.
Lemma nth_Ek l (T : ty) k : nfty T -> nftm k ->
  (nthMot l T)[lsingle k] = tyPi l l (tyVec l T k) (tyPi lzero l (tyFin k⟨↑⟩) T⟨↑⟩⟨↑⟩).
Proof using . intros NT Nk. unfold nthMot. push_subst. f_equal; [f_equal|f_equal]; try teq_core; pw. Qed.
Lemma nth_Ecs l (T : ty) k cs : nfty T -> nftm k ->
  (tyPi lzero l (tyFin k⟨↑⟩) T⟨↑⟩⟨↑⟩)[lsingle cs] = tyPi lzero l (tyFin k) T⟨↑⟩.
Proof using . intros NT Nk. push_subst. f_equal; [f_equal|]; teq_core. Qed.

Lemma lq_0l {l} : lwf (gL G) l -> lequiv (gL G) (lmax lzero l) l.
Proof using . intros Hl. eapply lequiv_trans; [apply lmax_comm; cbn; auto | apply lmax_zero; auto]. Qed.
Lemma lq_mot {l} : lwf (gL G) l -> lequiv (gL G) (lmax l (lmax lzero l)) l.
Proof using .
  intros Hl. eapply lequiv_trans; [apply lequiv_max; [apply lequiv_refl, Hl | apply lq_0l, Hl] | apply lmax_idem, Hl].
Qed.
Lemma lq_ll {l} : lwf (gL G) l -> lequiv (gL G) (lmax l l) l.
Proof using . apply lmax_idem. Qed.

(** Weakening by several locals at once. *)
Ltac wkn H := first [ exact H | eapply (wk1_ty G i Hi); [eassumption | wkn H] | eapply (wk1_tm G i Hi); [eassumption | wkn H] ].
Ltac wvar := eapply wf_tm_retype; [eapply wf_var; [rewrite Hi; eassumption | repeat constructor] | cbn; try reflexivity].
Ltac wvar_raw := eapply wf_var; [rewrite Hi; eassumption | repeat constructor].

Lemma nth_mot_wf {Γ l T} : lwf (gL G) l -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] nthMot l T @ l ].
Proof using Hi Hv.
  intros Hl HT. pose proof (ctx_of_wf_ty Hi HT) as H0.
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply ext_wf; [apply wft_nat; auto; now rewrite Hi | cbn; auto]).
  assert (HV : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] tyVec l T⟨↑⟩ (var 0) @ l ]) by (apply wft_vec; auto; [wkn HT | wvar]).
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HF : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ⊢[ i ] tyFin (var 1) @ lzero ])
    by (apply wft_fin; auto; wvar).
  assert (H3 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ,, tyFin (var 1) @ lzero ⊢[ i ] ])
    by (apply ext_wf; cbn; auto).
  unfold nthMot. eapply wft_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wft_pi; auto. eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wft_pi; cbn; auto. wkn HT.
Qed.

Lemma nth_base_wf {Γ l T} : lwf (gL G) l -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ⊢[ i ] nthBase l T : (nthMot l T)[lsingle zero] @ l ].
Proof using Hi Hv.
  intros Hl HT. pose proof (ctx_of_wf_ty Hi HT) as H0.
  rewrite nth_E0 by exact (wf_ty_nf HT). unfold nthBase.
  assert (Hz : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; auto; now rewrite Hi).
  assert (HV : [ G ; Γ ⊢[ i ] tyVec l T zero @ l ]) by (apply wft_vec; auto).
  assert (H1 : [ G ; Γ ,, tyVec l T zero @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HF : [ G ; Γ ,, tyVec l T zero @ l ⊢[ i ] tyFin zero @ lzero ])
    by (apply wft_fin; auto; apply wf_zero; auto; now rewrite Hi).
  assert (H2 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (HE : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢[ i ] tyEmpty lzero @ lzero ])
    by (apply wft_empty; cbn; auto; now rewrite Hi).
  assert (H3 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero ⊢[ i ] ])
    by (apply ext_wf; cbn; auto).
  eapply wf_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wf_lam; auto. eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; cbn; auto.
  eapply wf_tm_retype; [apply wf_elimEmpty; cbn; auto; [wkn HT|] | teq_core].
  eapply conv_tm'; [wvar|]. apply eqty_sym, eqty_fin_zero; [apply compt_self | now rewrite Hi].
Qed.

Lemma nth_step_wf {Γ l T} : lwf (gL G) l -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, nthMot l T @ l ⊢[ i ] nthStep l T : (nthMot l T)[lsucc] @ l ].
Proof using Hi Hv.
  intros Hl HT. pose proof (ctx_of_wf_ty Hi HT) as H0.
  pose proof (nth_mot_wf Hl HT) as HM. pose proof (ctx_of_wf_ty Hi HM) as H1.
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, nthMot l T @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  rewrite nth_ES. unfold nthStep.
  set (Δ0 := Γ ,, tyNat @ lzero ,, nthMot l T @ l) in *.
  assert (HV : [ G ; Δ0 ⊢[ i ] tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ])
    by (apply wft_vec; auto; [wkn HT | apply wf_succ; auto; wvar]).
  assert (H3 : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HF : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ⊢[ i ] tyFin (succ (var 2)) @ lzero ])
    by (apply wft_fin; auto; apply wf_succ; auto; wvar).
  set (Δ1 := Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ,, tyFin (succ (var 2)) @ lzero).
  assert (H4 : [ G ; Δ1 ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (Hk : [ G ; Δ1 ⊢[ i ] var 3 : tyNat @ lzero ]) by wvar.
  assert (HU : [ G ; Δ1 ⊢[ i ] tyUnit lzero @ lzero ]) by (apply wft_unit; cbn; auto; now rewrite Hi).
  assert (HFk : [ G ; Δ1 ⊢[ i ] tyFin (var 3) @ lzero ]) by (apply wft_fin; auto).
  assert (HS : [ G ; Δ1 ⊢[ i ] tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ])
    by (apply wft_sum; cbn; auto).
  assert (H5 : [ G ; Δ1 ,, tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ⊢[ i ] ])
    by (apply ext_wf; cbn; auto).
  assert (H5u : [ G ; Δ1 ,, tyUnit lzero @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (H5f : [ G ; Δ1 ,, tyFin (var 3) @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  (* the tuple, as a pair, in either branch *)
  assert (Hcs : forall X, [ G ; Δ1 ,, X @ lzero ⊢[ i ] ] ->
            [ G ; Δ1 ,, X @ lzero ⊢[ i ] var 2 : tySig l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) @ lmax l l ]
            /\ [ G ; Δ1 ,, X @ lzero ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]
            /\ [ G ; Δ1 ,, X @ lzero ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ⊢[ i ] tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5) @ l ]).
  { intros X HX. assert (HT5 : [ G ; Δ1 ,, X @ lzero ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by wkn HT.
    assert (HX5 : [ G ; Δ1 ,, X @ lzero ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ⊢[ i ] ]) by (apply ext_wf; auto).
    assert (Hk4 : [ G ; Δ1 ,, X @ lzero ⊢[ i ] var 4 : tyNat @ lzero ]) by wvar.
    split; [|split; [exact HT5|]].
    - eapply wf_lconv; [| apply lq_ll, Hl]. eapply conv_tm'; [wvar|].
      apply eqty_sym, eqty_vec_succ; auto using compt_self.
    - apply wft_vec; auto; [wkn HT | wvar]. }
  eapply wf_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wf_lam; auto. eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; cbn; auto.
  eapply wf_tm_retype; [apply wf_case; cbn; auto | teq_core].
  - wkn HT.
  - (* the head *)
    destruct (Hcs _ H5u) as (Hp & HT5 & HV5).
    eapply wf_tm_retype; [apply wf_fst; eauto | teq_core].
  - (* the tail, recursively *)
    destruct (Hcs _ H5f) as (Hp & HT5 & HV5).
    set (Δ2 := Δ1 ,, tyFin (var 3) @ lzero) in *.
    assert (Hk4 : [ G ; Δ2 ⊢[ i ] var 4 : tyNat @ lzero ]) by wvar.
    assert (HF4 : [ G ; Δ2 ⊢[ i ] tyFin (var 4) @ lzero ]) by (apply wft_fin; auto).
    assert (H6 : [ G ; Δ2 ,, tyFin (var 4) @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
    assert (HV4 : [ G ; Δ2 ⊢[ i ] tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ]) by (apply wft_vec; auto).
    assert (H7 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ⊢[ i ] ]) by (apply ext_wf; auto).
    assert (HF5 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ⊢[ i ] tyFin (var 5) @ lzero ])
      by (apply wft_fin; auto; wvar).
    assert (H8 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ,, tyFin (var 5) @ lzero ⊢[ i ] ])
      by (apply ext_wf; cbn; auto).
    eapply wf_tm_retype; [apply wf_app; cbn; auto | teq_core].
    + wkn HT.
    + eapply wf_lconv; [| apply lq_0l, Hl].
      eapply wf_tm_retype; [apply wf_app; auto | push_subst; f_equal; try teq_core; pw].
      * eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl]. apply wft_pi; cbn; auto. wkn HT.
      * eapply wf_lconv; [| apply lq_ll, Hl].
        wvar. unfold nthMot. push_ren. f_equal; f_equal; teq_core.
      * eapply wf_tm_retype; [apply wf_snd; eauto | push_subst; f_equal; try teq_core; pw].
    + wvar.
  - eapply wf_lconv; [| apply lq_ll; cbn; auto]. eapply conv_tm'; [wvar|].
    apply eqty_sym, eqty_fin_succ; auto using compt_self.
Qed.

Lemma nth_wf {Γ l T k cs j} : lwf (gL G) l -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ⊢[ i ] k : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] cs : tyVec l T k @ l ] ->
  [ G ; Γ ⊢[ i ] j : tyFin k @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmNth l T k cs j : T @ l ].
Proof using Hi Hv.
  intros Hl HT Hk Hcs Hj. pose proof (ctx_of_wf_ty Hi HT) as H0.
  pose proof (wf_ty_nf HT) as NT. pose proof (wf_tm_nf Hk) as Nk.
  assert (HV : [ G ; Γ ⊢[ i ] tyVec l T k @ l ]) by (apply wft_vec; auto).
  assert (H1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin k @ lzero ]) by (apply wft_fin; auto).
  assert (H2 : [ G ; Γ ,, tyFin k @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (Hk1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] k⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [wkn Hk | reflexivity]).
  assert (HF1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] tyFin k⟨↑⟩ @ lzero ]) by (apply wft_fin; auto).
  assert (H3 : [ G ; Γ ,, tyVec l T k @ l ,, tyFin k⟨↑⟩ @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  unfold tmNth.
  eapply wf_tm_retype; [apply wf_app; cbn; auto | teq_core].
  - wkn HT.
  - eapply wf_lconv; [| apply lq_0l, Hl].
    eapply wf_tm_retype; [apply wf_app; auto | apply nth_Ecs; assumption].
    + eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl]. apply wft_pi; cbn; auto. wkn HT.
    + eapply wf_lconv; [| apply lq_ll, Hl].
      rewrite <- nth_Ek by assumption.
      apply wf_natrec; auto using nth_mot_wf, nth_base_wf, nth_step_wf.
Qed.

Ltac wkne H := first [ exact H | eapply (wk1_eqty G i Hi); [eassumption | wkne H]
                     | eapply (wk1_eqtm G i Hi); [eassumption | wkne H] ].
Ltac wvar_eq := apply eqtm_refl; wvar.
Ltac sides := try solve [ cbn; auto | apply lequiv_refl; cbn; auto ].

Lemma nth_mot_eq {Γ l l' T T'} : lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] nthMot l T ≅ nthMot l' T' @ l ].
Proof using Hi Hv.
  intros H HT HTT. pose proof (lequiv_wf_l _ _ _ H) as Hl. pose proof (ctx_of_wf_ty Hi HT) as H0.
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply ext_wf; [apply wft_nat; auto; now rewrite Hi | cbn; auto]).
  assert (HV : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] tyVec l T⟨↑⟩ (var 0) @ l ]) by (apply wft_vec; auto; [wkn HT | wvar]).
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HF : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ⊢[ i ] tyFin (var 1) @ lzero ])
    by (apply wft_fin; auto; wvar).
  assert (H3 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ,, tyFin (var 1) @ lzero ⊢[ i ] ])
    by (apply ext_wf; cbn; auto).
  unfold nthMot. eapply eqty_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply eqty_pi; auto.
  - apply eqty_vec; auto; [wkn HT | wkne HTT | wvar_eq].
  - eapply eqty_lconv; [| apply lequiv_sym, lq_0l, Hl].
    apply eqty_pi; sides; [apply eqty_refl; exact HF | wkne HTT].
Qed.

Lemma nth_base_eq {Γ l l' T T'} : lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] nthBase l T ≅ nthBase l' T' : (nthMot l T)[lsingle zero] @ l ].
Proof using Hi Hv.
  intros H HT HTT. pose proof (lequiv_wf_l _ _ _ H) as Hl. pose proof (ctx_of_wf_ty Hi HT) as H0.
  rewrite nth_E0 by exact (wf_ty_nf HT). unfold nthBase.
  assert (Hz : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; auto; now rewrite Hi).
  assert (HV : [ G ; Γ ⊢[ i ] tyVec l T zero @ l ]) by (apply wft_vec; auto).
  assert (H1 : [ G ; Γ ,, tyVec l T zero @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HF : [ G ; Γ ,, tyVec l T zero @ l ⊢[ i ] tyFin zero @ lzero ])
    by (apply wft_fin; auto; apply wf_zero; auto; now rewrite Hi).
  assert (H2 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (HE : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢[ i ] tyEmpty lzero @ lzero ])
    by (apply wft_empty; cbn; auto; now rewrite Hi).
  assert (H3 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero ⊢[ i ] ])
    by (apply ext_wf; cbn; auto).
  eapply eqtm_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply eqtm_lam; auto; [apply eqty_vec; auto; apply eqtm_refl, Hz |].
  eapply eqtm_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply eqtm_lam; sides; [apply eqty_refl, HF |].
  eapply eq_tm_retype; [apply eqtm_elimEmpty; sides; [wkn HT | wkne HTT |] | teq_core].
  apply eqtm_refl. eapply conv_tm'; [wvar|]. apply eqty_sym, eqty_fin_zero; [apply compt_self | now rewrite Hi].
Qed.

Lemma nth_step_eq {Γ l l' T T'} : lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, nthMot l T @ l ⊢[ i ] nthStep l T ≅ nthStep l' T' : (nthMot l T)[lsucc] @ l ].
Proof using Hi Hv.
  intros H HT HTT. pose proof (lequiv_wf_l _ _ _ H) as Hl. pose proof (ctx_of_wf_ty Hi HT) as H0.
  pose proof (nth_mot_wf Hl HT) as HM. pose proof (ctx_of_wf_ty Hi HM) as H1.
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, nthMot l T @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  rewrite nth_ES. unfold nthStep.
  set (Δ0 := Γ ,, tyNat @ lzero ,, nthMot l T @ l) in *.
  assert (HV : [ G ; Δ0 ⊢[ i ] tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ])
    by (apply wft_vec; auto; [wkn HT | apply wf_succ; auto; wvar]).
  assert (H3 : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HF : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ⊢[ i ] tyFin (succ (var 2)) @ lzero ])
    by (apply wft_fin; auto; apply wf_succ; auto; wvar).
  set (Δ1 := Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ,, tyFin (succ (var 2)) @ lzero).
  assert (H4 : [ G ; Δ1 ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (Hk : [ G ; Δ1 ⊢[ i ] var 3 : tyNat @ lzero ]) by wvar.
  assert (HU : [ G ; Δ1 ⊢[ i ] tyUnit lzero @ lzero ]) by (apply wft_unit; cbn; auto; now rewrite Hi).
  assert (HFk : [ G ; Δ1 ⊢[ i ] tyFin (var 3) @ lzero ]) by (apply wft_fin; auto).
  assert (HS : [ G ; Δ1 ⊢[ i ] tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ])
    by (apply wft_sum; cbn; auto).
  assert (H5 : [ G ; Δ1 ,, tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ⊢[ i ] ])
    by (apply ext_wf; cbn; auto).
  assert (H5u : [ G ; Δ1 ,, tyUnit lzero @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (H5f : [ G ; Δ1 ,, tyFin (var 3) @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (Hcs : forall X, [ G ; Δ1 ,, X @ lzero ⊢[ i ] ] ->
            [ G ; Δ1 ,, X @ lzero ⊢[ i ] var 2 : tySig l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) @ lmax l l ]
            /\ [ G ; Δ1 ,, X @ lzero ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]
            /\ [ G ; Δ1 ,, X @ lzero ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ ≅ T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]
            /\ [ G ; Δ1 ,, X @ lzero ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ⊢[ i ]
                 tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5) ≅ tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5) @ l ]).
  { intros X HX. assert (HT5 : [ G ; Δ1 ,, X @ lzero ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by wkn HT.
    assert (HX5 : [ G ; Δ1 ,, X @ lzero ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ⊢[ i ] ]) by (apply ext_wf; auto).
    assert (Hk4 : [ G ; Δ1 ,, X @ lzero ⊢[ i ] var 4 : tyNat @ lzero ]) by wvar.
    split; [|split; [exact HT5|split; [wkne HTT|]]].
    - eapply wf_lconv; [| apply lq_ll, Hl]. eapply conv_tm'; [wvar|].
      apply eqty_sym, eqty_vec_succ; auto using compt_self.
    - apply eqty_vec; auto; [wkn HT | wkne HTT | wvar_eq]. }
  eapply eqtm_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply eqtm_lam; auto; [apply eqty_vec; auto; [wkn HT | wkne HTT | apply eqtm_refl, wf_succ; auto; wvar] |].
  eapply eqtm_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply eqtm_lam; sides; [apply eqty_refl, HF |].
  eapply eq_tm_retype; [apply eqtm_case; sides | teq_core].
  all: try solve [ apply eqty_refl; assumption | assumption | wkn HT | wkne HTT ].
  - (* the head *)
    destruct (Hcs _ H5u) as (Hp & HT5 & HTT5 & HVV5).
    eapply eq_tm_retype; [apply eqtm_fst; sides; apply eqtm_refl, Hp | teq_core].
  - (* the tail, recursively *)
    destruct (Hcs _ H5f) as (Hp & HT5 & HTT5 & HVV5).
    set (Δ2 := Δ1 ,, tyFin (var 3) @ lzero) in *.
    assert (Hk4 : [ G ; Δ2 ⊢[ i ] var 4 : tyNat @ lzero ]) by wvar.
    assert (HF4 : [ G ; Δ2 ⊢[ i ] tyFin (var 4) @ lzero ]) by (apply wft_fin; auto).
    assert (H6 : [ G ; Δ2 ,, tyFin (var 4) @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
    assert (HV4 : [ G ; Δ2 ⊢[ i ] tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ]) by (apply wft_vec; auto).
    assert (H7 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ⊢[ i ] ]) by (apply ext_wf; auto).
    assert (HF5 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ⊢[ i ] tyFin (var 5) @ lzero ])
      by (apply wft_fin; auto; wvar).
    assert (H8 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ,, tyFin (var 5) @ lzero ⊢[ i ] ])
      by (apply ext_wf; cbn; auto).
    eapply eq_tm_retype; [apply eqtm_app; sides | teq_core].
    + apply eqty_refl, HF4.
    + wkne HTT.
    + eapply eqtm_lconv; [| apply lq_0l, Hl].
      eapply eq_tm_retype; [apply eqtm_app; sides | push_subst; f_equal; try teq_core; pw].
      * apply eqty_vec; auto; first [wkne HTT | wvar_eq].
      * eapply eqty_lconv; [| apply lequiv_sym, lq_0l, Hl]. apply eqty_pi; sides; [apply eqty_refl, HF5 | wkne HTT].
      * eapply eqtm_lconv; [| apply lq_ll, Hl].
        apply eqtm_refl. wvar. unfold nthMot. push_ren. f_equal; f_equal; teq_core.
      * eapply eq_tm_retype; [apply eqtm_snd; sides; apply eqtm_refl, Hp | push_subst; f_equal; try teq_core; pw].
    + wvar_eq.
  - apply eqtm_refl. eapply wf_lconv; [| apply lq_ll; cbn; auto]. eapply conv_tm'; [wvar|].
    apply eqty_sym, eqty_fin_succ; auto using compt_self.
Qed.

Lemma nth_eq {Γ l l' T T' k k' cs cs' j j'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] k : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] k ≅ k' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] cs ≅ cs' : tyVec l T k @ l ] ->
  [ G ; Γ ⊢[ i ] j ≅ j' : tyFin k @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmNth l T k cs j ≅ tmNth l' T' k' cs' j' : T @ l ].
Proof using Hi Hv.
  intros H HT HTT Hk Hkk Hcs Hj. pose proof (lequiv_wf_l _ _ _ H) as Hl. pose proof (ctx_of_wf_ty Hi HT) as H0.
  pose proof (wf_ty_nf HT) as NT. pose proof (wf_tm_nf Hk) as Nk.
  assert (HV : [ G ; Γ ⊢[ i ] tyVec l T k @ l ]) by (apply wft_vec; auto).
  assert (H1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin k @ lzero ]) by (apply wft_fin; auto).
  assert (H2 : [ G ; Γ ,, tyFin k @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (Hk1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] k⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [wkn Hk | reflexivity]).
  assert (Hkk1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] k⟨↑⟩ ≅ k'⟨↑⟩ : tyNat @ lzero ])
    by (eapply eq_tm_retype; [wkne Hkk | reflexivity]).
  assert (HF1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] tyFin k⟨↑⟩ @ lzero ]) by (apply wft_fin; auto).
  assert (H3 : [ G ; Γ ,, tyVec l T k @ l ,, tyFin k⟨↑⟩ @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  unfold tmNth.
  eapply eq_tm_retype; [apply eqtm_app; sides | teq_core].
  - apply eqty_fin; auto.
  - wkne HTT.
  - eapply eqtm_lconv; [| apply lq_0l, Hl].
    eapply eq_tm_retype; [apply eqtm_app; sides | apply nth_Ecs; assumption].
    + apply eqty_vec; auto.
    + eapply eqty_lconv; [| apply lequiv_sym, lq_0l, Hl]. apply eqty_pi; sides; [apply eqty_fin; auto | wkne HTT].
    + eapply eqtm_lconv; [| apply lq_ll, Hl].
      rewrite <- nth_Ek by assumption.
      apply eqtm_natrec; auto using nth_mot_wf, nth_mot_eq, nth_base_eq, nth_step_eq.
Qed.

(** ** Finitary well-founded trees (M15a) *)

Lemma wk_under_tm {Γ X Y t T lx ly k} : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] t : T @ k ] -> [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] t⟨rlift ↑⟩ : T⟨rlift ↑⟩ @ k ].
Proof using Hi. intros HΔ HT. eapply weakening_r; eauto. apply wkr_up, wkr_shift1. Qed.
Lemma wk_under_eqtm {Γ X Y t t' T lx ly k} : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] t ≅ t' : T @ k ] ->
  [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] t⟨rlift ↑⟩ ≅ t'⟨rlift ↑⟩ : T⟨rlift ↑⟩ @ k ].
Proof using Hi. intros HΔ HT. eapply weakening_r; eauto. apply wkr_up, wkr_shift1. Qed.
Lemma wk_under3_tm {Γ X Y Z X0 lx ly lz l0 t T k} : [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] X0 @ l0 ] -> lwf (gL G) l0 -> [ G ; Γ ,, X0 @ l0 ⊢[ i ] t : T @ k ] ->
  [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ,, X0⟨↑⟩⟨↑⟩⟨↑⟩ @ l0 ⊢[ i ]
      t⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ : T⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ k ].
Proof using Hi.
  intros H HX Hl HT. pose proof (ctx_pre H) as H2. pose proof (ctx_pre H2) as H1.
  apply wk_under_tm; [apply ext_wf; [exact (wk3_ty H HX) | exact Hl]|].
  apply wk_under_tm; [apply ext_wf; [eapply wk1_ty; eauto; eapply wk1_ty; eauto | exact Hl]|].
  apply wk_under_tm; [apply ext_wf; [eapply wk1_ty; eauto | exact Hl]|]. exact HT.
Qed.
Lemma wk_under3_eqtm {Γ X Y Z X0 lx ly lz l0 t t' T k} : [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] X0 @ l0 ] -> lwf (gL G) l0 -> [ G ; Γ ,, X0 @ l0 ⊢[ i ] t ≅ t' : T @ k ] ->
  [ G ; Γ ,, X @ lx ,, Y @ ly ,, Z @ lz ,, X0⟨↑⟩⟨↑⟩⟨↑⟩ @ l0 ⊢[ i ]
      t⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ ≅ t'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ : T⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ k ].
Proof using Hi.
  intros H HX Hl HT. pose proof (ctx_pre H) as H2. pose proof (ctx_pre H2) as H1.
  apply wk_under_eqtm; [apply ext_wf; [exact (wk3_ty H HX) | exact Hl]|].
  apply wk_under_eqtm; [apply ext_wf; [eapply wk1_ty; eauto; eapply wk1_ty; eauto | exact Hl]|].
  apply wk_under_eqtm; [apply ext_wf; [eapply wk1_ty; eauto | exact Hl]|]. exact HT.
Qed.

Lemma wf_tm_func {Γ t T l Δ d d'} :
  [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] t[d] ≅ t[d'] : T[d] @ l ].
Proof using Hi. intros; eapply functionality; eauto. Qed.

(** The arity at equal shapes. *)
Lemma Wf_Na_eq {Γ A N N' a a' l} :
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] N[lsingle a] ≅ N'[lsingle a'] : tyNat @ lzero ].
Proof using Hi.
  intros HN HNN Ha Ha' Haa. eapply eqtm_trans.
  - exact (wf_tm_func HN (lsub_eq_single Ha Ha' Haa)).
  - exact (eqtm_subst Hi HNN (lsub_wf_single G i Hi _ _ _ _ (ctx_of_wf_tm Hi Ha') Ha')).
Qed.

Lemma Wf_E2 (N : tm) : (N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)] = N⟨↑⟩⟨↑⟩.
Proof using . teq_core. Qed.

(** The children's tuple type, over any shape context [Γ, X]. *)
Lemma Wf_cs_wf {Γ X lx l A N} : lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] tyWf l A N @ l ] -> [ G ; Γ ,, X @ lx ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] wfcsty l A N @ l ].
Proof using Hi Hv. intros Hl HW HN. pose proof (ctx_of_wf_tm Hi HN). apply wft_vec; auto. wkn HW. Qed.

(** The children, two locals further. *)
Lemma Wf_var1 {Γ X lx F lf Y ly l A N} :
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] ] -> [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfcsty l A N @ lf ] ->
  lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] var 1 : tyVec l (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ N⟨↑⟩⟨↑⟩ @ l ].
Proof using Hi.
  intros HΔ HF Hlf. pose proof (ctx_pre HΔ) as H2.
  eapply wf_conv; [eapply wf_lconv; [apply wf_var; [now rewrite Hi | do 2 constructor] | apply lequiv_sym, Hlf]|].
  rewrite Hi. eapply eqty_lconv; [|apply lequiv_sym, Hlf].
  apply eqty_sym. match goal with |- eq_ty _ _ _ _ ?T _ => change T with ((wfcsty l A N)⟨↑⟩⟨↑⟩) end.
  eapply wk1_eqty; eauto. eapply wk1_eqty; eauto.
Qed.

(** The child at an index, in the [ih] entry's scope. *)
Lemma Wf_nth_wf {Γ X lx F lf l A N} : lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] tyWf l A N @ l ] -> [ G ; Γ ,, X @ lx ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] ] -> [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfcsty l A N @ lf ] -> lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ]
      tmNth l (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ N⟨↑⟩⟨↑⟩ (var 1) (var 0) : (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l ].
Proof using Hi Hv.
  intros Hl HW HN H2 HF Hlf. pose proof (ctx_pre H2) as H1. pose proof (ctx_pre H1) as H0.
  assert (HN1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] N⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [wkn HN | reflexivity]).
  assert (H3 : [ G ; Γ ,, X @ lx ,, F @ lf ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ] ]) by (apply ext_wf; [apply wft_fin; auto | cbn; auto]).
  apply nth_wf; auto.
  - wkn HW.
  - eapply wf_tm_retype; [wkn HN1 | reflexivity].
  - exact (Wf_var1 H3 HF Hlf).
  - wvar.
Qed.

(** The induction hypothesis's type. *)
Lemma Wf_ih_wf {Γ X lx F lf l l' A N M} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] tyWf l A N @ l ] -> [ G ; Γ ,, X @ lx ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] ] -> [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfcsty l A N @ lf ] -> lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] wfihty l l' A N M @ lmax lzero l' ].
Proof using Hi Hv.
  intros Hl Hl' HW HN HM H2 HF Hlf. pose proof (ctx_pre H2) as H1. pose proof (ctx_pre H1) as H0.
  assert (HN1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] N⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [wkn HN | reflexivity]).
  assert (HF1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] tyFin N⟨↑⟩ @ lzero ]) by (apply wft_fin; auto).
  assert (H3 : [ G ; Γ ,, X @ lx ,, F @ lf ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  apply wft_pi; cbn; auto.
  exact (wf_ty_single Hi (wk_under3_ty H3 HW Hl HM) (Wf_nth_wf Hl HW HN H2 HF Hlf)).
Qed.

(** [sup_f] of the step's shape and children. *)
Lemma Wf_supf_step_wf {Γ X lx F lf Y ly l A N} : lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] X ≅ A @ l ] -> lequiv (gL G) lx l ->
  [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfcsty l A N @ lf ] -> lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ]
      tmSupf l A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1) : (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l ].
Proof using Hi Hv.
  intros Hl HA HN HΔ HXA Hlx HF Hlf.
  apply wf_supf; auto using compt_self.
  - exact (wk3_ty HΔ HA).
  - eapply wf_tm_retype; [exact (wk_under3_tm HΔ HA Hl HN) | reflexivity].
  - eapply wf_lconv; [eapply wf_conv; [apply wf_var; [now rewrite Hi | do 3 constructor] |] | apply lequiv_sym, Hlx].
    rewrite Hi. eapply eqty_lconv; [apply (wk3_eqty HΔ); apply eqty_sym, HXA | exact Hlx].
  - rewrite Wf_E2. exact (Wf_var1 HΔ HF Hlf).
Qed.

Lemma Wf_step_wf {Γ X lx F lf Y ly l l' A N M} : lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] X ≅ A @ l ] -> lequiv (gL G) lx l ->
  [ G ; Γ ,, X @ lx ⊢[ i ] F ≅ wfcsty l A N @ lf ] -> lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] wfstepty l A N M @ l' ].
Proof using Hi Hv.
  intros Hl HA HN HM HΔ HXA Hlx HF Hlf.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; auto using compt_self).
  exact (wf_ty_single Hi (wk_under3_ty HΔ HW Hl HM) (Wf_supf_step_wf Hl HA HN HΔ HXA Hlx HF Hlf)).
Qed.

Lemma pre_wf_r {Γ l l' A A' N'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyWf l' A' N' @ l ].
Proof using Hi Hv.
  intros H HAA HA' HN.
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l' ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  eapply wft_lconv; [| exact H].
  apply wft_wf; eauto using lequiv_wf_r, compt_self.
  eapply (stab_tm Hi HAA H); [apply ext_wf; eauto using lequiv_wf_r | exact HN].
Qed.

Lemma pre_supf_r {Γ l l' A A' N N' a a' cs'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] tmSupf l' A' N' a' cs' : tyWf l A N @ l ].
Proof using Hi Hv.
  intros H HA HAA HA' HN HNN HN' Haa Ha Ha' Hcs'.
  pose proof (lequiv_wf_l _ _ _ H) as Hl. pose proof (lequiv_wf_r _ _ _ H) as Hl'.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l A N ≅ tyWf l' A' N' @ l ]) by (apply eqty_wf; auto using compt_self).
  assert (HA3 : [ G ; Γ ⊢[ i ] A' @ l' ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓA' : [ G ; Γ ,, A' @ l' ⊢[ i ] ]) by (apply ext_wf; auto).
  eapply wf_lconv with (l' := l'); [| exact H].
  eapply (conv_tm' (T' := tyWf l' A' N')); [| eapply eqty_lconv; [exact EW | now apply lequiv_sym]].
  apply wf_supf; auto using compt_self.
  - exact (stab_tm Hi HAA H HΓA' HN').
  - eapply wf_lconv; [eapply conv_tm'; [exact Ha' | apply eqty_sym, HAA] | now apply lequiv_sym].
  - eapply wf_lconv; [eapply conv_tm'; [exact Hcs'|] | now apply lequiv_sym].
    apply eqty_sym, eqty_vec; auto.
    exact (Wf_Na_eq HN HNN Ha Ha' Haa).
Qed.

(** The induction hypothesis's type, along equal components. *)
Lemma Wf_ih_eq {Γ l1 l2 l3 l4 A A' N N' M M'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] -> [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ]
      wfihty l1 l2 A N M ≅ wfihty l3 l4 A' N' M' @ lmax lzero l2 ].
Proof using Hi Hv.
  intros H13 H24 HA HAA HA' HN HNN HN' HM HMM.
  pose proof (lequiv_wf_l _ _ _ H13) as Hl1. pose proof (lequiv_wf_l _ _ _ H24) as Hl2.
  pose proof (lequiv_wf_r _ _ _ H13) as Hl3.
  pose proof (ctx_of_wf_ty Hi HA) as H0.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; auto using compt_self).
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' @ l3 ])
    by (eapply wft_lconv; [exact (pre_wf_r H13 HAA (wft_lconv _ _ _ _ _ _ HA' H13) HN') | now apply lequiv_sym]).
  pose proof (Wf_cs_wf Hl1 HW HN) as HC.
  assert (EC : [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l1 A N ≅ wfcsty l3 A' N' @ l1 ])
    by (apply eqty_vec; auto; [wkn HW | wkne EW]).
  set (Δ := Γ ,, A @ l1 ,, wfcsty l1 A N @ l1) in *.
  assert (HΔ : [ G ; Δ ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HN1 : [ G ; Δ ⊢[ i ] N⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [wkn HN | reflexivity]).
  assert (HNN1 : [ G ; Δ ⊢[ i ] N⟨↑⟩ ≅ N'⟨↑⟩ : tyNat @ lzero ]) by (eapply eq_tm_retype; [wkne HNN | reflexivity]).
  assert (HF1 : [ G ; Δ ⊢[ i ] tyFin N⟨↑⟩ @ lzero ]) by (apply wft_fin; auto).
  assert (HΘ : [ G ; Δ ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (HN2 : [ G ; Δ ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ] N⟨↑⟩⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [wkn HN1 | reflexivity]).
  assert (HNN2 : [ G ; Δ ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ] N⟨↑⟩⟨↑⟩ ≅ N'⟨↑⟩⟨↑⟩ : tyNat @ lzero ])
    by (eapply eq_tm_retype; [wkne HNN1 | reflexivity]).
  assert (EF2 : [ G ; Δ ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ] tyFin N⟨↑⟩⟨↑⟩ ≅ tyFin N'⟨↑⟩⟨↑⟩ @ lzero ]) by (apply eqty_fin; auto).
  pose proof (Wf_nth_wf Hl1 HW HN HΔ (eqty_refl' HC) (lequiv_refl _ _ Hl1)) as Hn.
  assert (Hn' : [ G ; Δ ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ]
                  tmNth l3 (tyWf l3 A' N')⟨↑⟩⟨↑⟩⟨↑⟩ N'⟨↑⟩⟨↑⟩ (var 1) (var 0) : (tyWf l1 A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l1 ]).
  { eapply conv_tm'; [eapply wf_lconv; [| exact H13] | exact (wk3_eqty HΘ EW)].
    apply nth_wf; auto.
    - wkn HW'.
    - eapply wf_tm_retype; [wkn HN' | reflexivity].
    - exact (Wf_var1 HΘ EC H13).
    - eapply conv_tm'; [wvar | apply eqty_sym, EF2]. }
  assert (Hnn : [ G ; Δ ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ]
                  tmNth l1 (tyWf l1 A N)⟨↑⟩⟨↑⟩⟨↑⟩ N⟨↑⟩⟨↑⟩ (var 1) (var 0)
                  ≅ tmNth l3 (tyWf l3 A' N')⟨↑⟩⟨↑⟩⟨↑⟩ N'⟨↑⟩⟨↑⟩ (var 1) (var 0) : (tyWf l1 A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l1 ]).
  { apply nth_eq; auto.
    - wkn HW.
    - exact (wk3_eqty HΘ EW).
    - apply eqtm_refl, (Wf_var1 HΘ (eqty_refl' HC) (lequiv_refl _ _ Hl1)).
    - wvar_eq. }
  pose proof (wk_under3_ty HΘ HW Hl1 HM) as HM3.
  pose proof (wk_under3_eqty HΘ HW Hl1 HMM) as HMM3.
  apply eqty_pi; sides; [apply eqty_fin; auto|].
  eapply eqty_trans; [eapply (wf_ty_func HM3); eapply lsub_eq_single; [exact Hn | exact Hn' | exact Hnn] |].
  exact (eqty_single Hi HMM3 Hn').
Qed.

(** The step's type, along equal components, in the left telescope. *)
Lemma Wf_step_eq {Γ l1 l2 l3 l4 A A' N N' M M' I li} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A' @ l3 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] -> [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, I @ li ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, I @ li ⊢[ i ]
      wfstepty l1 A N M ≅ wfstepty l3 A' N' M' @ l2 ].
Proof using Hi Hv.
  intros H13 H24 HA HAA HA' HN HNN HN' HM HMM HΘ.
  pose proof (lequiv_wf_l _ _ _ H13) as Hl1. pose proof (lequiv_wf_r _ _ _ H13) as Hl3.
  pose proof (ctx_of_wf_ty Hi HA) as H0.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; auto using compt_self).
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply ext_wf; auto).
  pose proof (Wf_cs_wf Hl1 HW HN) as HC.
  assert (EC : [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l1 A N ≅ wfcsty l3 A' N' @ l1 ])
    by (apply eqty_vec; auto; [wkn HW | wkne EW]).
  assert (HAA3 : [ G ; Γ ⊢[ i ] A ≅ A' @ l3 ]) by (eapply eqty_lconv; [exact HAA | now apply lequiv_sym]).
  pose proof (Wf_supf_step_wf Hl1 HA HN HΘ (eqty_refl' HA) (lequiv_refl _ _ Hl1) (eqty_refl' HC) (lequiv_refl _ _ Hl1)) as Hs.
  pose proof (Wf_supf_step_wf Hl3 HA' HN' HΘ HAA3 H13 EC H13) as Hs'0.
  assert (Hs' : [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, I @ li ⊢[ i ]
                  tmSupf l3 A'⟨↑⟩⟨↑⟩⟨↑⟩ N'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1) : (tyWf l1 A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l1 ])
    by (eapply conv_tm'; [eapply wf_lconv; [exact Hs'0 | exact H13] | exact (wk3_eqty HΘ EW)]).
  assert (Hss : [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, I @ li ⊢[ i ]
                  tmSupf l1 A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1)
                  ≅ tmSupf l3 A'⟨↑⟩⟨↑⟩⟨↑⟩ N'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1) : (tyWf l1 A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l1 ]).
  { apply eqtm_supf; auto using compt_self.
    - exact (wk3_ty HΘ HA).
    - exact (wk3_eqty HΘ HAA).
    - eapply wf_tm_retype; [exact (wk_under3_tm HΘ HA Hl1 HN) | reflexivity].
    - eapply eq_tm_retype; [exact (wk_under3_eqtm HΘ HA Hl1 HNN) | reflexivity].
    - apply eqtm_refl, wf_var; [now rewrite Hi | do 3 constructor].
    - rewrite Wf_E2. apply eqtm_refl, (Wf_var1 HΘ (eqty_refl' HC) (lequiv_refl _ _ Hl1)). }
  pose proof (wk_under3_ty HΘ HW Hl1 HM) as HM3.
  pose proof (wk_under3_eqty HΘ HW Hl1 HMM) as HMM3.
  eapply eqty_trans; [eapply (wf_ty_func HM3); eapply lsub_eq_single; [exact Hs | exact Hs' | exact Hss] |].
  exact (eqty_single Hi HMM3 Hs').
Qed.

(** [elim_Wf]'s congruence, right-hand side: the primed telescope is formed,
    the step moved into it along the identity, and the type converted. *)
Lemma pre_elimWf_r {Γ l1 l2 l3 l4 A A' N N' M M' c' t t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] -> [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l1 A N @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ] wfihty l1 l2 A N M @ lmax lzero l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ⊢[ i ] c' : wfstepty l1 A N M @ l2 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyWf l1 A N @ l1 ] ->
  [ G ; Γ ⊢[ i ] t : tyWf l1 A N @ l1 ] -> [ G ; Γ ⊢[ i ] t' : tyWf l1 A N @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmElimWf l3 l4 A' N' M' c' t' : M[lsingle t] @ l2 ].
Proof using Hi Hv.
  intros H13 H24 HAA HA HA' HNN HN HN' HMM HM HM' HC HI Hc Htt Ht Ht'.
  pose proof (ctx_of_wf_tm Hi Ht) as HΓ.
  pose proof (lequiv_wf_l _ _ _ H13) as Hl1. pose proof (lequiv_wf_l _ _ _ H24) as Hl2.
  pose proof (lequiv_wf_r _ _ _ H13) as Hl3. pose proof (lequiv_wf_r _ _ _ H24) as Hl4.
  assert (HLI : lequiv (gL G) (lmax lzero l2) (lmax lzero l4)) by (apply lequiv_max; [apply lequiv_refl; cbn; auto | exact H24]).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; auto using compt_self).
  assert (HA'3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HN'3 : [ G ; Γ ,, A' @ l3 ⊢[ i ] N' : tyNat @ lzero ]) by exact (stab_tm Hi HAA H13 HΓA' HN').
  assert (HW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' @ l3 ]) by (apply wft_wf; auto using compt_self).
  assert (HΓW' : [ G ; Γ ,, tyWf l3 A' N' @ l3 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HM'4 : [ G ; Γ ,, tyWf l3 A' N' @ l3 ⊢[ i ] M' @ l4 ])
    by (eapply wft_lconv; [exact (stab_ty Hi EW H13 HΓW' HM') | now apply lequiv_sym]).
  (* the primed telescope *)
  pose proof (Wf_cs_wf (X := A') (lx := l3) Hl3 HW' HN'3) as HC'.
  assert (HΓA'C' : [ G ; Γ ,, A' @ l3 ,, wfcsty l3 A' N' @ l3 ⊢[ i ] ]) by (apply ext_wf; auto).
  pose proof (Wf_ih_wf Hl3 Hl4 HW' HN'3 HM'4 HΓA'C' (eqty_refl' HC') (lequiv_refl _ _ Hl3)) as HI'.
  (* the left telescope's equations with the primed one *)
  assert (EC : [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l1 A N ≅ wfcsty l3 A' N' @ l1 ])
    by (assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; auto using compt_self);
        assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply ext_wf; auto);
        apply eqty_vec; auto; [wkn HW | wkne EW]).
  assert (HC'A : [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l3 A' N' @ l1 ])
    by (eapply wft_lconv; [exact (Wf_cs_wf Hl3 HW' HN') | exact H13]).
  assert (HΓAC : [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HI'A : [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ] wfihty l3 l4 A' N' M' @ lmax lzero l2 ])
    by (eapply wft_lconv; [exact (Wf_ih_wf Hl3 Hl4 HW' HN' HM'4 HΓAC EC H13) | exact HLI]).
  pose proof (Wf_ih_eq H13 H24 HA HAA HA'3 HN HNN HN' HM HMM) as EI.
  (* the identity from the primed telescope to the left one *)
  assert (Hid0 : [ G ; Γ ⊢[ i ] lshift 0 : Γ ]) by (eapply lsub_wf_id; eauto).
  pose proof (proj2 (ctx_conv_ext Hid0 HA HAA HA' H13)) as Hid1.
  pose proof (proj2 (ctx_conv_ext Hid1 HC EC HC'A H13)) as Hid2.
  pose proof (proj2 (ctx_conv_ext Hid2 HI EI HI'A HLI)) as Hid3.
  assert (HΘ : [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2 ⊢[ i ] ])
    by (apply ext_wf; [exact HI | cbn; auto]).
  pose proof (Wf_step_eq H13 H24 HA HAA HA'3 HN HNN HN'3 HM HMM HΘ) as ES.
  assert (Hc' : [ G ; Γ ,, A' @ l3 ,, wfcsty l3 A' N' @ l3 ,, wfihty l3 l4 A' N' M' @ lmax lzero l4
                  ⊢[ i ] c' : wfstepty l3 A' N' M' @ l4 ]).
  { pose proof (wf_tm_subst Hi Hc Hid3) as X.
    pose proof (eqty_subst Hi ES Hid3) as Y.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ ES) as [N1 N2].
    rewrite nf_id in X by exact (wf_tm_nf Hc).
    rewrite (nf_id_ty (wfstepty l1 A N M)) in X, Y by exact N1.
    rewrite (nf_id_ty (wfstepty l3 A' N' M')) in Y by exact N2.
    eapply wf_lconv; [eapply conv_tm'; [exact X | exact (eqty_sym' Y)] | exact (lequiv_sym _ _ _ H24)]. }
  assert (Ht'W : [ G ; Γ ⊢[ i ] t' : tyWf l3 A' N' @ l3 ])
    by (eapply wf_lconv; [eapply conv_tm'; [exact Ht' | exact (eqty_sym' EW)] | exact (lequiv_sym _ _ _ H13)]).
  eapply wf_lconv with (l' := l4); [| exact H24].
  eapply (conv_tm' (T' := M'[lsingle t'])).
  - apply wf_elimWf; auto using compt_self.
  - eapply eqty_lconv; [|apply lequiv_sym, H24].
    eapply eqty_trans.
    + apply (wf_ty_func HM (d' := lsingle t')). now apply lsub_eq_single.
    + exact (eqty_single Hi HMM Ht').
Qed.

(** [elim_Wf]'s facts for a congruence (M15b), as [W_facts]: the
    scrutinee's types, the motive's contexts, the step's contexts and the
    step's types. *)
Lemma Wf_facts {Γ l1 l2 l3 l4 A A' N N' M M'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] -> [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ] wfihty l1 l2 A N M @ lmax lzero l2 ] ->
  [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ] /\ [ G ⊢[ i ] Γ ,, tyWf l1 A N @ l1 ≅ Γ ,, tyWf l3 A' N' @ l3 ] /\ [ G ⊢[ i ] Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ≅ Γ ,, A' @ l3 ,, wfcsty l3 A' N' @ l3 ,, wfihty l3 l4 A' N' M' @ lmax lzero l4 ] /\ [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2 ⊢[ i ]
      wfstepty l1 A N M ≅ wfstepty l3 A' N' M' @ l2 ].
Proof using Hi Hv.
  intros H13 H24 HAA HA HA' HNN HN HN' HMM HM HI.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (lequiv_wf_l _ _ _ H13) as Hl1. pose proof (lequiv_wf_l _ _ _ H24) as Hl2.
  pose proof (lequiv_wf_r _ _ _ H13) as Hl3.
  assert (HLI : lequiv (gL G) (lmax lzero l2) (lmax lzero l4)) by (apply lequiv_max; [apply lequiv_refl; cbn; auto | exact H24]).
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; auto using compt_self).
  assert (HA'3 : [ G ; Γ ⊢[ i ] A' @ l3 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HΓA' : [ G ; Γ ,, A' @ l3 ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HN'3 : [ G ; Γ ,, A' @ l3 ⊢[ i ] N' : tyNat @ lzero ]) by exact (stab_tm Hi HAA H13 HΓA' HN').
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply ext_wf; auto).
  pose proof (Wf_cs_wf Hl1 HW HN) as HC.
  assert (EC : [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l1 A N ≅ wfcsty l3 A' N' @ l1 ])
    by (apply eqty_vec; auto; [wkn HW | wkne EW]).
  pose proof (Wf_ih_eq H13 H24 HA HAA HA'3 HN HNN HN' HM HMM) as EI.
  assert (HΘ : [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2 ⊢[ i ] ])
    by (apply ext_wf; [exact HI | cbn; auto]).
  pose proof (Wf_step_eq H13 H24 HA HAA HA'3 HN HNN HN'3 HM HMM HΘ) as ES.
  refine (conj EW (conj _ (conj _ ES))).
  - apply eqc_ext; [apply eqc_refl; exact HΓ | exact HW | exact EW | exact H13].
  - apply eqc_ext; [apply eqc_ext; [apply eqc_ext; [apply eqc_refl; exact HΓ | exact HA | exact HAA | exact H13]
                                  | exact HC | exact EC | exact H13]
                  | exact HI | exact EI | exact HLI].
Qed.

(** [sup_f]'s children's types, along equal components (M15b). *)
Lemma Wf_cs_feq {Γ l1 l3 A A' N N' a a'} : lequiv (gL G) l1 l3 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tyVec l1 (tyWf l1 A N) N[lsingle a] ≅ tyVec l3 (tyWf l3 A' N') N'[lsingle a'] @ l1 ].
Proof using Hi Hv.
  intros H13 HA HAA HN HNN Haa Ha Ha'. pose proof (lequiv_wf_l _ _ _ H13) as Hl1.
  apply eqty_vec; auto using compt_self.
  - apply wft_wf; auto using compt_self.
  - apply eqty_wf; auto using compt_self.
  - exact (Wf_Na_eq HN HNN Ha Ha' Haa).
Qed.

(** The telescope weakened past one local, under its binders. *)
Lemma Wf_cs_ren l (A : ty) (N : tm) : (wfcsty l A N)⟨rlift ↑⟩ = wfcsty l A⟨↑⟩ N⟨rlift ↑⟩.
Proof using . wk_eqW. Qed.
Lemma Wf_ih_ren l l' (A : ty) (N : tm) (M : ty) :
  (wfihty l l' A N M)⟨rlift (rlift ↑)⟩ = wfihty l l' A⟨↑⟩ N⟨rlift ↑⟩ M⟨rlift ↑⟩.
Proof using . wk_eqW. Qed.
Lemma Wf_step_ren l (A : ty) (N : tm) (M : ty) :
  (wfstepty l A N M)⟨rlift (rlift (rlift ↑))⟩ = wfstepty l A⟨↑⟩ N⟨rlift ↑⟩ M⟨rlift ↑⟩.
Proof using . wk_eqW. Qed.

(** The children's tuple type at a shape [a]. *)
Lemma Wf_E5 l (A : ty) (N : tm) a : nfty (tyWf l A N) ->
  (wfcsty l A N)[lsingle a] = tyVec l (tyWf l A N) N[lsingle a].
Proof using . intros NW. push_subst. f_equal. teq_core. Qed.

(** The synthesized induction hypothesis's body and codomain, in
    [Γ, j : Fin N[a/x]]: [wfIH] is [λ^{0, l'}(Fin N[a/x]). wfbody], at
    [Π^{0, l'}(Fin N[a/x]). wfcod]. *)
Notation wfnth l A N a cs := (tmNth l (tyWf l A N)⟨↑⟩ N[lsingle a]⟨↑⟩ cs⟨↑⟩ (var 0)).
Notation wfbody l l' A N M c a cs :=
  (tmElimWf l l' A⟨↑⟩ N⟨rlift ↑⟩ M⟨rlift ↑⟩ c⟨rlift (rlift (rlift ↑))⟩ (wfnth l A N a cs)).
Notation wfcod l A N M a cs := (M⟨rlift ↑⟩[lsingle (wfnth l A N a cs)]).

Lemma Wf_E4 l l' (A : ty) (N : tm) (M : ty) a cs : nfty (tyWf l A N) ->
  (wfihty l l' A N M)[lsingle2 a cs] = tyPi lzero l' (tyFin N[lsingle a]) (wfcod l A N M a cs).
Proof using .
  intros NW. rewrite subst_tyPi. f_equal.
  - push_subst. f_equal. teq_core.
  - set (u0 := wfnth l A N a cs).
    set (u := tmNth l (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ N⟨↑⟩⟨↑⟩ (var 1) (var 0)).
    assert (Eu : u[llift (lsingle2 a cs)] = u0).
    { subst u u0. rewrite subst_tmNth. f_equal; try teq_core; pw. }
    rewrite subst_comp_ty, !ren_ren_comp_ty.
    rewrite (ren_subst_ty M _ _ (lcons (lshift 1) u0)), (ren_subst_ty M (rlift ↑) _ (lcons (lshift 1) u0)); auto.
    all: intros [|n]; pw.
    rewrite <- Eu. reflexivity.
Qed.

(** The step's type at [β]: the motive at the [sup_f]. *)
Lemma Wf_E6 l (A : ty) (N : tm) (M : ty) a cs h : nfty (tyWf l A N) ->
  (wfstepty l A N M)[lsingle3 a cs h] = M[lsingle (tmSupf l A N a cs)].
Proof using .
  intros NW. assert (NA : nfty A /\ nftm N) by (inversion NW; auto). destruct NA as [NA NN].
  set (s := tmSupf l A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1)).
  assert (Es : s[lsingle3 a cs h] = tmSupf l A N a cs).
  { subst s. push_subst. f_equal; try teq_core; pw. }
  rewrite subst_comp_ty, !ren_ren_comp_ty, (ren_subst_ty M _ _ (lsingle (tmSupf l A N a cs))); auto.
  intros [|n]; pw. first [exact Es | exact (eq_sym Es)].
Qed.

(** The synthesized induction hypothesis is typed at the [ih] entry's
    instance. *)
Lemma Wf_IH_body_wf {Γ l l' A N M c a cs} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l'
      ⊢[ i ] c : wfstepty l A N M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] wfbody l l' A N M c a cs : wfcod l A N M a cs @ l' ].
Proof using Hi Hv.
  intros Hl Hl' HA HN HM Hc Ha Hcs. pose proof (ctx_of_wf_ty Hi HA) as H0.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; auto using compt_self).
  assert (HNa : [ G ; Γ ⊢[ i ] N[lsingle a] : tyNat @ lzero ]) by exact (wf_tm_single Hi HN Ha).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; auto).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (HW1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] (tyWf l A N)⟨↑⟩ @ l ]) by wkn HW.
  assert (HA1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] A⟨↑⟩ @ l ]) by wkn HA.
  assert (HΓ1A : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HN1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l ⊢[ i ] N⟨rlift ↑⟩ : tyNat @ lzero ])
    by exact (wk_under_tm HΓ1A HN).
  assert (HM1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, (tyWf l A N)⟨↑⟩ @ l ⊢[ i ] M⟨rlift ↑⟩ @ l' ])
    by exact (wk_under_ty (ext_wf HW1 Hl) HM).
  pose proof (Wf_cs_wf Hl HW1 HN1) as HC1.
  assert (HΓ1AC : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l ,, wfcsty l A⟨↑⟩ N⟨rlift ↑⟩ @ l ⊢[ i ] ])
    by (apply ext_wf; auto).
  pose proof (Wf_ih_wf Hl Hl' HW1 HN1 HM1 HΓ1AC (eqty_refl' HC1) (lequiv_refl _ _ Hl)) as HI1.
  apply wf_elimWf; auto using compt_self.
  - (* the step, weakened under the telescope *)
    rewrite <- Wf_step_ren. eapply weakening_r; eauto.
    + repeat (eapply wkr_up'; [ | first [reflexivity | symmetry; first [apply Wf_cs_ren | apply Wf_ih_ren]]]).
      apply wkr_shift1.
    + apply ext_wf; [exact HI1 | cbn; auto].
  - (* the scrutinee: the child at the index *)
    apply nth_wf; auto.
    + eapply wf_tm_retype; [wkn HNa | reflexivity].
    + eapply wf_tm_retype; [wkn Hcs | reflexivity].
    + wvar.
Qed.

Lemma Wf_IH_wf {Γ l l' A N M c a cs} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l'
      ⊢[ i ] c : wfstepty l A N M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] wfIH l l' A N M c a cs : (wfihty l l' A N M)[lsingle2 a cs] @ lmax lzero l' ].
Proof using Hi Hv.
  intros Hl Hl' HA HN HM Hc Ha Hcs.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; auto using compt_self).
  rewrite Wf_E4 by exact (wf_ty_nf HW). unfold wfIH.
  apply wf_lam; cbn; auto; [apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)] |].
  exact (Wf_IH_body_wf Hl Hl' HA HN HM Hc Ha Hcs).
Qed.

Lemma pre_elimWf_beta {Γ l l' A N M c a cs} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l'
      ⊢[ i ] c : wfstepty l A N M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] c[lsingle3 a cs (wfIH l l' A N M c a cs)] : M[lsingle (tmSupf l A N a cs)] @ l' ].
Proof using Hi Hv.
  intros Hl Hl' HA HN HM Hc Ha Hcs.
  pose proof (ctx_of_wf_tm Hi Ha) as HΓ.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; auto using compt_self).
  rewrite <- (Wf_E6 l A N M a cs (wfIH l l' A N M c a cs) (wf_ty_nf HW)).
  eapply (wf_tm_subst Hi Hc). unfold lsingle3, lsingle2.
  apply lsub_wf_cons; [apply lsub_wf_cons; [apply lsub_wf_cons |] |].
  - eapply lsub_wf_id; eauto.
  - rewrite nf_id_ty by exact (wf_ty_nf HA). exact Ha.
  - change (lcons (lshift 0) a) with (lsingle a). rewrite Wf_E5 by exact (wf_ty_nf HW). exact Hcs.
  - change (lcons (lcons (lshift 0) a) cs) with (lsingle2 a cs). exact (Wf_IH_wf Hl Hl' HA HN HM Hc Ha Hcs).
Qed.

(** ... and respects equal pieces (the validity of [elim_Wf]'s β). *)
Lemma Wf_IH_body_eq {Γ l l' l4 l5 A A' N N' M M' c c' a a' cs cs'} :
  lequiv (gL G) l l4 -> lequiv (gL G) l' l5 ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] -> [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l'
      ⊢[ i ] c ≅ c' : wfstepty l A N M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] cs ≅ cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] wfbody l l' A N M c a cs ≅ wfbody l4 l5 A' N' M' c' a' cs'
      : wfcod l A N M a cs @ l' ].
Proof using Hi Hv.
  intros H14 H25 HA HAA HN HNN HM HMM Hcc Ha Ha' Haa Hcs Hcscs.
  pose proof (lequiv_wf_l _ _ _ H14) as Hl. pose proof (lequiv_wf_l _ _ _ H25) as Hl'.
  pose proof (ctx_of_wf_ty Hi HA) as H0.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; auto using compt_self).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l A N ≅ tyWf l4 A' N' @ l ]) by (apply eqty_wf; auto using compt_self).
  assert (HNa : [ G ; Γ ⊢[ i ] N[lsingle a] : tyNat @ lzero ]) by exact (wf_tm_single Hi HN Ha).
  pose proof (Wf_Na_eq HN HNN Ha Ha' Haa) as ENa.
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; auto).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ]) by (apply ext_wf; cbn; auto).
  assert (HW1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] (tyWf l A N)⟨↑⟩ @ l ]) by wkn HW.
  assert (HA1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] A⟨↑⟩ @ l ]) by wkn HA.
  assert (HΓ1A : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l ⊢[ i ] ]) by (apply ext_wf; auto).
  assert (HN1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l ⊢[ i ] N⟨rlift ↑⟩ : tyNat @ lzero ])
    by exact (wk_under_tm HΓ1A HN).
  assert (HΓ1W : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, (tyWf l A N)⟨↑⟩ @ l ⊢[ i ] ]) by exact (ext_wf HW1 Hl).
  assert (HM1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, (tyWf l A N)⟨↑⟩ @ l ⊢[ i ] M⟨rlift ↑⟩ @ l' ])
    by exact (wk_under_ty HΓ1W HM).
  pose proof (Wf_cs_wf Hl HW1 HN1) as HC1.
  assert (HΓ1AC : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l ,, wfcsty l A⟨↑⟩ N⟨rlift ↑⟩ @ l ⊢[ i ] ])
    by (apply ext_wf; auto).
  pose proof (Wf_ih_wf Hl Hl' HW1 HN1 HM1 HΓ1AC (eqty_refl' HC1) (lequiv_refl _ _ Hl)) as HI1.
  apply eqtm_elimWf; auto using compt_self.
  - wkne HAA.
  - exact (wk_under_eqtm HΓ1A HNN).
  - exact (wk_under_eqty HΓ1W HMM).
  - (* the steps, weakened under the telescope *)
    rewrite <- Wf_step_ren. eapply weakening_r; eauto.
    + repeat (eapply wkr_up'; [ | first [reflexivity | symmetry; first [apply Wf_cs_ren | apply Wf_ih_ren]]]).
      apply wkr_shift1.
    + apply ext_wf; [exact HI1 | cbn; auto].
  - (* the scrutinees: the children at the index *)
    apply nth_eq; auto.
    + wkne EW.
    + eapply wf_tm_retype; [wkn HNa | reflexivity].
    + eapply eq_tm_retype; [wkne ENa | reflexivity].
    + eapply eq_tm_retype; [wkne Hcscs | reflexivity].
    + wvar_eq.
Qed.

Lemma Wf_IH_eq {Γ l l' l4 l5 A A' N N' M M' c c' a a' cs cs'} :
  lequiv (gL G) l l4 -> lequiv (gL G) l' l5 ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] -> [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l'
      ⊢[ i ] c ≅ c' : wfstepty l A N M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] cs ≅ cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] wfIH l l' A N M c a cs ≅ wfIH l4 l5 A' N' M' c' a' cs'
      : (wfihty l l' A N M)[lsingle2 a cs] @ lmax lzero l' ].
Proof using Hi Hv.
  intros H14 H25 HA HAA HN HNN HM HMM Hcc Ha Ha' Haa Hcs Hcscs.
  pose proof (lequiv_wf_l _ _ _ H14) as Hl.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; auto using compt_self).
  rewrite Wf_E4 by exact (wf_ty_nf HW). unfold wfIH.
  apply eqtm_lam; sides.
  - apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)].
  - apply eqty_fin; [exact Hv | exact (Wf_Na_eq HN HNN Ha Ha' Haa)].
  - exact (Wf_IH_body_eq H14 H25 HA HAA HN HNN HM HMM Hcc Ha Ha' Haa Hcs Hcscs).
Qed.

End Aux.
