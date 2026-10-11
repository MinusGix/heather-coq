(** * The Static Code Lemma, level-equivalence direction (05:1055, M3_DESIGN.md E11)

    Below layer M, syntax related by [≡ₗ] to a well-typed one, with
    well-formed level annotations, is well typed at the same type and
    declaratively equal to it. The induction is on the left derivation
    (the right-hand syntax has the same shape); the only non-structural
    step is a global variable's local substitution, whose entries are
    converted from the last to the first by functionality ([telescope]). *)
From DeLaM.Typing Require Export CtxConv GStatic.

Lemma lle_D_typeof i : lle i lD -> typeof i = lD.
Proof. destruct i; unfold lle; cbn; intros; try reflexivity; lia. Qed.
Lemma lle_D_notM' {i} : lle i lD -> i <> lM.
Proof. intros H ->; unfold lle in H; cbn in H; lia. Qed.

(** ** Well-formed level annotations of typed syntax *)

Lemma lsub_lwf_llk L d : (forall n, tm_lwf L (llk d n)) -> lsub_lwf L d.
Proof.
  induction d as [k | d IH t]; intros H; cbn; [exact I|].
  split; [apply IH; intros n; exact (H (S n)) | exact (H 0)].
Qed.

Lemma lsub_lwf_entries {L d Δ Γ} : lsub_tail d Δ Γ ->
  (forall n A k, in_ctx Δ n A k -> tm_lwf L (llk d n)) -> lsub_lwf L d.
Proof.
  intros [_ Hl] H. apply lsub_lwf_llk. intros n.
  destruct (Nat.lt_ge_cases n (clen Δ)) as [Hn | Hn].
  - destruct (in_ctx_of_lt _ _ Hn) as (A & k & HA). exact (H _ _ _ HA).
  - replace n with (clen Δ + (n - clen Δ)) by lia. rewrite Hl. exact I.
Qed.

Lemma wrapU_lwf n L b : tm_lwf L (wrapU n b) <-> tm_lwf (n + L) b.
Proof. revert L; induction n as [|n IH]; intros L; cbn; [reflexivity|]. rewrite IH; cbn. now rewrite Nat.add_succ_r. Qed.
Lemma wrapG_lwf n L b : tm_lwf L (wrapG n b) <-> tm_lwf L b.
Proof. induction n; cbn; tauto. Qed.
Lemma wrapL_lwf n L b : tm_lwf L (wrapL n b) <-> tm_lwf L b.
Proof. induction n; cbn; tauto. Qed.
Lemma wrap_lwf nu ng nl L b : tm_lwf L (wrap nu ng nl b) <-> tm_lwf (nu + L) b.
Proof. unfold wrap. rewrite wrapU_lwf, wrapG_lwf, wrapL_lwf. reflexivity. Qed.

Lemma mkrb_lwf L MT Mt bs : ty_lwf (S L) MT -> ty_lwf (S L) Mt ->
  (forall k, k < nbr -> tm_lwf (br_nu k + L) (bs k)) -> tm_lwf L (mkrb MT Mt bs).
Proof.
  intros HT Ht Hb. unfold mkrb, wrapMT, wrapMt. cbn [tup_from br_ar tm_lwf].
  repeat split; auto;
    match goal with |- tm_lwf _ (wrap _ _ _ (bs ?k)) => apply wrap_lwf; apply (Hb k); lia end.
Qed.

Lemma elimT_lwf L l1 l2 MT Mt bs l Δ t : lwf L l1 -> lwf L l2 -> lwf L l -> ctx_lwf L Δ -> tm_lwf L t ->
  ty_lwf (S L) MT -> ty_lwf (S L) Mt -> (forall k, k < nbr -> tm_lwf (br_nu k + L) (bs k)) ->
  tm_lwf L (elimT l1 l2 (mkrb MT Mt bs) l Δ t).
Proof. intros. exact (conj H (conj H0 (conj (mkrb_lwf L MT Mt bs H4 H5 H6) (conj H1 (conj H2 H3))))). Qed.
Lemma elimt_lwf L l1 l2 MT Mt bs l Δ T t : lwf L l1 -> lwf L l2 -> lwf L l -> ctx_lwf L Δ ->
  ty_lwf L T -> tm_lwf L t ->
  ty_lwf (S L) MT -> ty_lwf (S L) Mt -> (forall k, k < nbr -> tm_lwf (br_nu k + L) (bs k)) ->
  tm_lwf L (elimt l1 l2 (mkrb MT Mt bs) l Δ T t).
Proof.
  intros. exact (conj H (conj H0 (conj (mkrb_lwf L MT Mt bs H5 H6 H7) (conj H1 (conj H2 (conj H3 H4)))))).
Qed.

Theorem typed_lwf :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> ctx_lwf (gL G) Γ) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> ty_lwf (gL G) T) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> tm_lwf (gL G) t) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    (* guarded: a failing [apply elimT_lwf] unfolds the recursor against every former *)
    try solve [lazymatch goal with
               | |- tm_lwf _ (elimT _ _ _ _ _ _) => apply elimT_lwf; auto
               | |- tm_lwf _ (elimt _ _ _ _ _ _ _) => apply elimt_lwf; auto end];
    cbn [ty_lwf tm_lwf ctx_lwf lsub_lwf]; try tauto.
  (* global variables: the entries of the local substitution *)
  all: try solve [eapply lsub_lwf_entries; [eassumption|]; intros ?n ?A ?k ?Hin;
                  match goal with IH : forall n A k, in_ctx _ n A k -> _ |- _ => eapply IH; eassumption end].
  (* defined globals (M9): the body too *)
  all: split; [assumption |]; eapply lsub_lwf_entries; [eassumption|]; intros ?n ?A ?k ?Hin;
    match goal with IH : forall n A k, in_ctx _ n A k -> _ |- _ => eapply IH; eassumption end.
Qed.

Lemma wf_ty_lwf {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> ty_lwf (gL G) T.
Proof. apply typed_lwf. Qed.
Lemma wf_tm_lwf {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> tm_lwf (gL G) t.
Proof. apply typed_lwf. Qed.
Lemma wf_ctx_lwf {G i Γ} : [ G ; Γ ⊢[ i ] ] -> ctx_lwf (gL G) Γ.
Proof. apply typed_lwf. Qed.

(** ** Levels *)

Lemma lequiv_lsuc' L l l' : lequiv L l l' -> lequiv L (lsuc l) (lsuc l').
Proof. intros (H1 & H2 & H); repeat split; cbn; auto. Qed.
Lemma lequiv_lmax' L l1 l2 l1' l2' : lequiv L l1 l1' -> lequiv L l2 l2' ->
  lequiv L (lmax l1 l2) (lmax l1' l2').
Proof. intros (? & ? & H) (? & ? & H'); repeat split; cbn; auto. Qed.
Lemma lq {L l l'} : lwf L l -> lwf L l' -> leqv l l' -> lequiv L l l'.
Proof. apply leqv_lequiv. Qed.

Lemma shift_subst_ty' (A : ty) d : A⟨↑⟩[d] = A[ldrop 1 d].
Proof. apply ren_subst_ty; intros n; rewrite llk_ldrop, rlk_shift1; reflexivity. Qed.

Lemma tail_ldrop1' {δ Δ Γ A l} : lsub_tail δ (Δ ,, A @ l) Γ -> lsub_tail (ldrop 1 δ) Δ Γ.
Proof.
  intros [Ht Hl]; split; [exact Ht|]. intros n. rewrite llk_ldrop.
  replace (1 + (clen Δ + n)) with (clen (Δ ,, A @ l) + n) by (cbn; lia). apply Hl.
Qed.

(** ** Facts at P *)

Lemma eqty_subst_single_D {G Γ A M M' t t0 l1 l2} :
  [ G ; Γ ,, A @ l2 ⊢[ lD ] M ≅ M' @ l1 ] -> [ G ; Γ ,, A @ l2 ⊢[ lD ] M' @ l1 ] ->
  [ G ; Γ ⊢[ lD ] t ≅ t0 : A @ l2 ] -> [ G ; Γ ⊢[ lD ] t : A @ l2 ] -> [ G ; Γ ⊢[ lD ] t0 : A @ l2 ] ->
  [ G ; Γ ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t0] @ l1 ].
Proof.
  intros HMM HM' Htt Ht Ht0. eapply eqty_trans.
  - exact (eqty_single (i := lD) eq_refl HMM Ht).
  - apply (wf_ty_func (i := lD) eq_refl HM' (d' := lsingle t0)).
    now apply (lsub_eq_single (i := lD) eq_refl).
Qed.

(** [J]'s motive contexts at equal carriers and points, over equal
    contexts, are equal (M11b). *)
Lemma J_ctx_eq' {G i Γ Γ' l1 l3 A A' a a'} : typeof i = i -> i <> lV -> lequiv (gL G) l1 l3 ->
  [ G ⊢[ i ] Γ ≅ Γ' ] ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ⊢[ i ] Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1
           ≅ Γ' ,, A' @ l3 ,, tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3 ].
Proof.
  intros Hi Hv H13 HΓΓ HA HAA Haa.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; eauto using lequiv_wf_l).
  assert (EId : [ G ; Γ ,, A @ l1 ⊢[ i ] tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) ≅ tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l1 ]).
  { apply eqty_id; auto.
    - apply wk1_ty; auto.
    - apply wk1_eqty; auto.
    - apply wk1_eqtm with (T := A); auto.
    - apply eqtm_refl, var0_wf; auto. }
  apply eqc_ext; [| exact (eqty_wf_l Hi EId) | exact EId | exact H13].
  apply eqc_ext; [exact HΓΓ | exact HA | exact HAA | exact H13].
Qed.

Lemma J_ctx_eq {G i Γ l1 l3 A A' a a'} : typeof i = i -> i <> lV -> lequiv (gL G) l1 l3 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ⊢[ i ] Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1
           ≅ Γ ,, A' @ l3 ,, tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3 ].
Proof.
  intros Hi Hv H13 HA HAA Haa.
  exact (J_ctx_eq' Hi Hv H13 (eqc_refl _ _ _ (ctx_of_wf_ty Hi HA)) HA HAA Haa).
Qed.

(** The equations a right-hand [J] needs, at P. *)
Lemma J_facts_D {G Γ l1 l2 l3 A A' a a' M M' u u' e e'} : lequiv (gL G) l1 l3 ->
  [ G ; Γ ⊢[ lD ] A @ l1 ] -> [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ lD ] A' @ l1 ] ->
  [ G ; Γ ⊢[ lD ] a : A @ l1 ] -> [ G ; Γ ⊢[ lD ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ lD ] a' : A @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ lD ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ lD ] M' @ l2 ] ->
  [ G ; Γ ⊢[ lD ] u : A @ l1 ] -> [ G ; Γ ⊢[ lD ] u ≅ u' : A @ l1 ] -> [ G ; Γ ⊢[ lD ] u' : A @ l1 ] ->
  [ G ; Γ ⊢[ lD ] e : tyId l1 A a u @ l1 ] -> [ G ; Γ ⊢[ lD ] e ≅ e' : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ lD ] e' : tyId l1 A a u @ l1 ] ->
  [ G ⊢[ lD ] Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1
            ≅ Γ ,, A' @ l3 ,, tyId l3 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ l3 ] /\
  [ G ; Γ ⊢[ lD ] M[lsingle2 a (tmRefl l1 A a)] ≅ M'[lsingle2 a' (tmRefl l3 A' a')] @ l2 ] /\
  [ G ; Γ ⊢[ lD ] M[lsingle2 u e] ≅ M'[lsingle2 u' e'] @ l2 ] /\
  [ G ; Γ ⊢[ lD ] tyId l1 A a u ≅ tyId l3 A' a' u' @ l1 ].
Proof.
  intros H13 HA HAA HA' Ha Haa Ha' HMM HM' Hu Huu Hu' He Hee He'.
  assert (Hi : typeof lD = lD) by reflexivity. assert (Hv : lD <> lV) by discriminate.
  pose proof (lequiv_wf_l _ _ _ H13) as Hl1.
  assert (Hr : [ G ; Γ ⊢[ lD ] tmRefl l1 A a : tyId l1 A a a @ l1 ]) by (apply wf_idrefl; auto).
  pose proof (pre_idrefl_r Hi Hv H13 HA HAA HA' Haa Ha') as Hr'.
  assert (Hrr : [ G ; Γ ⊢[ lD ] tmRefl l1 A a ≅ tmRefl l3 A' a' : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; auto).
  pose proof (lsub_eq_J Hi Hv Hl1 HA Ha Ha Ha' Haa Hr Hr' Hrr) as Hs.
  pose proof (lsub_eq_J Hi Hv Hl1 HA Ha Hu Hu' Huu He He' Hee) as Hs2.
  refine (conj (J_ctx_eq Hi Hv H13 HA HAA Haa) (conj _ (conj _ _))).
  - eapply eqty_trans; [exact (eqty_subst Hi HMM (lsub_eq_l Hs)) | exact (wf_ty_func Hi HM' Hs)].
  - eapply eqty_trans; [exact (eqty_subst Hi HMM (lsub_eq_l Hs2)) | exact (wf_ty_func Hi HM' Hs2)].
  - apply eqty_id; auto.
Qed.

(** The equations a right-hand [case] needs, at P (M12c): the motive
    contexts, the summands' contexts, and the right branch types against
    the left ones, in the right summands' contexts. *)
Lemma case_facts_D {G Γ l1 l2 l3 l4 l5 A A' B B' M M'} : lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 ->
  [ G ; Γ ⊢[ lD ] A @ l1 ] -> [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ lD ] A' @ l1 ] ->
  [ G ; Γ ⊢[ lD ] B @ l2 ] -> [ G ; Γ ⊢[ lD ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ lD ] B' @ l2 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ lD ] M @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ lD ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ lD ] M' @ l3 ] ->
  [ G ⊢[ lD ] Γ ,, tySum l1 l2 A B @ lmax l1 l2 ≅ Γ ,, tySum l4 l5 A' B' @ lmax l4 l5 ] /\
  [ G ⊢[ lD ] Γ ,, A @ l1 ≅ Γ ,, A' @ l4 ] /\ [ G ⊢[ lD ] Γ ,, B @ l2 ≅ Γ ,, B' @ l5 ] /\
  [ G ; Γ ,, A' @ l4 ⊢[ lD ] M'⟨rlift ↑⟩[lsingle (tmInl l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] ≅ M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] /\
  [ G ; Γ ,, B' @ l5 ⊢[ lD ] M'⟨rlift ↑⟩[lsingle (tmInr l4 l5 A'⟨↑⟩ B'⟨↑⟩ (var 0))] ≅ M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ].
Proof.
  intros H14 H25 HA HAA HA' HB HBB HB' HM HMM HM'.
  assert (Hi : typeof lD = lD) by reflexivity. assert (Hv : lD <> lV) by discriminate.
  pose proof (lequiv_wf_l _ _ _ H14) as W1. pose proof (lequiv_wf_l _ _ _ H25) as W2.
  pose proof (lequiv_wf_r _ _ _ H14) as W4. pose proof (lequiv_wf_r _ _ _ H25) as W5.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HS : [ G ; Γ ⊢[ lD ] tySum l1 l2 A B @ lmax l1 l2 ]) by (apply wft_sum; assumption).
  assert (ESS : [ G ; Γ ⊢[ lD ] tySum l1 l2 A B ≅ tySum l4 l5 A' B' @ lmax l1 l2 ]) by (apply eqty_sum; assumption).
  assert (HA'4 : [ G ; Γ ⊢[ lD ] A' @ l4 ]) by (eapply wft_lconv; [exact HA' | now apply lequiv_sym]).
  assert (HB'5 : [ G ; Γ ⊢[ lD ] B' @ l5 ]) by (eapply wft_lconv; [exact HB' | now apply lequiv_sym]).
  pose proof (ext_wf Hi HA'4 W4) as HΓA'. pose proof (ext_wf Hi HB'5 W5) as HΓB'.
  pose proof (var0_wf _ _ Hi _ _ _ HΓA') as Hv0A. pose proof (var0_wf _ _ Hi _ _ _ HΓB') as Hv0B.
  assert (HvA : [ G ; Γ ,, A' @ l4 ⊢[ lD ] var 0 : A⟨↑⟩ @ l1 ]).
  { eapply conv_tm'; [exact Hi | eapply wf_lconv; [exact Hv0A | exact H14] |].
    exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' HAA). }
  assert (HvB : [ G ; Γ ,, B' @ l5 ⊢[ lD ] var 0 : B⟨↑⟩ @ l2 ]).
  { eapply conv_tm'; [exact Hi | eapply wf_lconv; [exact Hv0B | exact H25] |].
    exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB' HBB). }
  assert (CS : [ G ⊢[ lD ] Γ ,, tySum l1 l2 A B @ lmax l1 l2 ≅ Γ ,, tySum l4 l5 A' B' @ lmax l4 l5 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HS | exact ESS | exact (lequiv_lmax' _ _ _ _ _ H14 H25)]).
  assert (CA : [ G ⊢[ lD ] Γ ,, A @ l1 ≅ Γ ,, A' @ l4 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HA | exact HAA | exact H14]).
  assert (CB : [ G ⊢[ lD ] Γ ,, B @ l2 ≅ Γ ,, B' @ l5 ])
    by (apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact HB | exact HBB | exact H25]).
  refine (conj CS (conj CA (conj CB (conj _ _)))).
  - apply eqty_sym, (case_branch_eq Hi HΓA' HM HMM HM').
    + apply wf_inl; [exact Hv | exact W1 | exact W2 | exact (wk1_ty _ _ Hi _ _ _ _ _ HΓA' HA)
                    | exact (wk1_ty _ _ Hi _ _ _ _ _ HΓA' HB) | exact HvA].
    + exact (pre_inl_r Hi Hv H14 H25 (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' HAA) (wk1_ty _ _ Hi _ _ _ _ _ HΓA' HA')
               (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' HBB) (wk1_ty _ _ Hi _ _ _ _ _ HΓA' HB') HvA).
    + apply eqtm_inl; [exact Hv | exact H14 | exact H25 | exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' HAA)
                      | exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓA' HBB) | exact (eqtm_refl _ _ _ _ _ _ HvA)].
  - apply eqty_sym, (case_branch_eq Hi HΓB' HM HMM HM').
    + apply wf_inr; [exact Hv | exact W1 | exact W2 | exact (wk1_ty _ _ Hi _ _ _ _ _ HΓB' HA)
                    | exact (wk1_ty _ _ Hi _ _ _ _ _ HΓB' HB) | exact HvB].
    + exact (pre_inr_r Hi Hv H14 H25 (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB' HAA) (wk1_ty _ _ Hi _ _ _ _ _ HΓB' HA')
               (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB' HBB) (wk1_ty _ _ Hi _ _ _ _ _ HΓB' HB') HvB).
    + apply eqtm_inr; [exact Hv | exact H14 | exact H25 | exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB' HAA)
                      | exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB' HBB) | exact (eqtm_refl _ _ _ _ _ _ HvB)].
Qed.

(** ** [elim_W]'s telescope at any layer but V (M13b)

    The children's and the induction hypothesis's types, formed at the
    layer itself from its [W]: the right-hand telescope of a congruence
    below D, whose premises only type the left one. Contexts live at
    [typeof i], so weakening goes through [weakening_all]. *)
Section WGen.
Context {G : gctx} {i : layer} (Hv : i <> lV).

Let up {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) : [ G ; Γ ⊢[ typeof i ] T @ l ] :=
  lift_ty H (lle_self_typeof i).
Let ctxi {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) : [ G ; Γ ⊢[ typeof i ] ] :=
  proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H.
Let exti {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) (Hl : lwf (gL G) l) : [ G ; Γ ,, T @ l ⊢[ typeof i ] ] :=
  wfc_ext _ _ _ _ _ (ctxi H) (up H) Hl.

Lemma wk1_ty_i {Γ X lx T l} : [ G ; Γ ⊢[ i ] X @ lx ] -> lwf (gL G) lx -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] T⟨↑⟩ @ l ].
Proof using . intros HX Hl HT. exact (wk1_ty_g G i _ _ _ _ _ (exti HX Hl) HT). Qed.
Lemma wk_under_ty_i {Γ X Y lx ly T l} : [ G ; Γ ,, Y @ ly ⊢[ i ] X⟨↑⟩ @ lx ] -> lwf (gL G) lx ->
  [ G ; Γ ,, X @ lx ⊢[ i ] T @ l ] -> [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] T⟨rlift ↑⟩ @ l ].
Proof using .
  intros HX Hl HT. eapply (proj1 (proj2 (proj2 weakening_all))); [exact HT | | exact (exti HX Hl)].
  apply wkr_up, wkr_shift1.
Qed.

Lemma W_fty_wf_i {Γ X lx l l' A B} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ] -> [ G ; Γ ,, X @ lx ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] wfty l l' A B @ lmax l' (lmax l l') ].
Proof using Hv.
  intros Hl Hl' HW HB.
  apply wft_pi; [exact Hv | exact Hl' | cbn; split; assumption | exact HB |].
  apply (wk1_ty_i HB Hl'). exact (wk1_ty_g G i _ _ _ _ _ (ctxi HB) HW).
Qed.

Lemma W_u_wf_i {Γ X lx F lf l l' A B} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ] -> [ G ; Γ ,, X @ lx ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] F @ lf ] -> lwf (gL G) lf ->
  [ G ; Γ ,, X @ lx ⊢[ typeof i ] F ≅ wfty l l' A B @ lf ] ->
  lequiv (gL G) lf (lmax l' (lmax l l')) ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, B⟨↑⟩ @ l' ⊢[ i ]
      app (var 1) l' (lmax l l') B⟨↑⟩⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 0)
      : (tyW l l' A B)⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax l l' ].
Proof using Hv.
  intros Hl Hl' HW HB HF Hlf EF Qf.
  assert (HL : lwf (gL G) (lmax l l')) by (cbn; split; assumption).
  pose proof (wk1_ty_i HF Hlf HB) as HB1.
  pose proof (wk1_ty_i HB1 Hl' HB1) as HB2.
  assert (HW2 : [ G ; Γ ,, X @ lx ,, B @ l' ⊢[ i ] (tyW l l' A B)⟨↑⟩⟨↑⟩ @ lmax l l' ])
    by exact (wk1_ty_i HB Hl' (wk1_ty_g G i _ _ _ _ _ (ctxi HB) HW)).
  pose proof (wk_under_ty_i HB1 Hl' HW2) as HW3.
  pose proof (wk_under_ty_i HB2 Hl' HW3) as HW4.
  pose proof (exti HB1 Hl') as HΔ.
  rewrite <- shift4_single0_ty. apply wf_app; [exact Hv | exact Hl' | exact HL | exact HB2 | exact HW4 | |].
  - eapply wf_conv; [eapply wf_lconv; [apply wf_var; [exact HΔ | do 2 constructor] | apply lequiv_sym, Qf]|].
    eapply eqty_lconv; [|apply lequiv_sym, Qf].
    apply eqty_sym. match goal with |- eq_ty _ _ _ _ ?T _ => change T with ((wfty l l' A B)⟨↑⟩⟨↑⟩) end.
    pose proof (ctxi HB1) as HΓXF.
    rewrite <- (typeof_idem i) in HΔ, HΓXF.
    exact (wk1_eqty_g G (typeof i) _ _ _ _ _ _ HΔ (wk1_eqty_g G (typeof i) _ _ _ _ _ _ HΓXF EF)).
  - apply wf_var; [exact HΔ | constructor].
Qed.

Lemma W_ih_wf_i {Γ X lx F lf l l' l'' A B M} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ i ] tyW l l' A B @ lmax l l' ] -> [ G ; Γ ,, X @ lx ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] F @ lf ] -> lwf (gL G) lf ->
  [ G ; Γ ,, X @ lx ⊢[ typeof i ] F ≅ wfty l l' A B @ lf ] ->
  lequiv (gL G) lf (lmax l' (lmax l l')) ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] wihty l l' l'' A B M @ lmax l' l'' ].
Proof using Hv.
  intros Hl Hl' Hl'' HW HB HM HF Hlf EF Qf.
  assert (HL : lwf (gL G) (lmax l l')) by (cbn; split; assumption).
  pose proof (wk1_ty_i HF Hlf HB) as HB1.
  pose proof (wk1_ty_g G i _ _ _ _ _ (ctxi HB) HW) as W1.
  pose proof (wk1_ty_i HF Hlf W1) as W2.
  pose proof (wk1_ty_i HB1 Hl' W2) as W3.
  pose proof (wk_under_ty_i W1 HL HM) as HM1.
  pose proof (wk_under_ty_i W2 HL HM1) as HM2.
  pose proof (wk_under_ty_i W3 HL HM2) as HM3.
  apply wft_pi; [exact Hv | exact Hl' | exact Hl'' | exact HB1 |].
  eapply (wf_ty_subst_g HM3). apply lsub_wf_single_g; [exact (exti HB1 Hl') |].
  exact (W_u_wf_i Hl Hl' HW HB HF Hlf EF Qf).
Qed.

End WGen.

(** ** [nth] and [elim_Wf]'s telescope at any layer but V (M15b)

    [Presupposition]'s [nth_wf] and [Wf_*_wf] hold at D and M; these are
    their ports to every layer but V, as [WGen] for [W]: contexts at
    [typeof i], the [case] on [Fin (S k)] and the pair at [Vec(S k)] typed
    through [wf_conv] along equations at [typeof i]. The type checker's
    [elim_Wf] at layer C builds its premises from them. *)
Section WfGen.
Context {G : gctx} {i : layer} (Hv : i <> lV).

Let up {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) : [ G ; Γ ⊢[ typeof i ] T @ l ] :=
  lift_ty H (lle_self_typeof i).
Lemma ext_g {Γ A l} : [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢[ typeof i ] ].
Proof using . intros H HA Hl. exact (wfc_ext _ _ _ _ _ H (up HA) Hl). Qed.
Let Ct : compt (typeof i) := compt_typeof i.
Let Hty : typeof (typeof i) = typeof i := typeof_idem i.
Let L0 {l} (Hl : lwf (gL G) l) : lequiv (gL G) (lmax lzero l) l.
Proof. eapply lequiv_trans; [apply lmax_comm; cbn; auto | apply lmax_zero; auto]. Qed.

Let upt {Γ t T l} (H : [ G ; Γ ⊢[ i ] t : T @ l ]) : [ G ; Γ ⊢[ typeof i ] t : T @ l ] :=
  lift_tm H (lle_self_typeof i).

Ltac teq_core := repeat first [ rewrite ren_as_r2l_ty | rewrite ren_as_r2l ];
  repeat first [ rewrite subst_comp_ty | rewrite subst_comp ];
  first [ apply subst_ext_ty | apply subst_ext
        | apply subst_id_ty; [assumption|] | apply subst_id; [assumption|]
        | symmetry; apply subst_id_ty; [assumption|] | symmetry; apply subst_id; [assumption|] ];
  intros [|[|[|[|[|[|[|[|?n]]]]]]]]; unfold lsucc; pw;
  try solve [apply ren_as_r2l | symmetry; apply ren_as_r2l].

Ltac gwk H := first [ exact H | eapply wk1_ty_g; [eassumption | gwk H] | eapply wk1_tm_g; [eassumption | gwk H] ].
Ltac gvar := eapply wf_tm_retype; [eapply wf_var; [eassumption | repeat constructor] | cbn; try reflexivity].
Ltac gext := apply ext_g; [assumption | assumption | cbn; auto].
(* conversion along an equation at [typeof i] *)
Ltac gconv := eapply wf_conv.

Lemma nth_mot_wf_g {Γ l T} : [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] nthMot l T @ l ].
Proof using Hv.
  intros H0 Hl HT.
  assert (HN : [ G ; Γ ⊢[ i ] tyNat @ lzero ]) by (apply wft_nat; auto).
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢[ typeof i ] ]) by gext.
  assert (HV : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] tyVec l T⟨↑⟩ (var 0) @ l ]) by (apply wft_vec; auto; [gwk HT | gvar]).
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ⊢[ typeof i ] ]) by gext.
  assert (HF : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ⊢[ i ] tyFin (var 1) @ lzero ])
    by (apply wft_fin; auto; gvar).
  assert (H3 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ,, tyFin (var 1) @ lzero ⊢[ typeof i ] ])
    by gext.
  unfold nthMot. eapply wft_lconv; [| apply lequiv_sym, lmax_idem, Hl].
  apply wft_pi; auto. eapply wft_lconv; [| apply lequiv_sym, L0, Hl].
  apply wft_pi; cbn; auto. gwk HT.
Qed.

Lemma nth_base_wf_g {Γ l T} : [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ⊢[ i ] nthBase l T : (nthMot l T)[lsingle zero] @ l ].
Proof using Hv.
  intros H0 Hl HT.
  rewrite nth_E0 by exact (wf_ty_nf HT). unfold nthBase.
  assert (Hz : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; auto).
  assert (HV : [ G ; Γ ⊢[ i ] tyVec l T zero @ l ]) by (apply wft_vec; auto).
  assert (H1 : [ G ; Γ ,, tyVec l T zero @ l ⊢[ typeof i ] ]) by gext.
  assert (HF : [ G ; Γ ,, tyVec l T zero @ l ⊢[ i ] tyFin zero @ lzero ])
    by (apply wft_fin; auto; apply wf_zero; auto).
  assert (H2 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢[ typeof i ] ]) by gext.
  assert (HE : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢[ i ] tyEmpty lzero @ lzero ])
    by (apply wft_empty; cbn; auto).
  assert (H3 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero ⊢[ typeof i ] ])
    by gext.
  eapply wf_lconv; [| apply lequiv_sym, lmax_idem, Hl].
  apply wf_lam; auto. eapply wf_lconv; [| apply lequiv_sym, L0, Hl].
  apply wf_lam; cbn; auto.
  eapply wf_tm_retype; [apply wf_elimEmpty; cbn; auto; [gwk HT|] | teq_core].
  eapply wf_conv; [gvar|]. apply eqty_sym, eqty_fin_zero; [exact Ct | rewrite Hty; exact H2].
Qed.

Lemma nth_step_wf_g {Γ l T} : [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, nthMot l T @ l ⊢[ i ] nthStep l T : (nthMot l T)[lsucc] @ l ].
Proof using Hv.
  intros H0 Hl HT.
  pose proof (nth_mot_wf_g H0 Hl HT) as HM.
  assert (HN : [ G ; Γ ⊢[ i ] tyNat @ lzero ]) by (apply wft_nat; auto).
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢[ typeof i ] ]) by gext.
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, nthMot l T @ l ⊢[ typeof i ] ]) by gext.
  rewrite nth_ES. unfold nthStep.
  set (Δ0 := Γ ,, tyNat @ lzero ,, nthMot l T @ l) in *.
  assert (HV : [ G ; Δ0 ⊢[ i ] tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ])
    by (apply wft_vec; auto; [gwk HT | apply wf_succ; auto; gvar]).
  assert (H3 : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ⊢[ typeof i ] ]) by gext.
  assert (HF : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ⊢[ i ] tyFin (succ (var 2)) @ lzero ])
    by (apply wft_fin; auto; apply wf_succ; auto; gvar).
  set (Δ1 := Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ,, tyFin (succ (var 2)) @ lzero).
  assert (H4 : [ G ; Δ1 ⊢[ typeof i ] ]) by gext.
  assert (Hk : [ G ; Δ1 ⊢[ i ] var 3 : tyNat @ lzero ]) by gvar.
  assert (HU : [ G ; Δ1 ⊢[ i ] tyUnit lzero @ lzero ]) by (apply wft_unit; cbn; auto).
  assert (HFk : [ G ; Δ1 ⊢[ i ] tyFin (var 3) @ lzero ]) by (apply wft_fin; auto).
  assert (HS : [ G ; Δ1 ⊢[ i ] tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ])
    by (apply wft_sum; cbn; auto).
  assert (H5 : [ G ; Δ1 ,, tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ⊢[ typeof i ] ])
    by gext.
  assert (H5u : [ G ; Δ1 ,, tyUnit lzero @ lzero ⊢[ typeof i ] ]) by gext.
  assert (H5f : [ G ; Δ1 ,, tyFin (var 3) @ lzero ⊢[ typeof i ] ]) by gext.
  (* the tuple, as a pair, in either branch *)
  assert (Hcs : forall X, [ G ; Δ1 ,, X @ lzero ⊢[ typeof i ] ] ->
            [ G ; Δ1 ,, X @ lzero ⊢[ i ] var 2 : tySig l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) @ lmax l l ]
            /\ [ G ; Δ1 ,, X @ lzero ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]
            /\ [ G ; Δ1 ,, X @ lzero ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ⊢[ i ] tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5) @ l ]).
  { intros X HX. assert (HT5 : [ G ; Δ1 ,, X @ lzero ⊢[ i ] T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwk HT.
    assert (HX5 : [ G ; Δ1 ,, X @ lzero ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ⊢[ typeof i ] ]) by gext.
    assert (Hk4 : [ G ; Δ1 ,, X @ lzero ⊢[ i ] var 4 : tyNat @ lzero ]) by gvar.
    split; [|split; [exact HT5|]].
    - eapply wf_lconv; [| apply lmax_idem, Hl]. eapply wf_conv; [gvar|].
      apply eqty_sym, eqty_vec_succ; [exact Ct | exact Hl | exact (up HT5) | exact (upt Hk4)].
    - apply wft_vec; auto; [gwk HT | gvar]. }
  eapply wf_lconv; [| apply lequiv_sym, lmax_idem, Hl].
  apply wf_lam; auto. eapply wf_lconv; [| apply lequiv_sym, L0, Hl].
  apply wf_lam; cbn; auto.
  eapply wf_tm_retype; [apply wf_case; cbn; auto | teq_core].
  - gwk HT.
  - (* the head *)
    destruct (Hcs _ H5u) as (Hp & HT5 & HV5).
    eapply wf_tm_retype; [apply wf_fst; eauto | teq_core].
  - (* the tail, recursively *)
    destruct (Hcs _ H5f) as (Hp & HT5 & HV5).
    set (Δ2 := Δ1 ,, tyFin (var 3) @ lzero) in *.
    assert (Hk4 : [ G ; Δ2 ⊢[ i ] var 4 : tyNat @ lzero ]) by gvar.
    assert (HF4 : [ G ; Δ2 ⊢[ i ] tyFin (var 4) @ lzero ]) by (apply wft_fin; auto).
    assert (H6 : [ G ; Δ2 ,, tyFin (var 4) @ lzero ⊢[ typeof i ] ]) by gext.
    assert (HV4 : [ G ; Δ2 ⊢[ i ] tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ]) by (apply wft_vec; auto).
    assert (H7 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ⊢[ typeof i ] ]) by gext.
    assert (HF5 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ⊢[ i ] tyFin (var 5) @ lzero ])
      by (apply wft_fin; auto; gvar).
    assert (H8 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ,, tyFin (var 5) @ lzero ⊢[ typeof i ] ])
      by gext.
    eapply wf_tm_retype; [apply wf_app; cbn; auto | teq_core].
    + gwk HT.
    + eapply wf_lconv; [| apply L0, Hl].
      eapply wf_tm_retype; [apply wf_app; auto | push_subst; f_equal; try teq_core; pw].
      * eapply wft_lconv; [| apply lequiv_sym, L0, Hl]. apply wft_pi; cbn; auto. gwk HT.
      * eapply wf_lconv; [| apply lmax_idem, Hl].
        gvar. unfold nthMot. push_ren. f_equal; f_equal; teq_core.
      * eapply wf_tm_retype; [apply wf_snd; eauto | push_subst; f_equal; try teq_core; pw].
    + gvar.
  - eapply wf_lconv; [| apply lmax_idem; cbn; auto]. eapply wf_conv; [gvar|].
    apply eqty_sym, eqty_fin_succ; [exact Ct | exact (upt Hk)].
Qed.

Lemma nth_wf_g {Γ l T k cs j} : lwf (gL G) l -> [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G ; Γ ⊢[ i ] k : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] cs : tyVec l T k @ l ] ->
  [ G ; Γ ⊢[ i ] j : tyFin k @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmNth l T k cs j : T @ l ].
Proof using Hv.
  intros Hl HT Hk Hcs Hj. pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HT) as H0.
  pose proof (wf_ty_nf HT) as NT. pose proof (wf_tm_nf Hk) as Nk.
  assert (HV : [ G ; Γ ⊢[ i ] tyVec l T k @ l ]) by (apply wft_vec; auto).
  assert (H1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ typeof i ] ]) by gext.
  assert (HF : [ G ; Γ ⊢[ i ] tyFin k @ lzero ]) by (apply wft_fin; auto).
  assert (H2 : [ G ; Γ ,, tyFin k @ lzero ⊢[ typeof i ] ]) by gext.
  assert (Hk1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] k⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [gwk Hk | reflexivity]).
  assert (HF1 : [ G ; Γ ,, tyVec l T k @ l ⊢[ i ] tyFin k⟨↑⟩ @ lzero ]) by (apply wft_fin; auto).
  assert (H3 : [ G ; Γ ,, tyVec l T k @ l ,, tyFin k⟨↑⟩ @ lzero ⊢[ typeof i ] ]) by gext.
  unfold tmNth.
  eapply wf_tm_retype; [apply wf_app; cbn; auto | teq_core].
  - gwk HT.
  - eapply wf_lconv; [| apply L0, Hl].
    eapply wf_tm_retype; [apply wf_app; auto | apply nth_Ecs; assumption].
    + eapply wft_lconv; [| apply lequiv_sym, L0, Hl]. apply wft_pi; cbn; auto. gwk HT.
    + eapply wf_lconv; [| apply lmax_idem, Hl].
      rewrite <- nth_Ek by assumption.
      apply wf_natrec; auto using nth_mot_wf_g, nth_base_wf_g, nth_step_wf_g.
Qed.

Lemma cpre {j Γ A l} : [ G ; Γ ,, A @ l ⊢[ j ] ] -> [ G ; Γ ⊢[ j ] ].
Proof using . inversion 1; auto. Qed.
Lemma wku_ty_g {Γ X Y lx ly T k} : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ typeof i ] ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] T @ k ] -> [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] T⟨rlift ↑⟩ @ k ].
Proof using . intros HΔ HT. eapply weakening_all; eauto. apply wkr_up, wkr_shift1. Qed.
Lemma wku_tm_g {Γ X Y lx ly t T k} : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ typeof i ] ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] t : T @ k ] -> [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ lx ⊢[ i ] t⟨rlift ↑⟩ : T⟨rlift ↑⟩ @ k ].
Proof using . intros HΔ HT. eapply weakening_all; eauto. apply wkr_up, wkr_shift1. Qed.
Lemma wk1_eqty_t {Γ A l T T' k} : [ G ; Γ ,, A @ l ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ typeof i ] T ≅ T' @ k ] ->
  [ G ; Γ ,, A @ l ⊢[ typeof i ] T⟨↑⟩ ≅ T'⟨↑⟩ @ k ].
Proof using . intros H HT. rewrite <- Hty in H. exact (wk1_eqty_g G (typeof i) _ _ _ _ _ _ H HT). Qed.

(** The step telescope at [i] ([Presupposition]'s [Wf_*_wf], with the
    contexts and the entries' equations at [typeof i]). *)
Lemma Wf_cs_wf_g {Γ X lx l A N} : lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] tyWf l A N @ l ] -> [ G ; Γ ,, X @ lx ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] wfcsty l A N @ l ].
Proof using Hv.
  intros Hl HW HN. pose proof (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ HN) as H1.
  apply wft_vec; auto. gwk HW.
Qed.

Lemma Wf_var1_g {Γ X lx F lf Y ly l A N} :
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ typeof i ] ] -> [ G ; Γ ,, X @ lx ⊢[ typeof i ] F ≅ wfcsty l A N @ lf ] ->
  lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] var 1 : tyVec l (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ N⟨↑⟩⟨↑⟩ @ l ].
Proof using .
  intros HΔ HF Hlf. pose proof (cpre HΔ) as H2.
  eapply wf_conv; [eapply wf_lconv; [apply wf_var; [exact HΔ | do 2 constructor] | apply lequiv_sym, Hlf]|].
  eapply eqty_lconv; [|apply lequiv_sym, Hlf].
  apply eqty_sym. match goal with |- eq_ty _ _ _ _ ?T _ => change T with ((wfcsty l A N)⟨↑⟩⟨↑⟩) end.
  exact (wk1_eqty_t HΔ (wk1_eqty_t H2 HF)).
Qed.

Lemma Wf_nth_wf_g {Γ X lx F lf l A N} : lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] tyWf l A N @ l ] -> [ G ; Γ ,, X @ lx ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ typeof i ] ] -> [ G ; Γ ,, X @ lx ⊢[ typeof i ] F ≅ wfcsty l A N @ lf ] ->
  lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ]
      tmNth l (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ N⟨↑⟩⟨↑⟩ (var 1) (var 0) : (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l ].
Proof using Hv.
  intros Hl HW HN H2 HF Hlf. pose proof (cpre H2) as H1.
  assert (HN1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] N⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [gwk HN | reflexivity]).
  assert (HF1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] tyFin N⟨↑⟩ @ lzero ]) by (apply wft_fin; auto).
  assert (H3 : [ G ; Γ ,, X @ lx ,, F @ lf ,, tyFin N⟨↑⟩ @ lzero ⊢[ typeof i ] ]) by gext.
  apply nth_wf_g; auto.
  - pose proof (cpre H1) as H0. gwk HW.
  - eapply wf_tm_retype; [gwk HN1 | reflexivity].
  - exact (Wf_var1_g H3 HF Hlf).
  - gvar.
Qed.

Lemma Wf_ih_wf_g {Γ X lx F lf l l' A N M} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] tyWf l A N @ l ] -> [ G ; Γ ,, X @ lx ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ typeof i ] ] -> [ G ; Γ ,, X @ lx ⊢[ typeof i ] F ≅ wfcsty l A N @ lf ] ->
  lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] wfihty l l' A N M @ lmax lzero l' ].
Proof using Hv.
  intros Hl Hl' HW HN HM H2 HF Hlf. pose proof (cpre H2) as H1. pose proof (cpre H1) as H0.
  assert (HN1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] N⟨↑⟩ : tyNat @ lzero ]) by (eapply wf_tm_retype; [gwk HN | reflexivity]).
  assert (HF1 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] tyFin N⟨↑⟩ @ lzero ]) by (apply wft_fin; auto).
  assert (H3 : [ G ; Γ ,, X @ lx ,, F @ lf ,, tyFin N⟨↑⟩ @ lzero ⊢[ typeof i ] ]) by gext.
  assert (W1 : [ G ; Γ ,, X @ lx ⊢[ i ] (tyWf l A N)⟨↑⟩ @ l ]) by gwk HW.
  assert (W2 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] (tyWf l A N)⟨↑⟩⟨↑⟩ @ l ]) by gwk HW.
  assert (W3 : [ G ; Γ ,, X @ lx ,, F @ lf ,, tyFin N⟨↑⟩ @ lzero ⊢[ i ] (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwk HW.
  pose proof (wku_ty_g (ext_g H1 W1 Hl) HM) as HM1.
  pose proof (wku_ty_g (ext_g H2 W2 Hl) HM1) as HM2.
  pose proof (wku_ty_g (ext_g H3 W3 Hl) HM2) as HM3.
  apply wft_pi; cbn; auto.
  eapply (wf_ty_subst_g HM3). apply lsub_wf_single_g; [exact H3 |].
  exact (Wf_nth_wf_g Hl HW HN H2 HF Hlf).
Qed.

Lemma Wf_step_wf_g {Γ X lx F lf Y ly l l' A N M} : lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ typeof i ] ] ->
  [ G ; Γ ⊢[ typeof i ] X ≅ A @ l ] -> lequiv (gL G) lx l ->
  [ G ; Γ ,, X @ lx ⊢[ typeof i ] F ≅ wfcsty l A N @ lf ] -> lequiv (gL G) lf l ->
  [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] wfstepty l A N M @ l' ].
Proof using Hv.
  intros Hl HA HN HM HΔ HXA Hlx HF Hlf.
  pose proof (cpre HΔ) as H2. pose proof (cpre H2) as H1. pose proof (cpre H1) as H0.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; auto).
  assert (W1 : [ G ; Γ ,, X @ lx ⊢[ i ] (tyWf l A N)⟨↑⟩ @ l ]) by gwk HW.
  assert (W2 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] (tyWf l A N)⟨↑⟩⟨↑⟩ @ l ]) by gwk HW.
  assert (W3 : [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwk HW.
  pose proof (wku_ty_g (ext_g H1 W1 Hl) HM) as HM1.
  pose proof (wku_ty_g (ext_g H2 W2 Hl) HM1) as HM2.
  pose proof (wku_ty_g (ext_g HΔ W3 Hl) HM2) as HM3.
  eapply (wf_ty_subst_g HM3). apply lsub_wf_single_g; [exact HΔ |].
  (* [sup_f] of the step's shape and children *)
  assert (A1 : [ G ; Γ ,, X @ lx ⊢[ i ] A⟨↑⟩ @ l ]) by gwk HA.
  assert (A2 : [ G ; Γ ,, X @ lx ,, F @ lf ⊢[ i ] A⟨↑⟩⟨↑⟩ @ l ]) by gwk HA.
  assert (A3 : [ G ; Γ ,, X @ lx ,, F @ lf ,, Y @ ly ⊢[ i ] A⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwk HA.
  apply wf_supf; auto.
  - eapply wf_tm_retype.
    + exact (wku_tm_g (ext_g HΔ A3 Hl) (wku_tm_g (ext_g H2 A2 Hl) (wku_tm_g (ext_g H1 A1 Hl) HN))).
    + reflexivity.
  - eapply wf_lconv; [eapply wf_conv; [apply wf_var; [exact HΔ | do 3 constructor] |] | apply lequiv_sym, Hlx].
    eapply eqty_lconv; [| exact Hlx].
    exact (wk1_eqty_t HΔ (wk1_eqty_t H2 (wk1_eqty_t H1 (eqty_sym _ _ _ _ _ _ HXA)))).
  - rewrite Wf_E2. exact (Wf_var1_g HΔ HF Hlf).
Qed.

End WfGen.

Section SC.
Context {G : gctx} {i : layer} (Hi : lle i lD).
Let Hty : typeof i = lD := lle_D_typeof i Hi.

Lemma sc_ctx {Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ lD ] ].
Proof using Hty. intros H; rewrite <- Hty; exact (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H). Qed.
Lemma sc_ctx_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] ].
Proof using Hty. intros H; rewrite <- Hty; exact (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H). Qed.
Lemma sc_ty {Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ lD ] T @ l ].
Proof using Hi. intros H; exact (lift_ty H Hi). Qed.
Lemma sc_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] t : T @ l ].
Proof using Hi. intros H; exact (lift_tm H Hi). Qed.
Lemma sc_eqty {Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ].
Proof using Hi. intros H; exact (lift_eqty H Hi). Qed.
Lemma sc_eqtm {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ].
Proof using Hi. intros H; exact (lift_eqtm H Hi). Qed.

(** Conversion at [i] along an equation at P. *)
Lemma sc_conv {Γ t T T' l} : [ G ; Γ ⊢[ i ] t : T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] t : T @ l ].
Proof using Hty. intros H HT; apply (wf_conv _ _ _ _ _ _ _ H); now rewrite Hty. Qed.
Lemma sc_eqconv {Γ t t' T T' l} : [ G ; Γ ⊢[ i ] t ≅ t' : T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ].
Proof using Hty. intros H HT; apply (eqtm_conv _ _ _ _ _ _ _ _ H); now rewrite Hty. Qed.

(** The context extended by related types. *)
Lemma sc_ext {Γ A A' l l'} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> lequiv (gL G) l l' ->
  [ G ⊢[ lD ] Γ ,, A @ l ≅ Γ ,, A' @ l' ].
Proof using Hty.
  intros HA HAA Hl. apply eqc_ext; [apply eqc_refl, (sc_ctx HA) | exact (sc_ty HA) | exact (sc_eqty HAA) | exact Hl].
Qed.
Lemma sc_cty {Γ Γ' T l} : [ G ⊢[ lD ] Γ ≅ Γ' ] -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ' ⊢[ i ] T @ l ].
Proof using Hty. intros Hc H; exact (ctxconv_ty Hc Hty H). Qed.
Lemma sc_ctm {Γ Γ' t T l} : [ G ⊢[ lD ] Γ ≅ Γ' ] -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ' ⊢[ i ] t : T @ l ].
Proof using Hty. intros Hc H; exact (ctxconv_tm Hc Hty H). Qed.

(** ** The global variables' entries, from the last to the first *)

Lemma telescope Γ Δ : forall d d',
  [ G ; Δ ⊢[ lD ] ] -> lsub_tail d Δ Γ -> lsub_tail d' Δ Γ -> [ G ; Γ ⊢[ lD ] ] -> LK dnftm d -> LK dnftm d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d] @ k ] /\
                                    [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ].
Proof using Hty.
  induction Δ as [| g | Δ IH B kB]; intros d d' HΔ Ht Ht' HΓ N N' Hd Hd' n A k Hin; inversion Hin; subst.
  - (* the last entry: its type only depends on the others *)
    inversion HΔ as [| | ? ? ? ? ? HΔ0 HB HkB]; subst.
    assert (R : forall m C km, in_ctx Δ m C km -> [ G ; Γ ⊢[ i ] llk (ldrop 1 d') m : C[ldrop 1 d'] @ km ]).
    { apply (IH (ldrop 1 d) (ldrop 1 d') HΔ0 (tail_ldrop1' Ht) (tail_ldrop1' Ht') HΓ (lk_dnf_ldrop _ _ N) (lk_dnf_ldrop _ _ N')).
      - intros m C km HC. rewrite llk_ldrop, <- shift_subst_ty'. exact (Hd _ _ _ (in_there _ _ _ _ _ _ HC)).
      - intros m C km HC. rewrite !llk_ldrop, <- shift_subst_ty'. exact (Hd' _ _ _ (in_there _ _ _ _ _ _ HC)). }
    assert (E : [ G ; Γ ⊢[ lD ] ldrop 1 d ≅ ldrop 1 d' : Δ ]).
    { refine (conj _ (conj _ _)).
      - constructor; [exact HΓ | now apply lk_dnf_ldrop | exact (tail_ldrop1' Ht) |].
        intros m C km HC. rewrite llk_ldrop, <- shift_subst_ty'. apply sc_tm, (Hd _ _ _ (in_there _ _ _ _ _ _ HC)).
      - constructor; [exact HΓ | now apply lk_dnf_ldrop | exact (tail_ldrop1' Ht') |].
        intros m C km HC. apply sc_tm, R, HC.
      - intros m C km HC. rewrite !llk_ldrop, <- shift_subst_ty'.
        apply sc_eqtm, (proj2 (Hd' _ _ _ (in_there _ _ _ _ _ _ HC))). }
    pose proof (wf_ty_func (i := lD) eq_refl HB E) as X.
    rewrite !shift_subst_ty'. apply (sc_conv (proj1 (Hd' _ _ _ (in_here _ _ _)))).
    rewrite shift_subst_ty'. exact (eqty_sym _ _ _ _ _ _ X).
  - rewrite shift_subst_ty', <- (llk_ldrop 1 d' _).
    match goal with Hm : in_ctx Δ _ _ _ |- _ => revert Hm end. intros Hm.
    inversion HΔ as [| | ? ? ? ? ? HΔ0 HB HkB]; subst.
    apply (IH (ldrop 1 d) (ldrop 1 d') HΔ0 (tail_ldrop1' Ht) (tail_ldrop1' Ht') HΓ (lk_dnf_ldrop _ _ N) (lk_dnf_ldrop _ _ N')).
    + intros m C km HC. rewrite llk_ldrop, <- shift_subst_ty'. exact (Hd _ _ _ (in_there _ _ _ _ _ _ HC)).
    + intros m C km HC. rewrite !llk_ldrop, <- shift_subst_ty'. exact (Hd' _ _ _ (in_there _ _ _ _ _ _ HC)).
    + exact Hm.
Qed.

(** ** One case per form

    Each takes the rule's premises and its induction hypotheses at the
    right-hand components, and gives the right-hand typing and the
    equation. *)

Lemma sc_tail {d d' Δ Γ} : lsub_tail d Δ Γ -> lsub_leq d d' -> lsub_tail d' Δ Γ.
Proof using .
  intros [Ht Hl] E; split; [exact Ht|]. intros n. pose proof (llk_leq _ _ (clen Δ + n) E) as X.
  rewrite Hl in X. destruct (llk d' (clen Δ + n)); cbn in X; try contradiction. now subst.
Qed.
Lemma sc_dnfl {d d'} : dnfl d -> lsub_leq d d' -> dnfl d'.
Proof using . intros H E; exact (proj2 (proj2 (proj2 leq_dnf_all)) _ _ E H). Qed.

Lemma sc_U {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tyU l' @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tyU l ≅ tyU l' @ lsuc l ].
Proof using .
  intros Hv HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_U; auto | apply lequiv_lsuc', Q].
  - apply eqty_U; auto.
Qed.

Lemma sc_El {Γ l l' t t'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] tyEl l' t' @ l ] /\ [ G ; Γ ⊢[ i ] tyEl l t ≅ tyEl l' t' @ l ].
Proof using Hty.
  intros Hv Hl Hl' E Ht [Ht' Htt]. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_El; [exact Hv | exact Hl' |] | exact Q].
    apply (sc_conv (T' := tyU l)); [eapply wf_lconv; [exact Ht' | apply lequiv_lsuc', lequiv_sym, Q]|].
    apply eqty_U; [discriminate | exact (sc_ctx_tm Ht) | exact (lequiv_sym _ _ _ Q)].
  - apply eqty_El; auto.
Qed.

Lemma sc_pi {Γ l1 l2 l1' l2' A A' B B'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyPi l1' l2' A' B' @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tyPi l1 l2 A B ≅ tyPi l1' l2' A' B' @ lmax l1 l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] [HB' HBB].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ext HA HAA Q1) as Hc. split.
  - eapply wft_lconv; [apply wft_pi; auto | apply lequiv_lmax'; assumption].
    + eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
    + eapply wft_lconv; [exact (sc_cty Hc HB') | apply lequiv_sym, Q2].
  - apply eqty_pi; auto.
Qed.

Lemma sc_code_U {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ] /\
  [ G ; Γ ⊢[ i ] tmU l ≅ tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ].
Proof using Hty.
  intros Hv HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. rewrite Hty in HΓ. split.
  - apply (sc_conv (T' := tyU (lsuc l'))).
    + eapply wf_lconv; [apply wf_code_U; [exact Hv | rewrite Hty; exact HΓ | exact Hl'] |].
      apply lequiv_lsuc', lequiv_lsuc', Q.
    + apply eqty_U; [discriminate | exact HΓ | apply lequiv_lsuc', Q].
  - apply eqtm_code_U; auto. now rewrite Hty.
Qed.

Lemma sc_code_pi {Γ l1 l2 l1' l2' s s' t t'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] /\
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmPi l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmPi l1 l2 s t ≅ tmPi l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 Hs [Hs' Hss] [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ctx_tm Hs) as HΓ.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; auto).
  assert (HElE : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l1' s' @ l1 ]) by (apply eqty_El; auto).
  pose proof (sc_ext HEl HElE Q1) as Hc.
  assert (Q12 : lequiv (gL G) (lmax l1 l2) (lmax l1' l2')) by (apply lequiv_lmax'; assumption).
  split.
  - apply (sc_conv (T' := tyU (lmax l1' l2'))).
    + eapply wf_lconv; [apply wf_code_pi; auto | apply lequiv_lsuc', Q12].
      * apply (sc_conv (T' := tyU l1)); [eapply wf_lconv; [exact Hs' | apply lequiv_lsuc', lequiv_sym, Q1]|].
        apply eqty_U; [discriminate | exact HΓ | apply lequiv_sym, Q1].
      * apply (sc_conv (T' := tyU l2));
          [eapply wf_lconv; [exact (sc_ctm Hc Ht') | apply lequiv_lsuc', lequiv_sym, Q2]|].
        apply eqty_U; [discriminate | exact (eqctx_wf_r (i := lD) eq_refl Hc) | apply lequiv_sym, Q2].
    + apply eqty_U; [discriminate | exact HΓ | exact Q12].
  - apply eqtm_code_pi; auto.
Qed.

Lemma sc_lam {Γ l1 l2 l1' l2' A A' B b b'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] b : B @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] b' : B @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] b ≅ b' : B @ l2 ] ->
  [ G ; Γ ⊢[ i ] lam l1' l2' A' b' : tyPi l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] lam l1 l2 A b ≅ lam l1' l2' A' b' : tyPi l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] Hb [Hb' Hbb].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ext HA HAA Q1) as Hc.
  pose proof (wf_tm_ty (i := lD) eq_refl (sc_tm Hb)) as HB.
  split.
  - apply (sc_conv (T' := tyPi l1' l2' A' B)).
    + eapply wf_lconv; [apply wf_lam; auto | apply lequiv_lmax'; assumption].
      * eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
      * eapply wf_lconv; [exact (sc_ctm Hc Hb') | apply lequiv_sym, Q2].
    + apply eqty_pi; auto using sc_ty, sc_eqty; first [discriminate | apply eqty_refl, HB].
  - apply eqtm_lam; auto.
Qed.

Lemma sc_app {Γ l1 l2 l1' l2' A A' B B' t t' s s'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] t : tyPi l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t' : tyPi l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] t ≅ t' : tyPi l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] s : A @ l1 ] -> [ G ; Γ ⊢[ i ] s' : A @ l1 ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] app t' l1' l2' A' B' s' : B[lsingle s] @ l2 ] /\
  [ G ; Γ ⊢[ i ] app t l1 l2 A B s ≅ app t' l1' l2' A' B' s' : B[lsingle s] @ l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB] Ht [Ht' Htt] Hs [Hs' Hss].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ext HA HAA Q1) as Hc.
  assert (HP : [ G ; Γ ⊢[ lD ] tyPi l1' l2' A' B' ≅ tyPi l1 l2 A B @ lmax l1' l2' ]).
  { eapply eqty_lconv; [apply eqty_sym, eqty_pi; auto using sc_ty, sc_eqty; discriminate |].
    apply lequiv_sym, lequiv_lmax'; assumption. }
  split.
  - apply (sc_conv (T' := B'[lsingle s'])).
    + eapply wf_lconv; [apply wf_app; auto | exact Q2].
      * eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
      * eapply wft_lconv; [exact (sc_cty Hc HB') | apply lequiv_sym, Q2].
      * apply (sc_conv (T' := tyPi l1 l2 A B)); [eapply wf_lconv; [exact Ht' |] | exact HP].
        apply lequiv_sym, lequiv_lmax'; assumption.
      * apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Hs' | apply lequiv_sym, Q1] |].
        eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q1].
    + apply (eqty_subst_single_D (sc_eqty HBB) (sc_ty HB') (sc_eqtm Hss) (sc_tm Hs) (sc_tm Hs')).
  - apply eqtm_app; auto.
Qed.

Lemma sc_natrec {Γ l l' M M' s s' z z' t t'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' @ l ] /\ [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M ≅ M' @ l ] ->
  [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ] /\
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z ≅ z' : M[lsucc] @ l ] ->
  [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] t' : tyNat @ lzero ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] natrec l' M' s' z' t' : M[lsingle t] @ l ] /\
  [ G ; Γ ⊢[ i ] natrec l M s z t ≅ natrec l' M' s' z' t' : M[lsingle t] @ l ].
Proof using Hty.
  intros Hv Hl Hl' E HM [HM' HMM] Hs [Hs' Hss] Hz [Hz' Hzz] Ht [Ht' Htt].
  pose proof (lq Hl Hl' E) as Q.
  pose proof (sc_ctx_tm Ht) as HΓ.
  assert (HN : [ G ; Γ ⊢[ lD ] tyNat @ lzero ]) by (apply wft_nat; [discriminate | exact HΓ]).
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ lD ] ]) by (apply wfc_ext; auto; exact I).
  assert (Hc : [ G ⊢[ lD ] Γ ,, tyNat @ lzero ,, M @ l ≅ Γ ,, tyNat @ lzero ,, M' @ l' ]).
  { apply eqc_ext; [apply eqc_refl, HΓN | exact (sc_ty HM) | exact (sc_eqty HMM) | exact Q]. }
  assert (Hz0 : [ G ; Γ ⊢[ lD ] zero : tyNat @ lzero ]) by (apply wf_zero; [discriminate | exact HΓ]).
  split.
  - apply (sc_conv (T' := M'[lsingle t'])).
    + eapply wf_lconv; [apply wf_natrec; auto | apply Q].
      * eapply wft_lconv; [exact HM' | apply lequiv_sym, Q].
      * apply (sc_conv (T' := M[lsingle zero])); [eapply wf_lconv; [exact Hs' | apply lequiv_sym, Q] |].
        eapply eqty_lconv; [apply eqty_sym, (eqty_single (i := lD) eq_refl (sc_eqty HMM) Hz0) |].
        apply lequiv_sym, Q.
      * apply (sc_conv (T' := M[lsucc])); [eapply wf_lconv; [exact (sc_ctm Hc Hz') | apply lequiv_sym, Q] |].
        pose proof (eqctx_wf_r (i := lD) eq_refl Hc) as HΓ'.
        eapply eqty_lconv; [apply eqty_sym | apply lequiv_sym, Q].
        exact (ctxconv_eqty (i := lD) Hc eq_refl (eqty_subst (i := lD) eq_refl (sc_eqty HMM)
                 (lsub_wf_lsucc (i := lD) eq_refl ltac:(discriminate) (eqctx_wf_l (i := lD) eq_refl Hc)))).
    + apply (eqty_subst_single_D (sc_eqty HMM) (sc_ty HM') (sc_eqtm Htt) (sc_tm Ht) (sc_tm Ht')).
  - apply eqtm_natrec; auto.
Qed.

(** Global variables *)
Lemma sc_entries {Γ Δ d d'} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] ] -> lsub_tail d Δ Γ -> dnfl d ->
  lsub_leq d d' -> lsub_lwf (gL G) d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> forall t', tm_leq (llk d n) t' -> tm_lwf (gL G) t' ->
     [ G ; Γ ⊢[ i ] t' : A[d] @ k ] /\ [ G ; Γ ⊢[ i ] llk d n ≅ t' : A[d] @ k ]) ->
  lsub_tail d' Δ Γ /\ dnfl d' /\
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) /\
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) /\
  [ G ; Γ ⊢[ lD ] d ≅ d' : Δ ].
Proof using Hty.
  intros HΓ HΔ Ht Nd E W Hd IH.
  assert (Ht' : lsub_tail d' Δ Γ) by exact (sc_tail Ht E).
  assert (Nd' : dnfl d') by exact (sc_dnfl Nd E).
  pose proof (fun n A k h => IH n A k h (llk d' n) (llk_leq _ _ _ E) (llk_lwf _ _ _ W)) as X.
  assert (Hd' : forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]).
  { exact (telescope Γ Δ d d' HΔ Ht Ht' HΓ (fun n => dnfl_llk _ n Nd) (fun n => dnfl_llk _ n Nd') Hd X). }
  refine (conj Ht' (conj Nd' (conj Hd' (conj (fun n A k h => proj2 (X n A k h)) _)))).
  refine (conj _ (conj _ _)).
  - constructor; [exact HΓ | intros n; apply dnfl_llk, Nd | exact Ht |].
    intros n A k h; apply sc_tm, Hd, h.
  - constructor; [exact HΓ | intros n; apply dnfl_llk, Nd' | exact Ht' |].
    intros n A k h; apply sc_tm, Hd', h.
  - intros n A k h; apply sc_eqtm, (proj2 (X n A k h)).
Qed.

Lemma lD_notV_sc : lD <> lV. Proof using . discriminate. Qed.

(** The unit type (M8c): at every layer below D but V (code since M8d). *)
Lemma sc_unit {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tyUnit l' @ l ] /\ [ G ; Γ ⊢[ i ] tyUnit l ≅ tyUnit l' @ l ].
Proof using .
  intros Hc HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_unit; auto | exact Q].
  - apply eqty_unit; auto.
Qed.

Lemma sc_code_unit {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tmUnit l' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmUnit l ≅ tmUnit l' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hc HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - apply (sc_conv (T' := tyU l')).
    + eapply wf_lconv; [apply wf_code_unit; auto | apply lequiv_lsuc', Q].
    + rewrite Hty in HΓ. apply eqty_U; [discriminate | exact HΓ | exact Q].
  - apply eqtm_code_unit; auto.
Qed.

Lemma sc_triv {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tmTriv l' : tyUnit l @ l ] /\ [ G ; Γ ⊢[ i ] tmTriv l ≅ tmTriv l' : tyUnit l @ l ].
Proof using Hty.
  intros Hc HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q.
  assert (H' : [ G ; Γ ⊢[ i ] tmTriv l' : tyUnit l @ l ]).
  { apply (sc_conv (T' := tyUnit l')).
    - eapply wf_lconv; [apply wf_triv; auto | exact Q].
    - rewrite Hty in HΓ. apply eqty_unit; [discriminate | exact HΓ | exact Q]. }
  split; [exact H' | apply eqtm_triv; auto].
Qed.

(** Dependent pairs (M8): likewise. *)
Lemma sc_sig {Γ l1 l2 l1' l2' A A' B B'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tySig l1' l2' A' B' @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tySig l1 l2 A B ≅ tySig l1' l2' A' B' @ lmax l1 l2 ].
Proof using Hty.
  intros Hc H1 H2 H1' H2' E1 E2 HA [HA' HAA] [HB' HBB].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ext HA HAA Q1) as Hx. split.
  - eapply wft_lconv; [apply wft_sig; auto | apply lequiv_lmax'; assumption].
    + eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
    + eapply wft_lconv; [exact (sc_cty Hx HB') | apply lequiv_sym, Q2].
  - apply eqty_sig; auto.
Qed.

Lemma sc_code_sig {Γ l1 l2 l1' l2' s s' t t'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] /\
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSig l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmSig l1 l2 s t ≅ tmSig l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using Hty.
  intros Hc H1 H2 H1' H2' E1 E2 Hs [Hs' Hss] [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ctx_tm Hs) as HΓ.
  pose proof Hc as Hv.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; auto).
  assert (HElE : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l1' s' @ l1 ]) by (apply eqty_El; auto).
  pose proof (sc_ext HEl HElE Q1) as Hx.
  assert (Q12 : lequiv (gL G) (lmax l1 l2) (lmax l1' l2')) by (apply lequiv_lmax'; assumption).
  split.
  - apply (sc_conv (T' := tyU (lmax l1' l2'))).
    + eapply wf_lconv; [apply wf_code_sig; auto | apply lequiv_lsuc', Q12].
      * apply (sc_conv (T' := tyU l1)); [eapply wf_lconv; [exact Hs' | apply lequiv_lsuc', lequiv_sym, Q1]|].
        apply eqty_U; [discriminate | exact HΓ | apply lequiv_sym, Q1].
      * apply (sc_conv (T' := tyU l2));
          [eapply wf_lconv; [exact (sc_ctm Hx Ht') | apply lequiv_lsuc', lequiv_sym, Q2]|].
        apply eqty_U; [discriminate | exact (eqctx_wf_r (i := lD) eq_refl Hx) | apply lequiv_sym, Q2].
    + apply eqty_U; [discriminate | exact HΓ | exact Q12].
  - apply eqtm_code_sig; auto.
Qed.

Lemma sc_pair {Γ l1 l2 l1' l2' A A' B B' a a' b b'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] b : B[lsingle a] @ l2 ] ->
  [ G ; Γ ⊢[ i ] b' : B[lsingle a] @ l2 ] /\ [ G ; Γ ⊢[ i ] b ≅ b' : B[lsingle a] @ l2 ] ->
  [ G ; Γ ⊢[ i ] tmPair l1' l2' A' B' a' b' : tySig l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmPair l1 l2 A B a b ≅ tmPair l1' l2' A' B' a' b' : tySig l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hc H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB] Ha [Ha' Haa] Hb [Hb' Hbb].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ext HA HAA Q1) as Hx.
  split.
  - apply (sc_conv (T' := tySig l1' l2' A' B')).
    + eapply wf_lconv; [apply wf_pair; auto | apply lequiv_lmax'; assumption].
      * eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
      * eapply wft_lconv; [exact (sc_cty Hx HB') | apply lequiv_sym, Q2].
      * apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Ha' | apply lequiv_sym, Q1] |].
        eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q1].
      * apply (sc_conv (T' := B[lsingle a])); [eapply wf_lconv; [exact Hb' | apply lequiv_sym, Q2] |].
        eapply eqty_lconv; [apply eqty_sym | apply lequiv_sym, Q2].
        exact (eqty_subst_single_D (sc_eqty HBB) (sc_ty HB') (sc_eqtm Haa) (sc_tm Ha) (sc_tm Ha')).
    + apply eqty_sig; auto using sc_ty, sc_eqty, lD_notV_sc.
  - apply eqtm_pair; auto.
Qed.

Lemma sc_fst {Γ l1 l2 l1' l2' A A' B B' p p'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] p : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] p' : tySig l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] p ≅ p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmFst l1' l2' A' B' p' : A @ l1 ] /\
  [ G ; Γ ⊢[ i ] tmFst l1 l2 A B p ≅ tmFst l1' l2' A' B' p' : A @ l1 ].
Proof using Hty.
  intros Hc H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB] Hp [Hp' Hpp].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ext HA HAA Q1) as Hx.
  assert (HP : [ G ; Γ ⊢[ lD ] tySig l1' l2' A' B' ≅ tySig l1 l2 A B @ lmax l1' l2' ]).
  { eapply eqty_lconv; [apply eqty_sym, eqty_sig; auto using sc_ty, sc_eqty, lD_notV_sc |].
    apply lequiv_sym, lequiv_lmax'; assumption. }
  split.
  - apply (sc_conv (T' := A')).
    + eapply wf_lconv; [apply wf_fst; auto | exact Q1].
      * eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
      * eapply wft_lconv; [exact (sc_cty Hx HB') | apply lequiv_sym, Q2].
      * apply (sc_conv (T' := tySig l1 l2 A B)); [eapply wf_lconv; [exact Hp' |] | exact HP].
        apply lequiv_sym, lequiv_lmax'; assumption.
    + exact (sc_eqty HAA).
  - apply eqtm_fst; auto.
Qed.

Lemma sc_snd {Γ l1 l2 l1' l2' A A' B B' p p'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] p : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] p' : tySig l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] p ≅ p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmSnd l1' l2' A' B' p' : B[lsingle (tmFst l1 l2 A B p)] @ l2 ] /\
  [ G ; Γ ⊢[ i ] tmSnd l1 l2 A B p ≅ tmSnd l1' l2' A' B' p' : B[lsingle (tmFst l1 l2 A B p)] @ l2 ].
Proof using Hty.
  intros Hc H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB] Hp [Hp' Hpp].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ext HA HAA Q1) as Hx.
  destruct (sc_fst Hc H1 H2 H1' H2' E1 E2 HA (conj HA' HAA) HB (conj HB' HBB) Hp (conj Hp' Hpp))
    as [Hf' Hff].
  assert (Hf : [ G ; Γ ⊢[ i ] tmFst l1 l2 A B p : A @ l1 ]) by (apply wf_fst; auto).
  assert (HP : [ G ; Γ ⊢[ lD ] tySig l1' l2' A' B' ≅ tySig l1 l2 A B @ lmax l1' l2' ]).
  { eapply eqty_lconv; [apply eqty_sym, eqty_sig; auto using sc_ty, sc_eqty, lD_notV_sc |].
    apply lequiv_sym, lequiv_lmax'; assumption. }
  split.
  - apply (sc_conv (T' := B'[lsingle (tmFst l1' l2' A' B' p')])).
    + eapply wf_lconv; [apply wf_snd; auto | exact Q2].
      * eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
      * eapply wft_lconv; [exact (sc_cty Hx HB') | apply lequiv_sym, Q2].
      * apply (sc_conv (T' := tySig l1 l2 A B)); [eapply wf_lconv; [exact Hp' |] | exact HP].
        apply lequiv_sym, lequiv_lmax'; assumption.
    + exact (eqty_subst_single_D (sc_eqty HBB) (sc_ty HB') (sc_eqtm Hff) (sc_tm Hf) (sc_tm Hf')).
  - apply eqtm_snd; auto.
Qed.

(** The identity type (M11a; every layer but V since M11b). The [_q]
    forms give the right-hand typing from level-equivalent annotations
    (presupposition at C uses them too). *)
Lemma sc_id_q {Γ l l' A A' a' b'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyId l' A' a' b' @ l ].
Proof using Hty.
  intros Hv Q HA' HAA Ha' Hb'.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A @ l ] -> [ G ; Γ ⊢[ i ] x : A' @ l' ]).
  { intros x Hx. apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Hx | apply lequiv_sym, Q]|].
    eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q]. }
  eapply wft_lconv; [apply wft_id; [exact Hv | eauto using lequiv_wf_r | | apply F, Ha' | apply F, Hb'] | exact Q].
  eapply wft_lconv; [exact HA' | apply lequiv_sym, Q].
Qed.

Lemma sc_id {Γ l l' A A' a a' b b'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] b' : A @ l ] /\ [ G ; Γ ⊢[ i ] b ≅ b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyId l' A' a' b' @ l ] /\ [ G ; Γ ⊢[ i ] tyId l A a b ≅ tyId l' A' a' b' @ l ].
Proof using Hty.
  intros Hv Hl Hl' E HA [HA' HAA] [Ha' Haa] [Hb' Hbb]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_id_q Hv Q HA' HAA Ha' Hb') | apply eqty_id; auto].
Qed.

Lemma sc_idrefl_q {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmRefl l' A' a' : tyId l A a a @ l ].
Proof using Hty.
  intros Hv Q HA HA' HAA Ha' Haa.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A @ l ] -> [ G ; Γ ⊢[ i ] x : A' @ l' ]).
  { intros x Hx. apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Hx | apply lequiv_sym, Q]|].
    eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q]. }
  apply (sc_conv (T' := tyId l' A' a' a')).
  - eapply wf_lconv; [apply wf_idrefl; [exact Hv | eauto using lequiv_wf_r | | apply F, Ha'] | exact Q].
    eapply wft_lconv; [exact HA' | apply lequiv_sym, Q].
  - apply eqty_id; [discriminate | exact Q | exact (sc_ty HA) | exact (sc_eqty HAA)
                   | exact (sc_eqtm Haa) | exact (sc_eqtm Haa)].
Qed.

Lemma sc_idrefl {Γ l l' A A' a a'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmRefl l' A' a' : tyId l A a a @ l ] /\
  [ G ; Γ ⊢[ i ] tmRefl l A a ≅ tmRefl l' A' a' : tyId l A a a @ l ].
Proof using Hty.
  intros Hv Hl Hl' E HA [HA' HAA] Ha [Ha' Haa]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_idrefl_q Hv Q HA HA' HAA Ha' Haa) | apply eqtm_idrefl; auto].
Qed.

Lemma sc_code_id_q {Γ l l' s s' t' u'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmId l' s' t' u' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hv Q Hs' Hss Ht' Hu'.
  pose proof (sc_ctx_tm Hs') as HΓ.
  assert (HEl : [ G ; Γ ⊢[ lD ] tyEl l s ≅ tyEl l' s' @ l ])
    by (apply eqty_El; [discriminate | exact Q | exact (sc_eqtm Hss)]).
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] x : tyEl l' s' @ l' ]).
  { intros x Hx. apply (sc_conv (T' := tyEl l s)); [eapply wf_lconv; [exact Hx | apply lequiv_sym, Q]|].
    eapply eqty_lconv; [apply eqty_sym, HEl | apply lequiv_sym, Q]. }
  apply (sc_conv (T' := tyU l')).
  - eapply wf_lconv; [apply wf_code_id; [exact Hv | eauto using lequiv_wf_r | | apply F, Ht' | apply F, Hu']
                     | apply lequiv_lsuc', Q].
    apply (sc_conv (T' := tyU l)); [eapply wf_lconv; [exact Hs' | apply lequiv_lsuc', lequiv_sym, Q]|].
    apply eqty_U; [discriminate | exact HΓ | apply lequiv_sym, Q].
  - apply eqty_U; [discriminate | exact HΓ | exact Q].
Qed.

Lemma sc_code_id {Γ l l' s s' t t' u u'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] /\ [ G ; Γ ⊢[ i ] u ≅ u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmId l' s' t' u' : tyU l @ lsuc l ] /\
  [ G ; Γ ⊢[ i ] tmId l s t u ≅ tmId l' s' t' u' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hv Hl Hl' E Hs [Hs' Hss] [Ht' Htt] [Hu' Huu]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_code_id_q Hv Q Hs' Hss Ht' Hu') | apply eqtm_code_id; auto].
Qed.

Lemma sc_J_q {Γ l1 l2 l1' l2' A A' a a' M M' c' u u' e e'} : i <> lV ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ] ->
  [ G ; Γ ⊢[ i ] u : A @ l1 ] -> [ G ; Γ ⊢[ i ] u' : A @ l1 ] -> [ G ; Γ ⊢[ i ] u ≅ u' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] e : tyId l1 A a u @ l1 ] -> [ G ; Γ ⊢[ i ] e' : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ i ] e ≅ e' : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmJ l1' l2' A' a' M' c' u' e' : M[lsingle2 u e] @ l2 ].
Proof using Hty.
  intros Hv Q1 Q2 HA HA' HAA Ha Ha' Haa HM' HMM Hc' Hu Hu' Huu He He' Hee.
  destruct (J_facts_D (l3 := l1') Q1 (sc_ty HA) (sc_eqty HAA) (sc_ty HA') (sc_tm Ha) (sc_eqtm Haa) (sc_tm Ha')
              (sc_eqty HMM) (sc_ty HM') (sc_tm Hu) (sc_eqtm Huu) (sc_tm Hu') (sc_tm He) (sc_eqtm Hee) (sc_tm He'))
    as (Hctx & HMs & HMs2 & HIdu).
  pose proof (sc_ctx_tm Ha) as HΓ.
  pose proof (lequiv_wf_r _ _ _ Q1) as H1'. pose proof (lequiv_wf_r _ _ _ Q2) as H2'.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A @ l1 ] -> [ G ; Γ ⊢[ i ] x : A' @ l1' ]).
  { intros x Hx. apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Hx | apply lequiv_sym, Q1]|].
    eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q1]. }
  assert (HA'1 : [ G ; Γ ⊢[ i ] A' @ l1' ]) by (eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1]).
  assert (HΓA' : [ G ; Γ ,, A' @ l1' ⊢[ typeof i ] ])
    by (rewrite Hty; apply wfc_ext; [exact HΓ | exact (sc_ty HA'1) | exact H1']).
  apply (sc_conv (T' := M'[lsingle2 u' e'])); [|exact HMs2].
  eapply wf_lconv with (l' := l2'); [|exact Q2].
  apply wf_J; [exact Hv | exact H1' | exact H2' | exact HA'1 | apply F, Ha' | | | | apply F, Hu' |].
  - apply wft_id; [exact Hv | exact H1' | apply wk1_ty_g; [exact HΓA' | exact HA'1]
                  | apply (wk1_tm_g _ _ _ _ _ _ A'); [exact HΓA' | apply F, Ha']
                  | apply var0_wf_g, HΓA'].
  - eapply wft_lconv; [exact (sc_cty Hctx HM') | apply lequiv_sym, Q2].
  - apply (sc_conv (T' := M[lsingle2 a (tmRefl l1 A a)])); [eapply wf_lconv; [exact Hc' | apply lequiv_sym, Q2]|].
    eapply eqty_lconv; [apply eqty_sym, HMs | apply lequiv_sym, Q2].
  - apply (sc_conv (T' := tyId l1 A a u)); [eapply wf_lconv; [exact He' | apply lequiv_sym, Q1]|].
    eapply eqty_lconv; [apply eqty_sym, HIdu | apply lequiv_sym, Q1].
Qed.

Lemma sc_J {Γ l1 l2 l1' l2' A A' a a' M M' c c' u u' e e'} : i <> lV ->
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ] ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M' @ l2 ] /\
  [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ] /\
  [ G ; Γ ⊢[ i ] c ≅ c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ] ->
  [ G ; Γ ⊢[ i ] u : A @ l1 ] -> [ G ; Γ ⊢[ i ] u' : A @ l1 ] /\ [ G ; Γ ⊢[ i ] u ≅ u' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] e : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ i ] e' : tyId l1 A a u @ l1 ] /\ [ G ; Γ ⊢[ i ] e ≅ e' : tyId l1 A a u @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmJ l1' l2' A' a' M' c' u' e' : M[lsingle2 u e] @ l2 ] /\
  [ G ; Γ ⊢[ i ] tmJ l1 l2 A a M c u e ≅ tmJ l1' l2' A' a' M' c' u' e' : M[lsingle2 u e] @ l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HId HA [HA' HAA] Ha [Ha' Haa] HM [HM' HMM] [Hc' Hcc] Hu [Hu' Huu] He [He' Hee].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_J_q Hv Q1 Q2 HA HA' HAA Ha Ha' Haa HM' HMM Hc' Hu Hu' Huu He He' Hee) | apply eqtm_J; auto].
Qed.

(** Strict equality (M10a; every layer but V since M10c), as the identity
    type. *)
Lemma sc_seq_q {Γ l l' A A' a' b'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tySEq l' A' a' b' @ l ].
Proof using Hty.
  intros Hv Q HA' HAA Ha' Hb'.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A @ l ] -> [ G ; Γ ⊢[ i ] x : A' @ l' ]).
  { intros x Hx. apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Hx | apply lequiv_sym, Q]|].
    eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q]. }
  eapply wft_lconv; [apply wft_seq; [exact Hv | eauto using lequiv_wf_r | | apply F, Ha' | apply F, Hb'] | exact Q].
  eapply wft_lconv; [exact HA' | apply lequiv_sym, Q].
Qed.

Lemma sc_seq {Γ l l' A A' a a' b b'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] b' : A @ l ] /\ [ G ; Γ ⊢[ i ] b ≅ b' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tySEq l' A' a' b' @ l ] /\ [ G ; Γ ⊢[ i ] tySEq l A a b ≅ tySEq l' A' a' b' @ l ].
Proof using Hty.
  intros Hv Hl Hl' E HA [HA' HAA] [Ha' Haa] [Hb' Hbb]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_seq_q Hv Q HA' HAA Ha' Hb') | apply eqty_seq; auto].
Qed.

Lemma sc_sempty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tySEmpty l' @ l ] /\ [ G ; Γ ⊢[ i ] tySEmpty l ≅ tySEmpty l' @ l ].
Proof using .
  intros Hv HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_sempty; auto | exact Q].
  - apply eqty_sempty; auto.
Qed.

Lemma sc_srefl_q {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] srefl l' A' a' : tySEq l A a a @ l ].
Proof using Hty.
  intros Hv Q HA HA' HAA Ha' Haa.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A @ l ] -> [ G ; Γ ⊢[ i ] x : A' @ l' ]).
  { intros x Hx. apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Hx | apply lequiv_sym, Q]|].
    eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q]. }
  apply (sc_conv (T' := tySEq l' A' a' a')).
  - eapply wf_lconv; [apply wf_srefl; [exact Hv | eauto using lequiv_wf_r | | apply F, Ha'] | exact Q].
    eapply wft_lconv; [exact HA' | apply lequiv_sym, Q].
  - apply eqty_seq; [discriminate | exact Q | exact (sc_ty HA) | exact (sc_eqty HAA)
                    | exact (sc_eqtm Haa) | exact (sc_eqtm Haa)].
Qed.

Lemma sc_srefl {Γ l l' A A' a a'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] srefl l' A' a' : tySEq l A a a @ l ] /\
  [ G ; Γ ⊢[ i ] srefl l A a ≅ srefl l' A' a' : tySEq l A a a @ l ].
Proof using Hty.
  intros Hv Hl Hl' E HA [HA' HAA] [Ha' Haa]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_srefl_q Hv Q HA HA' HAA Ha' Haa) | apply eqtm_srefl; auto].
Qed.

Lemma sc_elimSEmpty_q {Γ l1 l2 l1' l2' M M' e'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] M' @ l2 ] -> [ G ; Γ ⊢[ i ] M ≅ M' @ l2 ] -> [ G ; Γ ⊢[ i ] e' : tySEmpty l1 @ l1 ] ->
  [ G ; Γ ⊢[ i ] elimSEmpty l1' l2' M' e' : M @ l2 ].
Proof using Hty.
  intros Hv Q1 Q2 HM' HMM He'.
  pose proof (sc_ctx_tm He') as HΓ.
  apply (sc_conv (T' := M')); [| exact (sc_eqty HMM)].
  eapply wf_lconv; [apply wf_elimSEmpty; [exact Hv | eauto using lequiv_wf_r | eauto using lequiv_wf_r | |] | exact Q2].
  - eapply wft_lconv; [exact HM' | apply lequiv_sym, Q2].
  - apply (sc_conv (T' := tySEmpty l1)); [eapply wf_lconv; [exact He' | apply lequiv_sym, Q1]|].
    apply eqty_sempty; [discriminate | exact HΓ | apply lequiv_sym, Q1].
Qed.

Lemma sc_elimSEmpty {Γ l1 l2 l1' l2' M M' e e'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] M @ l2 ] -> [ G ; Γ ⊢[ i ] M' @ l2 ] /\ [ G ; Γ ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ⊢[ i ] e' : tySEmpty l1 @ l1 ] /\ [ G ; Γ ⊢[ i ] e ≅ e' : tySEmpty l1 @ l1 ] ->
  [ G ; Γ ⊢[ i ] elimSEmpty l1' l2' M' e' : M @ l2 ] /\
  [ G ; Γ ⊢[ i ] elimSEmpty l1 l2 M e ≅ elimSEmpty l1' l2' M' e' : M @ l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HM [HM' HMM] [He' Hee].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_elimSEmpty_q Hv Q1 Q2 HM' HMM He') | apply eqtm_elimSEmpty; auto].
Qed.

(** Strict equality's codes (M10c). *)
Lemma sc_code_seq_q {Γ l l' s s' t' u'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmSEq l' s' t' u' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hv Q Hs' Hss Ht' Hu'.
  pose proof (sc_ctx_tm Hs') as HΓ.
  assert (HEl : [ G ; Γ ⊢[ lD ] tyEl l s ≅ tyEl l' s' @ l ])
    by (apply eqty_El; [discriminate | exact Q | exact (sc_eqtm Hss)]).
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] x : tyEl l' s' @ l' ]).
  { intros x Hx. apply (sc_conv (T' := tyEl l s)); [eapply wf_lconv; [exact Hx | apply lequiv_sym, Q]|].
    eapply eqty_lconv; [apply eqty_sym, HEl | apply lequiv_sym, Q]. }
  apply (sc_conv (T' := tyU l')).
  - eapply wf_lconv; [apply wf_code_seq; [exact Hv | eauto using lequiv_wf_r | | apply F, Ht' | apply F, Hu']
                     | apply lequiv_lsuc', Q].
    apply (sc_conv (T' := tyU l)); [eapply wf_lconv; [exact Hs' | apply lequiv_lsuc', lequiv_sym, Q]|].
    apply eqty_U; [discriminate | exact HΓ | apply lequiv_sym, Q].
  - apply eqty_U; [discriminate | exact HΓ | exact Q].
Qed.

Lemma sc_code_seq {Γ l l' s s' t t' u u'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] /\ [ G ; Γ ⊢[ i ] u ≅ u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmSEq l' s' t' u' : tyU l @ lsuc l ] /\
  [ G ; Γ ⊢[ i ] tmSEq l s t u ≅ tmSEq l' s' t' u' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hv Hl Hl' E Hs [Hs' Hss] [Ht' Htt] [Hu' Huu]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_code_seq_q Hv Q Hs' Hss Ht' Hu') | apply eqtm_code_seq; auto].
Qed.

Lemma sc_code_sempty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tmSEmpty l' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmSEmpty l ≅ tmSEmpty l' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hc HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - apply (sc_conv (T' := tyU l')).
    + eapply wf_lconv; [apply wf_code_sempty; auto | apply lequiv_lsuc', Q].
    + rewrite Hty in HΓ. apply eqty_U; [discriminate | exact HΓ | exact Q].
  - apply eqtm_code_sempty; auto.
Qed.

(** The empty type (M12a; every layer but V since M12c). *)
Lemma sc_empty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tyEmpty l' @ l ] /\ [ G ; Γ ⊢[ i ] tyEmpty l ≅ tyEmpty l' @ l ].
Proof using .
  intros Hv HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_empty; auto | exact Q].
  - apply eqty_empty; auto.
Qed.

Lemma sc_elimEmpty_q {Γ l1 l2 l1' l2' M M' t t'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M' @ l1 ] -> [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M ≅ M' @ l1 ] ->
  [ G ; Γ ⊢[ i ] t : tyEmpty l2 @ l2 ] -> [ G ; Γ ⊢[ i ] t' : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ i ] elimEmpty l1' l2' M' t' : M[lsingle t] @ l1 ].
Proof using Hty.
  intros Hv Q1 Q2 HM' HMM Ht Ht' Htt.
  pose proof (sc_ctx_tm Ht) as HΓ.
  assert (HΓi : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hty; exact HΓ).
  pose proof (lequiv_wf_l _ _ _ Q2) as W2.
  assert (HE : [ G ; Γ ⊢[ i ] tyEmpty l2 @ l2 ]) by (apply wft_empty; assumption).
  assert (HEE : [ G ; Γ ⊢[ i ] tyEmpty l2 ≅ tyEmpty l2' @ l2 ]) by (apply eqty_empty; assumption).
  apply (sc_conv (T' := M'[lsingle t'])).
  - eapply wf_lconv with (l' := l1'); [| exact Q1].
    apply wf_elimEmpty; [exact Hv | eauto using lequiv_wf_r | eauto using lequiv_wf_r | |].
    + eapply wft_lconv; [exact (sc_cty (sc_ext HE HEE Q2) HM') | apply lequiv_sym, Q1].
    + apply (sc_conv (T' := tyEmpty l2)); [eapply wf_lconv; [exact Ht' | apply lequiv_sym, Q2]|].
      apply eqty_empty; [discriminate | exact HΓ | apply lequiv_sym, Q2].
  - exact (eqty_subst_single_D (sc_eqty HMM) (sc_ty HM') (sc_eqtm Htt) (sc_tm Ht) (sc_tm Ht')).
Qed.
Lemma sc_elimEmpty {Γ l1 l2 l1' l2' M M' t t'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M @ l1 ] ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M' @ l1 ] /\ [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M ≅ M' @ l1 ] ->
  [ G ; Γ ⊢[ i ] t : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ i ] t' : tyEmpty l2 @ l2 ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ i ] elimEmpty l1' l2' M' t' : M[lsingle t] @ l1 ] /\
  [ G ; Γ ⊢[ i ] elimEmpty l1 l2 M t ≅ elimEmpty l1' l2' M' t' : M[lsingle t] @ l1 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HM [HM' HMM] Ht [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_elimEmpty_q Hv Q1 Q2 HM' HMM Ht Ht' Htt) | apply eqtm_elimEmpty; auto].
Qed.

(** Binary sums (M12b; every layer but V since M12c). *)
Lemma sc_sum_q {Γ l1 l2 l1' l2' A' B'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] -> [ G ; Γ ⊢[ i ] tySum l1' l2' A' B' @ lmax l1 l2 ].
Proof using .
  intros Hv Q1 Q2 HA' HB'.
  eapply wft_lconv; [apply wft_sum; [exact Hv | eauto using lequiv_wf_r | eauto using lequiv_wf_r | |]
                    | exact (lequiv_lmax' _ _ _ _ _ Q1 Q2)].
  - eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
  - eapply wft_lconv; [exact HB' | apply lequiv_sym, Q2].
Qed.
Lemma sc_sum {Γ l1 l2 l1' l2' A A' B B'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tySum l1' l2' A' B' @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tySum l1 l2 A B ≅ tySum l1' l2' A' B' @ lmax l1 l2 ].
Proof using .
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_sum_q Hv Q1 Q2 HA' HB') | apply eqty_sum; auto].
Qed.

(** The injections, and their types. *)
Lemma sc_sum_conv {Γ l1 l2 l1' l2' A A' B B' x} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] x : tySum l1' l2' A' B' @ lmax l1' l2' ] -> [ G ; Γ ⊢[ i ] x : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hv Q1 Q2 HAA HBB Hx.
  apply (sc_conv (T' := tySum l1' l2' A' B')); [eapply wf_lconv; [exact Hx | exact (lequiv_lmax' _ _ _ _ _ Q1 Q2)]|].
  apply eqty_sum; [discriminate | exact Q1 | exact Q2 | exact (sc_eqty HAA) | exact (sc_eqty HBB)].
Qed.
Lemma sc_inl_q {Γ l1 l2 l1' l2' A A' B B' a'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmInl l1' l2' A' B' a' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hv Q1 Q2 HA' HAA HB' HBB Ha'.
  apply (sc_sum_conv Hv Q1 Q2 HAA HBB).
  apply wf_inl; [exact Hv | eauto using lequiv_wf_r | eauto using lequiv_wf_r | | |].
  - eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
  - eapply wft_lconv; [exact HB' | apply lequiv_sym, Q2].
  - apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Ha' | apply lequiv_sym, Q1]|].
    eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q1].
Qed.
Lemma sc_inr_q {Γ l1 l2 l1' l2' A A' B B' b'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] b' : B @ l2 ] ->
  [ G ; Γ ⊢[ i ] tmInr l1' l2' A' B' b' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hv Q1 Q2 HA' HAA HB' HBB Hb'.
  apply (sc_sum_conv Hv Q1 Q2 HAA HBB).
  apply wf_inr; [exact Hv | eauto using lequiv_wf_r | eauto using lequiv_wf_r | | |].
  - eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
  - eapply wft_lconv; [exact HB' | apply lequiv_sym, Q2].
  - apply (sc_conv (T' := B)); [eapply wf_lconv; [exact Hb' | apply lequiv_sym, Q2]|].
    eapply eqty_lconv; [apply eqty_sym, sc_eqty, HBB | apply lequiv_sym, Q2].
Qed.
Lemma sc_inl {Γ l1 l2 l1' l2' A A' B B' a a'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmInl l1' l2' A' B' a' : tySum l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmInl l1 l2 A B a ≅ tmInl l1' l2' A' B' a' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB] Ha [Ha' Haa].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_inl_q Hv Q1 Q2 HA' HAA HB' HBB Ha') | apply eqtm_inl; auto].
Qed.
Lemma sc_inr {Γ l1 l2 l1' l2' A A' B B' b b'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] b : B @ l2 ] -> [ G ; Γ ⊢[ i ] b' : B @ l2 ] /\ [ G ; Γ ⊢[ i ] b ≅ b' : B @ l2 ] ->
  [ G ; Γ ⊢[ i ] tmInr l1' l2' A' B' b' : tySum l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmInr l1 l2 A B b ≅ tmInr l1' l2' A' B' b' : tySum l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB] Hb [Hb' Hbb].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_inr_q Hv Q1 Q2 HA' HAA HB' HBB Hb') | apply eqtm_inr; auto].
Qed.

(** [case]: the right pieces moved to the right contexts along [case_facts_D]. *)
Lemma sc_case_q {Γ l1 l2 l3 l1' l2' l3' A A' B B' M M' c1' c2' t t'} : i <> lV ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> lequiv (gL G) l3 l3' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c1' : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ,, B @ l2 ⊢[ i ] c2' : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ⊢[ i ] t : tySum l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] t' : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmCase l1' l2' l3' A' B' M' c1' c2' t' : M[lsingle t] @ l3 ].
Proof using Hty.
  intros Hv Q1 Q2 Q3 HA HA' HAA HB HB' HBB HM HM' HMM Hc1' Hc2' Ht Ht' Htt.
  destruct (case_facts_D (l4 := l1') (l5 := l2') Q1 Q2 (sc_ty HA) (sc_eqty HAA) (sc_ty HA') (sc_ty HB)
              (sc_eqty HBB) (sc_ty HB') (sc_ty HM) (sc_eqty HMM) (sc_ty HM')) as (CS & CA & CB & EB1 & EB2).
  pose proof (lequiv_wf_r _ _ _ Q1) as H1'. pose proof (lequiv_wf_r _ _ _ Q2) as H2'.
  pose proof (lequiv_wf_r _ _ _ Q3) as H3'.
  apply (sc_conv (T' := M'[lsingle t'])).
  - eapply wf_lconv with (l' := l3'); [| exact Q3].
    apply wf_case; [exact Hv | exact H1' | exact H2' | exact H3' | | | | | |].
    + eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
    + eapply wft_lconv; [exact HB' | apply lequiv_sym, Q2].
    + eapply wft_lconv; [exact (sc_cty CS HM') | apply lequiv_sym, Q3].
    + eapply wf_lconv; [apply (sc_conv (sc_ctm CA Hc1') EB1) | apply lequiv_sym, Q3].
    + eapply wf_lconv; [apply (sc_conv (sc_ctm CB Hc2') EB2) | apply lequiv_sym, Q3].
    + apply (sc_conv (T' := tySum l1 l2 A B)).
      * eapply wf_lconv; [exact Ht' | apply lequiv_sym, lequiv_lmax'; assumption].
      * eapply eqty_lconv; [apply eqty_sym, eqty_sum; [discriminate | exact Q1 | exact Q2
                                                        | exact (sc_eqty HAA) | exact (sc_eqty HBB)]
                           | apply lequiv_sym, lequiv_lmax'; assumption].
  - exact (eqty_subst_single_D (sc_eqty HMM) (sc_ty HM') (sc_eqtm Htt) (sc_tm Ht) (sc_tm Ht')).
Qed.
Lemma sc_case {Γ l1 l2 l3 l1' l2' l3' A A' B B' M M' c1 c1' c2 c2' t t'} : i <> lV ->
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l3 -> lwf (gL G) l1' -> lwf (gL G) l2' -> lwf (gL G) l3' ->
  leqv l1 l1' -> leqv l2 l2' -> leqv l3 l3' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] /\
  [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c1 : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c1' : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] /\
  [ G ; Γ ,, A @ l1 ⊢[ i ] c1 ≅ c1' : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ,, B @ l2 ⊢[ i ] c2 : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ,, B @ l2 ⊢[ i ] c2' : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] /\
  [ G ; Γ ,, B @ l2 ⊢[ i ] c2 ≅ c2' : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Γ ⊢[ i ] t : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t' : tySum l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] t ≅ t' : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmCase l1' l2' l3' A' B' M' c1' c2' t' : M[lsingle t] @ l3 ] /\
  [ G ; Γ ⊢[ i ] tmCase l1 l2 l3 A B M c1 c2 t ≅ tmCase l1' l2' l3' A' B' M' c1' c2' t' : M[lsingle t] @ l3 ].
Proof using Hty.
  intros Hv H1 H2 H3 H1' H2' H3' E1 E2 E3 HA [HA' HAA] HB [HB' HBB] HM [HM' HMM] Hc1 [Hc1' Hcc1]
    Hc2 [Hc2' Hcc2] Ht [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2. pose proof (lq H3 H3' E3) as Q3.
  split; [exact (sc_case_q Hv Q1 Q2 Q3 HA HA' HAA HB HB' HBB HM HM' HMM Hc1' Hc2' Ht Ht' Htt)
         | apply eqtm_case; auto].
Qed.

(** The codes of [Empty] and [+] (M12c). *)
Lemma sc_code_empty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tmEmpty l' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmEmpty l ≅ tmEmpty l' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hc HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - apply (sc_conv (T' := tyU l')).
    + eapply wf_lconv; [apply wf_code_empty; auto | apply lequiv_lsuc', Q].
    + rewrite Hty in HΓ. apply eqty_U; [discriminate | exact HΓ | exact Q].
  - apply eqtm_code_empty; auto.
Qed.
Lemma sc_code_sum_q {Γ l1 l2 l1' l2' s' t'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSum l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using Hty.
  intros Hv Q1 Q2 Hs' Ht'.
  pose proof (sc_ctx_tm Hs') as HΓ.
  assert (F : forall l l' x, lequiv (gL G) l l' -> [ G ; Γ ⊢[ i ] x : tyU l @ lsuc l ] ->
            [ G ; Γ ⊢[ i ] x : tyU l' @ lsuc l' ]).
  { intros l l' x Q Hx. apply (sc_conv (T' := tyU l)); [eapply wf_lconv; [exact Hx | apply lequiv_lsuc', lequiv_sym, Q]|].
    apply eqty_U; [discriminate | exact HΓ | apply lequiv_sym, Q]. }
  apply (sc_conv (T' := tyU (lmax l1' l2'))).
  - eapply wf_lconv; [apply wf_code_sum; [exact Hv | eauto using lequiv_wf_r | eauto using lequiv_wf_r
                                         | exact (F _ _ _ Q1 Hs') | exact (F _ _ _ Q2 Ht')]
                     | apply lequiv_lsuc', lequiv_lmax'; assumption].
  - apply eqty_U; [discriminate | exact HΓ | apply lequiv_lmax'; assumption].
Qed.
Lemma sc_code_sum {Γ l1 l2 l1' l2' s s' t t'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] t : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] t' : tyU l2 @ lsuc l2 ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmSum l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmSum l1 l2 s t ≅ tmSum l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 Hs [Hs' Hss] Ht [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_code_sum_q Hv Q1 Q2 Hs' Ht') | apply eqtm_code_sum; auto].
Qed.

(** Well-founded trees (M13a; every layer but V since M13b): the right
    telescope of [elim_W] is formed at the layer itself (WGen), and moved
    along [W_facts] at P. *)
Lemma sc_W_q {Γ l1 l2 l1' l2' A A' B'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] -> [ G ; Γ ⊢[ i ] tyW l1' l2' A' B' @ lmax l1 l2 ].
Proof using Hty.
  intros Hv Q1 Q2 HA HA' HAA HB'.
  eapply wft_lconv; [apply wft_W; [exact Hv | eauto using lequiv_wf_r | eauto using lequiv_wf_r | |]
                    | exact (lequiv_lmax' _ _ _ _ _ Q1 Q2)].
  - eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
  - eapply wft_lconv; [exact (sc_cty (sc_ext HA HAA Q1) HB') | apply lequiv_sym, Q2].
Qed.
Lemma sc_W {Γ l1 l2 l1' l2' A A' B B'} : i <> lV ->
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyW l1' l2' A' B' @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tyW l1 l2 A B ≅ tyW l1' l2' A' B' @ lmax l1 l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_W_q Hv Q1 Q2 HA HA' HAA HB') | apply eqty_W; auto].
Qed.

Lemma sc_sup_q {Γ l1 l2 l1' l2' A A' B B' a a' f'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] f' : tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩ @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ⊢[ i ] tmSup l1' l2' A' B' a' f' : tyW l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hv Q1 Q2 HA HA' HAA HB HB' HBB Ha Ha' Haa Hf'.
  pose proof (lequiv_wf_r _ _ _ Q1) as W1'. pose proof (lequiv_wf_r _ _ _ Q2) as W2'.
  assert (QL : lequiv (gL G) (lmax l1 l2) (lmax l1' l2')) by exact (lequiv_lmax' _ _ _ _ _ Q1 Q2).
  pose proof (@W_sup_feq G lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Q1 Q2 (sc_ty HA) (sc_eqty HAA)
                (sc_ty HB) (sc_eqty HBB) (sc_eqtm Haa) (sc_tm Ha) (sc_tm Ha')) as EF.
  apply (sc_conv (T' := tyW l1' l2' A' B')).
  - eapply wf_lconv; [| exact QL].
    apply wf_sup; [exact Hv | exact W1' | exact W2' | | | |].
    + eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1].
    + eapply wft_lconv; [exact (sc_cty (sc_ext HA HAA Q1) HB') | apply lequiv_sym, Q2].
    + apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Ha' | apply lequiv_sym, Q1]|].
      eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q1].
    + apply (sc_conv (T' := tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩)).
      * eapply wf_lconv; [exact Hf' | apply lequiv_sym, lequiv_lmax'; assumption].
      * eapply eqty_lconv; [apply eqty_sym, EF | apply lequiv_sym, lequiv_lmax'; assumption].
  - apply eqty_W; [discriminate | exact Q1 | exact Q2 | exact (sc_ty HA) | exact (sc_eqty HAA) | exact (sc_eqty HBB)].
Qed.
Lemma sc_sup {Γ l1 l2 l1' l2' A A' B B' a a' f f'} : i <> lV ->
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] a : A @ l1 ] -> [ G ; Γ ⊢[ i ] a' : A @ l1 ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] f : tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩ @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ⊢[ i ] f' : tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩ @ lmax l2 (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] f ≅ f' : tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩ @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ⊢[ i ] tmSup l1' l2' A' B' a' f' : tyW l1 l2 A B @ lmax l1 l2 ] /\
  [ G ; Γ ⊢[ i ] tmSup l1 l2 A B a f ≅ tmSup l1' l2' A' B' a' f' : tyW l1 l2 A B @ lmax l1 l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] HB [HB' HBB] Ha [Ha' Haa] Hf [Hf' Hff].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_sup_q Hv Q1 Q2 HA HA' HAA HB HB' HBB Ha Ha' Haa Hf') | apply eqtm_sup; auto].
Qed.

Lemma sc_elimW_q {Γ l1 l2 l3 l1' l2' l3' A A' B B' M M' c' t t'} : i <> lV ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> lequiv (gL G) l3 l3' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] wihty l1 l2 l3 A B M @ lmax l2 l3 ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ⊢[ i ] c' : wstepty l1 l2 A B M @ l3 ] ->
  [ G ; Γ ⊢[ i ] t : tyW l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢[ i ] t' : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmElimW l1' l2' l3' A' B' M' c' t' : M[lsingle t] @ l3 ].
Proof using Hty.
  intros Hv Q1 Q2 Q3 HA HA' HAA HB HB' HBB HM HM' HMM HF HI Hc' Ht Ht' Htt.
  destruct (@W_facts G lD eq_refl ltac:(discriminate) _ _ _ _ l1' l2' l3' _ _ _ _ _ _ Q1 Q2 Q3
              (sc_eqty HAA) (sc_ty HA) (sc_ty HA') (sc_eqty HBB) (sc_ty HB) (sc_ty HB')
              (sc_eqty HMM) (sc_ty HM) (sc_ty HM') (sc_ty HF) (sc_ty HI)) as (EW & CW & CT & ES).
  pose proof (lequiv_wf_r _ _ _ Q1) as W1'. pose proof (lequiv_wf_r _ _ _ Q2) as W2'.
  pose proof (lequiv_wf_r _ _ _ Q3) as W3'.
  assert (QL : lequiv (gL G) (lmax l1 l2) (lmax l1' l2')) by exact (lequiv_lmax' _ _ _ _ _ Q1 Q2).
  assert (HA'4 : [ G ; Γ ⊢[ i ] A' @ l1' ]) by (eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1]).
  assert (HB'5 : [ G ; Γ ,, A' @ l1' ⊢[ i ] B' @ l2' ])
    by (eapply wft_lconv; [exact (sc_cty (sc_ext HA HAA Q1) HB') | apply lequiv_sym, Q2]).
  assert (HW' : [ G ; Γ ⊢[ i ] tyW l1' l2' A' B' @ lmax l1' l2' ])
    by (apply wft_W; [exact Hv | exact W1' | exact W2' | exact HA'4 | exact HB'5]).
  assert (HM'6 : [ G ; Γ ,, tyW l1' l2' A' B' @ lmax l1' l2' ⊢[ i ] M' @ l3' ])
    by (eapply wft_lconv; [exact (sc_cty CW HM') | apply lequiv_sym, Q3]).
  pose proof (W_fty_wf_i Hv W1' W2' HW' HB'5) as HF'.
  assert (WF' : lwf (gL G) (lmax l2' (lmax l1' l2'))) by (cbn; repeat split; assumption).
  assert (HI' : [ G ; Γ ,, A' @ l1' ,, wfty l1' l2' A' B' @ lmax l2' (lmax l1' l2')
                  ⊢[ i ] wihty l1' l2' l3' A' B' M' @ lmax l2' l3' ]).
  { apply (W_ih_wf_i Hv W1' W2' W3' HW' HB'5 HM'6 HF' WF'); [| apply lequiv_refl, WF'].
    rewrite Hty. apply eqty_refl, sc_ty, HF'. }
  assert (Hc'' : [ G ; Γ ,, A' @ l1' ,, wfty l1' l2' A' B' @ lmax l2' (lmax l1' l2')
                   ,, wihty l1' l2' l3' A' B' M' @ lmax l2' l3' ⊢[ i ] c' : wstepty l1' l2' A' B' M' @ l3' ]).
  { apply (sc_ctm CT). eapply wf_lconv; [| apply lequiv_sym, Q3].
    apply (sc_conv Hc'), eqty_sym, ES. }
  assert (Ht'W : [ G ; Γ ⊢[ i ] t' : tyW l1' l2' A' B' @ lmax l1' l2' ]).
  { eapply wf_lconv; [| apply lequiv_sym, QL].
    apply (sc_conv Ht'), eqty_sym, EW. }
  apply (sc_conv (T' := M'[lsingle t'])).
  - eapply wf_lconv with (l' := l3'); [| exact Q3].
    apply wf_elimW; [exact Hv | exact W1' | exact W2' | exact W3' | exact HA'4 | exact HB'5 | exact HM'6
                    | exact HF' | exact HI' | exact Hc'' | exact Ht'W].
  - exact (eqty_subst_single_D (sc_eqty HMM) (sc_ty HM') (sc_eqtm Htt) (sc_tm Ht) (sc_tm Ht')).
Qed.
Lemma sc_elimW {Γ l1 l2 l3 l1' l2' l3' A A' B B' M M' c c' t t'} : i <> lV ->
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l3 -> lwf (gL G) l1' -> lwf (gL G) l2' -> lwf (gL G) l3' ->
  leqv l1 l1' -> leqv l2 l2' -> leqv l3 l3' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B' @ l2 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M' @ l3 ] /\
  [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ⊢[ i ] wihty l1 l2 l3 A B M @ lmax l2 l3 ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ⊢[ i ] c : wstepty l1 l2 A B M @ l3 ] ->
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ⊢[ i ] c' : wstepty l1 l2 A B M @ l3 ] /\
  [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
      ⊢[ i ] c ≅ c' : wstepty l1 l2 A B M @ l3 ] ->
  [ G ; Γ ⊢[ i ] t : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] t' : tyW l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] tmElimW l1' l2' l3' A' B' M' c' t' : M[lsingle t] @ l3 ] /\
  [ G ; Γ ⊢[ i ] tmElimW l1 l2 l3 A B M c t ≅ tmElimW l1' l2' l3' A' B' M' c' t' : M[lsingle t] @ l3 ].
Proof using Hty.
  intros Hv H1 H2 H3 H1' H2' H3' E1 E2 E3 HA [HA' HAA] HB [HB' HBB] HM [HM' HMM] HF HI Hc0 [Hc' Hcc]
    Ht [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2. pose proof (lq H3 H3' E3) as Q3.
  split; [exact (sc_elimW_q Hv Q1 Q2 Q3 HA HA' HAA HB HB' HBB HM HM' HMM HF HI Hc' Ht Ht' Htt)
         | apply eqtm_elimW; auto].
Qed.

(** The code of [W] (M13b), as [Σ]'s. *)
Lemma sc_code_W {Γ l1 l2 l1' l2' s s' t t'} : i <> lV -> lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ] /\
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmW l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] /\
  [ G ; Γ ⊢[ i ] tmW l1 l2 s t ≅ tmW l1' l2' s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof using Hty.
  intros Hc H1 H2 H1' H2' E1 E2 Hs [Hs' Hss] [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (sc_ctx_tm Hs) as HΓ.
  pose proof Hc as Hv.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; auto).
  assert (HElE : [ G ; Γ ⊢[ i ] tyEl l1 s ≅ tyEl l1' s' @ l1 ]) by (apply eqty_El; auto).
  pose proof (sc_ext HEl HElE Q1) as Hx.
  assert (Q12 : lequiv (gL G) (lmax l1 l2) (lmax l1' l2')) by (apply lequiv_lmax'; assumption).
  split.
  - apply (sc_conv (T' := tyU (lmax l1' l2'))).
    + eapply wf_lconv; [apply wf_code_W; auto | apply lequiv_lsuc', Q12].
      * apply (sc_conv (T' := tyU l1)); [eapply wf_lconv; [exact Hs' | apply lequiv_lsuc', lequiv_sym, Q1]|].
        apply eqty_U; [discriminate | exact HΓ | apply lequiv_sym, Q1].
      * apply (sc_conv (T' := tyU l2));
          [eapply wf_lconv; [exact (sc_ctm Hx Ht') | apply lequiv_lsuc', lequiv_sym, Q2]|].
        apply eqty_U; [discriminate | exact (eqctx_wf_r (i := lD) eq_refl Hx) | apply lequiv_sym, Q2].
    + apply eqty_U; [discriminate | exact HΓ | exact Q12].
  - apply eqtm_code_W; auto.
Qed.

(** Length-indexed tuples and finite indices (M14a; every layer but V
    since M14b). *)
Lemma sc_vec {Γ l l' A A' n n'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] /\ [ G ; Γ ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyVec l' A' n' @ l ] /\ [ G ; Γ ⊢[ i ] tyVec l A n ≅ tyVec l' A' n' @ l ].
Proof using .
  intros Hv Hl Hl' E HA [HA' HAA] [Hn' Hnn]. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_vec; auto | exact Q].
    eapply wft_lconv; [exact HA' | apply lequiv_sym, Q].
  - apply eqty_vec; auto.
Qed.

Lemma sc_fin {Γ n n'} : i <> lV ->
  [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] /\ [ G ; Γ ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyFin n' @ lzero ] /\ [ G ; Γ ⊢[ i ] tyFin n ≅ tyFin n' @ lzero ].
Proof using . intros Hv [Hn' Hnn]. split; [apply wft_fin | apply eqty_fin]; auto. Qed.

(** The codes of [Vec] and [Fin] (M14b; every layer but V), as [+]'s. *)
Lemma sc_code_vec {Γ l l' s s' n n'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] /\ [ G ; Γ ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmVec l' s' n' : tyU l @ lsuc l ] /\
  [ G ; Γ ⊢[ i ] tmVec l s n ≅ tmVec l' s' n' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hv Hl Hl' E _ [Hs' Hss] [Hn' Hnn]. pose proof (lq Hl Hl' E) as Q.
  pose proof (sc_ctx_tm Hs') as HΓ. split.
  - apply (sc_conv (T' := tyU l')).
    + eapply wf_lconv; [apply wf_code_vec; [exact Hv | exact Hl' | | exact Hn'] | apply lequiv_lsuc', Q].
      apply (sc_conv (T' := tyU l)); [eapply wf_lconv; [exact Hs' | apply lequiv_lsuc', lequiv_sym, Q]|].
      apply eqty_U; [discriminate | exact HΓ | apply lequiv_sym, Q].
    + apply eqty_U; [discriminate | exact HΓ | exact Q].
  - apply eqtm_code_vec; auto.
Qed.

Lemma sc_code_fin {Γ n n'} : i <> lV ->
  [ G ; Γ ⊢[ i ] n' : tyNat @ lzero ] /\ [ G ; Γ ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmFin n' : tyU lzero @ lsuc lzero ] /\
  [ G ; Γ ⊢[ i ] tmFin n ≅ tmFin n' : tyU lzero @ lsuc lzero ].
Proof using . intros Hv [Hn' Hnn]. split; [apply wf_code_fin | apply eqtm_code_fin]; auto. Qed.

(** Finitary well-founded trees (M15a; every layer but V since M15b):
    as [W]'s, moved along [Wf_facts] at P. The right telescope of
    [elim_Wf] is typed from its own components ([WfGen]). *)
Lemma sc_eqc_inv {Γ Γ' A A' l l'} : [ G ⊢[ lD ] Γ ,, A @ l ≅ Γ' ,, A' @ l' ] ->
  [ G ⊢[ lD ] Γ ≅ Γ' ] /\ [ G ; Γ ⊢[ lD ] A ≅ A' @ l ].
Proof using . intros H; inversion H; subst; split; assumption. Qed.

Lemma sc_wf_q {Γ l l' A A' N'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] tyWf l' A' N' @ l ].
Proof using Hty.
  intros Hv Q HA HA' HAA HN'.
  eapply wft_lconv; [apply wft_wf; [exact Hv | eauto using lequiv_wf_r | |] | exact Q].
  - eapply wft_lconv; [exact HA' | apply lequiv_sym, Q].
  - exact (sc_ctm (sc_ext HA HAA Q) HN').
Qed.
Lemma sc_wf {Γ l l' A A' N N'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] /\ [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyWf l' A' N' @ l ] /\ [ G ; Γ ⊢[ i ] tyWf l A N ≅ tyWf l' A' N' @ l ].
Proof using Hty.
  intros Hv Hl Hl' E HA [HA' HAA] HN [HN' HNN]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_wf_q Hv Q HA HA' HAA HN') | apply eqty_wf; auto].
Qed.

Lemma sc_supf_q {Γ l l' A A' N N' a a' cs'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] tmSupf l' A' N' a' cs' : tyWf l A N @ l ].
Proof using Hty.
  intros Hv Q HA HA' HAA HN HN' HNN Ha Ha' Haa Hcs'.
  pose proof (lequiv_wf_r _ _ _ Q) as W'.
  pose proof (@Wf_cs_feq G lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ Q (sc_ty HA) (sc_eqty HAA)
                (sc_tm HN) (sc_eqtm HNN) (sc_eqtm Haa) (sc_tm Ha) (sc_tm Ha')) as EF.
  apply (sc_conv (T' := tyWf l' A' N')).
  - eapply wf_lconv; [| exact Q].
    apply wf_supf; [exact Hv | exact W' | | | |].
    + eapply wft_lconv; [exact HA' | apply lequiv_sym, Q].
    + exact (sc_ctm (sc_ext HA HAA Q) HN').
    + apply (sc_conv (T' := A)); [eapply wf_lconv; [exact Ha' | apply lequiv_sym, Q]|].
      eapply eqty_lconv; [apply eqty_sym, sc_eqty, HAA | apply lequiv_sym, Q].
    + apply (sc_conv (T' := tyVec l (tyWf l A N) N[lsingle a])).
      * eapply wf_lconv; [exact Hcs' | apply lequiv_sym, Q].
      * eapply eqty_lconv; [apply eqty_sym, EF | apply lequiv_sym, Q].
  - apply eqty_wf; [discriminate | exact Q | exact (sc_ty HA) | exact (sc_eqty HAA) | exact (sc_eqtm HNN)].
Qed.
Lemma sc_supf {Γ l l' A A' N N' a a' cs cs'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] /\ [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ] /\
  [ G ; Γ ⊢[ i ] cs ≅ cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
  [ G ; Γ ⊢[ i ] tmSupf l' A' N' a' cs' : tyWf l A N @ l ] /\
  [ G ; Γ ⊢[ i ] tmSupf l A N a cs ≅ tmSupf l' A' N' a' cs' : tyWf l A N @ l ].
Proof using Hty.
  intros Hv Hl Hl' E HA [HA' HAA] HN [HN' HNN] Ha [Ha' Haa] Hcs [Hcs' Hcscs]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_supf_q Hv Q HA HA' HAA HN HN' HNN Ha Ha' Haa Hcs') | apply eqtm_supf; auto].
Qed.

Lemma sc_elimWf_q {Γ l1 l2 l1' l2' A A' N N' M M' c' t t'} : i <> lV ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] -> [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M' @ l2 ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ] wfihty l1 l2 A N M @ lmax lzero l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ⊢[ i ] c' : wfstepty l1 A N M @ l2 ] ->
  [ G ; Γ ⊢[ i ] t : tyWf l1 A N @ l1 ] -> [ G ; Γ ⊢[ i ] t' : tyWf l1 A N @ l1 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyWf l1 A N @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmElimWf l1' l2' A' N' M' c' t' : M[lsingle t] @ l2 ].
Proof using Hty.
  intros Hv Q1 Q2 HA HA' HAA HN HN' HNN HM HM' HMM HI Hc' Ht Ht' Htt.
  destruct (@Wf_facts G lD eq_refl ltac:(discriminate) _ _ _ l1' l2' _ _ _ _ _ _ Q1 Q2
              (sc_eqty HAA) (sc_ty HA) (sc_ty HA') (sc_eqtm HNN) (sc_tm HN) (sc_tm HN')
              (sc_eqty HMM) (sc_ty HM) (sc_ty HI)) as (EW & CW & CT & ES).
  destruct (sc_eqc_inv CT) as [CT2 EI]. destruct (sc_eqc_inv CT2) as [CA EC].
  pose proof (lequiv_wf_r _ _ _ Q1) as W1'. pose proof (lequiv_wf_r _ _ _ Q2) as W2'.
  pose proof (lequiv_leqv _ _ _ Q1) as E1. pose proof (lequiv_leqv _ _ _ Q2) as E2.
  assert (HA'4 : [ G ; Γ ⊢[ i ] A' @ l1' ]) by (eapply wft_lconv; [exact HA' | apply lequiv_sym, Q1]).
  pose proof (sc_ctm (sc_ext HA HAA Q1) HN') as HN'5.
  assert (HW' : [ G ; Γ ⊢[ i ] tyWf l1' A' N' @ l1' ]) by (apply wft_wf; assumption).
  assert (HM'6 : [ G ; Γ ,, tyWf l1' A' N' @ l1' ⊢[ i ] M' @ l2' ])
    by (eapply wft_lconv; [exact (sc_cty CW HM') | apply lequiv_sym, Q2]).
  (* the right telescope from its own components ([WfGen]) *)
  pose proof (Wf_cs_wf_g Hv W1' HW' HN'5) as HC'.
  pose proof (ext_g (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ HN'5) HC' W1') as HΓC'.
  pose proof (Wf_ih_wf_g Hv W1' W2' HW' HN'5 HM'6 HΓC' (eqty_refl _ _ _ _ _ (lift_ty HC' (lle_self_typeof _)))
                (lequiv_refl _ _ W1')) as HI'.
  assert (Hc'' : [ G ; Γ ,, A' @ l1' ,, wfcsty l1' A' N' @ l1' ,, wfihty l1' l2' A' N' M' @ lmax lzero l2'
                   ⊢[ i ] c' : wfstepty l1' A' N' M' @ l2' ]).
  { apply (sc_ctm CT). eapply wf_lconv; [| apply lequiv_sym, Q2].
    apply (sc_conv Hc'), eqty_sym, ES. }
  assert (Ht'W : [ G ; Γ ⊢[ i ] t' : tyWf l1' A' N' @ l1' ]).
  { eapply wf_lconv; [| apply lequiv_sym, Q1].
    apply (sc_conv Ht'), eqty_sym, EW. }
  apply (sc_conv (T' := M'[lsingle t'])).
  - eapply wf_lconv with (l' := l2'); [| exact Q2].
    apply wf_elimWf; assumption.
  - exact (eqty_subst_single_D (sc_eqty HMM) (sc_ty HM') (sc_eqtm Htt) (sc_tm Ht) (sc_tm Ht')).
Qed.
Lemma sc_elimWf {Γ l1 l2 l1' l2' A A' N N' M M' c c' t t'} : i <> lV ->
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] N' : tyNat @ lzero ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M @ l2 ] ->
  [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M' @ l2 ] /\ [ G ; Γ ,, tyWf l1 A N @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] wfcsty l1 A N @ l1 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ⊢[ i ] wfihty l1 l2 A N M @ lmax lzero l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ⊢[ i ] c : wfstepty l1 A N M @ l2 ] ->
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ⊢[ i ] c' : wfstepty l1 A N M @ l2 ] /\
  [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
      ⊢[ i ] c ≅ c' : wfstepty l1 A N M @ l2 ] ->
  [ G ; Γ ⊢[ i ] t : tyWf l1 A N @ l1 ] ->
  [ G ; Γ ⊢[ i ] t' : tyWf l1 A N @ l1 ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyWf l1 A N @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmElimWf l1' l2' A' N' M' c' t' : M[lsingle t] @ l2 ] /\
  [ G ; Γ ⊢[ i ] tmElimWf l1 l2 A N M c t ≅ tmElimWf l1' l2' A' N' M' c' t' : M[lsingle t] @ l2 ].
Proof using Hty.
  intros Hv H1 H2 H1' H2' E1 E2 HA [HA' HAA] HN [HN' HNN] HM [HM' HMM] HC HI Hc0 [Hc' Hcc]
    Ht [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_elimWf_q Hv Q1 Q2 HA HA' HAA HN HN' HNN HM HM' HMM HI Hc' Ht Ht' Htt)
         | apply eqtm_elimWf; auto].
Qed.

(** The code of [Wf] (M15b), as [W]'s. *)
Lemma sc_code_wf {Γ l l' s s' n n'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n : tyNat @ lzero ] ->
  [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n' : tyNat @ lzero ] /\ [ G ; Γ ,, tyEl l s @ l ⊢[ i ] n ≅ n' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmWf l' s' n' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmWf l s n ≅ tmWf l' s' n' : tyU l @ lsuc l ].
Proof using Hty.
  intros Hv Hl Hl' E Hs [Hs' Hss] _ [Hn' Hnn]. pose proof (lq Hl Hl' E) as Q.
  pose proof (sc_ctx_tm Hs) as HΓ.
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l s @ l ]) by (apply wft_El; auto).
  assert (HElE : [ G ; Γ ⊢[ i ] tyEl l s ≅ tyEl l' s' @ l ]) by (apply eqty_El; auto).
  split.
  - apply (sc_conv (T' := tyU l')).
    + eapply wf_lconv; [apply wf_code_wf; [exact Hv | exact Hl' | |] | apply lequiv_lsuc', Q].
      * apply (sc_conv (T' := tyU l)); [eapply wf_lconv; [exact Hs' | apply lequiv_lsuc', lequiv_sym, Q]|].
        apply eqty_U; [discriminate | exact HΓ | apply lequiv_sym, Q].
      * exact (sc_ctm (sc_ext HEl HElE Q) Hn').
    + apply eqty_U; [discriminate | exact HΓ | exact Q].
  - apply eqtm_code_wf; auto.
Qed.

(** Propositional truncation (M16a), gated by [compt]: at [i] itself, by
    the presupposition lemmas' right-hand sides ([compt i] and [lle i lD]
    make [i] layer D). *)
Lemma sc_tySq {Γ l l' A A'} : compt i -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] tySq l' A' @ l ] /\ [ G ; Γ ⊢[ i ] tySq l A ≅ tySq l' A' @ l ].
Proof using .
  intros cp Hl Hl' E HA [HA' HAA]. pose proof (lq Hl Hl' E) as Q.
  split; [| apply eqty_sq; auto].
  eapply wft_lconv; [| exact Q].
  apply wft_sq; [exact cp | exact Hl' |]. eapply wft_lconv; [exact HA' | apply lequiv_sym, Q].
Qed.

Lemma sc_sq {Γ l l' A A' a a'} : compt i -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] /\ [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmSq l' A' a' : tySq l A @ l ] /\
  [ G ; Γ ⊢[ i ] tmSq l A a ≅ tmSq l' A' a' : tySq l A @ l ].
Proof using .
  intros cp Hl Hl' E HA [HA' HAA] Ha [Ha' Haa]. pose proof (lq Hl Hl' E) as Q.
  pose proof (compt_typeof_self i cp) as Hi'. pose proof (compt_notV i cp) as Hv'.
  split; [| apply eqtm_sq; auto].
  eapply pre_sq_r; eassumption.
Qed.

Lemma sc_elimSq {Γ l1 l2 l1' l2' A A' M M' c c' t t'} : compt i ->
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A' @ l1 ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M @ l2 ] ->
  [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M' @ l2 ] /\ [ G ; Γ ,, tySq l1 A @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] c' : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ] /\
  [ G ; Γ ,, A @ l1 ⊢[ i ] c ≅ c' : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ] ->
  [ G ; Γ ⊢[ i ] t : tySq l1 A @ l1 ] ->
  [ G ; Γ ⊢[ i ] t' : tySq l1 A @ l1 ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tySq l1 A @ l1 ] ->
  [ G ; Γ ⊢[ i ] tmElimSq l1' l2' A' M' c' t' : tySq l2 M[lsingle t] @ l2 ] /\
  [ G ; Γ ⊢[ i ] tmElimSq l1 l2 A M c t ≅ tmElimSq l1' l2' A' M' c' t' : tySq l2 M[lsingle t] @ l2 ].
Proof using .
  intros cp H1 H2 H1' H2' E1 E2 HA [HA' HAA] HM [HM' HMM] Hc [Hc' Hcc] Ht [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  pose proof (compt_typeof_self i cp) as Hi'. pose proof (compt_notV i cp) as Hv'.
  split; [| apply eqtm_elimSq; auto].
  eapply pre_elimSq_r; eassumption.
Qed.

End SC.

(** ** The lemma *)

Ltac sc_prep :=
  try match goal with H : lle lM lD |- _ => destruct (lle_D_notM' H eq_refl) end;
  repeat match goal with IH : lle ?j lD -> _, H : lle ?j lD |- _ => specialize (IH H) end;
  repeat match goal with
         | IH : forall n A k, in_ctx ?Δ n A k -> lle ?j lD -> _, H : lle ?j lD |- _ =>
             pose proof (fun n A k h => IH n A k h H); clear IH
         end;
  (* the right-hand syntax has the left's shape *)
  repeat leq_cases;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : ?x = ?y |- _ => is_var x; subst x
         end.

(** Conversions: the induction hypothesis, converted. *)
Ltac sc_conv_case :=
  match goal with
  | IH : forall x, ty_leq ?T x -> ty_lwf _ x -> _ /\ _, E : ty_leq ?T ?X, W : ty_lwf _ ?X |- _ =>
      destruct (IH X E W) as [?H1 ?H2]; split;
      first [eapply wft_lconv | eapply eqty_lconv]; eassumption
  | IH : forall x, tm_leq ?t x -> tm_lwf _ x -> _ /\ _, E : tm_leq ?t ?x, W : tm_lwf _ ?x |- _ =>
      destruct (IH x E W) as [?H1 ?H2]; split;
      first [ eapply wf_conv; eassumption | eapply wf_lconv; eassumption
            | eapply eqtm_conv; eassumption | eapply eqtm_lconv; eassumption ]
  end.

(** Global variables *)
Ltac sc_gvar_case :=
  match goal with
  | Hin : in_gctx _ _ (gdTy ?Δ _ _), E : lsub_leq ?d ?d', W : lsub_lwf _ ?d',
    HΓ : wf_ctx _ (typeof ?i) ?Γ, Hle : lle ?i lD |- _ =>
      pose proof HΓ as HΓD; rewrite (lle_D_typeof _ Hle) in HΓD;
      destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓD) Hin) as [HΔ _];
      destruct (sc_entries Hle HΓD HΔ ltac:(eassumption) ltac:(eassumption) E W
                  ltac:(eassumption) ltac:(eassumption)) as (Ht' & Nd' & Hd' & Heq & Hdd);
      split; [eapply wft_gvar | eapply eqty_gvar]; eassumption
  | Hin : in_gctx _ _ (gdTm ?Δ _ ?T _), E : lsub_leq ?d ?d', W : lsub_lwf _ ?d',
    HΓ : wf_ctx _ (typeof ?i) ?Γ, Hle : lle ?i lD |- _ =>
      pose proof HΓ as HΓD; rewrite (lle_D_typeof _ Hle) in HΓD;
      destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓD) Hin) as (HΔ & HT & _);
      destruct (sc_entries Hle HΓD HΔ ltac:(eassumption) ltac:(eassumption) E W
                  ltac:(eassumption) ltac:(eassumption)) as (Ht' & Nd' & Hd' & Heq & Hdd);
      split; [ apply (sc_conv Hle (T' := T[d'])); [eapply wf_gvar; eassumption |];
               exact (wf_ty_func (i := lD) eq_refl HT Hdd)
             | eapply eqtm_gvar; eassumption ]
  (* a defined global (M9): its carried body, by its hypothesis (M9_DESIGN.md N2) *)
  | Hin : in_gctx _ _ (gdDef ?Δ ?T _ ?t0), E : lsub_leq ?d ?d', W : lsub_lwf _ ?d',
    Hl0 : tm_leq ?t0 ?b, Eb : tm_leq ?b ?b', Wb : tm_lwf _ ?b',
    IHb : forall x, tm_leq ?b x -> tm_lwf _ x -> _ /\ _,
    HΓ : wf_ctx _ (typeof ?i) ?Γ, Hle : lle ?i lD |- _ =>
      pose proof HΓ as HΓD; rewrite (lle_D_typeof _ Hle) in HΓD;
      destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓD) Hin) as (HΔ & HT & _);
      destruct (IHb _ Eb Wb) as [Hb' Hbb]; pose proof (tm_leq_trans _ _ _ Hl0 Eb) as Hl0';
      destruct (sc_entries Hle HΓD HΔ ltac:(eassumption) ltac:(eassumption) E W
                  ltac:(eassumption) ltac:(eassumption)) as (Ht' & Nd' & Hd' & Heq & Hdd);
      split; [ apply (sc_conv Hle (T' := T[d'])); [eapply wf_gdef; eassumption |];
               exact (wf_ty_func (i := lD) eq_refl HT Hdd)
             | eapply eqtm_gdef; eassumption ]
  end.

Theorem static_code :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> lle i lD ->
     forall T', ty_leq T T' -> ty_lwf (gL G) T' -> [ G ; Γ ⊢[ i ] T' @ l ] /\ [ G ; Γ ⊢[ i ] T ≅ T' @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> lle i lD ->
     forall t', tm_leq t t' -> tm_lwf (gL G) t' -> [ G ; Γ ⊢[ i ] t' : T @ l ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I; sc_prep; cbn in *; sc_prep.
  all: first
    [ (* the same syntax *)
      solve [split; [econstructor; eauto | first [apply eqty_refl | apply eqtm_refl]; econstructor; eauto]]
    | solve [sc_conv_case]
    | solve [sc_gvar_case]
    | solve [eapply sc_U; eauto] | solve [eapply sc_El; eauto] | solve [eapply sc_pi; eauto]
    | solve [eapply sc_code_U; eauto] | solve [eapply sc_code_pi; eauto]
    | solve [eapply sc_lam; eauto] | solve [eapply sc_app; eauto] | solve [eapply sc_natrec; eauto]
    | solve [eapply sc_sig; eauto] | solve [eapply sc_code_sig; eauto]
    | solve [eapply sc_unit; eauto] | solve [eapply sc_code_unit; eauto] | solve [eapply sc_triv; eauto]
    | solve [eapply sc_pair; eauto] | solve [eapply sc_fst; eauto] | solve [eapply sc_snd; eauto]
    (* the identity type (every layer but V since M11b) *)
    | solve [eapply sc_id; eauto] | solve [eapply sc_idrefl; eauto] | solve [eapply sc_J; eauto]
    | solve [eapply sc_code_id; eauto]
    (* strict equality (every layer but V since M10c) *)
    | solve [eapply sc_seq; eauto] | solve [eapply sc_sempty; eauto] | solve [eapply sc_srefl; eauto]
    | solve [eapply sc_elimSEmpty; eauto]
    | solve [eapply sc_code_seq; eauto] | solve [eapply sc_code_sempty; eauto]
    (* the empty type and binary sums (M12a, M12b), with their codes (M12c) *)
    | solve [eapply sc_empty; eauto] | solve [eapply sc_elimEmpty; eauto]
    | solve [eapply sc_sum; eauto] | solve [eapply sc_inl; eauto] | solve [eapply sc_inr; eauto]
    | solve [eapply sc_case; eauto]
    | solve [eapply sc_code_empty; eauto] | solve [eapply sc_code_sum; eauto]
    (* well-founded trees (M13a) *)
    | solve [eapply sc_W; eauto] | solve [eapply sc_sup; eauto] | solve [eapply sc_elimW; eauto]
    | solve [eapply sc_code_W; eauto]
    (* length-indexed tuples and finite indices (M14a) *)
    | solve [eapply sc_vec; eauto] | solve [eapply sc_fin; eauto]
    (* their codes (M14b) *)
    | solve [eapply sc_code_vec; eauto] | solve [eapply sc_code_fin; eauto]
    (* finitary well-founded trees (M15a) *)
    | solve [eapply sc_wf; eauto] | solve [eapply sc_supf; eauto] | solve [eapply sc_elimWf; eauto]
    | solve [eapply sc_code_wf; eauto]
    (* propositional truncation (M16a) *)
    | solve [eapply sc_tySq; eauto] | solve [eapply sc_sq; eauto] | solve [eapply sc_elimSq; eauto]
    | match goal with
      | IH : forall x, tm_leq ?t x -> tm_lwf _ x -> _ /\ _, E : tm_leq ?t ?x, W : tm_lwf _ ?x
        |- _ /\ eq_tm _ _ _ (succ _) _ _ _ =>
          destruct (IH x E W); split; [apply wf_succ | apply eqtm_succ]; assumption
      end ].
Qed.

(** Named forms. *)
Lemma static_code_ty {G i Γ T T' l} : lle i lD -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T' @ l ] ->
  ty_leq T T' -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ].
Proof.
  intros Hi HT HT' E. exact (proj2 (proj1 (proj2 (proj2 static_code)) _ _ _ _ _ HT Hi _ E (wf_ty_lwf HT'))).
Qed.
Lemma static_code_tm {G i Γ t t' T l} : lle i lD -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t' : T @ l ] ->
  tm_leq t t' -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ].
Proof.
  intros Hi Ht Ht' E.
  exact (proj2 (proj1 (proj2 (proj2 (proj2 static_code))) _ _ _ _ _ _ Ht Hi _ E (wf_tm_lwf Ht'))).
Qed.

(** At a computing layer, typed [≡ₗ]-related syntax is equal: by the
    lemma at P, by the rule at M (M3_DESIGN.md E12). *)
Lemma leq_eqty {G i Γ T T' l} : compt i -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T' @ l ] ->
  ty_leq T T' -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ].
Proof.
  intros [-> | ->] HT HT' E; [exact (static_code_ty (lle_refl lD) HT HT' E) | exact (eqty_leq _ _ _ _ _ HT HT' E)].
Qed.
Lemma leq_eqtm {G i Γ t t' T l} : compt i -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t' : T @ l ] ->
  tm_leq t t' -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ].
Proof.
  intros [-> | ->] Ht Ht' E;
    [exact (static_code_tm (lle_refl lD) Ht Ht' E) | exact (eqtm_leq _ _ _ _ _ _ Ht Ht' E)].
Qed.

Lemma leq_eqctx_D {G} : forall Γ Γ', [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ' ⊢[ lD ] ] -> ctx_leq Γ Γ' ->
  [ G ⊢[ lD ] Γ ≅ Γ' ].
Proof.
  induction Γ as [| g | Γ IH A l]; intros [| g' | Γ' A' l'] H H' Ex; cbn in Ex; try contradiction.
  - now apply eqc_refl.
  - subst g'; now apply eqc_refl.
  - destruct Ex as (EΓ & EA & El).
    inversion H as [| | ? ? ? ? ? HΓ HA Hl]; subst.
    inversion H' as [| | ? ? ? ? ? HΓ' HA' Hl']; subst.
    pose proof (IH _ HΓ HΓ' EΓ) as Hc.
    pose proof (leqv_lequiv _ _ _ Hl Hl' El) as Q.
    apply eqc_ext; [exact Hc | exact HA | | exact Q].
    apply (leq_eqty compt_D HA); [| exact EA].
    eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D Hc) (i := lD) eq_refl HA') | exact Q].
Qed.
