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

Section SC.
Context {G : gctx} {i : layer} (Hi : lle i lD).
Let Hty : typeof i = lD := lle_D_typeof i Hi.

Lemma sc_ctx {Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ lD ] ].
Proof. intros H; rewrite <- Hty; exact (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H). Qed.
Lemma sc_ctx_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] ].
Proof. intros H; rewrite <- Hty; exact (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H). Qed.
Lemma sc_ty {Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ lD ] T @ l ].
Proof. intros H; exact (lift_ty H Hi). Qed.
Lemma sc_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] t : T @ l ].
Proof. intros H; exact (lift_tm H Hi). Qed.
Lemma sc_eqty {Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ].
Proof. intros H; exact (lift_eqty H Hi). Qed.
Lemma sc_eqtm {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ].
Proof. intros H; exact (lift_eqtm H Hi). Qed.

(** Conversion at [i] along an equation at P. *)
Lemma sc_conv {Γ t T T' l} : [ G ; Γ ⊢[ i ] t : T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] t : T @ l ].
Proof. intros H HT; apply (wf_conv _ _ _ _ _ _ _ H); now rewrite Hty. Qed.
Lemma sc_eqconv {Γ t t' T T' l} : [ G ; Γ ⊢[ i ] t ≅ t' : T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ].
Proof. intros H HT; apply (eqtm_conv _ _ _ _ _ _ _ _ H); now rewrite Hty. Qed.

(** The context extended by related types. *)
Lemma sc_ext {Γ A A' l l'} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> lequiv (gL G) l l' ->
  [ G ⊢[ lD ] Γ ,, A @ l ≅ Γ ,, A' @ l' ].
Proof.
  intros HA HAA Hl. apply eqc_ext; [apply eqc_refl, (sc_ctx HA) | exact (sc_ty HA) | exact (sc_eqty HAA) | exact Hl].
Qed.
Lemma sc_cty {Γ Γ' T l} : [ G ⊢[ lD ] Γ ≅ Γ' ] -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ' ⊢[ i ] T @ l ].
Proof. intros Hc H; exact (ctxconv_ty Hc Hty H). Qed.
Lemma sc_ctm {Γ Γ' t T l} : [ G ⊢[ lD ] Γ ≅ Γ' ] -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ' ⊢[ i ] t : T @ l ].
Proof. intros Hc H; exact (ctxconv_tm Hc Hty H). Qed.

(** ** The global variables' entries, from the last to the first *)

Lemma telescope Γ Δ : forall d d',
  [ G ; Δ ⊢[ lD ] ] -> lsub_tail d Δ Γ -> lsub_tail d' Δ Γ -> [ G ; Γ ⊢[ lD ] ] -> LK dnftm d -> LK dnftm d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d] @ k ] /\
                                    [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ].
Proof.
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
Proof.
  intros [Ht Hl] E; split; [exact Ht|]. intros n. pose proof (llk_leq _ _ (clen Δ + n) E) as X.
  rewrite Hl in X. destruct (llk d' (clen Δ + n)); cbn in X; try contradiction. now subst.
Qed.
Lemma sc_dnfl {d d'} : dnfl d -> lsub_leq d d' -> dnfl d'.
Proof. intros H E; exact (proj2 (proj2 (proj2 leq_dnf_all)) _ _ E H). Qed.

Lemma sc_U {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tyU l' @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tyU l ≅ tyU l' @ lsuc l ].
Proof.
  intros Hv HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_U; auto | apply lequiv_lsuc', Q].
  - apply eqty_U; auto.
Qed.

Lemma sc_El {Γ l l' t t'} : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] t ≅ t' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] tyEl l' t' @ l ] /\ [ G ; Γ ⊢[ i ] tyEl l t ≅ tyEl l' t' @ l ].
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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

Lemma lD_notV_sc : lD <> lV. Proof. discriminate. Qed.

(** The unit type (M8c): at every layer below D but V (code since M8d). *)
Lemma sc_unit {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tyUnit l' @ l ] /\ [ G ; Γ ⊢[ i ] tyUnit l ≅ tyUnit l' @ l ].
Proof.
  intros Hc HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_unit; auto | exact Q].
  - apply eqty_unit; auto.
Qed.

Lemma sc_code_unit {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tmUnit l' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmUnit l ≅ tmUnit l' : tyU l @ lsuc l ].
Proof.
  intros Hc HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - apply (sc_conv (T' := tyU l')).
    + eapply wf_lconv; [apply wf_code_unit; auto | apply lequiv_lsuc', Q].
    + rewrite Hty in HΓ. apply eqty_U; [discriminate | exact HΓ | exact Q].
  - apply eqtm_code_unit; auto.
Qed.

Lemma sc_triv {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tmTriv l' : tyUnit l @ l ] /\ [ G ; Γ ⊢[ i ] tmTriv l ≅ tmTriv l' : tyUnit l @ l ].
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
  intros Hv Hl Hl' E HA [HA' HAA] [Ha' Haa] [Hb' Hbb]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_id_q Hv Q HA' HAA Ha' Hb') | apply eqty_id; auto].
Qed.

Lemma sc_idrefl_q {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tmRefl l' A' a' : tyId l A a a @ l ].
Proof.
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
Proof.
  intros Hv Hl Hl' E HA [HA' HAA] Ha [Ha' Haa]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_idrefl_q Hv Q HA HA' HAA Ha' Haa) | apply eqtm_idrefl; auto].
Qed.

Lemma sc_code_id_q {Γ l l' s s' t' u'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmId l' s' t' u' : tyU l @ lsuc l ].
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
  intros Hv Hl Hl' E HA [HA' HAA] [Ha' Haa] [Hb' Hbb]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_seq_q Hv Q HA' HAA Ha' Hb') | apply eqty_seq; auto].
Qed.

Lemma sc_sempty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tySEmpty l' @ l ] /\ [ G ; Γ ⊢[ i ] tySEmpty l ≅ tySEmpty l' @ l ].
Proof.
  intros Hv HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - eapply wft_lconv; [apply wft_sempty; auto | exact Q].
  - apply eqty_sempty; auto.
Qed.

Lemma sc_srefl_q {Γ l l' A A' a a'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A' @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] srefl l' A' a' : tySEq l A a a @ l ].
Proof.
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
Proof.
  intros Hv Hl Hl' E HA [HA' HAA] [Ha' Haa]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_srefl_q Hv Q HA HA' HAA Ha' Haa) | apply eqtm_srefl; auto].
Qed.

Lemma sc_elimSEmpty_q {Γ l1 l2 l1' l2' M M' e'} : i <> lV -> lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ G ; Γ ⊢[ i ] M' @ l2 ] -> [ G ; Γ ⊢[ i ] M ≅ M' @ l2 ] -> [ G ; Γ ⊢[ i ] e' : tySEmpty l1 @ l1 ] ->
  [ G ; Γ ⊢[ i ] elimSEmpty l1' l2' M' e' : M @ l2 ].
Proof.
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
Proof.
  intros Hv H1 H2 H1' H2' E1 E2 HM [HM' HMM] [He' Hee].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2.
  split; [exact (sc_elimSEmpty_q Hv Q1 Q2 HM' HMM He') | apply eqtm_elimSEmpty; auto].
Qed.

(** Strict equality's codes (M10c). *)
Lemma sc_code_seq_q {Γ l l' s s' t' u'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
  [ G ; Γ ⊢[ i ] t' : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u' : tyEl l s @ l ] ->
  [ G ; Γ ⊢[ i ] tmSEq l' s' t' u' : tyU l @ lsuc l ].
Proof.
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
Proof.
  intros Hv Hl Hl' E Hs [Hs' Hss] [Ht' Htt] [Hu' Huu]. pose proof (lq Hl Hl' E) as Q.
  split; [exact (sc_code_seq_q Hv Q Hs' Hss Ht' Hu') | apply eqtm_code_seq; auto].
Qed.

Lemma sc_code_sempty {Γ l l'} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ i ] tmSEmpty l' : tyU l @ lsuc l ] /\ [ G ; Γ ⊢[ i ] tmSEmpty l ≅ tmSEmpty l' : tyU l @ lsuc l ].
Proof.
  intros Hc HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - apply (sc_conv (T' := tyU l')).
    + eapply wf_lconv; [apply wf_code_sempty; auto | apply lequiv_lsuc', Q].
    + rewrite Hty in HΓ. apply eqty_U; [discriminate | exact HΓ | exact Q].
  - apply eqtm_code_sempty; auto.
Qed.

End SC.

(** The empty type (M12a): gated to the computing layers, so below M only
    at D, where the presupposition lemmas give the right-hand sides. *)
Section SCD.
Context {G : gctx}.
Let HD : typeof lD = lD := eq_refl.
Let HDv : lD <> lV := ltac:(discriminate).

Lemma sc_empty {Γ l l'} : [ G ; Γ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' -> leqv l l' ->
  [ G ; Γ ⊢[ lD ] tyEmpty l' @ l ] /\ [ G ; Γ ⊢[ lD ] tyEmpty l ≅ tyEmpty l' @ l ].
Proof.
  intros HΓ Hl Hl' E. pose proof (lq Hl Hl' E) as Q. split.
  - exact (pre_empty_r HD HDv HΓ Q).
  - apply eqty_empty; auto using compt_D.
Qed.

Lemma sc_elimEmpty {Γ l1 l2 l1' l2' M M' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lwf (gL G) l1' -> lwf (gL G) l2' -> leqv l1 l1' -> leqv l2 l2' ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ lD ] M @ l1 ] ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ lD ] M' @ l1 ] /\ [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ lD ] M ≅ M' @ l1 ] ->
  [ G ; Γ ⊢[ lD ] t : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ lD ] t' : tyEmpty l2 @ l2 ] /\ [ G ; Γ ⊢[ lD ] t ≅ t' : tyEmpty l2 @ l2 ] ->
  [ G ; Γ ⊢[ lD ] elimEmpty l1' l2' M' t' : M[lsingle t] @ l1 ] /\
  [ G ; Γ ⊢[ lD ] elimEmpty l1 l2 M t ≅ elimEmpty l1' l2' M' t' : M[lsingle t] @ l1 ].
Proof.
  intros H1 H2 H1' H2' E1 E2 HM [HM' HMM] Ht [Ht' Htt].
  pose proof (lq H1 H1' E1) as Q1. pose proof (lq H2 H2' E2) as Q2. split.
  - exact (pre_elimEmpty_r HD HDv Q1 Q2 HM HMM HM' Htt Ht Ht').
  - apply eqtm_elimEmpty; auto using compt_D.
Qed.
End SCD.


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
    (* the empty type (M12a): at D only *)
    | match goal with
      | c : compt ?j, H : lle ?j lD |- _ =>
          destruct c; subst j; [| exfalso; exact (lle_D_notM' H eq_refl)]; cbn [typeof] in *;
          solve [ eapply sc_empty; eauto | eapply sc_elimEmpty; eauto ]
      end
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
