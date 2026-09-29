(** * Consequences of the substitution lemma: single substitutions,
    context conversion (stability) and functionality (ch. 5) *)
From DeLaM.Typing Require Export Substitution.

(** Layer-agnostic forms of the substitution lemma. *)
Lemma wf_ty_subst_g {G i Γ T l Δ d} :
  [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] T[d] @ l ].
Proof. intros; eapply substitution_all; eauto. Qed.
Lemma wf_tm_subst_g {G i Γ t T l Δ d} :
  [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] t[d] : T[d] @ l ].
Proof. intros; eapply substitution_all; eauto. Qed.
Lemma eqty_subst_g {G i Γ T T' l Δ d} :
  [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T'[d] @ l ].
Proof. intros; eapply substitution_all; eauto. Qed.
Lemma eqtm_subst_g {G i Γ t t' T l Δ d} :
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Δ ⊢[ i ] d : Γ ] ->
  [ G ; Δ ⊢[ i ] t[d] ≅ t'[d] : T[d] @ l ].
Proof. intros; eapply substitution_all; eauto. Qed.

(** ** The recursors' scopes under a typed substitution, as lemmas *)

Section RecScopes.
Context {G : gctx} {Γ Δ : ctx} {d : lsub} (Hd : [ G ; Δ ⊢[ lM ] d : Γ ]).

Lemma brctx_subst k MT Mt l1 l2 : k < nbr ->
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ] ->
  [ brG k G ; brΓ k Δ (wrapMT MT)[d] (wrapMt Mt)[d] l1 l2 ⊢[ lM ] ].
Proof.
  intros Hk H. pose proof (proj1 (proj2 substitution_all) _ _ _ H _ _ eq_refl _ _ (lsub_wf_bsub k _ _ _ _ Hk Hd))
    as X.
  rewrite brLocs_subst in X by (first [exact Hk | exact (lsub_wf_dnf Hd)]). exact X.
Qed.

Lemma brsub_wf k MT Mt l1 l2 : k < nbr ->
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ] ->
  [ brG k G ; brΓ k Δ (wrapMT MT)[d] (wrapMt Mt)[d] l1 l2 ⊢[ lM ]
      lliftn (br_nl k) (bsub k d) : brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ].
Proof.
  intros Hk H. pose proof (brctx_subst k MT Mt l1 l2 Hk H) as C. unfold brΓ in C |- *.
  rewrite <- (brLocs_len k (wrapMT MT) (wrapMt Mt) (lvren l1 (ush (br_nu k))) (lvren l2 (ush (br_nu k))) Hk).
  rewrite <- brLocs_subst in C |- * by (first [exact Hk | exact (lsub_wf_dnf Hd)]).
  apply lsub_wf_cexts; [apply lsub_wf_bsub; assumption | exact C].
Qed.

Lemma branch_subst k MT Mt l1 l2 b : k < nbr ->
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ] ->
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] b : brRes k (wrapMT MT) (wrapMt Mt)
      @ brLv k l1 l2 ] ->
  [ brG k G ; brΓ k Δ (wrapMT MT)[d] (wrapMt Mt)[d] l1 l2 ⊢[ lM ] b[lliftn (br_nl k) (bsub k d)]
      : brRes k (wrapMT MT)[d] (wrapMt Mt)[d] @ brLv k l1 l2 ].
Proof.
  intros Hk HC Hb. pose proof (wf_tm_subst_g Hb (brsub_wf k MT Mt l1 l2 Hk HC)) as X.
  rewrite brRes_subst in X by (first [exact Hk | exact (lsub_wf_dnf Hd)]). exact X.
Qed.

Lemma motT_subst_wf MT l : [ recGT G ; recΓT Γ ⊢[ lM ] MT @ l ] ->
  [ recGT G ; recΓT Δ ⊢[ lM ] MT[llift (gwk (uwk d))] @ l ].
Proof. intros H; exact (wf_ty_subst_g H (lsub_wf_recΓT _ _ _ _ Hd)). Qed.
Lemma mott_subst_wf Mt l : [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ l ] ->
  [ recGt G ; recΓt Δ ⊢[ lM ] Mt[llift (gwk (gwk (uwk d)))] @ l ].
Proof. intros H; exact (wf_ty_subst_g H (lsub_wf_recΓt _ _ _ _ Hd)). Qed.

End RecScopes.

Section Corollaries.
Context {G : gctx} {i : layer} (Hi : typeof i = i).

Lemma wf_ty_subst {Γ T l Δ d} :
  [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] T[d] @ l ].
Proof. intros; eapply substitution; eauto. Qed.
Lemma wf_tm_subst {Γ t T l Δ d} :
  [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] t[d] : T[d] @ l ].
Proof. intros; eapply substitution; eauto. Qed.
Lemma eqty_subst {Γ T T' l Δ d} :
  [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T'[d] @ l ].
Proof. intros; eapply substitution; eauto. Qed.
Lemma eqtm_subst {Γ t t' T l Δ d} :
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Δ ⊢[ i ] d : Γ ] ->
  [ G ; Δ ⊢[ i ] t[d] ≅ t'[d] : T[d] @ l ].
Proof. intros; eapply substitution; eauto. Qed.

(** Context well-formedness at [i]. *)
Lemma ctx_of_wf_ty {Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] ].
Proof. intros H; rewrite <- Hi; now apply ctx_extract in H. Qed.
Lemma ctx_of_wf_tm {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] ].
Proof. intros H; rewrite <- Hi; now apply ctx_extract in H. Qed.
Lemma ctx_of_eqty {Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] ].
Proof. intros H; rewrite <- Hi; now apply ctx_extract in H. Qed.
Lemma ctx_of_eqtm {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] ].
Proof. intros H; rewrite <- Hi; now apply ctx_extract in H. Qed.

(** ** Single substitutions *)

Lemma wf_ty_single {Γ A B a l l'} :
  [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] B[lsingle a] @ l' ].
Proof. intros HB Ha; eapply wf_ty_subst; eauto using lsub_wf_single, ctx_of_wf_tm. Qed.
Lemma wf_tm_single {Γ A B a b l l'} :
  [ G ; Γ ,, A @ l ⊢[ i ] b : B @ l' ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] b[lsingle a] : B[lsingle a] @ l' ].
Proof. intros HB Ha; eapply wf_tm_subst; eauto using lsub_wf_single, ctx_of_wf_tm. Qed.
Lemma eqty_single {Γ A B B' a l l'} :
  [ G ; Γ ,, A @ l ⊢[ i ] B ≅ B' @ l' ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] B[lsingle a] ≅ B'[lsingle a] @ l' ].
Proof. intros HB Ha; eapply eqty_subst; eauto using lsub_wf_single, ctx_of_wf_tm. Qed.

(** ** Context conversion of the last entry *)

Lemma nf_id_ty (T : ty) : nfty T -> T[lshift 0] = T.
Proof. intros; apply subst_id_ty; auto; intros; cbn; f_equal; lia. Qed.
Lemma nf_id (t : tm) : nftm t -> t[lshift 0] = t.
Proof. intros; apply subst_id; auto; intros; cbn; f_equal; lia. Qed.

(** The entry may also change its level annotation to an equivalent one. *)
Lemma lsub_wf_conv {Γ A A' l l'} :
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> lequiv (gL G) l l' -> [ G ; Γ ,, A' @ l' ⊢[ i ] ] ->
  [ G ; Γ ,, A' @ l' ⊢[ i ] lshift 0 : Γ ,, A @ l ].
Proof.
  intros HA Hl HΓ'. constructor; [rewrite Hi; exact HΓ' | apply lk_dnf_lshift | split; auto; intros; cbn; f_equal; lia |].
  intros n T l0 Hin. rewrite nf_id_ty by eauto using in_ctx_nf. cbn; rewrite Nat.add_0_r.
  inversion Hin as [Γ0 A0 l1|Γ0 A0 l1 T0 l2 m Hm]; subst.
  - eapply wf_conv; [eapply wf_lconv; [apply var0_wf; auto | exact Hl]|].
    rewrite Hi. apply wk1_eqty; auto.
  - apply wf_var; [now rewrite Hi | now constructor].
Qed.

Section Stab.
Context {Γ A A' l l'} (HA : [ G ; Γ ⊢[ i ] A ≅ A' @ l ]) (Hl : lequiv (gL G) l l')
  (HΓ : [ G ; Γ ,, A' @ l' ⊢[ i ] ]).

Lemma stab_ty {T k} : [ G ; Γ ,, A @ l ⊢[ i ] T @ k ] -> [ G ; Γ ,, A' @ l' ⊢[ i ] T @ k ].
Proof.
  intros H. rewrite <- (nf_id_ty T) by exact (wf_ty_nf H).
  eapply wf_ty_subst; eauto using lsub_wf_conv.
Qed.
Lemma stab_tm {t T k} :
  [ G ; Γ ,, A @ l ⊢[ i ] t : T @ k ] -> [ G ; Γ ,, A' @ l' ⊢[ i ] t : T @ k ].
Proof.
  intros H. rewrite <- (nf_id_ty T) by exact (wf_tm_nf_ty H).
  rewrite <- (nf_id t) by exact (wf_tm_nf H).
  eapply wf_tm_subst; eauto using lsub_wf_conv.
Qed.
Lemma stab_eqty {T T' k} :
  [ G ; Γ ,, A @ l ⊢[ i ] T ≅ T' @ k ] -> [ G ; Γ ,, A' @ l' ⊢[ i ] T ≅ T' @ k ].
Proof.
  intros H. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ H) as [N1 N2].
  rewrite <- (nf_id_ty T), <- (nf_id_ty T') by assumption.
  eapply eqty_subst; eauto using lsub_wf_conv.
Qed.
Lemma stab_eqtm {t t' T k} :
  [ G ; Γ ,, A @ l ⊢[ i ] t ≅ t' : T @ k ] -> [ G ; Γ ,, A' @ l' ⊢[ i ] t ≅ t' : T @ k ].
Proof.
  intros H. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ _ H)
    as (N1 & N2 & N3).
  rewrite <- (nf_id_ty T), <- (nf_id t), <- (nf_id t') by assumption.
  eapply eqtm_subst; eauto using lsub_wf_conv.
Qed.
End Stab.

End Corollaries.

(** ** Functionality: equal substitutions give equal results *)

Definition lsub_eq G i Δ d d' Γ : Prop :=
  [ G ; Δ ⊢[ i ] d : Γ ] /\ [ G ; Δ ⊢[ i ] d' : Γ ] /\
  (forall n T l, in_ctx Γ n T l -> [ G ; Δ ⊢[ i ] llk d n ≅ llk d' n : T[d] @ l ]).

Notation "[ G ; Δ ⊢[ i ] d ≅ d' : Γ ]" := (lsub_eq G i Δ d d' Γ)
  (at level 0, G, Δ, i, d, d', Γ at level 50).

Lemma lsub_eq_l {G i Δ d d' Γ} : [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] d : Γ ].
Proof. now intros []. Qed.
Lemma lsub_eq_r {G i Δ d d' Γ} : [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] d' : Γ ].
Proof. now intros (? & ? & ?). Qed.
Lemma lsub_eq_var {G i Δ d d' Γ n T l} : [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> in_ctx Γ n T l ->
  [ G ; Δ ⊢[ i ] llk d n ≅ llk d' n : T[d] @ l ].
Proof. intros (? & ? & H); apply H. Qed.

Section LsubEq.
Context {G : gctx} {i : layer} (Hi : typeof i = i).

Lemma lsub_eq_lift Δ d d' Γ A A' l :
  [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] A' @ l ] -> lwf (gL G) l ->
  [ G ; Δ ⊢[ i ] A[d] ≅ A[d'] @ l ] -> A' = A[d] ->
  [ G ; Δ ,, A' @ l ⊢[ i ] llift d ≅ llift d' : Γ ,, A @ l ].
Proof.
  intros Hd HA Hl HAA ->.
  assert (HΔ : [ G ; Δ ,, A[d] @ l ⊢[ i ] ])
    by (apply wfc_ext; [rewrite <- Hi; exact (lsub_wf_ctx (lsub_eq_l Hd)) | exact HA | exact Hl]).
  split; [exact (lsub_wf_lift G i Hi _ _ _ _ _ (lsub_eq_l Hd) HA Hl) | split].
  - constructor; [rewrite Hi; exact HΔ | apply lk_dnf_llift, (lsub_wf_dnf (lsub_eq_r Hd))
                 | apply tail_llift, (lsub_wf_tail (lsub_eq_r Hd)) |].
    intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst;
      rewrite llk_llift, shift_llift_ty.
    + eapply wf_conv; [apply var0_wf; auto|]. rewrite Hi. apply wk1_eqty; auto using eqty_sym.
    + apply wk1_tm; auto. exact (lsub_wf_var (lsub_eq_r Hd) Hm).
  - intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst;
      rewrite !llk_llift, shift_llift_ty.
    + apply eqtm_refl, var0_wf; auto.
    + apply wk1_eqtm; auto. exact (lsub_eq_var Hd Hm).
Qed.

End LsubEq.

Lemma eqc_refl G i Γ : [ G ; Γ ⊢[ i ] ] -> [ G ⊢[ i ] Γ ≅ Γ ].
Proof.
  induction 1; [now apply eqc_nil | now apply eqc_var |].
  apply eqc_ext; auto using eqty_refl, lequiv_refl.
Qed.

Lemma lsub_eq_gwk G D i Δ d d' Γ : [ ⊢ gext G D ] -> [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] ->
  [ gext G D ; Δ⟪S⟫ ⊢[ i ] gwk d ≅ gwk d' : Γ⟪S⟫ ].
Proof.
  intros Hg (Hd & Hd' & He).
  assert (Hw : gwk_wf (gwk_step gwk_id) (D :: gΨ G) (gΨ G)) by (constructor; constructor).
  refine (conj (lsub_wf_gwk _ _ _ _ _ _ Hg Hd) (conj (lsub_wf_gwk _ _ _ _ _ _ Hg Hd') _)).
  intros n A k Hin. destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & HA0 & ->).
  unfold gwk; rewrite !llk_glren. change (gren_tm ?x ?y) with x⟪y⟫.
  change (glren d S) with d⟪S⟫. rewrite <- gren_subst_ty.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ _ _ _ (He _ _ _ HA0) _ _ _ (le_n _) Hw Hg).
Qed.

Lemma lsub_eq_lift_CTyp G Δ0 d d' Γ Δ l :
  [ G ; Δ0 ⊢[ lM ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l ->
  [ G ; Δ0 ,, tyCTyp Δ l @ lzero ⊢[ lM ] llift d ≅ llift d' : Γ ,, tyCTyp Δ l @ lzero ].
Proof.
  intros Hd HΔ Hl. assert (H0 : [ G ; Δ0 ⊢[ lM ] tyCTyp Δ l @ lzero ])
    by (apply wft_CTyp; auto; exact (lsub_wf_ctx (lsub_eq_l Hd))).
  eapply (lsub_eq_lift (i := lM) eq_refl); [exact Hd | exact H0 | exact I | apply eqty_refl, H0 | reflexivity].
Qed.
Lemma lsub_eq_lift_CTrm G Δ0 d d' Γ Δ T l :
  [ G ; Δ0 ⊢[ lM ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] -> lwf (gL G) l ->
  [ G ; Δ0 ,, tyCTrm Δ T l @ lzero ⊢[ lM ] llift d ≅ llift d' : Γ ,, tyCTrm Δ T l @ lzero ].
Proof.
  intros Hd HΔ HT Hl. assert (H0 : [ G ; Δ0 ⊢[ lM ] tyCTrm Δ T l @ lzero ])
    by (apply wft_CTrm; auto; exact (lsub_wf_ctx (lsub_eq_l Hd))).
  eapply (lsub_eq_lift (i := lM) eq_refl); [exact Hd | exact H0 | exact I | apply eqty_refl, H0 | reflexivity].
Qed.

#[export] Hint Resolve lsub_eq_l lsub_eq_r : sub.
#[export] Hint Extern 3 (wf_tm _ _ _ (subst _ _) _ _) => eapply wf_tm_subst : sub.
#[export] Hint Extern 4 (eq_ty _ _ _ (subst _ _) (subst _ _) _) => eapply eqty_subst : sub.
#[export] Hint Resolve wft_U wf_code_nat wf_code_U wf_zero lequiv_refl : sub.
#[export] Hint Extern 2 (lsub_eq _ _ _ (llift _) (llift _) _) =>
  eapply lsub_eq_lift; [ .. | sub_rw; reflexivity ] : sub.
#[export] Hint Extern 3 (wf_ty _ _ _ (subst _ _) _) => eapply wf_ty_subst : sub.
#[export] Hint Extern 3 (eq_ty _ _ _ (subst ?T _) (subst ?T _) _) =>
  eapply eqty_subst; [ | eapply eqty_refl | ] : sub.



(** ** Functionality at every layer

    The same statement without [typeof i = i]: premises at [typeof i] use
    the lifted equivalence of substitutions, and context extensions lift
    the bound type to [typeof i] (as for the substitution lemma). *)

Lemma lsub_eq_lle G i j Δ d d' Γ : lle i j -> [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ j ] d ≅ d' : Γ ].
Proof.
  intros Hij (Hd & Hd' & He). refine (conj (lsub_wf_lle _ _ _ _ _ _ Hij Hd)
    (conj (lsub_wf_lle _ _ _ _ _ _ Hij Hd') _)).
  intros; eapply lift_eqtm; eauto.
Qed.
Lemma lsub_eq_typeof G i Δ d d' Γ : [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ typeof i ] d ≅ d' : Γ ].
Proof. apply lsub_eq_lle, lle_self_typeof. Qed.

Lemma lsub_eq_lift_g G i Δ d d' Γ A A' l :
  [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ typeof i ] A' @ l ] -> lwf (gL G) l ->
  [ G ; Δ ⊢[ typeof i ] A[d] ≅ A[d'] @ l ] -> A' = A[d] ->
  [ G ; Δ ,, A' @ l ⊢[ i ] llift d ≅ llift d' : Γ ,, A @ l ].
Proof.
  intros Hd HA Hl HAA ->.
  assert (HΔ : [ G ; Δ ,, A[d] @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact (lsub_wf_ctx (lsub_eq_l Hd)) | exact HA | exact Hl]).
  split; [exact (lsub_wf_lift_g G i _ _ _ _ _ (lsub_eq_l Hd) HA Hl) | split].
  - constructor; [exact HΔ | apply lk_dnf_llift, (lsub_wf_dnf (lsub_eq_r Hd))
                 | apply tail_llift, (lsub_wf_tail (lsub_eq_r Hd)) |].
    intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst;
      rewrite llk_llift, shift_llift_ty.
    + eapply wf_conv; [apply var0_wf_g; auto|].
      apply (wk1_eqty_g G (typeof i)); [rewrite typeof_idem; exact HΔ | now apply eqty_sym].
    + apply wk1_tm_g; auto. exact (lsub_wf_var (lsub_eq_r Hd) Hm).
  - intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst;
      rewrite !llk_llift, shift_llift_ty.
    + apply eqtm_refl, var0_wf_g; auto.
    + apply wk1_eqtm_g; auto. exact (lsub_eq_var Hd Hm).
Qed.

Lemma lsub_eq_lift_CTyp_g G i Δ0 d d' Γ Δ l :
  i = lM -> [ G ; Δ0 ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l ->
  [ G ; Δ0 ,, tyCTyp Δ l @ lzero ⊢[ i ] llift d ≅ llift d' : Γ ,, tyCTyp Δ l @ lzero ].
Proof. intros ->; apply lsub_eq_lift_CTyp. Qed.
Lemma lsub_eq_lift_CTrm_g G i Δ0 d d' Γ Δ T l :
  i = lM -> [ G ; Δ0 ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] -> lwf (gL G) l ->
  [ G ; Δ0 ,, tyCTrm Δ T l @ lzero ⊢[ i ] llift d ≅ llift d' : Γ ,, tyCTrm Δ T l @ lzero ].
Proof. intros ->; apply lsub_eq_lift_CTrm. Qed.

Lemma lsub_wf_lift_CTyp G Δ0 d Γ Δ l :
  [ G ; Δ0 ⊢[ lM ] d : Γ ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l ->
  [ G ; Δ0 ,, tyCTyp Δ l @ lzero ⊢[ lM ] llift d : Γ ,, tyCTyp Δ l @ lzero ].
Proof.
  intros Hd HΔ Hl. eapply lsub_wf_lift_g'; [exact Hd | | exact I | reflexivity].
  apply wft_CTyp; auto. exact (lsub_wf_ctx Hd).
Qed.
Lemma lsub_wf_lift_CTrm G Δ0 d Γ Δ T l :
  [ G ; Δ0 ⊢[ lM ] d : Γ ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] -> lwf (gL G) l ->
  [ G ; Δ0 ,, tyCTrm Δ T l @ lzero ⊢[ lM ] llift d : Γ ,, tyCTrm Δ T l @ lzero ].
Proof.
  intros Hd HΔ HT Hl. eapply lsub_wf_lift_g'; [exact Hd | | exact I | reflexivity].
  apply wft_CTrm; auto. exact (lsub_wf_ctx Hd).
Qed.

(** ** Equal substitutions in the recursors' scopes *)

Lemma lsub_eq_uwkn nu G i Δ d d' Γ : [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] ->
  [ gctx_uwk nu G ; ucren Δ (ush nu) ⊢[ i ] uwkn nu d ≅ uwkn nu d' : ucren Γ (ush nu) ].
Proof.
  intros (Hd & Hd' & He). refine (conj (lsub_wf_uwkn _ _ _ _ _ _ Hd) (conj (lsub_wf_uwkn _ _ _ _ _ _ Hd') _)).
  intros m T l Hin. destruct (in_ctx_uren_inv _ _ _ _ _ Hin) as (T0 & l0 & HT0 & -> & ->).
  rewrite !llk_uwkn by eauto using lsub_wf_dnf.
  replace ((uren_ty T0 (ush nu))[uwkn nu d]) with (uren_ty (T0[d]) (ush nu)).
  - apply uwk_eqtm, He, HT0.
  - apply (proj1 uren_subst_all). intros; now rewrite llk_uwkn by eauto using lsub_wf_dnf.
Qed.

Lemma lsub_eq_gwkn L Ψ Ds i Δ d d' Γ : [ ⊢ mkG L (Ds ++ Ψ) ] -> [ mkG L Ψ ; Δ ⊢[ i ] d ≅ d' : Γ ] ->
  [ mkG L (Ds ++ Ψ) ; gcren Δ (ush (length Ds)) ⊢[ i ] gwkn (length Ds) d ≅ gwkn (length Ds) d'
    : gcren Γ (ush (length Ds)) ].
Proof.
  intros HG (Hd & Hd' & He).
  refine (conj (lsub_wf_gwkn _ _ _ _ _ _ _ HG Hd) (conj (lsub_wf_gwkn _ _ _ _ _ _ _ HG Hd') _)).
  pose proof (gwk_stepn_wf Ds Ψ) as Hw.
  assert (Hξ : forall j, gwk_fn (gwk_stepn (length Ds)) j = ush (length Ds) j) by apply gwk_stepn_fn.
  intros m A k Hin. change (gcren ?x ?y) with x⟪y⟫ in Hin.
  destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & HA0 & ->).
  rewrite !llk_gwkn by eauto using lsub_wf_dnf.
  replace (A0⟪ush (length Ds)⟫[gwkn (length Ds) d]) with ((A0[d])⟪ush (length Ds)⟫).
  - pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ _ _ _ (He _ _ _ HA0)
                  _ _ _ (le_n _) Hw HG) as X.
    rewrite (proj1 (proj2 (proj2 gren_ext_all)) _ _ _ Hξ), !(proj1 (proj2 gren_ext_all) _ _ _ Hξ),
      (proj1 gren_ext_all _ _ _ Hξ) in X.
    exact X.
  - apply (proj1 gren_subst_all). intros; now rewrite llk_gwkn by eauto using lsub_wf_dnf.
Qed.

Lemma lsub_eq_bsub k G Δ d d' Γ : k < nbr -> [ G ; Δ ⊢[ lM ] d ≅ d' : Γ ] ->
  [ brG k G ; wkc (br_nu k) (br_ng k) Δ ⊢[ lM ] bsub k d ≅ bsub k d' : wkc (br_nu k) (br_ng k) Γ ].
Proof.
  intros Hk Hd. pose proof (wf_brG (ctx_glob _ _ _ (lsub_wf_ctx (lsub_eq_l Hd))) k Hk) as HG.
  unfold bsub, wkc, brG. rewrite <- (brDecls_len k Hk).
  apply (lsub_eq_gwkn _ (gΨ (gctx_uwk (br_nu k) G)) (brDecls k)); [exact HG|].
  apply lsub_eq_uwkn, Hd.
Qed.

Lemma lsub_eq_recΓT G Δ d d' Γ : [ G ; Δ ⊢[ lM ] d ≅ d' : Γ ] ->
  [ recGT G ; recΓT Δ ⊢[ lM ] llift (gwk (uwk d)) ≅ llift (gwk (uwk d')) : recΓT Γ ].
Proof.
  intros Hd. pose proof (wf_recΓT _ _ (lsub_wf_ctx (lsub_eq_l Hd))) as HΘ.
  unfold recΓT in *. inversion HΘ as [| |? ? ? A l HΔ HA Hl]; subst.
  eapply (lsub_eq_lift (i := lM) eq_refl); [ | exact HA | exact I | apply eqty_refl, HA | reflexivity].
  pose proof (wf_recGT (ctx_glob _ _ _ (lsub_wf_ctx (lsub_eq_l Hd)))) as HG.
  apply (lsub_eq_gwkn _ _ (gdCtx :: nil)); [exact HG|]. apply (lsub_eq_uwkn 1), Hd.
Qed.
Lemma lsub_eq_recΓt G Δ d d' Γ : [ G ; Δ ⊢[ lM ] d ≅ d' : Γ ] ->
  [ recGt G ; recΓt Δ ⊢[ lM ] llift (gwk (gwk (uwk d))) ≅ llift (gwk (gwk (uwk d'))) : recΓt Γ ].
Proof.
  intros Hd. pose proof (wf_recΓt _ _ (lsub_wf_ctx (lsub_eq_l Hd))) as HΘ.
  unfold recΓt in *. inversion HΘ as [| |? ? ? A l HΔ HA Hl]; subst.
  eapply (lsub_eq_lift (i := lM) eq_refl); [ | exact HA | exact I | apply eqty_refl, HA | reflexivity].
  pose proof (wf_recGt (ctx_glob _ _ _ (lsub_wf_ctx (lsub_eq_l Hd)))) as HG.
  apply (lsub_eq_gwkn _ _ (_ :: gdCtx :: nil)); [exact HG|]. apply (lsub_eq_uwkn 1), Hd.
Qed.

#[export] Hint Resolve lsub_eq_l lsub_eq_r lsub_eq_typeof lsub_wf_typeof : fung.
#[export] Hint Extern 3 (wf_tm _ _ _ (subst _ _) _ _) => eapply wf_tm_subst_g : fung.
#[export] Hint Extern 3 (wf_ty _ _ _ (subst _ _) _) => eapply wf_ty_subst_g : fung.
#[export] Hint Extern 4 (eq_ty _ _ _ (subst _ _) (subst _ _) _) => eapply eqty_subst_g : fung.
#[export] Hint Extern 3 (eq_ty _ _ _ (subst ?T _) (subst ?T _) _) =>
  eapply eqty_subst_g; [ eapply eqty_refl | ] : fung.
#[export] Hint Extern 2 (lsub_eq _ _ _ (llift _) (llift _) _) =>
  eapply lsub_eq_lift_g; [ .. | sub_rw; reflexivity ] : fung.
#[export] Hint Resolve wfc_ext wft_nat wft_El wft_U wf_code_nat wf_code_U wf_zero
  lequiv_wf_l lequiv_wf_r lequiv_refl compt_notV wf_ctx_nat wft_CTyp wft_CTrm eqc_refl : fung.
#[export] Hint Extern 1 (lwf _ _) => (cbn; first [exact I | assumption | split; assumption]) : fung.
#[export] Hint Extern 3 (wf_ty _ (typeof _) _ _ _) => eapply lift_ty; [ | apply lle_self_typeof ] : fung.
#[export] Hint Extern 3 (wf_tm _ (typeof _) _ _ _ _) => eapply lift_tm; [ | apply lle_self_typeof ] : fung.
#[export] Hint Extern 3 (eq_ty _ (typeof _) _ _ _ _) => eapply lift_eqty; [ | apply lle_self_typeof ] : fung.
#[export] Hint Extern 1 (wf_ctx _ (typeof (typeof _)) _) => rewrite typeof_idem : fung.
#[export] Hint Extern 1 (lsub_eq _ (typeof (typeof _)) _ _ _ _) => rewrite typeof_idem : fung.
#[export] Hint Extern 1 (lsub_wf _ (typeof (typeof _)) _ _ _) => rewrite typeof_idem : fung.
#[export] Hint Extern 1 (wf_ctx _ _ _) =>
  match goal with H : lsub_eq _ _ _ _ _ _ |- _ => exact (lsub_wf_ctx (lsub_eq_l H)) end : fung.
#[export] Hint Extern 1 (@eq ty _ _) => (sub_rw; reflexivity) : fung.
#[export] Hint Extern 20 (eq_tm _ _ _ _ _ _ _) => eapply eq_tm_retype : fung.

Ltac fung_premise :=
  rewrite ?typeof_idem;
  first [ solve [eauto 6 with fung]
        | solve [match goal with IH : forall Δ d d', lsub_eq _ _ _ _ _ _ -> eq_ty _ _ _ _ _ _ |- eq_ty _ _ _ _ _ _ =>
                   eapply IH; solve [eauto 8 with fung] end]
        | solve [eapply eq_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 10 with fung] end
                 | sub_rw; reflexivity]] ].

Ltac fung_step :=
  match goal with
  | Hc : eq_ty _ _ _ ?T ?T' ?l |- eq_tm _ _ _ _ _ (subst ?T _) ?l =>
      eapply eqtm_conv; [ | eapply eqty_subst_g ]
  | Hl : lequiv _ ?l ?l' |- eq_ty _ _ _ _ _ ?l => eapply eqty_lconv
  | Hl : lequiv _ ?l ?l' |- eq_tm _ _ _ _ _ _ ?l => eapply eqtm_lconv
  | |- eq_ty _ _ _ _ _ _ => eapply eqty_refl
  | |- eq_tm _ _ _ _ _ _ _ => eapply eqtm_refl
  end; fung_premise.

Ltac fung_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin; rewrite !llk_lcomp;
  match goal with
  | Hd : lsub_eq _ _ _ ?d ?d' _ |- context [lcomp ?e ?d0] =>
      rewrite <- (subst_subst_ty A e d0 (lcomp e d0) (fun m => llk_lcomp e d0 m))
  end;
  first
  [ match goal with IH : forall n A k (_ : in_ctx _ n A k) Δ d d', _ |- _ =>
      eapply (IH n A k Hin); eassumption end
  | match goal with
    | w : forall n A k (_ : in_ctx _ n A k), wf_tm _ _ _ _ _ _, Hd : lsub_eq _ _ _ _ _ _ |- _ =>
        eapply (wf_tm_subst_g (w n A k Hin)); first [exact (lsub_eq_l Hd) | exact (lsub_eq_r Hd)]
    end ].

Ltac fung_side :=
  first [ solve [eassumption] | solve [eauto with fung]
        | solve [eapply tail_lcomp; [eassumption | eapply lsub_wf_tail;
                                     first [eapply lsub_eq_l; eassumption | eapply lsub_eq_r; eassumption]]]
        | solve [eapply dnfl_lcomp; [eassumption | eapply lsub_wf_dnf;
                                     first [eapply lsub_eq_l; eassumption | eapply lsub_eq_r; eassumption]]] ].

Ltac fung_body :=
  match goal with
  | IH : forall Δ' e e', lsub_eq (gext ?G ?D) _ Δ' e e' (?Γ⟪S⟫) -> _,
    Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ |- _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext G D ])
        by (unfold gext; first [eapply wfg_ty | eapply wfg_tm];
            first [exact (ctx_glob _ _ _ (lsub_wf_ctx (lsub_eq_l Hd))) | eassumption | left; reflexivity
                  | right; reflexivity | cbn; eassumption | eapply lequiv_wf_l; eassumption
                  | eapply lequiv_wf_r; eassumption]);
      pose proof (IH _ _ _ (lsub_eq_gwk _ _ _ _ _ _ _ Hg Hd)) as X;
      rewrite body_subst_ty in X by (eauto with nf; reflexivity); exact X
  end.

(** The right-hand letbox body, typed under [gwk d']. *)
Ltac fung_body_wf :=
  match goal with
  | w : wf_tm (gext ?G ?D) _ (?Γ⟪S⟫) ?t _ _, Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ
    |- wf_tm _ _ _ (subst ?t (gwk ?d')) _ _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext G D ])
        by (unfold gext; first [eapply wfg_ty | eapply wfg_tm];
            first [exact (ctx_glob _ _ _ (lsub_wf_ctx (lsub_eq_l Hd))) | eassumption | left; reflexivity
                  | right; reflexivity | cbn; eassumption | eapply lequiv_wf_l; eassumption
                  | eapply lequiv_wf_r; eassumption]);
      pose proof (wf_tm_subst_g w (lsub_wf_gwk _ _ _ _ _ _ Hg (lsub_eq_r Hd))) as X;
      rewrite body_subst_ty in X by first [exact (lsub_wf_nf (lsub_eq_r Hd)) | reflexivity]; exact X
  end.

Ltac fung_manual :=
  match goal with
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      eapply eqty_gvar; [ .. | fung_entries | fung_entries | fung_entries]; fung_side
  | Hd : lsub_eq _ _ _ ?d _ _ |- eq_tm _ _ _ (gvar _ _) _ (subst (subst ?T ?e) ?d) _ =>
      rewrite (subst_subst_ty T e d (lcomp e d) (fun m => llk_lcomp e d m));
      eapply eqtm_gvar; [ .. | fung_entries | fung_entries | fung_entries]; fung_side
  | |- eq_tm _ _ _ (boxT _) _ _ _ => apply eqtm_refl; eapply wf_boxT; eauto; fung_side
  | |- eq_tm _ _ _ (boxt _) _ _ _ => apply eqtm_refl; eapply wf_boxt; eauto; fung_side
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_letboxT; try fung_body; try fung_body_wf;
      try (match goal with IH : forall Δ' e e', _ -> eq_ty _ _ _ (subst _ _) _ _ |- eq_ty _ _ _ _ _ _ =>
             eapply IH; eapply lsub_eq_lift_CTyp_g; eauto end);
      try (eapply wf_ty_subst_g; [eassumption | eapply lsub_wf_lift_CTyp; eauto with fung]);
      eauto 6 using eqc_refl, lequiv_refl, wf_ty_subst_g, lequiv_wf_l with fung
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_letboxt; try fung_body; try fung_body_wf;
      try (match goal with IH : forall Δ' e e', _ -> eq_ty _ _ _ (subst _ _) _ _ |- eq_ty _ _ _ _ _ _ =>
             eapply IH; eapply lsub_eq_lift_CTrm_g; eauto end);
      try (eapply wf_ty_subst_g; [eassumption | eapply lsub_wf_lift_CTrm; eauto with fung]);
      eauto 6 using eqc_refl, lequiv_refl, eqty_refl, wf_ty_subst_g, lequiv_wf_l with fung
  end.

(** The meta-functions (M5): the bodies at [gwk d] and [gwk d']. *)
Ltac fung_mf_setup :=
  match goal with
  | Hd : lsub_eq ?G ?i ?Δ ?d ?d' ?Γ, wT : wf_ty (gext ?G ?D) _ (?Γ⟪S⟫) ?T ?l |- _ =>
      let Hg := fresh "Hg" in let Hgd := fresh "Hgd" in
      assert (Hg : [ ⊢ gext G D ])
        by exact (ctx_glob _ _ _ (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ wT));
      assert (Hgd : lsub_eq (gext G D) i Δ⟪S⟫ (gwk d) (gwk d') Γ⟪S⟫)
        by exact (lsub_eq_gwk _ _ _ _ _ _ _ Hg Hd);
      pose proof (wf_ty_subst_g wT (lsub_eq_l Hgd));
      pose proof (wf_ty_subst_g wT (lsub_eq_r Hgd));
      try match goal with
          | IH : forall Δ0 e e', lsub_eq (gext G D) _ Δ0 e e' (Γ⟪S⟫) -> eq_ty _ _ _ (subst T _) _ _ |- _ =>
              pose proof (IH _ _ _ Hgd) end;
      try match goal with
          | wt : wf_tm (gext G D) _ (Γ⟪S⟫) ?t T _,
            IH : forall Δ0 e e', lsub_eq (gext G D) _ Δ0 e e' (Γ⟪S⟫) -> eq_tm _ _ _ (subst ?t _) _ _ _ |- _ =>
              pose proof (IH _ _ _ Hgd); pose proof (wf_tm_subst_g wt (lsub_eq_r Hgd)) end
  end.
Ltac fung_mf_rw :=
  match goal with Hd : lsub_eq _ _ _ ?d _ _ |- _ =>
    rewrite ?(gsingle_subst_ty _ d _ (lsub_wf_dnf (lsub_eq_l Hd))) end.
(** The instance's reflexivity, from its well-formedness premise at [d]. *)
Ltac fung_inst_refl :=
  match goal with
  | w : wf_ty ?G _ ?Γ ?T⦃gsingle ?o⦄ ?l, Hd : lsub_eq ?G _ ?Δ ?d _ ?Γ |- eq_ty _ _ _ _ _ _ =>
      let X := fresh "X" in
      pose proof (wf_ty_subst_g w (lsub_eq_l Hd)) as X;
      rewrite (gsingle_subst_ty _ d _ (lsub_wf_dnf (lsub_eq_l Hd))) in X;
      apply eqty_refl; exact X
  end.
Ltac fung_mf :=
  match goal with
  | |- eq_ty _ _ _ (tyCPi _ _) _ _ => fung_mf_setup; eapply eqty_cpi; eauto 6 with fung
  | |- eq_ty _ _ _ (tyTPi _ _ _ _) _ _ => fung_mf_setup; eapply eqty_tpi; eauto 6 with fung
  | |- eq_tm _ _ _ (clam _ _ _) _ _ _ => fung_mf_setup; eapply eqtm_clam; eauto 6 with fung
  | |- eq_tm _ _ _ (tlam _ _ _ _ _) _ _ _ =>
      fung_mf_setup; eapply eqtm_tlam; try solve [eauto 6 with fung];
      match goal with
      | X : wf_tm _ _ _ ?t ?T' _, E : eq_ty _ _ _ ?T ?T' _ |- wf_tm _ _ _ ?t ?T _ => exact (wf_conv _ _ _ _ _ _ _ X E)
      end
  | |- eq_tm _ _ _ (capp _ _) _ _ _ =>
      fung_mf_rw; fung_mf_setup; eapply eqtm_capp; try solve [eauto 6 with fung];
      fung_inst_refl
  | |- eq_tm _ _ _ (tapp _ _) _ _ _ =>
      fung_mf_rw; fung_mf_setup; eapply eqtm_tapp; try solve [eauto 6 with fung];
      first [fung_inst_refl | apply eqty_refl; assumption]
  end.

(** [UΠ] (M4): the body at [uwkn n d] and [uwkn n d']. *)
Ltac fung_upi_ih :=
  match goal with
  | Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ, IH : forall Δ e e', lsub_eq (gctx_uwk ?n ?G) _ Δ e e' _ -> _ |- _ =>
      apply IH, lsub_eq_uwkn, Hd
  end.
Ltac fung_upi_wf :=
  match goal with
  | Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ |- wf_ty (gctx_uwk _ _) _ _ _ _ =>
      eapply wf_ty_subst_g; [eassumption | apply lsub_wf_uwkn, (lsub_eq_l Hd)]
  end.
Ltac fung_upi :=
  match goal with
  | Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ |- eq_ty _ _ _ (tyUPi _ _ _) _ _ =>
      eapply eqty_upi;
      [ exact (lsub_wf_ctx (lsub_eq_l Hd)) | assumption | apply lequiv_refl; assumption
      | fung_upi_wf | fung_upi_ih ]
  | Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ |- eq_tm _ _ _ (ulam _ _ _ _) _ _ _ =>
      eapply eqtm_ulam;
      [ exact (lsub_wf_ctx (lsub_eq_l Hd)) | assumption | apply lequiv_refl; assumption
      | fung_upi_wf | fung_upi_ih | fung_upi_ih ]
  | Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ, Hn : length ?ls = ?n |- eq_tm _ _ _ (uapp (subst ?t _) ?ls) _ _ _ =>
      rewrite (subst_uinst_ty n ls _ d Hn (lsub_wf_dnf (lsub_eq_l Hd)));
      eapply eqtm_uapp;
      [ eassumption | fung_upi_wf | exact Hn | apply lequivs_refl; assumption
      | match goal with IH : forall Δ e e', lsub_eq G _ Δ e e' Γ -> eq_tm _ _ _ (subst t _) _ _ _ |- _ =>
          apply IH, Hd end ]
  end.

(** The context cases: equal substitutions of a prefix, lifted through the
    rest (M3_DESIGN.md E8). *)
Ltac fun_ctx :=
  match goal with
  | Heq : _ = cexts ?Γ0 ?As, Hd : lsub_eq _ _ _ ?d ?d' ?Γ0 |- _ =>
      let As' := fresh "As'" in let A' := fresh "A'" in let l' := fresh "l'" in
      let Θ' := fresh "Θ'" in let Hθ := fresh "Hθ" in
      destruct (cexts_inv _ _ _ (eq_sym Heq)) as [[-> ?] | (As' & A' & l' & Θ' & -> & Hθ & ->)];
      [ exact Hd
      | first [ discriminate Hθ
              | let HΓ := fresh "HΓ" in
                injection Hθ as HΓ <- <-;
                rewrite cexts_sub_snoc, !cexts_snoc, length_app, Nat.add_comm; cbn [Nat.add];
                rewrite !lliftn_S;
                match goal with
                | IHc : forall Γ As, _ = cexts Γ As -> _,
                  IHt : forall Δ d d', lsub_eq _ _ Δ d d' _ -> eq_ty _ _ _ _ _ _,
                  w : wf_ty _ _ _ _ _ |- _ =>
                    let X := fresh "X" in
                    pose proof (IHc _ _ HΓ _ _ _ Hd) as X; rewrite <- HΓ in X |- *;
                    eapply lsub_eq_lift_g;
                    [ exact X
                    | eapply lift_ty; [exact (wf_ty_subst_g w (lsub_eq_l X)) | apply lle_self_typeof]
                    | assumption
                    | eapply lift_eqty; [exact (IHt _ _ _ X) | apply lle_self_typeof]
                    | reflexivity ]
                end ] ]
  end.

(** The recursors' premises. *)
Ltac fun_rec_prem :=
  match goal with
  | |- eq_ty _ lD _ ?T ?T _ => apply eqty_refl; assumption
  (* the motive instance at [d] and [d'] (M3_DESIGN.md E10) *)
  | Hd : lsub_eq _ _ _ ?d ?d' ?Γ |- eq_ty _ _ _ (motT _ _ _ _) (motT _ _ _ _) _ =>
      eapply eq_ty_regty;
      [ match goal with IH : forall Δ d d', lsub_eq _ _ Δ d d' Γ -> eq_ty _ _ _ _ _ _ |- _ =>
          eapply IH; exact Hd end
      | rewrite motT_subst by first [hd_tac | exact (lsub_wf_dnf (lsub_eq_l Hd))]; reflexivity
      | rewrite motT_subst by first [hd_tac | exact (lsub_wf_dnf (lsub_eq_r Hd))]; reflexivity ]
  | Hd : lsub_eq _ _ _ ?d ?d' ?Γ |- eq_ty _ _ _ (mott _ _ _ _ _) (mott _ _ _ _ _) _ =>
      eapply eq_ty_regty;
      [ match goal with IH : forall Δ d d', lsub_eq _ _ Δ d d' Γ -> eq_ty _ _ _ _ _ _ |- _ =>
          eapply IH; exact Hd end
      | rewrite mott_subst by first [hd_tac | exact (lsub_wf_dnf (lsub_eq_l Hd))]; reflexivity
      | rewrite mott_subst by first [hd_tac | exact (lsub_wf_dnf (lsub_eq_r Hd))]; reflexivity ]
  | Hd : lsub_eq _ _ _ ?d ?d' ?Γ |- wf_ty (recGT _) _ _ _ _ =>
      eapply motT_subst_wf; [ first [exact (lsub_eq_l Hd) | exact (lsub_eq_r Hd)] | eassumption ]
  | Hd : lsub_eq _ _ _ ?d ?d' ?Γ |- wf_ty (recGt _) _ _ _ _ =>
      eapply mott_subst_wf; [ first [exact (lsub_eq_l Hd) | exact (lsub_eq_r Hd)] | eassumption ]
  | Hd : lsub_eq _ _ _ ?d ?d' ?Γ, IH : forall Δ d d', lsub_eq _ _ Δ d d' (recΓT ?Γ) -> _
    |- eq_ty (recGT _) _ _ _ _ _ => apply IH, lsub_eq_recΓT, Hd
  | Hd : lsub_eq _ _ _ ?d ?d' ?Γ, IH : forall Δ d d', lsub_eq _ _ Δ d d' (recΓt ?Γ) -> _
    |- eq_ty (recGt _) _ _ _ _ _ => apply IH, lsub_eq_recΓt, Hd
  | Hd : lsub_eq _ _ _ ?d ?d' ?Γ |- forall k, k < nbr -> wf_ctx (brG k _) _ _ =>
      let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
      eapply brctx_subst; [ first [exact (lsub_eq_l Hd) | exact (lsub_eq_r Hd)] | exact Hk
                          | match goal with w : forall k, k < nbr -> wf_ctx _ _ _ |- _ => apply w, Hk end ]
  | Hd : lsub_eq _ _ _ ?d ?d' ?Γ |- forall k, k < nbr -> wf_tm (brG k _) _ _ _ _ _ =>
      let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
      eapply branch_subst; [ exact (lsub_eq_r Hd) | exact Hk
                           | match goal with w : forall k, k < nbr -> wf_ctx _ _ _ |- _ => apply w, Hk end
                           | match goal with w : forall k, k < nbr -> wf_tm _ _ _ _ _ _ |- _ => apply w, Hk end ]
  | Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ |- forall k, k < nbr -> eq_tm (brG k _) _ _ _ _ _ _ =>
      let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
      match goal with
      | IHc : forall k, k < nbr -> forall Γ0 As, brΓ k Γ (wrapMT ?MT) (wrapMt ?Mt) ?l1 ?l2 = cexts Γ0 As -> _,
        IH : forall k, k < nbr -> forall Δ d d', lsub_eq _ _ Δ d d' (brΓ k Γ _ _ _ _) -> _ |- _ =>
          let X := fresh "X" in let Y := fresh "Y" in
          pose proof (IHc k Hk _ _ eq_refl _ _ _ (lsub_eq_bsub k _ _ _ _ _ Hk Hd)) as X;
          rewrite brLocs_subst in X by (first [exact Hk | exact (lsub_wf_dnf (lsub_eq_l Hd))]);
          rewrite brLocs_len in X by exact Hk;
          pose proof (IH k Hk _ _ _ X) as Y;
          rewrite brRes_subst in Y by (first [exact Hk | exact (lsub_wf_dnf (lsub_eq_l Hd))]);
          exact Y
      end
  end.

Ltac fun_rec :=
  match goal with
  | Hd : lsub_eq _ _ _ ?d ?d' _ |- eq_tm _ _ _ (elimT _ _ _ _ _ _) _ _ _ =>
      rewrite ?mkrb_subst; rewrite ?motT_subst by first [hd_tac | exact (lsub_wf_dnf (lsub_eq_l Hd))];
      eapply eqtm_elimT; first [fun_rec_prem | fung_premise]
  | Hd : lsub_eq _ _ _ ?d ?d' _ |- eq_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ _ =>
      rewrite ?mkrb_subst; rewrite ?mott_subst by first [hd_tac | exact (lsub_wf_dnf (lsub_eq_l Hd))];
      eapply eqtm_elimt; first [fun_rec_prem | fung_premise]
  end.

Theorem functionality_all :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Θ, [ G ; Θ ⊢[ i ] ] -> forall Γ As, Θ = cexts Γ As ->
     forall Δ d d', [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] ->
     [ G ; cexts Δ (cexts_sub As d) ⊢[ i ] lliftn (length As) d ≅ lliftn (length As) d' : cexts Γ As ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] ->
     forall Δ d d', [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T[d'] @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] ->
     forall Δ d d', [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] t[d] ≅ t[d'] : T[d] @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I; try fun_ctx;
    try match goal with c : compt ?i |- _ => pose proof (compt_notV _ c) end;
    try match goal with Hd : lsub_eq _ _ _ _ _ _ |- _ => pose proof (lsub_eq_l Hd) end;
    cbn [typeof] in *; sub_rw.
  all: try solve [eapply lsub_eq_var; eassumption].
  all: try fun_rec.
  all: try fung_upi.
  all: try fung_mf.
  all: try fung_manual.
  all: try (timeout 3 any_rule fung_premise).
  all: try (timeout 3 fung_step).
  (* code of Π and natrec: the binder premises need the substituted
     derivation of the bound type first *)
  - match goal with
    | Hd : lsub_eq _ _ ?Δ ?d ?d' ?Γ, Hw : lsub_wf ?G ?i ?Δ ?d ?Γ,
      ws : wf_tm ?G _ ?Γ ?s (tyU ?l) ?ll
      |- eq_tm _ _ _ (tmPi _ _ _ (@subst tm _ _ _)) _ _ _ =>
        assert (wf_tm G i Δ s[d] (tyU l) ll) by exact (wf_tm_subst_g ws Hw);
        assert (eq_tm G i Δ s[d] s[d'] (tyU l) ll)
          by (match goal with IH : forall Δ d d', _ -> eq_tm _ _ _ (subst ?x _) _ _ _ |- _ =>
                constr_eq x s; eapply IH; exact Hd end);
        assert (eq_ty G i Δ (tyEl l s)[d] (tyEl l s)[d'] l)
          by (push_subst; apply eqty_El; auto using lequiv_refl)
    end.
    eapply eqtm_code_pi; eauto 7 with fung.
  - match goal with
    | Hd : lsub_eq _ _ ?Δ ?d ?d' ?Γ, Hw : lsub_wf ?G ?i ?Δ ?d ?Γ,
      wM : wf_ty ?G _ (?Γ ,, tyNat @ lzero) ?M ?l
      |- eq_tm _ _ _ (natrec _ _ _ _ _) _ _ _ =>
        assert (Hnat : wf_ty G (typeof i) Δ tyNat lzero)
          by (apply wft_nat; [destruct i; cbn; congruence | rewrite typeof_idem; exact (lsub_wf_ctx Hw)]);
        assert (Hn : lsub_eq G i (Δ ,, tyNat @ lzero) (llift d) (llift d') (Γ ,, tyNat @ lzero))
          by (eapply lsub_eq_lift_g; [exact Hd | exact Hnat | exact I | | reflexivity];
              now apply eqty_refl);
        pose proof (wf_ty_subst_g wM (lsub_eq_l Hn));
        assert (eq_ty G i (Δ ,, tyNat @ lzero) M[llift d] M[llift d'] l)
          by (match goal with IH : forall Δ d d', _ -> eq_ty _ _ _ (subst ?x _) _ _ |- _ =>
                constr_eq x M; eapply IH; exact Hn end)
    end.
    eapply eqtm_natrec; try solve [eauto 6 with fung].
    all: eapply eq_tm_retype;
      [match goal with IH : _ |- _ => eapply IH; solve [eauto 6 with fung] end | sub_rw; reflexivity].
  (* code of Σ (M8), as for Π *)
  - match goal with
    | Hd : lsub_eq _ _ ?Δ ?d ?d' ?Γ, Hw : lsub_wf ?G ?i ?Δ ?d ?Γ,
      ws : wf_tm ?G _ ?Γ ?s (tyU ?l) ?ll
      |- eq_tm _ _ _ (tmSig _ _ _ (@subst tm _ _ _)) _ _ _ =>
        assert (wf_tm G i Δ s[d] (tyU l) ll) by exact (wf_tm_subst_g ws Hw);
        assert (eq_tm G i Δ s[d] s[d'] (tyU l) ll)
          by (match goal with IH : forall Δ d d', _ -> eq_tm _ _ _ (subst ?x _) _ _ _ |- _ =>
                constr_eq x s; eapply IH; exact Hd end);
        assert (eq_ty G i Δ (tyEl l s)[d] (tyEl l s)[d'] l)
          by (push_subst; apply eqty_El; auto using lequiv_refl)
    end.
    eapply eqtm_code_sig; eauto 7 with fung.
Qed.

Theorem functionality :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> typeof i = i ->
     forall Δ d d', [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T[d'] @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> typeof i = i ->
     forall Δ d d', [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] t[d] ≅ t[d'] : T[d] @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  destruct functionality_all as (_ & _ & H1 & H2 & _).
  refine (conj (fun _ _ => I) (conj (fun _ _ _ _ => I) (conj _ (conj _ (conj _ _))))); intros; eauto.
Qed.
