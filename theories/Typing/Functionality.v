(** * Consequences of the substitution lemma: single substitutions,
    context conversion (stability) and functionality (ch. 5) *)
From DeLaM.Typing Require Export Substitution.

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

Lemma lsub_wf_conv {Γ A A' l} :
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ,, A' @ l ⊢[ i ] ] ->
  [ G ; Γ ,, A' @ l ⊢[ i ] lshift 0 : Γ ,, A @ l ].
Proof.
  intros HA HΓ'. refine (conj HΓ' (conj (fun n => I) _)).
  intros n T l' Hin. rewrite nf_id_ty by eauto using in_ctx_nf. cbn; rewrite Nat.add_0_r.
  inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst.
  - eapply wf_conv; [apply var0_wf; auto|].
    rewrite Hi. apply wk1_eqty; auto.
  - apply wf_var; [now rewrite Hi | now constructor].
Qed.

Lemma stab_ty {Γ A A' l T l'} :
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ,, A' @ l ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] T @ l' ] -> [ G ; Γ ,, A' @ l ⊢[ i ] T @ l' ].
Proof.
  intros HA HΓ H. rewrite <- (nf_id_ty T) by exact (wf_ty_nf H).
  eapply wf_ty_subst; eauto using lsub_wf_conv.
Qed.
Lemma stab_tm {Γ A A' l t T l'} :
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ,, A' @ l ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t : T @ l' ] -> [ G ; Γ ,, A' @ l ⊢[ i ] t : T @ l' ].
Proof.
  intros HA HΓ H. rewrite <- (nf_id_ty T) by exact (wf_tm_nf_ty H).
  rewrite <- (nf_id t) by exact (wf_tm_nf H).
  eapply wf_tm_subst; eauto using lsub_wf_conv.
Qed.
Lemma stab_eqty {Γ A A' l T T' l'} :
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ,, A' @ l ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] T ≅ T' @ l' ] -> [ G ; Γ ,, A' @ l ⊢[ i ] T ≅ T' @ l' ].
Proof.
  intros HA HΓ H. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ H) as [N1 N2].
  rewrite <- (nf_id_ty T), <- (nf_id_ty T') by assumption.
  eapply eqty_subst; eauto using lsub_wf_conv.
Qed.
Lemma stab_eqtm {Γ A A' l t t' T l'} :
  [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ,, A' @ l ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t ≅ t' : T @ l' ] -> [ G ; Γ ,, A' @ l ⊢[ i ] t ≅ t' : T @ l' ].
Proof.
  intros HA HΓ H. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ _ H)
    as (N1 & N2 & N3).
  rewrite <- (nf_id_ty T), <- (nf_id t), <- (nf_id t') by assumption.
  eapply eqtm_subst; eauto using lsub_wf_conv.
Qed.

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
  assert (HΔ : [ G ; Δ ,, A[d] @ l ⊢[ i ] ]) by (apply wfc_ext; eauto using lsub_wf_ctx, lsub_eq_l).
  refine (conj (lsub_wf_lift G i Hi _ _ _ _ _ (lsub_eq_l Hd) HA Hl)
            (conj (conj HΔ (conj (lk_llift _ (lsub_wf_nf (lsub_eq_r Hd))) _)) _)).
  - intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst;
      rewrite llk_llift, shift_llift_ty.
    + eapply wf_conv; [apply var0_wf; auto|]. rewrite Hi. apply wk1_eqty; auto using eqty_sym.
    + apply wk1_tm; auto. exact (lsub_wf_var (lsub_eq_r Hd) Hm).
  - intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst;
      rewrite !llk_llift, shift_llift_ty.
    + apply eqtm_refl, var0_wf; auto.
    + apply wk1_eqtm; auto. exact (lsub_eq_var Hd Hm).
Qed.

End LsubEq.

#[export] Hint Resolve lsub_eq_l lsub_eq_r : sub.
#[export] Hint Extern 3 (wf_tm _ _ _ (subst _ _) _ _) => eapply wf_tm_subst : sub.
#[export] Hint Extern 4 (eq_ty _ _ _ (subst _ _) (subst _ _) _) => eapply eqty_subst : sub.
#[export] Hint Resolve wft_U wf_code_nat wf_code_U wf_zero lequiv_refl : sub.
#[export] Hint Extern 2 (lsub_eq _ _ _ (llift _) (llift _) _) =>
  eapply lsub_eq_lift; [ .. | sub_rw; reflexivity ] : sub.
#[export] Hint Extern 3 (wf_ty _ _ _ (subst _ _) _) => eapply wf_ty_subst : sub.
#[export] Hint Extern 3 (eq_ty _ _ _ (subst ?T _) (subst ?T _) _) =>
  eapply eqty_subst; [ | eapply eqty_refl | ] : sub.

Ltac fun_premise :=
  fix_layer;
  first [ solve [eauto 6 with sub]
        | solve [eapply eq_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 10 with sub] end
                 | sub_rw; reflexivity]] ].

Ltac fun_step :=
  match goal with
  | |- eq_ty _ _ _ (tyPi _ _ _ _) _ _ => eapply eqty_pi
  | |- eq_ty _ _ _ (tyEl _ _) _ _ => eapply eqty_El
  | |- eq_tm _ _ _ (tmPi _ _ _ _) _ _ _ => eapply eqtm_code_pi
  | |- eq_tm _ _ _ (succ _) _ _ _ => eapply eqtm_succ
  | |- eq_tm _ _ _ (natrec _ _ _ _ _) _ _ _ => eapply eqtm_natrec
  | |- eq_tm _ _ _ (lam _ _ _ _) _ _ _ => eapply eqtm_lam
  | |- eq_tm _ _ _ (app _ _ _ _ _ _) _ _ _ => eapply eqtm_app
  | Hc : eq_ty _ _ _ ?T ?T' ?l |- eq_tm _ _ _ _ _ (subst ?T _) ?l =>
      eapply eqtm_conv; [ | eapply eqty_subst ]
  | Hl : lequiv _ ?l ?l' |- eq_ty _ _ _ _ _ ?l => eapply eqty_lconv
  | Hl : lequiv _ ?l ?l' |- eq_tm _ _ _ _ _ _ ?l => eapply eqtm_lconv
  | |- eq_ty _ _ _ _ _ _ => eapply eqty_refl
  | |- eq_tm _ _ _ _ _ _ _ => eapply eqtm_refl
  end; fun_premise.

Theorem functionality :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> typeof i = i ->
     forall Δ d d', [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T[d'] @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> typeof i = i ->
     forall Δ d d', [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] t[d] ≅ t[d'] : T[d] @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end;
    try match goal with Hd : lsub_eq _ _ _ _ _ _ |- _ => pose proof (lsub_eq_l Hd) end;
    sub_rw.
  all: try solve [eapply lsub_eq_var; eassumption].
  all: try (timeout 3 fun_step).
  (* code of Π and natrec: the binder premises need the substituted
     derivation of the bound type first *)
  - match goal with
    | Hi : typeof ?i = ?i, Hd : lsub_eq _ _ ?Δ ?d ?d' ?Γ, Hw : lsub_wf _ _ ?Δ ?d ?Γ,
      ws : wf_tm ?G _ ?Γ ?s (tyU ?l) ?ll
      |- eq_tm _ _ _ (tmPi _ _ _ (@subst tm _ _ _)) _ _ _ =>
        assert (wf_tm G i Δ s[d] (tyU l) ll) by exact (wf_tm_subst Hi ws Hw);
        assert (eq_tm G i Δ s[d] s[d'] (tyU l) ll)
          by (match goal with IH : _ = _ -> _ |- _ => eapply IH; [reflexivity | exact Hd] end);
        assert (eq_ty G i Δ (tyEl l s)[d] (tyEl l s)[d'] l)
          by (push_subst; apply eqty_El; auto using lequiv_refl)
    end.
    eapply eqtm_code_pi; fix_layer; eauto 7 with sub.
  - match goal with
    | Hi : typeof ?i = ?i, Hd : lsub_eq _ _ ?Δ ?d ?d' ?Γ, Hw : lsub_wf _ _ ?Δ ?d ?Γ,
      wM : wf_ty ?G _ (?Γ ,, tyNat @ lzero) ?M ?l
      |- eq_tm _ _ _ (natrec _ _ _ _ _) _ _ _ =>
        assert (Hn : lsub_eq G i (Δ ,, tyNat @ lzero) (llift d) (llift d') (Γ ,, tyNat @ lzero))
          by (assert (Hnat : wf_ty G i Δ tyNat lzero)
                by (apply wft_nat; [auto with sub | rewrite Hi; eauto with sub]);
              eapply (lsub_eq_lift Hi); [exact Hd | exact Hnat | exact I | | reflexivity];
              now apply eqty_refl);
        pose proof (wf_ty_subst Hi wM (lsub_eq_l Hn));
        assert (eq_ty G i (Δ ,, tyNat @ lzero) M[llift d] M[llift d'] l)
          by (match goal with IH : _ = _ -> _ |- _ => eapply IH; [reflexivity | exact Hn] end)
    end.
    eapply eqtm_natrec; fix_layer; try solve [eauto 6 with sub].
    all: eapply eq_tm_retype;
      [match goal with IH : _ |- _ => eapply IH; solve [eauto 6 with sub] end | sub_rw; reflexivity].
Qed.
