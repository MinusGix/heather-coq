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
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ _ _ _ (He _ _ _ HA0) _ _ Hw Hg).
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

(** Global variables: compose the stored substitution with [d] and [d']. *)
Ltac fun_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin; rewrite !llk_lcomp;
  match goal with
  | Hd : lsub_eq _ _ _ ?d ?d' _ |- context [lcomp ?e ?d0] =>
      rewrite <- (subst_subst_ty A e d0 (lcomp e d0) (fun m => llk_lcomp e d0 m))
  end;
  first
  [ match goal with IH : forall n A k (_ : in_ctx _ n A k), _ = _ -> _ |- _ =>
      eapply (IH n A k Hin); [reflexivity | eassumption] end
  | match goal with
    | Hi : typeof ?i = ?i, w : forall n A k (_ : in_ctx _ n A k), wf_tm _ _ _ _ _ _,
      Hd : lsub_eq _ _ _ _ _ _ |- _ =>
        eapply (wf_tm_subst Hi (w n A k Hin)); first [exact (lsub_eq_l Hd) | exact (lsub_eq_r Hd)]
    end ].

Ltac fun_gvar_side :=
  first [ solve [eassumption] | solve [eauto with sub]
        | solve [match goal with Hi : typeof ?i = ?i |- _ => rewrite <- Hi end; eauto with sub]
        | solve [eapply tail_lcomp; [eassumption | eapply lsub_wf_tail;
                                     first [eapply lsub_eq_l; eassumption | eapply lsub_eq_r; eassumption]]]
        | solve [eapply dnfl_lcomp; [eassumption | eapply lsub_wf_dnf;
                                     first [eapply lsub_eq_l; eassumption | eapply lsub_eq_r; eassumption]]]
        | match goal with Hd : lsub_eq _ _ _ _ _ _, Hi : typeof ?i = ?i |- wf_ctx _ _ _ =>
            rewrite Hi; exact (lsub_wf_ctx (lsub_eq_l Hd)) || (rewrite <- Hi; exact (lsub_wf_ctx (lsub_eq_l Hd))) end ].

Ltac fun_gvar :=
  match goal with
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      eapply eqty_gvar; [ .. | fun_entries | fun_entries | fun_entries]; fun_gvar_side
  | Hd : lsub_eq _ _ _ ?d _ _ |- eq_tm _ _ _ (gvar _ _) _ (subst (subst ?T ?e) ?d) _ =>
      rewrite (subst_subst_ty T e d (lcomp e d) (fun m => llk_lcomp e d m));
      eapply eqtm_gvar; [ .. | fun_entries | fun_entries | fun_entries]; fun_gvar_side
  end.

(** letbox: congruence, with the body under [Ψ, U] and [gwk d]/[gwk d']. *)
Ltac fun_body :=
  match goal with
  | IH : forall Δ' e e', lsub_eq (gext ?G ?D) _ Δ' e e' (?Γ⟪S⟫) -> _,
    Hd : lsub_eq ?G _ ?Δ ?d ?d' ?Γ |- _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext G D ])
        by (unfold gext; first [eapply wfg_ty | eapply wfg_tm];
            first [exact (ctx_glob _ _ _ (lsub_wf_ctx (lsub_eq_l Hd))) | eassumption | left; reflexivity
                  | right; reflexivity | cbn; eassumption]);
      pose proof (IH _ _ _ (lsub_eq_gwk _ _ _ _ _ _ _ Hg Hd)) as X;
      rewrite body_subst_ty in X by (eauto with nf; reflexivity); exact X
  end.

Ltac fun_letbox :=
  match goal with
  | |- eq_tm _ _ _ (boxT _) _ _ _ =>
      apply eqtm_refl; eapply wf_boxT; eauto; fun_gvar_side
  | |- eq_tm _ _ _ (boxt _) _ _ _ =>
      apply eqtm_refl; eapply wf_boxt; eauto; fun_gvar_side
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ =>
      repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
      eapply eqtm_letboxT;
      [ .. | match goal with IH : forall Δ' e e', _ -> eq_ty _ _ _ (subst _ _) _ _ |- _ =>
                 eapply IH; first [eapply lsub_eq_lift_CTyp | eapply lsub_eq_lift_CTrm]; eauto end
      | fun_body | ];
      try match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end; eauto 6 using eqc_refl, lequiv_refl, wf_ty_subst, lequiv_wf_l with sub
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ =>
      repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
      eapply eqtm_letboxt;
      [ .. | match goal with IH : forall Δ' e e', _ -> eq_ty _ _ _ (subst _ _) _ _ |- _ =>
                 eapply IH; first [eapply lsub_eq_lift_CTyp | eapply lsub_eq_lift_CTrm]; eauto end
      | fun_body | ];
      try match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end; eauto 6 using eqc_refl, lequiv_refl, eqty_refl, wf_ty_subst, lequiv_wf_l with sub
  end.

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
  apply typing_mut; intros; try exact I;
    match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end;
    try match goal with Hd : lsub_eq _ _ _ _ _ _ |- _ => pose proof (lsub_eq_l Hd) end;
    sub_rw.
  all: try solve [eapply lsub_eq_var; eassumption].
  all: try fun_gvar.
  all: try fun_letbox.
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
                by (apply wft_nat; [auto with sub | exact (lsub_wf_ctx Hw)]);
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
