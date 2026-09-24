(** * Typed local substitutions and the substitution lemma (ch. 5)

    A local substitution is typed by its lookups: [Δ ⊢ d : Γ] when every
    variable of [Γ] is sent to a term of the substituted type.  Entries are
    in normal form ([nftm]), which every typed term is (see [typed_nf]);
    the identity laws inside the commutation lemmas need it.

    As for weakening, the lemma is proved for layers with [typeof i = i]. *)
From DeLaM.Syntax Require Export SubstCommute.
From DeLaM.Typing Require Export Properties.

(** ** Typed terms are in normal form *)

Lemma lk_lsingle a : nftm a -> LK nftm (lsingle a).
Proof. intros H [|n]; cbn; auto. Qed.
Lemma lk_lsingle2 t q : nftm t -> nftm q -> LK nftm (lsingle2 t q).
Proof. intros H1 H2 [|[|n]]; cbn; auto. Qed.
Lemma lk_lsucc : LK nftm lsucc.
Proof. intros [|n]; cbn; auto. Qed.
#[export] Hint Resolve lk_lsingle lk_lsingle2 lk_lsucc : nf.

Theorem typed_nf :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> nfty T) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> nftm t /\ nfty T) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> nfty T /\ nfty T') /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> nftm t /\ nftm t' /\ nfty T).
Proof.
  apply typing_mut; intros; cbn in *;
    intuition eauto using subst_nf_ty, subst_nf, ren_nf_ty, ren_nf, in_ctx_nf with nf.
  apply subst_nf; [assumption | apply lk_lsingle2; cbn; tauto].
Qed.

Lemma wf_ty_nf {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> nfty T.
Proof. apply typed_nf. Qed.
Lemma wf_tm_nf {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> nftm t.
Proof. apply typed_nf. Qed.
Lemma wf_tm_nf_ty {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> nfty T.
Proof. apply typed_nf. Qed.

(** ** Typed local substitutions *)

Definition lsub_wf G i Δ d Γ : Prop :=
  [ G ; Δ ⊢[ i ] ] /\ LK nftm d /\
  (forall n T l, in_ctx Γ n T l -> [ G ; Δ ⊢[ i ] llk d n : T[d] @ l ]).

Notation "[ G ; Δ ⊢[ i ] d : Γ ]" := (lsub_wf G i Δ d Γ)
  (at level 0, G, Δ, i, d, Γ at level 50).

Lemma lsub_wf_ctx {G i Δ d Γ} : [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] ].
Proof. now intros []. Qed.
Lemma lsub_wf_nf {G i Δ d Γ} : [ G ; Δ ⊢[ i ] d : Γ ] -> LK nftm d.
Proof. now intros (? & ? & ?). Qed.
Lemma lsub_wf_var {G i Δ d Γ n T l} :
  [ G ; Δ ⊢[ i ] d : Γ ] -> in_ctx Γ n T l -> [ G ; Δ ⊢[ i ] llk d n : T[d] @ l ].
Proof. intros (? & ? & H); apply H. Qed.

#[export] Hint Resolve lsub_wf_ctx lsub_wf_nf : nf.

Section Lsub.
Context (G : gctx) (i : layer) (Hi : typeof i = i) (Hv : i <> lV).

Lemma wkr_shift1 Γ A l : wkr ↑ (Γ ,, A @ l) Γ.
Proof. exact (wkr_step _ _ _ _ _ (wkr_id Γ)). Qed.

Lemma wk1_ty Γ A l T l' :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] T @ l' ] -> [ G ; Γ ,, A @ l ⊢[ i ] T⟨↑⟩ @ l' ].
Proof. intros; eapply weakening_r; eauto using wkr_shift1. Qed.
Lemma wk1_tm Γ A l t T l' :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] t : T @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t⟨↑⟩ : T⟨↑⟩ @ l' ].
Proof. intros; eapply weakening_r; eauto using wkr_shift1. Qed.
Lemma wk1_eqty Γ A l T T' l' :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] T⟨↑⟩ ≅ T'⟨↑⟩ @ l' ].
Proof. intros; eapply weakening_r; eauto using wkr_shift1. Qed.
Lemma wk1_eqtm Γ A l t t' T l' :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t⟨↑⟩ ≅ t'⟨↑⟩ : T⟨↑⟩ @ l' ].
Proof. intros; eapply weakening_r; eauto using wkr_shift1. Qed.

Lemma var0_wf Γ A l :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ,, A @ l ⊢[ i ] var 0 : A⟨↑⟩ @ l ].
Proof. intros; apply wf_var; [now rewrite Hi | constructor]. Qed.

Lemma lsub_wf_lift Δ d Γ A l :
  [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] A[d] @ l ] -> lwf (gL G) l ->
  [ G ; Δ ,, A[d] @ l ⊢[ i ] llift d : Γ ,, A @ l ].
Proof.
  intros Hd HA Hl.
  assert (HΔ : [ G ; Δ ,, A[d] @ l ⊢[ i ] ]) by (apply wfc_ext; eauto with nf).
  refine (conj HΔ (conj (lk_llift _ (lsub_wf_nf Hd)) _)).
  intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst.
  - rewrite llk_llift, shift_llift_ty. now apply var0_wf.
  - rewrite llk_llift, shift_llift_ty. apply wk1_tm; auto. exact (lsub_wf_var Hd Hm).
Qed.

Lemma lsub_wf_lift' Δ d Γ A A' l :
  [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] A' @ l ] -> lwf (gL G) l -> A' = A[d] ->
  [ G ; Δ ,, A' @ l ⊢[ i ] llift d : Γ ,, A @ l ].
Proof. intros ???->; now apply lsub_wf_lift. Qed.

Lemma lsub_wf_id Γ : [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] lshift 0 : Γ ].
Proof.
  intros HΓ; refine (conj HΓ (conj (fun n => I) _)).
  intros n T l Hin. rewrite (subst_id_ty T) by (eauto using in_ctx_nf; intros; cbn; f_equal; lia).
  cbn; rewrite Nat.add_0_r. apply wf_var; [now rewrite Hi | exact Hin].
Qed.

Lemma lsub_wf_single Γ A a l :
  [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] lsingle a : Γ ,, A @ l ].
Proof.
  intros HΓ Ha. refine (conj HΓ (conj (lk_lsingle _ (wf_tm_nf Ha)) _)).
  intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst; cbn.
  - rewrite shift_single_ty by exact (wf_tm_nf_ty Ha). exact Ha.
  - rewrite shift_single_ty by eauto using in_ctx_nf. rewrite Nat.add_0_r.
    apply wf_var; [now rewrite Hi | exact Hm].
Qed.

End Lsub.

(** ** The substitution lemma *)

Lemma wf_ty_retype G i Δ T l l' : [ G ; Δ ⊢[ i ] T @ l' ] -> l' = l -> [ G ; Δ ⊢[ i ] T @ l ].
Proof. now intros ? ->. Qed.

Lemma llk_llift0 d : llk (llift d) 0 = var 0.
Proof. now rewrite llk_llift. Qed.

Ltac sub_rw :=
  push_subst;
  rewrite ?llk_llift0, ?single_subst_ty, ?single_subst, ?single2_subst, ?lsucc_subst_ty,
          ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty by eauto with nf;
  push_subst.

#[export] Hint Resolve lsub_wf_ctx : sub.
#[export] Hint Resolve wfc_ext wft_nat wft_El lequiv_wf_l lequiv_wf_r wf_ctx_nat compt_notV : sub.
#[export] Hint Extern 2 (lsub_wf _ _ _ (llift _) _) =>
  eapply lsub_wf_lift'; [ .. | sub_rw; reflexivity ] : sub.
#[export] Hint Extern 20 (wf_tm _ _ _ _ _ _) => eapply wf_tm_retype : sub.
#[export] Hint Extern 20 (eq_tm _ _ _ _ _ _ _) => eapply eq_tm_retype : sub.
#[export] Hint Extern 1 (lwf _ _) =>
  (cbn; first [exact I | assumption | split; assumption]) : sub.
#[export] Hint Extern 1 =>
  match goal with Hi : typeof ?i = ?i |- context [typeof ?i] => rewrite Hi end : sub.
#[export] Hint Extern 1 (@eq ty _ _) => (sub_rw; reflexivity) : sub.

Ltac sub_premises := fix_layer; eauto 6 with sub.

Ltac sub_step :=
  match goal with
  | |- wf_ty _ _ _ _ _ =>
      first [ solve [eapply wft_nat; sub_premises] | solve [eapply wft_pi; sub_premises]
            | solve [eapply wft_U; sub_premises] | solve [eapply wft_El; sub_premises]
            | solve [eapply wft_lconv; sub_premises] ]
  | |- wf_tm _ _ _ _ _ _ =>
      first [ solve [eapply wf_code_nat; sub_premises]
            | solve [eapply wf_code_U; sub_premises] | solve [eapply wf_code_pi; sub_premises]
            | solve [eapply wf_zero; sub_premises] | solve [eapply wf_succ; sub_premises]
            | solve [eapply wf_natrec; sub_premises] | solve [eapply wf_lam; sub_premises]
            | solve [eapply wf_app; sub_premises] | solve [eapply wf_conv; sub_premises]
            | solve [eapply wf_lconv; sub_premises] ]
  | |- eq_ty _ _ _ _ _ _ =>
      first [ solve [eapply eqty_refl; sub_premises] | solve [eapply eqty_sym; sub_premises]
            | solve [eapply eqty_trans; sub_premises] | solve [eapply eqty_pi; sub_premises]
            | solve [eapply eqty_U; sub_premises] | solve [eapply eqty_El; sub_premises]
            | solve [eapply eqty_El_nat; sub_premises] | solve [eapply eqty_El_U; sub_premises]
            | solve [eapply eqty_El_pi; sub_premises] | solve [eapply eqty_lconv; sub_premises] ]
  | |- eq_tm _ _ _ _ _ _ _ =>
      first [ solve [eapply eqtm_refl; sub_premises] | solve [eapply eqtm_sym; sub_premises]
            | solve [eapply eqtm_trans; sub_premises] | solve [eapply eqtm_code_U; sub_premises]
            | solve [eapply eqtm_code_pi; sub_premises] | solve [eapply eqtm_succ; sub_premises]
            | solve [eapply eqtm_natrec; sub_premises] | solve [eapply eqtm_lam; sub_premises]
            | solve [eapply eqtm_app; sub_premises] | solve [eapply eqtm_conv; sub_premises]
            | solve [eapply eqtm_lconv; sub_premises]
            | solve [eapply eqtm_natrec_zero; sub_premises]
            | solve [eapply eqtm_natrec_succ; sub_premises]
            | solve [eapply eqtm_beta; sub_premises] | solve [eapply eqtm_eta; sub_premises] ]
  end.

Ltac sub_premise :=
  fix_layer;
  first [ solve [eauto 8 with sub]
        | solve [eapply wf_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with sub] end
                 | sub_rw; reflexivity]]
        | solve [eapply eq_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with sub] end
                 | sub_rw; reflexivity]] ].

Ltac sub_manual :=
  match goal with
  | |- wf_tm _ _ _ (tmPi _ _ _ _) _ _ => eapply wf_code_pi
  | |- wf_tm _ _ _ (natrec _ _ _ _ _) _ _ => eapply wf_natrec
  | |- eq_ty _ _ _ (tyPi _ _ _ _) (tyEl _ _) _ => eapply eqty_El_pi
  | |- eq_tm _ _ _ (tmPi _ _ _ _) _ _ _ => eapply eqtm_code_pi
  | |- eq_tm _ _ _ (natrec _ _ _ _ _) (natrec _ _ _ _ _) _ _ => eapply eqtm_natrec
  | |- eq_tm _ _ _ (natrec _ _ _ _ zero) _ _ _ => eapply eqtm_natrec_zero
  | |- eq_tm _ _ _ (natrec _ _ _ _ (succ _)) _ _ _ => eapply eqtm_natrec_succ
  | |- eq_tm _ _ _ (lam _ _ _ _) _ _ _ => eapply eqtm_eta
  end; sub_premise.

Theorem substitution :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> typeof i = i ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] T[d] @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> typeof i = i ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] t[d] : T[d] @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> typeof i = i ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T'[d] @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> typeof i = i ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] t[d] ≅ t'[d] : T[d] @ l ]).
Proof.
  apply typing_mut; intros; try exact I;
    match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end;
    try match goal with c : compt ?i |- _ => pose proof (compt_notV _ c) end;
    sub_rw.
  all: try solve [eapply lsub_wf_var; eassumption].
  all: try sub_step.
  all: sub_manual.
Qed.
