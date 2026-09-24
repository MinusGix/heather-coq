(** * Typed local substitutions and the substitution lemma (ch. 5)

    A local substitution is typed by its lookups: [Δ ⊢ d : Γ] when every
    variable of [Γ] is sent to a term of the substituted type.  Entries are
    in normal form ([nftm]), which every typed term is (see [typed_nf]);
    the identity laws inside the commutation lemmas need it.

    As for weakening, the lemma is proved for layers with [typeof i = i]. *)
From DeLaM.Syntax Require Export SubstCommute.
From DeLaM.Typing Require Export Properties.

(** ** Typed terms are in (deep) normal form *)

Lemma lk_lsingle a : nftm a -> LK nftm (lsingle a).
Proof. intros H [|n]; cbn; auto. Qed.
Lemma lk_lsingle2 t q : nftm t -> nftm q -> LK nftm (lsingle2 t q).
Proof. intros H1 H2 [|[|n]]; cbn; auto. Qed.
Lemma lk_lsucc : LK nftm lsucc.
Proof. intros [|n]; cbn; auto. Qed.
#[export] Hint Resolve lk_lsingle lk_lsingle2 lk_lsucc : nf.

Lemma lk_dnf_lsingle a : dnftm a -> LK dnftm (lsingle a).
Proof. intros H [|n]; cbn; auto. Qed.
Lemma lk_dnf_lsingle2 t q : dnftm t -> dnftm q -> LK dnftm (lsingle2 t q).
Proof. intros H1 H2 [|[|n]]; cbn; auto. Qed.
Lemma lk_dnf_lsucc : LK dnftm lsucc.
Proof. intros [|n]; cbn; auto. Qed.
Lemma lk_dnf_lshift k : LK dnftm (lshift k).
Proof. intros n; exact I. Qed.
#[export] Hint Resolve lk_dnf_lsingle lk_dnf_lsingle2 lk_dnf_lsucc lk_dnf_lshift : nf.

Lemma in_ctx_dnf Γ n T l : dnfctx Γ -> in_ctx Γ n T l -> dnfty T.
Proof. intros H Hin; induction Hin; cbn in *; apply ren_dnf_ty; tauto. Qed.

Definition dnf_decl (D : gdecl) : Prop :=
  match D with gdCtx => True | gdTy Δ _ _ => dnfctx Δ | gdTm Δ _ T _ => dnfctx Δ /\ dnfty T end.
Lemma in_gctx_dnf Ψ n D : in_gctx Ψ n D -> dnf_decl D.
Proof. destruct 1 as [? D0|? D0 ? ? _]; destruct D0; cbn; repeat split; apply gren_dnf_all. Qed.

Lemma dnfo_gsingle o : dnfo o -> forall i, dnfo (gsingle o i).
Proof. intros H [|i]; cbn; auto. Qed.

Theorem typed_dnf :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> dnfctx Γ) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> dnfty T) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> dnftm t /\ dnfty T) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> dnfty T /\ dnfty T') /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> dnftm t /\ dnftm t' /\ dnfty T) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> dnfctx Γ /\ dnfctx Γ').
Proof.
  apply typing_mut; intros; cbn in *;
    try match goal with H : in_gctx _ _ _ |- _ => pose proof (in_gctx_dnf _ _ _ H); cbn in * end;
    intuition eauto using subst_dnf_ty, subst_dnf, ren_dnf_ty, ren_dnf, in_ctx_dnf with nf.
  all: try solve [apply subst_dnf; [assumption | apply lk_dnf_lsingle2; cbn; tauto]].
  all: try solve [apply subst_dnf_ty; auto; intros n; apply dnfl_llk; auto].
  all: try solve [apply gsubst_dnf_all; auto; apply dnfo_gsingle; cbn; auto].
Qed.

Theorem typed_nf :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> nfty T) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> nftm t /\ nfty T) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> nfty T /\ nfty T') /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> nftm t /\ nftm t' /\ nfty T).
Proof.
  destruct typed_dnf as (_ & _ & H1 & H2 & H3 & H4 & _).
  refine (conj (fun _ _ => I) (conj (fun _ _ _ _ => I) (conj _ (conj _ (conj _ _))))); intros.
  - apply dnfty_nfty; eauto.
  - destruct (H2 _ _ _ _ _ _ H); split; auto using dnftm_nftm, dnfty_nfty.
  - destruct (H3 _ _ _ _ _ _ H); split; auto using dnfty_nfty.
  - destruct (H4 _ _ _ _ _ _ _ H) as (? & ? & ?); repeat split; auto using dnftm_nftm, dnfty_nfty.
Qed.

Lemma wf_ty_nf {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> nfty T.
Proof. apply typed_nf. Qed.
Lemma wf_tm_nf {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> nftm t.
Proof. apply typed_nf. Qed.
Lemma wf_tm_nf_ty {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> nfty T.
Proof. apply typed_nf. Qed.
Lemma wf_ty_dnf {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> dnfty T.
Proof. apply typed_dnf. Qed.
Lemma wf_tm_dnf {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> dnftm t.
Proof. apply typed_dnf. Qed.
Lemma wf_tm_dnf_ty {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> dnfty T.
Proof. apply typed_dnf. Qed.
Lemma wf_ctx_dnf {G i Γ} : [ G ; Γ ⊢[ i ] ] -> dnfctx Γ.
Proof. apply typed_dnf. Qed.

(** ** Typed local substitutions

    [Δ ⊢ᵢ d : Γ]: [Δ] is a context (at [typeof i], as for every judgment at
    [i]), the entries are deep-normal, [d] satisfies the tail condition of
    the paper (04:990), and every variable of [Γ] is sent to a term of the
    substituted type at layer [i]. *)

Record lsub_wf G i Δ d Γ : Prop := {
  lsw_ctx : [ G ; Δ ⊢[ typeof i ] ] ;
  lsw_dnf : LK dnftm d ;
  lsw_tail : lsub_tail d Γ Δ ;
  lsw_var : forall n T l, in_ctx Γ n T l -> [ G ; Δ ⊢[ i ] llk d n : T[d] @ l ]
}.

Notation "[ G ; Δ ⊢[ i ] d : Γ ]" := (lsub_wf G i Δ d Γ)
  (at level 0, G, Δ, i, d, Γ at level 50).

Lemma lsub_wf_ctx {G i Δ d Γ} : [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ typeof i ] ].
Proof. now intros []. Qed.
Lemma lsub_wf_dnf {G i Δ d Γ} : [ G ; Δ ⊢[ i ] d : Γ ] -> LK dnftm d.
Proof. now intros []. Qed.
Lemma lsub_wf_nf {G i Δ d Γ} : [ G ; Δ ⊢[ i ] d : Γ ] -> LK nftm d.
Proof. intros [] n; apply dnftm_nftm; auto. Qed.
Lemma lsub_wf_tail {G i Δ d Γ} : [ G ; Δ ⊢[ i ] d : Γ ] -> lsub_tail d Γ Δ.
Proof. now intros []. Qed.
Lemma lsub_wf_var {G i Δ d Γ n T l} :
  [ G ; Δ ⊢[ i ] d : Γ ] -> in_ctx Γ n T l -> [ G ; Δ ⊢[ i ] llk d n : T[d] @ l ].
Proof. intros []; auto. Qed.

#[export] Hint Resolve lsub_wf_ctx lsub_wf_nf lsub_wf_dnf : nf.

(** ** Tails *)

Lemma tail_llift d Γ Δ A B l l' : lsub_tail d Γ Δ -> lsub_tail (llift d) (Γ ,, A @ l) (Δ ,, B @ l').
Proof.
  intros [Ht Hl]; split; [exact Ht|]. intros n; cbn [clen].
  replace (S (clen Γ) + n) with (S (clen Γ + n)) by lia.
  rewrite llk_llift, Hl; cbn; f_equal; lia.
Qed.
Lemma tail_id Γ : lsub_tail (lshift 0) Γ Γ.
Proof. split; auto. intros n; cbn; f_equal; lia. Qed.
Lemma tail_single a Γ A l : lsub_tail (lsingle a) (Γ ,, A @ l) Γ.
Proof. split; auto. intros n; cbn; f_equal; lia. Qed.
Lemma tail_lcomp e d Θ Γ Δ : lsub_tail e Θ Γ -> lsub_tail d Γ Δ -> lsub_tail (lcomp e d) Θ Δ.
Proof.
  intros [H1 H2] [H3 H4]; split; [congruence|].
  intros n; rewrite llk_lcomp, H2; cbn; apply H4.
Qed.
#[export] Hint Resolve tail_llift tail_id tail_single tail_lcomp : nf.

Section Lsub.
Context (G : gctx) (i : layer).

Lemma wkr_shift1 Γ A l : wkr ↑ (Γ ,, A @ l) Γ.
Proof. exact (wkr_step _ _ _ _ _ (wkr_id Γ)). Qed.

Lemma wk1_ty_g Γ A l T l' :
  [ G ; Γ ,, A @ l ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] T @ l' ] -> [ G ; Γ ,, A @ l ⊢[ i ] T⟨↑⟩ @ l' ].
Proof. intros; eapply weakening_all; eauto using wkr_shift1. Qed.
Lemma wk1_tm_g Γ A l t T l' :
  [ G ; Γ ,, A @ l ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] t : T @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t⟨↑⟩ : T⟨↑⟩ @ l' ].
Proof. intros; eapply weakening_all; eauto using wkr_shift1. Qed.
Lemma wk1_eqty_g Γ A l T T' l' :
  [ G ; Γ ,, A @ l ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] T⟨↑⟩ ≅ T'⟨↑⟩ @ l' ].
Proof. intros; eapply weakening_all; eauto using wkr_shift1. Qed.
Lemma wk1_eqtm_g Γ A l t t' T l' :
  [ G ; Γ ,, A @ l ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t⟨↑⟩ ≅ t'⟨↑⟩ : T⟨↑⟩ @ l' ].
Proof. intros; eapply weakening_all; eauto using wkr_shift1. Qed.

Lemma var0_wf_g Γ A l :
  [ G ; Γ ,, A @ l ⊢[ typeof i ] ] -> [ G ; Γ ,, A @ l ⊢[ i ] var 0 : A⟨↑⟩ @ l ].
Proof. intros; apply wf_var; [assumption | constructor]. Qed.

Lemma lsub_wf_lift_g Δ d Γ A l :
  [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ typeof i ] A[d] @ l ] -> lwf (gL G) l ->
  [ G ; Δ ,, A[d] @ l ⊢[ i ] llift d : Γ ,, A @ l ].
Proof.
  intros Hd HA Hl.
  assert (HΔ : [ G ; Δ ,, A[d] @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact (lsub_wf_ctx Hd) | exact HA | exact Hl]).
  constructor; [exact HΔ | apply lk_dnf_llift; eauto with nf | apply tail_llift, (lsub_wf_tail Hd) |].
  intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst.
  - rewrite llk_llift, shift_llift_ty. now apply var0_wf_g.
  - rewrite llk_llift, shift_llift_ty. apply wk1_tm_g; auto. exact (lsub_wf_var Hd Hm).
Qed.

Lemma lsub_wf_lift_g' Δ d Γ A A' l :
  [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ typeof i ] A' @ l ] -> lwf (gL G) l -> A' = A[d] ->
  [ G ; Δ ,, A' @ l ⊢[ i ] llift d : Γ ,, A @ l ].
Proof. intros ???->; now apply lsub_wf_lift_g. Qed.

Lemma lsub_wf_id_g Γ : [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] lshift 0 : Γ ].
Proof.
  intros HΓ; constructor; [exact HΓ | apply lk_dnf_lshift | apply tail_id |].
  intros n T l Hin. rewrite (subst_id_ty T) by (eauto using in_ctx_nf; intros; cbn; f_equal; lia).
  cbn; rewrite Nat.add_0_r. apply wf_var; [assumption | exact Hin].
Qed.

Lemma lsub_wf_single_g Γ A a l :
  [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] lsingle a : Γ ,, A @ l ].
Proof.
  intros HΓ Ha. constructor; [exact HΓ | apply lk_dnf_lsingle, (wf_tm_dnf Ha) | apply tail_single |].
  intros n T l' Hin; inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 T0 l1 m Hm]; subst; cbn.
  - rewrite shift_single_ty by exact (wf_tm_nf_ty Ha). exact Ha.
  - rewrite shift_single_ty by eauto using in_ctx_nf. rewrite Nat.add_0_r.
    apply wf_var; [assumption | exact Hm].
Qed.

(** A substitution typed at [i] is typed at every layer above. *)
Lemma lsub_wf_lle j Δ d Γ : lle i j -> [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ j ] d : Γ ].
Proof.
  intros Hij [HΔ Hn Ht Hv]; constructor; auto.
  - exact (lift_ctx HΔ (lle_typeof _ _ Hij)).
  - intros; eapply lift_tm; eauto.
Qed.

End Lsub.

(** The M1 forms, at layers with [typeof i = i]. *)
Section LsubM1.
Context (G : gctx) (i : layer) (Hi : typeof i = i) (Hv : i <> lV).

Lemma wk1_ty Γ A l T l' :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] T @ l' ] -> [ G ; Γ ,, A @ l ⊢[ i ] T⟨↑⟩ @ l' ].
Proof. intros; apply wk1_ty_g; rewrite ?Hi; auto. Qed.
Lemma wk1_tm Γ A l t T l' :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] t : T @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t⟨↑⟩ : T⟨↑⟩ @ l' ].
Proof. intros; apply wk1_tm_g; rewrite ?Hi; auto. Qed.
Lemma wk1_eqty Γ A l T T' l' :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] T⟨↑⟩ ≅ T'⟨↑⟩ @ l' ].
Proof. intros; apply wk1_eqty_g; rewrite ?Hi; auto. Qed.
Lemma wk1_eqtm Γ A l t t' T l' :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t⟨↑⟩ ≅ t'⟨↑⟩ : T⟨↑⟩ @ l' ].
Proof. intros; apply wk1_eqtm_g; rewrite ?Hi; auto. Qed.
Lemma var0_wf Γ A l :
  [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ,, A @ l ⊢[ i ] var 0 : A⟨↑⟩ @ l ].
Proof. intros; apply var0_wf_g; rewrite ?Hi; auto. Qed.
Lemma lsub_wf_lift Δ d Γ A l :
  [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] A[d] @ l ] -> lwf (gL G) l ->
  [ G ; Δ ,, A[d] @ l ⊢[ i ] llift d : Γ ,, A @ l ].
Proof. intros; apply lsub_wf_lift_g; auto; rewrite ?Hi; auto. Qed.
Lemma lsub_wf_lift' Δ d Γ A A' l :
  [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] A' @ l ] -> lwf (gL G) l -> A' = A[d] ->
  [ G ; Δ ,, A' @ l ⊢[ i ] llift d : Γ ,, A @ l ].
Proof. intros ???->; now apply lsub_wf_lift. Qed.
Lemma lsub_wf_id Γ : [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] lshift 0 : Γ ].
Proof. intros; apply lsub_wf_id_g; rewrite ?Hi; auto. Qed.
Lemma lsub_wf_single Γ A a l :
  [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] lsingle a : Γ ,, A @ l ].
Proof. intros; apply lsub_wf_single_g; auto; rewrite ?Hi; auto. Qed.
End LsubM1.

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

(** Syntax for the new cases. *)

Lemma llift_gren_llk d ξ n : llk (llift d⟪ξ⟫) n = llk ((llift d)⟪ξ⟫) n.
Proof.
  cbn [gren GRen_lsub]. rewrite llk_glren, !llk_llift; destruct n; auto.
  rewrite llk_glren. change (gren_tm (ren_tm ?x ?r) ?ξ) with x⟨r⟩⟪ξ⟫. now rewrite gren_ren.
Qed.

Lemma gren_llift_subst_ty (M : ty) d ξ : M⟪ξ⟫[llift d⟪ξ⟫] = (M[llift d])⟪ξ⟫.
Proof. rewrite gren_subst_ty. apply subst_ext_ty, llift_gren_llk. Qed.

Lemma body_subst_ty (M : ty) b d : LK nftm d -> b[gwk d] = b ->
  (M⟪S⟫[lsingle b])[gwk d] = (M[llift d])⟪S⟫[lsingle b].
Proof.
  intros Hd Hb. rewrite single_subst_ty, Hb.
  - f_equal. apply gren_llift_subst_ty.
  - intros n; unfold gwk; rewrite llk_glren; apply gren_nf_all, Hd.
Qed.

Lemma gwk_gsingle d o : LK dnftm d -> forall n, llk ((gwk d)⦃gsingle o⦄) n = llk d n.
Proof.
  intros Hd n; cbn [gsubst GSubst_lsub]. rewrite llk_glsubst; unfold gwk; rewrite llk_glren.
  rewrite (proj1 (proj2 gsubst_gren_all) _ _ _ (fun j => GId j)) by reflexivity.
  apply gsubst_id; auto.
Qed.

Lemma gsingle_subst (t : tm) d o : LK dnftm d -> (t⦃gsingle o⦄)[d] = (t[gwk d])⦃gsingle o⦄.
Proof.
  intros Hd. rewrite gsubst_subst. symmetry; apply subst_ext. intros n; apply gwk_gsingle, Hd.
Qed.

(** A typed substitution under one global binder. *)
Lemma lsub_wf_gwk G D i Δ d Γ : [ ⊢ gext G D ] -> [ G ; Δ ⊢[ i ] d : Γ ] ->
  [ gext G D ; Δ⟪S⟫ ⊢[ i ] gwk d : Γ⟪S⟫ ].
Proof.
  intros Hg [HΔ Hn Ht Hv].
  assert (Hw : gwk_wf (gwk_step gwk_id) (D :: gΨ G) (gΨ G)) by (constructor; constructor).
  constructor.
  - exact (proj1 (proj2 gweakening) _ _ _ HΔ _ _ Hw Hg).
  - now apply lk_dnf_gwk.
  - exact (lsub_tail_gren _ _ _ S Ht).
  - intros n A k Hin. destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & HA0 & ->).
    unfold gwk; rewrite llk_glren. change (gren_tm ?x ?y) with x⟪y⟫.
    change (glren d S) with d⟪S⟫. rewrite <- gren_subst_ty.
    exact (proj1 (proj2 (proj2 (proj2 gweakening))) _ _ _ _ _ _ (Hv _ _ _ HA0) _ _ Hw Hg).
Qed.

Lemma lsub_wf_typeof G i Δ d Γ : [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ typeof i ] d : Γ ].
Proof. apply lsub_wf_lle, lle_self_typeof. Qed.

#[export] Hint Resolve lsub_wf_typeof : sub.
#[export] Hint Extern 2 (lsub_wf _ _ _ (llift _) _) =>
  eapply lsub_wf_lift_g'; [ .. | sub_rw; reflexivity ] : sub.
#[export] Hint Extern 3 (wf_ty _ (typeof _) _ _ _) => eapply lift_ty; [ | apply lle_self_typeof ] : sub.
#[export] Hint Extern 3 (wf_tm _ (typeof _) _ _ _ _) => eapply lift_tm; [ | apply lle_self_typeof ] : sub.
#[export] Hint Extern 1 (wf_ctx _ (typeof (typeof _)) _) => rewrite typeof_idem : sub.
#[export] Hint Extern 1 (lsub_wf _ (typeof (typeof _)) _ _ _) => rewrite typeof_idem : sub.
#[export] Hint Resolve wft_CTyp wft_CTrm : sub.
#[export] Hint Extern 1 (wf_ctx _ _ _) =>
  match goal with H : lsub_wf _ _ _ _ _ |- _ => exact (lsub_wf_ctx H) end : sub.

(** The lookup-typed substitution of [u^δ]/[U^δ], composed with [d]. *)
Ltac sub_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin; rewrite !llk_lcomp;
  match goal with
  | Hd : lsub_wf _ _ _ ?d _ |- context [lcomp ?e ?d] =>
      rewrite <- (subst_subst_ty A e d (lcomp e d) (fun m => llk_lcomp e d m))
  end;
  match goal with IH : forall n A k (_ : in_ctx _ n A k), _ |- _ => eapply (IH n A k Hin) end;
  eauto with sub.

Ltac sub_gvar_side :=
  first [ solve [eassumption] | solve [eauto with sub]
        | solve [eapply tail_lcomp; [eassumption | eapply lsub_wf_tail; eassumption]]
        | solve [eapply dnfl_lcomp; [eassumption | eapply lsub_wf_dnf; eassumption]] ].

(** The letbox body, under [Ψ, U] with [gwk d]. *)
Ltac sub_body :=
  match goal with
  | IH : forall Δ' d', lsub_wf (gext ?G ?D) _ Δ' d' (?Γ⟪S⟫) -> _,
    Hd : lsub_wf ?G _ ?Δ ?d ?Γ |- _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext G D ])
        by (unfold gext; first [eapply wfg_ty | eapply wfg_tm];
            first [exact (ctx_glob _ _ _ (lsub_wf_ctx Hd)) | eassumption | left; reflexivity
                  | right; reflexivity | cbn; eassumption | eapply lequiv_wf_l; eassumption]);
      pose proof (IH _ _ (lsub_wf_gwk _ _ _ _ _ _ Hg Hd)) as X;
      rewrite body_subst_ty in X by (eauto with nf; reflexivity); exact X
  end.

Ltac sub_manual2 :=
  match goal with
  | |- wf_ty _ _ _ (tyGvar _ _) _ =>
      eapply wft_gvar; [ .. | sub_entries]; sub_gvar_side
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      eapply eqty_gvar; [ .. | sub_entries | sub_entries | sub_entries]; sub_gvar_side
  | |- wf_tm _ _ _ (gvar _ _) _ _ =>
      match goal with Hd : lsub_wf _ _ _ ?d _ |- context [(?T[?e])[?d]] =>
        rewrite (subst_subst_ty T e d (lcomp e d) (fun m => llk_lcomp e d m)) end;
      eapply wf_gvar; [ .. | sub_entries]; sub_gvar_side
  | |- eq_tm _ _ _ (gvar _ _) _ _ _ =>
      match goal with Hd : lsub_wf _ _ _ ?d _ |- context [(?T[?e])[?d]] =>
        rewrite (subst_subst_ty T e d (lcomp e d) (fun m => llk_lcomp e d m)) end;
      eapply eqtm_gvar; [ .. | sub_entries | sub_entries | sub_entries]; sub_gvar_side
  | |- wf_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ => eapply wf_letboxT; [ .. | sub_body | ]; sub_premise
  | |- wf_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ => eapply wf_letboxt; [ .. | sub_body | ]; sub_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ (boxT _)) _ _ _ =>
      rewrite gsingle_subst by eauto with nf; eapply eqtm_letboxT_beta; [ .. | sub_body]; sub_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      rewrite gsingle_subst by eauto with nf; eapply eqtm_letboxt_beta; [ .. | sub_body]; sub_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxT; [ .. | sub_body | ]; sub_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxt; [ .. | sub_body | ]; sub_premise
  | |- wf_tm _ _ _ (boxT _) _ _ => eapply wf_boxT; sub_premise
  | |- wf_tm _ _ _ (boxt _) _ _ => eapply wf_boxt; sub_premise
  | |- eq_tm _ _ _ (boxT _) _ _ _ => eapply eqtm_boxT; sub_premise
  | |- eq_tm _ _ _ (boxt _) _ _ _ => eapply eqtm_boxt; sub_premise
  | |- wf_ty _ _ _ (tyCTyp _ _) _ => eapply wft_CTyp; sub_premise
  | |- wf_ty _ _ _ (tyCTrm _ _ _) _ => eapply wft_CTrm; sub_premise
  | |- eq_ty _ _ _ (tyCTyp _ _) _ _ => eapply eqty_CTyp; sub_premise
  | |- eq_ty _ _ _ (tyCTrm _ _ _) _ _ => eapply eqty_CTrm; sub_premise
  end.

Theorem substitution_all :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] T[d] @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] t[d] : T[d] @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T'[d] @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] t[d] ≅ t'[d] : T[d] @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    try match goal with c : compt ?i |- _ => pose proof (compt_notV _ c) end;
    cbn [typeof] in *; sub_rw.
  all: try solve [eapply lsub_wf_var; eassumption].
  all: try sub_step.
  all: try sub_manual.
  all: sub_manual2.
Qed.

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
  destruct substitution_all as (_ & _ & H1 & H2 & H3 & H4 & _).
  repeat split; intros; eauto.
Qed.
