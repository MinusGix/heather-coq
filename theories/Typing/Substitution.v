(** * Typed local substitutions and the substitution lemma (ch. 5)

    A local substitution is typed by its lookups: [Δ ⊢ d : Γ] when every
    variable of [Γ] is sent to a term of the substituted type.  Entries are
    in normal form ([nftm]), which every typed term is (see [typed_nf]);
    the identity laws inside the commutation lemmas need it.

    As for weakening, the lemma is proved for layers with [typeof i = i]. *)
From DeLaM.Syntax Require Export SubstCommute.
From DeLaM.Typing Require Export Properties TypedDnf.

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
  rewrite ?llk_llift0, ?single_subst_ty, ?single_subst, ?single2_subst, ?single2_subst_ty, ?lsucc_subst_ty,
          ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty by eauto with nf;
  push_subst.

#[export] Hint Resolve lsub_wf_ctx : sub.
#[export] Hint Resolve wfc_ext wft_nat wft_El lequiv_wf_l lequiv_wf_r wf_ctx_nat compt_notV : sub.
#[export] Hint Resolve wf_ctx_empty wft_empty_typeof : sub.
#[export] Hint Extern 1 (ty_leq _ _) =>
  apply (proj1 leq_subst_all); [apply lsub_leq_refl | assumption] : sub.
#[export] Hint Extern 1 (tm_leq _ _) =>
  apply (proj1 (proj2 leq_subst_all)); [apply lsub_leq_refl | assumption] : sub.
#[export] Hint Extern 2 (lsub_wf _ _ _ (llift _) _) =>
  eapply lsub_wf_lift'; [ .. | first [reflexivity | sub_rw; reflexivity] ] : sub.
#[export] Hint Extern 20 (wf_tm _ _ _ _ _ _) => eapply wf_tm_retype : sub.
#[export] Hint Extern 20 (eq_tm _ _ _ _ _ _ _) => eapply eq_tm_retype : sub.
#[export] Hint Extern 1 (lwf _ _) =>
  (cbn; first [exact I | assumption | split; assumption]) : sub.
#[export] Hint Extern 1 =>
  match goal with Hi : typeof ?i = ?i |- context [typeof ?i] => rewrite Hi end : sub.
#[export] Hint Extern 1 (@eq ty _ _) => (sub_rw; reflexivity) : sub.

Ltac sub_premises := fix_layer; eauto 6 with sub.

Ltac sub_step := any_rule sub_premises.

(** The recursors' specification laws (defined below). *)
Ltac sub_rec_rw := fail.

Ltac sub_premise :=
  fix_layer;
  first [ solve [eauto 8 with sub]
        | solve [eapply wf_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with sub] end
                 | sub_rw; reflexivity]]
        | solve [eapply eq_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with sub] end
                 | sub_rw; reflexivity]]
        (* the recursors' motive instances (M3_DESIGN.md E10) *)
        | solve [eapply wf_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with sub] end
                 | sub_rec_rw; reflexivity]]
        | solve [eapply eq_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with sub] end
                 | sub_rec_rw; reflexivity | sub_rec_rw; reflexivity]] ].

(** The rules whose premises need the induction hypotheses at a rewritten
    type ([sub_premise]). *)
Ltac sub_manual := any_rule sub_premise.

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

(** The meta-functions (M5): instances and η under local substitution. *)
Lemma gsingle_subst_ty (T : ty) d o : LK dnftm d -> (T⦃gsingle o⦄)[d] = (T[gwk d])⦃gsingle o⦄.
Proof.
  intros Hd. rewrite gsubst_subst_ty. symmetry; apply subst_ext_ty. intros n; apply gwk_gsingle, Hd.
Qed.
Lemma shift_gwk_subst (t : tm) d : t⟪S⟫[gwk d] = t[d]⟪S⟫.
Proof. symmetry; apply gren_subst. Qed.

(** A typed substitution under one global binder. *)
Lemma lsub_wf_gwk G D i Δ d Γ : [ ⊢ gext G D ] -> [ G ; Δ ⊢[ i ] d : Γ ] ->
  [ gext G D ; Δ⟪S⟫ ⊢[ i ] gwk d : Γ⟪S⟫ ].
Proof.
  intros Hg [HΔ Hn Ht Hv].
  assert (Hw : gwk_wf (gwk_step gwk_id) (D :: gΨ G) (gΨ G)) by (constructor; constructor).
  constructor.
  - exact (proj1 (proj2 gweakening) _ _ _ HΔ _ _ _ (le_n _) Hw Hg).
  - now apply lk_dnf_gwk.
  - exact (lsub_tail_gren _ _ _ S Ht).
  - intros n A k Hin. destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & HA0 & ->).
    unfold gwk; rewrite llk_glren. change (gren_tm ?x ?y) with x⟪y⟫.
    change (glren d S) with d⟪S⟫. rewrite <- gren_subst_ty.
    exact (proj1 (proj2 (proj2 (proj2 gweakening))) _ _ _ _ _ _ (Hv _ _ _ HA0) _ _ _ (le_n _) Hw Hg).
Qed.

Lemma lsub_wf_typeof G i Δ d Γ : [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ typeof i ] d : Γ ].
Proof. apply lsub_wf_lle, lle_self_typeof. Qed.

#[export] Hint Resolve lsub_wf_typeof : sub.
#[export] Hint Extern 2 (lsub_wf _ _ _ (llift _) _) =>
  eapply lsub_wf_lift_g'; [ .. | first [reflexivity | sub_rw; reflexivity] ] : sub.
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
                  | right; reflexivity | cbn; eassumption | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption]);
      pose proof (IH _ _ (lsub_wf_gwk _ _ _ _ _ _ Hg Hd)) as X;
      rewrite body_subst_ty in X by (eauto with nf; reflexivity); exact X
  end.


(** The meta-functions' bodies (M5): no instance in the body's type. *)
Ltac sub_gbody :=
  match goal with
  | IH : forall Δ' d', lsub_wf (gext ?G ?D) _ Δ' d' (?Γ⟪S⟫) -> _,
    Hd : lsub_wf ?G _ ?Δ ?d ?Γ |- _ =>
      let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext G D ])
        by (unfold gext; first [eapply wfg_ctx | eapply wfg_ty | eapply wfg_tm];
            first [exact (ctx_glob _ _ _ (lsub_wf_ctx Hd)) | eassumption | left; reflexivity
                  | right; reflexivity | cbn; eassumption | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption]);
      exact (IH _ _ (lsub_wf_gwk _ _ _ _ _ _ Hg Hd))
  end.
Ltac sub_mf_rw :=
  match goal with Hd : lsub_wf _ _ _ ?d _ |- _ =>
    rewrite ?(gsingle_subst_ty _ d _ (lsub_wf_dnf Hd)), ?(gsingle_subst _ d _ (lsub_wf_dnf Hd)),
      ?shift_gwk_subst
  end.

(** ** The recursors' specification under local substitution *)

Definition gwkn (n : nat) (d : lsub) : lsub := Nat.iter n gwk d.
Definition lliftn (n : nat) (d : lsub) : lsub := Nat.iter n llift d.
(** A local substitution moved into branch [k]'s scope, before its locals. *)
Definition bsub (k : nat) (d : lsub) : lsub := gwkn (br_ng k) (uwkn (br_nu k) d).

Lemma wrapU_subst n b d : (wrapU n b)[d] = wrapU n b[uwkn n d].
Proof.
  revert d; induction n; intros d; cbn [wrapU subst Subst_tm subst_tm]; auto.
  change (subst_tm (wrapU n b) (uwk d)) with (wrapU n b)[uwk d]. rewrite IHn. do 3 f_equal.
  unfold uwkn; now rewrite <- Nat.iter_succ_r.
Qed.
Lemma wrapG_subst n b d : (wrapG n b)[d] = wrapG n b[gwkn n d].
Proof.
  revert d; induction n; intros d; cbn [wrapG subst Subst_tm subst_tm]; auto.
  change (subst_tm (wrapG n b) (gwk d)) with (wrapG n b)[gwk d]. rewrite IHn. do 3 f_equal.
  unfold gwkn; now rewrite <- Nat.iter_succ_r.
Qed.
Lemma wrapL_subst n b d : (wrapL n b)[d] = wrapL n b[lliftn n d].
Proof.
  revert d; induction n; intros d; cbn [wrapL subst Subst_tm subst_tm]; auto.
  change (subst_tm (wrapL n b) (llift d)) with (wrapL n b)[llift d]. rewrite IHn. do 3 f_equal.
  unfold lliftn; now rewrite <- Nat.iter_succ_r.
Qed.
Lemma wrap_subst nu ng nl b d :
  (wrap nu ng nl b)[d] = wrap nu ng nl b[lliftn nl (gwkn ng (uwkn nu d))].
Proof. unfold wrap. now rewrite wrapU_subst, wrapG_subst, wrapL_subst. Qed.

Lemma mkrb_subst MT Mt bs d :
  (mkrb MT Mt bs)[d] = mkrb MT[llift (gwk (uwk d))] Mt[llift (gwk (gwk (uwk d)))]
                            (fun k => (bs k)[lliftn (br_nl k) (bsub k d)]).
Proof. unfold mkrb. cbn [tup_from subst Subst_tm subst_tm br_ar]. rewrite !wrap_subst. reflexivity. Qed.
Lemma wrapMT_subst MT d : (wrapMT MT)[d] = wrapMT MT[llift (gwk (uwk d))].
Proof. reflexivity. Qed.
Lemma wrapMt_subst Mt d : (wrapMt Mt)[d] = wrapMt Mt[llift (gwk (gwk (uwk d)))].
Proof. reflexivity. Qed.

Lemma uwk_usingle d l : LK dnftm d -> forall n, llk (ulsubst (uwk d) (usingle l)) n = llk d n.
Proof.
  intros Hd n. unfold uwk. rewrite llk_ulsubst, llk_ulren.
  rewrite (proj1 (proj2 uren_usubst_all) _ _ _ lvar) by reflexivity.
  apply (proj1 (proj2 usubst_id_all)); auto.
Qed.

(** Peeling commutes with a substitution on terms not headed by a
    variable (a substitution may turn a variable into a binder node). The
    bundles built by [mkrb]/[wrapMT]/[wrapMt] satisfy this by computation. *)
Definition hd_ok (t : tm) : Prop := match t with var _ | gvar _ _ | gdef _ _ _ => False | _ => True end.

Lemma peelU_subst b l d : hd_ok b -> LK dnftm d -> peelU b[d] l = (peelU b l)[d].
Proof.
  intros Hb Hd. destruct b; cbn [peelU subst Subst_tm subst_tm]; try contradiction; auto.
  rewrite (proj1 (proj2 usubst_subst_all) _ _ (ulsubst (uwk d) (usingle l)))
    by (intros; apply llk_ulsubst).
  apply subst_ext, uwk_usingle, Hd.
Qed.
Lemma peelG_subst b o d : hd_ok b -> LK dnftm d -> peelG b[d] o = (peelG b o)[d].
Proof.
  intros Hb Hd. destruct b; cbn [peelG subst Subst_tm subst_tm]; try contradiction; auto.
  symmetry; apply gsingle_subst, Hd.
Qed.
Lemma peelL_subst b a d : hd_ok b -> LK nftm d -> peelL b[d] a[d] = (peelL b a)[d].
Proof.
  intros Hb Hd. destruct b; cbn [peelL subst Subst_tm subst_tm]; try contradiction; auto.
  symmetry; now apply single_subst.
Qed.
Lemma getTy_subst t d : hd_ok t -> (getTy t)[d] = getTy t[d].
Proof. destruct t; cbn; try contradiction; reflexivity. Qed.

Ltac hd_tac := cbn; exact I.

Lemma motT_subst w lv g c d : hd_ok w -> hd_ok (peelU w lv) -> hd_ok (peelG (peelU w lv) (GCtx g)) ->
  hd_ok (peelL (peelG (peelU w lv) (GCtx g)) c) ->
  LK dnftm d -> (motT w lv g c)[d] = motT w[d] lv g c[d].
Proof.
  intros H1 H2 H3 H4 Hd. unfold motT.
  rewrite getTy_subst, <- peelL_subst by (auto; intros n; apply dnftm_nftm, Hd).
  rewrite <- peelG_subst, <- peelU_subst by auto. reflexivity.
Qed.
Lemma mott_subst w lv g U c d : hd_ok w -> hd_ok (peelU w lv) -> hd_ok (peelG (peelU w lv) (GCtx g)) ->
  hd_ok (peelG (peelG (peelU w lv) (GCtx g)) (GTy U)) ->
  hd_ok (peelL (peelG (peelG (peelU w lv) (GCtx g)) (GTy U)) c) ->
  LK dnftm d -> (mott w lv g U c)[d] = mott w[d] lv g U c[d].
Proof.
  intros H1 H2 H3 H4 H5 Hd. unfold mott.
  rewrite getTy_subst, <- peelL_subst by (auto; intros n; apply dnftm_nftm, Hd).
  rewrite <- !peelG_subst, <- peelU_subst by auto. reflexivity.
Qed.

(** Lookups of the lifted substitutions (the identity cases need normal
    entries, which typed substitutions have). *)
Lemma uwkn_S n d : uwkn (S n) d = uwk (uwkn n d).
Proof. reflexivity. Qed.
Lemma gwkn_S n d : gwkn (S n) d = gwk (gwkn n d).
Proof. reflexivity. Qed.
Lemma lliftn_S n d : lliftn (S n) d = llift (lliftn n d).
Proof. reflexivity. Qed.

Lemma llk_uwkn nu d n : LK dnftm d -> llk (uwkn nu d) n = uren_tm (llk d n) (ush nu).
Proof.
  intros Hd. induction nu.
  - rewrite (proj1 (proj2 uren_as_usubst_all) _ _ lvar) by reflexivity.
    symmetry; apply (proj1 (proj2 usubst_id_all)); auto.
  - rewrite uwkn_S. unfold uwk. rewrite llk_ulren, IHnu.
    apply (proj1 (proj2 uren_uren_all)); reflexivity.
Qed.
Lemma llk_gwkn ng d n : LK dnftm d -> llk (gwkn ng d) n = gren_tm (llk d n) (ush ng).
Proof.
  intros Hd. induction ng.
  - symmetry; apply (proj1 (proj2 gren_id_all)); auto.
  - rewrite gwkn_S. unfold gwk. rewrite llk_glren, IHng.
    apply (proj1 (proj2 gren_gren_all)); reflexivity.
Qed.
Lemma lk_dnf_gwkn ng d : LK dnftm d -> LK dnftm (gwkn ng d).
Proof. intros Hd; destruct ng; [exact Hd | intros n; cbn; unfold gwk; rewrite llk_glren; apply gren_dnf_all]. Qed.
Lemma ren_id_tm (t : tm) : nftm t -> t⟨rshift 0⟩ = t.
Proof.
  intros H. rewrite (ren_as_subst _ _ (lshift 0)); [apply subst_id; auto|];
    intros; cbn; f_equal; lia.
Qed.

Lemma llk_lliftn nl d n : LK nftm d -> llk (lliftn nl d) (n + nl) = ren_tm (llk d n) (rshift nl).
Proof.
  intros Hd. induction nl.
  - rewrite Nat.add_0_r. symmetry; apply ren_id_tm; apply Hd.
  - rewrite lliftn_S, Nat.add_succ_r, llk_llift, IHnl.
    change (ren_tm (ren_tm ?x ?a) ?b) with (x⟨a⟩⟨b⟩). apply ren_ren. intros m; cbn; lia.
Qed.
Lemma lk_dnf_lliftn nl d : LK dnftm d -> LK dnftm (lliftn nl d).
Proof. intros Hd; induction nl; cbn; auto with nf. Qed.
Lemma lk_dnf_bsub k d : LK dnftm d -> LK dnftm (bsub k d).
Proof. intros; apply lk_dnf_gwkn, lk_dnf_uwkn; auto. Qed.
#[export] Hint Resolve lk_dnf_uwkn lk_dnf_gwkn lk_dnf_lliftn lk_dnf_bsub : nf.

Lemma wkb_subst nu ng nl w d : LK dnftm d ->
  (wkb nu ng nl w)[lliftn nl (gwkn ng (uwkn nu d))] = wkb nu ng nl w[d].
Proof.
  intros Hd. unfold wkb. cbn [subst Subst_tm].
  rewrite (proj1 (proj2 ren_subst_all) _ _ _ (ldrop nl (lliftn nl (gwkn ng (uwkn nu d)))))
    by (intros n; rewrite llk_ldrop; cbn; f_equal; lia).
  rewrite (proj1 (proj2 uren_subst_all) _ _ (ulren d (ush nu))) by (intros; apply llk_ulren).
  rewrite (proj1 (proj2 gren_subst_all) _ _ (glren (ulren d (ush nu)) (ush ng)))
    by (intros; apply llk_glren).
  rewrite (proj1 (proj2 subst_ren_all) _ _ (lren (glren (ulren d (ush nu)) (ush ng)) (rshift nl)))
    by (intros; apply llk_lren).
  apply subst_ext. intros n.
  rewrite llk_ldrop, Nat.add_comm, llk_lliftn by (intros m; apply dnftm_nftm, lk_dnf_gwkn, lk_dnf_uwkn, Hd).
  rewrite llk_lren, llk_glren, llk_ulren, llk_gwkn, llk_uwkn by auto with nf. reflexivity.
Qed.
Lemma wkb_subst0 nu ng w d : LK dnftm d -> (wkb nu ng 0 w)[gwkn ng (uwkn nu d)] = wkb nu ng 0 w[d].
Proof. exact (wkb_subst nu ng 0 w d). Qed.
Lemma wkb_subst1 nu ng w d : LK dnftm d ->
  (wkb nu ng 1 w)[llift (gwkn ng (uwkn nu d))] = wkb nu ng 1 w[d].
Proof. exact (wkb_subst nu ng 1 w d). Qed.
Lemma wkb_subst2 nu ng w d : LK dnftm d ->
  (wkb nu ng 2 w)[llift (llift (gwkn ng (uwkn nu d)))] = wkb nu ng 2 w[d].
Proof. exact (wkb_subst nu ng 2 w d). Qed.
Lemma wkb_subst3 nu ng w d : LK dnftm d ->
  (wkb nu ng 3 w)[llift (llift (llift (gwkn ng (uwkn nu d))))] = wkb nu ng 3 w[d].
Proof. exact (wkb_subst nu ng 3 w d). Qed.
Lemma wkb_subst4 nu ng w d : LK dnftm d ->
  (wkb nu ng 4 w)[llift (llift (llift (llift (gwkn ng (uwkn nu d)))))] = wkb nu ng 4 w[d].
Proof. exact (wkb_subst nu ng 4 w d). Qed.
Lemma wkb_subst5 nu ng w d : LK dnftm d ->
  (wkb nu ng 5 w)[llift (llift (llift (llift (llift (gwkn ng (uwkn nu d))))))] = wkb nu ng 5 w[d].
Proof. exact (wkb_subst nu ng 5 w d). Qed.

Fixpoint cexts_sub (As : list (ty * lvl)) (d : lsub) : list (ty * lvl) :=
  match As with nil => nil | cons (A, l) As => cons (A[d], l) (cexts_sub As (llift d)) end.

Ltac rec_subst_rw :=
  rewrite ?motT_subst, ?mott_subst by first [hd_tac | auto 8 with nf];
  rewrite ?wkb_subst0, ?wkb_subst1, ?wkb_subst2, ?wkb_subst3, ?wkb_subst4, ?wkb_subst5, ?wkb_subst
    by auto with nf.

Lemma brLocs_subst k MT Mt a1 a2 d : k < nbr -> LK dnftm d ->
  cexts_sub (brLocs k (wrapMT MT) (wrapMt Mt) a1 a2) (bsub k d) =
  brLocs k (wrapMT MT)[d] (wrapMt Mt)[d] a1 a2.
Proof.
  intros Hk Hd.
  unfold bsub.
  br_all ltac:(destruct k; [cbn [brLocs cexts_sub br_ng br_nu br_ar mkLocs call_ty call_lv br_calls]; rec_subst_rw; reflexivity|]).
  lia.
Qed.

Lemma brRes_subst k MT Mt d : k < nbr -> LK dnftm d ->
  (brRes k (wrapMT MT) (wrapMt Mt))[lliftn (br_nl k) (bsub k d)] =
  brRes k (wrapMT MT)[d] (wrapMt Mt)[d].
Proof.
  intros Hk Hd.
  unfold bsub.
  br_all ltac:(destruct k; [cbn [brRes br_nl br_ng br_nu br_ar call_ty br_head]; rec_subst_rw; reflexivity|]).
  lia.
Qed.

Fixpoint tup_ok (t : tm) : Prop := match t with tmTup _ r => tup_ok r | var _ => False | _ => True end.
Lemma tup_nth_subst t k d : tup_ok t -> tup_nth t[d] k = (tup_nth t k)[d].
Proof. revert t; induction k; intros [] H; cbn in *; try contradiction; auto. Qed.

Ltac speel_push :=
  repeat first [ rewrite <- peelL_subst by first [hd_tac | intros ?; apply dnftm_nftm; auto]
               | rewrite <- peelG_subst by first [hd_tac | auto]
               | rewrite <- peelU_subst by first [hd_tac | auto] ];
  unfold rb_br; rewrite tup_nth_subst by hd_tac; reflexivity.

Lemma redT_subst_map l1 l2 MT Mt bs l Δ c d : LK dnftm d ->
  redT l1 l2 (mkrb MT Mt bs)[d] l Δ c =
  option_map (fun v => v[d]) (redT l1 l2 (mkrb MT Mt bs) l Δ c).
Proof. intros Hd; destruct c; cbn [redT option_map]; try reflexivity; f_equal; speel_push. Qed.
Lemma redt_subst_map l1 l2 MT Mt bs l Δ T c d : LK dnftm d ->
  redt l1 l2 (mkrb MT Mt bs)[d] l Δ T c =
  option_map (fun v => v[d]) (redt l1 l2 (mkrb MT Mt bs) l Δ T c).
Proof.
  intros Hd; destruct c; cbn [redt option_map]; redt_case T; cbn [redt option_map]; try reflexivity; f_equal; speel_push.
Qed.
Lemma redT_subst l1 l2 MT Mt bs l Δ c v d : LK dnftm d -> redT l1 l2 (mkrb MT Mt bs) l Δ c = Some v ->
  redT l1 l2 (mkrb MT Mt bs)[d] l Δ c = Some v[d].
Proof. intros Hd E. now rewrite redT_subst_map, E. Qed.
Lemma redt_subst l1 l2 MT Mt bs l Δ T c v d : LK dnftm d ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T c = Some v -> redt l1 l2 (mkrb MT Mt bs)[d] l Δ T c = Some v[d].
Proof. intros Hd E. now rewrite redt_subst_map, E. Qed.

(** ** Typed substitutions in the recursors' scopes *)

Lemma lsub_wf_ext G i Δ d d' Γ : (forall n, llk d n = llk d' n) ->
  [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] d' : Γ ].
Proof.
  intros He [HΔ Hn Ht Hv]; constructor; auto.
  - intros n; rewrite <- He; apply Hn.
  - destruct Ht as [Ht1 Ht2]; split; auto; intros n; rewrite <- He; apply Ht2.
  - intros n T l Hin. rewrite <- He, <- (subst_ext_ty T d d' He). now apply Hv.
Qed.

Lemma clen_uren Γ ρ : clen (ucren Γ ρ) = clen Γ.
Proof. induction Γ; cbn; auto. Qed.
Lemma ctx_tail_uren Γ ρ : ctx_tail (ucren Γ ρ) = ucren (ctx_tail Γ) ρ.
Proof. induction Γ; cbn; auto. Qed.

Lemma lsub_wf_uwkn nu G i Δ d Γ : [ G ; Δ ⊢[ i ] d : Γ ] ->
  [ gctx_uwk nu G ; ucren Δ (ush nu) ⊢[ i ] uwkn nu d : ucren Γ (ush nu) ].
Proof.
  intros [HΔ Hn Ht Hv]. constructor.
  - apply uwk_ctx, HΔ.
  - apply lk_dnf_uwkn, Hn.
  - destruct Ht as [Ht1 Ht2]. split; [rewrite !ctx_tail_uren; now f_equal|].
    intros m. rewrite !clen_uren, llk_uwkn, Ht2 by exact Hn. reflexivity.
  - intros m T l Hin. destruct (in_ctx_uren_inv _ _ _ _ _ Hin) as (T0 & l0 & HT0 & -> & ->).
    rewrite llk_uwkn by exact Hn.
    replace ((uren_ty T0 (ush nu))[uwkn nu d]) with (uren_ty (T0[d]) (ush nu)).
    + apply uwk_tm, Hv, HT0.
    + apply (proj1 uren_subst_all). intros; now rewrite llk_uwkn.
Qed.

Lemma lsub_wf_gwkn L Ψ Ds i Δ d Γ : [ ⊢ mkG L (Ds ++ Ψ) ] -> [ mkG L Ψ ; Δ ⊢[ i ] d : Γ ] ->
  [ mkG L (Ds ++ Ψ) ; gcren Δ (ush (length Ds)) ⊢[ i ] gwkn (length Ds) d : gcren Γ (ush (length Ds)) ].
Proof.
  intros HG [HΔ Hn Ht Hv].
  pose proof (gwk_stepn_wf Ds Ψ) as Hw.
  assert (Hξ : forall j, gwk_fn (gwk_stepn (length Ds)) j = ush (length Ds) j) by apply gwk_stepn_fn.
  constructor.
  - pose proof (proj1 (proj2 gweakening) _ _ _ HΔ _ _ _ (le_n _) Hw HG) as X.
    rewrite (proj1 (proj2 (proj2 gren_ext_all)) _ _ _ Hξ) in X. exact X.
  - apply lk_dnf_gwkn, Hn.
  - destruct Ht as [Ht1 Ht2]. split.
    + change (gcren ?x ?y) with x⟪y⟫. rewrite !ctx_tail_gren. now f_equal.
    + intros m. change (gcren ?x ?y) with x⟪y⟫. rewrite !clen_gren, llk_gwkn, Ht2 by exact Hn.
      reflexivity.
  - intros m A k Hin. change (gcren ?x ?y) with x⟪y⟫ in Hin.
    destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & HA0 & ->).
    rewrite llk_gwkn by exact Hn.
    replace (A0⟪ush (length Ds)⟫[gwkn (length Ds) d]) with ((A0[d])⟪ush (length Ds)⟫).
    + pose proof (proj1 (proj2 (proj2 (proj2 gweakening))) _ _ _ _ _ _ (Hv _ _ _ HA0) _ _ _ (le_n _) Hw HG) as X.
      rewrite (proj1 (proj2 (proj2 gren_ext_all)) _ _ _ Hξ), (proj1 (proj2 gren_ext_all) _ _ _ Hξ),
        (proj1 gren_ext_all _ _ _ Hξ) in X.
      exact X.
    + apply (proj1 gren_subst_all). intros; now rewrite llk_gwkn.
Qed.

Lemma lsub_wf_bsub k G Δ d Γ : k < nbr -> [ G ; Δ ⊢[ lM ] d : Γ ] ->
  [ brG k G ; wkc (br_nu k) (br_ng k) Δ ⊢[ lM ] bsub k d : wkc (br_nu k) (br_ng k) Γ ].
Proof.
  intros Hk Hd. pose proof (wf_brG (ctx_glob _ _ _ (lsub_wf_ctx Hd)) k Hk) as HG.
  unfold bsub, wkc, brG. rewrite <- (brDecls_len k Hk).
  apply (lsub_wf_gwkn _ (gΨ (gctx_uwk (br_nu k) G)) (brDecls k)).
  - exact HG.
  - apply lsub_wf_uwkn, Hd.
Qed.

Lemma wf_cexts_prefix G i Γ As : [ G ; cexts Γ As ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] ].
Proof.
  revert Γ; induction As as [|[A l] As IH]; intros Γ H; cbn in H; auto.
  apply IH in H. inversion H; auto.
Qed.

Lemma lsub_wf_cexts G i Δ d Γ As : [ G ; Δ ⊢[ i ] d : Γ ] ->
  [ G ; cexts Δ (cexts_sub As d) ⊢[ typeof i ] ] ->
  [ G ; cexts Δ (cexts_sub As d) ⊢[ i ] lliftn (length As) d : cexts Γ As ].
Proof.
  revert Δ d Γ; induction As as [|[A l] As IH]; intros Δ d Γ Hd HΘ; cbn [cexts cexts_sub length] in *; auto.
  rewrite lliftn_S. replace (llift (lliftn (length As) d)) with (lliftn (length As) (llift d))
    by (unfold lliftn; symmetry; exact (Nat.iter_succ_r (length As) _ llift d)).
  apply IH; [| exact HΘ].
  pose proof (wf_cexts_prefix _ _ _ _ HΘ) as HA. inversion HA; subst.
  apply lsub_wf_lift_g; auto.
Qed.

Lemma lsub_wf_recΓT G Δ d Γ : [ G ; Δ ⊢[ lM ] d : Γ ] ->
  [ recGT G ; recΓT Δ ⊢[ lM ] llift (gwk (uwk d)) : recΓT Γ ].
Proof.
  intros Hd. pose proof (wf_recΓT _ _ (lsub_wf_ctx Hd)) as HΘ.
  unfold recΓT in *. inversion HΘ as [| |? ? ? A l HΔ HA Hl]; subst.
  apply (lsub_wf_lift_g' _ _ _ _ _ _ (tyCTyp (cvar 0) (lvar 0))); auto.
  pose proof (wf_recGT (ctx_glob _ _ _ (lsub_wf_ctx Hd))) as HG.
  apply (lsub_wf_gwkn _ _ (gdCtx :: nil)); [exact HG|]. apply (lsub_wf_uwkn 1), Hd.
Qed.

Lemma lsub_wf_recΓt G Δ d Γ : [ G ; Δ ⊢[ lM ] d : Γ ] ->
  [ recGt G ; recΓt Δ ⊢[ lM ] llift (gwk (gwk (uwk d))) : recΓt Γ ].
Proof.
  intros Hd. pose proof (wf_recΓt _ _ (lsub_wf_ctx Hd)) as HΘ.
  unfold recΓt in *. inversion HΘ as [| |? ? ? A l HΔ HA Hl]; subst.
  apply (lsub_wf_lift_g' _ _ _ _ _ _ (tyCTrm (cvar 1) (gv 0) (lvar 0))); auto.
  pose proof (wf_recGt (ctx_glob _ _ _ (lsub_wf_ctx Hd))) as HG.
  apply (lsub_wf_gwkn _ _ (_ :: gdCtx :: nil)); [exact HG|]. apply (lsub_wf_uwkn 1), Hd.
Qed.

(** Shape: a typed recursor carries a bundle built by [mkrb]. *)
Lemma elimT_rb_shape G i Γ l1 l2 rb l Δ t T k :
  [ G ; Γ ⊢[ i ] elimT l1 l2 rb l Δ t : T @ k ] -> exists MT Mt bs, rb = mkrb MT Mt bs.
Proof.
  intros H; remember (elimT l1 l2 rb l Δ t) as e eqn:He; revert He.
  induction H; intros He; try discriminate; eauto. injection He; intros; subst; eauto.
Qed.
Lemma elimt_rb_shape G i Γ l1 l2 rb l Δ T0 t T k :
  [ G ; Γ ⊢[ i ] elimt l1 l2 rb l Δ T0 t : T @ k ] -> exists MT Mt bs, rb = mkrb MT Mt bs.
Proof.
  intros H; remember (elimt l1 l2 rb l Δ T0 t) as e eqn:He; revert He.
  induction H; intros He; try discriminate; eauto. injection He; intros; subst; eauto.
Qed.

Lemma cexts_sub_snoc As A l d :
  cexts_sub (As ++ (A, l) :: nil) d = cexts_sub As d ++ (A[lliftn (length As) d], l) :: nil.
Proof.
  revert d; induction As as [|[B k] As IH]; intros d; cbn [cexts_sub List.app length]; auto.
  rewrite IH. unfold lliftn. rewrite <- (Nat.iter_succ_r (length As) _ llift d). reflexivity.
Qed.

(** ** [UΠ] (M4): the body under [uwkn n d]; instances and η commute *)

Lemma uext_ush_lvar ls n m : length ls = n -> uext ls lvar (ush n m) = lvar m.
Proof.
  intros Hn; unfold uext, ush; rewrite Hn.
  destruct (Nat.ltb_spec (n + m) n); [lia|]. f_equal; lia.
Qed.
Lemma ulsubst_uwkn_uext n ls d i : length ls = n -> LK dnftm d ->
  llk (ulsubst (uwkn n d) (uext ls lvar)) i = llk d i.
Proof.
  intros Hn Hd. rewrite llk_ulsubst, llk_uwkn by exact Hd.
  rewrite (uren_usubst_tm _ _ _ lvar) by (intros m; symmetry; apply uext_ush_lvar, Hn).
  apply usubst_id; [apply Hd | reflexivity].
Qed.
Lemma subst_uinst_ty n ls (T : ty) d : length ls = n -> LK dnftm d ->
  T[uext ls lvar]ᵤ[d] = T[uwkn n d][uext ls lvar]ᵤ.
Proof.
  intros Hn Hd. rewrite usubst_subst_ty. apply subst_ext_ty; intros i.
  symmetry; apply ulsubst_uwkn_uext; assumption.
Qed.
Lemma subst_uinst_tm n ls (t : tm) d : length ls = n -> LK dnftm d ->
  t[uext ls lvar]ᵤ[d] = t[uwkn n d][uext ls lvar]ᵤ.
Proof.
  intros Hn Hd. rewrite usubst_subst. apply subst_ext; intros i.
  symmetry; apply ulsubst_uwkn_uext; assumption.
Qed.
Lemma subst_uren_ush n (t : tm) d : LK dnftm d -> t⟨ush n⟩ᵤ[uwkn n d] = t[d]⟨ush n⟩ᵤ.
Proof. intros Hd. symmetry; apply uren_subst_tm. intros i; apply llk_uwkn, Hd. Qed.

Ltac sub_upi_body :=
  match goal with
  | IH : forall Δ d, lsub_wf (gctx_uwk ?n ?G) _ Δ d _ -> _, Hd : lsub_wf ?G _ ?Δ ?d ?Γ |- _ =>
      apply IH, lsub_wf_uwkn, Hd
  end.
Ltac sub_upi_rw :=
  match goal with Hd : lsub_wf _ _ _ ?d _ |- _ =>
    try match goal with Hn : length ?ls = ?n |- _ =>
      rewrite ?(subst_uinst_ty n ls _ d Hn (lsub_wf_dnf Hd)),
        ?(subst_uinst_tm n ls _ d Hn (lsub_wf_dnf Hd)) end;
    rewrite ?(subst_uren_ush _ _ d (lsub_wf_dnf Hd))
  end.

(** The context cases: a prefix [Γ] of [cexts Γ As] is substituted. *)
Ltac sub_ctx :=
  match goal with
  | Heq : _ = cexts ?Γ0 ?As, Hd : lsub_wf _ _ _ ?d ?Γ0 |- _ =>
      let As' := fresh "As'" in let A' := fresh "A'" in let l' := fresh "l'" in
      let Θ' := fresh "Θ'" in let Hθ := fresh "Hθ" in
      destruct (cexts_inv _ _ _ (eq_sym Heq)) as [[-> ?] | (As' & A' & l' & Θ' & -> & Hθ & ->)];
      [ cbn; exact (lsub_wf_ctx Hd)
      | first [ discriminate Hθ
              | let HΓ := fresh "HΓ" in
                injection Hθ as HΓ <- <-; rewrite cexts_sub_snoc, cexts_snoc;
                match goal with
                | IHc : forall Γ As, _ = cexts Γ As -> _, IHt : forall Δ d, lsub_wf _ _ Δ d _ -> _ |- _ =>
                    let X := fresh "X" in
                    pose proof (IHc _ _ HΓ _ _ Hd) as X;
                    apply wfc_ext; [ exact X
                                   | eapply lift_ty; [ apply IHt; rewrite HΓ; now apply lsub_wf_cexts
                                                     | apply lle_self_typeof ]
                                   | assumption ]
                end ] ]
  end.

(** The recursors' premises under [d]. *)
Ltac sub_motive :=
  match goal with
  | IH : forall Δ d, lsub_wf _ _ Δ d (recΓT ?Γ) -> _, Hd : lsub_wf _ _ ?Δ ?d ?Γ |- _ =>
      apply IH, lsub_wf_recΓT, Hd
  | IH : forall Δ d, lsub_wf _ _ Δ d (recΓt ?Γ) -> _, Hd : lsub_wf _ _ ?Δ ?d ?Γ |- _ =>
      apply IH, lsub_wf_recΓt, Hd
  end.
Ltac sub_brctx_at k Hk :=
  match goal with
  | IH : forall k, k < nbr -> forall Γ0 As, brΓ k ?Γ (wrapMT ?MT) (wrapMt ?Mt) ?l1 ?l2 = cexts Γ0 As -> _,
    Hd : lsub_wf _ _ ?Δ ?d ?Γ |- _ =>
      let X := fresh "X" in
      pose proof (IH k Hk _ _ eq_refl _ _ (lsub_wf_bsub k _ _ _ _ Hk Hd)) as X;
      rewrite brLocs_subst in X by (first [exact Hk | exact (lsub_wf_dnf Hd)]); exact X
  end.
Ltac sub_brctx := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; sub_brctx_at k Hk.
Ltac sub_branches :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
  match goal with
  | IH : forall k, k < nbr -> forall Δ d, lsub_wf _ _ Δ d (brΓ k ?Γ (wrapMT ?MT) (wrapMt ?Mt) ?l1 ?l2) -> _,
    Hd : lsub_wf ?G _ ?Δ ?d ?Γ |- _ =>
      let C := fresh "C" in let W := fresh "W" in let X := fresh "X" in
      assert (C : [ brG k G ; brΓ k Δ (wrapMT MT)[d] (wrapMt Mt)[d] l1 l2 ⊢[ lM ] ]) by sub_brctx_at k Hk;
      assert (W : [ brG k G ; brΓ k Δ (wrapMT MT)[d] (wrapMt Mt)[d] l1 l2 ⊢[ lM ]
                    lliftn (br_nl k) (bsub k d) : brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ]);
      [ unfold brΓ in C |- *;
        rewrite <- (brLocs_len k (wrapMT MT) (wrapMt Mt) (lvren l1 (ush (br_nu k))) (lvren l2 (ush (br_nu k))) Hk);
        rewrite <- brLocs_subst in C |- * by (first [exact Hk | exact (lsub_wf_dnf Hd)]);
        apply lsub_wf_cexts; [ apply lsub_wf_bsub; assumption | exact C ]
      | pose proof (IH k Hk _ _ W) as X;
        rewrite brRes_subst in X by (first [exact Hk | exact (lsub_wf_dnf Hd)]); exact X ]
  end.

Ltac sub_rec_rw ::=
  match goal with Hd : lsub_wf _ _ _ ?d _ |- _ =>
    rewrite ?mkrb_subst;
    rewrite ?motT_subst, ?mott_subst by first [hd_tac | exact (lsub_wf_dnf Hd)]
  end;
  (* and the meta-functions' instance equations (M5) *)
  try sub_mf_rw.

(** [J]'s motive (M11a): under the induction hypothesis its context holds the
    substituted [Id] premise's type, the rule's only up to an equation. *)
Ltac sub_Jmot :=
  first
  [ first [eapply wf_ty_regctx | eapply eq_ty_regctx];
    [ match goal with
      | IH : forall Δ d, lsub_wf _ _ _ d (_ ,, _ @ _ ,, _ @ _) -> _ |- _ =>
          eapply IH; solve [eauto 16 with sub]
      end
    | sub_rw; reflexivity ]
  (* its [Id] premise: the substituted type, up to the same equation *)
  | eapply wf_ty_regty;
    [ match goal with
      | Hd : lsub_wf _ _ _ ?d _, IH : forall Δ d, lsub_wf _ _ _ d (_ ,, _ @ _) -> _ |- _ =>
          eapply (IH _ (llift d)); solve [eauto 16 with sub]
      end
    | sub_rw; reflexivity ] ].

Ltac sub_manual2 :=
  match goal with
  (* the identity type (M11a) *)
  | |- wf_tm _ _ _ (tmJ _ _ _ _ _ _ _ _) _ _ => eapply wf_J; first [solve [sub_Jmot] | sub_premise]
  | |- eq_tm _ _ _ (tmJ _ _ _ _ _ _ _ (tmRefl _ _ _)) _ _ _ =>
      eapply eqtm_J_beta; first [solve [sub_Jmot] | sub_premise]
  | |- eq_tm _ _ _ (tmJ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_J; first [solve [sub_Jmot] | sub_premise]
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
  (* defined globals (M9): the body stays in the definition's context *)
  | |- wf_tm _ _ _ (gdef _ _ _) _ _ =>
      match goal with Hd : lsub_wf _ _ _ ?d _ |- context [(?T[?e])[?d]] =>
        rewrite (subst_subst_ty T e d (lcomp e d) (fun m => llk_lcomp e d m)) end;
      eapply wf_gdef; [ .. | sub_entries | ]; sub_gvar_side
  | |- eq_tm _ _ _ (gdef _ _ _) (gdef _ _ _) _ _ =>
      match goal with Hd : lsub_wf _ _ _ ?d _ |- context [(?T[?e])[?d]] =>
        rewrite (subst_subst_ty T e d (lcomp e d) (fun m => llk_lcomp e d m)) end;
      eapply eqtm_gdef; [ .. | sub_entries | sub_entries | sub_entries | ]; sub_gvar_side
  | |- eq_tm _ _ _ (gdef _ _ _) _ _ _ =>
      match goal with Hd : lsub_wf _ _ _ ?d _ |- context [(?T[?e])[?d]] =>
        rewrite (subst_subst_ty T e d (lcomp e d) (fun m => llk_lcomp e d m)) end;
      match goal with Hd : lsub_wf _ _ _ ?d _ |- context [(?t[?e])[?d]] =>
        rewrite (subst_subst t e d (lcomp e d) (fun m => llk_lcomp e d m)) end;
      eapply eqtm_delta; [ .. | sub_entries | ]; sub_gvar_side
  | |- wf_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ => eapply wf_letboxT; try sub_body; sub_premise
  | |- wf_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ => eapply wf_letboxt; try sub_body; sub_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ (boxT _)) _ _ _ =>
      rewrite gsingle_subst by eauto with nf; eapply eqtm_letboxT_beta; try sub_body; sub_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      rewrite gsingle_subst by eauto with nf; eapply eqtm_letboxt_beta; try sub_body; sub_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxT; try sub_body; sub_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxt; try sub_body; sub_premise
  | |- wf_tm _ _ _ (boxT _) _ _ => eapply wf_boxT; sub_premise
  | |- eq_tm _ _ _ (boxT _) _ _ _ => eapply eqtm_boxT; sub_premise
  | |- eq_tm _ _ _ (boxt _) _ _ _ => eapply eqtm_boxt; sub_premise
  | |- wf_tm _ _ _ (boxt _) _ _ => eapply wf_boxt; sub_premise
  | |- wf_ty _ _ _ (tyCTyp _ _) _ => eapply wft_CTyp; sub_premise
  | |- wf_ty _ _ _ (tyCTrm _ _ _) _ => eapply wft_CTrm; sub_premise
  | |- eq_ty _ _ _ (tyCTyp _ _) _ _ => eapply eqty_CTyp; sub_premise
  | |- eq_ty _ _ _ (tyCTrm _ _ _) _ _ => eapply eqty_CTrm; sub_premise
  | |- wf_tm _ _ _ (elimT _ _ _ _ _ _) _ _ =>
      sub_rec_rw; eapply wf_elimT; [ .. | sub_motive | sub_motive | sub_brctx | sub_branches | ];
      sub_premise
  | |- wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ =>
      sub_rec_rw; eapply wf_elimt; [ .. | sub_motive | sub_motive | sub_brctx | sub_branches | | ];
      sub_premise
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ (boxT _)) _ _ _ =>
      match goal with
      | w : wf_tm _ _ _ (elimT _ _ _ _ _ (boxT _)) _ _, Hd : lsub_wf _ _ _ ?d _ |- _ =>
          destruct (elimT_rb_shape _ _ _ _ _ _ _ _ _ _ _ w) as (? & ? & ? & ->);
          eapply eqtm_elimT_beta; [sub_premise | apply redT_subst; [exact (lsub_wf_dnf Hd) | assumption] | sub_premise]
      end
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      match goal with
      | w : wf_tm _ _ _ (elimt _ _ _ _ _ _ (boxt _)) _ _, Hd : lsub_wf _ _ _ ?d _ |- _ =>
          destruct (elimt_rb_shape _ _ _ _ _ _ _ _ _ _ _ _ w) as (? & ? & ? & ->);
          eapply eqtm_elimt_beta; [sub_premise | apply redt_subst; [exact (lsub_wf_dnf Hd) | assumption] | sub_premise]
      end
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ _) _ _ _ =>
      sub_rec_rw; eapply eqtm_elimT;
      [ .. | sub_motive | sub_motive | sub_motive | sub_motive | sub_motive | sub_motive
           | sub_brctx | sub_brctx | sub_branches | sub_branches | ]; sub_premise
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ _ =>
      sub_rec_rw; eapply eqtm_elimt;
      [ .. | sub_motive | sub_motive | sub_motive | sub_motive | sub_motive | sub_motive
           | sub_brctx | sub_brctx | sub_branches | sub_branches | ]; sub_premise
  (* meta-functions (M5) *)
  | |- wf_ty _ _ _ (tyCPi _ _) _ => eapply wft_cpi; try sub_gbody; sub_premise
  | |- wf_ty _ _ _ (tyTPi _ _ _ _) _ => eapply wft_tpi; try sub_gbody; sub_premise
  | |- eq_ty _ _ _ (tyCPi _ _) _ _ => eapply eqty_cpi; try sub_gbody; sub_premise
  | |- eq_ty _ _ _ (tyTPi _ _ _ _) _ _ => eapply eqty_tpi; try sub_gbody; sub_premise
  | |- wf_tm _ _ _ (clam _ _ _) _ _ => eapply wf_clam; try sub_gbody; sub_premise
  | |- wf_tm _ _ _ (tlam _ _ _ _ _) _ _ => eapply wf_tlam; try sub_gbody; sub_premise
  | |- wf_tm _ _ _ (capp _ _) _ _ => sub_mf_rw; eapply wf_capp; try sub_gbody; sub_premise
  | |- wf_tm _ _ _ (tapp _ _) _ _ => sub_mf_rw; eapply wf_tapp; try sub_gbody; sub_premise
  | |- eq_tm _ _ _ (clam _ _ (capp _ _)) _ _ _ => sub_mf_rw; eapply eqtm_ceta; try sub_gbody; sub_premise
  | |- eq_tm _ _ _ (tlam _ _ _ _ (tapp _ _)) _ _ _ => sub_mf_rw; eapply eqtm_teta; try sub_gbody; sub_premise
  | |- eq_tm _ _ _ (clam _ _ _) _ _ _ => eapply eqtm_clam; try sub_gbody; sub_premise
  | |- eq_tm _ _ _ (tlam _ _ _ _ _) _ _ _ => eapply eqtm_tlam; try sub_gbody; sub_premise
  | |- eq_tm _ _ _ (capp (clam _ _ _) _) _ _ _ => sub_mf_rw; eapply eqtm_cbeta; try sub_gbody; sub_premise
  | |- eq_tm _ _ _ (tapp (tlam _ _ _ _ _) _) _ _ _ => sub_mf_rw; eapply eqtm_tbeta; try sub_gbody; sub_premise
  | |- eq_tm _ _ _ (capp _ _) _ _ _ => sub_mf_rw; eapply eqtm_capp; try sub_gbody; sub_premise
  | |- eq_tm _ _ _ (tapp _ _) _ _ _ => sub_mf_rw; eapply eqtm_tapp; try sub_gbody; sub_premise
  | |- wf_ty _ _ _ (tyUPi _ _ _) _ => eapply wft_upi; try sub_upi_body; sub_premise
  | |- eq_ty _ _ _ (tyUPi _ _ _) _ _ => eapply eqty_upi; try sub_upi_body; sub_premise
  | |- wf_tm _ _ _ (ulam _ _ _ _) _ _ => eapply wf_ulam; try sub_upi_body; sub_premise
  | |- eq_tm _ _ _ (ulam _ _ _ (uapp _ (ubvars _))) _ _ _ =>
      sub_upi_rw; eapply eqtm_ueta; try sub_upi_body; sub_premise
  | |- eq_tm _ _ _ (ulam _ _ _ _) _ _ _ => eapply eqtm_ulam; try sub_upi_body; sub_premise
  | |- wf_tm _ _ _ (uapp _ _) _ _ => sub_upi_rw; eapply wf_uapp; try sub_upi_body; sub_premise
  | |- eq_tm _ _ _ (uapp (ulam _ _ _ _) _) _ _ _ =>
      sub_upi_rw; eapply eqtm_ubeta; try sub_upi_body; sub_premise
  | |- eq_tm _ _ _ (uapp _ _) _ _ _ => sub_upi_rw; eapply eqtm_uapp; try sub_upi_body; sub_premise
  | |- eq_ty _ lM _ _ _ _ => eapply eqty_leq; sub_premise
  | |- eq_tm _ lM _ _ _ _ _ => eapply eqtm_leq; sub_premise
  end.

Theorem substitution_all :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Θ, [ G ; Θ ⊢[ i ] ] -> forall Γ As, Θ = cexts Γ As ->
     forall Δ d, [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; cexts Δ (cexts_sub As d) ⊢[ typeof i ] ]) /\
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
  apply typing_mut; intros; try exact I; try sub_ctx;
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
