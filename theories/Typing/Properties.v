(** * Syntactic metatheory needed before the logical relation

    - context extraction ("boundary" for contexts), all layers;
    - (local) weakening of every judgment, at every layer: the weakened
      context is well formed at [typeof i]; context extensions use lifting,
      and the letbox body uses global weakening. *)
From DeLaM.Typing Require Export Lifting.

(** ** Lookup under weakening *)

Lemma in_ctx_nf Γ n T l : in_ctx Γ n T l -> nfty T.
Proof. destruct 1; apply ren_nf_ty. Qed.

Lemma in_ctx_wk Γ n T l ρ Δ : in_ctx Γ n T l -> ρ : Δ ≤ Γ -> in_ctx Δ (rlk ρ n) T⟨ρ⟩ l.
Proof.
  intros Hin Hρ; revert n T l Hin; induction Hρ as [Γ|ρ Δ Γ A l' Hρ IH|ρ Δ Γ A l' Hρ IH];
    intros n T l Hin; cbn [wk_ren].
  - replace (rlk (rshift 0) n) with n by (cbn; lia).
    rewrite ren_id_ty by eauto using in_ctx_nf. exact Hin.
  - rewrite rlk_rup. replace T⟨rup ρ⟩ with T⟨ρ⟩⟨↑⟩.
    + constructor; auto.
    + rewrite ren_ren_comp_ty. apply ren_ext_ty; intros m; rlk_simpl; lia.
  - inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 B l1 m Hm]; subst; rewrite rlk_rlift.
    + rewrite shift_lift_ty. constructor.
    + rewrite shift_lift_ty. constructor; auto.
Qed.

(** ** Weakenings as renamings *)

Inductive wkr : rsub -> ctx -> ctx -> Prop :=
| wkr_id Γ : wkr (rshift 0) Γ Γ
| wkr_step r Δ Γ A l : wkr r Δ Γ -> wkr (rup r) (Δ ,, A @ l) Γ
| wkr_up r Δ Γ A l : wkr r Δ Γ -> wkr (rlift r) (Δ ,, A⟨r⟩ @ l) (Γ ,, A @ l).

Lemma wk_wf_wkr ρ Δ Γ : ρ : Δ ≤ Γ -> wkr ρ Δ Γ.
Proof. induction 1; cbn; now constructor. Qed.

Lemma in_ctx_wkr Γ n T l r Δ : in_ctx Γ n T l -> wkr r Δ Γ -> in_ctx Δ (rlk r n) T⟨r⟩ l.
Proof.
  intros Hin Hr; revert n T l Hin; induction Hr as [Γ|r Δ Γ A l' Hr IH|r Δ Γ A l' Hr IH];
    intros n T l Hin.
  - replace (rlk (rshift 0) n) with n by (cbn; lia).
    rewrite ren_id_ty by eauto using in_ctx_nf. exact Hin.
  - rewrite rlk_rup. replace T⟨rup r⟩ with T⟨r⟩⟨↑⟩.
    + constructor; auto.
    + rewrite ren_ren_comp_ty. apply ren_ext_ty; intros m; rlk_simpl; lia.
  - inversion Hin as [Γ0 A0 l0|Γ0 A0 l0 B l1 m Hm]; subst; rewrite rlk_rlift.
    + rewrite shift_lift_ty. constructor.
    + rewrite shift_lift_ty. constructor; auto.
Qed.

#[export] Hint Constructors wkr : wk.

Lemma wkr_tail r Δ Γ : wkr r Δ Γ -> ctx_tail Δ = ctx_tail Γ /\ forall n, rlk r (clen Γ + n) = clen Δ + n.
Proof.
  induction 1 as [Γ|r Δ Γ A l H [IH1 IH2]|r Δ Γ A l H [IH1 IH2]]; cbn [ctx_tail clen];
    split; auto; intros n.
  - rewrite rlk_rup, IH2; lia.
  - replace (S (clen Γ) + n) with (S (clen Γ + n)) by lia.
    rewrite rlk_rlift, IH2; lia.
Qed.

Lemma lsub_tail_wkr d Δ Γ Γ' r : wkr r Γ' Γ -> lsub_tail d Δ Γ -> lsub_tail (lren d r) Δ Γ'.
Proof.
  intros Hr [Ht Hl]. destruct (wkr_tail _ _ _ Hr) as [Ht' Hl']. split; [congruence|].
  intros n; rewrite llk_lren, Hl; cbn; now rewrite Hl'.
Qed.

Lemma nfl_lren d r : dnfl d -> dnfl (lren d r).
Proof. apply dnfl_lren. Qed.

Lemma wkr_gren r Δ Γ ξ : wkr r Δ Γ -> wkr r Δ⟪ξ⟫ Γ⟪ξ⟫.
Proof.
  induction 1; rewrite ?gren_cext.
  - apply wkr_id.
  - now apply wkr_step.
  - rewrite gren_ren_ty'. now apply wkr_up.
Qed.

(** ** Context extensions (the recursors' branch contexts) *)

Lemma cexts_snoc Γ As A l : cexts Γ (As ++ (A, l) :: nil) = cexts Γ As ,, A @ l.
Proof. revert Γ; induction As as [|[B k] As IH]; intros Γ; cbn; auto. Qed.

Lemma cexts_inv Γ0 As Θ : cexts Γ0 As = Θ ->
  (As = nil /\ Γ0 = Θ) \/
  (exists As' A l Θ', As = As' ++ (A, l) :: nil /\ Θ = Θ' ,, A @ l /\ Θ' = cexts Γ0 As').
Proof.
  revert Γ0; induction As as [|[A l] As IH] using rev_ind; intros Γ0 H.
  - left; auto.
  - right. rewrite cexts_snoc in H. exists As, A, l, (cexts Γ0 As); auto.
Qed.

Lemma cexts_ren_snoc As A l r :
  cexts_ren (As ++ (A, l) :: nil) r = cexts_ren As r ++ (A⟨rliftn (length As) r⟩, l) :: nil.
Proof.
  revert r; induction As as [|[B k] As IH]; intros r; cbn [cexts_ren List.app length]; auto.
  rewrite IH. change (rliftn (S (length As)) r) with (rlift (rliftn (length As) r)).
  now rewrite rliftn_succ.
Qed.

Lemma wkr_cexts r Δ Γ0 As : wkr r Δ Γ0 ->
  wkr (rliftn (length As) r) (cexts Δ (cexts_ren As r)) (cexts Γ0 As).
Proof.
  revert r Δ Γ0; induction As as [|[A l] As IH]; intros r Δ Γ0 H; cbn [cexts cexts_ren length]; auto.
  change (rliftn (S (length As)) r) with (rlift (rliftn (length As) r)).
  rewrite rliftn_succ. apply IH. now constructor.
Qed.

Lemma wkr_uren r Δ Γ ρ : wkr r Δ Γ -> wkr r (ucren Δ ρ) (ucren Γ ρ).
Proof.
  induction 1; cbn [ucren].
  - apply wkr_id.
  - now apply wkr_step.
  - rewrite (proj1 uren_ren_all). now apply wkr_up.
Qed.

Lemma wkr_wkc r Δ Γ nu ng : wkr r Δ Γ -> wkr r (wkc nu ng Δ) (wkc nu ng Γ).
Proof. intros H; unfold wkc. apply (wkr_gren _ _ _ (ush ng)), wkr_uren, H. Qed.

(** ** Context extraction *)

Theorem ctx_extract :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ typeof i ] ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; rewrite ?typeof_idem in *; auto.
  all: try solve [destruct i; cbn in *; auto].
  all: match goal with H : wf_ctx _ _ (cext _ _ _) |- _ => inversion H; subst; auto end.
Qed.

(** ** Weakening *)

(** Fold raw renamings/substitutions (exposed by [cbn]) back into notation form. *)
Ltac fold_subst :=
  repeat match goal with
         | |- context [ren_tm ?x ?y] => change (ren_tm x y) with (@ren tm Ren_tm x y)
         | |- context [ren_ty ?x ?y] => change (ren_ty x y) with (@ren ty Ren_ty x y)
         | |- context [subst_tm ?x ?y] => change (subst_tm x y) with (@subst tm Subst_tm x y)
         | |- context [subst_ty ?x ?y] => change (subst_ty x y) with (@subst ty Subst_ty x y)
         end.

(** The meta-functions' instances and η (M5). *)
Lemma gsingle_ren_ty (T : ty) o r : T⦃gsingle o⦄⟨r⟩ = T⟨r⟩⦃gsingle o⦄.
Proof. symmetry; apply (proj1 gsubst_ren_all). Qed.

Ltac wk_rewrite :=
  rewrite ?single_ren_ty, ?single_ren, ?lsucc_ren_ty, ?single2_ren, ?lsingle2_ren_ty, ?gsingle_ren_ty, <- ?gren_ren,
          ?shift_lift, ?shift_lift_ty, ?liftshift_lift_ty, ?liftshift_lift, ?lsingle3_ren,
          ?mkrb_ren, ?motT_ren, ?mott_ren, ?wrapMT_ren, ?wrapMt_ren.

#[export] Hint Resolve wfc_ext : wk.
#[export] Hint Resolve in_ctx_wkr : wk.
#[export] Hint Resolve wft_nat wft_El lequiv_wf_l lequiv_wf_r : wk.
#[export] Hint Extern 1 (ty_leq _ _) => apply (proj1 leq_ren_all); assumption : wk.
#[export] Hint Extern 1 (tm_leq _ _) => apply (proj1 (proj2 leq_ren_all)); assumption : wk.

Lemma wkr_up' r Δ Γ A A' l : wkr r Δ Γ -> A' = A⟨r⟩ -> wkr (rlift r) (Δ ,, A' @ l) (Γ ,, A @ l).
Proof. intros ? ->; now constructor. Qed.
Lemma wf_tm_retype G i Δ x T T' l :
  [ G ; Δ ⊢[ i ] x : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? ->. Qed.
Lemma eq_tm_retype G i Δ x y T T' l :
  [ G ; Δ ⊢[ i ] x ≅ y : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? ->. Qed.

#[export] Hint Extern 2 (wkr (rlift _) _ _) =>
  eapply wkr_up'; [ | first [reflexivity | push_ren; wk_rewrite; push_ren; reflexivity] ] : wk.
#[export] Hint Extern 20 (wf_tm _ _ _ _ _ _) => eapply wf_tm_retype : wk.
#[export] Hint Extern 20 (eq_tm _ _ _ _ _ _ _) => eapply eq_tm_retype : wk.
#[export] Hint Extern 1 (lwf _ _) =>
  (cbn; first [exact I | assumption | split; assumption]) : wk.
#[export] Hint Extern 1 =>
  match goal with Hi : typeof ?i = ?i |- context [typeof ?i] => rewrite Hi end : wk.
#[export] Hint Extern 1 (@eq ty _ _) => (push_ren; wk_rewrite; push_ren; reflexivity) : wk.

Ltac fix_layer :=
  repeat match goal with
         | Hi : typeof ?i = ?i |- context [typeof ?i] => rewrite Hi
         end;
  rewrite ?typeof_idem.

Lemma ctx_glob G i Γ : [ G ; Γ ⊢[ i ] ] -> [ ⊢ G ].
Proof. induction 1; auto. Qed.

#[export] Hint Resolve wft_CTyp wft_CTrm : wk.
#[export] Hint Extern 3 (wf_ty _ (typeof _) _ _ _) => eapply lift_ty; [ | apply lle_self_typeof ] : wk.
#[export] Hint Extern 3 (wf_tm _ (typeof _) _ _ _ _) => eapply lift_tm; [ | apply lle_self_typeof ] : wk.
#[export] Hint Extern 1 (wf_ctx _ (typeof (typeof _)) _) => rewrite typeof_idem : wk.
#[export] Hint Resolve lsub_tail_wkr nfl_lren : wk.

Ltac wk_premises := fix_layer; eauto 6 with wk.

Ltac wk_step := any_rule wk_premises.


Lemma wf_ctx_nat G i Δ : i <> lV -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tyNat @ lzero ⊢[ typeof i ] ].
Proof.
  intros Hv HΔ. apply wfc_ext; [exact HΔ | apply wft_nat; [destruct i; cbn; congruence | now rewrite typeof_idem] | exact I].
Qed.
#[export] Hint Resolve wf_ctx_nat : wk.
Lemma compt_notV i : compt i -> i <> lV.
Proof. now intros [-> | ->]. Qed.
#[export] Hint Resolve compt_notV : wk.
(** [Empty]'s motive context (M12a), as [natrec]'s; every layer but V
    since M12c. *)
Lemma wft_empty_typeof G i Δ l : i <> lV -> lwf (gL G) l -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ⊢[ typeof i ] tyEmpty l @ l ].
Proof.
  intros Hv Hl HΔ. apply wft_empty; [destruct i; cbn; congruence | now rewrite typeof_idem | exact Hl].
Qed.
Lemma wf_ctx_empty G i Δ l : i <> lV -> lwf (gL G) l -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tyEmpty l @ l ⊢[ typeof i ] ].
Proof. intros Hv Hl HΔ. apply wfc_ext; [exact HΔ | now apply wft_empty_typeof | exact Hl]. Qed.
#[export] Hint Resolve wf_ctx_empty wft_empty_typeof : wk.
(** [case]'s motive context (M12b). *)
Lemma wft_sum_typeof G i Δ l l' A B : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ⊢[ i ] B @ l' ] -> [ G ; Δ ⊢[ typeof i ] tySum l l' A B @ lmax l l' ].
Proof.
  intros Hv Hl Hl' HA HB. apply wft_sum; [destruct i; cbn; congruence | exact Hl | exact Hl'
                                       | eapply lift_ty; [exact HA | apply lle_self_typeof]
                                       | eapply lift_ty; [exact HB | apply lle_self_typeof]].
Qed.
Lemma wf_ctx_sum G i Δ l l' A B : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ⊢[ i ] B @ l' ] -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tySum l l' A B @ lmax l l' ⊢[ typeof i ] ].
Proof.
  intros Hv Hl Hl' HA HB HΔ. apply wfc_ext; [exact HΔ | now apply wft_sum_typeof | exact (conj Hl Hl')].
Qed.
#[export] Hint Resolve wf_ctx_sum wft_sum_typeof : wk.
(** [elim_W]'s motive context (M13a; every layer but V since M13b). *)
Lemma wft_W_typeof G i Δ l l' A B : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ,, A @ l ⊢[ i ] B @ l' ] -> [ G ; Δ ⊢[ typeof i ] tyW l l' A B @ lmax l l' ].
Proof.
  intros Hv Hl Hl' HA HB. apply wft_W; [destruct i; cbn; congruence | exact Hl | exact Hl'
                                     | eapply lift_ty; [exact HA | apply lle_self_typeof]
                                     | eapply lift_ty; [exact HB | apply lle_self_typeof]].
Qed.
Lemma wf_ctx_W G i Δ l l' A B : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ,, A @ l ⊢[ i ] B @ l' ] -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tyW l l' A B @ lmax l l' ⊢[ typeof i ] ].
Proof.
  intros Hv Hl Hl' HA HB HΔ. apply wfc_ext; [exact HΔ | now apply wft_W_typeof | exact (conj Hl Hl')].
Qed.
Lemma eqty_W_typeof G i Δ l l' A A' B B' : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Δ ,, A @ l ⊢[ i ] B ≅ B' @ l' ] ->
  [ G ; Δ ⊢[ typeof i ] tyW l l' A B ≅ tyW l l' A' B' @ lmax l l' ].
Proof.
  intros Hv Hl Hl' HA HAA HBB.
  apply eqty_W; [destruct i; cbn; congruence | apply lequiv_refl; assumption | apply lequiv_refl; assumption
                | eapply lift_ty; [exact HA | apply lle_self_typeof]
                | eapply lift_eqty; [exact HAA | apply lle_self_typeof]
                | eapply lift_eqty; [exact HBB | apply lle_self_typeof]].
Qed.
#[export] Hint Resolve wf_ctx_W wft_W_typeof : wk.
(** [elim_Wf]'s motive context (M15a). *)
Lemma wft_wf_typeof G i Δ l A N : lwf (gL G) l ->
  [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ typeof i ] tyWf l A N @ l ].
Proof.
  intros Hl HA HN. apply wft_wf; [apply compt_notV, compt_typeof | exact Hl
                                 | eapply lift_ty; [exact HA | apply lle_self_typeof]
                                 | eapply lift_tm; [exact HN | apply lle_self_typeof]].
Qed.
Lemma wf_ctx_Wf G i Δ l A N : lwf (gL G) l ->
  [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tyWf l A N @ l ⊢[ typeof i ] ].
Proof.
  intros Hl HA HN HΔ. apply wfc_ext; [exact HΔ | now apply wft_wf_typeof | exact Hl].
Qed.
Lemma eqty_wf_typeof G i Δ l A A' N N' : lwf (gL G) l ->
  [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Δ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ typeof i ] tyWf l A N ≅ tyWf l A' N' @ l ].
Proof.
  intros Hl HA HAA HNN.
  apply eqty_wf; [apply compt_notV, compt_typeof | apply lequiv_refl; assumption
                 | eapply lift_ty; [exact HA | apply lle_self_typeof]
                 | eapply lift_eqty; [exact HAA | apply lle_self_typeof]
                 | eapply lift_eqtm; [exact HNN | apply lle_self_typeof]].
Qed.
#[export] Hint Resolve wf_ctx_Wf wft_wf_typeof : wk.
(** [ind_∥∥]'s motive context (M16a). *)
Lemma wft_sq_typeof G i Δ l A : lwf (gL G) l -> [ G ; Δ ⊢[ i ] A @ l ] ->
  [ G ; Δ ⊢[ typeof i ] tySq l A @ l ].
Proof.
  intros Hl HA. apply wft_sq; [apply compt_notV, compt_typeof | exact Hl
                              | eapply lift_ty; [exact HA | apply lle_self_typeof]].
Qed.
Lemma wf_ctx_sq G i Δ l A : lwf (gL G) l -> [ G ; Δ ⊢[ i ] A @ l ] -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tySq l A @ l ⊢[ typeof i ] ].
Proof. intros Hl HA HΔ. apply wfc_ext; [exact HΔ | now apply wft_sq_typeof | exact Hl]. Qed.
#[export] Hint Resolve wf_ctx_sq wft_sq_typeof : wk.
(** [DVec]'s family context (M17a). *)
Lemma wft_fin_typeof G i Δ n : i <> lV -> [ G ; Δ ⊢[ i ] n : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ typeof i ] tyFin n @ lzero ].
Proof.
  intros Hv Hn. apply wft_fin; [destruct i; cbn; congruence | eapply lift_tm; [exact Hn | apply lle_self_typeof]].
Qed.
Lemma wf_ctx_fin G i Δ n : i <> lV -> [ G ; Δ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tyFin n @ lzero ⊢[ typeof i ] ].
Proof. intros Hv Hn HΔ. apply wfc_ext; [exact HΔ | now apply wft_fin_typeof | exact I]. Qed.
Lemma wf_ctx_fin_zero G i Δ : compt i -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tyFin zero @ lzero ⊢[ typeof i ] ].
Proof. intros Hc HΔ. apply wf_ctx_fin; [now apply compt_notV | apply wf_zero; [now apply compt_notV | exact HΔ] | exact HΔ]. Qed.
Lemma wf_ctx_fin_succ G i Δ n : compt i -> [ G ; Δ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ,, tyFin (succ n) @ lzero ⊢[ typeof i ] ].
Proof. intros Hc Hn HΔ. apply wf_ctx_fin; [now apply compt_notV | apply wf_succ; [now apply compt_notV | exact Hn] | exact HΔ]. Qed.
Lemma wft_fin_zero_typeof G i Δ : compt i -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ typeof i ] tyFin zero @ lzero ].
Proof. intros Hc HΔ. apply wft_fin_typeof; [now apply compt_notV | apply wf_zero; [now apply compt_notV | exact HΔ]]. Qed.
Lemma wft_fin_succ_typeof G i Δ n : compt i -> [ G ; Δ ⊢[ i ] n : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ typeof i ] tyFin (succ n) @ lzero ].
Proof. intros Hc Hn. apply wft_fin_typeof; [now apply compt_notV | apply wf_succ; [now apply compt_notV | exact Hn]]. Qed.
#[export] Hint Resolve wft_fin_typeof wft_fin_zero_typeof wft_fin_succ_typeof
  wf_ctx_fin wf_ctx_fin_zero wf_ctx_fin_succ : wk.
(** [DVec]'s successor, at a reduct spelled up to syntax (its renamed tail). *)
Lemma eqty_dvec_succ' G i Γ l n F T : compt i -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin (succ n) @ lzero ⊢[ i ] F @ l ] -> tySig l l (dvecHd n F) (dvecTl l n F) = T ->
  [ G ; Γ ⊢[ i ] tyDVec l (succ n) F ≅ T @ l ].
Proof. intros ? ? ? ? <-. now apply eqty_dvec_succ. Qed.
#[export] Hint Extern 3 (lwf _ (lmax _ _)) => (cbn; split; eauto using lequiv_wf_l, lequiv_wf_r) : wk.
(** A computing layer sees layer-C definitions (M9). *)
Lemma compt_lle_C i : compt i -> lle lC i.
Proof. intros [-> | ->]; unfold lle; cbn; lia. Qed.
#[export] Hint Resolve compt_lle_C : wk.

(* twice: [case]'s branch types (M12b) shift summands inside an injection *)
Ltac wk_eq := push_ren; wk_rewrite; push_ren; wk_rewrite; push_ren; reflexivity.

(** One premise: directly, or through an induction hypothesis up to a type equation. *)
Ltac wk_premise :=
  fix_layer;
  first [ solve [eauto 8 with wk]
        | solve [eapply wf_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with wk] end | wk_eq]]
        | solve [eapply eq_tm_retype;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with wk] end | wk_eq]]
        (* the recursors' motive instances (M3_DESIGN.md E10) *)
        | solve [eapply wf_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with wk] end | wk_eq]]
        | solve [eapply eq_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with wk] end | wk_eq | wk_eq]]
        (* [J]'s motive (M11a): its context's [Id] type commutes by an equation *)
        | solve [eapply wf_ty_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with wk] end | wk_eq]]
        | solve [eapply eq_ty_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 12 with wk] end | wk_eq]] ].

(** The lookup-typed local substitution of [u^δ]/[U^δ]: its entries are
    renamed, and its target context [Δ] is untouched. *)
Ltac wk_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin; rewrite !llk_lren;
  rewrite <- (subst_ren_ty A _ _ _ (fun m => llk_lren _ _ m));
  match goal with IH : forall n A k (_ : in_ctx _ n A k), _ |- _ => eapply (IH n A k Hin) end;
  eauto with wk.

(** The letbox body: weaken [Γ⟪↑⟫] under [Ψ, U]. *)
Ltac wk_body :=
  match goal with
  | IH : forall Δ' r', wkr r' Δ' (?Γ⟪S⟫) -> wf_ctx (gext ?G ?D) _ Δ' -> _,
    Hr : wkr ?r ?Δ ?Γ, HΔ : wf_ctx ?G _ ?Δ |- _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext G D ])
        by (unfold gext; first [eapply wfg_ty | eapply wfg_tm];
            first [exact (ctx_glob _ _ _ HΔ) | eassumption | left; reflexivity | right; reflexivity
                  | cbn; eassumption | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption]);
      assert (X : [ gext G D ; Δ⟪S⟫ ⊢[ lM ] ]);
      [ exact (proj1 (proj2 gweakening) _ _ _ HΔ _ (D :: gΨ G) (gwk_step gwk_id) (le_n _)
                 (gwkwf_step _ _ _ _ (gwkwf_id _)) Hg)
      | pose proof (IH _ _ (wkr_gren _ _ _ S Hr) X) as X';
        rewrite single_ren_ty, <- gren_ren_ty', ?ren_boxT, ?ren_boxt in X'; exact X' ]
  end.

(** ** The recursors' scopes of a weakened context *)

Definition gwk_stepn (n : nat) : gweak := Nat.iter n gwk_step gwk_id.
Lemma gwk_stepn_fn n i : gwk_fn (gwk_stepn n) i = n + i.
Proof. induction n; cbn; auto. Qed.
Lemma gwk_stepn_wf Ds Ψ : gwk_wf (gwk_stepn (length Ds)) (Ds ++ Ψ) Ψ.
Proof. induction Ds; cbn; constructor; auto. Qed.

(** [Δ] at [n] fresh levels and under [ng] fresh global bindings [Ds]. *)
Lemma wf_wkc G i Δ nu Ds : [ G ; Δ ⊢[ i ] ] ->
  [ ⊢ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ] ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ; wkc nu (length Ds) Δ ⊢[ i ] ].
Proof.
  intros HΔ HG.
  pose proof (proj1 (proj2 usubstitution) _ _ _ HΔ (nu + gL G) _ (usub_ok_ush nu (gL G))) as X.
  rewrite <- gctx_uwk_as in X.
  rewrite <- (proj1 (proj2 (proj2 uren_as_usubst_all)) Δ (ush nu)) in X by reflexivity.
  pose proof (proj1 (proj2 gweakening) _ _ _ X _ _ _ (le_n _) (gwk_stepn_wf Ds _) HG) as Y.
  unfold wkc. rewrite (proj1 (proj2 (proj2 gren_ext_all)) _ (ush (length Ds)) (gwk_fn (gwk_stepn (length Ds)))).
  - exact Y.
  - intros; now rewrite gwk_stepn_fn.
Qed.

Lemma wf_wkc_br G Δ k : k < nbr -> [ G ; Δ ⊢[ lM ] ] -> [ brG k G ; wkc (br_nu k) (br_ng k) Δ ⊢[ lM ] ].
Proof.
  intros Hk HΔ. pose proof (wf_brG (ctx_glob _ _ _ HΔ) k Hk) as HG.
  rewrite <- (brDecls_len k Hk). apply (wf_wkc _ _ _ _ (brDecls k) HΔ HG).
Qed.

Lemma wf_recΓT G Δ : [ G ; Δ ⊢[ lM ] ] -> [ recGT G ; recΓT Δ ⊢[ lM ] ].
Proof.
  intros HΔ. pose proof (wf_recGT (ctx_glob _ _ _ HΔ)) as HG.
  unfold recΓT. apply wfc_ext; [ | | exact I].
  - apply (wf_wkc _ _ _ 1 (gdCtx :: nil) HΔ HG).
  - apply wft_CTyp; [apply (wf_wkc _ _ _ 1 (gdCtx :: nil) HΔ HG) | apply wfc_var; [exact HG | reflexivity]
                    | cbn; lia].
Qed.

Lemma wf_recΓt G Δ : [ G ; Δ ⊢[ lM ] ] -> [ recGt G ; recΓt Δ ⊢[ lM ] ].
Proof.
  intros HΔ. pose proof (wf_recGt (ctx_glob _ _ _ HΔ)) as HG.
  assert (HΔ' : [ recGt G ; wkc 1 2 Δ ⊢[ lM ] ]) by apply (wf_wkc _ _ _ 1 (_ :: gdCtx :: nil) HΔ HG).
  unfold recΓt. apply wfc_ext; [exact HΔ' | | exact I].
  apply wft_CTrm; [exact HΔ' | apply wfc_var; [exact HG | reflexivity] | | cbn; lia].
  eapply wf_gv; [discriminate | apply wfc_var; [exact HG | reflexivity] | glookup | unfold lle; cbn; lia | reflexivity].
Qed.

Lemma wkr_recΓT r Δ Γ : wkr r Δ Γ -> wkr (rlift r) (recΓT Δ) (recΓT Γ).
Proof. intros H; unfold recΓT. apply wkr_up'; [exact (wkr_wkc _ _ _ 1 1 H) | reflexivity]. Qed.
Lemma wkr_recΓt r Δ Γ : wkr r Δ Γ -> wkr (rlift r) (recΓt Δ) (recΓt Γ).
Proof. intros H; unfold recΓt. apply wkr_up'; [exact (wkr_wkc _ _ _ 1 2 H) | reflexivity]. Qed.

Lemma wkr_brΓ k r Δ Γ wT wt l1 l2 : k < nbr -> wkr r Δ Γ ->
  wkr (rliftn (br_nl k) r) (brΓ k Δ wT⟨r⟩ wt⟨r⟩ l1 l2) (brΓ k Γ wT wt l1 l2).
Proof.
  intros Hk H. unfold brΓ.
  rewrite <- (brLocs_len k wT wt (lvren l1 (ush (br_nu k))) (lvren l2 (ush (br_nu k))) Hk).
  rewrite <- brLocs_ren by exact Hk. apply wkr_cexts, wkr_wkc, H.
Qed.

(** The meta-functions' bodies (M5): under the global binder, as letbox's. *)
Ltac wk_gbody :=
  match goal with
  | IH : forall Δ' r', wkr r' Δ' (?Γ⟪S⟫) -> wf_ctx (gext ?G ?D) _ Δ' -> _,
    Hr : wkr ?r ?Δ ?Γ, HΔ : wf_ctx ?G _ ?Δ |- _ =>
      let X := fresh "X" in let Hg := fresh "Hg" in
      assert (Hg : [ ⊢ gext G D ])
        by (unfold gext; first [eapply wfg_ctx | eapply wfg_ty | eapply wfg_tm];
            first [exact (ctx_glob _ _ _ HΔ) | eassumption | left; reflexivity | right; reflexivity
                  | cbn; eassumption | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption]);
      assert (X : [ gext G D ; Δ⟪S⟫ ⊢[ lM ] ]);
      [ exact (proj1 (proj2 gweakening) _ _ _ HΔ _ (D :: gΨ G) (gwk_step gwk_id) (le_n _)
                 (gwkwf_step _ _ _ _ (gwkwf_id _)) Hg)
      | exact (IH _ _ (wkr_gren _ _ _ S Hr) X) ]
  end.

(** The recursors' premises: motives under [⇑r], branch contexts and
    branches under [⇑ⁿr]. *)
Ltac wk_motive :=
  match goal with
  | IH : forall Δ r, wkr r Δ (recΓT ?Γ) -> _ -> _, Hr : wkr ?r ?Δ ?Γ, HΔ : wf_ctx _ _ ?Δ |- _ =>
      apply IH; [apply wkr_recΓT, Hr | apply wf_recΓT, HΔ]
  | IH : forall Δ r, wkr r Δ (recΓt ?Γ) -> _ -> _, Hr : wkr ?r ?Δ ?Γ, HΔ : wf_ctx _ _ ?Δ |- _ =>
      apply IH; [apply wkr_recΓt, Hr | apply wf_recΓt, HΔ]
  end.
Ltac wk_brctx :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
  match goal with
  | IH : forall k, k < nbr -> forall Γ0 As, brΓ k ?Γ ?wT ?wt ?l1 ?l2 = cexts Γ0 As -> _,
    Hr : wkr ?r ?Δ ?Γ, HΔ : wf_ctx _ _ ?Δ |- _ =>
      let X := fresh "X" in
      pose proof (IH k Hk _ _ eq_refl _ _ (wkr_wkc _ _ _ (br_nu k) (br_ng k) Hr) (wf_wkc_br _ _ k Hk HΔ)) as X;
      rewrite brLocs_ren in X by exact Hk; exact X
  end.
Ltac wk_branches :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
  match goal with
  | IH : forall k, k < nbr -> forall Δ r, wkr r Δ (brΓ k ?Γ ?wT ?wt ?l1 ?l2) -> _ -> _,
    IHc : forall k, k < nbr -> forall Γ0 As, brΓ k ?Γ ?wT ?wt ?l1 ?l2 = cexts Γ0 As -> _,
    Hr : wkr ?r ?Δ ?Γ, HΔ : wf_ctx _ _ ?Δ |- _ =>
      let X := fresh "X" in let C := fresh "C" in
      pose proof (IHc k Hk _ _ eq_refl _ _ (wkr_wkc _ _ _ (br_nu k) (br_ng k) Hr) (wf_wkc_br _ _ k Hk HΔ)) as C;
      rewrite brLocs_ren in C by exact Hk;
      pose proof (IH k Hk _ _ (wkr_brΓ k _ _ _ wT wt l1 l2 Hk Hr) C) as X;
      rewrite brRes_ren in X by exact Hk; exact X
  end.

(** [UΠ]'s body: the same renaming at the universe-weakened scope. *)
Ltac wk_upi_body :=
  match goal with
  | IH : forall Δ r, wkr r Δ _ -> wf_ctx (gctx_uwk ?n ?G) _ Δ -> _,
    Hr : wkr ?r ?Δ ?Γ, HΔ : wf_ctx ?G _ ?Δ |- _ =>
      apply IH; [apply wkr_uren, Hr | apply uwk_ctx, HΔ]
  end.

(** [J]'s motive (M11a): under the induction hypothesis its context holds the
    weakened [Id] premise's type, which is the rule's only up to an equation. *)
Ltac wk_Jmot :=
  first [eapply wf_ty_regctx | eapply eq_ty_regctx];
  [ match goal with
    | IH : forall Δ r, wkr r Δ (_ ,, _ @ _ ,, _ @ _) -> _ -> _ |- _ =>
        eapply IH; [ solve [eauto 12 with wk] | apply wfc_ext; solve [eauto 12 with wk] ]
    end
  | wk_eq ].

(** [elim_W]'s step (M13a): its context holds the children's and the
    induction hypothesis's types, which commute with the renaming only by an
    equation; so does the step's type. *)
Ltac wk_eqW := do 4 (push_ren; wk_rewrite); push_ren; rlk_simpl; reflexivity.
Ltac wk_Wctx :=
  repeat apply wfc_ext; fix_layer;
  first [ solve [eauto 12 with wk]
        | eapply lift_ty; [ match goal with
                            | IH : forall Δ r, wkr r Δ _ -> _ -> _ |- _ =>
                                eapply IH; [ repeat (eapply wkr_up'; [ | reflexivity]); eassumption | wk_Wctx ]
                            end
                          | apply lle_self_typeof ] ].
Ltac wk_Wstep :=
  first [eapply wf_tm_regctx | eapply eq_tm_regctx | eapply wf_ty_regboth];
  [ match goal with
    | IH : forall Δ r, wkr r Δ (_ ,, _ @ _ ,, _ @ _) -> _ -> _ |- _ =>
        eapply IH; [ repeat (eapply wkr_up'; [ | reflexivity]); eassumption | wk_Wctx ]
    end
  | wk_eqW | wk_eqW ].
(** [elim_Wf]'s motive, over [Wf] (M15a). *)
Ltac wk_Wfmot :=
  match goal with
  | IH : forall Δ r, wkr r Δ (_ ,, tyWf _ _ _ @ _) -> _ -> _ |- _ =>
      eapply IH; [ eapply wkr_up'; [eassumption | reflexivity]
                 | apply wf_ctx_Wf; fix_layer; solve [eauto 12 with wk] ]
  end.
(** Its motive, over [W]. *)
Ltac wk_Wmot :=
  match goal with
  | IH : forall Δ r, wkr r Δ (_ ,, tyW _ _ _ _ @ _) -> _ -> _ |- _ =>
      eapply IH; [ eapply wkr_up'; [eassumption | reflexivity]
                 | apply wf_ctx_W; fix_layer; solve [eauto 12 with wk] ]
  end.

(** [IWf] (M17b): a premise under binders whose types, like its own,
    commute with the renaming only by an equation, closed by congruence
    down to the renamed leaves. *)
Ltac wk_rext :=
  let n := fresh "n" in intros n;
  do 6 try (destruct n as [|n]; rlk_simpl; rewrite ?Nat.add_1_r; try solve [reflexivity | lia]);
  rlk_simpl; rewrite ?Nat.add_1_r; first [reflexivity | lia].
Ltac wk_leaf := first [ reflexivity
  | rewrite ?ren_ren_comp_ty, ?ren_ren_comp; first [apply ren_ext_ty | apply ren_ext_tm]; wk_rext ].
Ltac wk_cong := lazymatch goal with
  | |- ?x = ?y => let h := rhead x in
      lazymatch h with
      | ren_ty => wk_leaf | ren_tm => wk_leaf | @ren => wk_leaf
      | _ => first [reflexivity | f_equal]
      end
  end.
Ltac wk_eqI := push_ren; wk_rewrite; push_ren; wk_rewrite; push_ren; fold_subst; repeat wk_cong.
Ltac wk_Ictx :=
  repeat apply wfc_ext; fix_layer;
  first [ solve [eauto 12 with wk]
        | solve [push_ren; eauto 12 with wk]
        | eapply lift_ty; [ match goal with
                            | IH : forall Δ r, wkr r Δ _ -> _ -> _ |- _ =>
                                eapply IH; [ repeat (eapply wkr_up'; [ | reflexivity]); eassumption | wk_Ictx ]
                            end
                          | apply lle_self_typeof ] ].
Ltac wk_Iprem lem :=
  match goal with
  | IH : forall Δ r, wkr r Δ _ -> _ -> _ |- _ =>
      eapply lem; [ eapply IH; [ repeat (eapply wkr_up'; [ | reflexivity]); eassumption | ] | .. ];
      [ idtac | solve [wk_eqI] .. ]; wk_Ictx
  end.
Ltac wk_I :=
  fix_layer;
  first [ solve [wk_premise]
        | solve [wk_Iprem wf_tm_regctx] | solve [wk_Iprem eq_tm_regctx]
        | solve [wk_Iprem wf_ty_regboth] | solve [wk_Iprem eq_ty_regall]
        | solve [wk_Iprem wf_tm_regtm] ].

Ltac wk_manual :=
  match goal with
  (* [W] (M13a) *)
  | |- wf_tm _ _ _ (tmSup _ _ _ _ _ _) _ _ => eapply wf_sup; wk_premise
  | |- eq_tm _ _ _ (tmSup _ _ _ _ _ _) _ _ _ => eapply eqtm_sup; wk_premise
  | |- wf_tm _ _ _ (tmElimW _ _ _ _ _ _ _ _) _ _ => eapply wf_elimW; first [solve [wk_Wmot] | solve [wk_Wstep] | wk_premise]
  | |- eq_tm _ _ _ (tmElimW _ _ _ _ _ _ _ (tmSup _ _ _ _ _ _)) _ _ _ =>
      eapply eqtm_elimW_sup; first [solve [wk_Wmot] | solve [wk_Wstep] | wk_premise]
  | |- eq_tm _ _ _ (tmElimW _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimW; first [solve [wk_Wmot] | solve [wk_Wstep] | wk_premise]
  (* [Wf] (M15a) *)
  | |- wf_tm _ _ _ (tmSupf _ _ _ _ _) _ _ => eapply wf_supf; wk_premise
  | |- eq_tm _ _ _ (tmSupf _ _ _ _ _) _ _ _ => eapply eqtm_supf; wk_premise
  | |- wf_tm _ _ _ (tmElimWf _ _ _ _ _ _ _) _ _ => eapply wf_elimWf; first [solve [wk_Wfmot] | solve [wk_Wstep] | wk_premise]
  | |- eq_tm _ _ _ (tmElimWf _ _ _ _ _ _ (tmSupf _ _ _ _ _)) _ _ _ =>
      eapply eqtm_elimWf_supf; first [solve [wk_Wfmot] | solve [wk_Wstep] | wk_premise]
  | |- eq_tm _ _ _ (tmElimWf _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimWf; first [solve [wk_Wfmot] | solve [wk_Wstep] | wk_premise]
  (* the codes of [DVec] and [IWf] (M17c) *)
  | |- eq_ty _ _ _ (tyIWf _ _ _ _ _ _ _ _) (tyEl _ _) _ => eapply eqty_El_iwf; wk_I
  | |- eq_ty _ _ _ (tyDVec _ _ _) (tyEl _ _) _ => eapply eqty_El_dvec; wk_I
  | |- wf_tm _ _ _ (tmIWf _ _ _ _ _ _ _ _) _ _ => eapply wf_code_iwf; wk_I
  | |- eq_tm _ _ _ (tmIWf _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_code_iwf; wk_I
  | |- wf_tm _ _ _ (tmDVec _ _ _) _ _ => eapply wf_code_dvec; wk_I
  | |- eq_tm _ _ _ (tmDVec _ _ _) _ _ _ => eapply eqtm_code_dvec; wk_I
  (* [IWf] (M17b) *)
  | |- wf_ty _ _ _ (tyIWf _ _ _ _ _ _ _ _) _ => eapply wft_iwf; wk_I
  | |- eq_ty _ _ _ (tyIWf _ _ _ _ _ _ _ _) _ _ => eapply eqty_iwf; wk_I
  | |- wf_tm _ _ _ (tmSupi _ _ _ _ _ _ _ _ _) _ _ => eapply wf_supi; wk_I
  | |- eq_tm _ _ _ (tmSupi _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_supi; wk_I
  | |- wf_tm _ _ _ (tmElimIWf _ _ _ _ _ _ _ _ _ _ _ _) _ _ => eapply wf_elimIWf; wk_I
  | |- eq_tm _ _ _ (tmElimIWf _ _ _ _ _ _ _ _ _ _ _ (tmSupi _ _ _ _ _ _ _ _ _)) _ _ _ =>
      wk_rewrite; push_ren; eapply eqtm_elimIWf_supi; wk_I
  | |- eq_tm _ _ _ (tmElimIWf _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimIWf; wk_I
  (* [ind_∥∥] (M16a): its step's type, through the induction hypotheses *)
  | |- wf_tm _ _ _ (tmElimSq _ _ _ _ _ _) _ _ => eapply wf_elimSq; wk_premise
  | |- eq_tm _ _ _ (tmElimSq _ _ _ _ _ (tmSq _ _ _)) _ _ _ => eapply eqtm_elimSq_sq; wk_premise
  | |- eq_tm _ _ _ (tmElimSq _ _ _ _ _ _) _ _ _ => eapply eqtm_elimSq; wk_premise
  (* [case] (M12b): its branches' types, through the induction hypotheses *)
  | |- wf_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ _) _ _ => eapply wf_case; wk_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ (tmInl _ _ _ _ _)) _ _ _ => eapply eqtm_case_inl; wk_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ (tmInr _ _ _ _ _)) _ _ _ => eapply eqtm_case_inr; wk_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_case; wk_premise
  (* the identity type (M11a) *)
  | |- wf_tm _ _ _ (tmJ _ _ _ _ _ _ _ _) _ _ => eapply wf_J; first [solve [wk_Jmot] | wk_premise]
  | |- eq_tm _ _ _ (tmJ _ _ _ _ _ _ _ (tmRefl _ _ _)) _ _ _ =>
      eapply eqtm_J_beta; first [solve [wk_Jmot] | wk_premise]
  | |- eq_tm _ _ _ (tmJ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_J; first [solve [wk_Jmot] | wk_premise]
  (* meta-functions (M5) *)
  | |- wf_ty _ _ _ (tyCPi _ _) _ => eapply wft_cpi; try wk_gbody; wk_premise
  | |- wf_ty _ _ _ (tyTPi _ _ _ _) _ => eapply wft_tpi; try wk_gbody; wk_premise
  | |- eq_ty _ _ _ (tyCPi _ _) _ _ => eapply eqty_cpi; try wk_gbody; wk_premise
  | |- eq_ty _ _ _ (tyTPi _ _ _ _) _ _ => eapply eqty_tpi; try wk_gbody; wk_premise
  | |- wf_tm _ _ _ (clam _ _ _) _ _ => eapply wf_clam; try wk_gbody; wk_premise
  | |- wf_tm _ _ _ (tlam _ _ _ _ _) _ _ => eapply wf_tlam; try wk_gbody; wk_premise
  | |- wf_tm _ _ _ (capp _ _) _ _ => eapply wf_capp; try wk_gbody; wk_premise
  | |- wf_tm _ _ _ (tapp _ _) _ _ => eapply wf_tapp; try wk_gbody; wk_premise
  | |- eq_tm _ _ _ (clam _ _ (capp _ _)) _ _ _ => eapply eqtm_ceta; try wk_gbody; wk_premise
  | |- eq_tm _ _ _ (tlam _ _ _ _ (tapp _ _)) _ _ _ => eapply eqtm_teta; try wk_gbody; wk_premise
  | |- eq_tm _ _ _ (clam _ _ _) _ _ _ => eapply eqtm_clam; try wk_gbody; wk_premise
  | |- eq_tm _ _ _ (tlam _ _ _ _ _) _ _ _ => eapply eqtm_tlam; try wk_gbody; wk_premise
  | |- eq_tm _ _ _ (capp (clam _ _ _) _) _ _ _ =>
      rewrite <- gsubst_ren; eapply eqtm_cbeta; try wk_gbody; wk_premise
  | |- eq_tm _ _ _ (tapp (tlam _ _ _ _ _) _) _ _ _ =>
      rewrite <- gsubst_ren; eapply eqtm_tbeta; try wk_gbody; wk_premise
  | |- eq_tm _ _ _ (capp _ _) _ _ _ => eapply eqtm_capp; try wk_gbody; wk_premise
  | |- eq_tm _ _ _ (tapp _ _) _ _ _ => eapply eqtm_tapp; try wk_gbody; wk_premise
  | |- wf_ty _ _ _ (tyUPi _ _ _) _ => eapply wft_upi; try wk_upi_body; wk_premise
  | |- eq_ty _ _ _ (tyUPi _ _ _) _ _ => eapply eqty_upi; try wk_upi_body; wk_premise
  | |- wf_tm _ _ _ (ulam _ _ _ _) _ _ => eapply wf_ulam; try wk_upi_body; wk_premise
  | |- eq_tm _ _ _ (ulam _ _ _ (uapp _ (ubvars _))) _ _ _ => eapply eqtm_ueta; try wk_upi_body; wk_premise
  | |- eq_tm _ _ _ (ulam _ _ _ _) _ _ _ => eapply eqtm_ulam; try wk_upi_body; wk_premise
  | |- wf_tm _ _ _ (uapp _ _) _ _ => eapply wf_uapp; try wk_upi_body; wk_premise
  | |- eq_tm _ _ _ (uapp (ulam _ _ _ _) _) _ _ _ => eapply eqtm_ubeta; try wk_upi_body; wk_premise
  | |- eq_tm _ _ _ (uapp _ _) _ _ _ => eapply eqtm_uapp; try wk_upi_body; wk_premise
  (* dependent tuples (M17a): the tail's index annotation shifts the length *)
  | |- eq_ty _ _ _ (tyDVec _ (succ _) _) (tySig _ _ _ _) _ =>
      eapply eqty_dvec_succ'; [wk_premise .. |];
      repeat (f_equal; try ren_comm); rlk_simpl; reflexivity
  (* dependent pairs (M8) *)
  | |- eq_tm _ _ _ (tmPair _ _ _ _ (tmFst _ _ _ _ _) (tmSnd _ _ _ _ _)) _ _ _ =>
      eapply eqtm_sig_eta; wk_premise
  (* the unit type (M8c) *)
  | |- wf_ty _ _ _ (tyGvar _ _) _ => eapply wft_gvar; [ .. | wk_entries]; eauto with wk
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      eapply eqty_gvar; [ .. | wk_entries | wk_entries | wk_entries]; eauto with wk
  | |- wf_tm _ _ _ (gvar _ _) _ _ =>
      rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m));
      eapply wf_gvar; [ .. | wk_entries]; eauto with wk
  | |- eq_tm _ _ _ (gvar _ _) _ _ _ =>
      rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m));
      eapply eqtm_gvar; [ .. | wk_entries | wk_entries | wk_entries]; eauto with wk
  (* defined globals (M9): the body stays in the definition's context *)
  | |- wf_tm _ _ _ (gdef _ _ _) _ _ =>
      rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m));
      eapply wf_gdef; [ .. | wk_entries | ]; eauto with wk
  | |- eq_tm _ _ _ (gdef _ _ _) (gdef _ _ _) _ _ =>
      rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m));
      eapply eqtm_gdef; [ .. | wk_entries | wk_entries | wk_entries | ]; eauto with wk
  | |- eq_tm _ _ _ (gdef _ _ _) _ _ _ =>
      rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m)), (subst_ren _ _ _ _ (fun m => llk_lren _ _ m));
      eapply eqtm_delta; [ .. | wk_entries | ]; eauto with wk
  | |- wf_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ => eapply wf_letboxT; try wk_body; wk_premise
  | |- wf_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ => eapply wf_letboxt; try wk_body; wk_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ (boxT _)) _ _ _ =>
      rewrite <- gsubst_ren; eapply eqtm_letboxT_beta; try wk_body; wk_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      rewrite <- gsubst_ren; eapply eqtm_letboxt_beta; try wk_body; wk_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxT; try wk_body; wk_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ => eapply eqtm_letboxt; try wk_body; wk_premise
  | |- wf_tm _ _ _ (elimT _ _ _ _ _ _) _ _ =>
      eapply wf_elimT; [ .. | wk_motive | wk_motive | wk_brctx | wk_branches | ]; wk_premise
  | |- wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ =>
      eapply wf_elimt; [ .. | wk_motive | wk_motive | wk_brctx | wk_branches | | ]; wk_premise
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ (boxT _)) _ _ _ =>
      eapply eqtm_elimT_beta; [wk_premise | now apply redT_ren | wk_premise]
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      eapply eqtm_elimt_beta; [wk_premise | now apply redt_ren | wk_premise]
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimT;
      [ .. | wk_motive | wk_motive | wk_motive | wk_motive | wk_motive | wk_motive
           | wk_brctx | wk_brctx | wk_branches | wk_branches | ]; wk_premise
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimt;
      [ .. | wk_motive | wk_motive | wk_motive | wk_motive | wk_motive | wk_motive
           | wk_brctx | wk_brctx | wk_branches | wk_branches | ]; wk_premise

  end.

(** The context cases: a prefix [Γ] of [cexts Γ As] is weakened. *)
Ltac wk_ctx :=
  match goal with
  | Heq : _ = cexts ?Γ0 ?As, Hr : wkr ?r ?Δ ?Γ0, HΔ : wf_ctx _ _ ?Δ |- _ =>
      let As' := fresh "As'" in let A' := fresh "A'" in let l' := fresh "l'" in
      let Θ' := fresh "Θ'" in let Hθ := fresh "Hθ" in
      destruct (cexts_inv _ _ _ (eq_sym Heq)) as [[-> ?] | (As' & A' & l' & Θ' & -> & Hθ & ->)];
      [ cbn; exact HΔ
      | first [ discriminate Hθ
              | let HΓ := fresh "HΓ" in
                injection Hθ as HΓ <- <-; rewrite cexts_ren_snoc, cexts_snoc;
                match goal with
                | IHc : forall Γ As, _ = cexts Γ As -> _, IHt : forall Δ r, wkr r Δ _ -> _ -> _ |- _ =>
                    let X := fresh "X" in
                    pose proof (IHc _ _ HΓ _ _ Hr HΔ) as X;
                    apply wfc_ext; [ exact X
                                   | apply IHt; [ rewrite HΓ; now apply wkr_cexts
                                                | eapply lift_ctx; [exact X | apply lle_self_typeof] ]
                                   | assumption ]
                end ] ]
  end.

Theorem weakening_all :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Θ, [ G ; Θ ⊢[ i ] ] -> forall Γ As, Θ = cexts Γ As ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; cexts Δ (cexts_ren As r) ⊢[ i ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ : T⟨r⟩ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ ≅ T'⟨r⟩ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ ≅ t'⟨r⟩ : T⟨r⟩ @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I; try wk_ctx; cbn [typeof] in *; push_ren; wk_rewrite; push_ren.
  all: try wk_step.
  all: try wk_manual.
  all: any_rule wk_premise.
Qed.

(** The M1 form: layers with [typeof i = i]. *)
Theorem weakening_r :
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ : T⟨r⟩ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] T⟨r⟩ ≅ T'⟨r⟩ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> typeof i = i ->
     forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] t⟨r⟩ ≅ t'⟨r⟩ : T⟨r⟩ @ l ]).
Proof.
  destruct weakening_all as (_ & _ & H1 & H2 & H3 & H4 & _).
  refine (conj _ (conj _ (conj _ _))); intros * H Hi Δ r Hr HΔ; rewrite <- Hi in HΔ; eauto.
Qed.
