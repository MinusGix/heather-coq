(** * The recursor specification under global substitution (M3)

    Global substitution commutes with the bundle, peeling, the motive
    instances, the branch scopes and the β reducts, provided the
    substitution's objects are deep-normal ([gdnf]) and the peeled terms
    are not headed by a variable ([hd_ok]; bundles built by [mkrb] satisfy
    this by computation). Mirrors the local-substitution laws of
    [Substitution]. *)
From DeLaM.Typing Require Export Functionality.

Definition gupn (n : nat) (σ : gsub) : gsub := Nat.iter n gup σ.
(** A global substitution moved into branch [k]'s scope. *)
Definition gbsub (k : nat) (σ : gsub) : gsub := gupn (br_ng k) (guwkn (br_nu k) σ).

Definition gdnf (σ : gsub) : Prop := forall i, dnfo (σ i).

(** ** Lookups of the lifted substitutions *)

Lemma goren_id o : dnfo o -> goren o (fun i => i) = o.
Proof.
  destruct o; cbn; intros H; try reflexivity; f_equal.
  all: first [ apply (proj1 (proj2 (proj2 gren_id_all))); auto
             | apply (proj1 gren_id_all); auto
             | apply (proj1 (proj2 gren_id_all)); auto ].
Qed.

Lemma gouren_ush0 o : dnfo o -> gouren o (ush 0) = o.
Proof.
  destruct o; cbn; intros H; try reflexivity; f_equal.
  all: first
    [ rewrite (proj1 (proj2 (proj2 uren_as_usubst_all)) _ _ lvar) by reflexivity;
      apply usubst_id_ctx; auto
    | rewrite (proj1 uren_as_usubst_all _ _ lvar) by reflexivity; apply usubst_id_ty; auto
    | rewrite (proj1 (proj2 uren_as_usubst_all) _ _ lvar) by reflexivity; apply usubst_id; auto ].
Qed.

Lemma guwkn_lk n σ i : dnfo (σ i) -> guwkn n σ i = gouren (σ i) (ush n).
Proof.
  intros H; induction n as [|n IH].
  - symmetry; apply gouren_ush0, H.
  - change (guwkn (S n) σ i) with (gouren (guwkn n σ i) S). rewrite IH.
    apply gouren_gouren; reflexivity.
Qed.

Lemma gupn_ush n τ i : dnfo (τ i) -> gupn n τ (n + i) = goren (τ i) (ush n).
Proof.
  intros H; induction n as [|n IH].
  - symmetry; apply goren_id, H.
  - change (gupn (S n) τ (S n + i)) with (goren (gupn n τ (n + i)) S). rewrite IH.
    apply goren_goren; reflexivity.
Qed.

Lemma gupn_lt n τ i : i < n -> gupn n τ i = GId i.
Proof.
  revert i; induction n as [|n IH]; intros [|i] Hi; try lia; [reflexivity|].
  change (gupn (S n) τ (S i)) with (goren (gupn n τ i) S). rewrite IH by lia; reflexivity.
Qed.

Lemma gdnf_guwk σ : gdnf (guwk σ).
Proof. intros i; apply dnfo_gouren. Qed.
Lemma gdnf_gup σ : gdnf σ -> gdnf (gup σ).
Proof. intros H [|i]; [exact I | apply dnfo_goren]. Qed.
Lemma gdnf_guwkn n σ : gdnf σ -> gdnf (guwkn n σ).
Proof. destruct n; intros H; [exact H | apply gdnf_guwk]. Qed.
Lemma gdnf_gupn n σ : gdnf σ -> gdnf (gupn n σ).
Proof. induction n; intros H; [exact H | apply gdnf_gup, IHn, H]. Qed.
Lemma gdnf_gbsub k σ : gdnf σ -> gdnf (gbsub k σ).
Proof. intros; apply gdnf_gupn, gdnf_guwkn; assumption. Qed.
#[export] Hint Resolve gdnf_guwk gdnf_gup gdnf_guwkn gdnf_gupn gdnf_gbsub : nf.

(** ** The bundle *)

Lemma wrapU_gsubst n b σ : (wrapU n b)⦃σ⦄ = wrapU n b⦃guwkn n σ⦄.
Proof.
  revert σ; induction n; intros σ; cbn [wrapU gsubst GSubst_tm gsubst_tm]; auto.
  change (gsubst_tm (wrapU n b) (guwk σ)) with (wrapU n b)⦃guwk σ⦄. rewrite IHn. do 2 f_equal.
  unfold guwkn; now rewrite <- Nat.iter_succ_r.
Qed.
Lemma wrapG_gsubst n b σ : (wrapG n b)⦃σ⦄ = wrapG n b⦃gupn n σ⦄.
Proof.
  revert σ; induction n; intros σ; cbn [wrapG gsubst GSubst_tm gsubst_tm]; auto.
  change (gsubst_tm (wrapG n b) (gup σ)) with (wrapG n b)⦃gup σ⦄. rewrite IHn. do 2 f_equal.
  unfold gupn; now rewrite <- Nat.iter_succ_r.
Qed.
Lemma wrapL_gsubst n b σ : (wrapL n b)⦃σ⦄ = wrapL n b⦃σ⦄.
Proof. induction n; cbn; congruence. Qed.
Lemma wrap_gsubst nu ng nl b σ :
  (wrap nu ng nl b)⦃σ⦄ = wrap nu ng nl b⦃gupn ng (guwkn nu σ)⦄.
Proof. unfold wrap. now rewrite wrapU_gsubst, wrapG_gsubst, wrapL_gsubst. Qed.

Lemma mkrb_gsubst MT Mt bs σ :
  (mkrb MT Mt bs)⦃σ⦄ = mkrb MT⦃gup (guwk σ)⦄ Mt⦃gup (gup (guwk σ))⦄ (fun k => (bs k)⦃gbsub k σ⦄).
Proof. unfold mkrb. cbn [tup_from gsubst GSubst_tm gsubst_tm br_ar]. rewrite !wrap_gsubst. reflexivity. Qed.
Lemma wrapMT_gsubst MT σ : (wrapMT MT)⦃σ⦄ = wrapMT MT⦃gup (guwk σ)⦄.
Proof. reflexivity. Qed.
Lemma wrapMt_gsubst Mt σ : (wrapMt Mt)⦃σ⦄ = wrapMt Mt⦃gup (gup (guwk σ))⦄.
Proof. reflexivity. Qed.

(** ** Peeling *)

Lemma gs_gsingle (t : tm) o σ : gdnf σ ->
  t⦃gsingle o⦄⦃σ⦄ = t⦃gup σ⦄⦃gsingle (gosubst o σ)⦄.
Proof.
  intros Hσ.
  rewrite (gsubst_gsubst t _ _ (fun i => match i with 0 => gosubst o σ | S i => σ i end)),
          (gsubst_gsubst t _ _ (fun i => match i with 0 => gosubst o σ | S i => σ i end));
    auto; intros [|i]; cbn; auto.
  specialize (Hσ i); destruct (σ i) as [j|G|T|t0]; cbn in *; auto; f_equal.
  - rewrite (proj1 (proj2 (proj2 gsubst_gren_all)) _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id_ctx; auto.
  - rewrite (proj1 gsubst_gren_all _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id_ty; auto.
  - rewrite (proj1 (proj2 gsubst_gren_all) _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id; auto.
Qed.

(** The meta-functions' instances (M5). *)
Lemma gs_gsingle_ty (T : ty) o σ : gdnf σ ->
  T⦃gsingle o⦄⦃σ⦄ = T⦃gup σ⦄⦃gsingle (gosubst o σ)⦄.
Proof.
  intros Hσ.
  rewrite (gsubst_gsubst_ty T _ _ (fun i => match i with 0 => gosubst o σ | S i => σ i end)),
          (gsubst_gsubst_ty T _ _ (fun i => match i with 0 => gosubst o σ | S i => σ i end));
    auto; intros [|i]; cbn; auto.
  specialize (Hσ i); destruct (σ i) as [j|G|T0|t0]; cbn in *; auto; f_equal.
  - rewrite (proj1 (proj2 (proj2 gsubst_gren_all)) _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id_ctx; auto.
  - rewrite (proj1 gsubst_gren_all _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id_ty; auto.
  - rewrite (proj1 (proj2 gsubst_gren_all) _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id; auto.
Qed.

Lemma gs_gsingle_ctx (Γ : ctx) o σ : gdnf σ ->
  Γ⦃gsingle o⦄⦃σ⦄ = Γ⦃gup σ⦄⦃gsingle (gosubst o σ)⦄.
Proof.
  intros Hσ.
  rewrite (gsubst_gsubst_ctx Γ _ _ (fun i => match i with 0 => gosubst o σ | S i => σ i end)),
          (gsubst_gsubst_ctx Γ _ _ (fun i => match i with 0 => gosubst o σ | S i => σ i end));
    auto; intros [|i]; cbn; auto.
  specialize (Hσ i); destruct (σ i) as [j|G|T0|t0]; cbn in *; auto; f_equal.
  - rewrite (proj1 (proj2 (proj2 gsubst_gren_all)) _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id_ctx; auto.
  - rewrite (proj1 gsubst_gren_all _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id_ty; auto.
  - rewrite (proj1 (proj2 gsubst_gren_all) _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id; auto.
Qed.

Lemma gousubst_gouren_single o l : dnfo o -> gousubst (gouren o S) (usingle l) = o.
Proof.
  destruct o; cbn; intros H; try reflexivity; f_equal.
  all: first
    [ rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ lvar) by reflexivity;
      apply usubst_id_ctx; auto
    | rewrite (proj1 uren_usubst_all _ _ _ lvar) by reflexivity; apply usubst_id_ty; auto
    | rewrite (proj1 (proj2 uren_usubst_all) _ _ _ lvar) by reflexivity; apply usubst_id; auto ].
Qed.

Fixpoint gtup_ok (t : tm) : Prop :=
  match t with tmTup _ r => gtup_ok r | gvar _ _ | gdef _ _ _ => False | _ => True end.
Lemma tup_nth_gsubst t k σ : gtup_ok t -> tup_nth t⦃σ⦄ k = (tup_nth t k)⦃σ⦄.
Proof. revert t; induction k; intros [] H; cbn in *; try contradiction; auto. Qed.

Lemma peelU_gsubst b l σ : hd_ok b -> gdnf σ -> peelU b⦃σ⦄ l = (peelU b l)⦃σ⦄.
Proof.
  intros Hb Hσ. destruct b; cbn [peelU gsubst GSubst_tm gsubst_tm]; try contradiction; auto.
  rewrite (proj1 (proj2 usubst_gsubst_all) _ _ _ σ); [reflexivity|].
  intros i; symmetry; apply gousubst_gouren_single, Hσ.
Qed.
Lemma peelG_gsubst b o σ : hd_ok b -> gdnf σ -> peelG b⦃σ⦄ (gosubst o σ) = (peelG b o)⦃σ⦄.
Proof.
  intros Hb Hσ. destruct b; cbn [peelG gsubst GSubst_tm gsubst_tm]; try contradiction; auto.
  symmetry; apply gs_gsingle, Hσ.
Qed.
Lemma peelL_gsubst b a σ : hd_ok b -> peelL b⦃σ⦄ a⦃σ⦄ = (peelL b a)⦃σ⦄.
Proof.
  intros Hb. destruct b; cbn [peelL gsubst GSubst_tm gsubst_tm]; try contradiction; auto.
  symmetry; rewrite gsubst_subst; reflexivity.
Qed.
Lemma getTy_gsubst t σ : hd_ok t -> (getTy t)⦃σ⦄ = getTy t⦃σ⦄.
Proof. destruct t; cbn; try contradiction; reflexivity. Qed.

Lemma motT_gsubst w lv g c σ : hd_ok w -> hd_ok (peelU w lv) -> hd_ok (peelG (peelU w lv) (GCtx g)) ->
  hd_ok (peelL (peelG (peelU w lv) (GCtx g)) c) ->
  gdnf σ -> (motT w lv g c)⦃σ⦄ = motT w⦃σ⦄ lv g⦃σ⦄ c⦃σ⦄.
Proof.
  intros H1 H2 H3 H4 Hσ. unfold motT.
  rewrite getTy_gsubst, <- peelL_gsubst by auto.
  rewrite <- peelG_gsubst, <- peelU_gsubst by auto. reflexivity.
Qed.
Lemma mott_gsubst w lv g U c σ : hd_ok w -> hd_ok (peelU w lv) -> hd_ok (peelG (peelU w lv) (GCtx g)) ->
  hd_ok (peelG (peelG (peelU w lv) (GCtx g)) (GTy U)) ->
  hd_ok (peelL (peelG (peelG (peelU w lv) (GCtx g)) (GTy U)) c) ->
  gdnf σ -> (mott w lv g U c)⦃σ⦄ = mott w⦃σ⦄ lv g⦃σ⦄ U⦃σ⦄ c⦃σ⦄.
Proof.
  intros H1 H2 H3 H4 H5 Hσ. unfold mott.
  rewrite getTy_gsubst, <- peelL_gsubst by auto.
  rewrite <- !peelG_gsubst, <- peelU_gsubst by auto. reflexivity.
Qed.

(** ** The branch scopes *)

Lemma wkb_gsubst nu ng nl w σ : gdnf σ ->
  (wkb nu ng nl w)⦃gupn ng (guwkn nu σ)⦄ = wkb nu ng nl w⦃σ⦄.
Proof.
  intros Hσ. unfold wkb. cbn [gsubst GSubst_tm]. rewrite gsubst_ren_tm. f_equal.
  rewrite (proj1 (proj2 gsubst_gren_all) _ _ _ (fun i => goren (guwkn nu σ i) (ush ng)))
    by (intros i; symmetry; apply gupn_ush, gdnf_guwkn, Hσ).
  rewrite <- (proj1 (proj2 gren_gsubst_all) _ _ _ _ (fun _ => eq_refl)). f_equal.
  symmetry; apply (proj1 (proj2 uren_gsubst_all)). intros i; apply guwkn_lk, Hσ.
Qed.

Lemma wkc_gsubst nu ng Γ σ : gdnf σ -> (wkc nu ng Γ)⦃gupn ng (guwkn nu σ)⦄ = wkc nu ng Γ⦃σ⦄.
Proof.
  intros Hσ. unfold wkc. cbn [gsubst GSubst_ctx].
  rewrite (proj1 (proj2 (proj2 gsubst_gren_all)) _ _ _ (fun i => goren (guwkn nu σ i) (ush ng)))
    by (intros i; symmetry; apply gupn_ush, gdnf_guwkn, Hσ).
  rewrite <- (proj1 (proj2 (proj2 gren_gsubst_all)) _ _ _ _ (fun _ => eq_refl)). f_equal.
  symmetry; apply (proj1 (proj2 (proj2 uren_gsubst_all))). intros i; apply guwkn_lk, Hσ.
Qed.

Lemma cexts_gsubst Γ As σ :
  (cexts Γ As)⦃σ⦄ = cexts Γ⦃σ⦄ (map (fun '(A, l) => (A⦃σ⦄, l)) As).
Proof. revert Γ; induction As as [|[A l] As IH]; intros Γ; cbn; auto. Qed.

Ltac rec_gsubst_rw Hσ :=
  rewrite ?motT_gsubst, ?mott_gsubst by first [hd_tac | exact Hσ];
  rewrite ?wkb_gsubst by exact Hσ.

Lemma brLocs_gsubst k MT Mt a1 a2 σ : k < nbr -> gdnf σ ->
  map (fun '(A, l) => (A⦃gbsub k σ⦄, l)) (brLocs k (wrapMT MT) (wrapMt Mt) a1 a2) =
  brLocs k (wrapMT MT)⦃σ⦄ (wrapMt Mt)⦃σ⦄ a1 a2.
Proof.
  intros Hk Hσ. pose proof (gdnf_gbsub k σ Hσ) as Hb. unfold gbsub in Hb |- *.
  br_all ltac:(destruct k; [cbn [brLocs map br_ng br_nu br_ar mkLocs call_ty call_lv br_calls] in Hb |- *; rec_gsubst_rw Hb;
                      rewrite ?wkb_gsubst by exact Hσ; reflexivity|]).
  lia.
Qed.

Lemma brΓ_gsubst k Γ MT Mt l1 l2 σ : k < nbr -> gdnf σ ->
  (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)⦃gbsub k σ⦄ =
  brΓ k Γ⦃σ⦄ (wrapMT MT)⦃σ⦄ (wrapMt Mt)⦃σ⦄ l1 l2.
Proof.
  intros Hk Hσ. unfold brΓ. rewrite cexts_gsubst, brLocs_gsubst by assumption.
  unfold gbsub; rewrite wkc_gsubst by exact Hσ. reflexivity.
Qed.

Lemma brRes_gsubst k MT Mt σ : k < nbr -> gdnf σ ->
  (brRes k (wrapMT MT) (wrapMt Mt))⦃gbsub k σ⦄ = brRes k (wrapMT MT)⦃σ⦄ (wrapMt Mt)⦃σ⦄.
Proof.
  intros Hk Hσ. pose proof (gdnf_gbsub k σ Hσ) as Hb. unfold gbsub in Hb |- *.
  br_all ltac:(destruct k; [cbn [brRes br_ng br_nu br_ar call_ty br_head br_nl] in Hb |- *; rec_gsubst_rw Hb;
                      rewrite ?wkb_gsubst by exact Hσ; reflexivity|]).
  lia.
Qed.

Lemma recΓT_gsubst Γ σ : gdnf σ -> (recΓT Γ)⦃gup (guwk σ)⦄ = recΓT Γ⦃σ⦄.
Proof. intros Hσ. unfold recΓT. cbn [gsubst GSubst_ctx gcsubst]. now rewrite (wkc_gsubst 1 1). Qed.
Lemma recΓt_gsubst Γ σ : gdnf σ -> (recΓt Γ)⦃gup (gup (guwk σ))⦄ = recΓt Γ⦃σ⦄.
Proof.
  intros Hσ. unfold recΓt. cbn [gsubst GSubst_ctx gcsubst].
  change (gup (gup (guwk σ))) with (gupn 2 (guwkn 1 σ)). now rewrite (wkc_gsubst 1 2).
Qed.

(** ** The reducts *)

Lemma gs_single_ty' (M : ty) a σ : (subst_ty M (lsingle a))⦃σ⦄ = subst_ty M⦃σ⦄ (lsingle a⦃σ⦄).
Proof. change (subst_ty M (lsingle a)) with M[lsingle a]. rewrite gsubst_subst_ty; reflexivity. Qed.
Lemma gs_lsucc_ty' (M : ty) σ : (subst_ty M lsucc)⦃σ⦄ = subst_ty M⦃σ⦄ lsucc.
Proof. change (subst_ty M lsucc) with M[lsucc]. rewrite gsubst_subst_ty; reflexivity. Qed.

Lemma gs_single2_ty' (M : ty) t q σ :
  (subst_ty M (lsingle2 t q))⦃σ⦄ = subst_ty M⦃σ⦄ (lsingle2 t⦃σ⦄ q⦃σ⦄).
Proof. change (subst_ty M (lsingle2 t q)) with M[lsingle2 t q]. rewrite gsubst_subst_ty; reflexivity. Qed.
Lemma gs_shift_ty' (A : ty) σ : (A⟨↑⟩)⦃σ⦄ = (A⦃σ⦄)⟨↑⟩.
Proof. apply gsubst_ren_ty. Qed.
Lemma gs_shift' (t : tm) σ : (t⟨↑⟩)⦃σ⦄ = (t⦃σ⦄)⟨↑⟩.
Proof. apply gsubst_ren. Qed.
(** [case]'s branch types (M12c): the motive lifted past the payload. *)
Lemma gs_liftshift_ty' (A : ty) σ : (A⟨rlift ↑⟩)⦃σ⦄ = (A⦃σ⦄)⟨rlift ↑⟩.
Proof. apply gsubst_ren_ty. Qed.
Lemma gs_case_inl_ty' (M A B : ty) l l' σ :
  (subst_ty M⟨rlift ↑⟩ (lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))))⦃σ⦄
  = subst_ty M⦃σ⦄⟨rlift ↑⟩ (lsingle (tmInl l l' A⦃σ⦄⟨↑⟩ B⦃σ⦄⟨↑⟩ (var 0))).
Proof.
  rewrite gs_single_ty', gs_liftshift_ty'. f_equal. f_equal.
  change ((tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))⦃σ⦄) with (tmInl l l' (A⟨↑⟩)⦃σ⦄ (B⟨↑⟩)⦃σ⦄ (var 0)).
  now rewrite !gs_shift_ty'.
Qed.
(** [ind_∥∥]'s step type (M16b), under the squash. *)
Lemma gs_sq_step_ty' (M A : ty) l σ :
  (subst_ty M⟨rlift ↑⟩ (lsingle (tmSq l A⟨↑⟩ (var 0))))⦃σ⦄
  = subst_ty M⦃σ⦄⟨rlift ↑⟩ (lsingle (tmSq l A⦃σ⦄⟨↑⟩ (var 0))).
Proof.
  rewrite gs_single_ty', gs_liftshift_ty'. f_equal. f_equal.
  change ((tmSq l A⟨↑⟩ (var 0))⦃σ⦄) with (tmSq l (A⟨↑⟩)⦃σ⦄ (var 0)).
  now rewrite !gs_shift_ty'.
Qed.
Lemma gs_case_inr_ty' (M A B : ty) l l' σ :
  (subst_ty M⟨rlift ↑⟩ (lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))))⦃σ⦄
  = subst_ty M⦃σ⦄⟨rlift ↑⟩ (lsingle (tmInr l l' A⦃σ⦄⟨↑⟩ B⦃σ⦄⟨↑⟩ (var 0))).
Proof.
  rewrite gs_single_ty', gs_liftshift_ty'. f_equal. f_equal.
  change ((tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))⦃σ⦄) with (tmInr l l' (A⟨↑⟩)⦃σ⦄ (B⟨↑⟩)⦃σ⦄ (var 0)).
  now rewrite !gs_shift_ty'.
Qed.

(** [elimW]'s step telescope (M13b): the raw forms [cbn] leaves under the
    payload binders. *)
Lemma gs_ren_ty_raw (A : ty) r σ : gsubst_ty (ren_ty A r) σ = ren_ty (gsubst_ty A σ) r.
Proof. apply gsubst_ren_ty. Qed.
Lemma gs_ren_tm_raw (t : tm) r σ : gsubst_tm (ren_tm t r) σ = ren_tm (gsubst_tm t σ) r.
Proof. apply gsubst_ren. Qed.
(** [sup_f]'s children's length and [elim_Wf]'s step telescope (M15b). *)
Lemma gs_tm_subst_raw (t : tm) d σ : gsubst_tm (subst_tm t d) σ = subst_tm (gsubst_tm t σ) (glsubst d σ).
Proof. exact (gsubst_subst t d σ). Qed.
Lemma gs_ty_subst_raw (T : ty) d σ : gsubst_ty (subst_ty T d) σ = subst_ty (gsubst_ty T σ) (glsubst d σ).
Proof. exact (gsubst_subst_ty T d σ). Qed.
Lemma gs_tmNth_raw l T k cs i σ :
  gsubst_tm (tmNth l T k cs i) σ = tmNth l (gsubst_ty T σ) (gsubst_tm k σ) (gsubst_tm cs σ) (gsubst_tm i σ).
Proof.
  unfold tmNth, nthMot, nthBase, nthStep. cbn [gsubst GSubst_tm GSubst_ty gsubst_tm gsubst_ty].
  change (gsubst_tm ?x ?σ) with x⦃σ⦄; change (gsubst_ty ?x ?σ) with x⦃σ⦄.
  repeat rewrite ?gsubst_ren_ty, ?gsubst_ren. reflexivity.
Qed.

(** [sup_i]'s children's family and [elim_IWf]'s step telescope (M17c). *)
Lemma gs_llift_single_raw (b a : tm) σ :
  gsubst_tm (subst_tm b (llift (lsingle a))) σ = subst_tm (gsubst_tm b σ) (llift (lsingle (gsubst_tm a σ))).
Proof.
  rewrite gs_tm_subst_raw. apply subst_ext; intros [|[|n]]; rewrite ?llk_glsubst, ?llk_llift; cbn; auto.
  apply gsubst_ren.
Qed.
Lemma gs_single_tm_raw (b a : tm) σ :
  gsubst_tm (subst_tm b (lsingle a)) σ = subst_tm (gsubst_tm b σ) (lsingle (gsubst_tm a σ)).
Proof. rewrite gs_tm_subst_raw. apply subst_ext; intros [|n]; rewrite llk_glsubst; reflexivity. Qed.
Lemma gs_single_ty_raw (M : ty) a σ :
  gsubst_ty (subst_ty M (lsingle a)) σ = subst_ty (gsubst_ty M σ) (lsingle (gsubst_tm a σ)).
Proof. rewrite gs_ty_subst_raw. apply subst_ext_ty; intros [|n]; rewrite llk_glsubst; reflexivity. Qed.
Lemma gs_tmDNth_raw l n F cs i σ :
  gsubst_tm (tmDNth l n F cs i) σ = tmDNth l (gsubst_tm n σ) (gsubst_ty F σ) (gsubst_tm cs σ) (gsubst_tm i σ).
Proof.
  unfold tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS.
  repeat progress (cbn [glsubst lsingle gsubst GSubst_tm GSubst_ty gsubst_tm gsubst_ty]; fold gsubst_ty gsubst_tm;
    rewrite ?gs_ty_subst_raw, ?gs_tm_subst_raw, ?gs_ren_ty_raw, ?gs_ren_tm_raw).
  reflexivity.
Qed.
Lemma gs_iwfFam_raw l li X A N Ot C a σ :
  gsubst_ty (iwfFam l li X A N Ot C a) σ =
  iwfFam l li (gsubst_ty X σ) (gsubst_ty A σ) (gsubst_tm N σ) (gsubst_tm Ot σ) (gsubst_tm C σ) (gsubst_tm a σ).
Proof.
  unfold iwfFam. cbn [gsubst_ty]. fold gsubst_ty gsubst_tm.
  rewrite ?gs_llift_single_raw.
  change (gsubst_tm ?x ?σ0) with x⦃σ0⦄; change (gsubst_ty ?x ?σ0) with x⦃σ0⦄.
  repeat rewrite ?gsubst_ren_ty, ?gsubst_ren. reflexivity.
Qed.

Ltac gpeel_push Hσ :=
  repeat first [ rewrite <- peelL_gsubst by hd_tac
               | rewrite <- peelG_gsubst by first [hd_tac | exact Hσ]
               | rewrite <- peelU_gsubst by first [hd_tac | exact Hσ] ];
  unfold rb_br; rewrite tup_nth_gsubst by hd_tac;
  cbn [gosubst gsubst GSubst_tm GSubst_ty GSubst_ctx gsubst_tm gsubst_ty gcsubst recT rect]; fold gsubst_ty gsubst_tm gcsubst glsubst;
  (* [case]'s branch types (M12c), before the generic single substitution *)
  try match goal with |- context [tmInl _ _ _ _ (var 0)] => rewrite ?gs_case_inl_ty', ?gs_case_inr_ty' end;
  try match goal with |- context [tmSq _ _ (var 0)] => rewrite ?gs_sq_step_ty' end;
  rewrite ?gs_single_ty', ?gs_lsucc_ty', ?gs_single2_ty', ?gs_shift_ty', ?gs_shift';
  try match goal with |- context [tmSup _ _ _ _ (var 2) (var 1)] =>
    repeat progress (cbn [gsubst GSubst_tm GSubst_ty gsubst_tm gsubst_ty]; fold gsubst_ty gsubst_tm gcsubst glsubst;
      rewrite ?gsubst_ren_ty, ?gsubst_ren, ?gs_ren_ty_raw, ?gs_ren_tm_raw) end;
  try match goal with |- context [tmSupf _ _ _ (var 2) (var 1)] =>
    repeat progress (cbn [glsubst lsingle gsubst GSubst_tm GSubst_ty gsubst_tm gsubst_ty]; fold gsubst_ty gsubst_tm gcsubst glsubst;
      rewrite ?gs_ty_subst_raw, ?gs_tm_subst_raw, ?gs_tmNth_raw, ?gsubst_ren_ty, ?gsubst_ren, ?gs_ren_ty_raw, ?gs_ren_tm_raw) end;
  try (lazymatch goal with
       | |- context [iwfFam _ _ _ _ _ _ _ _] => idtac
       | |- context [tmDNth _ _ _ _ _] => idtac
       end;
    repeat progress (cbn [lsingle2 gsubst GSubst_tm GSubst_ty gsubst_tm gsubst_ty]; fold gsubst_ty gsubst_tm gcsubst glsubst;
      rewrite ?gs_iwfFam_raw, ?gs_tmDNth_raw, ?gs_single_tm_raw, ?gs_single_ty_raw, ?gs_llift_single_raw,
        ?gsubst_ren_ty, ?gsubst_ren, ?gs_ren_ty_raw, ?gs_ren_tm_raw));
  rewrite ?gs_tm_subst_raw; cbn [glsubst lsingle];
  reflexivity.

Lemma redT_gsubst l1 l2 MT Mt bs l Δ c v σ : gdnf σ ->
  redT l1 l2 (mkrb MT Mt bs) l Δ c = Some v ->
  redT l1 l2 (mkrb MT Mt bs)⦃σ⦄ l Δ⦃σ⦄ c⦃σ⦄ = Some v⦃σ⦄.
Proof.
  intros Hσ E. pose proof E as E0. apply (f_equal (option_map (fun x => x⦃σ⦄))) in E.
  cbn [option_map] in E. rewrite <- E. clear E.
  destruct c; cbn [redT] in E0; try discriminate E0;
    cbn [redT option_map gsubst GSubst_ty gsubst_ty]; fold gsubst_ty gsubst_tm gcsubst glsubst; f_equal; gpeel_push Hσ.
Qed.
Lemma redt_gsubst l1 l2 MT Mt bs l Δ T c v σ : gdnf σ ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T c = Some v ->
  redt l1 l2 (mkrb MT Mt bs)⦃σ⦄ l Δ⦃σ⦄ T⦃σ⦄ c⦃σ⦄ = Some v⦃σ⦄.
Proof.
  intros Hσ E. pose proof E as E0. apply (f_equal (option_map (fun x => x⦃σ⦄))) in E.
  cbn [option_map] in E. rewrite <- E. clear E.
  destruct c; cbn [redt] in E0; redt_case T; try discriminate E0;
    cbn [redt option_map gsubst GSubst_tm GSubst_ty gsubst_tm gsubst_ty]; fold gsubst_ty gsubst_tm gcsubst glsubst; f_equal; gpeel_push Hσ.
Qed.
