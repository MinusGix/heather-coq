(** * The recursors' specification under local substitution

    The syntactic laws [Substitution] uses that need the recursor
    specification but no typing: branch scopes, peels, the reducts and
    [redT]/[redt] commute with local substitution. Split off
    [Substitution] so that they build beside the typing metatheory
    ([Properties]) instead of after it. *)
From DeLaM.Syntax Require Export SubstCommute.
From DeLaM.Typing Require Export RecSpec.

(** ** Global renaming and the global single substitution under local substitution *)

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

(** [exact I] first: conversion reduces only what it must, where a [cbn]
    normalises the whole bundle (85% of [brLocs_subst], tried on every
    side condition of a [rewrite ?motT_subst]). *)
Ltac hd_tac := first [exact I | cbn; exact I].

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
Lemma wkb_subst6 nu ng w d : LK dnftm d ->
  (wkb nu ng 6 w)[llift (llift (llift (llift (llift (llift (gwkn ng (uwkn nu d)))))))] = wkb nu ng 6 w[d].
Proof. exact (wkb_subst nu ng 6 w d). Qed.
Lemma wkb_subst7 nu ng w d : LK dnftm d ->
  (wkb nu ng 7 w)[llift (llift (llift (llift (llift (llift (llift (gwkn ng (uwkn nu d))))))))] = wkb nu ng 7 w[d].
Proof. exact (wkb_subst nu ng 7 w d). Qed.
Lemma wkb_subst8 nu ng w d : LK dnftm d ->
  (wkb nu ng 8 w)[llift (llift (llift (llift (llift (llift (llift (llift (gwkn ng (uwkn nu d)))))))))] = wkb nu ng 8 w[d].
Proof. exact (wkb_subst nu ng 8 w d). Qed.
Lemma wkb_subst9 nu ng w d : LK dnftm d ->
  (wkb nu ng 9 w)[llift (llift (llift (llift (llift (llift (llift (llift (llift (gwkn ng (uwkn nu d))))))))))] = wkb nu ng 9 w[d].
Proof. exact (wkb_subst nu ng 9 w d). Qed.

Fixpoint cexts_sub (As : list (ty * lvl)) (d : lsub) : list (ty * lvl) :=
  match As with nil => nil | cons (A, l) As => cons (A[d], l) (cexts_sub As (llift d)) end.

Ltac rec_subst_rw :=
  rewrite ?motT_subst, ?mott_subst by first [hd_tac | auto 12 with nf];
  rewrite ?wkb_subst0, ?wkb_subst1, ?wkb_subst2, ?wkb_subst3, ?wkb_subst4, ?wkb_subst5, ?wkb_subst6, ?wkb_subst7, ?wkb_subst8, ?wkb_subst9, ?wkb_subst
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
