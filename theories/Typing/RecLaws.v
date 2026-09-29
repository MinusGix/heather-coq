(** * The recursor specification under the syntactic operations (M3)

    For each operation, the bundle ([mkrb]), the peeling of binders, the
    motive instances ([motT]/[mott]), the ambient weakening [wkb], the
    branch scopes ([brG], [brΓ], [brRes], [brLv]) and the reducts
    ([redT]/[redt]) commute with it, the operation being lifted past the
    branch's binders. The branch declarations mention only branch-bound
    variables, so the lifted operations fix them by computation. *)
From DeLaM.Typing Require Export Declarative.

(** ** Iterated lifts *)


Lemma uupn_S n φ : uupn (S n) φ = uup (uupn n φ).
Proof. reflexivity. Qed.
Lemma uupn_S' n φ i : uupn (S n) φ i = uupn n (uup φ) i.
Proof. unfold uupn; rewrite Nat.iter_succ_r; reflexivity. Qed.
Lemma uupn_ush n φ i : uupn n φ (n + i) = lvren (φ i) (ush n).
Proof.
  induction n.
  - cbn. symmetry; apply lvren_id; reflexivity.
  - rewrite uupn_S. change (S n + i) with (S (n + i)). cbn [uup]. rewrite IHn.
    apply lvren_lvren; reflexivity.
Qed.
Lemma uupn_lt n φ i : i < n -> uupn n φ i = lvar i.
Proof.
  revert i; induction n; intros i Hi; [lia|]. rewrite uupn_S. destruct i; cbn; auto.
  rewrite IHn by lia; reflexivity.
Qed.

(** ** Universe substitution *)

Section USubst.

Lemma tup_nth_usubst t k φ : tup_nth (usubst_tm t φ) k = usubst_tm (tup_nth t k) φ.
Proof. revert t; induction k; intros []; cbn; auto. Qed.

Lemma usingle_uup φ l n : lvsubst (uup φ n) (usingle (lvsubst l φ)) = lvsubst (usingle l n) φ.
Proof.
  destruct n; cbn; auto. rewrite (lvren_lvsubst _ _ _ lvar) by reflexivity.
  apply lvsubst_id; reflexivity.
Qed.

Lemma peelU_usubst b l φ : peelU (usubst_tm b φ) (lvsubst l φ) = usubst_tm (peelU b l) φ.
Proof.
  destruct b; cbn [usubst_tm peelU]; auto.
  transitivity (usubst_tm b (fun n => lvsubst (usingle l n) φ)).
  - apply (proj1 (proj2 usubst_usubst_all)); intros n; symmetry; apply usingle_uup.
  - symmetry; apply (proj1 (proj2 usubst_usubst_all)); reflexivity.
Qed.
Lemma peelG_usubst b o φ : peelG (usubst_tm b φ) (gousubst o φ) = usubst_tm (peelG b o) φ.
Proof.
  destruct b; cbn [usubst_tm peelG]; auto.
  symmetry; rewrite (proj1 (proj2 usubst_gsubst_all) _ _ _ (fun i => gousubst (gsingle o i) φ)) by auto.
  apply (proj1 (proj2 gsubst_ext_all)). intros [|i]; reflexivity.
Qed.
Lemma peelL_usubst b a φ : peelL (usubst_tm b φ) (usubst_tm a φ) = usubst_tm (peelL b a) φ.
Proof.
  destruct b; cbn [usubst_tm peelL]; auto.
  symmetry; apply (proj1 (proj2 usubst_subst_all)). intros [|n]; cbn; auto.
Qed.

Lemma getTy_usubst t φ : usubst_ty (getTy t) φ = getTy (usubst_tm t φ).
Proof. destruct t; reflexivity. Qed.

Lemma motT_usubst w lv g c φ :
  usubst_ty (motT w lv g c) φ = motT (usubst_tm w φ) (lvsubst lv φ) (ucsubst g φ) (usubst_tm c φ).
Proof.
  unfold motT. rewrite getTy_usubst, <- peelL_usubst, <- peelG_usubst, <- peelU_usubst.
  reflexivity.
Qed.
Lemma mott_usubst w lv g U c φ :
  usubst_ty (mott w lv g U c) φ =
  mott (usubst_tm w φ) (lvsubst lv φ) (ucsubst g φ) (usubst_ty U φ) (usubst_tm c φ).
Proof.
  unfold mott. rewrite getTy_usubst, <- peelL_usubst, <- !peelG_usubst, <- peelU_usubst.
  reflexivity.
Qed.

Lemma lvren_ush_usubst l n φ : lvsubst (lvren l (ush n)) (uupn n φ) = lvren (lvsubst l φ) (ush n).
Proof.
  rewrite (lvren_lvsubst _ _ _ (fun i => lvren (φ i) (ush n))) by (intros; symmetry; apply uupn_ush).
  symmetry; apply lvsubst_lvren; reflexivity.
Qed.

Lemma wkb_usubst nu ng nl w φ :
  usubst_tm (wkb nu ng nl w) (uupn nu φ) = wkb nu ng nl (usubst_tm w φ).
Proof.
  unfold wkb. rewrite usubst_ren_tm, usubst_gren_tm. do 2 f_equal.
  rewrite (uren_usubst_tm _ _ _ (fun i => lvren (φ i) (ush nu))) by (intros; symmetry; apply uupn_ush).
  symmetry; apply usubst_uren_tm; reflexivity.
Qed.
Lemma wkc_usubst nu ng Γ φ : ucsubst (wkc nu ng Γ) (uupn nu φ) = wkc nu ng (ucsubst Γ φ).
Proof.
  unfold wkc. rewrite (proj1 (proj2 (proj2 usubst_gren_all))). f_equal.
  rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ (fun i => lvren (φ i) (ush nu)))
    by (intros; symmetry; apply uupn_ush).
  symmetry; apply (proj1 (proj2 (proj2 usubst_uren_all))); reflexivity.
Qed.

Lemma wrapU_usubst n b φ : usubst_tm (wrapU n b) φ = wrapU n (usubst_tm b (uupn n φ)).
Proof.
  revert φ; induction n; intros φ; cbn [wrapU usubst_tm]; auto.
  rewrite IHn. f_equal. f_equal. apply (proj1 (proj2 usubst_ext_all)). intros i.
  symmetry; apply uupn_S'.
Qed.
Lemma wrapG_usubst n b φ : usubst_tm (wrapG n b) φ = wrapG n (usubst_tm b φ).
Proof. induction n; cbn; congruence. Qed.
Lemma wrapL_usubst n b φ : usubst_tm (wrapL n b) φ = wrapL n (usubst_tm b φ).
Proof. induction n; cbn; congruence. Qed.
Lemma wrap_usubst nu ng nl b φ :
  usubst_tm (wrap nu ng nl b) φ = wrap nu ng nl (usubst_tm b (uupn nu φ)).
Proof. unfold wrap. now rewrite wrapU_usubst, wrapG_usubst, wrapL_usubst. Qed.

Lemma mkrb_usubst MT Mt bs φ :
  usubst_tm (mkrb MT Mt bs) φ =
  mkrb (usubst_ty MT (uup φ)) (usubst_ty Mt (uup φ)) (fun k => usubst_tm (bs k) (uupn (br_nu k) φ)).
Proof.
  unfold mkrb. cbn [tup_from usubst_tm br_ar]. rewrite !wrap_usubst. reflexivity.
Qed.

Lemma wrapMT_usubst MT φ : usubst_tm (wrapMT MT) φ = wrapMT (usubst_ty MT (uup φ)).
Proof. reflexivity. Qed.
Lemma wrapMt_usubst Mt φ : usubst_tm (wrapMt Mt) φ = wrapMt (usubst_ty Mt (uup φ)).
Proof. reflexivity. Qed.

(** The branch scopes. *)

Lemma gdecl_uren_usubst D n φ :
  gdecl_usubst (gdecl_uren D (ush n)) (uupn n φ) = gdecl_uren (gdecl_usubst D φ) (ush n).
Proof.
  destruct D; cbn [gdecl_uren gdecl_usubst]; f_equal; rewrite ?lvren_ush_usubst; auto.
  all: first
    [ rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ (fun i => lvren (φ i) (ush n)))
        by (intros; symmetry; apply uupn_ush);
      symmetry; apply (proj1 (proj2 (proj2 usubst_uren_all))); reflexivity
    | rewrite (proj1 uren_usubst_all _ _ _ (fun i => lvren (φ i) (ush n)))
        by (intros; symmetry; apply uupn_ush);
      symmetry; apply (proj1 usubst_uren_all); reflexivity ].
Qed.

Lemma brDecls_usubst k n φ : k < nbr -> br_nu k = n ->
  map (fun D => gdecl_usubst D (uupn n φ)) (brDecls k) = brDecls k.
Proof.
  intros Hk <-. br_all ltac:(destruct k; [reflexivity|]); lia.
Qed.

Lemma brG_usubst k G L' φ : k < nbr ->
  gctx_usubst (brG k G) (br_nu k + L') (uupn (br_nu k) φ) = brG k (gctx_usubst G L' φ).
Proof.
  intros Hk. unfold brG, gctx_usubst, gctx_uwk; cbn [gL gΨ]. f_equal.
  rewrite map_app, brDecls_usubst by auto. f_equal.
  rewrite !map_map. apply map_ext; intros; apply gdecl_uren_usubst.
Qed.

Lemma cexts_usubst Γ As φ :
  ucsubst (cexts Γ As) φ = cexts (ucsubst Γ φ) (map (fun '(A, l) => (usubst_ty A φ, lvsubst l φ)) As).
Proof. revert Γ; induction As as [|[A l] As IH]; intros Γ; cbn; auto. Qed.

Lemma brLocs_usubst k wT wt a1 a2 φ : k < nbr ->
  map (fun '(A, l) => (usubst_ty A (uupn (br_nu k) φ), lvsubst l (uupn (br_nu k) φ)))
      (brLocs k wT wt a1 a2) =
  brLocs k (usubst_tm wT φ) (usubst_tm wt φ) (lvsubst a1 (uupn (br_nu k) φ))
    (lvsubst a2 (uupn (br_nu k) φ)).
Proof.
  intros Hk. br_all ltac:(destruct k;
    [cbn [brLocs map br_nu br_ar mkLocs call_ty call_lv br_calls br_ng]; rewrite ?motT_usubst, ?mott_usubst, ?wkb_usubst; reflexivity|]).
  lia.
Qed.

Lemma brΓ_usubst k Γ wT wt l1 l2 φ : k < nbr ->
  ucsubst (brΓ k Γ wT wt l1 l2) (uupn (br_nu k) φ) =
  brΓ k (ucsubst Γ φ) (usubst_tm wT φ) (usubst_tm wt φ) (lvsubst l1 φ) (lvsubst l2 φ).
Proof.
  intros Hk. unfold brΓ. rewrite cexts_usubst, wkc_usubst, brLocs_usubst by auto.
  now rewrite !lvren_ush_usubst.
Qed.

Lemma brRes_usubst k wT wt φ : k < nbr ->
  usubst_ty (brRes k wT wt) (uupn (br_nu k) φ) = brRes k (usubst_tm wT φ) (usubst_tm wt φ).
Proof.
  intros Hk. br_all ltac:(destruct k;
    [cbn [brRes br_nu br_ar call_ty br_head br_ng br_nl]; rewrite ?motT_usubst, ?mott_usubst, ?wkb_usubst; reflexivity|]).
  lia.
Qed.

Lemma brLv_usubst k l1 l2 φ :
  lvsubst (brLv k l1 l2) (uupn (br_nu k) φ) = brLv k (lvsubst l1 φ) (lvsubst l2 φ).
Proof. unfold brLv. destruct (br_isT k); apply lvren_ush_usubst. Qed.

(** The motive scopes. *)

Lemma recGT_usubst G L' φ :
  gctx_usubst (recGT G) (S L') (uup φ) = recGT (gctx_usubst G L' φ).
Proof.
  unfold recGT, gctx_usubst, gctx_uwk; cbn [gL gΨ map gdecl_usubst]. f_equal.
  rewrite !map_map. f_equal. apply map_ext; intros D; apply (gdecl_uren_usubst D 1).
Qed.
Lemma recGt_usubst G L' φ :
  gctx_usubst (recGt G) (S L') (uup φ) = recGt (gctx_usubst G L' φ).
Proof.
  unfold recGt, gctx_usubst, gctx_uwk; cbn [gL gΨ map gdecl_usubst]. f_equal.
  rewrite !map_map. f_equal. f_equal. apply map_ext; intros D; apply (gdecl_uren_usubst D 1).
Qed.
Lemma recΓT_usubst Γ φ : ucsubst (recΓT Γ) (uup φ) = recΓT (ucsubst Γ φ).
Proof. unfold recΓT; cbn [ucsubst]. now rewrite (wkc_usubst 1 1). Qed.
Lemma recΓt_usubst Γ φ : ucsubst (recΓt Γ) (uup φ) = recΓt (ucsubst Γ φ).
Proof. unfold recΓt; cbn [ucsubst]. now rewrite (wkc_usubst 1 2). Qed.

(** The reducts. *)

Lemma rb_br_usubst rb k φ : rb_br (usubst_tm rb φ) k = usubst_tm (rb_br rb k) φ.
Proof. apply tup_nth_usubst. Qed.

Lemma usubst_lsingle_ty M a φ : usubst_ty (subst_ty M (lsingle a)) φ = subst_ty (usubst_ty M φ) (lsingle (usubst_tm a φ)).
Proof. apply (proj1 usubst_subst_all). intros [|n]; reflexivity. Qed.
Lemma usubst_lsucc_ty M φ : usubst_ty (subst_ty M lsucc) φ = subst_ty (usubst_ty M φ) lsucc.
Proof. apply (proj1 usubst_subst_all). intros [|[|n]]; reflexivity. Qed.

Ltac upeel_push :=
  repeat first [ rewrite <- peelL_usubst | rewrite <- peelG_usubst | rewrite <- peelU_usubst ];
  rewrite rb_br_usubst; cbn [gousubst usubst_tm ucsubst usubst_ty lvsubst recT rect];
  rewrite ?usubst_lsingle_ty, ?usubst_lsucc_ty; reflexivity.

Lemma redT_usubst l1 l2 rb l Δ c v φ : redT l1 l2 rb l Δ c = Some v ->
  redT (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm rb φ) (lvsubst l φ) (ucsubst Δ φ) (usubst_ty c φ)
    = Some (usubst_tm v φ).
Proof. destruct c; cbn [redT usubst_ty]; intros E; inversion E; subst; f_equal; upeel_push. Qed.
Lemma redt_usubst l1 l2 rb l Δ T c v φ : redt l1 l2 rb l Δ T c = Some v ->
  redt (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm rb φ) (lvsubst l φ) (ucsubst Δ φ) (usubst_ty T φ)
    (usubst_tm c φ) = Some (usubst_tm v φ).
Proof.
  destruct c; cbn [redt usubst_tm]; try destruct T; cbn [usubst_ty];
    intros E; inversion E; subst; f_equal; upeel_push.
Qed.

End USubst.

(** ** Local renaming

    Local renaming does not enter the code, the code contexts or the index,
    and is lifted past each local binder of a component. *)

Definition rliftn (n : nat) (r : rsub) : rsub := Nat.iter n rlift r.

Lemma rliftn_succ n r : rlift (rliftn n r) = rliftn n (rlift r).
Proof. exact (Nat.iter_succ_r n rsub rlift r). Qed.

Lemma rlk_rliftn_ge n r m : rlk (rliftn n r) (n + m) = n + rlk r m.
Proof.
  induction n; cbn [rliftn Nat.iter plus]; auto.
  change (rliftn (S n) r) with (rlift (rliftn n r)). rewrite rlk_rlift, IHn. reflexivity.
Qed.

Lemma wrapU_ren n b r : (wrapU n b)⟨r⟩ = wrapU n b⟨r⟩.
Proof. induction n; cbn; congruence. Qed.
Lemma wrapG_ren n b r : (wrapG n b)⟨r⟩ = wrapG n b⟨r⟩.
Proof. induction n; cbn; congruence. Qed.
Lemma wrapL_ren n b r : (wrapL n b)⟨r⟩ = wrapL n b⟨rliftn n r⟩.
Proof.
  revert r; induction n; intros r; cbn [wrapL ren Ren_tm ren_tm]; auto.
  change (ren_tm (wrapL n b) (rlift r)) with (wrapL n b)⟨rlift r⟩. rewrite IHn. f_equal. f_equal.
  unfold rliftn; now rewrite Nat.iter_succ_r.
Qed.
Lemma wrap_ren nu ng nl b r : (wrap nu ng nl b)⟨r⟩ = wrap nu ng nl b⟨rliftn nl r⟩.
Proof. unfold wrap. now rewrite wrapU_ren, wrapG_ren, wrapL_ren. Qed.

Lemma mkrb_ren MT Mt bs r :
  (mkrb MT Mt bs)⟨r⟩ = mkrb MT⟨rlift r⟩ Mt⟨rlift r⟩ (fun k => (bs k)⟨rliftn (br_nl k) r⟩).
Proof. unfold mkrb. cbn [tup_from ren Ren_tm ren_tm br_ar]. rewrite !wrap_ren. reflexivity. Qed.
Lemma wrapMT_ren MT r : (wrapMT MT)⟨r⟩ = wrapMT MT⟨rlift r⟩.
Proof. reflexivity. Qed.
Lemma wrapMt_ren Mt r : (wrapMt Mt)⟨r⟩ = wrapMt Mt⟨rlift r⟩.
Proof. reflexivity. Qed.

Lemma getTy_ren t r : (getTy t)⟨r⟩ = getTy t⟨r⟩.
Proof. destruct t; reflexivity. Qed.
Lemma motT_ren w lv g c r : (motT w lv g c)⟨r⟩ = motT w⟨r⟩ lv g c⟨r⟩.
Proof.
  unfold motT. rewrite getTy_ren, <- peelL_ren, <- peelG_ren, <- peelU_ren. reflexivity.
Qed.
Lemma mott_ren w lv g U c r : (mott w lv g U c)⟨r⟩ = mott w⟨r⟩ lv g U c⟨r⟩.
Proof.
  unfold mott. rewrite getTy_ren, <- peelL_ren, <- !peelG_ren, <- peelU_ren. reflexivity.
Qed.

Lemma wkb_ren nu ng nl w r : (wkb nu ng nl w)⟨rliftn nl r⟩ = wkb nu ng nl w⟨r⟩.
Proof.
  unfold wkb. cbn [ren Ren_tm].
  rewrite (proj1 (proj2 ren_ren_all) _ _ _ (rcomp r (rshift nl))).
  2: { intros m; rewrite rlk_rcomp; cbn [rlk]. rewrite (Nat.add_comm m nl), rlk_rliftn_ge. lia. }
  rewrite <- !(proj1 (proj2 gren_ren_all)), <- !(proj1 (proj2 uren_ren_all)). do 2 f_equal.
  symmetry; apply (proj1 (proj2 ren_ren_all)). intros m; now rewrite rlk_rcomp.
Qed.

Fixpoint cexts_ren (As : list (ty * lvl)) (r : rsub) : list (ty * lvl) :=
  match As with nil => nil | cons (A, l) As => cons (A⟨r⟩, l) (cexts_ren As (rlift r)) end.

Lemma wkb_ren0 nu ng w r : (wkb nu ng 0 w)⟨r⟩ = wkb nu ng 0 w⟨r⟩.
Proof. exact (wkb_ren nu ng 0 w r). Qed.
Lemma wkb_ren1 nu ng w r : (wkb nu ng 1 w)⟨rlift r⟩ = wkb nu ng 1 w⟨r⟩.
Proof. exact (wkb_ren nu ng 1 w r). Qed.
Lemma wkb_ren2 nu ng w r : (wkb nu ng 2 w)⟨rlift (rlift r)⟩ = wkb nu ng 2 w⟨r⟩.
Proof. exact (wkb_ren nu ng 2 w r). Qed.
Lemma wkb_ren3 nu ng w r : (wkb nu ng 3 w)⟨rlift (rlift (rlift r))⟩ = wkb nu ng 3 w⟨r⟩.
Proof. exact (wkb_ren nu ng 3 w r). Qed.

Lemma brLocs_ren k wT wt a1 a2 r : k < nbr ->
  cexts_ren (brLocs k wT wt a1 a2) r = brLocs k wT⟨r⟩ wt⟨r⟩ a1 a2.
Proof.
  intros Hk.
  br_all ltac:(destruct k; [cbn [brLocs cexts_ren mkLocs call_ty call_lv br_calls br_nu br_ng br_ar];
    rewrite ?motT_ren, ?mott_ren, ?wkb_ren0, ?wkb_ren1, ?wkb_ren2, ?wkb_ren3; reflexivity|]).
  lia.
Qed.

Lemma brRes_ren k wT wt r : k < nbr -> (brRes k wT wt)⟨rliftn (br_nl k) r⟩ = brRes k wT⟨r⟩ wt⟨r⟩.
Proof.
  intros Hk. br_all ltac:(destruct k; [cbn [brRes br_nl br_ar call_ty br_head br_nu br_ng]; rewrite ?motT_ren, ?mott_ren, ?wkb_ren; reflexivity|]).
  lia.
Qed.
