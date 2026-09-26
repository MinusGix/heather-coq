(** * A β reduct is its branch at extended substitutions (M3_DESIGN.md E13)

    Peeling a wrapped branch with lists of levels, global images and
    local terms is the triple substitution of the branch body by the
    lists, the first peeled binder being the outermost (highest index).
    For a branch moved into a scope by [φ], [σ] and [e] (as a bundle
    under substitution is, [mkrb_usubst]/[mkrb_gsubst]/[mkrb_subst]),
    the reduct is the body at the extensions [uext ls φ], [gext_s os σ],
    [lext as e]. *)
From DeLaM.Typing Require Export RecInst.

(** ** Peeling lists of binders *)

Fixpoint peelUs (b : tm) (ls : list lvl) : tm :=
  match ls with nil => b | l :: ls => peelUs (peelU b l) ls end.
Fixpoint peelGs (b : tm) (os : list gobj) : tm :=
  match os with nil => b | o :: os => peelGs (peelG b o) os end.
Fixpoint peelLs (b : tm) (xs : list tm) : tm :=
  match xs with nil => b | a :: xs => peelLs (peelL b a) xs end.

(** The extensions: the list's last element is index 0. *)
Definition gext_s (os : list gobj) (σ : gsub) : gsub :=
  fun i => if i <? length os then nth (length os - S i) os (GId 0) else σ (i - length os).
Definition lext (xs : list tm) (e : lsub) : lsub := fold_left lcons xs e.

Lemma llk_lext xs : forall e i, llk (lext xs e) i =
  if i <? length xs then nth (length xs - S i) xs tmErr else llk e (i - length xs).
Proof.
  induction xs as [|a xs IH]; intros e i; cbn [lext fold_left length].
  - rewrite Nat.sub_0_r; reflexivity.
  - change (fold_left lcons xs (lcons e a)) with (lext xs (lcons e a)). rewrite IH.
    destruct (Nat.ltb_spec i (length xs)), (Nat.ltb_spec i (S (length xs))); try lia.
    + replace (S (length xs) - S i) with (S (length xs - S i)) by lia. reflexivity.
    + replace (i - length xs) with 0 by lia. replace (S (length xs) - S i) with 0 by lia. reflexivity.
    + replace (i - length xs) with (S (i - S (length xs))) by lia. reflexivity.
Qed.

(** ** Peeling a wrapped term *)

Lemma peelUs_wrapU ls : forall n b, length ls = n -> dnftm b ->
  peelUs (wrapU n b) ls = usubst_tm b (uext ls lvar).
Proof.
  induction ls as [|l ls IH]; intros n b Hn Hb; cbn in Hn; subst n; cbn [peelUs wrapU].
  - symmetry; apply (proj1 (proj2 usubst_id_all)); [exact Hb|]. intros i; unfold uext; cbn; f_equal; lia.
  - cbn [peelU]. rewrite wrapU_usubst, (IH _ _ eq_refl (proj1 (proj2 usubst_dnf_all) _ _)).
    apply (proj1 (proj2 usubst_usubst_all)). intros i. unfold uext; cbn [length].
    destruct (Nat.ltb_spec i (length ls)) as [Hi | Hi].
    + rewrite uupn_lt by exact Hi. cbn [lvsubst]. unfold uext.
      destruct (Nat.ltb_spec i (length ls)), (Nat.ltb_spec i (S (length ls))); try lia.
      replace (S (length ls) - S i) with (S (length ls - S i)) by lia. reflexivity.
    + assert (Hj : exists j, i = length ls + j) by (exists (i - length ls); lia).
      destruct Hj as [j ->]. rewrite uupn_ush.
      rewrite (lvren_lvsubst _ _ _ (fun m => uext ls lvar (length ls + m))) by reflexivity.
      assert (Hid : forall m, uext ls lvar (length ls + m) = lvar m).
      { intros m; unfold uext. destruct (Nat.ltb_spec (length ls + m) (length ls)); [lia|]. f_equal; lia. }
      destruct j as [|m].
      * rewrite Nat.add_0_r. destruct (Nat.ltb_spec (length ls) (S (length ls))); [|lia].
        rewrite Nat.sub_diag. cbn [usingle nth]. symmetry; apply lvsubst_id, Hid.
      * destruct (Nat.ltb_spec (length ls + S m) (S (length ls))); [lia|].
        cbn [usingle lvsubst]. rewrite Hid. f_equal; lia.
Qed.

Lemma gosubst_goren' o ξ τ : gosubst (goren o ξ) τ = gosubst o (fun i => τ (ξ i)).
Proof.
  destruct o; cbn [goren gosubst]; [reflexivity | f_equal ..].
  - now apply (proj1 (proj2 (proj2 gsubst_gren_all))).
  - now apply (proj1 gsubst_gren_all).
  - now apply (proj1 (proj2 gsubst_gren_all)).
Qed.
Lemma gosubst_id o τ : dnfo o -> (forall i, τ i = GId i) -> gosubst o τ = o.
Proof.
  intros Ho Hτ; destruct o; cbn [gosubst dnfo] in *; [apply Hτ | f_equal ..].
  - now apply (proj1 (proj2 (proj2 gsubst_id_all))).
  - now apply (proj1 gsubst_id_all).
  - now apply (proj1 (proj2 gsubst_id_all)).
Qed.

Lemma peelGs_wrapG os : forall n b, length os = n -> Forall dnfo os -> dnftm b ->
  peelGs (wrapG n b) os = gsubst_tm b (gext_s os (fun i => GId i)).
Proof.
  induction os as [|o os IH]; intros n b Hn Ho Hb; cbn in Hn; subst n; cbn [peelGs wrapG].
  - symmetry; apply (proj1 (proj2 gsubst_id_all)); [exact Hb|]. intros i; unfold gext_s; cbn; f_equal; lia.
  - inversion Ho as [| ? ? Ho0 Hos]; subst. cbn [peelG].
    change (gsubst_tm (wrapG (length os) b) (gsingle o)) with (wrapG (length os) b)⦃gsingle o⦄.
    rewrite wrapG_gsubst.
    assert (Hd : forall i, dnfo (gupn (length os) (gsingle o) i)) by (apply gdnf_gupn; intros [|i]; cbn; auto).
    etransitivity; [exact (IH _ _ eq_refl Hos (proj1 (proj2 gsubst_dnf_all) _ Hb _ Hd)) |].
    apply (proj1 (proj2 gsubst_gsubst_all)). intros i. unfold gext_s at 1; cbn [length].
    destruct (Nat.ltb_spec i (length os)) as [Hi | Hi].
    + rewrite gupn_lt by exact Hi. cbn [gosubst]. unfold gext_s.
      destruct (Nat.ltb_spec i (length os)), (Nat.ltb_spec i (S (length os))); try lia.
      replace (S (length os) - S i) with (S (length os - S i)) by lia. reflexivity.
    + assert (Hj : exists j, i = length os + j) by (exists (i - length os); lia).
      destruct Hj as [j ->]. rewrite gupn_ush by (destruct j; cbn; auto).
      rewrite gosubst_goren'.
      assert (Hid : forall m, gext_s os (fun i => GId i) (length os + m) = GId m).
      { intros m; unfold gext_s. destruct (Nat.ltb_spec (length os + m) (length os)); [lia|]. f_equal; lia. }
      destruct j as [|m].
      * rewrite Nat.add_0_r. destruct (Nat.ltb_spec (length os) (S (length os))); [|lia].
        rewrite Nat.sub_diag. cbn [gsingle nth]. symmetry; apply gosubst_id; [exact Ho0 | exact Hid].
      * destruct (Nat.ltb_spec (length os + S m) (S (length os))); [lia|].
        cbn [gsingle gosubst]. rewrite Hid. f_equal; lia.
Qed.

Lemma llk_lliftn_lt nl d n : n < nl -> llk (lliftn nl d) n = var n.
Proof.
  revert n; induction nl; intros n Hn; [lia|]. rewrite lliftn_S, llk_llift.
  destruct n; [reflexivity|]. rewrite IHnl by lia. cbn [ren_tm]. rewrite rlk_shift1. reflexivity.
Qed.

Lemma peelLs_wrapL xs : forall n b, length xs = n -> Forall dnftm xs -> dnftm b ->
  peelLs (wrapL n b) xs = subst_tm b (lext xs (lshift 0)).
Proof.
  induction xs as [|a xs IH]; intros n b Hn Ha Hb; cbn in Hn; subst n; cbn [peelLs wrapL].
  - symmetry; apply subst_id; [exact (dnftm_nftm _ Hb) | intros i; cbn; f_equal; lia].
  - inversion Ha as [| ? ? Ha0 Has]; subst. cbn [peelL].
    change (subst_tm (wrapL (length xs) b) (lsingle a)) with (wrapL (length xs) b)[lsingle a].
    rewrite wrapL_subst.
    assert (Hs : LK dnftm (lsingle a)) by (intros [|m]; cbn; auto).
    etransitivity; [exact (IH _ _ eq_refl Has (subst_dnf _ _ Hb (lk_dnf_lliftn _ _ Hs))) |].
    apply subst_subst. intros i. rewrite !llk_lext; cbn [length].
    destruct (Nat.ltb_spec i (length xs)) as [Hi | Hi].
    + rewrite llk_lliftn_lt by exact Hi. cbn [subst Subst_tm subst_tm]. rewrite llk_lext.
      destruct (Nat.ltb_spec i (length xs)), (Nat.ltb_spec i (S (length xs))); try lia.
      first [ replace (S (length xs) - S i) with (S (length xs - S i)) by lia; reflexivity
            | replace (length xs - i) with (S (length xs - S i)) by lia; reflexivity ].
    + assert (Hj : exists j, i = j + length xs) by (exists (i - length xs); lia).
      destruct Hj as [j ->]. rewrite llk_lliftn by (intros [|m]; cbn; auto using dnftm_nftm).
      rewrite (ren_subst _ _ _ (lshift 0)).
      * destruct j as [|m]; cbn [llk lsingle].
        -- destruct (Nat.ltb_spec (0 + length xs) (S (length xs))); [|lia].
           replace (S (length xs) - S (0 + length xs)) with 0 by lia. cbn [nth].
           symmetry; apply subst_id; [exact (dnftm_nftm _ Ha0) | intros; cbn; f_equal; lia].
        -- destruct (Nat.ltb_spec (S m + length xs) (S (length xs))); [lia|].
           cbn. f_equal; lia.
      * intros m. rewrite llk_lext. destruct (Nat.ltb_spec (rlk (rshift (length xs)) m) (length xs)).
        -- cbn in *; lia.
        -- cbn. f_equal. cbn in *; lia.
Qed.

Lemma dnf_wrapG n b : dnftm b -> dnftm (wrapG n b).
Proof. induction n; cbn; auto. Qed.
Lemma dnf_wrapL n b : dnftm b -> dnftm (wrapL n b).
Proof. induction n; cbn; auto. Qed.

Lemma peel_wrap nu ng nl b ls os xs : length ls = nu -> length os = ng -> length xs = nl ->
  Forall dnfo os -> Forall dnftm xs -> dnftm b ->
  peelLs (peelGs (peelUs (wrap nu ng nl b) ls) os) xs =
  ((usubst_tm b (uext ls lvar))⦃gext_s os (fun i => GId i)⦄)[lext xs (lshift 0)].
Proof.
  intros Hu Hg Hl Ho Hx Hb. unfold wrap.
  rewrite (peelUs_wrapU _ _ _ Hu (dnf_wrapG _ _ (dnf_wrapL _ _ Hb))), wrapG_usubst, wrapL_usubst.
  pose proof (proj1 (proj2 usubst_dnf_all) b (uext ls lvar)) as Hb'.
  rewrite (peelGs_wrapG _ _ _ Hg Ho (dnf_wrapL _ _ Hb')).
  change (gsubst_tm (wrapL nl ?x) ?s) with (wrapL nl x)⦃s⦄. rewrite wrapL_gsubst.
  apply (peelLs_wrapL _ _ _ Hl Hx).
  apply (proj1 (proj2 gsubst_dnf_all)); [exact Hb'|]. intros i; unfold gext_s.
  destruct (Nat.ltb_spec i (length os)); [|exact I].
  rewrite Forall_forall in Ho. destruct (Nat.lt_ge_cases (length os - S i) (length os)) as [Hlt | Hge].
  - apply Ho, nth_In, Hlt.
  - rewrite nth_overflow by exact Hge; exact I.
Qed.

(** ** Pointwise descriptions of the composite substitutions *)

Lemma uext_uupn ls φ i : lvsubst (uupn (length ls) φ i) (uext ls lvar) = uext ls φ i.
Proof.
  unfold uext at 2. destruct (Nat.ltb_spec i (length ls)) as [Hi | Hi].
  - rewrite uupn_lt by exact Hi. cbn [lvsubst]. unfold uext.
    destruct (Nat.ltb_spec i (length ls)); [reflexivity | lia].
  - replace i with (length ls + (i - length ls)) at 1 by lia. rewrite uupn_ush.
    rewrite (lvren_lvsubst _ _ _ lvar); [apply lvsubst_id; reflexivity|].
    intros m; unfold uext, ush. destruct (Nat.ltb_spec (length ls + m) (length ls)); [lia|]. f_equal; lia.
Qed.

Lemma gousubst_gouren' o ρ φ : gousubst (gouren o ρ) φ = gousubst o (fun i => φ (ρ i)).
Proof.
  destruct o; cbn [gouren gousubst]; [reflexivity | f_equal ..].
  - now apply (proj1 (proj2 (proj2 uren_usubst_all))).
  - now apply (proj1 uren_usubst_all).
  - now apply (proj1 (proj2 uren_usubst_all)).
Qed.
Lemma gousubst_id o φ : dnfo o -> (forall i, φ i = lvar i) -> gousubst o φ = o.
Proof.
  intros Ho Hφ; destruct o; cbn [gousubst dnfo] in *; [reflexivity | f_equal ..].
  - now apply (proj1 (proj2 (proj2 usubst_id_all))).
  - now apply (proj1 usubst_id_all).
  - now apply (proj1 (proj2 usubst_id_all)).
Qed.

Lemma gext_gbsub ls os σ i : gdnf σ ->
  gosubst (gousubst (gupn (length os) (guwkn (length ls) σ) i) (uext ls lvar)) (gext_s os (fun j => GId j)) =
  gext_s os σ i.
Proof.
  intros Hσ. unfold gext_s at 2. destruct (Nat.ltb_spec i (length os)) as [Hi | Hi].
  - rewrite gupn_lt by exact Hi. cbn [gousubst gosubst]. unfold gext_s.
    destruct (Nat.ltb_spec i (length os)); [reflexivity | lia].
  - replace i with (length os + (i - length os)) at 1 by lia.
    rewrite gupn_ush by (rewrite guwkn_lk by apply Hσ; apply dnfo_gouren).
    rewrite gousubst_goren, guwkn_lk by apply Hσ. rewrite gousubst_gouren', gosubst_goren'.
    rewrite gousubst_id; [apply gosubst_id; [apply Hσ|] | apply Hσ |].
    + intros m; unfold gext_s, ush. destruct (Nat.ltb_spec (length os + m) (length os)); [lia|]. f_equal; lia.
    + intros m; unfold uext, ush. destruct (Nat.ltb_spec (length ls + m) (length ls)); [lia|]. f_equal; lia.
Qed.

Lemma lext_bsub ls os xs e n : LK dnftm e ->
  (gsubst_tm (usubst_tm (llk (lliftn (length xs) (gwkn (length os) (uwkn (length ls) e))) n) (uext ls lvar))
     (gext_s os (fun j => GId j)))[lext xs (lshift 0)] = llk (lext xs e) n.
Proof.
  intros He. rewrite (llk_lext xs e). destruct (Nat.ltb_spec n (length xs)) as [Hn | Hn].
  - rewrite llk_lliftn_lt by exact Hn. cbn [usubst_tm gsubst_tm subst Subst_tm subst_tm].
    rewrite llk_lext. destruct (Nat.ltb_spec n (length xs)); [reflexivity | lia].
  - assert (Hj : exists m, n = m + length xs) by (exists (n - length xs); lia). destruct Hj as [m ->].
    replace (m + length xs - length xs) with m by lia.
    assert (He' : LK dnftm (gwkn (length os) (uwkn (length ls) e))) by auto with nf.
    rewrite llk_lliftn by (intros k; apply dnftm_nftm, He').
    rewrite llk_gwkn by auto with nf. rewrite llk_uwkn by exact He.
    rewrite (proj1 (proj2 usubst_ren_all)), (proj1 (proj2 usubst_gren_all)).
    rewrite (proj1 (proj2 uren_usubst_all) _ _ _ lvar).
    2: { intros k; unfold uext, ush. destruct (Nat.ltb_spec (length ls + k) (length ls)); [lia|]. f_equal; lia. }
    rewrite (proj1 (proj2 usubst_id_all) _ (He m) lvar (fun _ => eq_refl)).
    change (gsubst_tm (ren_tm ?x ?r) ?s) with (x⟨r⟩⦃s⦄). rewrite gsubst_ren. cbn [gsubst GSubst_tm].
    rewrite (proj1 (proj2 gsubst_gren_all) _ _ _ (fun j => GId j)).
    2: { intros k; unfold gext_s, ush. destruct (Nat.ltb_spec (length os + k) (length os)); [lia|]. f_equal; lia. }
    rewrite (proj1 (proj2 gsubst_id_all) _ (He m) (fun j => GId j) (fun _ => eq_refl)).
    rewrite (ren_subst _ _ _ (lshift 0)).
    + apply subst_id; [exact (dnftm_nftm _ (He m)) | intros; cbn; f_equal; lia].
    + intros k. rewrite llk_lext. destruct (Nat.ltb_spec (rlk (rshift (length xs)) k) (length xs)).
      * cbn in *; lia.
      * cbn. f_equal. cbn in *; lia.
Qed.

(** A reduct of a bundle moved by [φ], [σ], [e]: the branch body at the
    extended substitutions. *)
Lemma branch_inst b φ σ e ls os xs : Forall dnfo os -> Forall dnftm xs -> dnftm b -> gdnf σ -> LK dnftm e ->
  peelLs (peelGs (peelUs (wrap (length ls) (length os) (length xs)
    (((usubst_tm b (uupn (length ls) φ))⦃gupn (length os) (guwkn (length ls) σ)⦄)
       [lliftn (length xs) (gwkn (length os) (uwkn (length ls) e))])) ls) os) xs =
  ((usubst_tm b (uext ls φ))⦃gext_s os σ⦄)[lext xs e].
Proof.
  intros Ho Hx Hb Hσ He.
  rewrite peel_wrap by first
    [ reflexivity | assumption
    | exact (subst_dnf _ _ (proj1 (proj2 gsubst_dnf_all) _ (proj1 (proj2 usubst_dnf_all) _ _) _
                              (gdnf_gupn _ _ (gdnf_guwkn _ _ Hσ)))
               (lk_dnf_lliftn _ _ (lk_dnf_gwkn _ _ (lk_dnf_uwkn _ _ He)))) ].
  rewrite usubst_subst, usubst_gsubst.
  rewrite (usubst_usubst _ _ _ (uext ls φ)) by (intros; symmetry; apply uext_uupn).
  rewrite gsubst_subst.
  rewrite (gsubst_gsubst _ _ _ (gext_s os σ)) by (intros; symmetry; apply gext_gbsub, Hσ).
  apply subst_subst. intros n. symmetry.
  rewrite llk_glsubst, llk_ulsubst. apply lext_bsub, He.
Qed.

(** ** Building the extensions one image at a time *)

Lemma gext_s_app os o σ i :
  gext_s (os ++ o :: nil) σ i = match i with 0 => o | S j => gext_s os σ j end.
Proof.
  unfold gext_s. rewrite length_app; cbn [length]. rewrite Nat.add_1_r.
  destruct i as [|i].
  - destruct (Nat.ltb_spec 0 (S (length os))); [|lia].
    replace (S (length os) - 1) with (length os) by lia. rewrite app_nth2 by lia.
    rewrite Nat.sub_diag; reflexivity.
  - destruct (Nat.ltb_spec (S i) (S (length os))), (Nat.ltb_spec i (length os)); try lia.
    + rewrite app_nth1 by lia. f_equal; lia.
    + f_equal; lia.
Qed.

(** ** The motives' instances *)

Lemma motT_inst MT φ σ e k Δ a : dnfty MT -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnftm a ->
  motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))])) k Δ a =
  ((usubst_ty MT (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: nil) σ⦄)[lext (a :: nil) e].
Proof.
  intros HM Hσ He HΔ Ha.
  transitivity (getTy (peelLs (peelGs (peelUs (wrap (length (k :: nil)) (length (GCtx Δ :: nil)) (length (a :: nil))
    (((usubst_tm (tmTy MT) (uupn (length (k :: nil)) φ))⦃gupn (length (GCtx Δ :: nil)) (guwkn (length (k :: nil)) σ)⦄)
       [lliftn (length (a :: nil)) (gwkn (length (GCtx Δ :: nil)) (uwkn (length (k :: nil)) e))])) (k :: nil)) (GCtx Δ :: nil)) (a :: nil)));
    [reflexivity|].
  rewrite branch_inst; [reflexivity | repeat constructor; exact HΔ | repeat constructor; exact Ha
                       | exact HM | exact Hσ | exact He].
Qed.

Lemma mott_inst Mt φ σ e k Δ U a : dnfty Mt -> gdnf σ -> LK dnftm e -> dnfctx Δ -> dnfty U -> dnftm a ->
  mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))])) k Δ U a =
  ((usubst_ty Mt (uext (k :: nil) φ))⦃gext_s (GCtx Δ :: GTy U :: nil) σ⦄)[lext (a :: nil) e].
Proof.
  intros HM Hσ He HΔ HU Ha.
  transitivity (getTy (peelLs (peelGs (peelUs (wrap (length (k :: nil)) (length (GCtx Δ :: GTy U :: nil)) (length (a :: nil))
    (((usubst_tm (tmTy Mt) (uupn (length (k :: nil)) φ))⦃gupn (length (GCtx Δ :: GTy U :: nil)) (guwkn (length (k :: nil)) σ)⦄)
       [lliftn (length (a :: nil)) (gwkn (length (GCtx Δ :: GTy U :: nil)) (uwkn (length (k :: nil)) e))])) (k :: nil)) (GCtx Δ :: GTy U :: nil)) (a :: nil)));
    [reflexivity|].
  rewrite branch_inst; [reflexivity | repeat constructor; assumption | repeat constructor; exact Ha
                       | exact HM | exact Hσ | exact He].
Qed.

(** ** The scopes at instantiated levels *)

Lemma uext_ush ls φ i : uext ls φ (length ls + i) = φ i.
Proof. unfold uext. destruct (Nat.ltb_spec (length ls + i) (length ls)); [lia|]. f_equal; lia. Qed.

Lemma usub_ok_uext ls φ L' L : Forall (lwf L') ls -> usub_ok φ L' L -> usub_ok (uext ls φ) L' (length ls + L).
Proof.
  intros Hl Hφ i Hi. unfold uext. destruct (Nat.ltb_spec i (length ls)) as [Hi' | Hi'].
  - rewrite Forall_forall in Hl. apply Hl, nth_In; lia.
  - apply Hφ; lia.
Qed.

Lemma lvren_ush_uext l ls φ : lvsubst (lvren l (ush (length ls))) (uext ls φ) = lvsubst l φ.
Proof. apply lvren_lvsubst; intros n; symmetry; apply uext_ush. Qed.

Lemma gdecl_uren_uext D ls φ :
  gdecl_usubst (gdecl_uren D (ush (length ls))) (uext ls φ) = gdecl_usubst D φ.
Proof.
  destruct D; cbn [gdecl_uren gdecl_usubst]; f_equal; rewrite ?lvren_ush_uext; auto.
  all: first [ apply (proj1 (proj2 (proj2 uren_usubst_all))) | apply (proj1 uren_usubst_all) ];
    intros; symmetry; apply uext_ush.
Qed.

Lemma map_uren_uext Ψ ls φ :
  map (fun D => gdecl_usubst D (uext ls φ)) (map (fun D => gdecl_uren D (ush (length ls))) Ψ) =
  map (fun D => gdecl_usubst D φ) Ψ.
Proof. rewrite map_map. apply map_ext; intros; apply gdecl_uren_uext. Qed.

Lemma G_us_recGT_uext G L' φ k :
  G_us (recGT G) L' (uext (k :: nil) φ) = gext (G_us G L' φ) gdCtx.
Proof.
  unfold G_us, gctx_usubst, recGT, gctx_uwk, gext; cbn [gL gΨ map gdecl_usubst]. f_equal. f_equal.
  exact (map_uren_uext _ (k :: nil) φ).
Qed.
Lemma G_us_recGt_uext G L' φ k :
  G_us (recGt G) L' (uext (k :: nil) φ) = gext (gext (G_us G L' φ) gdCtx) (gdTy (cvar 0) lD k).
Proof.
  unfold G_us, gctx_usubst, recGt, gctx_uwk, gext; cbn [gL gΨ map gdecl_usubst]. f_equal. f_equal. f_equal.
  exact (map_uren_uext _ (k :: nil) φ).
Qed.
Lemma G_us_brG_uext k G L' φ ls : length ls = br_nu k ->
  G_us (brG k G) L' (uext ls φ) =
  mkG L' (map (fun D => gdecl_usubst D (uext ls φ)) (brDecls k) ++ gΨ (G_us G L' φ)).
Proof.
  intros Hn. unfold G_us, gctx_usubst, brG, gctx_uwk; cbn [gL gΨ]. f_equal.
  rewrite map_app. f_equal. rewrite <- Hn. exact (map_uren_uext _ ls φ).
Qed.

Lemma wkc_inst nu ng Γ ls os φ σ : length ls = nu -> length os = ng ->
  gcsubst (ucsubst (wkc nu ng Γ) (uext ls φ)) (gext_s os σ) = gcsubst (ucsubst Γ φ) σ.
Proof.
  intros <- <-. unfold wkc. rewrite usubst_gren_ctx'.
  rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ φ) by (intros; symmetry; apply uext_ush).
  apply (proj1 (proj2 (proj2 gsubst_gren_all))). intros i; unfold gext_s, ush.
  destruct (Nat.ltb_spec (length os + i) (length os)); [lia|]. f_equal; lia.
Qed.

Lemma recΓT_inst' Γ k φ Δ σ :
  gcsubst (ucsubst (recΓT Γ) (uext (k :: nil) φ)) (gext_s (GCtx Δ :: nil) σ) =
  gcsubst (ucsubst Γ φ) σ ,, tyCTyp Δ k @ lzero.
Proof.
  unfold recΓT. cbn [ucsubst gcsubst usubst_ty gsubst_ty lvsubst]. f_equal.
  apply (wkc_inst 1 1 Γ (k :: nil) (GCtx Δ :: nil)); reflexivity.
Qed.

Lemma recΓt_inst' Γ k φ Δ U σ : nfty U ->
  gcsubst (ucsubst (recΓt Γ) (uext (k :: nil) φ)) (gext_s (GCtx Δ :: GTy U :: nil) σ) =
  gcsubst (ucsubst Γ φ) σ ,, tyCTrm Δ U k @ lzero.
Proof.
  intros HU. unfold recΓt, gv. cbn [ucsubst gcsubst usubst_ty gsubst_ty lvsubst ulsubst glsubst]. f_equal.
  - apply (wkc_inst 1 2 Γ (k :: nil) (GCtx Δ :: GTy U :: nil)); reflexivity.
  - f_equal. unfold gext_s; cbn. apply subst_id_ty; [exact HU | intros; cbn; f_equal; lia].
Qed.

(** ** Ambient terms weakened into a branch, then instantiated *)

Lemma wkb_inst w ls os xs φ σ e :
  ((usubst_tm (wkb (length ls) (length os) (length xs) w) (uext ls φ))⦃gext_s os σ⦄)[lext xs e] =
  ((usubst_tm w φ)⦃σ⦄)[e].
Proof.
  unfold wkb. rewrite (proj1 (proj2 usubst_ren_all)), (proj1 (proj2 usubst_gren_all)).
  rewrite (proj1 (proj2 uren_usubst_all) _ _ _ φ) by (intros; symmetry; apply uext_ush).
  change (gsubst_tm (ren_tm ?x ?r) ?s) with (x⟨r⟩⦃s⦄). rewrite gsubst_ren. cbn [gsubst GSubst_tm].
  rewrite (proj1 (proj2 gsubst_gren_all) _ _ _ σ).
  2: { intros i; unfold gext_s, ush. destruct (Nat.ltb_spec (length os + i) (length os)); [lia|]. f_equal; lia. }
  apply ren_subst. intros n. rewrite llk_lext.
  destruct (Nat.ltb_spec (rlk (rshift (length xs)) n) (length xs)); cbn in *; [lia|]. f_equal; lia.
Qed.

Lemma motT_wkb_inst MT ls os xs φ σ e lv g c : gdnf (gext_s os σ) -> LK dnftm (lext xs e) ->
  ((usubst_ty (motT (wkb (length ls) (length os) (length xs) (wrapMT MT)) lv g c) (uext ls φ))⦃gext_s os σ⦄)
    [lext xs e] =
  motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))])) (lvsubst lv (uext ls φ))
    ((ucsubst g (uext ls φ))⦃gext_s os σ⦄) (((usubst_tm c (uext ls φ))⦃gext_s os σ⦄)[lext xs e]).
Proof.
  intros Hσ He. rewrite motT_usubst.
  rewrite motT_gsubst by first [exact Hσ | hd_tac].
  rewrite motT_subst by first [exact He | hd_tac].
  f_equal. rewrite wkb_inst. reflexivity.
Qed.

Lemma mott_wkb_inst Mt ls os xs φ σ e lv g U c : gdnf (gext_s os σ) -> LK dnftm (lext xs e) ->
  ((usubst_ty (mott (wkb (length ls) (length os) (length xs) (wrapMt Mt)) lv g U c) (uext ls φ))⦃gext_s os σ⦄)
    [lext xs e] =
  mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))]))
    (lvsubst lv (uext ls φ)) ((ucsubst g (uext ls φ))⦃gext_s os σ⦄) ((usubst_ty U (uext ls φ))⦃gext_s os σ⦄)
    (((usubst_tm c (uext ls φ))⦃gext_s os σ⦄)[lext xs e]).
Proof.
  intros Hσ He. rewrite mott_usubst.
  rewrite mott_gsubst by first [exact Hσ | hd_tac].
  rewrite mott_subst by first [exact He | hd_tac].
  f_equal. rewrite wkb_inst. reflexivity.
Qed.

(** ** The premises of a typed recursor, on their own

    A bundle whose motives and branches are typed gives typed recursors
    at any typed scrutinee (the result type by [RecInst]). *)

Definition RBwf (G : gctx) (Γ : ctx) (l1 l2 : lvl) (MT Mt : ty) (bs : nat -> tm) : Prop :=
  lwf (gL G) l1 /\ lwf (gL G) l2 /\
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] /\
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] /\
  (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) /\
  (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]).

Lemma elimT_prem {G Γ l1 l2 rb l Δ t T k} : [ G ; Γ ⊢[ lM ] elimT l1 l2 rb l Δ t : T @ k ] ->
  exists MT Mt bs, rb = mkrb MT Mt bs /\ RBwf G Γ l1 l2 MT Mt bs.
Proof.
  intros H; remember (elimT l1 l2 rb l Δ t) as x eqn:Hx; revert Hx.
  induction H; intros Hx; try discriminate; eauto.
  injection Hx; intros; subst. do 3 eexists; split; [reflexivity|]. repeat split; assumption.
Qed.
Lemma elimt_prem {G Γ l1 l2 rb l Δ T0 t T k} : [ G ; Γ ⊢[ lM ] elimt l1 l2 rb l Δ T0 t : T @ k ] ->
  exists MT Mt bs, rb = mkrb MT Mt bs /\ RBwf G Γ l1 l2 MT Mt bs.
Proof.
  intros H; remember (elimt l1 l2 rb l Δ T0 t) as x eqn:Hx; revert Hx.
  induction H; intros Hx; try discriminate; eauto.
  injection Hx; intros; subst. do 3 eexists; split; [reflexivity|]. repeat split; assumption.
Qed.

(** The recursors are typed at well-formed levels only (never at ω, M4). *)
Lemma elimT_lvl_wf {G Γ l1 l2 rb l Δ t T k} : [ G ; Γ ⊢[ lM ] elimT l1 l2 rb l Δ t : T @ k ] -> lwf (gL G) k.
Proof.
  intros H; remember (elimT l1 l2 rb l Δ t) as x eqn:Hx; revert Hx.
  induction H; intros Hx; try discriminate; eauto using lequiv_wf_l, lequiv_wf_r.
Qed.
Lemma elimt_lvl_wf {G Γ l1 l2 rb l Δ T0 t T k} : [ G ; Γ ⊢[ lM ] elimt l1 l2 rb l Δ T0 t : T @ k ] -> lwf (gL G) k.
Proof.
  intros H; remember (elimt l1 l2 rb l Δ T0 t) as x eqn:Hx; revert Hx.
  induction H; intros Hx; try discriminate; eauto using lequiv_wf_l, lequiv_wf_r.
Qed.

Lemma wf_elimT' {G Γ l1 l2 MT Mt bs l Δ t} : RBwf G Γ l1 l2 MT Mt bs -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : motT (wrapMT MT) l Δ t @ l1 ].
Proof.
  intros (H1 & H2 & HT & Ht & Hc & Hb) Hl HΔ Hs.
  apply wf_elimT; auto. exact (motT_wf _ _ _ _ _ _ _ HT Hl HΔ Hs).
Qed.
Lemma wf_elimt' {G Γ l1 l2 MT Mt bs l Δ T t} : RBwf G Γ l1 l2 MT Mt bs -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t : mott (wrapMt Mt) l Δ T t @ l2 ].
Proof.
  intros (H1 & H2 & HT & Ht & Hc & Hb) Hl HΔ HU Hs.
  apply wf_elimt; auto. exact (mott_wf _ _ _ _ _ _ _ _ Ht Hl HΔ HU Hs).
Qed.

(** [mkrb] is injective in its motives. *)
Lemma mkrb_inj_MT {MT Mt bs MT' Mt' bs'} : mkrb MT Mt bs = mkrb MT' Mt' bs' -> MT = MT' /\ Mt = Mt'.
Proof. unfold mkrb, wrapMT, wrapMt. intros H; injection H; intros; subst; auto. Qed.

(** Variants with explicit arities, for rewriting. *)
Lemma lvren_ush_uext' l n ls φ : length ls = n -> lvsubst (lvren l (ush n)) (uext ls φ) = lvsubst l φ.
Proof. intros <-; apply lvren_ush_uext. Qed.

Lemma motT_wkb_inst' MT nu ng nl ls os xs φ σ e d lv g c :
  length ls = nu -> length os = ng -> length xs = nl -> d = lext xs e ->
  gdnf (gext_s os σ) -> LK dnftm d ->
  ((usubst_ty (motT (wkb nu ng nl (wrapMT MT)) lv g c) (uext ls φ))⦃gext_s os σ⦄)[d] =
  motT (wrapMT ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))])) (lvsubst lv (uext ls φ))
    ((ucsubst g (uext ls φ))⦃gext_s os σ⦄) (((usubst_tm c (uext ls φ))⦃gext_s os σ⦄)[d]).
Proof. intros <- <- <- -> Hσ He. exact (motT_wkb_inst MT ls os xs φ σ e lv g c Hσ He). Qed.

Lemma mott_wkb_inst' Mt nu ng nl ls os xs φ σ e d lv g U c :
  length ls = nu -> length os = ng -> length xs = nl -> d = lext xs e ->
  gdnf (gext_s os σ) -> LK dnftm d ->
  ((usubst_ty (mott (wkb nu ng nl (wrapMt Mt)) lv g U c) (uext ls φ))⦃gext_s os σ⦄)[d] =
  mott (wrapMt ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))]))
    (lvsubst lv (uext ls φ)) ((ucsubst g (uext ls φ))⦃gext_s os σ⦄) ((usubst_ty U (uext ls φ))⦃gext_s os σ⦄)
    (((usubst_tm c (uext ls φ))⦃gext_s os σ⦄)[d]).
Proof. intros <- <- <- -> Hσ He. exact (mott_wkb_inst Mt ls os xs φ σ e lv g U c Hσ He). Qed.

Lemma wkc_inst' nu ng Γ ls os φ σ : length ls = nu -> length os = ng ->
  (ucsubst (wkc nu ng Γ) (uext ls φ))⦃gext_s os σ⦄ = (ucsubst Γ φ)⦃σ⦄.
Proof. exact (wkc_inst nu ng Γ ls os φ σ). Qed.

(** Code pieces substituted by the identity. *)
Lemma subst_lshift0_ty (T : ty) : nfty T -> T[lshift 0] = T.
Proof. intros H; apply subst_id_ty; [exact H | intros; cbn; f_equal; lia]. Qed.
Lemma subst_lshift0 (t : tm) : nftm t -> t[lshift 0] = t.
Proof. intros H; apply subst_id; [exact H | intros; cbn; f_equal; lia]. Qed.
