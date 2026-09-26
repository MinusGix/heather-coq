(** * The recursors' β-reducts are typed (M7_DESIGN.md A2b)

    Discharges [Preservation.RecRedTyped]. A reduct is its branch body at
    extended substitutions ([RecPeel.peel_wrap]):
      [((bs k)[uext ls lvar]ᵤ)⦃gext_s os id⦄[lext xs id]]
    with [ls] the code's levels, [os] the scrutinee's context and the
    code's pieces, [xs] the recursive calls. Its typing ([br_typed]) is the
    branch's typing under the universe, global and local substitution
    lemmas; per code shape, the pieces are typed by inverting the code's
    C-typing, and the recursive calls by the recursor rule at the
    sub-codes (no induction). The type is the branch type's instance,
    which [motT_wkb_inst]/[mott_wkb_inst] identify with the motive at the
    code. *)
From DeLaM.Validity Require Export Preservation.

(** ** Substitution extensions *)

Lemma lsub_wf_lcons {G i Δ d Γ A a l} : [ G ; Δ ⊢[ i ] d : Γ ] -> [ G ; Δ ⊢[ i ] a : A[d] @ l ] ->
  [ G ; Δ ⊢[ i ] lcons d a : Γ ,, A @ l ].
Proof.
  intros [HΔ Hn [Ht1 Ht2] Hv] Ha. constructor; [exact HΔ | intros [|n]; cbn; [exact (wf_tm_dnf Ha) | apply Hn] | |].
  - split; [exact Ht1 |]. intros n. cbn [clen llk Nat.add]. exact (Ht2 n).
  - intros n T l' Hin; inversion Hin as [Γ0 A0 l0 | Γ0 A0 l0 B0 l1 m Hm]; subst; cbn [llk];
      rewrite shift_subst_ldrop1; cbn [ldrop]; [exact Ha | exact (Hv _ _ _ Hm)].
Qed.

Lemma lext_snoc xs a e : lext (xs ++ a :: nil) e = lcons (lext xs e) a.
Proof. unfold lext. rewrite fold_left_app. reflexivity. Qed.

Lemma gext_s_nil σ i : gext_s nil σ i = σ i.
Proof. unfold gext_s; cbn. rewrite Nat.sub_0_r. reflexivity. Qed.

Lemma gsub_wf_snoc {G' G0 os σ D o} : [ G' ⊢ gext_s os σ : G0 ] -> dnfo o ->
  gobj_wf G' o (gdecl_gsubst D (gext_s os σ)) -> [ G' ⊢ gext_s (os ++ o :: nil) σ : gext G0 D ].
Proof.
  intros H Ho Hw. refine (gsub_wf_ext _ (gsub_wf_cons H Ho Hw)).
  intros i; rewrite gext_s_app; destruct i; reflexivity.
Qed.

Lemma gsub_wf_nil {G} : [ ⊢ G ] -> [ G ⊢ gext_s nil gid : G ].
Proof. intros HG. refine (gsub_wf_ext _ (gsub_wf_gid HG)). intros i; rewrite gext_s_nil; reflexivity. Qed.

Lemma G_us_lvar G : [ ⊢ G ] -> G_us G (gL G) lvar = G.
Proof.
  destruct G as [L Ψ]; intros HG. unfold G_us, gctx_usubst; cbn [gL gΨ]. f_equal.
  transitivity (map (fun D => D) Ψ); [| apply map_id].
  apply map_ext_in; intros D HD. apply gdecl_usubst_id, (glob_dnf _ _ HG _ HD).
Qed.

(** ** A branch at typed extensions *)

Lemma br_typed {G Γ l1 l2 MT Mt bs k ls os xs} : RBwf G Γ l1 l2 MT Mt bs -> [ G ; Γ ⊢[ lM ] ] -> k < 13 ->
  length ls = br_nu k -> Forall (lwf (gL G)) ls ->
  [ G ⊢ gext_s os gid : mkG (gL G) (map (fun D => gdecl_usubst D (uext ls lvar)) (brDecls k) ++ gΨ G) ] ->
  [ G ; Γ ⊢[ lM ] lext xs (lshift 0) : (ucsubst (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext ls lvar))⦃gext_s os gid⦄ ] ->
  [ G ; Γ ⊢[ lM ] ((usubst_tm (bs k) (uext ls lvar))⦃gext_s os gid⦄)[lext xs (lshift 0)] :
      ((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls lvar))⦃gext_s os gid⦄)[lext xs (lshift 0)]
      @ lvsubst (brLv k l1 l2) (uext ls lvar) ].
Proof.
  intros (_ & _ & _ & _ & _ & Hb) HΓ Hk Hn Hls Hσ Hd.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (Hφ : usub_ok (uext ls lvar) (gL G) (gL (brG k G))).
  { unfold brG, gctx_uwk; cbn [gL]. rewrite <- Hn. exact (usub_ok_uext ls lvar (gL G) (gL G) Hls (usub_ok_id _)). }
  pose proof (proj1 (proj2 (proj2 (proj2 usubstitution))) _ _ _ _ _ _ (Hb k Hk) _ _ Hφ) as X1.
  rewrite (G_us_brG_uext k G (gL G) lvar ls Hn), (G_us_lvar G HG) in X1.
  assert (Hσ' : [ gwk_to (mkG (gL G) (map (fun D => gdecl_usubst D (uext ls lvar)) (brDecls k) ++ gΨ G)) (gΨ G)
                  ⊢ gext_s os gid : mkG (gL G) (map (fun D => gdecl_usubst D (uext ls lvar)) (brDecls k) ++ gΨ G) ])
    by (destruct G; exact Hσ).
  pose proof (proj1 (proj2 (proj2 (proj2 gsubstitution))) _ _ _ _ _ _ X1 (gΨ G) _ Hσ') as X2.
  unfold gwk_to in X2; cbn [gL] in X2. destruct G as [L Ψ]; cbn [gL gΨ] in *.
  exact (proj1 (proj2 (proj2 (proj2 substitution))) _ _ _ _ _ _ X2 eq_refl _ _ Hd).
Qed.

(** ** The motives at the identity extensions *)

Lemma uup_lvar i : uup lvar i = lvar i.
Proof. destruct i; reflexivity. Qed.

Lemma motive_id_T MT : dnfty MT ->
  (usubst_ty MT (uup lvar))⦃gup (guwk gid)⦄[llift (gwk (uwk (lshift 0)))] = MT.
Proof.
  intros HM. replace (usubst_ty MT (uup lvar)) with MT by (symmetry; exact (usubst_id_ty MT (uup lvar) HM uup_lvar)).
  rewrite (gsubst_id_ty MT _ HM) by (intros [|i]; reflexivity).
  apply subst_id_ty; [exact (dnfty_nfty _ HM) |]. intros n; rewrite llk_llift; destruct n; [reflexivity | cbn; f_equal; lia].
Qed.

Lemma motive_id_t Mt : dnfty Mt ->
  (usubst_ty Mt (uup lvar))⦃gup (gup (guwk gid))⦄[llift (gwk (gwk (uwk (lshift 0))))] = Mt.
Proof.
  intros HM. replace (usubst_ty Mt (uup lvar)) with Mt by (symmetry; exact (usubst_id_ty Mt (uup lvar) HM uup_lvar)).
  rewrite (gsubst_id_ty Mt _ HM) by (intros [|[|i]]; reflexivity).
  apply subst_id_ty; [exact (dnfty_nfty _ HM) |]. intros n; rewrite llk_llift; destruct n; [reflexivity | cbn; f_equal; lia].
Qed.

(** ** The reducts, per code shape *)

Lemma lM_notV : lM <> lV. Proof. discriminate. Qed.
Lemma lwf_suc {L l} : lwf L l -> lwf L (lsuc l). Proof. exact (fun H => H). Qed.

Section RR.
Context {G : gctx} {Γ : ctx} {l1 l2 : lvl} {MT Mt : ty} {bs : nat -> tm}
  (HΓ : [ G ; Γ ⊢[ lM ] ]) (Hrb : RBwf G Γ l1 l2 MT Mt bs).

Lemma HG_rr : [ ⊢ G ]. Proof. exact (ctx_glob _ _ _ HΓ). Qed.
Lemma HMTd : dnfty MT. Proof. destruct Hrb as (_ & _ & H & _); exact (wf_ty_dnf H). Qed.
Lemma HMtd : dnfty Mt. Proof. destruct Hrb as (_ & _ & _ & H & _); exact (wf_ty_dnf H). Qed.
Lemma Hbd k : k < 13 -> dnftm (bs k).
Proof. intros Hk; destruct Hrb as (_ & _ & _ & _ & _ & H); exact (wf_tm_dnf (H k Hk)). Qed.
Lemma Hl1 : lwf (gL G) l1. Proof. exact (proj1 Hrb). Qed.
Lemma Hl2 : lwf (gL G) l2. Proof. exact (proj1 (proj2 Hrb)). Qed.

Lemma Γ_id : (ucsubst Γ lvar)⦃gid⦄ = Γ.
Proof.
  pose proof (wf_ctx_dnf HΓ) as Hd.
  replace (ucsubst Γ lvar) with Γ by (symmetry; exact (usubst_id_ctx Γ lvar Hd (fun _ => eq_refl))).
  exact (gsubst_id_ctx Γ gid Hd (fun _ => eq_refl)).
Qed.

Lemma Γ_id_raw : gcsubst (ucsubst Γ lvar) gid = Γ.
Proof. exact Γ_id. Qed.

Lemma brLv_T_id k ls : k < 4 -> length ls = br_nu k -> lvsubst (brLv k l1 l2) (uext ls lvar) = l1.
Proof.
  intros Hk Hn. unfold brLv. replace (Nat.ltb k 4) with true by (symmetry; apply Nat.ltb_lt, Hk).
  rewrite (lvren_ush_uext' l1 (br_nu k) ls lvar Hn). apply lvsubst_id; reflexivity.
Qed.

Lemma rr_T_nat {l Δ r} : [ G ; Δ ⊢[ lD ] ] -> redT l1 l2 (mkrb MT Mt bs) l Δ tyNat = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) lzero Δ (boxT tyNat) @ l1 ].
Proof.
  intros HΔ Hred.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 0 1 0 (bs 0)) nil) (GCtx Δ :: nil)) nil)
    by (cbn [redT] in Hred; injection Hred as <-; reflexivity).
  subst r.
  rewrite peel_wrap by first [reflexivity | repeat constructor; exact (wf_ctx_dnf HΔ) | exact (Hbd 0 ltac:(lia))].
  pose proof HG_rr as HG.
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext nil lvar)) (brDecls 0) ++ gΨ G) ]).
  { change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil).
    destruct G as [L Ψ]. exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) (wf_ctx_dnf HΔ) HΔ). }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext nil (lshift 0) :
                 (ucsubst (brΓ 0 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext nil lvar))⦃gext_s (GCtx Δ :: nil) gid⦄ ]).
  { cbn [brΓ brLocs cexts br_nu br_ng br_ar lext fold_left].
    rewrite (wkc_inst' 0 1 Γ nil (GCtx Δ :: nil) lvar gid eq_refl eq_refl). rewrite Γ_id.
    exact (lsub_wf_id G lM eq_refl Γ HΓ). }
  pose proof (br_typed (k := 0) (ls := nil) Hrb HΓ ltac:(lia) eq_refl (Forall_nil _) Hσ Hd) as X.
  rewrite (brLv_T_id 0 nil ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (motT_wkb_inst' MT 0 1 0 nil (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [repeat constructor; exact (wf_ctx_dnf HΔ) | intros i; exact I]
                  | apply lk_dnf_lext; [constructor | intros n; exact I]].
  rewrite (motive_id_T MT HMTd) in X. exact X.
Qed.

Lemma HCD' : lle lC lD. Proof. unfold lle; cbn; lia. Qed.

Lemma sl0 (A : ty) : nfty A -> subst_ty A (lshift 0) = A.
Proof. exact (subst_lshift0_ty A). Qed.
Ltac sl0_rw H := rewrite ?(sl0 _ (dnfty_nfty _ H)), ?(subst_lshift0_ty _ (dnfty_nfty _ H)).
Lemma sl0t (t : tm) : nftm t -> subst_tm t (lshift 0) = t.
Proof. exact (subst_lshift0 t). Qed.
Ltac sl0t_rw H := rewrite ?(sl0t _ (dnftm_nftm _ H)), ?(subst_lshift0 _ (dnftm_nftm _ H)).
Ltac sl0t_rw_in H X := rewrite ?(sl0t _ (dnftm_nftm _ H)), ?(subst_lshift0 _ (dnftm_nftm _ H)) in X.
Ltac sl0_rw_in H X := rewrite ?(sl0 _ (dnfty_nfty _ H)), ?(subst_lshift0_ty _ (dnfty_nfty _ H)) in X.

(** A recursive call at a boxed sub-code. *)
Lemma recT_wf {l Δ c} : lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] c @ l ] ->
  [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT c) : motT (wrapMT MT) l Δ (boxT c) @ l1 ].
Proof. intros Hl HΔ Hc. apply (wf_elimT' Hrb Hl HΔ). apply wf_boxT; assumption. Qed.

Lemma rr_T_pi {l Δ k k' A B r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyPi k k' A B @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyPi k k' A B) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) (lmax k k') Δ (boxT (tyPi k k' A B)) @ l1 ].
Proof.
  intros HΔ Hc Hred.
  destruct (inv_ty_pi Hc) as ((_ & Wk & Wk' & HA & HB) & _).
  pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_ctx_dnf HΔ) as HΔd.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (boxT B)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 3 2 (bs 1)) (k :: k' :: nil)) (GCtx Δ :: GTy A :: GTy B :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redT] in Hred; injection Hred as <-; reflexivity).
  subst r.
  pose proof HG_rr as HG.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (recT_wf Wk' HΔA HB) as Hx2.
  pose proof (wf_tm_dnf Hx1) as Hx1d. pose proof (wf_tm_dnf Hx2) as Hx2d. pose proof (Hbd 1 ltac:(lia)) as Hb1.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact Hx1d | exact Hx2d | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | exact Hxs | exact Hb1].
  (* the global substitution *)
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 1) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTy B :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTy (cvar 1 ,, gv 0 @ k) lC k') (o := GTy B)
              (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact HB. }
  (* the local substitution *)
  assert (Hd : [ G ; Γ ⊢[ lM ] lext (x1 :: x2 :: nil) (lshift 0) :
                 (ucsubst (brΓ 1 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext (k :: k' :: nil) lvar))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: nil) gid⦄ ]).
  { change (lext (x1 :: x2 :: nil) (lshift 0)) with (lcons (lcons (lshift 0) x1) x2).
    cbn [brΓ brLocs cexts br_nu br_ng br_ar].
    change ((ucsubst (wkc 2 3 Γ ,, ?T1 @ ?a ,, ?T2 @ ?a) ?φ)⦃?σ⦄)
      with ((ucsubst (wkc 2 3 Γ) φ)⦃σ⦄ ,, (usubst_ty T1 φ)⦃σ⦄ @ lvsubst a φ ,, (usubst_ty T2 φ)⦃σ⦄ @ lvsubst a φ).
    rewrite (wkc_inst' 2 3 Γ (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: nil) lvar gid eq_refl eq_refl), Γ_id.
    apply lsub_wf_lcons; [apply lsub_wf_lcons; [exact (lsub_wf_id G lM eq_refl Γ HΓ) |] |].
    - change (lshift 0) with (lext nil (lshift 0)).
      rewrite (motT_wkb_inst' MT 2 3 0 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: nil) nil lvar gid (lshift 0) _ _ _ _
                 eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [constructor | intros n; exact I]].
      rewrite (motive_id_T MT HMTd). cbn. sl0_rw HAd.
      rewrite (lvren_ush_uext' l1 2 (k :: k' :: nil) lvar eq_refl), (lvsubst_id l1 lvar (fun _ => eq_refl)).
      exact Hx1.
    - change (lcons (lshift 0) x1) with (lext (x1 :: nil) (lshift 0)).
      rewrite (motT_wkb_inst' MT 2 3 1 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: nil) (x1 :: nil) lvar gid (lshift 0)
                 _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_nil _)) | intros n; exact I]].
      rewrite (motive_id_T MT HMTd). cbn. sl0_rw HAd. sl0_rw HBd.
      rewrite (lvren_ush_uext' l1 2 (k :: k' :: nil) lvar eq_refl), (lvsubst_id l1 lvar (fun _ => eq_refl)).
      exact Hx2. }
  pose proof (br_typed (k := 1) (ls := k :: k' :: nil) Hrb HΓ ltac:(lia) eq_refl
                (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Hσ Hd) as X.
  rewrite (brLv_T_id 1 (k :: k' :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (motT_wkb_inst' MT 2 3 2 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: nil) (x1 :: x2 :: nil) lvar gid (lshift 0)
             _ _ _ _ eq_refl eq_refl eq_refl eq_refl) in X
    by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
             | apply lk_dnf_lext; [exact Hxs | intros n; exact I]].
  rewrite (motive_id_T MT HMTd) in X. cbn in X. sl0_rw_in HAd X. sl0_rw_in HBd X. exact X.
Qed.

Lemma rect_wf {l Δ T c} : lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] ->
  [ G ; Δ ⊢[ lC ] c : T @ l ] ->
  [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c) : mott (wrapMt Mt) l Δ T (boxt c) @ l2 ].
Proof. intros Hl HΔ HT Hc. apply (wf_elimt' Hrb Hl HΔ HT). apply wf_boxt; assumption. Qed.

Lemma brLv_t_id k ls : 4 <= k -> length ls = br_nu k -> lvsubst (brLv k l1 l2) (uext ls lvar) = l2.
Proof.
  intros Hk Hn. unfold brLv. replace (Nat.ltb k 4) with false by (symmetry; apply Nat.ltb_ge, Hk).
  rewrite (lvren_ush_uext' l2 (br_nu k) ls lvar Hn). apply lvsubst_id; reflexivity.
Qed.

Lemma rr_T_U {l Δ k r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyU k @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyU k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) (lsuc k) Δ (boxT (tyU k)) @ l1 ].
Proof.
  intros HΔ Hc Hred.
  destruct (inv_ty_U Hc) as ((_ & _ & Wk) & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 1 0 (bs 2)) (k :: nil)) (GCtx Δ :: nil)) nil)
    by (cbn [redT] in Hred; injection Hred as <-; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 2 ltac:(lia)) as Hb2.
  assert (Ho : Forall dnfo (GCtx Δ :: nil)) by (apply Forall_cons; [exact HΔd | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | apply Forall_nil | exact Hb2].
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 2) ++ gΨ G) ]).
  { change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil).
    destruct G as [L Ψ]. exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ). }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext nil (lshift 0) :
                 (ucsubst (brΓ 2 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext (k :: nil) lvar))⦃gext_s (GCtx Δ :: nil) gid⦄ ]).
  { cbn [brΓ brLocs cexts br_nu br_ng br_ar lext fold_left].
    rewrite (wkc_inst' 1 1 Γ (k :: nil) (GCtx Δ :: nil) lvar gid eq_refl eq_refl). rewrite Γ_id.
    exact (lsub_wf_id G lM eq_refl Γ HΓ). }
  pose proof (br_typed (k := 2) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_T_id 2 (k :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (motT_wkb_inst' MT 1 1 0 (k :: nil) (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros n; exact I]].
  rewrite (motive_id_T MT HMTd) in X. exact X.
Qed.

Lemma rr_T_El {l Δ k t r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyEl k t @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyEl k t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tyEl k t)) @ l1 ].
Proof.
  intros HΔ Hc Hred.
  destruct (inv_ty_El Hc) as ((_ & Wk & Ht) & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Ht) as Htd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 2 1 (bs 3)) (k :: nil)) (GCtx Δ :: GTm t :: nil)) (x1 :: nil))
    by (cbn [redT] in Hred; injection Hred as <-; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 3 ltac:(lia)) as Hb3.
  assert (HU : [ G ; Δ ⊢[ lD ] tyU k @ lsuc k ]) by (apply wft_U; [discriminate | exact HΔ | exact Wk]).
  pose proof (rect_wf (lwf_suc Wk) HΔ HU Ht) as Hx1. pose proof (wf_tm_dnf Hx1) as Hx1d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Htd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: nil)) by (apply Forall_cons; [exact Hx1d | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | exact Hxs | exact Hb3].
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 3) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm t :: nil) with ((nil ++ GCtx Δ :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 0) lC (tyU k) (lsuc k)) (o := GTm t)
              (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Htd _).
    cbn. exact Ht. }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext (x1 :: nil) (lshift 0) :
                 (ucsubst (brΓ 3 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext (k :: nil) lvar))⦃gext_s (GCtx Δ :: GTm t :: nil) gid⦄ ]).
  { change (lext (x1 :: nil) (lshift 0)) with (lcons (lshift 0) x1).
    cbn [brΓ brLocs cexts br_nu br_ng br_ar].
    change ((ucsubst (wkc 1 2 Γ ,, ?T1 @ ?a) ?φ)⦃?σ⦄)
      with ((ucsubst (wkc 1 2 Γ) φ)⦃σ⦄ ,, (usubst_ty T1 φ)⦃σ⦄ @ lvsubst a φ).
    rewrite (wkc_inst' 1 2 Γ (k :: nil) (GCtx Δ :: GTm t :: nil) lvar gid eq_refl eq_refl), Γ_id.
    apply lsub_wf_lcons; [exact (lsub_wf_id G lM eq_refl Γ HΓ) |].
    change (lshift 0) with (lext nil (lshift 0)).
    rewrite (mott_wkb_inst' Mt 1 2 0 (k :: nil) (GCtx Δ :: GTm t :: nil) nil lvar gid (lshift 0) _ _ _ _ _
               eq_refl eq_refl eq_refl eq_refl)
      by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros n; exact I]].
    rewrite (motive_id_t Mt HMtd). cbn.
    rewrite (lvren_ush_uext' l2 1 (k :: nil) lvar eq_refl), (lvsubst_id l2 lvar (fun _ => eq_refl)).
    sl0t_rw Htd. exact Hx1. }
  pose proof (br_typed (k := 3) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_T_id 3 (k :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (motT_wkb_inst' MT 1 2 1 (k :: nil) (GCtx Δ :: GTm t :: nil) (x1 :: nil) lvar gid (lshift 0) _ _ _ _
             eq_refl eq_refl eq_refl eq_refl) in X
    by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [exact Hxs | intros n; exact I]].
  rewrite (motive_id_T MT HMTd) in X. cbn in X. sl0t_rw_in Htd X. exact X.
Qed.

End RR.
