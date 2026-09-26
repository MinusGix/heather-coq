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

(** ** Term codes: the reducts at their natural motive instances *)

Lemma rr_t_var {l Δ T n r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] T @ l ] ->
  [ G ; Δ ⊢[ lV ] var n : T @ l ] -> redt l1 l2 (mkrb MT Mt bs) l Δ T (var n) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) l Δ T (boxt (var n)) @ l2 ].
Proof.
  intros HΔ Wl HT HV Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HT) as HTd. pose proof (wf_tm_dnf HV) as HVd.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 0 (bs 4)) (l :: nil)) (GCtx Δ :: GTy T :: GTm (var n) :: nil)) nil)
    by (cbn [redt] in Hred; injection Hred as <-; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 4 ltac:(lia)) as Hb.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy T :: GTm (var n) :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HTd | exact HVd | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | apply Forall_nil | exact Hb].
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy T :: GTm (var n) :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (l :: nil) lvar)) (brDecls 4) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy T :: GTm (var n) :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy T :: nil) ++ GTm (var n) :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lV (gv 0) l) (o := GTm (var n))
              (gsub_wf_snoc (D := gdTy (cvar 0) lD l) (o := GTy T)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HTd _) HVd _).
    - cbn. exact HT.
    - cbn. sl0_rw HTd. exact HV. }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext nil (lshift 0) :
                 (ucsubst (brΓ 4 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext (l :: nil) lvar))⦃gext_s (GCtx Δ :: GTy T :: GTm (var n) :: nil) gid⦄ ]).
  { cbn [brΓ brLocs cexts br_nu br_ng br_ar lext fold_left].
    rewrite (wkc_inst' 1 3 Γ (l :: nil) (GCtx Δ :: GTy T :: GTm (var n) :: nil) lvar gid eq_refl eq_refl). rewrite Γ_id.
    exact (lsub_wf_id G lM eq_refl Γ HΓ). }
  pose proof (br_typed (k := 4) (ls := l :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wl (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_t_id 4 (l :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 1 3 0 (l :: nil) (GCtx Δ :: GTy T :: GTm (var n) :: nil) nil lvar gid (lshift 0) _ _ _ _ _
             eq_refl eq_refl eq_refl eq_refl) in X
    by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. cbn in X. sl0_rw_in HTd X. rewrite Nat.add_0_r in X. exact X.
Qed.

(** The codes without pieces: the branch at the context alone. *)
Ltac rr_t_closed k nu ls :=
  intros;
  match goal with HΔ : [ _ ; ?Δ ⊢[ lD ] ], Hred : redt _ _ _ _ _ _ _ = Some ?r |- _ =>
    let HΔd := fresh "HΔd" in let Er := fresh "Er" in let HG := fresh "HG" in let Hb := fresh "Hb" in
    let Ho := fresh "Ho" in let Hσ := fresh "Hσ" in let Hd := fresh "Hd" in let X := fresh "X" in
    pose proof (wf_ctx_dnf HΔ) as HΔd;
    assert (Er : r = peelLs (peelGs (peelUs (wrap nu 1 0 (bs k)) ls) (GCtx Δ :: nil)) nil)
      by (cbn [redt] in Hred; injection Hred as <-; reflexivity);
    subst r; pose proof HG_rr as HG; pose proof (Hbd k ltac:(lia)) as Hb;
    assert (Ho : Forall dnfo (GCtx Δ :: nil)) by (apply Forall_cons; [exact HΔd | apply Forall_nil]);
    rewrite peel_wrap by first [reflexivity | exact Ho | apply Forall_nil | exact Hb];
    assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                   mkG (gL G) (map (fun D => gdecl_usubst D (uext ls lvar)) (brDecls k) ++ gΨ G) ])
      by (change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil);
          destruct G as [L Ψ]; exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ));
    assert (Hd : [ G ; Γ ⊢[ lM ] lext nil (lshift 0) :
                   (ucsubst (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext ls lvar))⦃gext_s (GCtx Δ :: nil) gid⦄ ])
      by (cbn [brΓ brLocs cexts br_nu br_ng br_ar lext fold_left];
          rewrite (wkc_inst' nu 1 Γ ls (GCtx Δ :: nil) lvar gid eq_refl eq_refl); rewrite Γ_id;
          exact (lsub_wf_id G lM eq_refl Γ HΓ))
  end.

Lemma rr_t_nat {l Δ T r} : [ G ; Δ ⊢[ lD ] ] -> redt l1 l2 (mkrb MT Mt bs) l Δ T tmNat = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc lzero) Δ (tyU lzero) (boxt tmNat) @ l2 ].
Proof.
  rr_t_closed 5 0 (@nil lvl).
  pose proof (br_typed (k := 5) (ls := nil) Hrb HΓ ltac:(lia) eq_refl (Forall_nil _) Hσ Hd) as X.
  rewrite (brLv_t_id 5 nil ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 0 1 0 nil (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

Lemma rr_t_zero {l Δ T r} : [ G ; Δ ⊢[ lD ] ] -> redt l1 l2 (mkrb MT Mt bs) l Δ T zero = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) lzero Δ tyNat (boxt zero) @ l2 ].
Proof.
  rr_t_closed 8 0 (@nil lvl).
  pose proof (br_typed (k := 8) (ls := nil) Hrb HΓ ltac:(lia) eq_refl (Forall_nil _) Hσ Hd) as X.
  rewrite (brLv_t_id 8 nil ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 0 1 0 nil (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

Lemma rr_t_U {l Δ T k r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> redt l1 l2 (mkrb MT Mt bs) l Δ T (tmU k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc (lsuc k)) Δ (tyU (lsuc k)) (boxt (tmU k)) @ l2 ].
Proof.
  intros HΔ0 Wk. rr_t_closed 7 1 (k :: nil).
  pose proof (br_typed (k := 7) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_t_id 7 (k :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 1 1 0 (k :: nil) (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

(** The type of a C-typed term, at D. *)
Lemma ctm_ty {Δ c T l} : [ G ; Δ ⊢[ lC ] c : T @ l ] -> [ G ; Δ ⊢[ lD ] T @ l ].
Proof. intros H. exact (wf_tm_ty (i := lD) eq_refl (lift_tm H HCD')). Qed.

Lemma rr_t_succ {l Δ T t r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] t : tyNat @ lzero ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (succ t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) lzero Δ tyNat (boxt (succ t)) @ l2 ].
Proof.
  intros HΔ Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Ht) as Htd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 0 2 1 (bs 9)) nil) (GCtx Δ :: GTm t :: nil)) (x1 :: nil))
    by (cbn [redt] in Hred; injection Hred as <-; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 9 ltac:(lia)) as Hb.
  pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Ht) Ht) as Hx1. pose proof (wf_tm_dnf Hx1) as Hx1d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Htd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: nil)) by (apply Forall_cons; [exact Hx1d | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | exact Hxs | exact Hb].
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext nil lvar)) (brDecls 9) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm t :: nil) with ((nil ++ GCtx Δ :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 0) lC tyNat lzero) (o := GTm t)
              (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Htd _).
    cbn. exact Ht. }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext (x1 :: nil) (lshift 0) :
                 (ucsubst (brΓ 9 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext nil lvar))⦃gext_s (GCtx Δ :: GTm t :: nil) gid⦄ ]).
  { change (lext (x1 :: nil) (lshift 0)) with (lcons (lshift 0) x1).
    cbn [brΓ brLocs cexts br_nu br_ng br_ar].
    change ((ucsubst (wkc 0 2 Γ ,, ?T1 @ ?a) ?φ)⦃?σ⦄)
      with ((ucsubst (wkc 0 2 Γ) φ)⦃σ⦄ ,, (usubst_ty T1 φ)⦃σ⦄ @ lvsubst a φ).
    rewrite (wkc_inst' 0 2 Γ nil (GCtx Δ :: GTm t :: nil) lvar gid eq_refl eq_refl), Γ_id.
    apply lsub_wf_lcons; [exact (lsub_wf_id G lM eq_refl Γ HΓ) |].
    change (lshift 0) with (lext nil (lshift 0)).
    rewrite (mott_wkb_inst' Mt 0 2 0 nil (GCtx Δ :: GTm t :: nil) nil lvar gid (lshift 0) _ _ _ _ _
               eq_refl eq_refl eq_refl eq_refl)
      by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros n; exact I]].
    rewrite (motive_id_t Mt HMtd). cbn.
    rewrite (lvren_ush_uext' l2 0 nil lvar eq_refl), (lvsubst_id l2 lvar (fun _ => eq_refl)).
    sl0t_rw Htd. exact Hx1. }
  pose proof (br_typed (k := 9) (ls := nil) Hrb HΓ ltac:(lia) eq_refl (Forall_nil _) Hσ Hd) as X.
  rewrite (brLv_t_id 9 nil ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 0 2 1 nil (GCtx Δ :: GTm t :: nil) (x1 :: nil) lvar gid (lshift 0) _ _ _ _ _
             eq_refl eq_refl eq_refl eq_refl) in X
    by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [exact Hxs | intros n; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. cbn in X. sl0t_rw_in Htd X. exact X.
Qed.

Lemma rr_t_pi {l Δ T k k' s t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmPi k k' s t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc (lmax k k')) Δ (tyU (lmax k k')) (boxt (tmPi k k' s t)) @ l2 ].
Proof.
  intros HΔ Wk Wk' Hs Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Hs) as Hsd. pose proof (wf_tm_dnf Ht) as Htd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k') (Δ ,, tyEl k s @ k) (tyU k') (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 3 2 (bs 6)) (k :: k' :: nil)) (GCtx Δ :: GTm s :: GTm t :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; injection Hred as <-; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 6 ltac:(lia)) as Hb.
  assert (HΔs : [ G ; Δ ,, tyEl k s @ k ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | apply wft_El; [discriminate | exact Wk | exact (lift_tm Hs HCD')] | exact Wk]).
  pose proof (rect_wf (lwf_suc Wk) HΔ (ctm_ty Hs) Hs) as Hx1.
  pose proof (rect_wf (lwf_suc Wk') HΔs (ctm_ty Ht) Ht) as Hx2.
  pose proof (wf_tm_dnf Hx1) as Hx1d. pose proof (wf_tm_dnf Hx2) as Hx2d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm s :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Hsd | exact Htd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact Hx1d | exact Hx2d | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | exact Hxs | exact Hb].
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm s :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 6) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm s :: GTm t :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTm s :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1 ,, tyEl k (gu 0) @ k) lC (tyU k') (lsuc k')) (o := GTm t)
              (gsub_wf_snoc (D := gdTm (cvar 0) lC (tyU k) (lsuc k)) (o := GTm s)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Hsd _) Htd _).
    - cbn. exact Hs.
    - cbn. sl0t_rw Hsd. exact Ht. }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext (x1 :: x2 :: nil) (lshift 0) :
                 (ucsubst (brΓ 6 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext (k :: k' :: nil) lvar))⦃gext_s (GCtx Δ :: GTm s :: GTm t :: nil) gid⦄ ]).
  { change (lext (x1 :: x2 :: nil) (lshift 0)) with (lcons (lcons (lshift 0) x1) x2).
    cbn [brΓ brLocs cexts br_nu br_ng br_ar].
    change ((ucsubst (wkc 2 3 Γ ,, ?T1 @ ?a ,, ?T2 @ ?a) ?φ)⦃?σ⦄)
      with ((ucsubst (wkc 2 3 Γ) φ)⦃σ⦄ ,, (usubst_ty T1 φ)⦃σ⦄ @ lvsubst a φ ,, (usubst_ty T2 φ)⦃σ⦄ @ lvsubst a φ).
    rewrite (wkc_inst' 2 3 Γ (k :: k' :: nil) (GCtx Δ :: GTm s :: GTm t :: nil) lvar gid eq_refl eq_refl), Γ_id.
    apply lsub_wf_lcons; [apply lsub_wf_lcons; [exact (lsub_wf_id G lM eq_refl Γ HΓ) |] |].
    - change (lshift 0) with (lext nil (lshift 0)).
      rewrite (mott_wkb_inst' Mt 2 3 0 (k :: k' :: nil) (GCtx Δ :: GTm s :: GTm t :: nil) nil lvar gid (lshift 0) _ _ _ _ _
                 eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros n; exact I]].
      rewrite (motive_id_t Mt HMtd). cbn. sl0t_rw Hsd.
      rewrite (lvren_ush_uext' l2 2 (k :: k' :: nil) lvar eq_refl), (lvsubst_id l2 lvar (fun _ => eq_refl)).
      exact Hx1.
    - change (lcons (lshift 0) x1) with (lext (x1 :: nil) (lshift 0)).
      rewrite (mott_wkb_inst' Mt 2 3 1 (k :: k' :: nil) (GCtx Δ :: GTm s :: GTm t :: nil) (x1 :: nil) lvar gid (lshift 0)
                 _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_nil _)) | intros n; exact I]].
      rewrite (motive_id_t Mt HMtd). cbn. sl0t_rw Hsd. sl0t_rw Htd.
      rewrite (lvren_ush_uext' l2 2 (k :: k' :: nil) lvar eq_refl), (lvsubst_id l2 lvar (fun _ => eq_refl)).
      exact Hx2. }
  pose proof (br_typed (k := 6) (ls := k :: k' :: nil) Hrb HΓ ltac:(lia) eq_refl
                (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Hσ Hd) as X.
  rewrite (brLv_t_id 6 (k :: k' :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 2 3 2 (k :: k' :: nil) (GCtx Δ :: GTm s :: GTm t :: nil) (x1 :: x2 :: nil) lvar gid (lshift 0)
             _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl) in X
    by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [exact Hxs | intros n; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. cbn in X. sl0t_rw_in Hsd X. sl0t_rw_in Htd X. exact X.
Qed.

Lemma rr_t_natrec {l Δ T k M s z t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ,, tyNat @ lzero ⊢[ lC ] M @ k ] -> [ G ; Δ ⊢[ lC ] s : M[lsingle zero] @ k ] ->
  [ G ; Δ ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z : M[lsucc] @ k ] -> [ G ; Δ ⊢[ lC ] t : tyNat @ lzero ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (natrec k M s z t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ M[lsingle t] (boxt (natrec k M s z t)) @ l2 ].
Proof.
  intros HΔ Wk HM Hs Hz Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HM) as HMd.
  pose proof (wf_tm_dnf Hs) as Hsd. pose proof (wf_tm_dnf Hz) as Hzd. pose proof (wf_tm_dnf Ht) as Htd.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k (Δ ,, tyNat @ lzero) (boxT M)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ (subst_ty M (lsingle zero)) (boxt s)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k (Δ ,, tyNat @ lzero ,, M @ k) (subst_ty M lsucc) (boxt z)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 5 4 (bs 10)) (k :: nil))
                             (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil)) (x1 :: x2 :: x3 :: x4 :: nil))
    by (cbn [redt] in Hred; injection Hred as <-; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 10 ltac:(lia)) as Hb.
  assert (HΔN : [ G ; Δ ,, tyNat @ lzero ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | apply wft_nat; [discriminate | exact HΔ] | exact I]).
  assert (HΔNM : [ G ; Δ ,, tyNat @ lzero ,, M @ k ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔN | exact (lift_ty HM HCD') | exact Wk]).
  pose proof (recT_wf Wk HΔN HM) as Hx1.
  pose proof (rect_wf Wk HΔ (ctm_ty Hs) Hs) as Hx2.
  pose proof (rect_wf Wk HΔNM (ctm_ty Hz) Hz) as Hx3.
  pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Ht) Ht) as Hx4.
  pose proof (wf_tm_dnf Hx1) as Hx1d. pose proof (wf_tm_dnf Hx2) as Hx2d.
  pose proof (wf_tm_dnf Hx3) as Hx3d. pose proof (wf_tm_dnf Hx4) as Hx4d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HMd | exact Hsd | exact Hzd | exact Htd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: nil))
    by (repeat apply Forall_cons; [exact Hx1d | exact Hx2d | exact Hx3d | exact Hx4d | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | exact Hxs | exact Hb].
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 10) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil)
      with (((((nil ++ GCtx Δ :: nil) ++ GTy M :: nil) ++ GTm s :: nil) ++ GTm z :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 3) lC tyNat lzero) (o := GTm t)
             (gsub_wf_snoc (D := gdTm (cvar 2 ,, tyNat @ lzero ,, gv 1 @ k) lC (tyGvar 1 lsucc) k) (o := GTm z)
               (gsub_wf_snoc (D := gdTm (cvar 1) lC (tyGvar 0 (lsingle zero)) k) (o := GTm s)
                 (gsub_wf_snoc (D := gdTy (cvar 0 ,, tyNat @ lzero) lC k) (o := GTy M)
                   (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HMd _) Hsd _) Hzd _) Htd _).
    - cbn. exact HM.
    - cbn. exact Hs.
    - cbn. sl0_rw HMd. exact Hz.
    - cbn. exact Ht. }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext (x1 :: x2 :: x3 :: x4 :: nil) (lshift 0) :
                 (ucsubst (brΓ 10 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext (k :: nil) lvar))⦃gext_s (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) gid⦄ ]).
  { change (lext (x1 :: x2 :: x3 :: x4 :: nil) (lshift 0)) with (lcons (lcons (lcons (lcons (lshift 0) x1) x2) x3) x4).
    cbn [brΓ brLocs cexts br_nu br_ng br_ar].
    change ((ucsubst (wkc 1 5 Γ ,, ?T1 @ ?a ,, ?T2 @ ?b ,, ?T3 @ ?b ,, ?T4 @ ?b) ?φ)⦃?σ⦄)
      with ((ucsubst (wkc 1 5 Γ) φ)⦃σ⦄ ,, (usubst_ty T1 φ)⦃σ⦄ @ lvsubst a φ ,, (usubst_ty T2 φ)⦃σ⦄ @ lvsubst b φ
              ,, (usubst_ty T3 φ)⦃σ⦄ @ lvsubst b φ ,, (usubst_ty T4 φ)⦃σ⦄ @ lvsubst b φ).
    rewrite (wkc_inst' 1 5 Γ (k :: nil) (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) lvar gid eq_refl eq_refl), Γ_id.
    rewrite (lvren_ush_uext' l1 1 (k :: nil) lvar eq_refl), (lvsubst_id l1 lvar (fun _ => eq_refl)).
    rewrite (lvren_ush_uext' l2 1 (k :: nil) lvar eq_refl), (lvsubst_id l2 lvar (fun _ => eq_refl)).
    apply lsub_wf_lcons; [apply lsub_wf_lcons; [apply lsub_wf_lcons; [apply lsub_wf_lcons;
      [exact (lsub_wf_id G lM eq_refl Γ HΓ) |] |] |] |].
    - change (lshift 0) with (lext nil (lshift 0)).
      rewrite (motT_wkb_inst' MT 1 5 0 (k :: nil) (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) nil lvar gid
                 (lshift 0) _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros n; exact I]].
      rewrite (motive_id_T MT HMTd). cbn. sl0_rw HMd. exact Hx1.
    - change (lcons (lshift 0) x1) with (lext (x1 :: nil) (lshift 0)).
      rewrite (mott_wkb_inst' Mt 1 5 1 (k :: nil) (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) (x1 :: nil) lvar gid
                 (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_nil _)) | intros n; exact I]].
      rewrite (motive_id_t Mt HMtd). cbn. sl0t_rw Hsd. exact Hx2.
    - change (lcons (lcons (lshift 0) x1) x2) with (lext (x1 :: x2 :: nil) (lshift 0)).
      rewrite (mott_wkb_inst' Mt 1 5 2 (k :: nil) (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) (x1 :: x2 :: nil)
                 lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_cons _ Hx2d (Forall_nil _))) | intros n; exact I]].
      rewrite (motive_id_t Mt HMtd). cbn. sl0_rw HMd. sl0t_rw Hzd. exact Hx3.
    - change (lcons (lcons (lcons (lshift 0) x1) x2) x3) with (lext (x1 :: x2 :: x3 :: nil) (lshift 0)).
      rewrite (mott_wkb_inst' Mt 1 5 3 (k :: nil) (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) (x1 :: x2 :: x3 :: nil)
                 lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_cons _ Hx2d (Forall_cons _ Hx3d (Forall_nil _))))
                                      | intros n; exact I]].
      rewrite (motive_id_t Mt HMtd). cbn. sl0t_rw Htd. exact Hx4. }
  pose proof (br_typed (k := 10) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_t_id 10 (k :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 1 5 4 (k :: nil) (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) (x1 :: x2 :: x3 :: x4 :: nil)
             lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl) in X
    by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [exact Hxs | intros n; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. cbn in X.
  sl0_rw_in HMd X. sl0t_rw_in Hsd X. sl0t_rw_in Hzd X. sl0t_rw_in Htd X. exact X.
Qed.

Lemma rr_t_lam {l Δ k k' A b k1 k2 A1 B r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lD ] B @ k' ] -> [ G ; Δ ,, A @ k ⊢[ lC ] b : B @ k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ (tyPi k1 k2 A1 B) (lam k k' A b) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lmax k k') Δ (tyPi k k' A B) (boxt (lam k k' A b)) @ l2 ].
Proof.
  intros HΔ Wk Wk' HA HB Hbt Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_tm_dnf Hbt) as Hbtd.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) B (boxt b)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 4 2 (bs 11)) (k :: k' :: nil)) (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; injection Hred as <-; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 11 ltac:(lia)) as Hb.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf Wk' HΔA HB Hbt) as Hx2.
  pose proof (wf_tm_dnf Hx1) as Hx1d. pose proof (wf_tm_dnf Hx2) as Hx2d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact Hbtd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil)) by (repeat apply Forall_cons; [exact Hx1d | exact Hx2d | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | exact Hxs | exact Hb].
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 11) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil)
      with ((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil) ++ GTm b :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 2 ,, gv 1 @ k) lC (gv 0) k') (o := GTm b)
             (gsub_wf_snoc (D := gdTy (cvar 1 ,, gv 0 @ k) lD k') (o := GTy B)
               (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _) Hbtd _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact HB.
    - cbn. sl0_rw HAd. sl0_rw HBd. exact Hbt. }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext (x1 :: x2 :: nil) (lshift 0) :
                 (ucsubst (brΓ 11 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext (k :: k' :: nil) lvar))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) gid⦄ ]).
  { change (lext (x1 :: x2 :: nil) (lshift 0)) with (lcons (lcons (lshift 0) x1) x2).
    cbn [brΓ brLocs cexts br_nu br_ng br_ar].
    change ((ucsubst (wkc 2 4 Γ ,, ?T1 @ ?a ,, ?T2 @ ?b) ?φ)⦃?σ⦄)
      with ((ucsubst (wkc 2 4 Γ) φ)⦃σ⦄ ,, (usubst_ty T1 φ)⦃σ⦄ @ lvsubst a φ ,, (usubst_ty T2 φ)⦃σ⦄ @ lvsubst b φ).
    rewrite (wkc_inst' 2 4 Γ (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) lvar gid eq_refl eq_refl), Γ_id.
    rewrite (lvren_ush_uext' l1 2 (k :: k' :: nil) lvar eq_refl), (lvsubst_id l1 lvar (fun _ => eq_refl)).
    rewrite (lvren_ush_uext' l2 2 (k :: k' :: nil) lvar eq_refl), (lvsubst_id l2 lvar (fun _ => eq_refl)).
    apply lsub_wf_lcons; [apply lsub_wf_lcons; [exact (lsub_wf_id G lM eq_refl Γ HΓ) |] |].
    - change (lshift 0) with (lext nil (lshift 0)).
      rewrite (motT_wkb_inst' MT 2 4 0 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) nil lvar gid (lshift 0)
                 _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros n; exact I]].
      rewrite (motive_id_T MT HMTd). cbn. sl0_rw HAd. exact Hx1.
    - change (lcons (lshift 0) x1) with (lext (x1 :: nil) (lshift 0)).
      rewrite (mott_wkb_inst' Mt 2 4 1 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) (x1 :: nil) lvar gid
                 (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_nil _)) | intros n; exact I]].
      rewrite (motive_id_t Mt HMtd). cbn. sl0_rw HAd. sl0_rw HBd. sl0t_rw Hbtd. exact Hx2. }
  pose proof (br_typed (k := 11) (ls := k :: k' :: nil) Hrb HΓ ltac:(lia) eq_refl
                (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Hσ Hd) as X.
  rewrite (brLv_t_id 11 (k :: k' :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 2 4 2 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) (x1 :: x2 :: nil) lvar gid
             (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl) in X
    by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [exact Hxs | intros n; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. cbn in X. sl0_rw_in HAd X. sl0_rw_in HBd X. sl0t_rw_in Hbtd X. exact X.
Qed.

Lemma rr_t_app {l Δ T k k' A B f a r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ⊢[ lC ] f : tyPi k k' A B @ lmax k k' ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (app f k k' A B a) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k' Δ B[lsingle a] (boxt (app f k k' A B a)) @ l2 ].
Proof.
  intros HΔ Wk Wk' HA HB Hf Ha Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_tm_dnf Hf) as Hfd. pose proof (wf_tm_dnf Ha) as Had.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (boxT B)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) (lmax k k') Δ (tyPi k k' A B) (boxt f)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 5 4 (bs 12)) (k :: k' :: nil))
                             (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil)) (x1 :: x2 :: x3 :: x4 :: nil))
    by (cbn [redt] in Hred; injection Hred as <-; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 12 ltac:(lia)) as Hb.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (Wkk : lwf (gL G) (lmax k k')) by (split; assumption).
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (recT_wf Wk' HΔA HB) as Hx2.
  pose proof (rect_wf Wkk HΔ (ctm_ty Hf) Hf) as Hx3. pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx4.
  pose proof (wf_tm_dnf Hx1) as Hx1d. pose proof (wf_tm_dnf Hx2) as Hx2d.
  pose proof (wf_tm_dnf Hx3) as Hx3d. pose proof (wf_tm_dnf Hx4) as Hx4d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact Hfd | exact Had | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: nil))
    by (repeat apply Forall_cons; [exact Hx1d | exact Hx2d | exact Hx3d | exact Hx4d | apply Forall_nil]).
  rewrite peel_wrap by first [reflexivity | exact Ho | exact Hxs | exact Hb].
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 12) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil)
      with (((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil) ++ GTm f :: nil) ++ GTm a :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 3) lC (gv 2) k) (o := GTm a)
             (gsub_wf_snoc (D := gdTm (cvar 2) lC (tyPi k k' (gv 1) (gv 0)) (lmax k k')) (o := GTm f)
               (gsub_wf_snoc (D := gdTy (cvar 1 ,, gv 0 @ k) lC k') (o := GTy B)
                 (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                   (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _) Hfd _) Had _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact HB.
    - cbn. sl0_rw HAd. sl0_rw HBd. exact Hf.
    - cbn. sl0_rw HAd. exact Ha. }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext (x1 :: x2 :: x3 :: x4 :: nil) (lshift 0) :
                 (ucsubst (brΓ 12 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext (k :: k' :: nil) lvar))⦃gext_s (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil) gid⦄ ]).
  { change (lext (x1 :: x2 :: x3 :: x4 :: nil) (lshift 0)) with (lcons (lcons (lcons (lcons (lshift 0) x1) x2) x3) x4).
    cbn [brΓ brLocs cexts br_nu br_ng br_ar].
    change ((ucsubst (wkc 2 5 Γ ,, ?T1 @ ?a ,, ?T2 @ ?a ,, ?T3 @ ?b ,, ?T4 @ ?b) ?φ)⦃?σ⦄)
      with ((ucsubst (wkc 2 5 Γ) φ)⦃σ⦄ ,, (usubst_ty T1 φ)⦃σ⦄ @ lvsubst a φ ,, (usubst_ty T2 φ)⦃σ⦄ @ lvsubst a φ
              ,, (usubst_ty T3 φ)⦃σ⦄ @ lvsubst b φ ,, (usubst_ty T4 φ)⦃σ⦄ @ lvsubst b φ).
    rewrite (wkc_inst' 2 5 Γ (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil) lvar gid eq_refl eq_refl), Γ_id.
    rewrite (lvren_ush_uext' l1 2 (k :: k' :: nil) lvar eq_refl), (lvsubst_id l1 lvar (fun _ => eq_refl)).
    rewrite (lvren_ush_uext' l2 2 (k :: k' :: nil) lvar eq_refl), (lvsubst_id l2 lvar (fun _ => eq_refl)).
    apply lsub_wf_lcons; [apply lsub_wf_lcons; [apply lsub_wf_lcons; [apply lsub_wf_lcons;
      [exact (lsub_wf_id G lM eq_refl Γ HΓ) |] |] |] |].
    - change (lshift 0) with (lext nil (lshift 0)).
      rewrite (motT_wkb_inst' MT 2 5 0 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil) nil lvar gid
                 (lshift 0) _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros n; exact I]].
      rewrite (motive_id_T MT HMTd). cbn. sl0_rw HAd. exact Hx1.
    - change (lcons (lshift 0) x1) with (lext (x1 :: nil) (lshift 0)).
      rewrite (motT_wkb_inst' MT 2 5 1 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (x1 :: nil)
                 lvar gid (lshift 0) _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_nil _)) | intros n; exact I]].
      rewrite (motive_id_T MT HMTd). cbn. sl0_rw HAd. sl0_rw HBd. exact Hx2.
    - change (lcons (lcons (lshift 0) x1) x2) with (lext (x1 :: x2 :: nil) (lshift 0)).
      rewrite (mott_wkb_inst' Mt 2 5 2 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil)
                 (x1 :: x2 :: nil) lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_cons _ Hx2d (Forall_nil _))) | intros n; exact I]].
      rewrite (motive_id_t Mt HMtd). cbn. sl0_rw HAd. sl0_rw HBd. sl0t_rw Hfd. exact Hx3.
    - change (lcons (lcons (lcons (lshift 0) x1) x2) x3) with (lext (x1 :: x2 :: x3 :: nil) (lshift 0)).
      rewrite (mott_wkb_inst' Mt 2 5 3 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil)
                 (x1 :: x2 :: x3 :: nil) lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
        by first [apply gdnf_gext_s; [exact Ho | intros i; exact I]
                 | apply lk_dnf_lext; [exact (Forall_cons _ Hx1d (Forall_cons _ Hx2d (Forall_cons _ Hx3d (Forall_nil _))))
                                      | intros n; exact I]].
      rewrite (motive_id_t Mt HMtd). cbn. sl0_rw HAd. sl0t_rw Had. exact Hx4. }
  pose proof (br_typed (k := 12) (ls := k :: k' :: nil) Hrb HΓ ltac:(lia) eq_refl
                (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Hσ Hd) as X.
  rewrite (brLv_t_id 12 (k :: k' :: nil) ltac:(lia) eq_refl) in X. cbn [brRes] in X.
  rewrite (mott_wkb_inst' Mt 2 5 4 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil)
             (x1 :: x2 :: x3 :: x4 :: nil) lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl) in X
    by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [exact Hxs | intros n; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. cbn in X.
  sl0_rw_in HAd X. sl0_rw_in HBd X. sl0t_rw_in Hfd X. sl0t_rw_in Had X. exact X.
Qed.

End RR.
