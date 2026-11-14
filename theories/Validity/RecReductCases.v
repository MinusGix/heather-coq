(** * The recursors' β-reducts are typed: the cases (M7_DESIGN.md A2b)

    The per-shape lemmas behind [RecReduct.rec_red_typed], which need
    neither conversion's algorithm nor [Preservation], so they build
    beside them. A reduct is its branch body at
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
From DeLaM.Validity Require Export AlgPrereq DeclConsequences.

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

(** ** A branch's global payloads, generically (M15b step 0)

    As [RecS.GS_br] for the relation: [GWall G' σ ds os] says each payload
    in [os] is normal and fits its declaration's image, oldest first,
    extending the substitution as it goes; [GW_br] turns it into the
    branch scope's substitution typing, and [gw_solve] proves it from the
    payloads' typings ([gs_norm] computes the images). *)
Fixpoint GWall G' (σ : gsub) (ds : list gdecl) (os : list gobj) : Prop :=
  match ds, os with
  | nil, nil => True
  | D :: ds, o :: os => dnfo o /\ gobj_wf G' o (gdecl_gsubst D σ) /\ GWall G' (gcons σ o) ds os
  | _, _ => False
  end.

Lemma GWall_wf G' L : forall ds os Ψ σ, [ G' ⊢ σ : mkG L Ψ ] -> GWall G' σ ds os ->
  [ G' ⊢ gext_s os σ : mkG L (rev ds ++ Ψ) ].
Proof.
  induction ds as [|D ds IH]; intros [|o os] Ψ σ Hσ H; try contradiction.
  - exact (gsub_wf_ext (fun i => eq_sym (gext_s_nil σ i)) Hσ).
  - destruct H as (Ho & Hw & H).
    assert (Hσ' : [ G' ⊢ gcons σ o : mkG L (D :: Ψ) ]) by exact (gsub_wf_cons Hσ Ho Hw).
    pose proof (IH _ _ _ Hσ' H) as X. cbn [rev]. rewrite <- app_assoc.
    exact (gsub_wf_ext (fun i => eq_sym (gext_s_cons _ _ _ i)) X).
Qed.

Lemma GW_br {G} k ls os : [ ⊢ G ] ->
  GWall G gid (rev (map (fun D => gdecl_usubst D (uext ls lvar)) (brDecls k))) os ->
  [ G ⊢ gext_s os gid : mkG (gL G) (map (fun D => gdecl_usubst D (uext ls lvar)) (brDecls k) ++ gΨ G) ].
Proof.
  intros HG H. destruct G as [L Ψ].
  pose proof (GWall_wf _ L _ _ Ψ gid (gsub_wf_gid HG) H) as X. rewrite rev_involutive in X. exact X.
Qed.

Ltac gw_solve :=
  gs_dnf;
  cbn [rev List.app map brDecls GWall gdecl_usubst gdecl_gsubst uext lvsubst Nat.ltb Nat.leb length nth Nat.sub
       gobj_wf dnfo];
  repeat split; first [assumption | eapply wf_ctx_dnf; eassumption | gs_norm; assumption].
Ltac rr_dnf :=
  repeat (apply Forall_cons;
          [cbn [dnfo]; first [eapply wf_ctx_dnf; eassumption | eapply wf_ty_dnf; eassumption
                             | eapply wf_tm_dnf; eassumption] |]);
  apply Forall_nil.

(** ** A branch at typed extensions *)

Lemma br_typed {G Γ l1 l2 MT Mt bs k ls os xs} : RBwf G Γ l1 l2 MT Mt bs -> [ G ; Γ ⊢[ lM ] ] -> k < nbr ->
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

Lemma HG_rr : [ ⊢ G ]. Proof using HΓ. exact (ctx_glob _ _ _ HΓ). Qed.
Lemma HMTd : dnfty MT. Proof using Hrb. destruct Hrb as (_ & _ & H & _); exact (wf_ty_dnf H). Qed.
Lemma HMtd : dnfty Mt. Proof using Hrb. destruct Hrb as (_ & _ & _ & H & _); exact (wf_ty_dnf H). Qed.
Lemma Hbd k : k < nbr -> dnftm (bs k).
Proof using Hrb. intros Hk; destruct Hrb as (_ & _ & _ & _ & _ & H); exact (wf_tm_dnf (H k Hk)). Qed.
Lemma Hl1 : lwf (gL G) l1. Proof using Hrb. exact (proj1 Hrb). Qed.
Lemma Hl2 : lwf (gL G) l2. Proof using Hrb. exact (proj1 (proj2 Hrb)). Qed.

Lemma Γ_id : (ucsubst Γ lvar)⦃gid⦄ = Γ.
Proof using HΓ.
  pose proof (wf_ctx_dnf HΓ) as Hd.
  replace (ucsubst Γ lvar) with Γ by (symmetry; exact (usubst_id_ctx Γ lvar Hd (fun _ => eq_refl))).
  exact (gsubst_id_ctx Γ gid Hd (fun _ => eq_refl)).
Qed.

Lemma Γ_id_raw : gcsubst (ucsubst Γ lvar) gid = Γ.
Proof using HΓ. exact Γ_id. Qed.

Lemma brLv_T_id k ls : br_isT k = true -> length ls = br_nu k -> lvsubst (brLv k l1 l2) (uext ls lvar) = l1.
Proof using .
  intros Hk Hn. unfold brLv. rewrite Hk.
  rewrite (lvren_ush_uext' l1 (br_nu k) ls lvar Hn). apply lvsubst_id; reflexivity.
Qed.

Lemma brLv_t_id k ls : br_isT k = false -> length ls = br_nu k -> lvsubst (brLv k l1 l2) (uext ls lvar) = l2.
Proof using .
  intros Hk Hn. unfold brLv. rewrite Hk.
  rewrite (lvren_ush_uext' l2 (br_nu k) ls lvar Hn). apply lvsubst_id; reflexivity.
Qed.

(** ** A branch's reduct, generically (M8_DESIGN.md J2, S2)

    The reduct peels the branch at the code's levels [ls], the global
    payloads [os] and the recursive calls [xs]; it is typed at the result's
    instance [T] and the branch level [lv]. The branch supplies the
    payloads' typings ([Hσ], [Hd]) and the two instance equations. *)
Lemma rr_br k ls os xs {T lv} : k < nbr -> length ls = br_nu k -> length os = br_ng k -> length xs = br_nl k ->
  Forall (lwf (gL G)) ls -> Forall dnfo os -> Forall dnftm xs ->
  [ G ⊢ gext_s os gid : mkG (gL G) (map (fun D => gdecl_usubst D (uext ls lvar)) (brDecls k) ++ gΨ G) ] ->
  [ G ; Γ ⊢[ lM ] lext xs (lshift 0) : (ucsubst (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext ls lvar))⦃gext_s os gid⦄ ] ->
  ((usubst_ty (brRes k (wrapMT MT) (wrapMt Mt)) (uext ls lvar))⦃gext_s os gid⦄)[lext xs (lshift 0)] = T ->
  lvsubst (brLv k l1 l2) (uext ls lvar) = lv ->
  [ G ; Γ ⊢[ lM ] peelLs (peelGs (peelUs (wrap (br_nu k) (br_ng k) (br_nl k) (bs k)) ls) os) xs : T @ lv ].
Proof using Hrb HΓ.
  intros Hk Hn Hng Hnl Hls Ho Hxs Hσ Hd <- <-.
  rewrite peel_wrap by first [exact Hn | exact Hng | exact Hnl | exact Ho | exact Hxs | exact (Hbd k Hk)].
  exact (br_typed Hrb HΓ Hk Hn Hls Hσ Hd).
Qed.

Ltac rr_side :=
  first [ reflexivity | apply gdnf_gext_s; [assumption | intros ?i; exact I]
        | apply lk_dnf_lext; [assumption | intros ?n; exact I]
        | apply lk_dnf_lext; [repeat (apply Forall_cons; [eapply wf_tm_dnf; eassumption |]); apply Forall_nil
                             | intros ?n; exact I]
        | repeat (apply lk_dnf_lcons; [| eapply wf_tm_dnf; eassumption]); intros ?n; exact I ].
Ltac rr_lext_base d := lazymatch d with lcons ?d' _ => rr_lext_base d' | lext _ ?e => e | _ => d end.
Ltac rr_lext_split d :=
  lazymatch d with
  | lcons ?d' ?a => let xs := rr_lext_split d' in eval cbn [List.app] in (xs ++ a :: nil)
  | lext ?xs _ => xs
  | _ => constr:(@nil tm)
  end.
Ltac rr_wkb_rw :=
  match goal with
  | |- context [ ((usubst_ty (motT (wkb ?nu ?ng ?nl ?w) ?lv ?g ?c) (uext ?ls lvar))⦃gext_s ?os gid⦄)[?d] ] =>
      let e0 := rr_lext_base d in let xs := rr_lext_split d in
      rewrite (motT_wkb_inst' _ nu ng nl ls os xs lvar gid e0 d lv g c) by rr_side;
      rewrite (motive_id_T _ HMTd)
  | |- context [ ((usubst_ty (mott (wkb ?nu ?ng ?nl ?w) ?lv ?g ?U ?c) (uext ?ls lvar))⦃gext_s ?os gid⦄)[?d] ] =>
      let e0 := rr_lext_base d in let xs := rr_lext_split d in
      rewrite (mott_wkb_inst' _ nu ng nl ls os xs lvar gid e0 d lv g U c) by rr_side;
      rewrite (motive_id_t _ HMtd)
  end.
Ltac rr_sl0 :=
  repeat first [ rewrite subst_lshift0_ty by (apply dnfty_nfty; eassumption)
               | rewrite subst_lshift0 by (apply dnftm_nftm; eassumption) ].
Ltac rr_res := cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar]; rr_wkb_rw; cbn; rr_sl0; rewrite ?Nat.add_0_r; reflexivity.
Ltac rr_ctx :=
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst mkLocs call_ty call_lv br_calls lext fold_left];
  rewrite ?gs_cext; rewrite wkc_inst' by reflexivity; rewrite Γ_id;
  repeat apply lsub_wf_lcons; [exact (lsub_wf_id G lM eq_refl Γ HΓ) | ..];
  repeat rr_wkb_rw; cbn;
  rewrite ?lvren_ush_uext' by reflexivity;
  rewrite ?(lvsubst_id l1 lvar (fun _ => eq_refl)), ?(lvsubst_id l2 lvar (fun _ => eq_refl)); rr_sl0.

(** [elimW]'s scope (M13b): its step telescope's [wfty]/[wihty]/[wstepty]
    are pushed through the substitutions whole, so the full [cbn] of
    [rr_ctx] (which would unfold their weakenings) is replaced by one that
    leaves renamings alone. *)
Ltac rr_ctx_W os :=
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst mkLocs call_ty call_lv br_calls lext fold_left];
  rewrite ?gs_cext; rewrite wkc_inst' by reflexivity; rewrite Γ_id;
  repeat apply lsub_wf_lcons; [exact (lsub_wf_id G lM eq_refl Γ HΓ) | ..];
  repeat rr_wkb_rw;
  cbn [gsubst GSubst_ctx GSubst_ty GSubst_tm]; rewrite ?uc_ext, ?gc_ext;
  rewrite ?us_wfty, ?us_wihty, ?us_wstepty, ?gs_wfty, ?gs_wihty, ?gs_wstepty;
  rewrite ?us_wfcsty, ?us_wfihty, ?us_wfstepty, ?gs_wfcsty, ?gs_wfihty, ?gs_wfstepty;
  rewrite ?us_iwfcsty, ?us_iwfihty, ?us_iwfstepty, ?us_iwfmotty, ?gs_iwfcsty, ?gs_iwfihty, ?gs_iwfstepty,
          ?gs_iwfmotty;
  rewrite ?lvren_ush_uext' by reflexivity;
  rewrite ?(lvsubst_id l1 lvar (fun _ => eq_refl)), ?(lvsubst_id l2 lvar (fun _ => eq_refl));
  unfold os; unfold uext, gext_s, gv, gu; try unfold lsingle; try unfold lsucc;
  cbn [length Nat.ltb Nat.leb Nat.sub nth lvsubst ucsubst usubst_tm usubst_ty ulsubst gcsubst gsubst_tm
       gsubst_ty glsubst pctx pty ptm subst_tm subst_ty lcomp gsubst GSubst_tm GSubst_ty GSubst_ctx subst
       Subst_tm Subst_ty lext fold_left llk lcons'];
  rr_sl0.

Lemma rr_T_nat {l Δ r} : [ G ; Δ ⊢[ lD ] ] -> redT l1 l2 (mkrb MT Mt bs) l Δ tyNat = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) lzero Δ (boxT tyNat) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hred.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 0 1 0 (bs 0)) nil) (GCtx Δ :: nil)) nil)
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r.
  rewrite peel_wrap by first [reflexivity | repeat constructor; exact (wf_ctx_dnf HΔ) | exact (Hbd 0 ltac:(lia))].
  pose proof HG_rr as HG.
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext nil lvar)) (brDecls 0) ++ gΨ G) ]).
  { change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil).
    destruct G as [L Ψ]. exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) (wf_ctx_dnf HΔ) HΔ). }
  assert (Hd : [ G ; Γ ⊢[ lM ] lext nil (lshift 0) :
                 (ucsubst (brΓ 0 Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext nil lvar))⦃gext_s (GCtx Δ :: nil) gid⦄ ]).
  { cbn [brΓ brLocs cexts br_nu br_ng br_ar lext fold_left mkLocs call_ty call_lv br_calls].
    rewrite (wkc_inst' 0 1 Γ nil (GCtx Δ :: nil) lvar gid eq_refl eq_refl). rewrite Γ_id.
    exact (lsub_wf_id G lM eq_refl Γ HΓ). }
  pose proof (br_typed (k := 0) (ls := nil) Hrb HΓ ltac:(lia) eq_refl (Forall_nil _) Hσ Hd) as X.
  rewrite (brLv_T_id 0 nil eq_refl eq_refl) in X. cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar] in X.
  rewrite (motT_wkb_inst' MT 0 1 0 nil (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [repeat constructor; exact (wf_ctx_dnf HΔ) | intros i; exact I]
                  | apply lk_dnf_lext; [constructor | intros n; exact I]].
  rewrite (motive_id_T MT HMTd) in X. exact X.
Qed.

Lemma HCD' : lle lC lD. Proof using . unfold lle; cbn; lia. Qed.

Lemma sl0 (A : ty) : nfty A -> subst_ty A (lshift 0) = A.
Proof using . exact (subst_lshift0_ty A). Qed.
Ltac sl0_rw H := rewrite ?(sl0 _ (dnfty_nfty _ H)), ?(subst_lshift0_ty _ (dnfty_nfty _ H)).
Lemma sl0t (t : tm) : nftm t -> subst_tm t (lshift 0) = t.
Proof using . exact (subst_lshift0 t). Qed.
Ltac sl0t_rw H := rewrite ?(sl0t _ (dnftm_nftm _ H)), ?(subst_lshift0 _ (dnftm_nftm _ H)).
Ltac sl0t_rw_in H X := rewrite ?(sl0t _ (dnftm_nftm _ H)), ?(subst_lshift0 _ (dnftm_nftm _ H)) in X.
Ltac sl0_rw_in H X := rewrite ?(sl0 _ (dnfty_nfty _ H)), ?(subst_lshift0_ty _ (dnfty_nfty _ H)) in X.

(** A recursive call at a boxed sub-code. *)
Lemma recT_wf {l Δ c} : lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] c @ l ] ->
  [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT c) : motT (wrapMT MT) l Δ (boxT c) @ l1 ].
Proof using Hrb HΓ. intros Hl HΔ Hc. apply (wf_elimT' Hrb Hl HΔ). apply wf_boxT; assumption. Qed.

(** A binder type ([Π], branch 1; [Σ], branch 13): its former [F] and
    inversion. *)
Ltac rr_T_bind kb F invF l Δ k k' A B r :=
  intros HΔ Hc Hred;
  destruct (invF _ _ _ _ _ _ _ _ Hc) as ((_ & Wk & Wk' & HA & HB) & _);
  pose proof (wf_ty_dnf HA) as HAd; pose proof (wf_ty_dnf HB) as HBd; pose proof (wf_ctx_dnf HΔ) as HΔd;
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 3 2 (bs kb)) (k :: k' :: nil)) (GCtx Δ :: GTy A :: GTy B :: nil))
                     (elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A) :: elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (boxT B) :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity);
  subst r; pose proof HG_rr as HG; pose proof (Hbd kb ltac:(lia)) as Hb;
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]);
  pose proof (recT_wf Wk HΔ HA) as Hx1; pose proof (recT_wf Wk' HΔA HB) as Hx2;
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | apply Forall_nil]);
  pose proof (Forall_cons _ (wf_tm_dnf Hx1) (Forall_cons _ (wf_tm_dnf Hx2) (Forall_nil _))) as Hxs;
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls kb) ++ gΨ G) ])
    by (change (GCtx Δ :: GTy A :: GTy B :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil);
        destruct G as [L Ψ];
        refine (gsub_wf_snoc (D := gdTy (cvar 1 ,, gv 0 @ k) lC k') (o := GTy B)
                  (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                     (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _);
        [cbn; exact HA | cbn; sl0_rw HAd; exact HB]);
  refine (rr_br kb (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: nil) (_ :: _ :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _)))
            Ho Hxs Hσ _ _ _);
  [rr_ctx; eassumption | rr_res | exact (brLv_T_id kb (k :: k' :: nil) eq_refl eq_refl)].

Lemma rr_T_pi {l Δ k k' A B r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyPi k k' A B @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyPi k k' A B) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) (lmax k k') Δ (boxT (tyPi k k' A B)) @ l1 ].
Proof using Hrb HΓ.
  rr_T_bind 1 tyPi @inv_ty_pi l Δ k k' A B r.
Qed.

Lemma rect_wf {l Δ T c} : lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] ->
  [ G ; Δ ⊢[ lC ] c : T @ l ] ->
  [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c) : mott (wrapMt Mt) l Δ T (boxt c) @ l2 ].
Proof using Hrb HΓ. intros Hl HΔ HT Hc. apply (wf_elimt' Hrb Hl HΔ HT). apply wf_boxt; assumption. Qed.



Lemma rr_T_U {l Δ k r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyU k @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyU k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) (lsuc k) Δ (boxT (tyU k)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_U Hc) as ((_ & _ & Wk) & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 1 0 (bs 2)) (k :: nil)) (GCtx Δ :: nil)) nil)
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 2 ltac:(lia)) as Hb2.
  assert (Ho : Forall dnfo (GCtx Δ :: nil)) by (apply Forall_cons; [exact HΔd | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 2) ++ gΨ G) ]).
  { change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil).
    destruct G as [L Ψ]. exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ). }
  refine (rr_br 2 (k :: nil) (GCtx Δ :: nil) nil ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho (Forall_nil _) Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 2 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_T_El {l Δ k t r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyEl k t @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyEl k t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tyEl k t)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_El Hc) as ((_ & Wk & Ht) & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Ht) as Htd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 2 1 (bs 3)) (k :: nil)) (GCtx Δ :: GTm t :: nil)) (x1 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 3 ltac:(lia)) as Hb3.
  assert (HU : [ G ; Δ ⊢[ lD ] tyU k @ lsuc k ]) by (apply wft_U; [discriminate | exact HΔ | exact Wk]).
  pose proof (rect_wf (lwf_suc Wk) HΔ HU Ht) as Hx1. pose proof (wf_tm_dnf Hx1) as Hx1d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Htd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: nil)) by (apply Forall_cons; [exact Hx1d | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 3) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm t :: nil) with ((nil ++ GCtx Δ :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 0) lC (tyU k) (lsuc k)) (o := GTm t)
              (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Htd _).
    cbn. exact Ht. }
  refine (rr_br 3 (k :: nil) (GCtx Δ :: GTm t :: nil) (x1 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 3 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_T_sig {l Δ k k' A B r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tySig k k' A B @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tySig k k' A B) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) (lmax k k') Δ (boxT (tySig k k' A B)) @ l1 ].
Proof using Hrb HΓ.
  rr_T_bind 13 tySig @inv_ty_sig l Δ k k' A B r.
Qed.

Lemma rr_T_unit {l Δ k r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyUnit k @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyUnit k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tyUnit k)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_unit Hc) as ((_ & _ & Wk) & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 1 0 (bs 14)) (k :: nil)) (GCtx Δ :: nil)) nil)
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 14 ltac:(lia)) as Hb14.
  assert (Ho : Forall dnfo (GCtx Δ :: nil)) by (apply Forall_cons; [exact HΔd | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 14) ++ gΨ G) ]).
  { change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil).
    destruct G as [L Ψ]. exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ). }
  refine (rr_br 14 (k :: nil) (GCtx Δ :: nil) nil ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho (Forall_nil _) Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 14 (k :: nil) eq_refl eq_refl).
Qed.

(** ** Term codes: the reducts at their natural motive instances *)

Lemma rr_t_var {l Δ T n r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] T @ l ] ->
  [ G ; Δ ⊢[ lV ] var n : T @ l ] -> redt l1 l2 (mkrb MT Mt bs) l Δ T (var n) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) l Δ T (boxt (var n)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wl HT HV Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HT) as HTd. pose proof (wf_tm_dnf HV) as HVd.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 0 (bs 4)) (l :: nil)) (GCtx Δ :: GTy T :: GTm (var n) :: nil)) nil)
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 4 ltac:(lia)) as Hb.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy T :: GTm (var n) :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HTd | exact HVd | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy T :: GTm (var n) :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (l :: nil) lvar)) (brDecls 4) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy T :: GTm (var n) :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy T :: nil) ++ GTm (var n) :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lV (gv 0) l) (o := GTm (var n))
              (gsub_wf_snoc (D := gdTy (cvar 0) lD l) (o := GTy T)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HTd _) HVd _).
    - cbn. exact HT.
    - cbn. sl0_rw HTd. exact HV. }
  refine (rr_br 4 (l :: nil) (GCtx Δ :: GTy T :: GTm (var n) :: nil) nil ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wl (Forall_nil _)) Ho (Forall_nil _) Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 4 (l :: nil) eq_refl eq_refl).
Qed.

(** The codes without pieces: the branch at the context alone. *)
Ltac rr_t_closed k nu ls :=
  intros;
  match goal with HΔ : [ _ ; ?Δ ⊢[ lD ] ], Hred : redt _ _ _ _ _ _ _ = Some ?r |- _ =>
    let HΔd := fresh "HΔd" in let Er := fresh "Er" in let HG := fresh "HG" in let Hb := fresh "Hb" in
    let Ho := fresh "Ho" in let Hσ := fresh "Hσ" in let Hd := fresh "Hd" in let X := fresh "X" in
    pose proof (wf_ctx_dnf HΔ) as HΔd;
    assert (Er : r = peelLs (peelGs (peelUs (wrap nu 1 0 (bs k)) ls) (GCtx Δ :: nil)) nil)
      by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity);
    subst r; pose proof HG_rr as HG; pose proof (Hbd k ltac:(lia)) as Hb;
    assert (Ho : Forall dnfo (GCtx Δ :: nil)) by (apply Forall_cons; [exact HΔd | apply Forall_nil]);
    rewrite peel_wrap by first [reflexivity | exact Ho | apply Forall_nil | exact Hb];
    assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                   mkG (gL G) (map (fun D => gdecl_usubst D (uext ls lvar)) (brDecls k) ++ gΨ G) ])
      by (change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil);
          destruct G as [L Ψ]; exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ));
    assert (Hd : [ G ; Γ ⊢[ lM ] lext nil (lshift 0) :
                   (ucsubst (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2) (uext ls lvar))⦃gext_s (GCtx Δ :: nil) gid⦄ ])
      by (cbn [brΓ brLocs cexts br_nu br_ng br_ar lext fold_left mkLocs call_ty call_lv br_calls];
          rewrite (wkc_inst' nu 1 Γ ls (GCtx Δ :: nil) lvar gid eq_refl eq_refl); rewrite Γ_id;
          exact (lsub_wf_id G lM eq_refl Γ HΓ))
  end.

Lemma rr_t_nat {l Δ T r} : [ G ; Δ ⊢[ lD ] ] -> redt l1 l2 (mkrb MT Mt bs) l Δ T tmNat = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc lzero) Δ (tyU lzero) (boxt tmNat) @ l2 ].
Proof using Hrb HΓ.
  rr_t_closed 5 0 (@nil lvl).
  pose proof (br_typed (k := 5) (ls := nil) Hrb HΓ ltac:(lia) eq_refl (Forall_nil _) Hσ Hd) as X.
  rewrite (brLv_t_id 5 nil eq_refl eq_refl) in X. cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar] in X.
  rewrite (mott_wkb_inst' Mt 0 1 0 nil (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

Lemma rr_t_zero {l Δ T r} : [ G ; Δ ⊢[ lD ] ] -> redt l1 l2 (mkrb MT Mt bs) l Δ T zero = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) lzero Δ tyNat (boxt zero) @ l2 ].
Proof using Hrb HΓ.
  rr_t_closed 8 0 (@nil lvl).
  pose proof (br_typed (k := 8) (ls := nil) Hrb HΓ ltac:(lia) eq_refl (Forall_nil _) Hσ Hd) as X.
  rewrite (brLv_t_id 8 nil eq_refl eq_refl) in X. cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar] in X.
  rewrite (mott_wkb_inst' Mt 0 1 0 nil (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

Lemma rr_t_U {l Δ T k r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> redt l1 l2 (mkrb MT Mt bs) l Δ T (tmU k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc (lsuc k)) Δ (tyU (lsuc k)) (boxt (tmU k)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ0 Wk. rr_t_closed 7 1 (k :: nil).
  pose proof (br_typed (k := 7) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_t_id 7 (k :: nil) eq_refl eq_refl) in X. cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar] in X.
  rewrite (mott_wkb_inst' Mt 1 1 0 (k :: nil) (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

Lemma rr_t_codeunit {l Δ T k r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> redt l1 l2 (mkrb MT Mt bs) l Δ T (tmUnit k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmUnit k)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ0 Wk. rr_t_closed 19 1 (k :: nil).
  pose proof (br_typed (k := 19) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_t_id 19 (k :: nil) eq_refl eq_refl) in X. cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar] in X.
  rewrite (mott_wkb_inst' Mt 1 1 0 (k :: nil) (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

Lemma rr_t_triv {l Δ T k r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> redt l1 l2 (mkrb MT Mt bs) l Δ T (tmTriv k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ (tyUnit k) (boxt (tmTriv k)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ0 Wk. rr_t_closed 20 1 (k :: nil).
  pose proof (br_typed (k := 20) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_t_id 20 (k :: nil) eq_refl eq_refl) in X. cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar] in X.
  rewrite (mott_wkb_inst' Mt 1 1 0 (k :: nil) (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

(** The type of a C-typed term, at D. *)
Lemma ctm_ty {Δ c T l} : [ G ; Δ ⊢[ lC ] c : T @ l ] -> [ G ; Δ ⊢[ lD ] T @ l ].
Proof using . intros H. exact (wf_tm_ty (i := lD) eq_refl (lift_tm H HCD')). Qed.

Lemma rr_t_succ {l Δ T t r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] t : tyNat @ lzero ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (succ t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) lzero Δ tyNat (boxt (succ t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Ht) as Htd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 0 2 1 (bs 9)) nil) (GCtx Δ :: GTm t :: nil)) (x1 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG.
  pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Ht) Ht) as Hx1. pose proof (wf_tm_dnf Hx1) as Hx1d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Htd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: nil)) by (apply Forall_cons; [exact Hx1d | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext nil lvar)) (brDecls 9) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm t :: nil) with ((nil ++ GCtx Δ :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 0) lC tyNat lzero) (o := GTm t)
              (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Htd _).
    cbn. exact Ht. }
  refine (rr_br 9 nil (GCtx Δ :: GTm t :: nil) (x1 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_nil _) Ho Hxs Hσ _ _ _).
  - rr_ctx. exact Hx1.
  - rr_res.
  - exact (brLv_t_id 9 nil eq_refl eq_refl).
Qed.

(** A binder code ([Π], branch 6; [Σ], branch 15). *)
Ltac rr_t_bind kb l Δ T k k' s t r :=
  intros HΔ Wk Wk' Hs Ht Hred;
  pose proof (wf_ctx_dnf HΔ) as HΔd; pose proof (wf_tm_dnf Hs) as Hsd; pose proof (wf_tm_dnf Ht) as Htd;
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 3 2 (bs kb)) (k :: k' :: nil)) (GCtx Δ :: GTm s :: GTm t :: nil))
                     (elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)
                      :: elimt l1 l2 (mkrb MT Mt bs) (lsuc k') (Δ ,, tyEl k s @ k) (tyU k') (boxt t) :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity);
  subst r; pose proof HG_rr as HG; pose proof (Hbd kb ltac:(lia)) as Hb;
  assert (HΔs : [ G ; Δ ,, tyEl k s @ k ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | apply wft_El; [discriminate | exact Wk | exact (lift_tm Hs HCD')] | exact Wk]);
  pose proof (rect_wf (lwf_suc Wk) HΔ (ctm_ty Hs) Hs) as Hx1;
  pose proof (rect_wf (lwf_suc Wk') HΔs (ctm_ty Ht) Ht) as Hx2;
  assert (Ho : Forall dnfo (GCtx Δ :: GTm s :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Hsd | exact Htd | apply Forall_nil]);
  pose proof (Forall_cons _ (wf_tm_dnf Hx1) (Forall_cons _ (wf_tm_dnf Hx2) (Forall_nil _))) as Hxs;
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm s :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls kb) ++ gΨ G) ])
    by (change (GCtx Δ :: GTm s :: GTm t :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTm s :: nil) ++ GTm t :: nil);
        destruct G as [L Ψ];
        refine (gsub_wf_snoc (D := gdTm (cvar 1 ,, tyEl k (gu 0) @ k) lC (tyU k') (lsuc k')) (o := GTm t)
                  (gsub_wf_snoc (D := gdTm (cvar 0) lC (tyU k) (lsuc k)) (o := GTm s)
                     (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Hsd _) Htd _);
        [cbn; exact Hs | cbn; sl0t_rw Hsd; exact Ht]);
  refine (rr_br kb (k :: k' :: nil) (GCtx Δ :: GTm s :: GTm t :: nil) (_ :: _ :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _)))
            Ho Hxs Hσ _ _ _);
  [rr_ctx; eassumption | rr_res | exact (brLv_t_id kb (k :: k' :: nil) eq_refl eq_refl)].

Lemma rr_t_pi {l Δ T k k' s t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmPi k k' s t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc (lmax k k')) Δ (tyU (lmax k k')) (boxt (tmPi k k' s t)) @ l2 ].
Proof using Hrb HΓ.
  rr_t_bind 6 l Δ T k k' s t r.
Qed.

Lemma rr_t_codesig {l Δ T k k' s t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSig k k' s t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc (lmax k k')) Δ (tyU (lmax k k')) (boxt (tmSig k k' s t)) @ l2 ].
Proof using Hrb HΓ.
  rr_t_bind 15 l Δ T k k' s t r.
Qed.

Lemma rr_t_natrec {l Δ T k M s z t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ,, tyNat @ lzero ⊢[ lC ] M @ k ] -> [ G ; Δ ⊢[ lC ] s : M[lsingle zero] @ k ] ->
  [ G ; Δ ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z : M[lsucc] @ k ] -> [ G ; Δ ⊢[ lC ] t : tyNat @ lzero ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (natrec k M s z t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ M[lsingle t] (boxt (natrec k M s z t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk HM Hs Hz Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HM) as HMd.
  pose proof (wf_tm_dnf Hs) as Hsd. pose proof (wf_tm_dnf Hz) as Hzd. pose proof (wf_tm_dnf Ht) as Htd.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k (Δ ,, tyNat @ lzero) (boxT M)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ (subst_ty M (lsingle zero)) (boxt s)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k (Δ ,, tyNat @ lzero ,, M @ k) (subst_ty M lsucc) (boxt z)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 5 4 (bs 10)) (k :: nil))
                             (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil)) (x1 :: x2 :: x3 :: x4 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
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
  refine (rr_br 10 (k :: nil) (GCtx Δ :: GTy M :: GTm s :: GTm z :: GTm t :: nil) (x1 :: x2 :: x3 :: x4 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 10 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_lam {l Δ k k' A b k1 k2 A1 B r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lD ] B @ k' ] -> [ G ; Δ ,, A @ k ⊢[ lC ] b : B @ k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ (tyPi k1 k2 A1 B) (lam k k' A b) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lmax k k') Δ (tyPi k k' A B) (boxt (lam k k' A b)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HA HB Hbt Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_tm_dnf Hbt) as Hbtd.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) B (boxt b)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 4 2 (bs 11)) (k :: k' :: nil)) (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 11 ltac:(lia)) as Hb.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf Wk' HΔA HB Hbt) as Hx2.
  pose proof (wf_tm_dnf Hx1) as Hx1d. pose proof (wf_tm_dnf Hx2) as Hx2d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact Hbtd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil)) by (repeat apply Forall_cons; [exact Hx1d | exact Hx2d | apply Forall_nil]).
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
  refine (rr_br 11 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm b :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 11 (k :: k' :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_app {l Δ T k k' A B f a r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ⊢[ lC ] f : tyPi k k' A B @ lmax k k' ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (app f k k' A B a) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k' Δ B[lsingle a] (boxt (app f k k' A B a)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HA HB Hf Ha Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_tm_dnf Hf) as Hfd. pose proof (wf_tm_dnf Ha) as Had.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (boxT B)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) (lmax k k') Δ (tyPi k k' A B) (boxt f)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 5 4 (bs 12)) (k :: k' :: nil))
                             (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil)) (x1 :: x2 :: x3 :: x4 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
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
  refine (rr_br 12 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm f :: GTm a :: nil) (x1 :: x2 :: x3 :: x4 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 12 (k :: k' :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_pair {l Δ T k k' A B a b r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ⊢[ lC ] a : A @ k ] -> [ G ; Δ ⊢[ lC ] b : B[lsingle a] @ k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmPair k k' A B a b) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lmax k k') Δ (tySig k k' A B) (boxt (tmPair k k' A B a b)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HA HB Ha Hb' Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_tm_dnf Ha) as Had. pose proof (wf_tm_dnf Hb') as Hbd'.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (boxT B)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k' Δ (B[lsingle a]) (boxt b)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 5 4 (bs 16)) (k :: k' :: nil))
                             (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm b :: nil)) (x1 :: x2 :: x3 :: x4 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 16 ltac:(lia)) as Hb.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (recT_wf Wk' HΔA HB) as Hx2.
  pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx3. pose proof (rect_wf Wk' HΔ (ctm_ty Hb') Hb') as Hx4.
  pose proof (wf_tm_dnf Hx1) as Hx1d. pose proof (wf_tm_dnf Hx2) as Hx2d.
  pose proof (wf_tm_dnf Hx3) as Hx3d. pose proof (wf_tm_dnf Hx4) as Hx4d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm b :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact Had | exact Hbd' | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: nil))
    by (repeat apply Forall_cons; [exact Hx1d | exact Hx2d | exact Hx3d | exact Hx4d | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm b :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 16) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm b :: nil)
      with (((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil) ++ GTm a :: nil) ++ GTm b :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 3) lC (tyGvar 1 (lsingle (gu 0))) k') (o := GTm b)
             (gsub_wf_snoc (D := gdTm (cvar 2) lC (gv 1) k) (o := GTm a)
               (gsub_wf_snoc (D := gdTy (cvar 1 ,, gv 0 @ k) lC k') (o := GTy B)
                 (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                   (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _) Had _) Hbd' _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact HB.
    - cbn. sl0_rw HAd. exact Ha.
    - cbn. sl0_rw HAd. sl0t_rw Had. exact Hb'. }
  refine (rr_br 16 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm b :: nil) (x1 :: x2 :: x3 :: x4 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 16 (k :: k' :: nil) eq_refl eq_refl).
Qed.

(** The projections (branches 17 and 18), which share their scope. *)
Ltac rr_t_proj kb l Δ k k' A B p :=
  intros HΔ Wk Wk' HA HB Hp Hred;
  pose proof (wf_ctx_dnf HΔ) as HΔd; pose proof (wf_ty_dnf HA) as HAd; pose proof (wf_ty_dnf HB) as HBd;
  pose proof (wf_tm_dnf Hp) as Hpd;
  lazymatch type of Hred with _ = Some ?r =>
    assert (Er : r = peelLs (peelGs (peelUs (wrap 2 4 3 (bs kb)) (k :: k' :: nil)) (GCtx Δ :: GTy A :: GTy B :: GTm p :: nil))
                       (elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A) :: elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (boxT B)
                        :: elimt l1 l2 (mkrb MT Mt bs) (lmax k k') Δ (tySig k k' A B) (boxt p) :: nil))
      by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity);
    subst r end;
  pose proof HG_rr as HG; pose proof (Hbd kb ltac:(lia)) as Hb;
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]);
  assert (Wkk : lwf (gL G) (lmax k k')) by (split; assumption);
  pose proof (recT_wf Wk HΔ HA) as Hx1; pose proof (recT_wf Wk' HΔA HB) as Hx2;
  pose proof (rect_wf Wkk HΔ (ctm_ty Hp) Hp) as Hx3;
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: GTm p :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact Hpd | apply Forall_nil]);
  pose proof (Forall_cons _ (wf_tm_dnf Hx1) (Forall_cons _ (wf_tm_dnf Hx2) (Forall_cons _ (wf_tm_dnf Hx3) (Forall_nil _))))
    as Hxs;
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: GTm p :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls kb) ++ gΨ G) ])
    by (change (GCtx Δ :: GTy A :: GTy B :: GTm p :: nil)
          with ((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil) ++ GTm p :: nil);
        destruct G as [L Ψ];
        refine (gsub_wf_snoc (D := gdTm (cvar 2) lC (tySig k k' (gv 1) (gv 0)) (lmax k k')) (o := GTm p)
                  (gsub_wf_snoc (D := gdTy (cvar 1 ,, gv 0 @ k) lC k') (o := GTy B)
                    (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                      (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _) Hpd _);
        [cbn; exact HA | cbn; sl0_rw HAd; exact HB | cbn; sl0_rw HAd; sl0_rw HBd; exact Hp]);
  refine (rr_br kb (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm p :: nil) (_ :: _ :: _ :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _);
  [rr_ctx; eassumption | rr_res | exact (brLv_t_id kb (k :: k' :: nil) eq_refl eq_refl)].

Lemma rr_t_fst {l Δ T k k' A B p r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmFst k k' A B p) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ A (boxt (tmFst k k' A B p)) @ l2 ].
Proof using Hrb HΓ.
  rr_t_proj 17 l Δ k k' A B p.
Qed.

Lemma rr_t_snd {l Δ T k k' A B p r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSnd k k' A B p) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k' Δ B[lsingle (tmFst k k' A B p)] (boxt (tmSnd k k' A B p)) @ l2 ].
Proof using Hrb HΓ.
  rr_t_proj 18 l Δ k k' A B p.
Qed.

(** ** The identity type (M11b) *)

Lemma sl1 (A : ty) : subst_ty A (lshift 1) = A⟨↑⟩.
Proof using . exact (subst_lshift1_ty A). Qed.
Lemma sl1t (t : tm) : subst_tm t (lshift 1) = t⟨↑⟩.
Proof using . exact (subst_lshift1 t). Qed.

Lemma rr_T_id {l Δ k A a b r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyId k A a b @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyId k A a b) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tyId k A a b)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_id Hc) as ((_ & Wk & HA & Ha & Hb') & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd.
  pose proof (wf_tm_dnf Ha) as Had. pose proof (wf_tm_dnf Hb') as Hbd'.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt b)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 4 3 (bs 21)) (k :: nil)) (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil))
                     (x1 :: x2 :: x3 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 21 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔ HA) as Hx1.
  pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx2. pose proof (rect_wf Wk HΔ (ctm_ty Hb') Hb') as Hx3.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact Had | exact Hbd' | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | exact (wf_tm_dnf Hx3) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 21) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil)
      with ((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTm a :: nil) ++ GTm b :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 2) lC (gv 1) k) (o := GTm b)
             (gsub_wf_snoc (D := gdTm (cvar 1) lC (gv 0) k) (o := GTm a)
               (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) Had _) Hbd' _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact Ha.
    - cbn. sl0_rw HAd. exact Hb'. }
  refine (rr_br 21 (k :: nil) (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil) (x1 :: x2 :: x3 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 21 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codeid {l Δ T k s t u r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ⊢[ lC ] t : tyEl k s @ k ] -> [ G ; Δ ⊢[ lC ] u : tyEl k s @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmId k s t u) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmId k s t u)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Hs Ht Hu Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Hs) as Hsd.
  pose proof (wf_tm_dnf Ht) as Htd. pose proof (wf_tm_dnf Hu) as Hud.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tyEl k s) (boxt t)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tyEl k s) (boxt u)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 4 3 (bs 22)) (k :: nil)) (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil))
                     (x1 :: x2 :: x3 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 22 ltac:(lia)) as Hb.
  assert (HU : [ G ; Δ ⊢[ lD ] tyU k @ lsuc k ]) by (apply wft_U; [discriminate | exact HΔ | exact Wk]).
  pose proof (rect_wf (lwf_suc Wk) HΔ HU Hs) as Hx1.
  pose proof (rect_wf Wk HΔ (ctm_ty Ht) Ht) as Hx2. pose proof (rect_wf Wk HΔ (ctm_ty Hu) Hu) as Hx3.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Hsd | exact Htd | exact Hud | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | exact (wf_tm_dnf Hx3) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 22) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil)
      with ((((nil ++ GCtx Δ :: nil) ++ GTm s :: nil) ++ GTm t :: nil) ++ GTm u :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 2) lC (tyEl k (gu 1)) k) (o := GTm u)
             (gsub_wf_snoc (D := gdTm (cvar 1) lC (tyEl k (gu 0)) k) (o := GTm t)
               (gsub_wf_snoc (D := gdTm (cvar 0) lC (tyU k) (lsuc k)) (o := GTm s)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Hsd _) Htd _) Hud _).
    - cbn. exact Hs.
    - cbn. sl0t_rw Hsd. exact Ht.
    - cbn. sl0t_rw Hsd. exact Hu. }
  refine (rr_br 22 (k :: nil) (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil) (x1 :: x2 :: x3 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 22 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_refl {l Δ T k A a r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmRefl k A a) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ (tyId k A a a) (boxt (tmRefl k A a)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk HA Ha Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_tm_dnf Ha) as Had.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 23)) (k :: nil)) (GCtx Δ :: GTy A :: GTm a :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 23 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx2.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTm a :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact Had | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTm a :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 23) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTm a :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTm a :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lC (gv 0) k) (o := GTm a)
             (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
               (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) Had _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact Ha. }
  refine (rr_br 23 (k :: nil) (GCtx Δ :: GTy A :: GTm a :: nil) (x1 :: x2 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 23 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_J {l Δ T k k' A a M c u e0 r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ] ->
  [ G ; Δ ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lC ] M @ k' ] ->
  [ G ; Δ ⊢[ lC ] c : M[lsingle2 a (tmRefl k A a)] @ k' ] ->
  [ G ; Δ ⊢[ lC ] u : A @ k ] -> [ G ; Δ ⊢[ lC ] e0 : tyId k A a u @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmJ k k' A a M c u e0) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k' Δ (M[lsingle2 u e0]) (boxt (tmJ k k' A a M c u e0)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HA Ha HI HM Hc Hu He0 Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_tm_dnf Ha) as Had.
  pose proof (wf_ty_dnf HM) as HMd. pose proof (wf_tm_dnf Hc) as Hcd.
  pose proof (wf_tm_dnf Hu) as Hud. pose proof (wf_tm_dnf He0) as Hed.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  set (x3 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) (boxT M)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k' Δ (M[lsingle2 a (tmRefl k A a)]) (boxt c)).
  set (x5 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt u)).
  set (x6 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tyId k A a u) (boxt e0)).
  set (os := GCtx Δ :: GTy A :: GTm a :: GTy M :: GTm c :: GTm u :: GTm e0 :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 7 6 (bs 24)) (k :: k' :: nil)) os) (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 24 ltac:(lia)) as Hb.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (HΔM : [ G ; Δ ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔA | exact (lift_ty HI HCD') | exact Wk]).
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx2.
  pose proof (recT_wf Wk' HΔM HM) as Hx3. pose proof (rect_wf Wk' HΔ (ctm_ty Hc) Hc) as Hx4.
  pose proof (rect_wf Wk HΔ (ctm_ty Hu) Hu) as Hx5. pose proof (rect_wf Wk HΔ (ctm_ty He0) He0) as Hx6.
  assert (Ho : Forall dnfo os)
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact Had | exact HMd | exact Hcd | exact Hud | exact Hed
                                  | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | exact (wf_tm_dnf Hx3)
                                  | exact (wf_tm_dnf Hx4) | exact (wf_tm_dnf Hx5) | exact (wf_tm_dnf Hx6) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s os gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 24) ++ gΨ G) ]).
  { change os with (((((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTm a :: nil) ++ GTy M :: nil) ++ GTm c :: nil)
                      ++ GTm u :: nil) ++ GTm e0 :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 5) lC (tyId k (gv 4) (gu 3) (gu 0)) k) (o := GTm e0)
             (gsub_wf_snoc (D := gdTm (cvar 4) lC (gv 3) k) (o := GTm u)
               (gsub_wf_snoc (D := gdTm (cvar 3) lC (tyGvar 0 (lsingle2 (gu 1) (tmRefl k (gv 2) (gu 1)))) k') (o := GTm c)
                 (gsub_wf_snoc (D := gdTy (cvar 2 ,, gv 1 @ k ,, tyId k (gv 1)⟨↑⟩ (gu 0)⟨↑⟩ (var 0) @ k) lC k') (o := GTy M)
                   (gsub_wf_snoc (D := gdTm (cvar 1) lC (gv 0) k) (o := GTm a)
                     (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                       (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) Had _) HMd _) Hcd _)
                 Hud _) Hed _).
    all: cbn; sl0_rw HAd; sl0t_rw Had; sl0t_rw Hud; rewrite ?sl1, ?sl1t; assumption. }
  refine (rr_br 24 (k :: k' :: nil) os (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; rewrite ?sl1, ?sl1t; eassumption.
  - rr_res.
  - exact (brLv_t_id 24 (k :: k' :: nil) eq_refl eq_refl).
Qed.

(** ** Strict equality (M10c), as the identity type and the unit type *)

Lemma rr_T_seq {l Δ k A a b r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tySEq k A a b @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tySEq k A a b) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tySEq k A a b)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_seq Hc) as ((_ & Wk & HA & Ha & Hb') & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd.
  pose proof (wf_tm_dnf Ha) as Had. pose proof (wf_tm_dnf Hb') as Hbd'.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt b)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 4 3 (bs 25)) (k :: nil)) (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil))
                     (x1 :: x2 :: x3 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 25 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔ HA) as Hx1.
  pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx2. pose proof (rect_wf Wk HΔ (ctm_ty Hb') Hb') as Hx3.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact Had | exact Hbd' | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | exact (wf_tm_dnf Hx3) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 25) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil)
      with ((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTm a :: nil) ++ GTm b :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 2) lC (gv 1) k) (o := GTm b)
             (gsub_wf_snoc (D := gdTm (cvar 1) lC (gv 0) k) (o := GTm a)
               (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) Had _) Hbd' _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact Ha.
    - cbn. sl0_rw HAd. exact Hb'. }
  refine (rr_br 25 (k :: nil) (GCtx Δ :: GTy A :: GTm a :: GTm b :: nil) (x1 :: x2 :: x3 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 25 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codeseq {l Δ T k s t u r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ⊢[ lC ] t : tyEl k s @ k ] -> [ G ; Δ ⊢[ lC ] u : tyEl k s @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSEq k s t u) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmSEq k s t u)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Hs Ht Hu Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Hs) as Hsd.
  pose proof (wf_tm_dnf Ht) as Htd. pose proof (wf_tm_dnf Hu) as Hud.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tyEl k s) (boxt t)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tyEl k s) (boxt u)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 4 3 (bs 26)) (k :: nil)) (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil))
                     (x1 :: x2 :: x3 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 26 ltac:(lia)) as Hb.
  assert (HU : [ G ; Δ ⊢[ lD ] tyU k @ lsuc k ]) by (apply wft_U; [discriminate | exact HΔ | exact Wk]).
  pose proof (rect_wf (lwf_suc Wk) HΔ HU Hs) as Hx1.
  pose proof (rect_wf Wk HΔ (ctm_ty Ht) Ht) as Hx2. pose proof (rect_wf Wk HΔ (ctm_ty Hu) Hu) as Hx3.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Hsd | exact Htd | exact Hud | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | exact (wf_tm_dnf Hx3) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 26) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil)
      with ((((nil ++ GCtx Δ :: nil) ++ GTm s :: nil) ++ GTm t :: nil) ++ GTm u :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 2) lC (tyEl k (gu 1)) k) (o := GTm u)
             (gsub_wf_snoc (D := gdTm (cvar 1) lC (tyEl k (gu 0)) k) (o := GTm t)
               (gsub_wf_snoc (D := gdTm (cvar 0) lC (tyU k) (lsuc k)) (o := GTm s)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Hsd _) Htd _) Hud _).
    - cbn. exact Hs.
    - cbn. sl0t_rw Hsd. exact Ht.
    - cbn. sl0t_rw Hsd. exact Hu. }
  refine (rr_br 26 (k :: nil) (GCtx Δ :: GTm s :: GTm t :: GTm u :: nil) (x1 :: x2 :: x3 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 26 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_srefl {l Δ T k A a r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (srefl k A a) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ (tySEq k A a a) (boxt (srefl k A a)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk HA Ha Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_tm_dnf Ha) as Had.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 29)) (k :: nil)) (GCtx Δ :: GTy A :: GTm a :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 29 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx2.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTm a :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact Had | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTm a :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 29) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTm a :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTm a :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lC (gv 0) k) (o := GTm a)
             (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
               (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) Had _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact Ha. }
  refine (rr_br 29 (k :: nil) (GCtx Δ :: GTy A :: GTm a :: nil) (x1 :: x2 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 29 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_T_sempty {l Δ k r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tySEmpty k @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tySEmpty k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tySEmpty k)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_sempty Hc) as ((_ & _ & Wk) & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 1 0 (bs 27)) (k :: nil)) (GCtx Δ :: nil)) nil)
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 27 ltac:(lia)) as Hb14.
  assert (Ho : Forall dnfo (GCtx Δ :: nil)) by (apply Forall_cons; [exact HΔd | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 27) ++ gΨ G) ]).
  { change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil).
    destruct G as [L Ψ]. exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ). }
  refine (rr_br 27 (k :: nil) (GCtx Δ :: nil) nil ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho (Forall_nil _) Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 27 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codesempty {l Δ T k r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSEmpty k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmSEmpty k)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ0 Wk. rr_t_closed 28 1 (k :: nil).
  pose proof (br_typed (k := 28) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_t_id 28 (k :: nil) eq_refl eq_refl) in X. cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar] in X.
  rewrite (mott_wkb_inst' Mt 1 1 0 (k :: nil) (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

(** [sEmpty]'s eliminator: the motive's level first, as the branch binds it. *)
Lemma rr_t_elimSEmpty {l Δ T k k' M e0 r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] M @ k' ] -> [ G ; Δ ⊢[ lC ] e0 : tySEmpty k @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (elimSEmpty k k' M e0) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k' Δ M (boxt (elimSEmpty k k' M e0)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HM He0 Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HM) as HMd. pose proof (wf_tm_dnf He0) as Hed.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k' Δ (boxT M)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tySEmpty k) (boxt e0)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 3 2 (bs 30)) (k' :: k :: nil)) (GCtx Δ :: GTy M :: GTm e0 :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 30 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk' HΔ HM) as Hx1. pose proof (rect_wf Wk HΔ (ctm_ty He0) He0) as Hx2.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy M :: GTm e0 :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HMd | exact Hed | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy M :: GTm e0 :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k' :: k :: nil) lvar)) (brDecls 30) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy M :: GTm e0 :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy M :: nil) ++ GTm e0 :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lC (tySEmpty k) k) (o := GTm e0)
             (gsub_wf_snoc (D := gdTy (cvar 0) lC k') (o := GTy M)
               (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HMd _) Hed _).
    - cbn. exact HM.
    - cbn. exact He0. }
  refine (rr_br 30 (k' :: k :: nil) (GCtx Δ :: GTy M :: GTm e0 :: nil) (x1 :: x2 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk' (Forall_cons _ Wk (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 30 (k' :: k :: nil) eq_refl eq_refl).
Qed.

(** ** The empty type and binary sums (M12c) *)

Lemma rr_T_empty {l Δ k r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyEmpty k @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyEmpty k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tyEmpty k)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_empty Hc) as ((_ & _ & Wk) & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 1 0 (bs 31)) (k :: nil)) (GCtx Δ :: nil)) nil)
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 31 ltac:(lia)) as Hb.
  assert (Ho : Forall dnfo (GCtx Δ :: nil)) by (apply Forall_cons; [exact HΔd | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 31) ++ gΨ G) ]).
  { change (GCtx Δ :: nil) with (nil ++ GCtx Δ :: nil).
    destruct G as [L Ψ]. exact (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ). }
  refine (rr_br 31 (k :: nil) (GCtx Δ :: nil) nil ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho (Forall_nil _) Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 31 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codeempty {l Δ T k r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> redt l1 l2 (mkrb MT Mt bs) l Δ T (tmEmpty k) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmEmpty k)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ0 Wk. rr_t_closed 32 1 (k :: nil).
  pose proof (br_typed (k := 32) (ls := k :: nil) Hrb HΓ ltac:(lia) eq_refl (Forall_cons _ Wk (Forall_nil _)) Hσ Hd) as X.
  rewrite (brLv_t_id 32 (k :: nil) eq_refl eq_refl) in X. cbn [brRes call_ty br_head br_nu br_ng br_nl br_ar] in X.
  rewrite (mott_wkb_inst' Mt 1 1 0 (k :: nil) (GCtx Δ :: nil) nil lvar gid (lshift 0) _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl)
    in X by first [apply gdnf_gext_s; [exact Ho | intros i; exact I] | apply lk_dnf_lext; [constructor | intros m; exact I]].
  rewrite (motive_id_t Mt HMtd) in X. exact X.
Qed.

(** [Empty]'s eliminator: the motive's level first, over the scrutinee. *)
Lemma rr_t_elimEmpty {l Δ T k k' M t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ,, tyEmpty k' @ k' ⊢[ lC ] M @ k ] -> [ G ; Δ ⊢[ lC ] t : tyEmpty k' @ k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (elimEmpty k k' M t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ (M[lsingle t]) (boxt (elimEmpty k k' M t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HM Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HM) as HMd. pose proof (wf_tm_dnf Ht) as Htd.
  assert (HΔE : [ G ; Δ ,, tyEmpty k' @ k' ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | apply wft_empty; [discriminate | exact HΔ | exact Wk'] | exact Wk']).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k (Δ ,, tyEmpty k' @ k') (boxT M)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k' Δ (tyEmpty k') (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 3 2 (bs 33)) (k :: k' :: nil)) (GCtx Δ :: GTy M :: GTm t :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 33 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔE HM) as Hx1. pose proof (rect_wf Wk' HΔ (ctm_ty Ht) Ht) as Hx2.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy M :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HMd | exact Htd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy M :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 33) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy M :: GTm t :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy M :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lC (tyEmpty k') k') (o := GTm t)
             (gsub_wf_snoc (D := gdTy (cvar 0 ,, tyEmpty k' @ k') lC k) (o := GTy M)
               (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HMd _) Htd _).
    - cbn. exact HM.
    - cbn. exact Ht. }
  refine (rr_br 33 (k :: k' :: nil) (GCtx Δ :: GTy M :: GTm t :: nil) (x1 :: x2 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 33 (k :: k' :: nil) eq_refl eq_refl).
Qed.

Lemma rr_T_sum {l Δ k k' A B r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tySum k k' A B @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tySum k k' A B) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) (lmax k k') Δ (boxT (tySum k k' A B)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_sum Hc) as ((_ & Wk & Wk' & HA & HB) & _).
  pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd. pose proof (wf_ctx_dnf HΔ) as HΔd.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' Δ (boxT B)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 3 2 (bs 34)) (k :: k' :: nil)) (GCtx Δ :: GTy A :: GTy B :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 34 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (recT_wf Wk' HΔ HB) as Hx2.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 34) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTy B :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTy (cvar 1) lC k') (o := GTy B)
              (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _).
    - cbn. exact HA.
    - cbn. exact HB. }
  refine (rr_br 34 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 34 (k :: k' :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codesum {l Δ T k k' s t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSum k k' s t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc (lmax k k')) Δ (tyU (lmax k k')) (boxt (tmSum k k' s t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' Hs Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Hs) as Hsd. pose proof (wf_tm_dnf Ht) as Htd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k') Δ (tyU k') (boxt t)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 3 2 (bs 35)) (k :: k' :: nil)) (GCtx Δ :: GTm s :: GTm t :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 35 ltac:(lia)) as Hb.
  pose proof (rect_wf (lwf_suc Wk) HΔ (ctm_ty Hs) Hs) as Hx1.
  pose proof (rect_wf (lwf_suc Wk') HΔ (ctm_ty Ht) Ht) as Hx2.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm s :: GTm t :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Hsd | exact Htd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm s :: GTm t :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 35) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm s :: GTm t :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTm s :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lC (tyU k') (lsuc k')) (o := GTm t)
              (gsub_wf_snoc (D := gdTm (cvar 0) lC (tyU k) (lsuc k)) (o := GTm s)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Hsd _) Htd _).
    - cbn. exact Hs.
    - cbn. exact Ht. }
  refine (rr_br 35 (k :: k' :: nil) (GCtx Δ :: GTm s :: GTm t :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 35 (k :: k' :: nil) eq_refl eq_refl).
Qed.

(** The injections (branches 36 and 37). *)
Ltac rr_t_inj kb U l Δ k k' A B a r :=
  intros HΔ Wk Wk' HA HB Ha Hred;
  pose proof (wf_ctx_dnf HΔ) as HΔd; pose proof (wf_ty_dnf HA) as HAd; pose proof (wf_ty_dnf HB) as HBd;
  pose proof (wf_tm_dnf Ha) as Had;
  let x3 := lazymatch U with
            | 1 => constr:(elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a))
            | _ => constr:(elimt l1 l2 (mkrb MT Mt bs) k' Δ B (boxt a))
            end in
  let Da := lazymatch U with 1 => constr:(gdTm (cvar 2) lC (gv 1) k) | _ => constr:(gdTm (cvar 2) lC (gv 0) k') end in
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 4 3 (bs kb)) (k :: k' :: nil)) (GCtx Δ :: GTy A :: GTy B :: GTm a :: nil))
                     (elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A) :: elimT l1 l2 (mkrb MT Mt bs) k' Δ (boxT B) :: x3 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity);
  subst r; pose proof HG_rr as HG; pose proof (Hbd kb ltac:(lia)) as Hb;
  pose proof (recT_wf Wk HΔ HA) as Hx1; pose proof (recT_wf Wk' HΔ HB) as Hx2;
  let Wa := lazymatch U with 1 => constr:(Wk) | _ => constr:(Wk') end in
  pose proof (rect_wf Wa HΔ (ctm_ty Ha) Ha) as Hx3;
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: GTm a :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact Had | apply Forall_nil]);
  pose proof (Forall_cons _ (wf_tm_dnf Hx1) (Forall_cons _ (wf_tm_dnf Hx2) (Forall_cons _ (wf_tm_dnf Hx3) (Forall_nil _))))
    as Hxs;
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: GTm a :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls kb) ++ gΨ G) ])
    by (change (GCtx Δ :: GTy A :: GTy B :: GTm a :: nil)
          with ((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil) ++ GTm a :: nil);
        destruct G as [L Ψ];
        refine (gsub_wf_snoc (D := Da) (o := GTm a)
                  (gsub_wf_snoc (D := gdTy (cvar 1) lC k') (o := GTy B)
                    (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                       (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _) Had _);
        cbn; sl0_rw HAd; sl0_rw HBd; assumption);
  refine (rr_br kb (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm a :: nil) (_ :: _ :: _ :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _);
  [rr_ctx; eassumption | rr_res | exact (brLv_t_id kb (k :: k' :: nil) eq_refl eq_refl)].

Lemma rr_t_inl {l Δ T k k' A B a r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmInl k k' A B a) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lmax k k') Δ (tySum k k' A B) (boxt (tmInl k k' A B a)) @ l2 ].
Proof using Hrb HΓ. rr_t_inj 36 (1) l Δ k k' A B a r. Qed.

Lemma rr_t_inr {l Δ T k k' A B b r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] b : B @ k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmInr k k' A B b) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lmax k k') Δ (tySum k k' A B) (boxt (tmInr k k' A B b)) @ l2 ].
Proof using Hrb HΓ. rr_t_inj 37 (0) l Δ k k' A B b r. Qed.

(** [case]: the branch scopes declare the branch types in their substituted
    form ([liftshift_cons_ty']). *)
Lemma rr_t_case {l Δ T k k' k'' A B M c1 c2 t r} : [ G ; Δ ⊢[ lD ] ] ->
  lwf (gL G) k -> lwf (gL G) k' -> lwf (gL G) k'' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ,, tySum k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] c1 : M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G ; Δ ,, B @ k' ⊢[ lC ] c2 : M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G ; Δ ⊢[ lC ] t : tySum k k' A B @ lmax k k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmCase k k' k'' A B M c1 c2 t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k'' Δ (M[lsingle t]) (boxt (tmCase k k' k'' A B M c1 c2 t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' Wk'' HA HB HM Hc1 Hc2 Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_ty_dnf HM) as HMd. pose proof (wf_tm_dnf Hc1) as Hc1d. pose proof (wf_tm_dnf Hc2) as Hc2d.
  pose proof (wf_tm_dnf Ht) as Htd.
  assert (Wkm : lwf (gL G) (lmax k k')) by (cbn; auto).
  assert (HS : [ G ; Δ ⊢[ lC ] tySum k k' A B @ lmax k k' ])
    by (apply wft_sum; [discriminate | exact Wk | exact Wk' | exact HA | exact HB]).
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (HΔB : [ G ; Δ ,, B @ k' ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HB HCD') | exact Wk']).
  assert (HΔS : [ G ; Δ ,, tySum k k' A B @ lmax k k' ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | exact (lift_ty HS HCD') | exact Wkm]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' Δ (boxT B)).
  set (x3 := elimT l1 l2 (mkrb MT Mt bs) k'' (Δ ,, tySum k k' A B @ lmax k k') (boxT M)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k'' (Δ ,, A @ k) (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) (boxt c1)).
  set (x5 := elimt l1 l2 (mkrb MT Mt bs) k'' (Δ ,, B @ k') (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) (boxt c2)).
  set (x6 := elimt l1 l2 (mkrb MT Mt bs) (lmax k k') Δ (tySum k k' A B) (boxt t)).
  set (os := GCtx Δ :: GTy A :: GTy B :: GTy M :: GTm c1 :: GTm c2 :: GTm t :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 3 7 6 (bs 38)) (k :: k' :: k'' :: nil)) os)
                     (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 38 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (recT_wf Wk' HΔ HB) as Hx2.
  pose proof (recT_wf Wk'' HΔS HM) as Hx3.
  pose proof (rect_wf Wk'' HΔA (ctm_ty Hc1) Hc1) as Hx4. pose proof (rect_wf Wk'' HΔB (ctm_ty Hc2) Hc2) as Hx5.
  pose proof (rect_wf Wkm HΔ (ctm_ty Ht) Ht) as Hx6.
  assert (Ho : Forall dnfo os)
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact HMd | exact Hc1d | exact Hc2d | exact Htd
                                  | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | exact (wf_tm_dnf Hx3)
                                  | exact (wf_tm_dnf Hx4) | exact (wf_tm_dnf Hx5) | exact (wf_tm_dnf Hx6) | apply Forall_nil]).
  pose proof Hc1 as Hc1'. pose proof Hc2 as Hc2'.
  rewrite DeLaM.Syntax.SubstCommute.liftshift_single_ty in Hc1', Hc2'.
  assert (Hσ : [ G ⊢ gext_s os gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: k'' :: nil) lvar)) (brDecls 38) ++ gΨ G) ]).
  { change os with (((((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil) ++ GTy M :: nil) ++ GTm c1 :: nil)
                      ++ GTm c2 :: nil) ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 5) lC (tySum k k' (gv 4) (gv 3)) (lmax k k')) (o := GTm t)
             (gsub_wf_snoc (D := gdTm (cvar 4 ,, gv 2 @ k') lC
                                     (tyGvar 1 (lcons (lshift 1) (tmInr k k' (gv 3)⟨↑⟩ (gv 2)⟨↑⟩ (var 0)))) k'') (o := GTm c2)
               (gsub_wf_snoc (D := gdTm (cvar 3 ,, gv 2 @ k) lC
                                       (tyGvar 0 (lcons (lshift 1) (tmInl k k' (gv 2)⟨↑⟩ (gv 1)⟨↑⟩ (var 0)))) k'') (o := GTm c1)
                 (gsub_wf_snoc (D := gdTy (cvar 2 ,, tySum k k' (gv 1) (gv 0) @ lmax k k') lC k'') (o := GTy M)
                   (gsub_wf_snoc (D := gdTy (cvar 1) lC k') (o := GTy B)
                     (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                       (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _) HMd _) Hc1d _)
               Hc2d _) Htd _).
    all: cbn; sl0_rw HAd; sl0_rw HBd; rewrite ?sl1, ?sl1t; assumption. }
  refine (rr_br 38 (k :: k' :: k'' :: nil) os (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_cons _ Wk'' (Forall_nil _)))) Ho Hxs Hσ _ _ _).
  - rr_ctx; rewrite ?sl1, ?sl1t, ?liftshift_cons_ty'; eassumption.
  - rr_res.
  - exact (brLv_t_id 38 (k :: k' :: k'' :: nil) eq_refl eq_refl).
Qed.

(** ** Well-founded trees (M13b) *)

Lemma rr_T_W {l Δ k k' A B r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyW k k' A B @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyW k k' A B) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) (lmax k k') Δ (boxT (tyW k k' A B)) @ l1 ].
Proof using Hrb HΓ.
  rr_T_bind 39 tyW @inv_ty_W l Δ k k' A B r.
Qed.

Lemma rr_t_codeW {l Δ T k k' s t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmW k k' s t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc (lmax k k')) Δ (tyU (lmax k k')) (boxt (tmW k k' s t)) @ l2 ].
Proof using Hrb HΓ.
  rr_t_bind 40 l Δ T k k' s t r.
Qed.

(** [sup]: the children's call at their [Π] type over the shape. *)
Lemma rr_t_sup {l Δ T k k' A B a f r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G ; Δ ⊢[ lC ] f : tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSup k k' A B a f) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lmax k k') Δ (tyW k k' A B) (boxt (tmSup k k' A B a f)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HA HB Ha Hf Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_tm_dnf Ha) as Had. pose proof (wf_tm_dnf Hf) as Hfd.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (boxT B)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) (lmax k' (lmax k k')) Δ
               (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) (boxt f)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 5 4 (bs 41)) (k :: k' :: nil))
                             (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm f :: nil)) (x1 :: x2 :: x3 :: x4 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 41 ltac:(lia)) as Hb.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (Wf : lwf (gL G) (lmax k' (lmax k k'))) by (cbn; repeat split; assumption).
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (recT_wf Wk' HΔA HB) as Hx2.
  pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx3. pose proof (rect_wf Wf HΔ (ctm_ty Hf) Hf) as Hx4.
  pose proof (wf_tm_dnf Hx1) as Hx1d. pose proof (wf_tm_dnf Hx2) as Hx2d.
  pose proof (wf_tm_dnf Hx3) as Hx3d. pose proof (wf_tm_dnf Hx4) as Hx4d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm f :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact Had | exact Hfd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: nil))
    by (repeat apply Forall_cons; [exact Hx1d | exact Hx2d | exact Hx3d | exact Hx4d | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm f :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: nil) lvar)) (brDecls 41) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm f :: nil)
      with (((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil) ++ GTm a :: nil) ++ GTm f :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 3) lC (tyPi k' (lmax k k') (tyGvar 1 (lsingle (gu 0)))
                                                  (tyW k k' (gv 2) (gv 1))⟨↑⟩) (lmax k' (lmax k k'))) (o := GTm f)
             (gsub_wf_snoc (D := gdTm (cvar 2) lC (gv 1) k) (o := GTm a)
               (gsub_wf_snoc (D := gdTy (cvar 1 ,, gv 0 @ k) lC k') (o := GTy B)
                 (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                   (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _) Had _) Hfd _).
    - cbn. exact HA.
    - cbn. sl0_rw HAd. exact HB.
    - cbn. sl0_rw HAd. exact Ha.
    - cbn. sl0_rw HAd. sl0_rw HBd. sl0t_rw Had. rewrite ?sl1, ?subst_liftshift_ty. exact Hf. }
  refine (rr_br 41 (k :: k' :: nil) (GCtx Δ :: GTy A :: GTy B :: GTm a :: GTm f :: nil) (x1 :: x2 :: x3 :: x4 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs Hσ _ _ _).
  - rr_ctx; rewrite ?sl1, ?sl1t, ?subst_liftshift_ty; eassumption.
  - rr_res.
  - exact (brLv_t_id 41 (k :: k' :: nil) eq_refl eq_refl).
Qed.

(** [elimW]: the step's telescope kept in notation form ([gs_wstepty] and
    its twins). *)
Lemma rr_t_elimW {l Δ T k k' k'' A B M c t r} : [ G ; Δ ⊢[ lD ] ] ->
  lwf (gL G) k -> lwf (gL G) k' -> lwf (gL G) k'' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ,, tyW k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] wfty k k' A B @ lmax k' (lmax k k') ] ->
  [ G ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ⊢[ lC ] wihty k k' k'' A B M @ lmax k' k'' ] ->
  [ G ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
      ⊢[ lC ] c : wstepty k k' A B M @ k'' ] ->
  [ G ; Δ ⊢[ lC ] t : tyW k k' A B @ lmax k k' ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmElimW k k' k'' A B M c t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k'' Δ (M[lsingle t]) (boxt (tmElimW k k' k'' A B M c t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' Wk'' HA HB HM HF HI Hc Ht Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_ty_dnf HB) as HBd.
  pose proof (wf_ty_dnf HM) as HMd. pose proof (wf_tm_dnf Hc) as Hcd. pose proof (wf_tm_dnf Ht) as Htd.
  assert (Wkm : lwf (gL G) (lmax k k')) by (cbn; auto).
  assert (Wf : lwf (gL G) (lmax k' (lmax k k'))) by (cbn; repeat split; assumption).
  assert (Wi : lwf (gL G) (lmax k' k'')) by (cbn; auto).
  assert (HW : [ G ; Δ ⊢[ lC ] tyW k k' A B @ lmax k k' ])
    by (apply wft_W; [discriminate | exact Wk | exact Wk' | exact HA | exact HB]).
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (HΔW : [ G ; Δ ,, tyW k k' A B @ lmax k k' ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | exact (lift_ty HW HCD') | exact Wkm]).
  assert (HΔAF : [ G ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔA | exact (lift_ty HF HCD') | exact Wf]).
  assert (HΔS : [ G ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'' ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔAF | exact (lift_ty HI HCD') | exact Wi]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (boxT B)).
  set (x3 := elimT l1 l2 (mkrb MT Mt bs) k'' (Δ ,, tyW k k' A B @ lmax k k') (boxT M)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k''
               (Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
               (wstepty k k' A B M) (boxt c)).
  set (x5 := elimt l1 l2 (mkrb MT Mt bs) (lmax k k') Δ (tyW k k' A B) (boxt t)).
  set (os := GCtx Δ :: GTy A :: GTy B :: GTy M :: GTm c :: GTm t :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 3 6 5 (bs 42)) (k :: k' :: k'' :: nil)) os)
                     (x1 :: x2 :: x3 :: x4 :: x5 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 42 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (recT_wf Wk' HΔA HB) as Hx2.
  pose proof (recT_wf Wk'' HΔW HM) as Hx3.
  pose proof (rect_wf Wk'' HΔS (ctm_ty Hc) Hc) as Hx4. pose proof (rect_wf Wkm HΔ (ctm_ty Ht) Ht) as Hx5.
  assert (Ho : Forall dnfo os)
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact HBd | exact HMd | exact Hcd | exact Htd
                                  | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: x5 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | exact (wf_tm_dnf Hx3)
                                  | exact (wf_tm_dnf Hx4) | exact (wf_tm_dnf Hx5) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s os gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: k' :: k'' :: nil) lvar)) (brDecls 42) ++ gΨ G) ]).
  { change os with ((((((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTy B :: nil) ++ GTy M :: nil) ++ GTm c :: nil)
                      ++ GTm t :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 4) lC (tyW k k' (gv 3) (gv 2)) (lmax k k')) (o := GTm t)
             (gsub_wf_snoc (D := gdTm (cvar 3 ,, gv 2 @ k ,, wfty k k' (gv 2) (gv 1) @ lmax k' (lmax k k')
                                        ,, wihty k k' k'' (gv 2) (gv 1) (gv 0) @ lmax k' k'')
                                     lC (wstepty k k' (gv 2) (gv 1) (gv 0)) k'') (o := GTm c)
               (gsub_wf_snoc (D := gdTy (cvar 2 ,, tyW k k' (gv 1) (gv 0) @ lmax k k') lC k'') (o := GTy M)
                 (gsub_wf_snoc (D := gdTy (cvar 1 ,, gv 0 @ k) lC k') (o := GTy B)
                   (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                     (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) HBd _) HMd _) Hcd _)
               Htd _).
    4: { cbn [gdecl_gsubst gsubst GSubst_ctx GSubst_ty GSubst_tm]; rewrite ?gc_ext, ?gs_wfty, ?gs_wihty, ?gs_wstepty.
         cbn; sl0_rw HAd; sl0_rw HBd; sl0_rw HMd; exact Hc. }
    all: cbn; sl0_rw HAd; sl0_rw HBd; assumption. }
  refine (rr_br 42 (k :: k' :: k'' :: nil) os (x1 :: x2 :: x3 :: x4 :: x5 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_cons _ Wk'' (Forall_nil _)))) Ho Hxs Hσ _ _ _).
  - rr_ctx_W os; eassumption.
  - rr_res.
  - exact (brLv_t_id 42 (k :: k' :: k'' :: nil) eq_refl eq_refl).
Qed.

(** ** From the natural instances to the redex's *)

(** ** Length-indexed tuples and finite indices (M14b): the length's call
    is a term call at [Nat], as [succ]'s. *)

Lemma rr_T_vec {l Δ k A n r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyVec k A n @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyVec k A n) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tyVec k A n)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_vec Hc) as ((_ & Wk & HA & Hn) & _).
  pose proof (wf_ty_dnf HA) as HAd. pose proof (wf_tm_dnf Hn) as Hnd. pose proof (wf_ctx_dnf HΔ) as HΔd.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt n)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 43)) (k :: nil)) (GCtx Δ :: GTy A :: GTm n :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 43 ltac:(lia)) as Hb.
  pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Hn) Hn) as Hx2.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTm n :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact HAd | exact Hnd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTy A :: GTm n :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 43) ++ gΨ G) ]).
  { change (GCtx Δ :: GTy A :: GTm n :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTy A :: nil) ++ GTm n :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lC tyNat lzero) (o := GTm n)
              (gsub_wf_snoc (D := gdTy (cvar 0) lC k) (o := GTy A)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) HAd _) Hnd _).
    - cbn. exact HA.
    - cbn. exact Hn. }
  refine (rr_br 43 (k :: nil) (GCtx Δ :: GTy A :: GTm n :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 43 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codevec {l Δ T k s n r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ⊢[ lC ] n : tyNat @ lzero ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmVec k s n) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmVec k s n)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Hs Hn Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Hs) as Hsd. pose proof (wf_tm_dnf Hn) as Hnd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt n)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 44)) (k :: nil)) (GCtx Δ :: GTm s :: GTm n :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG. pose proof (Hbd 44 ltac:(lia)) as Hb.
  pose proof (rect_wf (lwf_suc Wk) HΔ (ctm_ty Hs) Hs) as Hx1.
  pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Hn) Hn) as Hx2.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm s :: GTm n :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Hsd | exact Hnd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil))
    by (repeat apply Forall_cons; [exact (wf_tm_dnf Hx1) | exact (wf_tm_dnf Hx2) | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm s :: GTm n :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext (k :: nil) lvar)) (brDecls 44) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm s :: GTm n :: nil) with (((nil ++ GCtx Δ :: nil) ++ GTm s :: nil) ++ GTm n :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 1) lC tyNat lzero) (o := GTm n)
              (gsub_wf_snoc (D := gdTm (cvar 0) lC (tyU k) (lsuc k)) (o := GTm s)
                 (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Hsd _) Hnd _).
    - cbn. exact Hs.
    - cbn. exact Hn. }
  refine (rr_br 44 (k :: nil) (GCtx Δ :: GTm s :: GTm n :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs Hσ _ _ _).
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 44 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_T_fin {l Δ n r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyFin n @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyFin n) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) lzero Δ (boxT (tyFin n)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_fin Hc) as ((_ & Hn) & _).
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Hn) as Hnd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt n)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 0 2 1 (bs 45)) nil) (GCtx Δ :: GTm n :: nil)) (x1 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG.
  pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Hn) Hn) as Hx1. pose proof (wf_tm_dnf Hx1) as Hx1d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm n :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Hnd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: nil)) by (apply Forall_cons; [exact Hx1d | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm n :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext nil lvar)) (brDecls 45) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm n :: nil) with ((nil ++ GCtx Δ :: nil) ++ GTm n :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 0) lC tyNat lzero) (o := GTm n)
              (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Hnd _).
    cbn. exact Hn. }
  refine (rr_br 45 nil (GCtx Δ :: GTm n :: nil) (x1 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_nil _) Ho Hxs Hσ _ _ _).
  - rr_ctx. exact Hx1.
  - rr_res.
  - exact (brLv_T_id 45 nil eq_refl eq_refl).
Qed.

Lemma rr_t_codefin {l Δ T n r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] n : tyNat @ lzero ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmFin n) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc lzero) Δ (tyU lzero) (boxt (tmFin n)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Hn Hred.
  pose proof (wf_ctx_dnf HΔ) as HΔd. pose proof (wf_tm_dnf Hn) as Hnd.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt n)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 0 2 1 (bs 46)) nil) (GCtx Δ :: GTm n :: nil)) (x1 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof HG_rr as HG.
  pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Hn) Hn) as Hx1. pose proof (wf_tm_dnf Hx1) as Hx1d.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm n :: nil))
    by (repeat apply Forall_cons; [exact HΔd | exact Hnd | apply Forall_nil]).
  assert (Hxs : Forall dnftm (x1 :: nil)) by (apply Forall_cons; [exact Hx1d | apply Forall_nil]).
  assert (Hσ : [ G ⊢ gext_s (GCtx Δ :: GTm n :: nil) gid :
                 mkG (gL G) (map (fun D => gdecl_usubst D (uext nil lvar)) (brDecls 46) ++ gΨ G) ]).
  { change (GCtx Δ :: GTm n :: nil) with ((nil ++ GCtx Δ :: nil) ++ GTm n :: nil).
    destruct G as [L Ψ].
    refine (gsub_wf_snoc (D := gdTm (cvar 0) lC tyNat lzero) (o := GTm n)
              (gsub_wf_snoc (D := gdCtx) (o := GCtx Δ) (gsub_wf_nil HG) HΔd HΔ) Hnd _).
    cbn. exact Hn. }
  refine (rr_br 46 nil (GCtx Δ :: GTm n :: nil) (x1 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_nil _) Ho Hxs Hσ _ _ _).
  - rr_ctx. exact Hx1.
  - rr_res.
  - exact (brLv_t_id 46 nil eq_refl eq_refl).
Qed.

(** ** Finitary well-founded trees (M15b): the payloads through [GW_br]. *)

Lemma rr_T_wf {l Δ k A N r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyWf k A N @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyWf k A N) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tyWf k A N)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_wf Hc) as ((_ & Wk & HA & HN) & _).
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) lzero (Δ ,, A @ k) tyNat (boxt N)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 47)) (k :: nil)) (GCtx Δ :: GTy A :: GTm N :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf (l := lzero) I HΔA (ctm_ty HN) HN) as Hx2.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTm N :: nil)) by (rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil)) by rr_dnf.
  refine (rr_br 47 (k :: nil) (GCtx Δ :: GTy A :: GTm N :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs (GW_br 47 (k :: nil) _ HG_rr _) _ _ _).
  - gw_solve.
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 47 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codewf {l Δ T k s n r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] n : tyNat @ lzero ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmWf k s n) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmWf k s n)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Hs Hn Hred.
  assert (HΔE : [ G ; Δ ,, tyEl k s @ k ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | apply wft_El; [discriminate | exact Wk | exact (lift_tm Hs HCD')] | exact Wk]).
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) lzero (Δ ,, tyEl k s @ k) tyNat (boxt n)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 48)) (k :: nil)) (GCtx Δ :: GTm s :: GTm n :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (rect_wf (lwf_suc Wk) HΔ (ctm_ty Hs) Hs) as Hx1.
  pose proof (rect_wf (l := lzero) I HΔE (ctm_ty Hn) Hn) as Hx2.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm s :: GTm n :: nil)) by (rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil)) by rr_dnf.
  refine (rr_br 48 (k :: nil) (GCtx Δ :: GTm s :: GTm n :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs (GW_br 48 (k :: nil) _ HG_rr _) _ _ _).
  - gw_solve.
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 48 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_supf {l Δ T k A N a cs r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G ; Δ ⊢[ lC ] cs : tyVec k (tyWf k A N) N[lsingle a] @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSupf k A N a cs) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ (tyWf k A N) (boxt (tmSupf k A N a cs)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk HA HN Ha Hcs Hred.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) lzero (Δ ,, A @ k) tyNat (boxt N)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tyVec k (tyWf k A N) N[lsingle a]) (boxt cs)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 5 4 (bs 49)) (k :: nil))
                             (GCtx Δ :: GTy A :: GTm N :: GTm a :: GTm cs :: nil)) (x1 :: x2 :: x3 :: x4 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf (l := lzero) I HΔA (ctm_ty HN) HN) as Hx2.
  pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx3. pose proof (rect_wf Wk HΔ (ctm_ty Hcs) Hcs) as Hx4.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTm N :: GTm a :: GTm cs :: nil)) by (rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: nil)) by rr_dnf.
  refine (rr_br 49 (k :: nil) (GCtx Δ :: GTy A :: GTm N :: GTm a :: GTm cs :: nil) (x1 :: x2 :: x3 :: x4 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_nil _)) Ho Hxs
            (GW_br 49 (k :: nil) _ HG_rr _) _ _ _).
  - gw_solve.
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 49 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_elimWf {l Δ T k k' A N M c t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] ->
  [ G ; Δ ,, tyWf k A N @ k ⊢[ lC ] M @ k' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] wfcsty k A N @ k ] ->
  [ G ; Δ ,, A @ k ,, wfcsty k A N @ k ⊢[ lC ] wfihty k k' A N M @ lmax lzero k' ] ->
  [ G ; Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k' ⊢[ lC ] c : wfstepty k A N M @ k' ] ->
  [ G ; Δ ⊢[ lC ] t : tyWf k A N @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmElimWf k k' A N M c t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k' Δ (M[lsingle t]) (boxt (tmElimWf k k' A N M c t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HA HN HM HCs HI Hc Ht Hred.
  assert (HW : [ G ; Δ ⊢[ lC ] tyWf k A N @ k ]) by (apply wft_wf; [discriminate | exact Wk | exact HA | exact HN]).
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (HΔW : [ G ; Δ ,, tyWf k A N @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HW HCD') | exact Wk]).
  assert (HΔS : [ G ; Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k' ⊢[ lD ] ])
    by (apply wfc_ext; [apply wfc_ext; [exact HΔA | exact (lift_ty HCs HCD') | exact Wk] | exact (lift_ty HI HCD')
                       | cbn; auto]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) lzero (Δ ,, A @ k) tyNat (boxt N)).
  set (x3 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, tyWf k A N @ k) (boxT M)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k')
               (wfstepty k A N M) (boxt c)).
  set (x5 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tyWf k A N) (boxt t)).
  set (os := GCtx Δ :: GTy A :: GTm N :: GTy M :: GTm c :: GTm t :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 6 5 (bs 50)) (k :: k' :: nil)) os) (x1 :: x2 :: x3 :: x4 :: x5 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf (l := lzero) I HΔA (ctm_ty HN) HN) as Hx2.
  pose proof (recT_wf Wk' HΔW HM) as Hx3. pose proof (rect_wf Wk' HΔS (ctm_ty Hc) Hc) as Hx4.
  pose proof (rect_wf Wk HΔ (ctm_ty Ht) Ht) as Hx5.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (os)) by (unfold os; rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: x5 :: nil)) by rr_dnf.
  refine (rr_br 50 (k :: k' :: nil) os (x1 :: x2 :: x3 :: x4 :: x5 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs
            (GW_br 50 (k :: k' :: nil) os HG_rr _) _ _ _).
  - unfold os; gw_solve.
  - rr_ctx_W os; eassumption.
  - rr_res.
  - exact (brLv_t_id 50 (k :: k' :: nil) eq_refl eq_refl).
Qed.

(** ** Propositional truncation (M16b): the payloads through [GW_br]. *)

Lemma rr_T_sq {l Δ k A r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tySq k A @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tySq k A) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tySq k A)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_sq Hc) as ((_ & Wk & HA) & _).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 2 1 (bs 51)) (k :: nil)) (GCtx Δ :: GTy A :: nil)) (x1 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wk HΔ HA) as Hx1.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: nil)) by (rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: nil)) by rr_dnf.
  refine (rr_br 51 (k :: nil) (GCtx Δ :: GTy A :: nil) (x1 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs (GW_br 51 (k :: nil) _ HG_rr _) _ _ _).
  - gw_solve.
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 51 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codesq {l Δ T k s r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSqCode k s) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmSqCode k s)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Hs Hred.
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 2 1 (bs 52)) (k :: nil)) (GCtx Δ :: GTm s :: nil)) (x1 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (rect_wf (lwf_suc Wk) HΔ (ctm_ty Hs) Hs) as Hx1.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm s :: nil)) by (rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: nil)) by rr_dnf.
  refine (rr_br 52 (k :: nil) (GCtx Δ :: GTm s :: nil) (x1 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs (GW_br 52 (k :: nil) _ HG_rr _) _ _ _).
  - gw_solve.
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 52 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_sq {l Δ T k A a r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSq k A a) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k Δ (tySq k A) (boxt (tmSq k A a)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk HA Ha Hred.
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 53)) (k :: nil)) (GCtx Δ :: GTy A :: GTm a :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx2.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (GCtx Δ :: GTy A :: GTm a :: nil)) by (rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil)) by rr_dnf.
  refine (rr_br 53 (k :: nil) (GCtx Δ :: GTy A :: GTm a :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs (GW_br 53 (k :: nil) _ HG_rr _) _ _ _).
  - gw_solve.
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 53 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_elimSq {l Δ T k k' A M c t r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, tySq k A @ k ⊢[ lC ] M @ k' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] c : tySq k' M⟨rlift ↑⟩[lsingle (tmSq k A⟨↑⟩ (var 0))] @ k' ] ->
  [ G ; Δ ⊢[ lC ] t : tySq k A @ k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmElimSq k k' A M c t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k' Δ (tySq k' M[lsingle t]) (boxt (tmElimSq k k' A M c t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wk' HA HM Hc Ht Hred.
  assert (HS : [ G ; Δ ⊢[ lC ] tySq k A @ k ]) by (apply wft_sq; [discriminate | exact Wk | exact HA]).
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (HΔS : [ G ; Δ ,, tySq k A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HS HCD') | exact Wk]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, tySq k A @ k) (boxT M)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) k' (Δ ,, A @ k) (tySq k' M⟨rlift ↑⟩[lsingle (tmSq k A⟨↑⟩ (var 0))]) (boxt c)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) k Δ (tySq k A) (boxt t)).
  set (os := GCtx Δ :: GTy A :: GTy M :: GTm c :: GTm t :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 5 4 (bs 54)) (k :: k' :: nil)) os) (x1 :: x2 :: x3 :: x4 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wk HΔ HA) as Hx1. pose proof (recT_wf Wk' HΔS HM) as Hx2.
  pose proof (rect_wf Wk' HΔA (ctm_ty Hc) Hc) as Hx3. pose proof (rect_wf Wk HΔ (ctm_ty Ht) Ht) as Hx4.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (os)) by (unfold os; rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: nil)) by rr_dnf.
  refine (rr_br 54 (k :: k' :: nil) os (x1 :: x2 :: x3 :: x4 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wk' (Forall_nil _))) Ho Hxs
            (GW_br 54 (k :: k' :: nil) os HG_rr _) _ _ _).
  - (* the step type: as [RecSSq]'s [gs_solve_sq] *)
    unfold os; gs_dnf;
    cbn [rev List.app map brDecls GWall gdecl_usubst gdecl_gsubst uext lvsubst Nat.ltb Nat.leb length nth Nat.sub
         gobj_wf dnfo];
    repeat split;
    first [ assumption | eapply wf_ctx_dnf; eassumption | gs_norm; assumption
          | unfold gv; W_cbn; gs_norm; W_cbn; rewrite <- ?SubstCommute.liftshift_single_ty; assumption ].
  - rr_ctx; rewrite ?subst_lshift1_ty, <- ?SubstCommute.liftshift_single_ty; eassumption.
  - rr_res.
  - exact (brLv_t_id 54 (k :: k' :: nil) eq_refl eq_refl).
Qed.

(** The weakened payload types of the indexed trees (M17c): [rr_ctx]'s
    [cbn] computes a global under one or two weakenings to its
    substitution by a shift, which [rr_sh] turns back into the weakenings
    the calls are typed at. *)
Lemma subst_lshift2_ty (T : ty) : T[lshift 2] = T⟨↑⟩⟨↑⟩.
Proof using . rewrite <- subst_lshift1_ty, <- subst_lshift1_ty. rewrite subst_comp_ty. reflexivity. Qed.
Lemma subst_lshift2 (t : tm) : t[lshift 2] = t⟨↑⟩⟨↑⟩.
Proof using . rewrite <- subst_lshift1, <- subst_lshift1. rewrite subst_comp. reflexivity. Qed.
Ltac rr_sh := rewrite ?subst_lshift2_ty, ?subst_lshift2, ?subst_lshift1_ty, ?subst_lshift1.
(** [supi]'s and [elim_IWf]'s scopes: [rr_ctx_W]'s, with the children's tuple type pushed
    through the substitutions as [gs_norm] does (RecSBase), so that
    [iwfFam]'s weakenings are not computed into shifts. *)
Ltac rr_ctx_I os :=
  cbn [brΓ brLocs cexts br_nu br_ng br_nl br_ar ucsubst mkLocs call_ty call_lv br_calls lext fold_left];
  rewrite ?gs_cext; rewrite wkc_inst' by reflexivity; rewrite Γ_id;
  repeat apply lsub_wf_lcons; [exact (lsub_wf_id G lM eq_refl Γ HΓ) | ..];
  repeat rr_wkb_rw;
  cbn [gsubst GSubst_ctx GSubst_ty GSubst_tm]; rewrite ?uc_ext, ?gc_ext;
  rewrite ?us_iwfcsty, ?us_iwfihty, ?us_iwfstepty, ?us_iwfmotty, ?gs_iwfcsty, ?gs_iwfihty, ?gs_iwfstepty,
          ?gs_iwfmotty;
  rewrite ?us_El_raw, ?us_DVec_raw, ?gs_El_raw, ?gs_DVec_raw, ?usubst_lsingle, ?gs_tm_subst_raw,
    ?usubst_iwfFam, ?gs_iwfFam_raw, ?usubst_ren_ty', ?usubst_ren', ?grs_ty_raw, ?grs_tm_raw;
  rewrite ?lvren_ush_uext' by reflexivity;
  rewrite ?(lvsubst_id l1 lvar (fun _ => eq_refl)), ?(lvsubst_id l2 lvar (fun _ => eq_refl));
  unfold os; unfold uext, gext_s, gv, gu; try unfold lsingle; try unfold lsucc;
  cbn [length Nat.ltb Nat.leb Nat.sub nth lvsubst ucsubst usubst_tm usubst_ty ulsubst gcsubst gsubst_tm
       gsubst_ty glsubst pctx pty ptm subst_tm subst_ty lcomp gsubst GSubst_tm GSubst_ty GSubst_ctx subst
       Subst_tm Subst_ty lext fold_left llk lcons'];
  rr_sl0; rr_sh.

(** ** Dependent tuples and indexed trees (M17c): the payloads through
    [GW_br], as [Wf]'s. *)

Lemma rr_T_dvec {l Δ k n F r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyDVec k n F @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyDVec k n F) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) k Δ (boxT (tyDVec k n F)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_dvec Hc) as ((_ & Wk & Hn & HF) & _).
  assert (HΔF : [ G ; Δ ,, tyFin n @ lzero ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | apply wft_fin; [discriminate | exact (lift_tm Hn HCD')] | exact I]).
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt n)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k (Δ ,, tyFin n @ lzero) (boxT F)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 55)) (k :: nil)) (GCtx Δ :: GTm n :: GTy F :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Hn) Hn) as Hx1. pose proof (recT_wf Wk HΔF HF) as Hx2.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm n :: GTy F :: nil)) by (rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil)) by rr_dnf.
  refine (rr_br 55 (k :: nil) (GCtx Δ :: GTm n :: GTy F :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs (GW_br 55 (k :: nil) _ HG_rr _) _ _ _).
  - gw_solve.
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_T_id 55 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codedvec {l Δ T k n f r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k ->
  [ G ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> [ G ; Δ ,, tyFin n @ lzero ⊢[ lC ] f : tyU k @ lsuc k ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmDVec k n f) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc k) Δ (tyU k) (boxt (tmDVec k n f)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Hn Hf Hred.
  assert (HΔF : [ G ; Δ ,, tyFin n @ lzero ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | apply wft_fin; [discriminate | exact (lift_tm Hn HCD')] | exact I]).
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) lzero Δ tyNat (boxt n)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) (Δ ,, tyFin n @ lzero) (tyU k) (boxt f)).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 1 3 2 (bs 56)) (k :: nil)) (GCtx Δ :: GTm n :: GTm f :: nil))
                     (x1 :: x2 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (rect_wf (l := lzero) I HΔ (ctm_ty Hn) Hn) as Hx1.
  pose proof (rect_wf (lwf_suc Wk) HΔF (ctm_ty Hf) Hf) as Hx2.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo (GCtx Δ :: GTm n :: GTm f :: nil)) by (rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: nil)) by rr_dnf.
  refine (rr_br 56 (k :: nil) (GCtx Δ :: GTm n :: GTm f :: nil) (x1 :: x2 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_nil _)) Ho Hxs (GW_br 56 (k :: nil) _ HG_rr _) _ _ _).
  - gw_solve.
  - rr_ctx; eassumption.
  - rr_res.
  - exact (brLv_t_id 56 (k :: nil) eq_refl eq_refl).
Qed.

Lemma rr_T_iwf {l Δ k ki X A N Ot C m r} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] tyIWf k ki X A N Ot C m @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ (tyIWf k ki X A N Ot C m) = Some r ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) (lmax k ki) Δ (boxT (tyIWf k ki X A N Ot C m)) @ l1 ].
Proof using Hrb HΓ.
  intros HΔ Hc Hred.
  destruct (inv_ty_iwf Hc) as ((_ & Wk & Wki & HX & HA & HN & HO & HC & Hm) & _).
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (HΔAF : [ G ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔA | apply wft_fin; [discriminate | exact (lift_tm HN HCD')] | exact I]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) ki Δ (boxT X)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) lzero (Δ ,, A @ k) tyNat (boxt N)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) ki (Δ ,, A @ k) X⟨↑⟩ (boxt Ot)).
  set (x5 := elimt l1 l2 (mkrb MT Mt bs) ki (Δ ,, A @ k ,, tyFin N @ lzero) X⟨↑⟩⟨↑⟩ (boxt C)).
  set (x6 := elimt l1 l2 (mkrb MT Mt bs) ki Δ X (boxt m)).
  set (os := GCtx Δ :: GTy X :: GTy A :: GTm N :: GTm Ot :: GTm C :: GTm m :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 7 6 (bs 57)) (k :: ki :: nil)) os)
                     (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil))
    by (cbn [redT] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wki HΔ HX) as Hx1. pose proof (recT_wf Wk HΔ HA) as Hx2.
  pose proof (rect_wf (l := lzero) I HΔA (ctm_ty HN) HN) as Hx3. pose proof (rect_wf Wki HΔA (ctm_ty HO) HO) as Hx4.
  pose proof (rect_wf Wki HΔAF (ctm_ty HC) HC) as Hx5. pose proof (rect_wf Wki HΔ (ctm_ty Hm) Hm) as Hx6.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo os) by (unfold os; rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil)) by rr_dnf.
  refine (rr_br 57 (k :: ki :: nil) os (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wki (Forall_nil _))) Ho Hxs (GW_br 57 (k :: ki :: nil) os HG_rr _) _ _ _).
  - unfold os; gw_solve.
  - rr_ctx; rr_sh; eassumption.
  - rr_res.
  - exact (brLv_T_id 57 (k :: ki :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_codeiwf {l Δ T k ki x s n o c m r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) ki ->
  [ G ; Δ ⊢[ lC ] x : tyU ki @ lsuc ki ] -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] n : tyNat @ lzero ] ->
  [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] o : tyEl ki x⟨↑⟩ @ ki ] ->
  [ G ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ⊢[ lC ] c : tyEl ki x⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G ; Δ ⊢[ lC ] m : tyEl ki x @ ki ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmIWf k ki x s n o c m) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lsuc (lmax k ki)) Δ (tyU (lmax k ki)) (boxt (tmIWf k ki x s n o c m)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wki Hx Hs Hn Ho' Hc Hm Hred.
  assert (HΔE : [ G ; Δ ,, tyEl k s @ k ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔ | apply wft_El; [discriminate | exact Wk | exact (lift_tm Hs HCD')] | exact Wk]).
  assert (HΔEF : [ G ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔE | apply wft_fin; [discriminate | exact (lift_tm Hn HCD')] | exact I]).
  set (x1 := elimt l1 l2 (mkrb MT Mt bs) (lsuc ki) Δ (tyU ki) (boxt x)).
  set (x2 := elimt l1 l2 (mkrb MT Mt bs) (lsuc k) Δ (tyU k) (boxt s)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) lzero (Δ ,, tyEl k s @ k) tyNat (boxt n)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) ki (Δ ,, tyEl k s @ k) (tyEl ki x⟨↑⟩) (boxt o)).
  set (x5 := elimt l1 l2 (mkrb MT Mt bs) ki (Δ ,, tyEl k s @ k ,, tyFin n @ lzero) (tyEl ki x⟨↑⟩⟨↑⟩) (boxt c)).
  set (x6 := elimt l1 l2 (mkrb MT Mt bs) ki Δ (tyEl ki x) (boxt m)).
  set (os := GCtx Δ :: GTm x :: GTm s :: GTm n :: GTm o :: GTm c :: GTm m :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 7 6 (bs 58)) (k :: ki :: nil)) os)
                     (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (rect_wf (lwf_suc Wki) HΔ (ctm_ty Hx) Hx) as Hx1.
  pose proof (rect_wf (lwf_suc Wk) HΔ (ctm_ty Hs) Hs) as Hx2.
  pose proof (rect_wf (l := lzero) I HΔE (ctm_ty Hn) Hn) as Hx3. pose proof (rect_wf Wki HΔE (ctm_ty Ho') Ho') as Hx4.
  pose proof (rect_wf Wki HΔEF (ctm_ty Hc) Hc) as Hx5. pose proof (rect_wf Wki HΔ (ctm_ty Hm) Hm) as Hx6.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo os) by (unfold os; rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil)) by rr_dnf.
  refine (rr_br 58 (k :: ki :: nil) os (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: nil) ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wki (Forall_nil _))) Ho Hxs (GW_br 58 (k :: ki :: nil) os HG_rr _) _ _ _).
  - unfold os; gw_solve.
  - rr_ctx; rr_sh; eassumption.
  - rr_res.
  - exact (brLv_t_id 58 (k :: ki :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_supi {l Δ T k ki X A N Ot C a cs r} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) k -> lwf (gL G) ki ->
  [ G ; Δ ⊢[ lC ] X @ ki ] -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G ; Δ ,, A @ k ⊢[ lC ] Ot : X⟨↑⟩ @ ki ] ->
  [ G ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lC ] C : X⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G ; Δ ⊢[ lC ] cs : tyDVec (lmax k ki) N[lsingle a] (iwfFam k ki X A N Ot C a) @ lmax k ki ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmSupi k ki X A N Ot C a cs) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) (lmax k ki) Δ (tyIWf k ki X A N Ot C Ot[lsingle a])
                        (boxt (tmSupi k ki X A N Ot C a cs)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wki HX HA HN HO HC Ha Hcs Hred.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (HΔAF : [ G ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔA | apply wft_fin; [discriminate | exact (lift_tm HN HCD')] | exact I]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) ki Δ (boxT X)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) lzero (Δ ,, A @ k) tyNat (boxt N)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) ki (Δ ,, A @ k) X⟨↑⟩ (boxt Ot)).
  set (x5 := elimt l1 l2 (mkrb MT Mt bs) ki (Δ ,, A @ k ,, tyFin N @ lzero) X⟨↑⟩⟨↑⟩ (boxt C)).
  set (x6 := elimt l1 l2 (mkrb MT Mt bs) k Δ A (boxt a)).
  set (x7 := elimt l1 l2 (mkrb MT Mt bs) (lmax k ki) Δ
               (tyDVec (lmax k ki) N[lsingle a] (iwfFam k ki X A N Ot C a)) (boxt cs)).
  set (os := GCtx Δ :: GTy X :: GTy A :: GTm N :: GTm Ot :: GTm C :: GTm a :: GTm cs :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 2 8 7 (bs 59)) (k :: ki :: nil)) os)
                     (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wki HΔ HX) as Hx1. pose proof (recT_wf Wk HΔ HA) as Hx2.
  pose proof (rect_wf (l := lzero) I HΔA (ctm_ty HN) HN) as Hx3. pose proof (rect_wf Wki HΔA (ctm_ty HO) HO) as Hx4.
  pose proof (rect_wf Wki HΔAF (ctm_ty HC) HC) as Hx5. pose proof (rect_wf Wk HΔ (ctm_ty Ha) Ha) as Hx6.
  pose proof (rect_wf (l := lmax k ki) (conj Wk Wki) HΔ (ctm_ty Hcs) Hcs) as Hx7.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo os) by (unfold os; rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: nil)) by rr_dnf.
  refine (rr_br 59 (k :: ki :: nil) os (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: nil) ltac:(cbv; lia)
            eq_refl eq_refl eq_refl (Forall_cons _ Wk (Forall_cons _ Wki (Forall_nil _))) Ho Hxs
            (GW_br 59 (k :: ki :: nil) os HG_rr _) _ _ _).
  - unfold os; gw_solve.
  - rr_ctx_I os; eassumption.
  - rr_res.
  - exact (brLv_t_id 59 (k :: ki :: nil) eq_refl eq_refl).
Qed.

Lemma rr_t_elimIWf {l Δ T k ki k' X A N Ot C M c m t r} : [ G ; Δ ⊢[ lD ] ] ->
  lwf (gL G) k -> lwf (gL G) ki -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] X @ ki ] -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G ; Δ ,, A @ k ⊢[ lC ] Ot : X⟨↑⟩ @ ki ] ->
  [ G ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lC ] C : X⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G ; Δ ,, X @ ki ⊢[ lC ] iwfmotty k ki X A N Ot C @ lmax k ki ] ->
  [ G ; Δ ,, X @ ki ,, iwfmotty k ki X A N Ot C @ lmax k ki ⊢[ lC ] M @ k' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] iwfcsty k ki X A N Ot C @ lmax k ki ] ->
  [ G ; Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ⊢[ lC ] iwfihty k ki k' X A N Ot C M @ lmax lzero k' ] ->
  [ G ; Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ,, iwfihty k ki k' X A N Ot C M @ lmax lzero k'
      ⊢[ lC ] c : iwfstepty k ki X A N Ot C M @ k' ] ->
  [ G ; Δ ⊢[ lC ] m : X @ ki ] -> [ G ; Δ ⊢[ lC ] t : tyIWf k ki X A N Ot C m @ lmax k ki ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T (tmElimIWf k ki k' X A N Ot C M c m t) = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) k' Δ (M[lsingle2 m t]) (boxt (tmElimIWf k ki k' X A N Ot C M c m t)) @ l2 ].
Proof using Hrb HΓ.
  intros HΔ Wk Wki Wk' HX HA HN HO HC HMo HM HCs HI Hc Hm Ht Hred.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HA HCD') | exact Wk]).
  assert (HΔAF : [ G ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔA | apply wft_fin; [discriminate | exact (lift_tm HN HCD')] | exact I]).
  assert (HΔX : [ G ; Δ ,, X @ ki ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (lift_ty HX HCD') | exact Wki]).
  assert (HΔXM : [ G ; Δ ,, X @ ki ,, iwfmotty k ki X A N Ot C @ lmax k ki ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΔX | exact (lift_ty HMo HCD') | exact (conj Wk Wki)]).
  assert (HΔS : [ G ; Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ,, iwfihty k ki k' X A N Ot C M @ lmax lzero k'
                  ⊢[ lD ] ])
    by (apply wfc_ext; [apply wfc_ext; [exact HΔA | exact (lift_ty HCs HCD') | exact (conj Wk Wki)]
                       | exact (lift_ty HI HCD') | cbn; auto]).
  set (x1 := elimT l1 l2 (mkrb MT Mt bs) ki Δ (boxT X)).
  set (x2 := elimT l1 l2 (mkrb MT Mt bs) k Δ (boxT A)).
  set (x3 := elimt l1 l2 (mkrb MT Mt bs) lzero (Δ ,, A @ k) tyNat (boxt N)).
  set (x4 := elimt l1 l2 (mkrb MT Mt bs) ki (Δ ,, A @ k) X⟨↑⟩ (boxt Ot)).
  set (x5 := elimt l1 l2 (mkrb MT Mt bs) ki (Δ ,, A @ k ,, tyFin N @ lzero) X⟨↑⟩⟨↑⟩ (boxt C)).
  set (x6 := elimT l1 l2 (mkrb MT Mt bs) k' (Δ ,, X @ ki ,, iwfmotty k ki X A N Ot C @ lmax k ki) (boxT M)).
  set (x7 := elimt l1 l2 (mkrb MT Mt bs) k'
               (Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ,, iwfihty k ki k' X A N Ot C M @ lmax lzero k')
               (iwfstepty k ki X A N Ot C M) (boxt c)).
  set (x8 := elimt l1 l2 (mkrb MT Mt bs) ki Δ X (boxt m)).
  set (x9 := elimt l1 l2 (mkrb MT Mt bs) (lmax k ki) Δ (tyIWf k ki X A N Ot C m) (boxt t)).
  set (os := GCtx Δ :: GTy X :: GTy A :: GTm N :: GTm Ot :: GTm C :: GTy M :: GTm c :: GTm m :: GTm t :: nil).
  assert (Er : r = peelLs (peelGs (peelUs (wrap 3 10 9 (bs 60)) (k :: ki :: k' :: nil)) os)
                     (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil))
    by (cbn [redt] in Hred; apply Some_inj in Hred; rewrite <- Hred; reflexivity).
  subst r. pose proof (recT_wf Wki HΔ HX) as Hx1. pose proof (recT_wf Wk HΔ HA) as Hx2.
  pose proof (rect_wf (l := lzero) I HΔA (ctm_ty HN) HN) as Hx3. pose proof (rect_wf Wki HΔA (ctm_ty HO) HO) as Hx4.
  pose proof (rect_wf Wki HΔAF (ctm_ty HC) HC) as Hx5. pose proof (recT_wf Wk' HΔXM HM) as Hx6.
  pose proof (rect_wf Wk' HΔS (ctm_ty Hc) Hc) as Hx7. pose proof (rect_wf Wki HΔ (ctm_ty Hm) Hm) as Hx8.
  pose proof (rect_wf (l := lmax k ki) (conj Wk Wki) HΔ (ctm_ty Ht) Ht) as Hx9.
  gs_dnf. pose proof (wf_ctx_dnf HΔ) as HΔd.
  assert (Ho : Forall dnfo os) by (unfold os; rr_dnf).
  assert (Hxs : Forall dnftm (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil)) by rr_dnf.
  refine (rr_br 60 (k :: ki :: k' :: nil) os (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            (Forall_cons _ Wk (Forall_cons _ Wki (Forall_cons _ Wk' (Forall_nil _)))) Ho Hxs
            (GW_br 60 (k :: ki :: k' :: nil) os HG_rr _) _ _ _).
  - unfold os; gw_solve.
  - rr_ctx_I os; eassumption.
  - rr_res.
  - exact (brLv_t_id 60 (k :: ki :: k' :: nil) eq_refl eq_refl).
Qed.

Lemma HMT_rr : [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ].
Proof using Hrb. exact (proj1 (proj2 (proj2 Hrb))). Qed.
Lemma HMt_rr : [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ].
Proof using Hrb. exact (proj1 (proj2 (proj2 (proj2 Hrb)))). Qed.

Lemma motT_move {l0 l Δ c r} : [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) l0 Δ (boxT c) @ l1 ] ->
  lequiv (gL G) l0 l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] c @ l0 ] ->
  [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) l Δ (boxT c) @ l1 ].
Proof using Hrb HΓ.
  intros Hr El HΔ Hc.
  assert (Hb : [ G ; Γ ⊢[ lM ] boxT c : tyCTyp Δ l0 @ lzero ])
    by (apply wf_boxT; [exact HΓ | exact (lequiv_wf_l _ _ _ El) | exact HΔ | exact Hc]).
  pose proof (declM_motT_eq (eqty_refl _ _ _ _ _ HMT_rr) Hl1 El (eqc_refl _ _ _ HΔ) (eqtm_refl _ _ _ _ _ _ Hb)) as E.
  exact (wf_conv _ _ _ _ _ _ _ Hr (eqty_sym _ _ _ _ _ _ E)).
Qed.

Lemma mott_move {l0 l Δ U T c r} : [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) l0 Δ U (boxt c) @ l2 ] ->
  lequiv (gL G) l0 l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] U ≅ T @ l0 ] -> [ G ; Δ ⊢[ lC ] c : U @ l0 ] ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) l Δ T (boxt c) @ l2 ].
Proof using Hrb HΓ.
  intros Hr El HΔ EU Hc.
  assert (Hb : [ G ; Γ ⊢[ lM ] boxt c : tyCTrm Δ U l0 @ lzero ])
    by (apply wf_boxt; [exact HΓ | exact (lequiv_wf_l _ _ _ El) | exact HΔ | exact (ctm_ty Hc) | exact Hc]).
  pose proof (declM_mott_eq (eqty_refl _ _ _ _ _ HMt_rr) Hl2 El (eqc_refl _ _ _ HΔ) EU (eqtm_refl _ _ _ _ _ _ Hb)) as E.
  exact (wf_conv _ _ _ _ _ _ _ Hr (eqty_sym _ _ _ _ _ _ E)).
Qed.

Lemma lvl_eq_lequiv' {L k l} : lvl_eq L k l -> lwf L l -> lequiv L l k.
Proof using . intros [-> | E] W; [exact (lequiv_refl _ _ W) | exact (lequiv_sym _ _ _ E)]. Qed.

(** The type recursor. *)
Lemma rr_T_all {l Δ c r} : lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] c @ l ] ->
  redT l1 l2 (mkrb MT Mt bs) l Δ c = Some r -> [ G ; Γ ⊢[ lM ] r : motT (wrapMT MT) l Δ (boxT c) @ l1 ].
Proof using Hrb HΓ.
  intros Wl HΔ Hc Hred.
  destruct c; try discriminate Hred;
  first
  [ solve [ destruct (inv_ty_nat Hc) as (_ & Hk);
            pose proof (lvl_eq_lequiv' Hk I) as E;
            exact (motT_move (rr_T_nat HΔ Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_pi Hc) as ((_ & Wk & Wk' & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk (conj Wk Wk')) as E;
            exact (motT_move (rr_T_pi HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_U Hc) as ((_ & _ & Wk) & Hk);
            pose proof (lvl_eq_lequiv' Hk (lwf_suc Wk)) as E;
            exact (motT_move (rr_T_U HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_El Hc) as ((_ & Wk & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_El HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_sig Hc) as ((_ & Wk & Wk' & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk (conj Wk Wk')) as E;
            exact (motT_move (rr_T_sig HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_unit Hc) as ((_ & _ & Wk) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_unit HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_id Hc) as ((_ & Wk & _ & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_id HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_seq Hc) as ((_ & Wk & _ & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_seq HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_sempty Hc) as ((_ & _ & Wk) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_sempty HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_empty Hc) as ((_ & _ & Wk) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_empty HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_sum Hc) as ((_ & Wk & Wk' & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk (conj Wk Wk')) as E;
            exact (motT_move (rr_T_sum HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_W Hc) as ((_ & Wk & Wk' & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk (conj Wk Wk')) as E;
            exact (motT_move (rr_T_W HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_vec Hc) as ((_ & Wk & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_vec HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_fin Hc) as (_ & Hk);
            pose proof (lvl_eq_lequiv' Hk I) as E;
            exact (motT_move (rr_T_fin HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_wf Hc) as ((_ & Wk & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_wf HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_sq Hc) as ((_ & Wk & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_sq HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_dvec Hc) as ((_ & Wk & _ & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk Wk) as E;
            exact (motT_move (rr_T_dvec HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ]
  | solve [ destruct (inv_ty_iwf Hc) as ((_ & Wk & Wki & _) & Hk);
            pose proof (lvl_eq_lequiv' Hk (conj Wk Wki)) as E;
            exact (motT_move (rr_T_iwf HΔ Hc Hred) E HΔ (wft_lconv _ _ _ _ _ _ Hc E)) ] ].
Qed.

End RR.

(** ** The term recursor, by induction on the code's C-typing

    The statement quantifies over the redex's index and level, equal to
    the code's type and level: conversions of the code's typing are
    absorbed, and the [λ] reduct reads the index's codomain. *)

Definition RTC (G : gctx) (Δ : ctx) (c : tm) (U : ty) (l0 : lvl) : Prop :=
  [ G ; Δ ⊢[ lC ] c : U @ l0 ] ->
  forall Γ l1 l2 MT Mt bs, [ G ; Γ ⊢[ lM ] ] -> RBwf G Γ l1 l2 MT Mt bs -> [ G ; Δ ⊢[ lD ] ] ->
  forall l T r, lequiv (gL G) l l0 -> [ G ; Δ ⊢[ lD ] T ≅ U @ l ] ->
  redt l1 l2 (mkrb MT Mt bs) l Δ T c = Some r ->
  [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) l Δ T (boxt c) @ l2 ].

(** At a natural instance, then moved. *)
Lemma RTC_nat_inst {G Δ c U l0} :
  (forall Γ l1 l2 MT Mt bs, [ G ; Γ ⊢[ lM ] ] -> RBwf G Γ l1 l2 MT Mt bs -> [ G ; Δ ⊢[ lD ] ] ->
     forall l T r, redt l1 l2 (mkrb MT Mt bs) l Δ T c = Some r ->
     [ G ; Γ ⊢[ lM ] r : mott (wrapMt Mt) l0 Δ U (boxt c) @ l2 ]) ->
  RTC G Δ c U l0.
Proof.
  intros H Hc Γ l1 l2 MT Mt bs HΓ Hrb HΔ l T r El ET Hred.
  refine (mott_move HΓ Hrb (H Γ l1 l2 MT Mt bs HΓ Hrb HΔ l T r Hred) (lequiv_sym _ _ _ El) HΔ _ Hc).
  exact (eqty_sym _ _ _ _ _ _ (eqty_lconv _ _ _ _ _ _ _ ET (lequiv_sym _ _ _ El))).
Qed.

Lemma C_var {G Δ n U l0} : in_ctx Δ n U l0 -> RTC G Δ (var n) U l0.
Proof.
  intros Hin Hc Γ l1 l2 MT Mt bs HΓ Hrb HΔ l T r El ET Hred.
  pose proof (eqty_wf_l (i := lD) eq_refl ET) as HT.
  assert (HV : [ G ; Δ ⊢[ lV ] var n : T @ l ]).
  { eapply wf_lconv; [| exact El]. eapply wf_conv; [exact (wf_var _ lV _ _ _ _ HΔ Hin) |].
    exact (eqty_lconv _ _ _ _ _ _ _ ET (lequiv_sym _ _ _ El)). }
  exact (rr_t_var HΓ Hrb HΔ (lequiv_wf_l _ _ _ El) HT HV Hred).
Qed.

Lemma C_nat {G Δ} : RTC G Δ tmNat (tyU lzero) (lsuc lzero).
Proof. apply RTC_nat_inst. intros. exact (rr_t_nat H H0 H1 H2). Qed.
Lemma C_zero {G Δ} : RTC G Δ zero tyNat lzero.
Proof. apply RTC_nat_inst. intros. exact (rr_t_zero H H0 H1 H2). Qed.
Lemma C_U {G Δ k} : lwf (gL G) k -> RTC G Δ (tmU k) (tyU (lsuc k)) (lsuc (lsuc k)).
Proof. intros Wk. apply RTC_nat_inst. intros. exact (rr_t_U H H0 H1 Wk H2). Qed.
Lemma C_succ {G Δ t} : [ G ; Δ ⊢[ lC ] t : tyNat @ lzero ] -> RTC G Δ (succ t) tyNat lzero.
Proof. intros Ht. apply RTC_nat_inst. intros. exact (rr_t_succ H H0 H1 Ht H2). Qed.
Lemma C_pi {G Δ k k' s t} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  RTC G Δ (tmPi k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof. intros Wk Wk' Hs Ht. apply RTC_nat_inst. intros. exact (rr_t_pi H H0 H1 Wk Wk' Hs Ht H2). Qed.
Lemma C_natrec {G Δ k M s z t} : lwf (gL G) k -> [ G ; Δ ,, tyNat @ lzero ⊢[ lC ] M @ k ] ->
  [ G ; Δ ⊢[ lC ] s : M[lsingle zero] @ k ] -> [ G ; Δ ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z : M[lsucc] @ k ] ->
  [ G ; Δ ⊢[ lC ] t : tyNat @ lzero ] -> RTC G Δ (natrec k M s z t) M[lsingle t] k.
Proof. intros Wk HM Hs Hz Ht. apply RTC_nat_inst. intros. exact (rr_t_natrec H H0 H1 Wk HM Hs Hz Ht H2). Qed.
Lemma C_app {G Δ k k' A B f a} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] f : tyPi k k' A B @ lmax k k' ] ->
  [ G ; Δ ⊢[ lC ] a : A @ k ] -> RTC G Δ (app f k k' A B a) B[lsingle a] k'.
Proof. intros Wk Wk' HA HB Hf Ha. apply RTC_nat_inst. intros. exact (rr_t_app H H0 H1 Wk Wk' HA HB Hf Ha H2). Qed.

Lemma C_codesig {G Δ k k' s t} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  RTC G Δ (tmSig k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof. intros Wk Wk' Hs Ht. apply RTC_nat_inst. intros. exact (rr_t_codesig H H0 H1 Wk Wk' Hs Ht H2). Qed.
Lemma C_codeunit {G Δ k} : lwf (gL G) k -> RTC G Δ (tmUnit k) (tyU k) (lsuc k).
Proof. intros Wk. apply RTC_nat_inst. intros. exact (rr_t_codeunit H H0 H1 Wk H2). Qed.
Lemma C_triv {G Δ k} : lwf (gL G) k -> RTC G Δ (tmTriv k) (tyUnit k) k.
Proof. intros Wk. apply RTC_nat_inst. intros. exact (rr_t_triv H H0 H1 Wk H2). Qed.
Lemma C_pair {G Δ k k' A B a b} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] -> [ G ; Δ ⊢[ lC ] b : B[lsingle a] @ k' ] ->
  RTC G Δ (tmPair k k' A B a b) (tySig k k' A B) (lmax k k').
Proof. intros Wk Wk' HA HB Ha Hb. apply RTC_nat_inst. intros. exact (rr_t_pair H H0 H1 Wk Wk' HA HB Ha Hb H2). Qed.
Lemma C_fst {G Δ k k' A B p} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] ->
  RTC G Δ (tmFst k k' A B p) A k.
Proof. intros Wk Wk' HA HB Hp. apply RTC_nat_inst. intros. exact (rr_t_fst H H0 H1 Wk Wk' HA HB Hp H2). Qed.
Lemma C_snd {G Δ k k' A B p} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] ->
  RTC G Δ (tmSnd k k' A B p) B[lsingle (tmFst k k' A B p)] k'.
Proof. intros Wk Wk' HA HB Hp. apply RTC_nat_inst. intros. exact (rr_t_snd H H0 H1 Wk Wk' HA HB Hp H2). Qed.

Lemma C_codeid {G Δ k s t u} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ⊢[ lC ] t : tyEl k s @ k ] -> [ G ; Δ ⊢[ lC ] u : tyEl k s @ k ] ->
  RTC G Δ (tmId k s t u) (tyU k) (lsuc k).
Proof. intros Wk Hs Ht Hu. apply RTC_nat_inst. intros. exact (rr_t_codeid H H0 H1 Wk Hs Ht Hu H2). Qed.
Lemma C_refl {G Δ k A a} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  RTC G Δ (tmRefl k A a) (tyId k A a a) k.
Proof. intros Wk HA Ha. apply RTC_nat_inst. intros. exact (rr_t_refl H H0 H1 Wk HA Ha H2). Qed.
Lemma C_J {G Δ k k' A a M c u e0} : lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ] ->
  [ G ; Δ ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lC ] M @ k' ] ->
  [ G ; Δ ⊢[ lC ] c : M[lsingle2 a (tmRefl k A a)] @ k' ] ->
  [ G ; Δ ⊢[ lC ] u : A @ k ] -> [ G ; Δ ⊢[ lC ] e0 : tyId k A a u @ k ] ->
  RTC G Δ (tmJ k k' A a M c u e0) (M[lsingle2 u e0]) k'.
Proof.
  intros Wk Wk' HA Ha HI HM Hc Hu He0. apply RTC_nat_inst. intros.
  exact (rr_t_J H H0 H1 Wk Wk' HA Ha HI HM Hc Hu He0 H2).
Qed.

(** Strict equality (M10c). *)
Lemma C_codeseq {G Δ k s t u} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ⊢[ lC ] t : tyEl k s @ k ] -> [ G ; Δ ⊢[ lC ] u : tyEl k s @ k ] ->
  RTC G Δ (tmSEq k s t u) (tyU k) (lsuc k).
Proof. intros Wk Hs Ht Hu. apply RTC_nat_inst. intros. exact (rr_t_codeseq H H0 H1 Wk Hs Ht Hu H2). Qed.
Lemma C_codesempty {G Δ k} : lwf (gL G) k -> RTC G Δ (tmSEmpty k) (tyU k) (lsuc k).
Proof. intros Wk. apply RTC_nat_inst. intros. exact (rr_t_codesempty H H0 H1 Wk H2). Qed.
Lemma C_srefl {G Δ k A a} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  RTC G Δ (srefl k A a) (tySEq k A a a) k.
Proof. intros Wk HA Ha. apply RTC_nat_inst. intros. exact (rr_t_srefl H H0 H1 Wk HA Ha H2). Qed.
Lemma C_elimSEmpty {G Δ k k' M e0} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] M @ k' ] ->
  [ G ; Δ ⊢[ lC ] e0 : tySEmpty k @ k ] -> RTC G Δ (elimSEmpty k k' M e0) M k'.
Proof. intros Wk Wk' HM He0. apply RTC_nat_inst. intros. exact (rr_t_elimSEmpty H H0 H1 Wk Wk' HM He0 H2). Qed.

(** The empty type and binary sums (M12c). *)
Lemma C_codeempty {G Δ k} : lwf (gL G) k -> RTC G Δ (tmEmpty k) (tyU k) (lsuc k).
Proof. intros Wk. apply RTC_nat_inst. intros. exact (rr_t_codeempty H H0 H1 Wk H2). Qed.
Lemma C_elimEmpty {G Δ k k' M t} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ,, tyEmpty k' @ k' ⊢[ lC ] M @ k ] ->
  [ G ; Δ ⊢[ lC ] t : tyEmpty k' @ k' ] -> RTC G Δ (elimEmpty k k' M t) (M[lsingle t]) k.
Proof. intros Wk Wk' HM Ht. apply RTC_nat_inst. intros. exact (rr_t_elimEmpty H H0 H1 Wk Wk' HM Ht H2). Qed.
Lemma C_codesum {G Δ k k' s t} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ⊢[ lC ] t : tyU k' @ lsuc k' ] -> RTC G Δ (tmSum k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof. intros Wk Wk' Hs Ht. apply RTC_nat_inst. intros. exact (rr_t_codesum H H0 H1 Wk Wk' Hs Ht H2). Qed.
Lemma C_inl {G Δ k k' A B a} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] -> RTC G Δ (tmInl k k' A B a) (tySum k k' A B) (lmax k k').
Proof. intros Wk Wk' HA HB Ha. apply RTC_nat_inst. intros. exact (rr_t_inl H H0 H1 Wk Wk' HA HB Ha H2). Qed.
Lemma C_inr {G Δ k k' A B b} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] b : B @ k' ] -> RTC G Δ (tmInr k k' A B b) (tySum k k' A B) (lmax k k').
Proof. intros Wk Wk' HA HB Hb. apply RTC_nat_inst. intros. exact (rr_t_inr H H0 H1 Wk Wk' HA HB Hb H2). Qed.
Lemma C_case {G Δ k k' k'' A B M c1 c2 t} : lwf (gL G) k -> lwf (gL G) k' -> lwf (gL G) k'' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ,, tySum k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] c1 : M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G ; Δ ,, B @ k' ⊢[ lC ] c2 : M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G ; Δ ⊢[ lC ] t : tySum k k' A B @ lmax k k' ] ->
  RTC G Δ (tmCase k k' k'' A B M c1 c2 t) (M[lsingle t]) k''.
Proof.
  intros Wk Wk' Wk'' HA HB HM Hc1 Hc2 Ht. apply RTC_nat_inst. intros.
  exact (rr_t_case H H0 H1 Wk Wk' Wk'' HA HB HM Hc1 Hc2 Ht H2).
Qed.

(** Well-founded trees (M13b). *)
Lemma C_codeW {G Δ k k' s t} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] -> RTC G Δ (tmW k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof. intros Wk Wk' Hs Ht. apply RTC_nat_inst. intros. exact (rr_t_codeW H H0 H1 Wk Wk' Hs Ht H2). Qed.
Lemma C_sup {G Δ k k' A B a f} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G ; Δ ⊢[ lC ] f : tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  RTC G Δ (tmSup k k' A B a f) (tyW k k' A B) (lmax k k').
Proof. intros Wk Wk' HA HB Ha Hf. apply RTC_nat_inst. intros. exact (rr_t_sup H H0 H1 Wk Wk' HA HB Ha Hf H2). Qed.
Lemma C_elimW {G Δ k k' k'' A B M c t} : lwf (gL G) k -> lwf (gL G) k' -> lwf (gL G) k'' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G ; Δ ,, tyW k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] wfty k k' A B @ lmax k' (lmax k k') ] ->
  [ G ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ⊢[ lC ] wihty k k' k'' A B M @ lmax k' k'' ] ->
  [ G ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
      ⊢[ lC ] c : wstepty k k' A B M @ k'' ] ->
  [ G ; Δ ⊢[ lC ] t : tyW k k' A B @ lmax k k' ] ->
  RTC G Δ (tmElimW k k' k'' A B M c t) (M[lsingle t]) k''.
Proof.
  intros Wk Wk' Wk'' HA HB HM HF HI Hc Ht. apply RTC_nat_inst. intros.
  exact (rr_t_elimW H H0 H1 Wk Wk' Wk'' HA HB HM HF HI Hc Ht H2).
Qed.

Lemma C_codevec {G Δ k s n} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> RTC G Δ (tmVec k s n) (tyU k) (lsuc k).
Proof. intros Wk Hs Hn. apply RTC_nat_inst. intros. exact (rr_t_codevec H H0 H1 Wk Hs Hn H2). Qed.
Lemma C_codefin {G Δ n} : [ G ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> RTC G Δ (tmFin n) (tyU lzero) (lsuc lzero).
Proof. intros Hn. apply RTC_nat_inst. intros. exact (rr_t_codefin H H0 H1 Hn H2). Qed.

Lemma C_lam {G Δ k k' A B b} : lwf (gL G) k -> lwf (gL G) k' -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] b : B @ k' ] -> RTC G Δ (lam k k' A b) (tyPi k k' A B) (lmax k k').
Proof.
  intros Wk Wk' HA Hb Hc Γ l1 l2 MT Mt bs HΓ Hrb HΔ l T r El ET Hred.
  destruct T; try discriminate Hred.
  match type of Hred with context [ redt _ _ _ _ _ (tyPi ?a ?b' ?c ?d) _ ] =>
    rename a into k1, b' into k2, c into A1, d into B1 end.
  destruct (decl_pi_inj ET) as (E1 & E2 & EA & EB).
  pose proof (lift_ty HA HCD') as HAD.
  assert (HΔA : [ G ; Δ ,, A @ k ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact HAD | exact Wk]).
  assert (EB' : [ G ; Δ ,, A @ k ⊢[ lD ] B1 ≅ B @ k' ]).
  { refine (eqty_lconv _ _ _ _ _ _ _ _ E2).
    exact (stab_eqty (i := lD) eq_refl EA (lequiv_sym _ _ _ E1) HΔA EB). }
  pose proof (eqty_wf_l (i := lD) eq_refl EB') as HB1.
  pose proof (wf_conv _ _ _ _ _ _ _ Hb EB') as Hb1.
  pose proof (rr_t_lam HΓ Hrb HΔ Wk Wk' HA HB1 Hb1 Hred) as X.
  assert (EA' : [ G ; Δ ⊢[ lD ] A ≅ A1 @ k ])
    by exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EA) E1).
  assert (EU : [ G ; Δ ⊢[ lD ] tyPi k k' A B1 ≅ tyPi k1 k2 A1 B1 @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact E1 | exact E2 | exact HAD | exact EA' | exact (eqty_refl _ _ _ _ _ HB1)]).
  assert (EP : [ G ; Δ ⊢[ lD ] tyPi k k' A B1 ≅ tyPi k k' A B @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact (lequiv_refl _ _ Wk) | exact (lequiv_refl _ _ Wk') | exact HAD
                       | exact (eqty_refl _ _ _ _ _ HAD) | exact EB']).
  exact (mott_move HΓ Hrb X (lequiv_sym _ _ _ El) HΔ EU (wf_conv _ _ _ _ _ _ _ Hc EP)).
Qed.

Lemma C_conv {G Δ c U U' l0} : [ G ; Δ ⊢[ lC ] c : U' @ l0 ] -> [ G ; Δ ⊢[ lD ] U ≅ U' @ l0 ] ->
  RTC G Δ c U' l0 -> RTC G Δ c U l0.
Proof.
  intros Hc' EU IH Hc Γ l1 l2 MT Mt bs HΓ Hrb HΔ l T r El ET Hred.
  exact (IH Hc' Γ l1 l2 MT Mt bs HΓ Hrb HΔ l T r El
           (eqty_trans _ _ _ _ _ _ _ ET (eqty_lconv _ _ _ _ _ _ _ EU El)) Hred).
Qed.

Lemma C_lconv {G Δ c U l0 l0'} : [ G ; Δ ⊢[ lC ] c : U @ l0' ] -> lequiv (gL G) l0 l0' ->
  RTC G Δ c U l0' -> RTC G Δ c U l0.
Proof.
  intros Hc' E IH Hc Γ l1 l2 MT Mt bs HΓ Hrb HΔ l T r El ET Hred.
  exact (IH Hc' Γ l1 l2 MT Mt bs HΓ Hrb HΔ l T r (lequiv_trans _ _ _ _ El E) ET Hred).
Qed.

Lemma C_codewf {G Δ k s n} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] n : tyNat @ lzero ] -> RTC G Δ (tmWf k s n) (tyU k) (lsuc k).
Proof. intros Wk Hs Hn. apply RTC_nat_inst. intros. exact (rr_t_codewf H H0 H1 Wk Hs Hn H2). Qed.
Lemma C_supf {G Δ k A N a cs} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G ; Δ ⊢[ lC ] cs : tyVec k (tyWf k A N) N[lsingle a] @ k ] -> RTC G Δ (tmSupf k A N a cs) (tyWf k A N) k.
Proof. intros Wk HA HN Ha Hcs. apply RTC_nat_inst. intros. exact (rr_t_supf H H0 H1 Wk HA HN Ha Hcs H2). Qed.
Lemma C_elimWf {G Δ k k' A N M c t} : lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] ->
  [ G ; Δ ,, tyWf k A N @ k ⊢[ lC ] M @ k' ] -> [ G ; Δ ,, A @ k ⊢[ lC ] wfcsty k A N @ k ] ->
  [ G ; Δ ,, A @ k ,, wfcsty k A N @ k ⊢[ lC ] wfihty k k' A N M @ lmax lzero k' ] ->
  [ G ; Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k' ⊢[ lC ] c : wfstepty k A N M @ k' ] ->
  [ G ; Δ ⊢[ lC ] t : tyWf k A N @ k ] -> RTC G Δ (tmElimWf k k' A N M c t) (M[lsingle t]) k'.
Proof.
  intros Wk Wk' HA HN HM HCs HI Hc Ht. apply RTC_nat_inst. intros.
  exact (rr_t_elimWf H H0 H1 Wk Wk' HA HN HM HCs HI Hc Ht H2).
Qed.

(** Propositional truncation (M16b). *)
Lemma C_codesq {G Δ k s} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  RTC G Δ (tmSqCode k s) (tyU k) (lsuc k).
Proof. intros Wk Hs. apply RTC_nat_inst. intros. exact (rr_t_codesq H H0 H1 Wk Hs H2). Qed.
Lemma C_sq {G Δ k A a} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  RTC G Δ (tmSq k A a) (tySq k A) k.
Proof. intros Wk HA Ha. apply RTC_nat_inst. intros. exact (rr_t_sq H H0 H1 Wk HA Ha H2). Qed.
Lemma C_elimSq {G Δ k k' A M c t} : lwf (gL G) k -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] A @ k ] -> [ G ; Δ ,, tySq k A @ k ⊢[ lC ] M @ k' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] c : tySq k' M⟨rlift ↑⟩[lsingle (tmSq k A⟨↑⟩ (var 0))] @ k' ] ->
  [ G ; Δ ⊢[ lC ] t : tySq k A @ k ] -> RTC G Δ (tmElimSq k k' A M c t) (tySq k' M[lsingle t]) k'.
Proof.
  intros Wk Wk' HA HM Hc Ht. apply RTC_nat_inst. intros.
  exact (rr_t_elimSq H H0 H1 Wk Wk' HA HM Hc Ht H2).
Qed.

(** Dependent tuples and indexed trees (M17c). *)
Lemma C_codedvec {G Δ k n f} : lwf (gL G) k -> [ G ; Δ ⊢[ lC ] n : tyNat @ lzero ] ->
  [ G ; Δ ,, tyFin n @ lzero ⊢[ lC ] f : tyU k @ lsuc k ] -> RTC G Δ (tmDVec k n f) (tyU k) (lsuc k).
Proof. intros Wk Hn Hf. apply RTC_nat_inst. intros. exact (rr_t_codedvec H H0 H1 Wk Hn Hf H2). Qed.
Lemma C_codeiwf {G Δ k ki x s n o c m} : lwf (gL G) k -> lwf (gL G) ki ->
  [ G ; Δ ⊢[ lC ] x : tyU ki @ lsuc ki ] -> [ G ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] n : tyNat @ lzero ] ->
  [ G ; Δ ,, tyEl k s @ k ⊢[ lC ] o : tyEl ki x⟨↑⟩ @ ki ] ->
  [ G ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ⊢[ lC ] c : tyEl ki x⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G ; Δ ⊢[ lC ] m : tyEl ki x @ ki ] ->
  RTC G Δ (tmIWf k ki x s n o c m) (tyU (lmax k ki)) (lsuc (lmax k ki)).
Proof.
  intros Wk Wki Hx Hs Hn Ho Hc Hm. apply RTC_nat_inst. intros.
  exact (rr_t_codeiwf H H0 H1 Wk Wki Hx Hs Hn Ho Hc Hm H2).
Qed.
Lemma C_supi {G Δ k ki X A N Ot C a cs} : lwf (gL G) k -> lwf (gL G) ki ->
  [ G ; Δ ⊢[ lC ] X @ ki ] -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G ; Δ ,, A @ k ⊢[ lC ] Ot : X⟨↑⟩ @ ki ] ->
  [ G ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lC ] C : X⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G ; Δ ⊢[ lC ] cs : tyDVec (lmax k ki) N[lsingle a] (iwfFam k ki X A N Ot C a) @ lmax k ki ] ->
  RTC G Δ (tmSupi k ki X A N Ot C a cs) (tyIWf k ki X A N Ot C Ot[lsingle a]) (lmax k ki).
Proof.
  intros Wk Wki HX HA HN HO HC Ha Hcs. apply RTC_nat_inst. intros.
  exact (rr_t_supi H H0 H1 Wk Wki HX HA HN HO HC Ha Hcs H2).
Qed.
Lemma C_elimIWf {G Δ k ki k' X A N Ot C M c m t} : lwf (gL G) k -> lwf (gL G) ki -> lwf (gL G) k' ->
  [ G ; Δ ⊢[ lC ] X @ ki ] -> [ G ; Δ ⊢[ lC ] A @ k ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G ; Δ ,, A @ k ⊢[ lC ] Ot : X⟨↑⟩ @ ki ] ->
  [ G ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lC ] C : X⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G ; Δ ,, X @ ki ⊢[ lC ] iwfmotty k ki X A N Ot C @ lmax k ki ] ->
  [ G ; Δ ,, X @ ki ,, iwfmotty k ki X A N Ot C @ lmax k ki ⊢[ lC ] M @ k' ] ->
  [ G ; Δ ,, A @ k ⊢[ lC ] iwfcsty k ki X A N Ot C @ lmax k ki ] ->
  [ G ; Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ⊢[ lC ] iwfihty k ki k' X A N Ot C M @ lmax lzero k' ] ->
  [ G ; Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ,, iwfihty k ki k' X A N Ot C M @ lmax lzero k'
      ⊢[ lC ] c : iwfstepty k ki X A N Ot C M @ k' ] ->
  [ G ; Δ ⊢[ lC ] m : X @ ki ] -> [ G ; Δ ⊢[ lC ] t : tyIWf k ki X A N Ot C m @ lmax k ki ] ->
  RTC G Δ (tmElimIWf k ki k' X A N Ot C M c m t) (M[lsingle2 m t]) k'.
Proof.
  intros Wk Wki Wk' HX HA HN HO HC HMo HM HCs HI Hc Hm Ht. apply RTC_nat_inst. intros.
  exact (rr_t_elimIWf H H0 H1 Wk Wki Wk' HX HA HN HO HC HMo HM HCs HI Hc Hm Ht H2).
Qed.

Lemma rec_t_code {G i Δ c U l0} : [ G ; Δ ⊢[ i ] c : U @ l0 ] -> i = lC -> RTC G Δ c U l0.
Proof.
  induction 1; intros Ei; try discriminate Ei; subst;
    repeat match goal with IH : lC = lC -> _ |- _ => specialize (IH eq_refl) end;
    first
    [ solve [eapply C_var; eassumption] | solve [eapply C_nat] | solve [eapply C_zero]
    | solve [eapply C_U; eassumption] | solve [eapply C_succ; eassumption] | solve [eapply C_pi; eassumption]
    | solve [eapply C_natrec; eassumption] | solve [eapply C_app; eassumption] | solve [eapply C_lam; eassumption]
    | solve [eapply C_conv; eassumption] | solve [eapply C_lconv; eassumption]
    | solve [eapply C_codesig; eassumption] | solve [eapply C_codeunit; eassumption]
    | solve [eapply C_triv; eassumption] | solve [eapply C_pair; eassumption]
    | solve [eapply C_fst; eassumption] | solve [eapply C_snd; eassumption]
    | solve [eapply C_codeid; eassumption] | solve [eapply C_refl; eassumption]
    | solve [eapply C_J; eassumption]
    | solve [eapply C_codeseq; eassumption] | solve [eapply C_codesempty; eassumption]
    | solve [eapply C_srefl; eassumption] | solve [eapply C_elimSEmpty; eassumption]
    | solve [eapply C_codeempty; eassumption] | solve [eapply C_elimEmpty; eassumption]
    | solve [eapply C_codesum; eassumption] | solve [eapply C_inl; eassumption]
    | solve [eapply C_inr; eassumption] | solve [eapply C_case; eassumption]
    | solve [eapply C_codeW; eassumption] | solve [eapply C_sup; eassumption]
    | solve [eapply C_elimW; eassumption]
    | solve [eapply C_codevec; eassumption] | solve [eapply C_codefin; eassumption]
    | solve [eapply C_codewf; eassumption] | solve [eapply C_supf; eassumption]
    | solve [eapply C_elimWf; eassumption]
    | solve [eapply C_codesq; eassumption] | solve [eapply C_sq; eassumption]
    | solve [eapply C_elimSq; eassumption]
    | solve [eapply C_codedvec; eassumption] | solve [eapply C_codeiwf; eassumption]
    | solve [eapply C_supi; eassumption] | solve [eapply C_elimIWf; eassumption]
    | solve [intros _ ? ? ? ? ? ? _ _ _ ? ? ? _ _ Hred; cbn in Hred; discriminate Hred] ].
Qed.
