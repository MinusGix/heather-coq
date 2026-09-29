(** * The recursors' scope premises are admissible (M7_DESIGN.md C1, J3.3)

    The recursor rules take the well-formedness of the branch contexts
    ([brΓ]) as premises (M3_DESIGN.md E10), and the branches are typed at
    [brRes]. Both are motive instances in the branch scope: the motives
    weakened past the branch's levels, globals and locals ([wkb]), at
    scrutinees built from the branch's own global variables. So they are
    well formed when the motives are ([brΓ_wf], [brRes_wf]). The motives
    are moved into the branch scope by universe and global weakening under
    their own binders ([MT_br], [Mt_br]), instantiated by [motT_wf] and
    [mott_wf], and weakened past the recursive calls' locals. *)
From DeLaM.Typing Require Export InvAny AlgStruct.

(** ** The motives in the branch scope *)

Lemma MT_uwk {G Γ} nu MT l1 : [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
  [ recGT (gctx_uwk nu G) ; recΓT Γ⟨ush nu⟩ᵤ ⊢[ lM ] uren_ty MT (uupr (ush nu)) @ lvren (lvren l1 (ush nu)) (ush 1) ].
Proof.
  intros H.
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ H (S (nu + gL G)) (uup (fun j => lvar (ush nu j)))
                (usub_ok_uup _ _ _ (usub_ok_ush nu (gL G)))) as X.
  unfold G_us in X. rewrite recGT_usubst, <- gctx_uwk_as, recΓT_usubst, <- uren_ush_ctx in X.
  pose proof (lvren_ush_usubst l1 1 (fun j => lvar (ush nu j))) as E; change (uupn 1 ?φ) with (uup φ) in E.
  rewrite E, <- lvren_ush in X.
  rewrite <- (proj1 uren_as_usubst_all MT (uupr (ush nu))) in X by (intros [|n]; reflexivity).
  exact X.
Qed.

Lemma Mt_uwk {G Γ} nu Mt l2 : [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
  [ recGt (gctx_uwk nu G) ; recΓt Γ⟨ush nu⟩ᵤ ⊢[ lM ] uren_ty Mt (uupr (ush nu)) @ lvren (lvren l2 (ush nu)) (ush 1) ].
Proof.
  intros H.
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ H (S (nu + gL G)) (uup (fun j => lvar (ush nu j)))
                (usub_ok_uup _ _ _ (usub_ok_ush nu (gL G)))) as X.
  unfold G_us in X. rewrite recGt_usubst, <- gctx_uwk_as, recΓt_usubst, <- uren_ush_ctx in X.
  pose proof (lvren_ush_usubst l2 1 (fun j => lvar (ush nu j))) as E; change (uupn 1 ?φ) with (uup φ) in E.
  rewrite E, <- lvren_ush in X.
  rewrite <- (proj1 uren_as_usubst_all Mt (uupr (ush nu))) in X by (intros [|n]; reflexivity).
  exact X.
Qed.

Lemma gwk_ok_br {G} k : k < nbr -> gwk_ok (gwk_stepn (br_ng k)) (brG k G) (gctx_uwk (br_nu k) G).
Proof. intros Hk. split; [cbn; lia |]. unfold brG; cbn [gΨ]. rewrite <- (brDecls_len k Hk). apply gwk_stepn_wf. Qed.

Lemma MT_gwk {G Γ} k MT l : k < nbr -> [ ⊢ G ] ->
  [ recGT (gctx_uwk (br_nu k) G) ; recΓT Γ⟨ush (br_nu k)⟩ᵤ ⊢[ lM ] MT @ l ] ->
  [ recGT (brG k G) ; recΓT (wkc (br_nu k) (br_ng k) Γ) ⊢[ lM ] gren_ty MT (gupr (ush (br_ng k))) @ l ].
Proof.
  intros Hk HG H. destruct (gwk_ok_recGT (gwk_ok_br (G := G) k Hk)) as [HL Hw'].
  pose proof (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ H _ _ _ HL Hw' (wf_recGT (wf_brG HG k Hk))) as X.
  assert (Ef : forall i, gwk_fn (gwk_up (gwk_stepn (br_ng k))) i = gupr (ush (br_ng k)) i)
    by (intros [|i]; cbn [gwk_fn gupr]; [reflexivity | rewrite gwk_stepn_fn; reflexivity]).
  unfold gren, GRen_ty, GRen_ctx in X.
  rewrite (proj1 gren_ext_all MT _ _ Ef), (proj1 (proj2 (proj2 gren_ext_all)) _ _ _ Ef) in X.
  change (gcren ?Δ ?ξ) with (Δ⟪ξ⟫) in X. rewrite recΓT_gren in X. exact X.
Qed.

Lemma Mt_gwk {G Γ} k Mt l : k < nbr -> [ ⊢ G ] ->
  [ recGt (gctx_uwk (br_nu k) G) ; recΓt Γ⟨ush (br_nu k)⟩ᵤ ⊢[ lM ] Mt @ l ] ->
  [ recGt (brG k G) ; recΓt (wkc (br_nu k) (br_ng k) Γ) ⊢[ lM ] gren_ty Mt (gupr (gupr (ush (br_ng k)))) @ l ].
Proof.
  intros Hk HG H. destruct (gwk_ok_recGt (gwk_ok_br (G := G) k Hk)) as [HL Hw'].
  pose proof (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ H _ _ _ HL Hw' (wf_recGt (wf_brG HG k Hk))) as X.
  assert (Ef : forall i, gwk_fn (gwk_up (gwk_up (gwk_stepn (br_ng k)))) i = gupr (gupr (ush (br_ng k))) i)
    by (intros [|[|i]]; cbn [gwk_fn gupr]; [reflexivity | reflexivity | rewrite gwk_stepn_fn; reflexivity]).
  unfold gren, GRen_ty, GRen_ctx in X.
  rewrite (proj1 gren_ext_all Mt _ _ Ef), (proj1 (proj2 (proj2 gren_ext_all)) _ _ _ Ef) in X.
  change (gcren ?Δ ?ξ) with (Δ⟪ξ⟫) in X. rewrite recΓt_gren in X. exact X.
Qed.

(** ** Instances at the branch's own locals *)

Lemma ren_lift0_ty (T : ty) : nfty T -> T⟨rlift (rshift 0)⟩ = T.
Proof.
  intros H. assert (E0 : ren_ty T (rshift 0) = T) by exact (ren_id_ty T H).
  change (ren_ty T (rlift (rshift 0)) = T).
  pose proof (proj1 ren_ren_all T (rshift 0) (rlift (rshift 0)) (rshift 0)) as X.
  cbv beta in X. rewrite E0 in X. apply X. intros [|n]; cbn; lia.
Qed.

Section Br.
Context {G : gctx} {Γ : ctx} (HΓ : [ G ; Γ ⊢[ lM ] ]) (k : nat) (Hk : k < nbr).
Let nu := br_nu k.
Let ng := br_ng k.

Lemma motT_br0 MT l1 lv g c : [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
  lwf (gL (brG k G)) lv -> [ brG k G ; g ⊢[ lD ] ] ->
  [ brG k G ; wkc nu ng Γ ⊢[ lM ] c : tyCTyp g lv @ lzero ] ->
  [ brG k G ; wkc nu ng Γ ⊢[ lM ] motT (wkb nu ng 0 (wrapMT MT)) lv g c @ lvren l1 (ush nu) ].
Proof.
  intros HM Hl Hg Hc. pose proof (MT_gwk k _ _ Hk (ctx_glob _ _ _ HΓ) (MT_uwk nu MT l1 HM)) as Y.
  pose proof (motT_wf _ _ _ _ _ _ _ Y Hl Hg Hc) as X.
  unfold wkb, wrapMT; cbn [uren_tm gren_tm ren_tm]. unfold wrapMT in X.
  rewrite ren_lift0_ty by exact (dnfty_nfty _ (wf_ty_dnf Y)). exact X.
Qed.

Lemma mott_br0 Mt l2 lv g U c : [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
  lwf (gL (brG k G)) lv -> [ brG k G ; g ⊢[ lD ] ] -> [ brG k G ; g ⊢[ lD ] U @ lv ] ->
  [ brG k G ; wkc nu ng Γ ⊢[ lM ] c : tyCTrm g U lv @ lzero ] ->
  [ brG k G ; wkc nu ng Γ ⊢[ lM ] mott (wkb nu ng 0 (wrapMt Mt)) lv g U c @ lvren l2 (ush nu) ].
Proof.
  intros HM Hl Hg HU Hc. pose proof (Mt_gwk k _ _ Hk (ctx_glob _ _ _ HΓ) (Mt_uwk nu Mt l2 HM)) as Y.
  pose proof (mott_wf _ _ _ _ _ _ _ _ Y Hl Hg HU Hc) as X.
  unfold wkb, wrapMt; cbn [uren_tm gren_tm ren_tm]. unfold wrapMt in X.
  rewrite ren_lift0_ty by exact (dnfty_nfty _ (wf_ty_dnf Y)). exact X.
Qed.

End Br.

(** One more local of the branch scope. *)
Lemma wkb_S nu ng j w : (wkb nu ng j w)⟨↑⟩ = wkb nu ng (S j) w.
Proof.
  unfold wkb, ren, Ren_tm. apply (proj1 (proj2 ren_ren_all)). intros n; cbn; lia.
Qed.
Lemma motT_wkS nu ng j w lv g c : c⟨↑⟩ = c ->
  (motT (wkb nu ng j w) lv g c)⟨↑⟩ = motT (wkb nu ng (S j) w) lv g c.
Proof. intros Hc. rewrite motT_ren, wkb_S, Hc. reflexivity. Qed.
Lemma mott_wkS nu ng j w lv g U c : c⟨↑⟩ = c ->
  (mott (wkb nu ng j w) lv g U c)⟨↑⟩ = mott (wkb nu ng (S j) w) lv g U c.
Proof. intros Hc. rewrite mott_ren, wkb_S, Hc. reflexivity. Qed.

Lemma lM_notV' : lM <> lV. Proof. discriminate. Qed.

(** A branch-scope context entry or result: weaken to the scope's base, then
    instantiate. *)
Ltac br_inst k HΓ HMT HMt :=
  lazymatch goal with
  | |- [ _ ; _ ,, _ @ _ ⊢[ lM ] motT (wkb ?nu ?ng (S ?j) ?w) ?lv ?g ?c @ _ ] =>
      rewrite <- (motT_wkS nu ng j w lv g c eq_refl);
      apply (wk1_ty _ lM eq_refl); [br_ctx k HΓ HMT HMt | br_inst k HΓ HMT HMt]
  | |- [ _ ; _ ,, _ @ _ ⊢[ lM ] mott (wkb ?nu ?ng (S ?j) ?w) ?lv ?g ?U ?c @ _ ] =>
      rewrite <- (mott_wkS nu ng j w lv g U c eq_refl);
      apply (wk1_ty _ lM eq_refl); [br_ctx k HΓ HMT HMt | br_inst k HΓ HMT HMt]
  | |- [ _ ; _ ⊢[ lM ] motT (wkb _ _ 0 _) _ _ _ @ _ ] => eapply (motT_br0 HΓ k ltac:(lia)); [ exact HMT | .. ]
  | |- [ _ ; _ ⊢[ lM ] mott (wkb _ _ 0 _) _ _ _ _ @ _ ] => eapply (mott_br0 HΓ k ltac:(lia)); [ exact HMt | .. ]
  end
with br_ctx k HΓ HMT HMt :=
  lazymatch goal with
  | |- [ _ ; _ ,, _ @ _ ⊢[ lM ] ] => apply wfc_ext; [br_ctx k HΓ HMT HMt | br_inst k HΓ HMT HMt | ]
  | |- [ _ ; wkc _ _ _ ⊢[ lM ] ] => apply (wf_wkc_br _ _ k ltac:(lia) HΓ)
  end.

Lemma lwf_ush {L l} n : lwf L l -> lwf (n + L) (lvren l (ush n)).
Proof. apply lwf_lvren. intros m Hm; unfold ush; lia. Qed.

(** The instances of [U_M] in the [elimN] branch, at any position. *)
Lemma wf_UM_succ' G U g : [ G ; cvar g ,, tyNat @ lzero ,, tyGvar U (lshift 0) @ lvar 0 ⊢[ lD ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g ,, tyNat @ lzero) lC (lvar 0)) ->
  [ G ; cvar g ,, tyNat @ lzero ,, tyGvar U (lshift 0) @ lvar 0 ⊢[ lD ] tyGvar U lsucc @ lvar 0 ].
Proof.
  intros HΓ Hin. eapply wft_gvar; eauto.
  all: first [ discriminate | (unfold lle; cbn; lia) | (split; [reflexivity | intros; cbn; f_equal; lia])
             | (cbn; tauto) | idtac ].
  intros n A k HA. inversion HA as [? ? ? | ? ? ? ? ? ? HA']; subst; [|inversion HA'].
  cbn. apply wf_succ; [discriminate|].
  exact (wf_var _ lD _ 1 _ _ HΓ (in_there _ _ _ _ _ _ (in_here _ _ _))).
Qed.

Lemma wf_UM_zero' G U g : [ G ; cvar g ⊢[ lD ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g ,, tyNat @ lzero) lC (lvar 0)) ->
  [ G ; cvar g ⊢[ lD ] tyGvar U (lsingle zero) @ lvar 0 ].
Proof.
  intros HΓ Hin. eapply wft_gvar; eauto.
  all: first [ discriminate | (unfold lle; cbn; lia) | (split; [reflexivity | intros; cbn; f_equal; lia])
             | (cbn; tauto) | idtac ].
  intros n A k HA. inversion HA as [? ? ? | ? ? ? ? ? ? HA']; subst; [|inversion HA'].
  cbn. apply wf_zero; [discriminate | exact HΓ].
Qed.

(** A type variable over one more local, at a term. *)
Lemma wf_gv_single G i U g A lA l a : i <> lV -> [ G ; cvar g ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g ,, A @ lA) lC l) -> lle lC i -> dnfl (lsingle a) ->
  [ G ; cvar g ⊢[ i ] a : A⟨↑⟩[lsingle a] @ lA ] ->
  [ G ; cvar g ⊢[ i ] tyGvar U (lsingle a) @ l ].
Proof.
  intros Hv HΓ Hin Hle Hd Ha. eapply wft_gvar; eauto.
  - split; [reflexivity | intros; cbn; f_equal; lia].
  - intros n B k HB. inversion HB as [? ? ? | ? ? ? ? ? ? HB']; subst; [exact Ha | inversion HB'].
Qed.

(** Code rules with their result types as equations, for [eapply]. *)
Lemma wf_natrec' G i Γ l M s z t T : T = M[lsingle t] -> i <> lV -> lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] -> [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] -> [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] natrec l M s z t : T @ l ].
Proof. intros ->; apply wf_natrec. Qed.
Lemma wf_app' G i Γ l l' A B t s T : T = B[lsingle s] -> i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] -> [ G ; Γ ⊢[ i ] s : A @ l ] ->
  [ G ; Γ ⊢[ i ] app t l l' A B s : T @ l' ].
Proof. intros ->; apply wf_app. Qed.

Lemma wf_snd' G i Γ l l' A B p T : T = B[lsingle (tmFst l l' A B p)] -> i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] -> [ G ; Γ ⊢[ i ] tmSnd l l' A B p : T @ l' ].
Proof. intros ->; apply wf_snd. Qed.

Ltac code_side :=
  repeat match goal with
  | |- [ _ ; _ ⊢[ _ ] tyGvar _ lsucc @ _ ] => apply wf_UM_succ'; [ | glookup ]
  | |- [ _ ; _ ⊢[ _ ] tyGvar _ (lsingle zero) @ _ ] => apply wf_UM_zero'; [ | glookup ]
  | |- [ _ ; cvar _ ⊢[ _ ] tyGvar _ (lsingle _) @ _ ] =>
      eapply wf_gv_single; [ discriminate | | glookup | unfold lle; cbn; lia | cbn; tauto | cbn ]
  | |- [ _ ; _ ⊢[ _ ] tmNat : _ @ _ ] => apply wf_code_nat; [ discriminate | ]
  | |- [ _ ; _ ⊢[ _ ] tmU _ : _ @ _ ] => apply wf_code_U; [ discriminate | | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tmPi _ _ _ _ : _ @ _ ] => apply wf_code_pi; [ discriminate | lvl_ok | lvl_ok | | ]
  | |- [ _ ; _ ⊢[ _ ] zero : _ @ _ ] => apply wf_zero; [ discriminate | ]
  | |- [ _ ; _ ⊢[ _ ] succ _ : _ @ _ ] => apply wf_succ; [ discriminate | ]
  | |- [ _ ; _ ⊢[ _ ] natrec _ _ _ _ _ : _ @ _ ] => eapply wf_natrec'; [ reflexivity | discriminate | lvl_ok | .. ]
  | |- [ _ ; _ ⊢[ _ ] lam _ _ _ _ : _ @ _ ] => apply wf_lam; [ discriminate | lvl_ok | lvl_ok | | ]
  | |- [ _ ; _ ⊢[ _ ] app _ _ _ _ _ _ : _ @ _ ] => eapply wf_app'; [ reflexivity | discriminate | lvl_ok | lvl_ok | .. ]
  | |- [ _ ; _ ⊢[ _ ] tmSig _ _ _ _ : _ @ _ ] => apply wf_code_sig; [ discriminate | lvl_ok | lvl_ok | | ]
  | |- [ _ ; _ ⊢[ _ ] tmPair _ _ _ _ _ _ : _ @ _ ] => apply wf_pair; [ discriminate | lvl_ok | lvl_ok | .. ]
  | |- [ _ ; _ ⊢[ _ ] tmFst _ _ _ _ _ : _ @ _ ] => apply wf_fst; [ discriminate | lvl_ok | lvl_ok | .. ]
  | |- [ _ ; _ ⊢[ _ ] tmSnd _ _ _ _ _ : _ @ _ ] => eapply wf_snd'; [ reflexivity | discriminate | lvl_ok | lvl_ok | .. ]
  | |- [ _ ; _ ⊢[ _ ] tmUnit _ : _ @ _ ] => apply wf_code_unit; [ discriminate | | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tmTriv _ : _ @ _ ] => apply wf_triv; [ discriminate | | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] ] => progress wfd
  | |- [ _ ; _ ⊢[ _ ] _ @ _ ] => progress wfd
  | |- [ _ ; _ ⊢[ _ ] _ : _ @ _ ] => progress wfd
  end; try assumption.

(** The side conditions: levels, the scrutinees' contexts and typings. *)
Ltac br_side k HΓ :=
  first
  [ solve [cbn; lia]
  | solve [apply lwf_ush; assumption]
  | apply (wf_wkc_br _ _ k ltac:(lia) HΓ)
  | eapply wf_boxT; [ br_side k HΓ | br_side k HΓ | br_side k HΓ | unfold gv, gu; code_side ]
  | eapply wf_boxt; [ br_side k HΓ | br_side k HΓ | br_side k HΓ | unfold gv, gu; code_side | unfold gv, gu; code_side ]
  | unfold gv, gu; code_side ].

Section Adm.
Context {G : gctx} {Γ : ctx} (HΓ : [ G ; Γ ⊢[ lM ] ]) {l1 l2 : lvl} (Hl1 : lwf (gL G) l1) (Hl2 : lwf (gL G) l2)
  {MT Mt : ty} (HMT : [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ])
  (HMt : [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ]).

Lemma brΓ_wf k : k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ].
Proof.
  intros Hk. pose proof (wf_brG (ctx_glob _ _ _ HΓ) k Hk) as HG'.
  br_all ltac:(try (destruct k as [|k])). all: try (exfalso; lia).
  all: unfold brΓ; cbn [brLocs cexts mkLocs call_ty call_lv br_calls br_nu br_ng br_ar].
  all: match goal with |- [ brG ?kk _ ; _ ⊢[ _ ] ] => br_ctx kk HΓ HMT HMt; br_side kk HΓ end.
Qed.

Lemma brRes_wf k : k < nbr ->
  [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ].
Proof.
  intros Hk. pose proof (wf_brG (ctx_glob _ _ _ HΓ) k Hk) as HG'.
  br_all ltac:(try (destruct k as [|k])). all: try (exfalso; lia).
  all: unfold brΓ, brLv; cbn [brLocs cexts brRes br_isT mkLocs call_ty call_lv br_calls br_nu br_ng br_ar br_head br_nl].
  all: match goal with |- [ brG ?kk _ ; _ ⊢[ _ ] _ @ _ ] => br_inst kk HΓ HMT HMt; br_side kk HΓ end.
Qed.

End Adm.

(** ** The recursor rules without the scope premises (paper form, 04:1127) *)

Lemma wf_elimT_adm {G Γ l1 l2 MT Mt bs l Δ t} :
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
  [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : motT (wrapMT MT) l Δ t @ l1 ].
Proof.
  intros Hl1 Hl2 Hl HΔ HMT HMt Hb Ht. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  apply wf_elimT; try assumption.
  - exact (motT_wf _ _ _ _ _ _ _ HMT Hl HΔ Ht).
  - intros k Hk; exact (brΓ_wf HΓ Hl1 Hl2 HMT HMt k Hk).
Qed.

Lemma wf_elimt_adm {G Γ l1 l2 MT Mt bs l Δ T t} :
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t : mott (wrapMt Mt) l Δ T t @ l2 ].
Proof.
  intros Hl1 Hl2 Hl HΔ HMT HMt Hb HT Ht. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  apply wf_elimt; try assumption.
  - exact (mott_wf _ _ _ _ _ _ _ _ HMt Hl HΔ HT Ht).
  - intros k Hk; exact (brΓ_wf HΓ Hl1 Hl2 HMT HMt k Hk).
Qed.
