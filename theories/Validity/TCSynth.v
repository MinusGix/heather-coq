(** * Decidable type checking: synthesis (M7_DESIGN.md C1, J3.5)

    One step of the induction on size: whether a synthesizing term has a
    type. Annotated heads: their premises are decided in order, each at a
    type the earlier ones make well formed. The applications of the
    meta-level functions: the function's type (unique, [type_uniq]) is
    normalized, and its head must be the matching former, whose
    components give the result. *)
From DeLaM.Validity Require Export TCType.

Section Step.
Context (n : nat) (IH : IHsz n).

Let ihT T : sz_ty T < n -> TYD T := proj1 IH T.
Let ihC t : sz_tm t < n -> CKD t := proj1 (proj2 IH) t.
Let ihS t : sz_tm t < n -> synth t -> SYD t := proj1 (proj2 (proj2 IH)) t.
Let ihX Γ : sz_ctx Γ < n -> CXD Γ := proj2 (proj2 (proj2 IH)) Γ.

Ltac szl := cbn [sz_ty sz_tm sz_ctx sz_l] in *; lia.

Ltac notV := match goal with |- _ \/ forall T k, ~ wf_tm _ ?i _ _ _ _ =>
  let Hv := fresh "Hv" in
  destruct (layer_eq_dec i lV) as [-> | Hv]; [right; intros ? ? ?H; eapply typed_V; [| exact H]; cbn; tauto |] end.
Ltac atM := match goal with |- _ \/ forall T k, ~ wf_tm _ ?i _ _ _ _ =>
  let NM := fresh "NM" in
  destruct (layer_eq_dec i lM) as [-> | NM]; [| right; intros ? ? ?H; exact (NM (typed_m_only H I))] end.

Lemma ctx_idem {G i Γ} : [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ typeof (typeof i) ] ].
Proof. rewrite typeof_idem; exact (fun H => H). Qed.

Lemma sy_var m : SYD (var m).
Proof.
  intros G i Γ HΓ. destruct (in_ctx_dec Γ m) as [(T & l & Hin) | N].
  - left; exists T, l; exact (wf_var _ _ _ _ _ _ HΓ Hin).
  - right; intros T k H; destruct (inva_var H) as (T0 & l0 & (_ & Hin) & _); exact (N _ _ Hin).
Qed.

Lemma sy_junk t : junk t -> SYD t.
Proof. intros Hj G i Γ _. right; intros T k H; exact (no_junk H Hj). Qed.

Lemma sy_nat : SYD tmNat.
Proof. intros G i Γ HΓ. notV. left; eexists; eexists; exact (wf_code_nat _ _ _ Hv HΓ). Qed.

Lemma sy_zero : SYD zero.
Proof. intros G i Γ HΓ. notV. left; eexists; eexists; exact (wf_zero _ _ _ Hv HΓ). Qed.

Lemma sy_U l : SYD (tmU l).
Proof.
  intros G i Γ HΓ. notV.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_code_U H) as ((_ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_U _ _ _ _ Hv HΓ Hl).
Qed.

(** The unit type (M8c): the code and [⟨⟩], at every layer but V (M8d). *)
Lemma sy_code_unit l : SYD (tmUnit l).
Proof.
  intros G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_code_unit H) as ((_ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_unit _ _ _ _ Hc HΓ Hl).
Qed.

Lemma sy_code_sempty l : SYD (tmSEmpty l).
Proof.
  intros G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_code_sempty H) as ((_ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_sempty _ _ _ _ Hc HΓ Hl).
Qed.

Lemma sy_triv l : SYD (tmTriv l).
Proof.
  intros G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_triv H) as ((_ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_triv _ _ _ _ Hc HΓ Hl).
Qed.

Lemma HNat {G i Γ} : [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ typeof i ] tyNat @ lzero ].
Proof. intros HΓ; exact (wft_nat _ _ _ (typeof_notV i) (ctx_idem HΓ)). Qed.
Lemma HUniv {G i Γ l} : [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ typeof i ] tyU l @ lsuc l ].
Proof. intros HΓ Hl; exact (wft_U _ _ _ _ (typeof_notV i) (ctx_idem HΓ) Hl). Qed.

Lemma sy_succ t : sz_tm (succ t) <= n -> SYD (succ t).
Proof.
  intros Hsz G i Γ HΓ. notV.
  destruct (ihC t ltac:(szl) G i Γ _ _ (HNat HΓ)) as [Ht | N];
    [| right; intros T k H; destruct (inva_succ H) as ((_ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_succ _ _ _ _ Hv Ht).
Qed.

Lemma sy_codepi l l' s t : sz_tm (tmPi l l' s t) <= n -> SYD (tmPi l l' s t).
Proof.
  intros Hsz G i Γ HΓ. notV.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_code_pi H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros T k H; destruct (inva_code_pi H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihC s ltac:(szl) G i Γ _ _ (HUniv HΓ Hl)) as [Hs | N];
    [| right; intros T k H; destruct (inva_code_pi H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓs : [ G ; Γ ,, tyEl l s @ l ⊢[ typeof i ] ]).
  { apply wfc_ext; [exact HΓ | | exact Hl]. exact (wft_El _ _ _ _ _ (typeof_notV i) Hl (lift_to_typeof_tm Hs)). }
  destruct (ihC t ltac:(szl) G i _ _ _ (HUniv HΓs Hl')) as [Ht | N];
    [| right; intros T k H; destruct (inva_code_pi H) as ((_ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_pi _ _ _ _ _ _ _ Hv Hl Hl' Hs Ht).
Qed.

Lemma sy_natrec l M s z t : sz_tm (natrec l M s z t) <= n -> SYD (natrec l M s z t).
Proof.
  intros Hsz G i Γ HΓ. notV.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_natrec H) as ((_ & X & _) & _); contradiction].
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (HNat HΓ) | exact I]).
  destruct (ihT M ltac:(szl) G i _ l HΓN) as [HM | N];
    [| right; intros T k H; destruct (inva_natrec H) as ((_ & _ & X & _) & _); contradiction].
  pose proof (lift_to_typeof_ty HM) as HM'.
  pose proof (wf_ty_single (i := typeof i) (typeof_idem i) HM' (wf_zero _ _ _ (typeof_notV i) (ctx_idem HΓ))) as HMz.
  destruct (ihC s ltac:(szl) G i Γ _ _ HMz) as [Hs | N];
    [| right; intros T k H; destruct (inva_natrec H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓNM : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ typeof i ] ]) by (apply wfc_ext; assumption).
  pose proof (wf_ty_subst (typeof_idem i) HM' (lsub_wf_lsucc (typeof_idem i) (typeof_notV i) HΓNM)) as HMs.
  destruct (ihC z ltac:(szl) G i _ _ _ HMs) as [Hz | N];
    [| right; intros T k H; destruct (inva_natrec H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC t ltac:(szl) G i Γ _ _ (HNat HΓ)) as [Ht | N];
    [| right; intros T k H; destruct (inva_natrec H) as ((_ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_natrec _ _ _ _ _ _ _ _ Hv Hl HM Hs Hz Ht).
Qed.

Lemma sy_app t l l' A B s : sz_tm (app t l l' A B s) <= n -> SYD (app t l l' A B s).
Proof.
  intros Hsz G i Γ HΓ. notV.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_app H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros T k H; destruct (inva_app H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_app H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B ltac:(szl) G i _ l' HΓA) as [HB | N];
    [| right; intros T k H; destruct (inva_app H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  pose proof (wft_pi _ _ _ _ _ _ _ (typeof_notV i) Hl Hl' (lift_to_typeof_ty HA) (lift_to_typeof_ty HB)) as HP.
  destruct (ihC t ltac:(szl) G i Γ _ _ HP) as [Ht | N];
    [| right; intros T k H; destruct (inva_app H) as ((_ & _ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC s ltac:(szl) G i Γ _ _ (lift_to_typeof_ty HA)) as [Hs | N];
    [| right; intros T k H; destruct (inva_app H) as ((_ & _ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_app _ _ _ _ _ _ _ _ _ Hv Hl Hl' HA HB Ht Hs).
Qed.

Lemma sy_gvar u d : sz_tm (gvar u d) <= n -> SYD (gvar u d).
Proof.
  intros Hsz G i Γ HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (in_gctx_dec (gΨ G) u) as [(D & Hin) | N];
    [| right; intros T k H; destruct (inva_gvar H) as (? & ? & ? & ? & (_ & X & _) & _); exact (N _ X)].
  destruct D as [| Δ i' l0 | Δ i' T0 l0 | Δd Td ld td];
    try (right; intros T k H; destruct (inva_gvar H) as (? & ? & ? & ? & (_ & X & _) & _);
         discriminate (in_gctx_det Hin X)).
  destruct (gctx_decl_ok _ _ _ HG Hin) as (HΔ & _ & _).
  assert (Inv : forall T k, [ G ; Γ ⊢[ i ] gvar u d : T @ k ] ->
    lle i' i /\ lsub_tail d Δ Γ /\ dnfl d /\
    (forall m A k1, in_ctx Δ m A k1 -> [ G ; Γ ⊢[ i ] llk d m : A[d] @ k1 ])).
  { intros T k H. destruct (inva_gvar H) as (Δ' & i'' & T0' & l0' & (_ & X & Hle & Ht & Hd & He) & _).
    pose proof (in_gctx_det Hin X) as E. injection E as <- <- <- <-. tauto. }
  destruct (lle_dec i' i) as [Hle | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lsub_tail_dec d Δ Γ) as [Ht | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (dnfl_dec d) as [Hd | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (sub_dec Δ d HΓ HΔ Ht Hd
              (fun m A k1 HA => ihC (llk d m) ltac:(pose proof (sz_llk d m); szl) G i Γ A k1 HA))
    as [He | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists; exact (wf_gvar _ _ _ _ _ _ _ _ _ HΓ Hin Hle Ht Hd He).
Qed.

(** A defined global (M9): [gvar]'s premises, the carried body level
    equivalent to the declared one, and the body checked at the use layer. *)
Lemma sy_gdef u b d : sz_tm (gdef u b d) <= n -> SYD (gdef u b d).
Proof.
  intros Hsz G i Γ HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (in_gctx_dec (gΨ G) u) as [(D & Hin) | N];
    [| right; intros T k H; destruct (inva_gdef H) as (? & ? & ? & ? & (_ & X & _) & _); exact (N _ X)].
  destruct D as [| Δy iy ly | Δm im Tm lm | Δ T0 l0 t0];
    try (right; intros T k H; destruct (inva_gdef H) as (? & ? & ? & ? & (_ & X & _) & _);
         discriminate (in_gctx_det Hin X)).
  destruct (gctx_decl_ok _ _ _ HG Hin) as (HΔ & HT0 & _ & _).
  assert (Inv : forall T k, [ G ; Γ ⊢[ i ] gdef u b d : T @ k ] ->
    tm_leq t0 b /\ lle lC i /\ lsub_tail d Δ Γ /\ dnfl d /\
    (forall m A k1, in_ctx Δ m A k1 -> [ G ; Γ ⊢[ i ] llk d m : A[d] @ k1 ]) /\
    [ G ; Δ ⊢[ i ] b : T0 @ l0 ]).
  { intros T k H. destruct (inva_gdef H) as (Δ' & T0' & l0' & t0' & (_ & X & Hl & Hle & Ht & Hd & He & Hb) & _).
    pose proof (in_gctx_det Hin X) as E. injection E as <- <- <- <-. tauto. }
  destruct (tm_leq_dec t0 b) as [Hl | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lle_dec lC i) as [Hle | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lsub_tail_dec d Δ Γ) as [Ht | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (dnfl_dec d) as [Hd | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (sub_dec Δ d HΓ HΔ Ht Hd
              (fun m A k1 HA => ihC (llk d m) ltac:(pose proof (sz_llk d m); szl) G i Γ A k1 HA))
    as [He | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihC b ltac:(szl) G i Δ T0 l0 (lift_ty HT0 (lle_D_compt _ (compt_typeof i)))) as [Hb | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists; exact (wf_gdef _ _ _ _ _ _ _ _ _ _ HΓ Hin Hl Hle Ht Hd He Hb).
Qed.

Lemma sy_letboxT l' l Δ M t' t : sz_tm (letboxT l' l Δ M t' t) <= n ->
  SYD (letboxT l' l Δ M t' t).
Proof.
  intros Hsz G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  Ltac inv_lbT X := let H := fresh "H" in intros ? ? H; destruct (inv_letboxT eq_refl H) as (X & _).
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; inv_lbT X; destruct X as (_ & X & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; inv_lbT X; destruct X as (_ & _ & X & _); contradiction].
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; inv_lbT X; destruct X as (_ & _ & _ & X & _); contradiction].
  pose proof (wft_CTyp _ _ _ _ HΓ HΔ Hl) as HC.
  assert (HΓC : [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  destruct (ihT M ltac:(szl) G lM _ l' HΓC) as [HM | N]; [| right; inv_lbT X; destruct X as (_ & _ & _ & _ & X & _); contradiction].
  destruct (ihC t' ltac:(szl) _ lM _ _ _ (letboxT_body_wf HΔ Hl HM)) as [Ht' | N];
    [| right; inv_lbT X; destruct X as (_ & _ & _ & _ & _ & X & _); contradiction].
  destruct (ihC t ltac:(szl) G lM Γ _ _ HC) as [Ht | N]; [| right; inv_lbT X; destruct X as (_ & _ & _ & _ & _ & _ & X); contradiction].
  left; eexists; eexists; exact (wf_letboxT _ _ _ _ _ _ _ _ Hl' Hl HΔ HM Ht' Ht).
Qed.

Lemma sy_letboxt l' l Δ A M t' t : sz_tm (letboxt l' l Δ A M t' t) <= n ->
  SYD (letboxt l' l Δ A M t' t).
Proof.
  intros Hsz G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  Ltac inv_lbt X := let H := fresh "H" in intros ? ? H; destruct (inv_letboxt eq_refl H) as (X & _).
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; inv_lbt X; destruct X as (_ & X & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; inv_lbt X; destruct X as (_ & _ & X & _); contradiction].
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; inv_lbt X; destruct X as (_ & _ & _ & X & _); contradiction].
  destruct (ihT A ltac:(szl) G lD Δ l HΔ) as [HA | N]; [| right; inv_lbt X; destruct X as (_ & _ & _ & _ & X & _); contradiction].
  pose proof (wft_CTrm _ _ _ _ _ HΓ HΔ HA Hl) as HC.
  assert (HΓC : [ G ; Γ ,, tyCTrm Δ A l @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  destruct (ihT M ltac:(szl) G lM _ l' HΓC) as [HM | N]; [| right; inv_lbt X; destruct X as (_ & _ & _ & _ & _ & X & _); contradiction].
  destruct (ihC t' ltac:(szl) _ lM _ _ _ (letboxt_body_wf HA Hl HM)) as [Ht' | N];
    [| right; inv_lbt X; destruct X as (_ & _ & _ & _ & _ & _ & X & _); contradiction].
  destruct (ihC t ltac:(szl) G lM Γ _ _ HC) as [Ht | N]; [| right; inv_lbt X; destruct X as (_ & _ & _ & _ & _ & _ & _ & X); contradiction].
  left; eexists; eexists; exact (wf_letboxt _ _ _ _ _ _ _ _ _ Hl' Hl HΔ HA HM Ht' Ht).
Qed.

(** ** The recursors *)

Lemma sy_elimT l1 l2 rb l Δ t : sz_tm (elimT l1 l2 rb l Δ t) <= n ->
  SYD (elimT l1 l2 rb l Δ t).
Proof.
  intros Hsz G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (rb_view rb) as [(MT & Mt & bs & ->) | N];
    [| right; intros T k H; destruct (inv_elimT eq_refl H) as (MT & Mt & bs & (E & _) & _); exact (N _ _ _ E)].
  pose proof (sz_mkrb MT Mt bs) as (SMT & SMt & Sbs).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : T @ k ] ->
    lwf (gL G) l1 /\ lwf (gL G) l2 /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] /\ [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] /\
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) /\
    [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ]).
  { intros T k H. destruct (inv_elimT eq_refl H) as (MT' & Mt' & bs' & (E & _ & _ & H1 & H2 & H3 & HΔ & HM1 & HM2 & _ & Hb & Ht) & _).
    destruct (mkrb_inj_MT E) as [<- <-]. pose proof (mkrb_inj_br E) as Eb.
    repeat split; try assumption. intros k0 Hk0. rewrite (Eb k0 Hk0). exact (Hb k0 Hk0). }
  destruct (lwf_Dec (gL G) l1) as [Hl1 | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lwf_Dec (gL G) l2) as [Hl2 | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT MT ltac:(szl) (recGT G) lM (recΓT Γ) (lvren l1 (ush 1)) (wf_recΓT _ _ HΓ)) as [HMT | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT Mt ltac:(szl) (recGt G) lM (recΓt Γ) (lvren l2 (ush 1)) (wf_recΓt _ _ HΓ)) as [HMt | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (dec_forall_lt' (fun k => [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) nbr
              (fun k Hk => ihC (bs k) ltac:(specialize (Sbs k Hk); szl) (brG k G) lM _ _ _
                             (brRes_wf HΓ Hl1 Hl2 HMT HMt k Hk))) as [Hb | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihC t ltac:(szl) G lM Γ _ _ (wft_CTyp _ _ _ _ HΓ HΔ Hl)) as [Ht | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists; exact (wf_elimT_adm Hl1 Hl2 Hl HΔ HMT HMt Hb Ht).
Qed.

Lemma sy_elimt l1 l2 rb l Δ A t : sz_tm (elimt l1 l2 rb l Δ A t) <= n ->
  SYD (elimt l1 l2 rb l Δ A t).
Proof.
  intros Hsz G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (rb_view rb) as [(MT & Mt & bs & ->) | N];
    [| right; intros T k H; destruct (inv_elimt eq_refl H) as (MT & Mt & bs & (E & _) & _); exact (N _ _ _ E)].
  pose proof (sz_mkrb MT Mt bs) as (SMT & SMt & Sbs).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ A t : T @ k ] ->
    lwf (gL G) l1 /\ lwf (gL G) l2 /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] /\ [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] /\
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) /\
    [ G ; Δ ⊢[ lD ] A @ l ] /\ [ G ; Γ ⊢[ lM ] t : tyCTrm Δ A l @ lzero ]).
  { intros T k H.
    destruct (inv_elimt eq_refl H) as (MT' & Mt' & bs' & (E & _ & _ & H1 & H2 & H3 & HΔ & HM1 & HM2 & _ & Hb & HA & Ht) & _).
    destruct (mkrb_inj_MT E) as [<- <-]. pose proof (mkrb_inj_br E) as Eb.
    repeat split; try assumption. intros k0 Hk0. rewrite (Eb k0 Hk0). exact (Hb k0 Hk0). }
  destruct (lwf_Dec (gL G) l1) as [Hl1 | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lwf_Dec (gL G) l2) as [Hl2 | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT MT ltac:(szl) (recGT G) lM (recΓT Γ) (lvren l1 (ush 1)) (wf_recΓT _ _ HΓ)) as [HMT | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT Mt ltac:(szl) (recGt G) lM (recΓt Γ) (lvren l2 (ush 1)) (wf_recΓt _ _ HΓ)) as [HMt | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (dec_forall_lt' (fun k => [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) nbr
              (fun k Hk => ihC (bs k) ltac:(specialize (Sbs k Hk); szl) (brG k G) lM _ _ _
                             (brRes_wf HΓ Hl1 Hl2 HMT HMt k Hk))) as [Hb | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT A ltac:(szl) G lD Δ l HΔ) as [HA | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihC t ltac:(szl) G lM Γ _ _ (wft_CTrm _ _ _ _ _ HΓ HΔ HA Hl)) as [Ht | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists; exact (wf_elimt_adm Hl1 Hl2 Hl HΔ HMT HMt Hb HA Ht).
Qed.

(** ** The abstractions, by their annotations (C1b) *)

Lemma sy_ulam m l T b : sz_tm (ulam m l T b) <= n -> SYD (ulam m l T b).
Proof.
  intros Hsz G i Γ HΓ. atM.
  Ltac inv_ul X := let H := fresh "H" in intros ? ? H; destruct (inv_ulam eq_refl H) as (X & _).
  destruct (lt_dec 0 m) as [Hm | N]; [| right; inv_ul X; destruct X as (_ & _ & X & _); contradiction].
  destruct (lwf_Dec (m + gL G) l) as [Hl | N]; [| right; inv_ul X; destruct X as (_ & _ & _ & X & _); contradiction].
  destruct (ihT T ltac:(szl) (gctx_uwk m G) lM (Γ⟨ush m⟩ᵤ) l (uwk_ctx m HΓ)) as [HT | N];
    [| right; inv_ul X; destruct X as (_ & _ & _ & _ & X & _); contradiction].
  destruct (ihC b ltac:(szl) (gctx_uwk m G) lM (Γ⟨ush m⟩ᵤ) T l HT) as [Hb | N];
    [| right; inv_ul X; destruct X as (_ & _ & _ & _ & _ & X); contradiction].
  left; eexists; eexists; exact (wf_ulam _ _ _ _ _ _ HΓ Hm Hl HT Hb).
Qed.

Lemma sy_clam l T b : sz_tm (clam l T b) <= n -> SYD (clam l T b).
Proof.
  intros Hsz G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  Ltac inv_cl X := let H := fresh "H" in intros ? ? H; destruct (inv_clam eq_refl H) as (X & _).
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; inv_cl X; destruct X as (_ & _ & X & _); contradiction].
  pose proof (ctx_S (wfg_ctx' HG) HΓ) as HΓ1.
  destruct (ihT T ltac:(szl) (gext G gdCtx) lM Γ⟪S⟫ l HΓ1) as [HT | N];
    [| right; inv_cl X; destruct X as (_ & _ & _ & X & _); contradiction].
  destruct (ihC b ltac:(szl) (gext G gdCtx) lM Γ⟪S⟫ T l HT) as [Hb | N];
    [| right; inv_cl X; destruct X as (_ & _ & _ & _ & X); contradiction].
  left; eexists; eexists; exact (wf_clam _ _ _ _ _ HΓ Hl HT Hb).
Qed.

Lemma sy_tlam Δ l l' T b : sz_tm (tlam Δ l l' T b) <= n -> SYD (tlam Δ l l' T b).
Proof.
  intros Hsz G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  Ltac inv_tl X := let H := fresh "H" in intros ? ? H; destruct (inv_tlam eq_refl H) as (X & _).
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; inv_tl X; destruct X as (_ & _ & X & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; inv_tl X; destruct X as (_ & _ & _ & X & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; inv_tl X; destruct X as (_ & _ & _ & _ & X & _); contradiction].
  pose proof (ctx_S (wfg_ty' HΔ (or_intror eq_refl) Hl) HΓ) as HΓ1.
  destruct (ihT T ltac:(szl) _ lM Γ⟪S⟫ l' HΓ1) as [HT | N];
    [| right; inv_tl X; destruct X as (_ & _ & _ & _ & _ & X & _); contradiction].
  destruct (ihC b ltac:(szl) _ lM Γ⟪S⟫ T l' HT) as [Hb | N];
    [| right; inv_tl X; destruct X as (_ & _ & _ & _ & _ & _ & X); contradiction].
  left; eexists; eexists; exact (wf_tlam _ _ _ _ _ _ _ HΓ HΔ Hl Hl' HT Hb).
Qed.

(** ** The applications of the meta-level functions *)

(** A checked function of another former is untyped at this one. *)
Lemma sy_uapp f ls : sz_tm (uapp f ls) <= n -> SYD (uapp f ls).
Proof.
  intros Hsz G i Γ HΓ. atM.
  destruct (synth_dec f) as [Hs | Hs];
    [| right; intros T k H; destruct (inv_uapp eq_refl H) as (m & l & T0 & (_ & _ & _ & _ & _ & Ht) & _);
       pose proof (chk_at_whnf Hs Ht (whnf_tyUPi _ _ _)) as Eh; clear H;
       destruct f; cbn in Eh, Hs; first [discriminate Eh | exact (Hs I)]].
  destruct (ihS f ltac:(szl) Hs G lM Γ HΓ) as [(F & kf & Hf) | N];
    [| right; intros T k H; destruct (inv_uapp eq_refl H) as (m & l & T0 & (_ & _ & _ & _ & _ & Ht) & _); exact (N _ _ Ht)].
  pose proof (wf_tm_ty (i := lM) eq_refl Hf) as HF.
  destruct (whnf_normalization_ty_c compt_M HF) as (W & _ & Hw & EW).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] uapp f ls : T @ k ] -> exists m l T0,
    [ G ; Γ ⊢[ lM ] W ≅ tyUPi m l T0 @ kf ] /\ length ls = m /\ Forall (lwf (gL G)) ls).
  { intros T k H. destruct (inv_uapp eq_refl H) as (m & l & T0 & (_ & _ & _ & Hlen & Hls & Ht) & _).
    destruct (type_uniq f Hs _ _ _ _ _ _ _ Hf Ht) as (_ & E).
    exists m, l, T0; split; [| split; assumption].
    eapply eqty_trans; [apply eqty_sym; exact EW | exact E]. }
  destruct (upi_view W) as [(m & l & T0 & ->) | Nh];
    [| right; intros T k H; destruct (Inv _ _ H) as (m & l & T0 & E & _); apply Nh;
       exact (decl_head_c compt_M E Hw (whnf_tyUPi _ _ _))].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW. destruct (inv_ty_upi HW) as ((_ & _ & Hm & Hl & HT0) & Hk).
  destruct (Nat.eq_dec (length ls) m) as [Hlen | N];
    [| right; intros T k H; destruct (Inv _ _ H) as (m' & l' & T0' & E & Hlen & _);
       destruct (upi_inj E) as (Em & _); congruence].
  destruct (Forall_dec (lwf (gL G)) (lwf_dec (gL G)) ls) as [Hls | N];
    [| right; intros T k H; destruct (Inv _ _ H) as (_ & _ & _ & _ & _ & X); contradiction].
  left; eexists; eexists. eapply wf_uapp; [exact Hl | exact HT0 | exact Hlen | exact Hls |].
  exact (wf_lvl (lvl_eq_sym Hk) (wf_conv _ _ _ _ _ _ _ Hf (eqty_sym _ _ _ _ _ _ EW))).
Qed.

Lemma sy_capp f Δ : sz_tm (capp f Δ) <= n -> SYD (capp f Δ).
Proof.
  intros Hsz G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (synth_dec f) as [Hs | Hs];
    [| right; intros T k H; destruct (inv_capp eq_refl H) as (l & T0 & (_ & _ & _ & _ & Ht & _) & _);
       pose proof (chk_at_whnf Hs Ht (whnf_tyCPi _ _)) as Eh; clear H;
       destruct f; cbn in Eh, Hs; first [discriminate Eh | exact (Hs I)]].
  destruct (ihS f ltac:(szl) Hs G lM Γ HΓ) as [(F & kf & Hf) | N];
    [| right; intros T k H; destruct (inv_capp eq_refl H) as (l & T0 & (_ & _ & _ & _ & Ht & _) & _); exact (N _ _ Ht)].
  pose proof (wf_tm_ty (i := lM) eq_refl Hf) as HF.
  destruct (whnf_normalization_ty_c compt_M HF) as (W & _ & Hw & EW).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] capp f Δ : T @ k ] -> [ G ; Δ ⊢[ lD ] ] /\ exists l T0,
    [ G ; Γ ⊢[ lM ] W ≅ tyCPi l T0 @ kf ]).
  { intros T k H. destruct (inv_capp eq_refl H) as (l & T0 & (_ & _ & _ & HΔ & Ht & _) & _).
    destruct (type_uniq f Hs _ _ _ _ _ _ _ Hf Ht) as (_ & E).
    split; [exact HΔ |]. exists l, T0. eapply eqty_trans; [apply eqty_sym; exact EW | exact E]. }
  destruct (cpi_view W) as [(l & T0 & ->) | Nh];
    [| right; intros T k H; destruct (Inv _ _ H) as (_ & l & T0 & E); apply Nh;
       exact (decl_head_c compt_M E Hw (whnf_tyCPi _ _))].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW. destruct (inv_ty_cpi HW) as ((_ & _ & Hl & HT0) & Hk).
  destruct (ihX Δ ltac:(szl) G lD HG) as [HΔ | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists. eapply wf_capp; [exact Hl | exact HT0 | exact HΔ | | exact (inst_c_ty HΓ HΔ HT0)].
  exact (wf_lvl (lvl_eq_sym Hk) (wf_conv _ _ _ _ _ _ _ Hf (eqty_sym _ _ _ _ _ _ EW))).
Qed.

Lemma sy_tapp f A : sz_tm (tapp f A) <= n -> SYD (tapp f A).
Proof.
  intros Hsz G i Γ HΓ. atM.
  destruct (synth_dec f) as [Hs | Hs];
    [| right; intros T k H; destruct (inv_tapp eq_refl H) as (Δ & l & l' & T0 & (_ & Ht & _) & _);
       pose proof (chk_at_whnf Hs Ht (whnf_tyTPi _ _ _ _)) as Eh; clear H;
       destruct f; cbn in Eh, Hs; first [discriminate Eh | exact (Hs I)]].
  destruct (ihS f ltac:(szl) Hs G lM Γ HΓ) as [(F & kf & Hf) | N];
    [| right; intros T k H; destruct (inv_tapp eq_refl H) as (Δ & l & l' & T0 & (_ & Ht & _) & _); exact (N _ _ Ht)].
  pose proof (wf_tm_ty (i := lM) eq_refl Hf) as HF.
  destruct (whnf_normalization_ty_c compt_M HF) as (W & _ & Hw & EW).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] tapp f A : T @ k ] -> exists Δ l l' T0,
    [ G ; Γ ⊢[ lM ] W ≅ tyTPi Δ l l' T0 @ kf ] /\ [ G ; Δ ⊢[ lD ] A @ l ]).
  { intros T k H. destruct (inv_tapp eq_refl H) as (Δ & l & l' & T0 & (_ & Ht & _ & _ & _ & _ & HA & _) & _).
    destruct (type_uniq f Hs _ _ _ _ _ _ _ Hf Ht) as (_ & E).
    exists Δ, l, l', T0; split; [| exact HA]. eapply eqty_trans; [apply eqty_sym; exact EW | exact E]. }
  destruct (tpi_view W) as [(Δ & l & l' & T0 & ->) | Nh];
    [| right; intros T k H; destruct (Inv _ _ H) as (Δ & l & l' & T0 & E & _); apply Nh;
       exact (decl_head_c compt_M E Hw (whnf_tyTPi _ _ _ _))].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW.
  destruct (inv_ty_tpi HW) as ((_ & _ & HΔ & Hl & Hl' & HT0) & Hk).
  destruct (ihT A ltac:(szl) G lD Δ l HΔ) as [HA | N].
  - left; eexists; eexists. eapply wf_tapp; [| exact HΔ | exact Hl | exact Hl' | exact HT0 | exact HA |
                                           exact (inst_t_ty HΓ HA HT0)].
    exact (wf_lvl (lvl_eq_sym Hk) (wf_conv _ _ _ _ _ _ _ Hf (eqty_sym _ _ _ _ _ _ EW))).
  - right; intros T k H. destruct (Inv _ _ H) as (Δ' & l1 & l2 & T0' & E & HA').
    destruct (tpi_inj E) as (Q1 & _ & EΔ & _). apply N.
    exact (wft_lconv _ _ _ _ _ _ (ctxconv_ty (eqctx_sym_D EΔ) (i := lD) eq_refl HA') Q1).
Qed.

(** ** Dependent pairs (M8): at every layer but V (M8d) *)

Lemma sy_codesig l l' s t : sz_tm (tmSig l l' s t) <= n -> SYD (tmSig l l' s t).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_code_sig H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros T k H; destruct (inva_code_sig H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihC s ltac:(szl) G i Γ _ _ (HUniv HΓ Hl)) as [Hs | N];
    [| right; intros T k H; destruct (inva_code_sig H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓs : [ G ; Γ ,, tyEl l s @ l ⊢[ typeof i ] ]).
  { apply wfc_ext; [exact HΓ | | exact Hl]. exact (wft_El _ _ _ _ _ (typeof_notV i) Hl (lift_to_typeof_tm Hs)). }
  destruct (ihC t ltac:(szl) G i _ _ _ (HUniv HΓs Hl')) as [Ht | N];
    [| right; intros T k H; destruct (inva_code_sig H) as ((_ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_sig _ _ _ _ _ _ _ Hc Hl Hl' Hs Ht).
Qed.

(** The identity type's code (M11b): every layer but V. *)
Lemma sy_code_id l s t u : sz_tm (tmId l s t u) <= n -> SYD (tmId l s t u).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_code_id H) as ((_ & X & _) & _); contradiction].
  destruct (ihC s ltac:(szl) G i Γ _ _ (HUniv HΓ Hl)) as [Hs | N];
    [| right; intros T k H; destruct (inva_code_id H) as ((_ & _ & X & _) & _); contradiction].
  pose proof (wft_El _ _ _ _ _ (typeof_notV i) Hl (lift_to_typeof_tm Hs)) as HEl.
  destruct (ihC t ltac:(szl) G i Γ _ _ HEl) as [Ht | N];
    [| right; intros T k H; destruct (inva_code_id H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihC u ltac:(szl) G i Γ _ _ HEl) as [Hu | N];
    [| right; intros T k H; destruct (inva_code_id H) as ((_ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_id _ _ _ _ _ _ _ Hc Hl Hs Ht Hu).
Qed.

(** Strict equality's codes (M10c; every layer but V). *)
Lemma sy_code_seq l s t u : sz_tm (tmSEq l s t u) <= n -> SYD (tmSEq l s t u).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_code_seq H) as ((_ & X & _) & _); contradiction].
  destruct (ihC s ltac:(szl) G i Γ _ _ (HUniv HΓ Hl)) as [Hs | N];
    [| right; intros T k H; destruct (inva_code_seq H) as ((_ & _ & X & _) & _); contradiction].
  pose proof (wft_El _ _ _ _ _ (typeof_notV i) Hl (lift_to_typeof_tm Hs)) as HEl.
  destruct (ihC t ltac:(szl) G i Γ _ _ HEl) as [Ht | N];
    [| right; intros T k H; destruct (inva_code_seq H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihC u ltac:(szl) G i Γ _ _ HEl) as [Hu | N];
    [| right; intros T k H; destruct (inva_code_seq H) as ((_ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_seq _ _ _ _ _ _ _ Hc Hl Hs Ht Hu).
Qed.

(** The annotations of a pair or a projection, decided in order. *)
Lemma sy_sig_annot {G i Γ l l' A B} (P : Prop) :
  sz_ty A < n -> sz_ty B < n -> [ G ; Γ ⊢[ typeof i ] ] ->
  (P -> lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ]) ->
  (lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ]) \/ ~ P.
Proof.
  intros HzA HzB HΓ Inv.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros H; apply N, (Inv H)].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros H; apply N, (Inv H)].
  destruct (ihT A HzA G i Γ l HΓ) as [HA | N]; [| right; intros H; apply N, (Inv H)].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B HzB G i _ l' HΓA) as [HB | N]; [| right; intros H; apply N, (Inv H)].
  left; auto.
Qed.

Lemma sy_pair l l' A B a b : sz_tm (tmPair l l' A B a b) <= n -> SYD (tmPair l l' A B a b).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (sy_sig_annot (l := l) (l' := l') (A := A) (B := B)
              (exists T k, [ G ; Γ ⊢[ i ] tmPair l l' A B a b : T @ k ]) ltac:(szl) ltac:(szl) HΓ)
    as [(Hl & Hl' & HA & HB) | N];
    [ intros (T & k & H); destruct (inva_pair H) as ((_ & ? & ? & ? & ? & _) & _); auto
    | | right; intros T k H; apply N; eauto ].
  destruct (ihC a ltac:(szl) G i Γ _ _ (lift_to_typeof_ty HA)) as [Ha | N];
    [| right; intros T k H; destruct (inva_pair H) as ((_ & _ & _ & _ & _ & X & _) & _); contradiction].
  pose proof (wf_ty_single (i := typeof i) (typeof_idem i) (lift_to_typeof_ty HB) (lift_to_typeof_tm Ha)) as HBa.
  destruct (ihC b ltac:(szl) G i Γ _ _ HBa) as [Hb | N];
    [| right; intros T k H; destruct (inva_pair H) as ((_ & _ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_pair _ _ _ _ _ _ _ _ _ Hc Hl Hl' HA HB Ha Hb).
Qed.

Lemma sy_proj (fs : bool) l l' A B p :
  sz_tm (if fs then tmFst l l' A B p else tmSnd l l' A B p) <= n ->
  SYD (if fs then tmFst l l' A B p else tmSnd l l' A B p).
Proof.
  intros Hsz G i Γ HΓ.
  assert (Inv : forall T k, [ G ; Γ ⊢[ i ] (if fs then tmFst l l' A B p else tmSnd l l' A B p) : T @ k ] ->
    i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ]).
  { intros T k H; destruct fs; [exact (proj1 (inva_fst H)) | exact (proj1 (inva_snd H))]. }
  assert (Hz : sz_ty A < n /\ sz_ty B < n /\ sz_tm p < n) by (destruct fs; cbn [sz_tm] in Hsz; lia).
  destruct Hz as (HzA & HzB & Hzp).
  destruct (layer_eq_dec i lV) as [-> | Hc]; [right; intros T k H; apply (proj1 (Inv _ _ H)); reflexivity |].
  destruct (sy_sig_annot (l := l) (l' := l')
              (exists T k, [ G ; Γ ⊢[ i ] (if fs then tmFst l l' A B p else tmSnd l l' A B p) : T @ k ])
              HzA HzB HΓ) as [(Hl & Hl' & HA & HB) | N];
    [ intros (T & k & H); destruct (Inv _ _ H) as (_ & ? & ? & ? & ? & _); auto
    | | right; intros T k H; apply N; eauto ].
  pose proof (wft_sig _ _ _ _ _ _ _ (typeof_notV i) Hl Hl' (lift_to_typeof_ty HA) (lift_to_typeof_ty HB)) as HS.
  destruct (ihC p Hzp G i Γ _ _ HS) as [Hp | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  left; destruct fs; eexists; eexists; [exact (wf_fst _ _ _ _ _ _ _ _ Hc Hl Hl' HA HB Hp) |
                                        exact (wf_snd _ _ _ _ _ _ _ _ Hc Hl Hl' HA HB Hp)].
Qed.

(** Strict equality (M10a; every layer but V since M10c). *)
Lemma sy_srefl l A a : sz_tm (srefl l A a) <= n -> SYD (srefl l A a).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_srefl H) as ((_ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_srefl H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihC a ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Ha | N];
    [| right; intros T k H; destruct (inva_srefl H) as ((_ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_srefl _ _ _ _ _ _ Hc Hl HA Ha).
Qed.

Lemma sy_elimSEmpty l l' M e : sz_tm (elimSEmpty l l' M e) <= n -> SYD (elimSEmpty l l' M e).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_elimSEmpty H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros T k H; destruct (inva_elimSEmpty H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT M ltac:(szl) G i Γ l' HΓ) as [HM | N];
    [| right; intros T k H; destruct (inva_elimSEmpty H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HSE : [ G ; Γ ⊢[ typeof i ] tySEmpty l @ l ])
    by exact (wft_sempty _ _ _ _ (typeof_notV i) (ctx_idem HΓ) Hl).
  destruct (ihC e ltac:(szl) G i Γ _ _ HSE) as [He | N];
    [| right; intros T k H; destruct (inva_elimSEmpty H) as ((_ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_elimSEmpty _ _ _ _ _ _ _ Hc Hl Hl' HM He).
Qed.

(** The empty type's eliminator (M12a; every layer but V since M12c). *)
Lemma sy_elimEmpty l l' M t : sz_tm (elimEmpty l l' M t) <= n -> SYD (elimEmpty l l' M t).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_elimEmpty H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros T k H; destruct (inva_elimEmpty H) as ((_ & _ & X & _) & _); contradiction].
  pose proof (wft_empty _ _ _ _ Hc HΓ Hl') as HE.
  assert (HΓE : [ G ; Γ ,, tyEmpty l' @ l' ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HE) | exact Hl']).
  destruct (ihT M ltac:(szl) G i _ l HΓE) as [HM | N];
    [| right; intros T k H; destruct (inva_elimEmpty H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihC t ltac:(szl) G i Γ _ _ (lift_to_typeof_ty HE)) as [Ht | N];
    [| right; intros T k H; destruct (inva_elimEmpty H) as ((_ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_elimEmpty _ _ _ _ _ _ _ Hc Hl Hl' HM Ht).
Qed.

(** The identity type (M11a; every layer but V since M11b). *)
Lemma sy_refl l A a : sz_tm (tmRefl l A a) <= n -> SYD (tmRefl l A a).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_idrefl H) as ((_ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_idrefl H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihC a ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Ha | N];
    [| right; intros T k H; destruct (inva_idrefl H) as ((_ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_idrefl _ _ _ _ _ _ Hc Hl HA Ha).
Qed.

(** [J]: its motive context's [Id] entry is built, not decided. *)
Lemma sy_J l l' A a M c u e : sz_tm (tmJ l l' A a M c u e) <= n -> SYD (tmJ l l' A a M c u e).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  pose proof (typeof_idem i) as Hty.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_J H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros T k H; destruct (inva_J H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_J H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihC a ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Ha | N];
    [| right; intros T k H; destruct (inva_J H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  assert (HI : [ G ; Γ ,, A @ l ⊢[ i ] tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ]).
  { apply wft_id; [exact Hc | exact Hl | apply wk1_ty_g; assumption | apply wk1_tm_g; assumption
                  | apply var0_wf_g; assumption]. }
  assert (HΓAI : [ G ; Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓA | exact (lift_to_typeof_ty HI) | exact Hl]).
  destruct (ihT M ltac:(szl) G i _ l' HΓAI) as [HM | N];
    [| right; intros T k H; destruct (inva_J H) as ((_ & _ & _ & _ & _ & _ & X & _) & _); contradiction].
  assert (Hr : [ G ; Γ ⊢[ i ] tmRefl l A a : tyId l A a a @ l ]) by exact (wf_idrefl _ _ _ _ _ _ Hc Hl HA Ha).
  assert (HMr : [ G ; Γ ⊢[ typeof i ] M[lsingle2 a (tmRefl l A a)] @ l' ]).
  { refine (wf_ty_subst Hty (lift_to_typeof_ty HM) (lsub_wf_J Hty _ _ _)); apply lift_to_typeof_tm; assumption. }
  destruct (ihC c ltac:(szl) G i Γ _ _ HMr) as [Hc' | N];
    [| right; intros T k H; destruct (inva_J H) as ((_ & _ & _ & _ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC u ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Hu | N];
    [| right; intros T k H; destruct (inva_J H) as ((_ & _ & _ & _ & _ & _ & _ & _ & X & _) & _); contradiction].
  assert (HId : [ G ; Γ ⊢[ typeof i ] tyId l A a u @ l ]).
  { apply wft_id; [exact (typeof_notV i) | exact Hl | ..]; apply lift_to_typeof_ty || apply lift_to_typeof_tm;
      assumption. }
  destruct (ihC e ltac:(szl) G i Γ _ _ HId) as [He | N];
    [| right; intros T k H; destruct (inva_J H) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_J _ _ _ _ _ _ _ _ _ _ _ Hc Hl Hl' HA Ha HI HM Hc' Hu He).
Qed.

(** Binary sums (M12b; every layer but V since M12c). *)
Lemma sy_inl l l' A B a : sz_tm (tmInl l l' A B a) <= n -> SYD (tmInl l l' A B a).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_inl H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N];
    [| right; intros T k H; destruct (inva_inl H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_inl H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihT B ltac:(szl) G i Γ l' HΓ) as [HB | N];
    [| right; intros T k H; destruct (inva_inl H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC a ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Ha | N];
    [| right; intros T k H; destruct (inva_inl H) as ((_ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_inl _ _ _ _ _ _ _ _ Hc Hl Hl' HA HB Ha).
Qed.

Lemma sy_inr l l' A B b : sz_tm (tmInr l l' A B b) <= n -> SYD (tmInr l l' A B b).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_inr H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N];
    [| right; intros T k H; destruct (inva_inr H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_inr H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihT B ltac:(szl) G i Γ l' HΓ) as [HB | N];
    [| right; intros T k H; destruct (inva_inr H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC b ltac:(szl) G i Γ B l' (lift_to_typeof_ty HB)) as [Hb | N];
    [| right; intros T k H; destruct (inva_inr H) as ((_ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_inr _ _ _ _ _ _ _ _ Hc Hl Hl' HA HB Hb).
Qed.

(** [case]: its branch types are built from the decided motive. *)
Lemma sy_case l l' l'' A B M c1 c2 t : sz_tm (tmCase l l' l'' A B M c1 c2 t) <= n ->
  SYD (tmCase l l' l'' A B M c1 c2 t).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  pose proof (typeof_idem i) as Hty.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_case H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N];
    [| right; intros T k H; destruct (inva_case H) as ((_ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l'') as [Hl'' | N];
    [| right; intros T k H; destruct (inva_case H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_case H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihT B ltac:(szl) G i Γ l' HΓ) as [HB | N];
    [| right; intros T k H; destruct (inva_case H) as ((_ & _ & _ & _ & _ & X & _) & _); contradiction].
  pose proof (wft_sum _ _ _ _ _ _ _ Hc Hl Hl' HA HB) as HS.
  assert (HΓS : [ G ; Γ ,, tySum l l' A B @ lmax l l' ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HS) | exact (conj Hl Hl')]).
  destruct (ihT M ltac:(szl) G i _ l'' HΓS) as [HM | N];
    [| right; intros T k H; destruct (inva_case H) as ((_ & _ & _ & _ & _ & _ & X & _) & _); contradiction].
  pose proof (lift_to_typeof_ty HM) as HM0.
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  assert (HΓB : [ G ; Γ ,, B @ l' ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HB) | exact Hl']).
  assert (Hf1 : [ G ; Γ ,, A @ l ⊢[ i ] tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0) : (tySum l l' A B)⟨↑⟩ @ lmax l l' ])
    by (apply wf_inl; [exact Hc | exact Hl | exact Hl' | apply wk1_ty_g; assumption | apply wk1_ty_g; assumption
                      | apply var0_wf_g; assumption]).
  assert (Hf2 : [ G ; Γ ,, B @ l' ⊢[ i ] tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0) : (tySum l l' A B)⟨↑⟩ @ lmax l l' ])
    by (apply wf_inr; [exact Hc | exact Hl | exact Hl' | apply wk1_ty_g; assumption | apply wk1_ty_g; assumption
                      | apply var0_wf_g; assumption]).
  pose proof (lift_to_typeof_tm Hf1) as Hf1'. pose proof (lift_to_typeof_tm Hf2) as Hf2'.
  pose proof (eqty_wf_l Hty (case_branch_eq Hty HΓA HM0 (eqty_refl _ _ _ _ _ HM0) HM0 Hf1' Hf1'
                                (eqtm_refl _ _ _ _ _ _ Hf1'))) as Hbr1.
  pose proof (eqty_wf_l Hty (case_branch_eq Hty HΓB HM0 (eqty_refl _ _ _ _ _ HM0) HM0 Hf2' Hf2'
                                (eqtm_refl _ _ _ _ _ _ Hf2'))) as Hbr2.
  destruct (ihC c1 ltac:(szl) G i _ _ _ Hbr1) as [Hc1 | N];
    [| right; intros T k H; destruct (inva_case H) as ((_ & _ & _ & _ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC c2 ltac:(szl) G i _ _ _ Hbr2) as [Hc2 | N];
    [| right; intros T k H; destruct (inva_case H) as ((_ & _ & _ & _ & _ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC t ltac:(szl) G i Γ _ _ (lift_to_typeof_ty HS)) as [Ht | N];
    [| right; intros T k H; destruct (inva_case H) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_case _ _ _ _ _ _ _ _ _ _ _ _ Hc Hl Hl' Hl'' HA HB HM Hc1 Hc2 Ht).
Qed.

(** The codes of [Empty] and [+] (M12c; every layer but V). *)
Lemma sy_code_empty l : SYD (tmEmpty l).
Proof.
  intros G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N];
    [| right; intros T k H; destruct (inva_code_empty H) as ((_ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_empty _ _ _ _ Hc HΓ Hl).
Qed.

Lemma sy_code_sum l l' s t : sz_tm (tmSum l l' s t) <= n -> SYD (tmSum l l' s t).
Proof.
  intros Hsz G i Γ HΓ.
  notV. rename Hv into Hc.
  destruct (lwf_Dec (gL G) l) as [Hl | N];
    [| right; intros T k H; destruct (inva_code_sum H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N];
    [| right; intros T k H; destruct (inva_code_sum H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihC s ltac:(szl) G i Γ _ _ (HUniv HΓ Hl)) as [Hs | N];
    [| right; intros T k H; destruct (inva_code_sum H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihC t ltac:(szl) G i Γ _ _ (HUniv HΓ Hl')) as [Ht | N];
    [| right; intros T k H; destruct (inva_code_sum H) as ((_ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_sum _ _ _ _ _ _ _ Hc Hl Hl' Hs Ht).
Qed.

(** Well-founded trees (M13a): the computing layers only. [sup]'s child
    function is checked at the function type its shape determines. *)
Lemma sy_sup l l' A B a f : sz_tm (tmSup l l' A B a f) <= n -> SYD (tmSup l l' A B a f).
Proof.
  intros Hsz G i Γ HΓ.
  destruct (compt_dec i) as [Hc | N]; [| right; intros T k H; destruct (inva_sup H) as ((X & _) & _); contradiction].
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV Hc) as Hv.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_sup H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N];
    [| right; intros T k H; destruct (inva_sup H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_sup H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B ltac:(szl) G i _ l' HΓA) as [HB | N];
    [| right; intros T k H; destruct (inva_sup H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC a ltac:(szl) G i Γ A l (lift_to_typeof_ty HA)) as [Ha | N];
    [| right; intros T k H; destruct (inva_sup H) as ((_ & _ & _ & _ & _ & X & _) & _); contradiction].
  pose proof (wft_W _ _ _ _ _ _ _ Hc Hl Hl' HA HB) as HW.
  pose proof (wf_ty_single Hi HB Ha) as HBa.
  pose proof (ext_wf Hi HBa Hl') as HΓB.
  pose proof (wft_pi _ _ _ _ _ _ _ Hv Hl' (lwf_max Hl Hl') HBa (wk1_ty _ _ Hi _ _ _ _ _ HΓB HW)) as HF.
  destruct (ihC f ltac:(szl) G i Γ _ _ (lift_to_typeof_ty HF)) as [Hf | N];
    [| right; intros T k H; destruct (inva_sup H) as ((_ & _ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_sup _ _ _ _ _ _ _ _ _ Hc Hl Hl' HA HB Ha Hf).
Qed.

(** [elim_W]: the step telescope and the step type are built from the
    decided shape, positions and motive. *)
Lemma sy_elimW l l' l'' A B M c t : sz_tm (tmElimW l l' l'' A B M c t) <= n ->
  SYD (tmElimW l l' l'' A B M c t).
Proof.
  intros Hsz G i Γ HΓ.
  destruct (compt_dec i) as [Hc | N]; [| right; intros T k H; destruct (inva_elimW H) as ((X & _) & _); contradiction].
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV Hc) as Hv.
  destruct (lwf_Dec (gL G) l) as [Hl | N];
    [| right; intros T k H; destruct (inva_elimW H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N];
    [| right; intros T k H; destruct (inva_elimW H) as ((_ & _ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l'') as [Hl'' | N];
    [| right; intros T k H; destruct (inva_elimW H) as ((_ & _ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_elimW H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B ltac:(szl) G i _ l' HΓA) as [HB | N];
    [| right; intros T k H; destruct (inva_elimW H) as ((_ & _ & _ & _ & _ & X & _) & _); contradiction].
  pose proof (wft_W _ _ _ _ _ _ _ Hc Hl Hl' HA HB) as HW.
  assert (WL : lwf (gL G) (lmax l l')) by exact (lwf_max Hl Hl').
  assert (HΓW : [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HW) | exact WL]).
  destruct (ihT M ltac:(szl) G i _ l'' HΓW) as [HM | N];
    [| right; intros T k H; destruct (inva_elimW H) as ((_ & _ & _ & _ & _ & _ & X & _) & _); contradiction].
  pose proof (W_fty_wf Hi Hv (X := A) (lx := l) Hl Hl' HW HB) as HF.
  pose proof (ext_wf Hi HF (lwf_max Hl' WL)) as HΓAF.
  pose proof (W_ih_wf Hi Hv Hl Hl' Hl'' HW HB HM HΓAF (eqty_refl' HF) (lequiv_refl _ _ (lwf_max Hl' WL))) as HI.
  pose proof (ext_wf Hi HI (lwf_max Hl' Hl'')) as HΓT.
  pose proof (eqty_wf_l Hi (W_step_eq Hi Hv (lequiv_refl _ _ Hl) (lequiv_refl _ _ Hl') (lequiv_refl _ _ Hl'')
                              HA (eqty_refl' HA) HA HB (eqty_refl' HB) HB HM (eqty_refl' HM) (eqty_refl' HW)
                              HF (eqty_refl' HF) HΓT)) as HS.
  destruct (ihC c ltac:(szl) G i _ _ _ (lift_to_typeof_ty HS)) as [Hc0 | N];
    [| right; intros T k H; destruct (inva_elimW H) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _) & _);
       contradiction].
  destruct (ihC t ltac:(szl) G i Γ _ _ (lift_to_typeof_ty HW)) as [Ht | N];
    [| right; intros T k H; destruct (inva_elimW H) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X) & _);
       contradiction].
  left; eexists; eexists; exact (wf_elimW _ _ _ _ _ _ _ _ _ _ _ Hc Hl Hl' Hl'' HA HB HM HF HI Hc0 Ht).
Qed.

(** ** The step *)

Lemma sy_step t : sz_tm t <= n -> synth t -> SYD t.
Proof.
  intros Hsz Hs. destruct t; cbn in Hs; try contradiction;
    first [ apply sy_var | apply sy_nat | apply sy_zero | apply sy_U
          | apply sy_junk; exact I
          | apply sy_succ | apply sy_codepi | apply sy_natrec | apply sy_app | apply sy_gvar | apply sy_gdef
          | apply sy_letboxT | apply sy_letboxt | apply sy_elimT | apply sy_elimt
          | apply sy_ulam | apply sy_clam | apply sy_tlam
          | apply sy_uapp | apply sy_capp | apply sy_tapp
          | apply sy_codesig | apply sy_pair
          | apply (sy_proj true) | apply (sy_proj false) | apply sy_code_unit | apply sy_triv
          | apply sy_srefl | apply sy_elimSEmpty | apply sy_refl | apply sy_J | apply sy_code_id | apply sy_elimEmpty
          | apply sy_code_seq | apply sy_code_sempty | apply sy_inl | apply sy_inr | apply sy_case
          | apply sy_code_empty | apply sy_code_sum | apply sy_sup | apply sy_elimW ]; assumption.
Qed.

End Step.
