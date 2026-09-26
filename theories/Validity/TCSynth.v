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

Let ihT T : sz_ty T < n -> nlr_ty T -> TYD T := proj1 IH T.
Let ihC t : sz_tm t < n -> nlr_tm t -> CKD t := proj1 (proj2 IH) t.
Let ihS t : sz_tm t < n -> nlr_tm t -> synth t -> SYD t := proj1 (proj2 (proj2 IH)) t.
Let ihX Γ : sz_ctx Γ < n -> nlr_ctx Γ -> CXD Γ := proj2 (proj2 (proj2 IH)) Γ.

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

Lemma HNat {G i Γ} : [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ typeof i ] tyNat @ lzero ].
Proof. intros HΓ; exact (wft_nat _ _ _ (typeof_notV i) (ctx_idem HΓ)). Qed.
Lemma HUniv {G i Γ l} : [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l -> [ G ; Γ ⊢[ typeof i ] tyU l @ lsuc l ].
Proof. intros HΓ Hl; exact (wft_U _ _ _ _ (typeof_notV i) (ctx_idem HΓ) Hl). Qed.

Lemma sy_succ t : sz_tm (succ t) <= n -> nlr_tm (succ t) -> SYD (succ t).
Proof.
  intros Hsz Hn G i Γ HΓ. notV.
  destruct (ihC t ltac:(szl) Hn G i Γ _ _ (HNat HΓ)) as [Ht | N];
    [| right; intros T k H; destruct (inva_succ H) as ((_ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_succ _ _ _ _ Hv Ht).
Qed.

Lemma sy_codepi l l' s t : sz_tm (tmPi l l' s t) <= n -> nlr_tm (tmPi l l' s t) -> SYD (tmPi l l' s t).
Proof.
  intros Hsz [Hns Hnt] G i Γ HΓ. notV.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_code_pi H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros T k H; destruct (inva_code_pi H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihC s ltac:(szl) Hns G i Γ _ _ (HUniv HΓ Hl)) as [Hs | N];
    [| right; intros T k H; destruct (inva_code_pi H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓs : [ G ; Γ ,, tyEl l s @ l ⊢[ typeof i ] ]).
  { apply wfc_ext; [exact HΓ | | exact Hl]. exact (wft_El _ _ _ _ _ (typeof_notV i) Hl (lift_to_typeof_tm Hs)). }
  destruct (ihC t ltac:(szl) Hnt G i _ _ _ (HUniv HΓs Hl')) as [Ht | N];
    [| right; intros T k H; destruct (inva_code_pi H) as ((_ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_code_pi _ _ _ _ _ _ _ Hv Hl Hl' Hs Ht).
Qed.

Lemma sy_natrec l M s z t : sz_tm (natrec l M s z t) <= n -> nlr_tm (natrec l M s z t) -> SYD (natrec l M s z t).
Proof.
  intros Hsz (HnM & Hns & Hnz & Hnt) G i Γ HΓ. notV.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_natrec H) as ((_ & X & _) & _); contradiction].
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (HNat HΓ) | exact I]).
  destruct (ihT M ltac:(szl) HnM G i _ l HΓN) as [HM | N];
    [| right; intros T k H; destruct (inva_natrec H) as ((_ & _ & X & _) & _); contradiction].
  pose proof (lift_to_typeof_ty HM) as HM'.
  pose proof (wf_ty_single (i := typeof i) (typeof_idem i) HM' (wf_zero _ _ _ (typeof_notV i) (ctx_idem HΓ))) as HMz.
  destruct (ihC s ltac:(szl) Hns G i Γ _ _ HMz) as [Hs | N];
    [| right; intros T k H; destruct (inva_natrec H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓNM : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ typeof i ] ]) by (apply wfc_ext; assumption).
  pose proof (wf_ty_subst (typeof_idem i) HM' (lsub_wf_lsucc (typeof_idem i) (typeof_notV i) HΓNM)) as HMs.
  destruct (ihC z ltac:(szl) Hnz G i _ _ _ HMs) as [Hz | N];
    [| right; intros T k H; destruct (inva_natrec H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC t ltac:(szl) Hnt G i Γ _ _ (HNat HΓ)) as [Ht | N];
    [| right; intros T k H; destruct (inva_natrec H) as ((_ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_natrec _ _ _ _ _ _ _ _ Hv Hl HM Hs Hz Ht).
Qed.

Lemma sy_app t l l' A B s : sz_tm (app t l l' A B s) <= n -> nlr_tm (app t l l' A B s) -> SYD (app t l l' A B s).
Proof.
  intros Hsz (Hnt & HnA & HnB & Hns) G i Γ HΓ. notV.
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; destruct (inva_app H) as ((_ & X & _) & _); contradiction].
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; intros T k H; destruct (inva_app H) as ((_ & _ & X & _) & _); contradiction].
  destruct (ihT A ltac:(szl) HnA G i Γ l HΓ) as [HA | N];
    [| right; intros T k H; destruct (inva_app H) as ((_ & _ & _ & X & _) & _); contradiction].
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [exact HΓ | exact (lift_to_typeof_ty HA) | exact Hl]).
  destruct (ihT B ltac:(szl) HnB G i _ l' HΓA) as [HB | N];
    [| right; intros T k H; destruct (inva_app H) as ((_ & _ & _ & _ & X & _) & _); contradiction].
  pose proof (wft_pi _ _ _ _ _ _ _ (typeof_notV i) Hl Hl' (lift_to_typeof_ty HA) (lift_to_typeof_ty HB)) as HP.
  destruct (ihC t ltac:(szl) Hnt G i Γ _ _ HP) as [Ht | N];
    [| right; intros T k H; destruct (inva_app H) as ((_ & _ & _ & _ & _ & X & _) & _); contradiction].
  destruct (ihC s ltac:(szl) Hns G i Γ _ _ (lift_to_typeof_ty HA)) as [Hs | N];
    [| right; intros T k H; destruct (inva_app H) as ((_ & _ & _ & _ & _ & _ & X) & _); contradiction].
  left; eexists; eexists; exact (wf_app _ _ _ _ _ _ _ _ _ Hv Hl Hl' HA HB Ht Hs).
Qed.

Lemma sy_gvar u d : sz_tm (gvar u d) <= n -> nlr_tm (gvar u d) -> SYD (gvar u d).
Proof.
  intros Hsz Hn G i Γ HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (in_gctx_dec (gΨ G) u) as [(D & Hin) | N];
    [| right; intros T k H; destruct (inva_gvar H) as (? & ? & ? & ? & (_ & X & _) & _); exact (N _ X)].
  destruct D as [| Δ i' l0 | Δ i' T0 l0];
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
              (fun m A k1 HA => ihC (llk d m) ltac:(pose proof (sz_llk d m); szl) (nlr_llk d m Hn) G i Γ A k1 HA))
    as [He | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists; exact (wf_gvar _ _ _ _ _ _ _ _ _ HΓ Hin Hle Ht Hd He).
Qed.

Lemma sy_letboxT l' l Δ M t' t : sz_tm (letboxT l' l Δ M t' t) <= n -> nlr_tm (letboxT l' l Δ M t' t) ->
  SYD (letboxT l' l Δ M t' t).
Proof.
  intros Hsz (HnΔ & HnM & Hnt' & Hnt) G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  Ltac inv_lbT X := let H := fresh "H" in intros ? ? H; destruct (inv_letboxT eq_refl H) as (X & _).
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; inv_lbT X; destruct X as (_ & X & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; inv_lbT X; destruct X as (_ & _ & X & _); contradiction].
  destruct (ihX Δ ltac:(szl) HnΔ G lD HG) as [HΔ | N]; [| right; inv_lbT X; destruct X as (_ & _ & _ & X & _); contradiction].
  pose proof (wft_CTyp _ _ _ _ HΓ HΔ Hl) as HC.
  assert (HΓC : [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  destruct (ihT M ltac:(szl) HnM G lM _ l' HΓC) as [HM | N]; [| right; inv_lbT X; destruct X as (_ & _ & _ & _ & X & _); contradiction].
  destruct (ihC t' ltac:(szl) Hnt' _ lM _ _ _ (letboxT_body_wf HΔ Hl HM)) as [Ht' | N];
    [| right; inv_lbT X; destruct X as (_ & _ & _ & _ & _ & X & _); contradiction].
  destruct (ihC t ltac:(szl) Hnt G lM Γ _ _ HC) as [Ht | N]; [| right; inv_lbT X; destruct X as (_ & _ & _ & _ & _ & _ & X); contradiction].
  left; eexists; eexists; exact (wf_letboxT _ _ _ _ _ _ _ _ Hl' Hl HΔ HM Ht' Ht).
Qed.

Lemma sy_letboxt l' l Δ A M t' t : sz_tm (letboxt l' l Δ A M t' t) <= n -> nlr_tm (letboxt l' l Δ A M t' t) ->
  SYD (letboxt l' l Δ A M t' t).
Proof.
  intros Hsz (HnΔ & HnA & HnM & Hnt' & Hnt) G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  Ltac inv_lbt X := let H := fresh "H" in intros ? ? H; destruct (inv_letboxt eq_refl H) as (X & _).
  destruct (lwf_Dec (gL G) l') as [Hl' | N]; [| right; inv_lbt X; destruct X as (_ & X & _); contradiction].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; inv_lbt X; destruct X as (_ & _ & X & _); contradiction].
  destruct (ihX Δ ltac:(szl) HnΔ G lD HG) as [HΔ | N]; [| right; inv_lbt X; destruct X as (_ & _ & _ & X & _); contradiction].
  destruct (ihT A ltac:(szl) HnA G lD Δ l HΔ) as [HA | N]; [| right; inv_lbt X; destruct X as (_ & _ & _ & _ & X & _); contradiction].
  pose proof (wft_CTrm _ _ _ _ _ HΓ HΔ HA Hl) as HC.
  assert (HΓC : [ G ; Γ ,, tyCTrm Δ A l @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  destruct (ihT M ltac:(szl) HnM G lM _ l' HΓC) as [HM | N]; [| right; inv_lbt X; destruct X as (_ & _ & _ & _ & _ & X & _); contradiction].
  destruct (ihC t' ltac:(szl) Hnt' _ lM _ _ _ (letboxt_body_wf HA Hl HM)) as [Ht' | N];
    [| right; inv_lbt X; destruct X as (_ & _ & _ & _ & _ & _ & X & _); contradiction].
  destruct (ihC t ltac:(szl) Hnt G lM Γ _ _ HC) as [Ht | N]; [| right; inv_lbt X; destruct X as (_ & _ & _ & _ & _ & _ & _ & X); contradiction].
  left; eexists; eexists; exact (wf_letboxt _ _ _ _ _ _ _ _ _ Hl' Hl HΔ HA HM Ht' Ht).
Qed.

(** ** The recursors *)

Lemma sy_elimT l1 l2 rb l Δ t : sz_tm (elimT l1 l2 rb l Δ t) <= n -> nlr_tm (elimT l1 l2 rb l Δ t) ->
  SYD (elimT l1 l2 rb l Δ t).
Proof.
  intros Hsz (Hnrb & HnΔ & Hnt) G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (rb_view rb) as [(MT & Mt & bs & ->) | N];
    [| right; intros T k H; destruct (inv_elimT eq_refl H) as (MT & Mt & bs & (E & _) & _); exact (N _ _ _ E)].
  destruct (nlr_mkrb _ _ _ Hnrb) as (HnMT & HnMt & Hnbs). pose proof (sz_mkrb MT Mt bs) as (SMT & SMt & Sbs).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : T @ k ] ->
    lwf (gL G) l1 /\ lwf (gL G) l2 /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] /\ [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] /\
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) /\
    [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ]).
  { intros T k H. destruct (inv_elimT eq_refl H) as (MT' & Mt' & bs' & (E & _ & _ & H1 & H2 & H3 & HΔ & HM1 & HM2 & _ & Hb & Ht) & _).
    destruct (mkrb_inj_MT E) as [<- <-]. pose proof (mkrb_inj_br E) as Eb.
    repeat split; try assumption. intros k0 Hk0. rewrite (Eb k0 Hk0). exact (Hb k0 Hk0). }
  destruct (lwf_Dec (gL G) l1) as [Hl1 | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lwf_Dec (gL G) l2) as [Hl2 | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihX Δ ltac:(szl) HnΔ G lD HG) as [HΔ | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT MT ltac:(szl) HnMT (recGT G) lM (recΓT Γ) (lvren l1 (ush 1)) (wf_recΓT _ _ HΓ)) as [HMT | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT Mt ltac:(szl) HnMt (recGt G) lM (recΓt Γ) (lvren l2 (ush 1)) (wf_recΓt _ _ HΓ)) as [HMt | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (dec_forall_lt' (fun k => [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) 13
              (fun k Hk => ihC (bs k) ltac:(specialize (Sbs k Hk); szl) (Hnbs k Hk) (brG k G) lM _ _ _
                             (brRes_wf HΓ Hl1 Hl2 HMT HMt k Hk))) as [Hb | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihC t ltac:(szl) Hnt G lM Γ _ _ (wft_CTyp _ _ _ _ HΓ HΔ Hl)) as [Ht | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists; exact (wf_elimT_adm Hl1 Hl2 Hl HΔ HMT HMt Hb Ht).
Qed.

Lemma sy_elimt l1 l2 rb l Δ A t : sz_tm (elimt l1 l2 rb l Δ A t) <= n -> nlr_tm (elimt l1 l2 rb l Δ A t) ->
  SYD (elimt l1 l2 rb l Δ A t).
Proof.
  intros Hsz (Hnrb & HnΔ & HnA & Hnt) G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (rb_view rb) as [(MT & Mt & bs & ->) | N];
    [| right; intros T k H; destruct (inv_elimt eq_refl H) as (MT & Mt & bs & (E & _) & _); exact (N _ _ _ E)].
  destruct (nlr_mkrb _ _ _ Hnrb) as (HnMT & HnMt & Hnbs). pose proof (sz_mkrb MT Mt bs) as (SMT & SMt & Sbs).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ A t : T @ k ] ->
    lwf (gL G) l1 /\ lwf (gL G) l2 /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] /\ [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] /\
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) /\
    [ G ; Δ ⊢[ lD ] A @ l ] /\ [ G ; Γ ⊢[ lM ] t : tyCTrm Δ A l @ lzero ]).
  { intros T k H.
    destruct (inv_elimt eq_refl H) as (MT' & Mt' & bs' & (E & _ & _ & H1 & H2 & H3 & HΔ & HM1 & HM2 & _ & Hb & HA & Ht) & _).
    destruct (mkrb_inj_MT E) as [<- <-]. pose proof (mkrb_inj_br E) as Eb.
    repeat split; try assumption. intros k0 Hk0. rewrite (Eb k0 Hk0). exact (Hb k0 Hk0). }
  destruct (lwf_Dec (gL G) l1) as [Hl1 | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lwf_Dec (gL G) l2) as [Hl2 | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (lwf_Dec (gL G) l) as [Hl | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihX Δ ltac:(szl) HnΔ G lD HG) as [HΔ | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT MT ltac:(szl) HnMT (recGT G) lM (recΓT Γ) (lvren l1 (ush 1)) (wf_recΓT _ _ HΓ)) as [HMT | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT Mt ltac:(szl) HnMt (recGt G) lM (recΓt Γ) (lvren l2 (ush 1)) (wf_recΓt _ _ HΓ)) as [HMt | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (dec_forall_lt' (fun k => [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) 13
              (fun k Hk => ihC (bs k) ltac:(specialize (Sbs k Hk); szl) (Hnbs k Hk) (brG k G) lM _ _ _
                             (brRes_wf HΓ Hl1 Hl2 HMT HMt k Hk))) as [Hb | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihT A ltac:(szl) HnA G lD Δ l HΔ) as [HA | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  destruct (ihC t ltac:(szl) Hnt G lM Γ _ _ (wft_CTrm _ _ _ _ _ HΓ HΔ HA Hl)) as [Ht | N];
    [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists; exact (wf_elimt_adm Hl1 Hl2 Hl HΔ HMT HMt Hb HA Ht).
Qed.

(** ** The applications of the meta-level functions *)

(** A checked function of another former is untyped at this one. *)
Ltac chk_refute Hs Ht W Hnot :=
  let Eh := fresh "Eh" in pose proof (chk_at_whnf Hs Ht W) as Eh;
  match goal with f : tm |- _ => destruct f; cbn in Eh, Hnot; first [discriminate Eh | contradiction] end.

Lemma sy_uapp f ls : sz_tm (uapp f ls) <= n -> nlr_tm (uapp f ls) -> SYD (uapp f ls).
Proof.
  intros Hsz [Hu Hn] G i Γ HΓ. atM.
  destruct (synth_dec f) as [Hs | Hs];
    [| right; intros T k H; destruct (inv_uapp eq_refl H) as (m & l & T0 & (_ & _ & _ & _ & _ & Ht) & _);
       pose proof (chk_at_whnf Hs Ht (whnf_tyUPi _ _ _)) as Eh; clear H;
       destruct f; cbn in Eh, Hu; first [discriminate Eh | contradiction]].
  destruct (ihS f ltac:(szl) Hn Hs G lM Γ HΓ) as [(F & kf & Hf) | N];
    [| right; intros T k H; destruct (inv_uapp eq_refl H) as (m & l & T0 & (_ & _ & _ & _ & _ & Ht) & _); exact (N _ _ Ht)].
  pose proof (wf_tm_ty (i := lM) eq_refl Hf) as HF.
  destruct (whnf_normalization_ty_c compt_M HF) as (W & _ & Hw & EW).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] uapp f ls : T @ k ] -> exists m l T0,
    [ G ; Γ ⊢[ lM ] W ≅ tyUPi m l T0 @ kf ] /\ length ls = m /\ Forall (lwf (gL G)) ls).
  { intros T k H. destruct (inv_uapp eq_refl H) as (m & l & T0 & (_ & _ & _ & Hlen & Hls & Ht) & _).
    destruct (type_uniq f Hn Hs _ _ _ _ _ _ _ Hf Ht) as (_ & E).
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

Lemma sy_capp f Δ : sz_tm (capp f Δ) <= n -> nlr_tm (capp f Δ) -> SYD (capp f Δ).
Proof.
  intros Hsz (Hc & Hn & HnΔ) G i Γ HΓ. atM. pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (synth_dec f) as [Hs | Hs];
    [| right; intros T k H; destruct (inv_capp eq_refl H) as (l & T0 & (_ & _ & _ & _ & Ht & _) & _);
       pose proof (chk_at_whnf Hs Ht (whnf_tyCPi _ _)) as Eh; clear H;
       destruct f; cbn in Eh, Hc; first [discriminate Eh | contradiction]].
  destruct (ihS f ltac:(szl) Hn Hs G lM Γ HΓ) as [(F & kf & Hf) | N];
    [| right; intros T k H; destruct (inv_capp eq_refl H) as (l & T0 & (_ & _ & _ & _ & Ht & _) & _); exact (N _ _ Ht)].
  pose proof (wf_tm_ty (i := lM) eq_refl Hf) as HF.
  destruct (whnf_normalization_ty_c compt_M HF) as (W & _ & Hw & EW).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] capp f Δ : T @ k ] -> [ G ; Δ ⊢[ lD ] ] /\ exists l T0,
    [ G ; Γ ⊢[ lM ] W ≅ tyCPi l T0 @ kf ]).
  { intros T k H. destruct (inv_capp eq_refl H) as (l & T0 & (_ & _ & _ & HΔ & Ht & _) & _).
    destruct (type_uniq f Hn Hs _ _ _ _ _ _ _ Hf Ht) as (_ & E).
    split; [exact HΔ |]. exists l, T0. eapply eqty_trans; [apply eqty_sym; exact EW | exact E]. }
  destruct (cpi_view W) as [(l & T0 & ->) | Nh];
    [| right; intros T k H; destruct (Inv _ _ H) as (_ & l & T0 & E); apply Nh;
       exact (decl_head_c compt_M E Hw (whnf_tyCPi _ _))].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW. destruct (inv_ty_cpi HW) as ((_ & _ & Hl & HT0) & Hk).
  destruct (ihX Δ ltac:(szl) HnΔ G lD HG) as [HΔ | N]; [| right; intros T k H; apply N, (Inv _ _ H)].
  left; eexists; eexists. eapply wf_capp; [exact Hl | exact HT0 | exact HΔ | | exact (inst_c_ty HΓ HΔ HT0)].
  exact (wf_lvl (lvl_eq_sym Hk) (wf_conv _ _ _ _ _ _ _ Hf (eqty_sym _ _ _ _ _ _ EW))).
Qed.

Lemma sy_tapp f A : sz_tm (tapp f A) <= n -> nlr_tm (tapp f A) -> SYD (tapp f A).
Proof.
  intros Hsz (Hc & Hn & HnA) G i Γ HΓ. atM.
  destruct (synth_dec f) as [Hs | Hs];
    [| right; intros T k H; destruct (inv_tapp eq_refl H) as (Δ & l & l' & T0 & (_ & Ht & _) & _);
       pose proof (chk_at_whnf Hs Ht (whnf_tyTPi _ _ _ _)) as Eh; clear H;
       destruct f; cbn in Eh, Hc; first [discriminate Eh | contradiction]].
  destruct (ihS f ltac:(szl) Hn Hs G lM Γ HΓ) as [(F & kf & Hf) | N];
    [| right; intros T k H; destruct (inv_tapp eq_refl H) as (Δ & l & l' & T0 & (_ & Ht & _) & _); exact (N _ _ Ht)].
  pose proof (wf_tm_ty (i := lM) eq_refl Hf) as HF.
  destruct (whnf_normalization_ty_c compt_M HF) as (W & _ & Hw & EW).
  assert (Inv : forall T k, [ G ; Γ ⊢[ lM ] tapp f A : T @ k ] -> exists Δ l l' T0,
    [ G ; Γ ⊢[ lM ] W ≅ tyTPi Δ l l' T0 @ kf ] /\ [ G ; Δ ⊢[ lD ] A @ l ]).
  { intros T k H. destruct (inv_tapp eq_refl H) as (Δ & l & l' & T0 & (_ & Ht & _ & _ & _ & _ & HA & _) & _).
    destruct (type_uniq f Hn Hs _ _ _ _ _ _ _ Hf Ht) as (_ & E).
    exists Δ, l, l', T0; split; [| exact HA]. eapply eqty_trans; [apply eqty_sym; exact EW | exact E]. }
  destruct (tpi_view W) as [(Δ & l & l' & T0 & ->) | Nh];
    [| right; intros T k H; destruct (Inv _ _ H) as (Δ & l & l' & T0 & E & _); apply Nh;
       exact (decl_head_c compt_M E Hw (whnf_tyTPi _ _ _ _))].
  pose proof (eqty_wf_r (i := lM) eq_refl EW) as HW.
  destruct (inv_ty_tpi HW) as ((_ & _ & HΔ & Hl & Hl' & HT0) & Hk).
  destruct (ihT A ltac:(szl) HnA G lD Δ l HΔ) as [HA | N].
  - left; eexists; eexists. eapply wf_tapp; [| exact HΔ | exact Hl | exact Hl' | exact HT0 | exact HA |
                                           exact (inst_t_ty HΓ HA HT0)].
    exact (wf_lvl (lvl_eq_sym Hk) (wf_conv _ _ _ _ _ _ _ Hf (eqty_sym _ _ _ _ _ _ EW))).
  - right; intros T k H. destruct (Inv _ _ H) as (Δ' & l1 & l2 & T0' & E & HA').
    destruct (tpi_inj E) as (Q1 & _ & EΔ & _). apply N.
    exact (wft_lconv _ _ _ _ _ _ (ctxconv_ty (eqctx_sym_D EΔ) (i := lD) eq_refl HA') Q1).
Qed.

(** ** The step *)

Lemma sy_step t : sz_tm t <= n -> nlr_tm t -> synth t -> SYD t.
Proof.
  intros Hsz Hn Hs. destruct t; cbn in Hs; try contradiction;
    first [ apply sy_var | apply sy_nat | apply sy_zero | apply sy_U
          | apply sy_junk; exact I
          | apply sy_succ | apply sy_codepi | apply sy_natrec | apply sy_app | apply sy_gvar
          | apply sy_letboxT | apply sy_letboxt | apply sy_elimT | apply sy_elimt
          | apply sy_uapp | apply sy_capp | apply sy_tapp ]; assumption.
Qed.

End Step.
