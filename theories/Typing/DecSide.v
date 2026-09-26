(** * Decidable side conditions and the redex-free fragment (M7_DESIGN.md C1, J1, J3.2)

    The syntactic premises of the typing rules are decidable: context and
    global lookups (deterministic, [in_ctx_det], [in_gctx_det]), the tail
    condition and deep normality of local substitutions, the layer order,
    and the shape of a recursor bundle ([rb_view], by an extraction
    [unrb] inverse to [mkrb]).

    The fragment [nlr]: no [uapp (ulam …)], [capp (clam …)], [tapp (tlam …)]
    anywhere (J1). The size [sz] is the induction measure of the
    decision procedure: the entries of a local substitution and the parts
    of a bundle are smaller than the node holding them. *)
From DeLaM.Syntax Require Export LevelDec.
From DeLaM.Typing Require Export InvAny.

Lemma dec_not {P} : Dec P -> Dec (~ P).
Proof. unfold Dec; tauto. Qed.
Lemma dec_forall_lt' (P : nat -> Prop) n : (forall x, x < n -> Dec (P x)) -> Dec (forall x, x < n -> P x).
Proof.
  induction n as [|n IH]; intros HP; [left; intros x Hx; lia |].
  destruct (IH (fun x Hx => HP x (Nat.lt_lt_succ_r _ _ Hx))) as [Y | N].
  - destruct (HP n (Nat.lt_succ_diag_r n)) as [Hn | Hn].
    + left; intros x Hx. destruct (Nat.eq_dec x n); [subst; exact Hn | apply Y; lia].
    + right; intros H; apply Hn, H; lia.
  - right; intros H; apply N; intros x Hx; apply H; lia.
Qed.

(** ** Lookups *)

Lemma in_ctx_dec Γ n : (exists T l, in_ctx Γ n T l) \/ (forall T l, ~ in_ctx Γ n T l).
Proof.
  revert n; induction Γ as [| g | Γ IH A k]; intros n.
  - right; intros T l H; inversion H.
  - right; intros T l H; inversion H.
  - destruct n as [|n].
    + left; exists A⟨↑⟩, k; constructor.
    + destruct (IH n) as [(T & l & H) | N].
      * left; exists T⟨↑⟩, l; apply in_there; exact H.
      * right; intros T l H; inversion H; subst; eapply N; eassumption.
Qed.

Lemma in_gctx_dec Ψ u : (exists D, in_gctx Ψ u D) \/ (forall D, ~ in_gctx Ψ u D).
Proof.
  revert u; induction Ψ as [|D0 Ψ IH]; intros u.
  - right; intros D H; inversion H.
  - destruct u as [|u].
    + left; eexists; constructor.
    + destruct (IH u) as [(D & H) | N].
      * left; eexists; apply ing_there; exact H.
      * right; intros D H; inversion H; subst; eapply N; eassumption.
Qed.

Lemma gctx_var_dec G g : Dec (gctx_var G g).
Proof.
  unfold gctx_var. destruct (nth_error (gΨ G) g) as [[| |]|];
    first [left; reflexivity | right; discriminate].
Qed.

Lemma lle_dec i j : Dec (lle i j).
Proof. unfold lle. destruct (le_dec (lrank i) (lrank j)); [left | right]; assumption. Qed.

Lemma lwf_Dec L l : Dec (lwf L l).
Proof. destruct (lwf_dec L l); [left | right]; assumption. Qed.

Lemma lvl_dec_eq (k k' : lvl) : {k = k'} + {k <> k'}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Lemma lvl_eq_dec L k l : Dec (lvl_eq L k l).
Proof.
  unfold lvl_eq. destruct (lvl_dec_eq k l) as [E | E]; [left; left; exact E |].
  destruct (lequiv_dec L k l) as [Q | Q]; [left; right; exact Q | right; intros [X | X]; contradiction].
Qed.

Lemma layer_eq_dec (i j : layer) : Dec (i = j).
Proof. destruct i, j; first [left; reflexivity | right; discriminate]. Qed.

(** ** Local substitutions *)

Lemma labsorb_dec d t : Dec (labsorb d t).
Proof. destruct d as [[|k]|]; destruct t; cbn; try (right; tauto). apply dec_nat_eq. Qed.

Lemma dnf_dec_all :
  (forall T, Dec (dnfty T)) /\ (forall t, Dec (dnftm t)) /\ (forall Γ, Dec (dnfctx Γ)) /\ (forall d, Dec (dnfl d)).
Proof.
  apply syn_ind; intros; cbn [dnfty dnftm dnfctx dnfl];
    repeat first [ apply dec_and | assumption | apply dec_True | apply dec_not; apply labsorb_dec ].
Qed.
Lemma dnfl_dec d : Dec (dnfl d). Proof. apply dnf_dec_all. Qed.

Lemma ctx_tail_cases Γ : ctx_tail Γ = cnil \/ exists g, ctx_tail Γ = cvar g.
Proof. induction Γ as [| g | Γ IH A k]; cbn; auto. right; eexists; reflexivity. Qed.

Lemma ctx_tail_eq_dec Δ Γ : Dec (ctx_tail Δ = ctx_tail Γ).
Proof.
  destruct (ctx_tail_cases Δ) as [-> | (g & ->)], (ctx_tail_cases Γ) as [-> | (g' & ->)];
    try (right; discriminate); [left; reflexivity |].
  destruct (Nat.eq_dec g g') as [-> | N]; [left; reflexivity | right; intros E; injection E; contradiction].
Qed.

Lemma shift_tail_dec e : forall b, Dec (forall n, llk e n = var (b + n)).
Proof.
  induction e as [k | e IH t]; intros b; cbn [llk].
  - destruct (Nat.eq_dec k b) as [-> | N].
    + left; intros n; f_equal; lia.
    + right; intros H; specialize (H 0); injection H; lia.
  - assert (Ht : Dec (t = var b)).
    { destruct t; try (right; discriminate). destruct (Nat.eq_dec n b) as [-> | N];
        [left; reflexivity | right; intros E; injection E; contradiction]. }
    destruct Ht as [-> | Nt]; [| right; intros H; apply Nt; rewrite (H 0); f_equal; lia].
    destruct (IH (S b)) as [Y | N].
    + left; intros [|n]; [f_equal; lia | rewrite Y; f_equal; lia].
    + right; intros H; apply N; intros n. rewrite (H (S n)); f_equal; lia.
Qed.

Lemma lsub_tail_dec d Δ Γ : Dec (lsub_tail d Δ Γ).
Proof.
  unfold lsub_tail. apply dec_and; [apply ctx_tail_eq_dec |].
  apply (dec_iff (P := forall n, llk (ldrop (clen Δ) d) n = var (clen Γ + n))).
  - split; intros H n; [rewrite <- llk_ldrop | rewrite llk_ldrop]; apply H.
  - apply shift_tail_dec.
Qed.

(** ** The recursor bundle *)

Fixpoint unwrapU (n : nat) (x : tm) : option tm :=
  match n with 0 => Some x | S n => match x with bindU b => unwrapU n b | _ => None end end.
Fixpoint unwrapG (n : nat) (x : tm) : option tm :=
  match n with 0 => Some x | S n => match x with bindG b => unwrapG n b | _ => None end end.
Fixpoint unwrapL (n : nat) (x : tm) : option tm :=
  match n with 0 => Some x | S n => match x with bindL b => unwrapL n b | _ => None end end.
Definition unwrap (nu ng nl : nat) (x : tm) : option tm :=
  match unwrapU nu x with
  | Some y => match unwrapG ng y with Some z => unwrapL nl z | None => None end
  | None => None
  end.

Lemma unwrap_wrap nu ng nl b : unwrap nu ng nl (wrap nu ng nl b) = Some b.
Proof.
  unfold unwrap, wrap.
  assert (EU : forall n x, unwrapU n (wrapU n x) = Some x) by (induction n; cbn; auto).
  assert (EG : forall n x, unwrapG n (wrapG n x) = Some x) by (induction n; cbn; auto).
  assert (EL : forall n x, unwrapL n (wrapL n x) = Some x) by (induction n; cbn; auto).
  rewrite EU, EG, EL. reflexivity.
Qed.

Lemma unwrap_inv nu ng nl x b : unwrap nu ng nl x = Some b -> x = wrap nu ng nl b.
Proof.
  unfold unwrap, wrap.
  assert (EU : forall n x y, unwrapU n x = Some y -> x = wrapU n y)
    by (induction n; intros [] y H; cbn in H; try discriminate; try (injection H; intros; subst; reflexivity);
        cbn; f_equal; auto).
  assert (EG : forall n x y, unwrapG n x = Some y -> x = wrapG n y)
    by (induction n; intros [] y H; cbn in H; try discriminate; try (injection H; intros; subst; reflexivity);
        cbn; f_equal; auto).
  assert (EL : forall n x y, unwrapL n x = Some y -> x = wrapL n y)
    by (induction n; intros [] y H; cbn in H; try discriminate; try (injection H; intros; subst; reflexivity);
        cbn; f_equal; auto).
  destruct (unwrapU nu x) as [y|] eqn:Ey; [| discriminate].
  destruct (unwrapG ng y) as [z|] eqn:Ez; [| discriminate].
  intros Eb. rewrite (EU _ _ _ Ey), (EG _ _ _ Ez), (EL _ _ _ Eb). reflexivity.
Qed.

Definition wrap_br (f : nat -> tm) (k : nat) : tm := let '(nu, ng, nl) := br_ar k in wrap nu ng nl (f k).
Definition unwrap_br (k : nat) (a : tm) : option tm := let '(nu, ng, nl) := br_ar k in unwrap nu ng nl a.

Lemma unwrap_br_wrap f k : unwrap_br k (wrap_br f k) = Some (f k).
Proof. unfold unwrap_br, wrap_br. destruct (br_ar k) as [[nu ng] nl]. apply unwrap_wrap. Qed.
Lemma unwrap_br_inv k a b : unwrap_br k a = Some b -> a = wrap_br (fun _ => b) k.
Proof. unfold unwrap_br, wrap_br. destruct (br_ar k) as [[nu ng] nl]. apply unwrap_inv. Qed.

Fixpoint unbrs (x : tm) (k n : nat) {struct n} : option (list tm) :=
  match n with
  | 0 => match x with tmErr => Some nil | _ => None end
  | S n => match x with
           | tmTup a r =>
               match unwrap_br k a, unbrs r (S k) n with
               | Some b, Some bs => Some (b :: bs)
               | _, _ => None
               end
           | _ => None
           end
  end.

Definition unrb (rb : tm) : option (ty * ty * list tm) :=
  match rb with
  | tmTup (bindU (bindG (bindL (tmTy MT)))) (tmTup (bindU (bindG (bindG (bindL (tmTy Mt))))) r) =>
      match unbrs r 0 13 with Some bs => Some (MT, Mt, bs) | None => None end
  | _ => None
  end.

(** Case analysis on the scrutinees of an extraction that succeeded. *)
Ltac split_matches H :=
  repeat match type of H with
  | context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E; try discriminate H
  end.

Lemma tup_from_ext f g k n : (forall j, k <= j -> f j = g j) -> tup_from f k n = tup_from g k n.
Proof.
  revert k; induction n as [|n IH]; intros k H; cbn; [reflexivity |].
  rewrite (H k (le_n _)), (IH (S k)); [reflexivity | intros j Hj; apply H; lia].
Qed.

Lemma unbrs_tup f k n : unbrs (tup_from (wrap_br f) k n) k n = Some (map f (seq k n)).
Proof.
  revert k; induction n as [|n IH]; intros k; cbn; [reflexivity |].
  rewrite unwrap_br_wrap, IH. reflexivity.
Qed.

Lemma unbrs_inv n : forall x k bs, unbrs x k n = Some bs ->
  x = tup_from (wrap_br (fun j => nth (j - k) bs tmErr)) k n.
Proof.
  induction n as [|n IH]; intros x k bs H; cbn [unbrs] in H; split_matches H; cbn [tup_from].
  - reflexivity.
  - injection H as <-. rewrite (IH _ _ _ E1), (unwrap_br_inv _ _ _ E0). f_equal.
    + unfold wrap_br. rewrite Nat.sub_diag. reflexivity.
    + apply tup_from_ext. intros j Hj. unfold wrap_br.
      replace (j - k) with (S (j - S k)) by lia. reflexivity.
Qed.

Lemma mkrb_as MT Mt bs : mkrb MT Mt bs = tmTup (wrapMT MT) (tmTup (wrapMt Mt) (tup_from (wrap_br bs) 0 13)).
Proof. reflexivity. Qed.

Lemma unrb_mkrb MT Mt bs : unrb (mkrb MT Mt bs) = Some (MT, Mt, map bs (seq 0 13)).
Proof. rewrite mkrb_as. unfold unrb, wrapMT, wrapMt. rewrite unbrs_tup. reflexivity. Qed.

Lemma unrb_inv rb MT Mt bs : unrb rb = Some (MT, Mt, bs) -> rb = mkrb MT Mt (fun k => nth k bs tmErr).
Proof.
  unfold unrb. intros H. split_matches H. injection H as <- <- <-. subst.
  rewrite mkrb_as. unfold wrapMT, wrapMt. do 2 f_equal.
  match goal with Er : unbrs _ 0 13 = Some _ |- _ => rewrite (unbrs_inv _ _ _ _ Er) end.
  apply tup_from_ext. intros j _. unfold wrap_br. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma rb_view rb : (exists MT Mt bs, rb = mkrb MT Mt bs) \/ (forall MT Mt bs, rb <> mkrb MT Mt bs).
Proof.
  destruct (unrb rb) as [[[MT Mt] bs]|] eqn:E.
  - left; exists MT, Mt, (fun k => nth k bs tmErr). exact (unrb_inv _ _ _ _ E).
  - right; intros MT Mt bs ->. rewrite unrb_mkrb in E. discriminate.
Qed.

(** ** The redex-free fragment *)

Definition not_ulam (t : tm) : Prop := match t with ulam _ _ _ => False | _ => True end.
Definition not_clam (t : tm) : Prop := match t with clam _ _ => False | _ => True end.
Definition not_tlam (t : tm) : Prop := match t with tlam _ _ _ => False | _ => True end.

Fixpoint nlr_ty (T : ty) : Prop :=
  match T with
  | tyErr | tyNat | tyU _ => True
  | tyPi _ _ A B => nlr_ty A /\ nlr_ty B
  | tyEl _ t => nlr_tm t
  | tyGvar _ d => nlr_l d
  | tyCTyp Δ _ => nlr_ctx Δ
  | tyCTrm Δ T _ => nlr_ctx Δ /\ nlr_ty T
  | tyUPi _ _ T | tyCPi _ T => nlr_ty T
  | tyTPi Δ _ _ T => nlr_ctx Δ /\ nlr_ty T
  end
with nlr_tm (t : tm) : Prop :=
  match t with
  | var _ | tmErr | tmNat | tmU _ | zero => True
  | tmPi _ _ s t => nlr_tm s /\ nlr_tm t
  | succ t => nlr_tm t
  | natrec _ M s z t => nlr_ty M /\ nlr_tm s /\ nlr_tm z /\ nlr_tm t
  | lam _ _ A t => nlr_ty A /\ nlr_tm t
  | app t _ _ A B s => nlr_tm t /\ nlr_ty A /\ nlr_ty B /\ nlr_tm s
  | gvar _ d => nlr_l d
  | boxT T => nlr_ty T
  | boxt t => nlr_tm t
  | letboxT _ _ Δ M t' t => nlr_ctx Δ /\ nlr_ty M /\ nlr_tm t' /\ nlr_tm t
  | letboxt _ _ Δ T M t' t => nlr_ctx Δ /\ nlr_ty T /\ nlr_ty M /\ nlr_tm t' /\ nlr_tm t
  | tmTy T => nlr_ty T
  | tmTup s t => nlr_tm s /\ nlr_tm t
  | bindU b | bindG b | bindL b => nlr_tm b
  | elimT _ _ rb _ Δ t => nlr_tm rb /\ nlr_ctx Δ /\ nlr_tm t
  | elimt _ _ rb _ Δ T t => nlr_tm rb /\ nlr_ctx Δ /\ nlr_ty T /\ nlr_tm t
  | ulam _ _ t | clam _ t | tlam _ _ t => nlr_tm t
  | uapp t _ => not_ulam t /\ nlr_tm t
  | capp t Δ => not_clam t /\ nlr_tm t /\ nlr_ctx Δ
  | tapp t T => not_tlam t /\ nlr_tm t /\ nlr_ty T
  end
with nlr_ctx (Γ : ctx) : Prop :=
  match Γ with cnil | cvar _ => True | cext Γ A _ => nlr_ctx Γ /\ nlr_ty A end
with nlr_l (d : lsub) : Prop :=
  match d with lshift _ => True | lcons d t => nlr_l d /\ nlr_tm t end.

Lemma nlr_dec_all :
  (forall T, Dec (nlr_ty T)) /\ (forall t, Dec (nlr_tm t)) /\ (forall Γ, Dec (nlr_ctx Γ)) /\ (forall d, Dec (nlr_l d)).
Proof.
  apply syn_ind; intros; cbn [nlr_ty nlr_tm nlr_ctx nlr_l];
    repeat first [ apply dec_and | assumption | apply dec_True ].
  all: match goal with
       | |- Dec (not_ulam ?t) => destruct t; cbn; first [apply dec_True | apply dec_False]
       | |- Dec (not_clam ?t) => destruct t; cbn; first [apply dec_True | apply dec_False]
       | |- Dec (not_tlam ?t) => destruct t; cbn; first [apply dec_True | apply dec_False]
       end.
Qed.

Lemma nlr_llk d n : nlr_l d -> nlr_tm (llk d n).
Proof. revert n; induction d as [k | d IH t]; intros [|n] H; cbn in *; try tauto. apply IH; tauto. Qed.

Lemma nlr_tup f k n : nlr_tm (tup_from f k n) -> forall j, k <= j -> j < k + n -> nlr_tm (f j).
Proof.
  revert k; induction n as [|n IH]; intros k H j Hj Hj'; [lia |]. cbn in H.
  destruct (Nat.eq_dec j k) as [-> | N]; [exact (proj1 H) | apply (IH (S k)); [exact (proj2 H) | lia | lia]].
Qed.

Lemma nlr_wrap nu ng nl b : nlr_tm (wrap nu ng nl b) -> nlr_tm b.
Proof.
  unfold wrap. induction nu as [|nu IH]; cbn; [| exact IH].
  induction ng as [|ng IHg]; cbn; [| exact IHg]. induction nl as [|nl IHl]; cbn; [auto | exact IHl].
Qed.

Lemma nlr_mkrb MT Mt bs : nlr_tm (mkrb MT Mt bs) -> nlr_ty MT /\ nlr_ty Mt /\ forall k, k < 13 -> nlr_tm (bs k).
Proof.
  rewrite mkrb_as. unfold wrapMT, wrapMt. cbn [nlr_tm]. intros (HT & Ht & Hb). refine (conj HT (conj Ht _)).
  intros k Hk. pose proof (nlr_tup _ _ _ Hb k ltac:(lia) ltac:(lia)) as X.
  unfold wrap_br in X. destruct (br_ar k) as [[nu ng] nl]. exact (nlr_wrap _ _ _ _ X).
Qed.

(** ** The size of syntax *)

Fixpoint sz_ty (T : ty) : nat :=
  match T with
  | tyErr | tyNat | tyU _ => 1
  | tyPi _ _ A B => S (sz_ty A + sz_ty B)
  | tyEl _ t => S (sz_tm t)
  | tyGvar _ d => S (sz_l d)
  | tyCTyp Δ _ => S (sz_ctx Δ)
  | tyCTrm Δ T _ => S (sz_ctx Δ + sz_ty T)
  | tyUPi _ _ T | tyCPi _ T => S (sz_ty T)
  | tyTPi Δ _ _ T => S (sz_ctx Δ + sz_ty T)
  end
with sz_tm (t : tm) : nat :=
  match t with
  | var _ | tmErr | tmNat | tmU _ | zero => 1
  | tmPi _ _ s t => S (sz_tm s + sz_tm t)
  | succ t => S (sz_tm t)
  | natrec _ M s z t => S (sz_ty M + sz_tm s + sz_tm z + sz_tm t)
  | lam _ _ A t => S (sz_ty A + sz_tm t)
  | app t _ _ A B s => S (sz_tm t + sz_ty A + sz_ty B + sz_tm s)
  | gvar _ d => S (sz_l d)
  | boxT T => S (sz_ty T)
  | boxt t => S (sz_tm t)
  | letboxT _ _ Δ M t' t => S (sz_ctx Δ + sz_ty M + sz_tm t' + sz_tm t)
  | letboxt _ _ Δ T M t' t => S (sz_ctx Δ + sz_ty T + sz_ty M + sz_tm t' + sz_tm t)
  | tmTy T => S (sz_ty T)
  | tmTup s t => S (sz_tm s + sz_tm t)
  | bindU b | bindG b | bindL b => S (sz_tm b)
  | elimT _ _ rb _ Δ t => S (sz_tm rb + sz_ctx Δ + sz_tm t)
  | elimt _ _ rb _ Δ T t => S (sz_tm rb + sz_ctx Δ + sz_ty T + sz_tm t)
  | ulam _ _ t | clam _ t | tlam _ _ t => S (sz_tm t)
  | uapp t _ => S (sz_tm t)
  | capp t Δ => S (sz_tm t + sz_ctx Δ)
  | tapp t T => S (sz_tm t + sz_ty T)
  end
with sz_ctx (Γ : ctx) : nat :=
  match Γ with cnil | cvar _ => 1 | cext Γ A _ => S (sz_ctx Γ + sz_ty A) end
with sz_l (d : lsub) : nat :=
  match d with lshift _ => 1 | lcons d t => S (sz_l d + sz_tm t) end.

Lemma sz_llk d n : sz_tm (llk d n) <= sz_l d.
Proof. revert n; induction d as [k | d IH t]; intros [|n]; cbn; try lia. specialize (IH n); lia. Qed.

Lemma sz_tup f k n : forall j, k <= j -> j < k + n -> sz_tm (f j) < sz_tm (tup_from f k n).
Proof.
  revert k; induction n as [|n IH]; intros k j Hj Hj'; [lia |]. cbn [tup_from sz_tm].
  destruct (Nat.eq_dec j k) as [-> | N]; [lia | specialize (IH (S k) j ltac:(lia) ltac:(lia)); lia].
Qed.

Lemma sz_wrap nu ng nl b : sz_tm b <= sz_tm (wrap nu ng nl b).
Proof.
  unfold wrap. induction nu as [|nu IH]; cbn; [| lia].
  induction ng as [|ng IHg]; cbn; [| lia]. induction nl as [|nl IHl]; cbn; lia.
Qed.

Lemma sz_mkrb MT Mt bs : sz_ty MT < sz_tm (mkrb MT Mt bs) /\ sz_ty Mt < sz_tm (mkrb MT Mt bs) /\
  forall k, k < 13 -> sz_tm (bs k) < sz_tm (mkrb MT Mt bs).
Proof.
  rewrite mkrb_as. unfold wrapMT, wrapMt. cbn [sz_tm]. split; [lia | split; [lia |]].
  intros k Hk. pose proof (sz_tup (wrap_br bs) 0 13 k ltac:(lia) ltac:(lia)) as X.
  assert (Y : sz_tm (bs k) <= sz_tm (wrap_br bs k))
    by (unfold wrap_br; destruct (br_ar k) as [[nu ng] nl]; apply sz_wrap).
  lia.
Qed.
