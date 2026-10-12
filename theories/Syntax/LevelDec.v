(** * Decidability of level equivalence (M6_DESIGN.md H3)

    [leqv] is semantic (equal evaluation under every valuation). A level
    evaluates to [max c (max_x (v x + k_x))], where [k_x] is the offset of
    the variable [x] ([loff]) and [c] the value at the zero valuation. So
    two levels are equivalent iff they agree at the zero valuation and have
    the same offsets, which is decidable as only finitely many variables
    occur. Then [≡ₗ] on syntax is decided structurally.

    Decidability is stated in [Prop] (M6_DESIGN.md H1). *)
From DeLaM.Syntax Require Export LevelEq.

Definition Dec (P : Prop) : Prop := P \/ ~ P.

Lemma dec_and {P Q} : Dec P -> Dec Q -> Dec (P /\ Q).
Proof. unfold Dec; tauto. Qed.
Lemma dec_True : Dec True. Proof. now left. Qed.
Lemma dec_False : Dec False. Proof. now right. Qed.
Lemma dec_nat_eq (n m : nat) : Dec (n = m).
Proof. destruct (Nat.eq_dec n m); [left|right]; auto. Qed.
Lemma dec_iff {P Q} : (P <-> Q) -> Dec P -> Dec Q.
Proof. unfold Dec; tauto. Qed.

Lemma dec_forall_lt (P : nat -> Prop) : (forall x, Dec (P x)) ->
  forall n, Dec (forall x, x < n -> P x).
Proof.
  intros HP n; induction n as [|n IH].
  - left; intros x Hx; lia.
  - destruct IH as [IH|IH].
    + destruct (HP n) as [Hn|Hn].
      * left; intros x Hx. destruct (Nat.eq_dec x n); [subst; exact Hn | apply IH; lia].
      * right; intros H; apply Hn, H; lia.
    + right; intros H; apply IH; intros x Hx; apply H; lia.
Qed.

(** ** The normal form of a level *)

Definition omax (a b : option nat) : option nat :=
  match a, b with
  | Some a, Some b => Some (Nat.max a b)
  | Some a, None => Some a
  | None, b => b
  end.

(** The offset of the variable [x] in [l], if it occurs. *)
Fixpoint loff (l : lvl) (x : nat) : option nat :=
  match l with
  | lvar n => if Nat.eqb n x then Some 0 else None
  | lzero | lomega => None
  | lsuc l => option_map S (loff l x)
  | lmax l l' => omax (loff l x) (loff l' x)
  end.

(** The largest [v x + k_x], if some variable occurs. *)
Fixpoint lvm (v : nat -> nat) (l : lvl) : option nat :=
  match l with
  | lvar n => Some (v n)
  | lzero | lomega => None
  | lsuc l => option_map S (lvm v l)
  | lmax l l' => omax (lvm v l) (lvm v l')
  end.

Definition lz : nat -> nat := fun _ => 0.

Definition odflt (a : option nat) : nat := match a with Some a => a | None => 0 end.

Lemma leval_split v l : leval v l = Nat.max (leval lz l) (odflt (lvm v l)).
Proof.
  induction l as [n| |l IH|l1 IH1 l2 IH2|]; cbn; try lia.
  - rewrite IH; destruct (lvm v l); cbn; lia.
  - rewrite IH1, IH2; destruct (lvm v l1), (lvm v l2); cbn; lia.
Qed.

Lemma lvm_none v l x : lvm v l = None -> loff l x = None.
Proof.
  induction l as [n| |l IH|l1 IH1 l2 IH2|]; cbn; intros H; try discriminate; auto.
  - destruct (lvm v l); cbn in H; [discriminate|]. now rewrite IH.
  - destruct (lvm v l1), (lvm v l2); cbn in H; try discriminate. now rewrite IH1, IH2.
Qed.

Lemma lvm_of_loff v l x k : loff l x = Some k -> exists m, lvm v l = Some m.
Proof.
  intros H; destruct (lvm v l) as [m|] eqn:E; eauto.
  rewrite (lvm_none _ _ x E) in H; discriminate.
Qed.

(** Case analysis on the [omax]/[option_map] of hypotheses. *)
Ltac odestr := repeat match goal with
  | H : context [ lvm ?v ?l ] |- _ =>
      lazymatch type of H with lvm _ _ = _ => fail | _ => idtac end;
      let E := fresh "E" in destruct (lvm v l) eqn:E; cbn in H
  | H : context [ loff ?l ?x ] |- _ =>
      lazymatch type of H with loff _ _ = _ => fail | _ => idtac end;
      let E := fresh "F" in destruct (loff l x) eqn:E; cbn in H
  end; try discriminate;
  repeat match goal with H : Some _ = Some _ |- _ => injection H as H end; subst.

Lemma lvm_ub v l m : lvm v l = Some m -> forall x k, loff l x = Some k -> v x + k <= m.
Proof.
  revert m; induction l as [n| |l IH|l1 IH1 l2 IH2|]; cbn; intros m Hm x k Hk;
    try discriminate.
  - destruct (Nat.eqb_spec n x); [subst|discriminate]. injection Hm; injection Hk; lia.
  - odestr. specialize (IH _ eq_refl _ _ F). lia.
  - odestr;
      repeat match goal with
      | IH : forall m, Some _ = Some m -> forall x k, loff ?l x = Some k -> _,
        F : loff ?l x = Some _ |- _ => specialize (IH _ eq_refl _ _ F)
      | E : lvm v ?l = None, F : loff ?l x = Some _ |- _ =>
          rewrite (lvm_none _ _ x E) in F; discriminate
      end; lia.
Qed.

Lemma lvm_attained v l m : lvm v l = Some m -> exists x k, loff l x = Some k /\ m = v x + k.
Proof.
  revert m; induction l as [n| |l IH|l1 IH1 l2 IH2|]; cbn; intros m Hm; try discriminate.
  - exists n, 0. rewrite Nat.eqb_refl. injection Hm; split; [reflexivity|lia].
  - odestr. destruct (IH _ eq_refl) as (x & k & Hk & ->). exists x, (S k). rewrite Hk; split; [reflexivity|lia].
  - odestr.
    + destruct (IH1 _ eq_refl) as (x1 & k1 & Hk1 & ->), (IH2 _ eq_refl) as (x2 & k2 & Hk2 & ->).
      destruct (Nat.le_ge_cases (v x1 + k1) (v x2 + k2)).
      * exists x2. destruct (loff l1 x2) as [k1'|] eqn:F.
        -- exists (Nat.max k1' k2). rewrite Hk2; split; [reflexivity|].
           pose proof (lvm_ub _ _ _ E _ _ F). lia.
        -- exists k2. rewrite Hk2; split; [reflexivity|lia].
      * exists x1. destruct (loff l2 x1) as [k2'|] eqn:F.
        -- exists (Nat.max k1 k2'). rewrite Hk1; split; [reflexivity|].
           pose proof (lvm_ub _ _ _ E0 _ _ F). lia.
        -- exists k1. rewrite Hk1; split; [reflexivity|lia].
    + destruct (IH1 _ eq_refl) as (x & k & Hk & ->). exists x, k.
      rewrite Hk, (lvm_none _ _ x E0); split; reflexivity.
    + destruct (IH2 _ eq_refl) as (x & k & Hk & ->). exists x, k.
      rewrite Hk, (lvm_none _ _ x E); split; reflexivity.
Qed.

(** Levels with the same offsets have the same [lvm]. *)
Lemma lvm_loff v l l' : (forall x, loff l x = loff l' x) -> lvm v l = lvm v l'.
Proof.
  intros H. destruct (lvm v l) as [m|] eqn:E, (lvm v l') as [m'|] eqn:E'.
  - f_equal. apply Nat.le_antisymm.
    + destruct (lvm_attained _ _ _ E) as (x & k & Hk & ->).
      apply (lvm_ub _ _ _ E'); now rewrite <- H.
    + destruct (lvm_attained _ _ _ E') as (x & k & Hk & ->).
      apply (lvm_ub _ _ _ E); now rewrite H.
  - destruct (lvm_attained _ _ _ E) as (x & k & Hk & _).
    rewrite H, (lvm_none _ _ x E') in Hk; discriminate.
  - destruct (lvm_attained _ _ _ E') as (x & k & Hk & _).
    rewrite <- H, (lvm_none _ _ x E) in Hk; discriminate.
  - reflexivity.
Qed.

(** Evaluation at the valuation that is [N] at [x] and 0 elsewhere. *)
Definition lpt (x N : nat) : nat -> nat := fun y => if Nat.eqb y x then N else 0.

Lemma leval_lpt l x N : leval (lpt x N) l =
  match loff l x with Some k => Nat.max (leval lz l) (N + k) | None => leval lz l end.
Proof.
  induction l as [n| |l IH|l1 IH1 l2 IH2|]; cbn [leval loff]; try reflexivity.
  - unfold lpt, lz; destruct (Nat.eqb_spec n x); cbn; lia.
  - rewrite IH; destruct (loff l x); cbn [option_map]; lia.
  - rewrite IH1, IH2; destruct (loff l1 x), (loff l2 x); cbn [omax]; lia.
Qed.

Lemma leqv_iff l l' : leqv l l' <-> leval lz l = leval lz l' /\ forall x, loff l x = loff l' x.
Proof.
  split.
  - intros H; split; [apply H|]. intros x.
    set (N := S (leval lz l + leval lz l')).
    pose proof (H (lpt x N)) as Hx. rewrite !leval_lpt in Hx.
    pose proof (H lz) as H0.
    destruct (loff l x), (loff l' x); f_equal; subst N; lia.
  - intros (H0 & H) v. rewrite (leval_split v l), (leval_split v l'), H0, (lvm_loff v l l' H).
    reflexivity.
Qed.

(** Variables at or above [lbnd l] don't occur in [l]. *)
Fixpoint lbnd (l : lvl) : nat :=
  match l with
  | lvar n => S n
  | lzero | lomega => 0
  | lsuc l => lbnd l
  | lmax l l' => Nat.max (lbnd l) (lbnd l')
  end.

Lemma loff_lbnd l x : lbnd l <= x -> loff l x = None.
Proof.
  induction l as [n| |l IH|l1 IH1 l2 IH2|]; cbn; intros Hx; try reflexivity.
  - destruct (Nat.eqb_spec n x); [lia|reflexivity].
  - rewrite IH; [reflexivity|lia].
  - rewrite IH1, IH2; [reflexivity|lia|lia].
Qed.

Lemma dec_option_nat_eq (a b : option nat) : Dec (a = b).
Proof.
  destruct a as [a|], b as [b|]; try (right; discriminate); [|now left].
  destruct (Nat.eq_dec a b); [left; congruence | right; congruence].
Qed.

Lemma leqv_dec l l' : Dec (leqv l l').
Proof.
  eapply dec_iff; [symmetry; apply leqv_iff|].
  apply dec_and; [apply dec_nat_eq|].
  eapply dec_iff; [|apply (dec_forall_lt (fun x => loff l x = loff l' x) (fun x => dec_option_nat_eq _ _)
                             (Nat.max (lbnd l) (lbnd l')))].
  split.
  - intros H x. destruct (Nat.lt_ge_cases x (Nat.max (lbnd l) (lbnd l'))); [now apply H|].
    rewrite !loff_lbnd by lia; reflexivity.
  - intros H x _; apply H.
Qed.

Lemma lequiv_dec L l l' : Dec (lequiv L l l').
Proof.
  unfold lequiv. apply dec_and; [|apply dec_and]; [..|apply leqv_dec];
    destruct (lwf_dec L l), (lwf_dec L l'); unfold Dec; tauto.
Qed.

(** ** Level equivalence of syntax *)

Lemma leqvs_dec ls ls' : Dec (Forall2 leqv ls ls').
Proof.
  revert ls'; induction ls as [|l ls IH]; intros [|l' ls'].
  - left; constructor.
  - right; intros H; inversion H.
  - right; intros H; inversion H.
  - destruct (leqv_dec l l') as [H1|H1]; [destruct (IH ls') as [H2|H2]|].
    + left; constructor; auto.
    + right; intros H; inversion H; auto.
    + right; intros H; inversion H; auto.
Qed.

Ltac dec_solve := repeat apply dec_and;
  first [ apply dec_True | apply dec_False | apply leqv_dec | apply leqvs_dec
        | apply dec_nat_eq | eauto ].

Lemma leq_dec_all :
  (forall T T', Dec (ty_leq T T')) /\ (forall t t', Dec (tm_leq t t')) /\
  (forall Γ Γ', Dec (ctx_leq Γ Γ')) /\ (forall d d', Dec (lsub_leq d d')).
Proof.
  apply syn_ind; intros;
    match goal with |- Dec (_ _ ?x) => destruct x end; try exact dec_False; cbn; dec_solve.
Qed.

Lemma ty_leq_dec T T' : Dec (ty_leq T T'). Proof. apply leq_dec_all. Qed.
Lemma tm_leq_dec t t' : Dec (tm_leq t t'). Proof. apply leq_dec_all. Qed.
Lemma ctx_leq_dec Γ Γ' : Dec (ctx_leq Γ Γ'). Proof. apply leq_dec_all. Qed.
Lemma lsub_leq_dec d d' : Dec (lsub_leq d d'). Proof. apply leq_dec_all. Qed.
