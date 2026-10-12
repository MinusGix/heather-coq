(** * Level equivalence of syntax: levels, reflexivity and lookups

    One of the parts [LevelEq] puts together; they build in parallel. *)
From DeLaM.Syntax Require Export LevelEqDef GSubst.

(** ** Levels *)

Lemma leqv_refl l : leqv l l.
Proof. intros v; reflexivity. Qed.
Lemma leqv_sym l l' : leqv l l' -> leqv l' l.
Proof. intros H v; symmetry; apply H. Qed.
Lemma leqv_trans l1 l2 l3 : leqv l1 l2 -> leqv l2 l3 -> leqv l1 l3.
Proof. intros H H' v; rewrite H; apply H'. Qed.

Lemma leval_ext v v' l : (forall n, v n = v' n) -> leval v l = leval v' l.
Proof. intros H; induction l; cbn; auto. Qed.

Lemma leqv_lvren l l' ρ : leqv l l' -> leqv (lvren l ρ) (lvren l' ρ).
Proof. intros H v; rewrite !leval_lvren; apply H. Qed.
Lemma leqv_lvsubst l l' φ φ' : leqv l l' -> (forall n, leqv (φ n) (φ' n)) ->
  leqv (lvsubst l φ) (lvsubst l' φ').
Proof.
  intros H Hφ v; rewrite !leval_lvsubst, H. apply leval_ext; intros n; apply Hφ.
Qed.
Lemma leqv_uup φ φ' : (forall n, leqv (φ n) (φ' n)) -> forall n, leqv (uup φ n) (uup φ' n).
Proof. intros H [|n]; cbn; [apply leqv_refl | apply leqv_lvren, H]. Qed.

Lemma lequiv_leqv L l l' : lequiv L l l' -> leqv l l'.
Proof. intros (_ & _ & H); exact H. Qed.
Lemma leqv_lequiv L l l' : lwf L l -> lwf L l' -> leqv l l' -> lequiv L l l'.
Proof. intros; repeat split; auto. Qed.

Lemma leqv_uupn k φ φ' : (forall n, leqv (φ n) (φ' n)) -> forall n, leqv (uupn k φ n) (uupn k φ' n).
Proof. intros H; unfold uupn; induction k; [assumption | apply leqv_uup; assumption]. Qed.

(** Level lists (the arguments of [uapp]), pointwise. *)
Lemma leqvs_refl ls : Forall2 leqv ls ls.
Proof. induction ls; constructor; auto using leqv_refl. Qed.
Lemma leqvs_sym ls ls' : Forall2 leqv ls ls' -> Forall2 leqv ls' ls.
Proof. induction 1; constructor; auto using leqv_sym. Qed.
Lemma leqvs_trans ls1 ls2 ls3 : Forall2 leqv ls1 ls2 -> Forall2 leqv ls2 ls3 -> Forall2 leqv ls1 ls3.
Proof.
  intros H; revert ls3; induction H; intros ls3 H'; inversion H'; subst; constructor;
    eauto using leqv_trans.
Qed.
Lemma leqvs_lvren ls ls' ρ : Forall2 leqv ls ls' ->
  Forall2 leqv (map (fun l => lvren l ρ) ls) (map (fun l => lvren l ρ) ls').
Proof. induction 1; cbn; constructor; auto using leqv_lvren. Qed.
Lemma leqvs_lvsubst ls ls' φ φ' : Forall2 leqv ls ls' -> (forall n, leqv (φ n) (φ' n)) ->
  Forall2 leqv (map (fun l => lvsubst l φ) ls) (map (fun l => lvsubst l φ') ls').
Proof. induction 1; cbn; constructor; auto using leqv_lvsubst. Qed.

#[export] Hint Resolve leqv_refl leqv_sym leqv_lvren leqv_lvsubst leqv_uup leqv_uupn : leq.
#[export] Hint Resolve leqvs_refl leqvs_sym leqvs_lvren leqvs_lvsubst : leq.

(** ** Equivalence *)

Ltac leq_start := intros ?Pty ?Ptm ?Pctx ?Pl; apply syn_ind; subst Pty Ptm Pctx Pl; cbn beta; intros.
(** Case on the right-hand side of a relation hypothesis. The mismatched
    formers are closed by conversion before [cbn], which then runs on one
    goal instead of one per former. *)
Ltac leq_cases := match goal with
  | H : ty_leq ?y ?x |- _ => is_var x; tryif is_var y then fail else (destruct x; try exact (False_ind _ H); cbn in H)
  | H : tm_leq ?y ?x |- _ => is_var x; tryif is_var y then fail else (destruct x; try exact (False_ind _ H); cbn in H)
  | H : ctx_leq ?y ?x |- _ => is_var x; tryif is_var y then fail else (destruct x; try exact (False_ind _ H); cbn in H)
  | H : lsub_leq ?y ?x |- _ => is_var x; tryif is_var y then fail else (destruct x; try exact (False_ind _ H); cbn in H)
  end.

Lemma leq_refl_all :
  let Pty T := ty_leq T T in let Ptm t := tm_leq t t in
  let Pctx Γ := ctx_leq Γ Γ in let Pl d := lsub_leq d d in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; cbn; intuition auto with leq. Qed.

Lemma ty_leq_refl T : ty_leq T T. Proof. apply leq_refl_all. Qed.
Lemma tm_leq_refl t : tm_leq t t. Proof. apply leq_refl_all. Qed.
Lemma ctx_leq_refl Γ : ctx_leq Γ Γ. Proof. apply leq_refl_all. Qed.
Lemma lsub_leq_refl d : lsub_leq d d. Proof. apply leq_refl_all. Qed.
#[export] Hint Resolve ty_leq_refl tm_leq_refl ctx_leq_refl lsub_leq_refl : leq.

(** ** Lookups and smart constructors *)

Lemma llk_leq d d' n : lsub_leq d d' -> tm_leq (llk d n) (llk d' n).
Proof.
  revert d' n; induction d as [k | d IH t]; intros [k' | d' t'] n H; cbn in H |- *; try contradiction.
  - subst; reflexivity.
  - destruct H as [Hd Ht]; destruct n; [exact Ht | exact (IH _ _ Hd)].
Qed.

Lemma lcons'_leq d d' t t' : lsub_leq d d' -> tm_leq t t' -> lsub_leq (lcons' d t) (lcons' d' t').
Proof.
  intros Hd Ht. destruct d as [k | d0 t0], d' as [k' | d0' t0']; cbn in Hd; try contradiction.
  - subst k'. destruct k as [|k]; [cbn; tauto|].
    destruct t; leq_cases; cbn; try tauto.
    subst. destruct (Nat.eqb _ k); cbn; tauto.
  - cbn; tauto.
Qed.

Lemma lnorm_leq d d' : lsub_leq d d' -> lsub_leq (lnorm d) (lnorm d').
Proof.
  revert d'; induction d as [k | d IH t]; intros [k' | d' t'] H; cbn in H |- *; try contradiction; auto.
  destruct H; apply lcons'_leq; auto.
Qed.

Lemma ldrop_leq k d d' : lsub_leq d d' -> lsub_leq (ldrop k d) (ldrop k d').
Proof.
  revert d d'; induction k; intros d d' H; cbn; auto.
  destruct d, d'; cbn in H |- *; try contradiction; [subst; reflexivity | apply IHk; tauto].
Qed.

#[export] Hint Resolve llk_leq lcons'_leq lnorm_leq ldrop_leq : leq.
