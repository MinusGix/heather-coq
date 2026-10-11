(** * Level equivalence of syntax: its laws (M3_DESIGN.md E11)

    [≡ₗ] ([LevelEqDef]) is an equivalence and every syntactic operation
    respects it, given related arguments. *)
From DeLaM.Syntax Require Export LevelEqDef.

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

Lemma leq_sym_all :
  let Pty T := forall T', ty_leq T T' -> ty_leq T' T in
  let Ptm t := forall t', tm_leq t t' -> tm_leq t' t in
  let Pctx Γ := forall Γ', ctx_leq Γ Γ' -> ctx_leq Γ' Γ in
  let Pl d := forall d', lsub_leq d d' -> lsub_leq d' d in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Lemma leq_trans_all :
  let Pty T := forall T' T'', ty_leq T T' -> ty_leq T' T'' -> ty_leq T T'' in
  let Ptm t := forall t' t'', tm_leq t t' -> tm_leq t' t'' -> tm_leq t t'' in
  let Pctx Γ := forall Γ' Γ'', ctx_leq Γ Γ' -> ctx_leq Γ' Γ'' -> ctx_leq Γ Γ'' in
  let Pl d := forall d' d'', lsub_leq d d' -> lsub_leq d' d'' -> lsub_leq d d'' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof.
  leq_start; repeat leq_cases; cbn in *; try contradiction;
    intuition (subst; eauto using leqv_trans, leqvs_trans).
Qed.

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

(** ** Operations *)

Lemma leq_ren_all :
  let Pty T := forall T' r, ty_leq T T' -> ty_leq (ren_ty T r) (ren_ty T' r) in
  let Ptm t := forall t' r, tm_leq t t' -> tm_leq (ren_tm t r) (ren_tm t' r) in
  let Pctx (Γ : ctx) := True in
  let Pl d := forall d' r, lsub_leq d d' -> lsub_leq (lren d r) (lren d' r) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try exact I; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Lemma leq_gren_all :
  let Pty T := forall T' ξ, ty_leq T T' -> ty_leq (gren_ty T ξ) (gren_ty T' ξ) in
  let Ptm t := forall t' ξ, tm_leq t t' -> tm_leq (gren_tm t ξ) (gren_tm t' ξ) in
  let Pctx Γ := forall Γ' ξ, ctx_leq Γ Γ' -> ctx_leq (gcren Γ ξ) (gcren Γ' ξ) in
  let Pl d := forall d' ξ, lsub_leq d d' -> lsub_leq (glren d ξ) (glren d' ξ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Lemma leq_uren_all :
  let Pty T := forall T' ρ, ty_leq T T' -> ty_leq (uren_ty T ρ) (uren_ty T' ρ) in
  let Ptm t := forall t' ρ, tm_leq t t' -> tm_leq (uren_tm t ρ) (uren_tm t' ρ) in
  let Pctx Γ := forall Γ' ρ, ctx_leq Γ Γ' -> ctx_leq (ucren Γ ρ) (ucren Γ' ρ) in
  let Pl d := forall d' ρ, lsub_leq d d' -> lsub_leq (ulren d ρ) (ulren d' ρ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Lemma leq_usubst_all :
  let Pty T := forall T' φ φ', (forall n, leqv (φ n) (φ' n)) -> ty_leq T T' ->
    ty_leq (usubst_ty T φ) (usubst_ty T' φ') in
  let Ptm t := forall t' φ φ', (forall n, leqv (φ n) (φ' n)) -> tm_leq t t' ->
    tm_leq (usubst_tm t φ) (usubst_tm t' φ') in
  let Pctx Γ := forall Γ' φ φ', (forall n, leqv (φ n) (φ' n)) -> ctx_leq Γ Γ' ->
    ctx_leq (ucsubst Γ φ) (ucsubst Γ' φ') in
  let Pl d := forall d' φ φ', (forall n, leqv (φ n) (φ' n)) -> lsub_leq d d' ->
    lsub_leq (ulsubst d φ) (ulsubst d' φ') in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Definition leq_ren_tm t := proj1 (proj2 leq_ren_all) t.
Definition leq_gren_tm t := proj1 (proj2 leq_gren_all) t.
Definition leq_uren_tm t := proj1 (proj2 leq_uren_all) t.
Lemma leq_llift d d' : lsub_leq d d' -> lsub_leq (llift d) (llift d').
Proof. intros H; unfold llift; apply lcons'_leq; [apply (proj2 (proj2 (proj2 leq_ren_all))), H | reflexivity]. Qed.
Lemma leq_gwk d d' : lsub_leq d d' -> lsub_leq (gwk d) (gwk d').
Proof. intros H; apply (proj2 (proj2 (proj2 leq_gren_all))), H. Qed.
Lemma leq_uwk d d' : lsub_leq d d' -> lsub_leq (uwk d) (uwk d').
Proof. intros H; apply (proj2 (proj2 (proj2 leq_uren_all))), H. Qed.
Lemma leq_uwkn k d d' : lsub_leq d d' -> lsub_leq (uwkn k d) (uwkn k d').
Proof. intros H; unfold uwkn; induction k; [assumption | apply leq_uwk; assumption]. Qed.
#[export] Hint Resolve leq_llift leq_gwk leq_uwk leq_uwkn : leq.

Lemma leq_subst_all :
  let Pty T := forall T' d d', lsub_leq d d' -> ty_leq T T' -> ty_leq (subst_ty T d) (subst_ty T' d') in
  let Ptm t := forall t' d d', lsub_leq d d' -> tm_leq t t' -> tm_leq (subst_tm t d) (subst_tm t' d') in
  let Pctx (Γ : ctx) := True in
  let Pl e := forall e' d d', lsub_leq d d' -> lsub_leq e e' -> lsub_leq (lcomp e d) (lcomp e' d') in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try exact I; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Lemma gobj_leq_goren o o' ξ : gobj_leq o o' -> gobj_leq (goren o ξ) (goren o' ξ).
Proof.
  destruct o, o'; cbn; try contradiction; intros H; subst; auto;
    first [apply (proj1 (proj2 (proj2 leq_gren_all))) | apply (proj1 leq_gren_all) | apply (proj1 (proj2 leq_gren_all))];
    exact H.
Qed.
Lemma gobj_leq_gouren o o' ρ : gobj_leq o o' -> gobj_leq (gouren o ρ) (gouren o' ρ).
Proof.
  destruct o, o'; cbn; try contradiction; intros H; subst; auto;
    first [apply (proj1 (proj2 (proj2 leq_uren_all))) | apply (proj1 leq_uren_all) | apply (proj1 (proj2 leq_uren_all))];
    exact H.
Qed.
Lemma gobj_leq_gup σ σ' : (forall i, gobj_leq (σ i) (σ' i)) -> forall i, gobj_leq (gup σ i) (gup σ' i).
Proof. intros H [|i]; cbn; [reflexivity | apply gobj_leq_goren, H]. Qed.
Lemma gobj_leq_guwk σ σ' : (forall i, gobj_leq (σ i) (σ' i)) -> forall i, gobj_leq (guwk σ i) (guwk σ' i).
Proof. intros H i; apply gobj_leq_gouren, H. Qed.
Lemma pty_leq o o' d d' : gobj_leq o o' -> lsub_leq d d' -> ty_leq (pty o d) (pty o' d').
Proof.
  destruct o, o'; cbn; try contradiction; intros H Hd; subst; cbn; auto;
    apply (proj1 leq_subst_all); assumption.
Qed.
Lemma ptm_leq o o' d d' : gobj_leq o o' -> lsub_leq d d' -> tm_leq (ptm o d) (ptm o' d').
Proof.
  destruct o, o'; cbn; try contradiction; intros H Hd; subst; cbn; auto;
    apply (proj1 (proj2 leq_subst_all)); assumption.
Qed.
Lemma pdef_leq o o' b b' d d' : gobj_leq o o' -> tm_leq b b' -> lsub_leq d d' ->
  tm_leq (pdef o b d) (pdef o' b' d').
Proof.
  intros H Hb Hd. destruct o, o'; cbn in H; try contradiction; subst; cbn; auto;
    apply (proj1 (proj2 leq_subst_all)); assumption.
Qed.
Lemma pctx_leq o o' : gobj_leq o o' -> ctx_leq (pctx o) (pctx o').
Proof. destruct o, o'; cbn; try contradiction; intros H; subst; auto. Qed.
Lemma gobj_leq_guwkn k σ σ' : (forall i, gobj_leq (σ i) (σ' i)) -> forall i, gobj_leq (guwkn k σ i) (guwkn k σ' i).
Proof. intros H; unfold guwkn; induction k; [assumption | apply gobj_leq_guwk; assumption]. Qed.
#[export] Hint Resolve gobj_leq_gup gobj_leq_guwk gobj_leq_guwkn pty_leq ptm_leq pdef_leq pctx_leq : leq.

Lemma leq_gsubst_all :
  let Pty T := forall T' σ σ', (forall i, gobj_leq (σ i) (σ' i)) -> ty_leq T T' ->
    ty_leq (gsubst_ty T σ) (gsubst_ty T' σ') in
  let Ptm t := forall t' σ σ', (forall i, gobj_leq (σ i) (σ' i)) -> tm_leq t t' ->
    tm_leq (gsubst_tm t σ) (gsubst_tm t' σ') in
  let Pctx Γ := forall Γ' σ σ', (forall i, gobj_leq (σ i) (σ' i)) -> ctx_leq Γ Γ' ->
    ctx_leq (gcsubst Γ σ) (gcsubst Γ' σ') in
  let Pl d := forall d' σ σ', (forall i, gobj_leq (σ i) (σ' i)) -> lsub_leq d d' ->
    lsub_leq (glsubst d σ) (glsubst d' σ') in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

(** ** Notation-level corollaries *)

Lemma ty_leq_sym T T' : ty_leq T T' -> ty_leq T' T. Proof. apply leq_sym_all. Qed.
Lemma tm_leq_sym t t' : tm_leq t t' -> tm_leq t' t. Proof. apply leq_sym_all. Qed.
Lemma ty_leq_trans T1 T2 T3 : ty_leq T1 T2 -> ty_leq T2 T3 -> ty_leq T1 T3. Proof. apply leq_trans_all. Qed.
Lemma tm_leq_trans t1 t2 t3 : tm_leq t1 t2 -> tm_leq t2 t3 -> tm_leq t1 t3. Proof. apply leq_trans_all. Qed.
Lemma gobj_leq_refl o : gobj_leq o o.
Proof. destruct o; cbn; auto using ctx_leq_refl, ty_leq_refl, tm_leq_refl. Qed.
#[export] Hint Resolve ty_leq_refl tm_leq_refl ctx_leq_refl lsub_leq_refl gobj_leq_refl : leq.

(** ** Well-formed level annotations

    [x] has every level annotation well formed in [L]. With [≡ₗ], this
    gives level equivalence of the annotations ([leqv_lequiv]). *)

Fixpoint ty_lwf (L : nat) (T : ty) {struct T} : Prop :=
  match T with
  | tyErr | tyNat => True
  | tyPi l1 l2 A B | tySig l1 l2 A B | tySum l1 l2 A B | tyW l1 l2 A B =>
      lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ ty_lwf L B
  | tyU l | tyUnit l | tySEmpty l | tyEmpty l => lwf L l
  | tyVec l A n => lwf L l /\ ty_lwf L A /\ tm_lwf L n
  | tyFin n => tm_lwf L n
  | tyWf l A N => lwf L l /\ ty_lwf L A /\ tm_lwf L N
  | tySq l A => lwf L l /\ ty_lwf L A
  | tySEq l A a b => lwf L l /\ ty_lwf L A /\ tm_lwf L a /\ tm_lwf L b
  | tyId l A a b => lwf L l /\ ty_lwf L A /\ tm_lwf L a /\ tm_lwf L b
  | tyEl l t => lwf L l /\ tm_lwf L t
  | tyGvar _ d => lsub_lwf L d
  | tyCTyp Δ l => ctx_lwf L Δ /\ lwf L l
  | tyCTrm Δ A l => ctx_lwf L Δ /\ ty_lwf L A /\ lwf L l
  | tyUPi n l A => lwf (n + L) l /\ ty_lwf (n + L) A
  | tyCPi l A => lwf L l /\ ty_lwf L A
  | tyTPi Δ l1 l2 A => ctx_lwf L Δ /\ lwf L l1 /\ lwf L l2 /\ ty_lwf L A
  end
with tm_lwf (L : nat) (t : tm) {struct t} : Prop :=
  match t with
  | var _ | tmErr | tmNat | zero => True
  | tmPi l1 l2 s t | tmSig l1 l2 s t | tmSum l1 l2 s t | tmW l1 l2 s t => lwf L l1 /\ lwf L l2 /\ tm_lwf L s /\ tm_lwf L t
  | tmVec l s n => lwf L l /\ tm_lwf L s /\ tm_lwf L n
  | tmFin n => tm_lwf L n
  | tmWf l s n => lwf L l /\ tm_lwf L s /\ tm_lwf L n
  | tmU l | tmUnit l | tmTriv l | tmSEmpty l | tmEmpty l => lwf L l
  | srefl l A a => lwf L l /\ ty_lwf L A /\ tm_lwf L a
  | tmRefl l A a => lwf L l /\ ty_lwf L A /\ tm_lwf L a
  | tmId l s t u => lwf L l /\ tm_lwf L s /\ tm_lwf L t /\ tm_lwf L u
  | tmSEq l s t u => lwf L l /\ tm_lwf L s /\ tm_lwf L t /\ tm_lwf L u
  | tmJ l1 l2 A a M c u e =>
      lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ tm_lwf L a /\ ty_lwf L M /\
      tm_lwf L c /\ tm_lwf L u /\ tm_lwf L e
  | elimSEmpty l1 l2 M e => lwf L l1 /\ lwf L l2 /\ ty_lwf L M /\ tm_lwf L e
  | elimEmpty l1 l2 M e => lwf L l1 /\ lwf L l2 /\ ty_lwf L M /\ tm_lwf L e
  | tmInl l1 l2 A B a | tmInr l1 l2 A B a => lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ ty_lwf L B /\ tm_lwf L a
  | tmSup l1 l2 A B a f => lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ ty_lwf L B /\ tm_lwf L a /\ tm_lwf L f
  | tmElimW l1 l2 l3 A B M c t => lwf L l1 /\ lwf L l2 /\ lwf L l3 /\ ty_lwf L A /\ ty_lwf L B /\
      ty_lwf L M /\ tm_lwf L c /\ tm_lwf L t
  | tmSupf l A N a cs => lwf L l /\ ty_lwf L A /\ tm_lwf L N /\ tm_lwf L a /\ tm_lwf L cs
  | tmElimWf l1 l2 A N M c t => lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ tm_lwf L N /\
      ty_lwf L M /\ tm_lwf L c /\ tm_lwf L t
  | tmSq l A a => lwf L l /\ ty_lwf L A /\ tm_lwf L a
  | tmElimSq l1 l2 A M c t => lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ ty_lwf L M /\ tm_lwf L c /\ tm_lwf L t
  | tmCase l1 l2 l3 A B M c1 c2 t => lwf L l1 /\ lwf L l2 /\ lwf L l3 /\ ty_lwf L A /\ ty_lwf L B /\
      ty_lwf L M /\ tm_lwf L c1 /\ tm_lwf L c2 /\ tm_lwf L t
  | succ t => tm_lwf L t
  | natrec l M s z t => lwf L l /\ ty_lwf L M /\ tm_lwf L s /\ tm_lwf L z /\ tm_lwf L t
  | lam l1 l2 A t => lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ tm_lwf L t
  | app t l1 l2 A B s => tm_lwf L t /\ lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ ty_lwf L B /\ tm_lwf L s
  | gvar _ d => lsub_lwf L d
  | gdef _ b d => tm_lwf L b /\ lsub_lwf L d
  | boxT T => ty_lwf L T
  | boxt t => tm_lwf L t
  | letboxT l1 l2 Δ M t1 t => lwf L l1 /\ lwf L l2 /\ ctx_lwf L Δ /\ ty_lwf L M /\ tm_lwf L t1 /\ tm_lwf L t
  | letboxt l1 l2 Δ A M t1 t =>
      lwf L l1 /\ lwf L l2 /\ ctx_lwf L Δ /\ ty_lwf L A /\ ty_lwf L M /\ tm_lwf L t1 /\ tm_lwf L t
  | tmTy T => ty_lwf L T
  | tmTup s t => tm_lwf L s /\ tm_lwf L t
  | bindU b => tm_lwf (S L) b
  | bindG b | bindL b => tm_lwf L b
  | elimT l1 l2 rb l Δ t => lwf L l1 /\ lwf L l2 /\ tm_lwf L rb /\ lwf L l /\ ctx_lwf L Δ /\ tm_lwf L t
  | elimt l1 l2 rb l Δ A t =>
      lwf L l1 /\ lwf L l2 /\ tm_lwf L rb /\ lwf L l /\ ctx_lwf L Δ /\ ty_lwf L A /\ tm_lwf L t
  | ulam n l T t => lwf (n + L) l /\ ty_lwf (n + L) T /\ tm_lwf (n + L) t
  | uapp t ls => tm_lwf L t /\ Forall (lwf L) ls
  | clam l T t => lwf L l /\ ty_lwf L T /\ tm_lwf L t
  | capp t Δ => tm_lwf L t /\ ctx_lwf L Δ
  | tlam Δ l1 l2 T t => ctx_lwf L Δ /\ lwf L l1 /\ lwf L l2 /\ ty_lwf L T /\ tm_lwf L t
  | tapp t A => tm_lwf L t /\ ty_lwf L A
  | tmPair l1 l2 A B a b => lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ ty_lwf L B /\ tm_lwf L a /\ tm_lwf L b
  | tmFst l1 l2 A B p | tmSnd l1 l2 A B p =>
      lwf L l1 /\ lwf L l2 /\ ty_lwf L A /\ ty_lwf L B /\ tm_lwf L p
  end
with ctx_lwf (L : nat) (Γ : ctx) {struct Γ} : Prop :=
  match Γ with
  | cnil | cvar _ => True
  | cext Γ A l => ctx_lwf L Γ /\ ty_lwf L A /\ lwf L l
  end
with lsub_lwf (L : nat) (d : lsub) {struct d} : Prop :=
  match d with lshift _ => True | lcons d t => lsub_lwf L d /\ tm_lwf L t end.

Lemma llk_lwf L d n : lsub_lwf L d -> tm_lwf L (llk d n).
Proof. revert n; induction d as [k | d IH t]; intros [|n] H; cbn in *; tauto || apply IH; tauto. Qed.

(** [≡ₗ] preserves deep normality (which never looks at levels). *)
Lemma leq_labsorb d d' t t' : lsub_leq d d' -> tm_leq t t' -> labsorb d t -> labsorb d' t'.
Proof.
  intros Hd Ht H. destruct d as [[|k] | d0 t0]; cbn in H; try contradiction.
  destruct d' as [k' | d0' t0']; cbn in Hd; try contradiction. subst k'.
  destruct t; cbn in H; try contradiction. destruct t'; cbn in Ht; try contradiction.
  cbn; congruence.
Qed.

Lemma leq_dnf_all :
  let Pty T := forall T', ty_leq T T' -> dnfty T -> dnfty T' in
  let Ptm t := forall t', tm_leq t t' -> dnftm t -> dnftm t' in
  let Pctx Γ := forall Γ', ctx_leq Γ Γ' -> dnfctx Γ -> dnfctx Γ' in
  let Pl d := forall d', lsub_leq d d' -> dnfl d -> dnfl d' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof.
  leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto using leq_sym_all).
  match goal with
  | H : labsorb ?d' ?t', Hn : labsorb ?d ?t -> False, Hd : lsub_leq ?d ?d', Ht : tm_leq ?t ?t' |- False =>
      exact (Hn (leq_labsorb _ _ _ _ (proj2 (proj2 (proj2 leq_sym_all)) _ _ Hd)
                   (proj1 (proj2 leq_sym_all) _ _ Ht) H))
  end.
Qed.
