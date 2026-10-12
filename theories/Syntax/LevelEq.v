(** * Level equivalence of syntax: its laws (M3_DESIGN.md E11)

    [≡ₗ] ([LevelEqDef]) is an equivalence and every syntactic operation
    respects it, given related arguments. The laws are split over
    [LevelEqBase] (levels, reflexivity, lookups) and, on top of it and
    building in parallel, [LevelEqSym], [LevelEqTrans], [LevelEqRen],
    [LevelEqURen] and [LevelEqSubst]: each is a syntax induction of a few
    seconds, and in one file they took 80 s of the critical path. *)
From DeLaM.Syntax Require Export LevelEqSym LevelEqTrans LevelEqSubst.

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
