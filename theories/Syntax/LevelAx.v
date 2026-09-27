(** * The paper's level equivalence (04:251), complete (M7_DESIGN.md C3 K3)

    The paper axiomatises [L ⊢ l ≈ l' : Level]: the PER rules, congruence
    for [1+] and [⊔], and six algebraic rules. Ours ([lequiv], Level.v) is
    semantic: equal evaluation under every valuation. They coincide on
    well-formed levels:
    - soundness: each axiom is one of Level.v's lemmas;
    - completeness: every well-formed [l] is axiomatically equal to the
      normal form [nf (leval lz l) (loff l)] (the paper's
      [flatten (adjust (count l))], 04:410, without dropping a redundant
      constant), whose data [leqv] determines (LevelDec.v, [leqv_iff]).
    The well-formedness judgment is [lwf] in both (04:229). *)
From DeLaM.Syntax Require Export LevelDec.

Inductive leqP (L : nat) : lvl -> lvl -> Prop :=
| leqP_refl l : lwf L l -> leqP L l l
| leqP_sym l l' : leqP L l l' -> leqP L l' l
| leqP_trans l l' l'' : leqP L l l' -> leqP L l' l'' -> leqP L l l''
| leqP_suc l l' : leqP L l l' -> leqP L (lsuc l) (lsuc l')
| leqP_max l1 l2 l3 l4 : leqP L l1 l2 -> leqP L l3 l4 -> leqP L (lmax l1 l3) (lmax l2 l4)
| leqP_max_zero l : lwf L l -> leqP L (lmax l lzero) l
| leqP_assoc l l' l'' : lwf L l -> lwf L l' -> lwf L l'' ->
    leqP L (lmax (lmax l l') l'') (lmax l (lmax l' l''))
| leqP_comm l l' : lwf L l -> lwf L l' -> leqP L (lmax l l') (lmax l' l)
| leqP_idem l : lwf L l -> leqP L (lmax l l) l
| leqP_suc_max l l' : lwf L l -> lwf L l' ->
    leqP L (lsuc (lmax l l')) (lmax (lsuc l) (lsuc l'))
| leqP_absorb n : n < L -> leqP L (lmax (lvar n) (lsuc (lvar n))) (lsuc (lvar n)).

(** ** Soundness, and presupposition (04:306) *)

Lemma leqP_lequiv L l l' : leqP L l l' -> lequiv L l l'.
Proof.
  induction 1; eauto using lequiv_refl, lequiv_sym, lequiv_trans, lequiv_suc, lequiv_max,
    lmax_zero, lmax_assoc, lmax_comm, lmax_idem, lsuc_max, lvar_absorb.
Qed.

Lemma leqP_wf_l L l l' : leqP L l l' -> lwf L l.
Proof. intros H; exact (lequiv_wf_l _ _ _ (leqP_lequiv _ _ _ H)). Qed.
Lemma leqP_wf_r L l l' : leqP L l l' -> lwf L l'.
Proof. intros H; exact (lequiv_wf_r _ _ _ (leqP_lequiv _ _ _ H)). Qed.

(** ** Completeness *)

Fixpoint sucn (k : nat) (l : lvl) : lvl :=
  match k with 0 => l | S k => lsuc (sucn k l) end.

Lemma sucn_add a b l : sucn (a + b) l = sucn a (sucn b l).
Proof. induction a; cbn; congruence. Qed.
Lemma lwf_sucn L k l : lwf L (sucn k l) <-> lwf L l.
Proof. induction k; cbn; tauto. Qed.

(** A variable [x] with offset [k] is the atom [k + x]; an absent one is [0]. *)
Definition atom (x : nat) (o : option nat) : lvl :=
  match o with Some k => sucn k (lvar x) | None => lzero end.

Fixpoint nfv (n : nat) (f : nat -> option nat) : lvl :=
  match n with
  | 0 => lzero
  | S n => lmax (nfv n f) (atom n (f n))
  end.

Lemma nfv_ext n f g : (forall x, x < n -> f x = g x) -> nfv n f = nfv n g.
Proof. induction n; cbn; intros H; [reflexivity|]. rewrite IHn, H by (intros; apply H; lia) || lia; reflexivity. Qed.

Section Complete.
Variable L : nat.
Local Notation "a ≈ b" := (leqP L a b) (at level 70).

Definition nf (c : nat) (f : nat -> option nat) : lvl := lmax (sucn c lzero) (nfv L f).

Lemma lwf_atom x o : x < L -> lwf L (atom x o).
Proof. intros Hx; destruct o; cbn; [apply lwf_sucn; cbn|]; auto. Qed.
Lemma lwf_nfv n f : n <= L -> lwf L (nfv n f).
Proof. induction n; cbn; intros; [exact I | split; [apply IHn | apply lwf_atom]]; lia. Qed.
Lemma lwf_nf c f : lwf L (nf c f).
Proof. split; [apply lwf_sucn; exact I | apply lwf_nfv; lia]. Qed.

(** Lemmas are applied by goal shape: [sucn ?k ?l] unifies with any level. *)
Ltac wf := repeat first
  [ assumption | exact I | progress cbn [lwf]
  | match goal with
    | |- lwf _ (sucn _ _) => apply lwf_sucn
    | |- lwf _ (nf _ _) => apply lwf_nf
    | |- lwf _ (atom _ _) => apply lwf_atom
    | |- lwf _ (nfv _ _) => apply lwf_nfv
    end
  | split
  | match goal with H : _ ≈ _ |- _ => apply leqP_wf_l in H || apply leqP_wf_r in H end
  | lia ].

Local Hint Constructors leqP : core.

Lemma lr l : lwf L l -> l ≈ l. Proof. auto. Qed.
Lemma tr l' l l'' : l ≈ l' -> l' ≈ l'' -> l ≈ l''. Proof. eauto. Qed.
Lemma max_l a a' b : a ≈ a' -> lwf L b -> lmax a b ≈ lmax a' b. Proof. auto. Qed.
Lemma max_r a b b' : lwf L a -> b ≈ b' -> lmax a b ≈ lmax a b'. Proof. auto. Qed.

Lemma zero_max a : lwf L a -> lmax lzero a ≈ a.
Proof. intros; apply (tr (lmax a lzero)); [apply leqP_comm; [exact I|] | apply leqP_max_zero]; auto. Qed.

Lemma medial a b c d : lwf L a -> lwf L b -> lwf L c -> lwf L d ->
  lmax (lmax a b) (lmax c d) ≈ lmax (lmax a c) (lmax b d).
Proof.
  intros. apply (tr (lmax a (lmax b (lmax c d)))); [apply leqP_assoc; wf|].
  apply (tr (lmax a (lmax (lmax b c) d))); [apply max_r; [wf | apply leqP_sym, leqP_assoc; wf]|].
  apply (tr (lmax a (lmax (lmax c b) d))); [apply max_r, max_l; [wf | apply leqP_comm | ..]; wf|].
  apply (tr (lmax a (lmax c (lmax b d)))); [apply max_r; [wf | apply leqP_assoc; wf]|].
  apply leqP_sym, leqP_assoc; wf.
Qed.

Lemma sucn_cong k a a' : a ≈ a' -> sucn k a ≈ sucn k a'.
Proof. induction k; cbn; auto. Qed.

Lemma sucn_max k a b : lwf L a -> lwf L b -> sucn k (lmax a b) ≈ lmax (sucn k a) (sucn k b).
Proof.
  intros; induction k as [|k IH]; [cbn; auto|].
  apply (tr (lsuc (lmax (sucn k a) (sucn k b)))); [now apply leqP_suc|].
  apply leqP_suc_max; wf.
Qed.

(** The paper's second absorption lemma (04:335), from absorption at [l]. *)
Lemma absorbn l : lwf L l -> lmax l (lsuc l) ≈ lsuc l -> forall b, lmax l (sucn b l) ≈ sucn b l.
Proof.
  intros Hl H1 b; induction b as [|b IH]; [cbn; auto|].
  change (sucn (S b) l) with (lsuc (sucn b l)).
  assert (Hs : lsuc (sucn b l) ≈ lmax (lsuc l) (lsuc (sucn b l))).
  { apply (tr (lsuc (lmax l (sucn b l)))); [apply leqP_suc; auto|]. apply leqP_suc_max; wf. }
  apply (tr (lmax l (lmax (lsuc l) (lsuc (sucn b l))))); [apply max_r; wf|].
  apply (tr (lmax (lmax l (lsuc l)) (lsuc (sucn b l)))); [apply leqP_sym, leqP_assoc; wf|].
  apply (tr (lmax (lsuc l) (lsuc (sucn b l)))); [apply max_l; wf|].
  now apply leqP_sym.
Qed.

Lemma merge l a b : lwf L l -> lmax l (lsuc l) ≈ lsuc l ->
  lmax (sucn a l) (sucn b l) ≈ sucn (Nat.max a b) l.
Proof.
  intros Hl H1.
  assert (Hle : forall a d, lmax (sucn a l) (sucn (a + d) l) ≈ sucn (a + d) l).
  { intros a' d. rewrite sucn_add.
    apply (tr (sucn a' (lmax l (sucn d l)))); [apply leqP_sym, sucn_max; wf|].
    apply sucn_cong, absorbn; auto. }
  destruct (Nat.le_ge_cases a b) as [H|H].
  - replace (Nat.max a b) with (a + (b - a)) by lia. replace b with (a + (b - a)) at 1 by lia.
    apply Hle.
  - apply (tr (lmax (sucn b l) (sucn a l))); [apply leqP_comm; wf|].
    replace (Nat.max a b) with (b + (a - b)) by lia. replace a with (b + (a - b)) at 1 by lia.
    apply Hle.
Qed.

Lemma absorb_zero : lmax lzero (lsuc lzero) ≈ lsuc lzero.
Proof. apply zero_max; exact I. Qed.

Lemma atom_merge x o o' : x < L -> lmax (atom x o) (atom x o') ≈ atom x (omax o o').
Proof.
  intros Hx; destruct o, o'; cbn [atom omax]; try (apply merge; wf; auto).
  - apply leqP_max_zero; wf.
  - apply zero_max; wf.
  - apply leqP_max_zero; wf.
Qed.

Lemma nfv_none n : n <= L -> nfv n (fun _ => None) ≈ lzero.
Proof.
  induction n as [|n IHn]; cbn [nfv atom]; intros; [apply lr; exact I|].
  apply (tr (nfv n (fun _ => None))); [apply leqP_max_zero; wf | apply IHn; lia].
Qed.

Lemma nfv_var y n : y < L -> n <= L ->
  nfv n (loff (lvar y)) ≈ (if Nat.ltb y n then lvar y else lzero).
Proof.
  intros Hy; induction n as [|n IH]; cbn [nfv]; intros Hn; [apply lr; exact I|].
  cbn [loff atom]. destruct (Nat.eqb_spec y n) as [Heq|Hne].
  - subst y. rewrite (proj2 (Nat.ltb_ge n n)) in IH by lia. rewrite (proj2 (Nat.ltb_lt n (S n))) by lia.
    apply (tr (lmax lzero (lvar n))); [apply max_l; [apply IH; lia | wf]|]. apply zero_max; wf.
  - apply (tr (nfv n (loff (lvar y)))); [apply leqP_max_zero; wf|].
    apply (tr _ _ _ (IH ltac:(lia))).
    destruct (Nat.ltb_spec y n), (Nat.ltb_spec y (S n)); try lia; apply lr; wf.
Qed.

Lemma nfv_max n f g : n <= L -> lmax (nfv n f) (nfv n g) ≈ nfv n (fun x => omax (f x) (g x)).
Proof.
  induction n; cbn [nfv]; intros Hn; [apply leqP_max_zero; wf|].
  eapply tr; [apply medial; wf|].
  apply leqP_max; [apply IHn; lia | apply atom_merge; lia].
Qed.

Lemma nfv_suc n f : n <= L ->
  lsuc (nfv n f) ≈ lmax (lsuc lzero) (nfv n (fun x => option_map S (f x))).
Proof.
  induction n as [|n IH]; cbn [nfv]; intros Hn; [apply leqP_sym, leqP_max_zero; wf|].
  set (f' := fun x => option_map S (f x)).
  assert (Hw : lwf L (nfv n f')) by wf.
  apply (tr (lmax (lsuc (nfv n f)) (lsuc (atom n (f n))))); [apply leqP_suc_max; wf|].
  apply (tr (lmax (lmax (lsuc lzero) (nfv n f')) (lsuc (atom n (f n)))));
    [apply max_l; [apply IH; lia | wf]|].
  destruct (f n) as [k|] eqn:E; subst f'; cbn [atom option_map sucn].
  - apply leqP_assoc; wf.
  - apply (tr (lmax (lsuc lzero) (lmax (nfv n (fun x => option_map S (f x))) (lsuc lzero))));
      [apply leqP_assoc; wf|].
    apply (tr (lmax (lsuc lzero) (lmax (lsuc lzero) (nfv n (fun x => option_map S (f x))))));
      [apply max_r; [wf | apply leqP_comm; wf]|].
    apply (tr (lmax (lmax (lsuc lzero) (lsuc lzero)) (nfv n (fun x => option_map S (f x)))));
      [apply leqP_sym, leqP_assoc; wf|].
    apply leqP_max; [apply leqP_idem; wf | apply leqP_sym, leqP_max_zero; wf].
Qed.

Lemma leqP_nf l : lwf L l -> l ≈ nf (leval lz l) (loff l).
Proof.
  unfold nf; induction l as [y| |l IH|l1 IH1 l2 IH2|]; cbn [lwf]; intros Hl.
  - cbn [leval]. unfold lz; cbn [sucn].
    apply leqP_sym, (tr (nfv L (loff (lvar y)))); [apply zero_max; wf|].
    apply (tr _ _ _ (nfv_var y L Hl ltac:(lia))). rewrite (proj2 (Nat.ltb_lt y L)) by lia; auto.
  - cbn [leval sucn]. rewrite (nfv_ext _ _ (fun _ => None)) by reflexivity.
    apply leqP_sym, (tr (nfv L (fun _ => None))); [apply zero_max; wf|]. apply nfv_none; lia.
  - specialize (IH Hl). cbn [leval]. rewrite (nfv_ext _ (loff (lsuc l)) (fun x => option_map S (loff l x)))
      by reflexivity.
    set (f := loff l) in *; set (c := leval lz l) in *.
    apply (tr (lsuc (lmax (sucn c lzero) (nfv L f)))); [now apply leqP_suc|].
    apply (tr (lmax (lsuc (sucn c lzero)) (lsuc (nfv L f)))); [apply leqP_suc_max; wf|].
    apply (tr (lmax (lsuc (sucn c lzero)) (lmax (lsuc lzero) (nfv L (fun x => option_map S (f x))))));
      [apply max_r; [wf | apply nfv_suc; lia]|].
    apply (tr (lmax (lmax (lsuc (sucn c lzero)) (lsuc lzero)) (nfv L (fun x => option_map S (f x)))));
      [apply leqP_sym, leqP_assoc; wf|].
    apply max_l; [|wf].
    change (lmax (sucn (S c) lzero) (sucn 1 lzero) ≈ sucn (S c) lzero).
    replace (sucn (S c) lzero) with (sucn (Nat.max (S c) 1) lzero) at 2 by (f_equal; lia).
    apply merge; [exact I | apply absorb_zero].
  - destruct Hl as [Hl1 Hl2]. specialize (IH1 Hl1); specialize (IH2 Hl2). cbn [leval].
    rewrite (nfv_ext _ (loff (lmax l1 l2)) (fun x => omax (loff l1 x) (loff l2 x))) by reflexivity.
    apply (tr _ _ _ (leqP_max _ _ _ _ _ IH1 IH2)).
    eapply tr; [apply medial; wf|].
    apply leqP_max; [apply merge; [exact I | apply absorb_zero] | apply nfv_max; lia].
  - contradiction.
Qed.

End Complete.

Theorem lequiv_leqP L l l' : lequiv L l l' -> leqP L l l'.
Proof.
  intros (Hl & Hl' & H). apply leqv_iff in H as (Hc & Ho).
  apply (leqP_trans _ _ (nf L (leval lz l) (loff l))); [now apply leqP_nf|].
  unfold nf; rewrite Hc, (nfv_ext _ _ (loff l')) by (intros; apply Ho); fold (nf L (leval lz l') (loff l')).
  apply leqP_sym; now apply leqP_nf.
Qed.

Theorem leqP_iff L l l' : leqP L l l' <-> lequiv L l l'.
Proof. split; [apply leqP_lequiv | apply lequiv_leqP]. Qed.

(** Consequences: the paper's substitution lemma (04:392) and
    decidability (04:350), via the semantic side. *)
Lemma leqP_lvsubst L L' l l' φ : usub_ok φ L' L -> leqP L l l' ->
  leqP L' (lvsubst l φ) (lvsubst l' φ).
Proof. rewrite !leqP_iff; apply lequiv_lvsubst. Qed.

Lemma leqP_dec L l l' : Dec (leqP L l l').
Proof. eapply dec_iff; [symmetry; apply leqP_iff | apply lequiv_dec]. Qed.
