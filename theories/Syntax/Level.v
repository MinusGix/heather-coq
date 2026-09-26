(** * Universe levels (ch. 4 §"Universe Levels")

    [l ::= ℓ | 0 | 1+l | l ⊔ l' | ω], with de Bruijn level variables.

    Equivalence and order are defined SEMANTICALLY: by evaluation under every
    valuation of the level variables (see M1_DESIGN.md).  The paper's
    algebraic rules are lemmas.  Evaluation with every variable at 0 is a
    well-founded measure for the logical relation's recursion on levels. *)
From Coq Require Export Arith Lia List.

Inductive lvl : Type :=
| lvar (n : nat)
| lzero
| lsuc (l : lvl)
| lmax (l l' : lvl)
| lomega.

Fixpoint leval (v : nat -> nat) (l : lvl) : nat :=
  match l with
  | lvar n => v n
  | lzero => 0
  | lsuc l => S (leval v l)
  | lmax l l' => Nat.max (leval v l) (leval v l')
  | lomega => 0          (* ω is never evaluated: it is not well-formed *)
  end.

(** [L ⊢ l : Level]: variables bound in the universe context, no ω. *)
Fixpoint lwf (L : nat) (l : lvl) : Prop :=
  match l with
  | lvar n => n < L
  | lzero => True
  | lsuc l => lwf L l
  | lmax l l' => lwf L l /\ lwf L l'
  | lomega => False
  end.

(** [L ⊢ l ≈ l' : Level] *)
Definition lequiv (L : nat) (l l' : lvl) : Prop :=
  lwf L l /\ lwf L l' /\ forall v, leval v l = leval v l'.

(** [l < l'] *)
Definition llt (L : nat) (l l' : lvl) : Prop :=
  lwf L l /\ lwf L l' /\ forall v, leval v l < leval v l'.

Definition lmeasure (l : lvl) : nat := leval (fun _ => 0) l.

(** ** Equivalence is a PER, reflexive on well-formed levels *)

Lemma lequiv_refl L l : lwf L l -> lequiv L l l.
Proof. repeat split; auto. Qed.
Lemma lequiv_sym L l l' : lequiv L l l' -> lequiv L l' l.
Proof. intros (? & ? & H); repeat split; auto. Qed.
Lemma lequiv_trans L l l' l'' : lequiv L l l' -> lequiv L l' l'' -> lequiv L l l''.
Proof. intros (? & ? & H) (? & ? & H'); repeat split; auto. intros v; now rewrite H. Qed.
Lemma lequiv_wf_l L l l' : lequiv L l l' -> lwf L l.
Proof. now intros []. Qed.
Lemma lequiv_wf_r L l l' : lequiv L l l' -> lwf L l'.
Proof. now intros (? & ? & ?). Qed.

(** ** The paper's congruence and algebraic rules *)

Lemma lequiv_suc L l l' : lequiv L l l' -> lequiv L (lsuc l) (lsuc l').
Proof. intros (? & ? & H); repeat split; auto. intros v; cbn; auto. Qed.
Lemma lequiv_max L l1 l2 l3 l4 :
  lequiv L l1 l2 -> lequiv L l3 l4 -> lequiv L (lmax l1 l3) (lmax l2 l4).
Proof. intros (? & ? & H) (? & ? & H'); repeat split; auto. intros v; cbn; auto. Qed.

Ltac lalg := repeat split; cbn; auto; intros; lia.

Lemma lmax_zero L l : lwf L l -> lequiv L (lmax l lzero) l.
Proof. lalg. Qed.
Lemma lmax_assoc L l l' l'' : lwf L l -> lwf L l' -> lwf L l'' ->
  lequiv L (lmax (lmax l l') l'') (lmax l (lmax l' l'')).
Proof. lalg. Qed.
Lemma lmax_comm L l l' : lwf L l -> lwf L l' -> lequiv L (lmax l l') (lmax l' l).
Proof. lalg. Qed.
Lemma lmax_idem L l : lwf L l -> lequiv L (lmax l l) l.
Proof. lalg. Qed.
Lemma lsuc_max L l l' : lwf L l -> lwf L l' ->
  lequiv L (lsuc (lmax l l')) (lmax (lsuc l) (lsuc l')).
Proof. lalg. Qed.
Lemma lvar_absorb L n : n < L -> lequiv L (lmax (lvar n) (lsuc (lvar n))) (lsuc (lvar n)).
Proof. lalg. Qed.

(** ** Order *)

Lemma llt_suc L l : lwf L l -> llt L l (lsuc l).
Proof. repeat split; auto; intros; cbn; lia. Qed.
Lemma llt_equiv_r L l l' l'' : llt L l l' -> lequiv L l' l'' -> llt L l l''.
Proof. intros (? & ? & H) (? & ? & H'); repeat split; auto. intros v; rewrite <- H'; auto. Qed.
Lemma llt_equiv_l L l l' l'' : lequiv L l l' -> llt L l' l'' -> llt L l l''.
Proof. intros (? & ? & H) (? & ? & H'); repeat split; auto. intros v; rewrite H; auto. Qed.

(** The measure: the logical relation recurses on it. *)
Lemma llt_measure L l l' : llt L l l' -> lmeasure l < lmeasure l'.
Proof. intros (_ & _ & H); apply H. Qed.
Lemma lequiv_measure L l l' : lequiv L l l' -> lmeasure l = lmeasure l'.
Proof. intros (_ & _ & H); apply H. Qed.

(** ** Weakening of the universe context *)

Lemma lwf_weaken L L' l : L <= L' -> lwf L l -> lwf L' l.
Proof. induction l; cbn; intuition lia. Qed.
Lemma lequiv_weaken L L' l l' : L <= L' -> lequiv L l l' -> lequiv L' l l'.
Proof. intros HL (? & ? & H); repeat split; eauto using lwf_weaken. Qed.

(** ** Universe renaming and substitution (M3)

    Level variables are de Bruijn indices ([lvar 0] is the most recently
    bound level); binders are introduced by the code recursors' branches
    (and later by [UΠ]). *)

Definition uupr (ρ : nat -> nat) : nat -> nat :=
  fun n => match n with 0 => 0 | S n => S (ρ n) end.

Fixpoint lvren (l : lvl) (ρ : nat -> nat) : lvl :=
  match l with
  | lvar n => lvar (ρ n)
  | lzero => lzero
  | lsuc l => lsuc (lvren l ρ)
  | lmax l l' => lmax (lvren l ρ) (lvren l' ρ)
  | lomega => lomega
  end.

Fixpoint lvsubst (l : lvl) (φ : nat -> lvl) : lvl :=
  match l with
  | lvar n => φ n
  | lzero => lzero
  | lsuc l => lsuc (lvsubst l φ)
  | lmax l l' => lmax (lvsubst l φ) (lvsubst l' φ)
  | lomega => lomega
  end.

(** [φ] under one level binder. *)
Definition uup (φ : nat -> lvl) : nat -> lvl :=
  fun n => match n with 0 => lvar 0 | S n => lvren (φ n) S end.

Lemma map_ext_id {A} (f : A -> A) ls : (forall x, f x = x) -> map f ls = ls.
Proof. intros H; induction ls; cbn; f_equal; auto. Qed.

(** Under [n] level binders. *)
Definition uuprn (n : nat) (ρ : nat -> nat) : nat -> nat := Nat.iter n uupr ρ.
Definition uupn (n : nat) (φ : nat -> lvl) : nat -> lvl := Nat.iter n uup φ.

(** [ls/ℓ⃗] on top of [φ]: the list's last element is index 0. *)
Definition uext (ls : list lvl) (φ : nat -> lvl) : nat -> lvl :=
  fun i => if i <? length ls then nth (length ls - S i) ls lzero else φ (i - length ls).

(** [l/ℓ]: instantiate the most recent level variable. *)
Definition usingle (l : lvl) : nat -> lvl :=
  fun n => match n with 0 => l | S n => lvar n end.

Lemma leval_lvren v l ρ : leval v (lvren l ρ) = leval (fun n => v (ρ n)) l.
Proof. induction l; cbn; auto. Qed.
Lemma leval_lvsubst v l φ : leval v (lvsubst l φ) = leval (fun n => leval v (φ n)) l.
Proof. induction l; cbn; auto. Qed.

Lemma lvren_ext l ρ ρ' : (forall n, ρ n = ρ' n) -> lvren l ρ = lvren l ρ'.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.
Lemma lvren_lvren l ρ ρ' ρ'' : (forall n, ρ'' n = ρ' (ρ n)) -> lvren (lvren l ρ) ρ' = lvren l ρ''.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.
Lemma lvsubst_ext l φ φ' : (forall n, φ n = φ' n) -> lvsubst l φ = lvsubst l φ'.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.
Lemma lvren_lvsubst l ρ φ φ' : (forall n, φ' n = φ (ρ n)) -> lvsubst (lvren l ρ) φ = lvsubst l φ'.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.
Lemma lvsubst_lvren l φ ρ φ' : (forall n, φ' n = lvren (φ n) ρ) -> lvren (lvsubst l φ) ρ = lvsubst l φ'.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.
Lemma lvsubst_lvsubst l φ ψ θ : (forall n, θ n = lvsubst (φ n) ψ) ->
  lvsubst (lvsubst l φ) ψ = lvsubst l θ.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.
Lemma lvren_id l ρ : (forall n, ρ n = n) -> lvren l ρ = l.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.
Lemma lvsubst_id l φ : (forall n, φ n = lvar n) -> lvsubst l φ = l.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.
Lemma lvren_as_lvsubst l ρ φ : (forall n, φ n = lvar (ρ n)) -> lvren l ρ = lvsubst l φ.
Proof. intros H; induction l; cbn; rewrite ?H; congruence. Qed.

Lemma uupr_ext ρ ρ' : (forall n, ρ n = ρ' n) -> forall n, uupr ρ n = uupr ρ' n.
Proof. intros H [|n]; cbn; auto. Qed.
Lemma uupr_comp ρ ρ' ρ'' : (forall n, ρ'' n = ρ' (ρ n)) -> forall n, uupr ρ'' n = uupr ρ' (uupr ρ n).
Proof. intros H [|n]; cbn; auto. Qed.
Lemma uupr_id ρ : (forall n, ρ n = n) -> forall n, uupr ρ n = n.
Proof. intros H [|n]; cbn; auto. Qed.
Lemma uup_ext φ φ' : (forall n, φ n = φ' n) -> forall n, uup φ n = uup φ' n.
Proof. intros H [|n]; cbn; auto. now rewrite H. Qed.
Lemma uup_uupr ρ φ φ' : (forall n, φ' n = φ (ρ n)) -> forall n, uup φ' n = uup φ (uupr ρ n).
Proof. intros H [|n]; cbn; auto. now rewrite H. Qed.
Lemma uup_lvren φ ρ φ' : (forall n, φ' n = lvren (φ n) ρ) ->
  forall n, uup φ' n = lvren (uup φ n) (uupr ρ).
Proof.
  intros H [|n]; cbn; auto. rewrite H, !(lvren_lvren _ _ _ (fun m => S (ρ m))); auto.
Qed.
Lemma uup_lvsubst φ ψ θ : (forall n, θ n = lvsubst (φ n) ψ) ->
  forall n, uup θ n = lvsubst (uup φ n) (uup ψ).
Proof.
  intros H [|n]; cbn; auto. rewrite H.
  rewrite (lvsubst_lvren _ _ _ (fun m => lvren (ψ m) S)) by auto.
  symmetry; apply lvren_lvsubst; auto.
Qed.
Lemma uup_id φ : (forall n, φ n = lvar n) -> forall n, uup φ n = lvar n.
Proof. intros H [|n]; cbn; auto. now rewrite H. Qed.
Lemma uup_as ρ φ : (forall n, φ n = lvar (ρ n)) -> forall n, uup φ n = lvar (uupr ρ n).
Proof. intros H [|n]; cbn; auto. now rewrite H. Qed.

(** Under [k] binders (M4: the n-ary binder of [UΠ]). *)
Lemma uuprn_ext k ρ ρ' : (forall n, ρ n = ρ' n) -> forall n, uuprn k ρ n = uuprn k ρ' n.
Proof. intros H; unfold uuprn; induction k; [assumption | apply uupr_ext; assumption]. Qed.
Lemma uuprn_comp k ρ ρ' ρ'' : (forall n, ρ'' n = ρ' (ρ n)) ->
  forall n, uuprn k ρ'' n = uuprn k ρ' (uuprn k ρ n).
Proof. intros H; unfold uuprn; induction k; [assumption | apply uupr_comp; assumption]. Qed.
Lemma uuprn_id k ρ : (forall n, ρ n = n) -> forall n, uuprn k ρ n = n.
Proof. intros H; unfold uuprn; induction k; [assumption | apply uupr_id; assumption]. Qed.
Lemma uupn_ext k φ φ' : (forall n, φ n = φ' n) -> forall n, uupn k φ n = uupn k φ' n.
Proof. intros H; unfold uupn; induction k; [assumption | apply uup_ext; assumption]. Qed.
Lemma uupn_uuprn k ρ φ φ' : (forall n, φ' n = φ (ρ n)) -> forall n, uupn k φ' n = uupn k φ (uuprn k ρ n).
Proof. intros H; unfold uupn, uuprn; induction k; [assumption | apply uup_uupr; assumption]. Qed.
Lemma uupn_lvren k φ ρ φ' : (forall n, φ' n = lvren (φ n) ρ) ->
  forall n, uupn k φ' n = lvren (uupn k φ n) (uuprn k ρ).
Proof. intros H; unfold uupn, uuprn; induction k; [assumption | apply uup_lvren; assumption]. Qed.
Lemma uupn_lvsubst k φ ψ θ : (forall n, θ n = lvsubst (φ n) ψ) ->
  forall n, uupn k θ n = lvsubst (uupn k φ n) (uupn k ψ).
Proof. intros H; unfold uupn; induction k; [assumption | apply uup_lvsubst; assumption]. Qed.
Lemma uupn_id k φ : (forall n, φ n = lvar n) -> forall n, uupn k φ n = lvar n.
Proof. intros H; unfold uupn; induction k; [assumption | apply uup_id; assumption]. Qed.
Lemma uupn_as k ρ φ : (forall n, φ n = lvar (ρ n)) -> forall n, uupn k φ n = lvar (uuprn k ρ n).
Proof. intros H; unfold uupn, uuprn; induction k; [assumption | apply uup_as; assumption]. Qed.

(** ** Typed universe renamings and substitutions: [φ : L' ⇒ L] *)

Definition uren_ok (ρ : nat -> nat) (L' L : nat) : Prop := forall n, n < L -> ρ n < L'.
Definition usub_ok (φ : nat -> lvl) (L' L : nat) : Prop := forall n, n < L -> lwf L' (φ n).

Lemma lwf_lvren L L' l ρ : uren_ok ρ L' L -> lwf L l -> lwf L' (lvren l ρ).
Proof. intros H; induction l; cbn; intuition. Qed.
Lemma lwf_lvsubst L L' l φ : usub_ok φ L' L -> lwf L l -> lwf L' (lvsubst l φ).
Proof. intros H; induction l; cbn; intuition. Qed.
Lemma lequiv_lvren L L' l l' ρ : uren_ok ρ L' L -> lequiv L l l' -> lequiv L' (lvren l ρ) (lvren l' ρ).
Proof.
  intros H (? & ? & E); repeat split; eauto using lwf_lvren.
  intros v; rewrite !leval_lvren; apply E.
Qed.
Lemma lequiv_lvsubst L L' l l' φ : usub_ok φ L' L -> lequiv L l l' ->
  lequiv L' (lvsubst l φ) (lvsubst l' φ).
Proof.
  intros H (? & ? & E); repeat split; eauto using lwf_lvsubst.
  intros v; rewrite !leval_lvsubst; apply E.
Qed.
Lemma llt_lvsubst L L' l l' φ : usub_ok φ L' L -> llt L l l' -> llt L' (lvsubst l φ) (lvsubst l' φ).
Proof.
  intros H (? & ? & E); repeat split; eauto using lwf_lvsubst.
  intros v; rewrite !leval_lvsubst; apply E.
Qed.

Lemma uren_ok_S L : uren_ok S (S L) L.
Proof. intros n; lia. Qed.
Lemma uren_ok_uupr ρ L' L : uren_ok ρ L' L -> uren_ok (uupr ρ) (S L') (S L).
Proof. intros H [|n] Hn; cbn; [lia|]. specialize (H n); lia. Qed.
Lemma usub_ok_uup φ L' L : usub_ok φ L' L -> usub_ok (uup φ) (S L') (S L).
Proof.
  intros H [|n] Hn; cbn; [lia|]. apply (lwf_lvren L'); [apply uren_ok_S | apply H; lia].
Qed.
Lemma usub_ok_single L l : lwf L l -> usub_ok (usingle l) L (S L).
Proof. intros H [|n] Hn; cbn; auto. lia. Qed.
Lemma usub_ok_id L : usub_ok lvar L L.
Proof. intros n Hn; exact Hn. Qed.
Lemma usub_ok_ren ρ L' L : uren_ok ρ L' L -> usub_ok (fun n => lvar (ρ n)) L' L.
Proof. intros H n Hn; cbn; auto. Qed.

(** ** Level growth: an equivalent level mentions only the variables it
    must (M3_DESIGN.md E14). Worlds may add levels at the top; a level of
    the grown context equivalent to one of the base context is itself
    well formed in the base context. *)

Lemma lwf_dec L l : {lwf L l} + {~ lwf L l}.
Proof.
  induction l as [n| |l IH|l IH l' IH'|]; cbn.
  - apply lt_dec.
  - left; exact I.
  - exact IH.
  - destruct IH, IH'; tauto.
  - right; tauto.
Qed.

Lemma leval_ext_lwf L l v v' : lwf L l -> (forall n, n < L -> v n = v' n) -> leval v l = leval v' l.
Proof. intros Hl Hv; induction l; cbn in *; intuition. Qed.

Lemma lwf_var_escape L L' l : lwf L' l -> ~ lwf L l -> exists y, L <= y /\ forall v, v y <= leval v l.
Proof.
  induction l as [n| |l IH|l IH l' IH'|]; cbn; intros H1 H2.
  - exists n; split; [lia | auto].
  - tauto.
  - destruct (IH H1 H2) as (y & Hy & Hv). exists y; split; [exact Hy | intros v; specialize (Hv v); lia].
  - destruct (lwf_dec L l) as [Hl|Hl].
    + destruct (IH' (proj2 H1) (fun H => H2 (conj Hl H))) as (y & Hy & Hv).
      exists y; split; [exact Hy | intros v; specialize (Hv v); lia].
    + destruct (IH (proj1 H1) Hl) as (y & Hy & Hv).
      exists y; split; [exact Hy | intros v; specialize (Hv v); lia].
  - tauto.
Qed.

Lemma lequiv_shrink L L' l l' : lequiv L' l l' -> lwf L l' -> lequiv L l l'.
Proof.
  intros (H1 & H2 & H) Hl'. repeat split; [| exact Hl' | exact H].
  destruct (lwf_dec L l) as [Hl|Hl]; [exact Hl|exfalso].
  destruct (lwf_var_escape L L' l H1 Hl) as (y & Hy & Hv).
  set (v := fun n => if Nat.eqb n y then S (lmeasure l') else 0).
  specialize (Hv v). rewrite (H v) in Hv.
  rewrite (leval_ext_lwf L l' v (fun _ => 0) Hl') in Hv.
  - unfold v in Hv. rewrite Nat.eqb_refl in Hv. unfold lmeasure in Hv. lia.
  - intros n Hn. unfold v. destruct (Nat.eqb_spec n y); [lia | reflexivity].
Qed.

(** ** Level permutations (M3_DESIGN.md E14): bijections of the level
    variables that fix every variable from [L] up. *)

Definition uperm (π πi : nat -> nat) (L : nat) : Prop :=
  (forall n, πi (π n) = n) /\ (forall n, π (πi n) = n) /\
  (forall n, n < L -> π n < L) /\ (forall n, L <= n -> π n = n).

Lemma uperm_inv π πi L : uperm π πi L -> uperm πi π L.
Proof.
  intros (H1 & H2 & H3 & H4). repeat split; auto.
  - intros n Hn. destruct (lt_dec (πi n) L) as [Hlt|Hge]; [exact Hlt|].
    rewrite <- (H2 n), (H4 (πi n)) in Hn by lia. lia.
  - intros n Hn. rewrite <- (H4 n Hn) at 1. apply H1.
Qed.

Lemma uperm_grow π πi L L' : L <= L' -> uperm π πi L -> uperm π πi L'.
Proof.
  intros HL (H1 & H2 & H3 & H4). repeat split; auto.
  - intros n Hn. destruct (lt_dec n L); [specialize (H3 n); lia | rewrite H4; lia].
  - intros n Hn; apply H4; lia.
Qed.

Lemma uperm_ok π πi L : uperm π πi L -> uren_ok π L L.
Proof. intros (_ & _ & H & _); exact H. Qed.

Lemma lvren_uperm_inv π πi L l : uperm π πi L -> lvren (lvren l π) πi = l.
Proof. intros (H1 & _); rewrite (lvren_lvren l π πi (fun n => n)) by auto; apply lvren_id; auto. Qed.

(** Lift a level fact of a smaller universe context: [lup H] with
    [H : L <= L']. *)
Ltac lup H :=
  match goal with
  | |- lwf _ _ => eapply lwf_weaken; [exact H | first [eassumption | eauto using lequiv_wf_l, lequiv_wf_r]]
  | |- lequiv _ _ _ => eapply lequiv_weaken; [exact H | first [eassumption | eauto using lequiv_sym]]
  end.
