(** * Universe levels (ch. 4 §"Universe Levels")

    [l ::= ℓ | 0 | 1+l | l ⊔ l' | ω], with de Bruijn level variables.

    Equivalence and order are defined SEMANTICALLY: by evaluation under every
    valuation of the level variables (see M1_DESIGN.md).  The paper's
    algebraic rules are lemmas.  Evaluation with every variable at 0 is a
    well-founded measure for the logical relation's recursion on levels. *)
From Coq Require Import Arith Lia.

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

(** Levels do not mention local or global variables. Level substitution
    (for universe polymorphism) arrives with [UΠ]. *)
