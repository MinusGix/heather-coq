(** * Closed canonicity at every type former (M7_DESIGN.md B1)

    For a global context of context variables only and the empty local
    context, at D and M; at D, also with definitions (M9, [closed_ok]):
    - a well-formed type reduces to a whnf type former, not a neutral one
      ([closed_type_canonicity]);
    - a typed term reduces to a value whose shape the type's head
      determines ([closed_canonicity], [canon_head]): a numeral constructor
      at [Nat], a code at a universe, [λ] at [Π], [box] at [□], [Λ] at
      [UΠ], a context or type abstraction at [CΠ]/[TΠ], a pair at [Σ], [⟨⟩]
      at [Unit], [srefl] at [sEq], and nothing at [sEmpty] (M10a), [refl] at
      [Id] (M11a), nothing at [Empty] (M12a) and an injection at [+]
      (M12b).

    Closed whnfs are not neutral ([no_closed_neutral]). A value's typing
    inversion equates its type with its canonical type former, and head
    discrimination ([decl_head_c]) identifies that former's head with the
    head of the type's whnf. *)
From DeLaM.Validity Require Export Consistency.

(** The values at a type head ([ty_head]). *)
Definition canon_head (h : nat) (w : tm) : Prop :=
  match h with
  | 1 => w = zero \/ exists t, w = succ t
  | 2 => w = tmNat \/ (exists l, w = tmU l) \/ (exists l l' s t, w = tmPi l l' s t) \/
         (exists l l' s t, w = tmSig l l' s t) \/ (exists l, w = tmUnit l) \/
         (exists l s t u, w = tmId l s t u) \/ (exists l s t u, w = tmSEq l s t u) \/
         (exists l, w = tmSEmpty l) \/ (exists l, w = tmEmpty l) \/ exists l l' s t, w = tmSum l l' s t
  | 3 => exists l l' A t, w = lam l l' A t
  | 4 => exists T, w = boxT T
  | 5 => exists t, w = boxt t
  | 6 => exists n l T t, w = ulam n l T t
  | 7 => exists l T t, w = clam l T t
  | 8 => exists Δ l l' T t, w = tlam Δ l l' T t
  | 10 => exists l l' A B a b, w = tmPair l l' A B a b
  | 11 => exists l, w = tmTriv l
  | 12 => exists l A a, w = srefl l A a
  | 14 => exists l A a, w = tmRefl l A a
  | 16 => (exists l l' A B a, w = tmInl l l' A B a) \/ exists l l' A B b, w = tmInr l l' A B b
  | _ => False
  end.

(** A value has the canonical shape of its whnf type. *)
Lemma value_canon {G i Γ w W k} : compt i -> whnf w -> ~ whne w -> whnf_ty W ->
  [ G ; Γ ⊢[ i ] w : W @ k ] -> canon_head (ty_head W) w.
Proof.
  intros Hc Hw Hn HW Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct Hw; [contradiction | ..];
    first [ pose proof (inv_code_nat Hi Hx) as X | pose proof (inv_code_U Hi Hx) as X
          | pose proof (inv_code_pi Hi Hx) as X | pose proof (inv_zero Hi Hx) as X
          | pose proof (inv_succ Hi Hx) as X | pose proof (inv_lam Hi Hx) as X
          | pose proof (inv_boxT Hi Hx) as X | pose proof (inv_boxt Hi Hx) as X
          | pose proof (inv_ulam Hi Hx) as X | pose proof (inv_clam Hi Hx) as X
          | pose proof (inv_tlam Hi Hx) as X
          | pose proof (inv_code_sig Hi Hx) as X | pose proof (inv_pair Hi Hx) as X
          | pose proof (inv_code_unit Hi Hx) as X | pose proof (inv_triv Hi Hx) as X
          | pose proof (inv_srefl Hi Hx) as X | pose proof (inv_idrefl Hi Hx) as X
          | pose proof (inv_code_id Hi Hx) as X
          | pose proof (inv_code_seq Hi Hx) as X | pose proof (inv_code_sempty Hi Hx) as X
          | pose proof (inv_inl Hi Hx) as X | pose proof (inv_inr Hi Hx) as X
          | pose proof (inv_code_empty Hi Hx) as X | pose proof (inv_code_sum Hi Hx) as X ];
    repeat match goal with H : exists _, _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H end;
    match goal with E : [ _ ; _ ⊢[ _ ] W ≅ _ @ _ ] |- _ =>
      rewrite (decl_head_c Hc E HW); [| auto with whnf] end;
    cbn; eauto 16.
Qed.

(** ** Types *)

Theorem closed_type_canonicity {G i T k} : compt i -> closed_ok i G -> [ G ; cnil ⊢[ i ] T @ k ] ->
  exists W, reds_ty T W /\ whnf_ty W /\ ~ whne_ty W /\ [ G ; cnil ⊢[ i ] T ≅ W @ k ].
Proof.
  intros Hc HG HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (tgt_whnf Hc HT) as (W & Hr & Hw & E). exists W; split; [exact Hr | split; [exact Hw | split; [| exact E]]].
  pose proof (eqty_wf_r Hi E) as HW. intros Hn. destruct Hn as [U d | l ν Hν].
  - destruct (tyGvar_decl HW) as (Δ & i' & l' & Hin). exact (closed_ok_tyGvar HG Hin).
  - destruct (inv_ty_El HW) as ((_ & _ & Ht) & _). exact (no_closed_neutral_ok HG Ht Hν).
Qed.

(** ** Terms *)

Theorem closed_canonicity {G i t T k} : compt i -> closed_ok i G -> [ G ; cnil ⊢[ i ] t : T @ k ] ->
  exists W w, reds_ty T W /\ whnf_ty W /\ ~ whne_ty W /\
    reds t w /\ whnf w /\ ~ whne w /\ [ G ; cnil ⊢[ i ] t ≅ w : T @ k ] /\ canon_head (ty_head W) w.
Proof.
  intros Hc HG Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (closed_type_canonicity Hc HG (wf_tm_ty Hi Ht)) as (W & HrT & HW & HnW & E).
  destruct (tgt_whnf_tm i Hc Ht) as (w & Hr & Hw).
  pose proof (red_tm_sound Hc Ht Hr Hw) as Ew.
  assert (EW : [ G ; cnil ⊢[ typeof i ] W ≅ T @ k ]) by (rewrite Hi; exact (eqty_sym _ _ _ _ _ _ E)).
  pose proof (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Ew) EW) as Hw0.
  assert (Hn : ~ whne w) by exact (no_closed_neutral_ok HG Hw0).
  exists W, w. repeat split; try assumption. exact (value_canon Hc Hw Hn HW Hw0).
Qed.

(** At a type already in whnf, the value's shape is read off the type
    itself; [cbn] on [canon_head (ty_head T) w] gives it. *)
Corollary closed_canonicity_whnf {G i t T k} : compt i -> closed_ok i G -> whnf_ty T ->
  [ G ; cnil ⊢[ i ] t : T @ k ] ->
  exists w, reds t w /\ whnf w /\ [ G ; cnil ⊢[ i ] t ≅ w : T @ k ] /\ canon_head (ty_head T) w.
Proof.
  intros Hc HG HwT Ht.
  destruct (closed_canonicity Hc HG Ht) as (W & w & HrT & HW & _ & Hr & Hw & _ & E & C).
  rewrite <- (reds_ty_whnf_det _ _ _ (Relation_Operators.rt1n_refl _ _ _) HrT HwT HW) in C.
  exists w; repeat split; assumption.
Qed.

(** ** Strict equality (M10a) *)

Lemma seq_inj_c {G i Γ l l1 l2 A A' a a' b b'} : compt i ->
  [ G ; Γ ⊢[ i ] tySEq l1 A a b ≅ tySEq l2 A' a' b' @ l ] ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\
  [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] /\ [ G ; Γ ⊢[ i ] b ≅ b' : A @ l1 ].
Proof. intros Hc H. destruct Hc as [-> | ->]; [exact (decl_seq_inj H) | exact (declM_seq_inj H)]. Qed.

(** No closed proof of [sEmpty]: its canonical head admits no value. *)
Corollary closed_sempty_empty {G i t l k} : compt i -> closed_ok i G ->
  ~ [ G ; cnil ⊢[ i ] t : tySEmpty l @ k ].
Proof.
  intros Hc HG Ht. destruct (closed_canonicity_whnf Hc HG (whnf_tySEmpty _) Ht) as (w & _ & _ & _ & C).
  exact C.
Qed.

(** No closed term of [Empty] (M12a): its canonical head admits no value
    either. This is consistency at [Empty], at D and M. *)
Corollary closed_empty_empty {G i t l k} : compt i -> closed_ok i G ->
  ~ [ G ; cnil ⊢[ i ] t : tyEmpty l @ k ].
Proof.
  intros Hc HG Ht. destruct (closed_canonicity_whnf Hc HG (whnf_tyEmpty _) Ht) as (w & _ & _ & _ & C).
  exact C.
Qed.

(** A closed proof of [sEq^l(A; a; b)] computes to [srefl], and its
    endpoints are then equal (MX §18: [sEq] imports no equation). *)
Corollary closed_seq_canonicity {G i t l A a b k} : compt i -> closed_ok i G ->
  [ G ; cnil ⊢[ i ] t : tySEq l A a b @ k ] ->
  (exists l' A' a', reds t (srefl l' A' a')) /\ [ G ; cnil ⊢[ i ] a ≅ b : A @ l ].
Proof.
  intros Hc HG Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (closed_canonicity_whnf Hc HG (whnf_tySEq _ _ _ _) Ht) as (w & Hr & _ & E & (l' & A' & a' & ->)).
  split; [eauto|].
  destruct (inv_srefl Hi (eqtm_wf_r Hi E)) as (_ & _ & ET).
  destruct (seq_inj_c Hc ET) as (_ & _ & Ea & Eb).
  exact (eqtm_trans _ _ _ _ _ _ _ _ Ea (eqtm_sym _ _ _ _ _ _ _ Eb)).
Qed.

(** ** The identity type (M11a) *)

(** A closed proof of [Id^l(A; a; b)] computes to [refl], and its
    endpoints are then equal. *)
Corollary closed_id_canonicity {G i t l A a b k} : compt i -> closed_ok i G ->
  [ G ; cnil ⊢[ i ] t : tyId l A a b @ k ] ->
  (exists l' A' a', reds t (tmRefl l' A' a')) /\ [ G ; cnil ⊢[ i ] a ≅ b : A @ l ].
Proof.
  intros Hc HG Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (closed_canonicity_whnf Hc HG (whnf_tyId _ _ _ _) Ht) as (w & Hr & _ & E & (l' & A' & a' & ->)).
  split; [eauto|].
  destruct (inv_idrefl Hi (eqtm_wf_r Hi E)) as (_ & _ & ET).
  destruct (id_inj_c Hc ET) as (_ & _ & Ea & Eb).
  exact (eqtm_trans _ _ _ _ _ _ _ _ Ea (eqtm_sym _ _ _ _ _ _ _ Eb)).
Qed.

(** ** Binary sums (M12b) *)

(** A closed term of [A + B] computes to an injection, whose payload is a
    closed term of its summand: the disjunction property at [+]. *)
Corollary closed_sum_canonicity {G i t l l' A B k} : compt i -> closed_ok i G ->
  [ G ; cnil ⊢[ i ] t : tySum l l' A B @ k ] ->
  (exists l1 l2 C D a, reds t (tmInl l1 l2 C D a) /\ [ G ; cnil ⊢[ i ] a : A @ l ]) \/
  (exists l1 l2 C D b, reds t (tmInr l1 l2 C D b) /\ [ G ; cnil ⊢[ i ] b : B @ l' ]).
Proof.
  intros Hc HG Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (closed_canonicity_whnf Hc HG (whnf_tySum _ _ _ _) Ht)
    as (w & Hr & _ & E & [(l1 & l2 & C & D & a & ->) | (l1 & l2 & C & D & b & ->)]).
  - left. exists l1, l2, C, D, a. exact (conj Hr (inl_payload Hc (eqtm_wf_r Hi E))).
  - right. exists l1, l2, C, D, b. exact (conj Hr (inr_payload Hc (eqtm_wf_r Hi E))).
Qed.

(** For example, closed functions compute to [λ]s. *)
Corollary closed_pi_canonicity {G i t l l' A B k} : compt i -> closed_ok i G ->
  [ G ; cnil ⊢[ i ] t : tyPi l l' A B @ k ] ->
  exists l1 l2 A' b, reds t (lam l1 l2 A' b) /\ [ G ; cnil ⊢[ i ] t ≅ lam l1 l2 A' b : tyPi l l' A B @ k ].
Proof.
  intros Hc HG Ht.
  destruct (closed_canonicity_whnf Hc HG (whnf_tyPi _ _ _ _) Ht) as (w & Hr & _ & E & (l1 & l2 & A' & b & ->)).
  exists l1, l2, A', b. split; assumption.
Qed.
