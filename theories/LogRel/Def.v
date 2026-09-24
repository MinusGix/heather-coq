(** * The Kripke logical relation for MLTT (ch. 7 §"Kripke Logical Relations
    for MLTT", j = prog)

    [Prop]-valued, as required by the universe hierarchy (see
    logrel-coq-spike/SPIKE_UNIVERSES.md).  A type relation carries its term
    relation as an index: [LR n rec G Γ T T' l R] says that [T] and [T'] are
    related at level [l] and [R] relates their terms.

    Staging.  Π relates its domain at a level [l1 ≤ l1 ⊔ l2], so levels
    cannot be the recursion index.  Stage [n] is a single inductive family
    over all levels; only the universe case refers to earlier stages, for a
    level [l0] of measure below [n] (via [rec]).  [LogRel l] uses stage
    [lmeasure l]; stages are related by cumulativity.

    Level equivalences are folded into each case (the paper's separate
    level-conversion case becomes a lemma).  The universe case is indexed
    by the level read off the left type's normal form, so that two
    derivations for the same type have syntactically the same relation.
    The Π case records the generic equality of domains and codomains (the
    paper records it for the whole Π type, which is derivable). *)
From DeLaM.Typing Require Export Generic.

Section LRDef.
Context `{E : GenericEq}.

Definition RedRel := gctx -> ctx -> ty -> ty -> lvl -> (tm -> tm -> Prop) -> Prop.

(** Equivalence of term relations.  Every case of the relation accepts any
    term relation equivalent to its canonical one ("saturation"), so that
    constructions like symmetry can name their term relations explicitly
    (e.g. [flip domR]) without choice or extensionality axioms. *)
Definition releq (R R' : tm -> tm -> Prop) := forall t t', R t t' <-> R' t t'.

(** ** Natural numbers *)

Inductive NatRel (G : gctx) (Γ : ctx) : tm -> tm -> Prop :=
| natrel t t' w w' :
    [ G ; Γ ⊢g t ⤳* w : tyNat @ lzero ] -> [ G ; Γ ⊢g t' ⤳* w' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ w ≈ w' : tyNat @ lzero ] -> NatNf G Γ w w' -> NatRel G Γ t t'
with NatNf (G : gctx) (Γ : ctx) : tm -> tm -> Prop :=
| natnf_zero : NatNf G Γ zero zero
| natnf_succ t t' : NatRel G Γ t t' -> NatNf G Γ (succ t) (succ t')
| natnf_ne ν ν' : [ G ; Γ ⊢ ν ~ ν' : tyNat @ lzero ] -> NatNf G Γ ν ν'.

Scheme NatRel_mut := Induction for NatRel Sort Prop
  with NatNf_mut := Induction for NatNf Sort Prop.

(** ** Universes: codes whose decodings are related one stage down

    As for the annotations of applications in the Π case, the decodings
    are related for every choice of equivalent annotations on [El]. *)

Definition URel (rec : lvl -> RedRel) (G : gctx) (Γ : ctx) (l0 : lvl) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyU l0 @ lsuc l0 ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyU l0 @ lsuc l0 ] /\
    whnf w /\ whnf w' /\ [ G ; Γ ⊢ w ≈ w' : tyU l0 @ lsuc l0 ] /\
    forall la lb, lequiv (gL G) la l0 -> lequiv (gL G) lb l0 ->
      exists R, rec l0 G Γ (tyEl la w) (tyEl lb w') l0 R.

(** ** Neutral types *)

Definition NeRel (G : gctx) (Γ : ctx) (V V' : ty) (l : lvl) : tm -> tm -> Prop :=
  fun t t' => exists ν ν',
    [ G ; Γ ⊢g t ⤳* ν : V @ l ] /\ [ G ; Γ ⊢g t' ⤳* ν' : V' @ l ] /\
    [ G ; Γ ⊢ ν ~ ν' : V @ l ] /\ [ G ; Γ ⊢ ν ~ ν' : V' @ l ].

(** ** Dependent functions

    Kripke quantification is over order-preserving embeddings [r : Δ ≤ Γ]
    (OPE data, closed under composition); the generic laws take the
    underlying renaming ([wk_wf_wkr]). *)

Definition DomRel (G : gctx) (Γ : ctx) :=
  forall Δ (r : wk), wk_wf r Δ Γ -> [ G ; Δ ⊢g ] -> tm -> tm -> Prop.
Definition CodRel (G : gctx) (Γ : ctx) (domR : DomRel G Γ) :=
  forall Δ (r : wk) (Hr : wk_wf r Δ Γ) (HΔ : [ G ; Δ ⊢g ]) a a', domR Δ r Hr HΔ a a' -> tm -> tm -> Prop.

(** Related functions: reduce to related weak-head normal forms whose
    applications to related arguments are related, in every weakening, for
    every choice of (equivalent) annotations on the application. *)
Definition PiRel (G : gctx) (Γ : ctx) (l1 l2 l3 l4 : lvl) (A B A' B' : ty)
    (domR : DomRel G Γ) (codR : CodRel G Γ domR) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyPi l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢g t' ⤳* w' : tyPi l3 l4 A' B' @ lmax l1 l2 ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tyPi l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢ w ≈ w' : tyPi l3 l4 A' B' @ lmax l1 l2 ] /\
    forall Δ (r : wk) (Hr : wk_wf r Δ Γ) (HΔ : [ G ; Δ ⊢g ]) a a' (ha : domR Δ r Hr HΔ a a')
      la lb la' lb' A1 B1 A1' B1',
      lequiv (gL G) la l1 -> lequiv (gL G) lb l2 ->
      lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
      [ G ; Δ ⊢ A⟨r⟩ ≈ A1 @ l1 ] -> [ G ; Δ ,, A⟨r⟩ @ l1 ⊢ B⟨rlift r⟩ ≈ B1 @ l2 ] ->
      [ G ; Δ ⊢ A'⟨r⟩ ≈ A1' @ l1 ] -> [ G ; Δ ,, A'⟨r⟩ @ l1 ⊢ B'⟨rlift r⟩ ≈ B1' @ l2 ] ->
      codR Δ r Hr HΔ a a' ha (app w⟨r⟩ la lb A1 B1 a) (app w'⟨r⟩ la' lb' A1' B1' a').

(** ** The relation, stage [n] *)

Inductive LR (n : nat) (rec : lvl -> RedRel) : RedRel :=
| LRnat G Γ T T' l R :
    lequiv (gL G) l lzero ->
    [ G ; Γ ⊢g T ⤳* tyNat @ l ] -> [ G ; Γ ⊢g T' ⤳* tyNat @ l ] ->
    releq R (NatRel G Γ) ->
    LR n rec G Γ T T' l R
| LRU G Γ T T' l l1 l2 R :
    lequiv (gL G) l (lsuc l1) -> lequiv (gL G) l2 l1 -> lmeasure l1 < n ->
    [ G ; Γ ⊢g T ⤳* tyU l1 @ l ] -> [ G ; Γ ⊢g T' ⤳* tyU l2 @ l ] ->
    releq R (URel rec G Γ l1) ->
    LR n rec G Γ T T' l R
| LRne G Γ T T' l V V' R :
    [ G ; Γ ⊢g T ⤳* V @ l ] -> [ G ; Γ ⊢g T' ⤳* V' @ l ] -> [ G ; Γ ⊢ V ~ V' @ l ] ->
    releq R (NeRel G Γ V V' l) ->
    LR n rec G Γ T T' l R
| LRpi G Γ T T' l l1 l2 l3 l4 A B A' B'
    (domR : DomRel G Γ) (codR : CodRel G Γ domR) R :
    lequiv (gL G) l (lmax l1 l2) -> lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
    lwf (gL G) l1 -> lwf (gL G) l2 ->
    [ G ; Γ ⊢g T ⤳* tyPi l1 l2 A B @ l ] -> [ G ; Γ ⊢g T' ⤳* tyPi l3 l4 A' B' @ l ] ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢g A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g B @ l2 ] -> [ G ; Γ ,, A' @ l1 ⊢g B' @ l2 ] ->
    [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    (forall Δ (r : wk) (Hr : wk_wf r Δ Γ) (HΔ : [ G ; Δ ⊢g ]),
        LR n rec G Δ A⟨r⟩ A'⟨r⟩ l1 (domR Δ r Hr HΔ)) ->
    (forall Δ (r : wk) (Hr : wk_wf r Δ Γ) (HΔ : [ G ; Δ ⊢g ]) a a' (ha : domR Δ r Hr HΔ a a'),
        LR n rec G Δ B⟨rlift r⟩[lsingle a] B'⟨rlift r⟩[lsingle a'] l2
           (codR Δ r Hr HΔ a a' ha)) ->
    releq R (PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR) ->
    LR n rec G Γ T T' l R.

(** ** Stages *)

Fixpoint LRbelow (n : nat) : lvl -> RedRel :=
  match n with
  | 0 => fun _ _ _ _ _ _ _ => False
  | S n => fun l0 => if Nat.eqb (lmeasure l0) n then LR n (LRbelow n) else LRbelow n l0
  end.

(** The relation for types at level [l]. *)
Definition LogRel (l : lvl) : RedRel := LR (lmeasure l) (LRbelow (lmeasure l)).

Lemma LRbelow_spec n l0 : lmeasure l0 < n -> LRbelow n l0 = LogRel l0.
Proof.
  induction n as [|n IH]; intros Hlt; [lia|]. cbn.
  destruct (Nat.eqb_spec (lmeasure l0) n) as [<-|Hne]; [reflexivity|]. apply IH; lia.
Qed.

End LRDef.
