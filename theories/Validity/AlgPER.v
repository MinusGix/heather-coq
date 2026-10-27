(** * Symmetry and transitivity of algorithmic conversion (08:199; M6_DESIGN.md step 4)

    On typed syntax. The swapped derivation compares binders of the other
    side ([Γ ,, A'], [gdTy Δ'], the right motives' branch scopes), so each
    case moves the induction hypothesis there by the conversion lemma.
    Neutrals infer some type; its equation with the other side's follows
    from soundness of both derivations.

    The parts build beside one another: the shared lemmas ([AlgPERBase]),
    symmetry ([AlgPERSym]) and transitivity ([AlgPERTrans]), which uses
    none of symmetry. *)
From DeLaM.Validity Require Export AlgPERSym AlgPERTrans.
