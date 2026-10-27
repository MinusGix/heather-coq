(** * The axioms the main results depend on

    Not part of [make all]: [Print Assumptions] walks every proof term a
    theorem depends on, about 30 s each for the consequences at the end of
    the build, where nothing else runs beside it. Run [make assumptions]
    before merging a change that could add an axiom; every line should
    print "Closed under the global context" (README: no admits, no
    axioms). *)
From DeLaM.Syntax Require Import Subst GSubst Universe.
From DeLaM.Typing Require Import USubstitution Unfold.
From DeLaM.Validity Require Import ConsistencyDef DefStuck.

Print Assumptions subst_subst.
Print Assumptions gsubst_gsubst.
Print Assumptions usubst_gsubst.
Print Assumptions usubstitution.
Print Assumptions unfolding.
Print Assumptions consistency_def.
Print Assumptions consistency_M_def.
Print Assumptions closed_canonicity_fails_M.
Print Assumptions stuck_rec_not_numeral.
