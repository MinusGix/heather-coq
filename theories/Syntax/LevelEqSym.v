(** * Level equivalence of syntax: symmetry

    One of the parts [LevelEq] puts together; they build in parallel. *)
From DeLaM.Syntax Require Export LevelEqBase.

Lemma leq_sym_all :
  let Pty T := forall T', ty_leq T T' -> ty_leq T' T in
  let Ptm t := forall t', tm_leq t t' -> tm_leq t' t in
  let Pctx Γ := forall Γ', ctx_leq Γ Γ' -> ctx_leq Γ' Γ in
  let Pl d := forall d', lsub_leq d d' -> lsub_leq d' d in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.
