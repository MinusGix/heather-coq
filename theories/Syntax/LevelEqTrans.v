(** * Level equivalence of syntax: transitivity

    One of the parts [LevelEq] puts together; they build in parallel. *)
From DeLaM.Syntax Require Export LevelEqBase.

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
