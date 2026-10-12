(** * Level equivalence of syntax: level renamings and substitutions

    One of the parts [LevelEq] puts together; they build in parallel. *)
From DeLaM.Syntax Require Export LevelEqBase.

Lemma leq_uren_all :
  let Pty T := forall T' ρ, ty_leq T T' -> ty_leq (uren_ty T ρ) (uren_ty T' ρ) in
  let Ptm t := forall t' ρ, tm_leq t t' -> tm_leq (uren_tm t ρ) (uren_tm t' ρ) in
  let Pctx Γ := forall Γ' ρ, ctx_leq Γ Γ' -> ctx_leq (ucren Γ ρ) (ucren Γ' ρ) in
  let Pl d := forall d' ρ, lsub_leq d d' -> lsub_leq (ulren d ρ) (ulren d' ρ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Lemma leq_usubst_all :
  let Pty T := forall T' φ φ', (forall n, leqv (φ n) (φ' n)) -> ty_leq T T' ->
    ty_leq (usubst_ty T φ) (usubst_ty T' φ') in
  let Ptm t := forall t' φ φ', (forall n, leqv (φ n) (φ' n)) -> tm_leq t t' ->
    tm_leq (usubst_tm t φ) (usubst_tm t' φ') in
  let Pctx Γ := forall Γ' φ φ', (forall n, leqv (φ n) (φ' n)) -> ctx_leq Γ Γ' ->
    ctx_leq (ucsubst Γ φ) (ucsubst Γ' φ') in
  let Pl d := forall d' φ φ', (forall n, leqv (φ n) (φ' n)) -> lsub_leq d d' ->
    lsub_leq (ulsubst d φ) (ulsubst d' φ') in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.
