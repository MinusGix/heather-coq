(** * Level equivalence of syntax: renamings and global renamings

    One of the parts [LevelEq] puts together; they build in parallel. *)
From DeLaM.Syntax Require Export LevelEqBase.

(** ** Operations *)

Lemma leq_ren_all :
  let Pty T := forall T' r, ty_leq T T' -> ty_leq (ren_ty T r) (ren_ty T' r) in
  let Ptm t := forall t' r, tm_leq t t' -> tm_leq (ren_tm t r) (ren_tm t' r) in
  let Pctx (Γ : ctx) := True in
  let Pl d := forall d' r, lsub_leq d d' -> lsub_leq (lren d r) (lren d' r) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try exact I; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Lemma leq_gren_all :
  let Pty T := forall T' ξ, ty_leq T T' -> ty_leq (gren_ty T ξ) (gren_ty T' ξ) in
  let Ptm t := forall t' ξ, tm_leq t t' -> tm_leq (gren_tm t ξ) (gren_tm t' ξ) in
  let Pctx Γ := forall Γ' ξ, ctx_leq Γ Γ' -> ctx_leq (gcren Γ ξ) (gcren Γ' ξ) in
  let Pl d := forall d' ξ, lsub_leq d d' -> lsub_leq (glren d ξ) (glren d' ξ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.
