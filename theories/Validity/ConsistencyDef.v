(** * Consistency with definitions, at D and M (M9 follow-up)

    Closed canonicity fails at M once the global context has a definition
    ([DefStuck.v]): the recursor stays stuck on a boxed defined global. Yet
    consistency survives: unfold every definition ([Typing/Unfold.v]); the
    unfolded derivation lives under a global context that still has only
    context variables and definitions ([unf_no_opaque]), and its term
    mentions no definition ([unf_gfree]), so no stuck recursor can occur in
    its normal form ([Consistency.v], [consistency_gen]). The type itself,
    [Π (x : Ty ℓ). El x], is fixed by unfolding, as is a context of
    universes. *)
From DeLaM.Typing Require Import Unfold.
From DeLaM.Validity Require Export Consistency.

Lemma unf_no_opaque G : no_opaque G -> no_opaque (unf_G G).
Proof.
  intros HG n D Hin. destruct (in_gctx_unf_inv _ _ _ Hin) as (D0 & HD0 & ->).
  destruct (HG _ _ HD0) as [-> | (Δ & T & l & t & ->)]; [left; reflexivity | right].
  do 4 eexists; reflexivity.
Qed.

Lemma unf_univ_ctx Γ : univ_ctx Γ -> univ_ctx (unf_ctx Γ).
Proof.
  intros HΓ n T k Hin. destruct (in_ctx_unf_inv _ _ _ _ Hin) as (T0 & HT0 & ->).
  destruct (HΓ _ _ _ HT0) as (l & ->). exists l; reflexivity.
Qed.

(** No term of [Π (x : Ty ℓ). El x], at D or M, in a global context of
    context variables and definitions and a local context of universes. *)
Theorem consistency_def {G i Γ t l1 l2 l l' k} : compt i -> no_opaque G -> univ_ctx Γ ->
  ~ [ G ; Γ ⊢[ i ] t : tyPi l1 l2 (tyU l) (tyEl l' (var 0)) @ k ].
Proof.
  intros Hc HG HΓ Ht.
  pose proof (proj1 (proj2 (proj2 (proj2 unfolding))) _ _ _ _ _ _ Ht) as Hu. cbn [unf_ty unf_tm] in Hu.
  exact (consistency_gen Hc (unf_no_opaque _ HG) (unf_univ_ctx _ HΓ) (or_intror (unf_gfree t)) Hu).
Qed.

(** The paper's statement: the empty local context. *)
Corollary consistency_def_closed {G i t l1 l2 l l' k} : compt i -> no_opaque G ->
  ~ [ G ; cnil ⊢[ i ] t : tyPi l1 l2 (tyU l) (tyEl l' (var 0)) @ k ].
Proof. intros Hc HG. exact (consistency_def Hc HG univ_ctx_nil). Qed.

(** In particular at M, where [closed_ok] excludes definitions. *)
Corollary consistency_M_def {G t l1 l2 l l' k} : no_opaque G ->
  ~ [ G ; cnil ⊢[ lM ] t : tyPi l1 l2 (tyU l) (tyEl l' (var 0)) @ k ].
Proof. exact (consistency_def_closed compt_M). Qed.

Print Assumptions consistency_def.
Print Assumptions consistency_M_def.
