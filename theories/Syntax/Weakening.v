(** * Local weakenings: order-preserving embeddings

    [wk_wf ρ Δ Γ] ("ρ : Δ ≤ Γ") embeds Γ into Δ.  Both contexts share their
    tail ([·] or a context variable [g]): weakenings only add explicit
    entries.  This is the Kripke index of the logical relation for local
    contexts (M1_DESIGN.md: global/universe weakenings extend this later). *)
From DeLaM.Syntax Require Export Subst.

Inductive wk : Type := wk_id | wk_step (ρ : wk) | wk_up (ρ : wk).

Fixpoint wk_ren (ρ : wk) : rsub :=
  match ρ with
  | wk_id => rshift 0
  | wk_step ρ => rup (wk_ren ρ)
  | wk_up ρ => rlift (wk_ren ρ)
  end.
Coercion wk_ren : wk >-> rsub.

(** Contexts with the same tail differ only in explicit entries. *)
Fixpoint ctx_tail (Γ : ctx) : ctx :=
  match Γ with cext Γ _ _ => ctx_tail Γ | Γ => Γ end.

Inductive wk_wf : wk -> ctx -> ctx -> Prop :=
| wkwf_id Γ : wk_wf wk_id Γ Γ
| wkwf_step ρ Δ Γ A l : wk_wf ρ Δ Γ -> wk_wf (wk_step ρ) (cext Δ A l) Γ
| wkwf_up ρ Δ Γ A l : wk_wf ρ Δ Γ -> wk_wf (wk_up ρ) (cext Δ A⟨ρ⟩ l) (cext Γ A l).

Notation "ρ : Δ ≤ Γ" := (wk_wf ρ Δ Γ) (at level 70, Δ at next level).

(** ** Composition *)

Fixpoint wk_comp (ρ' ρ : wk) : wk :=          (* first ρ, then ρ' *)
  match ρ', ρ with
  | wk_id, ρ => ρ
  | wk_step ρ', ρ => wk_step (wk_comp ρ' ρ)
  | wk_up ρ', wk_id => wk_up ρ'
  | wk_up ρ', wk_step ρ => wk_step (wk_comp ρ' ρ)
  | wk_up ρ', wk_up ρ => wk_up (wk_comp ρ' ρ)
  end.

Lemma rlk_shift0 n : rlk (rshift 0) n = n.
Proof. cbn; lia. Qed.

Lemma rlk_wk_comp ρ' ρ n : rlk (wk_comp ρ' ρ) n = rlk ρ' (rlk ρ n).
Proof.
  revert ρ n; induction ρ' as [|ρ' IH|ρ' IH]; intros ρ n.
  - destruct ρ; cbn [wk_comp wk_ren]; now rewrite rlk_shift0.
  - cbn [wk_comp wk_ren]. rewrite !rlk_rup, IH; reflexivity.
  - destruct ρ as [|ρ|ρ]; cbn [wk_comp wk_ren].
    + now rewrite rlk_shift0.
    + rewrite !rlk_rup, rlk_rlift, IH; reflexivity.
    + rewrite !rlk_rlift; destruct n; auto; now rewrite IH.
Qed.

Lemma wk_comp_wf ρ' ρ Ξ Δ Γ : ρ' : Ξ ≤ Δ -> ρ : Δ ≤ Γ -> wk_comp ρ' ρ : Ξ ≤ Γ.
Proof.
  intros H'; revert ρ Γ; induction H' as [Θ|ρ' Ξ Δ A l H' IH|ρ' Ξ Δ A l H' IH];
    intros ρ Γ0 H; cbn.
  - destruct ρ; exact H.
  - constructor; auto.
  - inversion H as [Θ|ρ0 Δ0 Γ1 A0 l0 H0|ρ0 Δ0 Γ1 A0 l0 H0]; subst; cbn.
    + constructor; auto.
    + constructor; auto.
    + replace A0⟨ρ0⟩⟨ρ'⟩ with A0⟨wk_comp ρ' ρ0⟩.
      * constructor; auto.
      * symmetry; apply ren_ren_ty; intros; now rewrite rlk_wk_comp.
Qed.

(** Weakening by one entry, [↑]. *)
Definition wk1 : wk := wk_step wk_id.
Lemma wk1_ren n : rlk wk1 n = S n.
Proof. cbn; lia. Qed.

Lemma wk_wf_tail ρ Δ Γ : ρ : Δ ≤ Γ -> ctx_tail Δ = ctx_tail Γ.
Proof. induction 1; cbn; auto. Qed.
