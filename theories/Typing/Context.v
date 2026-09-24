(** * Layers, global contexts, local context lookup (ch. 4) *)
From Coq Require Export List.
From DeLaM.Syntax Require Export Weakening.

(** ** Layers [V < C < D < M] *)

Inductive layer : Type := lV | lC | lD | lM.

(** [typeof i]: where the types and contexts of layer-[i] judgments live. *)
Definition typeof (i : layer) : layer :=
  match i with lM => lM | _ => lD end.

(** Layers with computation (β/η available). *)
Definition compt (i : layer) : Prop := i = lD \/ i = lM.

Lemma typeof_idem i : typeof (typeof i) = typeof i.
Proof. now destruct i. Qed.
Lemma compt_typeof i : compt (typeof i).
Proof. destruct i; cbn; unfold compt; auto. Qed.
Lemma compt_typeof_self i : compt i -> typeof i = i.
Proof. now intros [-> | ->]. Qed.

(** ** Global contexts

    [Ψ ::= · | Ψ, g : Ctx | Ψ, U : (Δ ⊢ᵢ @l) | Ψ, u : (Δ ⊢ᵢ T @l)],
    de Bruijn (index 0 = most recent).  M1 only uses [g : Ctx]. *)
Inductive gdecl : Type :=
| gdCtx
| gdTy (Δ : ctx) (i : layer) (l : lvl)
| gdTm (Δ : ctx) (i : layer) (T : ty) (l : lvl).

(** The universe context [L] (a number of level variables) and [Ψ]. *)
Record gctx : Type := mkG { gL : nat ; gΨ : list gdecl }.

Definition gctx_var (G : gctx) (g : nat) : Prop := nth_error (gΨ G) g = Some gdCtx.

(** ** Local context lookup: [x : T @ l ∈ Γ], with [T] weakened into [Γ] *)

Notation "Γ ,, A @ l" := (cext Γ A l) (at level 20, A at next level).

Inductive in_ctx : ctx -> nat -> ty -> lvl -> Prop :=
| in_here Γ A l : in_ctx (Γ ,, A @ l) 0 A⟨↑⟩ l
| in_there Γ A l B l' n : in_ctx Γ n A l -> in_ctx (Γ ,, B @ l') (S n) A⟨↑⟩ l.
