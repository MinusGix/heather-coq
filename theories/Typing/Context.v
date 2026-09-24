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

(** The layer order [V < C < D < M]. *)
Definition lrank (i : layer) : nat := match i with lV => 0 | lC => 1 | lD => 2 | lM => 3 end.
Definition lle (i j : layer) : Prop := lrank i <= lrank j.

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

(** Extending [Ψ] by one binding. *)
Definition gext (G : gctx) (D : gdecl) : gctx := mkG (gL G) (D :: gΨ G).

(** Global renaming of a binding, and lookup: [U : (Δ ⊢ᵢ @l) ∈ Ψ] with the
    binding weakened into [Ψ] (like [in_ctx] for local variables). *)
Definition gdecl_ren (D : gdecl) (ξ : nat -> nat) : gdecl :=
  match D with
  | gdCtx => gdCtx
  | gdTy Δ i l => gdTy Δ⟪ξ⟫ i l
  | gdTm Δ i T l => gdTm Δ⟪ξ⟫ i T⟪ξ⟫ l
  end.

Inductive in_gctx : list gdecl -> nat -> gdecl -> Prop :=
| ing_here Ψ D : in_gctx (D :: Ψ) 0 (gdecl_ren D S)
| ing_there Ψ D D' n : in_gctx Ψ n D -> in_gctx (D' :: Ψ) (S n) (gdecl_ren D S).

(** ** Shape of local contexts *)

Fixpoint clen (Γ : ctx) : nat := match Γ with cnil | cvar _ => 0 | cext Γ _ _ => S (clen Γ) end.
Fixpoint ctail (Γ : ctx) : ctx := match Γ with cnil => cnil | cvar g => cvar g | cext Γ _ _ => ctail Γ end.

(** The tail condition of typed local substitutions [δ : Γ → Δ] (04:990):
    [Γ] and [Δ] end in the same way ([·] or the same [g]), and past the
    variables of [Δ], [δ] is the shift by [|Γ|].  For a context ending in
    [g] this fixes how [g]'s own variables are sent, which the lookup
    typing of [δ] cannot see. *)
Definition lsub_tail (d : lsub) (Δ Γ : ctx) : Prop :=
  ctail Δ = ctail Γ /\ forall n, llk d (clen Δ + n) = var (clen Γ + n).

(** ** Local context lookup: [x : T @ l ∈ Γ], with [T] weakened into [Γ] *)

Notation "Γ ,, A @ l" := (cext Γ A l) (at level 20, A at next level).

Inductive in_ctx : ctx -> nat -> ty -> lvl -> Prop :=
| in_here Γ A l : in_ctx (Γ ,, A @ l) 0 A⟨↑⟩ l
| in_there Γ A l B l' n : in_ctx Γ n A l -> in_ctx (Γ ,, B @ l') (S n) A⟨↑⟩ l.
