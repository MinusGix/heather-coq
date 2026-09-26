(** * Decidability of type checking (M7_DESIGN.md C1, C1b)

    At every layer, for all syntax: well-formedness of global contexts,
    contexts and types, and typing, are decidable (in [Prop], as M6's
    conversion, H1). And whether a synthesizing term has a type, which is
    then unique ([type_uniq]).

    The steps ([ty_step], [cx_step], [sy_step], [ck_step]) decide each
    problem from the problems about smaller syntax; an induction on the
    size bound closes them. The unconditional statements decide the
    presuppositions first: an ill-formed global context, context or type
    refutes the judgments above it. *)
From DeLaM.Validity Require Export TCCheck.

Theorem sz_all n : IHsz n.
Proof.
  induction n as [|n IH].
  - repeat split; intros; lia.
  - split; [| split; [| split]].
    + intros T Hsz. apply (ty_step n IH); lia.
    + intros t Hsz. apply (ck_step n IH); lia.
    + intros t Hsz Hs. apply (sy_step n IH); [lia | exact Hs].
    + intros Γ Hsz. apply (cx_step n IH); lia.
Qed.

Corollary tyd T : TYD T.
Proof. exact (proj1 (sz_all (S (sz_ty T))) T (Nat.lt_succ_diag_r _)). Qed.
Corollary ckd t : CKD t.
Proof. exact (proj1 (proj2 (sz_all (S (sz_tm t)))) t (Nat.lt_succ_diag_r _)). Qed.
Corollary syd t : synth t -> SYD t.
Proof. exact (proj1 (proj2 (proj2 (sz_all (S (sz_tm t))))) t (Nat.lt_succ_diag_r _)). Qed.
Corollary cxd Γ : CXD Γ.
Proof. exact (proj2 (proj2 (proj2 (sz_all (S (sz_ctx Γ))))) Γ (Nat.lt_succ_diag_r _)). Qed.

(** ** Global contexts *)

Theorem wf_glob_dec G : Dec ([ ⊢ G ]).
Proof.
  destruct G as [L Ψ]. induction Ψ as [|D Ψ IHΨ].
  - left; constructor.
  - destruct IHΨ as [HG | N]; [| right; intros H; inversion H; contradiction].
    destruct D as [| Δ i l | Δ i T l].
    + left; now constructor.
    + destruct (cxd Δ (mkG L Ψ) lD HG) as [HΔ | N]; [| right; intros H; inversion H; contradiction].
      destruct (layer_eq_dec i lC) as [Ei | Ni];
        [| destruct (layer_eq_dec i lD) as [Ei | Ni']; [| right; intros H; inversion H; subst;
             match goal with X : _ \/ _ |- _ => destruct X; contradiction end]].
      all: destruct (lwf_Dec L l) as [Hl | N]; [| right; intros H; inversion H; contradiction].
      all: left; constructor; auto.
    + destruct (cxd Δ (mkG L Ψ) lD HG) as [HΔ | N];
        [| right; intros H; inversion H; subst; apply N; exact (ctx_of_wf_ty (i := lD) eq_refl ltac:(eassumption))].
      destruct (tyd T (mkG L Ψ) lD Δ l HΔ) as [HT | N]; [| right; intros H; inversion H; contradiction].
      destruct (layer_eq_dec i lV) as [Ei | Ni];
        [| destruct (layer_eq_dec i lC) as [Ei | Ni']; [| right; intros H; inversion H; subst;
             match goal with X : _ \/ _ |- _ => destruct X; contradiction end]].
      all: destruct (lwf_Dec L l) as [Hl | N]; [| right; intros H; inversion H; contradiction].
      all: left; constructor; auto.
Qed.

(** ** Contexts, types, terms *)

Theorem wf_ctx_dec G i Γ : Dec ([ G ; Γ ⊢[ i ] ]).
Proof.
  destruct (wf_glob_dec G) as [HG | N]; [exact (cxd Γ G i HG) |].
  right; intros H; exact (N (ctx_glob _ _ _ H)).
Qed.

Theorem wf_ty_dec G i Γ T k : Dec ([ G ; Γ ⊢[ i ] T @ k ]).
Proof.
  destruct (wf_ctx_dec G (typeof i) Γ) as [HΓ | N]; [exact (tyd T G i Γ k HΓ) |].
  right; intros H; exact (N (ctx_of_ty_any H)).
Qed.

Theorem wf_tm_dec G i Γ t T k : Dec ([ G ; Γ ⊢[ i ] t : T @ k ]).
Proof.
  destruct (wf_ty_dec G (typeof i) Γ T k) as [HT | N]; [exact (ckd t G i Γ T k HT) |].
  right; intros H; exact (N (wf_tm_ty_any H)).
Qed.

(** Type inference: a synthesizing term's typability is decidable, and its
    type is unique up to equality ([type_uniq]). *)
Theorem infer_dec G i Γ t : synth t ->
  (exists T k, [ G ; Γ ⊢[ i ] t : T @ k ]) \/ (forall T k, ~ [ G ; Γ ⊢[ i ] t : T @ k ]).
Proof.
  intros Hs. destruct (wf_ctx_dec G (typeof i) Γ) as [HΓ | N]; [exact (syd t Hs G i Γ HΓ) |].
  right; intros T k H; exact (N (ctx_of_tm_any H)).
Qed.
