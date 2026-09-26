(** * Decidability of type checking (M7_DESIGN.md C1)

    For syntax in the redex-free fragment ([nlr], J1), at every layer:
    well-formedness of global contexts, contexts and types, and typing,
    are decidable (in [Prop], as M6's conversion, H1). And whether a
    synthesizing term has a type, which is then unique ([type_uniq]).

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
    + intros T Hsz Hn. apply (ty_step n IH); [lia | exact Hn].
    + intros t Hsz Hn. apply (ck_step n IH); [lia | exact Hn].
    + intros t Hsz Hn Hs. apply (sy_step n IH); [lia | exact Hn | exact Hs].
    + intros Γ Hsz Hn. apply (cx_step n IH); [lia | exact Hn].
Qed.

Corollary tyd T : nlr_ty T -> TYD T.
Proof. exact (proj1 (sz_all (S (sz_ty T))) T (Nat.lt_succ_diag_r _)). Qed.
Corollary ckd t : nlr_tm t -> CKD t.
Proof. exact (proj1 (proj2 (sz_all (S (sz_tm t)))) t (Nat.lt_succ_diag_r _)). Qed.
Corollary syd t : nlr_tm t -> synth t -> SYD t.
Proof. exact (proj1 (proj2 (proj2 (sz_all (S (sz_tm t))))) t (Nat.lt_succ_diag_r _)). Qed.
Corollary cxd Γ : nlr_ctx Γ -> CXD Γ.
Proof. exact (proj2 (proj2 (proj2 (sz_all (S (sz_ctx Γ))))) Γ (Nat.lt_succ_diag_r _)). Qed.

(** ** Global contexts *)

Definition nlr_decl (D : gdecl) : Prop :=
  match D with gdCtx => True | gdTy Δ _ _ => nlr_ctx Δ | gdTm Δ _ T _ => nlr_ctx Δ /\ nlr_ty T end.
Definition nlr_gctx (G : gctx) : Prop := Forall nlr_decl (gΨ G).

Theorem wf_glob_dec G : nlr_gctx G -> Dec ([ ⊢ G ]).
Proof.
  destruct G as [L Ψ]. unfold nlr_gctx; cbn [gΨ]. induction Ψ as [|D Ψ IHΨ]; intros Hn.
  - left; constructor.
  - inversion Hn as [| ? ? HD HΨ]; subst.
    destruct (IHΨ HΨ) as [HG | N]; [| right; intros H; inversion H; contradiction].
    destruct D as [| Δ i l | Δ i T l]; cbn in HD.
    + left; now constructor.
    + destruct (cxd Δ HD (mkG L Ψ) lD HG) as [HΔ | N]; [| right; intros H; inversion H; contradiction].
      destruct (layer_eq_dec i lC) as [Ei | Ni];
        [| destruct (layer_eq_dec i lD) as [Ei | Ni']; [| right; intros H; inversion H; subst;
             match goal with X : _ \/ _ |- _ => destruct X; contradiction end]].
      all: destruct (lwf_Dec L l) as [Hl | N]; [| right; intros H; inversion H; contradiction].
      all: left; constructor; auto.
    + destruct HD as [HnΔ HnT].
      destruct (cxd Δ HnΔ (mkG L Ψ) lD HG) as [HΔ | N];
        [| right; intros H; inversion H; subst; apply N; exact (ctx_of_wf_ty (i := lD) eq_refl ltac:(eassumption))].
      destruct (tyd T HnT (mkG L Ψ) lD Δ l HΔ) as [HT | N]; [| right; intros H; inversion H; contradiction].
      destruct (layer_eq_dec i lV) as [Ei | Ni];
        [| destruct (layer_eq_dec i lC) as [Ei | Ni']; [| right; intros H; inversion H; subst;
             match goal with X : _ \/ _ |- _ => destruct X; contradiction end]].
      all: destruct (lwf_Dec L l) as [Hl | N]; [| right; intros H; inversion H; contradiction].
      all: left; constructor; auto.
Qed.

(** ** Contexts, types, terms *)

Theorem wf_ctx_dec G i Γ : nlr_gctx G -> nlr_ctx Γ -> Dec ([ G ; Γ ⊢[ i ] ]).
Proof.
  intros HnG HnΓ. destruct (wf_glob_dec G HnG) as [HG | N]; [exact (cxd Γ HnΓ G i HG) |].
  right; intros H; exact (N (ctx_glob _ _ _ H)).
Qed.

Theorem wf_ty_dec G i Γ T k : nlr_gctx G -> nlr_ctx Γ -> nlr_ty T -> Dec ([ G ; Γ ⊢[ i ] T @ k ]).
Proof.
  intros HnG HnΓ HnT. destruct (wf_ctx_dec G (typeof i) Γ HnG HnΓ) as [HΓ | N]; [exact (tyd T HnT G i Γ k HΓ) |].
  right; intros H; exact (N (ctx_of_ty_any H)).
Qed.

Theorem wf_tm_dec G i Γ t T k : nlr_gctx G -> nlr_ctx Γ -> nlr_tm t -> nlr_ty T ->
  Dec ([ G ; Γ ⊢[ i ] t : T @ k ]).
Proof.
  intros HnG HnΓ Hnt HnT. destruct (wf_ty_dec G (typeof i) Γ T k HnG HnΓ HnT) as [HT | N];
    [exact (ckd t Hnt G i Γ T k HT) |].
  right; intros H; exact (N (wf_tm_ty_any H)).
Qed.

(** Type inference: a synthesizing term's typability is decidable, and its
    type is unique up to equality ([type_uniq]). *)
Theorem infer_dec G i Γ t : nlr_gctx G -> nlr_ctx Γ -> nlr_tm t -> synth t ->
  (exists T k, [ G ; Γ ⊢[ i ] t : T @ k ]) \/ (forall T k, ~ [ G ; Γ ⊢[ i ] t : T @ k ]).
Proof.
  intros HnG HnΓ Hnt Hs. destruct (wf_ctx_dec G (typeof i) Γ HnG HnΓ) as [HΓ | N]; [exact (syd t Hnt Hs G i Γ HΓ) |].
  right; intros T k H; exact (N (ctx_of_tm_any H)).
Qed.
