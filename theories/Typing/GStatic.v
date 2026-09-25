(** * Static code under global substitutions

    Code typed at a static layer (C or V) only mentions static global
    variables and context variables.  So two global substitutions that
    agree on those send it to the same code: this is what makes [box c]
    related to itself under related global substitutions, as boxed code
    is equal only to itself (06:534, 07a:390). *)
From DeLaM.Typing Require Export GSubstitution.

Definition static_decl (D : gdecl) : Prop :=
  match D with
  | gdCtx => True
  | gdTy _ i _ => lle i lC
  | gdTm _ i _ _ => lle i lC
  end.

(** [σ] and [σ'] agree on the static bindings of [G]. *)
Definition gsub_agree (G : gctx) (σ σ' : gsub) : Prop :=
  forall n D, in_gctx (gΨ G) n D -> static_decl D -> σ n = σ' n.

Lemma in_ctx_of_lt Δ n : n < clen Δ -> exists A k, in_ctx Δ n A k.
Proof.
  revert n; induction Δ as [| g | Δ IH A k]; cbn; intros n Hn; [lia | lia |].
  destruct n as [| n].
  - do 2 eexists; constructor.
  - destruct (IH n ltac:(lia)) as (A' & k' & H). do 2 eexists; constructor; exact H.
Qed.

Lemma glsubst_ext (d : lsub) σ σ' : (forall n, (llk d n)⦃σ⦄ = (llk d n)⦃σ'⦄) -> d⦃σ⦄ = d⦃σ'⦄.
Proof.
  induction d as [k | d IH t]; intros H; [reflexivity |].
  cbn [gsubst GSubst_lsub glsubst]. change (glsubst d σ) with d⦃σ⦄. change (glsubst d σ') with d⦃σ'⦄.
  rewrite (IH (fun n => H (S n))). f_equal. exact (H 0).
Qed.

(** The local substitution of a global variable's use, entrywise. *)
Lemma glsubst_agree_entries {d Δ Γ σ σ'} : lsub_tail d Δ Γ ->
  (forall n A k, in_ctx Δ n A k -> (llk d n)⦃σ⦄ = (llk d n)⦃σ'⦄) -> d⦃σ⦄ = d⦃σ'⦄.
Proof.
  intros [_ Hl] H. apply glsubst_ext. intros n.
  destruct (Nat.lt_ge_cases n (clen Δ)) as [Hn | Hn].
  - destruct (in_ctx_of_lt _ _ Hn) as (A & k & HA). exact (H _ _ _ HA).
  - replace n with (clen Δ + (n - clen Δ)) by lia. rewrite Hl. reflexivity.
Qed.

Lemma lle_C_notM {i} : lle i lC -> i <> lM.
Proof. intros Hi ->. discriminate (lle_M _ Hi). Qed.

Theorem static_gsubst :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> lle i lC ->
     forall σ σ', gsub_agree G σ σ' -> T⦃σ⦄ = T⦃σ'⦄) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> lle i lC ->
     forall σ σ', gsub_agree G σ σ' -> t⦃σ⦄ = t⦃σ'⦄) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    try match goal with Hi : lle lM lC |- _ => destruct (lle_C_notM Hi eq_refl) end;
    try match goal with Hi : lle ?i lC |- _ =>
      repeat match goal with IH : lle i lC -> _ |- _ => specialize (IH Hi) end end;
    cbn [gsubst GSubst_ty GSubst_tm]; simpl;
    try solve [eauto | f_equal; eauto].
  (* global variables: the same image, at the same local substitution *)
  all: match goal with
       | Ha : gsub_agree _ ?σ ?σ', Hin : in_gctx _ ?x ?D, Hl : lle _ ?i, Hi : lle ?i lC |- _ =>
           rewrite (Ha _ _ Hin (lle_trans _ _ _ Hl Hi))
       end;
    change (glsubst ?d ?s) with d⦃s⦄; f_equal;
    (eapply glsubst_agree_entries; [eassumption |]);
    intros ?n ?A ?k HA; match goal with IH : forall n A k, in_ctx _ n A k -> _ |- _ => eapply IH end;
    eassumption.
Qed.
