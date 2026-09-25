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

(** ** Substitutions that differ by identity expansions

    [U ↦ U'] and [U ↦ U'^id] (a type variable instantiated at the identity)
    act alike on well-typed syntax, where a type binding is only used as a
    type variable and a term binding as a term variable.  The [letbox]
    case of the fundamental theorem pushes related substitutions under the
    new binding with [U₀^id] rather than [U₀]: [U₀^id] is typed up to
    context conversion, which the [GId] image is not (as the paper's
    [σ, U^id/U]). *)

Definition id_obj (D : gdecl) (j : nat) : gobj :=
  match D with
  | gdCtx => GId j
  | gdTy _ _ _ => GTy (tyGvar j (lshift 0))
  | gdTm _ _ _ _ => GTm (gvar j (lshift 0))
  end.

Definition obj_equiv (D : gdecl) (o o' : gobj) : Prop :=
  o = o' \/ exists j, o = GId j /\ o' = id_obj D j.

Definition gsub_equiv (G : gctx) (σ τ : gsub) : Prop :=
  forall n D, in_gctx (gΨ G) n D -> obj_equiv D (σ n) (τ n).

Lemma gsub_equiv_up {G σ τ} D : gsub_equiv G σ τ -> gsub_equiv (gext G D) (gup σ) (gup τ).
Proof.
  intros H n D0 Hin. inversion Hin as [Ψ0 D1 | Ψ0 D1 D2 m Hm]; subst; cbn [gup]; [left; reflexivity|].
  destruct (H _ _ Hm) as [-> | (j & -> & ->)]; [left; reflexivity | right].
  exists (S j); split; [reflexivity|]. destruct D1; reflexivity.
Qed.

Lemma lnorm_nf d : nf_l d -> lnorm d = d.
Proof.
  induction d as [k | d IH t]; intros Hd; [reflexivity|]. destruct Hd as [Hd Ha].
  cbn [lnorm]. rewrite (IH Hd). destruct d as [[|k] | d0 t0], t; cbn in *; try reflexivity.
  destruct (Nat.eqb_spec n k) as [-> | Hne]; [| reflexivity].
  exfalso; apply Ha; cbn; first [reflexivity | apply Nat.eqb_refl | tauto].
Qed.

Lemma pty_id_obj j x : nf_l x -> pty (GTy (tyGvar j (lshift 0))) x = pty (GId j) x.
Proof. intros Hx. cbn. f_equal. exact (lnorm_nf _ Hx). Qed.
Lemma ptm_id_obj j x : nf_l x -> ptm (GTm (gvar j (lshift 0))) x = ptm (GId j) x.
Proof. intros Hx. cbn. f_equal. exact (lnorm_nf _ Hx). Qed.

Theorem equiv_gsubst :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] ->
     forall σ τ, gsub_equiv G σ τ -> (forall n, dnfo (τ n)) -> Γ⦃σ⦄ = Γ⦃τ⦄) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] ->
     forall σ τ, gsub_equiv G σ τ -> (forall n, dnfo (τ n)) -> T⦃σ⦄ = T⦃τ⦄) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] ->
     forall σ τ, gsub_equiv G σ τ -> (forall n, dnfo (τ n)) -> t⦃σ⦄ = t⦃τ⦄) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    cbn [gsubst GSubst_ty GSubst_tm GSubst_ctx]; simpl;
    try solve [eauto | f_equal; eauto].
  (* context variables *)
  1: match goal with
    | Ha : gsub_equiv _ ?σ ?τ, Hc : gctx_var _ ?g |- _ =>
        destruct (Ha _ _ (gctx_var_in _ _ Hc)) as [E | (j & E1 & E2)]; [now rewrite E | now rewrite E1, E2]
     end.
  (* global variables *)
  1-2: match goal with
       | Ha : gsub_equiv _ ?σ ?τ, Hin : in_gctx _ ?x _, Hτ : forall n, dnfo (?τ n) |- _ =>
           assert (Ed : glsubst d σ = glsubst d τ)
             by (change (glsubst d σ) with d⦃σ⦄; change (glsubst d τ) with d⦃τ⦄;
                 eapply glsubst_agree_entries; [eassumption |];
                 intros ?n ?A ?k HA; match goal with IH : forall n A k, in_ctx _ n A k -> _ |- _ =>
                   eapply IH; eassumption end);
           assert (Nd : nf_l (glsubst d τ))
             by (apply dnfl_nf; change (glsubst d τ) with d⦃τ⦄;
                 apply (proj2 (proj2 (proj2 gsubst_dnf_all))); assumption);
           rewrite Ed; destruct (Ha _ _ Hin) as [E | (j & E1 & E2)];
             [now rewrite E | rewrite E1, E2; cbn [id_obj]]
       end.
  1: exact (eq_sym (pty_id_obj _ _ Nd)).
  1: exact (eq_sym (ptm_id_obj _ _ Nd)).
  (* letbox: under the new binding *)
  all: f_equal; eauto; match goal with IH : forall σ τ, gsub_equiv (gext _ _) σ τ -> _ |- _ =>
         apply IH; [apply gsub_equiv_up; assumption | intros [|n]; cbn; auto using dnfo_goren] end.
Qed.
