(** * The Static Code Lemma, the paper's direction (05:1055; M7_DESIGN.md A3)

    At layers V and C, declaratively equal types and terms are related by
    [≡ₗ] (syntactic equality up to level equivalence), and equal local
    contexts too. With [StaticCode.static_code] (the converse), equality of
    typed syntax at V and C is exactly [≡ₗ].

    Below D no rule computes: the rules usable at V/C are the PER rules,
    the congruences, level and type conversion, and the global-variable
    congruences. The induction is on the equality derivation. The only
    non-structural step is the global variables': their local substitutions
    are normal ([dnfl]) and agree past the variables of [Δ] ([lsub_tail]),
    so entrywise [≡ₗ] gives [lsub_leq] ([l_canon_leq], as [l_canon]). *)
From DeLaM.Syntax Require Export LevelDec.
From DeLaM.Typing Require Export StaticCode.

(** ** Normal local substitutions, entrywise *)

Lemma tm_leq_var_l m x : tm_leq (var m) x -> x = var m.
Proof. destruct x; cbn; intros H; try contradiction; now subst. Qed.
Lemma tm_leq_var_r m x : tm_leq x (var m) -> x = var m.
Proof. intros H. exact (tm_leq_var_l m x (tm_leq_sym _ _ H)). Qed.

Lemma l_canon_leq d1 d2 : nf_l d1 -> nf_l d2 -> (forall n, tm_leq (llk d1 n) (llk d2 n)) -> lsub_leq d1 d2.
Proof.
  revert d2; induction d1 as [k1 | d1 IH t1]; intros d2 N1 N2 H.
  - assert (d2 = lshift k1) as ->.
    { apply shift_canon; [exact N2 |]. intros n. exact (tm_leq_var_l _ _ (H n)). }
    apply lsub_leq_refl.
  - destruct d2 as [k2 | d2 t2].
    + exfalso. assert (E : lcons d1 t1 = lshift k2).
      { apply shift_canon; [exact N1 |]. intros n. exact (tm_leq_var_r _ _ (H n)). }
      discriminate E.
    + cbn in N1, N2 |- *. destruct N1, N2. split.
      * apply IH; auto. intros n; exact (H (S n)).
      * exact (H 0).
Qed.

(** The local substitutions of a global variable. *)
Lemma lsub_leq_entries {d d' Δ Γ} : dnfl d -> dnfl d' -> lsub_tail d Δ Γ -> lsub_tail d' Δ Γ ->
  (forall n A k, in_ctx Δ n A k -> tm_leq (llk d n) (llk d' n)) -> lsub_leq d d'.
Proof.
  intros N N' [_ Ht] [_ Ht'] H. apply l_canon_leq; [exact (dnfl_nf _ N) | exact (dnfl_nf _ N') |].
  intros n. destruct (Nat.lt_ge_cases n (clen Δ)) as [Hn | Hn].
  - destruct (in_ctx_of_lt _ _ Hn) as (A & k & HA). exact (H _ _ _ HA).
  - replace n with (clen Δ + (n - clen Δ)) by lia. rewrite Ht, Ht'. apply tm_leq_refl.
Qed.

(** ** The lemma *)

Lemma lle_C_not_compt {i} : lle i lC -> ~ compt i.
Proof. intros H [-> | ->]; unfold lle in H; cbn in H; lia. Qed.
Lemma lle_C_not_M {i} : lle i lC -> i <> lM.
Proof. intros H ->; unfold lle in H; cbn in H; lia. Qed.

Theorem static_code_eq :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> True) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> True) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> lle i lC -> ty_leq T T') /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> lle i lC -> tm_leq t t') /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> lle i lC -> ctx_leq Γ Γ').
Proof.
  apply typing_mut; intros.
  par: (
    (try exact I;
    (* the computing and M-only rules do not apply below D *)
    try match goal with
        | Hc : compt ?i, Hle : lle ?i lC |- _ => exfalso; exact (lle_C_not_compt Hle Hc)
        | Hle : lle lM lC |- _ => exfalso; exact (lle_C_not_M Hle eq_refl)
        end;
    repeat match goal with
      | IH : lle ?i lC -> _, Hle : lle ?i lC |- _ => specialize (IH Hle)
      | IH : forall n A k, in_ctx _ n A k -> lle ?i lC -> _, Hle : lle ?i lC |- _ =>
          pose proof (fun n A k h => IH n A k h Hle); clear IH
      end;
    first
    [ solve [apply ty_leq_refl | apply tm_leq_refl | apply ctx_leq_refl]
    | solve [eapply ty_leq_sym; eassumption | eapply tm_leq_sym; eassumption
            | eapply ty_leq_trans; eassumption | eapply tm_leq_trans; eassumption]
    | solve [split; [reflexivity | eapply lsub_leq_entries; eassumption]]
    | solve [split; [reflexivity | split; [assumption | eapply lsub_leq_entries; eassumption]]]
    | solve [cbn; repeat split; try assumption; eapply lequiv_leqv; eassumption] ])).
Qed.

Corollary static_code_eqty {G i Γ T T' l} : lle i lC -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> ty_leq T T'.
Proof. intros Hle H. exact (proj1 (proj2 (proj2 (proj2 (proj2 static_code_eq)))) _ _ _ _ _ _ H Hle). Qed.
Corollary static_code_eqtm {G i Γ t t' T l} : lle i lC -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> tm_leq t t'.
Proof. intros Hle H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 static_code_eq))))) _ _ _ _ _ _ _ H Hle). Qed.
Corollary static_code_eqctx {G i Γ Γ'} : lle i lC -> [ G ⊢[ i ] Γ ≅ Γ' ] -> ctx_leq Γ Γ'.
Proof. intros Hle H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 static_code_eq))))) _ _ _ _ H Hle). Qed.

(** ** Equality below D is exactly [≡ₗ] *)

Lemma lle_C_D {i} : lle i lC -> lle i lD.
Proof. unfold lle; cbn; lia. Qed.

Theorem static_code_iff_ty {G i Γ T T' l} : lle i lC -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T' @ l ] ->
  [ G ; Γ ⊢[ i ] T ≅ T' @ l ] <-> ty_leq T T'.
Proof.
  intros Hle HT HT'. split; [exact (static_code_eqty Hle) | exact (static_code_ty (lle_C_D Hle) HT HT')].
Qed.

Theorem static_code_iff_tm {G i Γ t t' T l} : lle i lC -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] <-> tm_leq t t'.
Proof.
  intros Hle Ht Ht'. split; [exact (static_code_eqtm Hle) | exact (static_code_tm (lle_C_D Hle) Ht Ht')].
Qed.

(** Equality of typed syntax below D is decidable. *)
Corollary decl_eqty_dec_static {G i Γ T T' l} : lle i lC -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T' @ l ] ->
  Dec ([ G ; Γ ⊢[ i ] T ≅ T' @ l ]).
Proof. intros Hle HT HT'. exact (dec_iff (iff_sym (static_code_iff_ty Hle HT HT')) (ty_leq_dec T T')). Qed.
Corollary decl_eqtm_dec_static {G i Γ t t' T l} : lle i lC -> [ G ; Γ ⊢[ i ] t : T @ l ] ->
  [ G ; Γ ⊢[ i ] t' : T @ l ] -> Dec ([ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]).
Proof. intros Hle Ht Ht'. exact (dec_iff (iff_sym (static_code_iff_tm Hle Ht Ht')) (tm_leq_dec t t')). Qed.

