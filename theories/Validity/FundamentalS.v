(** * The fundamental theorem with global substitutions, layer P

    Every P-derivation is valid at related global substitutions, at the P
    and the M instance ([⊩^{≥P}_P]), together with its context (and, for
    terms, its type).  Each case is one of the rule lemmas of [RulesS], a
    PER/conversion lemma of [ValidS], or a context lemma.

    M2 transition: still for global contexts that bind context variables
    only; the global variables' cases come next. *)
From DeLaM.Validity Require Export RulesS.

#[local] Existing Instance LR_P.

Section FundamentalS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation GValid := (GValid EP EM).

(** ** The judgments' semantics *)

Section Sem.
Context {E : GenericEq}.
Definition SemCtx (G : gctx) (Γ : ctx) : Prop :=
  GValid G /\ @VCtxS EP EM EP LR_P G Γ /\ @VCtxS EP EM EM LR_P G Γ.
Definition SemTy (G : gctx) (Γ : ctx) (T T' : ty) (l : lvl) : Prop :=
  SemCtx G Γ /\ @VTyS EP EM EP LR_P G Γ T T' l /\ @VTyS EP EM EM LR_P G Γ T T' l.
Definition SemTm (G : gctx) (Γ : ctx) (t t' : tm) (T : ty) (l : lvl) : Prop :=
  SemCtx G Γ /\ @VTyS EP EM EP LR_P G Γ T T l /\ @VTyS EP EM EM LR_P G Γ T T l /\
  @VTmS EP EM EP LR_P G Γ t t' T l /\ @VTmS EP EM EM LR_P G Γ t t' T l.
End Sem.

Lemma ctx_only_GValid {G} : ctx_only G -> GValid G.
Proof. intros HG n D Hin. now rewrite (HG _ _ Hin). Qed.

(** ** Case tactic

    Every goal is closed by a named lemma applied with [simple eapply] (a
    plain [eapply] unfolds the validity definitions while searching for the
    arity, which is costly on large substituted terms). *)

Ltac f_lwf :=
  first [ eassumption | exact I | eapply lequiv_wf_l; eassumption | eapply lequiv_wf_r; eassumption
        | progress cbn [lwf]; first [split; f_lwf | f_lwf] ].
Ltac f_side :=
  first [eassumption | typeclasses eauto | apply lequiv_refl; f_lwf | apply lequiv_sym; eassumption | f_lwf].

(** Presupposed typings of left-hand sides and types. *)
Ltac f_types :=
  repeat match goal with
  | H : wf_tm ?G lD ?Γ ?t ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G lD Γ T l |- _ => fail
      | _ => pose proof (wf_tm_ty (i := lD) eq_refl H)
      end
  | H : eq_ty ?G lD ?Γ ?T ?T' ?l |- _ =>
      lazymatch goal with
      | _ : wf_ty G lD Γ T l |- _ => fail
      | _ => pose proof (eqty_wf_l (i := lD) eq_refl H)
      end
  | H : eq_tm ?G lD ?Γ ?t ?t' ?T ?l |- _ =>
      lazymatch goal with
      | _ : wf_tm G lD Γ t T l |- _ => fail
      | _ => pose proof (eqtm_wf_l (i := lD) eq_refl H)
      end
  end.

Ltac f_ctx :=
  first [ eassumption | apply VCtxS_nil | solve [simple eapply VCtxS_var; f_side]
        | solve [simple eapply VCtxS_tl; f_side]
        | solve [simple eapply VCtxS_ext; f_side] ].

Ltac f_rules :=
  first
  [ solve [simple eapply VS_var; f_side]
  | solve [simple eapply VS_nat; f_side] | solve [simple eapply VS_zero; f_side] | solve [simple eapply VS_code_nat; f_side]
  | solve [simple eapply VS_El_nat; f_side]
  | solve [simple eapply VS_succ; f_side]
  | solve [simple eapply VS_U; f_side] | solve [simple eapply VS_El; f_side]
  | solve [simple eapply VS_code_U; f_side] | solve [simple eapply VS_El_U; f_side]
  | solve [simple eapply VS_pi; f_side] | solve [simple eapply VS_app; f_side]
  | solve [simple eapply VS_lam; f_side] | solve [simple eapply VS_natrec; f_side]
  | solve [simple eapply VS_code_pi; f_side]
  | solve [simple eapply VS_beta; f_side] | solve [simple eapply VS_eta; f_side]
  | solve [simple eapply VS_natrec_zero; f_side] | solve [simple eapply VS_natrec_succ; f_side]
  | solve [simple eapply VS_El_pi; f_side] ].

Ltac f_ty :=
  first
  [ eassumption
  | solve [simple eapply VTyS_sym; f_side] | solve [simple eapply VTyS_trans; f_side]
  | solve [simple eapply VTyS_lconv; f_side]
  | solve [simple eapply VTyS_trans; [eassumption | simple eapply VTyS_sym; f_side]]
  | solve [simple eapply VTyS_trans; [simple eapply VTyS_sym; f_side | eassumption]]
  | solve [simple eapply VTyS_lookup; f_side]
  | solve [simple eapply VTyS_single; f_side]
  | f_rules
  | solve [simple eapply VTyS_single; [eassumption | f_rules]]
  | solve [simple eapply VTyS_single;
           [ first [eassumption | simple eapply VTyS_trans; [eassumption | simple eapply VTyS_sym; f_side]]
           | first [eassumption | simple eapply VTmS_trans; [eassumption | simple eapply VTmS_sym; f_side]]]] ].

Ltac f_tm :=
  first
  [ eassumption
  | solve [simple eapply VTmS_sym; f_side] | solve [simple eapply VTmS_trans; f_side]
  | solve [simple eapply VTmS_conv; f_side] | solve [simple eapply VTmS_lconv; f_side]
  | f_rules ].

Ltac f_goal :=
  lazymatch goal with
  | |- GValid _ => first [eassumption | apply ctx_only_GValid; assumption]
  | |- @VCtxS _ _ _ _ _ _ => f_ctx
  | |- @VTyS _ _ _ _ _ _ _ _ _ => f_ty
  | |- @VTmS _ _ _ _ _ _ _ _ _ _ => f_tm
  end.

(** ** The theorem *)

Theorem fundamentalS :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> i = lD -> ctx_only G -> SemCtx G Γ) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> i = lD -> ctx_only G -> SemTy G Γ T T l) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> i = lD -> ctx_only G -> SemTm G Γ t t T l) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> i = lD -> ctx_only G -> SemTy G Γ T T' l) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> i = lD -> ctx_only G ->
     SemTm G Γ t t' T l) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; try exact I;
    try match goal with H : lM = lD |- _ => discriminate H end;
    try match goal with
        | Hc : ctx_only _, Hin : in_gctx _ _ (gdTm _ _ _ _) |- _ => discriminate (Hc _ _ Hin)
        | Hc : ctx_only _, Hin : in_gctx _ _ (gdTy _ _ _) |- _ => discriminate (Hc _ _ Hin)
        end;
    ft_prep;
    repeat match goal with Hc : ctx_only ?G, IH : ctx_only ?G -> _ |- _ => specialize (IH Hc) end;
    unfold SemTy, SemTm in *; unfold SemCtx in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    f_types;
    repeat split.
  all: f_goal.
Qed.

End FundamentalS.
