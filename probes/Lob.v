(** * Löb at the reflexive cell R: [fix] makes later code

    Heather-coq issues #47 and #54 (`docs/design/LOB.md` has the findings),
    after the layer-structure probe (`probes/LayerStructure.v`, #48).  That
    probe placed the reflexive cell R in the grid: a program row [P₀] that
    hosts and analyses its own code but runs it only from one level up.
    This one adds Löb there.

    The toy has two layers, R (depth 0) and U (depth 1), with [R ≤ U].
    [▷A] is R's typed, closed code of type [A], formable at both.
    - Löb: [z : ▷A ⊢_R M : A] gives [lfix A M : ▷A], code that contains
      itself.  [lfix] is an opaque code node: no reduction or analysis
      unfolds it.  Its internal form [llob : ▷(▷A → A) → ▷A] is the GL
      axiom, and [lapp : ▷(A → B) → ▷A → ▷B] is K.
    - Analysis: [csize], the size of the code's syntax tree.
    - Release at U: [run : ▷A → A] (axiom T), unfolding an [lfix] once.
    - At R itself: no [run].  Instead a fuelled run [runk n] (the delay
      observed for [n] steps) and a grounded release [evalg t d], which
      runs code that is not headed by [lfix] and returns [d] for code that
      is (Weaver's meaningfulness predicate as a code head).

    Results (no axioms):
    - normalization at both layers, so [Empty] and [▷Empty] are empty;
    - R cannot prove its own consistency: no closed R-term has type
      [▷Empty → Empty], while U has [λx. run x] (Gödel's second theorem, as
      GL has it);
    - the liar [lfix z. succ (run z)] unfolds forever where [run] is at R,
      and its fuelled form at R answers [n] with fuel [n];
    - four side conditions, each with a counterexample: no T at R, Löb's
      body closed, [lfix] not unfolded by conversion, and code formers
      that keep [lfix]-headed code ungrounded.

    Standalone: [coqc probes/Lob.v]. *)
From Coq Require Import List Arith Lia.
Import ListNotations.

(** ** Syntax *)

Inductive lay := LR | LU.

(** [R ≤ U]: R's programs are U's programs. *)
Definition lle (i j : lay) : Prop := match i, j with LU, LR => False | _, _ => True end.
Definition dep (j : lay) : nat := match j with LR => 0 | LU => 1 end.

Inductive ty :=
| tNat
| tEmpty
| tArr (A B : ty)
| tLater (A : ty).

Inductive tm :=
| var (x : nat)
| lam (A : ty) (t : tm)
| app (t u : tm)
| lit (k : nat)
| succ (t : tm)
| lbox (s : tm)          (* code of a closed R-term *)
| lfix (A : ty) (M : tm) (* Löb: code of [M], whose variable 0 is the code itself *)
| lhole (A : ty)         (* untypable: an unknown code, used only by the model of [no_R_consistency] *)
| csize (t : tm)
| lapp (B : ty) (t u : tm)
| llob (A : ty) (t : tm)
| evalg (t d : tm)
| runk (n : nat) (t d : tm)
| run (t : tm).

Definition upren (ξ : nat -> nat) (x : nat) : nat :=
  match x with 0 => 0 | S x => S (ξ x) end.

(** [lbox]'s contents are closed, so renaming and substitution stop there.
    [lfix]'s body is closed but for its own variable when Löb is closed (the
    sound configuration); the open configuration lets it see the context,
    so substitution goes under [lfix]. *)
Fixpoint ren (ξ : nat -> nat) (t : tm) : tm :=
  match t with
  | var x => var (ξ x)
  | lam A t => lam A (ren (upren ξ) t)
  | app t u => app (ren ξ t) (ren ξ u)
  | lit k => lit k
  | succ t => succ (ren ξ t)
  | lbox s => lbox s
  | lfix A M => lfix A (ren (upren ξ) M)
  | lhole A => lhole A
  | csize t => csize (ren ξ t)
  | lapp B t u => lapp B (ren ξ t) (ren ξ u)
  | llob A t => llob A (ren ξ t)
  | evalg t d => evalg (ren ξ t) (ren ξ d)
  | runk n t d => runk n (ren ξ t) (ren ξ d)
  | run t => run (ren ξ t)
  end.

Definition up (σ : nat -> tm) (x : nat) : tm :=
  match x with 0 => var 0 | S x => ren S (σ x) end.

Fixpoint subst (σ : nat -> tm) (t : tm) : tm :=
  match t with
  | var x => σ x
  | lam A t => lam A (subst (up σ) t)
  | app t u => app (subst σ t) (subst σ u)
  | lit k => lit k
  | succ t => succ (subst σ t)
  | lbox s => lbox s
  | lfix A M => lfix A (subst (up σ) M)
  | lhole A => lhole A
  | csize t => csize (subst σ t)
  | lapp B t u => lapp B (subst σ t) (subst σ u)
  | llob A t => llob A (subst σ t)
  | evalg t d => evalg (subst σ t) (subst σ d)
  | runk n t d => runk n (subst σ t) (subst σ d)
  | run t => run (subst σ t)
  end.

Definition scons (u : tm) (σ : nat -> tm) (x : nat) : tm :=
  match x with 0 => u | S x => σ x end.

Fixpoint size (t : tm) : nat :=
  match t with
  | var _ | lit _ | lhole _ => 1
  | lam _ t | succ t | lbox t | lfix _ t | csize t | llob _ t | run t => S (size t)
  | app t u | lapp _ t u | evalg t u | runk _ t u => S (size t + size u)
  end.

(** *** Code values *)

Definition cval (t : tm) : Prop :=
  match t with lbox _ | lfix _ _ | lhole _ => True | _ => False end.
(** Code with contents: everything but a hole. *)
Definition runnable (t : tm) : Prop :=
  match t with lbox _ | lfix _ _ => True | _ => False end.
(** Grounded code: not headed by [lfix]. *)
Definition isbox (t : tm) : Prop := match t with lbox _ => True | _ => False end.

(** What running the code does: its contents, and for [lfix] its body with
    the code itself for its variable (one unfolding). *)
Definition contents (t : tm) : tm :=
  match t with
  | lbox s => s
  | lfix A M => subst (scons (lfix A M) var) M
  | _ => var 0
  end.

(** What [csize] reads: an [lfix] node and its body. *)
Definition csz (t : tm) : nat :=
  match t with lbox s => size s | lfix _ M => S (size M) | _ => 0 end.

(** K.  Two grounded codes apply to grounded code.  If either is headed by
    [lfix], so is the result: its variable is unused, and its body is the
    application of the two unfoldings.  [leak] is the counterexample's rule
    instead, which grounds the result. *)
Definition kapp (leak : bool) (B : ty) (v w : tm) : tm :=
  match v, w with
  | lhole _, _ | _, lhole _ => lhole B
  | lbox s, lbox u => lbox (app s u)
  | _, _ =>
      if leak then lbox (app (contents v) (contents w))
      else lfix B (app (ren S (contents v)) (ren S (contents w)))
  end.

(** The GL axiom: [llob ⌜f⌝] is [lfix z. f z]. *)
Definition lob (A : ty) (v : tm) : tm :=
  match v with
  | lhole _ => lhole A
  | _ => lfix A (app (ren S (contents v)) (var 0))
  end.

(** Fuel.  A fuelled run with fuel [S n] caps every fuelled run in what it
    runs at [n].  Grounded code is capped too ([evalg] runs it without
    fuel); an [lfix] is left alone, since only a run unfolds it, and that
    run caps the unfolding. *)
Fixpoint capk (n : nat) (t : tm) : tm :=
  match t with
  | var x => var x
  | lam A t => lam A (capk n t)
  | app t u => app (capk n t) (capk n u)
  | lit k => lit k
  | succ t => succ (capk n t)
  | lbox s => lbox (capk n s)
  | lfix A M => lfix A M
  | lhole A => lhole A
  | csize t => csize (capk n t)
  | lapp B t u => lapp B (capk n t) (capk n u)
  | llob A t => llob A (capk n t)
  | evalg t d => evalg (capk n t) (capk n d)
  | runk m t d => runk (Nat.min m n) (capk n t) (capk n d)
  | run t => run (capk n t)
  end.

(** Every fuelled run outside an [lfix] has fuel below [N]. *)
Fixpoint fuel_lt (N : nat) (t : tm) : Prop :=
  match t with
  | var _ | lit _ | lfix _ _ | lhole _ => True
  | lam _ t | succ t | lbox t | csize t | llob _ t | run t => fuel_lt N t
  | app t u | lapp _ t u | evalg t u => fuel_lt N t /\ fuel_lt N u
  | runk m t d => m < N /\ fuel_lt N t /\ fuel_lt N d
  end.

Lemma fuel_lt_mono N N' t : N <= N' -> fuel_lt N t -> fuel_lt N' t.
Proof. intros HN; induction t; cbn; intuition lia. Qed.

Lemma fuel_bound t : exists N, fuel_lt N t.
Proof.
  induction t; cbn;
    repeat match goal with H : exists N, fuel_lt N _ |- _ => destruct H end;
    try solve [exists 0; exact I | eauto].
  all: first
    [ exists (x + x0 + S n); repeat split; try lia; eapply fuel_lt_mono; try eassumption; lia
    | exists (x + x0); split; eapply fuel_lt_mono; try eassumption; lia ].
Qed.

Lemma fuel_lt_capk n t : fuel_lt (S n) (capk n t).
Proof. induction t; cbn; intuition lia. Qed.

(** *** Substitution lemmas *)

Lemma ren_ext ξ ζ t : (forall x, ξ x = ζ x) -> ren ξ t = ren ζ t.
Proof.
  revert ξ ζ; induction t; intros ξ ζ H; cbn; f_equal; auto.
  all: apply IHt; intros []; cbn; auto.
Qed.

Lemma subst_ext σ τ t : (forall x, σ x = τ x) -> subst σ t = subst τ t.
Proof.
  revert σ τ; induction t; intros σ τ H; cbn; f_equal; auto.
  all: apply IHt; intros []; cbn; f_equal; auto.
Qed.

Lemma ren_ren ξ ζ t : ren ξ (ren ζ t) = ren (fun x => ξ (ζ x)) t.
Proof.
  revert ξ ζ; induction t; intros ξ ζ; cbn; f_equal; auto.
  all: rewrite IHt; apply ren_ext; intros []; reflexivity.
Qed.

Lemma ren_subst σ ξ t : subst σ (ren ξ t) = subst (fun x => σ (ξ x)) t.
Proof.
  revert σ ξ; induction t; intros σ ξ; cbn; f_equal; auto.
  all: rewrite IHt; apply subst_ext; intros []; reflexivity.
Qed.

Lemma subst_ren ξ σ t : ren ξ (subst σ t) = subst (fun x => ren ξ (σ x)) t.
Proof.
  revert ξ σ; induction t; intros ξ σ; cbn; f_equal; auto.
  all: rewrite IHt; apply subst_ext; intros []; cbn; [reflexivity |].
  all: rewrite !ren_ren; apply ren_ext; reflexivity.
Qed.

Lemma subst_subst τ σ t : subst τ (subst σ t) = subst (fun x => subst τ (σ x)) t.
Proof.
  revert τ σ; induction t; intros τ σ; cbn; f_equal; auto.
  all: rewrite IHt; apply subst_ext; intros []; cbn; [reflexivity |].
  all: rewrite ren_subst, subst_ren; apply subst_ext; reflexivity.
Qed.

Lemma subst_var t : subst var t = t.
Proof.
  induction t; cbn; f_equal; auto.
  all: rewrite <- IHt at 2; apply subst_ext; intros []; reflexivity.
Qed.

Lemma subst_beta σ u t :
  subst (scons u var) (subst (up σ) t) = subst (scons u σ) t.
Proof.
  rewrite subst_subst; apply subst_ext; intros [|x]; cbn; [reflexivity |].
  rewrite ren_subst; apply subst_var.
Qed.

Lemma subst_ren_S u t : subst (scons u var) (ren S t) = t.
Proof. rewrite ren_subst; apply subst_var. Qed.

(** ** Reduction: weak head, call by name, untyped *)

Section Red.
Variable leak : bool.

Inductive red : tm -> tm -> Prop :=
| r_beta A t u : red (app (lam A t) u) (subst (scons u var) t)
| r_app t t' u : red t t' -> red (app t u) (app t' u)
| r_succ_lit k : red (succ (lit k)) (lit (S k))
| r_succ t t' : red t t' -> red (succ t) (succ t')
| r_csize_v v : cval v -> red (csize v) (lit (csz v))
| r_csize t t' : red t t' -> red (csize t) (csize t')
| r_lapp_v B v w : cval v -> cval w -> red (lapp B v w) (kapp leak B v w)
| r_lapp1 B t t' u : red t t' -> red (lapp B t u) (lapp B t' u)
| r_lapp2 B v u u' : cval v -> red u u' -> red (lapp B v u) (lapp B v u')
| r_llob_v A v : cval v -> red (llob A v) (lob A v)
| r_llob A t t' : red t t' -> red (llob A t) (llob A t')
| r_evalg_box s d : red (evalg (lbox s) d) s
| r_evalg_nobox v d : cval v -> ~ isbox v -> red (evalg v d) d
| r_evalg t t' d : red t t' -> red (evalg t d) (evalg t' d)
| r_runk_zero t d : red (runk 0 t d) d
| r_runk_hit n v d : runnable v -> red (runk (S n) v d) (capk n (contents v))
| r_runk_hole n A d : red (runk (S n) (lhole A) d) d
| r_runk n t t' d : red t t' -> red (runk (S n) t d) (runk (S n) t' d)
| r_run v : runnable v -> red (run v) (contents v)
| r_run_c t t' : red t t' -> red (run t) (run t').

Inductive reds : tm -> tm -> Prop :=
| reds_refl t : reds t t
| reds_step t t' t'' : red t t' -> reds t' t'' -> reds t t''.

Definition value (t : tm) : Prop :=
  match t with lam _ _ | lit _ | lbox _ | lfix _ _ | lhole _ => True | _ => False end.

Definition evalto (t v : tm) : Prop := reds t v /\ value v.

Lemma cval_value v : cval v -> value v.
Proof. destruct v; cbn; tauto. Qed.

Lemma value_nored t t' : value t -> ~ red t t'.
Proof. destruct t; cbn; intros Hv Hr; try contradiction; inversion Hr. Qed.

Lemma cval_nored t t' : cval t -> ~ red t t'.
Proof. intros H; apply value_nored, cval_value, H. Qed.

Lemma runnable_cval v : runnable v -> cval v.
Proof. destruct v; cbn; tauto. Qed.

Ltac no_red := match goal with
  | H : red ?v _, Hv : cval ?v |- _ => exfalso; exact (cval_nored _ _ Hv H)
  | H : red ?v _, Hv : runnable ?v |- _ => exfalso; exact (cval_nored _ _ (runnable_cval _ Hv) H)
  | H : red (lam _ _) _ |- _ => inversion H
  | H : red (lit _) _ |- _ => inversion H
  | H : red (lbox _) _ |- _ => inversion H
  | H : red (lfix _ _) _ |- _ => inversion H
  | H : red (lhole _) _ |- _ => inversion H
  | H : runnable (lhole _) |- _ => destruct H
  | H : ~ isbox (lbox _) |- _ => exfalso; exact (H I)
  | H : cval (lam _ _) |- _ => destruct H
  end.

Lemma red_det t u u' : red t u -> red t u' -> u = u'.
Proof.
  intros H; revert u'; induction H; intros u'' H'; inversion H'; subst;
    try reflexivity; repeat no_red; f_equal; auto.
Qed.

Lemma reds_trans t t' t'' : reds t t' -> reds t' t'' -> reds t t''.
Proof. induction 1; eauto using reds. Qed.

Lemma reds_cong (f : tm -> tm) :
  (forall t t', red t t' -> red (f t) (f t')) ->
  forall t t', reds t t' -> reds (f t) (f t').
Proof. intros Hf; induction 1; eauto using reds. Qed.

Lemma red1 t t' : red t t' -> reds t t'.
Proof. intros H; econstructor; [exact H | constructor]. Qed.

Lemma evalto_det t v v' : evalto t v -> evalto t v' -> v = v'.
Proof.
  intros [H Hv]; revert v' Hv; induction H as [t | t t1 t2 Hs _ IH];
    intros v' Hv [H' Hv'].
  - destruct H' as [| t t1 t2' Hs']; [reflexivity |].
    exfalso; exact (value_nored _ _ Hv Hs').
  - destruct H' as [| t t1' t2' Hs' H'].
    + exfalso; exact (value_nored _ _ Hv' Hs).
    + rewrite (red_det _ _ _ Hs Hs') in IH; apply IH; auto; split; auto.
Qed.

Lemma evalto_value v : value v -> evalto v v.
Proof. split; [constructor | assumption]. Qed.

Lemma evalto_value_inv v v' : value v -> evalto v v' -> v' = v.
Proof. intros Hv H; exact (evalto_det _ _ _ H (evalto_value _ Hv)). Qed.

Lemma evalto_expand t t1 v : reds t t1 -> evalto t1 v -> evalto t v.
Proof. intros H [H1 Hv]; split; [exact (reds_trans _ _ _ H H1) | exact Hv]. Qed.

(** *** Divergence: the never-ending delay *)

(** A term diverges when it always takes one more step: the trace of its
    reduction is the delay [never]. *)
CoInductive diverges : tm -> Prop :=
| dv t t1 t' : red t t1 -> reds t1 t' -> diverges t' -> diverges t.

Lemma diverges_back t t' : reds t t' -> diverges t' -> diverges t.
Proof.
  intros [| t0 a t1 Ha Hr] Hd; [exact Hd |].
  exact (dv _ _ _ Ha Hr Hd).
Qed.

Lemma diverges_no_value t : diverges t -> ~ exists v, evalto t v.
Proof.
  intros Hd (v & H & Hv); induction H as [t0 | t0 t1 v Hs Hr IH].
  - destruct Hd as [t0 a t' Ha _ _]; exact (value_nored _ _ Hv Ha).
  - apply IH; [| exact Hv].
    destruct Hd as [t0 a t' Ha Hr' Hd'].
    rewrite (red_det _ _ _ Hs Ha); exact (diverges_back _ _ Hr' Hd').
Qed.

(** A term that reduces to itself in one or more steps diverges. *)
Lemma cycle_diverges t t1 : red t t1 -> reds t1 t -> diverges t.
Proof. intros H1 H2; cofix CIH; exact (dv _ _ _ H1 H2 CIH). Qed.

End Red.

Arguments value : clear implicits.
Global Hint Resolve red1 : core.

(** ** Typing *)

(** A configuration: whether R runs its own code ([c_tR], axiom T at R),
    and whether Löb's body sees the context ([c_open]).  The sound
    configuration has neither. *)
Record cfg := { c_tR : bool; c_open : bool }.
Definition good : cfg := {| c_tR := false; c_open := false |}.

Section Typing.
Variable C : cfg.

Definition evals (j : lay) : bool := match j with LU => true | LR => c_tR C end.
Definition ctxL (Γ : list ty) : list ty := if c_open C then Γ else [].

(** [Γ ⊢ⱼ t : A].  Code's contents are R-terms; [lfix]'s body is an R-term
    whose variable 0 is the code itself. *)
Inductive typed : lay -> list ty -> tm -> ty -> Prop :=
| ty_var j Γ x A : nth_error Γ x = Some A -> typed j Γ (var x) A
| ty_lam j Γ A B t : typed j (A :: Γ) t B -> typed j Γ (lam A t) (tArr A B)
| ty_app j Γ A B t u : typed j Γ t (tArr A B) -> typed j Γ u A -> typed j Γ (app t u) B
| ty_lit j Γ k : typed j Γ (lit k) tNat
| ty_succ j Γ t : typed j Γ t tNat -> typed j Γ (succ t) tNat
| ty_lbox j Γ A s : typed LR [] s A -> typed j Γ (lbox s) (tLater A)
| ty_lfix j Γ A M : typed LR (tLater A :: ctxL Γ) M A -> typed j Γ (lfix A M) (tLater A)
| ty_csize j Γ A t : typed j Γ t (tLater A) -> typed j Γ (csize t) tNat
| ty_lapp j Γ A B t u :
    typed j Γ t (tLater (tArr A B)) -> typed j Γ u (tLater A) -> typed j Γ (lapp B t u) (tLater B)
| ty_llob j Γ A t : typed j Γ t (tLater (tArr (tLater A) A)) -> typed j Γ (llob A t) (tLater A)
| ty_evalg j Γ A t d : typed j Γ t (tLater A) -> typed j Γ d A -> typed j Γ (evalg t d) A
| ty_runk n j Γ A t d : typed j Γ t (tLater A) -> typed j Γ d A -> typed j Γ (runk n t d) A
| ty_run j Γ A t : evals j = true -> typed j Γ t (tLater A) -> typed j Γ (run t) A
| ty_lift i j Γ t A : lle i j -> typed i Γ t A -> typed j Γ t A.

Lemma ty_lift_R j Γ t A : typed LR Γ t A -> typed j Γ t A.
Proof. intros H; apply (ty_lift LR); [destruct j; exact I | exact H]. Qed.

(** *** Inversions *)

Lemma typed_lbox_inv j Γ s T : typed j Γ (lbox s) T -> exists A, T = tLater A /\ typed LR [] s A.
Proof. intros H; remember (lbox s) as t eqn:E; induction H; inversion E; subst; eauto. Qed.

Lemma typed_lfix_inv j Γ B M T : typed j Γ (lfix B M) T ->
  T = tLater B /\ typed LR (tLater B :: ctxL Γ) M B.
Proof. intros H; remember (lfix B M) as t eqn:E; induction H; inversion E; subst; eauto. Qed.

Lemma typed_lhole_inv j Γ A T : ~ typed j Γ (lhole A) T.
Proof. intros H; remember (lhole A) as t eqn:E; induction H; inversion E; subst; eauto. Qed.

(** *** Renaming and substitution *)

Lemma typed_ren j Γ t A : typed j Γ t A -> forall Δ ξ,
  (forall x B, nth_error Γ x = Some B -> nth_error Δ (ξ x) = Some B) ->
  typed j Δ (ren ξ t) A.
Proof.
  induction 1; intros Δ ξ Hξ; cbn; try solve [econstructor; eauto].
  - apply ty_lam, IHtyped; intros [|x] B'; cbn; auto.
  - apply ty_lfix, IHtyped; intros [|x] B'; cbn; [auto |].
    unfold ctxL in *; destruct (c_open C); [apply Hξ | destruct x; discriminate].
Qed.

(** A substitution of R-terms: [σ x] is an R-term of [Γ x]'s type in [Δ]. *)
Lemma typed_subst j Γ t A : typed j Γ t A -> forall Δ σ,
  (forall x B, nth_error Γ x = Some B -> typed LR Δ (σ x) B) ->
  typed j Δ (subst σ t) A.
Proof.
  induction 1; intros Δ σ Hσ; cbn; try solve [econstructor; eauto].
  - apply ty_lift_R; eauto.
  - apply ty_lam, IHtyped; intros [|x] B' Hx; cbn in *.
    + apply ty_var; exact Hx.
    + apply (typed_ren _ Δ); [eauto | exact (fun _ _ h => h)].
  - apply ty_lfix, IHtyped; intros [|x] B' Hx; cbn in *.
    + apply ty_var; exact Hx.
    + unfold ctxL in *; destruct (c_open C); [| destruct x; discriminate].
      apply (typed_ren _ Δ); [eauto | exact (fun _ _ h => h)].
Qed.

(** Running well-typed code gives a well-typed R-term. *)
Lemma typed_contents v A : typed LR [] v (tLater A) -> runnable v -> typed LR [] (contents v) A.
Proof.
  intros H Hr; destruct v; try destruct Hr; cbn.
  - destruct (typed_lbox_inv _ _ _ _ H) as (A' & [= <-] & Hs); exact Hs.
  - destruct (typed_lfix_inv _ _ _ _ _ H) as ([= <-] & HM).
    apply (typed_subst _ _ _ _ HM); intros [|x] B Hx; cbn in *.
    + injection Hx as <-; exact H.
    + unfold ctxL in Hx; destruct (c_open C); destruct x; discriminate.
Qed.

Lemma typed_capk n j Γ t A : typed j Γ t A -> typed j Γ (capk n t) A.
Proof. induction 1; cbn; eauto using typed. Qed.

(** Closed terms are fixed by substitution. *)
Lemma typed_subst_closed j Γ t A : typed j Γ t A ->
  forall σ, (forall x, x < length Γ -> σ x = var x) -> subst σ t = t.
Proof.
  induction 1; intros σ Hσ; cbn; [apply Hσ, nth_error_Some; congruence | ..];
    f_equal; auto.
  - apply IHtyped; intros [|x] Hx; cbn; [reflexivity |].
    rewrite Hσ; [reflexivity | cbn in Hx; lia].
  - apply IHtyped; intros [|x] Hx; cbn; [reflexivity |].
    unfold ctxL in Hx; destruct (c_open C); cbn in Hx; [| lia].
    rewrite Hσ; [reflexivity | lia].
Qed.

Lemma closed_subst t A σ : typed LR [] t A -> subst σ t = t.
Proof. intros H; apply (typed_subst_closed _ _ _ _ H); cbn; lia. Qed.

End Typing.

(** ** Metatheory *)

(** The relation does not depend on layers.  Code is related when both
    sides evaluate to one and the same well-typed code value (syntactic
    equality, since [csize] sees syntax), and grounded code ([lbox]) also
    has related contents, which is what makes [evalg] safe at R.  Nothing
    is asked of an [lfix]'s contents: that would be the circle Löb closes.
    Running an [lfix] is justified instead by the fundamental theorem one
    depth down ([run] at U) or at lower fuel ([runk]).

    [h] admits holes: unknown code, with no contents.  It is the model in
    which R's terms are shown parametric in the code they cannot run
    ([no_R_consistency]); the fundamental theorem holds with holes for
    R-terms, which do not [run]. *)
Section Metatheory.
Variable C : cfg.
Hypotheses (HtR : c_tR C = false) (Hopen : c_open C = false).
Variable h : bool.
Local Notation red := (red false).
Local Notation reds := (reds false).
Local Notation evalto := (evalto false).
Local Notation typed := (typed C).
Implicit Types (t u v w s d : tm) (A B : ty) (Γ : list ty) (σ : nat -> tm).

Fixpoint R (A : ty) : tm -> tm -> Prop :=
  match A with
  | tNat => fun t t' => exists k, evalto t (lit k) /\ evalto t' (lit k)
  | tEmpty => fun _ _ => False
  | tArr A B => fun t t' => forall u u', R A u u' -> R B (app t u) (app t' u')
  | tLater A => fun t t' => exists w, evalto t w /\ evalto t' w /\
      match w with
      | lbox s => typed LR [] w (tLater A) /\ R A s s
      | lfix _ _ => typed LR [] w (tLater A)
      | lhole B => h = true /\ B = A
      | _ => False
      end
  end.

Lemma R_sym A t t' : R A t t' -> R A t' t.
Proof.
  revert t t'; induction A; cbn; intros t t' H; try contradiction.
  - destruct H as (k & H1 & H2); eauto.
  - intros u u' Hu; apply IHA2, H, IHA1, Hu.
  - destruct H as (w & H1 & H2 & H3); eauto.
Qed.

Lemma R_trans A t t' t'' : R A t t' -> R A t' t'' -> R A t t''.
Proof.
  revert t t' t''; induction A; cbn; intros t t' t'' H H'; try contradiction.
  - destruct H as (k & H1 & H2), H' as (k' & H1' & H2').
    pose proof (evalto_det _ _ _ _ H2 H1') as E; injection E as ->; eauto.
  - intros u u' Hu.
    apply (IHA2 _ (app t' u')); [apply H, Hu |].
    apply H', (IHA1 _ u); [apply R_sym, Hu | exact Hu].
  - destruct H as (w & H1 & H2 & H3), H' as (w' & H1' & H2' & _).
    pose proof (evalto_det _ _ _ _ H2 H1') as <-; eauto.
Qed.

Lemma R_refl_l A t t' : R A t t' -> R A t t.
Proof. intros H; exact (R_trans _ _ _ _ H (R_sym _ _ _ H)). Qed.

(** Weak-head expansion. *)
Lemma R_expand A t t1 t' t1' : reds t t1 -> reds t' t1' -> R A t1 t1' -> R A t t'.
Proof.
  revert t t1 t' t1'; induction A; cbn; intros t t1 t' t1' H H' HR; try contradiction.
  - destruct HR as (k & H1 & H2); eauto using evalto_expand.
  - intros u u' Hu; apply (IHA2 _ (app t1 u) _ (app t1' u')); [| | apply HR, Hu].
    all: apply (reds_cong _ (fun t => app t _)); [intros; constructor; assumption | assumption].
  - destruct HR as (w & H1 & H2 & H3); exists w.
    split; [| split]; [eapply evalto_expand; eassumption .. | exact H3].
Qed.

Lemma R_red1 A t t1 t' : red t t1 -> R A t1 t' -> R A t t'.
Proof. intros H; apply R_expand; [apply red1, H | constructor]. Qed.

(** Both sides reduce, each to a term related to the other's. *)
Lemma R_red2 A t t1 t' t1' : red t t1 -> red t' t1' -> R A t1 t1' -> R A t t'.
Proof. intros H H'; apply R_expand; apply red1; assumption. Qed.

Definition Rsub (Γ : list ty) (σ σ' : nat -> tm) : Prop :=
  forall x A, nth_error Γ x = Some A -> R A (σ x) (σ' x).

Lemma Rsub_cons Γ A σ σ' u u' :
  Rsub Γ σ σ' -> R A u u' -> Rsub (A :: Γ) (scons u σ) (scons u' σ').
Proof. intros H Hu [|x] B; cbn; [intros [= <-]; exact Hu | apply H]. Qed.

Lemma Rsub_var_nil : Rsub [] var var.
Proof. intros [] ?; discriminate. Qed.

(** *** The cases *)

Lemma R_lam A B t t' σ σ' :
  (forall u u', R A u u' -> R B (subst (scons u σ) t) (subst (scons u' σ') t')) ->
  R (tArr A B) (lam A (subst (up σ) t)) (lam A (subst (up σ') t')).
Proof.
  intros IH u u' Hu.
  apply (R_red2 _ _ (subst (scons u var) (subst (up σ) t)) _
           (subst (scons u' var) (subst (up σ') t'))); [constructor | constructor |].
  rewrite !subst_beta; apply IH, Hu.
Qed.

Lemma R_lit k : R tNat (lit k) (lit k).
Proof. exists k; split; apply evalto_value; exact I. Qed.

Lemma R_succ t t' : R tNat t t' -> R tNat (succ t) (succ t').
Proof.
  intros (k & [H Hv] & [H' Hv']).
  assert (Hc : forall t0 t1, reds t0 t1 -> reds (succ t0) (succ t1))
    by (apply reds_cong; constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hc _ _ H) (Hc _ _ H')).
  apply (R_red2 _ _ (lit (S k)) _ (lit (S k))); [constructor | constructor | apply R_lit].
Qed.

(** A code value with its side condition is related to itself. *)
Lemma R_later_val A w : value w ->
  match w with
  | lbox s => typed LR [] w (tLater A) /\ R A s s
  | lfix _ _ => typed LR [] w (tLater A)
  | lhole B => h = true /\ B = A
  | _ => False
  end -> R (tLater A) w w.
Proof. intros Hv Hw; exists w; split; [| split]; [apply evalto_value; exact Hv .. | exact Hw]. Qed.

(** Code evaluation, its congruences and its side conditions: unpack both
    sides of a related pair of codes into the one value they reach. *)
Lemma R_later_inv A t t' : R (tLater A) t t' ->
  exists w, reds t w /\ reds t' w /\ cval w /\
    match w with
    | lbox s => typed LR [] w (tLater A) /\ R A s s
    | lfix _ _ => typed LR [] w (tLater A)
    | lhole B => h = true /\ B = A
    | _ => False
    end.
Proof.
  intros (w & [H _] & [H' _] & Hw); exists w; split; [| split; [| split]]; auto.
  destruct w; cbn; tauto.
Qed.

Lemma R_csize A t t' : R (tLater A) t t' -> R tNat (csize t) (csize t').
Proof.
  intros Ht; destruct (R_later_inv _ _ _ Ht) as (w & H & H' & Hc & _).
  assert (Hr : forall t0 t1, reds t0 t1 -> reds (csize t0) (csize t1))
    by (apply reds_cong; constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hr _ _ H) (Hr _ _ H')).
  apply (R_red2 _ _ (lit (csz w)) _ (lit (csz w))); [constructor; exact Hc .. | apply R_lit].
Qed.

Lemma reds_lapp B t t' u : reds t t' -> reds (lapp B t u) (lapp B t' u).
Proof. apply (reds_cong _ (fun t => lapp B t u)); constructor; assumption. Qed.

Lemma reds_lapp2 B v u u' : cval v -> reds u u' -> reds (lapp B v u) (lapp B v u').
Proof. intros Hv; apply (reds_cong _ (fun u => lapp B v u)); constructor; assumption. Qed.

Lemma R_lapp A B t t' u u' :
  R (tLater (tArr A B)) t t' -> R (tLater A) u u' -> R (tLater B) (lapp B t u) (lapp B t' u').
Proof.
  intros Ht Hu.
  destruct (R_later_inv _ _ _ Ht) as (v & H1 & H1' & Hv & Hvok).
  destruct (R_later_inv _ _ _ Hu) as (w & H2 & H2' & Hw & Hwok).
  apply (R_expand _ _ (lapp B v w) _ (lapp B v w)).
  1, 2: eapply reds_trans; [apply reds_lapp; eassumption | apply reds_lapp2; eassumption].
  apply (R_red2 _ _ (kapp false B v w) _ (kapp false B v w)); [constructor; assumption .. |].
  apply R_later_val.
  { destruct v, w; try contradiction; exact I. }
  assert (Hfix : forall A' v, typed LR [] v (tLater A') -> runnable v ->
            typed LR (tLater B :: ctxL C []) (ren S (contents v)) A')
    by (intros A' v' Hv' Hr; apply (typed_ren _ _ []); [apply typed_contents; assumption |
                                                       intros [] ?; discriminate]).
  destruct v, w; try contradiction; cbn [kapp];
    repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; auto;
    try (apply ty_lfix, (ty_app _ _ _ A); apply Hfix; first [assumption | exact I]).
  destruct (typed_lbox_inv _ _ _ _ _ H) as (A1 & [= <-] & Hs1).
  destruct (typed_lbox_inv _ _ _ _ _ H3) as (A2 & [= <-] & Hs2).
  split; [apply ty_lbox, (ty_app _ _ _ A); assumption |].
  match goal with Hf : R (tArr A B) _ _, Ha : R A _ _ |- _ => exact (Hf _ _ Ha) end.
Qed.

Lemma R_llob A t t' :
  R (tLater (tArr (tLater A) A)) t t' -> R (tLater A) (llob A t) (llob A t').
Proof.
  intros Ht; destruct (R_later_inv _ _ _ Ht) as (v & H1 & H1' & Hv & Hvok).
  assert (Hr : forall t0 t1, reds t0 t1 -> reds (llob A t0) (llob A t1))
    by (apply reds_cong; constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hr _ _ H1) (Hr _ _ H1')).
  apply (R_red2 _ _ (lob A v) _ (lob A v)); [constructor; assumption .. |].
  destruct v; try contradiction; cbn [lob].
  1, 2: apply R_later_val; [exact I |];
    apply ty_lfix, (ty_app _ _ _ (tLater A)); [| apply ty_var; reflexivity];
    apply (typed_ren _ _ []); [apply typed_contents; [apply Hvok | exact I] | intros [] ?; discriminate].
  apply R_later_val; [exact I | split; [apply Hvok | reflexivity]].
Qed.

Lemma R_evalg A t t' d d' : R (tLater A) t t' -> R A d d' -> R A (evalg t d) (evalg t' d').
Proof.
  intros Ht Hd; destruct (R_later_inv _ _ _ Ht) as (v & H1 & H1' & Hv & Hvok).
  assert (Hr : forall d0 t0 t1, reds t0 t1 -> reds (evalg t0 d0) (evalg t1 d0))
    by (intros d0; apply (reds_cong _ (fun t => evalg t d0)); constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hr _ _ _ H1) (Hr _ _ _ H1')).
  destruct v; try contradiction.
  - apply (R_red2 _ _ v _ v); [constructor .. | apply Hvok].
  - apply (R_red2 _ _ d _ d'); [constructor; [exact I | intros []] .. | exact Hd].
  - apply (R_red2 _ _ d _ d'); [constructor; [exact I | intros []] .. | exact Hd].
Qed.

Lemma R_runk m A t t' d d' :
  (forall m', m = S m' -> forall s, typed LR [] s A -> R A (capk m' s) (capk m' s)) ->
  R (tLater A) t t' -> R A d d' -> R A (runk m t d) (runk m t' d').
Proof.
  intros HB Ht Hd; destruct m as [|m'].
  { apply (R_red2 _ _ d _ d'); [constructor .. | exact Hd]. }
  destruct (R_later_inv _ _ _ Ht) as (v & H1 & H1' & Hv & Hvok).
  assert (Hr : forall d0 t0 t1, reds t0 t1 -> reds (runk (S m') t0 d0) (runk (S m') t1 d0))
    by (intros d0; apply (reds_cong _ (fun t => runk (S m') t d0)); constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hr _ _ _ H1) (Hr _ _ _ H1')).
  destruct v; try contradiction.
  1, 2: match goal with |- R _ (runk _ ?w _) _ =>
          apply (R_red2 _ _ (capk m' (contents w)) _ (capk m' (contents w))) end;
    [constructor; exact I .. | apply (HB m' eq_refl), typed_contents; [apply Hvok | exact I]].
  apply (R_red2 _ _ d _ d'); [constructor .. | exact Hd].
Qed.

Lemma R_run A t t' : h = false ->
  (forall s, typed LR [] s A -> R A s s) ->
  R (tLater A) t t' -> R A (run t) (run t').
Proof.
  intros Hh HB Ht; destruct (R_later_inv _ _ _ Ht) as (v & H1 & H1' & Hv & Hvok).
  assert (Hr : forall t0 t1, reds t0 t1 -> reds (run t0) (run t1))
    by (apply reds_cong; constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hr _ _ H1) (Hr _ _ H1')).
  destruct v; try contradiction.
  1, 2: match goal with |- R _ (run ?w) _ => apply (R_red2 _ _ (contents w) _ (contents w)) end;
    [constructor; exact I .. | apply HB, typed_contents; [apply Hvok | exact I]].
  destruct Hvok as [E _]; congruence.
Qed.

(** *** The fundamental theorem, by recursion on depth, then fuel *)

(** [run] at U uses the theorem at R's depth for the code's contents;
    [runk] at its own depth uses it at lower fuel; [evalg] uses grounded
    code's related contents, which the relation carries.  An [lfix] is
    related by its typing alone. *)
Lemma FT_depth n : forall N j Γ t A, typed j Γ t A -> fuel_lt N t ->
  dep j < n -> (h = true -> j = LR) ->
  forall σ σ', Rsub Γ σ σ' -> R A (subst σ t) (subst σ' t).
Proof.
  induction n as [|n IHn]; [intros; lia |].
  intros N; induction N as [N IHN] using lt_wf_ind; intros j Γ t A Hty.
  induction Hty as [j Γ x A Hx | j Γ A B t Ht IHt | j Γ A B t u Ht IHt Hu IHu
    | j Γ k | j Γ t Ht IHt | j Γ A s Hs IHs | j Γ A M HM _ | j Γ A t Ht IHt
    | j Γ A B t u Ht IHt Hu IHu | j Γ A t Ht IHt | j Γ A t d Ht IHt Hd IHd
    | m j Γ A t d Ht IHt Hd IHd | j Γ A t He Ht IHt | i j Γ t A Hij Ht IHt];
    intros Hf Hn Hh σ σ' Hσ; cbn in Hf; cbn [subst].
  - apply Hσ, Hx.
  - apply R_lam; intros u u' Hu; apply IHt; auto using Rsub_cons.
  - destruct Hf as [Hf1 Hf2]; apply (IHt Hf1 Hn Hh _ _ Hσ), IHu; assumption.
  - apply R_lit.
  - apply R_succ, IHt; assumption.
  - apply R_later_val; [exact I | split; [apply ty_lbox, Hs |]].
    rewrite <- (subst_var s).
    apply IHs; [exact Hf | cbn; lia | reflexivity | exact Rsub_var_nil].
  - (* Löb: the body is closed but for the code itself *)
    assert (HM' : typed LR [tLater A] M A) by (unfold ctxL in HM; rewrite Hopen in HM; exact HM).
    assert (Hc : forall τ, subst (up τ) M = M)
      by (intros τ; apply (typed_subst_closed _ _ _ _ _ HM'); intros [|x] Hx; cbn in *; [reflexivity | lia]).
    rewrite !Hc; apply R_later_val; [exact I |].
    apply ty_lfix; unfold ctxL; rewrite Hopen; exact HM'.
  - apply (R_csize A), IHt; assumption.
  - destruct Hf as [Hf1 Hf2]; apply (R_lapp A); [apply IHt | apply IHu]; assumption.
  - apply R_llob, IHt; assumption.
  - destruct Hf as [Hf1 Hf2]; apply R_evalg; [apply IHt | apply IHd]; assumption.
  - destruct Hf as (Hm & Hf1 & Hf2).
    apply R_runk; [| apply IHt | apply IHd]; try assumption.
    intros m' -> s Hs; rewrite <- (subst_var (capk m' s)).
    apply (IHN (S m') Hm LR []); [apply typed_capk, Hs | apply fuel_lt_capk | cbn; lia
      | reflexivity | exact Rsub_var_nil].
  - (* T at U: the contents are R-terms, one depth down *)
    assert (Ej : j = LU) by (destruct j; [cbn in He; congruence | reflexivity]); subst j.
    assert (Hh' : h = false) by (destruct h; [discriminate (Hh eq_refl) | reflexivity]).
    apply R_run; [exact Hh' | | apply IHt; assumption].
    intros s Hs; rewrite <- (subst_var s); destruct (fuel_bound s) as [Ns HNs].
    apply (IHn Ns LR []); [exact Hs | exact HNs | cbn in *; lia | reflexivity | exact Rsub_var_nil].
  - apply IHt; [exact Hf | | | exact Hσ].
    + destruct i, j; cbn in Hij, Hn |- *; try contradiction; lia.
    + intros E; specialize (Hh E); subst j; destruct i; [reflexivity | contradiction].
Qed.

Theorem FT_typed j Γ t A : typed j Γ t A -> (h = true -> j = LR) ->
  forall σ σ', Rsub Γ σ σ' -> R A (subst σ t) (subst σ' t).
Proof.
  intros H Hh; destruct (fuel_bound t) as [N HN].
  apply (FT_depth (S (dep j)) N _ _ _ _ H HN); [lia | exact Hh].
Qed.

Lemma FT_closed j t A : typed j [] t A -> (h = true -> j = LR) -> R A t t.
Proof.
  intros H Hh; rewrite <- (subst_var t); exact (FT_typed _ _ _ _ H Hh _ _ Rsub_var_nil).
Qed.

End Metatheory.

(** ** In the sound configuration *)

Lemma FT_good h j t A : typed good j [] t A -> (h = true -> j = LR) -> R good h A t t.
Proof. exact (FT_closed good eq_refl eq_refl h j t A). Qed.

Lemma no_hole : false = true -> forall j : lay, j = LR.
Proof. discriminate. Qed.

(** Normalization at both layers, U's [run] of code with [lfix] included. *)
Theorem normalization j t : typed good j [] t tNat -> exists k, evalto false t (lit k).
Proof. intros H; destruct (FT_good false j t tNat H (fun E => no_hole E j)) as (k & Hk & _); eauto. Qed.

Theorem Empty_empty j t : ~ typed good j [] t tEmpty.
Proof. intros H; exact (FT_good false j t tEmpty H (fun E => no_hole E j)). Qed.

(** [▷Empty] is empty too: an [lfix] of it would unfold to an R-term of
    [Empty]. *)
Theorem later_Empty_empty j t : ~ typed good j [] t (tLater tEmpty).
Proof.
  intros H; pose proof (FT_good false j t _ H (fun E => no_hole E j)) as Ht.
  destruct (R_later_inv good false _ _ _ Ht) as (w & _ & _ & _ & Hw).
  destruct w; try contradiction.
  - destruct Hw as [_ []].
  - apply (Empty_empty LR (contents (lfix A w))), typed_contents; [exact Hw | exact I].
  - destruct Hw as [[=] _].
Qed.

(** R cannot prove its own consistency, [▷Empty → Empty]: in the model with
    holes, such a function would take the hole, an unknown code it cannot
    run, to an element of [Empty].  U proves it, by running the code
    (Gödel's second incompleteness theorem as GL has it: [□⊥ → ⊥] is not
    a theorem, and holds one level up). *)
Theorem no_R_consistency f : ~ typed good LR [] f (tArr (tLater tEmpty) tEmpty).
Proof.
  intros H; pose proof (FT_good true LR f _ H (fun _ => eq_refl)) as Hf.
  apply (Hf (lhole tEmpty) (lhole tEmpty)).
  exact (R_later_val good true tEmpty (lhole tEmpty) I (conj eq_refl eq_refl)).
Qed.

Example U_consistency :
  typed good LU [] (lam (tLater tEmpty) (run (var 0))) (tArr (tLater tEmpty) tEmpty).
Proof. apply ty_lam, ty_run; [reflexivity | apply ty_var; reflexivity]. Qed.

(** *** Löb, K and the fixed-point equation *)

(** The rule: [z : ▷A ⊢_R M : A] gives [lfix A M : ▷A], at R or U. *)
Example lob_rule j A M : typed good LR [tLater A] M A -> typed good j [] (lfix A M) (tLater A).
Proof. intros H; apply ty_lfix, H. Qed.

(** The GL axiom [▷(▷A → A) → ▷A], and K, at R. *)
Example lob_axiom A :
  typed good LR [] (lam (tLater (tArr (tLater A) A)) (llob A (var 0)))
    (tArr (tLater (tArr (tLater A) A)) (tLater A)).
Proof. apply ty_lam, ty_llob, ty_var; reflexivity. Qed.

Example k_axiom A B :
  typed good LR [] (lam (tLater (tArr A B)) (lam (tLater A) (lapp B (var 1) (var 0))))
    (tArr (tLater (tArr A B)) (tArr (tLater A) (tLater B))).
Proof. apply ty_lam, ty_lam, (ty_lapp _ _ _ A); apply ty_var; reflexivity. Qed.

(** Kleene's second recursion theorem: [llob ⌜f⌝] is a code [L] with
    [run L ⇝ f L], one unfolding per run. *)
Lemma lob_unfold A f :
  red false (llob A (lbox f)) (lfix A (app (ren S f) (var 0))) /\
  red false (run (lfix A (app (ren S f) (var 0)))) (app f (lfix A (app (ren S f) (var 0)))).
Proof.
  split; [apply (r_llob_v false A (lbox f)); exact I |].
  match goal with |- red _ (run ?L) _ =>
    replace (app f L) with (contents L) by (cbn; rewrite subst_ren_S; reflexivity) end.
  apply r_run; exact I.
Qed.

(** Guarded recursion at U, [fix : (▷A → A) → A] for a closed R-function:
    [gfix f ⇝* f L] where [run L ⇝ f L], so [L] is [next (gfix f)]. *)
Definition gfix (A : ty) (f : tm) : tm := run (llob A (lbox f)).

Example gfix_typed A f : typed good LR [] f (tArr (tLater A) A) -> typed good LU [] (gfix A f) A.
Proof. intros H; apply ty_run; [reflexivity | apply ty_llob, ty_lbox, H]. Qed.

Lemma gfix_unfold A f : exists L,
  reds false (gfix A f) (app f L) /\ red false (run L) (app f L).
Proof.
  destruct (lob_unfold A f) as [H1 H2]; eexists; split; [| exact H2].
  eapply reds_step; [apply r_run_c, H1 | apply red1, H2].
Qed.

(** *** Grounded release at R *)

(** [evalg] runs grounded code and refuses an [lfix]: the liar with
    grounded release, [lfix z. succ (evalg z 0)], is refused at R and
    answers [1] when U runs it (one unfolding, then the refusal). *)
Definition gliar : tm := lfix tNat (succ (evalg (var 0) (lit 0))).

Example gliar_typed : typed good LR [] gliar (tLater tNat).
Proof.
  apply ty_lfix, ty_succ, ty_evalg; [apply ty_var; reflexivity | apply ty_lit].
Qed.

Example gliar_refused : evalto false (evalg gliar (lit 7)) (lit 7).
Proof.
  split; [| exact I]; apply red1, r_evalg_nobox; [exact I | intros []].
Qed.

Example gliar_run : evalto false (run gliar) (lit 1).
Proof.
  split; [| exact I].
  eapply reds_step; [apply r_run; exact I |]; cbn.
  eapply reds_step; [apply r_succ, r_evalg_nobox; [exact I | intros []] |].
  apply red1, r_succ_lit.
Qed.

Example grounded_runs : evalto false (evalg (lbox (lit 3)) (lit 7)) (lit 3).
Proof. split; [apply red1, r_evalg_box | exact I]. Qed.

(** *** The fuelled liar: the delay observed for [n] steps *)

(** [dk n := lfix z. succ (runk n z 0)], run at R with fuel [n].  Each unit
    of fuel is one unfolding: the trace is [succ (succ (… 0))] with [n]
    [succ]s, the never-ending trace of [liar_nat] below cut after [n]
    unfoldings, with the default in the hole. *)
Definition dk (n : nat) : tm := lfix tNat (succ (runk n (var 0) (lit 0))).
Definition fliar (n : nat) : tm := runk n (dk n) (lit 0).

Example fliar_typed n : typed good LR [] (fliar n) tNat.
Proof.
  apply ty_runk; [| apply ty_lit].
  apply ty_lfix, ty_succ, ty_runk; [apply ty_var; reflexivity | apply ty_lit].
Qed.

Lemma red_iter_succ leak k t t' : red leak t t' ->
  red leak (Nat.iter k succ t) (Nat.iter k succ t').
Proof. intros H; induction k; cbn; [exact H | apply r_succ, IHk]. Qed.

Lemma reds_iter_succ leak k t t' : reds leak t t' ->
  reds leak (Nat.iter k succ t) (Nat.iter k succ t').
Proof. apply reds_cong, red_iter_succ. Qed.

Lemma dk_trace n m : m <= n -> reds false (runk m (dk n) (lit 0)) (Nat.iter m succ (lit 0)).
Proof.
  induction m as [|m IH]; intros Hm; [apply red1, r_runk_zero |].
  eapply reds_step; [apply r_runk_hit; exact I |]; cbn.
  replace (Nat.min n m) with m by lia.
  apply (reds_iter_succ false 1), IH; lia.
Qed.

Lemma iter_succ_lit leak k : reds leak (Nat.iter k succ (lit 0)) (lit k).
Proof.
  induction k as [|k IH]; [constructor |]; cbn.
  apply (reds_trans _ _ (succ (lit k))); [apply (reds_iter_succ leak 1), IH | apply red1, r_succ_lit].
Qed.

Theorem fuel_liar n : reds false (fliar n) (Nat.iter n succ (lit 0)) /\ evalto false (fliar n) (lit n).
Proof.
  pose proof (dk_trace n n (le_n n)) as H; split; [exact H |].
  split; [eapply reds_trans; [exact H | apply iter_succ_lit] | exact I].
Qed.

(** ** Counterexamples: each side condition is needed *)

(** *** No T at R: with [run] at R, the liar *)

Definition cfg_tR : cfg := {| c_tR := true; c_open := false |}.

(** [lfix z. run z], run: [Empty] is inhabited at R, by a term that
    reduces to itself. *)
Definition liar (A : ty) : tm := run (lfix A (run (var 0))).

Theorem liar_typed A : typed cfg_tR LR [] (liar A) A.
Proof. apply ty_run; [reflexivity |]; apply ty_lfix, ty_run; [reflexivity | apply ty_var; reflexivity]. Qed.

Theorem liar_diverges A : diverges false (liar A).
Proof. apply (cycle_diverges _ _ (liar A)); [apply r_run; exact I | constructor]. Qed.

(** Its numeral form, [lfix z. succ (run z)]: the trace passes through
    [succ (succ (… liar_nat))] for every count of unfoldings and never
    ends.  [fuel_liar] is it cut at [n]. *)
Definition liar_nat : tm := run (lfix tNat (succ (run (var 0)))).

Theorem liar_nat_typed : typed cfg_tR LR [] liar_nat tNat.
Proof. apply ty_run; [reflexivity |]; apply ty_lfix, ty_succ, ty_run; [reflexivity | apply ty_var; reflexivity]. Qed.

Lemma liar_nat_step : red false liar_nat (succ liar_nat).
Proof. apply r_run; exact I. Qed.

Theorem liar_nat_trace k : reds false liar_nat (Nat.iter k succ liar_nat).
Proof.
  induction k as [|k IH]; [constructor |].
  eapply reds_trans; [exact IH |].
  rewrite Nat.iter_succ_r; apply red1, red_iter_succ, liar_nat_step.
Qed.

Theorem liar_nat_diverges : diverges false liar_nat.
Proof.
  enough (H : forall k, diverges false (Nat.iter k succ liar_nat)) by exact (H 0).
  cofix CIH; intros k.
  apply (dv _ _ (Nat.iter (S k) succ liar_nat) (Nat.iter (S k) succ liar_nat)); [| constructor | apply CIH].
  rewrite Nat.iter_succ_r; apply red_iter_succ, liar_nat_step.
Qed.

(** *** Löb's body closed: an open body takes in U's release *)

Definition cfg_open : cfg := {| c_tR := false; c_open := true |}.

(** With the context visible in Löb's body, the R-term
    [λe. lfix z. e z : (▷A → A) → ▷A] is the internal Löb rule for any
    function, and U applies it to its own release [λx. run x]. *)
Definition urun (A : ty) : tm := lam (tLater A) (run (var 0)).
Definition oliar_body (A : ty) : tm := run (lfix A (app (var 1) (var 0))).
Definition oliar (A : ty) : tm := app (lam (tArr (tLater A) A) (oliar_body A)) (urun A).

Theorem oliar_typed A : typed cfg_open LU [] (oliar A) A.
Proof.
  apply (ty_app _ _ _ (tArr (tLater A) A)).
  - apply ty_lam, ty_run; [reflexivity |].
    apply ty_lfix; cbn; apply (ty_app _ _ _ (tLater A)); apply ty_var; reflexivity.
  - apply ty_lam, ty_run; [reflexivity | apply ty_var; reflexivity].
Qed.

Theorem oliar_diverges A : diverges false (oliar A).
Proof.
  set (L := lfix A (app (urun A) (var 0))).
  apply (diverges_back _ _ (run L)); [apply red1, r_beta |].
  apply (cycle_diverges _ _ (app (urun A) L)); [apply r_run; exact I |].
  apply red1, r_beta.
Qed.

(** *** [lfix] opaque: unfolding it identifies codes that R tells apart *)

(** [lfix A M] and its unfolding, as grounded code, differ in size and in
    groundedness, so no conversion sound for numerals and a congruence for
    [csize] identifies them. *)
Example unfold_csize :
  evalto false (csize (lfix tNat (lit 0))) (lit 2) /\
  evalto false (csize (lbox (contents (lfix tNat (lit 0))))) (lit 1).
Proof. split; (split; [apply red1, r_csize_v; exact I | exact I]). Qed.

Example unfold_evalg :
  evalto false (evalg (lfix tNat (lit 0)) (lit 5)) (lit 5) /\
  evalto false (evalg (lbox (contents (lfix tNat (lit 0)))) (lit 5)) (lit 0).
Proof.
  split; (split; [| exact I]); apply red1; [apply r_evalg_nobox; [exact I | intros []] | apply r_evalg_box].
Qed.

Theorem no_unfolding_conversion (conv : tm -> tm -> Prop) :
  (forall A M, conv (lfix A M) (lbox (contents (lfix A M)))) ->
  (forall t t', conv t t' -> conv (csize t) (csize t')) ->
  ~ (forall t t' k k', conv t t' -> evalto false t (lit k) -> evalto false t' (lit k') -> k = k').
Proof.
  intros Hunf Hcs Hsound.
  destruct unfold_csize as [H2 H1].
  discriminate (Hsound _ _ _ _ (Hcs _ _ (Hunf tNat (lit 0))) H2 H1).
Qed.

(** *** Code formers keep [lfix]-headed code ungrounded *)

(** With [leak], K applied to an [lfix] gives grounded code, and grounded
    release runs the unfolding: a liar through K.  [F := lfix z. λx. succ
    (evalg (z ⊛ ⌜0⌝) 0)], [X := evalg (F ⊛ ⌜0⌝) 0], and [X ⇝* succ X]. *)
Definition kF : tm :=
  lfix (tArr tNat tNat) (lam tNat (succ (evalg (lapp tNat (var 1) (lbox (lit 0))) (lit 0)))).
Definition kX : tm := evalg (lapp tNat kF (lbox (lit 0))) (lit 0).

Theorem kX_typed : typed good LR [] kX tNat.
Proof.
  apply ty_evalg; [| apply ty_lit].
  apply (ty_lapp _ _ _ tNat); [| apply ty_lbox, ty_lit].
  apply ty_lfix, ty_lam, ty_succ, ty_evalg; [| apply ty_lit].
  apply (ty_lapp _ _ _ tNat); [apply ty_var; reflexivity | apply ty_lbox, ty_lit].
Qed.

(** In the sound reduction, [F ⊛ ⌜0⌝] is headed by [lfix], so [evalg]
    refuses it. *)
Example kX_sound : evalto false kX (lit 0).
Proof.
  split; [| exact I].
  eapply reds_step; [apply r_evalg, r_lapp_v; exact I |]; cbn [kapp].
  apply red1, r_evalg_nobox; [exact I | intros []].
Qed.

Lemma kX_leak_step : exists t1, red true kX t1 /\ reds true t1 (succ kX).
Proof.
  eexists; split; [apply r_evalg, r_lapp_v; exact I |]; cbn [kapp].
  eapply reds_step; [apply r_evalg_box |]; cbn.
  apply red1, r_beta.
Qed.

Theorem kX_leak_diverges : diverges true kX.
Proof.
  enough (H : forall k, diverges true (Nat.iter k succ kX)) by exact (H 0).
  cofix CIH; intros k.
  destruct kX_leak_step as (t1 & H1 & H2).
  apply (dv _ _ (Nat.iter k succ t1) (Nat.iter (S k) succ kX)); [apply red_iter_succ, H1 | | apply CIH].
  rewrite Nat.iter_succ_r; apply reds_iter_succ, H2.
Qed.

Print Assumptions normalization.
Print Assumptions no_R_consistency.
Print Assumptions later_Empty_empty.
Print Assumptions fuel_liar.
Print Assumptions liar_nat_diverges.
Print Assumptions oliar_diverges.
Print Assumptions kX_leak_diverges.
Print Assumptions no_unfolding_conversion.
