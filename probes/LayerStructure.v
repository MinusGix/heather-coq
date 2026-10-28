(** * Layer structures: their side conditions, found by counterexample

    Heather-coq issue #48 (`docs/design/LAYER_STRUCTURE.md` has the
    findings).  A toy calculus, STLC with [Nat] and code, is parameterized
    by a layer structure: a type of layers with a few capabilities each.
    Under six side conditions it normalizes at every total layer and its
    conversion is sound for numerals (section [Metatheory]).  Each
    condition is necessary: for each, a structure that meets the other
    five has a well-typed closed numeral without a normal form, or a
    conversion between two distinct numerals (section [Counterexamples]).
    The {code, program} × meta-depth grid meets all six, at every depth
    and with a partial top level; DeLaM is its depth-1 slice (section
    [Grid]).

    The toy's code is closed and untyped: [Code c] holds a closed
    layer-[c] term [s] of any type [A], as [box A s], tagged with its type
    (DeLaM's code of types, read as Σ A. □A).  On code there is
    - an analysis [csize] (a fold with a fixed motive, standing in for the
      recursors): the size of the syntax tree;
    - an evaluation [run c B t d] (T, with a type conditional): [s] if [t]
      is [box B s], [d] if its tag is not [B];
    - [quote c t] (axiom 4): [box A s] boxed again, as code one level up.
    General recursion [fix] is typable only at partial layers.

    Standalone, no axioms: [coqc probes/LayerStructure.v]. *)
From Coq Require Import List Arith Lia.
Import ListNotations.

(** ** Layer structures *)

(** A layer is a tuple of capabilities (issue #48):
    - [ls_computes]: β is part of its conversion (else equality is static);
    - [ls_typeof]: the layer its judgments' types live at (a code layer's
      types are its program layer's, as [typeof C = D]);
    - [ls_hosts k c]: [Code c] is a type at type layer [k], with [box] and
      the analysis [csize];
    - [ls_evals j c]: layer [j] may [run] layer-[c] code;
    - [ls_total]: [fix] is not typable;
    - [ls_depth]: the meta depth, read at a type layer.
    [ls_le] says what lifts into what. *)
Record LS := {
  ls_L : Type;
  ls_dec : forall x y : ls_L, {x = y} + {x <> y};
  ls_le : ls_L -> ls_L -> Prop;
  ls_typeof : ls_L -> ls_L;
  ls_computes : ls_L -> bool;
  ls_hosts : ls_L -> ls_L -> Prop;
  ls_evals : ls_L -> ls_L -> Prop;
  ls_total : ls_L -> bool;
  ls_depth : ls_L -> nat;
}.

(** ** Syntax *)

Section Syntax.
Context {L : Type}.

Inductive ty : Type :=
| tNat
| tArr (A B : ty)
| tCode (c : L).

Inductive tm : Type :=
| var (x : nat)
| lam (A : ty) (t : tm)
| app (t u : tm)
| lit (k : nat)
| succ (t : tm)
| box (A : ty) (s : tm)
| csize (t : tm)
| run (c : L) (B : ty) (t d : tm)
| quote (c : L) (t : tm)
| fix_ (A : ty) (t : tm).

Definition upren (ξ : nat -> nat) (x : nat) : nat :=
  match x with 0 => 0 | S x => S (ξ x) end.

(** A [box]'s contents are closed (its typing rule checks them in the empty
    context), so renaming and substitution stop at [box]. *)
Fixpoint ren (ξ : nat -> nat) (t : tm) : tm :=
  match t with
  | var x => var (ξ x)
  | lam A t => lam A (ren (upren ξ) t)
  | app t u => app (ren ξ t) (ren ξ u)
  | lit k => lit k
  | succ t => succ (ren ξ t)
  | box A s => box A s
  | csize t => csize (ren ξ t)
  | run c B t d => run c B (ren ξ t) (ren ξ d)
  | quote c t => quote c (ren ξ t)
  | fix_ A t => fix_ A (ren (upren ξ) t)
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
  | box A s => box A s
  | csize t => csize (subst σ t)
  | run c B t d => run c B (subst σ t) (subst σ d)
  | quote c t => quote c (subst σ t)
  | fix_ A t => fix_ A (subst (up σ) t)
  end.

Definition scons (u : tm) (σ : nat -> tm) (x : nat) : tm :=
  match x with 0 => u | S x => σ x end.

Fixpoint size (t : tm) : nat :=
  match t with
  | var _ | lit _ => 1
  | lam _ t | succ t | box _ t | csize t | quote _ t | fix_ _ t => S (size t)
  | app t u | run _ _ t u => S (size t + size u)
  end.

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

(** The substitution of β under a substitution. *)
Lemma subst_beta σ u t :
  subst (scons u var) (subst (up σ) t) = subst (scons u σ) t.
Proof.
  rewrite subst_subst; apply subst_ext; intros [|x]; cbn; [reflexivity |].
  rewrite ren_subst; apply subst_var.
Qed.

Lemma subst_single_comp σ u t :
  subst σ (subst (scons u var) t) = subst (scons (subst σ u) σ) t.
Proof. rewrite subst_subst; apply subst_ext; intros []; reflexivity. Qed.

(** *** Reduction: weak head, call by name, untyped *)

Inductive red : tm -> tm -> Prop :=
| r_beta A t u : red (app (lam A t) u) (subst (scons u var) t)
| r_app t t' u : red t t' -> red (app t u) (app t' u)
| r_succ_lit k : red (succ (lit k)) (lit (S k))
| r_succ t t' : red t t' -> red (succ t) (succ t')
| r_csize_box A s : red (csize (box A s)) (lit (size s))
| r_csize t t' : red t t' -> red (csize t) (csize t')
| r_run_hit c B s d : red (run c B (box B s) d) s
| r_run_miss c A B s d : A <> B -> red (run c B (box A s) d) d
| r_run c B t t' d : red t t' -> red (run c B t d) (run c B t' d)
| r_quote_box c A s : red (quote c (box A s)) (box (tCode c) (box A s))
| r_quote c t t' : red t t' -> red (quote c t) (quote c t')
| r_fix A t : red (fix_ A t) (subst (scons (fix_ A t) var) t).

Inductive reds : tm -> tm -> Prop :=
| reds_refl t : reds t t
| reds_step t t' t'' : red t t' -> reds t' t'' -> reds t t''.

Definition value (t : tm) : Prop :=
  match t with lam _ _ | lit _ | box _ _ => True | _ => False end.

(** [t ⇓ v]. *)
Definition evalto (t v : tm) : Prop := reds t v /\ value v.

Lemma value_nored t t' : value t -> ~ red t t'.
Proof. destruct t; cbn; intros Hv Hr; try contradiction; inversion Hr. Qed.

Lemma red_det t u u' : red t u -> red t u' -> u = u'.
Proof.
  intros H; revert u'; induction H; intros u'' H'; inversion H'; subst;
    try reflexivity; try congruence;
    repeat match goal with
           | H : red (lam _ _) _ |- _ => inversion H
           | H : red (lit _) _ |- _ => inversion H
           | H : red (box _ _) _ |- _ => inversion H
           end;
    f_equal; auto.
Qed.

Lemma reds_trans t t' t'' : reds t t' -> reds t' t'' -> reds t t''.
Proof. induction 1; eauto using reds. Qed.

Lemma reds_cong (f : tm -> tm) :
  (forall t t', red t t' -> red (f t) (f t')) ->
  forall t t', reds t t' -> reds (f t) (f t').
Proof. intros Hf; induction 1; eauto using reds. Qed.

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

End Syntax.

Arguments ty : clear implicits.
Arguments tm : clear implicits.

(** ** Typing and conversion, over a layer structure *)

Section Rules.
Variable Λ : LS.

Local Notation L := (ls_L Λ).
Local Notation lle := (ls_le Λ).
Local Notation typeof := (ls_typeof Λ).
Local Notation computes := (ls_computes Λ).
Local Notation hosts := (ls_hosts Λ).
Local Notation evals := (ls_evals Λ).
Local Notation total := (ls_total Λ).
Local Notation depth := (ls_depth Λ).
Local Notation ty := (ty L).
Local Notation tm := (tm L).
Implicit Types (t u v s d : tm) (A B : ty) (Γ : list ty) (σ : nat -> tm).

(** Types formable at type layer [k]: [Code c] where [k] hosts [c]. *)
Fixpoint wf_ty (k : L) (A : ty) : Prop :=
  match A with
  | tNat => True
  | tArr A B => wf_ty k A /\ wf_ty k B
  | tCode c => hosts k c
  end.

(** [Γ ⊢ⱼ t : A].  Types are checked where they are introduced. *)
Inductive typed : L -> list ty -> tm -> ty -> Prop :=
| ty_var j Γ x A : nth_error Γ x = Some A -> typed j Γ (var x) A
| ty_lam j Γ A B t :
    wf_ty (typeof j) A -> typed j (A :: Γ) t B -> typed j Γ (lam A t) (tArr A B)
| ty_app j Γ A B t u :
    typed j Γ t (tArr A B) -> typed j Γ u A -> typed j Γ (app t u) B
| ty_lit j Γ k : typed j Γ (lit k) tNat
| ty_succ j Γ t : typed j Γ t tNat -> typed j Γ (succ t) tNat
| ty_box j Γ c A s :
    hosts (typeof j) c -> wf_ty (typeof c) A -> typed c [] s A ->
    typed j Γ (box A s) (tCode c)
| ty_csize j Γ c t : typed j Γ t (tCode c) -> typed j Γ (csize t) tNat
| ty_run j Γ c B t d :
    evals j c -> hosts (typeof j) c -> wf_ty (typeof c) B ->
    typed j Γ t (tCode c) -> typed j Γ d B -> typed j Γ (run c B t d) B
| ty_quote j Γ c c' t :
    hosts (typeof c') c -> hosts (typeof j) c' ->
    typed j Γ t (tCode c) -> typed j Γ (quote c t) (tCode c')
| ty_fix j Γ A t :
    total j = false -> wf_ty (typeof j) A -> typed j (A :: Γ) t A ->
    typed j Γ (fix_ A t) A
| ty_lift i j Γ t A : lle i j -> typed i Γ t A -> typed j Γ t A.

(** [Γ ⊢ⱼ t ≡ t' : A]: congruences everywhere, computation only at
    computing layers.  [box]'s congruence compares its contents by the
    code layer's own conversion. *)
Inductive conv : L -> list ty -> tm -> tm -> ty -> Prop :=
| cv_refl j Γ t A : typed j Γ t A -> conv j Γ t t A
| cv_sym j Γ t t' A : conv j Γ t t' A -> conv j Γ t' t A
| cv_trans j Γ t t' t'' A : conv j Γ t t' A -> conv j Γ t' t'' A -> conv j Γ t t'' A
| cv_lift i j Γ t t' A : lle i j -> conv i Γ t t' A -> conv j Γ t t' A
| cv_lam j Γ A B t t' :
    wf_ty (typeof j) A -> conv j (A :: Γ) t t' B ->
    conv j Γ (lam A t) (lam A t') (tArr A B)
| cv_app j Γ A B t t' u u' :
    conv j Γ t t' (tArr A B) -> conv j Γ u u' A -> conv j Γ (app t u) (app t' u') B
| cv_succ j Γ t t' : conv j Γ t t' tNat -> conv j Γ (succ t) (succ t') tNat
| cv_box j Γ c A s s' :
    hosts (typeof j) c -> wf_ty (typeof c) A -> conv c [] s s' A ->
    conv j Γ (box A s) (box A s') (tCode c)
| cv_csize j Γ c t t' : conv j Γ t t' (tCode c) -> conv j Γ (csize t) (csize t') tNat
| cv_run j Γ c B t t' d d' :
    evals j c -> hosts (typeof j) c -> wf_ty (typeof c) B ->
    conv j Γ t t' (tCode c) -> conv j Γ d d' B ->
    conv j Γ (run c B t d) (run c B t' d') B
| cv_quote j Γ c c' t t' :
    hosts (typeof c') c -> hosts (typeof j) c' -> conv j Γ t t' (tCode c) ->
    conv j Γ (quote c t) (quote c t') (tCode c')
| cv_fix j Γ A t t' :
    total j = false -> wf_ty (typeof j) A -> conv j (A :: Γ) t t' A ->
    conv j Γ (fix_ A t) (fix_ A t') A
| cv_beta j Γ A B t u :
    computes j = true -> wf_ty (typeof j) A -> typed j (A :: Γ) t B -> typed j Γ u A ->
    conv j Γ (app (lam A t) u) (subst (scons u var) t) B
| cv_succ_lit j Γ k : computes j = true -> conv j Γ (succ (lit k)) (lit (S k)) tNat
| cv_csize_box j Γ c A s :
    computes j = true -> typed j Γ (box A s) (tCode c) ->
    conv j Γ (csize (box A s)) (lit (size s)) tNat
| cv_run_hit j Γ c B s d :
    computes j = true -> evals j c -> hosts (typeof j) c -> wf_ty (typeof c) B ->
    typed c [] s B -> typed j Γ d B -> conv j Γ (run c B (box B s) d) s B
| cv_run_miss j Γ c A B s d :
    computes j = true -> A <> B -> evals j c -> hosts (typeof j) c -> wf_ty (typeof c) B ->
    typed j Γ (box A s) (tCode c) -> typed j Γ d B -> conv j Γ (run c B (box A s) d) d B
| cv_quote_box j Γ c c' A s :
    computes j = true -> hosts (typeof c') c -> hosts (typeof j) c' ->
    typed j Γ (box A s) (tCode c) ->
    conv j Γ (quote c (box A s)) (box (tCode c) (box A s)) (tCode c').

(** *** The side conditions *)

(** (S1) Hosted, hence analysed, code is static. *)
Definition static_code := forall k c, hosts k c -> computes c = false.
(** (W1) Nothing that computes lifts into a static layer. *)
Definition static_down := forall i j, lle i j -> computes j = false -> computes i = false.
(** (S2) Evaluation is strictly upward in meta depth. *)
Definition eval_up := forall j c, evals j c -> hosts (typeof j) c ->
  depth (typeof c) < depth (typeof j).
(** (W2) Lifting never lowers the meta depth. *)
Definition depth_mono := forall i j, lle i j -> depth (typeof i) <= depth (typeof j).
(** (W3) Nothing partial lifts into a total layer. *)
Definition total_down := forall i j, lle i j -> total j = true -> total i = true.
(** (W4) A layer evaluates only code that lifts into it. *)
Definition eval_lift := forall j c, evals j c -> lle c j.

(** ** Metatheory *)

(** The relation does not depend on layers: it is about untyped
    evaluation.  Code is related when both sides evaluate to one and the
    same well-typed [box]: syntactic equality, since [csize] observes
    syntax. *)
Fixpoint R (A : ty) : tm -> tm -> Prop :=
  match A with
  | tNat => fun t t' => exists k, evalto t (lit k) /\ evalto t' (lit k)
  | tArr A B => fun t t' => forall u u', R A u u' -> R B (app t u) (app t' u')
  | tCode c => fun t t' => exists A s,
      evalto t (box A s) /\ evalto t' (box A s) /\ wf_ty (typeof c) A /\ typed c [] s A
  end.

Lemma R_sym A t t' : R A t t' -> R A t' t.
Proof.
  revert t t'; induction A; cbn; intros t t' H.
  - destruct H as (k & H1 & H2); eauto.
  - intros u u' Hu; apply IHA2, H, IHA1, Hu.
  - destruct H as (A & s & H1 & H2 & H3); eauto 6.
Qed.

Lemma R_trans A t t' t'' : R A t t' -> R A t' t'' -> R A t t''.
Proof.
  revert t t' t''; induction A; cbn; intros t t' t'' H H'.
  - destruct H as (k & H1 & H2), H' as (k' & H1' & H2').
    pose proof (evalto_det _ _ _ H2 H1') as E; injection E as ->; eauto.
  - intros u u' Hu.
    apply (IHA2 _ (app t' u')); [apply H, Hu |].
    apply H', (IHA1 _ u); [apply R_sym, Hu | exact Hu].
  - destruct H as (A & s & H1 & H2 & H3 & H4), H' as (A' & s' & H1' & H2' & _).
    pose proof (evalto_det _ _ _ H2 H1') as E; injection E as -> ->; eauto 6.
Qed.

Lemma R_refl_l A t t' : R A t t' -> R A t t.
Proof. intros H; exact (R_trans _ _ _ _ H (R_sym _ _ _ H)). Qed.

Lemma evalto_expand t t1 v : reds t t1 -> evalto t1 v -> evalto t v.
Proof. intros H [H1 Hv]; split; [exact (reds_trans _ _ _ H H1) | exact Hv]. Qed.

(** Weak-head expansion. *)
Lemma R_expand A t t1 t' t1' : reds t t1 -> reds t' t1' -> R A t1 t1' -> R A t t'.
Proof.
  revert t t1 t' t1'; induction A; cbn; intros t t1 t' t1' H H' HR.
  - destruct HR as (k & H1 & H2); eauto using evalto_expand.
  - intros u u' Hu; apply (IHA2 _ (app t1 u) _ (app t1' u')); [| | apply HR, Hu].
    all: apply (reds_cong (fun t => app t _)); [intros; constructor; assumption | assumption].
  - destruct HR as (A & s & H1 & H2 & H3); eauto 7 using evalto_expand.
Qed.

Lemma R_red1 A t t1 t' : red t t1 -> R A t1 t' -> R A t t'.
Proof. intros H; apply R_expand; [econstructor; [exact H | constructor] | constructor]. Qed.

Definition Rsub (Γ : list ty) (σ σ' : nat -> tm) : Prop :=
  forall x A, nth_error Γ x = Some A -> R A (σ x) (σ' x).

Lemma Rsub_cons Γ A σ σ' u u' :
  Rsub Γ σ σ' -> R A u u' -> Rsub (A :: Γ) (scons u σ) (scons u' σ').
Proof. intros H Hu [|x] B; cbn; [intros [= <-]; exact Hu | apply H]. Qed.

Lemma Rsub_sym Γ σ σ' : Rsub Γ σ σ' -> Rsub Γ σ' σ.
Proof. intros H x A Hx; apply R_sym, H, Hx. Qed.

Lemma Rsub_refl_r Γ σ σ' : Rsub Γ σ σ' -> Rsub Γ σ' σ'.
Proof. intros H x A Hx; apply (R_refl_l _ _ (σ x)), R_sym, H, Hx. Qed.

(** Closed terms are fixed by substitution. *)
Lemma typed_subst_closed j Γ t A : typed j Γ t A ->
  forall σ, (forall x, x < length Γ -> σ x = var x) -> subst σ t = t.
Proof.
  induction 1; intros σ Hσ; cbn; f_equal; auto.
  - apply Hσ, nth_error_Some; congruence.
  - apply IHtyped; intros [|x] Hx; cbn; [reflexivity |].
    rewrite Hσ; [reflexivity | cbn in Hx; lia].
  - apply IHtyped; intros [|x] Hx; cbn; [reflexivity |].
    rewrite Hσ; [reflexivity | cbn in Hx; lia].
Qed.

Lemma closed_subst c s A σ : typed c [] s A -> subst σ s = s.
Proof. intros H; apply (typed_subst_closed _ _ _ _ H); cbn; lia. Qed.

Lemma Rsub_var_nil : Rsub [] var var.
Proof. intros [] ?; discriminate. Qed.

(** The congruence cases. *)
Lemma reds_app_l u t t' : reds t t' -> reds (app t u) (app t' u).
Proof. apply (reds_cong (fun t => app t u)); constructor; assumption. Qed.

Lemma R_lam A B t t' σ σ' :
  (forall u u', R A u u' -> R B (subst (scons u σ) t) (subst (scons u' σ') t')) ->
  R (tArr A B) (lam A (subst (up σ) t)) (lam A (subst (up σ') t')).
Proof.
  intros IH u u' Hu.
  apply (R_expand _ _ (subst (scons u var) (subst (up σ) t)) _
           (subst (scons u' var) (subst (up σ') t'))).
  1, 2: econstructor; [apply r_beta | constructor].
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
  apply (R_red1 _ _ (lit (S k))); [constructor |].
  apply R_sym, (R_red1 _ _ (lit (S k))); [constructor | apply R_lit].
Qed.

Lemma R_box c A s : wf_ty (typeof c) A -> typed c [] s A -> R (tCode c) (box A s) (box A s).
Proof. intros HA Hs; exists A, s; split; [|split; [|split]]; auto; apply evalto_value; exact I. Qed.

Lemma R_code_inv c A s t : R (tCode c) (box A s) t -> wf_ty (typeof c) A /\ typed c [] s A.
Proof.
  intros (A' & s' & H & _ & HA & Hs).
  pose proof (evalto_value_inv (box A s) _ I H) as E; injection E as -> ->; auto.
Qed.

Lemma R_csize c t t' : R (tCode c) t t' -> R tNat (csize t) (csize t').
Proof.
  intros (A & s & [H _] & [H' _] & _).
  assert (Hc : forall t0 t1, reds t0 t1 -> reds (csize t0) (csize t1))
    by (apply reds_cong; constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hc _ _ H) (Hc _ _ H')).
  apply (R_red1 _ _ (lit (size s))); [constructor |].
  apply R_sym, (R_red1 _ _ (lit (size s))); [constructor | apply R_lit].
Qed.

Lemma R_quote c c' t t' : hosts (typeof c') c ->
  R (tCode c) t t' -> R (tCode c') (quote c t) (quote c t').
Proof.
  intros Hh (A & s & [H _] & [H' _] & HA & Hs).
  assert (Hc : forall t0 t1, reds t0 t1 -> reds (quote c t0) (quote c t1))
    by (apply reds_cong; constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hc _ _ H) (Hc _ _ H')).
  apply (R_red1 _ _ (box (tCode c) (box A s))); [constructor |].
  apply R_sym, (R_red1 _ _ (box (tCode c) (box A s))); [constructor |].
  apply R_box; [exact Hh | constructor; assumption].
Qed.

Definition ty_eq_dec (A B : ty) : {A = B} + {A <> B}.
Proof. decide equality; apply ls_dec. Defined.

(** The evaluation case, given the theorem for the code's contents. *)
Lemma R_run c B t t' d d' :
  (forall s, typed c [] s B -> R B s s) ->
  R (tCode c) t t' -> R B d d' -> R B (run c B t d) (run c B t' d').
Proof.
  intros HB (A & s & [Ht Hv] & [Ht' _] & HA & Hs) Hd.
  assert (Hc : forall d0 t0 t1, reds t0 t1 -> reds (run c B t0 d0) (run c B t1 d0))
    by (intros d0; apply (reds_cong (fun t => run c B t d0)); constructor; assumption).
  apply (R_expand _ _ _ _ _ (Hc _ _ _ Ht) (Hc _ _ _ Ht')).
  destruct (ty_eq_dec A B) as [-> | Hne].
  - apply (R_red1 _ _ s); [constructor |].
    apply R_sym, (R_red1 _ _ s); [constructor |]; apply HB, Hs.
  - apply (R_red1 _ _ d); [constructor; exact Hne |].
    apply R_sym, (R_red1 _ _ d'); [constructor; exact Hne |]; apply R_sym, Hd.
Qed.

(** *** The fundamental theorem, by recursion on the meta depth *)

Section FT.
Hypotheses (Heval : eval_up) (Hdepth : depth_mono) (Htotal : total_down)
  (Hlift : eval_lift).

(** The only case that needs the depth is evaluation: [run] at [j] checks
    its code's contents at a layer of lower depth ([eval_up]), so it uses
    the theorem below [j]'s depth.  Nothing else looks inside a [box]. *)
Lemma FT_depth n : forall j Γ t A, typed j Γ t A -> depth (typeof j) < n ->
  total j = true -> forall σ σ', Rsub Γ σ σ' -> R A (subst σ t) (subst σ' t).
Proof.
  induction n as [|n IHn]; intros j Γ t A Hty; [intros; lia |].
  induction Hty as [j Γ x A Hx | j Γ A B t HA Ht IHt | j Γ A B t u Ht IHt Hu IHu
    | j Γ k | j Γ t Ht IHt | j Γ c A s Hh HA Hs _ | j Γ c t Ht IHt
    | j Γ c B t d He Hh HB Ht IHt Hd IHd | j Γ c c' t Hh Hh' Ht IHt
    | j Γ A t Hp HA Ht _ | i j Γ t A Hij Ht IHt];
    intros Hn Htot σ σ' Hσ; cbn.
  - apply Hσ, Hx.
  - apply R_lam; intros u u' Hu; apply IHt; auto using Rsub_cons.
  - apply (IHt Hn Htot _ _ Hσ), IHu; assumption.
  - apply R_lit.
  - apply R_succ, IHt; assumption.
  - apply R_box; assumption.
  - apply (R_csize c), IHt; assumption.
  - apply R_run; [| apply IHt | apply IHd]; try assumption.
    intros s Hs; rewrite <- (subst_var s).
    apply (IHn c []); [exact Hs | | | exact Rsub_var_nil].
    + pose proof (Heval _ _ He Hh); lia.
    + exact (Htotal _ _ (Hlift _ _ He) Htot).
  - apply R_quote; [assumption | apply IHt; assumption].
  - congruence.
  - apply IHt; [pose proof (Hdepth _ _ Hij); lia | exact (Htotal _ _ Hij Htot) | exact Hσ].
Qed.

Theorem FT_typed j Γ t A : typed j Γ t A -> total j = true ->
  forall σ σ', Rsub Γ σ σ' -> R A (subst σ t) (subst σ' t).
Proof. intros H; apply (FT_depth (S (depth (typeof j))) _ _ _ _ H); lia. Qed.

Lemma FT_closed j t A : typed j [] t A -> total j = true -> R A t t.
Proof.
  intros H Ht; rewrite <- (subst_var t); exact (FT_typed _ _ _ _ H Ht _ _ Rsub_var_nil).
Qed.

(** Normalization: a closed numeral at a total layer evaluates to a
    literal.  Conversion's two side conditions are not needed. *)
Theorem normalization j t : typed j [] t tNat -> total j = true ->
  exists k, evalto t (lit k).
Proof. intros H Ht; destruct (FT_closed _ _ _ H Ht) as (k & Hk & _); eauto. Qed.

(** **** Conversion *)

Hypotheses (Hstatic : static_code) (Hsdown : static_down).

(** At a static layer conversion is syntactic equality. *)
Lemma conv_static j Γ t t' A : conv j Γ t t' A -> computes j = false ->
  t = t' /\ typed j Γ t A.
Proof.
  induction 1; intros Hc; try congruence.
  all: repeat match goal with
         | IH : computes ?i = false -> _ /\ _ |- _ =>
             let E := fresh "E" in let Hty := fresh "Hty" in
             destruct IH as [E Hty];
             [ first [ exact Hc | eapply Hsdown; eassumption | eapply Hstatic; eassumption ]
             | subst ]
         end.
  all: split; [reflexivity | eauto using typed].
Qed.

Theorem FT_conv j Γ t t' A : conv j Γ t t' A -> total j = true ->
  forall σ σ', Rsub Γ σ σ' -> R A (subst σ t) (subst σ' t').
Proof.
  induction 1 as [j Γ t A Ht | j Γ t t' A _ IH | j Γ t t' t'' A _ IH1 _ IH2
    | i j Γ t t' A Hij _ IH | j Γ A B t t' HA _ IH | j Γ A B t t' u u' _ IHt _ IHu
    | j Γ t t' _ IH | j Γ c A s s' Hh HA Hs _ | j Γ c t t' _ IH
    | j Γ c B t t' d d' He Hh HB _ IHt _ IHd | j Γ c c' t t' Hh Hh' _ IH
    | j Γ A t t' Hp _ _ _
    | j Γ A B t u _ HA Ht Hu | j Γ k _ | j Γ c A s _ Hb
    | j Γ c B s d _ He Hh HB Hs Hd | j Γ c A B s d _ Hne He Hh HB Hb Hd
    | j Γ c c' A s _ Hh Hh' Hb];
    intros Htot σ σ' Hσ; cbn [subst].
  - exact (FT_typed _ _ _ _ Ht Htot _ _ Hσ).
  - apply R_sym, IH; [exact Htot | apply Rsub_sym, Hσ].
  - apply (R_trans _ _ (subst σ' t')); [apply IH1 | apply IH2]; auto.
    exact (Rsub_refl_r _ _ _ Hσ).
  - apply IH; [exact (Htotal _ _ Hij Htot) | exact Hσ].
  - apply R_lam; intros u u' Hu; apply IH; auto using Rsub_cons.
  - apply (IHt Htot _ _ Hσ), IHu; assumption.
  - apply R_succ, IH; assumption.
  - destruct (conv_static _ _ _ _ _ Hs (Hstatic _ _ Hh)) as [<- Hs'].
    apply R_box; assumption.
  - apply (R_csize c), IH; assumption.
  - apply R_run; [| apply IHt | apply IHd]; try assumption.
    intros s Hs; apply (FT_closed c); [exact Hs |].
    exact (Htotal _ _ (Hlift _ _ He) Htot).
  - apply R_quote; [assumption | apply IH; assumption].
  - congruence.
  - rewrite subst_single_comp.
    apply (R_red1 _ _ (subst (scons (subst σ u) var) (subst (up σ) t))); [constructor |].
    rewrite subst_beta; apply (FT_typed _ _ _ _ Ht Htot).
    apply Rsub_cons; [exact Hσ | exact (FT_typed _ _ _ _ Hu Htot _ _ Hσ)].
  - apply (R_red1 _ _ (lit (S k))); [constructor | apply R_lit].
  - apply (R_red1 _ _ (lit (size s))); [constructor | apply R_lit].
  - rewrite (closed_subst _ _ _ _ Hs).
    apply (R_red1 _ _ s); [constructor |].
    exact (FT_closed _ _ _ Hs (Htotal _ _ (Hlift _ _ He) Htot)).
  - apply (R_red1 _ _ (subst σ d)); [constructor; exact Hne |].
    exact (FT_typed _ _ _ _ Hd Htot _ _ Hσ).
  - pose proof (FT_typed _ _ _ _ Hb Htot _ _ Hσ) as Hr; cbn [subst] in Hr.
    destruct (R_code_inv _ _ _ _ Hr) as [HA Hs].
    apply (R_red1 _ _ (box (tCode c) (box A s))); [constructor |].
    apply R_box; [exact Hh | constructor; assumption].
Qed.

(** Conversion is sound for numerals at total layers. *)
Theorem conv_sound j t t' : conv j [] t t' tNat -> total j = true ->
  exists k, evalto t (lit k) /\ evalto t' (lit k).
Proof.
  intros H Ht; rewrite <- (subst_var t), <- (subst_var t').
  exact (FT_conv _ _ _ _ _ H Ht _ _ Rsub_var_nil).
Qed.

End FT.
End Rules.

(** All six side conditions. *)
Record good (Λ : LS) : Prop := {
  g_static : static_code Λ;
  g_sdown : static_down Λ;
  g_eval : eval_up Λ;
  g_depth : depth_mono Λ;
  g_total : total_down Λ;
  g_lift : eval_lift Λ;
}.

(** ** Terms without a normal form *)

Ltac inv_value_red := match goal with
  | H : red (lam _ _) _ |- _ => inversion H
  | H : red (lit _) _ |- _ => inversion H
  | H : red (box _ _) _ |- _ => inversion H
  end.

Section Diverge.
Context {L : Type}.
Local Notation tm := (tm L).

(** General recursion: [fix x. x]. *)
Definition loop : tm := fix_ tNat (var 0).

Lemma loop_reds t v : reds t v -> t = loop -> v = loop.
Proof.
  induction 1 as [| t t1 t2 Hs _ IH]; intros E; [exact E |].
  apply IH; subst; inversion Hs; reflexivity.
Qed.

Lemma loop_diverges : ~ exists v, evalto loop v.
Proof. intros (v & H & Hv); rewrite (loop_reds _ _ H eq_refl) in Hv; exact Hv. Qed.

(** The liar: [d := λx. succ (run x (λ_. 0) x)] applied to its own code,
    [d ⌜d⌝ ⇝ succ (d ⌜d⌝)].  Lawvere's diagonal: [run] makes every code
    of a function on codes that function. *)
Section Liar.
Variable c : L.

Definition lB : ty L := tArr (tCode c) tNat.
Definition ldflt : tm := lam (tCode c) (lit 0).
Definition ld : tm := lam (tCode c) (succ (app (run c lB (var 0) ldflt) (var 0))).
Definition lY : tm := app (run c lB (box lB ld) ldflt) (box lB ld).
Definition lΩ : tm := app ld (box lB ld).

Inductive LInv : tm -> Prop :=
| li_Ω : LInv lΩ
| li_Y : LInv (succ lY)
| li_succ t : LInv t -> LInv (succ t).

Lemma LInv_not_lit t : LInv t -> forall k, t <> lit k.
Proof. destruct 1; discriminate. Qed.

Lemma red_lY t : red lY t -> t = lΩ.
Proof.
  intros Hr; inversion Hr; subst; try inv_value_red.
  match goal with H : red (run _ _ _ _) _ |- _ => inversion H; subst end.
  - reflexivity.
  - contradiction.
  - inv_value_red.
Qed.

Lemma LInv_red t t' : LInv t -> red t t' -> LInv t'.
Proof.
  intros H; revert t'; induction H as [| | t H IH]; intros t' Hr.
  - inversion Hr; subst; [exact li_Y |].
    match goal with H : red ld _ |- _ => inversion H end.
  - inversion Hr; subst.
    match goal with H : red lY _ |- _ => rewrite (red_lY _ H) end.
    exact (li_succ _ li_Ω).
  - inversion Hr; subst.
    + exfalso; exact (LInv_not_lit _ H _ eq_refl).
    + apply li_succ, IH; assumption.
Qed.

Lemma liar_diverges : ~ exists v, evalto lΩ v.
Proof.
  intros (v & H & Hv).
  assert (Hi : LInv v).
  { pose proof li_Ω as Hi; clear Hv; induction H as [| t t1 t2 Hs _ IH]; [exact Hi |].
    exact (IH (LInv_red _ _ Hi Hs)). }
  destruct Hi; exact Hv.
Qed.

End Liar.

Lemma run_loop_diverges c : ~ exists v, evalto (run c tNat (box tNat loop) (lit 0)) v.
Proof.
  intros (v & H & Hv); inversion H; subst; [exact Hv |].
  match goal with Hs : red (run _ _ _ _) _ |- _ => inversion Hs; subst end.
  - apply loop_diverges; eexists; split; eassumption.
  - contradiction.
  - inv_value_red.
Qed.

End Diverge.

(** Typing the liar: [d] is typed at a layer [a] that runs [c]-code, and
    must be [c]-code itself, so [Code c] is a type of [c]'s own programs. *)
Section LiarTyped.
Variable Λ : LS.
Local Notation typeof := (ls_typeof Λ).
Local Notation hosts := (ls_hosts Λ).

Lemma ld_typed a c : ls_evals Λ a c -> hosts (typeof a) c -> hosts (typeof c) c ->
  typed Λ a [] (ld c) (lB c).
Proof.
  intros He Ha Hc; unfold ld, lB, ldflt.
  apply ty_lam; [exact Ha |].
  apply ty_succ, (ty_app _ _ _ (tCode c)); [| apply ty_var; reflexivity].
  apply ty_run; [exact He | exact Ha | split; [exact Hc | exact I] | apply ty_var; reflexivity |].
  apply ty_lam; [exact Ha | apply ty_lit].
Qed.

Lemma lΩ_typed j c : typed Λ c [] (ld c) (lB c) -> typed Λ j [] (ld c) (lB c) ->
  hosts (typeof j) c -> hosts (typeof c) c -> typed Λ j [] (lΩ c) tNat.
Proof.
  intros Hc Hj Hh Hcc; apply (ty_app _ _ _ (tCode c)); [exact Hj |].
  apply ty_box; [exact Hh | split; [exact Hcc | exact I] | exact Hc].
Qed.

(** Two codes equal by β, told apart by [csize]: [(λx. x) 0] and [0]. *)
Definition s1 {L} : tm L := app (lam tNat (var 0)) (lit 0).

Lemma s1_typed c : typed Λ c [] s1 tNat.
Proof. apply (ty_app _ _ _ tNat); [apply ty_lam; [exact I | apply ty_var; reflexivity] | apply ty_lit]. Qed.

Lemma collapse j c : hosts (typeof j) c -> ls_computes Λ j = true ->
  conv Λ c [] s1 (lit 0) tNat -> conv Λ j [] (lit 4) (lit 1) tNat.
Proof.
  intros Hh Hj Hc.
  apply (cv_trans _ _ _ _ (csize (box tNat s1))).
  { apply cv_sym, (cv_csize_box _ _ _ c); [exact Hj | apply ty_box; auto using s1_typed; exact I]. }
  apply (cv_trans _ _ _ _ (csize (box tNat (lit 0)))).
  { apply (cv_csize _ _ _ c), cv_box; [exact Hh | exact I | exact Hc]. }
  apply (cv_csize_box _ _ _ c); [exact Hj | apply ty_box; [exact Hh | exact I | apply ty_lit]].
Qed.

Lemma collapse_unsound j : conv Λ j [] (lit 4) (lit 1) tNat ->
  ~ (forall t t', conv Λ j [] t t' tNat -> exists k, evalto t (lit k) /\ evalto t' (lit k)).
Proof.
  intros H Hs; destruct (Hs _ _ H) as (k & H4 & H1).
  apply evalto_value_inv in H4, H1; try exact I; congruence.
Qed.

End LiarTyped.

(** ** The grid: {code, program} × meta depth, plus V *)

Inductive cell := gV | gC (k : nat) | gP (k : nat).

Definition cell_eq_dec (x y : cell) : {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition level (x : cell) : nat := match x with gV => 0 | gC k | gP k => k end.

(** [C_k ≤ C_k'], [C_k ≤ P_k'] and [P_k ≤ P_k'] for [k ≤ k'], never
    [P_k ≤ C_k']: a program does not become code. *)
Definition gle (x y : cell) : Prop :=
  match x, y with
  | gV, _ => True
  | gC k, gC k' | gC k, gP k' | gP k, gP k' => k <= k'
  | _, _ => False
  end.

(** [C_k]'s programs and their types are [P_k]'s. *)
Definition gtypeof (x : cell) : cell := match x with gV => gP 0 | gC k | gP k => gP k end.
Definition gcomputes (x : cell) : bool := match x with gP _ => true | _ => false end.

(** [P_k'] hosts [C_k] for [k < k' ≤ n]; with [refl], also for [k = k']:
    every program row may then analyse its own code (the reflexive cell
    R, below). *)
Definition ghosts (n : nat) (refl : bool) (x c : cell) : Prop :=
  match x, c with
  | gP k', gC k => (if refl then k <= k' else k < k') /\ k' <= n
  | _, _ => False
  end.

(** [n] meta levels; code is hosted reflexively when [hrefl], run at its
    own level when [erefl]; total below level [m]. *)
Definition grid_gen (n : nat) (hrefl erefl : bool) (m : nat) : LS := {|
  ls_L := cell;
  ls_dec := cell_eq_dec;
  ls_le := gle;
  ls_typeof := gtypeof;
  ls_computes := gcomputes;
  ls_hosts := ghosts n hrefl;
  ls_evals := fun x c => ghosts n erefl (gtypeof x) c /\ gle c x;
  ls_total := fun x => level x <? m;
  ls_depth := level;
|}.

Definition grid n m := grid_gen n false false m.

Ltac solve_cond :=
  intros;
  repeat match goal with x : cell |- _ => destruct x end;
  cbn -[Nat.ltb] in *; rewrite ?Nat.ltb_lt in *;
  intuition (try discriminate; try lia; try congruence).

(** The grid meets every side condition, at every depth [n], with code
    hosted at its own level or not, and partial from any level [m] up. *)
Theorem grid_good n hrefl m : good (grid_gen n hrefl false m).
Proof.
  constructor; unfold static_code, static_down, eval_up, depth_mono, total_down,
    eval_lift; cbn -[Nat.ltb]; destruct hrefl; solve_cond.
Qed.

Corollary grid_normalization n hrefl m j t :
  typed (grid_gen n hrefl false m) j [] t tNat -> level j < m ->
  exists k, evalto t (lit k).
Proof.
  intros H Hj; destruct (grid_good n hrefl m) as [Hs Hsd He Hd Ht Hl].
  apply (normalization _ He Hd Ht Hl j); [exact H | cbn; apply Nat.ltb_lt, Hj].
Qed.

Corollary grid_conv_sound n hrefl m j t t' :
  conv (grid_gen n hrefl false m) j [] t t' tNat -> level j < m ->
  exists k, evalto t (lit k) /\ evalto t' (lit k).
Proof.
  intros H Hj; destruct (grid_good n hrefl m) as [Hs Hsd He Hd Ht Hl].
  apply (conv_sound _ He Hd Ht Hl Hs Hsd j); [exact H | cbn; apply Nat.ltb_lt, Hj].
Qed.

(** *** A partial top level *)

(** With [fix] at level [n] only, every lower level still normalizes
    ([grid_normalization] at [m = n]), and the top really is partial. *)
Lemma partial_top n : typed (grid n n) (gP n) [] loop tNat /\ ~ exists v : tm cell, evalto loop v.
Proof.
  split; [| exact loop_diverges].
  apply ty_fix; [cbn; apply Nat.ltb_irrefl | exact I | apply ty_var; reflexivity].
Qed.

(** *** Depth two: □□, T and 4 *)

Section Depth2.
Local Notation G := (grid 2 3).

(** [□□]: code of code, at [P₂]. *)
Example boxbox : typed G (gP 2) [] (box (tCode (gC 0)) (box tNat (lit 7))) (tCode (gC 1)).
Proof.
  apply ty_box; cbn; [lia | lia |].
  apply ty_box; cbn; [lia | exact I | apply ty_lit].
Qed.

(** Axiom 4, [□A → □□A], as [quote]. *)
Definition four : tm cell := lam (tCode (gC 0)) (quote (gC 0) (var 0)).

Example four_typed : typed G (gP 2) [] four (tArr (tCode (gC 0)) (tCode (gC 1))).
Proof.
  apply ty_lam; cbn; [lia |].
  apply ty_quote with (c := gC 0); cbn; [lia | lia | apply ty_var; reflexivity].
Qed.

(** Axiom T twice, [□□A → A]: run the outer code, then the inner. *)
Definition eval2 : tm cell :=
  lam (tCode (gC 1))
    (run (gC 0) tNat (run (gC 1) (tCode (gC 0)) (var 0) (box tNat (lit 0))) (lit 0)).

Example eval2_typed : typed G (gP 2) [] eval2 (tArr (tCode (gC 1)) tNat).
Proof.
  apply ty_lam; cbn; [lia |].
  apply ty_run; cbn; [lia | lia | exact I | | apply ty_lit].
  apply ty_run; cbn; [lia | lia | lia | apply ty_var; reflexivity |].
  apply ty_box; cbn; [lia | exact I | apply ty_lit].
Qed.

Example eval2_four : evalto (app eval2 (app four (box tNat (lit 7)))) (lit 7).
Proof.
  split; [| exact I].
  repeat (eapply reds_step; [solve [repeat constructor] |]); cbn; apply reds_refl.
Qed.

End Depth2.

(** ** DeLaM is the grid's depth-1 slice *)

Inductive layer := lV | lC | lD | lM.

Definition layer_eq_dec (x y : layer) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** As [Typing/Context.v]: [typeof], [compt], [lle]. *)
Definition dtypeof (i : layer) : layer := match i with lM => lM | _ => lD end.
Definition dcomputes (i : layer) : bool := match i with lD | lM => true | _ => false end.
Definition lrank (i : layer) : nat := match i with lV => 0 | lC => 1 | lD => 2 | lM => 3 end.
Definition dlle (i j : layer) : Prop := lrank i <= lrank j.
Definition ddepth (i : layer) : nat := match i with lM => 1 | _ => 0 end.
Definition dhosts (k c : layer) : Prop := k = lM /\ c = lC.

Definition dls (le : layer -> layer -> Prop) (comp : layer -> bool)
    (hosts evals : layer -> layer -> Prop) (tot : layer -> bool) : LS := {|
  ls_L := layer;
  ls_dec := layer_eq_dec;
  ls_le := le;
  ls_typeof := dtypeof;
  ls_computes := comp;
  ls_hosts := hosts;
  ls_evals := evals;
  ls_total := tot;
  ls_depth := ddepth;
|}.

(** DeLaM: [□] at M over C, with the recursors and [letbox] there. *)
Definition delam : LS := dls dlle dcomputes dhosts dhosts (fun _ => true).

Ltac solve_dcond :=
  intros;
  repeat match goal with x : layer |- _ => destruct x end;
  cbn in *; unfold dlle, dhosts in *; cbn in *;
  intuition (try discriminate; try lia; try congruence).

Theorem delam_good : good delam.
Proof.
  constructor; unfold static_code, static_down, eval_up, depth_mono, total_down,
    eval_lift; cbn; solve_dcond.
Qed.

Definition emb (i : layer) : cell :=
  match i with lV => gV | lC => gC 0 | lD => gP 0 | lM => gP 1 end.

Lemma emb_inj i j : emb i = emb j -> i = j.
Proof. destruct i, j; cbn; congruence. Qed.

Lemma emb_le i j : dlle i j <-> gle (emb i) (emb j).
Proof. unfold dlle; destruct i, j; cbn; lia. Qed.

Lemma emb_typeof i : emb (dtypeof i) = gtypeof (emb i).
Proof. destruct i; reflexivity. Qed.

Lemma emb_computes i : dcomputes i = gcomputes (emb i).
Proof. destruct i; reflexivity. Qed.

Lemma emb_depth i : ddepth (dtypeof i) = level (gtypeof (emb i)).
Proof. destruct i; reflexivity. Qed.

Lemma emb_hosts k c : dhosts k c <-> ghosts 1 false (emb k) (emb c).
Proof. unfold dhosts; destruct k, c; cbn; intuition (try discriminate; try lia). Qed.

Lemma emb_evals j c : dhosts j c <->
  ls_evals (grid 1 2) (emb j) (emb c).
Proof. unfold dhosts; destruct j, c; cbn; intuition (try discriminate; try lia). Qed.

Lemma emb_total i : ls_total delam i = ls_total (grid 1 2) (emb i).
Proof. destruct i; reflexivity. Qed.

(** The slice is [V, C₀, P₀, P₁]; of depth-1 cells only [C₁], code of M,
    is missing, and nothing hosts it, so [□□] and axiom 4 are not
    formable. *)
Lemma emb_image x : (exists i, emb i = x) <-> x = gV \/ x = gC 0 \/ x = gP 0 \/ x = gP 1.
Proof.
  split; [intros [[] <-]; cbn; tauto |].
  intros [-> | [-> | [-> | ->]]]; [exists lV | exists lC | exists lD | exists lM]; reflexivity.
Qed.

Lemma grid1_C1_unhosted k : ~ ghosts 1 false k (gC 1).
Proof. destruct k; cbn; lia. Qed.

(** ** Counterexamples: each side condition is needed *)

(** For each condition, a structure that meets the other five, in which
    normalization or conversion soundness fails. *)

(** *** (S1) Analysed code computes: DeLaM with C computing *)

Definition cx_static : LS :=
  dls dlle (fun i => match i with lV => false | _ => true end) dhosts dhosts (fun _ => true).

Lemma cx_static_others : static_down cx_static /\ eval_up cx_static /\
  depth_mono cx_static /\ total_down cx_static /\ eval_lift cx_static.
Proof.
  unfold static_down, eval_up, depth_mono, total_down, eval_lift; cbn.
  repeat split; solve_dcond.
Qed.

Lemma cx_static_fails : ~ static_code cx_static.
Proof. intros H; discriminate (H lM lC (conj eq_refl eq_refl)). Qed.

(** [csize ⌜(λx. x) 0⌝ ≡ csize ⌜0⌝] at M: [4 ≡ 1]. *)
Lemma cx_static_collapse : conv cx_static lM [] (lit 4) (lit 1) tNat.
Proof.
  apply (collapse cx_static lM lC); [split; reflexivity | reflexivity |].
  apply (cv_beta cx_static lC [] tNat tNat (var 0) (lit 0));
    [reflexivity | exact I | apply ty_var; reflexivity | apply ty_lit].
Qed.

(** *** (W1) A computing layer lifts into analysed code: DeLaM with D ≤ C *)

Definition cx_sdown : LS :=
  dls (fun i j => dlle i j \/ (i = lD /\ j = lC)) dcomputes dhosts dhosts (fun _ => true).

Lemma cx_sdown_others : static_code cx_sdown /\ eval_up cx_sdown /\
  depth_mono cx_sdown /\ total_down cx_sdown /\ eval_lift cx_sdown.
Proof.
  unfold static_code, eval_up, depth_mono, total_down, eval_lift; cbn.
  repeat split; solve_dcond.
Qed.

Lemma cx_sdown_fails : ~ static_down cx_sdown.
Proof. intros H; discriminate (H lD lC (or_intror (conj eq_refl eq_refl)) eq_refl). Qed.

Lemma cx_sdown_collapse : conv cx_sdown lM [] (lit 4) (lit 1) tNat.
Proof.
  apply (collapse cx_sdown lM lC); [split; reflexivity | reflexivity |].
  apply cv_lift with (i := lD); [right; split; reflexivity |].
  apply (cv_beta cx_sdown lD [] tNat tNat (var 0) (lit 0));
    [reflexivity | exact I | apply ty_var; reflexivity | apply ty_lit].
Qed.

(** *** (S2) Evaluation at the code's own depth: the reflexive cell with T *)

(** Every program row hosts and runs its own code.  This is the cell R of
    the Weaver/Löb design (issue #47) given T at R itself. *)
Definition cx_eval : LS := grid_gen 1 true true 2.

Lemma cx_eval_others : static_code cx_eval /\ static_down cx_eval /\
  depth_mono cx_eval /\ total_down cx_eval /\ eval_lift cx_eval.
Proof.
  unfold static_code, static_down, depth_mono, total_down, eval_lift; cbn -[Nat.ltb].
  repeat split; solve_cond.
Qed.

Lemma cx_eval_fails : ~ eval_up cx_eval.
Proof.
  intros H; assert (Hc : ls_evals cx_eval (gC 0) (gC 0)) by (cbn; lia).
  specialize (H _ _ Hc ltac:(cbn; lia)); cbn in H; lia.
Qed.

Lemma cx_eval_liar : typed cx_eval (gP 0) [] (lΩ (gC 0)) tNat /\
  ls_total cx_eval (gP 0) = true /\ ~ exists v, evalto (lΩ (gC 0)) v.
Proof.
  split; [| split; [reflexivity | apply liar_diverges]].
  assert (Hd : typed cx_eval (gC 0) [] (ld (gC 0)) (lB (gC 0)))
    by (apply ld_typed; cbn; lia).
  apply lΩ_typed; [exact Hd | apply ty_lift with (i := (gC 0)); [cbn; lia | exact Hd] | cbn; lia | cbn; lia].
Qed.

(** *** (W2) Lifting lowers the depth: [C₁ ≤ C₀] *)

(** Code of M lowered into code of D, which D hosts (reflexively). *)
Definition cx_depth : LS := {|
  ls_L := cell;
  ls_dec := cell_eq_dec;
  ls_le := fun x y => gle x y \/ (x = gC 1 /\ y = gC 0);
  ls_typeof := gtypeof;
  ls_computes := gcomputes;
  ls_hosts := ghosts 1 true;
  ls_evals := fun x c => ghosts 1 false (gtypeof x) c /\ gle c x;
  ls_total := fun _ => true;
  ls_depth := level;
|}.

Lemma cx_depth_others : static_code cx_depth /\ static_down cx_depth /\
  eval_up cx_depth /\ total_down cx_depth /\ eval_lift cx_depth.
Proof.
  unfold static_code, static_down, eval_up, total_down, eval_lift; cbn.
  repeat split; solve_cond.
Qed.

Lemma cx_depth_fails : ~ depth_mono cx_depth.
Proof. intros H; specialize (H (gC 1) (gC 0) (or_intror (conj eq_refl eq_refl))); cbn in H; lia. Qed.

Lemma cx_depth_liar : typed cx_depth (gC 1) [] (lΩ (gC 0)) tNat /\
  ~ exists v, evalto (lΩ (gC 0)) v.
Proof.
  split; [| apply liar_diverges].
  assert (Hd : typed cx_depth (gC 1) [] (ld (gC 0)) (lB (gC 0)))
    by (apply ld_typed; cbn; lia).
  apply lΩ_typed; [apply ty_lift with (i := (gC 1)); [right; split; reflexivity | exact Hd]
                  | exact Hd | cbn; lia | cbn; lia].
Qed.

(** *** (W3) A partial layer lifts into a total one: DeLaM with D partial *)

Definition cx_total : LS :=
  dls dlle dcomputes dhosts dhosts (fun i => match i with lD => false | _ => true end).

Lemma cx_total_others : static_code cx_total /\ static_down cx_total /\
  eval_up cx_total /\ depth_mono cx_total /\ eval_lift cx_total.
Proof.
  unfold static_code, static_down, eval_up, depth_mono, eval_lift; cbn.
  repeat split; solve_dcond.
Qed.

Lemma cx_total_fails : ~ total_down cx_total.
Proof.
  intros H; assert (Hle : ls_le cx_total lD lM) by (cbn; unfold dlle; cbn; lia).
  discriminate (H _ _ Hle eq_refl).
Qed.

Lemma cx_total_loop : typed cx_total lM [] loop tNat /\ ~ exists v : tm layer, evalto loop v.
Proof.
  split; [| apply loop_diverges].
  apply ty_lift with (i := lD); [cbn; unfold dlle; cbn; lia |].
  apply ty_fix; [reflexivity | exact I | apply ty_var; reflexivity].
Qed.

(** *** (W4) A total layer runs code that does not lift into it *)

(** C and D partial, M total, and neither C nor D lifts into M. *)
Definition cx_lift : LS :=
  dls (fun i j => dlle i j /\ ~ ((i = lC \/ i = lD) /\ j = lM)) dcomputes dhosts dhosts
    (fun i => match i with lC | lD => false | _ => true end).

Lemma cx_lift_others : static_code cx_lift /\ static_down cx_lift /\
  eval_up cx_lift /\ depth_mono cx_lift /\ total_down cx_lift.
Proof.
  unfold static_code, static_down, eval_up, depth_mono, total_down; cbn.
  repeat split; solve_dcond.
Qed.

Lemma cx_lift_fails : ~ eval_lift cx_lift.
Proof.
  intros H; destruct (H lM lC (conj eq_refl eq_refl)) as [_ Hn].
  apply Hn; split; [left |]; reflexivity.
Qed.

Lemma cx_lift_loop : typed cx_lift lM [] (run lC tNat (box tNat loop) (lit 0)) tNat /\
  ~ exists v, evalto (run lC tNat (box tNat loop) (lit 0)) v.
Proof.
  split; [| apply run_loop_diverges].
  apply ty_run; [split; reflexivity | split; reflexivity | exact I | | apply ty_lit].
  apply ty_box; [split; reflexivity | exact I |].
  apply ty_fix; [reflexivity | exact I | apply ty_var; reflexivity].
Qed.

(** ** The reflexive cell R (issue #47) *)

(** R's code is hosted at R itself, analysed there but run only one level
    up.  In the grid that is reflexive hosting with evaluation still
    strictly upward, [grid_gen n true false m], which [grid_good] covers:
    every program row may analyse its own code.  Running it at its own
    level, [grid_gen n true true m], is [cx_eval]: the liar. *)
Definition gridR (n m : nat) : LS := grid_gen n true false m.

Example R_analyses_own_code :
  typed (gridR 1 2) (gP 0) [] (csize (box tNat (lit 0))) tNat.
Proof. apply ty_csize with (c := gC 0), ty_box; cbn; [lia | exact I | apply ty_lit]. Qed.

Example R_runs_below : typed (gridR 1 2) (gP 1) []
  (lam (tCode (gC 0)) (run (gC 0) tNat (var 0) (lit 0))) (tArr (tCode (gC 0)) tNat).
Proof.
  apply ty_lam; cbn; [lia |].
  apply ty_run; cbn; [lia | lia | exact I | apply ty_var; reflexivity | apply ty_lit].
Qed.

Lemma R_no_own_eval c : ~ ls_evals (gridR 1 2) (gP 0) c.
Proof. destruct c; cbn; lia. Qed.
