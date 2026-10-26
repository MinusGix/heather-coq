(** * The domain model at DeLaM's code layer: a probe

    Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès and
    Weirich, "Definitional Inversion, Without Normalisation"
    (arXiv:2607.13662, `H/docs/2607.13662v1.pdf`; Heather's
    `docs/definitional-inversion-survey.md` and
    `issues/definitional-inversion-domain-model.md`) prove injectivity of
    Π without normalisation, from a domain model whose compact elements
    are finite data and a logical relation by recursion on those
    witnesses. The question of this probe: does the method extend to
    DeLaM's code layer, where boxed code is compared by syntactic equality
    and the recursor [elim_Typ] inspects a code's structure?

    The object theory is MLTTη (Π with β and η, [𝒰 : 𝒰]) plus one code
    former in DeLaM's shape:
    - codes [cd] (layer C): [cU], [cPi a b] and code variables [cv u]
      (global variables at layer C). Codes are first order (no binders),
      so the recursor's motive is not indexed by a context; see the end
      of the file for what that leaves out;
    - [Code] (DeLaM's [□(· ⊢ Ty)]), [box c], whose congruence is
      reflexivity only (Static Code, as in this repo since M2's D3);
    - [elim P bU bPi t], [elim_Typ]'s shape: the [Π] branch binds the two
      subcodes as global code variables [U_S], [U_T] and the two
      recursive results as local variables, and β passes it the codes
      themselves;
    - [letbox P t s], which splices a code into a code variable.

    Part 1 (the model and its soundness). The domain is an interface:
    the operations of the paper's §2.5 on [D] (U, Π, λ, application, the
    projector [p]) and its semantic typing, with the paper's facts about
    them as hypotheses, plus the new elements: a type code [CODE], and
    one element [Q c] per code, flat (a code is finite data, below
    nothing but [⊥]), with [CASEQ] reading a code off an element. The
    interpretation [den] is concrete. An environment has a local part
    (domain elements) and a {e syntactic} global part: code variables are
    interpreted by codes, [den (box c) ρ τ = Q (c[τ])], because the
    recursor and the box congruence both see code literally. Checked:
    - the semantic renaming and substitution lemmas, local and global
      ([den_ren], [den_sub]), and continuity of [den] in its local
      environment ([den_cont], which β needs);
    - soundness for the whole calculus ([soundness]): typing gives
      semantic typing, conversion gives equal denotations. The recursor
      is interpreted by structural recursion on the code ([recR]);
    - from soundness alone (as the paper's Thm 2.32): Static Code
      ([static_code]: [box c ≡ box c'] implies [c = c']) and
      disjointness of [Code] from [𝒰] and [Π] ([code_not_U],
      [code_not_pi]).

    Part 2 (the relation). The relation at the old witnesses is
    abstract, with the paper's clauses and §2.7 laws as hypotheses; at
    the new ones it is the clause the paper's [ℕ] suggests: at the type
    witness [Cd] both types reduce to [Code], and at the term witness
    [Q c] both terms reduce to [box c], the same code. The syntactic side
    (the judgment the clauses mention, its substitution lemma) is
    abstract too, and consistent (everywhere true satisfies it).
    Checked:
    - the clause satisfies the laws of §2.7 ([RCd_*]; flatness makes
      monotonicity and joins trivial), including head reduction both ways
      ([RCd_hred], from determinism of reduction);
    - the fundamental theorem's cases for [Code], [box], [elim] and its
      two β-rules (the recursor by induction on the code, [elim_box]),
      and [letbox] and its β-rule;
    - adequacy ([adequacy], the paper's Thm 2.35) by induction on the
      derivation, from those and the paper's cases for MLTTη's rules;
    - Π-injectivity ([pi_injectivity], [pi_injectivity_closed]): the
      paper's two-line proof of Cor. 2.37, unchanged.

    The notes at the end of the file say what the probe leaves out and
    how it bears on the four layer-M equations of
    [Validity/DeclConsequences.v]. No axioms ([Print Assumptions] at the
    end). Standalone: [coqc probes/CodeDomainModel.v], about 3 s. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

(** ** Syntax *)

Inductive cd : Type := cU | cPi (a b : cd) | cv (u : nat).

Inductive tm : Type :=
| var (n : nat)
| U
| Pi (A B : tm)
| lam (A t : tm)
| app (t s : tm)
| Code
| box (c : cd)
(** [elim P bU bPi t]: [P] binds a local variable (the scrutinee);
    [bPi] binds two code variables ([U_S] = [cv 1], [U_T] = [cv 0]) and
    then two local ones ([x_S] = [var 1], [x_T] = [var 0]). *)
| elim (P bU bPi t : tm)
(** [letbox P t s]: [P] binds a local variable, [s] a code variable. *)
| letbox (P t s : tm).

Definition scons {A} (x : A) (f : nat -> A) (n : nat) : A :=
  match n with 0 => x | S n => f n end.
Notation "x .: f" := (scons x f) (at level 55, right associativity).

Definition up (r : nat -> nat) : nat -> nat := 0 .: (fun n => S (r n)).

Fixpoint cren (c : cd) (g : nat -> nat) : cd :=
  match c with cU => cU | cPi a b => cPi (cren a g) (cren b g) | cv u => cv (g u) end.

Fixpoint csub (c : cd) (θ : nat -> cd) : cd :=
  match c with cU => cU | cPi a b => cPi (csub a θ) (csub b θ) | cv u => θ u end.

(** Renaming, local ([r]) and global ([g]) at once. *)
Fixpoint ren (t : tm) (r g : nat -> nat) : tm :=
  match t with
  | var n => var (r n)
  | U => U
  | Pi A B => Pi (ren A r g) (ren B (up r) g)
  | lam A t => lam (ren A r g) (ren t (up r) g)
  | app t s => app (ren t r g) (ren s r g)
  | Code => Code
  | box c => box (cren c g)
  | elim P bU bPi t => elim (ren P (up r) g) (ren bU r g) (ren bPi (up (up r)) (up (up g))) (ren t r g)
  | letbox P t s => letbox (ren P (up r) g) (ren t r g) (ren s r (up g))
  end.

Definition upl (σ : nat -> tm) : nat -> tm := var 0 .: (fun n => ren (σ n) S (fun u => u)).
Definition upg (σ : nat -> tm) : nat -> tm := fun n => ren (σ n) (fun k => k) S.
Definition upc (θ : nat -> cd) : nat -> cd := cv 0 .: (fun u => cren (θ u) S).

(** Substitution: [σ] for the local variables, [θ] for the code
    variables. [σ]'s terms are in the target scope, so [θ] does not act
    on them. *)
Fixpoint sub (t : tm) (σ : nat -> tm) (θ : nat -> cd) : tm :=
  match t with
  | var n => σ n
  | U => U
  | Pi A B => Pi (sub A σ θ) (sub B (upl σ) θ)
  | lam A t => lam (sub A σ θ) (sub t (upl σ) θ)
  | app t s => app (sub t σ θ) (sub s σ θ)
  | Code => Code
  | box c => box (csub c θ)
  | elim P bU bPi t =>
      elim (sub P (upl σ) θ) (sub bU σ θ) (sub bPi (upl (upl (upg (upg σ)))) (upc (upc θ))) (sub t σ θ)
  | letbox P t s => letbox (sub P (upl σ) θ) (sub t σ θ) (sub s (upg σ) (upc θ))
  end.

Definition gid : nat -> cd := cv.
(** [M[N]], the single substitution of the last local variable. *)
Definition inst (M N : tm) : tm := sub M (N .: var) gid.
(** A context weakened by [k] code variables (global weakening). *)
Definition gshift (k : nat) (Γ : list tm) : list tm := map (fun A => ren A (fun n => n) (fun u => k + u)) Γ.

(** The [Π] branch's scope: [U_S, U_T] global, [x_S : P[box U_S]],
    [x_T : P[box U_T]], and its result type [P[box (cPi U_S U_T)]]. *)
Definition sh2 (u : nat) : cd := cv (S (S u)).
Definition brS (P : tm) : tm := sub P (box (cv 1) .: var) sh2.
Definition brT (P : tm) : tm := sub P (box (cv 0) .: (fun n => var (S n))) sh2.
Definition brRes (P : tm) : tm := sub P (box (cPi (cv 1) (cv 0)) .: (fun n => var (S (S n)))) sh2.
(** [letbox]'s body type [P[box u]] under the new code variable. *)
Definition lbRes (P : tm) : tm := sub P (box (cv 0) .: var) (fun u => cv (S u)).
(** [elim]'s β at [cPi a b]: the subcodes for [U_S], [U_T], the
    recursive calls for [x_S], [x_T]. *)
Definition betaPi (P bU bPi : tm) (a b : cd) : tm :=
  sub bPi (elim P bU bPi (box b) .: elim P bU bPi (box a) .: var) (b .: a .: gid).

(** Code well-formedness at layer C: its code variables are in scope. *)
Fixpoint cwf (Ψ : nat) (c : cd) : Prop :=
  match c with cU => True | cPi a b => cwf Ψ a /\ cwf Ψ b | cv u => u < Ψ end.

(** ** The declarative system: typing as the diagonal of conversion

    One judgment [Ψ ; Γ ⊢ M ≡ N : A] ([eqj]), typing being [M ≡ M] (the
    Lean mechanisation's choice, survey §2). [Ψ] counts the code
    variables. Every rule carries the presuppositions its soundness case
    uses (the paper's §4), and the congruences of [elim] and [letbox]
    also their right-hand sides' typing, which the relation's head
    reductions of the right-hand side need (Part 2). [box]'s only
    conversion is reflexivity. *)

Inductive eqj : nat -> list tm -> tm -> tm -> tm -> Prop :=
| e_var Ψ Γ n A : nth_error Γ n = Some A ->
    eqj Ψ Γ (var n) (var n) (ren A (fun k => S n + k) (fun u => u))
| e_sym Ψ Γ M N A : eqj Ψ Γ M N A -> eqj Ψ Γ N M A
| e_trans Ψ Γ M N O A : eqj Ψ Γ M N A -> eqj Ψ Γ N O A -> eqj Ψ Γ M O A
| e_conv Ψ Γ M N A B : eqj Ψ Γ M N A -> eqj Ψ Γ A B U -> eqj Ψ Γ M N B
| e_U Ψ Γ : eqj Ψ Γ U U U
| e_Pi Ψ Γ A A' B B' : eqj Ψ Γ A A' U -> eqj Ψ (A :: Γ) B B' U -> eqj Ψ Γ (Pi A B) (Pi A' B') U
| e_lam Ψ Γ A A' B M M' : eqj Ψ Γ A A' U -> eqj Ψ (A :: Γ) M M' B ->
    eqj Ψ Γ (lam A M) (lam A' M') (Pi A B)
| e_app Ψ Γ A B M M' N N' : eqj Ψ Γ M M' (Pi A B) -> eqj Ψ Γ N N' A ->
    eqj Ψ Γ (app M N) (app M' N') (inst B N)
| e_beta Ψ Γ A B M N : eqj Ψ Γ A A U -> eqj Ψ (A :: Γ) M M B -> eqj Ψ Γ N N A ->
    eqj Ψ Γ (app (lam A M) N) (inst M N) (inst B N)
| e_eta Ψ Γ A B M N : eqj Ψ Γ A A U -> eqj Ψ Γ M M (Pi A B) -> eqj Ψ Γ N N (Pi A B) ->
    eqj Ψ (A :: Γ) (app (ren M S (fun u => u)) (var 0)) (app (ren N S (fun u => u)) (var 0)) B ->
    eqj Ψ Γ M N (Pi A B)
| e_Code Ψ Γ : eqj Ψ Γ Code Code U
| e_box Ψ Γ c : cwf Ψ c -> eqj Ψ Γ (box c) (box c) Code
| e_elim Ψ Γ P P' bU bU' bPi bPi' t t' :
    eqj Ψ (Code :: Γ) P P' U ->
    eqj Ψ Γ bU bU' (inst P (box cU)) ->
    eqj (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi' (brRes P) ->
    eqj Ψ Γ t t' Code ->
    eqj Ψ (Code :: Γ) P' P' U ->
    eqj Ψ Γ bU' bU' (inst P' (box cU)) ->
    eqj (S (S Ψ)) (brT P' :: brS P' :: gshift 2 Γ) bPi' bPi' (brRes P') ->
    eqj Ψ Γ (elim P bU bPi t) (elim P' bU' bPi' t') (inst P t)
| e_elimU Ψ Γ P bU bPi :
    eqj Ψ (Code :: Γ) P P U ->
    eqj Ψ Γ bU bU (inst P (box cU)) ->
    eqj (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi (brRes P) ->
    eqj Ψ Γ (elim P bU bPi (box cU)) bU (inst P (box cU))
| e_elimPi Ψ Γ P bU bPi a b :
    eqj Ψ (Code :: Γ) P P U ->
    eqj Ψ Γ bU bU (inst P (box cU)) ->
    eqj (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi (brRes P) ->
    cwf Ψ a -> cwf Ψ b ->
    eqj Ψ Γ (elim P bU bPi (box (cPi a b))) (betaPi P bU bPi a b) (inst P (box (cPi a b)))
| e_letbox Ψ Γ P P' t t' s s' :
    eqj Ψ (Code :: Γ) P P' U ->
    eqj Ψ Γ t t' Code ->
    eqj (S Ψ) (gshift 1 Γ) s s' (lbRes P) ->
    eqj Ψ (Code :: Γ) P' P' U ->
    eqj (S Ψ) (gshift 1 Γ) s' s' (lbRes P') ->
    eqj Ψ Γ (letbox P t s) (letbox P' t' s') (inst P t)
| e_letboxb Ψ Γ P c s :
    eqj Ψ (Code :: Γ) P P U ->
    cwf Ψ c ->
    eqj (S Ψ) (gshift 1 Γ) s s (lbRes P) ->
    eqj Ψ Γ (letbox P (box c) s) (sub s var (c .: gid)) (inst P (box c)).

(** ** Syntactic lemmas: renamings and substitutions compose

    Pure syntax, for Part 2: the fundamental theorem reads every premise
    under a substitution, so it needs the usual composition laws, for
    the two kinds of variable and the binders of [elim] and [letbox]. *)

Lemma csub_cren c g θ : csub (cren c g) θ = csub c (fun u => θ (g u)).
Proof. induction c; cbn; f_equal; auto. Qed.

Lemma csub_csub c θ τ : csub (csub c θ) τ = csub c (fun u => csub (θ u) τ).
Proof. induction c; cbn; f_equal; auto. Qed.

Lemma csub_ext c θ θ' : (forall u, θ u = θ' u) -> csub c θ = csub c θ'.
Proof. intros H; induction c; cbn; f_equal; auto. Qed.

Lemma csub_id c : csub c gid = c.
Proof. induction c; cbn; f_equal; auto. Qed.

Lemma cren_ext c g g' : (forall u, g u = g' u) -> cren c g = cren c g'.
Proof. intros H; induction c; cbn; f_equal; auto. Qed.
Lemma cren_cren c g g' : cren (cren c g) g' = cren c (fun u => g' (g u)).
Proof. induction c; cbn; f_equal; auto. Qed.
Lemma cren_csub c θ g : cren (csub c θ) g = csub c (fun u => cren (θ u) g).
Proof. induction c; cbn; f_equal; auto. Qed.
Lemma cren_as_csub c g : cren c g = csub c (fun u => cv (g u)).
Proof. induction c; cbn; f_equal; auto. Qed.
Lemma cren_id c : cren c (fun u => u) = c.
Proof. induction c; cbn; f_equal; auto. Qed.

Lemma up_ext r r' : (forall n, r n = r' n) -> forall n, up r n = up r' n.
Proof. intros H [| n]; cbn; f_equal; auto. Qed.

Lemma ren_ext t : forall r r' g g', (forall n, r n = r' n) -> (forall u, g u = g' u) ->
  ren t r g = ren t r' g'.
Proof.
  induction t; intros r r' g g' Hr Hg; cbn; f_equal; auto using cren_ext;
    match goal with IH : forall _ _ _ _, _ -> _ -> ren ?t _ _ = _ |- ren ?t _ _ = _ =>
      apply IH; repeat apply up_ext; assumption end.
Qed.

Lemma upl_ext σ σ' : (forall n, σ n = σ' n) -> forall n, upl σ n = upl σ' n.
Proof. intros H [| n]; cbn; [reflexivity | rewrite H; reflexivity]. Qed.
Lemma upg_ext σ σ' : (forall n, σ n = σ' n) -> forall n, upg σ n = upg σ' n.
Proof. intros H n; unfold upg; rewrite H; reflexivity. Qed.
Lemma upc_ext θ θ' : (forall u, θ u = θ' u) -> forall u, upc θ u = upc θ' u.
Proof. intros H [| u]; cbn; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma sub_ext t : forall σ σ' θ θ', (forall n, σ n = σ' n) -> (forall u, θ u = θ' u) ->
  sub t σ θ = sub t σ' θ'.
Proof.
  induction t; intros σ σ' θ θ' Hσ Hθ; cbn; f_equal; auto using csub_ext;
    match goal with IH : forall _ _ _ _, _ -> _ -> sub ?t _ _ = _ |- sub ?t _ _ = _ =>
      apply IH; repeat (apply upl_ext || apply upg_ext || apply upc_ext); assumption end.
Qed.

Ltac rw_ih := match goal with IH : forall _ _ _ _, _ |- _ => rewrite IH end.

Lemma ren_ren t : forall r g r' g', ren (ren t r g) r' g' = ren t (fun n => r' (r n)) (fun u => g' (g u)).
Proof.
  induction t; intros r g r' g'; cbn; f_equal; rewrite ?cren_cren; auto;
    rw_ih; apply ren_ext; intros [| [| ?]]; reflexivity.
Qed.

Lemma ren_sub t : forall r g σ θ, sub (ren t r g) σ θ = sub t (fun n => σ (r n)) (fun u => θ (g u)).
Proof.
  induction t; intros r g σ θ; cbn; f_equal; rewrite ?csub_cren; auto;
    rw_ih; apply sub_ext; intros [| [| ?]]; reflexivity.
Qed.

Lemma sub_ren t : forall σ θ r g,
  ren (sub t σ θ) r g = sub t (fun n => ren (σ n) r g) (fun u => cren (θ u) g).
Proof.
  induction t; intros σ θ r g; cbn; f_equal; rewrite ?cren_csub; auto;
    rw_ih; apply sub_ext; intros [| [| ?]]; cbn; unfold upg;
    rewrite ?ren_ren, ?cren_cren; try reflexivity; (apply ren_ext || apply cren_ext); reflexivity.
Qed.

Lemma sub_sub t : forall σ θ σ' θ',
  sub (sub t σ θ) σ' θ' = sub t (fun n => sub (σ n) σ' θ') (fun u => csub (θ u) θ').
Proof.
  induction t; intros σ θ σ' θ'; cbn; f_equal; rewrite ?csub_csub; auto;
    rw_ih; apply sub_ext; intros [| [| ?]]; cbn; unfold upg;
    rewrite ?ren_sub, ?sub_ren, ?csub_cren, ?cren_csub; try reflexivity;
    (apply sub_ext || apply csub_ext); intros; unfold upl, upc; cbn; unfold upg;
    rewrite ?ren_ren, ?cren_cren, ?cren_id; reflexivity.
Qed.

(** A substitution by variables is a renaming. *)
Lemma sub_vars t : forall σ θ r g, (forall n, σ n = var (r n)) -> (forall u, θ u = cv (g u)) ->
  sub t σ θ = ren t r g.
Proof.
  induction t; intros σ θ r g Hσ Hθ; cbn; try apply Hσ; f_equal; auto.
  all: try (rewrite cren_as_csub; apply csub_ext; exact Hθ).
  all: match goal with IH : forall _ _ _ _, _ -> _ -> _ |- _ => apply IH end; intros [| [| ?]]; cbn; unfold upg;
       rewrite ?Hσ, ?Hθ; reflexivity.
Qed.

Lemma ren_id t : forall r g, (forall n, r n = n) -> (forall u, g u = u) -> ren t r g = t.
Proof.
  induction t; intros r g Hr Hg; cbn; f_equal; auto.
  all: try (rewrite (cren_ext _ _ _ Hg); apply cren_id).
  all: match goal with IH : forall _ _, _ -> _ -> _ |- _ => apply IH end; intros [| [| ?]]; cbn; rewrite ?Hr, ?Hg;
       reflexivity.
Qed.

Lemma sub_id' t σ θ : (forall n, σ n = var n) -> (forall u, θ u = cv u) -> sub t σ θ = t.
Proof.
  intros Hσ Hθ. rewrite (sub_vars t σ θ (fun n => n) (fun u => u) Hσ Hθ). apply ren_id; reflexivity.
Qed.

Lemma sub_id t : sub t var gid = t.
Proof. apply sub_id'; reflexivity. Qed.

(** The instances Part 2 uses. [σ2]/[τ2] below are the substitutions
    [sub] uses under [elim]'s [Π] branch. *)

Lemma sub_inst P N σ τ : sub (inst P N) σ τ = sub P (sub N σ τ .: σ) τ.
Proof. unfold inst. rewrite sub_sub. apply sub_ext; [intros [| n] | intros u]; reflexivity. Qed.

Lemma inst_upl P N σ τ : inst (sub P (upl σ) τ) N = sub P (N .: σ) τ.
Proof.
  unfold inst. rewrite sub_sub. apply sub_ext.
  - intros [| n]; cbn; [reflexivity |]. rewrite ren_sub. apply sub_id'; reflexivity.
  - intros u. apply csub_id.
Qed.

Lemma brRes_up P σ τ :
  sub (brRes P) (upl (upl (upg (upg σ)))) (upc (upc τ)) = brRes (sub P (upl σ) τ).
Proof.
  unfold brRes. rewrite !sub_sub. apply sub_ext.
  - intros [| n]; cbn; [reflexivity |]. unfold upg. rewrite ren_sub, !ren_ren.
    symmetry. apply sub_vars; reflexivity.
  - intros u; cbn. rewrite !cren_cren, cren_as_csub. reflexivity.
Qed.

Lemma brRes_inst P N1 N2 σ a b τ : sub (brRes P) (N1 .: N2 .: σ) (b .: a .: τ) = sub P (box (cPi a b) .: σ) τ.
Proof. unfold brRes. rewrite sub_sub. apply sub_ext; [intros [| n] | intros u]; reflexivity. Qed.
Lemma brS_inst P σ a b τ : sub (brS P) σ (b .: a .: τ) = sub P (box a .: σ) τ.
Proof. unfold brS. rewrite sub_sub. apply sub_ext; [intros [| n] | intros u]; reflexivity. Qed.
Lemma brT_inst P N σ a b τ : sub (brT P) (N .: σ) (b .: a .: τ) = sub P (box b .: σ) τ.
Proof. unfold brT. rewrite sub_sub. apply sub_ext; [intros [| n] | intros u]; reflexivity. Qed.

Lemma betaPi_sub P bU bPi σ τ a b :
  betaPi (sub P (upl σ) τ) (sub bU σ τ) (sub bPi (upl (upl (upg (upg σ)))) (upc (upc τ))) a b =
  sub bPi (elim (sub P (upl σ) τ) (sub bU σ τ) (sub bPi (upl (upl (upg (upg σ)))) (upc (upc τ))) (box b)
           .: elim (sub P (upl σ) τ) (sub bU σ τ) (sub bPi (upl (upl (upg (upg σ)))) (upc (upc τ))) (box a)
           .: σ) (b .: a .: τ).
Proof.
  unfold betaPi. rewrite sub_sub. apply sub_ext.
  - intros [| [| n]]; cbn; [reflexivity | reflexivity |]. unfold upg. rewrite !ren_sub. apply sub_id'; reflexivity.
  - intros [| [| u]]; cbn; [reflexivity | reflexivity |]. rewrite !csub_cren. apply csub_id.
Qed.

Lemma lbRes_up P σ τ : sub (lbRes P) (upg σ) (upc τ) = lbRes (sub P (upl σ) τ).
Proof.
  unfold lbRes. rewrite !sub_sub. apply sub_ext.
  - intros [| n]; cbn; [reflexivity |]. unfold upg. rewrite ren_sub. symmetry. apply sub_vars; reflexivity.
  - intros u; cbn. rewrite cren_as_csub. reflexivity.
Qed.

Lemma letbox_beta_sub s σ τ c : sub (sub s (upg σ) (upc τ)) var (c .: gid) = sub s σ (c .: τ).
Proof.
  rewrite sub_sub. apply sub_ext.
  - intros n. unfold upg. rewrite ren_sub. apply sub_id'; reflexivity.
  - intros [| u]; cbn; [reflexivity |]. rewrite csub_cren. apply csub_id.
Qed.

Lemma sub_gsingle s c σ τ : sub (sub s var (c .: gid)) σ τ = sub s σ (csub c τ .: τ).
Proof. rewrite sub_sub. apply sub_ext; [intros n | intros [| u]]; reflexivity. Qed.

(** ** Head reduction (weak head, deterministic) *)

Inductive hred : tm -> tm -> Prop :=
| hr_beta A t s : hred (app (lam A t) s) (inst t s)
| hr_app t t' s : hred t t' -> hred (app t s) (app t' s)
| hr_elimU P bU bPi : hred (elim P bU bPi (box cU)) bU
| hr_elimPi P bU bPi a b : hred (elim P bU bPi (box (cPi a b))) (betaPi P bU bPi a b)
| hr_elim P bU bPi t t' : hred t t' -> hred (elim P bU bPi t) (elim P bU bPi t')
| hr_lbb P c s : hred (letbox P (box c) s) (sub s var (c .: gid))
| hr_lb P t t' s : hred t t' -> hred (letbox P t s) (letbox P t' s).

Inductive hreds : tm -> tm -> Prop :=
| hs_refl M : hreds M M
| hs_step M N O : hred M N -> hreds N O -> hreds M O.

Lemma hred_det M N1 N2 : hred M N1 -> hred M N2 -> N1 = N2.
Proof.
  intros H1; revert N2; induction H1; intros N2 H2; inversion H2; subst; auto;
    try match goal with H : hred (lam _ _) _ |- _ => inversion H | H : hred (box _) _ |- _ => inversion H end;
    f_equal; auto.
Qed.

Lemma hreds_trans M N O : hreds M N -> hreds N O -> hreds M O.
Proof. induction 1; eauto using hreds. Qed.

Lemma hreds_det M N1 N2 : hreds M N1 -> hreds M N2 -> hreds N1 N2 \/ hreds N2 N1.
Proof.
  intros H1; revert N2; induction H1 as [M | M N O HMN HNO IH]; intros N2 H2; [left; exact H2 |].
  destruct H2 as [| M N' O' HMN' HNO']; [right; eauto using hreds |].
  rewrite (hred_det _ _ _ HMN HMN') in IH. exact (IH _ HNO').
Qed.

Lemma hreds_whnf M N : (forall N', ~ hred M N') -> hreds M N -> N = M.
Proof. intros Hn H; destruct H as [| M N' O H _]; [reflexivity | exfalso; exact (Hn _ H)]. Qed.

Lemma hreds_box c N : hreds (box c) N -> N = box c.
Proof. apply hreds_whnf. intros N' H; inversion H. Qed.
Lemma hreds_Pi A B N : hreds (Pi A B) N -> N = Pi A B.
Proof. apply hreds_whnf. intros N' H; inversion H. Qed.

Lemma hreds_elim P bU bPi t t' : hreds t t' -> hreds (elim P bU bPi t) (elim P bU bPi t').
Proof. induction 1; eauto using hreds, hred. Qed.
Lemma hreds_letbox P t t' s : hreds t t' -> hreds (letbox P t s) (letbox P t' s).
Proof. induction 1; eauto using hreds, hred. Qed.
Lemma hreds_one M N : hred M N -> hreds M N.
Proof. eauto using hreds. Qed.

(** ** Part 1: the domain model *)

Section Model.

(** The domain [D] (the paper's ideals of compacts) and its operations
    (§2.5, Fig. 4 right). [LAM] and [PI] take Coq functions; only on
    continuous ones ([Cont]) does the paper's [D] give them meaning, so β
    is assumed only there. *)
Variable D : Type.
Variables (BOT UU : D) (PI : D -> (D -> D) -> D) (LAM : (D -> D) -> D) (APP : D -> D -> D)
  (p : D -> D -> D).
(** Semantic typing [x : a] on [D] (§2.2, last display). *)
Variable TY : D -> D -> Prop.
(** The new elements: the type code of [Code], one element per code,
    and the case on a code. In the paper's terms: [C] gains the codes
    [Cd :ₙ₊₁ U] and [Q c :ₙ₊₁ Cd] for every code [c], a constant summand
    of the domain equation, and [CASEQ x k = ⋁ {k c | Q c ≤ x}]. *)
Variables (CODE : D) (Q : cd -> D) (CASEQ : D -> (cd -> D) -> D).
Variable Cont : (D -> D) -> Prop.

(** The paper's facts (§2.2–§2.5) about MLTTη's part. *)
Hypothesis TY_bot : forall a, TY BOT a.
Hypothesis TY_U : TY UU UU.
Hypothesis TY_p : forall a u, TY a UU -> TY (p a u) a.
Hypothesis p_id : forall a u, TY u a -> p a u = u.
Hypothesis TY_pi : forall a f, TY a UU -> (forall u, TY u a -> TY (f u) UU) ->
  TY (PI a (fun u => f (p a u))) UU.
Hypothesis TY_lam : forall a f g, TY a UU -> (forall u, TY u a -> TY (f u) (g u)) ->
  TY (LAM (fun u => f (p a u))) (PI a (fun u => g (p a u))).
Hypothesis TY_app : forall m n a g, TY m (PI a g) -> TY n a -> TY (APP m n) (g n).
Hypothesis beta : forall f x, Cont f -> APP (LAM f) x = f x.
Hypothesis eta : forall a g m, TY a UU -> TY m (PI a g) -> LAM (fun u => APP m (p a u)) = m.
Hypothesis LAM_ext : forall f g, (forall u, f u = g u) -> LAM f = LAM g.
Hypothesis PI_ext : forall a f g, (forall u, f u = g u) -> PI a f = PI a g.
Hypothesis U_not_PI : forall a f, UU <> PI a f.
Hypothesis Cont_const : forall x, Cont (fun _ => x).
Hypothesis Cont_id : Cont (fun u => u).
Hypothesis Cont_APP : forall F G, Cont F -> Cont G -> Cont (fun u => APP (F u) (G u)).
Hypothesis Cont_p : forall F G, Cont F -> Cont G -> Cont (fun u => p (F u) (G u)).
Hypothesis Cont_LAM : forall (H : D -> D -> D), (forall v, Cont (fun u => H u v)) ->
  Cont (fun u => LAM (H u)).
Hypothesis Cont_PI : forall F (H : D -> D -> D), Cont F -> (forall v, Cont (fun u => H u v)) ->
  Cont (fun u => PI (F u) (H u)).

(** The new elements' facts. Each holds in the extended model: [Cd] and
    [Q c] are new constructors of [C], the code part is flat, and an
    ideal typed by [Cd] is [{⊥}] or [{⊥, Q c}]. *)
Hypothesis TY_CODE : TY CODE UU.
Hypothesis TY_Q : forall c, TY (Q c) CODE.
Hypothesis CODE_inv : forall x, TY x CODE -> x = BOT \/ exists c, x = Q c.
Hypothesis CASEQ_BOT : forall k, CASEQ BOT k = BOT.
Hypothesis CASEQ_Q : forall c k, CASEQ (Q c) k = k c.
Hypothesis CASEQ_ext : forall x k k', (forall c, k c = k' c) -> CASEQ x k = CASEQ x k'.
Hypothesis Cont_CASEQ : forall F (K : D -> cd -> D), Cont F -> (forall c, Cont (fun u => K u c)) ->
  Cont (fun u => CASEQ (F u) (K u)).
Hypothesis Q_inj : forall c c', Q c = Q c' -> c = c'.
Hypothesis CODE_not_U : CODE <> UU.
Hypothesis CODE_not_PI : forall a f, CODE <> PI a f.

(** *** The interpretation

    Environments: [ρ : nat -> D] for the local variables, [τ : nat -> cd]
    for the code variables (syntactic). The recursor is read off the code
    by structural recursion: [recR] interprets the branch [cU] by [fU],
    and [cPi a b] by [fPi] with the subcodes in the code environment and
    the recursive results in the local one; a code variable (a stuck
    recursor, DeLaM's [elim (box U^δ)]) is [⊥]. *)

Fixpoint recR (fU fPi : (nat -> D) -> (nat -> cd) -> D) (ρ : nat -> D) (τ : nat -> cd) (c : cd) : D :=
  match c with
  | cU => fU ρ τ
  | cPi a b => fPi (recR fU fPi ρ τ b .: recR fU fPi ρ τ a .: ρ) (b .: a .: τ)
  | cv _ => BOT
  end.

Fixpoint den (t : tm) (ρ : nat -> D) (τ : nat -> cd) {struct t} : D :=
  match t with
  | var n => ρ n
  | U => UU
  | Pi A B => PI (den A ρ τ) (fun u => den B (p (den A ρ τ) u .: ρ) τ)
  | lam A t => LAM (fun u => den t (p (den A ρ τ) u .: ρ) τ)
  | app t s => APP (den t ρ τ) (den s ρ τ)
  | Code => CODE
  | box c => Q (csub c τ)
  | elim P bU bPi t => CASEQ (den t ρ τ) (recR (den bU) (den bPi) ρ τ)
  | letbox P t s => CASEQ (den t ρ τ) (fun c => den s ρ (c .: τ))
  end.

(** *** Extensionality, renaming, substitution *)

Lemma recR_ext fU fPi gU gPi ρ ρ' τ τ' :
  (forall n, ρ n = ρ' n) -> (forall u, τ u = τ' u) ->
  (forall ρ1 ρ2 τ1 τ2, (forall n, ρ1 n = ρ2 n) -> (forall u, τ1 u = τ2 u) -> fU ρ1 τ1 = gU ρ2 τ2) ->
  (forall ρ1 ρ2 τ1 τ2, (forall n, ρ1 n = ρ2 n) -> (forall u, τ1 u = τ2 u) -> fPi ρ1 τ1 = gPi ρ2 τ2) ->
  forall c, recR fU fPi ρ τ c = recR gU gPi ρ' τ' c.
Proof.
  intros Hρ Hτ HU HPi c; induction c as [| a IHa b IHb | u]; cbn; auto.
  apply HPi.
  - intros [| [| n]]; cbn; auto.
  - intros [| [| u]]; cbn; auto.
Qed.

Lemma den_ext t : forall ρ ρ' τ τ', (forall n, ρ n = ρ' n) -> (forall u, τ u = τ' u) ->
  den t ρ τ = den t ρ' τ'.
Proof.
  induction t as [n | | A IHA B IHB | A IHA t IHt | t IHt s IHs | | c | P IHP bU IHU bPi IHPi t IHt
                 | P IHP t IHt s IHs];
    intros ρ ρ' τ τ' Hρ Hτ; cbn; auto.
  - erewrite IHA by eauto. apply PI_ext; intros u. apply IHB; auto.
    intros [| n]; cbn; auto.
  - apply LAM_ext; intros u. erewrite IHA by eauto. apply IHt; auto. intros [| n]; cbn; auto.
  - erewrite IHt, IHs by eauto. reflexivity.
  - f_equal. induction c as [| a IHa b IHb | u]; cbn; f_equal; auto.
  - erewrite IHt by eauto. apply CASEQ_ext; intros c. apply recR_ext; auto.
  - erewrite IHt by eauto. apply CASEQ_ext; intros c. apply IHs; auto. intros [| u]; cbn; auto.
Qed.

Lemma den_ren t : forall r g ρ τ, den (ren t r g) ρ τ = den t (fun n => ρ (r n)) (fun u => τ (g u)).
Proof.
  induction t as [n | | A IHA B IHB | A IHA t IHt | t IHt s IHs | | c | P IHP bU IHU bPi IHPi t IHt
                 | P IHP t IHt s IHs];
    intros r g ρ τ; cbn; auto.
  - rewrite IHA. apply PI_ext; intros u. rewrite IHB. apply den_ext; auto. intros [| n]; reflexivity.
  - apply LAM_ext; intros u. rewrite IHA, IHt. apply den_ext; auto. intros [| n]; reflexivity.
  - rewrite IHt, IHs. reflexivity.
  - rewrite csub_cren. reflexivity.
  - rewrite IHt. apply CASEQ_ext; intros c.
    revert c; fix F 1; intros [| a b | u]; cbn; auto.
    rewrite IHPi. apply den_ext.
    + intros [| [| n]]; cbn; auto.
    + intros [| [| u]]; cbn; auto.
  - rewrite IHt. apply CASEQ_ext; intros c. rewrite IHs. apply den_ext; auto. intros [| u]; reflexivity.
Qed.

Lemma den_sub t : forall σ θ ρ τ,
  den (sub t σ θ) ρ τ = den t (fun n => den (σ n) ρ τ) (fun u => csub (θ u) τ).
Proof.
  induction t as [n | | A IHA B IHB | A IHA t IHt | t IHt s IHs | | c | P IHP bU IHU bPi IHPi t IHt
                 | P IHP t IHt s IHs];
    intros σ θ ρ τ; cbn; auto.
  - rewrite IHA. apply PI_ext; intros u. rewrite IHB. apply den_ext; auto.
    intros [| n]; cbn; auto. unfold upl; cbn. rewrite den_ren. apply den_ext; reflexivity.
  - apply LAM_ext; intros u. rewrite IHA, IHt. apply den_ext; auto.
    intros [| n]; cbn; auto. unfold upl; cbn. rewrite den_ren. apply den_ext; reflexivity.
  - rewrite IHt, IHs. reflexivity.
  - rewrite csub_csub. reflexivity.
  - rewrite IHt. apply CASEQ_ext; intros c.
    revert c; fix F 1; intros [| a b | u]; cbn; auto.
    rewrite IHPi. apply den_ext.
    + intros [| [| n]]; cbn; auto. unfold upl, upg; cbn. rewrite !den_ren. apply den_ext; reflexivity.
    + intros [| [| u]]; cbn; auto. unfold upc; cbn. rewrite !csub_cren. apply csub_ext; reflexivity.
  - rewrite IHt. apply CASEQ_ext; intros c. rewrite IHs. apply den_ext.
    + intros n. unfold upg. rewrite den_ren. apply den_ext; reflexivity.
    + intros [| u]; cbn; auto. rewrite csub_cren. apply csub_ext; reflexivity.
Qed.

Lemma den_inst M N ρ τ : den (inst M N) ρ τ = den M (den N ρ τ .: ρ) τ.
Proof.
  unfold inst. rewrite den_sub. apply den_ext; [intros [| n]; reflexivity | intros u; reflexivity].
Qed.

(** The branch scopes' types, read in an environment. *)
Lemma den_brS P ρ a b τ : den (brS P) ρ (b .: a .: τ) = den P (Q a .: ρ) τ.
Proof. unfold brS. rewrite den_sub. apply den_ext; [intros [| n] | intros u]; reflexivity. Qed.
Lemma den_brT P x ρ a b τ : den (brT P) (x .: ρ) (b .: a .: τ) = den P (Q b .: ρ) τ.
Proof. unfold brT. rewrite den_sub. apply den_ext; [intros [| n] | intros u]; reflexivity. Qed.
Lemma den_brRes P x y ρ a b τ : den (brRes P) (x .: y .: ρ) (b .: a .: τ) = den P (Q (cPi a b) .: ρ) τ.
Proof. unfold brRes. rewrite den_sub. apply den_ext; [intros [| n] | intros u]; reflexivity. Qed.
Lemma den_lbRes P ρ c τ : den (lbRes P) ρ (c .: τ) = den P (Q c .: ρ) τ.
Proof. unfold lbRes. rewrite den_sub. apply den_ext; [intros [| n] | intros u]; reflexivity. Qed.

(** *** Continuity in the local environment (β needs it) *)

Lemma den_cont t : forall (F : D -> nat -> D) τ, (forall n, Cont (fun u => F u n)) ->
  Cont (fun u => den t (F u) τ).
Proof.
  induction t as [n | | A IHA B IHB | A IHA t IHt | t IHt s IHs | | c | P IHP bU IHU bPi IHPi t IHt
                 | P IHP t IHt s IHs];
    intros F τ HF; cbn.
  - exact (HF n).
  - apply Cont_const.
  - apply Cont_PI; [apply IHA; exact HF |]. intros v.
    apply (IHB (fun u => p (den A (F u) τ) v .: F u)). intros [| n]; cbn; auto.
  - apply (Cont_LAM (fun u v => den t (p (den A (F u) τ) v .: F u) τ)). intros v.
    apply (IHt (fun u => p (den A (F u) τ) v .: F u)). intros [| n]; cbn; auto.
  - apply Cont_APP; auto.
  - apply Cont_const.
  - apply Cont_const.
  - apply (Cont_CASEQ _ (fun u => recR (den bU) (den bPi) (F u) τ)); [apply IHt; exact HF |].
    intros c. revert τ; induction c as [| a IHa b IHb | w]; intros τ; cbn; auto.
    apply (IHPi (fun u => recR (den bU) (den bPi) (F u) τ b .: recR (den bU) (den bPi) (F u) τ a .: F u)).
    intros [| [| n]]; cbn; auto.
  - apply (Cont_CASEQ _ (fun u c => den s (F u) (c .: τ))); [apply IHt; exact HF |].
    intros c. apply IHs. exact HF.
Qed.

(** *** Soundness *)

(** [ρ] fits [Γ] under [τ] (the paper's Def. 2.30): each variable's value
    has its type. Contexts need no well-formedness for soundness. *)
Definition fits (Γ : list tm) (ρ : nat -> D) (τ : nat -> cd) : Prop :=
  forall n A, nth_error Γ n = Some A -> TY (ρ n) (den A (fun k => ρ (S n + k)) τ).

Lemma fits_cons Γ A ρ τ u : fits Γ ρ τ -> TY u (den A ρ τ) -> fits (A :: Γ) (u .: ρ) τ.
Proof.
  intros H Hu [| n] B HB; cbn in HB.
  - injection HB as <-. erewrite den_ext; [exact Hu | intros k; reflexivity | reflexivity].
  - specialize (H n B HB). erewrite den_ext; [exact H | intros k; reflexivity | reflexivity].
Qed.

Lemma fits_gshift k Γ ρ τ τ' : fits Γ ρ τ -> (forall u, τ' (k + u) = τ u) -> fits (gshift k Γ) ρ τ'.
Proof.
  intros H Hτ n A HA. unfold gshift in HA. rewrite nth_error_map in HA.
  destruct (nth_error Γ n) as [B |] eqn:HB; cbn in HA; [| discriminate].
  injection HA as <-. rewrite den_ren. erewrite den_ext; [exact (H n B HB) | reflexivity | exact Hτ].
Qed.

Lemma fits_bot Γ τ : fits Γ (fun _ => BOT) τ.
Proof. intros n A _. apply TY_bot. Qed.

(** The recursor's interpretation along a code: both sides' readings
    agree, and the left one has the motive's type at [Q c]. The [cPi]
    step is the [Π] branch's soundness hypothesis, at the environment
    with the subcodes and the recursive results, which fits the branch's
    scope by the induction hypotheses. *)
Lemma recR_sound P bU bU' bPi bPi' Γ ρ τ :
  fits Γ ρ τ ->
  (den bU ρ τ = den bU' ρ τ /\ TY (den bU ρ τ) (den (inst P (box cU)) ρ τ)) ->
  (forall ρ' τ', fits (brT P :: brS P :: gshift 2 Γ) ρ' τ' ->
     den bPi ρ' τ' = den bPi' ρ' τ' /\ TY (den bPi ρ' τ') (den (brRes P) ρ' τ')) ->
  forall c, recR (den bU) (den bPi) ρ τ c = recR (den bU') (den bPi') ρ τ c /\
            TY (recR (den bU) (den bPi) ρ τ c) (den P (Q c .: ρ) τ).
Proof.
  intros Hρ [EU TU] HPi c. induction c as [| a [Ea Ta] b [Eb Tb] | u]; cbn.
  - split; [exact EU |]. rewrite den_inst in TU. exact TU.
  - assert (Hf : fits (brT P :: brS P :: gshift 2 Γ)
              (recR (den bU) (den bPi) ρ τ b .: recR (den bU) (den bPi) ρ τ a .: ρ) (b .: a .: τ)).
    { apply fits_cons; [apply fits_cons |].
      - apply (fits_gshift 2 Γ ρ τ). exact Hρ. intros u; reflexivity.
      - rewrite den_brS. exact Ta.
      - rewrite den_brT. exact Tb. }
    destruct (HPi _ _ Hf) as [E T]. rewrite den_brRes in T. split.
    + rewrite <- Ea, <- Eb. exact E.
    + exact T.
  - split; [reflexivity | apply TY_bot].
Qed.

Theorem soundness Ψ Γ M N A : eqj Ψ Γ M N A ->
  forall ρ τ, fits Γ ρ τ -> den M ρ τ = den N ρ τ /\ TY (den M ρ τ) (den A ρ τ).
Proof.
  induction 1 as
    [Ψ Γ n A HA | Ψ Γ M N A _ IH | Ψ Γ M N O A _ IH1 _ IH2 | Ψ Γ M N A B _ IH1 _ IH2 | Ψ Γ
    | Ψ Γ A A' B B' _ IHA _ IHB | Ψ Γ A A' B M M' _ IHA _ IHM | Ψ Γ A B M M' N N' _ IHM _ IHN
    | Ψ Γ A B M N _ IHA _ IHM _ IHN | Ψ Γ A B M N _ IHA _ IHM _ IHN _ IHe | Ψ Γ | Ψ Γ c _
    | Ψ Γ P P' bU bU' bPi bPi' t t' _ IHP _ IHU _ IHPi _ IHt _ _ _ _ _ _ | Ψ Γ P bU bPi _ IHP _ IHU _ IHPi
    | Ψ Γ P bU bPi a b _ IHP _ IHU _ IHPi _ _ | Ψ Γ P P' t t' s s' _ IHP _ IHt _ IHs _ _ _ _
    | Ψ Γ P c s _ IHP _ _ IHs];
    intros ρ τ Hρ.
  - (* variable *)
    split; [reflexivity |]. cbn. rewrite den_ren. exact (Hρ n A HA).
  - destruct (IH ρ τ Hρ) as [E T]. split; [auto | rewrite <- E; exact T].
  - destruct (IH1 ρ τ Hρ) as [E1 T1], (IH2 ρ τ Hρ) as [E2 _]. split; [congruence | exact T1].
  - destruct (IH1 ρ τ Hρ) as [E1 T1], (IH2 ρ τ Hρ) as [E2 _]. split; [exact E1 | rewrite <- E2; exact T1].
  - split; [reflexivity | exact TY_U].
  - (* Π *)
    destruct (IHA ρ τ Hρ) as [EA TA]. cbn in TA |- *. split.
    + rewrite <- EA. apply PI_ext; intros u. apply (IHB _ _ (fits_cons _ _ _ _ _ Hρ (TY_p _ _ TA))).
    + apply (TY_pi _ (fun u => den B (u .: ρ) τ) TA). intros u Hu.
      exact (proj2 (IHB _ _ (fits_cons _ _ _ _ _ Hρ Hu))).
  - (* λ *)
    destruct (IHA ρ τ Hρ) as [EA TA]. cbn in TA |- *. split.
    + apply LAM_ext; intros u. rewrite <- EA. apply (IHM _ _ (fits_cons _ _ _ _ _ Hρ (TY_p _ _ TA))).
    + apply (TY_lam _ (fun u => den M (u .: ρ) τ) (fun u => den B (u .: ρ) τ) TA). intros u Hu.
      exact (proj2 (IHM _ _ (fits_cons _ _ _ _ _ Hρ Hu))).
  - (* application *)
    destruct (IHM ρ τ Hρ) as [EM TM], (IHN ρ τ Hρ) as [EN TN]. cbn. split; [congruence |].
    rewrite den_inst. cbn in TM. pose proof (TY_app _ _ _ _ TM TN) as T. cbn in T.
    rewrite (p_id _ _ TN) in T. exact T.
  - (* β *)
    destruct (IHA ρ τ Hρ) as [_ TA], (IHN ρ τ Hρ) as [_ TN]. cbn in TA.
    assert (E : den (app (lam A M) N) ρ τ = den (inst M N) ρ τ).
    { cbn. rewrite beta.
      - rewrite (p_id _ _ TN), den_inst. reflexivity.
      - apply (den_cont M (fun u => p (den A ρ τ) u .: ρ)). intros [| n]; cbn.
        + apply Cont_p; [apply Cont_const | apply Cont_id].
        + apply Cont_const. }
    split; [exact E |]. rewrite E, !den_inst. exact (proj2 (IHM _ _ (fits_cons _ _ _ _ _ Hρ TN))).
  - (* η *)
    destruct (IHA ρ τ Hρ) as [_ TA], (IHM ρ τ Hρ) as [_ TM], (IHN ρ τ Hρ) as [_ TN].
    cbn in TA, TM, TN |- *. split; [| exact TM].
    rewrite <- (eta _ _ _ TA TM), <- (eta _ _ _ TA TN). apply LAM_ext; intros u.
    destruct (IHe _ _ (fits_cons _ _ _ _ _ Hρ (TY_p _ u TA))) as [E _]. cbn in E.
    rewrite !den_ren in E. erewrite (den_ext M), (den_ext N); [exact E | ..]; reflexivity.
  - split; [reflexivity | exact TY_CODE].
  - split; [reflexivity | apply TY_Q].
  - (* the recursor *)
    destruct (IHt ρ τ Hρ) as [Et Tt]. cbn in Tt |- *.
    assert (HR := recR_sound P bU bU' bPi bPi' Γ ρ τ Hρ (IHU ρ τ Hρ) IHPi).
    split.
    + rewrite <- Et. apply CASEQ_ext; intros c. exact (proj1 (HR c)).
    + rewrite den_inst. destruct (CODE_inv _ Tt) as [E | [c E]]; rewrite E.
      * rewrite CASEQ_BOT. apply TY_bot.
      * rewrite CASEQ_Q. exact (proj2 (HR c)).
  - (* β at [cU] *)
    destruct (IHU ρ τ Hρ) as [_ TU]. cbn. rewrite CASEQ_Q. split; [reflexivity |]. cbn. exact TU.
  - (* β at [cPi a b] *)
    assert (HR := recR_sound P bU bU bPi bPi Γ ρ τ Hρ (IHU ρ τ Hρ) IHPi).
    cbn. rewrite CASEQ_Q. split.
    + unfold betaPi. rewrite den_sub. cbn. apply den_ext.
      * intros [| [| n]]; cbn; rewrite ?CASEQ_Q; reflexivity.
      * intros [| [| u]]; reflexivity.
    + rewrite den_inst. exact (proj2 (HR (cPi (csub a τ) (csub b τ)))).
  - (* letbox *)
    destruct (IHt ρ τ Hρ) as [Et Tt]. cbn in Tt |- *. split.
    + rewrite <- Et. apply CASEQ_ext; intros c.
      apply (IHs _ _ (fits_gshift 1 Γ ρ τ (c .: τ) Hρ (fun u => eq_refl))).
    + rewrite den_inst. destruct (CODE_inv _ Tt) as [E | [c E]]; rewrite E.
      * rewrite CASEQ_BOT. apply TY_bot.
      * rewrite CASEQ_Q. destruct (IHs _ _ (fits_gshift 1 Γ ρ τ (c .: τ) Hρ (fun u => eq_refl))) as [_ T].
        rewrite den_lbRes in T. exact T.
  - (* letbox's β *)
    cbn. rewrite CASEQ_Q. split.
    + rewrite den_sub. apply den_ext; [reflexivity |]. intros [| u]; reflexivity.
    + rewrite den_inst. destruct (IHs _ _ (fits_gshift 1 Γ ρ τ (csub c τ .: τ) Hρ (fun u => eq_refl))) as [_ T].
      rewrite den_lbRes in T. exact T.
Qed.

(** *** Consequences of soundness alone (as the paper's Thm 2.32)

    The environment [(⊥, id)] fits every context: local variables are
    [⊥], and code variables are themselves. *)

Theorem static_code Ψ Γ c c' A : eqj Ψ Γ (box c) (box c') A -> c = c'.
Proof.
  intros H. destruct (soundness _ _ _ _ _ H (fun _ => BOT) gid (fits_bot Γ gid)) as [E _].
  cbn in E. rewrite !csub_id in E. exact (Q_inj _ _ E).
Qed.

Theorem code_not_U Ψ Γ A : ~ eqj Ψ Γ Code U A.
Proof.
  intros H. destruct (soundness _ _ _ _ _ H (fun _ => BOT) gid (fits_bot Γ gid)) as [E _].
  exact (CODE_not_U E).
Qed.

Theorem code_not_pi Ψ Γ A B T : ~ eqj Ψ Γ Code (Pi A B) T.
Proof.
  intros H. destruct (soundness _ _ _ _ _ H (fun _ => BOT) gid (fits_bot Γ gid)) as [E _].
  exact (CODE_not_PI _ _ E).
Qed.

Theorem U_not_pi Ψ Γ A B T : ~ eqj Ψ Γ U (Pi A B) T.
Proof.
  intros H. destruct (soundness _ _ _ _ _ H (fun _ => BOT) gid (fits_bot Γ gid)) as [E _].
  exact (U_not_PI _ _ E).
Qed.

(** ** Part 2: the logical relation

    *** The syntactic side

    The relation's syntactic premises are read in a judgment [J], with
    the closure properties the clauses and the fundamental theorem use:
    the rules of [eqj] they apply, and the syntactic substitution lemma
    ([J_subst]) over well-typed parallel substitutions [TyS]. Both are
    abstract: the intended instance is [J := eqj] with its standard
    syntactic metatheory, which is not this probe's question (the
    paper's development proves it too). Taking [J] and [TyS] to be
    everywhere true satisfies every hypothesis of this block, so they are
    consistent. *)

Variable J : nat -> list tm -> tm -> tm -> tm -> Prop.
Hypothesis J_sym : forall Ψ Γ M N A, J Ψ Γ M N A -> J Ψ Γ N M A.
Hypothesis J_trans : forall Ψ Γ M N O A, J Ψ Γ M N A -> J Ψ Γ N O A -> J Ψ Γ M O A.
Hypothesis J_conv : forall Ψ Γ M N A B, J Ψ Γ M N A -> J Ψ Γ A B U -> J Ψ Γ M N B.
Hypothesis J_U : forall Ψ Γ, J Ψ Γ U U U.
Hypothesis J_Code : forall Ψ Γ, J Ψ Γ Code Code U.
Hypothesis J_box : forall Ψ Γ c, cwf Ψ c -> J Ψ Γ (box c) (box c) Code.
Hypothesis J_elim : forall Ψ Γ P P' bU bU' bPi bPi' t t',
  J Ψ (Code :: Γ) P P' U -> J Ψ Γ bU bU' (inst P (box cU)) ->
  J (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi' (brRes P) -> J Ψ Γ t t' Code ->
  J Ψ Γ (elim P bU bPi t) (elim P' bU' bPi' t') (inst P t).
Hypothesis J_elimU : forall Ψ Γ P bU bPi,
  J Ψ (Code :: Γ) P P U -> J Ψ Γ bU bU (inst P (box cU)) ->
  J (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi (brRes P) ->
  J Ψ Γ (elim P bU bPi (box cU)) bU (inst P (box cU)).
Hypothesis J_elimPi : forall Ψ Γ P bU bPi a b,
  J Ψ (Code :: Γ) P P U -> J Ψ Γ bU bU (inst P (box cU)) ->
  J (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi (brRes P) -> cwf Ψ a -> cwf Ψ b ->
  J Ψ Γ (elim P bU bPi (box (cPi a b))) (betaPi P bU bPi a b) (inst P (box (cPi a b))).
Hypothesis J_letbox : forall Ψ Γ P P' t t' s s',
  J Ψ (Code :: Γ) P P' U -> J Ψ Γ t t' Code -> J (S Ψ) (gshift 1 Γ) s s' (lbRes P) ->
  J Ψ Γ (letbox P t s) (letbox P' t' s') (inst P t).
Hypothesis J_letboxb : forall Ψ Γ P c s,
  J Ψ (Code :: Γ) P P U -> cwf Ψ c -> J (S Ψ) (gshift 1 Γ) s s (lbRes P) ->
  J Ψ Γ (letbox P (box c) s) (sub s var (c .: gid)) (inst P (box c)).

(** [TyS Ψ' Δ Ψ Γ σ σ' τ]: [σ ≡ σ' : Δ → Γ] on local variables, with
    [τ] for the code variables (one code substitution: codes have no
    conversion but identity, so the two sides share it). *)
Variable TyS : nat -> list tm -> nat -> list tm -> (nat -> tm) -> (nat -> tm) -> (nat -> cd) -> Prop.
Hypothesis J_subst : forall Ψ Γ M N A Ψ' Δ σ σ' τ,
  eqj Ψ Γ M N A -> TyS Ψ' Δ Ψ Γ σ σ' τ -> J Ψ' Δ (sub M σ τ) (sub N σ' τ) (sub A σ τ).
Hypothesis TyS_refl_r : forall Ψ' Δ Ψ Γ σ σ' τ, TyS Ψ' Δ Ψ Γ σ σ' τ -> TyS Ψ' Δ Ψ Γ σ' σ' τ.
Hypothesis TyS_cwf : forall Ψ' Δ Ψ Γ σ σ' τ, TyS Ψ' Δ Ψ Γ σ σ' τ -> forall u, u < Ψ -> cwf Ψ' (τ u).
Hypothesis TyS_cons : forall Ψ' Δ Ψ Γ σ σ' τ A N N',
  TyS Ψ' Δ Ψ Γ σ σ' τ -> J Ψ' Δ N N' (sub A σ τ) -> TyS Ψ' Δ Ψ (A :: Γ) (N .: σ) (N' .: σ') τ.
Hypothesis TyS_gshift : forall Ψ' Δ Ψ Γ σ σ' τ k τ',
  TyS Ψ' Δ Ψ Γ σ σ' τ -> (forall u, τ' (k + u) = τ u) -> (forall u, u < k -> cwf Ψ' (τ' u)) ->
  TyS Ψ' Δ (k + Ψ) (gshift k Γ) σ σ' τ'.
Hypothesis TyS_upl : forall Ψ' Δ Ψ Γ σ σ' τ A,
  TyS Ψ' Δ Ψ Γ σ σ' τ -> TyS Ψ' (sub A σ τ :: Δ) Ψ (A :: Γ) (upl σ) (upl σ') τ.
Hypothesis TyS_br : forall Ψ' Δ Ψ Γ σ σ' τ P,
  TyS Ψ' Δ Ψ Γ σ σ' τ ->
  TyS (S (S Ψ')) (brT (sub P (upl σ) τ) :: brS (sub P (upl σ) τ) :: gshift 2 Δ)
      (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ)
      (upl (upl (upg (upg σ)))) (upl (upl (upg (upg σ')))) (upc (upc τ)).
Hypothesis TyS_upg : forall Ψ' Δ Ψ Γ σ σ' τ,
  TyS Ψ' Δ Ψ Γ σ σ' τ -> TyS (S Ψ') (gshift 1 Δ) (S Ψ) (gshift 1 Γ) (upg σ) (upg σ') (upc τ).

(** Typed head reduction [Γ ⊢ M ⇝* N : A] (the paper's §2.6). *)
Definition tred Ψ Γ M N A : Prop := hreds M N /\ J Ψ Γ M N A.

Lemma tred_refl Ψ Γ M A : J Ψ Γ M M A -> tred Ψ Γ M M A.
Proof. split; [constructor | assumption]. Qed.

(** *** The clause for [Code]

    The paper's [ℕ] clause, with codes in place of numerals: at the type
    witness [Cd], both types reduce to [Code]; at a term witness, either
    [⊥] (nothing more) or [Q c], where both terms reduce to [box c], the
    same code. [w : option cd] is the term witness: [None] is [⊥],
    [Some c] is [Q c]. Codes are first order and flat, so the clause does
    not recurse: it compares the code syntactically, as Static Code
    does. *)

Definition RCdTy Ψ Γ A A' : Prop := tred Ψ Γ A Code U /\ tred Ψ Γ A' Code U.

Definition RCdTm Ψ Γ M M' A (w : option cd) : Prop :=
  RCdTy Ψ Γ A A /\
  match w with
  | None => True
  | Some c => cwf Ψ c /\ tred Ψ Γ M (box c) Code /\ tred Ψ Γ M' (box c) Code
  end.

(** The witnesses' order is flat: [None] below everything, [Some c]
    below itself. *)
Definition wle (w w' : option cd) : Prop := w = None \/ w = w'.
Definition wcompat (w1 w2 : option cd) : Prop := w1 = None \/ w2 = None \/ w1 = w2.
Definition wjoin (w1 w2 : option cd) : option cd := match w1 with None => w2 | Some _ => w1 end.

(** The laws of the paper's §2.7, at the new witnesses. *)

Lemma RCd_isType Ψ Γ M N A w : RCdTm Ψ Γ M N A w -> RCdTy Ψ Γ A A.
Proof. intros [H _]; exact H. Qed.

Lemma RCd_bot Ψ Γ M N A : RCdTy Ψ Γ A A -> RCdTm Ψ Γ M N A None.
Proof. intros H; split; [exact H | exact I]. Qed.

Lemma RCd_symmTy Ψ Γ A B : RCdTy Ψ Γ A B -> RCdTy Ψ Γ B A.
Proof. intros [H1 H2]; split; assumption. Qed.

Lemma RCd_transTy Ψ Γ A B C : RCdTy Ψ Γ A B -> RCdTy Ψ Γ B C -> RCdTy Ψ Γ A C.
Proof. intros [H1 _] [_ H2]; split; assumption. Qed.

Lemma RCd_symm Ψ Γ M N A w : RCdTm Ψ Γ M N A w -> RCdTm Ψ Γ N M A w.
Proof. destruct w as [c |]; intros [HA H]; split; try exact HA; [| exact I]. tauto. Qed.

Lemma RCd_trans Ψ Γ M1 M2 M3 A w : RCdTm Ψ Γ M1 M2 A w -> RCdTm Ψ Γ M2 M3 A w -> RCdTm Ψ Γ M1 M3 A w.
Proof. destruct w as [c |]; intros [HA H] [_ H']; split; try exact HA; [| exact I]. tauto. Qed.

Lemma RCd_conv Ψ Γ M N A B w : RCdTy Ψ Γ A B -> RCdTm Ψ Γ M N A w -> RCdTm Ψ Γ M N B w.
Proof. intros [_ HB] [_ H]; split; [split; exact HB | exact H]. Qed.

Lemma RCd_mono Ψ Γ M N A w w' : wle w w' -> RCdTm Ψ Γ M N A w' -> RCdTm Ψ Γ M N A w.
Proof. intros [-> | ->] H; [exact (RCd_bot _ _ _ _ _ (RCd_isType _ _ _ _ _ _ H)) | exact H]. Qed.

Lemma RCd_join Ψ Γ M N A w1 w2 : wcompat w1 w2 ->
  RCdTm Ψ Γ M N A w1 -> RCdTm Ψ Γ M N A w2 -> RCdTm Ψ Γ M N A (wjoin w1 w2).
Proof. intros [-> | [-> | ->]] H1 H2; cbn; [exact H2 | destruct w1; exact H1 | destruct w2; exact H2]. Qed.

(** Lemma 2.34 (head reduction), both directions. The forward one needs
    determinism of reduction, as the paper's [ℕ] clause does. *)
Lemma RCd_hred Ψ Γ M M1 N N1 A w :
  tred Ψ Γ M M1 A -> tred Ψ Γ N N1 A -> J Ψ Γ M N A ->
  RCdTm Ψ Γ M N A w <-> RCdTm Ψ Γ M1 N1 A w.
Proof.
  intros [RM JM] [RN JN] _.
  assert (Fwd : forall X X1 c, hreds X X1 -> J Ψ Γ X X1 A -> J Ψ Γ A Code U ->
                tred Ψ Γ X (box c) Code -> tred Ψ Γ X1 (box c) Code).
  { intros X X1 c R JX HA [R' J']. split.
    - destruct (hreds_det _ _ _ R R') as [H | H]; [exact H | rewrite (hreds_box _ _ H); constructor].
    - apply (J_trans _ _ _ X); [apply J_sym, (J_conv _ _ _ _ A) |]; assumption. }
  assert (Bwd : forall X X1 c, hreds X X1 -> J Ψ Γ X X1 A -> J Ψ Γ A Code U ->
                tred Ψ Γ X1 (box c) Code -> tred Ψ Γ X (box c) Code).
  { intros X X1 c R JX HA [R' J']. split.
    - exact (hreds_trans _ _ _ R R').
    - apply (J_trans _ _ _ X1); [apply (J_conv _ _ _ _ A) |]; assumption. }
  split; intros [HA H]; split; try exact HA; destruct w as [c |]; try exact I;
    destruct HA as [[_ JA] _]; destruct H as (Hc & HM & HN); eauto 6.
Qed.

(** *** The relation at every witness

    The compact elements [C] of the paper's §2.4, with [mem u x] for
    [u ∈ x] (an ideal of compacts) and [sty u a] for [u :ₙ a]. Of them,
    the probe names [⊥], the universe's type code [U], the codes [Cd]
    and [Q c] of Part 1, and [Π(⊥,⊥)], the witness of Cor. 2.37. The
    hypotheses on them hold in the paper's model extended by the flat
    code summand: [Q c]'s ideal is [{⊥, Q c}], [CODE]'s is [{⊥, Cd}], a
    compact of [CASEQ x k] is [⊥] or one of [k c] for a [Q c ∈ x]. *)

Variable C : Type.
Variables (cbot cUc cCd cPiw : C) (cQ : cd -> C).
Variable mem : C -> D -> Prop.
Variable sty : C -> C -> Prop.

Hypothesis mem_BOT : forall u, mem u BOT -> u = cbot.
Hypothesis mem_UU : forall a, mem a UU -> a = cbot \/ a = cUc.
Hypothesis mem_UU_U : mem cUc UU.
Hypothesis mem_CODE : forall a, mem a CODE -> a = cbot \/ a = cCd.
Hypothesis mem_CODE_Cd : mem cCd CODE.
Hypothesis mem_Q : forall u c, mem u (Q c) -> u = cbot \/ u = cQ c.
Hypothesis mem_CASEQ : forall u x k, mem u (CASEQ x k) -> u = cbot \/ exists c, mem (cQ c) x /\ mem u (k c).
Hypothesis mem_PI : forall x f, mem cPiw (PI x f).
Hypothesis sty_U : sty cUc cUc.
Hypothesis sty_Cd : sty cCd cUc.
Hypothesis sty_Q : forall c, sty (cQ c) cCd.
Hypothesis sty_Piw : sty cPiw cUc.
Hypothesis cQ_not_bot : forall c, cQ c <> cbot.
Hypothesis cQ_inj : forall c c', cQ c = cQ c' -> c = c'.

(** The relation, [Γ ⊨ A ≡ A' type ∣a] and [Γ ⊨ M ≡ M' : A ∣u:a], at a
    code-variable count [Ψ]. At the old witnesses it is the paper's and
    stays abstract: the clauses below are those the probe uses ([⊥], the
    universe, and the consequence of the [Π] clause Cor. 2.37 reads), and
    the laws of §2.7 are hypotheses, which the paper proves at the old
    witnesses and [RCd_*] above prove at the new ones. The new clauses
    are [Rty_Cd] and [Rtm_Cd]. *)

Variable Rty : nat -> list tm -> tm -> tm -> C -> Prop.
Variable Rtm : nat -> list tm -> tm -> tm -> tm -> C -> C -> Prop.

Definition wQ (w : option cd) : C := match w with None => cbot | Some c => cQ c end.

Hypothesis Rty_bot : forall Ψ Γ A A', Rty Ψ Γ A A' cbot.
Hypothesis Rtm_tybot : forall Ψ Γ M M' A u, Rtm Ψ Γ M M' A u cbot.
Hypothesis Rtm_U : forall Ψ Γ M M' A u, Rtm Ψ Γ M M' A u cUc <-> tred Ψ Γ A U U /\ Rty Ψ Γ M M' u.
Hypothesis Rty_Piw : forall Ψ Γ T T', Rty Ψ Γ T T' cPiw ->
  exists A B A' B', tred Ψ Γ T (Pi A B) U /\ tred Ψ Γ T' (Pi A' B') U /\
                    J Ψ Γ A A' U /\ J Ψ (A :: Γ) B B' U.
Hypothesis Rty_Cd : forall Ψ Γ A A', Rty Ψ Γ A A' cCd <-> RCdTy Ψ Γ A A'.
Hypothesis Rtm_Cd : forall Ψ Γ M M' A w, Rtm Ψ Γ M M' A (wQ w) cCd <-> RCdTm Ψ Γ M M' A w.

Hypothesis LR_bot : forall Ψ Γ M N A a, sty a cUc -> Rty Ψ Γ A A a -> Rtm Ψ Γ M N A cbot a.
Hypothesis LR_symTy : forall Ψ Γ A B a, Rty Ψ Γ A B a -> Rty Ψ Γ B A a.
Hypothesis LR_transTy : forall Ψ Γ A B C a, Rty Ψ Γ A B a -> Rty Ψ Γ B C a -> Rty Ψ Γ A C a.
Hypothesis LR_conv : forall Ψ Γ M N A B u a, Rty Ψ Γ A B a -> Rtm Ψ Γ M N A u a -> Rtm Ψ Γ M N B u a.
Hypothesis LR_hred : forall Ψ Γ M M1 N N1 A u a,
  tred Ψ Γ M M1 A -> tred Ψ Γ N N1 A -> J Ψ Γ M N A ->
  Rtm Ψ Γ M N A u a <-> Rtm Ψ Γ M1 N1 A u a.

Lemma Rty_refl_l Ψ Γ A B a : Rty Ψ Γ A B a -> Rty Ψ Γ A A a.
Proof. intros H. exact (LR_transTy _ _ _ _ _ _ H (LR_symTy _ _ _ _ _ H)). Qed.

(** *** Validity (the statement of the paper's Thm 2.35)

    Related substitutions over [ρ] (§2.7, last display), and validity of
    a judgment: under related substitutions, every compact of the type's
    and the term's denotations relates the substituted sides. *)

Definition SubRel Ψ' Δ Ψ Γ σ σ' τ ρ : Prop :=
  TyS Ψ' Δ Ψ Γ σ σ' τ /\
  forall n A, nth_error Γ n = Some A -> forall u a,
    mem u (ρ n) -> mem a (den A (fun k => ρ (S n + k)) τ) -> sty a cUc -> sty u a ->
    Rtm Ψ' Δ (σ n) (σ' n) (sub (ren A (fun k => S n + k) (fun u => u)) σ τ) u a.

Definition VTy Ψ Γ A A' : Prop :=
  forall Ψ' Δ σ σ' τ ρ, fits Γ ρ τ -> SubRel Ψ' Δ Ψ Γ σ σ' τ ρ ->
  forall a, mem a (den A ρ τ) -> sty a cUc -> Rty Ψ' Δ (sub A σ τ) (sub A' σ' τ) a.

Definition VTm Ψ Γ M M' A : Prop :=
  forall Ψ' Δ σ σ' τ ρ, fits Γ ρ τ -> SubRel Ψ' Δ Ψ Γ σ σ' τ ρ ->
  forall a u, mem a (den A ρ τ) -> sty a cUc -> mem u (den M ρ τ) -> sty u a ->
  Rtm Ψ' Δ (sub M σ τ) (sub M' σ' τ) (sub A σ τ) u a.

(** Validity at [𝒰] gives validity as types (ToType). *)
Lemma VTm_VTy Ψ Γ M N : VTm Ψ Γ M N U -> VTy Ψ Γ M N.
Proof.
  intros H Ψ' Δ σ σ' τ ρ Hf HS a Ha Hsa.
  exact (proj2 (proj1 (Rtm_U _ _ _ _ _ _) (H Ψ' Δ σ σ' τ ρ Hf HS cUc a mem_UU_U sty_U Ha Hsa))).
Qed.

Lemma SubRel_cons Ψ' Δ Ψ Γ σ σ' τ ρ A N N' x :
  SubRel Ψ' Δ Ψ Γ σ σ' τ ρ -> J Ψ' Δ N N' (sub A σ τ) ->
  (forall u a, mem u x -> mem a (den A ρ τ) -> sty a cUc -> sty u a -> Rtm Ψ' Δ N N' (sub A σ τ) u a) ->
  SubRel Ψ' Δ Ψ (A :: Γ) (N .: σ) (N' .: σ') τ (x .: ρ).
Proof.
  intros [TS H] JN HN. split; [apply TyS_cons; assumption |].
  intros [| n] B HB u a Hu Ha Hsa Hsu; cbn in HB.
  - injection HB as <-. rewrite ren_sub. exact (HN u a Hu Ha Hsa Hsu).
  - specialize (H n B HB u a Hu Ha Hsa Hsu). rewrite ren_sub in H |- *. exact H.
Qed.

Lemma SubRel_gshift Ψ' Δ Ψ Γ σ σ' τ ρ k τ' :
  SubRel Ψ' Δ Ψ Γ σ σ' τ ρ -> (forall u, τ' (k + u) = τ u) -> (forall u, u < k -> cwf Ψ' (τ' u)) ->
  SubRel Ψ' Δ (k + Ψ) (gshift k Γ) σ σ' τ' ρ.
Proof.
  intros [TS H] Hτ Hc. split; [eapply TyS_gshift; eassumption |].
  intros n A HA u a Hu Ha Hsa Hsu. unfold gshift in HA. rewrite nth_error_map in HA.
  destruct (nth_error Γ n) as [B |] eqn:HB; cbn in HA; [| discriminate]. injection HA as <-.
  rewrite den_ren in Ha. erewrite den_ext in Ha; [| intros j; reflexivity | intros w; exact (Hτ w)].
  specialize (H n B HB u a Hu Ha Hsa Hsu).
  rewrite ren_ren, ren_sub. rewrite ren_sub in H.
  erewrite sub_ext; [exact H | intros j; reflexivity | intros w; exact (Hτ w)].
Qed.

(** The terms reducing to one [box c] relate at [Code], at every
    compact of [Q c]. *)
Lemma Rtm_code_box Ψ' Δ N N' c :
  cwf Ψ' c -> tred Ψ' Δ N (box c) Code -> tred Ψ' Δ N' (box c) Code ->
  forall u a, mem u (Q c) -> mem a CODE -> sty a cUc -> sty u a -> Rtm Ψ' Δ N N' Code u a.
Proof.
  intros Hc HN HN' u a Hu Ha _ _.
  destruct (mem_CODE _ Ha) as [-> | ->]; [apply Rtm_tybot |].
  assert (HC : RCdTy Ψ' Δ Code Code) by (split; apply tred_refl, J_Code).
  destruct (mem_Q _ _ Hu) as [-> | ->].
  - apply (proj2 (Rtm_Cd _ _ _ _ _ None)). split; [exact HC | exact I].
  - apply (proj2 (Rtm_Cd _ _ _ _ _ (Some c))). split; [exact HC | auto].
Qed.

Lemma cwf_csub Ψ Ψ' c τ : cwf Ψ c -> (forall u, u < Ψ -> cwf Ψ' (τ u)) -> cwf Ψ' (csub c τ).
Proof. intros Hc Hτ; induction c; cbn in *; intuition. Qed.

(** *** The fundamental theorem's cases for the new formers *)

Lemma V_Code Ψ Γ : VTm Ψ Γ Code Code U.
Proof.
  intros Ψ' Δ σ σ' τ ρ _ _ a u Ha _ Hu _. cbn in *.
  destruct (mem_UU _ Ha) as [-> | ->]; [apply Rtm_tybot |].
  apply Rtm_U. split; [apply tred_refl, J_U |].
  destruct (mem_CODE _ Hu) as [-> | ->]; [apply Rty_bot |].
  apply Rty_Cd. split; apply tred_refl, J_Code.
Qed.

Lemma V_box Ψ Γ c : cwf Ψ c -> VTm Ψ Γ (box c) (box c) Code.
Proof.
  intros Hc Ψ' Δ σ σ' τ ρ _ [TS _] a u Ha Hsa Hu Hsu. cbn in *.
  assert (Hc' : cwf Ψ' (csub c τ)) by exact (cwf_csub _ _ _ _ Hc (TyS_cwf _ _ _ _ _ _ _ TS)).
  apply (Rtm_code_box _ _ _ _ (csub c τ)); auto; apply tred_refl, J_box; exact Hc'.
Qed.

(** The eliminators' cases share the premises and the substitution; a
    section fixes them. [elimS]/[lbS] are the substituted eliminators,
    awaiting their scrutinee. *)

Notation elimS P bU bPi σ τ :=
  (elim (sub P (upl σ) τ) (sub bU σ τ) (sub bPi (upl (upl (upg (upg σ)))) (upc (upc τ)))).
Notation lbS P s σ τ X := (letbox (sub P (upl σ) τ) X (sub s (upg σ) (upc τ))).

Lemma J_refl_l Ψ Γ M N A : J Ψ Γ M N A -> J Ψ Γ M M A.
Proof. intros H. exact (J_trans _ _ _ _ _ _ H (J_sym _ _ _ _ _ H)). Qed.

Lemma betaPi_subst P bU bPi a b σ τ :
  sub (betaPi P bU bPi a b) σ τ =
  betaPi (sub P (upl σ) τ) (sub bU σ τ) (sub bPi (upl (upl (upg (upg σ)))) (upc (upc τ))) (csub a τ) (csub b τ).
Proof.
  rewrite betaPi_sub. unfold betaPi. rewrite sub_sub.
  apply sub_ext; [intros [| [| n]] | intros [| [| u]]]; reflexivity.
Qed.

Lemma lbRes_inst P σ c τ : sub (lbRes P) σ (c .: τ) = sub P (box c .: σ) τ.
Proof. unfold lbRes. rewrite sub_sub. apply sub_ext; [intros [| n] | intros u]; reflexivity. Qed.

Section Elims.

Variables (Ψ : nat) (Γ : list tm) (P P' : tm).
Hypothesis HP : eqj Ψ (Code :: Γ) P P' U.
Hypothesis HP' : eqj Ψ (Code :: Γ) P' P' U.
Hypothesis VP : VTm Ψ (Code :: Γ) P P' U.

Variables (Ψ' : nat) (Δ : list tm) (σ σ' : nat -> tm) (τ : nat -> cd) (ρ : nat -> D).
Hypothesis Hfit : fits Γ ρ τ.
Hypothesis HS : SubRel Ψ' Δ Ψ Γ σ σ' τ ρ.

Let TS : TyS Ψ' Δ Ψ Γ σ σ' τ := proj1 HS.
Let TS' : TyS Ψ' Δ Ψ Γ σ' σ' τ := TyS_refl_r _ _ _ _ _ _ _ TS.

(** The motive, substituted and instantiated at convertible codes. *)
Lemma JP_inst X X' : J Ψ' Δ X X' Code -> J Ψ' Δ (sub P (X .: σ) τ) (sub P' (X' .: σ') τ) U.
Proof. intros H. exact (J_subst _ _ _ _ _ _ _ _ _ _ HP (TyS_cons _ _ _ _ _ _ _ Code _ _ TS H)). Qed.

Lemma JP_up : J Ψ' (Code :: Δ) (sub P (upl σ) τ) (sub P' (upl σ') τ) U.
Proof. exact (J_subst _ _ _ _ _ _ _ _ _ _ HP (TyS_upl _ _ _ _ _ _ _ Code TS)). Qed.
Lemma JP_up' : J Ψ' (Code :: Δ) (sub P' (upl σ') τ) (sub P' (upl σ') τ) U.
Proof. exact (J_subst _ _ _ _ _ _ _ _ _ _ HP' (TyS_upl _ _ _ _ _ _ _ Code TS')). Qed.

(** The motive at a box, as a type (the [⊥] cases use it). *)
Lemma SubRel_box N' c :
  cwf Ψ' c -> tred Ψ' Δ N' (box c) Code ->
  SubRel Ψ' Δ Ψ (Code :: Γ) (box c .: σ) (N' .: σ') τ (Q c .: ρ).
Proof.
  intros Hc HN'. apply SubRel_cons; [exact HS | apply J_sym, HN' |].
  intros u a Hu Ha Hsa Hsu. apply (Rtm_code_box _ _ _ _ c); auto. apply tred_refl, J_box, Hc.
Qed.

Lemma Rty_P_box c a :
  cwf Ψ' c -> mem a (den P (Q c .: ρ) τ) -> sty a cUc -> Rty Ψ' Δ (sub P (box c .: σ) τ) (sub P (box c .: σ) τ) a.
Proof.
  intros Hc Ha Hsa. apply (Rty_refl_l _ _ _ (sub P' (box c .: σ') τ)).
  apply (VTm_VTy _ _ _ _ VP _ _ _ _ _ _ (fits_cons Γ Code ρ τ (Q c) Hfit (TY_Q c))); [| exact Ha | exact Hsa].
  apply SubRel_box; [exact Hc |]. apply tred_refl, J_box, Hc.
Qed.

(** The scrutinee step, shared by [elim] and [letbox]: once the
    scrutinee's denotation is [Q c], its validity at [Q c : Cd] makes
    both sides reduce to [box c], and the case at [box c] carries over
    by head expansion and conversion along the motive. *)
Variables (t t' : tm).
Hypothesis HT : eqj Ψ Γ t t' Code.
Hypothesis VT : VTm Ψ Γ t t' Code.

Lemma scrut_case (F F' : tm -> tm) (k : cd -> D) :
  (forall X X', J Ψ' Δ X X' Code -> J Ψ' Δ (F X) (F' X') (sub P (X .: σ) τ)) ->
  (forall N c, tred Ψ' Δ N (box c) Code -> tred Ψ' Δ (F N) (F (box c)) (sub P (N .: σ) τ)) ->
  (forall N N' c, J Ψ' Δ N N' Code -> tred Ψ' Δ N' (box c) Code ->
     tred Ψ' Δ (F' N') (F' (box c)) (sub P (N .: σ) τ)) ->
  (forall c, cwf Ψ' c -> forall u a, mem a (den P (Q c .: ρ) τ) -> sty a cUc -> mem u (k c) -> sty u a ->
     Rtm Ψ' Δ (F (box c)) (F' (box c)) (sub P (box c .: σ) τ) u a) ->
  forall u a, mem a (den P (den t ρ τ .: ρ) τ) -> sty a cUc -> mem u (CASEQ (den t ρ τ) k) -> sty u a ->
  Rtm Ψ' Δ (F (sub t σ τ)) (F' (sub t' σ' τ)) (sub P (sub t σ τ .: σ) τ) u a.
Proof.
  intros JF RF RF' Hbox u a Ha Hsa Hu Hsu.
  assert (JT : J Ψ' Δ (sub t σ τ) (sub t' σ' τ) Code) by exact (J_subst _ _ _ _ _ _ _ _ _ _ HT TS).
  destruct (soundness _ _ _ _ _ HT ρ τ Hfit) as [_ TT].
  assert (St : SubRel Ψ' Δ Ψ (Code :: Γ) (sub t σ τ .: σ) (sub t' σ' τ .: σ') τ (den t ρ τ .: ρ)).
  { apply SubRel_cons; [exact HS | exact JT |]. intros u' a' Hu' Ha' Hsa' Hsu'.
    exact (VT _ _ _ _ _ _ Hfit HS a' u' Ha' Hsa' Hu' Hsu'). }
  assert (Ft : fits (Code :: Γ) (den t ρ τ .: ρ) τ) by exact (fits_cons _ _ _ _ _ Hfit TT).
  (* both sides' motives, at the scrutinees *)
  assert (Rt : Rty Ψ' Δ (sub P (sub t σ τ .: σ) τ) (sub P' (sub t' σ' τ .: σ') τ) a)
    by exact (VTm_VTy _ _ _ _ VP _ _ _ _ _ _ Ft St a Ha Hsa).
  destruct (mem_CASEQ _ _ _ Hu) as [-> | [c [Hc Hu']]].
  { apply LR_bot; [exact Hsa |]. exact (Rty_refl_l _ _ _ _ _ Rt). }
  assert (Et : den t ρ τ = Q c).
  { destruct (CODE_inv _ TT) as [E | [c0 E]]; rewrite E in Hc.
    - exfalso. exact (cQ_not_bot _ (mem_BOT _ Hc)).
    - destruct (mem_Q _ _ Hc) as [E' | E']; [exfalso; exact (cQ_not_bot _ E') |].
      rewrite E, (cQ_inj _ _ E'). reflexivity. }
  rewrite Et in Ha, St, Ft.
  assert (Rc := VT _ _ _ _ _ _ Hfit HS cCd (cQ c) mem_CODE_Cd sty_Cd Hc (sty_Q c)).
  apply (proj1 (Rtm_Cd _ _ _ _ _ (Some c))) in Rc. destruct Rc as [_ (Hcw & Rl & Rr)].
  assert (Rb : Rty Ψ' Δ (sub P (box c .: σ) τ) (sub P' (sub t' σ' τ .: σ') τ) a)
    by exact (VTm_VTy _ _ _ _ VP _ _ _ _ _ _ Ft (SubRel_box _ _ Hcw Rr) a Ha Hsa).
  apply (proj2 (LR_hred _ _ _ _ _ _ _ u a (RF _ _ Rl) (RF' _ _ _ JT Rr) (JF _ _ JT))).
  apply (LR_conv _ _ _ _ (sub P (box c .: σ) τ)); [exact (LR_transTy _ _ _ _ _ _ Rb (LR_symTy _ _ _ _ _ Rt)) |].
  exact (Hbox c Hcw u a Ha Hsa Hu' Hsu).
Qed.

(** **** [elim] *)

Variables (bU bU' bPi bPi' : tm).
Hypothesis HU : eqj Ψ Γ bU bU' (inst P (box cU)).
Hypothesis HU' : eqj Ψ Γ bU' bU' (inst P' (box cU)).
Hypothesis HPi : eqj (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi' (brRes P).
Hypothesis HPi' : eqj (S (S Ψ)) (brT P' :: brS P' :: gshift 2 Γ) bPi' bPi' (brRes P').
Hypothesis VU : VTm Ψ Γ bU bU' (inst P (box cU)).
Hypothesis VPi : VTm (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi' (brRes P).

Lemma JU : J Ψ' Δ (sub bU σ τ) (sub bU' σ' τ) (inst (sub P (upl σ) τ) (box cU)).
Proof.
  rewrite inst_upl. pose proof (J_subst _ _ _ _ _ _ _ _ _ _ HU TS) as H. rewrite sub_inst in H. exact H.
Qed.
Lemma JU' : J Ψ' Δ (sub bU' σ' τ) (sub bU' σ' τ) (inst (sub P' (upl σ') τ) (box cU)).
Proof.
  rewrite inst_upl. pose proof (J_subst _ _ _ _ _ _ _ _ _ _ HU' TS') as H. rewrite sub_inst in H. exact H.
Qed.
Lemma JPi : J (S (S Ψ')) (brT (sub P (upl σ) τ) :: brS (sub P (upl σ) τ) :: gshift 2 Δ)
  (sub bPi (upl (upl (upg (upg σ)))) (upc (upc τ))) (sub bPi' (upl (upl (upg (upg σ')))) (upc (upc τ)))
  (brRes (sub P (upl σ) τ)).
Proof. rewrite <- brRes_up. exact (J_subst _ _ _ _ _ _ _ _ _ _ HPi (TyS_br _ _ _ _ _ _ _ P TS)). Qed.
Lemma JPi' : J (S (S Ψ')) (brT (sub P' (upl σ') τ) :: brS (sub P' (upl σ') τ) :: gshift 2 Δ)
  (sub bPi' (upl (upl (upg (upg σ')))) (upc (upc τ))) (sub bPi' (upl (upl (upg (upg σ')))) (upc (upc τ)))
  (brRes (sub P' (upl σ') τ)).
Proof. rewrite <- brRes_up. exact (J_subst _ _ _ _ _ _ _ _ _ _ HPi' (TyS_br _ _ _ _ _ _ _ P' TS')). Qed.

Lemma JE X X' : J Ψ' Δ X X' Code ->
  J Ψ' Δ (elimS P bU bPi σ τ X) (elimS P' bU' bPi' σ' τ X') (sub P (X .: σ) τ).
Proof. intros H. rewrite <- inst_upl. apply J_elim; auto using JP_up, JU, JPi. Qed.
Lemma JE_l X X' : J Ψ' Δ X X' Code ->
  J Ψ' Δ (elimS P bU bPi σ τ X) (elimS P bU bPi σ τ X') (sub P (X .: σ) τ).
Proof.
  intros H. rewrite <- inst_upl.
  apply J_elim; [exact (J_refl_l _ _ _ _ _ JP_up) | exact (J_refl_l _ _ _ _ _ JU) | exact (J_refl_l _ _ _ _ _ JPi) | exact H].
Qed.
Lemma JE_r X X' Y : J Ψ' Δ X X' Code -> J Ψ' Δ Y X Code ->
  J Ψ' Δ (elimS P' bU' bPi' σ' τ X) (elimS P' bU' bPi' σ' τ X') (sub P (Y .: σ) τ).
Proof.
  intros H HY. apply (J_conv _ _ _ _ (sub P' (X .: σ') τ)); [| apply J_sym, JP_inst, HY].
  rewrite <- inst_upl. apply J_elim; auto using JP_up', JU', JPi'.
Qed.

Lemma tredE N c : tred Ψ' Δ N (box c) Code ->
  tred Ψ' Δ (elimS P bU bPi σ τ N) (elimS P bU bPi σ τ (box c)) (sub P (N .: σ) τ).
Proof. intros [R H]. split; [apply hreds_elim, R | apply JE_l, H]. Qed.
Lemma tredE' N N' c : J Ψ' Δ N N' Code -> tred Ψ' Δ N' (box c) Code ->
  tred Ψ' Δ (elimS P' bU' bPi' σ' τ N') (elimS P' bU' bPi' σ' τ (box c)) (sub P (N .: σ) τ).
Proof. intros HN [R H]. split; [apply hreds_elim, R | apply (JE_r _ _ _ H HN)]. Qed.

Lemma tredE_U : tred Ψ' Δ (elimS P bU bPi σ τ (box cU)) (sub bU σ τ) (sub P (box cU .: σ) τ).
Proof.
  split; [apply hreds_one, hr_elimU |]. rewrite <- inst_upl.
  apply J_elimU; [exact (J_refl_l _ _ _ _ _ JP_up) | exact (J_refl_l _ _ _ _ _ JU) | exact (J_refl_l _ _ _ _ _ JPi)].
Qed.
Lemma tredE_U' : tred Ψ' Δ (elimS P' bU' bPi' σ' τ (box cU)) (sub bU' σ' τ) (sub P (box cU .: σ) τ).
Proof.
  split; [apply hreds_one, hr_elimU |].
  apply (J_conv _ _ _ _ (sub P' (box cU .: σ') τ)); [| apply J_sym, JP_inst, J_box; exact I].
  rewrite <- inst_upl. apply J_elimU; auto using JP_up', JU', JPi'.
Qed.

Lemma tredE_Pi a b : cwf Ψ' a -> cwf Ψ' b ->
  tred Ψ' Δ (elimS P bU bPi σ τ (box (cPi a b)))
    (betaPi (sub P (upl σ) τ) (sub bU σ τ) (sub bPi (upl (upl (upg (upg σ)))) (upc (upc τ))) a b)
    (sub P (box (cPi a b) .: σ) τ).
Proof.
  intros Ha Hb. split; [apply hreds_one, hr_elimPi |]. rewrite <- inst_upl.
  apply J_elimPi; [exact (J_refl_l _ _ _ _ _ JP_up) | exact (J_refl_l _ _ _ _ _ JU) | exact (J_refl_l _ _ _ _ _ JPi) | exact Ha | exact Hb].
Qed.
Lemma tredE_Pi' a b : cwf Ψ' a -> cwf Ψ' b ->
  tred Ψ' Δ (elimS P' bU' bPi' σ' τ (box (cPi a b)))
    (betaPi (sub P' (upl σ') τ) (sub bU' σ' τ) (sub bPi' (upl (upl (upg (upg σ')))) (upc (upc τ))) a b)
    (sub P (box (cPi a b) .: σ) τ).
Proof.
  intros Ha Hb. split; [apply hreds_one, hr_elimPi |].
  apply (J_conv _ _ _ _ (sub P' (box (cPi a b) .: σ') τ)); [| apply J_sym, JP_inst, J_box; split; assumption].
  rewrite <- inst_upl. apply J_elimPi; auto using JP_up', JU', JPi'.
Qed.

(** The recursor at [box c], by induction on the code [c]: the [Π]
    step is the branch's validity at the subcodes and the recursive
    calls, which relate at the subcodes' motives by the induction
    hypotheses; a code variable (a stuck recursor) denotes [⊥]. *)
Lemma elim_box c : cwf Ψ' c -> forall u a, mem a (den P (Q c .: ρ) τ) -> sty a cUc ->
  mem u (recR (den bU) (den bPi) ρ τ c) -> sty u a ->
  Rtm Ψ' Δ (elimS P bU bPi σ τ (box c)) (elimS P' bU' bPi' σ' τ (box c)) (sub P (box c .: σ) τ) u a.
Proof.
  induction c as [| a0 IHa b0 IHb | w]; intros Hc u a Ha Hsa Hu Hsu; cbn in Hu.
  - apply (proj2 (LR_hred _ _ _ _ _ _ _ u a tredE_U tredE_U' (JE _ _ (J_box Ψ' Δ cU I)))).
    assert (Ha' : mem a (den (inst P (box cU)) ρ τ)) by (rewrite den_inst; exact Ha).
    pose proof (VU _ _ _ _ _ _ Hfit HS a u Ha' Hsa Hu Hsu) as R. rewrite sub_inst in R. exact R.
  - destruct Hc as [Hca Hcb].
    set (Ea := elimS P bU bPi σ τ (box a0)). set (Eb := elimS P bU bPi σ τ (box b0)).
    set (Ea' := elimS P' bU' bPi' σ' τ (box a0)). set (Eb' := elimS P' bU' bPi' σ' τ (box b0)).
    set (ra := recR (den bU) (den bPi) ρ τ a0). set (rb := recR (den bU) (den bPi) ρ τ b0).
    pose proof (fun c => proj2 (recR_sound P bU bU' bPi bPi' Γ ρ τ Hfit (soundness _ _ _ _ _ HU ρ τ Hfit)
                (soundness _ _ _ _ _ HPi) c)) as TR.
    assert (Fb : fits (brT P :: brS P :: gshift 2 Γ) (rb .: ra .: ρ) (b0 .: a0 .: τ)).
    { apply fits_cons; [apply fits_cons |].
      - apply (fits_gshift 2 Γ ρ τ). exact Hfit. intros w; reflexivity.
      - rewrite den_brS. exact (TR a0).
      - rewrite den_brT. exact (TR b0). }
    assert (Sb : SubRel Ψ' Δ (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) (Eb .: Ea .: σ) (Eb' .: Ea' .: σ')
                   (b0 .: a0 .: τ) (rb .: ra .: ρ)).
    { apply SubRel_cons; [apply SubRel_cons | |].
      - apply (SubRel_gshift _ _ _ _ _ _ _ _ 2 (b0 .: a0 .: τ) HS); [intros w; reflexivity |].
        intros [| [| w]] Hw; cbn; [exact Hcb | exact Hca | lia].
      - rewrite brS_inst. apply JE, J_box, Hca.
      - intros u' a' Hu' Ha' Hsa' Hsu'. rewrite den_brS in Ha'. rewrite brS_inst. exact (IHa Hca u' a' Ha' Hsa' Hu' Hsu').
      - rewrite brT_inst. apply JE, J_box, Hcb.
      - intros u' a' Hu' Ha' Hsa' Hsu'. rewrite den_brT in Ha'. rewrite brT_inst. exact (IHb Hcb u' a' Ha' Hsa' Hu' Hsu'). }
    apply (proj2 (LR_hred _ _ _ _ _ _ _ u a (tredE_Pi _ _ Hca Hcb) (tredE_Pi' _ _ Hca Hcb)
                    (JE _ _ (J_box Ψ' Δ (cPi a0 b0) (conj Hca Hcb))))).
    rewrite !betaPi_sub.
    assert (Ha' : mem a (den (brRes P) (rb .: ra .: ρ) (b0 .: a0 .: τ))) by (rewrite den_brRes; exact Ha).
    pose proof (VPi _ _ _ _ _ _ Fb Sb a u Ha' Hsa Hu Hsu) as R. rewrite brRes_inst in R. exact R.
  - rewrite (mem_BOT _ Hu). apply LR_bot; [exact Hsa |]. exact (Rty_P_box _ _ Hc Ha Hsa).
Qed.

Lemma elim_case u a :
  mem a (den P (den t ρ τ .: ρ) τ) -> sty a cUc -> mem u (CASEQ (den t ρ τ) (recR (den bU) (den bPi) ρ τ)) ->
  sty u a ->
  Rtm Ψ' Δ (elimS P bU bPi σ τ (sub t σ τ)) (elimS P' bU' bPi' σ' τ (sub t' σ' τ)) (sub P (sub t σ τ .: σ) τ) u a.
Proof.
  apply scrut_case; [exact JE | exact tredE | exact tredE' |]. exact elim_box.
Qed.

(** [elim]'s two β-rules: the left side reduces, the right side is
    the reduct already. *)
Lemma elimU_case u a : mem a (den P (Q cU .: ρ) τ) -> sty a cUc ->
  mem u (recR (den bU) (den bPi) ρ τ cU) -> sty u a ->
  Rtm Ψ' Δ (elimS P bU bPi σ τ (box cU)) (sub bU' σ' τ) (sub P (box cU .: σ) τ) u a.
Proof.
  intros Ha Hsa Hu Hsu. assert (Jc : J Ψ' Δ (box cU) (box cU) Code) by exact (J_box Ψ' Δ cU I).
  apply (proj1 (LR_hred _ _ _ _ _ _ _ u a (tred_refl _ _ _ _ (JE_l _ _ Jc)) tredE_U' (JE _ _ Jc))).
  exact (elim_box cU I u a Ha Hsa Hu Hsu).
Qed.

Lemma elimPi_case a0 b0 u a : cwf Ψ' a0 -> cwf Ψ' b0 ->
  mem a (den P (Q (cPi a0 b0) .: ρ) τ) -> sty a cUc ->
  mem u (recR (den bU) (den bPi) ρ τ (cPi a0 b0)) -> sty u a ->
  Rtm Ψ' Δ (elimS P bU bPi σ τ (box (cPi a0 b0)))
    (betaPi (sub P' (upl σ') τ) (sub bU' σ' τ) (sub bPi' (upl (upl (upg (upg σ')))) (upc (upc τ))) a0 b0)
    (sub P (box (cPi a0 b0) .: σ) τ) u a.
Proof.
  intros Hca Hcb Ha Hsa Hu Hsu.
  assert (Jc : J Ψ' Δ (box (cPi a0 b0)) (box (cPi a0 b0)) Code) by exact (J_box Ψ' Δ (cPi a0 b0) (conj Hca Hcb)).
  apply (proj1 (LR_hred _ _ _ _ _ _ _ u a (tred_refl _ _ _ _ (JE_l _ _ Jc)) (tredE_Pi' _ _ Hca Hcb) (JE _ _ Jc))).
  exact (elim_box (cPi a0 b0) (conj Hca Hcb) u a Ha Hsa Hu Hsu).
Qed.

(** **** [letbox]: no recursion, the scrutinee step and the body at the
    spliced code. *)

Variables (s s' : tm).
Hypothesis Hs : eqj (S Ψ) (gshift 1 Γ) s s' (lbRes P).
Hypothesis Hs' : eqj (S Ψ) (gshift 1 Γ) s' s' (lbRes P').
Hypothesis Vs : VTm (S Ψ) (gshift 1 Γ) s s' (lbRes P).

Lemma Js : J (S Ψ') (gshift 1 Δ) (sub s (upg σ) (upc τ)) (sub s' (upg σ') (upc τ)) (lbRes (sub P (upl σ) τ)).
Proof. rewrite <- lbRes_up. exact (J_subst _ _ _ _ _ _ _ _ _ _ Hs (TyS_upg _ _ _ _ _ _ _ TS)). Qed.
Lemma Js' : J (S Ψ') (gshift 1 Δ) (sub s' (upg σ') (upc τ)) (sub s' (upg σ') (upc τ)) (lbRes (sub P' (upl σ') τ)).
Proof. rewrite <- lbRes_up. exact (J_subst _ _ _ _ _ _ _ _ _ _ Hs' (TyS_upg _ _ _ _ _ _ _ TS')). Qed.

Lemma JL X X' : J Ψ' Δ X X' Code -> J Ψ' Δ (lbS P s σ τ X) (lbS P' s' σ' τ X') (sub P (X .: σ) τ).
Proof. intros H. rewrite <- inst_upl. apply J_letbox; [exact JP_up | exact H | exact Js]. Qed.

Lemma tredL N c : tred Ψ' Δ N (box c) Code -> tred Ψ' Δ (lbS P s σ τ N) (lbS P s σ τ (box c)) (sub P (N .: σ) τ).
Proof.
  intros [R H]. split; [apply hreds_letbox, R |]. rewrite <- inst_upl.
  apply J_letbox; [exact (J_refl_l _ _ _ _ _ JP_up) | exact H | exact (J_refl_l _ _ _ _ _ Js)].
Qed.
Lemma tredL' N N' c : J Ψ' Δ N N' Code -> tred Ψ' Δ N' (box c) Code ->
  tred Ψ' Δ (lbS P' s' σ' τ N') (lbS P' s' σ' τ (box c)) (sub P (N .: σ) τ).
Proof.
  intros HN [R H]. split; [apply hreds_letbox, R |].
  apply (J_conv _ _ _ _ (sub P' (N' .: σ') τ)); [| apply J_sym, JP_inst, HN].
  rewrite <- inst_upl. apply J_letbox; [exact JP_up' | exact H | exact Js'].
Qed.

Lemma tredL_b c : cwf Ψ' c -> tred Ψ' Δ (lbS P s σ τ (box c)) (sub s σ (c .: τ)) (sub P (box c .: σ) τ).
Proof.
  intros Hc. split; [rewrite <- letbox_beta_sub; apply hreds_one, hr_lbb |].
  rewrite <- letbox_beta_sub, <- inst_upl.
  apply J_letboxb; [exact (J_refl_l _ _ _ _ _ JP_up) | exact Hc | exact (J_refl_l _ _ _ _ _ Js)].
Qed.
Lemma tredL_b' c : cwf Ψ' c -> tred Ψ' Δ (lbS P' s' σ' τ (box c)) (sub s' σ' (c .: τ)) (sub P (box c .: σ) τ).
Proof.
  intros Hc. split; [rewrite <- letbox_beta_sub; apply hreds_one, hr_lbb |].
  apply (J_conv _ _ _ _ (sub P' (box c .: σ') τ)); [| apply J_sym, JP_inst, J_box, Hc].
  rewrite <- letbox_beta_sub, <- inst_upl. apply J_letboxb; [exact JP_up' | exact Hc | exact Js'].
Qed.

(** The body, at the spliced code: [s]'s validity under the code
    substitution extended by [c]. *)
Lemma lb_body c : cwf Ψ' c -> forall u a, mem a (den P (Q c .: ρ) τ) -> sty a cUc ->
  mem u (den s ρ (c .: τ)) -> sty u a ->
  Rtm Ψ' Δ (sub s σ (c .: τ)) (sub s' σ' (c .: τ)) (sub P (box c .: σ) τ) u a.
Proof.
  intros Hc u a Ha Hsa Hu Hsu.
  assert (S1 : SubRel Ψ' Δ (S Ψ) (gshift 1 Γ) σ σ' (c .: τ) ρ).
  { apply (SubRel_gshift _ _ _ _ _ _ _ _ 1 (c .: τ) HS); [intros w; reflexivity |].
    intros [| w] Hw; [exact Hc | lia]. }
  assert (Ha' : mem a (den (lbRes P) ρ (c .: τ))) by (rewrite den_lbRes; exact Ha).
  pose proof (Vs _ _ _ _ _ _ (fits_gshift 1 Γ ρ τ (c .: τ) Hfit (fun w => eq_refl)) S1 a u Ha' Hsa Hu Hsu) as R.
  rewrite lbRes_inst in R. exact R.
Qed.

Lemma lb_box c : cwf Ψ' c -> forall u a, mem a (den P (Q c .: ρ) τ) -> sty a cUc ->
  mem u (den s ρ (c .: τ)) -> sty u a ->
  Rtm Ψ' Δ (lbS P s σ τ (box c)) (lbS P' s' σ' τ (box c)) (sub P (box c .: σ) τ) u a.
Proof.
  intros Hc u a Ha Hsa Hu Hsu.
  apply (proj2 (LR_hred _ _ _ _ _ _ _ u a (tredL_b _ Hc) (tredL_b' _ Hc) (JL _ _ (J_box _ _ _ Hc)))).
  exact (lb_body c Hc u a Ha Hsa Hu Hsu).
Qed.

Lemma letbox_case u a :
  mem a (den P (den t ρ τ .: ρ) τ) -> sty a cUc -> mem u (CASEQ (den t ρ τ) (fun c => den s ρ (c .: τ))) ->
  sty u a ->
  Rtm Ψ' Δ (lbS P s σ τ (sub t σ τ)) (lbS P' s' σ' τ (sub t' σ' τ)) (sub P (sub t σ τ .: σ) τ) u a.
Proof.
  apply (scrut_case (fun X => lbS P s σ τ X) (fun X => lbS P' s' σ' τ X)); [exact JL | exact tredL | exact tredL' |].
  exact lb_box.
Qed.

Lemma letboxb_case c u a : cwf Ψ' c -> mem a (den P (Q c .: ρ) τ) -> sty a cUc ->
  mem u (den s ρ (c .: τ)) -> sty u a ->
  Rtm Ψ' Δ (lbS P s σ τ (box c)) (sub s' σ' (c .: τ)) (sub P (box c .: σ) τ) u a.
Proof.
  intros Hc Ha Hsa Hu Hsu. assert (Jc : J Ψ' Δ (box c) (box c) Code) by exact (J_box _ _ _ Hc).
  assert (Jl : J Ψ' Δ (lbS P s σ τ (box c)) (lbS P s σ τ (box c)) (sub P (box c .: σ) τ))
    by exact (J_refl_l _ _ _ _ _ (JL _ _ Jc)).
  apply (proj1 (LR_hred _ _ _ _ _ _ _ u a (tred_refl _ _ _ _ Jl) (tredL_b' _ Hc) (JL _ _ Jc))).
  exact (lb_box c Hc u a Ha Hsa Hu Hsu).
Qed.

End Elims.

Lemma V_elim Ψ Γ P P' bU bU' bPi bPi' t t' :
  eqj Ψ (Code :: Γ) P P' U -> eqj Ψ Γ bU bU' (inst P (box cU)) ->
  eqj (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi' (brRes P) -> eqj Ψ Γ t t' Code ->
  eqj Ψ (Code :: Γ) P' P' U -> eqj Ψ Γ bU' bU' (inst P' (box cU)) ->
  eqj (S (S Ψ)) (brT P' :: brS P' :: gshift 2 Γ) bPi' bPi' (brRes P') ->
  VTm Ψ (Code :: Γ) P P' U -> VTm Ψ Γ bU bU' (inst P (box cU)) ->
  VTm (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi' (brRes P) -> VTm Ψ Γ t t' Code ->
  VTm Ψ Γ (elim P bU bPi t) (elim P' bU' bPi' t') (inst P t).
Proof.
  intros HP HU HPi HT HP' HU' HPi' VP VU VPi VT Ψ' Δ σ σ' τ ρ Hfit HS a u Ha Hsa Hu Hsu.
  rewrite sub_inst. rewrite den_inst in Ha.
  exact (elim_case Ψ Γ P P' HP HP' VP Ψ' Δ σ σ' τ ρ Hfit HS t t' HT VT bU bU' bPi bPi' HU HU' HPi HPi' VU VPi
           u a Ha Hsa Hu Hsu).
Qed.

Lemma V_elimU Ψ Γ P bU bPi :
  eqj Ψ (Code :: Γ) P P U -> eqj Ψ Γ bU bU (inst P (box cU)) ->
  eqj (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi (brRes P) ->
  VTm Ψ (Code :: Γ) P P U -> VTm Ψ Γ bU bU (inst P (box cU)) ->
  VTm (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi (brRes P) ->
  VTm Ψ Γ (elim P bU bPi (box cU)) bU (inst P (box cU)).
Proof.
  intros HP HU HPi VP VU VPi Ψ' Δ σ σ' τ ρ Hfit HS a u Ha Hsa Hu Hsu.
  rewrite sub_inst. rewrite den_inst in Ha. cbn [den csub] in Ha, Hu. rewrite CASEQ_Q in Hu.
  exact (elimU_case Ψ Γ P P HP HP VP Ψ' Δ σ σ' τ ρ Hfit HS bU bU bPi bPi HU HU HPi HPi VU VPi u a Ha Hsa Hu Hsu).
Qed.

Lemma V_elimPi Ψ Γ P bU bPi a0 b0 :
  eqj Ψ (Code :: Γ) P P U -> eqj Ψ Γ bU bU (inst P (box cU)) ->
  eqj (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi (brRes P) -> cwf Ψ a0 -> cwf Ψ b0 ->
  VTm Ψ (Code :: Γ) P P U -> VTm Ψ Γ bU bU (inst P (box cU)) ->
  VTm (S (S Ψ)) (brT P :: brS P :: gshift 2 Γ) bPi bPi (brRes P) ->
  VTm Ψ Γ (elim P bU bPi (box (cPi a0 b0))) (betaPi P bU bPi a0 b0) (inst P (box (cPi a0 b0))).
Proof.
  intros HP HU HPi Ha0 Hb0 VP VU VPi Ψ' Δ σ σ' τ ρ Hfit HS a u Ha Hsa Hu Hsu.
  rewrite sub_inst, betaPi_subst. rewrite den_inst in Ha. cbn [den csub] in Ha, Hu. rewrite CASEQ_Q in Hu.
  assert (Hτ := TyS_cwf _ _ _ _ _ _ _ (proj1 HS)).
  exact (elimPi_case Ψ Γ P P HP HP VP Ψ' Δ σ σ' τ ρ Hfit HS bU bU bPi bPi HU HU HPi HPi VU VPi
           (csub a0 τ) (csub b0 τ) u a (cwf_csub _ _ _ _ Ha0 Hτ) (cwf_csub _ _ _ _ Hb0 Hτ) Ha Hsa Hu Hsu).
Qed.

Lemma V_letbox Ψ Γ P P' t t' s s' :
  eqj Ψ (Code :: Γ) P P' U -> eqj Ψ Γ t t' Code -> eqj (S Ψ) (gshift 1 Γ) s s' (lbRes P) ->
  eqj Ψ (Code :: Γ) P' P' U -> eqj (S Ψ) (gshift 1 Γ) s' s' (lbRes P') ->
  VTm Ψ (Code :: Γ) P P' U -> VTm Ψ Γ t t' Code -> VTm (S Ψ) (gshift 1 Γ) s s' (lbRes P) ->
  VTm Ψ Γ (letbox P t s) (letbox P' t' s') (inst P t).
Proof.
  intros HP HT Hs HP' Hs' VP VT Vs Ψ' Δ σ σ' τ ρ Hfit HS a u Ha Hsa Hu Hsu.
  rewrite sub_inst. rewrite den_inst in Ha.
  exact (letbox_case Ψ Γ P P' HP HP' VP Ψ' Δ σ σ' τ ρ Hfit HS t t' HT VT s s' Hs Hs' Vs u a Ha Hsa Hu Hsu).
Qed.

Lemma V_letboxb Ψ Γ P c s :
  eqj Ψ (Code :: Γ) P P U -> cwf Ψ c -> eqj (S Ψ) (gshift 1 Γ) s s (lbRes P) ->
  VTm Ψ (Code :: Γ) P P U -> VTm (S Ψ) (gshift 1 Γ) s s (lbRes P) ->
  VTm Ψ Γ (letbox P (box c) s) (sub s var (c .: gid)) (inst P (box c)).
Proof.
  intros HP Hc Hs VP Vs Ψ' Δ σ σ' τ ρ Hfit HS a u Ha Hsa Hu Hsu.
  rewrite sub_inst, sub_gsingle. rewrite den_inst in Ha. cbn [den] in Ha, Hu. rewrite CASEQ_Q in Hu.
  exact (letboxb_case Ψ Γ P P HP HP Ψ' Δ σ σ' τ ρ Hfit HS s s Hs Hs Vs (csub c τ) u a
           (cwf_csub _ _ _ _ Hc (TyS_cwf _ _ _ _ _ _ _ (proj1 HS))) Ha Hsa Hu Hsu).
Qed.

(** *** Adequacy and Π-injectivity

    The fundamental theorem (the paper's Thm 2.35) by induction on the
    derivation. Its cases for MLTTη's rules are the paper's (§2.9), as
    hypotheses: they use the clauses at the old witnesses and the §2.7
    laws, which hold at the new witnesses ([RCd_*]). The cases for the
    new rules are the lemmas above. *)

Hypothesis V_var : forall Ψ Γ n A, nth_error Γ n = Some A ->
  VTm Ψ Γ (var n) (var n) (ren A (fun k => S n + k) (fun u => u)).
Hypothesis V_sym : forall Ψ Γ M N A, eqj Ψ Γ M N A -> VTm Ψ Γ M N A -> VTm Ψ Γ N M A.
Hypothesis V_trans : forall Ψ Γ M N O A, eqj Ψ Γ M N A -> eqj Ψ Γ N O A ->
  VTm Ψ Γ M N A -> VTm Ψ Γ N O A -> VTm Ψ Γ M O A.
Hypothesis V_conv : forall Ψ Γ M N A B, eqj Ψ Γ M N A -> eqj Ψ Γ A B U ->
  VTm Ψ Γ M N A -> VTm Ψ Γ A B U -> VTm Ψ Γ M N B.
Hypothesis V_U : forall Ψ Γ, VTm Ψ Γ U U U.
Hypothesis V_Pi : forall Ψ Γ A A' B B', eqj Ψ Γ A A' U -> eqj Ψ (A :: Γ) B B' U ->
  VTm Ψ Γ A A' U -> VTm Ψ (A :: Γ) B B' U -> VTm Ψ Γ (Pi A B) (Pi A' B') U.
Hypothesis V_lam : forall Ψ Γ A A' B M M', eqj Ψ Γ A A' U -> eqj Ψ (A :: Γ) M M' B ->
  VTm Ψ Γ A A' U -> VTm Ψ (A :: Γ) M M' B -> VTm Ψ Γ (lam A M) (lam A' M') (Pi A B).
Hypothesis V_app : forall Ψ Γ A B M M' N N', eqj Ψ Γ M M' (Pi A B) -> eqj Ψ Γ N N' A ->
  VTm Ψ Γ M M' (Pi A B) -> VTm Ψ Γ N N' A -> VTm Ψ Γ (app M N) (app M' N') (inst B N).
Hypothesis V_beta : forall Ψ Γ A B M N, eqj Ψ Γ A A U -> eqj Ψ (A :: Γ) M M B -> eqj Ψ Γ N N A ->
  VTm Ψ Γ A A U -> VTm Ψ (A :: Γ) M M B -> VTm Ψ Γ N N A ->
  VTm Ψ Γ (app (lam A M) N) (inst M N) (inst B N).
Hypothesis V_eta : forall Ψ Γ A B M N, eqj Ψ Γ A A U -> eqj Ψ Γ M M (Pi A B) -> eqj Ψ Γ N N (Pi A B) ->
  eqj Ψ (A :: Γ) (app (ren M S (fun u => u)) (var 0)) (app (ren N S (fun u => u)) (var 0)) B ->
  VTm Ψ Γ A A U -> VTm Ψ Γ M M (Pi A B) -> VTm Ψ Γ N N (Pi A B) ->
  VTm Ψ (A :: Γ) (app (ren M S (fun u => u)) (var 0)) (app (ren N S (fun u => u)) (var 0)) B ->
  VTm Ψ Γ M N (Pi A B).

Theorem adequacy Ψ Γ M N A : eqj Ψ Γ M N A -> VTm Ψ Γ M N A.
Proof.
  induction 1.
  - apply V_var; assumption.
  - eapply V_sym; eassumption.
  - eapply V_trans; eassumption.
  - eapply V_conv; eassumption.
  - apply V_U.
  - apply V_Pi; assumption.
  - apply V_lam; assumption.
  - eapply V_app; eassumption.
  - apply V_beta; assumption.
  - apply V_eta; assumption.
  - apply V_Code.
  - apply V_box; assumption.
  - apply V_elim; assumption.
  - apply V_elimU; assumption.
  - apply V_elimPi; assumption.
  - apply V_letbox; assumption.
  - apply V_letboxb; assumption.
Qed.

(** Cor. 2.37, as in the paper: the fundamental theorem at [Π(⊥,⊥)]
    and the [Π] clause. The new clauses do not enter. The premise is the
    paper's identity substitution related over [⊥] (Thm 2.36), which
    asks the context's types to be valid; in the empty context it holds
    outright ([pi_injectivity_closed]). *)
Theorem pi_injectivity Ψ Γ A B A' B' :
  eqj Ψ Γ (Pi A B) (Pi A' B') U -> SubRel Ψ Γ Ψ Γ var var gid (fun _ => BOT) ->
  J Ψ Γ A A' U /\ J Ψ (A :: Γ) B B' U.
Proof.
  intros H HS.
  pose proof (VTm_VTy _ _ _ _ (adequacy _ _ _ _ _ H) Ψ Γ var var gid (fun _ => BOT) (fits_bot Γ gid) HS
                cPiw (mem_PI _ _) sty_Piw) as R.
  rewrite !sub_id in R.
  destruct (Rty_Piw _ _ _ _ R) as (A0 & B0 & A0' & B0' & [R1 _] & [R2 _] & HA & HB).
  apply hreds_Pi in R1, R2. injection R1 as <- <-. injection R2 as <- <-. split; assumption.
Qed.

Hypothesis TyS_id : forall Ψ Γ, TyS Ψ Γ Ψ Γ var var gid.

Corollary pi_injectivity_closed Ψ A B A' B' :
  eqj Ψ [] (Pi A B) (Pi A' B') U -> J Ψ [] A A' U /\ J Ψ [A] B B' U.
Proof.
  intros H. apply (pi_injectivity _ _ _ _ _ _ H). split; [apply TyS_id |].
  intros [| n] A0 HA0; discriminate.
Qed.

End Model.

(** * Findings

    1. Π-injectivity still follows. Adequacy extends to the code former
       with one new clause, which is not recursive and compares codes
       syntactically; it satisfies every law of §2.7 because codes are
       flat. The recursor's case needs an induction on the code inside
       the fundamental theorem's case ([elim_box]); the relation's own
       recursion on witnesses is untouched. Cor. 2.37 does not see the
       new clauses.

    2. The model keeps code as syntax, as the rule of thumb asks ([elim]
       inspects a code's constructors, [box]'s congruence compares code
       literally): [Q] is injective and a code is a flat element. Code
       variables, too, must be interpreted by codes (the global
       environment [τ] is syntactic and is at once the code
       substitution), not by [⊥]: with [⊥], [box (cv 0)] and
       [box (cv 1)] would denote one element, and Static Code would no
       longer follow from soundness. As it is, [static_code],
       [code_not_U] and [code_not_pi] follow from soundness alone. A
       stuck recursor ([elim] at a code variable) denotes [⊥] and is
       related by the Bot law.

    3. The four layer-M equations [AlgSound.v] draws from
       [DeclConsequences] are not inversions. [declM_inst_c_eq] and
       [declM_inst_t_eq] are global functionality (a context or D-type
       variable instantiated at convertible objects gives convertible
       results); [declM_motT_eq] and [declM_mott_eq] combine it with
       level equivalence and the scrutinees' conversion. This repo
       derives them from the Kripke fundamental theorem's escape
       ([VTyS_inst_c2]/[_t2], then [escM_VTyS]; M6_DESIGN.md), which
       needs the normalisation-strength relation. A domain-model relation
       cannot replace that step: it is [⊤] at [⊥] and records syntax only
       in the clauses injectivity reads, so it has no escape lemma.
       Functionality is syntactic metatheory there, proved before the
       model (here, local and two-sided: [J_subst]). In a domain-model
       development the four equations therefore need a syntactic proof
       of global functionality, the global analogue of [J_subst] with two
       convertible global substitutions; M7_DESIGN.md K2 records that
       removing the rules' instance premises needs the same lemma.

       The probe's global variables are layer-C codes, whose only
       conversion is identity, so its global substitution is one-sided
       and that analogue is trivial here. At D-objects it is not, and
       [box] is the case that could break it: boxed code compares
       literally, so [box c⦃σ⦄ ≅ box c⦃σ'⦄] needs [c⦃σ⦄ = c⦃σ'⦄] where
       [σ] and [σ'] differ at contexts or D-types. That is
       [Typing/GStatic.v]'s [static_gsubst]: C-typed code under two
       substitutions agreeing on the static bindings (contexts and
       D-objects excluded) is unchanged up to [≡ₗ]. So the case special
       to DeLaM is already a syntactic lemma of this repo. The model
       agrees with it: were code to depend on a context's image, [Q_inj]
       would separate [box c⦃Δ⦄] from [box c⦃Δ'⦄] and soundness would
       refute the equation. Not checked here: the rest of syntactic
       global functionality for DeLaM's rules (congruences, and the rules
       that carry the four equations as premises, M3 E10 and M5 G2).

    4. Left out:
       - codes with binders and contexts: DeLaM's [□(Γ ⊢ Ty)], codes of
         [Π] binding a variable, and a motive indexed by a context and a
         level. No eliminator inspects a context, so by the rule of thumb
         the model may erase contexts ([CΠ] as a [Π] over a one-point
         domain); [□]'s injectivity in [Γ] would then come from the
         clause's syntactic premise, as Π's domain does, and
         [□(Γ ⊢ Ty)] and [□(Γ ⊢ Tm A)] need distinct type codes since
         [elim_Typ] and [elim_Trm] inspect different codes. The split of
         [static_gsubst] is also the model's: only the static (layer C)
         global variables need a syntactic interpretation, as [τ] here;
         context and D-type variables ([CΠ], [TΠ]) can be interpreted
         semantically, since no code depends on their images;
       - levels and the universe tower (the paper's §3), and code levels
         compared by [≡ₗ] (a code summand quotiented by [≡ₗ]);
       - layers V and D as judgments of their own;
       - proofs of the abstract parts: the relation's construction, its
         clauses and laws at the old witnesses, the paper's cases for
         MLTTη ([V_var] … [V_eta]), and the syntactic metatheory ([J_*],
         [TyS_*]). *)

Print Assumptions soundness.
Print Assumptions static_code.
Print Assumptions RCd_hred.
Print Assumptions adequacy.
Print Assumptions pi_injectivity_closed.
