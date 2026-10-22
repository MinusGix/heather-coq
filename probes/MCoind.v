(** * Heather's indexed [M]: the rules in a model, and the bridge (M18a)

    Heather's kernel has an indexed negative coinductive former
    (H/docs/kernel-coinduction-design.md §1; MinusGix/heather#111):
    [M^{l,l',li}(I; i.S; i s.P; i s p.o)(j)], observed only by [out],
    introduced only by the apomorphic [corec], with β under [out] and no η.
    This file models it in Coq by a negative coinductive record with
    primitive projections, Rocq's own form of the same discipline (a
    [cofix] unfolds only under a projection, and Rocq has no η for
    coinductive records, which is checked below), and checks:

    - [out_corec]: β, as the kernel's [m_out_corec] (H/crates/kernel/src/
      term.rs) writes it, holds by [eq_refl] at an open index, carrier,
      step and seed: the reduct types at [out]'s type at [j], with the
      child's index [o j (projT1 r) p] computed and no index equation (Q2's
      "β at an open, computed child index").
    - The constructor. Design §1.4's [in(σ; j; s; f) := corec(_. Unit;
      _ _. (s, λp. inr (f p)); j; ⟨⟩)] does not type at an indexed [M]: the
      step is under the bound index [i], where [s : S j] is not an
      [S i] ([in_unit_fails]). It types when [I] is [Unit] ([in_unit],
      the streams of H/crates/kernel/tests/m.rs). The indexed constructor
      takes the observation type itself as its carrier ([in_]), and its
      β is [out (in_ j s f) = existT s f] by [eq_refl], up to Π-η only.
    - Negative controls, the kernel's verdicts, each a [Goal] whose
      [reflexivity] fails: no η ([t = mkM (out t)]), two [corec]s of one
      tree are not convertible ([zeros_u = zeros_n]) although every
      approximation of the two is the same ([zeros_same]) and they are
      bisimilar ([zeros_bisim]), a tree is not its reconstruction
      [in (out t)], and a [corec] that rebuilds a variable is not the
      variable. [zeros_same] is why the relation at [M] keeps a clause
      of generic equality beside its observations (MRelProbe.v,
      M18_DESIGN.md Q1): without it the relation would relate two terms
      the algorithm separates.
    - Bisimilarity as an instance of the indexed [M] (design §4), its
      index the pair of trees, its shapes the equations of the roots'
      shapes, its positions moved across them by [eq_rect] ([Bisim]), and
      the indexed variant, where the children's indices are moved along
      the shapes' equation too ([IBisim]). A proof by coinduction is a
      [corec] with the user's relation as the carrier ([bisim_refl],
      [ibisim_refl]).
    - The bridge (Q3): [Bisim t u <-> forall n, Same (approx n t) (approx
      n u)] over the finite cut trees. Left to right ([bisim_approx]) by
      induction on [n], nothing assumed. Right to left ([approx_bisim]) a
      [corec] into [Bisim] whose carrier is [forall n, Same …]; it merges
      the depth-[n] proofs of the shapes' equation, so it assumes UIP on
      the shapes ([UIP_S]), which holds axiom-free when they have decidable
      equality ([approx_bisim_dec], by Hedberg's [UIP_dec]); [bridge_dec]
      is the two directions together.

    No axioms: [Print Assumptions] at the end. Standalone: [coqc
    probes/MCoind.v], a few seconds. *)

From Coq Require Import Eqdep_dec.

Set Primitive Projections.

(** ** The former *)

Section MDef.
Variables (I : Type) (S : I -> Type) (P : forall i, S i -> Type)
  (o : forall i (s : S i), P i s -> I).

CoInductive M (j : I) : Type := mkM { out : { s : S j & forall p : P j s, M (o j s p) } }.

(** [corec]'s step type at [i] (the kernel's [m_step_ty]):
    [Σ(s : S i). Π(p : P i s). X (o i s p) + M (o i s p)]. *)
Definition StepTy (X : I -> Type) (i : I) : Type :=
  { s : S i & forall p : P i s, (X (o i s p) + M (o i s p))%type }.

Definition mkStep (X : I -> Type) (i : I) (s : S i)
  (k : forall p : P i s, (X (o i s p) + M (o i s p))%type) : StepTy X i :=
  existT (fun s => forall p : P i s, (X (o i s p) + M (o i s p))%type) s k.

CoFixpoint corec (X : I -> Type) (c : forall i, X i -> StepTy X i) (j : I) (x : X j) : M j :=
  mkM j (existT (fun s => forall p : P j s, M (o j s p)) (projT1 (c j x))
         (fun p => match projT2 (c j x) p with inl y => corec X c _ y | inr t => t end)).

(** β, transcribed from [m_out_corec] with [r := c[j, x]] written twice:
    [pair(fst r, λ(p : P[j, fst r]). case(_. M(o[j, fst r, p]); …;
    y. corec(…; o[j, fst r, p]; y); t. t; (snd r) p))]. Everything open. *)
Lemma out_corec X (c : forall i, X i -> StepTy X i) j (x : X j) :
  out j (corec X c j x) =
  existT (fun s => forall p : P j s, M (o j s p)) (projT1 (c j x))
    (fun p : P j (projT1 (c j x)) =>
       match projT2 (c j x) p return M (o j (projT1 (c j x)) p) with
       | inl y => corec X c (o j (projT1 (c j x)) p) y
       | inr t => t
       end).
Proof. reflexivity. Qed.

(** No η: a tree is not convertible to the record built from its
    observation (Rocq has no η for coinductive records). *)
Goal forall j (t : M j), t = mkM j (out j t).
Proof. intros. Fail reflexivity. Abort.

(** The indexed constructor: the carrier is [out]'s type itself, the seed
    the node, and every child exits. *)
Definition Node (i : I) : Type := { s : S i & forall p : P i s, M (o i s p) }.

Definition in_ (j : I) (s : S j) (f : forall p : P j s, M (o j s p)) : M j :=
  corec Node (fun i x => mkStep Node i (projT1 x) (fun p => inr (projT2 x p))) j (existT _ s f).

Lemma out_in j (s : S j) (f : forall p : P j s, M (o j s p)) :
  out j (in_ j s f) = existT _ s f.
Proof. reflexivity. Qed.

(** The design's [in] at carrier [Unit] is not a step at the bound index:
    [s : S j] where [S i] is wanted. *)
Lemma in_unit_fails : True.
Proof.
  (* "The term s has type S j while it is expected to have type S i." *)
  Fail pose (fun j (s : S j) (f : forall p : P j s, M (o j s p)) =>
    corec (fun _ => unit) (fun i _ => mkStep (fun _ => unit) i s (fun p => inr (f p))) j tt).
  exact Logic.I.
Qed.

(** A tree is not its own reconstruction, at a variable. *)
Goal forall j (t : M j), t = in_ j (projT1 (out j t)) (projT2 (out j t)).
Proof. intros. Fail reflexivity. Abort.

(** A [corec] is not a variable, even when it is the variable's
    reconstruction. *)
Goal forall j (t : M j),
  corec M (fun i t => mkStep M i (projT1 (out i t)) (fun p => inl (projT2 (out i t) p))) j t = t.
Proof. intros. Fail reflexivity. Abort.

End MDef.

Arguments mkM {I S P o j}.
Arguments out {I S P o j}.
Arguments corec {I S P o} X c j x.
Arguments StepTy {I} S P o X i.
Arguments mkStep {I S P o X i} s k.

(** ** Unindexed trees, their approximations, and the constructor at [Unit] *)

Section Unindexed.
Variables (S : Type) (P : S -> Type).

Definition T : Type := @M unit (fun _ => S) (fun _ s => P s) (fun _ _ _ => tt) tt.
Definition shape (t : T) : S := projT1 (out t).
Definition kid (t : T) : P (shape t) -> T := projT2 (out t).

(** At [I := Unit] the design's constructor types, and computes as it says. *)
Definition in_unit (s : S) (f : P s -> T) : T :=
  corec (fun _ => unit) (fun _ _ => mkStep s (fun p => inr (f p))) tt tt.

Lemma out_in_unit s f : out (in_unit s f) = existT _ s f.
Proof. reflexivity. Qed.

(** Finite trees cut at a depth (the finite library's [ITree] with its
    [Cut]), the cut of a tree, and sameness of finite trees: the shapes
    equal, the children the same across that equation. *)
Inductive Tr : Type := Cut | Nd (s : S) (k : P s -> Tr).

Fixpoint approx (n : nat) (t : T) : Tr :=
  match n with 0 => Cut | Datatypes.S n => Nd (shape t) (fun p => approx n (kid t p)) end.

Fixpoint Same (a b : Tr) : Type :=
  match a, b with
  | Cut, Cut => unit
  | Nd s k, Nd s' k' => { e : s = s' & forall p, Same (k p) (k' (eq_rect s P p s' e)) }
  | _, _ => False
  end.

(** Bisimilarity, an instance of the indexed [M] (design §4): index the
    pair of trees, shape the equation of the roots' shapes, positions the
    left root's, children the pair of children, the right one at the
    position moved across the equation. *)
Definition BI : Type := (T * T)%type.
Definition BS (ix : BI) : Type := shape (fst ix) = shape (snd ix).
Definition BP (ix : BI) (e : BS ix) : Type := P (shape (fst ix)).
Definition Bo (ix : BI) (e : BS ix) (p : BP ix e) : BI :=
  (kid (fst ix) p, kid (snd ix) (eq_rect _ P p _ e)).

Definition Bisim (t u : T) : Type := @M BI BS BP Bo (t, u).

(** A proof by coinduction: [corec] with the relation as its carrier.
    Here the relation is equality. *)
Definition bisim_refl (t : T) : Bisim t t :=
  corec (fun ix => fst ix = snd ix)
    (fun ix (e : fst ix = snd ix) =>
       match ix as ix0 return fst ix0 = snd ix0 -> StepTy BS BP Bo _ ix0 with
       | (t1, t2) => fun e =>
           match e in _ = t2' return StepTy BS BP Bo _ (t1, t2') with
           | eq_refl => mkStep eq_refl (fun p => inl eq_refl)
           end
       end e)
    (t, t) eq_refl.

(** ** The bridge *)

Lemma bisim_approx n : forall t u : T, Bisim t u -> Same (approx n t) (approx n u).
Proof.
  induction n as [|n IH]; intros t u b; [exact tt|].
  exists (projT1 (out b)). intros p. exact (IH _ _ (projT2 (out b) p)).
Defined.

Hypothesis UIP_S : forall (a b : S) (e e' : a = b), e = e'.

(** The carrier: depth-indexed sameness of the pair. *)
Definition Approx (ix : BI) : Type := forall n, Same (approx n (fst ix)) (approx n (snd ix)).

Definition approx_step (ix : BI) (h : Approx ix) : StepTy BS BP Bo Approx ix :=
  mkStep (projT1 (h 1))
    (fun p : P (shape (fst ix)) => inl (fun n =>
       match UIP_S _ _ (projT1 (h (Datatypes.S n))) (projT1 (h 1)) in _ = e
       return Same (approx n (kid (fst ix) p)) (approx n (kid (snd ix) (eq_rect _ P p _ e)))
       with eq_refl => projT2 (h (Datatypes.S n)) p end)).

Definition approx_bisim (t u : T) (h : forall n, Same (approx n t) (approx n u)) : Bisim t u :=
  corec (Approx) approx_step (t, u) h.

End Unindexed.

Arguments shape {S P} t. Arguments kid {S P} t p. Arguments approx {S P} n t.
Arguments Same {S P} a b. Arguments Bisim {S P} t u. Arguments bisim_approx {S P} n t u b.
Arguments approx_bisim {S P} UIP_S t u h.

(** Two descriptions of the stream of [Unit]-shaped nodes with one child
    each, over the carrier [Unit] and over [nat]. *)

Section Zeros.
Definition Z : Type := T unit (fun _ => unit).
Definition zeros_u : Z :=
  corec (fun _ => unit) (fun _ _ => mkStep tt (fun _ => inl tt)) tt tt.
Definition zeros_n : Z :=
  corec (fun _ => nat) (fun _ n => mkStep tt (fun _ => inl (Datatypes.S n))) tt 0.

(** Distinct values (the kernel's [two_corecs_of_one_tree_are_distinct]). *)
Goal zeros_u = zeros_n.
Proof. Fail reflexivity. Abort.

(** … whose approximations are the same at every depth. *)
Lemma zeros_same_gen n : forall m, @Same unit (fun _ => unit) (approx n zeros_u)
  (approx n (corec (fun _ => nat) (fun _ n => mkStep tt (fun _ => inl (Datatypes.S n))) tt m : Z)).
Proof.
  induction n as [|n IH]; intros m; [exact tt|].
  exists eq_refl. intros p. exact (IH (Datatypes.S m)).
Defined.

Lemma zeros_same n : Same (approx n zeros_u) (approx n zeros_n).
Proof. exact (zeros_same_gen n 0). Defined.
End Zeros.

(** Shapes with decidable equality need no assumption (Hedberg). *)
Definition approx_bisim_dec (S : Type) (P : S -> Type) (dec : forall a b : S, {a = b} + {a <> b})
  (t u : T S P) (h : forall n, Same (approx n t) (approx n u)) : Bisim t u :=
  approx_bisim (UIP_dec dec) t u h.

Definition bridge_dec (S : Type) (P : S -> Type) (dec : forall a b : S, {a = b} + {a <> b})
  (t u : T S P) : (Bisim t u -> forall n, Same (approx n t) (approx n u)) *
                  ((forall n, Same (approx n t) (approx n u)) -> Bisim t u) :=
  (fun b n => bisim_approx n t u b, approx_bisim_dec S P dec t u).

(** The two zero streams are bisimilar, through the bridge ([unit] has
    decidable equality). *)
Definition zeros_bisim : Bisim zeros_u zeros_n :=
  approx_bisim_dec unit (fun _ => unit)
    (fun a b : unit => match a, b with tt, tt => left eq_refl end) zeros_u zeros_n zeros_same.

(** ** Indexed bisimilarity

    At an indexed [M], the children of [t] and [u] at positions related by
    the shapes' equation [e] sit at the indices [o j s p] and
    [o j s' (e ▸ p)], equal only along [e]. The index of [IBisim] is a
    node index with two trees there, and the right child is moved to the
    left child's index along the same equation. *)
Section IBisim.
Variables (I : Type) (S : I -> Type) (P : forall i, S i -> Type)
  (o : forall i (s : S i), P i s -> I).
Local Notation MM := (@M I S P o).

Definition ishape {j} (t : MM j) : S j := projT1 (out t).
Definition ikid {j} (t : MM j) : forall p : P j (ishape t), MM (o j (ishape t) p) := projT2 (out t).

Definition IBI : Type := { j : I & (MM j * MM j)%type }.
Definition IBS (ix : IBI) : Type := ishape (fst (projT2 ix)) = ishape (snd (projT2 ix)).
Definition IBP (ix : IBI) (e : IBS ix) : Type := P (projT1 ix) (ishape (fst (projT2 ix))).

(** The right child, moved to the left child's index along [e]. *)
Definition ikid_moved (j : I) (t u : MM j) (e : ishape t = ishape u) (p : P j (ishape t)) :
    MM (o j (ishape t) p) :=
  match e in _ = s' return (forall q : P j s', MM (o j s' q)) -> MM (o j (ishape t) p) with
  | eq_refl => fun k => k p
  end (ikid u).

Definition IBo (ix : IBI) (e : IBS ix) (p : IBP ix e) : IBI :=
  existT (fun j => (MM j * MM j)%type) (o _ _ p)
    (ikid (fst (projT2 ix)) p, ikid_moved (projT1 ix) (fst (projT2 ix)) (snd (projT2 ix)) e p).

Definition IBisim (j : I) (t u : MM j) : Type := @M IBI IBS IBP IBo (existT _ j (t, u)).

(** Reflexivity, by [corec] at the carrier "the two trees are equal". The
    moved child at [eq_refl] is the child itself, by [ikid_moved]'s β. *)
Definition ibisim_refl (j : I) (t : MM j) : IBisim j t t :=
  corec (fun ix => fst (projT2 ix) = snd (projT2 ix))
    (fun ix =>
       match ix as ix0 return fst (projT2 ix0) = snd (projT2 ix0) -> StepTy IBS IBP IBo _ ix0 with
       | existT _ j0 (t1, t2) => fun e =>
           match e in _ = t2' return StepTy IBS IBP IBo _ (existT _ j0 (t1, t2')) with
           | eq_refl => mkStep eq_refl (fun p => inl eq_refl)
           end
       end)
    (existT _ j (t, t)) eq_refl.
End IBisim.

Print Assumptions out_corec.
Print Assumptions out_in.
Print Assumptions bisim_approx.
Print Assumptions bisim_refl.
Print Assumptions bridge_dec.
Print Assumptions zeros_bisim.
Print Assumptions ibisim_refl.
