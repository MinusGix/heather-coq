(** * Depth-indexed bisimilarity on interaction trees: a probe
    (Heather [issues/interaction-trees-container-model.md], question 1)

    Heather's [docs/interaction-trees-fit.md] §3.7 proposes stating weak
    bisimilarity (eutt) predicatively, as [Π n. euttₙ], where each [euttₙ]
    is inductive: Tau peeling stays inductive and [EqTau]/[EqVis] consume an
    index. Its conjecture: for deterministic trees the ω-approximants meet at
    the greatest fixed point (the paco/Knaster–Tarski definition). This file
    settles it in Coq, for interaction trees over container events
    ([Cmd : Type], [Resp : Cmd -> Type]) with arbitrary, possibly infinite,
    response types.

    Checked below:
    - [eutt_gfp_omega]: the conjecture. [eutt_gfp t u <-> forall n,
      eutt_n n t u]. The inclusion of the gfp in every approximant is
      unconditional ([gfp_omega]); the converse ([omega_post]) needs the
      equality of commands to be proof-irrelevant ([UIP_Cmd], below).
    - [euttI_iff]: the approximants written as one inductive family over
      [nat], as the doc phrases them ([I0] at index 0, [IVis]/[ITau] at
      [S n], peeling at any [n]), agree with the [Fixpoint] form.
    - The omega relation is usable on its own, with no gfp in sight (the
      position Heather is in, with no impredicative [Prop]): reflexive
      ([omega_refl]) and symmetric ([omega_sym]) outright, transitive
      ([omega_trans]), a congruence for [bind] ([omega_bind]), and it
      absorbs Taus ([omega_tau_l]). Transitivity and [bind] are proved
      by induction on the index, using [omega_post] but not the gfp.
    - [spin_not_euttT]: the index must be consumed by [EqTau]. With an
      inductive (index-free) Tau-Tau rule the silent divergence [spin] is
      not related to itself at any index.
    - [milner]: the boundary. In an image-infinite nondeterministic LTS
      (the choice tree [Br(λn. aⁿ)] against [Br(λn. aⁿ) ⊕ a^ω]) every
      approximant holds and the gfp fails, so choice trees (doc §6.2) do
      reopen the question.

    Where determinism is used: in the post-fixpoint proof [omega_post], the
    number of Taus a side peels before reaching a [Ret]/[Vis] is fixed by the
    tree ([fin], [post_left]), so the per-index derivations all go through
    the same node and the [∀ n ∃ derivation] swaps to [∃ ∀ n]. The one other
    swap is the command equality in the [Vis] clause: each index gives its
    own proof [p : c1 = c2], and this proof merges them by asking those
    proofs to be equal: the hypothesis [UIP_Cmd], which holds axiom-free for
    any [Cmd] with decidable equality ([UIP_Cmd_of_dec]). Whether the
    theorem fails without it (a [Cmd] that is not a set) is not checked
    here. Reflexivity and symmetry do not need it. If Heather states the
    clause with [sEq], which is definitionally irrelevant, the per-index
    proofs are convertible and the swap needs nothing; stated with [Id], it
    needs [Cmd] to be a set.

    No axioms: [Print Assumptions] at the end of the file. Standalone:
    [coqc probes/ItreeDepthBisim.v]. *)

From Coq Require Import Arith Lia Eqdep_dec.

Section ITree.

Variable Cmd : Type.
Variable Resp : Cmd -> Type.

(** Interaction trees, negative style, as in Xia et al. *)

Variant itreeF (R X : Type) : Type :=
| RetF (r : R)
| TauF (t : X)
| VisF (c : Cmd) (k : Resp c -> X).

Arguments RetF {R X} r.
Arguments TauF {R X} t.
Arguments VisF {R X} c k.

CoInductive itree (R : Type) : Type := go { observe : itreeF R (itree R) }.

Arguments go {R} _.
Arguments observe {R} _.

Definition Ret {R} (r : R) : itree R := go (RetF r).
Definition Tau {R} (t : itree R) : itree R := go (TauF t).
Definition Vis {R} (c : Cmd) (k : Resp c -> itree R) : itree R := go (VisF c k).

(** Proof irrelevance of command equality: the only extra hypothesis, used
    only where an index-wise family of proofs [c1 = c2] must be merged. *)

Definition UIP_Cmd : Prop := forall (c1 c2 : Cmd) (p q : c1 = c2), p = q.

Lemma UIP_Cmd_of_dec :
  (forall c1 c2 : Cmd, {c1 = c2} + {c1 <> c2}) -> UIP_Cmd.
Proof. intros dec c1 c2 p q. apply UIP_dec. exact dec. Qed.

Section Rel.

Context {R : Type}.

Notation rel := (itree R -> itree R -> Prop).

(** One step of eutt. The [Ret]/[Tau]/[Vis] matches look at [observe]; the
    [Tau]-[Tau] and [Vis]-[Vis] clauses go to [Rel], the peeling rules are
    inductive. The trees are not indices of [euttF], so no inversion ever
    needs the injectivity of [VisF] in its dependent argument. *)

Definition baseF (Rel : rel) (ot ou : itreeF R (itree R)) : Prop :=
  match ot, ou with
  | RetF r1, RetF r2 => r1 = r2
  | TauF t, TauF u => Rel t u
  | VisF c1 k1, VisF c2 k2 =>
      exists p : c1 = c2, forall a, Rel (k1 a) (k2 (eq_rect c1 Resp a c2 p))
  | _, _ => False
  end.

Inductive euttF (Rel : rel) : rel :=
| eBase t u : baseF Rel (observe t) (observe u) -> euttF Rel t u
| eTauL t t' u : observe t = TauF t' -> euttF Rel t' u -> euttF Rel t u
| eTauR t u u' : observe u = TauF u' -> euttF Rel t u' -> euttF Rel t u.

Lemma baseF_mono (R1 R2 : rel) ot ou :
  (forall x y, R1 x y -> R2 x y) -> baseF R1 ot ou -> baseF R2 ot ou.
Proof.
  intros HR H. destruct ot, ou; simpl in *; auto.
  destruct H as [p Hp]. exists p. intro a. apply HR, Hp.
Qed.

Lemma euttF_mono (R1 R2 : rel) t u :
  (forall x y, R1 x y -> R2 x y) -> euttF R1 t u -> euttF R2 t u.
Proof.
  intros HR H. induction H as [t u Hb|t t' u Ht _ IH|t u u' Hu _ IH].
  - apply eBase. eapply baseF_mono; eassumption.
  - eapply eTauL; eassumption.
  - eapply eTauR; eassumption.
Qed.

(** [euttF] reads its trees only through [observe]. *)
Lemma euttF_obs (Rel : rel) t u t' u' :
  observe t = observe t' -> observe u = observe u' ->
  euttF Rel t u -> euttF Rel t' u'.
Proof.
  intros Ht Hu H. revert t' u' Ht Hu.
  induction H as [t u Hb|t t0 u Ht0 _ IH|t u u0 Hu0 _ IH]; intros t' u' Ht Hu.
  - apply eBase. rewrite <- Ht, <- Hu. exact Hb.
  - eapply eTauL. { rewrite <- Ht. exact Ht0. } apply IH; auto.
  - eapply eTauR. { rewrite <- Hu. exact Hu0. } apply IH; auto.
Qed.

(** ** The two definitions *)

(** The approximants: index 0 relates everything, [S n] is one step over
    index [n]. The index is consumed exactly by the [Tau]-[Tau] and
    [Vis]-[Vis] clauses; peeling is free. *)
Fixpoint eutt_n (n : nat) : rel :=
  match n with
  | 0 => fun _ _ => True
  | S n => euttF (eutt_n n)
  end.

Definition eutt_omega : rel := fun t u => forall n, eutt_n n t u.

(** The greatest fixed point, Knaster–Tarski style (paco's [nu]). *)
Definition eutt_gfp : rel :=
  fun t u => exists Rel : rel, (forall x y, Rel x y -> euttF Rel x y) /\ Rel t u.

(** ** Basic facts about the approximants *)

Lemma eutt_n_down n t u : eutt_n (S n) t u -> eutt_n n t u.
Proof.
  revert t u. induction n as [|n IH]; intros t u H; [exact I|].
  simpl in *. eapply euttF_mono; [|exact H]. exact IH.
Qed.

Lemma eutt_n_obs n t u t' u' :
  observe t = observe t' -> observe u = observe u' ->
  eutt_n n t u -> eutt_n n t' u'.
Proof. destruct n; [trivial|]. apply euttF_obs. Qed.

(** Removing a leading [Tau] costs at most one index. *)
Lemma unTauL n t t' u :
  observe t = TauF t' -> eutt_n (S n) t u -> eutt_n n t' u.
Proof.
  intros Ht H. simpl in H. revert t' Ht.
  induction H as [t u Hb|t t0 u Ht0 H0 _|t u u0 Hu0 _ IH]; intros t' Ht.
  - rewrite Ht in Hb. destruct (observe u) as [r|u0|c k] eqn:Hu;
      simpl in Hb; try contradiction.
    destruct n; [exact I|]. simpl. eapply eTauR; eassumption.
  - rewrite Ht in Ht0. injection Ht0 as <-. apply eutt_n_down. exact H0.
  - specialize (IH t' Ht). destruct n; [exact I|].
    simpl. eapply eTauR; eassumption.
Qed.

Lemma unTauR n t u u' :
  observe u = TauF u' -> eutt_n (S n) t u -> eutt_n n t u'.
Proof.
  intros Hu H. simpl in H. revert u' Hu.
  induction H as [t u Hb|t t0 u Ht0 _ IH|t u u0 Hu0 H0 _]; intros u' Hu.
  - rewrite Hu in Hb. destruct (observe t) as [r|t0|c k] eqn:Ht;
      simpl in Hb; try contradiction.
    destruct n; [exact I|]. simpl. eapply eTauL; eassumption.
  - specialize (IH u' Hu). destruct n; [exact I|].
    simpl. eapply eTauL; eassumption.
  - rewrite Hu in Hu0. injection Hu0 as <-. apply eutt_n_down. exact H0.
Qed.

Lemma omega_unTauL t t' u :
  observe t = TauF t' -> eutt_omega t u -> eutt_omega t' u.
Proof. intros Ht H n. apply (unTauL n t); auto. Qed.

Lemma omega_unTauR t u u' :
  observe u = TauF u' -> eutt_omega t u -> eutt_omega t u'.
Proof. intros Hu H n. apply (unTauR n t u); auto. Qed.

(** ** gfp ⊆ every approximant: no hypothesis *)

Lemma gfp_omega t u : eutt_gfp t u -> eutt_omega t u.
Proof.
  intros [Rel [Hpost HR]] n. revert t u HR.
  induction n as [|n IH]; intros t u HR; [exact I|].
  simpl. eapply euttF_mono; [exact IH|]. apply Hpost, HR.
Qed.

(** ** Finite Tau prefixes: where determinism enters *)

Definition notau (t : itree R) : Prop := forall t', observe t <> TauF t'.

(** [t] reaches a [Ret] or [Vis] after finitely many [Tau]s. Since a tree
    has one [observe], the number of [Tau]s and the node reached are fixed
    by [t]: no derivation can choose them. *)
Lemma notau_dec t : notau t \/ exists t', observe t = TauF t'.
Proof.
  destruct (observe t) as [r|t'|c k] eqn:E; [left| |left];
    try (intros t0 E0; rewrite E in E0; discriminate).
  right. exists t'. reflexivity.
Qed.

Inductive fin : itree R -> Prop :=
| fin_stop t : notau t -> fin t
| fin_tau t t' : observe t = TauF t' -> fin t' -> fin t.

Lemma euttF_fin_l (Rel : rel) t u : euttF Rel t u -> notau u -> fin t.
Proof.
  intros H Hu. induction H as [t u Hb|t t' u Ht _ IH|t u u' Hu' _ _].
  - apply fin_stop. intros t' Ht. rewrite Ht in Hb.
    destruct (observe u) eqn:E; simpl in Hb; try contradiction.
    exact (Hu _ E).
  - eapply fin_tau; eauto.
  - exfalso. exact (Hu _ Hu').
Qed.

Lemma euttF_fin_r (Rel : rel) t u : euttF Rel t u -> notau t -> fin u.
Proof.
  intros H Ht. induction H as [t u Hb|t t' u Ht' _ _|t u u' Hu _ IH].
  - apply fin_stop. intros u' Hu. rewrite Hu in Hb.
    destruct (observe t) eqn:E; simpl in Hb; try contradiction.
    exact (Ht _ E).
  - exfalso. exact (Ht _ Ht').
  - eapply fin_tau; eauto.
Qed.

(** Between two [notau] trees a derivation can only be [eBase]. *)
Lemma euttF_base (Rel : rel) t u :
  notau t -> notau u -> euttF Rel t u -> baseF Rel (observe t) (observe u).
Proof.
  intros Ht Hu H. destruct H as [t u Hb|t t' u Ht' _|t u u' Hu' _].
  - exact Hb.
  - exfalso. exact (Ht _ Ht').
  - exfalso. exact (Hu _ Hu').
Qed.

(** ** The approximants' intersection is a post-fixed point *)

Section Post.

Hypothesis uip : UIP_Cmd.

(** The one place where an index-wise family of witnesses is merged: the
    command equalities. *)
Lemma base_omega t u :
  notau t -> notau u -> eutt_omega t u ->
  baseF eutt_omega (observe t) (observe u).
Proof.
  intros Ht Hu H.
  assert (Hb : forall n, baseF (eutt_n n) (observe t) (observe u)).
  { intro n. apply euttF_base; auto. exact (H (S n)). }
  pose proof (Hb 0) as H0.
  destruct (observe t) as [r1|t'|c1 k1] eqn:Et, (observe u) as [r2|u'|c2 k2];
    simpl in H0 |- *; try contradiction.
  - exact H0.
  - exfalso. exact (Ht _ Et).
  - destruct H0 as [p _]. exists p. intros a n.
    destruct (Hb n) as [q Hq]. rewrite (uip _ _ p q). apply Hq.
Qed.

Lemma post_left t u :
  fin t -> notau u -> eutt_omega t u -> euttF eutt_omega t u.
Proof.
  intros Hf Hu. revert u Hu.
  induction Hf as [t Ht|t t' Ht _ IH]; intros u Hu H.
  - apply eBase. apply base_omega; auto.
  - eapply eTauL; [exact Ht|]. apply IH; auto. eapply omega_unTauL; eauto.
Qed.

Lemma post_right t u :
  notau t -> fin u -> eutt_omega t u -> euttF eutt_omega t u.
Proof.
  intros Ht Hf. revert t Ht.
  induction Hf as [u Hu|u u' Hu _ IH]; intros t Ht H.
  - apply eBase. apply base_omega; auto.
  - eapply eTauR; [exact Hu|]. apply IH; auto. eapply omega_unTauR; eauto.
Qed.

Lemma omega_post t u : eutt_omega t u -> euttF eutt_omega t u.
Proof.
  intros H. destruct (notau_dec u) as [Hu|[u' Hu]].
  - apply post_left; auto.
    apply (euttF_fin_l (eutt_n 0) t u); [exact (H 1)|exact Hu].
  - destruct (notau_dec t) as [Ht|[t' Ht]].
    + apply post_right; auto.
      apply (euttF_fin_r (eutt_n 0) t u); [exact (H 1)|exact Ht].
    + apply eBase. rewrite Ht, Hu. simpl.
      apply (omega_unTauR t' u u'); auto. eapply omega_unTauL; eauto.
Qed.

Lemma omega_gfp t u : eutt_omega t u -> eutt_gfp t u.
Proof. intros H. exists eutt_omega. split; [exact omega_post | exact H]. Qed.

(** The conjecture of [docs/interaction-trees-fit.md] §3.7. *)
Theorem eutt_gfp_omega t u : eutt_gfp t u <-> eutt_omega t u.
Proof. split; [apply gfp_omega | apply omega_gfp]. Qed.

End Post.

(** ** The approximants as one inductive family

    The doc's phrasing: an inductive family over [nat] with inductive Tau
    peeling and the index consumed by [EqTau]/[EqVis]. *)

Inductive euttI : nat -> rel :=
| I0 t u : euttI 0 t u
| IRet n t u r : observe t = RetF r -> observe u = RetF r -> euttI (S n) t u
| ITau n t u t' u' : observe t = TauF t' -> observe u = TauF u' ->
    euttI n t' u' -> euttI (S n) t u
| IVis n t u c1 c2 (p : c1 = c2) k1 k2 :
    observe t = VisF c1 k1 -> observe u = VisF c2 k2 ->
    (forall a, euttI n (k1 a) (k2 (eq_rect c1 Resp a c2 p))) ->
    euttI (S n) t u
| ITauL n t t' u : observe t = TauF t' -> euttI (S n) t' u -> euttI (S n) t u
| ITauR n t u u' : observe u = TauF u' -> euttI (S n) t u' -> euttI (S n) t u.

Lemma euttI_n n t u : euttI n t u -> eutt_n n t u.
Proof.
  induction 1 as [t u|n t u r Ht Hu|n t u t' u' Ht Hu _ IH
                 |n t u c1 c2 p k1 k2 Ht Hu _ IH|n t t' u Ht _ IH|n t u u' Hu _ IH].
  - exact I.
  - apply eBase. rewrite Ht, Hu. reflexivity.
  - apply eBase. rewrite Ht, Hu. exact IH.
  - apply eBase. rewrite Ht, Hu. exists p. exact IH.
  - eapply eTauL; eassumption.
  - eapply eTauR; eassumption.
Qed.

Lemma n_euttI n t u : eutt_n n t u -> euttI n t u.
Proof.
  revert t u. induction n as [|n IHn]; intros t u H; [apply I0|].
  simpl in H.
  induction H as [t u Hb|t t' u Ht _ IH|t u u' Hu _ IH].
  - destruct (observe t) as [r1|t'|c1 k1] eqn:Ht,
             (observe u) as [r2|u'|c2 k2] eqn:Hu;
      simpl in Hb; try contradiction.
    + subst r2. eapply IRet; eassumption.
    + eapply ITau; eauto.
    + destruct Hb as [p Hp]. eapply IVis with (p := p); eauto.
  - eapply ITauL; eassumption.
  - eapply ITauR; eassumption.
Qed.

Lemma euttI_iff n t u : euttI n t u <-> eutt_n n t u.
Proof. split; [apply euttI_n | apply n_euttI]. Qed.

(** ** The omega relation on its own: an equivalence, and Tau-invariant *)

Lemma eutt_n_refl n t : eutt_n n t t.
Proof.
  revert t. induction n as [|n IH]; intro t; [exact I|].
  simpl. apply eBase. destruct (observe t) as [r|t'|c k]; simpl; auto.
  exists eq_refl. intro a. apply IH.
Qed.

Lemma eutt_n_sym n t u : eutt_n n t u -> eutt_n n u t.
Proof.
  revert t u. induction n as [|n IHn]; intros t u H; [exact I|].
  simpl in *. induction H as [t u Hb|t t' u Ht _ IH|t u u' Hu _ IH].
  - apply eBase.
    destruct (observe t) as [r1|t'|c1 k1], (observe u) as [r2|u'|c2 k2];
      simpl in *; try contradiction; auto.
    destruct Hb as [p Hp]. destruct p. exists eq_refl.
    intro a. apply IHn, Hp.
  - eapply eTauR; eassumption.
  - eapply eTauL; eassumption.
Qed.

Lemma omega_refl t : eutt_omega t t.
Proof. intro n. apply eutt_n_refl. Qed.

Lemma omega_sym t u : eutt_omega t u -> eutt_omega u t.
Proof. intros H n. apply eutt_n_sym, H. Qed.

Lemma omega_tau_l t u : eutt_omega t u -> eutt_omega (Tau t) u.
Proof.
  intros H n. destruct n; [exact I|].
  eapply eTauL; [reflexivity|]. exact (H (S n)).
Qed.

Lemma omega_tau t : eutt_omega (Tau t) t.
Proof. apply omega_tau_l, omega_refl. Qed.

Lemma omega_fin_l t u : eutt_omega t u -> fin u -> fin t.
Proof.
  intros H Hf. revert t H.
  induction Hf as [u Hu|u u' Hu _ IH]; intros t H.
  - eapply euttF_fin_l; [exact (H 1)|exact Hu].
  - apply IH. eapply omega_unTauR; eauto.
Qed.

Lemma omega_fin_r t u : eutt_omega t u -> fin t -> fin u.
Proof. intros H Hf. eapply omega_fin_l; [apply omega_sym, H|exact Hf]. Qed.

Section Trans.

Hypothesis uip : UIP_Cmd.

(** Transitivity, by induction on the index, with [omega_post] (and so
    [UIP_Cmd]) to unfold the hypotheses. No gfp. *)

Section Step.

Variable n : nat.
Hypothesis IHn :
  forall t u v, eutt_omega t u -> eutt_omega u v -> eutt_n n t v.

Lemma trans_base t u v :
  notau t -> notau u -> notau v ->
  eutt_omega t u -> eutt_omega u v -> euttF (eutt_n n) t v.
Proof.
  intros Ht Hu Hv Htu Huv. apply eBase.
  pose proof (euttF_base _ _ _ Ht Hu (omega_post uip _ _ Htu)) as H1.
  pose proof (euttF_base _ _ _ Hu Hv (omega_post uip _ _ Huv)) as H2.
  destruct (observe t) as [r1|t'|c1 k1] eqn:Et, (observe u) as [r2|u'|c2 k2],
           (observe v) as [r3|v'|c3 k3];
    simpl in *; try contradiction.
  - congruence.
  - exfalso. exact (Ht _ Et).
  - destruct H1 as [p Hp], H2 as [q Hq]. destruct p, q. exists eq_refl.
    intro a. apply (IHn _ (k2 a)); [apply Hp|apply Hq].
Qed.

Lemma trans_left t u v :
  fin t -> notau v ->
  eutt_omega t u -> eutt_omega u v -> euttF (eutt_n n) t v.
Proof.
  intros Hf Hv. revert u.
  induction Hf as [t Ht|t t' Ht _ IH]; intros u Htu Huv.
  - assert (Hfu : fin u) by (eapply omega_fin_r; [exact Htu|apply fin_stop, Ht]).
    revert Htu Huv. induction Hfu as [u Hu|u u' Hu _ IHu]; intros Htu Huv.
    + apply trans_base with u; auto.
    + apply IHu.
      * eapply omega_unTauR; eauto.
      * eapply omega_unTauL; eauto.
  - eapply eTauL; [exact Ht|]. apply IH with u; auto.
    eapply omega_unTauL; eauto.
Qed.

End Step.

Lemma omega_trans t u v :
  eutt_omega t u -> eutt_omega u v -> eutt_omega t v.
Proof.
  intros Htu Huv n. revert t u v Htu Huv.
  induction n as [|n IHn]; intros t u v Htu Huv; [exact I|]. simpl.
  destruct (notau_dec v) as [Hv|[v' Hv]].
  - (* [v] is not a [Tau]: [t]'s prefix is finite, through [u]. *)
    apply trans_left with u; auto.
    apply omega_fin_l with u; [exact Htu|].
    apply omega_fin_l with v; [exact Huv|]. apply fin_stop, Hv.
  - destruct (notau_dec t) as [Ht|[t' Ht]].
    + (* [t] is not a [Tau]: the mirror image, through symmetry. *)
      apply (eutt_n_sym (S n)). change (eutt_n (S n) v t).
      apply trans_left with u.
      * intros x y z Hxy Hyz. apply IHn with y; auto.
      * apply omega_fin_r with u; [exact Huv|].
        apply omega_fin_r with t; [exact Htu|]. apply fin_stop, Ht.
      * exact Ht.
      * apply omega_sym, Huv.
      * apply omega_sym, Htu.
    + apply eBase. rewrite Ht, Hv. simpl. apply IHn with u.
      * eapply omega_unTauL; eauto.
      * eapply omega_unTauR; eauto.
Qed.

End Trans.

End Rel.

(** ** [bind] is a congruence *)

CoFixpoint bind {R Q} (t : itree R) (k : R -> itree Q) : itree Q :=
  match observe t with
  | RetF r => k r
  | TauF t' => Tau (bind t' k)
  | VisF c h => Vis c (fun a => bind (h a) k)
  end.

Lemma bind_obs {R Q} (t : itree R) (k : R -> itree Q) :
  observe (bind t k) =
  match observe t with
  | RetF r => observe (k r)
  | TauF t' => TauF (bind t' k)
  | VisF c h => VisF c (fun a => bind (h a) k)
  end.
Proof.
  change (observe (bind t k)) with (observe (match observe t with
    | RetF r => k r
    | TauF t' => Tau (bind t' k)
    | VisF c h => Vis c (fun a => bind (h a) k)
    end)).
  destruct (observe t); reflexivity.
Qed.

Lemma omega_bind (uip : UIP_Cmd) {R Q} (t t' : itree R) (k k' : R -> itree Q) :
  eutt_omega t t' -> (forall r, eutt_omega (k r) (k' r)) ->
  eutt_omega (bind t k) (bind t' k').
Proof.
  intros Ht Hk n. revert t t' Ht.
  induction n as [|n IHn]; intros t t' Ht; [exact I|].
  pose proof (omega_post uip _ _ Ht) as H. simpl.
  clear Ht. induction H as [t t' Hb|t t0 t' Ht0 _ IH|t t' t0 Ht0 _ IH].
  - destruct (observe t) as [r1|t1|c1 k1] eqn:Ht,
             (observe t') as [r2|t2|c2 k2] eqn:Ht';
      simpl in Hb; try contradiction.
    + subst r2. apply (eutt_n_obs (S n) (k r1) (k' r1)).
      * rewrite bind_obs, Ht. reflexivity.
      * rewrite bind_obs, Ht'. reflexivity.
      * apply Hk.
    + apply eBase. rewrite !bind_obs, Ht, Ht'. simpl. apply IHn, Hb.
    + apply eBase. rewrite !bind_obs, Ht, Ht'. simpl.
      destruct Hb as [p Hp]. destruct p. exists eq_refl.
      intro a. apply IHn, Hp.
  - eapply eTauL; [|exact IH]. rewrite bind_obs, Ht0. reflexivity.
  - eapply eTauR; [|exact IH]. rewrite bind_obs, Ht0. reflexivity.
Qed.

(** ** The index must be consumed by [EqTau]

    With an inductive Tau-Tau rule (a fourth peeling rule, no index),
    the silent divergence is not related to itself at any index. *)

CoFixpoint spin {R} : itree R := Tau spin.

Lemma spin_obs {R} : observe (@spin R) = TauF spin.
Proof. reflexivity. Qed.

Section TauFree.

Context {R : Type}.

Definition baseT (Rel : itree R -> itree R -> Prop) (ot ou : itreeF R (itree R)) : Prop :=
  match ot, ou with
  | RetF r1, RetF r2 => r1 = r2
  | VisF c1 k1, VisF c2 k2 =>
      exists p : c1 = c2, forall a, Rel (k1 a) (k2 (eq_rect c1 Resp a c2 p))
  | _, _ => False
  end.

Inductive euttT (Rel : itree R -> itree R -> Prop) : itree R -> itree R -> Prop :=
| tBase t u : baseT Rel (observe t) (observe u) -> euttT Rel t u
| tTau t t' u u' : observe t = TauF t' -> observe u = TauF u' ->
    euttT Rel t' u' -> euttT Rel t u
| tTauL t t' u : observe t = TauF t' -> euttT Rel t' u -> euttT Rel t u
| tTauR t u u' : observe u = TauF u' -> euttT Rel t u' -> euttT Rel t u.

Lemma spin_not_euttT Rel : ~ euttT Rel spin spin.
Proof.
  assert (forall t u, euttT Rel t u -> observe t = TauF spin ->
                      observe u = TauF spin -> False) as H.
  { induction 1 as [t u Hb|t t' u u' Ht Hu _ IH|t t' u Ht _ IH|t u u' Hu _ IH];
      intros Hts Hus.
    - rewrite Hts, Hus in Hb. exact Hb.
    - rewrite Hts in Ht. rewrite Hus in Hu.
      injection Ht as <-. injection Hu as <-. apply IH; reflexivity.
    - rewrite Hts in Ht. injection Ht as <-. apply IH; [reflexivity|exact Hus].
    - rewrite Hus in Hu. injection Hu as <-. apply IH; [exact Hts|reflexivity]. }
  intro Hs. exact (H _ _ Hs eq_refl eq_refl).
Qed.

End TauFree.

End ITree.

(** ** The boundary: image-infinite nondeterminism (Milner)

    Choice trees add an internal branching node. Their bisimilarity matches
    a branch on one side with {e some} branch on the other, and that [∃]
    does not swap with the index's [∀]. The classic witness, as a labelled
    transition system with one action [a]: [A m] is [aᵐ], [Om] is [a^ω],
    [T] is [Σ_{n} aⁿ⁺¹] (a branch for every length), [U] is [T + a^ω]. *)

Module Milner.

Inductive st := A (m : nat) | Om | T | U.

Inductive step : st -> st -> Prop :=
| sA m : step (A (S m)) (A m)
| sOm : step Om Om
| sT m : step T (A m)
| sU m : step U (A m)
| sUO : step U Om.

Definition bisF (Rel : st -> st -> Prop) (x y : st) : Prop :=
  (forall x', step x x' -> exists y', step y y' /\ Rel x' y') /\
  (forall y', step y y' -> exists x', step x x' /\ Rel x' y').

Fixpoint bis_n (n : nat) : st -> st -> Prop :=
  match n with 0 => fun _ _ => True | S n => bisF (bis_n n) end.

Definition bis_gfp (x y : st) : Prop :=
  exists Rel, (forall x y, Rel x y -> bisF Rel x y) /\ Rel x y.

Lemma bis_n_refl n x : bis_n n x x.
Proof.
  revert x. induction n as [|n IH]; intro x; [exact I|].
  split; intros z Hz; exists z; auto.
Qed.

(** [aᵐ] and [a^ω] agree for [n] steps when [m >= n]. *)
Lemma bis_n_A_Om n m : n <= m -> bis_n n (A m) Om.
Proof.
  revert m. induction n as [|n IH]; intros m Hm; [exact I|].
  destruct m as [|m]; [lia|]. split.
  - intros x' Hx. inversion Hx; subst. exists Om. split; [constructor|].
    apply IH. lia.
  - intros y' Hy. inversion Hy; subst. exists (A m). split; [constructor|].
    apply IH. lia.
Qed.

Lemma omega_TU n : bis_n n T U.
Proof.
  destruct n as [|n]; [exact I|]. split.
  - intros x' Hx. inversion Hx; subst. eexists. split; [constructor|].
    apply bis_n_refl.
  - intros y' Hy. inversion Hy; subst.
    + eexists. split; [constructor|]. apply bis_n_refl.
    + exists (A n). split; [constructor|]. apply bis_n_A_Om. lia.
Qed.

Lemma not_gfp_TU : ~ bis_gfp T U.
Proof.
  intros [Rel [Hpost HR]].
  assert (Hm : forall m, ~ Rel (A m) Om).
  { induction m as [|m IH]; intro H; destruct (Hpost _ _ H) as [_ Hb].
    - destruct (Hb Om sOm) as [x' [Hx _]]. inversion Hx.
    - destruct (Hb Om sOm) as [x' [Hx Hr]]. inversion Hx; subst. exact (IH Hr). }
  destruct (Hpost _ _ HR) as [_ Hb].
  destruct (Hb Om sUO) as [x' [Hx Hr]]. inversion Hx; subst. exact (Hm _ Hr).
Qed.

Theorem milner : (forall n, bis_n n T U) /\ ~ bis_gfp T U.
Proof. split; [exact omega_TU | exact not_gfp_TU]. Qed.

End Milner.

Print Assumptions eutt_gfp_omega.
Print Assumptions euttI_iff.
Print Assumptions omega_trans.
Print Assumptions omega_bind.
Print Assumptions spin_not_euttT.
Print Assumptions Milner.milner.
