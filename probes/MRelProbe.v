(** * The relation at Heather's indexed [M]: a probe (M18a, Q1 and Q2)

    H/docs/kernel-coinduction-design.md §9 Q1 proposes the term relation
    at [M(σ)(j)] as an ω-intersection of observations, [∀ n. MRelₙ], that
    never mentions [corec]'s carrier. This file checks the shape of that
    relation and the four arguments the round rests on, over an abstract
    interface: the terms, the Kripke worlds, the generic equivalence and
    the relations of the signature's components are section variables,
    and each property the development provides for them is a hypothesis,
    named after the lemma or law that gives it there (M18_DESIGN.md, "The
    relation", maps them one by one).

    The relation ([MRn n w m t t'], left-indexed as [IWfRel]):
    - at every depth, [t] and [t'] are generically equal at [M(m)]
      ([geqM]; in the development: both reduce to whnfs related by [≈],
      the first clauses of [WRel]);
    - at depth [n+1], the shapes [fst (out t)], [fst (out t')] are related
      at [S[m]], and in every later world, at related positions, the
      children [snd (out t) p], [snd (out t') p'] are related at depth [n]
      at the child index [o[m, fst (out t), p]].
    [MR := ∀ n, MRn n]. It is defined from the components' relations
    alone, by recursion on [n], so it is a new case of [LR] whose premises
    are [LRiwf]'s (index type, shapes at related indices, positions at
    related shapes, the child index at related positions, the index) and
    nothing else: no carrier, and no change to the reducibility universe.

    Checked:
    - Escape is the depth-0 clause ([MR_escape]). It cannot be dropped:
      the observations alone relate two [corec]s that conversion separates
      (MCoind.v, [zeros_same] against [zeros_u = zeros_n]).
    - The relation is a Kripke PER, closed under conversion (typed
      weak-head expansion) and under a related change of index ([MRn_mono],
      [MRn_conv], [MRn_idx], [MRn_sym], [MRn_trans]).
    - Neutrals are related ([MR_ne]), by induction on the depth, from the
      neutral laws of [out]'s projections.
    - [out]'s validity: related trees have related shapes and, at related
      positions, children related at every depth ([MR_out]): the ∀-depth
      moves inside the Kripke and position quantifiers, so the observation
      is related at [Σ(s : S[m]). Π(p). M(o)] with the full relation
      at the child, which is what [SigRel]/[PiRel] need.
    - [corec]'s validity ([MR_corec]): for related indices and seeds
      related by the carrier's relation, the two [corec]s are related, by
      induction on the depth with the index and the seed generalized. The
      step's validity is its fundamental-theorem hypothesis at the step
      type, whose [+]'s relation holds the carrier's relation on [inl]
      (a new seed: the induction hypothesis), [M]'s full relation on
      [inr] (an existing tree) and neutrals; β and [case]'s β are
      conversions. The carrier's relation is used only here, in the proof:
      it is a premise of the lemma, not part of the relation.

    No axioms: [Print Assumptions] at the end. Standalone: [coqc
    probes/MRelProbe.v], a second. *)

Section MRel.

(** ** The interface *)

Variables (tm wd : Type).

(** Worlds and their order (Kripke weakenings, [kwk], composed by
    [kw_comp]). A term means the same in a later world: the probe leaves
    weakening implicit, as a hypothesis that every relation is monotone. *)
Variable le : wd -> wd -> Prop.
Hypothesis le_refl : forall {w}, le w w.
Hypothesis le_trans : forall {w1 w2 w3}, le w1 w2 -> le w2 w3 -> le w1 w3.

(** Conversion: what the relations are closed under (typed weak-head
    expansion, [LRred_tm], and irrelevance at convertible types,
    [LR_irrel]). An equivalence. *)
Variable conv : tm -> tm -> Prop.
Hypothesis conv_refl : forall {t}, conv t t.
Hypothesis conv_sym : forall {t u}, conv t u -> conv u t.
Hypothesis conv_trans : forall {t u v}, conv t u -> conv u v -> conv t v.

(** The signature's child index [o[m, s, p]], and the two observations of
    a tree: [fst (out t)] and [snd (out t) p] (with their annotations, read
    off [out]'s type). *)
Variables (o : tm -> tm -> tm -> tm) (fstout : tm -> tm) (kid : tm -> tm -> tm).
Hypothesis o_conv : forall {m m1 s s1 p p1}, conv m m1 -> conv s s1 -> conv p p1 ->
  conv (o m s p) (o m1 s1 p1).
Hypothesis fstout_conv : forall {t t1}, conv t t1 -> conv (fstout t) (fstout t1).
Hypothesis kid_conv : forall {t t1 p p1}, conv t t1 -> conv p p1 -> conv (kid t p) (kid t1 p1).

(** The index type's relation ([LRiwf]'s [idxR]): a Kripke PER. *)
Variable idxR : wd -> tm -> tm -> Prop.
Hypothesis idx_mono : forall {w w' m m'}, le w w' -> idxR w m m' -> idxR w' m m'.
Hypothesis idx_sym : forall {w m m'}, idxR w m m' -> idxR w m' m.
Hypothesis idx_trans : forall {w m1 m2 m3}, idxR w m1 m2 -> idxR w m2 m3 -> idxR w m1 m3.
Hypothesis idx_conv : forall {w m m' m1 m1'}, conv m m1 -> conv m' m1' -> idxR w m m' -> idxR w m1 m1'.

(** The shapes' relation at [S[m]] ([domR] at an index): a Kripke PER,
    closed under conversion, the same at related indices (irrelevance:
    [S[m] ~ S[m']] are related types). *)
Variable shR : wd -> tm -> tm -> tm -> Prop.
Hypothesis sh_mono : forall {w w' m s s'}, le w w' -> shR w m s s' -> shR w' m s s'.
Hypothesis sh_sym : forall {w m s s'}, shR w m s s' -> shR w m s' s.
Hypothesis sh_trans : forall {w m s1 s2 s3}, shR w m s1 s2 -> shR w m s2 s3 -> shR w m s1 s3.
Hypothesis sh_conv : forall {w m m1 s s' s1 s1'}, conv m m1 -> conv s s1 -> conv s' s1' ->
  shR w m s s' -> shR w m1 s1 s1'.
Hypothesis sh_idx : forall {w m m1 s s'}, idxR w m m1 -> shR w m s s' -> shR w m1 s s'.

(** The positions' relation at [P[m, s]]: a Kripke PER, closed under
    conversion, the same at related indices and at related shapes. *)
Variable posR : wd -> tm -> tm -> tm -> tm -> Prop.
Hypothesis pos_mono : forall {w w' m s p p'}, le w w' -> posR w m s p p' -> posR w' m s p p'.
Hypothesis pos_sym : forall {w m s p p'}, posR w m s p p' -> posR w m s p' p.
Hypothesis pos_trans : forall {w m s p1 p2 p3}, posR w m s p1 p2 -> posR w m s p2 p3 -> posR w m s p1 p3.
Hypothesis pos_conv : forall {w m m1 s s1 p p' p1 p1'}, conv m m1 -> conv s s1 -> conv p p1 -> conv p' p1' ->
  posR w m s p p' -> posR w m1 s1 p1 p1'.
Hypothesis pos_idx : forall {w m m1 s p p'}, idxR w m m1 -> posR w m s p p' -> posR w m1 s p p'.
Hypothesis pos_sh : forall {w m s s1 p p'}, shR w m s s1 -> posR w m s p p' -> posR w m s1 p p'.

(** The child index at related data ([LRiwf]'s premise on [C]). *)
Hypothesis o_rel : forall {w m m1 s s1 p p1}, idxR w m m1 -> shR w m s s1 -> posR w m s p p1 ->
  idxR w (o m s p) (o m1 s1 p1).

(** The generic equivalence at [M(m)]: [≈] ([geqM]) and [~] ([gneM]), as
    [GenericEqLaws] states them: PERs, monotone ([geq_tm_wk]), closed
    under conversion of the terms ([geq_tm_red]-style expansion) and of
    the type ([geq_tm_conv], at a related index, by [M]'s congruence). *)
Variables (geqM gneM : wd -> tm -> tm -> tm -> Prop).
Hypothesis geq_mono : forall {w w' m t t'}, le w w' -> geqM w m t t' -> geqM w' m t t'.
Hypothesis geq_sym : forall {w m t t'}, geqM w m t t' -> geqM w m t' t.
Hypothesis geq_trans : forall {w m t1 t2 t3}, geqM w m t1 t2 -> geqM w m t2 t3 -> geqM w m t1 t3.
Hypothesis geq_conv : forall {w m m1 t t' t1 t1'}, conv m m1 -> conv t t1 -> conv t' t1' ->
  geqM w m t t' -> geqM w m1 t1 t1'.
Hypothesis geq_idx : forall {w m m1 t t'}, idxR w m m1 -> geqM w m t t' -> geqM w m1 t t'.
Hypothesis gne_geq : forall {w m t t'}, gneM w m t t' -> geqM w m t t'.

(** [out]'s neutral laws: the projections of a neutral [out] are neutral,
    so its shapes are related by the shapes' reflection ([LR_neutral] at
    [S[m]]) and its children, at related positions, are neutral at the
    child index ([gne_tm_app] after [gne_tm_snd]). *)
Hypothesis gne_fstout : forall {w m t t'}, gneM w m t t' -> shR w m (fstout t) (fstout t').
Hypothesis gne_kid : forall {w w' m t t' p p'}, gneM w m t t' -> le w w' ->
  posR w' m (fstout t) p p' -> gneM w' (o m (fstout t) p) (kid t p) (kid t' p').

(** ** The relation *)

Fixpoint MRn (n : nat) (w : wd) (m t t' : tm) : Prop :=
  geqM w m t t' /\
  match n with
  | 0 => True
  | S n =>
      shR w m (fstout t) (fstout t') /\
      forall w', le w w' -> forall p p', posR w' m (fstout t) p p' ->
        MRn n w' (o m (fstout t) p) (kid t p) (kid t' p')
  end.

Definition MR (w : wd) (m t t' : tm) : Prop := forall n, MRn n w m t t'.

Lemma MR_escape w m t t' : MR w m t t' -> geqM w m t t'.
Proof. intros H. exact (proj1 (H 0)). Qed.

(** ** A Kripke PER, closed under conversion and related indices *)

Lemma MRn_mono n : forall w w' m t t', le w w' -> MRn n w m t t' -> MRn n w' m t t'.
Proof.
  induction n as [|n IH]; intros w w' m t t' Hw [Hg H]; (split; [eauto|]); [exact I|].
  destruct H as [Hs Hk]. split; [eauto|].
  intros w'' Hw'' p p' Hp. apply Hk; eauto.
Qed.

Lemma MRn_conv n : forall w m m1 t t' t1 t1', conv m m1 -> conv t t1 -> conv t' t1' ->
  MRn n w m t t' -> MRn n w m1 t1 t1'.
Proof.
  induction n as [|n IH]; intros w m m1 t t' t1 t1' Hm Ht Ht' [Hg H]; (split; [eauto|]); [exact I|].
  destruct H as [Hs Hk]. split; [exact (sh_conv Hm (fstout_conv Ht) (fstout_conv Ht') Hs)|].
  intros w' Hw' p p' Hp.
  assert (Hp0 : posR w' m (fstout t) p p')
    by exact (pos_conv (conv_sym Hm) (conv_sym (fstout_conv Ht)) conv_refl conv_refl Hp).
  exact (IH w' _ _ _ _ _ _ (o_conv Hm (fstout_conv Ht) conv_refl) (kid_conv Ht conv_refl)
    (kid_conv Ht' conv_refl) (Hk w' Hw' p p' Hp0)).
Qed.

(** The position at the left shape, related to itself. *)
Lemma pos_refl_l {w m s p p'} : posR w m s p p' -> posR w m s p p.
Proof. intros H. exact (pos_trans H (pos_sym H)). Qed.

Lemma sh_refl_l {w m s s'} : shR w m s s' -> shR w m s s.
Proof. intros H. exact (sh_trans H (sh_sym H)). Qed.

Lemma MRn_idx n : forall w m m1 t t', idxR w m m1 -> MRn n w m t t' -> MRn n w m1 t t'.
Proof.
  induction n as [|n IH]; intros w m m1 t t' Hm [Hg H]; (split; [eauto|]); [exact I|].
  destruct H as [Hs Hk]. split; [eauto|].
  intros w' Hw' p p' Hp.
  assert (Hp0 : posR w' m (fstout t) p p') by exact (pos_idx (idx_sym (idx_mono Hw' Hm)) Hp).
  exact (IH w' _ _ _ _ (o_rel (idx_mono Hw' Hm) (sh_refl_l (sh_mono Hw' Hs)) (pos_refl_l Hp0))
    (Hk w' Hw' p p' Hp0)).
Qed.

Lemma MRn_sym n : forall w m t t', idxR w m m -> MRn n w m t t' -> MRn n w m t' t.
Proof.
  induction n as [|n IH]; intros w m t t' Hm [Hg H]; (split; [eauto|]); [exact I|].
  destruct H as [Hs Hk]. split; [eauto|].
  intros w' Hw' p' p Hp'.
  (* [p'] at the right shape; move it to the left one and flip *)
  assert (Hs' : shR w' m (fstout t) (fstout t')) by eauto.
  assert (Hp : posR w' m (fstout t) p p').
  { apply pos_sym. apply (pos_sh (sh_sym Hs')). exact Hp'. }
  assert (Hm' : idxR w' m m) by eauto.
  assert (Hc := IH w' _ _ _ (o_rel Hm' (sh_refl_l Hs') (pos_refl_l Hp)) (Hk w' Hw' p p' Hp)).
  exact (MRn_idx n _ _ _ _ _ (o_rel Hm' Hs' Hp) Hc).
Qed.

Lemma MRn_trans n : forall w m t1 t2 t3, idxR w m m ->
  MRn n w m t1 t2 -> MRn n w m t2 t3 -> MRn n w m t1 t3.
Proof.
  induction n as [|n IH]; intros w m t1 t2 t3 Hm [Hg12 H12] [Hg23 H23]; (split; [eauto|]); [exact I|].
  destruct H12 as [Hs12 Hk12], H23 as [Hs23 Hk23]. split; [eauto|].
  intros w' Hw' p1 p3 Hp13.
  assert (Hm' : idxR w' m m) by eauto.
  assert (Hs12' : shR w' m (fstout t1) (fstout t2)) by eauto.
  assert (Hp11 : posR w' m (fstout t1) p1 p1) by (eapply pos_refl_l; exact Hp13).
  assert (Hc12 := Hk12 w' Hw' p1 p1 Hp11).
  assert (Hp13' : posR w' m (fstout t2) p1 p3) by (apply (pos_sh Hs12'); exact Hp13).
  assert (Hc23 := Hk23 w' Hw' p1 p3 Hp13').
  assert (Ho : idxR w' (o m (fstout t2) p1) (o m (fstout t1) p1)).
  { apply o_rel; [exact Hm'|apply sh_sym; exact Hs12'|apply (pos_sh Hs12'); exact Hp11]. }
  apply (IH w' _ _ (kid t2 p1)).
  - apply o_rel; [exact Hm'|eapply sh_refl_l; exact Hs12'|exact Hp11].
  - exact Hc12.
  - exact (MRn_idx n _ _ _ _ _ Ho Hc23).
Qed.

Lemma MR_mono w w' m t t' : le w w' -> MR w m t t' -> MR w' m t t'.
Proof. intros Hw H n. exact (MRn_mono n _ _ _ _ _ Hw (H n)). Qed.
Lemma MR_conv w m m1 t t' t1 t1' : conv m m1 -> conv t t1 -> conv t' t1' -> MR w m t t' -> MR w m1 t1 t1'.
Proof. intros Hm Ht Ht' H n. exact (MRn_conv n _ _ _ _ _ _ _ Hm Ht Ht' (H n)). Qed.
Lemma MR_sym w m t t' : idxR w m m -> MR w m t t' -> MR w m t' t.
Proof. intros Hm H n. exact (MRn_sym n _ _ _ _ Hm (H n)). Qed.
Lemma MR_trans w m t1 t2 t3 : idxR w m m -> MR w m t1 t2 -> MR w m t2 t3 -> MR w m t1 t3.
Proof. intros Hm H12 H23 n. exact (MRn_trans n _ _ _ _ _ Hm (H12 n) (H23 n)). Qed.

(** ** Neutrals *)

Lemma MRn_ne n : forall w m t t', gneM w m t t' -> MRn n w m t t'.
Proof.
  induction n as [|n IH]; intros w m t t' H; (split; [eauto|]); [exact I|].
  split; [eauto|]. intros w' Hw' p p' Hp. apply IH. eapply gne_kid; eauto.
Qed.

Lemma MR_ne w m t t' : gneM w m t t' -> MR w m t t'.
Proof. intros H n. exact (MRn_ne n _ _ _ _ H). Qed.

(** ** [out] *)

Lemma MR_out w m t t' : MR w m t t' ->
  shR w m (fstout t) (fstout t') /\
  forall w', le w w' -> forall p p', posR w' m (fstout t) p p' ->
    MR w' (o m (fstout t) p) (kid t p) (kid t' p').
Proof.
  intros H. split; [exact (proj1 (proj2 (H 1)))|].
  intros w' Hw' p p' Hp n. exact (proj2 (proj2 (H (S n))) w' Hw' p p' Hp).
Qed.

(** ** [corec]

    One coalgebra, fixed: [cr m x] is [corec(…; X; c; m; x)], [stp m x]
    its step's instance [c[m, x]], [fst_]/[sndapp] the step's projections
    and the application of its second at a position, [caseM i u] the
    reduct's [case(u; y. corec(…; i; y); t. t)] at the child index [i],
    [inl]/[inr] the injections. [X w m x x'] is the carrier's relation at
    [X[m]], given by the validity of [X] (any level: it is never part of a
    type's relation). *)
Variables (cr stp : tm -> tm -> tm) (fst_ : tm -> tm) (sndapp : tm -> tm -> tm)
  (caseM : tm -> tm -> tm) (inl inr : tm -> tm).
Variable X : wd -> tm -> tm -> tm -> Prop.
Hypothesis X_mono : forall {w w' m x x'}, le w w' -> X w m x x' -> X w' m x x'.

(** β under [out] (the kernel's [m_out_corec]), as conversions, and
    [case]'s β. *)
Hypothesis beta_fst : forall {m x}, conv (fstout (cr m x)) (fst_ (stp m x)).
Hypothesis beta_kid : forall {m x p},
  conv (kid (cr m x) p) (caseM (o m (fst_ (stp m x)) p) (sndapp (stp m x) p)).
Hypothesis case_inl : forall {i y}, conv (caseM i (inl y)) (cr i y).
Hypothesis case_inr : forall {i t}, conv (caseM i (inr t)) t.
Hypothesis caseM_conv : forall {i i1 u u1}, conv i i1 -> conv u u1 -> conv (caseM i u) (caseM i1 u1).

(** [case] on a neutral sum is neutral (its neutral law: the scrutinee
    neutral, the branches compared at the child index). [gneSum w i u u']
    is [~] at [X[i] + M(i)]. *)
Variable gneSum : wd -> tm -> tm -> tm -> Prop.
Hypothesis case_ne : forall {w i i' u u'}, idxR w i i' -> gneSum w i u u' ->
  gneM w i (caseM i u) (caseM i' u').

(** The generic congruence of two [corec]s of this coalgebra at related
    indices and related seeds: the kernel's [corec ≈ corec] arm (carrier,
    step, seed), from the escape of the carrier's, the step's and the
    seed's validity, at the type's index. *)
Hypothesis geq_corec : forall {w m m' x x'}, idxR w m m' -> X w m x x' -> geqM w m (cr m x) (cr m' x').

(** The relation at the step's [+] at the child index [i]: [SumRel]'s
    three whnf cases, each side reducing to its whnf. *)
Definition SumR (w : wd) (i u u' : tm) : Prop :=
  (exists y y', conv u (inl y) /\ conv u' (inl y') /\ X w i y y') \/
  (exists t t', conv u (inr t) /\ conv u' (inr t') /\ MR w i t t') \/
  gneSum w i u u'.

(** The step's validity at related indices and seeds, read through [Σ]'s
    and [Π]'s relations at the step type
    [Σ(s : S[m]). Π(p : P[m, s]). X[o] + M(o)]. *)
Hypothesis step_valid : forall {w m m' x x'}, idxR w m m' -> X w m x x' ->
  shR w m (fst_ (stp m x)) (fst_ (stp m' x')) /\
  forall w', le w w' -> forall p p', posR w' m (fst_ (stp m x)) p p' ->
    SumR w' (o m (fst_ (stp m x)) p) (sndapp (stp m x) p) (sndapp (stp m' x') p').

Lemma MRn_corec n : forall w m m' x x', idxR w m m' -> X w m x x' -> MRn n w m (cr m x) (cr m' x').
Proof.
  induction n as [|n IH]; intros w m m' x x' Hm Hx; (split; [eauto|]); [exact I|].
  destruct (step_valid Hm Hx) as [Hs Hk].
  split.
  { exact (sh_conv conv_refl (conv_sym beta_fst) (conv_sym beta_fst) Hs). }
  intros w' Hw' p p' Hp.
  (* the positions at the step's shape; the child's index computed there *)
  assert (Hp0 : posR w' m (fst_ (stp m x)) p p').
  { exact (pos_conv conv_refl beta_fst conv_refl conv_refl Hp). }
  set (i := o m (fst_ (stp m x)) p). set (i' := o m' (fst_ (stp m' x')) p').
  assert (Hi : idxR w' i i') by (apply o_rel; eauto).
  assert (Hc : MRn n w' i (caseM i (sndapp (stp m x) p)) (caseM i' (sndapp (stp m' x') p'))).
  { destruct (Hk w' Hw' p p' Hp0) as [(y & y' & Hy & Hy' & HX)|[(t & t' & Ht & Ht' & HM)|Hne]].
    - (* new seeds: the induction hypothesis at the child index *)
      eapply MRn_conv; [apply conv_refl| | |exact (IH w' i i' y y' Hi HX)].
      + exact (conv_sym (conv_trans (caseM_conv conv_refl Hy) case_inl)).
      + exact (conv_sym (conv_trans (caseM_conv conv_refl Hy') case_inl)).
    - (* existing trees: the full relation at the child index *)
      eapply MRn_conv; [apply conv_refl| | |exact (HM n)].
      + exact (conv_sym (conv_trans (caseM_conv conv_refl Ht) case_inr)).
      + exact (conv_sym (conv_trans (caseM_conv conv_refl Ht') case_inr)).
    - exact (MRn_ne n _ _ _ _ (case_ne Hi Hne)). }
  eapply MRn_conv; [| | |exact Hc].
  - unfold i. apply o_conv; [apply conv_refl|apply conv_sym, beta_fst|apply conv_refl].
  - apply conv_sym, beta_kid.
  - apply conv_sym, beta_kid.
Qed.

Lemma MR_corec w m m' x x' : idxR w m m' -> X w m x x' -> MR w m (cr m x) (cr m' x').
Proof. intros Hm Hx n. exact (MRn_corec n _ _ _ _ _ Hm Hx). Qed.

End MRel.

Print Assumptions MR_corec.
Print Assumptions MR_out.
Print Assumptions MR_ne.
Print Assumptions MR_trans.
