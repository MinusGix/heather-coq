(** * How [nth] computes, untyped (M15_DESIGN.md, M15a)

    The reductions of [nth] that [WfNth]'s validity lemmas use: they need
    no logical relation, so they build beside it instead of after it. *)
From DeLaM.Typing Require Export PresupAux.

(** Equations of shifted and substituted types, pointwise. *)
Ltac teq := repeat first [ rewrite ren_as_r2l_ty | rewrite ren_as_r2l ];
  repeat first [ rewrite subst_comp_ty | rewrite subst_comp ];
  first [ apply subst_ext_ty | apply subst_ext
        | apply subst_id_ty; [assumption|] | apply subst_id; [assumption|]
        | symmetry; apply subst_id_ty; [assumption|] | symmetry; apply subst_id; [assumption|] ];
  intros [|[|[|[|[|[|[|[|?n]]]]]]]]; unfold lsucc; pw;
  try solve [apply ren_as_r2l | symmetry; apply ren_as_r2l].

(** ** How [nth] computes, untyped

    [elim_Wf]'s motive at the spine compares eliminations at terms with
    the same weak-head normal form as an [nth] (M15_DESIGN.md): at a
    successor length and an [inl] or [inr] index, [nth] reduces to the
    head or to [nth] at the tail; at a zero or neutral length, or a neutral
    index, to a neutral. *)

Lemma reds_eq a b : a = b -> reds a b.
Proof using . intros ->; constructor. Qed.

Ltac nth_eq := unfold tmNth, nthMot, nthBase, nthStep; push_ren; push_subst;
  shift_cancel; pw; shift_cancel;
  repeat change (ren_ty ?x ?r) with x⟨r⟩; repeat change (ren_tm ?x ?r) with x⟨r⟩; pw;
  repeat f_equal; shift_cancel; try reflexivity; try teq.

Section NthReds.
Context (l : lvl) (T : ty) (NT : nfty T).

Definition nthCase (m c0 : tm) : tm -> tm :=
  tmCase lzero lzero l (tyUnit lzero) (tyFin m) T⟨↑⟩
    (tmFst l l T⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩ m⟨↑⟩⟨↑⟩) c0⟨↑⟩)
    (tmNth l T⟨↑⟩ m⟨↑⟩ (tmSnd l l T⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩ m⟨↑⟩⟨↑⟩) c0⟨↑⟩) (var 0)).

Lemma nth_reds_cong {k k' c0 i} : reds k k' -> reds (tmNth l T k c0 i)
  (app (app (natrec l (nthMot l T) (nthBase l T) (nthStep l T) k') l l (tyVec l T k)
          (tyPi lzero l (tyFin k⟨↑⟩) T⟨↑⟩⟨↑⟩) c0) lzero l (tyFin k) T⟨↑⟩ i).
Proof using . intros H. unfold tmNth. now apply reds_app, reds_app, reds_natrec. Qed.

Lemma nth_reds_succ {k m c0 i} : nftm m -> nftm c0 -> reds k (succ m) ->
  reds (tmNth l T k c0 i) (nthCase m c0 i).
Proof using NT.
  intros Nm Nc Hk. eapply reds_trans; [exact (nth_reds_cong Hk)|].
  eapply Relation_Operators.rt1n_trans; [apply red_app, red_app, red_natrec_succ|].
  unfold nthStep at 1. rewrite !subst_lam.
  eapply Relation_Operators.rt1n_trans; [apply red_app, red_beta|].
  rewrite !subst_lam.
  eapply Relation_Operators.rt1n_trans; [apply red_beta|].
  apply reds_eq. unfold nthCase. nth_eq.
Qed.

Lemma nth_reds_inl {k m c0 i k1 k2 C D u} : nftm m -> nftm c0 -> reds k (succ m) ->
  reds i (tmInl k1 k2 C D u) -> reds (tmNth l T k c0 i) (tmFst l l T (tyVec l T⟨↑⟩ m⟨↑⟩) c0).
Proof using NT.
  intros Nm Nc Hk Hi. eapply reds_trans; [exact (nth_reds_succ Nm Nc Hk)|].
  unfold nthCase. eapply reds_trans; [apply reds_case, Hi|].
  eapply Relation_Operators.rt1n_trans; [apply red_case_inl|].
  apply reds_eq. push_subst. repeat f_equal; try teq.
Qed.

Lemma nth_reds_inr {k m c0 i k1 k2 C D j} : nftm m -> nftm c0 -> reds k (succ m) ->
  reds i (tmInr k1 k2 C D j) ->
  reds (tmNth l T k c0 i) (tmNth l T m (tmSnd l l T (tyVec l T⟨↑⟩ m⟨↑⟩) c0) j).
Proof using NT.
  intros Nm Nc Hk Hi. eapply reds_trans; [exact (nth_reds_succ Nm Nc Hk)|].
  unfold nthCase. eapply reds_trans; [apply reds_case, Hi|].
  eapply Relation_Operators.rt1n_trans; [apply red_case_inr|].
  apply reds_eq. rewrite subst_tmNth. push_subst. repeat f_equal; try teq.
Qed.

Lemma nth_reds_case_ne {k m c0 i ν} : nftm m -> nftm c0 -> reds k (succ m) -> reds i ν -> whne ν ->
  exists X, reds (tmNth l T k c0 i) X /\ whne X.
Proof using NT.
  intros Nm Nc Hk Hi Hν. eexists. split; [eapply reds_trans; [exact (nth_reds_succ Nm Nc Hk) | apply reds_case, Hi]|].
  now apply whne_case.
Qed.

Lemma nth_reds_zero {k c0 i ν} : reds k zero -> reds i ν -> whne ν ->
  exists X, reds (tmNth l T k c0 i) X /\ whne X.
Proof using .
  intros Hk Hi Hν. eexists. split.
  - eapply reds_trans; [exact (nth_reds_cong Hk)|].
    eapply Relation_Operators.rt1n_trans; [apply red_app, red_app, red_natrec_zero|].
    unfold nthBase at 1.
    eapply Relation_Operators.rt1n_trans; [apply red_app, red_beta|].
    rewrite !subst_lam.
    eapply Relation_Operators.rt1n_trans; [apply red_beta|].
    push_subst. pw. apply reds_elimEmpty. exact Hi.
  - now apply whne_elimEmpty.
Qed.

Lemma nth_reds_ne {k c0 i ν} : reds k ν -> whne ν -> exists X, reds (tmNth l T k c0 i) X /\ whne X.
Proof using .
  intros Hk Hν. eexists. split; [exact (nth_reds_cong Hk)|]. now apply whne_app, whne_app, whne_natrec.
Qed.

End NthReds.
