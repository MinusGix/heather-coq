(** * Validity of the release of a squashed absurdity (M16_DESIGN.md, M16c)

    [unsquash^l(t) : Empty^l] for [t : ∥Empty^l∥^l]. The relation at a
    squash keeps, on each side alone, a [squash] whose payload is related
    to itself, or a neutral related to itself ([SqNf]). At [Empty] the
    payload's self-relation is a neutral it reduces to, so the release
    steps to the payload and on to that neutral; at a neutral scrutinee
    the release is neutral ([gne_tm_unsq]). The result relation at
    [Empty] compares the two sides' neutrals with nothing ([EmptyRel]), so
    each side is handled alone, as at [ind_∥∥]. *)
From DeLaM.Validity Require Export Squash Empty.

Section Unsq.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** One side: a good term at [∥Empty^l∥] released at a level equivalent to
    [l] reduces to a neutral related to itself. *)
Lemma unsq_side {G Δ l k s} : lwf (gL G) l -> lequiv (gL G) l k -> SqG G Δ l (tyEmpty l) s ->
  exists ν, [ G ; Δ ⊢g tmUnsq k s ⤳* ν : tyEmpty l @ l ] /\ [ G ; Δ ⊢ ν ~ ν : tyEmpty l @ l ].
Proof.
  intros Hw Hk (w & Hr & Hn).
  pose proof (pre_unsq_r ge_typeof ge_notV ge_compt Hk (tmred_wf _ _ _ _ _ _ _ Hr)) as He.
  destruct Hn as [k0 C a Hk0 HC Ha | ν0 Hν0].
  - (* a [squash]: β to the payload, which reduces to a neutral *)
    apply (LRtm_empty Hw) in Ha. destruct Ha as (ν & _ & Hν & _ & Hνν & _).
    exists ν. split; [| exact Hνν].
    split; [exact He | |].
    + eapply reds_trans; [apply reds_unsq, (tmred_red _ _ _ _ _ _ _ Hr)|].
      econstructor; [apply red_unsq_sq | exact (tmred_red _ _ _ _ _ _ _ Hν)].
    + apply eqtm_empty_irr; [exact ge_compt | exact Hw | exact He | exact (gne_tm_typed_l Hνν)].
  - (* a neutral: the release is neutral *)
    pose proof (gne_tm_refl_r (gne_tm_unsq Hk Hν0 Hν0)) as Hνν.
    exists (tmUnsq k ν0). split; [| exact Hνν].
    split; [exact He | apply reds_unsq, (tmred_red _ _ _ _ _ _ _ Hr) |].
    apply eqtm_empty_irr; [exact ge_compt | exact Hw | exact He | exact (gne_tm_typed_l Hνν)].
Qed.

Lemma V_unsq {G Γ l l' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ t t' (tySq l (tyEmpty l)) l -> VTm G Γ (tmUnsq l t) (tmUnsq l' t') (tyEmpty l) l.
Proof.
  intros Hw Hl Vt Δ d d' Hd. pose proof (Vt _ _ _ Hd) as Xt.
  rewrite !subst_tySq, !subst_tyEmpty in Xt. rewrite !subst_tyEmpty, !subst_unsq.
  destruct (LRtm_sq_inv Xt) as [Gt Gt'].
  destruct (unsq_side Hw (lequiv_refl _ _ Hw) Gt) as (ν & Hν & Hνν).
  destruct (unsq_side Hw Hl Gt') as (ν' & Hν' & Hν'ν').
  apply (LRtm_empty Hw). exists ν, ν'. auto.
Qed.

End Unsq.
