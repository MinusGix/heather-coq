(** * Reduction under global renaming

    The recursor laws of [GRenRecBase] and the recursors' reducts of
    [GRenRedt], which build in parallel, and reduction under global
    renaming, which needs both. *)
From DeLaM.Typing Require Export GRenRecBase GRenRedt.

(** [DVec]'s successor step (M17a): the head's and the tail's instances. *)
Lemma red_dvec_succ_gren l n F ξ :
  red_ty (tyDVec l (succ n) F)⟪ξ⟫ (tySig l l (dvecHd n F) (dvecTl l n F))⟪ξ⟫.
Proof. push_gren. gren_rewrite. push_gren. rewrite !gren_ren. constructor. Qed.

Lemma red_gren_both :
  (forall t u, red t u -> forall ξ, red t⟪ξ⟫ u⟪ξ⟫) /\
  (forall T U, red_ty T U -> forall ξ, red_ty T⟪ξ⟫ U⟪ξ⟫).
Proof.
  apply red_both; intros; cbn [gren GRen_tm gren_tm GRen_ty gren_ty]; fold gren_ty gren_tm;
    change (gren_tm ?x ?ξ) with x⟪ξ⟫; change (gren_ty ?x ?ξ) with x⟪ξ⟫;
    change (gcren ?x ?ξ) with x⟪ξ⟫.
  all: rewrite ?gren_single2, ?gren_single, ?gren_single3, ?gren_wIH, ?gren_wfIH, ?gren_gsingle; try now constructor.
  all: rewrite ?gren_iwfIH; try now constructor.
  all: rewrite ?gren_iwiIH; try now constructor.
  all: rewrite ?gren_mOutCorec; try now constructor.
  all: try (constructor; auto; fail).
  all: first [ constructor; now apply redT_gren | constructor; now apply redt_gren
             | rewrite <- usubst_gren; now constructor
             (* δ: the body's instance *)
             | rewrite gren_subst; now constructor
             (* [Vec]'s successor step: the tail's shifts *)
             | rewrite gren_ren_ty', gren_ren; now constructor
             | now apply red_dvec_succ_gren ].
Qed.

Lemma red_gren t u ξ : red t u -> red t⟪ξ⟫ u⟪ξ⟫.
Proof. intros H; now apply red_gren_both. Qed.
Lemma red_ty_gren T U ξ : red_ty T U -> red_ty T⟪ξ⟫ U⟪ξ⟫.
Proof. intros H; now apply red_gren_both. Qed.
Lemma reds_gren t u ξ : reds t u -> reds t⟪ξ⟫ u⟪ξ⟫.
Proof. unfold reds; induction 1; [constructor|econstructor; eauto using red_gren]. Qed.
Lemma reds_ty_gren T U ξ : reds_ty T U -> reds_ty T⟪ξ⟫ U⟪ξ⟫.
Proof. unfold reds_ty; induction 1; [constructor|econstructor; eauto using red_ty_gren]. Qed.
