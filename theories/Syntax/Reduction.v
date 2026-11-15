(** * Untyped weak-head reduction (ch. 6 §"Reduction Relations")

    Deliberate deviation: the paper's redexes repeat level/type annotations
    ([El (l⊔l') (Π^{l,l'} …)], [app (λ^{l,l'} x:S. t) l l' S …]).  Typing
    only fixes annotations up to [≈] and conversion, so matching them
    syntactically would leave well-typed redexes stuck.  Reduction here
    ignores annotations, as annotations never affect computation.

    The relation, its determinacy and congruences are in [ReductionBase],
    which needs no universe or global substitution lemmas and so builds
    beside them; the instances' commutations with renaming are in
    [ReductionRen], which needs only [Subst]; this file adds stability
    under renaming. *)
From Coq Require Import Relations Lia.
From DeLaM.Syntax Require Export ReductionBase ReductionRen Universe.

Lemma peelU_ren b l r : peelU b⟨r⟩ l = (peelU b l)⟨r⟩.
Proof. destruct b; cbn; auto. apply usubst_ren. Qed.
Lemma peelG_ren b o r : peelG b⟨r⟩ o = (peelG b o)⟨r⟩.
Proof. destruct b; cbn; auto. apply gsubst_ren. Qed.

Ltac peel_push r :=
  repeat first [ rewrite <- peelL_ren | rewrite <- peelG_ren | rewrite <- peelU_ren ];
  unfold rb_br; rewrite tup_nth_ren; reflexivity.

Lemma redT_ren l1 l2 rb l Δ c v r : redT l1 l2 rb l Δ c = Some v ->
  redT l1 l2 rb⟨r⟩ l Δ c = Some v⟨r⟩.
Proof. destruct c; cbn [redT]; intros [= <-]; f_equal; peel_push r. Qed.
Lemma redt_ren l1 l2 rb l Δ T c v r : redt l1 l2 rb l Δ T c = Some v ->
  redt l1 l2 rb⟨r⟩ l Δ T c = Some v⟨r⟩.
Proof.
  destruct c; cbn [redt]; redt_case T; intros E; first [discriminate E | apply Some_inj in E; subst v]; f_equal; peel_push r.
Qed.

Lemma red_ubeta_ren n l T b ls r : length ls = n -> red (uapp (ulam n l T⟨r⟩ b⟨r⟩) ls) b[uext ls lvar]ᵤ⟨r⟩.
Proof. intros; rewrite <- usubst_ren. now constructor. Qed.

(** [Vec]'s successor step (M14a): the tail's shifts commute with renaming. *)
Lemma red_vec_succ_ren l A n r :
  red_ty (tyVec l A (succ n))⟨r⟩ (tySig l l A (tyVec l A⟨↑⟩ n⟨↑⟩))⟨r⟩.
Proof.
  change (red_ty (tyVec l A⟨r⟩ (succ n⟨r⟩)) (tySig l l A⟨r⟩ (tyVec l A⟨↑⟩⟨rlift r⟩ n⟨↑⟩⟨rlift r⟩))).
  rewrite (ren_swap_ty A ↑ (rlift r) r ↑), (ren_swap n ↑ (rlift r) r ↑) by (intros; rlk_simpl; lia).
  constructor.
Qed.

(** [DVec]'s successor step (M17a): the head's and the tail's instances
    commute with renaming. *)
Lemma red_dvec_succ_ren l n F r :
  red_ty (tyDVec l (succ n) F)⟨r⟩ (tySig l l (dvecHd n F) (dvecTl l n F))⟨r⟩.
Proof.
  assert (E : (tySig l l (dvecHd n F) (dvecTl l n F))⟨r⟩
              = tySig l l (dvecHd n⟨r⟩ F⟨rlift r⟩) (dvecTl l n⟨r⟩ F⟨rlift r⟩)).
  { change ((tySig l l ?A ?B)⟨r⟩) with (tySig l l A⟨r⟩ B⟨rlift r⟩).
    rewrite !lsingle_ren_ty. f_equal.
    change ((tyDVec l ?m ?G)⟨?r0⟩) with (tyDVec l m⟨r0⟩ G⟨rlift r0⟩).
    rewrite lsingle_ren_ty. cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
    repeat (f_equal; try ren_comm). all: rlk_simpl; reflexivity. }
  rewrite E. constructor.
Qed.

Lemma red_ren_both :
  (forall t u, red t u -> forall r, red t⟨r⟩ u⟨r⟩) /\
  (forall T U, red_ty T U -> forall r, red_ty T⟨r⟩ U⟨r⟩).
Proof.
  apply red_both; intros; cbn;
    first [ now constructor
          | now apply red_vec_succ_ren
          | now apply red_dvec_succ_ren
          | now apply red_ubeta_ren
          | constructor; first [now apply redT_ren | now apply redt_ren]
          | cbn [ren_tm]; rewrite <- gsubst_ren; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩;
            first [rewrite lsingle2_ren | rewrite lsingle_ren]; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩; rewrite lsingle3_ren, wIH_ren; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩; rewrite lsingle3_ren, wfIH_ren; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩; rewrite lsingle3_ren, iwfIH_ren; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩; rewrite lsingle3_ren, iwiIH_ren; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩; rewrite mOutCorec_ren; constructor
          (* δ: the body's instance *)
          | erewrite subst_ren by (intros; apply llk_lren); constructor ].
Qed.

Lemma red_ren t u r : red t u -> red t⟨r⟩ u⟨r⟩.
Proof. intros H; now apply red_ren_both. Qed.
Lemma red_ty_ren T U r : red_ty T U -> red_ty T⟨r⟩ U⟨r⟩.
Proof. intros H; now apply red_ren_both. Qed.
Lemma reds_ren t u r : reds t u -> reds t⟨r⟩ u⟨r⟩.
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto using red_ren]. Qed.
Lemma reds_ty_ren T U r : reds_ty T U -> reds_ty T⟨r⟩ U⟨r⟩.
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto using red_ty_ren]. Qed.
