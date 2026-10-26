(** * Untyped weak-head reduction (ch. 6 §"Reduction Relations")

    Deliberate deviation: the paper's redexes repeat level/type annotations
    ([El (l⊔l') (Π^{l,l'} …)], [app (λ^{l,l'} x:S. t) l l' S …]).  Typing
    only fixes annotations up to [≈] and conversion, so matching them
    syntactically would leave well-typed redexes stuck.  Reduction here
    ignores annotations, as annotations never affect computation.

    The relation, its determinacy and congruences are in [ReductionBase],
    which needs no universe or global substitution lemmas and so builds
    beside them; this file adds stability under renaming. *)
From Coq Require Import Relations Lia.
From DeLaM.Syntax Require Export ReductionBase Universe.

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

(** [elim_W]'s β (M13a): the step's instance and the synthesized induction
    hypothesis commute with renaming. *)
Lemma lsingle_ren_ty (T : ty) s r : T[lsingle s]⟨r⟩ = T⟨rlift r⟩[lsingle s⟨r⟩].
Proof.
  rewrite (subst_ren_ty _ _ (lcons (r2l r) s⟨r⟩)), (ren_subst_ty _ _ _ (lcons (r2l r) s⟨r⟩)); auto.
  all: intros [|n]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; auto; f_equal; lia.
Qed.
Lemma lsingle3_ren (c a f h : tm) r :
  c[lsingle3 a f h]⟨r⟩ = c⟨rlift (rlift (rlift r))⟩[lsingle3 a⟨r⟩ f⟨r⟩ h⟨r⟩].
Proof.
  rewrite (subst_ren _ _ (lcons (lcons (lcons (r2l r) a⟨r⟩) f⟨r⟩) h⟨r⟩)),
          (ren_subst _ _ _ (lcons (lcons (lcons (r2l r) a⟨r⟩) f⟨r⟩) h⟨r⟩)); auto.
  all: intros [|[|[|n]]]; cbn; rlk_simpl; rewrite ?llk_r2l; cbn; rlk_simpl; auto; f_equal; lia.
Qed.
Lemma ren_swap_ty (T : ty) r1 r2 r1' r2' :
  (forall n, rlk r2 (rlk r1 n) = rlk r2' (rlk r1' n)) -> T⟨r1⟩⟨r2⟩ = T⟨r1'⟩⟨r2'⟩.
Proof. intros H; rewrite !ren_ren_comp_ty; apply ren_ext_ty; intros; rewrite !rlk_rcomp; apply H. Qed.
Lemma ren_swap (t : tm) r1 r2 r1' r2' :
  (forall n, rlk r2 (rlk r1 n) = rlk r2' (rlk r1' n)) -> t⟨r1⟩⟨r2⟩ = t⟨r1'⟩⟨r2'⟩.
Proof. intros H; rewrite !ren_ren_comp; apply ren_ext_tm; intros; rewrite !rlk_rcomp; apply H. Qed.
Lemma wIH_ren l l' l'' A B M c a f r :
  (wIH l l' l'' A B M c a f)⟨r⟩ =
  wIH l l' l'' A⟨r⟩ B⟨rlift r⟩ M⟨rlift r⟩ c⟨rlift (rlift (rlift r))⟩ a⟨r⟩ f⟨r⟩.
Proof.
  unfold wIH. change (ren (lam ?l1 ?l2 ?X ?Y) ?r0) with (lam l1 l2 X⟨r0⟩ Y⟨rlift r0⟩).
  rewrite lsingle_ren_ty. f_equal.
  change (ren (tmElimW ?k1 ?k2 ?k3 ?X ?Y ?Z ?u ?v) ?r0)
    with (tmElimW k1 k2 k3 X⟨r0⟩ Y⟨rlift r0⟩ Z⟨rlift r0⟩ u⟨rlift (rlift (rlift r0))⟩ v⟨r0⟩).
  change (ren (app ?u ?k1 ?k2 ?X ?Y ?v) ?r0) with (app u⟨r0⟩ k1 k2 X⟨r0⟩ Y⟨rlift r0⟩ v⟨r0⟩).
  change (tyW ?k1 ?k2 ?X⟨?r0⟩ ?Y⟨rlift ?r0⟩) with (tyW k1 k2 X Y)⟨r0⟩.
  f_equal.
  all: try (apply ren_swap_ty; intros [|[|[|[|n]]]]; rlk_simpl; reflexivity).
  all: try (apply ren_swap; intros [|[|[|[|n]]]]; rlk_simpl; reflexivity).
  f_equal.
  all: try (apply ren_swap; intros [|[|[|[|n]]]]; rlk_simpl; reflexivity).
  - rewrite <- lsingle_ren_ty. apply ren_swap_ty; intros [|n]; rlk_simpl; reflexivity.
  - rewrite !ren_ren_comp_ty. apply ren_ext_ty; intros [|[|n]]; rlk_simpl; reflexivity.
Qed.

(** [nth] and [elim_Wf]'s induction hypothesis (M15a) commute with
    renaming: the shifts inside commute with the lifted renaming. *)
Ltac ren_comm := first [ reflexivity
  | rewrite ?ren_ren_comp_ty, ?ren_ren_comp; first [apply ren_ext_ty | apply ren_ext_tm];
    intros [|[|[|[|[|[|[|?n]]]]]]]; rlk_simpl; first [reflexivity | lia] ].
Lemma tmNth_ren l T k cs i r :
  (tmNth l T k cs i)⟨r⟩ = tmNth l T⟨r⟩ k⟨r⟩ cs⟨r⟩ i⟨r⟩.
Proof.
  unfold tmNth, nthMot, nthBase, nthStep; cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk].
  (* the raw [fix ren_ty] blocks [cbn] leaves made [f_equal] take 12 s *)
  fold ren_ty ren_tm.
  repeat f_equal; rewrite ?rlk_rlift, ?rlk_rup; cbn; try ren_comm.
Qed.
Lemma wfIH_ren l l' A N M c a cs r :
  (wfIH l l' A N M c a cs)⟨r⟩ =
  wfIH l l' A⟨r⟩ N⟨rlift r⟩ M⟨rlift r⟩ c⟨rlift (rlift (rlift r))⟩ a⟨r⟩ cs⟨r⟩.
Proof.
  unfold wfIH. change (ren (lam ?l1 ?l2 ?X ?Y) ?r0) with (lam l1 l2 X⟨r0⟩ Y⟨rlift r0⟩).
  change (ren (tyFin ?n) ?r0) with (tyFin n⟨r0⟩).
  rewrite lsingle_ren. f_equal.
  change (ren (tmElimWf ?k1 ?k2 ?X ?Y ?Z ?u ?v) ?r0)
    with (tmElimWf k1 k2 X⟨r0⟩ Y⟨rlift r0⟩ Z⟨rlift r0⟩ u⟨rlift (rlift (rlift r0))⟩ v⟨r0⟩).
  rewrite tmNth_ren. f_equal; try ren_comm.
  change (tyWf ?k1 ?X⟨?r0⟩ ?Y⟨rlift ?r0⟩) with (tyWf k1 X Y)⟨r0⟩.
  f_equal; try ren_comm.
  rewrite <- lsingle_ren. ren_comm.
Qed.

(** [dnth] and [elim_IWf]'s induction hypothesis (M17b), as [nth] and
    [wfIH]. *)
Ltac rext := intros [|?n]; rlk_simpl; first [reflexivity | lia | revert n; rext].
Ltac ren_comm10 := first [ reflexivity
  | rewrite ?ren_ren_comp_ty, ?ren_ren_comp; first [apply ren_ext_ty | apply ren_ext_tm]; rext ].
(** Congruence down to the renamed leaves, which [ren_comm10] closes. *)
Ltac rhead t := lazymatch t with ?f _ => rhead f | _ => t end.
Ltac ren_cong := lazymatch goal with
  | |- ?x = ?y => let h := rhead x in
      lazymatch h with
      | ren_ty => ren_comm10 | ren_tm => ren_comm10 | @ren => ren_comm10
      | _ => first [reflexivity | f_equal]
      end
  end.
Lemma tmDNth_ren l n F cs i r :
  (tmDNth l n F cs i)⟨r⟩ = tmDNth l n⟨r⟩ F⟨rlift r⟩ cs⟨r⟩ i⟨r⟩.
Proof.
  unfold tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS.
  rewrite ?lsingle_ren_ty, ?lsingle_ren.
  cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  rewrite ?lsingle_ren_ty, ?lsingle_ren.
  cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  repeat ren_cong.
Qed.
Lemma llift_lsingle_ren (t : tm) s r :
  t[llift (lsingle s)]⟨rlift r⟩ = t⟨rlift (rlift r)⟩[llift (lsingle s⟨r⟩)].
Proof.
  rewrite (subst_ren _ _ (lcons (lcons (r2l (rup r)) s⟨r⟩⟨↑⟩) (var 0))),
          (ren_subst _ _ _ (lcons (lcons (r2l (rup r)) s⟨r⟩⟨↑⟩) (var 0))); auto.
  all: intros [|[|n]]; rewrite ?llk_llift; cbn [llk lsingle]; rewrite ?llk_r2l; rlk_simpl; cbn;
    rewrite ?llk_r2l; rlk_simpl; auto.
  all: try (apply ren_swap; intros; rlk_simpl; reflexivity).
  all: try (f_equal; rlk_simpl; lia).
  rewrite Nat.add_0_r, Nat.add_1_r; rlk_simpl; reflexivity.
Qed.
(** [M]'s β reduct (M18b): the instances inside commute with renaming. *)
Ltac lkr := repeat first
  [ progress (rewrite ?llk_llift, ?llk_lren, ?llk_r2l, ?llk_lcomp)
  | progress rlk_simpl
  | progress cbn [llk lsingle lsingle2 lsingle3 lcons' r2l rlk Nat.add] ].
Lemma llift_lsingle_ren_ty (T : ty) s r :
  T[llift (lsingle s)]⟨rlift r⟩ = T⟨rlift (rlift r)⟩[llift (lsingle s⟨r⟩)].
Proof.
  rewrite (subst_ren_ty _ _ (lcons (lcons (r2l (rup r)) s⟨r⟩⟨↑⟩) (var 0))),
          (ren_subst_ty _ _ _ (lcons (lcons (r2l (rup r)) s⟨r⟩⟨↑⟩) (var 0))); auto.
  all: intros [|[|n]]; rewrite ?llk_llift; cbn [llk lsingle]; rewrite ?llk_r2l; rlk_simpl; cbn;
    rewrite ?llk_r2l; rlk_simpl; auto.
  all: try (apply ren_swap; intros; rlk_simpl; reflexivity).
  all: try (f_equal; rlk_simpl; lia).
  rewrite Nat.add_0_r, Nat.add_1_r; rlk_simpl; reflexivity.
Qed.
Lemma llift2_lsingle_ren (t : tm) s r :
  t[llift (llift (lsingle s))]⟨rlift (rlift r)⟩ = t⟨rlift (rlift (rlift r))⟩[llift (llift (lsingle s⟨r⟩))].
Proof.
  rewrite (subst_ren _ _ (lren (llift (llift (lsingle s))) (rlift (rlift r)))),
          (ren_subst _ _ _ (lren (llift (llift (lsingle s))) (rlift (rlift r)))); auto.
  - intros [|[|[|n]]]; lkr; auto;
      first [ cbn [ren_tm]; rewrite ?Nat.add_0_r; f_equal; rlk_simpl; rewrite ?Nat.add_0_r; lia
            | change (ren_tm ?x ?r0) with x⟨r0⟩; ren_cong ].
  - intros n; now rewrite llk_lren.
Qed.
Lemma llift_lsingle2_ren (t : tm) a b r :
  t[llift (lsingle2 a b)]⟨rlift r⟩ = t⟨rlift (rlift (rlift r))⟩[llift (lsingle2 a⟨r⟩ b⟨r⟩)].
Proof.
  rewrite (subst_ren _ _ (lren (llift (lsingle2 a b)) (rlift r))),
          (ren_subst _ _ _ (lren (llift (lsingle2 a b)) (rlift r))); auto.
  - intros [|[|[|n]]]; lkr; auto;
      first [ cbn [ren_tm]; rewrite ?Nat.add_0_r; f_equal; rlk_simpl; rewrite ?Nat.add_0_r; lia
            | change (ren_tm ?x ?r0) with x⟨r0⟩; ren_cong ].
  - intros n; now rewrite llk_lren.
Qed.
Lemma ren_shift_lift (t : tm) r : t⟨↑⟩⟨rlift r⟩ = t⟨r⟩⟨↑⟩.
Proof. apply ren_swap; intros; rlk_simpl; reflexivity. Qed.
Ltac mrext := intros [|?n]; rlk_simpl; rewrite ?Nat.add_1_r, ?Nat.add_0_r; rlk_simpl;
  first [reflexivity | lia | revert n; mrext].
Ltac mren_comm := first [ reflexivity
  | rewrite ?ren_ren_comp_ty, ?ren_ren_comp; first [apply ren_ext_ty | apply ren_ext_tm]; mrext ].
(* Congruence first unless a side is a renaming: a failing [mren_comm]
   rewrites the whole equation (#60) *)
Ltac mcong := lazymatch goal with
  | |- ren _ _ = _ => first [reflexivity | mren_comm | cong_spine]
  | |- _ = ren _ _ => first [reflexivity | mren_comm | cong_spine]
  | |- _ = _ => first [reflexivity | cong_spine | mren_comm] end.
(* Each pass pushes the renaming through the constructors, then rewrites
   every law as often as it applies: a failed [rewrite] traverses the whole
   term, so one law at a time between pushes cost 12 s (#60). *)
Ltac mren_push := repeat progress
  (cbn [ren Ren_tm Ren_ty ren_tm ren_ty]; fold ren_ty ren_tm;
   rewrite ?lsingle_ren_ty, ?lsingle_ren, ?lsingle2_ren, ?lsingle2_ren_ty,
     ?llift_lsingle_ren_ty, ?llift_lsingle_ren, ?llift2_lsingle_ren,
     ?llift_lsingle2_ren, ?ren_shift_lift).
Lemma mOutCorec_ren l l' li X A B C k Y c j y r :
  (mOutCorec l l' li X A B C k Y c j y)⟨r⟩ =
  mOutCorec l l' li X⟨r⟩ A⟨rlift r⟩ B⟨rlift (rlift r)⟩ C⟨rlift (rlift (rlift r))⟩ k Y⟨rlift r⟩
    c⟨rlift (rlift r)⟩ j⟨r⟩ y⟨r⟩.
Proof.
  unfold mOutCorec. mren_push.
  repeat match goal with
    | |- context [ren_ty ?x ?r0] => change (ren_ty x r0) with x⟨r0⟩
    | |- context [ren_tm ?x ?r0] => change (ren_tm x r0) with x⟨r0⟩ end.
  repeat mcong.
Qed.

Lemma iwfIH_ren l li l' X A N Ot C M c a cs r :
  (iwfIH l li l' X A N Ot C M c a cs)⟨r⟩ =
  iwfIH l li l' X⟨r⟩ A⟨r⟩ N⟨rlift r⟩ Ot⟨rlift r⟩ C⟨rlift (rlift r)⟩ M⟨rlift (rlift r)⟩
    c⟨rlift (rlift (rlift r))⟩ a⟨r⟩ cs⟨r⟩.
Proof.
  unfold iwfIH, iwfFam. change (ren (lam ?l1 ?l2 ?X ?Y) ?r0) with (lam l1 l2 X⟨r0⟩ Y⟨rlift r0⟩).
  change (ren (tyFin ?n) ?r0) with (tyFin n⟨r0⟩).
  rewrite lsingle_ren. f_equal.
  change (ren (tmElimIWf ?k1 ?k2 ?k3 ?X ?Y ?Z ?W ?V ?U ?u ?v ?w) ?r0)
    with (tmElimIWf k1 k2 k3 X⟨r0⟩ Y⟨r0⟩ Z⟨rlift r0⟩ W⟨rlift r0⟩ V⟨rlift (rlift r0)⟩ U⟨rlift (rlift r0)⟩
            u⟨rlift (rlift (rlift r0))⟩ v⟨r0⟩ w⟨r0⟩).
  rewrite tmDNth_ren, llift_lsingle_ren. f_equal; try ren_comm.
  f_equal; try ren_comm.
  - rewrite <- lsingle_ren. ren_comm.
  - cbn [ren Ren_tm Ren_ty ren_ty]. fold ren_ty ren_tm.
    f_equal; try ren_comm.
    etransitivity; [apply (ren_swap _ _ _ (rlift r) (rlift ↑)); rext|].
    change (ren_tm ?x ?r0) with x⟨r0⟩. rewrite llift_lsingle_ren. reflexivity.
Qed.

Lemma iwfFam_ren l li X A N Ot C a r :
  (iwfFam l li X A N Ot C a)⟨rlift r⟩ =
  iwfFam l li X⟨r⟩ A⟨r⟩ N⟨rlift r⟩ Ot⟨rlift r⟩ C⟨rlift (rlift r)⟩ a⟨r⟩.
Proof.
  unfold iwfFam. cbn [ren Ren_tm Ren_ty ren_ty]. fold ren_ty ren_tm.
  rewrite llift_lsingle_ren. f_equal; ren_comm.
Qed.

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
