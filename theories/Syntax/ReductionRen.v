(** * The reducts' instances under renaming

    The single substitutions in the reducts, the recursors' reducts and
    the eliminators' induction hypotheses commute with local renaming.
    Only [Subst]'s laws are needed, so this builds beside [ReductionBase],
    [GSubst] and [Universe]; [Reduction] uses it for stability of
    reduction under renaming. *)
From Coq Require Import Lia.
From DeLaM.Syntax Require Export Recursor Subst.

Lemma lsingle_ren (b s : tm) r : b[lsingle s]⟨r⟩ = b⟨rlift r⟩[lsingle s⟨r⟩].
Proof.
  rewrite (subst_ren _ _ (lcons (r2l r) s⟨r⟩)), (ren_subst _ _ _ (lcons (r2l r) s⟨r⟩)); auto.
  all: intros [|n]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; auto; f_equal; lia.
Qed.

Lemma lsingle2_ren (z t q : tm) r :
  z[lsingle2 t q]⟨r⟩ = z⟨rlift (rlift r)⟩[lsingle2 t⟨r⟩ q⟨r⟩].
Proof.
  rewrite (subst_ren _ _ (lcons (lcons (r2l r) t⟨r⟩) q⟨r⟩)),
          (ren_subst _ _ _ (lcons (lcons (r2l r) t⟨r⟩) q⟨r⟩)); auto.
  all: intros [|[|n]]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; rewrite ?rlk_rup; cbn;
    auto; f_equal; lia.
Qed.

Lemma lsingle2_ren_ty (M : ty) t q r :
  M[lsingle2 t q]⟨r⟩ = M⟨rlift (rlift r)⟩[lsingle2 t⟨r⟩ q⟨r⟩].
Proof.
  rewrite (subst_ren_ty _ _ (lcons (lcons (r2l r) t⟨r⟩) q⟨r⟩)),
          (ren_subst_ty _ _ _ (lcons (lcons (r2l r) t⟨r⟩) q⟨r⟩)); auto.
  all: intros [|[|n]]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; rewrite ?rlk_rup; cbn;
    auto; f_equal; lia.
Qed.

(** The reducts commute with local renaming (which does not enter the
    code, [Δ] or the index). *)
Lemma tup_nth_ren t k r : tup_nth t⟨r⟩ k = (tup_nth t k)⟨r⟩.
Proof. revert t; induction k; intros []; cbn; auto. Qed.
Lemma peelL_ren b a r : peelL b⟨r⟩ a⟨r⟩ = (peelL b a)⟨r⟩.
Proof. destruct b; cbn; auto. symmetry; apply lsingle_ren. Qed.

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
