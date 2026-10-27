(** * The recursors' reducts under global renaming

    [redT_gren] and [redt_gren], the recursors' reducts under global
    renaming, with the raw commutations they rewrite by. Split off
    [GRenSyntax] so that they build beside [GRenRecBase]: only reduction
    ([GRenRec]'s [red_gren_both]) needs them. *)
From DeLaM.Typing Require Export GRenSyntax.

Lemma tup_nth_gren t k ξ : tup_nth t⟪ξ⟫ k = (tup_nth t k)⟪ξ⟫.
Proof. revert t; induction k; intros []; cbn; auto. Qed.

Lemma gren_ty_subst_raw M d ξ : gren_ty (subst_ty M d) ξ = subst_ty (gren_ty M ξ) (glren d ξ).
Proof. exact (gren_subst_ty M d ξ). Qed.
Lemma gren_ren_ty_raw (A : ty) r ξ : gren_ty (ren_ty A r) ξ = ren_ty (gren_ty A ξ) r.
Proof. apply gren_ren_ty. Qed.
Lemma gren_ren_tm_raw (t : tm) r ξ : gren_tm (ren_tm t r) ξ = ren_tm (gren_tm t ξ) r.
Proof. apply (proj1 (proj2 gren_ren_all)). Qed.

(** [sup_f]'s children's length and [elim_Wf]'s step telescope (M15b). *)
Lemma gren_tm_subst_raw (t : tm) d ξ : gren_tm (subst_tm t d) ξ = subst_tm (gren_tm t ξ) (glren d ξ).
Proof. exact (gren_subst t d ξ). Qed.
Lemma gren_tmNth_raw l T k cs i ξ :
  gren_tm (tmNth l T k cs i) ξ = tmNth l (gren_ty T ξ) (gren_tm k ξ) (gren_tm cs ξ) (gren_tm i ξ).
Proof.
  unfold tmNth, nthMot, nthBase, nthStep. cbn [gren GRen_tm gren_tm GRen_ty gren_ty].
  change (gren_tm ?x ?ξ) with x⟪ξ⟫; change (gren_ty ?x ?ξ) with x⟪ξ⟫.
  repeat rewrite ?gren_ren_ty', ?gren_ren. reflexivity.
Qed.

(** [sup_i]'s children and [elim_IWf]'s step telescope (M17c). *)
Lemma gren_llift_single_raw (b a : tm) ξ : b[llift (lsingle a)]⟪ξ⟫ = b⟪ξ⟫[llift (lsingle a⟪ξ⟫)].
Proof.
  rewrite gren_subst. apply subst_ext; intros [|[|n]]; rewrite ?llk_glren, ?llk_llift; cbn; auto.
  change (gren_tm ?x ?ξ0) with x⟪ξ0⟫. rewrite gren_ren. reflexivity.
Qed.
Lemma gren_tmDNth_raw l n F cs i ξ :
  gren_tm (tmDNth l n F cs i) ξ = tmDNth l (gren_tm n ξ) (gren_ty F ξ) (gren_tm cs ξ) (gren_tm i ξ).
Proof.
  unfold tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS.
  repeat progress (cbn [gren GRen_tm gren_tm GRen_ty gren_ty]; fold gren_ty gren_tm;
    change (gren_tm ?x ?ξ) with x⟪ξ⟫; change (gren_ty ?x ?ξ) with x⟪ξ⟫;
    rewrite ?gren_ren_ty', ?gren_ren, ?gren_single_ty, ?gren_single).
  reflexivity.
Qed.
Lemma gren_iwfFam_raw l li X A N Ot C a ξ :
  gren_ty (iwfFam l li X A N Ot C a) ξ =
  iwfFam l li (gren_ty X ξ) (gren_ty A ξ) (gren_tm N ξ) (gren_tm Ot ξ) (gren_tm C ξ) (gren_tm a ξ).
Proof.
  unfold iwfFam. cbn [gren_ty]. fold gren_ty gren_tm.
  change (gren_tm ?x ?ξ0) with x⟪ξ0⟫; change (gren_ty ?x ?ξ0) with x⟪ξ0⟫.
  repeat rewrite ?gren_ren_ty', ?gren_ren, ?gren_llift_single_raw. reflexivity.
Qed.

Ltac gpeel_push :=
  repeat first [ rewrite <- peelL_gren | rewrite <- peelG_gren | rewrite <- peelU_gren ];
  unfold rb_br; rewrite tup_nth_gren;
  cbn [goren gren GRen_tm GRen_ty GRen_ctx gren_tm recT rect]; fold gren_ty gren_tm;
  rewrite ?gren_ty_subst_raw;
  rewrite ?gren_ren_ty', ?gren_ren;
  (* [case]'s branch types (M12c): the injection under the single substitution *)
  try match goal with |- context [tmInl _ _ _ _ (var 0)] =>
    cbn [glren lsingle gren_tm gren_ty]; fold gren_ty gren_tm; rewrite ?gren_ren_ty', ?gren_ren end;
  (* [ind_∥∥]'s step type (M16b): the same, under the squash *)
  try match goal with |- context [tmSq _ _ (var 0)] =>
    cbn [glren lsingle gren_tm gren_ty]; fold gren_ty gren_tm;
    rewrite ?gren_ty_subst_raw, ?gren_ren_ty', ?gren_ren end;
  (* [elimW]'s step telescope (M13b): renamings and substitutions nested
     under the payload binders *)
  try match goal with |- context [tmSup _ _ _ _ (var 2) (var 1)] =>
    repeat progress (cbn [glren lsingle gren_tm gren_ty]; fold gren_ty gren_tm;
      rewrite ?gren_ty_subst_raw, ?gren_ren_ty_raw, ?gren_ren_tm_raw, ?gren_ren_ty', ?gren_ren) end;
  try match goal with |- context [tmSupf _ _ _ (var 2) (var 1)] =>
    repeat progress (cbn [glren lsingle gren_tm gren_ty]; fold gren_ty gren_tm;
      rewrite ?gren_ty_subst_raw, ?gren_tm_subst_raw, ?gren_tmNth_raw, ?gren_ren_ty_raw, ?gren_ren_tm_raw,
        ?gren_ren_ty', ?gren_ren) end;
  (* [sup_i]'s children and [elim_IWf]'s step telescope (M17c) *)
  try match goal with |- context [tmSupi _ _ _ _ _ _ _ _ _] =>
    repeat progress (cbn [glren lsingle lsingle2 gren_tm gren_ty]; fold gren_ty gren_tm gcren;
      rewrite ?gren_ty_subst_raw, ?gren_tm_subst_raw, ?gren_tmDNth_raw, ?gren_iwfFam_raw, ?gren_ren_ty_raw,
        ?gren_ren_tm_raw, ?gren_ren_ty', ?gren_ren) end;
  rewrite ?gren_tm_subst_raw; cbn [glren lsingle];
  reflexivity.

Lemma redT_gren l1 l2 rb l Δ c v ξ : redT l1 l2 rb l Δ c = Some v ->
  redT l1 l2 rb⟪ξ⟫ l Δ⟪ξ⟫ c⟪ξ⟫ = Some v⟪ξ⟫.
Proof.
  destruct c; cbn [redT gren GRen_ty gren_ty]; intros E.
  par: (first [discriminate E | apply Some_inj in E; subst v]; f_equal; gpeel_push).
Qed.
Lemma redt_gren l1 l2 rb l Δ T c v ξ : redt l1 l2 rb l Δ T c = Some v ->
  redt l1 l2 rb⟪ξ⟫ l Δ⟪ξ⟫ T⟪ξ⟫ c⟪ξ⟫ = Some v⟪ξ⟫.
Proof.
  destruct c; cbn [redt gren GRen_tm gren_tm]; redt_case T; cbn [gren_ty]; fold gren_ty gren_tm; intros E.
  (* each former's case in a worker (13 s in all) *)
  par: (first [discriminate E | apply Some_inj in E; subst v]; f_equal; gpeel_push).
Qed.
