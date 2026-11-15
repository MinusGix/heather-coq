(** * The reducts under universe substitution

    [redT_usubst] and [redt_usubst], with the commutations they rewrite
    by. Split off [RecLaws]: they need only [Universe], so they build
    beside the typing rules ([RecSpec], [Declarative]). *)
From DeLaM.Syntax Require Export Recursor Universe.

Section USubst.

Lemma tup_nth_usubst t k φ : tup_nth (usubst_tm t φ) k = usubst_tm (tup_nth t k) φ.
Proof. revert t; induction k; intros []; cbn; auto. Qed.

Lemma usingle_uup φ l n : lvsubst (uup φ n) (usingle (lvsubst l φ)) = lvsubst (usingle l n) φ.
Proof.
  destruct n; cbn; auto. rewrite (lvren_lvsubst _ _ _ lvar) by reflexivity.
  apply lvsubst_id; reflexivity.
Qed.

Lemma peelU_usubst b l φ : peelU (usubst_tm b φ) (lvsubst l φ) = usubst_tm (peelU b l) φ.
Proof.
  destruct b; cbn [usubst_tm peelU]; auto.
  transitivity (usubst_tm b (fun n => lvsubst (usingle l n) φ)).
  - apply (proj1 (proj2 usubst_usubst_all)); intros n; symmetry; apply usingle_uup.
  - symmetry; apply (proj1 (proj2 usubst_usubst_all)); reflexivity.
Qed.
Lemma peelG_usubst b o φ : peelG (usubst_tm b φ) (gousubst o φ) = usubst_tm (peelG b o) φ.
Proof.
  destruct b; cbn [usubst_tm peelG]; auto.
  symmetry; rewrite (proj1 (proj2 usubst_gsubst_all) _ _ _ (fun i => gousubst (gsingle o i) φ)) by auto.
  apply (proj1 (proj2 gsubst_ext_all)). intros [|i]; reflexivity.
Qed.
Lemma peelL_usubst b a φ : peelL (usubst_tm b φ) (usubst_tm a φ) = usubst_tm (peelL b a) φ.
Proof.
  destruct b; cbn [usubst_tm peelL]; auto.
  symmetry; apply (proj1 (proj2 usubst_subst_all)). intros [|n]; cbn; auto.
Qed.

(** The reducts. *)

Lemma rb_br_usubst rb k φ : rb_br (usubst_tm rb φ) k = usubst_tm (rb_br rb k) φ.
Proof. apply tup_nth_usubst. Qed.

Lemma usubst_lsingle_ty M a φ : usubst_ty (subst_ty M (lsingle a)) φ = subst_ty (usubst_ty M φ) (lsingle (usubst_tm a φ)).
Proof. apply (proj1 usubst_subst_all). intros [|n]; reflexivity. Qed.
Lemma usubst_lsingle_tm (b a : tm) φ : usubst_tm (subst_tm b (lsingle a)) φ = subst_tm (usubst_tm b φ) (lsingle (usubst_tm a φ)).
Proof. apply (proj1 (proj2 usubst_subst_all)). intros [|n]; reflexivity. Qed.
Lemma usubst_lsucc_ty M φ : usubst_ty (subst_ty M lsucc) φ = subst_ty (usubst_ty M φ) lsucc.
Proof. apply (proj1 usubst_subst_all). intros [|[|n]]; reflexivity. Qed.
Lemma usubst_lsingle2_ty M t q φ :
  usubst_ty (subst_ty M (lsingle2 t q)) φ = subst_ty (usubst_ty M φ) (lsingle2 (usubst_tm t φ) (usubst_tm q φ)).
Proof. apply (proj1 usubst_subst_all). intros [|[|n]]; reflexivity. Qed.

(** [J]'s motive context shifts its carrier and point (M11b). *)
Lemma usubst_shift_ty (T : ty) φ : usubst_ty T⟨↑⟩ φ = (usubst_ty T φ)⟨↑⟩.
Proof. exact (proj1 usubst_ren_all T _ φ). Qed.
Lemma usubst_shift (t : tm) φ : usubst_tm t⟨↑⟩ φ = (usubst_tm t φ)⟨↑⟩.
Proof. exact (proj1 (proj2 usubst_ren_all) t _ φ). Qed.
(** [case]'s branch types (M12c) lift their motive past the payload. *)
Lemma usubst_liftshift_ty (T : ty) φ : usubst_ty T⟨rlift ↑⟩ φ = (usubst_ty T φ)⟨rlift ↑⟩.
Proof. exact (proj1 usubst_ren_all T _ φ). Qed.

(** [elimW]'s step telescope (M13b) renames under two and three binders. *)
Lemma usubst_ren_ty (T : ty) r φ : usubst_ty (ren_ty T r) φ = ren_ty (usubst_ty T φ) r.
Proof. exact (proj1 usubst_ren_all T _ φ). Qed.
Lemma usubst_ren_tm (t : tm) r φ : usubst_tm (ren_tm t r) φ = ren_tm (usubst_tm t φ) r.
Proof. exact (proj1 (proj2 usubst_ren_all) t _ φ). Qed.

(** [elim_Wf]'s step telescope (M15b) holds an [nth]. *)
Lemma usubst_tmNth_r l T k cs i φ :
  usubst_tm (tmNth l T k cs i) φ =
  tmNth (lvsubst l φ) (usubst_ty T φ) (usubst_tm k φ) (usubst_tm cs φ) (usubst_tm i φ).
Proof.
  unfold tmNth, nthMot, nthBase, nthStep; cbn [usubst_tm usubst_ty lvsubst].
  rewrite ?usubst_ren_ty, ?usubst_ren_tm. reflexivity.
Qed.

(** [sup_i]'s children and [elim_IWf]'s step telescope (M17c) hold an
    [iwfFam] and a [dnth]. *)
Lemma usubst_llift_single_r (b a : tm) φ :
  usubst_tm (subst_tm b (llift (lsingle a))) φ = subst_tm (usubst_tm b φ) (llift (lsingle (usubst_tm a φ))).
Proof. apply (proj1 (proj2 usubst_subst_all)). intros [|[|n]]; rewrite ?llk_llift; cbn; rewrite ?usubst_ren_tm; reflexivity. Qed.
Lemma usubst_tmDNth_r l n F cs i φ :
  usubst_tm (tmDNth l n F cs i) φ =
  tmDNth (lvsubst l φ) (usubst_tm n φ) (usubst_ty F φ) (usubst_tm cs φ) (usubst_tm i φ).
Proof.
  unfold tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS;
    repeat progress (cbn [usubst_tm usubst_ty lvsubst];
      rewrite ?usubst_lsingle_ty, ?usubst_ren_ty, ?usubst_ren_tm).
  reflexivity.
Qed.
Lemma usubst_iwfFam_r l li X A N Ot C a φ :
  usubst_ty (iwfFam l li X A N Ot C a) φ =
  iwfFam (lvsubst l φ) (lvsubst li φ) (usubst_ty X φ) (usubst_ty A φ) (usubst_tm N φ)
    (usubst_tm Ot φ) (usubst_tm C φ) (usubst_tm a φ).
Proof.
  unfold iwfFam. cbn [usubst_tm usubst_ty lvsubst].
  rewrite ?usubst_ren_ty, ?usubst_ren_tm, ?usubst_llift_single_r. reflexivity.
Qed.

(** [sup_ii]'s children and [elim_IWi]'s step telescope (M19c) hold an
    [iwiFam]. *)
Lemma usubst_llift_single_ty_r (B : ty) a φ :
  usubst_ty (subst_ty B (llift (lsingle a))) φ = subst_ty (usubst_ty B φ) (llift (lsingle (usubst_tm a φ))).
Proof. apply (proj1 usubst_subst_all). intros [|[|n]]; rewrite ?llk_llift; cbn; rewrite ?usubst_ren_tm; reflexivity. Qed.
Lemma usubst_llift2_single_r (b a : tm) φ :
  usubst_tm (subst_tm b (llift (llift (lsingle a)))) φ =
  subst_tm (usubst_tm b φ) (llift (llift (lsingle (usubst_tm a φ)))).
Proof.
  apply (proj1 (proj2 usubst_subst_all)).
  intros [|[|[|n]]]; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; rewrite ?usubst_ren_tm; reflexivity.
Qed.
Lemma usubst_iwiFam_r l lp li X A N D Ot C a φ :
  usubst_ty (iwiFam l lp li X A N D Ot C a) φ =
  iwiFam (lvsubst l φ) (lvsubst lp φ) (lvsubst li φ) (usubst_ty X φ) (usubst_ty A φ) (usubst_tm N φ)
    (usubst_ty D φ) (usubst_tm Ot φ) (usubst_tm C φ) (usubst_tm a φ).
Proof.
  unfold iwiFam, iwiFamCod. cbn [usubst_tm usubst_ty lvsubst].
  rewrite ?usubst_ren_ty, ?usubst_ren_tm, ?usubst_llift2_single_r, ?usubst_llift_single_ty_r. reflexivity.
Qed.

Ltac upeel_push :=
  repeat first [ rewrite <- peelL_usubst | rewrite <- peelG_usubst | rewrite <- peelU_usubst ];
  rewrite rb_br_usubst; cbn [gousubst usubst_tm ucsubst usubst_ty lvsubst recT rect];
  rewrite ?usubst_lsingle_ty, ?usubst_lsucc_ty, ?usubst_lsingle2_ty, ?usubst_shift_ty, ?usubst_shift,
    ?usubst_liftshift_ty;
  cbn [usubst_tm usubst_ty lvsubst]; rewrite ?usubst_shift_ty, ?usubst_ren_ty, ?usubst_ren_tm;
  (* [sup_f]'s children's length and [elim_Wf]'s step telescope (M15b) *)
  rewrite ?usubst_lsingle_tm, ?usubst_lsingle_ty, ?usubst_tmNth_r; cbn [usubst_tm usubst_ty lvsubst];
  rewrite ?usubst_ren_ty, ?usubst_ren_tm;
  (* [sup_i]'s children and [elim_IWf]'s step telescope (M17c) *)
  rewrite ?usubst_iwfFam_r, ?usubst_iwiFam_r, ?usubst_tmDNth_r, ?usubst_lsingle2_ty; cbn [usubst_tm usubst_ty lvsubst];
  rewrite ?usubst_ren_ty, ?usubst_ren_tm, ?usubst_lsingle_tm;
  reflexivity.

Lemma redT_usubst l1 l2 rb l Δ c v φ : redT l1 l2 rb l Δ c = Some v ->
  redT (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm rb φ) (lvsubst l φ) (ucsubst Δ φ) (usubst_ty c φ)
    = Some (usubst_tm v φ).
Proof. destruct c; cbn [redT usubst_ty]; intros E; inversion E; subst; f_equal; upeel_push. Qed.
Lemma redt_usubst l1 l2 rb l Δ T c v φ : redt l1 l2 rb l Δ T c = Some v ->
  redt (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm rb φ) (lvsubst l φ) (ucsubst Δ φ) (usubst_ty T φ)
    (usubst_tm c φ) = Some (usubst_tm v φ).
Proof.
  destruct c; cbn [redt usubst_tm]; redt_case T; cbn [usubst_ty];
    intros E; first [discriminate E | apply Some_inj in E; subst v]; f_equal; upeel_push.
Qed.

End USubst.
