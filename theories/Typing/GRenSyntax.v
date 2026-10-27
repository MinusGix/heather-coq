(** * Syntax under global renaming

    The syntactic laws of global renaming that need no typing, split off
    [GWeakening] so that they build beside the typing metatheory instead
    of after it. *)
From DeLaM.Typing Require Export Context.

Coercion gwk_fn : gweak >-> Funclass.

(** ** Syntax under global renaming *)

Lemma gren_ren_ty' (A : ty) r ξ : (A⟨r⟩)⟪ξ⟫ = (A⟪ξ⟫)⟨r⟩.
Proof. apply gren_ren_ty. Qed.

Lemma gcren_gcren (Γ : ctx) ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> Γ⟪ξ⟫⟪ζ⟫ = Γ⟪θ⟫.
Proof. apply (proj1 (proj2 (proj2 gren_gren_all))). Qed.
Lemma gren_gren_ty (T : ty) ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> T⟪ξ⟫⟪ζ⟫ = T⟪θ⟫.
Proof. apply (proj1 gren_gren_all). Qed.
Lemma gren_gren_tm' (t : tm) ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> t⟪ξ⟫⟪ζ⟫ = t⟪θ⟫.
Proof. apply (proj1 (proj2 gren_gren_all)). Qed.

Lemma in_ctx_gren Γ n T l ξ : in_ctx Γ n T l -> in_ctx Γ⟪ξ⟫ n T⟪ξ⟫ l.
Proof.
  induction 1; cbn [gren GRen_ctx gcren]; change (gren_ty ?A ?ξ) with A⟪ξ⟫;
    rewrite gren_ren_ty'; now constructor.
Qed.

Lemma in_ctx_gren_inv Γ n T l ξ : in_ctx Γ⟪ξ⟫ n T l -> exists T0, in_ctx Γ n T0 l /\ T = T0⟪ξ⟫.
Proof.
  revert n T; induction Γ as [| g | Γ IH A k]; intros n T H; inversion H; subst.
  - exists A⟨↑⟩; split; [constructor | symmetry; apply gren_ren_ty'].
  - match goal with Hm : in_ctx _ _ _ _ |- _ => destruct (IH _ _ Hm) as (T0 & HT0 & ->) end.
    exists T0⟨↑⟩; split; [now constructor | symmetry; apply gren_ren_ty'].
Qed.

Lemma clen_gren Γ ξ : clen Γ⟪ξ⟫ = clen Γ.
Proof. induction Γ; cbn; auto. Qed.
Lemma ctx_tail_gren Γ ξ : ctx_tail Γ⟪ξ⟫ = (ctx_tail Γ)⟪ξ⟫.
Proof. induction Γ; cbn; auto. Qed.

Lemma lsub_tail_gren d Δ Γ ξ : lsub_tail d Δ Γ -> lsub_tail d⟪ξ⟫ Δ⟪ξ⟫ Γ⟪ξ⟫.
Proof.
  intros [Ht Hl]; split.
  - rewrite !ctx_tail_gren; now f_equal.
  - intros n; rewrite !clen_gren. cbn [gren GRen_lsub]. rewrite llk_glren, Hl; reflexivity.
Qed.

Lemma nfl_gren d ξ : dnfl d -> dnfl d⟪ξ⟫.
Proof. intros; apply gren_dnf_all. Qed.

Lemma gren_lsingle a ξ : (lsingle a)⟪ξ⟫ = lsingle a⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_lsingle2 t q ξ : (lsingle2 t q)⟪ξ⟫ = lsingle2 t⟪ξ⟫ q⟪ξ⟫.
Proof. reflexivity. Qed.
Lemma gren_lsucc ξ : lsucc⟪ξ⟫ = lsucc.
Proof. reflexivity. Qed.

Lemma gren_single_ty (M : ty) a ξ : M[lsingle a]⟪ξ⟫ = M⟪ξ⟫[lsingle a⟪ξ⟫].
Proof. rewrite gren_subst_ty; reflexivity. Qed.
Lemma gren_single (b a : tm) ξ : b[lsingle a]⟪ξ⟫ = b⟪ξ⟫[lsingle a⟪ξ⟫].
Proof. rewrite gren_subst; reflexivity. Qed.
Lemma gren_single2 (z t q : tm) ξ : z[lsingle2 t q]⟪ξ⟫ = z⟪ξ⟫[lsingle2 t⟪ξ⟫ q⟪ξ⟫].
Proof. rewrite gren_subst; reflexivity. Qed.
Lemma gren_single2_ty (M : ty) t q ξ : M[lsingle2 t q]⟪ξ⟫ = M⟪ξ⟫[lsingle2 t⟪ξ⟫ q⟪ξ⟫].
Proof. rewrite gren_subst_ty; reflexivity. Qed.
Lemma gren_lsucc_ty (M : ty) ξ : M[lsucc]⟪ξ⟫ = M⟪ξ⟫[lsucc].
Proof. rewrite gren_subst_ty; reflexivity. Qed.
Lemma gren_single3 (c a f h : tm) ξ : c[lsingle3 a f h]⟪ξ⟫ = c⟪ξ⟫[lsingle3 a⟪ξ⟫ f⟪ξ⟫ h⟪ξ⟫].
Proof. rewrite gren_subst; reflexivity. Qed.

(** The letbox body's type [M⟪↑⟫[box U^id/x]] under [⇑ξ]. *)
Lemma gren_letbox_ty (M : ty) b ξ : b⟪gupr ξ⟫ = b ->
  M⟪S⟫[lsingle b]⟪gupr ξ⟫ = M⟪ξ⟫⟪S⟫[lsingle b].
Proof.
  intros Hb. rewrite gren_single_ty, Hb. f_equal.
  rewrite !(gren_gren_ty _ _ _ (fun i => S (ξ i))); auto.
Qed.
Lemma gcren_shift_up (Γ : ctx) ξ : Γ⟪S⟫⟪gupr ξ⟫ = Γ⟪ξ⟫⟪S⟫.
Proof. rewrite !(gcren_gcren _ _ _ (fun i => S (ξ i))); auto. Qed.

(** η of the meta-functions (M5): the function weakened under the binder. *)
Lemma gren_shift_up_tm (t : tm) ξ : t⟪S⟫⟪gupr ξ⟫ = t⟪ξ⟫⟪S⟫.
Proof. rewrite !(gren_gren_tm _ _ _ (fun i => S (ξ i))); auto. Qed.

(** Letbox β under global renaming: [t'⦃o/U⦄⟪ξ⟫ = t'⟪⇑ξ⟫⦃o⟪ξ⟫/U⦄]. *)
Lemma gren_gsingle (t : tm) o ξ : t⦃gsingle o⦄⟪ξ⟫ = t⟪gupr ξ⟫⦃gsingle (goren o ξ)⦄.
Proof.
  cbn [gsubst gren GSubst_tm GRen_tm].
  rewrite (proj1 (proj2 gren_gsubst_all) _ _ _ (fun i => goren (gsingle o i) ξ)) by auto.
  symmetry; apply (proj1 (proj2 gsubst_gren_all)). intros [|i]; reflexivity.
Qed.
(** The instances of the meta-functions (M5). *)
Lemma gren_gsingle_ty (T : ty) o ξ : T⦃gsingle o⦄⟪ξ⟫ = T⟪gupr ξ⟫⦃gsingle (goren o ξ)⦄.
Proof.
  cbn [gsubst gren GSubst_ty GRen_ty].
  rewrite (proj1 gren_gsubst_all _ _ _ (fun i => goren (gsingle o i) ξ)) by auto.
  symmetry; apply (proj1 gsubst_gren_all). intros [|i]; reflexivity.
Qed.

(** The reducts commute with global renaming. *)
Lemma tup_nth_gren t k ξ : tup_nth t⟪ξ⟫ k = (tup_nth t k)⟪ξ⟫.
Proof. revert t; induction k; intros []; cbn; auto. Qed.
Lemma peelU_gren b l ξ : peelU b⟪ξ⟫ l = (peelU b l)⟪ξ⟫.
Proof. destruct b; cbn; auto. apply usubst_gren. Qed.
Lemma peelG_gren b o ξ : peelG b⟪ξ⟫ (goren o ξ) = (peelG b o)⟪ξ⟫.
Proof. destruct b; cbn; auto. symmetry; apply gren_gsingle. Qed.
Lemma peelL_gren b a ξ : peelL b⟪ξ⟫ a⟪ξ⟫ = (peelL b a)⟪ξ⟫.
Proof. destruct b; cbn; auto. symmetry; apply gren_single. Qed.

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
