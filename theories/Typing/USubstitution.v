(** * Universe substitution of every judgment (M3_DESIGN.md E6)

    [φ : L' ⇒ L] ([usub_ok φ L' L]: the images of the variables of [L] are
    levels well-formed in [L']) sends every judgment under [G = (L, Ψ)] to
    one under [G[φ] = (L', Ψ[φ])], at every layer. The recursors' motives
    and branches are typed under fresh levels: there [φ] is lifted
    ([uup]), and the scopes commute with it ([RecLaws]). Universe
    weakening is the special case of a renaming. *)
From DeLaM.Typing Require Export RecLaws.

(** ** Lookups *)

Lemma usubst_ren_ty' (A : ty) r φ : usubst_ty (ren_ty A r) φ = ren_ty (usubst_ty A φ) r.
Proof. apply (proj1 usubst_ren_all). Qed.

Lemma in_ctx_usubst Γ n T l φ : in_ctx Γ n T l -> in_ctx (ucsubst Γ φ) n (usubst_ty T φ) (lvsubst l φ).
Proof. induction 1; cbn [ucsubst]; rewrite usubst_ren_ty'; now constructor. Qed.

Lemma in_ctx_usubst_inv Γ n T l φ : in_ctx (ucsubst Γ φ) n T l ->
  exists T0 l0, in_ctx Γ n T0 l0 /\ T = usubst_ty T0 φ /\ l = lvsubst l0 φ.
Proof.
  revert n T l; induction Γ as [| g | Γ IH A k]; intros n T l H; inversion H; subst.
  - exists A⟨↑⟩, k; split; [apply in_here | split; [symmetry; apply usubst_ren_ty' | reflexivity]].
  - match goal with Hm : in_ctx _ _ _ _ |- _ => destruct (IH _ _ _ Hm) as (T0 & l0 & HT0 & -> & ->) end.
    exists T0⟨↑⟩, l0; split; [now apply in_there | split; [symmetry; apply usubst_ren_ty' | reflexivity]].
Qed.

Lemma clen_usubst Γ φ : clen (ucsubst Γ φ) = clen Γ.
Proof. induction Γ; cbn; auto. Qed.
Lemma ctx_tail_usubst Γ φ : ctx_tail (ucsubst Γ φ) = ucsubst (ctx_tail Γ) φ.
Proof. induction Γ; cbn; auto. Qed.

Lemma lsub_tail_usubst d Δ Γ φ : lsub_tail d Δ Γ ->
  lsub_tail (ulsubst d φ) (ucsubst Δ φ) (ucsubst Γ φ).
Proof.
  intros [Ht Hl]; split.
  - rewrite !ctx_tail_usubst; now f_equal.
  - intros n; rewrite !clen_usubst, llk_ulsubst, Hl; reflexivity.
Qed.

Lemma dnfl_usubst d φ : dnfl (ulsubst d φ).
Proof. apply usubst_dnf_all. Qed.

Lemma gdecl_ren_usubst D ξ φ : gdecl_usubst (gdecl_ren D ξ) φ = gdecl_ren (gdecl_usubst D φ) ξ.
Proof.
  destruct D; cbn; f_equal; try reflexivity;
    first [apply (proj1 (proj2 (proj2 usubst_gren_all))) | apply (proj1 usubst_gren_all) | apply (proj1 (proj2 usubst_gren_all))].
Qed.

Lemma in_gctx_usubst Ψ n D φ : in_gctx Ψ n D ->
  in_gctx (map (fun D => gdecl_usubst D φ) Ψ) n (gdecl_usubst D φ).
Proof. induction 1; cbn; rewrite gdecl_ren_usubst; now constructor. Qed.

Lemma gctx_var_usubst G g L' φ : gctx_var G g -> gctx_var (gctx_usubst G L' φ) g.
Proof.
  unfold gctx_var, gctx_usubst; cbn. intros H. now rewrite nth_error_map, H.
Qed.

Lemma usub_ok_uupn n φ L' L : usub_ok φ L' L -> usub_ok (uupn n φ) (n + L') (n + L).
Proof. induction n; cbn; auto. intros H; apply usub_ok_uup, IHn, H. Qed.

(** ** Equations for the rules' own substitutions *)

Lemma usubst_lsingle (b a : tm) φ : usubst_tm (subst_tm b (lsingle a)) φ = subst_tm (usubst_tm b φ) (lsingle (usubst_tm a φ)).
Proof. apply (proj1 (proj2 usubst_subst_all)). intros [|n]; reflexivity. Qed.
Lemma usubst_lsingle2 (z t q : tm) φ :
  usubst_tm (subst_tm z (lsingle2 t q)) φ = subst_tm (usubst_tm z φ) (lsingle2 (usubst_tm t φ) (usubst_tm q φ)).
Proof. apply (proj1 (proj2 usubst_subst_all)). intros [|[|n]]; reflexivity. Qed.
Lemma usubst_ren' (t : tm) r φ : usubst_tm (ren_tm t r) φ = ren_tm (usubst_tm t φ) r.
Proof. apply (proj1 (proj2 usubst_ren_all)). Qed.
Lemma usubst_gren_ty' (T : ty) ξ φ : usubst_ty (gren_ty T ξ) φ = gren_ty (usubst_ty T φ) ξ.
Proof. apply (proj1 usubst_gren_all). Qed.
Lemma usubst_gren_ctx' (Γ : ctx) ξ φ : ucsubst (gcren Γ ξ) φ = gcren (ucsubst Γ φ) ξ.
Proof. apply (proj1 (proj2 (proj2 usubst_gren_all))). Qed.
Lemma usubst_gsingle (t : tm) o φ :
  usubst_tm (gsubst_tm t (gsingle o)) φ = gsubst_tm (usubst_tm t φ) (gsingle (gousubst o φ)).
Proof.
  rewrite (proj1 (proj2 usubst_gsubst_all) _ _ _ (fun i => gousubst (gsingle o i) φ)) by auto.
  apply (proj1 (proj2 gsubst_ext_all)). intros [|i]; reflexivity.
Qed.
Lemma usubst_subst_ty' (T : ty) d φ :
  usubst_ty (subst_ty T d) φ = subst_ty (usubst_ty T φ) (ulsubst d φ).
Proof. apply (proj1 usubst_subst_all). intros; apply llk_ulsubst. Qed.
Lemma usubst_subst' (t : tm) d φ :
  usubst_tm (subst_tm t d) φ = subst_tm (usubst_tm t φ) (ulsubst d φ).
Proof. apply (proj1 (proj2 usubst_subst_all)). intros; apply llk_ulsubst. Qed.

(** The instances of the meta-functions (M5). *)
Lemma usubst_gsingle_ty (T : ty) o φ :
  usubst_ty (gsubst_ty T (gsingle o)) φ = gsubst_ty (usubst_ty T φ) (gsingle (gousubst o φ)).
Proof.
  rewrite (proj1 usubst_gsubst_all _ _ _ (fun i => gousubst (gsingle o i) φ)) by auto.
  apply (proj1 gsubst_ext_all). intros [|i]; reflexivity.
Qed.
Lemma usubst_gren_tm' (t : tm) ξ φ : usubst_tm (gren_tm t ξ) φ = gren_tm (usubst_tm t φ) ξ.
Proof. apply (proj1 (proj2 usubst_gren_all)). Qed.

(** [elim_W]'s β (M13a): the step's instance and its induction hypothesis. *)
Lemma usubst_lsingle3 (c a f h : tm) φ :
  usubst_tm (subst_tm c (lsingle3 a f h)) φ =
  subst_tm (usubst_tm c φ) (lsingle3 (usubst_tm a φ) (usubst_tm f φ) (usubst_tm h φ)).
Proof. apply (proj1 (proj2 usubst_subst_all)). intros [|[|[|n]]]; reflexivity. Qed.
Lemma usubst_wIH l l' l'' A B M c a f φ :
  usubst_tm (wIH l l' l'' A B M c a f) φ =
  wIH (lvsubst l φ) (lvsubst l' φ) (lvsubst l'' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_ty M φ)
    (usubst_tm c φ) (usubst_tm a φ) (usubst_tm f φ).
Proof.
  unfold wIH; cbn [usubst_tm usubst_ty lvsubst].
  rewrite ?usubst_ren_ty', ?usubst_ren', ?usubst_lsingle_ty. cbn [usubst_ty]. reflexivity.
Qed.

Ltac us_rewrite :=
  rewrite ?usubst_lsingle_ty, ?usubst_lsingle2_ty, ?usubst_lsucc_ty, ?usubst_lsingle, ?usubst_lsingle2,
    ?usubst_ren_ty', ?usubst_ren', ?usubst_gren_ty', ?usubst_gren_ctx', ?usubst_gsingle,
    ?usubst_gsingle_ty, ?usubst_gren_tm',
    ?usubst_subst_ty', ?usubst_lsingle3, ?usubst_wIH, ?motT_usubst, ?mott_usubst, ?mkrb_usubst, ?wrapMT_usubst, ?wrapMt_usubst.

Ltac us_push :=
  cbn [usubst_ty usubst_tm ucsubst ulsubst lvsubst gousubst gctx_usubst gdecl_usubst map gL gΨ gext typeof uup] in *.

(** ** The scope of [UΠ] (M4): [n] fresh levels *)

Lemma gctx_uwk_usubst n G L' φ :
  gctx_usubst (gctx_uwk n G) (n + L') (uupn n φ) = gctx_uwk n (gctx_usubst G L' φ).
Proof.
  unfold gctx_usubst, gctx_uwk; cbn [gL gΨ]. f_equal.
  rewrite !map_map. apply map_ext; intros; apply gdecl_uren_usubst.
Qed.
Lemma ucren_ush_usubst n Γ φ : ucsubst (ucren Γ (ush n)) (uupn n φ) = ucren (ucsubst Γ φ) (ush n).
Proof.
  rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ (fun i => lvren (φ i) (ush n)))
    by (intros; symmetry; apply uupn_ush).
  symmetry; apply (proj1 (proj2 (proj2 usubst_uren_all))); reflexivity.
Qed.
Lemma uren_ush_usubst_tm n t φ : usubst_tm (uren_tm t (ush n)) (uupn n φ) = uren_tm (usubst_tm t φ) (ush n).
Proof.
  rewrite (proj1 (proj2 uren_usubst_all) _ _ _ (fun i => lvren (φ i) (ush n)))
    by (intros; symmetry; apply uupn_ush).
  symmetry; apply (proj1 (proj2 usubst_uren_all)); reflexivity.
Qed.

Lemma ubvars_length n : length (ubvars n) = n.
Proof. unfold ubvars. now rewrite length_map, length_rev, length_seq. Qed.
Lemma ubvars_uupn n φ : map (fun l => lvsubst l (uupn n φ)) (ubvars n) = ubvars n.
Proof.
  unfold ubvars. rewrite map_map. apply map_ext_in. intros a Ha.
  apply in_rev, in_seq in Ha. cbn [lvsubst]. apply uupn_lt; lia.
Qed.

(** The [UΠ] β reduct commutes with universe substitution (M4). *)
Lemma uext_usubst_lvl n ls φ i : length ls = n ->
  lvsubst (uext ls lvar i) φ = lvsubst (uupn n φ i) (uext (map (fun l => lvsubst l φ) ls) lvar).
Proof.
  intros Hn. destruct (Nat.ltb_spec i n) as [Hi | Hi].
  - rewrite uupn_lt by exact Hi. cbn [lvsubst]. unfold uext. rewrite length_map, Hn.
    destruct (Nat.ltb_spec i n); [|lia].
    rewrite <- (map_nth (fun l => lvsubst l φ) ls lzero). reflexivity.
  - replace i with (n + (i - n)) by lia. rewrite uupn_ush.
    rewrite (lvren_lvsubst _ _ _ lvar).
    + rewrite (lvsubst_id (φ (i - n)) lvar) by reflexivity. unfold uext. subst n.
      destruct (Nat.ltb_spec (length ls + (i - length ls)) (length ls)); [lia|].
      cbn [lvsubst]. f_equal; lia.
    + intros m; unfold ush, uext. rewrite length_map, Hn.
      destruct (Nat.ltb_spec (n + m) n); [lia|]. f_equal; lia.
Qed.

Lemma usubst_ubeta n ls φ (b : tm) : length ls = n ->
  b[uext ls lvar]ᵤ[φ]ᵤ = b[uupn n φ]ᵤ[uext (map (fun l => lvsubst l φ) ls) lvar]ᵤ.
Proof.
  intros Hn. rewrite (usubst_usubst b _ _ _ (fun i => eq_refl)).
  rewrite (usubst_usubst b _ _ _ (fun i => eq_refl)).
  apply (proj1 (proj2 usubst_ext_all)); intros i. apply uext_usubst_lvl, Hn.
Qed.

Lemma usubst_ubeta_ty n ls φ (T : ty) : length ls = n ->
  T[uext ls lvar]ᵤ[φ]ᵤ = T[uupn n φ]ᵤ[uext (map (fun l => lvsubst l φ) ls) lvar]ᵤ.
Proof.
  intros Hn. rewrite (usubst_usubst_ty T _ _ _ (fun i => eq_refl)).
  rewrite (usubst_usubst_ty T _ _ _ (fun i => eq_refl)).
  apply (proj1 usubst_ext_all); intros i. apply uext_usubst_lvl, Hn.
Qed.
Lemma usubst_ubeta_lvl n ls φ l : length ls = n ->
  lvsubst (lvsubst l (uext ls lvar)) φ = lvsubst (lvsubst l (uupn n φ)) (uext (map (fun l => lvsubst l φ) ls) lvar).
Proof.
  intros Hn. rewrite (lvsubst_lvsubst l _ _ _ (fun i => eq_refl)).
  rewrite (lvsubst_lvsubst l _ _ _ (fun i => eq_refl)).
  apply lvsubst_ext; intros i. apply uext_usubst_lvl, Hn.
Qed.

Lemma lwfs_usubst ls φ L' L : usub_ok φ L' L -> Forall (lwf L) ls ->
  Forall (lwf L') (map (fun l => lvsubst l φ) ls).
Proof. intros Hφ H; induction H; cbn; constructor; eauto using lwf_lvsubst. Qed.
Lemma lequivs_usubst ls ls' φ L' L : usub_ok φ L' L -> Forall2 (lequiv L) ls ls' ->
  Forall2 (lequiv L') (map (fun l => lvsubst l φ) ls) (map (fun l => lvsubst l φ) ls').
Proof. intros Hφ H; induction H; cbn; constructor; eauto using lequiv_lvsubst. Qed.

(** ** The theorem *)

Definition G_us (G : gctx) (L' : nat) (φ : nat -> lvl) : gctx := gctx_usubst G L' φ.

Lemma us_ext G D L' φ : gctx_usubst (gext G D) L' φ = gext (gctx_usubst G L' φ) (gdecl_usubst D φ).
Proof. reflexivity. Qed.

#[local] Hint Resolve lwf_lvsubst lequiv_lvsubst in_ctx_usubst in_gctx_usubst gctx_var_usubst
  lsub_tail_usubst dnfl_usubst usub_ok_uup usub_ok_uupn lwfs_usubst lequivs_usubst : us.
#[local] Hint Extern 1 (_ = _ \/ _ = _) => first [left; reflexivity | right; reflexivity] : us.
#[local] Hint Extern 1 (_ <> _) => assumption : us.
#[local] Hint Extern 1 (in_gctx _ _ _) =>
  match goal with Hin : in_gctx _ _ _ |- _ => exact (in_gctx_usubst _ _ _ _ Hin) end : us.
#[local] Hint Extern 1 (compt _) => assumption : us.
#[local] Hint Extern 1 (lle _ _) => assumption : us.
#[local] Hint Extern 1 (ty_leq _ _) =>
  apply (proj1 leq_usubst_all); [intros; apply leqv_refl | assumption] : us.
#[local] Hint Extern 1 (tm_leq _ _) =>
  apply (proj1 (proj2 leq_usubst_all)); [intros; apply leqv_refl | assumption] : us.

Lemma us_wf_regty G i Δ x T T' l :
  [ G ; Δ ⊢[ i ] x : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? ->. Qed.
Lemma us_eq_regty G i Δ x y T T' l :
  [ G ; Δ ⊢[ i ] x ≅ y : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? ->. Qed.

Ltac us_eq := us_push; us_rewrite; us_push; first [reflexivity | f_equal; reflexivity].

(** A premise: an induction hypothesis, up to an equation of the type. *)
Ltac us_ih :=
  match goal with
  | IH : forall L' φ, usub_ok φ L' _ -> _ |- _ =>
      first [ eapply IH; solve [eauto with us]
            | eapply us_wf_regty; [eapply IH; solve [eauto with us] | us_eq]
            | eapply us_eq_regty; [eapply IH; solve [eauto with us] | us_eq] ]
  end.

Ltac us_prem := first [ solve [eauto with us] | us_ih ].

(** The lookup-typed local substitution of [u^δ]/[U^δ]. *)
Ltac us_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin;
  let A0 := fresh "A0" in let k0 := fresh "k0" in let HA0 := fresh "HA0" in
  destruct (in_ctx_usubst_inv _ _ _ _ _ Hin) as (A0 & k0 & HA0 & -> & ->);
  rewrite !llk_ulsubst;
  first [ rewrite <- usubst_subst_ty' | idtac ];
  match goal with IH : forall n A k (_ : in_ctx _ n A k), _ |- _ => eapply (IH n A0 k0 HA0) end;
  eauto with us.

Ltac us_step := any_rule us_prem.

Lemma lvren_ush1_usubst l φ : lvsubst (lvren l (ush 1)) (uup φ) = lvren (lvsubst l φ) (ush 1).
Proof. exact (lvren_ush_usubst l 1 φ). Qed.

(** Specialize the induction hypotheses at [φ]: the premises at the same
    universe context directly, the motives at [uup φ], the branches at
    [uupn nu φ]; then push [φ] through the syntax everywhere. *)
Ltac us_spec :=
  repeat match goal with
  | IH : forall L' φ, usub_ok φ L' (gL ?G) -> _, H : usub_ok ?φ ?L' (gL ?G) |- _ =>
      specialize (IH L' φ H)
  | IH : forall L' φ, usub_ok φ L' (gL (gext ?G _)) -> _, H : usub_ok ?φ ?L' (gL ?G) |- _ =>
      specialize (IH L' φ H)
  | IH : forall L' φ, usub_ok φ L' (gL (recGT ?G)) -> _, H : usub_ok ?φ ?L' (gL ?G) |- _ =>
      specialize (IH (S L') (uup φ) (usub_ok_uup _ _ _ H));
      rewrite recGT_usubst, recΓT_usubst, ?lvren_ush1_usubst in IH
  | IH : forall L' φ, usub_ok φ L' (gL (recGt ?G)) -> _, H : usub_ok ?φ ?L' (gL ?G) |- _ =>
      specialize (IH (S L') (uup φ) (usub_ok_uup _ _ _ H));
      rewrite recGt_usubst, recΓt_usubst, ?lvren_ush1_usubst in IH
  | IH : forall L' φ, usub_ok φ L' (gL (gctx_uwk ?n ?G)) -> _, H : usub_ok ?φ ?L' (gL ?G) |- _ =>
      specialize (IH (n + L') (uupn n φ) (usub_ok_uupn _ _ _ _ H));
      rewrite gctx_uwk_usubst, ucren_ush_usubst in IH
  end.

(** [us_rw_all]: generated by [tools/gen_push.py] from [us_rewrite]'s lemma
    list, in the goal and every hypothesis. *)
Ltac us_rw_all_at h k := lazymatch h with
  | @subst_ty => first [k usubst_lsingle_ty | k usubst_lsingle2_ty | k usubst_lsucc_ty | k usubst_subst_ty']
  | @subst => first [k usubst_lsingle_ty | k usubst_lsingle2_ty | k usubst_lsucc_ty | k usubst_lsingle | k usubst_lsingle2
                    | k usubst_lsingle3 | k usubst_subst_ty']
  | @subst_tm => first [k usubst_lsingle | k usubst_lsingle2 | k usubst_lsingle3]
  | @wIH => k usubst_wIH
  | @ren_ty => k usubst_ren_ty'
  | @ren => first [k usubst_ren_ty' | k usubst_ren']
  | @ren_tm => k usubst_ren'
  | @gren_ty => k usubst_gren_ty'
  | @gren => first [k usubst_gren_ty' | k usubst_gren_ctx' | k usubst_gren_tm']
  | @gcren => k usubst_gren_ctx'
  | @gsubst_tm => k usubst_gsingle
  | @gsubst => first [k usubst_gsingle | k usubst_gsingle_ty]
  | @gsubst_ty => k usubst_gsingle_ty
  | @gren_tm => k usubst_gren_tm'
  | @motT => k motT_usubst
  | @mott => k mott_usubst
  | @mkrb => k mkrb_usubst
  | @wrapMT => k wrapMT_usubst
  | @wrapMt => k wrapMt_usubst
  end.
Ltac us_rw_all := repeat match goal with
  | |- context [@usubst_ty ?t _] => let h := head_of t in us_rw_all_at h ltac:(fun L => rewrite L)
  | H : context [@usubst_ty ?t _] |- _ => let h := head_of t in us_rw_all_at h ltac:(fun L => rewrite L in H)
  | |- context [@usubst_tm ?t _] => let h := head_of t in us_rw_all_at h ltac:(fun L => rewrite L)
  | H : context [@usubst_tm ?t _] |- _ => let h := head_of t in us_rw_all_at h ltac:(fun L => rewrite L in H)
  | |- context [@ucsubst ?t _] => let h := head_of t in us_rw_all_at h ltac:(fun L => rewrite L)
  | H : context [@ucsubst ?t _] |- _ => let h := head_of t in us_rw_all_at h ltac:(fun L => rewrite L in H)
  end.
Ltac us_rewrite_all := us_rw_all; us_push.

(** The branch premises: the induction hypotheses at [uupn nu φ]. *)
Ltac us_branches :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
  match goal with
  | IH : forall k, k < nbr -> forall L' φ, usub_ok φ L' _ -> _, H : usub_ok ?φ ?L' _ |- _ =>
      let X := fresh "X" in
      pose proof (IH k Hk (br_nu k + L') (uupn (br_nu k) φ) (usub_ok_uupn _ _ _ _ H)) as X;
      rewrite brG_usubst in X by exact Hk; rewrite brΓ_usubst in X by exact Hk;
      rewrite ?brRes_usubst, ?brLv_usubst in X by exact Hk;
      exact X
  end.

Ltac us_Δ tac :=
  match goal with
  | Hin : in_gctx _ _ (gdTy ?Δ _ _), H : usub_ok ?φ _ _ |- _ => tac (ucsubst Δ φ)
  | Hin : in_gctx _ _ (gdTm ?Δ _ _ _), H : usub_ok ?φ _ _ |- _ => tac (ucsubst Δ φ)
  | Hin : in_gctx _ _ (gdDef ?Δ _ _ _), H : usub_ok ?φ _ _ |- _ => tac (ucsubst Δ φ)
  end.

Ltac us_manual :=
  match goal with
  (* [case] (M12b): its branches' types shift the summands inside the
     injection, which the first pass exposes only after [cbn] *)
  | |- context [tmCase _ _ _ _ _ _ _ _ _] => us_rewrite_all; us_step
  (* [elim_W] (M13a): its step telescope nests the shifts deeper *)
  | |- context [tmElimW _ _ _ _ _ _ _ _] => us_rewrite_all; us_rewrite_all; us_step
  | |- wf_ty _ _ _ (tyGvar _ _) _ =>
      us_Δ ltac:(fun D => eapply wft_gvar with (Δ := D)); [ .. | us_entries]; eauto with us
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      us_Δ ltac:(fun D => eapply eqty_gvar with (Δ := D));
      [ .. | us_entries | us_entries | us_entries]; eauto with us
  | |- wf_tm _ _ _ (gvar _ _) _ _ =>
      us_Δ ltac:(fun D => eapply wf_gvar with (Δ := D)); [ .. | us_entries]; eauto with us
  | |- eq_tm _ _ _ (gvar _ _) _ _ _ =>
      us_Δ ltac:(fun D => eapply eqtm_gvar with (Δ := D));
      [ .. | us_entries | us_entries | us_entries]; eauto with us
  (* defined globals (M9) *)
  | |- wf_tm _ _ _ (gdef _ _ _) _ _ =>
      us_Δ ltac:(fun D => eapply wf_gdef with (Δ := D)); [ .. | us_entries | ]; eauto with us
  | |- eq_tm _ _ _ (gdef _ _ _) (gdef _ _ _) _ _ =>
      us_Δ ltac:(fun D => eapply eqtm_gdef with (Δ := D));
      [ .. | us_entries | us_entries | us_entries | ]; eauto with us
  | |- eq_tm _ _ _ (gdef _ _ _) _ _ _ =>
      rewrite usubst_subst'; us_Δ ltac:(fun D => eapply eqtm_delta with (Δ := D));
      [ .. | us_entries | ]; eauto with us
  | |- wf_tm _ _ _ (elimT _ _ _ _ _ _) _ _ =>
      eapply wf_elimT; [ .. | us_branches | us_branches | ]; eauto with us
  | |- wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ =>
      eapply wf_elimt; [ .. | us_branches | us_branches | | ]; eauto with us
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ (boxT _)) _ _ _ =>
      eapply eqtm_elimT_beta; [eauto | now apply redT_usubst | eauto]
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      eapply eqtm_elimt_beta; [eauto | now apply redt_usubst | eauto]
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimT; [ .. | us_branches | us_branches | us_branches | us_branches | ];
      eauto with us
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimt; [ .. | us_branches | us_branches | us_branches | us_branches | ];
      eauto with us
  (* [t T] (M5): the binding's level is not in the conclusion *)
  | Hb : wf_ty (gctx_usubst (gext _ (gdTy _ lD ?k)) _ ?φ) _ _ _ _ |- wf_tm _ _ _ (tapp _ _) _ _ =>
      eapply wf_tapp with (l := lvsubst k φ); eauto with us
  | Hb : wf_ty (gctx_usubst (gext _ (gdTy _ lD ?k)) _ ?φ) _ _ _ _ |- eq_tm _ _ _ (tapp _ _) _ _ _ =>
      eapply eqtm_tapp with (l := lvsubst k φ); eauto with us
  | |- _ => solve [econstructor; eauto with us]
  end.

(** [UΠ]'s elimination, β and η: commute [φ] with the instance, and with
    η's bound variables. *)
Ltac us_upi :=
  match goal with
  | Hn : length ?ls = ?n, H : usub_ok ?φ _ _ |- context [uapp _ (map _ ?ls)] =>
      rewrite ?(usubst_ubeta_ty n ls φ _ Hn), ?(usubst_ubeta_lvl n ls φ _ Hn),
        ?(usubst_ubeta n ls φ _ Hn);
      first [ eapply wf_uapp | eapply eqtm_uapp | eapply eqtm_ubeta ];
      eauto with us; now rewrite length_map
  | |- context [ubvars ?n] =>
      rewrite uren_ush_usubst_tm, ubvars_uupn; eapply eqtm_ueta; eauto with us
  end.

Theorem usubstitution :
  (forall G, [ ⊢ G ] -> forall L' φ, usub_ok φ L' (gL G) -> [ ⊢ G_us G L' φ ]) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> forall L' φ, usub_ok φ L' (gL G) ->
     [ G_us G L' φ ; ucsubst Γ φ ⊢[ i ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> forall L' φ, usub_ok φ L' (gL G) ->
     [ G_us G L' φ ; ucsubst Γ φ ⊢[ i ] usubst_ty T φ @ lvsubst l φ ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> forall L' φ, usub_ok φ L' (gL G) ->
     [ G_us G L' φ ; ucsubst Γ φ ⊢[ i ] usubst_tm t φ : usubst_ty T φ @ lvsubst l φ ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> forall L' φ, usub_ok φ L' (gL G) ->
     [ G_us G L' φ ; ucsubst Γ φ ⊢[ i ] usubst_ty T φ ≅ usubst_ty T' φ @ lvsubst l φ ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> forall L' φ, usub_ok φ L' (gL G) ->
     [ G_us G L' φ ; ucsubst Γ φ ⊢[ i ] usubst_tm t φ ≅ usubst_tm t' φ : usubst_ty T φ @ lvsubst l φ ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> forall L' φ, usub_ok φ L' (gL G) ->
     [ G_us G L' φ ⊢[ i ] ucsubst Γ φ ≅ ucsubst Γ' φ ]).
Proof.
  unfold G_us. apply typing_mut; intros; us_spec; us_push; us_rewrite_all.
  all: try us_step.
  all: first [us_upi | us_manual].
Qed.

Print Assumptions usubstitution.

(** ** Universe weakening: [n] fresh levels *)

Lemma uwk_as_usubst n : forall i, (fun j => lvar (ush n j)) i = lvar (ush n i).
Proof. reflexivity. Qed.

Lemma gdecl_uren_as_usubst D n :
  gdecl_uren D (ush n) = gdecl_usubst D (fun j => lvar (ush n j)).
Proof.
  destruct D; cbn [gdecl_uren gdecl_usubst]; f_equal; try reflexivity;
    first [ apply lvren_as_lvsubst; reflexivity
          | apply (proj1 (proj2 (proj2 uren_as_usubst_all))); reflexivity
          | apply (proj1 uren_as_usubst_all); reflexivity
          | apply (proj1 (proj2 uren_as_usubst_all)); reflexivity ].
Qed.

Lemma gctx_uwk_as n G : gctx_uwk n G = gctx_usubst G (n + gL G) (fun j => lvar (ush n j)).
Proof.
  unfold gctx_uwk, gctx_usubst. f_equal. apply map_ext; intros; apply gdecl_uren_as_usubst.
Qed.

Lemma usub_ok_ush n L : usub_ok (fun j => lvar (ush n j)) (n + L) L.
Proof. intros j Hj; cbn; unfold ush; lia. Qed.

Lemma uwk_glob n G : [ ⊢ G ] -> [ ⊢ gctx_uwk n G ].
Proof. intros H; rewrite gctx_uwk_as. apply (proj1 usubstitution); auto using usub_ok_ush. Qed.

(** Universe weakening of contexts, types and terms. *)
Lemma uren_ush_ctx Γ n : ucren Γ (ush n) = ucsubst Γ (fun j => lvar (ush n j)).
Proof. apply (proj1 (proj2 (proj2 uren_as_usubst_all))); reflexivity. Qed.
Lemma uren_ush_ty T n : uren_ty T (ush n) = usubst_ty T (fun j => lvar (ush n j)).
Proof. apply (proj1 uren_as_usubst_all); reflexivity. Qed.
Lemma uren_ush_tm t n : uren_tm t (ush n) = usubst_tm t (fun j => lvar (ush n j)).
Proof. apply (proj1 (proj2 uren_as_usubst_all)); reflexivity. Qed.
Lemma lvren_ush l n : lvren l (ush n) = lvsubst l (fun j => lvar (ush n j)).
Proof. apply lvren_as_lvsubst; reflexivity. Qed.

Lemma uwk_ctx n {G i Γ} : [ G ; Γ ⊢[ i ] ] -> [ gctx_uwk n G ; ucren Γ (ush n) ⊢[ i ] ].
Proof.
  intros H. rewrite gctx_uwk_as, uren_ush_ctx.
  exact (proj1 (proj2 usubstitution) _ _ _ H _ _ (usub_ok_ush n (gL G))).
Qed.
Lemma uwk_tm n {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] ->
  [ gctx_uwk n G ; ucren Γ (ush n) ⊢[ i ] uren_tm t (ush n) : uren_ty T (ush n) @ lvren l (ush n) ].
Proof.
  intros H. rewrite gctx_uwk_as, uren_ush_ctx, uren_ush_tm, uren_ush_ty, lvren_ush.
  exact (proj1 (proj2 (proj2 (proj2 usubstitution))) _ _ _ _ _ _ H _ _ (usub_ok_ush n (gL G))).
Qed.

Lemma in_ctx_uren_inv Γ n T l ρ : in_ctx (ucren Γ ρ) n T l ->
  exists T0 l0, in_ctx Γ n T0 l0 /\ T = uren_ty T0 ρ /\ l = lvren l0 ρ.
Proof.
  revert n T l; induction Γ as [| g | Γ IH A k]; intros n T l H; inversion H; subst.
  - exists A⟨↑⟩, k; split; [apply in_here | split; [symmetry; apply (proj1 uren_ren_all) | reflexivity]].
  - match goal with Hm : in_ctx _ _ _ _ |- _ => destruct (IH _ _ _ Hm) as (T0 & l0 & HT0 & -> & ->) end.
    exists T0⟨↑⟩, l0; split; [now apply in_there | split; [symmetry; apply (proj1 uren_ren_all) | reflexivity]].
Qed.
Lemma uwk_eqtm n {G i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ gctx_uwk n G ; ucren Γ (ush n) ⊢[ i ] uren_tm t (ush n) ≅ uren_tm t' (ush n) : uren_ty T (ush n)
    @ lvren l (ush n) ].
Proof.
  intros H. rewrite gctx_uwk_as, uren_ush_ctx, !uren_ush_tm, uren_ush_ty, lvren_ush.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ _ _ _ H _ _
           (usub_ok_ush n (gL G))).
Qed.
Lemma uwk_ty n {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] ->
  [ gctx_uwk n G ; ucren Γ (ush n) ⊢[ i ] uren_ty T (ush n) @ lvren l (ush n) ].
Proof.
  intros H. rewrite gctx_uwk_as, uren_ush_ctx, uren_ush_ty, lvren_ush.
  exact (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ H _ _ (usub_ok_ush n (gL G))).
Qed.

(** ** Weak-head normal forms and reduction under universe substitution
    (M3_DESIGN.md E14) *)

Lemma whne_usubst t φ : whne t -> whne (usubst_tm t φ).
Proof. induction 1; cbn; whne_step. Qed.
Lemma whnf_usubst t φ : whnf t -> whnf (usubst_tm t φ).
Proof. destruct 1; cbn; auto using whne_usubst with whnf. Qed.
Lemma whne_ty_usubst T φ : whne_ty T -> whne_ty (usubst_ty T φ).
Proof. destruct 1; cbn; constructor; auto using whne_usubst. Qed.
Lemma whnf_ty_usubst T φ : whnf_ty T -> whnf_ty (usubst_ty T φ).
Proof. destruct 1; cbn; auto using whne_ty_usubst with whnf. Qed.

Lemma red_usubst_both :
  (forall t u, red t u -> forall φ, red (usubst_tm t φ) (usubst_tm u φ)) /\
  (forall T U, red_ty T U -> forall φ, red_ty (usubst_ty T φ) (usubst_ty U φ)).
Proof.
  apply red_both; intros; cbn [usubst_tm usubst_ty ucsubst gousubst];
    rewrite ?usubst_lsingle, ?usubst_lsingle2, ?usubst_lsingle3, ?usubst_wIH, ?usubst_gsingle; try now constructor.
  all: try (constructor; auto; fail).
  (* δ: the body's instance *)
  all: try solve [change (usubst_tm (subst_tm ?b ?d) ?φ) with (b[d][φ]ᵤ); rewrite usubst_subst; constructor].
  (* [Vec]'s successor step: the tail's shifts *)
  all: try solve [change (usubst_ty (ren_ty ?A ?r) ?φ) with (A⟨r⟩[φ]ᵤ);
                  change (usubst_tm (ren_tm ?n ?r) ?φ) with (n⟨r⟩[φ]ᵤ);
                  rewrite usubst_ren_ty, usubst_ren; constructor].
  - constructor. now apply redT_usubst.
  - constructor. now apply redt_usubst.
  - match goal with Hn : length ?ls = ?n |- _ => rewrite (usubst_ubeta n ls φ _ Hn) end.
    constructor. now rewrite length_map.
Qed.

Lemma red_usubst t u φ : red t u -> red (usubst_tm t φ) (usubst_tm u φ).
Proof. intros H; now apply red_usubst_both. Qed.
Lemma red_ty_usubst T U φ : red_ty T U -> red_ty (usubst_ty T φ) (usubst_ty U φ).
Proof. intros H; now apply red_usubst_both. Qed.
Lemma reds_usubst t u φ : reds t u -> reds (usubst_tm t φ) (usubst_tm u φ).
Proof. unfold reds; induction 1; [constructor|econstructor; eauto using red_usubst]. Qed.
Lemma reds_ty_usubst T U φ : reds_ty T U -> reds_ty (usubst_ty T φ) (usubst_ty U φ).
Proof. unfold reds_ty; induction 1; [constructor|econstructor; eauto using red_ty_usubst]. Qed.
