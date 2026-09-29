(** * Structural properties of algorithmic conversion (M6_DESIGN.md step 3)

    Local and global weakening, universe substitution, closure under [≡ₗ].
    Each family is closed by one tactic run on every rule (M8_DESIGN.md
    J1): push the operation through the goal, instantiate every induction
    hypothesis at the scope it lives in and normalize it, reapply a rule,
    and discharge the premises. Only rules with irregular premises (the
    local substitutions' entries, the recursor branches, reductions for
    [≡ₗ]) keep a named lemma, so a new rule needs no code here. Local contexts of layer D (the [Δ]s of
    contextual types) do not depend on the ambient context, so local
    weakening leaves [ac_ctx] untouched. *)
From DeLaM.Syntax Require Export LevelRed.
From DeLaM.Typing Require Export Algorithmic Properties GWeakening.

Ltac push_ren_in H := revert H; push_ren; intros H.

Lemma posty_ren W r : posty W -> posty W⟨r⟩.
Proof.
  destruct 1; cbn; first [apply posty_nat | apply posty_U | apply posty_CTyp | apply posty_CTrm | idtac].
  apply posty_ne, whne_ty_ren; assumption.
Qed.

(** ** Retyping *)

Lemma ac_tm_eq {G Γ t t' T T'} : ac_tm G Γ t t' T -> T = T' -> ac_tm G Γ t t' T'.
Proof. now intros ? <-. Qed.
Lemma ac_tmne_eq {G Γ t t' T T'} : ac_tmne G Γ t t' T -> T = T' -> ac_tmne G Γ t t' T'.
Proof. now intros ? <-. Qed.
Lemma ac_tm_eq3 {G Γ t1 t2 u1 u2 T T'} : ac_tm G Γ t1 t2 T -> t1 = u1 -> t2 = u2 -> T = T' ->
  ac_tm G Γ u1 u2 T'.
Proof. now intros ? <- <- <-. Qed.
Lemma ac_ty_eq3 {G Γ T1 T2 U1 U2} : ac_ty G Γ T1 T2 -> T1 = U1 -> T2 = U2 -> ac_ty G Γ U1 U2.
Proof. now intros ? <- <-. Qed.

(** ** Local weakening *)

Definition AW_ty G Γ T T' : Prop := forall Δ r, wkr r Δ Γ -> ac_ty G Δ T⟨r⟩ T'⟨r⟩.
Definition AW_tynf G Γ T T' : Prop := forall Δ r, wkr r Δ Γ -> ac_tynf G Δ T⟨r⟩ T'⟨r⟩.
Definition AW_tyne G Γ T T' : Prop := forall Δ r, wkr r Δ Γ -> ac_tyne G Δ T⟨r⟩ T'⟨r⟩.
Definition AW_tm G Γ t t' T : Prop := forall Δ r, wkr r Δ Γ -> ac_tm G Δ t⟨r⟩ t'⟨r⟩ T⟨r⟩.
Definition AW_tmnf G Γ t t' T : Prop := forall Δ r, wkr r Δ Γ -> ac_tmnf G Δ t⟨r⟩ t'⟨r⟩ T⟨r⟩.
Definition AW_tmne G Γ t t' T : Prop := forall Δ r, wkr r Δ Γ -> ac_tmne G Δ t⟨r⟩ t'⟨r⟩ T⟨r⟩.
Definition AW_tmnee G Γ t t' T : Prop := forall Δ r, wkr r Δ Γ -> ac_tmnee G Δ t⟨r⟩ t'⟨r⟩ T⟨r⟩.
Definition AW_sub G Γ d d' Θ : Prop := forall Δ r, wkr r Δ Γ -> ac_sub G Δ (lren d r) (lren d' r) Θ.

(** The recursors: motives under [⇑r], branches under [⇑ⁿr]. *)
Lemma W_branches {G Γ MT Mt l1 l2 bs bs' Δ r} : wkr r Δ Γ ->
  (forall j, j < nbr -> AW_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  forall j, j < nbr -> ac_tm (brG j G) (brΓ j Δ (wrapMT MT⟨rlift r⟩) (wrapMt Mt⟨rlift r⟩) l1 l2)
                       ((bs j)⟨rliftn (br_nl j) r⟩) ((bs' j)⟨rliftn (br_nl j) r⟩)
                       (brRes j (wrapMT MT⟨rlift r⟩) (wrapMt Mt⟨rlift r⟩)).
Proof.
  intros Hr IH j Hj. pose proof (IH j Hj _ _ (wkr_brΓ j r Δ Γ (wrapMT MT) (wrapMt Mt) l1 l2 Hj Hr)) as X.
  rewrite brRes_ren, wrapMT_ren, wrapMt_ren in X by exact Hj. exact X.
Qed.

(** Every rule is closed by one tactic: push the renaming through the
    goal, reapply a rule, and discharge each premise directly or by an
    induction hypothesis at the weakening that reaches its context
    ([mk_wkr]), normalizing the renaming the same way. *)
(** Premises that are judgments are closed first, from the normalized
    induction hypotheses: they fix the evars that side conditions share. *)
Ltac ac_prem :=
  lazymatch goal with
  | |- ac_ty _ _ _ _ => eassumption | |- ac_tynf _ _ _ _ => eassumption
  | |- ac_tyne _ _ _ _ => eassumption | |- ac_ctx _ _ _ => eassumption
  | |- ac_tm _ _ _ _ _ => eassumption | |- ac_tmnf _ _ _ _ _ => eassumption
  | |- ac_tmne _ _ _ _ _ => eassumption | |- ac_tmnee _ _ _ _ _ => eassumption
  | |- ac_sub _ _ _ _ _ => eassumption
  end.

Ltac mk_wkr Hr Γ Γ' :=
  lazymatch Γ' with
  | Γ => constr:(Hr)
  | cext ?Γ1 ?A ?l => let h := mk_wkr Hr Γ Γ1 in constr:(wkr_up _ _ _ A l h)
  | uren Γ ?ρ => constr:(wkr_uren _ _ _ ρ Hr)
  | gren Γ ?ξ => constr:(wkr_gren _ _ _ ξ Hr)
  | recΓT Γ => constr:(wkr_recΓT _ _ _ Hr)
  | recΓt Γ => constr:(wkr_recΓt _ _ _ Hr)
  end.

Ltac W_norm := push_ren; wk_rewrite; rewrite <- ?gren_ren_ty'; push_ren.
Ltac W_norm_in X := revert X; W_norm; intros X.

(** Each induction hypothesis, at the weakening that reaches its context,
    normalized once. *)
Ltac W_inst Hr :=
  lazymatch type of Hr with wkr _ _ ?Γ =>
    repeat match goal with
    | IH : forall Δ' r', wkr r' Δ' ?Γ' -> _ |- _ =>
        let h := mk_wkr Hr Γ Γ' in
        let X := fresh "X" in pose proof (IH _ _ h) as X; W_norm_in X; clear IH
    end
  end.

Ltac W_prem :=
  first [ eassumption
        | solve [eauto using posty_ren, reds_ty_ren, whnf_ty_ren, reds_ren, whnf_ren, in_ctx_wkr]
        | solve [eapply W_branches; eassumption]
        | (* the entries of a local substitution *)
          let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
          intros n A k Hin; rewrite !llk_lren; rewrite <- (subst_ren_ty A _ _ _ (fun m => llk_lren _ _ m));
          match goal with IH : forall n A k, in_ctx _ n A k -> _ |- _ => eapply IH; eassumption end ].

Ltac W_case :=
  unfold AW_ty, AW_tynf, AW_tyne, AW_tm, AW_tmnf, AW_tmne, AW_tmnee, AW_sub in *;
  let Δ := fresh "Δ" in let r := fresh "r" in let Hr := fresh "Hr" in
  intros Δ r Hr; W_norm; W_inst Hr;
  first [ solve [econstructor; try ac_prem; W_prem]
        | rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m)); solve [econstructor; try ac_prem; W_prem] ].

Theorem ac_wk_all :
  (forall G Γ T T', ac_ty G Γ T T' -> AW_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> AW_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> AW_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> True) /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AW_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AW_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AW_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AW_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> AW_sub G Γ d d' Δ).
Proof. apply ac_mut; intros; try exact I; W_case. Qed.

(** ** Global weakening

    The algorithm checks no level against the universe context, but the
    scopes it builds ([gctx_uwk], [recGT], [brG]) mention it, so the
    statement is at a [gwk_ok] weakening. *)

Ltac push_gren_in H := revert H; push_gren; intros H.

Lemma posty_gren W ξ : posty W -> posty W⟪ξ⟫.
Proof.
  destruct 1; cbn; first [apply posty_nat | apply posty_U | apply posty_CTyp | apply posty_CTrm | idtac].
  apply posty_ne, whne_ty_gren; assumption.
Qed.

Lemma gwk_ok_ext {γ G' G} D : gwk_ok γ G' G -> gwk_ok (gwk_up γ) (gext G' (gdecl_ren D γ)) (gext G D).
Proof. intros [HL Hw]; split; [exact HL | exact (gwkwf_up _ _ _ D Hw)]. Qed.
Lemma gwk_ok_uwk {γ G' G} n : gwk_ok γ G' G -> gwk_ok γ (gctx_uwk n G') (gctx_uwk n G).
Proof. intros [HL Hw]; split; [cbn; lia | exact (gwk_wf_uren _ _ _ (ush n) Hw)]. Qed.
Lemma gwk_ok_recGT {γ G' G} : gwk_ok γ G' G -> gwk_ok (gwk_up γ) (recGT G') (recGT G).
Proof. intros H; split; [cbn; destruct H; lia | exact (recGT_gwk _ _ _ H)]. Qed.
Lemma gwk_ok_recGt {γ G' G} : gwk_ok γ G' G -> gwk_ok (gwk_up (gwk_up γ)) (recGt G') (recGt G).
Proof. intros H; split; [cbn; destruct H; lia | exact (recGt_gwk _ _ _ H)]. Qed.
Lemma gwk_ok_brG {γ G' G} k : k < nbr -> gwk_ok γ G' G -> gwk_ok (gwk_upn (br_ng k) γ) (brG k G') (brG k G).
Proof. intros Hk H; split; [cbn; destruct H; lia | exact (brG_gwk _ _ _ _ Hk H)]. Qed.

Definition AG_ty G Γ T T' : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_ty G' Γ⟪γ⟫ T⟪γ⟫ T'⟪γ⟫.
Definition AG_tynf G Γ T T' : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tynf G' Γ⟪γ⟫ T⟪γ⟫ T'⟪γ⟫.
Definition AG_tyne G Γ T T' : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tyne G' Γ⟪γ⟫ T⟪γ⟫ T'⟪γ⟫.
Definition AG_ctx G Δ Δ' : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_ctx G' Δ⟪γ⟫ Δ'⟪γ⟫.
Definition AG_tm G Γ t t' T : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tm G' Γ⟪γ⟫ t⟪γ⟫ t'⟪γ⟫ T⟪γ⟫.
Definition AG_tmnf G Γ t t' T : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tmnf G' Γ⟪γ⟫ t⟪γ⟫ t'⟪γ⟫ T⟪γ⟫.
Definition AG_tmne G Γ t t' T : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tmne G' Γ⟪γ⟫ t⟪γ⟫ t'⟪γ⟫ T⟪γ⟫.
Definition AG_tmnee G Γ t t' T : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tmnee G' Γ⟪γ⟫ t⟪γ⟫ t'⟪γ⟫ T⟪γ⟫.
Definition AG_sub G Γ d d' Θ : Prop := forall G' (γ : gweak), gwk_ok γ G' G ->
  ac_sub G' Γ⟪γ⟫ d⟪γ⟫ d'⟪γ⟫ Θ⟪γ⟫.

Lemma G_branches {G Γ MT Mt l1 l2 bs bs' G' γ} : gwk_ok γ G' G ->
  (forall j, j < nbr -> AG_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  forall j, j < nbr -> ac_tm (brG j G') (brΓ j Γ⟪γ⟫ (wrapMT MT⟪gupr γ⟫) (wrapMt Mt⟪gupr (gupr γ)⟫) l1 l2)
                       ((bs j)⟪guprn (br_ng j) γ⟫) ((bs' j)⟪guprn (br_ng j) γ⟫)
                       (brRes j (wrapMT MT⟪gupr γ⟫) (wrapMt Mt⟪gupr (gupr γ)⟫)).
Proof.
  intros Hγ IH j Hj. pose proof (IH j Hj _ _ (gwk_ok_brG j Hj Hγ)) as X.
  rewrite ?gren_gwk_upn_ctx, ?gren_gwk_upn_tm, ?gren_gwk_upn_ty in X.
  rewrite brΓ_gren, brRes_gren, ?wrapMT_gren, ?wrapMt_gren in X by exact Hj. exact X.
Qed.

Lemma G_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> AG_tm G Γ (llk d n) (llk d' n) A[d]) -> AG_sub G Γ d d' Θ.
Proof.
  intros IH G' γ Hγ. apply acs_pt. intros n A k Hin.
  destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & Hin0 & ->).
  change (llk (glren d γ) n) with (llk d⟪γ⟫ n). change (llk (glren d' γ) n) with (llk d'⟪γ⟫ n).
  rewrite !llk_glren, <- gren_subst_ty. exact (IH n A0 k Hin0 _ _ Hγ).
Qed.

(** Every rule is closed by one tactic, as for local weakening. *)
Ltac mk_gwk Hγ G G' :=
  lazymatch G' with
  | G => constr:(Hγ)
  | gext G ?D => constr:(gwk_ok_ext D Hγ)
  | gctx_uwk ?n G => constr:(gwk_ok_uwk n Hγ)
  | recGT G => constr:(gwk_ok_recGT Hγ)
  | recGt G => constr:(gwk_ok_recGt Hγ)
  end.

Ltac G_norm :=
  push_gren; cbn [gwk_fn gdecl_ren goren];
  rewrite ?gren_letbox_ty by reflexivity;
  rewrite ?gren_single_ty, ?gren_lsucc_ty, ?gren_ren, ?gren_ren_ty', ?gren_uren_ctx, ?gcren_shift_up,
          ?gren_shift_up_tm, ?mkrb_gren, ?motT_gren, ?mott_gren, ?wrapMT_gren, ?wrapMt_gren,
          ?recΓT_gren, ?recΓt_gren, ?gren_gsingle_ty;
  cbn [gwk_fn gdecl_ren goren]; push_gren.
Ltac G_norm_in X := revert X; G_norm; intros X.

Ltac G_inst Hγ :=
  lazymatch type of Hγ with gwk_ok _ _ ?G =>
    repeat match goal with
    | IH : forall G'' γ', gwk_ok γ' G'' ?G0 -> _ |- _ =>
        let h := mk_gwk Hγ G G0 in
        let X := fresh "X" in pose proof (IH _ _ h) as X; G_norm_in X; clear IH
    end
  end.

Ltac G_prem :=
  first [ eassumption
        | solve [eauto using posty_gren, reds_ty_gren, whnf_ty_gren, reds_gren, whnf_gren, in_ctx_gren]
        | match goal with
          | Hγ : gwk_ok _ _ _, Hin : in_gctx _ _ _ |- in_gctx _ _ _ =>
              let X := fresh "X" in pose proof (in_gctx_gwk _ _ _ _ _ (proj2 Hγ) Hin) as X;
              cbn [gdecl_ren] in X; exact X
          end
        | apply (proj1 leq_gren_all); assumption
        | apply (proj1 (proj2 leq_gren_all)); assumption
        | apply (proj2 (proj2 (proj2 leq_gren_all))); assumption
        | solve [eapply G_branches; eassumption] ].

Ltac G_case :=
  unfold AG_ty, AG_tynf, AG_tyne, AG_ctx, AG_tm, AG_tmnf, AG_tmne, AG_tmnee, AG_sub in *;
  let G' := fresh "G'" in let γ := fresh "γ" in let Hγ := fresh "Hγ" in
  intros G' γ Hγ; G_norm; G_inst Hγ;
  first [ solve [econstructor; try ac_prem; G_prem]
        | rewrite gren_subst_ty; solve [econstructor; try ac_prem; G_prem] ].

Theorem ac_gwk_all :
  (forall G Γ T T', ac_ty G Γ T T' -> AG_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> AG_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> AG_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> AG_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AG_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AG_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AG_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AG_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> AG_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros; first [solve [eapply G_acs_pt; eassumption] | G_case].
Qed.

(** ** Universe substitution

    [φ] need not be well formed: the judgments do not look at the level
    context. *)

Ltac upush := cbn [usubst_ty usubst_tm ucsubst ulsubst lvsubst gousubst gdecl_usubst].
Ltac upush_in H := cbn [usubst_ty usubst_tm ucsubst ulsubst lvsubst gousubst gdecl_usubst] in H.

Lemma leqv_us {l l'} φ : leqv l l' -> leqv (lvsubst l φ) (lvsubst l' φ).
Proof. intros H; apply leqv_lvsubst; [exact H | intros; apply leqv_refl]. Qed.

Lemma posty_us W φ : posty W -> posty (usubst_ty W φ).
Proof. destruct 1; upush; constructor; now apply whne_ty_usubst. Qed.

Definition AU_ty G Γ T T' : Prop := forall L' φ,
  ac_ty (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ).
Definition AU_tynf G Γ T T' : Prop := forall L' φ,
  ac_tynf (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ).
Definition AU_tyne G Γ T T' : Prop := forall L' φ,
  ac_tyne (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ).
Definition AU_ctx G Δ Δ' : Prop := forall L' φ,
  ac_ctx (gctx_usubst G L' φ) (ucsubst Δ φ) (ucsubst Δ' φ).
Definition AU_tm G Γ t t' T : Prop := forall L' φ,
  ac_tm (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ).
Definition AU_tmnf G Γ t t' T : Prop := forall L' φ,
  ac_tmnf (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ).
Definition AU_tmne G Γ t t' T : Prop := forall L' φ,
  ac_tmne (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ).
Definition AU_tmnee G Γ t t' T : Prop := forall L' φ,
  ac_tmnee (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ).
Definition AU_sub G Γ d d' Θ : Prop := forall L' φ,
  ac_sub (gctx_usubst G L' φ) (ucsubst Γ φ) (ulsubst d φ) (ulsubst d' φ) (ucsubst Θ φ).

Lemma U_branches {G Γ MT Mt l1 l2 bs bs' L' φ} :
  (forall j, j < nbr -> AU_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  forall j, j < nbr -> ac_tm (brG j (gctx_usubst G L' φ))
                       (brΓ j (ucsubst Γ φ) (wrapMT (usubst_ty MT (uup φ))) (wrapMt (usubst_ty Mt (uup φ)))
                          (lvsubst l1 φ) (lvsubst l2 φ))
                       (usubst_tm (bs j) (uupn (br_nu j) φ)) (usubst_tm (bs' j) (uupn (br_nu j) φ))
                       (brRes j (wrapMT (usubst_ty MT (uup φ))) (wrapMt (usubst_ty Mt (uup φ)))).
Proof.
  intros IH j Hj. pose proof (IH j Hj (br_nu j + L') (uupn (br_nu j) φ)) as X.
  rewrite brG_usubst, brΓ_usubst, brRes_usubst in X by exact Hj. exact X.
Qed.

Lemma U_actmne_uapp {G Γ n l T ν ν' ls ls'} : AU_tmnee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' -> AU_tmne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros IH Hn Hls L' φ; upush. change (usubst_ty T[uext ls lvar]ᵤ φ) with (T[uext ls lvar]ᵤ[φ]ᵤ).
  rewrite (usubst_ubeta_ty n ls φ T Hn).
  pose proof (IH L' φ) as X; upush_in X.
  eapply actmne_uapp; [exact X | now rewrite length_map | apply leqvs_lvsubst; [exact Hls | intros; apply leqv_refl]].
Qed.

Lemma U_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> AU_tm G Γ (llk d n) (llk d' n) A[d]) -> AU_sub G Γ d d' Θ.
Proof.
  intros IH L' φ. apply acs_pt. intros n A k Hin.
  destruct (in_ctx_usubst_inv _ _ _ _ _ Hin) as (A0 & k0 & Hin0 & -> & ->).
  rewrite !llk_ulsubst, <- usubst_subst_ty'. exact (IH n A0 k0 Hin0 L' φ).
Qed.

(** Every other rule is closed by one tactic, as for local weakening. *)
Ltac U_norm :=
  upush;
  rewrite ?usubst_lsingle_ty, ?usubst_lsucc_ty, ?usubst_gren_ctx', ?usubst_gren_ty', ?usubst_gren_tm',
          ?usubst_ren', ?usubst_ren_ty', ?gctx_uwk_usubst, ?ucren_ush_usubst, ?uren_ush_usubst_tm,
          ?ubvars_uupn, ?mkrb_usubst, ?motT_usubst, ?mott_usubst, ?wrapMT_usubst, ?wrapMt_usubst,
          ?recGT_usubst, ?recΓT_usubst, ?recGt_usubst, ?recΓt_usubst, ?usubst_gsingle_ty;
  cbn [gousubst]; upush.
Ltac U_norm_in X := revert X; U_norm; intros X.

(** Each induction hypothesis at the substitution that reaches its scope
    ([φ] itself, [φ] under the universe binders of a [UΠ], or under the
    recursor motives' level binder), normalized once. *)
Ltac U_inst L' φ :=
  repeat match goal with
  | IH : forall (L'' : nat) (φ' : nat -> lvl), _ |- _ =>
      let X := fresh "X" in pose proof (IH L' φ) as X;
      lazymatch type of X with
      | context [gctx_usubst (gctx_uwk ?n _) _ _] => clear X; pose proof (IH (n + L') (uupn n φ)) as X
      | context [gctx_usubst (recGT _) _ _] => clear X; pose proof (IH (S L') (uup φ)) as X
      | context [gctx_usubst (recGt _) _ _] => clear X; pose proof (IH (S L') (uup φ)) as X
      | _ => idtac
      end;
      U_norm_in X; clear IH
  end.

Ltac U_prem L' φ :=
  first [ eassumption
        | apply leqv_us; assumption
        | solve [eauto using posty_us, reds_ty_usubst, whnf_ty_usubst, reds_usubst, whnf_usubst, in_ctx_usubst]
        | match goal with
          | Hin : in_gctx _ _ _ |- in_gctx _ _ _ =>
              let X := fresh "X" in pose proof (in_gctx_usubst _ _ _ φ Hin) as X; upush_in X; exact X
          end
        | apply (proj1 leq_usubst_all); [intros; apply leqv_refl | assumption]
        | apply (proj1 (proj2 leq_usubst_all)); [intros; apply leqv_refl | assumption]
        | apply (proj2 (proj2 (proj2 leq_usubst_all))); [intros; apply leqv_refl | assumption]
        | solve [eapply U_branches; eassumption] ].

Ltac U_case :=
  unfold AU_ty, AU_tynf, AU_tyne, AU_ctx, AU_tm, AU_tmnf, AU_tmne, AU_tmnee, AU_sub in *;
  let L' := fresh "L'" in let φ := fresh "φ" in
  intros L' φ; U_norm; U_inst L' φ;
  first [ solve [econstructor; try ac_prem; U_prem L' φ]
        | rewrite usubst_subst_ty'; solve [econstructor; try ac_prem; U_prem L' φ] ].

Theorem ac_us_all :
  (forall G Γ T T', ac_ty G Γ T T' -> AU_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> AU_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> AU_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> AU_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AU_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AU_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AU_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AU_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> AU_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first [solve [eapply U_acs_pt; eassumption] | solve [eapply U_actmne_uapp; eassumption] | U_case].
Qed.

(** ** Closure under [≡ₗ] on the right

    With reflexivity, this gives the instances' [≡ₗ] laws. The right
    side of a recursor is [≡ₗ]-related to a bundle, so it is a bundle. *)

Lemma ctx_leq_trans Γ1 Γ2 Γ3 : ctx_leq Γ1 Γ2 -> ctx_leq Γ2 Γ3 -> ctx_leq Γ1 Γ3.
Proof. apply leq_trans_all. Qed.
Lemma lsub_leq_trans d1 d2 d3 : lsub_leq d1 d2 -> lsub_leq d2 d3 -> lsub_leq d1 d3.
Proof. apply leq_trans_all. Qed.

(** Destruct the variable a [≡ₗ] hypothesis is stuck on. *)
Ltac lstep E :=
  match type of E with
  | ty_leq _ ?x => is_var x; destruct x
  | tm_leq _ ?x => is_var x; destruct x
  | ctx_leq _ ?x => is_var x; destruct x
  | lsub_leq _ ?x => is_var x; destruct x
  | context [match ?x with _ => _ end] => is_var x; destruct x
  end; cbn [ty_leq tm_leq ctx_leq lsub_leq] in E; try contradiction.

Fixpoint unwrap (n : nat) (t : tm) : tm :=
  match n, t with
  | S n, (bindU b | bindG b | bindL b) => unwrap n b
  | _, _ => t
  end.

Lemma unwrap_wrap nu ng nl b : unwrap (nu + ng + nl) (wrap nu ng nl b) = b.
Proof.
  unfold wrap. induction nu as [|nu IH]; cbn [wrapU plus unwrap]; [|exact IH].
  induction ng as [|ng IH']; cbn [wrapG plus unwrap]; [|exact IH'].
  induction nl as [|nl IH'']; cbn [wrapL unwrap]; [reflexivity | exact IH''].
Qed.

Lemma leq_wrap_inv nu ng nl b x : tm_leq (wrap nu ng nl b) x -> exists b', x = wrap nu ng nl b' /\ tm_leq b b'.
Proof.
  unfold wrap. revert x; induction nu as [|nu IH]; intros x E; cbn [wrapU] in *.
  - revert x E; induction ng as [|ng IH']; intros x E; cbn [wrapG] in *.
    + revert x E; induction nl as [|nl IH'']; intros x E; cbn [wrapL] in *; [now exists x|].
      destruct x; cbn [tm_leq] in E; try contradiction.
      destruct (IH'' _ E) as (b' & -> & Eb). now exists b'.
    + destruct x; cbn [tm_leq] in E; try contradiction.
      destruct (IH' _ E) as (b' & -> & Eb). now exists b'.
  - destruct x; cbn [tm_leq] in E; try contradiction.
    destruct (IH _ E) as (b' & -> & Eb). now exists b'.
Qed.

Lemma tup_from_ext f g k n : (forall j, k <= j -> j < k + n -> f j = g j) -> tup_from f k n = tup_from g k n.
Proof.
  revert k; induction n as [|n IH]; intros k H; cbn [tup_from]; [reflexivity|].
  f_equal; [apply H; lia | apply IH; intros j H1 H2; apply H; lia].
Qed.

Lemma leq_tup_from_inv f k n x : tm_leq (tup_from f k n) x ->
  exists g, x = tup_from g k n /\ forall j, k <= j -> j < k + n -> tm_leq (f j) (g j).
Proof.
  revert k x; induction n as [|n IH]; intros k x E; cbn [tup_from] in *.
  - lstep E. exists f; split; [reflexivity | intros; lia].
  - lstep E. destruct E as [Ea Erest].
    destruct (IH _ _ Erest) as (g & -> & Eg).
    match type of Ea with tm_leq _ ?a => exists (fun j => if Nat.eqb j k then a else g j) end. split.
    + rewrite Nat.eqb_refl. f_equal. apply tup_from_ext. intros j H1 _.
      destruct (Nat.eqb_spec j k); [lia | reflexivity].
    + intros j H1 H2. destruct (Nat.eqb_spec j k) as [->|Hne]; [exact Ea | apply Eg; lia].
Qed.

Lemma mkrb_leq_inv MT Mt bs rb : tm_leq (mkrb MT Mt bs) rb ->
  exists MT2 Mt2 bs2, rb = mkrb MT2 Mt2 bs2 /\ ty_leq MT MT2 /\ ty_leq Mt Mt2 /\
    forall k, k < nbr -> tm_leq (bs k) (bs2 k).
Proof.
  unfold mkrb, wrapMT, wrapMt. intros E.
  lstep E. destruct E as [E1 E].
  do 4 lstep E1.
  match goal with |- context [tmTup (bindU (bindG (bindL (tmTy ?T)))) _] => exists T end.
  lstep E. destruct E as [E2 E].
  do 5 lstep E2.
  match goal with |- context [tmTup (bindU (bindG (bindG (bindL (tmTy ?T))))) _] => exists T end.
  destruct (leq_tup_from_inv _ _ _ _ E) as (g & -> & Eg).
  exists (fun k => let '(nu, ng, nl) := br_ar k in unwrap (nu + ng + nl) (g k)).
  split; [| split; [exact E1 | split; [exact E2 |]]].
  - do 2 f_equal. apply tup_from_ext. intros j _ Hj. cbn in Hj.
    specialize (Eg j (Nat.le_0_l j) Hj). destruct (br_ar j) as [[nu ng] nl].
    destruct (leq_wrap_inv _ _ _ _ _ Eg) as (b' & -> & _). now rewrite unwrap_wrap.
  - intros k Hk. specialize (Eg k (Nat.le_0_l k) Hk). destruct (br_ar k) as [[nu ng] nl].
    destruct (leq_wrap_inv _ _ _ _ _ Eg) as (b' & -> & Eb). now rewrite unwrap_wrap.
Qed.

Ltac linv E := lstep E; repeat match type of E with _ /\ _ => let E' := fresh "E" in destruct E as [E' E] end.

#[local] Hint Resolve leqv_trans leqvs_trans ty_leq_trans tm_leq_trans ctx_leq_trans lsub_leq_trans : lq.

Definition AL_ty G Γ T T' : Prop := forall T2, ty_leq T' T2 -> ac_ty G Γ T T2.
Definition AL_tynf G Γ T T' : Prop := forall T2, ty_leq T' T2 -> ac_tynf G Γ T T2.
Definition AL_tyne G Γ T T' : Prop := forall T2, ty_leq T' T2 -> ac_tyne G Γ T T2.
Definition AL_ctx G Δ Δ' : Prop := forall Δ2, ctx_leq Δ' Δ2 -> ac_ctx G Δ Δ2.
Definition AL_tm G Γ t t' T : Prop := forall t2, tm_leq t' t2 -> ac_tm G Γ t t2 T.
Definition AL_tmnf G Γ t t' T : Prop := forall t2, tm_leq t' t2 -> ac_tmnf G Γ t t2 T.
Definition AL_tmne G Γ t t' T : Prop := forall t2, tm_leq t' t2 -> ac_tmne G Γ t t2 T.
Definition AL_tmnee G Γ t t' T : Prop := forall t2, tm_leq t' t2 -> ac_tmnee G Γ t t2 T.
Definition AL_sub G Γ d d' Θ : Prop := forall d2, lsub_leq d' d2 -> ac_sub G Γ d d2 Θ.

Lemma L_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  AL_tynf G Γ W W' -> AL_ty G Γ T T'.
Proof.
  intros H1 H2 H3 H4 IH T2 E. destruct (reds_ty_leq _ _ _ H2 E) as (W2 & HW2 & EW).
  eapply act_red; [exact H1 | exact HW2 | exact H3 | exact (whnf_ty_leq _ _ EW H4) | exact (IH _ EW)].
Qed.

Lemma L_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> AL_tmnf G Γ w w' W -> AL_tm G Γ t t' T.
Proof.
  intros H1 H2 H3 H4 H5 H6 IH t2 E. destruct (reds_leq _ _ _ H4 E) as (w2 & Hw2 & Ew).
  eapply actm_red; [exact H1 | exact H2 | exact H3 | exact Hw2 | exact H5 | exact (whnf_leq _ _ Ew H6)
                   | exact (IH _ Ew)].
Qed.

(** The right bundle, [≡ₗ]-related to [mkrb MT' Mt' bs'], is a bundle. *)
Ltac L_bundle :=
  match goal with Erb : tm_leq (mkrb _ _ _) _ |- _ =>
    let MT2 := fresh "MT2" in let Mt2 := fresh "Mt2" in let bs2 := fresh "bs2" in
    let EMT := fresh "EMT" in let EMt := fresh "EMt" in let Ebs := fresh "Ebs" in
    destruct (mkrb_leq_inv _ _ _ _ Erb) as (MT2 & Mt2 & bs2 & -> & EMT & EMt & Ebs)
  end.

Lemma L_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> AL_tm G Γ (llk d n) (llk d' n) A[d]) -> AL_sub G Γ d d' Θ.
Proof. intros IH d2 E. apply acs_pt. intros n A k Hin. exact (IH n A k Hin _ (llk_leq _ _ n E)). Qed.

(** The right side's [≡ₗ]-image is inverted to the rule's shape (a
    bundle for the recursors), and the rule reapplied; an induction
    hypothesis takes the [≡ₗ] of its sub-structure, or, for the η rules,
    of the expansion. *)
Ltac L_prem :=
  first [ eassumption
        | solve [eauto with lq]
        | match goal with IH : forall x, _ -> _ |- _ =>
            apply IH; cbn [tm_leq ty_leq]; repeat split;
            first [ eassumption | apply leqv_refl | apply leqvs_refl | apply ty_leq_refl | reflexivity
                  | apply leq_ren_tm; eassumption | apply leq_uren_tm; eassumption
                  | apply leq_gren_tm; eassumption ]
          end
        | match goal with IHb : forall k, k < nbr -> forall x, _ -> _, Ebs : forall k, k < nbr -> _ |- _ =>
            let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; exact (IHb k Hk _ (Ebs k Hk))
          end ].

Ltac L_case :=
  unfold AL_ty, AL_tynf, AL_tyne, AL_ctx, AL_tm, AL_tmnf, AL_tmne, AL_tmnee, AL_sub in *;
  let x := fresh "x" in let E := fresh "E" in intros x E;
  first [ solve [econstructor; L_prem]
        | solve [linv E; try L_bundle;
                 try match goal with Es : context [match ?x with _ => _ end] |- _ =>
                       is_var x; linv Es; linv Es end;
                 subst; econstructor; L_prem] ].

Theorem ac_leq_all :
  (forall G Γ T T', ac_ty G Γ T T' -> AL_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> AL_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> AL_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> AL_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AL_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AL_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AL_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AL_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> AL_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first [ solve [eapply L_act_red; eassumption] | solve [eapply L_actm_red; eassumption]
          | solve [eapply L_acs_pt; eassumption] | L_case ].
Qed.

