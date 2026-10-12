(** * Level equivalence of syntax: substitutions and global substitutions

    One of the parts [LevelEq] puts together; they build in parallel. *)
From DeLaM.Syntax Require Export LevelEqRen LevelEqURen.

Definition leq_ren_tm t := proj1 (proj2 leq_ren_all) t.
Definition leq_gren_tm t := proj1 (proj2 leq_gren_all) t.
Definition leq_uren_tm t := proj1 (proj2 leq_uren_all) t.
Lemma leq_llift d d' : lsub_leq d d' -> lsub_leq (llift d) (llift d').
Proof. intros H; unfold llift; apply lcons'_leq; [apply (proj2 (proj2 (proj2 leq_ren_all))), H | reflexivity]. Qed.
Lemma leq_gwk d d' : lsub_leq d d' -> lsub_leq (gwk d) (gwk d').
Proof. intros H; apply (proj2 (proj2 (proj2 leq_gren_all))), H. Qed.
Lemma leq_uwk d d' : lsub_leq d d' -> lsub_leq (uwk d) (uwk d').
Proof. intros H; apply (proj2 (proj2 (proj2 leq_uren_all))), H. Qed.
Lemma leq_uwkn k d d' : lsub_leq d d' -> lsub_leq (uwkn k d) (uwkn k d').
Proof. intros H; unfold uwkn; induction k; [assumption | apply leq_uwk; assumption]. Qed.
#[export] Hint Resolve leq_llift leq_gwk leq_uwk leq_uwkn : leq.

Lemma leq_subst_all :
  let Pty T := forall T' d d', lsub_leq d d' -> ty_leq T T' -> ty_leq (subst_ty T d) (subst_ty T' d') in
  let Ptm t := forall t' d d', lsub_leq d d' -> tm_leq t t' -> tm_leq (subst_tm t d) (subst_tm t' d') in
  let Pctx (Γ : ctx) := True in
  let Pl e := forall e' d d', lsub_leq d d' -> lsub_leq e e' -> lsub_leq (lcomp e d) (lcomp e' d') in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try exact I; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.

Lemma gobj_leq_goren o o' ξ : gobj_leq o o' -> gobj_leq (goren o ξ) (goren o' ξ).
Proof.
  destruct o, o'; cbn; try contradiction; intros H; subst; auto;
    first [apply (proj1 (proj2 (proj2 leq_gren_all))) | apply (proj1 leq_gren_all) | apply (proj1 (proj2 leq_gren_all))];
    exact H.
Qed.
Lemma gobj_leq_gouren o o' ρ : gobj_leq o o' -> gobj_leq (gouren o ρ) (gouren o' ρ).
Proof.
  destruct o, o'; cbn; try contradiction; intros H; subst; auto;
    first [apply (proj1 (proj2 (proj2 leq_uren_all))) | apply (proj1 leq_uren_all) | apply (proj1 (proj2 leq_uren_all))];
    exact H.
Qed.
Lemma gobj_leq_gup σ σ' : (forall i, gobj_leq (σ i) (σ' i)) -> forall i, gobj_leq (gup σ i) (gup σ' i).
Proof. intros H [|i]; cbn; [reflexivity | apply gobj_leq_goren, H]. Qed.
Lemma gobj_leq_guwk σ σ' : (forall i, gobj_leq (σ i) (σ' i)) -> forall i, gobj_leq (guwk σ i) (guwk σ' i).
Proof. intros H i; apply gobj_leq_gouren, H. Qed.
Lemma pty_leq o o' d d' : gobj_leq o o' -> lsub_leq d d' -> ty_leq (pty o d) (pty o' d').
Proof.
  destruct o, o'; cbn; try contradiction; intros H Hd; subst; cbn; auto;
    apply (proj1 leq_subst_all); assumption.
Qed.
Lemma ptm_leq o o' d d' : gobj_leq o o' -> lsub_leq d d' -> tm_leq (ptm o d) (ptm o' d').
Proof.
  destruct o, o'; cbn; try contradiction; intros H Hd; subst; cbn; auto;
    apply (proj1 (proj2 leq_subst_all)); assumption.
Qed.
Lemma pdef_leq o o' b b' d d' : gobj_leq o o' -> tm_leq b b' -> lsub_leq d d' ->
  tm_leq (pdef o b d) (pdef o' b' d').
Proof.
  intros H Hb Hd. destruct o, o'; cbn in H; try contradiction; subst; cbn; auto;
    apply (proj1 (proj2 leq_subst_all)); assumption.
Qed.
Lemma pctx_leq o o' : gobj_leq o o' -> ctx_leq (pctx o) (pctx o').
Proof. destruct o, o'; cbn; try contradiction; intros H; subst; auto. Qed.
Lemma gobj_leq_guwkn k σ σ' : (forall i, gobj_leq (σ i) (σ' i)) -> forall i, gobj_leq (guwkn k σ i) (guwkn k σ' i).
Proof. intros H; unfold guwkn; induction k; [assumption | apply gobj_leq_guwk; assumption]. Qed.
#[export] Hint Resolve gobj_leq_gup gobj_leq_guwk gobj_leq_guwkn pty_leq ptm_leq pdef_leq pctx_leq : leq.

Lemma leq_gsubst_all :
  let Pty T := forall T' σ σ', (forall i, gobj_leq (σ i) (σ' i)) -> ty_leq T T' ->
    ty_leq (gsubst_ty T σ) (gsubst_ty T' σ') in
  let Ptm t := forall t' σ σ', (forall i, gobj_leq (σ i) (σ' i)) -> tm_leq t t' ->
    tm_leq (gsubst_tm t σ) (gsubst_tm t' σ') in
  let Pctx Γ := forall Γ' σ σ', (forall i, gobj_leq (σ i) (σ' i)) -> ctx_leq Γ Γ' ->
    ctx_leq (gcsubst Γ σ) (gcsubst Γ' σ') in
  let Pl d := forall d' σ σ', (forall i, gobj_leq (σ i) (σ' i)) -> lsub_leq d d' ->
    lsub_leq (glsubst d σ) (glsubst d' σ') in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try leq_cases; cbn in *; try contradiction; intuition (subst; eauto with leq). Qed.
