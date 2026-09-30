(** * The global substitution algebra (ported from spike/Syntax.v)

    Global substitutions are meta-level functions [nat -> gobj]; laws are
    stated pointwise.  As for local substitutions, one mutual induction per
    law, now with a motive on contexts too (global operations traverse
    them).  The [u^δ]/[U^δ] cases instantiate a global object with a local
    substitution ([pty]/[ptm]), and use the local laws. *)
From Coq Require Import Arith Lia.
From DeLaM.Syntax Require Export Subst.

(** ** Instantiation commutes with the local operations *)

Lemma pty_ren o e r : ren_ty (pty o e) r = pty o (lren e r).
Proof. destruct o; cbn; auto. apply (proj1 subst_ren_all). intros; apply llk_lren. Qed.
Lemma ptm_ren o e r : ren_tm (ptm o e) r = ptm o (lren e r).
Proof. destruct o; cbn; auto. apply (proj1 (proj2 subst_ren_all)). intros; apply llk_lren. Qed.
Lemma pdef_ren o b e r : ren_tm (pdef o b e) r = pdef o b (lren e r).
Proof. destruct o; try reflexivity; apply ptm_ren. Qed.
Lemma pty_subst o e d : subst_ty (pty o e) d = pty o (lcomp e d).
Proof. destruct o; cbn; auto. apply (proj1 subst_subst_all). intros; apply llk_lcomp. Qed.
Lemma ptm_subst o e d : subst_tm (ptm o e) d = ptm o (lcomp e d).
Proof. destruct o; cbn; auto. apply (proj1 (proj2 subst_subst_all)). intros; apply llk_lcomp. Qed.
Lemma pdef_subst o b e d : subst_tm (pdef o b e) d = pdef o b (lcomp e d).
Proof. destruct o; try reflexivity; apply ptm_subst. Qed.

(** ** Global substitution commutes with local renaming and substitution *)

Lemma gsubst_ren_all :
  let Pty T := forall r σ, gsubst_ty (ren_ty T r) σ = ren_ty (gsubst_ty T σ) r in
  let Ptm t := forall r σ, gsubst_tm (ren_tm t r) σ = ren_tm (gsubst_tm t σ) r in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof. syn_start; try lk_cases; cbn; rewrite ?pty_ren, ?ptm_ren, ?pdef_ren; law_auto. Qed.
Definition gsubst_ren_tm t := proj1 (proj2 gsubst_ren_all) t.

Lemma llift_gsubst d d' σ : (forall n, llk d' n = gsubst_tm (llk d n) σ) ->
  forall n, llk (llift d') n = gsubst_tm (llk (llift d) n) σ.
Proof. intros H [|n]; rewrite !llk_llift; auto. rewrite H; symmetry; apply gsubst_ren_tm. Qed.

(** Global renaming and substitution, needed for [gwk] under [gsubst]. *)

Lemma goren_goren o ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> goren (goren o ξ) ζ = goren o θ.
Proof.
  intros H; destruct o; cbn; f_equal; auto.
  - now apply (proj1 (proj2 (proj2 gren_gren_all))).
  - now apply (proj1 gren_gren_all).
  - now apply (proj1 (proj2 gren_gren_all)).
Qed.

Lemma pty_gren o e ξ : gren_ty (pty o e) ξ = pty (goren o ξ) (glren e ξ).
Proof. destruct o; cbn; auto. apply (proj1 gren_subst_all). intros; apply llk_glren. Qed.
Lemma ptm_gren o e ξ : gren_tm (ptm o e) ξ = ptm (goren o ξ) (glren e ξ).
Proof. destruct o; cbn; auto. apply (proj1 (proj2 gren_subst_all)). intros; apply llk_glren. Qed.
Lemma pdef_gren o b e ξ : gren_tm (pdef o b e) ξ = pdef (goren o ξ) (gren_tm b ξ) (glren e ξ).
Proof. destruct o; try reflexivity; apply ptm_gren. Qed.
Lemma pctx_gren o ξ : gcren (pctx o) ξ = pctx (goren o ξ).
Proof. destruct o; reflexivity. Qed.

Lemma gup_ext σ τ : (forall i, σ i = τ i) -> forall i, gup σ i = gup τ i.
Proof. intros H [|i]; cbn; auto. now rewrite H. Qed.
Lemma gup_gupr ξ σ τ : (forall i, τ i = σ (ξ i)) -> forall i, gup τ i = gup σ (gupr ξ i).
Proof. intros H [|i]; cbn; auto. now rewrite H. Qed.
Lemma gup_goren σ τ ξ : (forall i, τ i = goren (σ i) ξ) -> forall i, gup τ i = goren (gup σ i) (gupr ξ).
Proof.
  intros H [|i]; cbn; auto. rewrite H.
  rewrite !(goren_goren _ _ _ (fun j => S (ξ j))); auto.
Qed.
#[export] Hint Resolve gup_ext gup_gupr gup_goren : subst.

(** Global substitutions under a level binder. *)
Lemma gouren_gouren o ρ ρ' ρ'' : (forall n, ρ'' n = ρ' (ρ n)) -> gouren (gouren o ρ) ρ' = gouren o ρ''.
Proof.
  intros H; destruct o; cbn; f_equal; auto.
  - now apply (proj1 (proj2 (proj2 uren_uren_all))).
  - now apply (proj1 uren_uren_all).
  - now apply (proj1 (proj2 uren_uren_all)).
Qed.
Lemma gouren_goren o ρ ξ : gouren (goren o ξ) ρ = goren (gouren o ρ) ξ.
Proof.
  destruct o; cbn; f_equal; auto.
  - apply (proj1 (proj2 (proj2 uren_gren_all))).
  - apply (proj1 uren_gren_all).
  - apply (proj1 (proj2 uren_gren_all)).
Qed.
Lemma guwk_ext σ τ : (forall i, σ i = τ i) -> forall i, guwk σ i = guwk τ i.
Proof. intros H i; unfold guwk; now rewrite H. Qed.
Lemma guwk_gupr ξ σ τ : (forall i, τ i = σ (ξ i)) -> forall i, guwk τ i = guwk σ (ξ i).
Proof. intros H i; unfold guwk; now rewrite H. Qed.
Lemma guwk_goren σ τ ξ : (forall i, τ i = goren (σ i) ξ) -> forall i, guwk τ i = goren (guwk σ i) ξ.
Proof. intros H i; unfold guwk; rewrite H. apply gouren_goren. Qed.
Lemma gup_gouren σ τ ρ : (forall i, τ i = gouren (σ i) ρ) -> forall i, gup τ i = gouren (gup σ i) ρ.
Proof. intros H [|i]; cbn; auto. rewrite H. symmetry; apply gouren_goren. Qed.
Lemma guwk_gouren σ τ ρ : (forall i, τ i = gouren (σ i) ρ) ->
  forall i, guwk τ i = gouren (guwk σ i) (uupr ρ).
Proof.
  intros H i; unfold guwk; rewrite H.
  rewrite !(gouren_gouren _ _ _ (fun m => S (ρ m))); auto.
Qed.
#[export] Hint Resolve guwk_ext guwk_gupr guwk_goren gup_gouren guwk_gouren : subst.

Lemma guwkn_ext k σ τ : (forall i, σ i = τ i) -> forall i, guwkn k σ i = guwkn k τ i.
Proof. intros H; unfold guwkn; induction k; [assumption | apply guwk_ext; assumption]. Qed.
Lemma guwkn_gupr k ξ σ τ : (forall i, τ i = σ (ξ i)) -> forall i, guwkn k τ i = guwkn k σ (ξ i).
Proof. intros H; unfold guwkn; induction k; [assumption | apply guwk_gupr; assumption]. Qed.
Lemma guwkn_goren k σ τ ξ : (forall i, τ i = goren (σ i) ξ) -> forall i, guwkn k τ i = goren (guwkn k σ i) ξ.
Proof. intros H; unfold guwkn; induction k; [assumption | apply guwk_goren; assumption]. Qed.
Lemma guwkn_gouren k σ τ ρ : (forall i, τ i = gouren (σ i) ρ) ->
  forall i, guwkn k τ i = gouren (guwkn k σ i) (uuprn k ρ).
Proof. intros H; unfold guwkn, uuprn; induction k; [assumption | apply guwk_gouren; assumption]. Qed.
#[export] Hint Resolve guwkn_ext guwkn_gupr guwkn_goren guwkn_gouren : subst.

Lemma pty_uren o e ρ : uren_ty (pty o e) ρ = pty (gouren o ρ) (ulren e ρ).
Proof. destruct o; cbn; auto. apply (proj1 uren_subst_all). intros; apply llk_ulren. Qed.
Lemma ptm_uren o e ρ : uren_tm (ptm o e) ρ = ptm (gouren o ρ) (ulren e ρ).
Proof. destruct o; cbn; auto. apply (proj1 (proj2 uren_subst_all)). intros; apply llk_ulren. Qed.
Lemma pdef_uren o b e ρ : uren_tm (pdef o b e) ρ = pdef (gouren o ρ) (uren_tm b ρ) (ulren e ρ).
Proof. destruct o; try reflexivity; apply ptm_uren. Qed.
Lemma pctx_uren o ρ : ucren (pctx o) ρ = pctx (gouren o ρ).
Proof. destruct o; reflexivity. Qed.

(** Universe renaming distributes over global substitution. *)
Lemma uren_gsubst_all :
  let Pty T := forall σ ρ τ, (forall i, τ i = gouren (σ i) ρ) -> uren_ty (gsubst_ty T σ) ρ = gsubst_ty (uren_ty T ρ) τ in
  let Ptm t := forall σ ρ τ, (forall i, τ i = gouren (σ i) ρ) -> uren_tm (gsubst_tm t σ) ρ = gsubst_tm (uren_tm t ρ) τ in
  let Pctx Γ := forall σ ρ τ, (forall i, τ i = gouren (σ i) ρ) -> ucren (gcsubst Γ σ) ρ = gcsubst (ucren Γ ρ) τ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn; rewrite ?pty_uren, ?ptm_uren, ?pdef_uren, ?pctx_uren; law_auto.
Qed.
Definition uren_gsubst_tm t := proj1 (proj2 uren_gsubst_all) t.

Lemma uwk_gsubst d d' σ : (forall n, llk d' n = gsubst_tm (llk d n) σ) ->
  forall n, llk (uwk d') n = gsubst_tm (llk (uwk d) n) (guwk σ).
Proof.
  intros H n; unfold uwk; rewrite !llk_ulren, H.
  apply uren_gsubst_tm; reflexivity.
Qed.
#[export] Hint Resolve uwk_gsubst : subst.
Lemma uwkn_gsubst k d d' σ : (forall n, llk d' n = gsubst_tm (llk d n) σ) ->
  forall n, llk (uwkn k d') n = gsubst_tm (llk (uwkn k d) n) (guwkn k σ).
Proof. intros H; unfold uwkn, guwkn; induction k; [assumption | apply uwk_gsubst; assumption]. Qed.
#[export] Hint Resolve uwkn_gsubst : subst.

Lemma gsubst_ext_all :
  let Pty T := forall σ τ, (forall i, σ i = τ i) -> gsubst_ty T σ = gsubst_ty T τ in
  let Ptm t := forall σ τ, (forall i, σ i = τ i) -> gsubst_tm t σ = gsubst_tm t τ in
  let Pctx Γ := forall σ τ, (forall i, σ i = τ i) -> gcsubst Γ σ = gcsubst Γ τ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof. syn_start3; try lk_cases; law_auto. Qed.

Lemma gsubst_gren_all :
  let Pty T := forall ξ σ τ, (forall i, τ i = σ (ξ i)) -> gsubst_ty (gren_ty T ξ) σ = gsubst_ty T τ in
  let Ptm t := forall ξ σ τ, (forall i, τ i = σ (ξ i)) -> gsubst_tm (gren_tm t ξ) σ = gsubst_tm t τ in
  let Pctx Γ := forall ξ σ τ, (forall i, τ i = σ (ξ i)) -> gcsubst (gcren Γ ξ) σ = gcsubst Γ τ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof. syn_start3; try lk_cases; law_auto. Qed.

Lemma gren_gsubst_all :
  let Pty T := forall σ ξ τ, (forall i, τ i = goren (σ i) ξ) -> gren_ty (gsubst_ty T σ) ξ = gsubst_ty T τ in
  let Ptm t := forall σ ξ τ, (forall i, τ i = goren (σ i) ξ) -> gren_tm (gsubst_tm t σ) ξ = gsubst_tm t τ in
  let Pctx Γ := forall σ ξ τ, (forall i, τ i = goren (σ i) ξ) -> gcren (gcsubst Γ σ) ξ = gcsubst Γ τ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn; rewrite ?pty_gren, ?ptm_gren, ?pdef_gren, ?pctx_gren; law_auto.
Qed.

Lemma gwk_gsubst d d' σ : (forall n, llk d' n = gsubst_tm (llk d n) σ) ->
  forall n, llk (gwk d') n = gsubst_tm (llk (gwk d) n) (gup σ).
Proof.
  intros H n; unfold gwk; rewrite !llk_glren, H.
  rewrite (proj1 (proj2 gren_gsubst_all) _ _ _ (fun i => goren (σ i) S)) by auto.
  symmetry; apply (proj1 (proj2 gsubst_gren_all)); auto.
Qed.
#[export] Hint Resolve llift_gsubst gwk_gsubst : subst.

(** [(t[δ])⦃σ⦄ = (t⦃σ⦄)[δ⦃σ⦄]] *)
Lemma gsubst_subst_all :
  let Pty T := forall d σ d', (forall n, llk d' n = gsubst_tm (llk d n) σ) ->
               gsubst_ty (subst_ty T d) σ = subst_ty (gsubst_ty T σ) d' in
  let Ptm t := forall d σ d', (forall n, llk d' n = gsubst_tm (llk d n) σ) ->
               gsubst_tm (subst_tm t d) σ = subst_tm (gsubst_tm t σ) d' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases; cbn; rewrite ?pty_subst, ?ptm_subst, ?pdef_subst; law_auto.
  all: now rewrite H.
Qed.

(** Composition of global substitutions. *)
Lemma pty_gsubst o e τ : gsubst_ty (pty o e) τ = pty (gosubst o τ) (glsubst e τ).
Proof. destruct o; cbn; auto. apply (proj1 gsubst_subst_all). intros; apply llk_glsubst. Qed.
Lemma ptm_gsubst o e τ : gsubst_tm (ptm o e) τ = ptm (gosubst o τ) (glsubst e τ).
Proof. destruct o; cbn; auto. apply (proj1 (proj2 gsubst_subst_all)). intros; apply llk_glsubst. Qed.
Lemma pdef_gsubst o b e τ : gsubst_tm (pdef o b e) τ = pdef (gosubst o τ) (gsubst_tm b τ) (glsubst e τ).
Proof. destruct o; try reflexivity; apply ptm_gsubst. Qed.
Lemma pctx_gsubst o τ : gcsubst (pctx o) τ = pctx (gosubst o τ).
Proof. destruct o; reflexivity. Qed.

Lemma goren_gosubst o τ : goren (gosubst o τ) S = gosubst (goren o S) (gup τ).
Proof.
  destruct o; cbn; auto; f_equal.
  - rewrite (proj1 (proj2 (proj2 gren_gsubst_all)) _ _ _ (fun i => goren (τ i) S)) by auto.
    symmetry; apply (proj1 (proj2 (proj2 gsubst_gren_all))); auto.
  - rewrite (proj1 gren_gsubst_all _ _ _ (fun i => goren (τ i) S)) by auto.
    symmetry; apply (proj1 gsubst_gren_all); auto.
  - rewrite (proj1 (proj2 gren_gsubst_all) _ _ _ (fun i => goren (τ i) S)) by auto.
    symmetry; apply (proj1 (proj2 gsubst_gren_all)); auto.
Qed.
Lemma gup_gosubst σ τ θ : (forall i, θ i = gosubst (σ i) τ) -> forall i, gup θ i = gosubst (gup σ i) (gup τ).
Proof. intros H [|i]; cbn; auto. rewrite H. apply goren_gosubst. Qed.
Lemma gouren_gosubst o τ : gouren (gosubst o τ) S = gosubst (gouren o S) (guwk τ).
Proof.
  destruct o; cbn; auto; f_equal.
  - apply (proj1 (proj2 (proj2 uren_gsubst_all))); reflexivity.
  - apply (proj1 uren_gsubst_all); reflexivity.
  - apply (proj1 (proj2 uren_gsubst_all)); reflexivity.
Qed.
Lemma guwk_gosubst σ τ θ : (forall i, θ i = gosubst (σ i) τ) -> forall i, guwk θ i = gosubst (guwk σ i) (guwk τ).
Proof. intros H i; unfold guwk at 1; rewrite H. apply gouren_gosubst. Qed.
#[export] Hint Resolve gup_gosubst guwk_gosubst : subst.
Lemma guwkn_gosubst k σ τ θ : (forall i, θ i = gosubst (σ i) τ) ->
  forall i, guwkn k θ i = gosubst (guwkn k σ i) (guwkn k τ).
Proof. intros H; unfold guwkn; induction k; [assumption | apply guwk_gosubst; assumption]. Qed.
#[export] Hint Resolve guwkn_gosubst : subst.

Lemma gsubst_gsubst_all :
  let Pty T := forall σ τ θ, (forall i, θ i = gosubst (σ i) τ) -> gsubst_ty (gsubst_ty T σ) τ = gsubst_ty T θ in
  let Ptm t := forall σ τ θ, (forall i, θ i = gosubst (σ i) τ) -> gsubst_tm (gsubst_tm t σ) τ = gsubst_tm t θ in
  let Pctx Γ := forall σ τ θ, (forall i, θ i = gosubst (σ i) τ) -> gcsubst (gcsubst Γ σ) τ = gcsubst Γ θ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn; rewrite ?pty_gsubst, ?ptm_gsubst, ?pdef_gsubst, ?pctx_gsubst; law_auto.
Qed.

(** Identity: needs the deep normal form (box contents and the contexts
    and types of [□]/[letbox] included, since global substitution enters
    them). *)

Fixpoint dnfty (T : ty) : Prop :=
  match T with
  | tyErr | tyNat | tyU _ | tyUnit _ | tySEmpty _ | tyEmpty _ => True
  | tySEq _ A a b => dnfty A /\ dnftm a /\ dnftm b
  | tyId _ A a b => dnfty A /\ dnftm a /\ dnftm b
  | tyPi _ _ A B | tySig _ _ A B => dnfty A /\ dnfty B
  | tyEl _ t => dnftm t
  | tyGvar _ d => dnfl d
  | tyCTyp Δ _ => dnfctx Δ
  | tyCTrm Δ T _ => dnfctx Δ /\ dnfty T
  | tyUPi _ _ T => dnfty T
  | tyCPi _ T => dnfty T
  | tyTPi Δ _ _ T => dnfctx Δ /\ dnfty T
  end
with dnftm (t : tm) : Prop :=
  match t with
  | var _ | tmErr | tmNat | tmU _ | zero | tmUnit _ | tmTriv _ | tmSEmpty _ => True
  | tmPi _ _ s t | tmSig _ _ s t => dnftm s /\ dnftm t
  | succ t => dnftm t
  | natrec _ M s z t => dnfty M /\ dnftm s /\ dnftm z /\ dnftm t
  | lam _ _ A t => dnfty A /\ dnftm t
  | app t _ _ A B s => dnftm t /\ dnfty A /\ dnfty B /\ dnftm s
  | gvar _ d => dnfl d
  | gdef _ b d => dnftm b /\ dnfl d
  | boxT T => dnfty T
  | boxt t => dnftm t
  | letboxT _ _ Δ M t' t => dnfctx Δ /\ dnfty M /\ dnftm t' /\ dnftm t
  | letboxt _ _ Δ T M t' t => dnfctx Δ /\ dnfty T /\ dnfty M /\ dnftm t' /\ dnftm t
  | tmTy T => dnfty T
  | tmTup s t => dnftm s /\ dnftm t
  | bindU b | bindG b | bindL b => dnftm b
  | elimT _ _ rb _ Δ t => dnftm rb /\ dnfctx Δ /\ dnftm t
  | elimt _ _ rb _ Δ T t => dnftm rb /\ dnfctx Δ /\ dnfty T /\ dnftm t
  | uapp t _ => dnftm t
  | ulam _ _ T t | clam _ T t => dnfty T /\ dnftm t
  | tlam Δ _ _ T t => dnfctx Δ /\ dnfty T /\ dnftm t
  | capp t Δ => dnftm t /\ dnfctx Δ
  | tapp t T => dnftm t /\ dnfty T
  | tmPair _ _ A B a b => dnfty A /\ dnfty B /\ dnftm a /\ dnftm b
  | tmFst _ _ A B p | tmSnd _ _ A B p => dnfty A /\ dnfty B /\ dnftm p
  | srefl _ A a | elimSEmpty _ _ A a | elimEmpty _ _ A a => dnfty A /\ dnftm a
  | tmRefl _ A a => dnfty A /\ dnftm a
  | tmId _ s t u => dnftm s /\ dnftm t /\ dnftm u
  | tmSEq _ s t u => dnftm s /\ dnftm t /\ dnftm u
  | tmJ _ _ A a M c u e => dnfty A /\ dnftm a /\ dnfty M /\ dnftm c /\ dnftm u /\ dnftm e
  end
with dnfctx (Γ : ctx) : Prop :=
  match Γ with cnil | cvar _ => True | cext Γ A _ => dnfctx Γ /\ dnfty A end
with dnfl (d : lsub) : Prop :=
  match d with lshift _ => True | lcons d t => dnfl d /\ dnftm t /\ ~ labsorb d t end.

Lemma dnfl_nf d : dnfl d -> nf_l d.
Proof. induction d; cbn; tauto. Qed.
Lemma dnfl_llk d n : dnfl d -> dnftm (llk d n).
Proof. revert n; induction d as [k|d IH t]; intros [|n] H; cbn in *; try tauto. apply IH; tauto. Qed.
#[export] Hint Resolve dnfl_nf dnfl_llk : nf.

Ltac lk_cases_dnf :=
  match goal with
  | |- LK _ (lshift _) => intros ?n; cbn; intros; auto
  | Hn : dnfl (lcons ?d ?t), IHd : dnfl ?d -> LK _ ?d |- LK _ (lcons ?d ?t) =>
      cbn in Hn; destruct Hn as (?Hd & ?Ht & ?Ha);
      intros [|?n]; cbn; [assumption | exact (IHd ltac:(assumption) _)]
  end.
Lemma gsubst_id_all :
  let Pty T := dnfty T -> forall σ, (forall i, σ i = GId i) -> gsubst_ty T σ = T in
  let Ptm t := dnftm t -> forall σ, (forall i, σ i = GId i) -> gsubst_tm t σ = t in
  let Pctx Γ := dnfctx Γ -> forall σ, (forall i, σ i = GId i) -> gcsubst Γ σ = Γ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, dnfl d -> LK Ptm d).
Proof.
  assert (Hup : forall σ, (forall i, σ i = GId i) -> forall i, gup σ i = GId i).
  { intros σ H [|i]; cbn; auto. now rewrite H. }
  assert (Huw : forall σ, (forall i, σ i = GId i) -> forall i, guwk σ i = GId i).
  { intros σ H i; unfold guwk; now rewrite H. }
  assert (Huwn : forall k σ, (forall i, σ i = GId i) -> forall i, guwkn k σ i = GId i).
  { intros k σ H; unfold guwkn; induction k; [assumption | apply Huw; assumption]. }
  syn_start3; try lk_cases_dnf; cbn in *; try tauto;
    try solve [f_equal; intuition eauto].
  all: match goal with Hs : forall i, ?σ i = GId i |- context [?σ ?u] => rewrite Hs; cbn end;
    try reflexivity.
  all: f_equal; repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: first
    [ (* a defined global's body *)
      match goal with IH : dnftm ?b -> _ |- gsubst_tm ?b _ = ?b => apply IH; assumption end
    | apply l_canon; auto with nf; intros n;
      rewrite llk_glsubst; match goal with IH : dnfl ?d -> LK _ ?d |- _ => apply IH end; auto with nf ].
Qed.

(** ** Exported laws, in notation form *)

Section GLaws.
Lemma gsubst_ren_ty (T : ty) r σ : T⟨r⟩⦃σ⦄ = T⦃σ⦄⟨r⟩.
Proof. apply (proj1 gsubst_ren_all). Qed.
Lemma gsubst_ren (t : tm) r σ : t⟨r⟩⦃σ⦄ = t⦃σ⦄⟨r⟩.
Proof. apply (proj1 (proj2 gsubst_ren_all)). Qed.
Lemma gsubst_subst_ty (T : ty) d σ : T[d]⦃σ⦄ = T⦃σ⦄[d⦃σ⦄].
Proof. apply (proj1 gsubst_subst_all). intros; apply llk_glsubst. Qed.
Lemma gsubst_subst (t : tm) d σ : t[d]⦃σ⦄ = t⦃σ⦄[d⦃σ⦄].
Proof. apply (proj1 (proj2 gsubst_subst_all)). intros; apply llk_glsubst. Qed.
Lemma gren_ren_ty (T : ty) r ξ : T⟨r⟩⟪ξ⟫ = T⟪ξ⟫⟨r⟩.
Proof. apply (proj1 gren_ren_all). Qed.
Lemma gren_ren (t : tm) r ξ : t⟨r⟩⟪ξ⟫ = t⟪ξ⟫⟨r⟩.
Proof. apply (proj1 (proj2 gren_ren_all)). Qed.
Lemma gren_subst_ty (T : ty) d ξ : T[d]⟪ξ⟫ = T⟪ξ⟫[d⟪ξ⟫].
Proof. apply (proj1 gren_subst_all). intros; apply llk_glren. Qed.
Lemma gren_subst (t : tm) d ξ : t[d]⟪ξ⟫ = t⟪ξ⟫[d⟪ξ⟫].
Proof. apply (proj1 (proj2 gren_subst_all)). intros; apply llk_glren. Qed.
Lemma gsubst_gsubst_ty (T : ty) σ τ θ : (forall i, θ i = gosubst (σ i) τ) -> T⦃σ⦄⦃τ⦄ = T⦃θ⦄.
Proof. apply (proj1 gsubst_gsubst_all). Qed.
Lemma gsubst_gsubst (t : tm) σ τ θ : (forall i, θ i = gosubst (σ i) τ) -> t⦃σ⦄⦃τ⦄ = t⦃θ⦄.
Proof. apply (proj1 (proj2 gsubst_gsubst_all)). Qed.
Lemma gsubst_gsubst_ctx (Γ : ctx) σ τ θ : (forall i, θ i = gosubst (σ i) τ) -> Γ⦃σ⦄⦃τ⦄ = Γ⦃θ⦄.
Proof. apply (proj1 (proj2 (proj2 gsubst_gsubst_all))). Qed.
Lemma gsubst_id_ty (T : ty) σ : dnfty T -> (forall i, σ i = GId i) -> T⦃σ⦄ = T.
Proof. intros; apply (proj1 gsubst_id_all); auto. Qed.
Lemma gsubst_id (t : tm) σ : dnftm t -> (forall i, σ i = GId i) -> t⦃σ⦄ = t.
Proof. intros; apply (proj1 (proj2 gsubst_id_all)); auto. Qed.
Lemma gsubst_id_ctx (Γ : ctx) σ : dnfctx Γ -> (forall i, σ i = GId i) -> Γ⦃σ⦄ = Γ.
Proof. intros; apply (proj1 (proj2 (proj2 gsubst_id_all))); auto. Qed.
End GLaws.

Print Assumptions gsubst_gsubst.

(** ** Global renaming: outputs are deep-normal; identity on deep-normal input *)

Lemma dnfl_lcons' d t : dnfl d -> dnftm t -> dnfl (lcons' d t).
Proof.
  intros Hd Ht. destruct d as [[|k]|]; destruct t; cbn in *; try tauto.
  destruct (Nat.eqb_spec n k); cbn; auto.
Qed.

Lemma gren_dnf_all :
  let Pty T := forall ξ, dnfty (gren_ty T ξ) in
  let Ptm t := forall ξ, dnftm (gren_tm t ξ) in
  let Pctx Γ := forall ξ, dnfctx (gcren Γ ξ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, forall ξ, dnfl (glren d ξ)).
Proof.
  intros Pty Ptm Pctx; apply syn_ind; subst Pty Ptm Pctx; cbn beta; intros; try exact I;
    cbn; intuition auto using dnfl_lcons'.
Qed.

Lemma uren_dnf_all :
  let Pty T := forall ρ, dnfty (uren_ty T ρ) in
  let Ptm t := forall ρ, dnftm (uren_tm t ρ) in
  let Pctx Γ := forall ρ, dnfctx (ucren Γ ρ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, forall ρ, dnfl (ulren d ρ)).
Proof.
  intros Pty Ptm Pctx; apply syn_ind; subst Pty Ptm Pctx; cbn beta; intros; try exact I;
    cbn; intuition auto using dnfl_lcons'.
Qed.

Lemma gren_id_all :
  let Pty T := dnfty T -> forall ξ, (forall i, ξ i = i) -> gren_ty T ξ = T in
  let Ptm t := dnftm t -> forall ξ, (forall i, ξ i = i) -> gren_tm t ξ = t in
  let Pctx Γ := dnfctx Γ -> forall ξ, (forall i, ξ i = i) -> gcren Γ ξ = Γ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, dnfl d -> LK Ptm d).
Proof.
  assert (Hup : forall ξ, (forall i, ξ i = i) -> forall i, gupr ξ i = i).
  { intros ξ H [|i]; cbn; auto. }
  syn_start3; try lk_cases_dnf; cbn in *; try tauto;
    try solve [f_equal; intuition eauto].
  all: try match goal with Hs : forall i, ?ξ i = i |- context [?ξ ?u] => rewrite Hs end.
  all: f_equal; repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: first
    [ (* a defined global's body *)
      match goal with IH : dnftm ?b -> _ |- gren_tm ?b _ = ?b => apply IH; assumption end
    | apply l_canon; auto with nf; intros n;
      rewrite llk_glren; match goal with IH : dnfl ?d -> LK _ ?d |- _ => apply IH end; auto with nf ].
Qed.

(** ** Deep normal forms: preserved by the local operations; imply [nf] *)

Lemma dnf_nf_all :
  let Pty T := dnfty T -> nfty T in
  let Ptm t := dnftm t -> nftm t in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, dnfl d -> nfl d).
Proof.
  intros Pty Ptm; apply syn_ind; subst Pty Ptm; cbn beta; intros; try exact I; cbn in *; intuition.
Qed.
Lemma dnfl_nfl d : dnfl d -> nfl d.
Proof. apply dnf_nf_all. Qed.
Lemma dnftm_nftm t : dnftm t -> nftm t.
Proof. apply dnf_nf_all. Qed.
Lemma dnfty_nfty T : dnfty T -> nfty T.
Proof. apply dnf_nf_all. Qed.

Lemma dnfl_r2l r : dnfl (r2l r).
Proof. induction r; cbn; auto. apply dnfl_lcons'; cbn; auto. Qed.
Lemma dnfl_lnorm d : dnfl d -> dnfl (lnorm d).
Proof. induction d; cbn; intuition auto using dnfl_lcons'. Qed.

Lemma ren_dnf_all :
  let Pty T := dnfty T -> forall r, dnfty (ren_ty T r) in
  let Ptm t := dnftm t -> forall r, dnftm (ren_tm t r) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\
  (forall d, dnfl d -> forall r, dnfl (lren d r)).
Proof.
  intros Pty Ptm; apply syn_ind; subst Pty Ptm; cbn beta; intros; try exact I;
    cbn in *; intuition auto using dnfl_r2l, dnfl_lcons'.
Qed.
Lemma ren_dnf (t : tm) r : dnftm t -> dnftm t⟨r⟩.
Proof. intros; now apply ren_dnf_all. Qed.
Lemma ren_dnf_ty (T : ty) r : dnfty T -> dnfty T⟨r⟩.
Proof. intros; now apply ren_dnf_all. Qed.
Lemma dnfl_lren d r : dnfl d -> dnfl (lren d r).
Proof. intros; now apply ren_dnf_all. Qed.

Lemma dnfl_ldrop k d : dnfl d -> dnfl (ldrop k d).
Proof. revert d; induction k; intros [m|d t]; cbn; intuition. Qed.
Lemma dnfl_lnorm_lk d : LK dnftm d -> dnfl (lnorm d).
Proof.
  induction d as [k|d IH t]; intros H; cbn; auto.
  apply dnfl_lcons'; [apply IH; intros n; exact (H (S n)) | exact (H 0)].
Qed.
Lemma lk_dnf_llift d : LK dnftm d -> LK dnftm (llift d).
Proof. intros H [|n]; rewrite llk_llift; cbn; [exact I | apply ren_dnf, H]. Qed.
Lemma lk_dnf_gwk d : LK dnftm d -> LK dnftm (gwk d).
Proof. intros H n; unfold gwk; rewrite llk_glren; apply gren_dnf_all. Qed.
Lemma lk_dnf_ldrop k d : LK dnftm d -> LK dnftm (ldrop k d).
Proof. intros H n; rewrite llk_ldrop; apply H. Qed.
Lemma lk_dnf_uwk d : LK dnftm (uwk d).
Proof. intros n; unfold uwk; rewrite llk_ulren; apply uren_dnf_all. Qed.
Lemma lk_dnf_uwkn k d : LK dnftm d -> LK dnftm (uwkn k d).
Proof. intros H; unfold uwkn; induction k; [assumption | apply lk_dnf_uwk]. Qed.
#[export] Hint Resolve lk_dnf_llift lk_dnf_gwk lk_dnf_ldrop dnfl_lnorm_lk lk_dnf_uwk lk_dnf_uwkn : nf.

Lemma subst_dnf_all :
  let Pty T := dnfty T -> forall d, LK dnftm d -> dnfty (subst_ty T d) in
  let Ptm t := dnftm t -> forall d, LK dnftm d -> dnftm (subst_tm t d) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\
  (forall d0, dnfl d0 -> forall d, LK dnftm d -> dnfl (lcomp d0 d)).
Proof.
  intros Pty Ptm; apply syn_ind; subst Pty Ptm; cbn beta; intros; try exact I;
    cbn in *; intuition eauto 6 with nf.
  apply dnfl_lcons'; intuition eauto.
Qed.
Lemma subst_dnf (t : tm) d : dnftm t -> LK dnftm d -> dnftm t[d].
Proof. intros; now apply subst_dnf_all. Qed.
Lemma subst_dnf_ty (T : ty) d : dnfty T -> LK dnftm d -> dnfty T[d].
Proof. intros; now apply subst_dnf_all. Qed.
Lemma dnfl_lcomp d0 d : dnfl d0 -> LK dnftm d -> dnfl (lcomp d0 d).
Proof. intros; now apply subst_dnf_all. Qed.

Definition dnfo (o : gobj) : Prop :=
  match o with GId _ => True | GCtx Γ => dnfctx Γ | GTy T => dnfty T | GTm t => dnftm t end.

Lemma dnfo_goren o ξ : dnfo (goren o ξ).
Proof. destruct o; cbn; [exact I | apply gren_dnf_all..]. Qed.
Lemma dnfo_gouren o ρ : dnfo (gouren o ρ).
Proof. destruct o; cbn; [exact I | apply uren_dnf_all..]. Qed.

Lemma gsubst_dnf_all :
  let Pty T := dnfty T -> forall σ, (forall i, dnfo (σ i)) -> dnfty (gsubst_ty T σ) in
  let Ptm t := dnftm t -> forall σ, (forall i, dnfo (σ i)) -> dnftm (gsubst_tm t σ) in
  let Pctx Γ := dnfctx Γ -> forall σ, (forall i, dnfo (σ i)) -> dnfctx (gcsubst Γ σ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\
  (forall d, dnfl d -> forall σ, (forall i, dnfo (σ i)) -> dnfl (glsubst d σ)).
Proof.
  assert (Hup : forall σ, (forall i, dnfo (σ i)) -> forall i, dnfo (gup σ i)).
  { intros σ H [|i]; cbn; auto using dnfo_goren. }
  assert (Huw : forall σ, (forall i, dnfo (σ i)) -> forall i, dnfo (guwk σ i)).
  { intros σ H i; apply dnfo_gouren. }
  assert (Huwn : forall k σ, (forall i, dnfo (σ i)) -> forall i, dnfo (guwkn k σ i)).
  { intros k σ H; unfold guwkn; induction k; [assumption | apply Huw; assumption]. }
  intros Pty Ptm Pctx; apply syn_ind; subst Pty Ptm Pctx; cbn beta; intros; try exact I;
    cbn in *; intuition auto using dnfl_lcons'.
  all: match goal with Hs : forall i, dnfo (?σ i) |- context [?σ ?u] =>
         let Hu := fresh "Hu" in pose proof (Hs u) as Hu; destruct (σ u); cbn in *; auto end.
  all: apply subst_dnf_all; auto; intros n; apply dnfl_llk; auto.
Qed.
