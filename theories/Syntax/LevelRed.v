(** * Reduction and normal forms up to level equivalence (M3_DESIGN.md E6')

    Level annotations never affect computation: [≡ₗ]-related terms have
    related reducts, and weak-head normal forms are closed under [≡ₗ].
    With determinism, the weak-head normal forms of related terms are
    related. *)
From DeLaM.Syntax Require Export Reduction.

(** [leq_cases], also through the nested matches [cbn] leaves when a
    pattern has depth two. *)
Ltac leq_cases' := first
  [ leq_cases
  | match goal with H : context [match ?x with _ => _ end] |- _ =>
      is_var x; destruct x; try exact (False_ind _ H); cbn in H; try contradiction end ].
(** Split all relation hypotheses down to variables. *)
Ltac leq_split := repeat first
  [ match goal with H : _ /\ _ |- _ => destruct H | H : False |- _ => destruct H end
  | leq_cases' ].

(** ** Normal forms *)

Lemma whne_leq t t' : tm_leq t t' -> whne t -> whne t'.
Proof.
  intros E H; revert t' E; induction H; intros x E; leq_split; subst; eauto with whnf.
Qed.

Lemma whnf_leq t t' : tm_leq t t' -> whnf t -> whnf t'.
Proof.
  intros E H; destruct H; leq_split; eauto using whne_leq with whnf.
Qed.

Lemma whne_ty_leq T T' : ty_leq T T' -> whne_ty T -> whne_ty T'.
Proof.
  intros E H; destruct H; leq_split; subst; eauto using whne_leq with whnf.
Qed.

Lemma whnf_ty_leq T T' : ty_leq T T' -> whnf_ty T -> whnf_ty T'.
Proof.
  intros E H; destruct H; leq_split; eauto using whne_ty_leq with whnf.
Qed.

(** ** Single substitutions and peeling *)

Lemma leq_lsingle s s' : tm_leq s s' -> lsub_leq (lsingle s) (lsingle s').
Proof. intros; cbn; auto. Qed.
Lemma leq_lsingle2 t t' r r' : tm_leq t t' -> tm_leq r r' -> lsub_leq (lsingle2 t r) (lsingle2 t' r').
Proof. intros; cbn; auto. Qed.
Lemma leq_gsingle o o' : gobj_leq o o' -> forall i, gobj_leq (gsingle o i) (gsingle o' i).
Proof. intros H [|i]; cbn; auto. Qed.
Lemma leq_usingle l l' : leqv l l' -> forall n, leqv (usingle l n) (usingle l' n).
Proof. intros H [|n]; cbn; auto using leqv_refl. Qed.

Lemma leq_peelU b b' l l' : tm_leq b b' -> leqv l l' -> tm_leq (peelU b l) (peelU b' l').
Proof.
  intros E Hl; destruct b; leq_split; cbn; auto.
  apply (proj1 (proj2 leq_usubst_all)); [apply leq_usingle, Hl | exact E].
Qed.
Lemma leq_peelG b b' o o' : tm_leq b b' -> gobj_leq o o' -> tm_leq (peelG b o) (peelG b' o').
Proof.
  intros E Ho; destruct b; leq_split; cbn; auto.
  apply (proj1 (proj2 leq_gsubst_all)); [apply leq_gsingle, Ho | exact E].
Qed.
Lemma leq_peelL b b' a a' : tm_leq b b' -> tm_leq a a' -> tm_leq (peelL b a) (peelL b' a').
Proof.
  intros E Ha; destruct b; leq_split; cbn; auto.
  apply (proj1 (proj2 leq_subst_all)); [apply leq_lsingle, Ha | exact E].
Qed.

Lemma leq_tup_nth t t' k : tm_leq t t' -> tm_leq (tup_nth t k) (tup_nth t' k).
Proof.
  revert t t'; induction k as [|k IH]; intros t t' E; destruct t; leq_split; cbn in *;
    intuition.
Qed.
Lemma leq_rb_br rb rb' k : tm_leq rb rb' -> tm_leq (rb_br rb k) (rb_br rb' k).
Proof. apply leq_tup_nth. Qed.

Lemma leqv_uext ls ls' φ : Forall2 leqv ls ls' -> forall i, leqv (uext ls φ i) (uext ls' φ i).
Proof.
  intros H i; unfold uext. rewrite <- (Forall2_length H).
  destruct (i <? length ls); [|apply leqv_refl].
  remember (length ls - S i) as k eqn:Ek; clear Ek. revert k; induction H; intros [|k]; cbn;
    auto using leqv_refl.
Qed.

#[export] Hint Resolve leq_peelU leq_peelG leq_peelL leq_rb_br leq_lsingle : leq.

(** ** The β reducts *)

Section Reducts.
Context {l1 l2 l1' l2' rb rb'} (E1 : leqv l1 l1') (E2 : leqv l2 l2') (Erb : tm_leq rb rb').

Lemma leqv_lsuc a b : leqv a b -> leqv (lsuc a) (lsuc b).
Proof using . intros H v; cbn; now rewrite H. Qed.
Lemma leqv_lmax a b a' b' : leqv a a' -> leqv b b' -> leqv (lmax a b) (lmax a' b').
Proof using . intros H H' v; cbn; now rewrite H, H'. Qed.

(** Goal-directed: peel the reducts' structure down to the hypotheses.
    A failing [apply] of a peeling lemma unfolds its conclusion against the
    goal, so the lemmas are chosen by the goal's head (90 s → 3 s in
    [redt_leq]); other goals get the original alternatives. *)
Ltac leq_head t := lazymatch t with ?f _ => leq_head f | _ => t end.
Ltac leq_any := first
  [ exact I | reflexivity | apply leqv_refl
  | apply leq_peelL | apply leq_peelG | apply leq_peelU | apply leq_rb_br
  | apply leqv_lsuc | apply leqv_lmax
  | apply (proj1 leq_ren_all) | apply (proj1 (proj2 leq_ren_all))
  | progress unfold recT, rect
  | progress cbn [ctx_leq ty_leq tm_leq gobj_leq lsub_leq]
  | split
  | apply (proj1 leq_subst_all) ].
Ltac leq_step :=
  first
  [ assumption
  | lazymatch goal with
    | |- True => exact I
    | |- _ /\ _ => split
    | |- tm_leq (peelL _ _) (peelL _ _) => apply leq_peelL
    | |- tm_leq (peelG _ _) (peelG _ _) => apply leq_peelG
    | |- tm_leq (peelU _ _) (peelU _ _) => apply leq_peelU
    | |- tm_leq (rb_br _ _) (rb_br _ _) => apply leq_rb_br
    | |- tm_leq (rect _ _ _ _ _ _ _) _ => progress unfold recT, rect
    | |- tm_leq (recT _ _ _ _ _ _) _ => progress unfold recT, rect
    | |- leqv (lsuc _) (lsuc _) => apply leqv_lsuc
    | |- leqv (lmax _ _) (lmax _ _) => apply leqv_lmax
    | |- leqv _ _ => first [reflexivity | apply leqv_refl]
    | |- tm_leq (ren_tm _ _) (ren_tm _ _) => apply (proj1 (proj2 leq_ren_all))
    | |- ty_leq (ren_ty _ _) (ren_ty _ _) => apply (proj1 leq_ren_all)
    | |- ty_leq (subst_ty _ _) (subst_ty _ _) => apply (proj1 leq_subst_all)
    | |- ?R ?a _ =>
        let h := leq_head a in
        tryif is_constructor h
        then first [progress cbn [ctx_leq ty_leq tm_leq gobj_leq lsub_leq] | leq_any]
        else leq_any
    | |- _ => leq_any
    end ].
Ltac leq_go := repeat leq_step.

Lemma redT_leq l l' Δ Δ' c c' r : leqv l l' -> ctx_leq Δ Δ' -> ty_leq c c' ->
  redT l1 l2 rb l Δ c = Some r -> exists r', redT l1' l2' rb' l' Δ' c' = Some r' /\ tm_leq r r'.
Proof using E1 E2 Erb.
  intros El EΔ Ec H; destruct c; leq_split; cbn [redT redt] in H; try discriminate;
    injection H as <-; refine (ex_intro _ _ (conj eq_refl _));
    subst; leq_go.
Qed.

Lemma redt_leq l l' Δ Δ' T T' c c' r : leqv l l' -> ctx_leq Δ Δ' -> ty_leq T T' -> tm_leq c c' ->
  redt l1 l2 rb l Δ T c = Some r -> exists r', redt l1' l2' rb' l' Δ' T' c' = Some r' /\ tm_leq r r'.
Proof using E1 E2 Erb.
  intros El EΔ ET Ec H; destruct c; leq_split; cbn [redT redt] in H; try discriminate.
  all: try (injection H as <-; refine (ex_intro _ _ (conj eq_refl _));
            subst; solve [leq_go]).
  (* λ reads the index *)
  destruct T; try discriminate; leq_split; injection H as <-; refine (ex_intro _ _ (conj eq_refl _)).
  subst; leq_go.
Qed.

End Reducts.

(** [elim_W]'s synthesized induction hypothesis (M13a). *)
Lemma leq_wIH k1 k2 k3 A B M c a f k1' k2' k3' A' B' M' c' a' f' :
  leqv k1 k1' -> leqv k2 k2' -> leqv k3 k3' -> ty_leq A A' -> ty_leq B B' -> ty_leq M M' ->
  tm_leq c c' -> tm_leq a a' -> tm_leq f f' ->
  tm_leq (wIH k1 k2 k3 A B M c a f) (wIH k1' k2' k3' A' B' M' c' a' f').
Proof.
  intros E1 E2 E3 EA EB EM Ec Ea Ef. unfold wIH.
  pose proof (proj1 leq_ren_all) as Rty. pose proof (proj1 (proj2 leq_ren_all)) as Rtm.
  pose proof (proj1 leq_subst_all) as Sty. cbn beta in Rty, Rtm, Sty.
  cbn [tm_leq ty_leq]; repeat split; auto using leqv_refl.
  all: repeat first [ apply leqv_lmax | apply Rty | apply Rtm | apply Sty | assumption
                    | apply leq_lsingle | progress cbn [ty_leq tm_leq]; repeat split ].
Qed.

(** ** One step *)

Lemma red_leq_both :
  (forall t u, red t u -> forall t', tm_leq t t' -> exists u', red t' u' /\ tm_leq u u') /\
  (forall T U, red_ty T U -> forall T', ty_leq T T' -> exists U', red_ty T' U' /\ ty_leq U U').
Proof.
  apply red_both; intros; leq_split;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; subst.
  all: try match goal with
           | IH : forall t', tm_leq ?t t' -> exists u', _, E : tm_leq ?t ?x |- _ =>
               destruct (IH x E) as (? & ? & ?)
           | IH : forall T', ty_leq ?T T' -> exists U', _, E : ty_leq ?T ?x |- _ =>
               destruct (IH x E) as (? & ? & ?)
           end.
  all: try match goal with
           | H : redT _ _ _ _ _ _ = Some _ |- _ =>
               eapply redT_leq in H; [destruct H as (? & ? & ?) | eassumption ..]
           | H : redt _ _ _ _ _ _ _ = Some _ |- _ =>
               eapply redt_leq in H; [destruct H as (? & ? & ?) | eassumption ..]
           end.
  all: try match goal with H : Forall2 leqv ?ls ?ls' |- _ => pose proof (eq_sym (Forall2_length H)) end.
  all: eexists; split; [solve [eauto with red] |].
  all: try solve [cbn; repeat split; auto].
  all: first
    [ apply (proj1 (proj2 leq_subst_all)); [unfold lsingle3; split; [cbn; repeat split; auto | apply leq_wIH; auto] | auto]
    | apply (proj1 (proj2 leq_subst_all)); cbn; repeat split; auto
    | apply (proj1 (proj2 leq_gsubst_all)); [apply leq_gsingle; cbn; auto | auto]
    | apply (proj1 (proj2 leq_usubst_all)); [apply leqv_uext; assumption | assumption] ].
Qed.

Lemma red_leq t u t' : red t u -> tm_leq t t' -> exists u', red t' u' /\ tm_leq u u'.
Proof. intros H; exact (proj1 red_leq_both _ _ H t'). Qed.
Lemma red_ty_leq T U T' : red_ty T U -> ty_leq T T' -> exists U', red_ty T' U' /\ ty_leq U U'.
Proof. intros H; exact (proj2 red_leq_both _ _ H T'). Qed.

(** ** Many steps, and weak-head normal forms *)

Lemma reds_leq t w t' : reds t w -> tm_leq t t' -> exists w', reds t' w' /\ tm_leq w w'.
Proof.
  intros H; revert t'; induction H as [t | t u w Htu Huw IH]; intros t' E.
  - exists t'; split; [constructor | exact E].
  - destruct (red_leq _ _ _ Htu E) as (u' & Hu' & Eu).
    destruct (IH _ Eu) as (w' & Hw' & Ew). exists w'; split; [econstructor; eassumption | exact Ew].
Qed.
Lemma reds_ty_leq T W T' : reds_ty T W -> ty_leq T T' -> exists W', reds_ty T' W' /\ ty_leq W W'.
Proof.
  intros H; revert T'; induction H as [T | T U W Htu Huw IH]; intros T' E.
  - exists T'; split; [constructor | exact E].
  - destruct (red_ty_leq _ _ _ Htu E) as (U' & Hu' & Eu).
    destruct (IH _ Eu) as (W' & Hw' & Ew). exists W'; split; [econstructor; eassumption | exact Ew].
Qed.

Lemma reds_whnf_leq t t' w w' : tm_leq t t' -> reds t w -> reds t' w' -> whnf w -> whnf w' ->
  tm_leq w w'.
Proof.
  intros E H H' Hw Hw'. destruct (reds_leq _ _ _ H E) as (u & Hu & Eu).
  now rewrite (reds_whnf_det _ _ _ H' Hu Hw' (whnf_leq _ _ Eu Hw)).
Qed.
Lemma reds_ty_whnf_leq T T' W W' : ty_leq T T' -> reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  ty_leq W W'.
Proof.
  intros E H H' Hw Hw'. destruct (reds_ty_leq _ _ _ H E) as (U & Hu & Eu).
  now rewrite (reds_ty_whnf_det _ _ _ H' Hu Hw' (whnf_ty_leq _ _ Eu Hw)).
Qed.
