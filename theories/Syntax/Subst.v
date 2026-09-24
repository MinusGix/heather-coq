(** * The local substitution algebra (ported from spike/Syntax.v)

    Every law is proved once by mutual induction over types, terms and local
    substitutions.  The generic tactic [syn_start; law_auto] handles every
    congruence case; [u^δ]/[U^δ] cases go through canonicity ([l_canon]):
    operation outputs are normal, so two of them are equal iff their lookups
    are.

    Composition laws are unconditional.  Identity laws need the input in
    normal form ([nfty]/[nftm]), which holds for every operation output and
    for every term without global variables. *)
From Coq Require Import Arith Lia.
From DeLaM.Syntax Require Export Term.

(** ** Canonical form of local substitutions *)

Definition labsorb (d : lsub) (t : tm) : Prop :=
  match d, t with lshift (S k), var m => m = k | _, _ => False end.

Fixpoint nf_l (d : lsub) : Prop :=
  match d with lshift _ => True | lcons d t => nf_l d /\ ~ labsorb d t end.

Lemma llk_lcons' d t n : llk (lcons' d t) n = llk (lcons d t) n.
Proof.
  destruct d as [[|k]|]; destruct t; cbn; auto.
  destruct (Nat.eqb_spec n0 k) as [->|]; destruct n; cbn; f_equal; lia.
Qed.

Lemma nf_lcons' d t : nf_l d -> nf_l (lcons' d t).
Proof.
  destruct d as [[|k]|]; destruct t; cbn; try tauto.
  destruct (Nat.eqb_spec n k); cbn; auto.
Qed.

Lemma nf_lnorm d : nf_l (lnorm d).
Proof. induction d; cbn; auto using nf_lcons'. Qed.
Lemma llk_lnorm d n : llk (lnorm d) n = llk d n.
Proof.
  revert n; induction d as [k|d IH t]; intros n; cbn; auto.
  rewrite llk_lcons'. destruct n; cbn; auto.
Qed.

Lemma shift_canon d k : nf_l d -> (forall n, llk d n = var (n + k)) -> d = lshift k.
Proof.
  revert k; induction d as [k'|d IH t]; intros k Hnf H.
  - specialize (H 0); cbn in H. injection H as ->. reflexivity.
  - cbn in Hnf; destruct Hnf as [Hd Hab].
    pose proof (H 0) as Ht; cbn in Ht; subst t.
    assert (d = lshift (S k)) as ->.
    { apply IH; auto. intros n. specialize (H (S n)); cbn in H. rewrite H. f_equal; lia. }
    cbn in Hab. exfalso; auto.
Qed.

(** Canonicity: normal local substitutions are equal iff their lookups are. *)
Lemma l_canon d1 d2 : nf_l d1 -> nf_l d2 -> (forall n, llk d1 n = llk d2 n) -> d1 = d2.
Proof.
  revert d2; induction d1 as [k1|d1 IH t1]; intros d2 N1 N2 H.
  - symmetry; apply shift_canon; auto. intros n; now rewrite <- H.
  - destruct d2 as [k2|d2 t2].
    + apply shift_canon; auto.
    + cbn in N1, N2; destruct N1, N2. f_equal.
      * apply IH; auto. intros n; exact (H (S n)).
      * exact (H 0).
Qed.

(** ** Lookup lemmas *)

Lemma rlk_rdrop k r n : rlk (rdrop k r) n = rlk r (k + n).
Proof. revert r; induction k; intros [m|r m]; cbn; auto; lia. Qed.
Lemma rlk_rup r n : rlk (rup r) n = S (rlk r n).
Proof. revert n; induction r as [k|r IH m]; intros [|n]; cbn; auto; lia. Qed.
Lemma rlk_rlift r n :
  rlk (rlift r) n = match n with 0 => 0 | S n => S (rlk r n) end.
Proof. destruct n; cbn; auto using rlk_rup. Qed.
Lemma rlk_shift1 n : rlk ↑ n = S n.
Proof. cbn; lia. Qed.
Lemma llk_r2l r n : llk (r2l r) n = var (rlk r n).
Proof.
  revert n; induction r as [k|r IH m]; intros n; cbn; auto.
  rewrite llk_lcons'. destruct n; cbn; auto.
Qed.
Lemma nf_r2l r : nf_l (r2l r).
Proof. induction r; cbn; auto using nf_lcons'. Qed.
Lemma llk_ldrop k d n : llk (ldrop k d) n = llk d (k + n).
Proof. revert d; induction k; intros [m|d t]; cbn; auto; f_equal; lia. Qed.

Lemma llk_lren d r n : llk (lren d r) n = ren_tm (llk d n) r.
Proof.
  revert n; induction d as [k|d IH t]; intros n; cbn.
  - rewrite llk_r2l, rlk_rdrop. do 2 f_equal; lia.
  - rewrite llk_lcons'. destruct n; cbn; auto.
Qed.
Lemma nf_lren d r : nf_l (lren d r).
Proof. induction d; cbn; auto using nf_r2l, nf_lcons'. Qed.

Lemma llk_lcomp d' d n : llk (lcomp d' d) n = subst_tm (llk d' n) d.
Proof.
  revert n; induction d' as [k|d' IH t]; intros n; cbn.
  - rewrite llk_lnorm, llk_ldrop. f_equal; lia.
  - rewrite llk_lcons'. destruct n; cbn; auto.
Qed.
Lemma nf_lcomp d' d : nf_l (lcomp d' d).
Proof. induction d'; cbn; auto using nf_lnorm, nf_lcons'. Qed.

Lemma llk_llift d n :
  llk (llift d) n = match n with 0 => var 0 | S n => ren_tm (llk d n) ↑ end.
Proof. unfold llift; rewrite llk_lcons'; destruct n; cbn; auto using llk_lren. Qed.
Lemma nf_llift d : nf_l (llift d).
Proof. apply nf_lcons', nf_lren. Qed.

#[export] Hint Resolve nf_lren nf_lcomp nf_llift nf_r2l nf_lnorm : nf.

(** ** The generic proof pattern *)

(** A statement about terms, lifted to local substitutions via lookups. *)
Definition LK (P : tm -> Prop) (d : lsub) : Prop := forall n, P (llk d n).

Ltac var_battery :=
  first [ reflexivity | solve [eauto] | solve [symmetry; eauto]
        | solve [f_equal; eauto] | solve [f_equal; symmetry; eauto] ].

Ltac lk_cases :=
  match goal with
  | |- LK _ (lshift _) => intros ?n; cbn; intros; var_battery
  | IHd : LK _ ?d |- LK _ (lcons ?d ?t) =>
      intros [|?n]; cbn; [assumption | exact (IHd _)]
  end.

Ltac syn_start :=
  intros ?Pty ?Ptm; apply syn_ind; subst Pty Ptm; cbn beta; intros; try exact I.

Ltac lsub_eq :=
  apply l_canon; [auto with nf | auto with nf | intros ?n];
  repeat first [ rewrite llk_lren | rewrite llk_lcomp ].

Ltac law_auto :=
  cbn; try solve [eauto with subst | symmetry; eauto with subst];
  try solve [f_equal; eauto with subst];
  try solve [f_equal; try lsub_eq; eauto with subst].

(** ** Renaming *)

Lemma rlift_ext r r' : (forall n, rlk r n = rlk r' n) -> forall n, rlk (rlift r) n = rlk (rlift r') n.
Proof. intros H [|n]; rewrite !rlk_rlift; auto. Qed.
Lemma rlift_comp r1 r2 r3 : (forall n, rlk r3 n = rlk r2 (rlk r1 n)) ->
  forall n, rlk (rlift r3) n = rlk (rlift r2) (rlk (rlift r1) n).
Proof. intros H [|n]; rewrite !rlk_rlift; auto. Qed.
#[export] Hint Resolve rlift_ext rlift_comp : subst.

Lemma ren_ext_all :
  let Pty T := forall r r', (forall n, rlk r n = rlk r' n) -> ren_ty T r = ren_ty T r' in
  let Ptm t := forall r r', (forall n, rlk r n = rlk r' n) -> ren_tm t r = ren_tm t r' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases; law_auto.
Qed.

Lemma ren_ren_all :
  let Pty T := forall r1 r2 r3, (forall n, rlk r3 n = rlk r2 (rlk r1 n)) ->
               ren_ty (ren_ty T r1) r2 = ren_ty T r3 in
  let Ptm t := forall r1 r2 r3, (forall n, rlk r3 n = rlk r2 (rlk r1 n)) ->
               ren_tm (ren_tm t r1) r2 = ren_tm t r3 in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases; law_auto.
  all: now rewrite H.
Qed.

(** ** Substitution *)

Lemma llift_ext d d' : (forall n, llk d n = llk d' n) -> forall n, llk (llift d) n = llk (llift d') n.
Proof. intros H [|n]; rewrite !llk_llift; auto. now rewrite H. Qed.
#[export] Hint Resolve llift_ext : subst.

Lemma subst_ext_all :
  let Pty T := forall d d', (forall n, llk d n = llk d' n) -> subst_ty T d = subst_ty T d' in
  let Ptm t := forall d d', (forall n, llk d n = llk d' n) -> subst_tm t d = subst_tm t d' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof. syn_start; try lk_cases; law_auto. Qed.

Lemma llift_rcomp r d d' : (forall n, llk d' n = llk d (rlk r n)) ->
  forall n, llk (llift d') n = llk (llift d) (rlk (rlift r) n).
Proof. intros H [|n]; rewrite rlk_rlift, !llk_llift; auto. now rewrite H. Qed.
#[export] Hint Resolve llift_rcomp : subst.

Lemma ren_subst_all :
  let Pty T := forall r d d', (forall n, llk d' n = llk d (rlk r n)) ->
               subst_ty (ren_ty T r) d = subst_ty T d' in
  let Ptm t := forall r d d', (forall n, llk d' n = llk d (rlk r n)) ->
               subst_tm (ren_tm t r) d = subst_tm t d' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases;
    law_auto.
  all: now rewrite H.
Qed.

Definition ren_ren_tm t := proj1 (proj2 ren_ren_all) t.

Lemma rup_shift_l r m : rlk (rup r) m = rlk ↑ (rlk r m).
Proof. rewrite rlk_rup; cbn; lia. Qed.
Lemma rup_shift_r r m : rlk (rup r) m = rlk (rlift r) (rlk ↑ m).
Proof. unfold rshift1; cbn [rlk]; rewrite Nat.add_1_r, rlk_rlift, rlk_rup; reflexivity. Qed.

Lemma llift_ren r d d' : (forall n, llk d' n = ren_tm (llk d n) r) ->
  forall n, llk (llift d') n = ren_tm (llk (llift d) n) (rlift r).
Proof.
  intros H [|n]; rewrite !llk_llift; auto. rewrite H.
  rewrite (ren_ren_tm _ _ _ _ (rup_shift_l r)), (ren_ren_tm _ _ _ _ (rup_shift_r r)); reflexivity.
Qed.
#[export] Hint Resolve llift_ren : subst.

Lemma subst_ren_all :
  let Pty T := forall d d' r, (forall n, llk d' n = ren_tm (llk d n) r) ->
               ren_ty (subst_ty T d) r = subst_ty T d' in
  let Ptm t := forall d d' r, (forall n, llk d' n = ren_tm (llk d n) r) ->
               ren_tm (subst_tm t d) r = subst_tm t d' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases;
    law_auto.
  all: now rewrite H.
Qed.

Definition subst_ren_tm t := proj1 (proj2 subst_ren_all) t.
Definition ren_subst_tm t := proj1 (proj2 ren_subst_all) t.

Lemma llift_subst d d' d'' : (forall n, llk d'' n = subst_tm (llk d n) d') ->
  forall n, llk (llift d'') n = subst_tm (llk (llift d) n) (llift d').
Proof.
  intros H [|n]; rewrite !llk_llift; cbn [subst_tm]; rewrite ?llk_llift; [reflexivity|].
  rewrite H, (subst_ren_tm _ _ (lren d' ↑)) by (intros; apply llk_lren).
  symmetry; apply ren_subst_tm. intros m.
  rewrite llk_lren; unfold rshift1 at 2; cbn [rlk]; rewrite Nat.add_1_r, llk_llift; reflexivity.
Qed.
#[export] Hint Resolve llift_subst : subst.

Lemma subst_subst_all :
  let Pty T := forall d d' d'', (forall n, llk d'' n = subst_tm (llk d n) d') ->
               subst_ty (subst_ty T d) d' = subst_ty T d'' in
  let Ptm t := forall d d' d'', (forall n, llk d'' n = subst_tm (llk d n) d') ->
               subst_tm (subst_tm t d) d' = subst_tm t d'' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases;
    law_auto.
  all: now rewrite H.
Qed.

Lemma ren_as_subst_all :
  let Pty T := forall r d, (forall n, llk d n = var (rlk r n)) -> ren_ty T r = subst_ty T d in
  let Ptm t := forall r d, (forall n, llk d n = var (rlk r n)) -> ren_tm t r = subst_tm t d in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  assert (Hl : forall r d, (forall n, llk d n = var (rlk r n)) ->
            forall n, llk (llift d) n = var (rlk (rlift r) n)).
  { intros r d H [|n]; rewrite llk_llift, rlk_rlift; auto. rewrite H; cbn; f_equal; lia. }
  syn_start; try lk_cases;
    cbn; try solve [symmetry; auto]; try solve [f_equal; eauto].
  all: f_equal; lsub_eq; eauto.
Qed.

(** ** Normal forms and identity laws *)

Fixpoint nfty (T : ty) : Prop :=
  match T with
  | tyErr | tyNat | tyU _ => True
  | tyPi _ _ A B => nfty A /\ nfty B
  | tyEl _ t => nftm t
  | tyGvar _ d => nfl d
  end
with nftm (t : tm) : Prop :=
  match t with
  | var _ | tmErr | tmNat | tmU _ | zero => True
  | tmPi _ _ s t => nftm s /\ nftm t
  | succ t => nftm t
  | natrec _ M s z t => nfty M /\ nftm s /\ nftm z /\ nftm t
  | lam _ _ A t => nfty A /\ nftm t
  | app t _ _ A B s => nftm t /\ nfty A /\ nfty B /\ nftm s
  | gvar _ d => nfl d
  end
with nfl (d : lsub) : Prop :=
  match d with lshift _ => True | lcons d t => nfl d /\ nftm t /\ ~ labsorb d t end.

Lemma nfl_nf d : nfl d -> nf_l d.
Proof. induction d; cbn; tauto. Qed.
Lemma nfl_llk d n : nfl d -> nftm (llk d n).
Proof. revert n; induction d as [k|d IH t]; intros [|n] H; cbn in *; try tauto. apply IH; tauto. Qed.
#[export] Hint Resolve nfl_nf nfl_llk : nf.

Lemma llift_id d : (forall n, llk d n = var n) -> forall n, llk (llift d) n = var n.
Proof. intros H [|n]; rewrite llk_llift; auto. rewrite H; cbn; f_equal; lia. Qed.
#[export] Hint Resolve llift_id : subst.

Ltac lk_cases_nf :=
  match goal with
  | |- LK _ (lshift _) => intros ?n; cbn; intros; auto
  | Hn : nfl (lcons ?d ?t), IHd : nfl ?d -> LK _ ?d |- LK _ (lcons ?d ?t) =>
      cbn in Hn; destruct Hn as (?Hd & ?Ht & ?Ha);
      intros [|?n]; cbn; [assumption | exact (IHd ltac:(assumption) _)]
  end.

Lemma subst_id_all :
  let Pty T := nfty T -> forall d, (forall n, llk d n = var n) -> subst_ty T d = T in
  let Ptm t := nftm t -> forall d, (forall n, llk d n = var n) -> subst_tm t d = t in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, nfl d -> LK Ptm d).
Proof.
  syn_start; try lk_cases_nf; cbn in *; try tauto;
    try solve [f_equal; intuition eauto with subst].
  all: f_equal; apply l_canon; auto with nf; intros n; rewrite llk_lcomp;
    match goal with IH : nfl ?d -> LK _ ?d |- _ => apply IH end; auto with nf.
Qed.

(** ** Exported laws, in notation form *)

Section Laws.

Lemma ren_ext_ty (T : ty) r r' : (forall n, rlk r n = rlk r' n) -> T⟨r⟩ = T⟨r'⟩.
Proof. intros; apply (proj1 ren_ext_all); auto. Qed.
Lemma ren_ext_tm (t : tm) r r' : (forall n, rlk r n = rlk r' n) -> t⟨r⟩ = t⟨r'⟩.
Proof. intros; apply (proj1 (proj2 ren_ext_all)); auto. Qed.
Lemma ren_ren_ty (T : ty) r1 r2 r3 : (forall n, rlk r3 n = rlk r2 (rlk r1 n)) -> T⟨r1⟩⟨r2⟩ = T⟨r3⟩.
Proof. intros; apply (proj1 ren_ren_all); auto. Qed.
Lemma ren_ren (t : tm) r1 r2 r3 : (forall n, rlk r3 n = rlk r2 (rlk r1 n)) -> t⟨r1⟩⟨r2⟩ = t⟨r3⟩.
Proof. intros; apply (proj1 (proj2 ren_ren_all)); auto. Qed.
Lemma subst_ext_ty (T : ty) d d' : (forall n, llk d n = llk d' n) -> T[d] = T[d'].
Proof. intros; apply (proj1 subst_ext_all); auto. Qed.
Lemma subst_ext (t : tm) d d' : (forall n, llk d n = llk d' n) -> t[d] = t[d'].
Proof. intros; apply (proj1 (proj2 subst_ext_all)); auto. Qed.
Lemma ren_subst_ty (T : ty) r d d' : (forall n, llk d' n = llk d (rlk r n)) -> T⟨r⟩[d] = T[d'].
Proof. intros; apply (proj1 ren_subst_all); auto. Qed.
Lemma ren_subst (t : tm) r d d' : (forall n, llk d' n = llk d (rlk r n)) -> t⟨r⟩[d] = t[d'].
Proof. intros; apply (proj1 (proj2 ren_subst_all)); auto. Qed.
Lemma subst_ren_ty (T : ty) d d' r : (forall n, llk d' n = (llk d n)⟨r⟩) -> T[d]⟨r⟩ = T[d'].
Proof. intros; apply (proj1 subst_ren_all); auto. Qed.
Lemma subst_ren (t : tm) d d' r : (forall n, llk d' n = (llk d n)⟨r⟩) -> t[d]⟨r⟩ = t[d'].
Proof. intros; apply (proj1 (proj2 subst_ren_all)); auto. Qed.
Lemma subst_subst_ty (T : ty) d d' d'' : (forall n, llk d'' n = (llk d n)[d']) -> T[d][d'] = T[d''].
Proof. intros; apply (proj1 subst_subst_all); auto. Qed.
Lemma subst_subst (t : tm) d d' d'' : (forall n, llk d'' n = (llk d n)[d']) -> t[d][d'] = t[d''].
Proof. intros; apply (proj1 (proj2 subst_subst_all)); auto. Qed.
Lemma ren_as_subst_ty (T : ty) r d : (forall n, llk d n = var (rlk r n)) -> T⟨r⟩ = T[d].
Proof. intros; apply (proj1 ren_as_subst_all); auto. Qed.
Lemma ren_as_subst (t : tm) r d : (forall n, llk d n = var (rlk r n)) -> t⟨r⟩ = t[d].
Proof. intros; apply (proj1 (proj2 ren_as_subst_all)); auto. Qed.
Lemma subst_id_ty (T : ty) d : nfty T -> (forall n, llk d n = var n) -> T[d] = T.
Proof. intros; apply (proj1 subst_id_all); auto. Qed.
Lemma subst_id (t : tm) d : nftm t -> (forall n, llk d n = var n) -> t[d] = t.
Proof. intros; apply (proj1 (proj2 subst_id_all)); auto. Qed.
End Laws.

Print Assumptions subst_subst.
