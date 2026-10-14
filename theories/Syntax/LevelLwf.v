(** * Well-formed level annotations under the syntactic operations (M17b)

    [ty_lwf]/[tm_lwf] are kept by renaming, local and universe-level
    substitution: what the Static Code Lemma needs to instantiate its
    induction hypothesis at a synthesized type, [elim_IWf]'s induction
    hypothesis's ([iwfihty_lwf], [iwfihty_leq]), whose right-hand side is
    built from the right components rather than read off a derivation. *)
From DeLaM.Syntax Require Import LevelRed.
From DeLaM.Syntax Require Import LevelEq.

Lemma lcons'_lwf L d t : lsub_lwf L d -> tm_lwf L t -> lsub_lwf L (lcons' d t).
Proof.
  intros Hd Ht. unfold lcons'. destruct d as [[|k] | d0 t0]; try exact (conj Hd Ht).
  destruct t; try exact (conj Hd Ht). destruct (Nat.eqb n k); [exact I | exact (conj Hd Ht)].
Qed.

Lemma r2l_lwf L r : lsub_lwf L (r2l r).
Proof. induction r as [k | r IH m]; cbn; [exact I | apply lcons'_lwf; [exact IH | exact I]]. Qed.

Lemma lwf_ren_all :
  let Pty T := forall L r, ty_lwf L T -> ty_lwf L (ren_ty T r) in
  let Ptm t := forall L r, tm_lwf L t -> tm_lwf L (ren_tm t r) in
  let Pctx (Γ : ctx) := True in
  let Pl d := forall L r, lsub_lwf L d -> lsub_lwf L (lren d r) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; try exact I; cbn in *; intuition eauto using lcons'_lwf, r2l_lwf. Qed.

Lemma uuprn_ok n ρ L' L : uren_ok ρ L' L -> uren_ok (uuprn n ρ) (n + L') (n + L).
Proof.
  intros H. induction n as [|n IH]; [exact H|].
  intros [|m] Hm; change (uuprn (S n) ρ) with (uupr (uuprn n ρ)); unfold uupr; [lia|].
  specialize (IH m ltac:(lia)). lia.
Qed.

Lemma uupr_ok ρ L' L : uren_ok ρ L' L -> uren_ok (uupr ρ) (S L') (S L).
Proof. exact (uuprn_ok 1 ρ L' L). Qed.
Lemma lwfs_lvren L L' ρ ls : uren_ok ρ L' L -> Forall (lwf L) ls -> Forall (lwf L') (map (fun l => lvren l ρ) ls).
Proof. intros H Hs. apply Forall_map. eapply Forall_impl; [| exact Hs]. intros l. exact (lwf_lvren _ _ _ _ H). Qed.

Lemma lwf_uren_all :
  let Pty T := forall L L' ρ, uren_ok ρ L' L -> ty_lwf L T -> ty_lwf L' (uren_ty T ρ) in
  let Ptm t := forall L L' ρ, uren_ok ρ L' L -> tm_lwf L t -> tm_lwf L' (uren_tm t ρ) in
  let Pctx Γ := forall L L' ρ, uren_ok ρ L' L -> ctx_lwf L Γ -> ctx_lwf L' (ucren Γ ρ) in
  let Pl d := forall L L' ρ, uren_ok ρ L' L -> lsub_lwf L d -> lsub_lwf L' (ulren d ρ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; cbn in *; intuition eauto using lwf_lvren, uuprn_ok, uupr_ok, lwfs_lvren, lcons'_lwf. Qed.

Lemma lwf_gren_all :
  let Pty T := forall L ξ, ty_lwf L T -> ty_lwf L (gren_ty T ξ) in
  let Ptm t := forall L ξ, tm_lwf L t -> tm_lwf L (gren_tm t ξ) in
  let Pctx Γ := forall L ξ, ctx_lwf L Γ -> ctx_lwf L (gcren Γ ξ) in
  let Pl d := forall L ξ, lsub_lwf L d -> lsub_lwf L (glren d ξ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof. leq_start; cbn in *; intuition eauto using lcons'_lwf. Qed.

Lemma lwf_llift L d : lsub_lwf L d -> lsub_lwf L (llift d).
Proof. intros H. unfold llift. apply lcons'_lwf; [apply (proj2 (proj2 (proj2 lwf_ren_all))), H | exact I]. Qed.
Lemma lwf_uwk L d : lsub_lwf L d -> lsub_lwf (S L) (uwk d).
Proof. intros H. unfold uwk. apply (proj2 (proj2 (proj2 lwf_uren_all)) _ L); [intros m Hm; lia | exact H]. Qed.
Lemma lwf_uwkn n L d : lsub_lwf L d -> lsub_lwf (n + L) (uwkn n d).
Proof. intros H. induction n as [|n IH]; [exact H|]. exact (lwf_uwk _ _ IH). Qed.
Lemma lwf_gwk L d : lsub_lwf L d -> lsub_lwf L (gwk d).
Proof. intros H. exact (proj2 (proj2 (proj2 lwf_gren_all)) _ _ _ H). Qed.
Lemma lwf_lnorm L d : lsub_lwf L d -> lsub_lwf L (lnorm d).
Proof. induction d as [k | d IH t]; cbn; [auto | intros [H1 H2]; apply lcons'_lwf; auto]. Qed.
Lemma lwf_ldrop L k d : lsub_lwf L d -> lsub_lwf L (ldrop k d).
Proof.
  revert d; induction k as [|k IH]; intros d H; destruct d as [j | d t]; cbn in *; auto; try exact I.
  apply IH; tauto.
Qed.

Lemma lwf_subst_all :
  let Pty T := forall L d, lsub_lwf L d -> ty_lwf L T -> ty_lwf L (subst_ty T d) in
  let Ptm t := forall L d, lsub_lwf L d -> tm_lwf L t -> tm_lwf L (subst_tm t d) in
  let Pctx (Γ : ctx) := True in
  let Pl d0 := forall L d, lsub_lwf L d -> lsub_lwf L d0 -> lsub_lwf L (lcomp d0 d) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof.
  leq_start; try exact I; cbn in *;
    intuition eauto using llk_lwf, lwf_llift, lcons'_lwf, lwf_uwkn, lwf_gwk, lwf_uwk, lwf_lnorm, lwf_ldrop.
Qed.

Definition lwf_ren_ty T := proj1 lwf_ren_all T.
Definition lwf_ren_tm t := proj1 (proj2 lwf_ren_all) t.
Definition lwf_subst_ty T := proj1 lwf_subst_all T.
Definition lwf_subst_tm t := proj1 (proj2 lwf_subst_all) t.
Definition leq_ren_ty T := proj1 leq_ren_all T.
Definition leq_subst_ty T := proj1 leq_subst_all T.
Definition leq_subst_tm t := proj1 (proj2 leq_subst_all) t.

Lemma lwf_lsingle L a : tm_lwf L a -> lsub_lwf L (lsingle a).
Proof. intros H. exact (conj I H). Qed.
Lemma lwf_lsingle2 L a b : tm_lwf L a -> tm_lwf L b -> lsub_lwf L (lsingle2 a b).
Proof. intros H H'. exact (conj (conj I H) H'). Qed.

Lemma lwf_tmDNth L k n F cs i :
  lwf L k -> tm_lwf L n -> ty_lwf L F -> tm_lwf L cs -> tm_lwf L i ->
  tm_lwf L (tmDNth k n F cs i).
Proof.
  intros E1 En EF Ec Ei.
  unfold tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS.
  pose proof lwf_ren_ty as Rty. pose proof lwf_ren_tm as Rtm.
  pose proof lwf_subst_ty as Sty. cbn beta in Rty, Rtm, Sty.
  cbn [tm_lwf ty_lwf]; repeat split.
  all: repeat first [ assumption | exact I | apply Sty | lazymatch goal with |- lsub_lwf _ _ => apply lwf_lsingle end | apply Rty | apply Rtm
                    | progress cbn [ty_lwf tm_lwf lsub_lwf]; repeat split ].
Qed.

Lemma iwfihty_lwf L l li l' X A N Ot C M : lwf L l -> lwf L li -> lwf L l' ->
  ty_lwf L X -> ty_lwf L A -> tm_lwf L N -> tm_lwf L Ot -> tm_lwf L C -> ty_lwf L M ->
  ty_lwf L (iwfihty l li l' X A N Ot C M).
Proof.
  intros E1 E2 E3 EX EA EN EO EC EM.
  pose proof lwf_ren_ty as Rty. pose proof lwf_ren_tm as Rtm.
  pose proof lwf_subst_ty as Sty. cbn beta in Rty, Rtm, Sty.
  match goal with |- context [tmDNth ?k ?n ?F ?cs ?i] =>
    assert (H : tm_lwf L (tmDNth k n F cs i)); [| revert H; generalize (tmDNth k n F cs i); intros x H] end.
  { apply lwf_tmDNth; [split; assumption | apply Rtm, Rtm; assumption | | exact I | exact I].
    cbn [ty_lwf]; repeat split; repeat first [ assumption | apply Rty | apply Rtm ]. }
  cbn [ty_lwf tm_lwf]; repeat split; try assumption; [apply Rtm; assumption |].
  apply Sty; [apply lwf_lsingle2; [apply Rtm; assumption | assumption] | repeat apply Rty; assumption].
Qed.

Lemma iwfihty_leq l li l' X A N Ot C M k ki k' X' A' N' Ot' C' M' : leqv l k -> leqv li ki -> leqv l' k' ->
  ty_leq X X' -> ty_leq A A' -> tm_leq N N' -> tm_leq Ot Ot' -> tm_leq C C' -> ty_leq M M' ->
  ty_leq (iwfihty l li l' X A N Ot C M) (iwfihty k ki k' X' A' N' Ot' C' M').
Proof.
  intros E1 E2 E3 EX EA EN EO EC EM.
  pose proof (proj1 leq_ren_all) as Rty. pose proof (proj1 (proj2 leq_ren_all)) as Rtm.
  pose proof (proj1 leq_subst_all) as Sty. cbn beta in Rty, Rtm, Sty.
  match goal with |- ty_leq ?a ?b =>
    match a with context [tmDNth ?k ?n ?F ?cs ?i] =>
    match b with context [tmDNth ?k' ?n' ?F' ?cs' ?i'] =>
    assert (H : tm_leq (tmDNth k n F cs i) (tmDNth k' n' F' cs' i'));
    [| revert H; generalize (tmDNth k n F cs i) (tmDNth k' n' F' cs' i'); intros x x' H] end end end.
  { apply leq_tmDNth; [apply leqv_lmax; assumption | apply Rtm, Rtm; assumption | | reflexivity | reflexivity].
    cbn [ty_leq]; repeat split; repeat first [ assumption | apply Rty | apply Rtm ]. }
  cbn [ty_leq tm_leq]; repeat split; try apply leqv_refl; try assumption; [apply Rtm; assumption |].
  apply Sty; [apply leq_lsingle2; [apply Rtm; assumption | assumption] | repeat apply Rty; assumption].
Qed.
