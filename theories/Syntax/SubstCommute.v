(** * Substitution commutes with the typing rules' own substitutions

    The substitution lemma pushes an arbitrary [d] through [B[a/x]],
    [M[succ x/x]], [z[t/x, r/y]] and weakenings.  Everything is reduced to
    pointwise equations between lookups.  Identity laws need normal forms
    ([nftm]) of the substitution's entries: [LK nftm d]. *)
From DeLaM.Syntax Require Export Commute.

(** ** Substitution preserves normal forms *)

Lemma nfl_lnorm_lk d : LK nftm d -> nfl (lnorm d).
Proof.
  induction d as [k|d IH t]; intros H; cbn; auto.
  apply nfl_lcons'.
  - apply IH; intros n; exact (H (S n)).
  - exact (H 0).
Qed.

Lemma lk_ldrop k d : LK nftm d -> LK nftm (ldrop k d).
Proof. intros H n; rewrite llk_ldrop; apply H. Qed.

Lemma lk_llift d : LK nftm d -> LK nftm (llift d).
Proof. intros H [|n]; rewrite llk_llift; cbn; [exact I | apply ren_nf]. Qed.
Lemma lk_gwk d : LK nftm d -> LK nftm (gwk d).
Proof. intros H n; unfold gwk; rewrite llk_glren; apply gren_nf, H. Qed.

Lemma lk_uwk d : LK nftm (uwk d).
Proof. intros n; unfold uwk; rewrite llk_ulren; apply dnftm_nftm, uren_dnf_all. Qed.

Lemma lk_uwkn k d : LK nftm d -> LK nftm (uwkn k d).
Proof. intros H; unfold uwkn; induction k; [assumption | apply lk_uwk]. Qed.

#[export] Hint Resolve lk_llift lk_gwk lk_ldrop nfl_lnorm_lk lk_uwk lk_uwkn : nf.

Lemma subst_nf_all :
  let Pty T := nfty T -> forall d, LK nftm d -> nfty (subst_ty T d) in
  let Ptm t := nftm t -> forall d, LK nftm d -> nftm (subst_tm t d) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\
  (forall d0, nfl d0 -> forall d, LK nftm d -> nfl (lcomp d0 d)).
Proof.
  intros Pty Ptm; apply syn_ind; subst Pty Ptm; cbn beta; intros; try exact I;
    cbn in *; intuition eauto 6 with nf.
  apply nfl_lcons'; intuition eauto.
Qed.

Lemma subst_nf_ty (T : ty) d : nfty T -> LK nftm d -> nfty T[d].
Proof. intros; now apply subst_nf_all. Qed.
Lemma subst_nf (t : tm) d : nftm t -> LK nftm d -> nftm t[d].
Proof. intros; now apply subst_nf_all. Qed.

(** ** Reduction to pointwise equations *)

Lemma subst2_eq_ty (T : ty) d1 d2 d3 d4 :
  (forall n, (llk d1 n)[d2] = (llk d3 n)[d4]) -> T[d1][d2] = T[d3][d4].
Proof.
  intros H.
  rewrite (subst_subst_ty T d1 d2 (lcomp d1 d2)), (subst_subst_ty T d3 d4 (lcomp d3 d4))
    by (intros; apply llk_lcomp).
  apply subst_ext_ty; intros n; rewrite !llk_lcomp; apply H.
Qed.
Lemma subst2_eq (t : tm) d1 d2 d3 d4 :
  (forall n, (llk d1 n)[d2] = (llk d3 n)[d4]) -> t[d1][d2] = t[d3][d4].
Proof.
  intros H.
  rewrite (subst_subst t d1 d2 (lcomp d1 d2)), (subst_subst t d3 d4 (lcomp d3 d4))
    by (intros; apply llk_lcomp).
  apply subst_ext; intros n; rewrite !llk_lcomp; apply H.
Qed.

Lemma ren_as_r2l_ty (T : ty) r : T⟨r⟩ = T[r2l r].
Proof. apply ren_as_subst_ty; intros; apply llk_r2l. Qed.
Lemma ren_as_r2l (t : tm) r : t⟨r⟩ = t[r2l r].
Proof. apply ren_as_subst; intros; apply llk_r2l. Qed.

(** [u⟨↑⟩[a/x] = u] and its two-variable version. *)
Lemma shift_single (u a : tm) : nftm u -> u⟨↑⟩[lsingle a] = u.
Proof.
  intros Hu. rewrite (ren_subst _ _ _ (lshift 0)).
  - apply subst_id; auto. intros; cbn; f_equal; lia.
  - intros n; rewrite rlk_shift1; cbn; f_equal; lia.
Qed.
Lemma shift2_single2 (u t q : tm) : nftm u -> u⟨↑⟩⟨↑⟩[lsingle2 t q] = u.
Proof.
  intros Hu. rewrite ren_ren_comp, (ren_subst _ _ _ (lshift 0)).
  - apply subst_id; auto. intros; cbn; f_equal; lia.
  - intros n; rlk_simpl; cbn; f_equal; lia.
Qed.
Lemma shift2_single2_ty (A : ty) t q : nfty A -> A⟨↑⟩⟨↑⟩[lsingle2 t q] = A.
Proof.
  intros HA. rewrite ren_ren_comp_ty, (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; auto. intros; cbn; f_equal; lia.
  - intros n; rlk_simpl; cbn; f_equal; lia.
Qed.

(** ** Commutations *)

Lemma shift_llift_ty (A : ty) d : A⟨↑⟩[llift d] = A[d]⟨↑⟩.
Proof.
  rewrite (ren_subst_ty _ _ _ (lren d ↑)), (subst_ren_ty _ _ (lren d ↑)); auto.
  all: intros n; rewrite ?llk_lren, ?rlk_shift1, ?llk_llift; reflexivity.
Qed.
Lemma shift_llift (t : tm) d : t⟨↑⟩[llift d] = t[d]⟨↑⟩.
Proof.
  rewrite (ren_subst _ _ _ (lren d ↑)), (subst_ren _ _ (lren d ↑)); auto.
  all: intros n; rewrite ?llk_lren, ?rlk_shift1, ?llk_llift; reflexivity.
Qed.

Lemma shift2_as (u : tm) : u⟨↑⟩⟨↑⟩ = u[lshift 2].
Proof. rewrite ren_ren_comp; apply ren_as_subst; intros; rlk_simpl; cbn; f_equal; lia. Qed.
Lemma shift_cons2 (u x : tm) : u⟨↑⟩[lcons (lshift 2) x] = u[lshift 2].
Proof. apply ren_subst; intros; rlk_simpl; cbn; f_equal; lia. Qed.
Lemma shift2_as_ty (T : ty) : T⟨↑⟩⟨↑⟩ = T[lshift 2].
Proof. rewrite ren_ren_comp_ty; apply ren_as_subst_ty; intros; rlk_simpl; cbn; f_equal; lia. Qed.
Lemma shift_cons2_ty (T : ty) x : T⟨↑⟩[lcons (lshift 2) x] = T[lshift 2].
Proof. apply ren_subst_ty; intros; rlk_simpl; cbn; f_equal; lia. Qed.

Lemma liftshift_llift_ty (B : ty) d : B⟨rlift ↑⟩[llift (llift d)] = B[llift d]⟨rlift ↑⟩.
Proof.
  rewrite ren_as_r2l_ty, (ren_as_r2l_ty B[llift d]).
  apply subst2_eq_ty; intros [|n]; rewrite ?llk_r2l, ?llk_llift; rlk_simpl; cbn.
  - rewrite !llk_llift; reflexivity.
  - rewrite !llk_llift. change (ren_tm ?x ?r) with x⟨r⟩.
    now rewrite shift2_as, shift_cons2.
Qed.

Lemma liftshift_llift (N : tm) d : N⟨rlift ↑⟩[llift (llift d)] = N[llift d]⟨rlift ↑⟩.
Proof.
  rewrite ren_as_r2l, (ren_as_r2l N[llift d]).
  apply subst2_eq; intros [|n]; rewrite ?llk_r2l, ?llk_llift; rlk_simpl; cbn.
  - rewrite !llk_llift; reflexivity.
  - rewrite !llk_llift. change (ren_tm ?x ?r) with x⟨r⟩.
    now rewrite shift2_as, shift_cons2.
Qed.

(** [elim_W]'s step under three binders, and its induction hypothesis (M13a). *)
Lemma lift3shift_llift (t : tm) d :
  t⟨rlift (rlift (rlift ↑))⟩[llift (llift (llift (llift d)))] = t[llift (llift (llift d))]⟨rlift (rlift (rlift ↑))⟩.
Proof.
  rewrite (ren_subst _ _ _ (lren (llift (llift (llift d))) (rlift (rlift (rlift ↑))))),
          (subst_ren _ _ (lren (llift (llift (llift d))) (rlift (rlift (rlift ↑))))); auto.
  - intros n; now rewrite llk_lren.
  - intros [|[|[|n]]]; rewrite llk_lren; rlk_simpl; rewrite ?llk_llift; cbn; try reflexivity.
    rewrite ?llk_llift. cbn. change (ren_tm ?x ?r) with x⟨r⟩.
    rewrite !ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; lia.
Qed.

(** [elim_IWf]'s child index and motive, under two binders (M17b). *)
Lemma lift2shift_llift (t : tm) d :
  t⟨rlift (rlift ↑)⟩[llift (llift (llift d))] = t[llift (llift d)]⟨rlift (rlift ↑)⟩.
Proof.
  rewrite (ren_subst _ _ _ (lren (llift (llift d)) (rlift (rlift ↑)))),
          (subst_ren _ _ (lren (llift (llift d)) (rlift (rlift ↑)))); auto.
  - intros n; now rewrite llk_lren.
  - intros [|[|n]]; rewrite llk_lren; rlk_simpl; rewrite ?llk_llift; cbn; try reflexivity.
    rewrite ?llk_llift. cbn. change (ren_tm ?x ?r) with x⟨r⟩.
    rewrite !ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; lia.
Qed.
Lemma lift2shift_llift_ty (T : ty) d :
  T⟨rlift (rlift ↑)⟩[llift (llift (llift d))] = T[llift (llift d)]⟨rlift (rlift ↑)⟩.
Proof.
  rewrite (ren_subst_ty _ _ _ (lren (llift (llift d)) (rlift (rlift ↑)))),
          (subst_ren_ty _ _ (lren (llift (llift d)) (rlift (rlift ↑)))); auto.
  - intros n; now rewrite llk_lren.
  - intros [|[|n]]; rewrite llk_lren; rlk_simpl; rewrite ?llk_llift; cbn; try reflexivity.
    rewrite ?llk_llift. cbn. change (ren_tm ?x ?r) with x⟨r⟩.
    rewrite !ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; lia.
Qed.

(** [nth] (M15a): no side condition. *)
Lemma subst_tmNth l T k cs i d : (tmNth l T k cs i)[d] = tmNth l T[d] k[d] cs[d] i[d].
Proof.
  unfold tmNth, nthMot, nthBase, nthStep. push_subst.
  rewrite ?llk_llift. cbn.
  repeat progress rewrite ?shift_llift_ty, ?shift_llift, ?llk_llift.
  reflexivity.
Qed.

Section Nf.
Variables (d : lsub) (Hd : LK nftm d).

Lemma single_subst_ty (B : ty) s : B[lsingle s][d] = B[llift d][lsingle s[d]].
Proof.
  apply subst2_eq_ty; intros [|n]; rewrite ?llk_llift; cbn; auto.
  change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift_single by apply Hd. now rewrite Nat.add_0_r.
Qed.
Lemma single_subst (b s : tm) : b[lsingle s][d] = b[llift d][lsingle s[d]].
Proof.
  apply subst2_eq; intros [|n]; rewrite ?llk_llift; cbn; auto.
  change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift_single by apply Hd. now rewrite Nat.add_0_r.
Qed.

Lemma single2_subst (z t q : tm) :
  z[lsingle2 t q][d] = z[llift (llift d)][lsingle2 t[d] q[d]].
Proof.
  apply subst2_eq; intros [|[|n]]; rewrite ?llk_llift; cbn; auto.
  change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift2_single2 by apply Hd. now rewrite Nat.add_0_r.
Qed.
Lemma single2_subst_ty (M : ty) t q :
  M[lsingle2 t q][d] = M[llift (llift d)][lsingle2 t[d] q[d]].
Proof.
  apply subst2_eq_ty; intros [|[|n]]; rewrite ?llk_llift; cbn; auto.
  change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift2_single2 by apply Hd. now rewrite Nat.add_0_r.
Qed.

Lemma single3_subst (c a f h : tm) :
  c[lsingle3 a f h][d] = c[llift (llift (llift d))][lsingle3 a[d] f[d] h[d]].
Proof.
  apply subst2_eq; intros [|[|[|n]]]; rewrite ?llk_llift; cbn; auto.
  change (ren_tm ?x ?r) with x⟨r⟩. rewrite ?llk_llift. cbn. change (ren_tm ?x ?r) with x⟨r⟩.
  rewrite !ren_ren_comp, (ren_subst _ _ _ (lshift 0)).
  - rewrite Nat.add_0_r. symmetry; apply subst_id; [apply Hd | intros; cbn; f_equal; lia].
  - intros m; rlk_simpl; cbn; f_equal; lia.
Qed.
Lemma subst_wIH l l' l'' A B M c a f :
  (wIH l l' l'' A B M c a f)[d] =
  wIH l l' l'' A[d] B[llift d] M[llift d] c[llift (llift (llift d))] a[d] f[d].
Proof.
  unfold wIH. rewrite subst_lam, subst_elimW, subst_app, subst_var, (llk_llift d 0), single_subst_ty.
  cbn beta iota.
  repeat progress rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?lift3shift_llift, ?single_subst_ty.
  reflexivity.
Qed.
(** [elim_Wf]'s induction hypothesis (M15a). *)
Lemma subst_wfIH l l' A N M c a cs :
  (wfIH l l' A N M c a cs)[d] =
  wfIH l l' A[d] N[llift d] M[llift d] c[llift (llift (llift d))] a[d] cs[d].
Proof.
  unfold wfIH. rewrite subst_lam, subst_tyFin, subst_elimWf, subst_tmNth, subst_var, (llk_llift d 0).
  rewrite ?subst_tyWf.
  repeat progress rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?liftshift_llift,
    ?lift3shift_llift, ?single_subst.
  reflexivity.
Qed.
End Nf.

(** [dnth] and [elim_IWf]'s induction hypothesis (M17b): [dnth]'s family
    is instantiated under its binders, so the instances need [d] normal. *)
Lemma subst_tmDNth l n F cs i d : LK nftm d ->
  (tmDNth l n F cs i)[d] = tmDNth l n[d] F[llift d] cs[d] i[d].
Proof.
  intros Hd.
  unfold tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS. push_subst.
  repeat progress (
    repeat match goal with
      | |- context [subst (subst ?B (lsingle ?u)) ?e] =>
          let H := fresh in assert (H : LK nftm e) by (repeat apply lk_llift; exact Hd);
          rewrite (single_subst_ty e H B u); clear H; push_subst
      end;
    rewrite ?llk_llift; cbn [llk];
    rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?liftshift_llift).
  reflexivity.
Qed.
Lemma llift_single_subst (c a : tm) d : LK nftm d ->
  c[llift (lsingle a)][llift d] = c[llift (llift d)][llift (lsingle a[d])].
Proof.
  intros Hd. apply subst2_eq; intros [|[|n]]; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; auto.
  - change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift_llift. reflexivity.
  - rewrite Nat.add_0_r, Nat.add_1_r. change (ren_tm ?x ?r) with x⟨r⟩.
    rewrite shift_llift, shift_single by apply Hd. reflexivity.
Qed.
Lemma subst_iwfIH l li l' X A N Ot C M c a cs d : LK nftm d ->
  (iwfIH l li l' X A N Ot C M c a cs)[d] =
  iwfIH l li l' X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] M[llift (llift d)]
    c[llift (llift (llift d))] a[d] cs[d].
Proof.
  intros Hd. unfold iwfIH, iwfFam. rewrite subst_lam, subst_tyFin, subst_elimIWf, subst_tmDNth, subst_var, (llk_llift d 0)
    by (repeat apply lk_llift; exact Hd).
  repeat progress (push_subst; rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?liftshift_llift,
    ?lift3shift_llift, ?lift2shift_llift, ?lift2shift_llift_ty, ?(single_subst d Hd),
    ?(llift_single_subst _ _ _ Hd)).
  reflexivity.
Qed.

Lemma subst_iwfFam l li X A N Ot C a d : LK nftm d ->
  (iwfFam l li X A N Ot C a)[llift d] =
  iwfFam l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] a[d].
Proof.
  intros Hd. unfold iwfFam. push_subst.
  rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?liftshift_llift,
    ?lift2shift_llift, ?lift2shift_llift_ty, ?(llift_single_subst _ _ _ Hd).
  reflexivity.
Qed.

(** [M]'s [out]-of-[corec] reduct (M18b): its instances sit under up to
    three binders. *)
Lemma llift_single_subst_ty (B : ty) a d : LK nftm d ->
  B[llift (lsingle a)][llift d] = B[llift (llift d)][llift (lsingle a[d])].
Proof.
  intros Hd. apply subst2_eq_ty; intros [|[|n]]; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; auto.
  - change (ren_tm ?x ?r) with x⟨r⟩. rewrite shift_llift. reflexivity.
  - rewrite Nat.add_0_r, Nat.add_1_r. change (ren_tm ?x ?r) with x⟨r⟩.
    rewrite shift_llift, shift_single by apply Hd. reflexivity.
Qed.
Lemma llift2_single_subst (c a : tm) d : LK nftm d ->
  c[llift (llift (lsingle a))][llift (llift d)] = c[llift (llift (llift d))][llift (llift (lsingle a[d]))].
Proof.
  intros Hd. apply subst2_eq; intros [|[|[|n]]]; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; auto.
  all: rewrite ?Nat.add_0_r, ?Nat.add_1_r; rewrite ?llk_llift; cbn; rewrite ?llk_llift.
  all: repeat change (ren_tm ?x ?r) with x⟨r⟩.
  all: rewrite ?shift_llift, ?shift_single by apply Hd; reflexivity.
Qed.
Lemma llift2_single_subst_ty (c : ty) a d : LK nftm d ->
  c[llift (llift (lsingle a))][llift (llift d)] = c[llift (llift (llift d))][llift (llift (lsingle a[d]))].
Proof.
  intros Hd. apply subst2_eq_ty; intros [|[|[|n]]]; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; auto.
  all: rewrite ?Nat.add_0_r, ?Nat.add_1_r; rewrite ?llk_llift; cbn; rewrite ?llk_llift.
  all: repeat change (ren_tm ?x ?r) with x⟨r⟩.
  all: rewrite ?shift_llift, ?shift_single by apply Hd; reflexivity.
Qed.
Lemma llift3_single_subst (c a : tm) d : LK nftm d ->
  c[llift (llift (llift (lsingle a)))][llift (llift (llift d))] =
  c[llift (llift (llift (llift d)))][llift (llift (llift (lsingle a[d])))].
Proof.
  intros Hd. apply subst2_eq; intros [|[|[|[|n]]]]; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; auto.
  all: rewrite ?Nat.add_0_r, ?Nat.add_1_r; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; rewrite ?llk_llift.
  all: repeat change (ren_tm ?x ?r) with x⟨r⟩.
  all: rewrite ?shift_llift, ?shift_single by apply Hd; reflexivity.
Qed.
Lemma llift_single2_subst (c a b : tm) d : LK nftm d ->
  c[llift (lsingle2 a b)][llift d] = c[llift (llift (llift d))][llift (lsingle2 a[d] b[d])].
Proof.
  intros Hd. apply subst2_eq; intros [|[|[|n]]]; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; auto.
  all: rewrite ?Nat.add_0_r, ?Nat.add_1_r; rewrite ?llk_llift; cbn; rewrite ?llk_llift.
  all: repeat change (ren_tm ?x ?r) with x⟨r⟩.
  all: rewrite ?shift_llift, ?shift2_single2 by apply Hd; reflexivity.
Qed.

Ltac lk_solve Hd := repeat apply lk_llift; exact Hd.
Ltac msubst_step Hd :=
  match goal with
  | |- context [subst (subst ?B (lsingle ?u)) ?e] =>
      let H := fresh in assert (H : LK nftm e) by lk_solve Hd;
      first [rewrite (single_subst_ty e H B u) | rewrite (single_subst e H B u)]; clear H
  | |- context [subst (subst ?B (lsingle2 ?u ?v)) ?e] =>
      let H := fresh in assert (H : LK nftm e) by lk_solve Hd;
      first [rewrite (single2_subst_ty e H B u v) | rewrite (single2_subst e H B u v)]; clear H
  | |- context [subst (subst ?B (llift (lsingle ?u))) (llift ?e)] =>
      let H := fresh in assert (H : LK nftm e) by lk_solve Hd;
      first [rewrite (llift_single_subst_ty B u e H) | rewrite (llift_single_subst B u e H)]; clear H
  | |- context [subst (subst ?B (llift (llift (lsingle ?u)))) (llift (llift ?e))] =>
      let H := fresh in assert (H : LK nftm e) by lk_solve Hd;
      first [rewrite (llift2_single_subst_ty B u e H) | rewrite (llift2_single_subst B u e H)]; clear H
  | |- context [subst (subst ?B (llift (llift (llift (lsingle ?u))))) (llift (llift (llift ?e)))] =>
      let H := fresh in assert (H : LK nftm e) by lk_solve Hd;
      rewrite (llift3_single_subst B u e H); clear H
  | |- context [subst (subst ?B (llift (lsingle2 ?u ?v))) (llift ?e)] =>
      let H := fresh in assert (H : LK nftm e) by lk_solve Hd;
      rewrite (llift_single2_subst B u v e H); clear H
  end.

Lemma subst_mOutCorec l l' li X A B C k Y c j y d : LK nftm d ->
  (mOutCorec l l' li X A B C k Y c j y)[d] =
  mOutCorec l l' li X[d] A[llift d] B[llift (llift d)] C[llift (llift (llift d))] k Y[llift d]
    c[llift (llift d)] j[d] y[d].
Proof.
  intros Hd. unfold mOutCorec.
  repeat progress (push_subst; repeat msubst_step Hd;
    rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?liftshift_llift,
      ?lift3shift_llift, ?lift2shift_llift, ?lift2shift_llift_ty, ?(llk_llift _ 0)).
  reflexivity.
Qed.

Lemma lsucc_subst_ty (M : ty) d : M[lsucc][llift (llift d)] = M[llift d][lsucc].
Proof.
  apply subst2_eq_ty; intros [|n]; cbn.
  - rewrite !llk_llift; reflexivity.
  - rewrite llk_llift. replace (n + 2) with (S (S n)) by lia.
    rewrite !llk_llift. change (ren_tm (llk d n) ↑) with (llk d n)⟨↑⟩.
    change (ren_tm ?x ?r) with x⟨r⟩. unfold lsucc. now rewrite shift2_as, shift_cons2.
Qed.

(** [M[succ x/x][t/x, r/y] = M[succ t/x]]. *)
Lemma lsucc_single2_ty (M : ty) t q : M[lsucc][lsingle2 t q] = M[lsingle (succ t)].
Proof.
  rewrite (subst_subst_ty _ _ _ (lsingle (succ t))); auto.
  intros [|n]; cbn; auto. replace (n + 2) with (S (S n)) by lia. reflexivity.
Qed.

(** [B⟨↑⟩⁺[x/x] = B]: the η-rule's codomain. *)
Lemma liftshift_single_var_ty (B : ty) : nfty B -> B⟨rlift ↑⟩[lsingle (var 0)] = B.
Proof.
  intros HB. rewrite (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; auto. intros; cbn; f_equal; lia.
  - intros [|n]; rlk_simpl; cbn; f_equal; lia.
Qed.

(** [case]'s branch types (M12b): the motive under the branch's variable,
    at the injection of that variable. *)
Lemma liftshift_single_ty (M : ty) f : M⟨rlift ↑⟩[lsingle f] = M[lcons (lshift 1) f].
Proof. apply ren_subst_ty; intros [|n]; rlk_simpl; cbn; [reflexivity | f_equal; lia]. Qed.
(** The same in [subst_ty] form, as the recursor's [case] scopes present it (M12c). *)
Lemma liftshift_cons_ty' (M : ty) f : subst_ty M (lcons (lshift 1) f) = subst_ty M⟨rlift ↑⟩ (lsingle f).
Proof. symmetry; exact (liftshift_single_ty M f). Qed.
Lemma shift_cons1_ty (T : ty) x : T⟨↑⟩[lcons (lshift 1) x] = T[lshift 1].
Proof. apply ren_subst_ty; intros; rlk_simpl; cbn; f_equal; lia. Qed.
Lemma shift1_as_ty (T : ty) : T⟨↑⟩ = T[lshift 1].
Proof. apply ren_as_subst_ty; intros; rlk_simpl; cbn; f_equal; lia. Qed.
Lemma up1_single_ty (M : ty) f a : M[lcons (lshift 1) f][lsingle a] = M[lsingle f[lsingle a]].
Proof. apply subst_subst_ty; intros [|n]; cbn; [reflexivity|]. now rewrite Nat.add_1_r. Qed.

(** ** Cancelling shifts against substitutions

    Rewrites the leaves a pushed substitution leaves behind, of the form
    [X⟨↑⟩…[llift … (lsingle a)]], to the shifted [X] directly: a shift
    commutes with a lifted renaming or substitution and is cancelled by
    a single substitution. Proving the same leaves pointwise (through
    [subst_comp] and [subst_ext], one case per variable) cost 75 s in
    [nth_reds_succ] (WfNth.v). *)
Ltac nf_side := first [assumption | apply ren_nf_ty | apply ren_nf].
Ltac shift_cancel := repeat match goal with
  | |- context [ (?A⟨↑⟩)⟨rlift ?r⟩ ] => first [rewrite (shift_lift_ty A r) | rewrite (shift_lift A r)]
  | |- context [ (?A⟨↑⟩)[llift ?d] ] => first [rewrite (shift_llift_ty A d) | rewrite (shift_llift A d)]
  | |- context [ (?A⟨↑⟩⟨↑⟩)[lsingle2 ?a ?b] ] =>
      first [rewrite (shift2_single2_ty A a b) by nf_side | rewrite (shift2_single2 A a b) by nf_side]
  | |- context [ (?A⟨↑⟩)[lsingle ?a] ] =>
      first [rewrite (shift_single_ty A a) by nf_side | rewrite (shift_single A a) by nf_side]
  end.

(** [IWi]'s field type and [elim_IWi]'s induction hypothesis (M19). *)
Lemma subst_iwiFamCod l lp li X A N D Ot C a d : LK nftm d ->
  (iwiFamCod l lp li X A N D Ot C a)[llift (llift d)] =
  iwiFamCod l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))] a[d].
Proof.
  intros Hd. unfold iwiFamCod. push_subst.
  rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?liftshift_llift, ?lift2shift_llift,
    ?lift2shift_llift_ty, ?lift3shift_llift, ?(llift2_single_subst _ _ _ Hd).
  reflexivity.
Qed.
Lemma subst_iwiFam l lp li X A N D Ot C a d : LK nftm d ->
  (iwiFam l lp li X A N D Ot C a)[llift d] =
  iwiFam l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))] a[d].
Proof.
  intros Hd. unfold iwiFam. push_subst.
  rewrite (subst_iwiFamCod _ _ _ _ _ _ _ _ _ _ _ Hd), (llift_single_subst_ty _ _ _ Hd). reflexivity.
Qed.
Lemma subst_iwiIH l lp li l' X A N D Ot C M c a cs d : LK nftm d ->
  (iwiIH l lp li l' X A N D Ot C M c a cs)[d] =
  iwiIH l lp li l' X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))]
    M[llift (llift d)] c[llift (llift (llift d))] a[d] cs[d].
Proof.
  intros Hd. unfold iwiIH. push_subst. rewrite subst_tmDNth by (repeat apply lk_llift; exact Hd).
  rewrite ?llk_llift; cbn [llk].
  repeat progress (push_subst; rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?liftshift_llift,
    ?lift3shift_llift, ?lift2shift_llift, ?lift2shift_llift_ty, ?(single_subst d Hd),
    ?(llift_single_subst_ty _ _ _ Hd), ?(llift2_single_subst _ _ _ Hd), ?(subst_iwiFam _ _ _ _ _ _ _ _ _ _ _ Hd),
    ?(subst_iwiFamCod _ _ _ _ _ _ _ _ _ _ _ Hd)).
  rewrite !llk_llift. reflexivity.
Qed.
