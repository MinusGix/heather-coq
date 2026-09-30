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

End Nf.

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
