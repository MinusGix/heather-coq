(** * Commutation lemmas used by the typing rules' substitutions

    Everything here is an instance of the extensional laws in [Subst]:
    both sides are turned into a single renaming / substitution and compared
    pointwise. *)
From DeLaM.Syntax Require Export Reduction.

(** ** Syntactic composition of renamings *)

Fixpoint rcomp (r1 r2 : rsub) : rsub :=         (* first r1, then r2 *)
  match r1 with
  | rshift k => rdrop k r2
  | rcons r m => rcons (rcomp r r2) (rlk r2 m)
  end.

Lemma rlk_rcomp r1 r2 n : rlk (rcomp r1 r2) n = rlk r2 (rlk r1 n).
Proof.
  revert n; induction r1 as [k|r IH m]; intros n; cbn.
  - rewrite rlk_rdrop; f_equal; lia.
  - destruct n; auto.
Qed.

Lemma ren_ren_comp_ty (T : ty) r1 r2 : T⟨r1⟩⟨r2⟩ = T⟨rcomp r1 r2⟩.
Proof. apply ren_ren_ty; intros; now rewrite rlk_rcomp. Qed.
Lemma ren_ren_comp (t : tm) r1 r2 : t⟨r1⟩⟨r2⟩ = t⟨rcomp r1 r2⟩.
Proof. apply ren_ren; intros; now rewrite rlk_rcomp. Qed.

Ltac rlk_simpl :=
  repeat first [ rewrite rlk_rcomp | rewrite rlk_rlift | rewrite rlk_rup | rewrite rlk_shift1
               | progress cbn [rlk rshift1] ].


(** ** Constructor equations, in notation form (pushing operations inward)

    [cbn] on these mutual fixpoints exposes raw [fix] bodies; rewriting with
    these equations keeps everything in notation form. *)
Section Push.
Variables (r : rsub) (d : lsub).
Lemma ren_tyNat : tyNat⟨r⟩ = tyNat. Proof. reflexivity. Qed.
Lemma ren_tyPi l l' A B : (tyPi l l' A B)⟨r⟩ = tyPi l l' A⟨r⟩ B⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_tyU l : (tyU l)⟨r⟩ = tyU l. Proof. reflexivity. Qed.
Lemma ren_tyEl l t : (tyEl l t)⟨r⟩ = tyEl l t⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_var n : (var n)⟨r⟩ = var (rlk r n). Proof. reflexivity. Qed.
Lemma ren_tmNat : tmNat⟨r⟩ = tmNat. Proof. reflexivity. Qed.
Lemma ren_tmPi l l' s t : (tmPi l l' s t)⟨r⟩ = tmPi l l' s⟨r⟩ t⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_tmU l : (tmU l)⟨r⟩ = tmU l. Proof. reflexivity. Qed.
Lemma ren_zero : zero⟨r⟩ = zero. Proof. reflexivity. Qed.
Lemma ren_succ t : (succ t)⟨r⟩ = succ t⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_natrec l M s z t :
  (natrec l M s z t)⟨r⟩ = natrec l M⟨rlift r⟩ s⟨r⟩ z⟨rlift (rlift r)⟩ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_lam l l' A t : (lam l l' A t)⟨r⟩ = lam l l' A⟨r⟩ t⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_app t l l' A B s :
  (app t l l' A B s)⟨r⟩ = app t⟨r⟩ l l' A⟨r⟩ B⟨rlift r⟩ s⟨r⟩.
Proof. reflexivity. Qed.

Lemma subst_tyNat : tyNat[d] = tyNat. Proof. reflexivity. Qed.
Lemma subst_tyPi l l' A B : (tyPi l l' A B)[d] = tyPi l l' A[d] B[llift d]. Proof. reflexivity. Qed.
Lemma subst_tyU l : (tyU l)[d] = tyU l. Proof. reflexivity. Qed.
Lemma subst_tyEl l t : (tyEl l t)[d] = tyEl l t[d]. Proof. reflexivity. Qed.
Lemma subst_var n : (var n)[d] = llk d n. Proof. reflexivity. Qed.
Lemma subst_tmNat : tmNat[d] = tmNat. Proof. reflexivity. Qed.
Lemma subst_tmPi l l' s t : (tmPi l l' s t)[d] = tmPi l l' s[d] t[llift d]. Proof. reflexivity. Qed.
Lemma subst_tmU l : (tmU l)[d] = tmU l. Proof. reflexivity. Qed.
Lemma subst_zero : zero[d] = zero. Proof. reflexivity. Qed.
Lemma subst_succ t : (succ t)[d] = succ t[d]. Proof. reflexivity. Qed.
Lemma subst_natrec l M s z t :
  (natrec l M s z t)[d] = natrec l M[llift d] s[d] z[llift (llift d)] t[d].
Proof. reflexivity. Qed.
Lemma subst_lam l l' A t : (lam l l' A t)[d] = lam l l' A[d] t[llift d]. Proof. reflexivity. Qed.
Lemma subst_app t l l' A B s :
  (app t l l' A B s)[d] = app t[d] l l' A[d] B[llift d] s[d].
Proof. reflexivity. Qed.
End Push.

Ltac push_ren := repeat progress (
  rewrite ?ren_tyNat, ?ren_tyPi, ?ren_tyU, ?ren_tyEl, ?ren_var, ?ren_tmNat, ?ren_tmPi,
          ?ren_tmU, ?ren_zero, ?ren_succ, ?ren_natrec, ?ren_lam, ?ren_app).
Ltac push_subst := repeat progress (
  rewrite ?subst_tyNat, ?subst_tyPi, ?subst_tyU, ?subst_tyEl, ?subst_var, ?subst_tmNat,
          ?subst_tmPi, ?subst_tmU, ?subst_zero, ?subst_succ, ?subst_natrec, ?subst_lam,
          ?subst_app).

(** ** Weakening past a binder *)

Lemma shift_lift_ty (A : ty) r : A⟨↑⟩⟨rlift r⟩ = A⟨r⟩⟨↑⟩.
Proof. rewrite !ren_ren_comp_ty. apply ren_ext_ty; intros n; rlk_simpl; lia. Qed.
Lemma shift_lift (t : tm) r : t⟨↑⟩⟨rlift r⟩ = t⟨r⟩⟨↑⟩.
Proof. rewrite !ren_ren_comp. apply ren_ext_tm; intros n; rlk_simpl; lia. Qed.

Lemma liftshift_lift_ty (B : ty) r : B⟨rlift ↑⟩⟨rlift (rlift r)⟩ = B⟨rlift r⟩⟨rlift ↑⟩.
Proof.
  rewrite !ren_ren_comp_ty. apply ren_ext_ty; intros [|n]; rlk_simpl; auto;
    destruct n; rlk_simpl; auto; lia.
Qed.

(** ** Single substitutions under renaming *)

Lemma single_ren_ty (B : ty) (s : tm) r : B[lsingle s]⟨r⟩ = B⟨rlift r⟩[lsingle s⟨r⟩].
Proof.
  rewrite (subst_ren_ty _ _ (lcons (r2l r) s⟨r⟩)), (ren_subst_ty _ _ _ (lcons (r2l r) s⟨r⟩)); auto.
  all: intros [|n]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; auto; f_equal; lia.
Qed.
Lemma single_ren (b s : tm) r : b[lsingle s]⟨r⟩ = b⟨rlift r⟩[lsingle s⟨r⟩].
Proof. apply lsingle_ren. Qed.

Lemma lsucc_ren_ty (M : ty) r : M[lsucc]⟨rlift (rlift r)⟩ = M⟨rlift r⟩[lsucc].
Proof.
  rewrite (subst_ren_ty _ _ (lcons (r2l (rup (rup r))) (succ (var 1)))),
          (ren_subst_ty _ _ _ (lcons (r2l (rup (rup r))) (succ (var 1)))); auto.
  all: intros [|n]; cbn; rewrite ?llk_r2l; try replace (n + 2) with (S (S n)) by lia;
    cbn; rewrite ?rlk_rup; cbn; auto; f_equal; lia.
Qed.

Lemma single2_ren (z t q : tm) r :
  z[lsingle2 t q]⟨r⟩ = z⟨rlift (rlift r)⟩[lsingle2 t⟨r⟩ q⟨r⟩].
Proof. apply lsingle2_ren. Qed.

(** [A⟨↑⟩[a/x] = A] -- needs the normal form invariant of identity laws. *)
Lemma shift_single_ty (A : ty) (a : tm) : nfty A -> A⟨↑⟩[lsingle a] = A.
Proof.
  intros HA. rewrite (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; auto. intros; cbn; f_equal; lia.
  - intros n; rewrite rlk_shift1; cbn; f_equal; lia.
Qed.

(** ** Operation outputs are in normal form *)

Lemma nfl_lcons' d t : nfl d -> nftm t -> nfl (lcons' d t).
Proof.
  intros Hd Ht. destruct d as [[|k]|]; destruct t; cbn in *; try tauto.
  destruct (Nat.eqb_spec n k); cbn; auto.
Qed.
Lemma nfl_r2l r : nfl (r2l r).
Proof. induction r; cbn; auto. apply nfl_lcons'; cbn; auto. Qed.
Lemma nfl_lnorm d : nfl d -> nfl (lnorm d).
Proof. induction d; cbn; intuition auto using nfl_lcons'. Qed.
Lemma nfl_ldrop k d : nfl d -> nfl (ldrop k d).
Proof. revert d; induction k; intros [m|d t]; cbn; intuition. Qed.

Lemma ren_nf_all :
  let Pty T := forall r, nfty (ren_ty T r) in
  let Ptm t := forall r, nftm (ren_tm t r) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\
  (forall d, forall r, nfl (lren d r)).
Proof.
  intros Pty Ptm; apply syn_ind; subst Pty Ptm; cbn beta; intros; try exact I;
    cbn; intuition auto using nfl_r2l, nfl_lcons'.
Qed.
Lemma ren_nf_ty (T : ty) r : nfty T⟨r⟩.
Proof. apply ren_nf_all. Qed.
Lemma ren_nf (t : tm) r : nftm t⟨r⟩.
Proof. apply ren_nf_all. Qed.

Lemma gren_nf_all :
  let Pty T := nfty T -> forall ξ, nfty (gren_ty T ξ) in
  let Ptm t := nftm t -> forall ξ, nftm (gren_tm t ξ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ : ctx, True) /\
  (forall d, nfl d -> forall ξ, nfl (glren d ξ)).
Proof.
  intros Pty Ptm; apply syn_ind; subst Pty Ptm; cbn beta; intros; try exact I;
    cbn in *; intuition auto using nfl_lcons'.
Qed.
Lemma gren_nf (t : tm) ξ : nftm t -> nftm t⟪ξ⟫.
Proof. intros; now apply gren_nf_all. Qed.

(** Identity renaming on renaming outputs. *)
Lemma ren_id_ty (T : ty) : nfty T -> T⟨rshift 0⟩ = T.
Proof.
  intros H. rewrite (ren_as_subst_ty _ _ (lshift 0)); [apply subst_id_ty; auto|];
    intros; cbn; f_equal; lia.
Qed.
