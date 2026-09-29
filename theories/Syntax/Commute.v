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

Lemma ren_tyGvar U e : (tyGvar U e)⟨r⟩ = tyGvar U (lren e r). Proof. reflexivity. Qed.
Lemma ren_tyCTyp Δ l : (tyCTyp Δ l)⟨r⟩ = tyCTyp Δ l. Proof. reflexivity. Qed.
Lemma ren_tyCTrm Δ T l : (tyCTrm Δ T l)⟨r⟩ = tyCTrm Δ T l. Proof. reflexivity. Qed.
Lemma ren_gvar u e : (gvar u e)⟨r⟩ = gvar u (lren e r). Proof. reflexivity. Qed.
Lemma ren_boxT T : (boxT T)⟨r⟩ = boxT T. Proof. reflexivity. Qed.
Lemma ren_boxt t : (boxt t)⟨r⟩ = boxt t. Proof. reflexivity. Qed.
Lemma ren_letboxT l' l Δ M t' t :
  (letboxT l' l Δ M t' t)⟨r⟩ = letboxT l' l Δ M⟨rlift r⟩ t'⟨r⟩ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_letboxt l' l Δ T M t' t :
  (letboxt l' l Δ T M t' t)⟨r⟩ = letboxt l' l Δ T M⟨rlift r⟩ t'⟨r⟩ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_elimT l1 l2 rb l Δ t : (elimT l1 l2 rb l Δ t)⟨r⟩ = elimT l1 l2 rb⟨r⟩ l Δ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_elimt l1 l2 rb l Δ T t : (elimt l1 l2 rb l Δ T t)⟨r⟩ = elimt l1 l2 rb⟨r⟩ l Δ T t⟨r⟩.
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
Lemma subst_tyGvar U e : (tyGvar U e)[d] = tyGvar U (lcomp e d). Proof. reflexivity. Qed.
Lemma subst_tyCTyp Δ l : (tyCTyp Δ l)[d] = tyCTyp Δ l. Proof. reflexivity. Qed.
Lemma subst_tyCTrm Δ T l : (tyCTrm Δ T l)[d] = tyCTrm Δ T l. Proof. reflexivity. Qed.
Lemma subst_gvar u e : (gvar u e)[d] = gvar u (lcomp e d). Proof. reflexivity. Qed.
Lemma subst_boxT T : (boxT T)[d] = boxT T. Proof. reflexivity. Qed.
Lemma subst_boxt t : (boxt t)[d] = boxt t. Proof. reflexivity. Qed.
Lemma subst_letboxT l' l Δ M t' t :
  (letboxT l' l Δ M t' t)[d] = letboxT l' l Δ M[llift d] t'[gwk d] t[d].
Proof. reflexivity. Qed.
Lemma subst_letboxt l' l Δ T M t' t :
  (letboxt l' l Δ T M t' t)[d] = letboxt l' l Δ T M[llift d] t'[gwk d] t[d].
Proof. reflexivity. Qed.
Lemma subst_elimT l1 l2 rb l Δ t : (elimT l1 l2 rb l Δ t)[d] = elimT l1 l2 rb[d] l Δ t[d].
Proof. reflexivity. Qed.
Lemma subst_elimt l1 l2 rb l Δ T t : (elimt l1 l2 rb l Δ T t)[d] = elimt l1 l2 rb[d] l Δ T t[d].
Proof. reflexivity. Qed.
(** [UΠ] (M4): the body's scope, and its instances and weakenings. *)
Lemma ren_tyUPi n l T : (tyUPi n l T)⟨r⟩ = tyUPi n l T⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_ulam n l T t : (ulam n l T t)⟨r⟩ = ulam n l T⟨r⟩ t⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_uapp t ls : (uapp t ls)⟨r⟩ = uapp t⟨r⟩ ls. Proof. reflexivity. Qed.
Lemma ren_usubst_ty (T : ty) φ : T[φ]ᵤ⟨r⟩ = T⟨r⟩[φ]ᵤ. Proof. symmetry; apply usubst_ren_ty. Qed.
Lemma ren_usubst_tm (t : tm) φ : t[φ]ᵤ⟨r⟩ = t⟨r⟩[φ]ᵤ. Proof. symmetry; apply usubst_ren. Qed.
Lemma ren_uren_tm (t : tm) ρ : t⟨ρ⟩ᵤ⟨r⟩ = t⟨r⟩⟨ρ⟩ᵤ. Proof. symmetry; apply uren_ren_all. Qed.
Lemma subst_tyUPi n l T : (tyUPi n l T)[d] = tyUPi n l T[uwkn n d]. Proof. reflexivity. Qed.
Lemma subst_ulam n l T t : (ulam n l T t)[d] = ulam n l T[uwkn n d] t[uwkn n d]. Proof. reflexivity. Qed.
Lemma subst_uapp t ls : (uapp t ls)[d] = uapp t[d] ls. Proof. reflexivity. Qed.
(** The meta-functions (M5): the body under a global binder, the arguments
    in their own scopes. *)
Lemma ren_tyCPi l T : (tyCPi l T)⟨r⟩ = tyCPi l T⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tyTPi Δ l l' T : (tyTPi Δ l l' T)⟨r⟩ = tyTPi Δ l l' T⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_clam l T t : (clam l T t)⟨r⟩ = clam l T⟨r⟩ t⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_capp t Δ : (capp t Δ)⟨r⟩ = capp t⟨r⟩ Δ. Proof. reflexivity. Qed.
Lemma ren_tlam Δ l l' T t : (tlam Δ l l' T t)⟨r⟩ = tlam Δ l l' T⟨r⟩ t⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tapp t T : (tapp t T)⟨r⟩ = tapp t⟨r⟩ T. Proof. reflexivity. Qed.
Lemma subst_tyCPi l T : (tyCPi l T)[d] = tyCPi l T[gwk d]. Proof. reflexivity. Qed.
Lemma subst_tyTPi Δ l l' T : (tyTPi Δ l l' T)[d] = tyTPi Δ l l' T[gwk d]. Proof. reflexivity. Qed.
Lemma subst_clam l T t : (clam l T t)[d] = clam l T[gwk d] t[gwk d]. Proof. reflexivity. Qed.
Lemma subst_capp t Δ : (capp t Δ)[d] = capp t[d] Δ. Proof. reflexivity. Qed.
Lemma subst_tlam Δ l l' T t : (tlam Δ l l' T t)[d] = tlam Δ l l' T[gwk d] t[gwk d]. Proof. reflexivity. Qed.
Lemma subst_tapp t T : (tapp t T)[d] = tapp t[d] T. Proof. reflexivity. Qed.
(** Dependent pairs (M8): the family binds one local. *)
Lemma ren_tySig l l' A B : (tySig l l' A B)⟨r⟩ = tySig l l' A⟨r⟩ B⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_tmSig l l' s t : (tmSig l l' s t)⟨r⟩ = tmSig l l' s⟨r⟩ t⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_pair l l' A B a b :
  (tmPair l l' A B a b)⟨r⟩ = tmPair l l' A⟨r⟩ B⟨rlift r⟩ a⟨r⟩ b⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_fst l l' A B p : (tmFst l l' A B p)⟨r⟩ = tmFst l l' A⟨r⟩ B⟨rlift r⟩ p⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_snd l l' A B p : (tmSnd l l' A B p)⟨r⟩ = tmSnd l l' A⟨r⟩ B⟨rlift r⟩ p⟨r⟩.
Proof. reflexivity. Qed.
Lemma subst_tySig l l' A B : (tySig l l' A B)[d] = tySig l l' A[d] B[llift d]. Proof. reflexivity. Qed.
Lemma subst_tmSig l l' s t : (tmSig l l' s t)[d] = tmSig l l' s[d] t[llift d]. Proof. reflexivity. Qed.
Lemma subst_pair l l' A B a b :
  (tmPair l l' A B a b)[d] = tmPair l l' A[d] B[llift d] a[d] b[d].
Proof. reflexivity. Qed.
Lemma subst_fst l l' A B p : (tmFst l l' A B p)[d] = tmFst l l' A[d] B[llift d] p[d].
Proof. reflexivity. Qed.
Lemma subst_snd l l' A B p : (tmSnd l l' A B p)[d] = tmSnd l l' A[d] B[llift d] p[d].
Proof. reflexivity. Qed.
(** The unit type (M8c). *)
Lemma ren_tyUnit l : (tyUnit l)⟨r⟩ = tyUnit l. Proof. reflexivity. Qed.
Lemma ren_tmUnit l : (tmUnit l)⟨r⟩ = tmUnit l. Proof. reflexivity. Qed.
Lemma ren_triv l : (tmTriv l)⟨r⟩ = tmTriv l. Proof. reflexivity. Qed.
Lemma subst_tyUnit l : (tyUnit l)[d] = tyUnit l. Proof. reflexivity. Qed.
Lemma subst_tmUnit l : (tmUnit l)[d] = tmUnit l. Proof. reflexivity. Qed.
Lemma subst_triv l : (tmTriv l)[d] = tmTriv l. Proof. reflexivity. Qed.
(** Strict equality (M10a). *)
Lemma ren_tySEq l A a b : (tySEq l A a b)⟨r⟩ = tySEq l A⟨r⟩ a⟨r⟩ b⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tySEmpty l : (tySEmpty l)⟨r⟩ = tySEmpty l. Proof. reflexivity. Qed.
Lemma ren_srefl l A a : (srefl l A a)⟨r⟩ = srefl l A⟨r⟩ a⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_elimSEmpty l l' M e : (elimSEmpty l l' M e)⟨r⟩ = elimSEmpty l l' M⟨r⟩ e⟨r⟩.
Proof. reflexivity. Qed.
Lemma subst_tySEq l A a b : (tySEq l A a b)[d] = tySEq l A[d] a[d] b[d]. Proof. reflexivity. Qed.
Lemma subst_tySEmpty l : (tySEmpty l)[d] = tySEmpty l. Proof. reflexivity. Qed.
Lemma subst_srefl l A a : (srefl l A a)[d] = srefl l A[d] a[d]. Proof. reflexivity. Qed.
Lemma subst_elimSEmpty l l' M e : (elimSEmpty l l' M e)[d] = elimSEmpty l l' M[d] e[d].
Proof. reflexivity. Qed.
(** Defined globals (M9): the body stays in its own local scope. *)
Lemma ren_gdef u b e : (gdef u b e)⟨r⟩ = gdef u b (lren e r). Proof. reflexivity. Qed.
Lemma subst_gdef u b e : (gdef u b e)[d] = gdef u b (lcomp e d). Proof. reflexivity. Qed.
End Push.

Ltac push_ren := repeat progress (
  rewrite ?ren_tyNat, ?ren_tyPi, ?ren_tyU, ?ren_tyEl, ?ren_var, ?ren_tmNat, ?ren_tmPi,
          ?ren_tmU, ?ren_zero, ?ren_succ, ?ren_natrec, ?ren_lam, ?ren_app,
          ?ren_tyGvar, ?ren_tyCTyp, ?ren_tyCTrm, ?ren_gvar, ?ren_boxT, ?ren_boxt,
          ?ren_letboxT, ?ren_letboxt, ?ren_elimT, ?ren_elimt,
          ?ren_tyUPi, ?ren_ulam, ?ren_uapp, ?ren_usubst_ty, ?ren_usubst_tm, ?ren_uren_tm,
          ?ren_tyCPi, ?ren_tyTPi, ?ren_clam, ?ren_capp, ?ren_tlam, ?ren_tapp,
          ?ren_tySig, ?ren_tmSig, ?ren_pair, ?ren_fst, ?ren_snd, ?ren_tyUnit, ?ren_tmUnit, ?ren_triv, ?ren_gdef,
          ?ren_tySEq, ?ren_tySEmpty, ?ren_srefl, ?ren_elimSEmpty).
Ltac push_subst := repeat progress (
  rewrite ?subst_tyNat, ?subst_tyPi, ?subst_tyU, ?subst_tyEl, ?subst_var, ?subst_tmNat,
          ?subst_tmPi, ?subst_tmU, ?subst_zero, ?subst_succ, ?subst_natrec, ?subst_lam,
          ?subst_app, ?subst_tyGvar, ?subst_tyCTyp, ?subst_tyCTrm, ?subst_gvar, ?subst_boxT,
          ?subst_boxt, ?subst_letboxT, ?subst_letboxt, ?subst_elimT, ?subst_elimt,
          ?subst_tyUPi, ?subst_ulam, ?subst_uapp,
          ?subst_tyCPi, ?subst_tyTPi, ?subst_clam, ?subst_capp, ?subst_tlam, ?subst_tapp,
          ?subst_tySig, ?subst_tmSig, ?subst_pair, ?subst_fst, ?subst_snd,
          ?subst_tyUnit, ?subst_tmUnit, ?subst_triv, ?subst_gdef,
          ?subst_tySEq, ?subst_tySEmpty, ?subst_srefl, ?subst_elimSEmpty).

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
