(** * Commutation lemmas used by the typing rules' substitutions

    Everything here is an instance of the extensional laws in [Subst]:
    both sides are turned into a single renaming / substitution and compared
    pointwise. *)
From DeLaM.Syntax Require Export Reduction.

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
Lemma ren_tyEmpty l : (tyEmpty l)⟨r⟩ = tyEmpty l. Proof. reflexivity. Qed.
Lemma ren_tySum l l' A B : (tySum l l' A B)⟨r⟩ = tySum l l' A⟨r⟩ B⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_inl l l' A B a : (tmInl l l' A B a)⟨r⟩ = tmInl l l' A⟨r⟩ B⟨r⟩ a⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_inr l l' A B a : (tmInr l l' A B a)⟨r⟩ = tmInr l l' A⟨r⟩ B⟨r⟩ a⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_case l l' l'' A B M c1 c2 t :
  (tmCase l l' l'' A B M c1 c2 t)⟨r⟩ = tmCase l l' l'' A⟨r⟩ B⟨r⟩ M⟨rlift r⟩ c1⟨rlift r⟩ c2⟨rlift r⟩ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_elimEmpty l l' M t : (elimEmpty l l' M t)⟨r⟩ = elimEmpty l l' M⟨rlift r⟩ t⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_srefl l A a : (srefl l A a)⟨r⟩ = srefl l A⟨r⟩ a⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_elimSEmpty l l' M e : (elimSEmpty l l' M e)⟨r⟩ = elimSEmpty l l' M⟨r⟩ e⟨r⟩.
Proof. reflexivity. Qed.
Lemma subst_tySEq l A a b : (tySEq l A a b)[d] = tySEq l A[d] a[d] b[d]. Proof. reflexivity. Qed.
Lemma subst_tySEmpty l : (tySEmpty l)[d] = tySEmpty l. Proof. reflexivity. Qed.
Lemma subst_tyEmpty l : (tyEmpty l)[d] = tyEmpty l. Proof. reflexivity. Qed.
Lemma subst_tySum l l' A B : (tySum l l' A B)[d] = tySum l l' A[d] B[d]. Proof. reflexivity. Qed.
Lemma subst_inl l l' A B a : (tmInl l l' A B a)[d] = tmInl l l' A[d] B[d] a[d]. Proof. reflexivity. Qed.
Lemma subst_inr l l' A B a : (tmInr l l' A B a)[d] = tmInr l l' A[d] B[d] a[d]. Proof. reflexivity. Qed.
Lemma subst_case l l' l'' A B M c1 c2 t :
  (tmCase l l' l'' A B M c1 c2 t)[d] = tmCase l l' l'' A[d] B[d] M[llift d] c1[llift d] c2[llift d] t[d].
Proof. reflexivity. Qed.
Lemma subst_elimEmpty l l' M t : (elimEmpty l l' M t)[d] = elimEmpty l l' M[llift d] t[d]. Proof. reflexivity. Qed.
Lemma subst_srefl l A a : (srefl l A a)[d] = srefl l A[d] a[d]. Proof. reflexivity. Qed.
Lemma subst_elimSEmpty l l' M e : (elimSEmpty l l' M e)[d] = elimSEmpty l l' M[d] e[d].
Proof. reflexivity. Qed.
(** The identity type (M11a). *)
Lemma ren_tyId l A a b : (tyId l A a b)⟨r⟩ = tyId l A⟨r⟩ a⟨r⟩ b⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_refl l A a : (tmRefl l A a)⟨r⟩ = tmRefl l A⟨r⟩ a⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tmId l s t u : (tmId l s t u)⟨r⟩ = tmId l s⟨r⟩ t⟨r⟩ u⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tmSEq l s t u : (tmSEq l s t u)⟨r⟩ = tmSEq l s⟨r⟩ t⟨r⟩ u⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tmSEmpty l : (tmSEmpty l)⟨r⟩ = tmSEmpty l. Proof. reflexivity. Qed.
Lemma ren_tmEmpty l : (tmEmpty l)⟨r⟩ = tmEmpty l. Proof. reflexivity. Qed.
Lemma ren_tmSum l l' s t : (tmSum l l' s t)⟨r⟩ = tmSum l l' s⟨r⟩ t⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tmW l l' s t : (tmW l l' s t)⟨r⟩ = tmW l l' s⟨r⟩ t⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_tmVec l s n : (tmVec l s n)⟨r⟩ = tmVec l s⟨r⟩ n⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tmFin n : (tmFin n)⟨r⟩ = tmFin n⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tmWf l s n : (tmWf l s n)⟨r⟩ = tmWf l s⟨r⟩ n⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_J l l' A a M c u e :
  (tmJ l l' A a M c u e)⟨r⟩ = tmJ l l' A⟨r⟩ a⟨r⟩ M⟨rlift (rlift r)⟩ c⟨r⟩ u⟨r⟩ e⟨r⟩.
Proof. reflexivity. Qed.
Lemma subst_tyId l A a b : (tyId l A a b)[d] = tyId l A[d] a[d] b[d]. Proof. reflexivity. Qed.
Lemma subst_refl l A a : (tmRefl l A a)[d] = tmRefl l A[d] a[d]. Proof. reflexivity. Qed.
Lemma subst_tmId l s t u : (tmId l s t u)[d] = tmId l s[d] t[d] u[d]. Proof. reflexivity. Qed.
Lemma subst_tmSEq l s t u : (tmSEq l s t u)[d] = tmSEq l s[d] t[d] u[d]. Proof. reflexivity. Qed.
Lemma subst_tmSEmpty l : (tmSEmpty l)[d] = tmSEmpty l. Proof. reflexivity. Qed.
Lemma subst_tmEmpty l : (tmEmpty l)[d] = tmEmpty l. Proof. reflexivity. Qed.
Lemma subst_tmSum l l' s t : (tmSum l l' s t)[d] = tmSum l l' s[d] t[d]. Proof. reflexivity. Qed.
Lemma subst_tmW l l' s t : (tmW l l' s t)[d] = tmW l l' s[d] t[llift d]. Proof. reflexivity. Qed.
Lemma subst_tmVec l s n : (tmVec l s n)[d] = tmVec l s[d] n[d]. Proof. reflexivity. Qed.
Lemma subst_tmFin n : (tmFin n)[d] = tmFin n[d]. Proof. reflexivity. Qed.
Lemma subst_tmWf l s n : (tmWf l s n)[d] = tmWf l s[d] n[llift d]. Proof. reflexivity. Qed.
Lemma subst_J l l' A a M c u e :
  (tmJ l l' A a M c u e)[d] = tmJ l l' A[d] a[d] M[llift (llift d)] c[d] u[d] e[d].
Proof. reflexivity. Qed.
(** Well-founded trees (M13a): [B] binds the shape, [M] the scrutinee, the
    step its three variables. *)
Lemma ren_tyW l l' A B : (tyW l l' A B)⟨r⟩ = tyW l l' A⟨r⟩ B⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_sup l l' A B a f : (tmSup l l' A B a f)⟨r⟩ = tmSup l l' A⟨r⟩ B⟨rlift r⟩ a⟨r⟩ f⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_elimW l l' l'' A B M c t :
  (tmElimW l l' l'' A B M c t)⟨r⟩ = tmElimW l l' l'' A⟨r⟩ B⟨rlift r⟩ M⟨rlift r⟩ c⟨rlift (rlift (rlift r))⟩ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_wIH l l' l'' A B M c a f :
  (wIH l l' l'' A B M c a f)⟨r⟩ =
  wIH l l' l'' A⟨r⟩ B⟨rlift r⟩ M⟨rlift r⟩ c⟨rlift (rlift (rlift r))⟩ a⟨r⟩ f⟨r⟩.
Proof. apply wIH_ren. Qed.
Lemma subst_tyW l l' A B : (tyW l l' A B)[d] = tyW l l' A[d] B[llift d]. Proof. reflexivity. Qed.
Lemma subst_sup l l' A B a f : (tmSup l l' A B a f)[d] = tmSup l l' A[d] B[llift d] a[d] f[d].
Proof. reflexivity. Qed.
Lemma subst_elimW l l' l'' A B M c t :
  (tmElimW l l' l'' A B M c t)[d] = tmElimW l l' l'' A[d] B[llift d] M[llift d] c[llift (llift (llift d))] t[d].
Proof. reflexivity. Qed.
(** Length-indexed tuples and finite indices (M14a): no binder. *)
Lemma ren_tyVec l A n : (tyVec l A n)⟨r⟩ = tyVec l A⟨r⟩ n⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_tyFin n : (tyFin n)⟨r⟩ = tyFin n⟨r⟩. Proof. reflexivity. Qed.
Lemma subst_tyVec l A n : (tyVec l A n)[d] = tyVec l A[d] n[d]. Proof. reflexivity. Qed.
Lemma subst_tyFin n : (tyFin n)[d] = tyFin n[d]. Proof. reflexivity. Qed.
(** Wf trees (M15a): [N] binds the arity, [M] the scrutinee, the step its
    three variables; [tmNth] and [wfIH] are definitions. *)
Lemma ren_tyWf l A N : (tyWf l A N)⟨r⟩ = tyWf l A⟨r⟩ N⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma ren_supf l A N a cs : (tmSupf l A N a cs)⟨r⟩ = tmSupf l A⟨r⟩ N⟨rlift r⟩ a⟨r⟩ cs⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_elimWf l l' A N M c t :
  (tmElimWf l l' A N M c t)⟨r⟩ = tmElimWf l l' A⟨r⟩ N⟨rlift r⟩ M⟨rlift r⟩ c⟨rlift (rlift (rlift r))⟩ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_tmNth l T k cs i : (tmNth l T k cs i)⟨r⟩ = tmNth l T⟨r⟩ k⟨r⟩ cs⟨r⟩ i⟨r⟩.
Proof. apply tmNth_ren. Qed.
Lemma ren_wfIH l l' A N M c a cs :
  (wfIH l l' A N M c a cs)⟨r⟩ =
  wfIH l l' A⟨r⟩ N⟨rlift r⟩ M⟨rlift r⟩ c⟨rlift (rlift (rlift r))⟩ a⟨r⟩ cs⟨r⟩.
Proof. apply wfIH_ren. Qed.
Lemma subst_tyWf l A N : (tyWf l A N)[d] = tyWf l A[d] N[llift d]. Proof. reflexivity. Qed.
Lemma subst_supf l A N a cs : (tmSupf l A N a cs)[d] = tmSupf l A[d] N[llift d] a[d] cs[d].
Proof. reflexivity. Qed.
Lemma subst_elimWf l l' A N M c t :
  (tmElimWf l l' A N M c t)[d] = tmElimWf l l' A[d] N[llift d] M[llift d] c[llift (llift (llift d))] t[d].
Proof. reflexivity. Qed.
(** Propositional truncation (M16a): [M] binds the scrutinee, the step the
    payload. *)
Lemma ren_tySq l A : (tySq l A)⟨r⟩ = tySq l A⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_sq l A a : (tmSq l A a)⟨r⟩ = tmSq l A⟨r⟩ a⟨r⟩. Proof. reflexivity. Qed.
Lemma ren_elimSq l l' A M c t :
  (tmElimSq l l' A M c t)⟨r⟩ = tmElimSq l l' A⟨r⟩ M⟨rlift r⟩ c⟨rlift r⟩ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma subst_tySq l A : (tySq l A)[d] = tySq l A[d]. Proof. reflexivity. Qed.
Lemma subst_sq l A a : (tmSq l A a)[d] = tmSq l A[d] a[d]. Proof. reflexivity. Qed.
Lemma subst_elimSq l l' A M c t :
  (tmElimSq l l' A M c t)[d] = tmElimSq l l' A[d] M[llift d] c[llift d] t[d].
Proof. reflexivity. Qed.
(** Dependent tuples (M17a): [F] binds the position. *)
Lemma ren_tyDVec l n F : (tyDVec l n F)⟨r⟩ = tyDVec l n⟨r⟩ F⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma subst_tyDVec l n F : (tyDVec l n F)[d] = tyDVec l n[d] F[llift d]. Proof. reflexivity. Qed.
Lemma ren_tmSqCode l s : (tmSqCode l s)⟨r⟩ = tmSqCode l s⟨r⟩. Proof. reflexivity. Qed.
Lemma subst_tmSqCode l s : (tmSqCode l s)[d] = tmSqCode l s[d]. Proof. reflexivity. Qed.
(** Indexed finitary trees (M17b): [N] and [Ot] bind the shape, [C] the
    shape and the position, [M] the index and the scrutinee, the step its
    three variables; [tmDNth], [iwfIH] are definitions. *)
Lemma ren_tyIWf l li X A N Ot C m :
  (tyIWf l li X A N Ot C m)⟨r⟩ = tyIWf l li X⟨r⟩ A⟨r⟩ N⟨rlift r⟩ Ot⟨rlift r⟩ C⟨rlift (rlift r)⟩ m⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_supi l li X A N Ot C a cs :
  (tmSupi l li X A N Ot C a cs)⟨r⟩ =
  tmSupi l li X⟨r⟩ A⟨r⟩ N⟨rlift r⟩ Ot⟨rlift r⟩ C⟨rlift (rlift r)⟩ a⟨r⟩ cs⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_elimIWf l li l' X A N Ot C M c m t :
  (tmElimIWf l li l' X A N Ot C M c m t)⟨r⟩ =
  tmElimIWf l li l' X⟨r⟩ A⟨r⟩ N⟨rlift r⟩ Ot⟨rlift r⟩ C⟨rlift (rlift r)⟩ M⟨rlift (rlift r)⟩
    c⟨rlift (rlift (rlift r))⟩ m⟨r⟩ t⟨r⟩.
Proof. reflexivity. Qed.
Lemma ren_tmDNth l n F cs i : (tmDNth l n F cs i)⟨r⟩ = tmDNth l n⟨r⟩ F⟨rlift r⟩ cs⟨r⟩ i⟨r⟩.
Proof. apply tmDNth_ren. Qed.
Lemma ren_iwfIH l li l' X A N Ot C M c a cs :
  (iwfIH l li l' X A N Ot C M c a cs)⟨r⟩ =
  iwfIH l li l' X⟨r⟩ A⟨r⟩ N⟨rlift r⟩ Ot⟨rlift r⟩ C⟨rlift (rlift r)⟩ M⟨rlift (rlift r)⟩
    c⟨rlift (rlift (rlift r))⟩ a⟨r⟩ cs⟨r⟩.
Proof. apply iwfIH_ren. Qed.
Lemma ren_iwfFam l li X A N Ot C a :
  (iwfFam l li X A N Ot C a)⟨rlift r⟩ =
  iwfFam l li X⟨r⟩ A⟨r⟩ N⟨rlift r⟩ Ot⟨rlift r⟩ C⟨rlift (rlift r)⟩ a⟨r⟩.
Proof. apply iwfFam_ren. Qed.
Lemma subst_tyIWf l li X A N Ot C m :
  (tyIWf l li X A N Ot C m)[d] = tyIWf l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] m[d].
Proof. reflexivity. Qed.
Lemma subst_supi l li X A N Ot C a cs :
  (tmSupi l li X A N Ot C a cs)[d] =
  tmSupi l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] a[d] cs[d].
Proof. reflexivity. Qed.
Lemma subst_elimIWf l li l' X A N Ot C M c m t :
  (tmElimIWf l li l' X A N Ot C M c m t)[d] =
  tmElimIWf l li l' X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] M[llift (llift d)]
    c[llift (llift (llift d))] m[d] t[d].
Proof. reflexivity. Qed.
(** The codes of [DVec] and [IWf] (M17c), binding as their types. *)
Lemma ren_tmDVec l n f : (tmDVec l n f)⟨r⟩ = tmDVec l n⟨r⟩ f⟨rlift r⟩. Proof. reflexivity. Qed.
Lemma subst_tmDVec l n f : (tmDVec l n f)[d] = tmDVec l n[d] f[llift d]. Proof. reflexivity. Qed.
Lemma ren_tmIWf l li x s n o c m :
  (tmIWf l li x s n o c m)⟨r⟩ = tmIWf l li x⟨r⟩ s⟨r⟩ n⟨rlift r⟩ o⟨rlift r⟩ c⟨rlift (rlift r)⟩ m⟨r⟩.
Proof. reflexivity. Qed.
Lemma subst_tmIWf l li x s n o c m :
  (tmIWf l li x s n o c m)[d] = tmIWf l li x[d] s[d] n[llift d] o[llift d] c[llift (llift d)] m[d].
Proof. reflexivity. Qed.
(** Defined globals (M9): the body stays in its own local scope. *)
Lemma ren_gdef u b e : (gdef u b e)⟨r⟩ = gdef u b (lren e r). Proof. reflexivity. Qed.
Lemma subst_gdef u b e : (gdef u b e)[d] = gdef u b (lcomp e d). Proof. reflexivity. Qed.
End Push.

(** The head constant of an application (for the syntactic push tactics,
    generated by [tools/gen_push.py]). *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

(** [push_ren]: generated by [tools/gen_push.py] from its lemma list. *)
Ltac push_ren_at h k := lazymatch h with
  | @tyNat => k ren_tyNat
  | @tyPi => k ren_tyPi
  | @tyU => k ren_tyU
  | @tyEl => k ren_tyEl
  | @var => k ren_var
  | @tmNat => k ren_tmNat
  | @tmPi => k ren_tmPi
  | @tmU => k ren_tmU
  | @zero => k ren_zero
  | @succ => k ren_succ
  | @natrec => k ren_natrec
  | @lam => k ren_lam
  | @app => k ren_app
  | @tyGvar => k ren_tyGvar
  | @tyCTyp => k ren_tyCTyp
  | @tyCTrm => k ren_tyCTrm
  | @gvar => k ren_gvar
  | @boxT => k ren_boxT
  | @boxt => k ren_boxt
  | @letboxT => k ren_letboxT
  | @letboxt => k ren_letboxt
  | @elimT => k ren_elimT
  | @elimt => k ren_elimt
  | @tyUPi => k ren_tyUPi
  | @ulam => k ren_ulam
  | @uapp => k ren_uapp
  | @usubst => first [k ren_usubst_ty | k ren_usubst_tm]
  | @uren => k ren_uren_tm
  | @tyCPi => k ren_tyCPi
  | @tyTPi => k ren_tyTPi
  | @clam => k ren_clam
  | @capp => k ren_capp
  | @tlam => k ren_tlam
  | @tapp => k ren_tapp
  | @tySig => k ren_tySig
  | @tmSig => k ren_tmSig
  | @tmPair => k ren_pair
  | @tmFst => k ren_fst
  | @tmSnd => k ren_snd
  | @tyUnit => k ren_tyUnit
  | @tmUnit => k ren_tmUnit
  | @tmTriv => k ren_triv
  | @gdef => k ren_gdef
  | @tySEq => k ren_tySEq
  | @tySEmpty => k ren_tySEmpty
  | @tyEmpty => k ren_tyEmpty
  | @tySum => k ren_tySum
  | @tmInl => k ren_inl
  | @tmInr => k ren_inr
  | @tmCase => k ren_case
  | @elimEmpty => k ren_elimEmpty
  | @srefl => k ren_srefl
  | @elimSEmpty => k ren_elimSEmpty
  | @tyId => k ren_tyId
  | @tmRefl => k ren_refl
  | @tmId => k ren_tmId
  | @tmSEq => k ren_tmSEq
  | @tmSEmpty => k ren_tmSEmpty
  | @tmEmpty => k ren_tmEmpty
  | @tmSum => k ren_tmSum
  | @tmW => k ren_tmW
  | @tmVec => k ren_tmVec
  | @tmFin => k ren_tmFin
  | @tmWf => k ren_tmWf
  | @tmJ => k ren_J
  | @tyW => k ren_tyW
  | @tmSup => k ren_sup
  | @tmElimW => k ren_elimW
  | @wIH => k ren_wIH
  | @tyVec => k ren_tyVec
  | @tyFin => k ren_tyFin
  | @tyWf => k ren_tyWf
  | @tmSupf => k ren_supf
  | @tmElimWf => k ren_elimWf
  | @tmNth => k ren_tmNth
  | @wfIH => k ren_wfIH
  | @tySq => k ren_tySq
  | @tmSq => k ren_sq
  | @tmElimSq => k ren_elimSq
  | @tmSqCode => k ren_tmSqCode
  | @tyDVec => k ren_tyDVec
  | @tyIWf => k ren_tyIWf
  | @tmSupi => k ren_supi
  | @tmElimIWf => k ren_elimIWf
  | @tmDVec => k ren_tmDVec
  | @tmIWf => k ren_tmIWf
  | @tmDNth => k ren_tmDNth
  | @iwfIH => k ren_iwfIH
  | @iwfFam => k ren_iwfFam
  end.
Ltac push_ren := repeat match goal with
  | |- context [@ren _ _ ?t _] => let h := head_of t in push_ren_at h ltac:(fun L => rewrite L)
  end.
(** [push_subst]: generated by [tools/gen_push.py] from its lemma list. *)
Ltac push_subst_at h k := lazymatch h with
  | @tyNat => k subst_tyNat
  | @tyPi => k subst_tyPi
  | @tyU => k subst_tyU
  | @tyEl => k subst_tyEl
  | @var => k subst_var
  | @tmNat => k subst_tmNat
  | @tmPi => k subst_tmPi
  | @tmU => k subst_tmU
  | @zero => k subst_zero
  | @succ => k subst_succ
  | @natrec => k subst_natrec
  | @lam => k subst_lam
  | @app => k subst_app
  | @tyGvar => k subst_tyGvar
  | @tyCTyp => k subst_tyCTyp
  | @tyCTrm => k subst_tyCTrm
  | @gvar => k subst_gvar
  | @boxT => k subst_boxT
  | @boxt => k subst_boxt
  | @letboxT => k subst_letboxT
  | @letboxt => k subst_letboxt
  | @elimT => k subst_elimT
  | @elimt => k subst_elimt
  | @tyUPi => k subst_tyUPi
  | @ulam => k subst_ulam
  | @uapp => k subst_uapp
  | @tyCPi => k subst_tyCPi
  | @tyTPi => k subst_tyTPi
  | @clam => k subst_clam
  | @capp => k subst_capp
  | @tlam => k subst_tlam
  | @tapp => k subst_tapp
  | @tySig => k subst_tySig
  | @tmSig => k subst_tmSig
  | @tmPair => k subst_pair
  | @tmFst => k subst_fst
  | @tmSnd => k subst_snd
  | @tyUnit => k subst_tyUnit
  | @tmUnit => k subst_tmUnit
  | @tmTriv => k subst_triv
  | @gdef => k subst_gdef
  | @tySEq => k subst_tySEq
  | @tySEmpty => k subst_tySEmpty
  | @tyEmpty => k subst_tyEmpty
  | @tySum => k subst_tySum
  | @tmInl => k subst_inl
  | @tmInr => k subst_inr
  | @tmCase => k subst_case
  | @elimEmpty => k subst_elimEmpty
  | @srefl => k subst_srefl
  | @elimSEmpty => k subst_elimSEmpty
  | @tyId => k subst_tyId
  | @tmRefl => k subst_refl
  | @tmId => k subst_tmId
  | @tmSEq => k subst_tmSEq
  | @tmSEmpty => k subst_tmSEmpty
  | @tmEmpty => k subst_tmEmpty
  | @tmSum => k subst_tmSum
  | @tmW => k subst_tmW
  | @tmVec => k subst_tmVec
  | @tmFin => k subst_tmFin
  | @tmWf => k subst_tmWf
  | @tmJ => k subst_J
  | @tyW => k subst_tyW
  | @tmSup => k subst_sup
  | @tmElimW => k subst_elimW
  | @tyVec => k subst_tyVec
  | @tyFin => k subst_tyFin
  | @tyWf => k subst_tyWf
  | @tmSupf => k subst_supf
  | @tmElimWf => k subst_elimWf
  | @tySq => k subst_tySq
  | @tmSq => k subst_sq
  | @tmElimSq => k subst_elimSq
  | @tmSqCode => k subst_tmSqCode
  | @tyDVec => k subst_tyDVec
  | @tyIWf => k subst_tyIWf
  | @tmSupi => k subst_supi
  | @tmElimIWf => k subst_elimIWf
  | @tmDVec => k subst_tmDVec
  | @tmIWf => k subst_tmIWf
  end.
Ltac push_subst := repeat match goal with
  | |- context [@subst _ _ ?t _] => let h := head_of t in push_subst_at h ltac:(fun L => rewrite L)
  end.

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
Lemma liftshift_lift (N : tm) r : N⟨rlift ↑⟩⟨rlift (rlift r)⟩ = N⟨rlift r⟩⟨rlift ↑⟩.
Proof.
  rewrite !ren_ren_comp. apply ren_ext_tm; intros [|n]; rlk_simpl; auto;
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
