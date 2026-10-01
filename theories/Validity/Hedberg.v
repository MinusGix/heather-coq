(** * Hedberg's theorem, in the syntax (after M12c)

    Heather's [docs/no-uip-model.md] §5.2 predicts UIP wherever the model's
    fibres are discrete, and names the syntax's side of it: Hedberg's
    theorem, UIP at every type with decidable equality. With [Empty] and
    [+] (M12) it can be stated, and this file proves it, as terms:

    - [hedberg_wf]: for [T] and [dec : DecEq T], where
      [DecEq T = Π(x y : T). Id(T; x; y) + ¬Id(T; x; y)], the term
      [hedberg l T dec] has type [Π(x y : T). uip_pt l T x y].
    - [hedbergU_wf]: the internal statement, one closed term of
      [Π(a : Ty l). DecEq(El a) → Π(x y : El a). uip_pt (El a) x y].
    - [uip_bool_wf]: UIP at [Bool = Unit + Unit], from the decider
      [decBool]. On the diagonal it is [refl], by [Unit]-η. Off it, [J]
      transports [tt] along the path into [El(case w of ⌜Unit⌝ | ⌜Empty⌝)],
      which decodes to [Unit] at one injection and to [Empty] at the other.
    - [uip_nat_wf]: UIP at [Nat], from the decider [decNat]: [natrec] on
      [x], then on [y]. [refl] at [(0, 0)]. At [(succ n, succ m)], [case] on
      the hypothesis at [m]: [ap succ] of an equation, or a refutation
      composed with [ap pred] ([pred(succ b) ≡ b] by [natrec]-β). Off the
      diagonal [0 ≠ succ m], again [J] into a code: [El(natrec(⌜Unit⌝,
      ⌜Empty⌝, w))].

    The proof is the textbook one. The collapse
    [f(r) := case dec x y of inl e ⇒ e | inr n ⇒ elim_Empty(n r)] is
    constant ([const], by [case]-β). Every path has [r = f(refl)⁻¹ · f(r)]
    ([key], by [J]; at [refl] it is [s⁻¹ · s = refl], [linv]). So
    [p = f(refl)⁻¹ · f(p) = f(refl)⁻¹ · f(q) = q]. Everything is at layer D,
    as [uip_unit] is; [J]-β and [case]-β also hold at M.

    The terms are built by macros over their leaves. Each macro commutes
    with substitution and renaming ([*_subst], [*_ren]). [sy] decides the
    syntactic equations between the types the rules compute and the
    spellings the lemmas state. It pushes the operations through the macros
    without unfolding them: unfolded, the equations of [apg] alone took
    half a minute. *)
From DeLaM.Validity Require Import Canonicity Uip.

(** ** Path algebra, as macros over a carrier [T] *)

(** [r⁻¹ : Id(T; v; u)] for [r : Id(T; u; v)]. *)
Definition pinv (l : lvl) (T : ty) (u v r : tm) : tm :=
  tmJ l l T u (tyId l T⟨↑⟩⟨↑⟩ (var 1) u⟨↑⟩⟨↑⟩) (tmRefl l T u) v r.
(** [r · s : Id(T; u; w)] for [r : Id(T; u; v)] and [s : Id(T; v; w)], by [J] on [s]. *)
Definition pcat (l : lvl) (T : ty) (u v w r s : tm) : tm :=
  tmJ l l T v (tyId l T⟨↑⟩⟨↑⟩ u⟨↑⟩⟨↑⟩ (var 1)) r w s.
(** [linv]'s motive, over [w : T] and [s : Id(T; x; w)]: [s⁻¹ · s = refl]. *)
Definition Mlinv (l : lvl) (T : ty) (x : tm) : ty :=
  tyId l (tyId l T⟨↑⟩⟨↑⟩ (var 1) (var 1))
    (pcat l T⟨↑⟩⟨↑⟩ (var 1) x⟨↑⟩⟨↑⟩ (var 1) (pinv l T⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ (var 1) (var 0)) (var 0))
    (tmRefl l T⟨↑⟩⟨↑⟩ (var 1)).
(** [s⁻¹ · s = refl], by [J] on [s]. *)
Definition linv (l : lvl) (T : ty) (x w s : tm) : tm :=
  tmJ l l T x (Mlinv l T x) (tmRefl l (tyId l T x x) (tmRefl l T x)) w s.

(** ** Decidable equality, and the path collapse it gives *)

Definition tyNeg (l : lvl) (A : ty) : ty := tyPi l l A (tyEmpty l).
(** [Id(T; x; y) + ¬Id(T; x; y)] over [x y : T]. *)
Definition DecB (l : lvl) (T : ty) : ty :=
  tySum l l (tyId l T⟨↑⟩⟨↑⟩ (var 1) (var 0)) (tyNeg l (tyId l T⟨↑⟩⟨↑⟩ (var 1) (var 0))).
(** [Π(x y : T). Id(T; x; y) + ¬Id(T; x; y)]. *)
Definition DecEq (l : lvl) (T : ty) : ty := tyPi l l T (tyPi l l T⟨↑⟩ (DecB l T)).
Definition DecB1 (l : lvl) (T : ty) (u : tm) : ty :=
  tySum l l (tyId l T⟨↑⟩ u⟨↑⟩ (var 0)) (tyNeg l (tyId l T⟨↑⟩ u⟨↑⟩ (var 0))).
Definition SumI (l : lvl) (T : ty) (u v : tm) : ty := tySum l l (tyId l T u v) (tyNeg l (tyId l T u v)).
(** [dec u v]. *)
Definition decapp (l : lvl) (T : ty) (dec u v : tm) : tm :=
  app (app dec l l T (tyPi l l T⟨↑⟩ (DecB l T)) u) l l T (DecB1 l T u) v.
(** [case s of inl e ⇒ e | inr n ⇒ elim_Empty(n r)]: [r] is the fallback. *)
Definition fcase (l : lvl) (T : ty) (u v r s : tm) : tm :=
  tmCase l l l (tyId l T u v) (tyNeg l (tyId l T u v)) (tyId l T u v)⟨↑⟩ (var 0)
    (elimEmpty l l (tyId l T u v)⟨↑⟩⟨↑⟩ (app (var 0) l l (tyId l T u v)⟨↑⟩ (tyEmpty l) r⟨↑⟩)) s.
(** Hedberg's collapse [f_{u,v} : Id(T; u; v) → Id(T; u; v)], constant in [r]. *)
Definition Fv (l : lvl) (T : ty) (dec u v r : tm) : tm := fcase l T u v r (decapp l T dec u v).
(** [f_{x,x}(refl)⁻¹], and [g(t) := f_{x,x}(refl)⁻¹ · t]. *)
Definition cinv (l : lvl) (T : ty) (dec x : tm) : tm := pinv l T x x (Fv l T dec x x (tmRefl l T x)).
Definition gpath (l : lvl) (T : ty) (dec x v t : tm) : tm := pcat l T x x v (cinv l T dec x) t.

(** ** The proof *)

(** [key]'s motive over [v : T] and [r : Id(T; x; v)]: [r = g(f_{x,v}(r))]. *)
Definition Mkey (l : lvl) (T : ty) (dec x : tm) : ty :=
  tyId l (tyId l T⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ (var 1)) (var 0)
    (gpath l T⟨↑⟩⟨↑⟩ dec⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ (var 1) (Fv l T⟨↑⟩⟨↑⟩ dec⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ (var 1) (var 0))).
(** [r = g(f(r))], by [J] on [r]: at [refl] it is [linv]'s [f(refl)⁻¹ · f(refl) = refl], reversed. *)
Definition key (l : lvl) (T : ty) (dec x v r : tm) : tm :=
  tmJ l l T x (Mkey l T dec x)
    (pinv l (tyId l T x x) (gpath l T dec x x (Fv l T dec x x (tmRefl l T x))) (tmRefl l T x)
       (linv l T x x (Fv l T dec x x (tmRefl l T x))))
    v r.
(** [const]'s motive over [z : Id + ¬Id], and its [inr] instance. *)
Definition Mconst (l : lvl) (T : ty) (x y p q : tm) : ty :=
  tyId l (tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩) (fcase l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ p⟨↑⟩ (var 0)) (fcase l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ q⟨↑⟩ (var 0)).
Definition Mconst_inr (l : lvl) (T : ty) (x y p q : tm) : ty :=
  let I := tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ in
  tyId l I (fcase l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ p⟨↑⟩ (tmInr l l I (tyNeg l I) (var 0)))
    (fcase l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ q⟨↑⟩ (tmInr l l I (tyNeg l I) (var 0))).
(** [f(p) = f(q)], by [case] on [dec x y]: [refl] at [inl], [elim_Empty] at [inr]. *)
Definition const (l : lvl) (T : ty) (dec x y p q : tm) : tm :=
  tmCase l l l (tyId l T x y) (tyNeg l (tyId l T x y)) (Mconst l T x y p q)
    (tmRefl l (tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩) (var 0))
    (elimEmpty l l (Mconst_inr l T x y p q)⟨↑⟩ (app (var 0) l l (tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩) (tyEmpty l) p⟨↑⟩))
    (decapp l T dec x y).
(** [ap g]'s motive, and [ap g e : g(f(p)) = g(f(q))] for [e : f(p) = f(q)]. *)
Definition Map (l : lvl) (T : ty) (dec x y p : tm) : ty :=
  tyId l (tyId l T⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ y⟨↑⟩⟨↑⟩)
    (gpath l T⟨↑⟩⟨↑⟩ dec⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ y⟨↑⟩⟨↑⟩ (Fv l T⟨↑⟩⟨↑⟩ dec⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ y⟨↑⟩⟨↑⟩ p⟨↑⟩⟨↑⟩))
    (gpath l T⟨↑⟩⟨↑⟩ dec⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ y⟨↑⟩⟨↑⟩ (var 1)).
Definition apg (l : lvl) (T : ty) (dec x y p q e : tm) : tm :=
  tmJ l l (tyId l T x y) (Fv l T dec x y p) (Map l T dec x y p)
    (tmRefl l (tyId l T x y) (gpath l T dec x y (Fv l T dec x y p))) (Fv l T dec x y q) e.
(** [p = g(f(p)) = g(f(q)) = q]. *)
Definition body (l : lvl) (T : ty) (dec x y p q : tm) : tm :=
  let I := tyId l T x y in
  let gp := gpath l T dec x y (Fv l T dec x y p) in
  let gq := gpath l T dec x y (Fv l T dec x y q) in
  pcat l I p gq q (pcat l I p gp gq (key l T dec x y p) (apg l T dec x y p q (const l T dec x y p q)))
    (pinv l I q gq (key l T dec x y q)).

(** Hedberg's theorem for [T], from a decider [dec]. *)
Definition uipL (l : lvl) : lvl := lmax l (lmax l (lmax l (lmax l l))).
Definition uipT (l : lvl) (T : ty) : ty :=
  tyPi l (lmax l (lmax l (lmax l l))) T (tyPi l (lmax l (lmax l l)) T⟨↑⟩ (uip_pt l T⟨↑⟩⟨↑⟩ (var 1) (var 0))).
Definition hedberg (l : lvl) (T : ty) (dec : tm) : tm :=
  lam l (lmax l (lmax l (lmax l l))) T (lam l (lmax l (lmax l l)) T⟨↑⟩
    (lam l (lmax l l) (tyId l T⟨↑⟩⟨↑⟩ (var 1) (var 0)) (lam l l (tyId l T⟨↑⟩⟨↑⟩ (var 1) (var 0))⟨↑⟩
      (body l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ dec⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 3) (var 2) (var 1) (var 0))))).

(** ** The internal statement, and the instance at [Bool] *)

(** [Π(a : Ty l). DecEq(El a) → UIP(El a)]. *)
Definition HedbergT (l : lvl) : ty :=
  tyPi (lsuc l) (lmax l (uipL l)) (tyU l) (tyPi l (uipL l) (DecEq l (tyEl l (var 0))) (uipT l (tyEl l (var 1)))).
Definition hedbergU (l : lvl) : tm :=
  lam (lsuc l) (lmax l (uipL l)) (tyU l) (lam l (uipL l) (DecEq l (tyEl l (var 0))) (hedberg l (tyEl l (var 1)) (var 0))).

Definition tyBool (l : lvl) : ty := tySum l l (tyUnit l) (tyUnit l).
Definition binl (l : lvl) (e : tm) : tm := tmInl l l (tyUnit l) (tyUnit l) e.
Definition binr (l : lvl) (e : tm) : tm := tmInr l l (tyUnit l) (tyUnit l) e.
(** The discriminator [El(case s of inl ⇒ c1 | inr ⇒ c2)], for closed codes [c1 c2]. *)
Definition Disc (l : lvl) (c1 c2 s : tm) : ty :=
  tyEl l (tmCase l l (lsuc l) (tyUnit l) (tyUnit l) (tyU l) c1 c2 s).
(** [n : Id(Bool; a; w)] transports [tt : Disc(a)] to [Disc(w)]. *)
Definition disj (l : lvl) (c1 c2 a w n : tm) : tm := tmJ l l (tyBool l) a (Disc l c1 c2 (var 1)) (tmTriv l) w n.
(** The decider: [case x], then [case y]; [refl] on the diagonal (by [Unit]-η), [disj] off it. *)
Definition dec_same (l : lvl) (s : tm) : tm :=
  tmInl l l (tyId l (tyBool l) s s) (tyNeg l (tyId l (tyBool l) s s)) (tmRefl l (tyBool l) s).
Definition dec_diff (l : lvl) (a w c1 c2 : tm) : tm :=
  tmInr l l (tyId l (tyBool l) a w) (tyNeg l (tyId l (tyBool l) a w))
    (lam l l (tyId l (tyBool l) a w) (disj l c1 c2 a⟨↑⟩ w⟨↑⟩ (var 0))).
Definition decBool (l : lvl) : tm :=
  let B := tyBool l in let U := tyUnit l in
  lam l l B (lam l l B
    (tmCase l l l U U (SumI l B (var 0) (var 1))
      (tmCase l l l U U (SumI l B (binl l (var 1)) (var 0))
        (tmInl l l (tyId l B (binl l (var 1)) (binl l (var 0))) (tyNeg l (tyId l B (binl l (var 1)) (binl l (var 0))))
          (tmRefl l B (binl l (var 1))))
        (dec_diff l (binl l (var 1)) (binr l (var 0)) (tmUnit l) (tmEmpty l)) (var 1))
      (tmCase l l l U U (SumI l B (binr l (var 1)) (var 0))
        (dec_diff l (binr l (var 1)) (binl l (var 0)) (tmEmpty l) (tmUnit l))
        (tmInl l l (tyId l B (binr l (var 1)) (binr l (var 0))) (tyNeg l (tyId l B (binr l (var 1)) (binr l (var 0))))
          (tmRefl l B (binr l (var 1)))) (var 1))
      (var 1))).
(** UIP at [Bool], by Hedberg. *)
Definition uip_bool (l : lvl) : tm := hedberg l (tyBool l) (decBool l).

(** *** [Nat] *)

(** [pred t], by [natrec]: [pred(succ t) ≡ t]. *)
Definition pred (t : tm) : tm := natrec lzero tyNat zero (var 1) t.
(** [El(natrec(c1, c2, s))], for closed codes [c1 c2]: [c1] at [zero], [c2] at a successor. *)
Definition DiscN (c1 c2 s : tm) : ty := tyEl lzero (natrec (lsuc lzero) (tyU lzero) c1 c2 s).
Definition disjN (c1 c2 a w n : tm) : tm := tmJ lzero lzero tyNat a (DiscN c1 c2 (var 1)) (tmTriv lzero) w n.
Definition sameN (s : tm) : tm :=
  tmInl lzero lzero (tyId lzero tyNat s s) (tyNeg lzero (tyId lzero tyNat s s)) (tmRefl lzero tyNat s).
Definition diffN (a w c1 c2 : tm) : tm :=
  tmInr lzero lzero (tyId lzero tyNat a w) (tyNeg lzero (tyId lzero tyNat a w))
    (lam lzero lzero (tyId lzero tyNat a w) (disjN c1 c2 a⟨↑⟩ w⟨↑⟩ (var 0))).
(** [ap succ e : Id(succ a; succ b)] and [ap pred p : Id(a; b)]. *)
Definition apsucc (a b e : tm) : tm :=
  tmJ lzero lzero tyNat a (tyId lzero tyNat (succ a⟨↑⟩⟨↑⟩) (succ (var 1))) (tmRefl lzero tyNat (succ a)) b e.
Definition predap (a b p : tm) : tm :=
  tmJ lzero lzero tyNat (succ a) (tyId lzero tyNat a⟨↑⟩⟨↑⟩ (pred (var 1))) (tmRefl lzero tyNat a) (succ b) p.
(** At [(succ n, succ m)], from [h : Π(y : Nat). n = y + n ≠ y]: [case h m]. *)
Definition stepSS (n m h : tm) : tm :=
  tmCase lzero lzero lzero (tyId lzero tyNat n m) (tyNeg lzero (tyId lzero tyNat n m))
    (SumI lzero tyNat (succ n) (succ m))⟨↑⟩
    (tmInl lzero lzero (tyId lzero tyNat (succ n⟨↑⟩) (succ m⟨↑⟩)) (tyNeg lzero (tyId lzero tyNat (succ n⟨↑⟩) (succ m⟨↑⟩)))
       (apsucc n⟨↑⟩ m⟨↑⟩ (var 0)))
    (tmInr lzero lzero (tyId lzero tyNat (succ n⟨↑⟩) (succ m⟨↑⟩)) (tyNeg lzero (tyId lzero tyNat (succ n⟨↑⟩) (succ m⟨↑⟩)))
       (lam lzero lzero (tyId lzero tyNat (succ n⟨↑⟩) (succ m⟨↑⟩))
          (app (var 1) lzero lzero (tyId lzero tyNat n⟨↑⟩⟨↑⟩ m⟨↑⟩⟨↑⟩) (tyEmpty lzero) (predap n⟨↑⟩⟨↑⟩ m⟨↑⟩⟨↑⟩ (var 0)))))
    (app h lzero lzero tyNat (SumI lzero tyNat n⟨↑⟩ (var 0)) m).
(** The decider, by [natrec] on [x], then on [y]. *)
Definition decNat : tm :=
  lam lzero lzero tyNat
    (natrec lzero (tyPi lzero lzero tyNat (SumI lzero tyNat (var 1) (var 0)))
       (lam lzero lzero tyNat
          (natrec lzero (SumI lzero tyNat zero (var 0)) (sameN zero)
             (diffN zero (succ (var 1)) (tmUnit lzero) (tmEmpty lzero)) (var 0)))
       (lam lzero lzero tyNat
          (natrec lzero (SumI lzero tyNat (succ (var 3)) (var 0))
             (diffN (succ (var 2)) zero (tmEmpty lzero) (tmUnit lzero))
             (stepSS (var 4) (var 1) (var 3)) (var 0)))
       (var 0)).
(** UIP at [Nat], by Hedberg. *)
Definition uip_nat : tm := hedberg lzero tyNat decNat.

(** ** Syntactic equations: unfold, push the operations to the leaves *)

Lemma llk_llift_S d n : llk (llift d) (S n) = (llk d n)⟨↑⟩.
Proof. rewrite llk_llift; reflexivity. Qed.
Lemma llk_llift_0 d : llk (llift d) 0 = var 0.
Proof. rewrite llk_llift; reflexivity. Qed.

Ltac nf_tac := first [ apply ren_nf_ty | apply ren_nf | eapply wf_ty_nf; eassumption
                     | eapply wf_tm_nf; eassumption | eapply wf_tm_nf_ty; eassumption | assumption ].
Ltac sy_step := first
  [ progress push_ren | progress push_subst
  | rewrite shift_lift_ty | rewrite shift_lift
  | rewrite shift_llift_ty | rewrite shift_llift
  | rewrite shift2_single2_ty by nf_tac | rewrite shift2_single2 by nf_tac
  | rewrite shift_single_ty by nf_tac | rewrite shift_single by nf_tac
  | rewrite llk_llift_S | rewrite llk_llift_0
  | progress rlk_simpl
  | progress cbn [rlk rshift1 llk lsingle2 lsingle lsucc Nat.add] ].
Ltac sy0 := repeat sy_step; try reflexivity.

(** Each macro commutes with substitution and renaming, so the equations
    below push through macros without unfolding them. *)
Lemma tyNeg_subst (d : lsub) l A : (tyNeg l A)[d] = tyNeg l A[d]. Proof. unfold tyNeg; sy0. Qed.
Lemma tyNeg_ren (ρ : rsub) l A : (tyNeg l A)⟨ρ⟩ = tyNeg l A⟨ρ⟩. Proof. unfold tyNeg; sy0. Qed.
Lemma SumI_subst (d : lsub) l T u v : (SumI l T u v)[d] = SumI l T[d] u[d] v[d].
Proof. unfold SumI; push_subst; rewrite !tyNeg_subst; reflexivity. Qed.
Lemma SumI_ren (ρ : rsub) l T u v : (SumI l T u v)⟨ρ⟩ = SumI l T⟨ρ⟩ u⟨ρ⟩ v⟨ρ⟩.
Proof. unfold SumI; push_ren; rewrite !tyNeg_ren; reflexivity. Qed.
Lemma DecB_subst (d : lsub) l T : (DecB l T)[llift (llift d)] = DecB l T[d].
Proof. unfold DecB; sy0; rewrite !tyNeg_subst; sy0. Qed.
Lemma DecB_ren (ρ : rsub) l T : (DecB l T)⟨rlift (rlift ρ)⟩ = DecB l T⟨ρ⟩.
Proof. unfold DecB; sy0; rewrite !tyNeg_ren; sy0. Qed.
Lemma DecEq_subst (d : lsub) l T : (DecEq l T)[d] = DecEq l T[d].
Proof. unfold DecEq; push_subst; rewrite DecB_subst; sy0. Qed.
Lemma DecEq_ren (ρ : rsub) l T : (DecEq l T)⟨ρ⟩ = DecEq l T⟨ρ⟩.
Proof. unfold DecEq; push_ren; rewrite DecB_ren; sy0. Qed.
Lemma DecB1_subst (d : lsub) l T u : (DecB1 l T u)[llift d] = DecB1 l T[d] u[d].
Proof. unfold DecB1; sy0; rewrite !tyNeg_subst; sy0. Qed.
Lemma DecB1_ren (ρ : rsub) l T u : (DecB1 l T u)⟨rlift ρ⟩ = DecB1 l T⟨ρ⟩ u⟨ρ⟩.
Proof. unfold DecB1; sy0; rewrite !tyNeg_ren; sy0. Qed.
Lemma decapp_subst (d : lsub) l T dec u v : (decapp l T dec u v)[d] = decapp l T[d] dec[d] u[d] v[d].
Proof. unfold decapp; push_subst; rewrite DecB1_subst; push_subst; rewrite DecB_subst; sy0. Qed.
Lemma decapp_ren (ρ : rsub) l T dec u v : (decapp l T dec u v)⟨ρ⟩ = decapp l T⟨ρ⟩ dec⟨ρ⟩ u⟨ρ⟩ v⟨ρ⟩.
Proof. unfold decapp; push_ren; rewrite DecB1_ren; push_ren; rewrite DecB_ren; sy0. Qed.
Lemma fcase_subst (d : lsub) l T u v r s : (fcase l T u v r s)[d] = fcase l T[d] u[d] v[d] r[d] s[d].
Proof. unfold fcase; push_subst; rewrite !tyNeg_subst; sy0. Qed.
Lemma fcase_ren (ρ : rsub) l T u v r s : (fcase l T u v r s)⟨ρ⟩ = fcase l T⟨ρ⟩ u⟨ρ⟩ v⟨ρ⟩ r⟨ρ⟩ s⟨ρ⟩.
Proof. unfold fcase; push_ren; rewrite !tyNeg_ren; sy0. Qed.
Lemma pinv_subst (d : lsub) l T u v r : (pinv l T u v r)[d] = pinv l T[d] u[d] v[d] r[d]. Proof. unfold pinv; sy0. Qed.
Lemma pinv_ren (ρ : rsub) l T u v r : (pinv l T u v r)⟨ρ⟩ = pinv l T⟨ρ⟩ u⟨ρ⟩ v⟨ρ⟩ r⟨ρ⟩. Proof. unfold pinv; sy0. Qed.
Lemma pcat_subst (d : lsub) l T u v w r s : (pcat l T u v w r s)[d] = pcat l T[d] u[d] v[d] w[d] r[d] s[d].
Proof. unfold pcat; sy0. Qed.
Lemma pcat_ren (ρ : rsub) l T u v w r s : (pcat l T u v w r s)⟨ρ⟩ = pcat l T⟨ρ⟩ u⟨ρ⟩ v⟨ρ⟩ w⟨ρ⟩ r⟨ρ⟩ s⟨ρ⟩.
Proof. unfold pcat; sy0. Qed.
Lemma Fv_subst (d : lsub) l T dec u v r : (Fv l T dec u v r)[d] = Fv l T[d] dec[d] u[d] v[d] r[d].
Proof. unfold Fv; rewrite fcase_subst, decapp_subst; reflexivity. Qed.
Lemma Fv_ren (ρ : rsub) l T dec u v r : (Fv l T dec u v r)⟨ρ⟩ = Fv l T⟨ρ⟩ dec⟨ρ⟩ u⟨ρ⟩ v⟨ρ⟩ r⟨ρ⟩.
Proof. unfold Fv; rewrite fcase_ren, decapp_ren; reflexivity. Qed.
Lemma cinv_subst (d : lsub) l T dec x : (cinv l T dec x)[d] = cinv l T[d] dec[d] x[d].
Proof. unfold cinv; rewrite pinv_subst, Fv_subst; push_subst; reflexivity. Qed.
Lemma cinv_ren (ρ : rsub) l T dec x : (cinv l T dec x)⟨ρ⟩ = cinv l T⟨ρ⟩ dec⟨ρ⟩ x⟨ρ⟩.
Proof. unfold cinv; rewrite pinv_ren, Fv_ren; push_ren; reflexivity. Qed.
Lemma gpath_subst (d : lsub) l T dec x v t : (gpath l T dec x v t)[d] = gpath l T[d] dec[d] x[d] v[d] t[d].
Proof. unfold gpath; rewrite pcat_subst, cinv_subst; reflexivity. Qed.
Lemma gpath_ren (ρ : rsub) l T dec x v t : (gpath l T dec x v t)⟨ρ⟩ = gpath l T⟨ρ⟩ dec⟨ρ⟩ x⟨ρ⟩ v⟨ρ⟩ t⟨ρ⟩.
Proof. unfold gpath; rewrite pcat_ren, cinv_ren; reflexivity. Qed.

Ltac sy_macro := first
  [ rewrite gpath_subst | rewrite gpath_ren | rewrite cinv_subst | rewrite cinv_ren
  | rewrite Fv_subst | rewrite Fv_ren | rewrite fcase_subst | rewrite fcase_ren
  | rewrite decapp_subst | rewrite decapp_ren | rewrite pcat_subst | rewrite pcat_ren
  | rewrite pinv_subst | rewrite pinv_ren | rewrite DecEq_subst | rewrite DecEq_ren
  | rewrite SumI_subst | rewrite SumI_ren | rewrite tyNeg_subst | rewrite tyNeg_ren ].
(** Unfold the one-off definitions (motives and proofs), keep the macros. *)
Ltac sy := repeat progress unfold hedberg, uipT, uip_pt, body, apg, Map, const, Mconst, Mconst_inr, key, Mkey,
  linv, Mlinv;
  repeat first [sy_macro | sy_step]; try reflexivity.

Lemma Mkey_at l T dec x a b : nfty T -> nftm dec -> nftm x ->
  (Mkey l T dec x)[lsingle2 a b] = tyId l (tyId l T x a) b (gpath l T dec x a (Fv l T dec x a b)).
Proof. intros. sy. Qed.

Lemma Mlinv_at l T x a b : nfty T -> nftm x ->
  (Mlinv l T x)[lsingle2 a b] = tyId l (tyId l T a a) (pcat l T a x a (pinv l T x a b) b) (tmRefl l T a).
Proof. intros. sy. Qed.

Section Hedberg.
Context {G : gctx}.

Let Hv : lD <> lV. Proof. discriminate. Qed.

(** *** Contexts and weakening at layer D *)

Lemma ext {Γ A l} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ lD ] ].
Proof. intros Hl HA. apply wfc_ext; [exact (ctx_of_wf_ty eq_refl HA) | exact HA | exact Hl]. Qed.

Lemma wkty {Γ A l T l'} : [ G ; Γ ,, A @ l ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] T @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ lD ] T⟨↑⟩ @ l' ].
Proof. intros. apply wk1_ty_g; assumption. Qed.
Lemma wktm {Γ A l t T l'} : [ G ; Γ ,, A @ l ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] t : T @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ lD ] t⟨↑⟩ : T⟨↑⟩ @ l' ].
Proof. intros. apply wk1_tm_g; assumption. Qed.
Lemma wk2ty {Γ A B l1 l2 T l} : [ G ; Γ ,, A @ l1 ,, B @ l2 ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ,, A @ l1 ,, B @ l2 ⊢[ lD ] T⟨↑⟩⟨↑⟩ @ l ].
Proof. intros H HT. apply (wkty H), (wkty (ctx_of_ext H)), HT. Qed.
Lemma wk2tm {Γ A B l1 l2 t T l} : [ G ; Γ ,, A @ l1 ,, B @ l2 ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] t : T @ l ] ->
  [ G ; Γ ,, A @ l1 ,, B @ l2 ⊢[ lD ] t⟨↑⟩⟨↑⟩ : T⟨↑⟩⟨↑⟩ @ l ].
Proof. intros H Ht. apply (wktm H), (wktm (ctx_of_ext H)), Ht. Qed.

Lemma var0 {Γ A l} : [ G ; Γ ,, A @ l ⊢[ lD ] ] -> [ G ; Γ ,, A @ l ⊢[ lD ] var 0 : A⟨↑⟩ @ l ].
Proof. intros H. exact (wf_var _ lD _ _ _ _ H (in_here _ _ _)). Qed.
Lemma var1 {Γ A B l l'} : [ G ; Γ ,, A @ l ,, B @ l' ⊢[ lD ] ] ->
  [ G ; Γ ,, A @ l ,, B @ l' ⊢[ lD ] var 1 : A⟨↑⟩⟨↑⟩ @ l ].
Proof. intros H. exact (wf_var _ lD _ _ _ _ H (in_there _ _ _ _ _ _ (in_here _ _ _))). Qed.

(** [J]'s motive context over [a]. *)
Lemma jctx {Γ l T a} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] a : T @ l ] ->
  [ G ; Γ ,, T @ l ⊢[ lD ] tyId l T⟨↑⟩ a⟨↑⟩ (var 0) @ l ] /\
  [ G ; Γ ,, T @ l ,, tyId l T⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ lD ] ].
Proof.
  intros Hl HT Ha. pose proof (ext Hl HT) as H1.
  assert (HI : [ G ; Γ ,, T @ l ⊢[ lD ] tyId l T⟨↑⟩ a⟨↑⟩ (var 0) @ l ])
    by (apply wft_id; [exact Hv | exact Hl | exact (wkty H1 HT) | exact (wktm H1 Ha) | exact (var0 H1)]).
  split; [exact HI | exact (ext Hl HI)].
Qed.

(** In [J]'s motive context: [var 1 : T] and [var 0 : Id(T; a; var 1)]. *)
Lemma jvar0 {Γ l T a} : [ G ; Γ ,, T @ l ,, tyId l T⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ lD ] ] ->
  [ G ; Γ ,, T @ l ,, tyId l T⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ lD ] var 0 : tyId l T⟨↑⟩⟨↑⟩ a⟨↑⟩⟨↑⟩ (var 1) @ l ].
Proof. intros H. eapply wf_tm_retype; [exact (var0 H) | sy]. Qed.

(** *** Inverse and composition *)

Lemma pinv_wf {Γ l T u v r} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] r : tyId l T u v @ l ] ->
  [ G ; Γ ⊢[ lD ] pinv l T u v r : tyId l T v u @ l ].
Proof.
  intros Hl HT Hu Hv' Hr. destruct (jctx Hl HT Hu) as [HI HM].
  eapply wf_tm_retype; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl HT Hu HI _ _ Hv' Hr) | sy].
  - apply wft_id; [exact Hv | exact Hl | exact (wk2ty HM HT) | exact (var1 HM) | exact (wk2tm HM Hu)].
  - eapply wf_tm_retype; [apply wf_idrefl; [exact Hv | exact Hl | exact HT | exact Hu] | sy].
Qed.

Lemma pcat_wf {Γ l T u v w r s} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] w : T @ l ] ->
  [ G ; Γ ⊢[ lD ] r : tyId l T u v @ l ] -> [ G ; Γ ⊢[ lD ] s : tyId l T v w @ l ] ->
  [ G ; Γ ⊢[ lD ] pcat l T u v w r s : tyId l T u w @ l ].
Proof.
  intros Hl HT Hu Hv' Hw Hr Hs. destruct (jctx Hl HT Hv') as [HI HM].
  eapply wf_tm_retype; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl HT Hv' HI _ _ Hw Hs) | sy].
  - apply wft_id; [exact Hv | exact Hl | exact (wk2ty HM HT) | exact (wk2tm HM Hu) | exact (var1 HM)].
  - eapply wf_tm_retype; [exact Hr | sy].
Qed.

(** [refl⁻¹ ≡ refl] and [r · refl ≡ r], by [J]-β. *)
Lemma pinv_refl {Γ l T u} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] u : T @ l ] ->
  [ G ; Γ ⊢[ lD ] pinv l T u u (tmRefl l T u) ≅ tmRefl l T u : tyId l T u u @ l ].
Proof.
  intros Hl HT Hu. destruct (jctx Hl HT Hu) as [HI HM].
  eapply eq_tm_retype; [refine (eqtm_J_beta _ _ _ _ _ _ _ _ _ compt_D Hl Hl HT Hu HI _ _) | sy].
  - apply wft_id; [exact Hv | exact Hl | exact (wk2ty HM HT) | exact (var1 HM) | exact (wk2tm HM Hu)].
  - eapply wf_tm_retype; [apply wf_idrefl; [exact Hv | exact Hl | exact HT | exact Hu] | sy].
Qed.

Lemma pcat_refl {Γ l T u v r} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] r : tyId l T u v @ l ] ->
  [ G ; Γ ⊢[ lD ] pcat l T u v v r (tmRefl l T v) ≅ r : tyId l T u v @ l ].
Proof.
  intros Hl HT Hu Hv' Hr. destruct (jctx Hl HT Hv') as [HI HM].
  eapply eq_tm_retype; [refine (eqtm_J_beta _ _ _ _ _ _ _ _ _ compt_D Hl Hl HT Hv' HI _ _) | sy].
  - apply wft_id; [exact Hv | exact Hl | exact (wk2ty HM HT) | exact (wk2tm HM Hu) | exact (var1 HM)].
  - eapply wf_tm_retype; [exact Hr | sy].
Qed.

(** *** [s⁻¹ · s = refl] *)

Lemma linv_wf {Γ l T x w s} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] x : T @ l ] -> [ G ; Γ ⊢[ lD ] w : T @ l ] -> [ G ; Γ ⊢[ lD ] s : tyId l T x w @ l ] ->
  [ G ; Γ ⊢[ lD ] linv l T x w s : tyId l (tyId l T w w) (pcat l T w x w (pinv l T x w s) s) (tmRefl l T w) @ l ].
Proof.
  intros Hl HT Hx Hw Hs. destruct (jctx Hl HT Hx) as [HI HM].
  pose proof (wk2ty HM HT) as HT2. pose proof (var1 HM) as Hy. pose proof (wk2tm HM Hx) as Hx2.
  pose proof (jvar0 HM) as Hp.
  eapply wf_tm_retype; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl HT Hx HI _ _ Hw Hs) | apply Mlinv_at; nf_tac].
  - apply wft_id; [exact Hv | exact Hl | apply wft_id; [exact Hv | exact Hl | exact HT2 | exact Hy | exact Hy] | |].
    + apply (pcat_wf Hl HT2 Hy Hx2 Hy); [apply (pinv_wf Hl HT2 Hx2 Hy Hp) | exact Hp].
    + apply wf_idrefl; [exact Hv | exact Hl | exact HT2 | exact Hy].
  - rewrite Mlinv_at by nf_tac.
    pose proof (wf_idrefl _ _ _ _ _ _ Hv Hl HT Hx) as Hr.
    pose proof (wft_id _ _ _ _ _ _ _ Hv Hl HT Hx Hx) as HIxx.
    eapply wf_conv; [exact (wf_idrefl _ _ _ _ _ _ Hv Hl HIxx Hr) |].
    apply eqty_id; [exact Hv | exact (lequiv_refl _ _ Hl) | exact HIxx | exact (eqty_refl _ _ _ _ _ HIxx) | | exact (eqtm_refl _ _ _ _ _ _ Hr)].
    exact (eqtm_trans _ _ _ _ _ _ _ _ (pcat_refl Hl HT Hx Hx (pinv_wf Hl HT Hx Hx Hr)) (pinv_refl Hl HT Hx)).
Qed.

(** *** Levels: [l ⊔ l ≈ l] *)

Lemma lc_ty {Γ T l} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ lmax l l ] -> [ G ; Γ ⊢[ lD ] T @ l ].
Proof. intros Hl H. exact (wft_lconv _ _ _ _ _ _ H (lequiv_sym _ _ _ (lmax_idem _ _ Hl))). Qed.
Lemma lc_tm {Γ t T l} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] t : T @ lmax l l ] -> [ G ; Γ ⊢[ lD ] t : T @ l ].
Proof. intros Hl H. exact (wf_lconv _ _ _ _ _ _ _ H (lequiv_sym _ _ _ (lmax_idem _ _ Hl))). Qed.
Lemma cl_tm {Γ t T l} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] t : T @ l ] -> [ G ; Γ ⊢[ lD ] t : T @ lmax l l ].
Proof. intros Hl H. exact (wf_lconv _ _ _ _ _ _ _ H (lmax_idem _ _ Hl)). Qed.

(** *** Decidable equality *)

Lemma id_wf {Γ l T u v} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] tyId l T u v @ l ].
Proof. intros. apply wft_id; assumption. Qed.

Lemma neg_wf {Γ l A} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] A @ l ] -> [ G ; Γ ⊢[ lD ] tyNeg l A @ l ].
Proof. intros Hl HA. apply (lc_ty Hl), wft_pi; [exact Hv | exact Hl | exact Hl | exact HA | apply wft_empty; [exact Hv | exact (ext Hl HA) | exact Hl]]. Qed.

Lemma sumI_wf {Γ l T u v} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] SumI l T u v @ lmax l l ].
Proof. intros Hl HT Hu Hv'. pose proof (id_wf Hl HT Hu Hv') as HI. apply wft_sum; [exact Hv | exact Hl | exact Hl | exact HI | exact (neg_wf Hl HI)]. Qed.

Lemma decpi_wf {Γ l T} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ,, T @ l ⊢[ lD ] tyPi l l T⟨↑⟩ (DecB l T) @ l ].
Proof.
  intros Hl HT. pose proof (ext Hl HT) as H1. pose proof (wkty H1 HT) as HT1. pose proof (ext Hl HT1) as H2.
  apply (lc_ty Hl), wft_pi; [exact Hv | exact Hl | exact Hl | exact HT1 |].
  apply (lc_ty Hl). exact (sumI_wf Hl (wk2ty H2 HT) (var1 H2) (var0 H2)).
Qed.

Lemma deceq_wf {Γ l T} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] DecEq l T @ l ].
Proof. intros Hl HT. apply (lc_ty Hl), wft_pi; [exact Hv | exact Hl | exact Hl | exact HT | exact (decpi_wf Hl HT)]. Qed.

Lemma decapp_wf {Γ l T dec u v} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] -> [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] ->
  [ G ; Γ ⊢[ lD ] decapp l T dec u v : SumI l T u v @ lmax l l ].
Proof.
  intros Hl HT Hdec Hu Hv'. pose proof (ext Hl HT) as H1.
  apply (cl_tm Hl). eapply wf_tm_retype; [refine (wf_app _ _ _ _ _ _ _ _ _ Hv Hl Hl HT _ _ Hv') | unfold DecB1, SumI; sy].
  - apply (lc_ty Hl). exact (sumI_wf Hl (wkty H1 HT) (wktm H1 Hu) (var0 H1)).
  - apply (cl_tm Hl). eapply wf_tm_retype;
      [exact (wf_app _ _ _ _ _ _ _ _ _ Hv Hl Hl HT (decpi_wf Hl HT) (cl_tm Hl Hdec) Hu) | unfold DecB, DecB1; sy].
Qed.

(** *** The collapse *)

Lemma fcase_prem {Γ l T u v r} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] r : tyId l T u v @ l ] ->
  let I := tyId l T u v in let N := tyNeg l I in
  [ G ; Γ ,, tySum l l I N @ lmax l l ⊢[ lD ] I⟨↑⟩ @ l ] /\
  [ G ; Γ ,, I @ l ⊢[ lD ] var 0 : I⟨↑⟩⟨rlift ↑⟩[lsingle (tmInl l l I⟨↑⟩ N⟨↑⟩ (var 0))] @ l ] /\
  [ G ; Γ ,, N @ l ⊢[ lD ] elimEmpty l l I⟨↑⟩⟨↑⟩ (app (var 0) l l I⟨↑⟩ (tyEmpty l) r⟨↑⟩)
      : I⟨↑⟩⟨rlift ↑⟩[lsingle (tmInr l l I⟨↑⟩ N⟨↑⟩ (var 0))] @ l ].
Proof.
  intros Hl HT Hu Hv' Hr I N. pose proof (id_wf Hl HT Hu Hv') as HI. pose proof (neg_wf Hl HI) as HN.
  pose proof (ext (l := lmax l l) (conj Hl Hl) (sumI_wf Hl HT Hu Hv')) as HS.
  pose proof (ext Hl HI) as HΓI. pose proof (ext Hl HN) as HΓN.
  pose proof (wkty HΓN HI) as HI1.
  split; [exact (wkty HS HI) | split].
  - eapply wf_tm_retype; [exact (var0 HΓI) | unfold I, N; sy].
  - eapply wf_tm_retype; [refine (wf_elimEmpty _ _ _ _ _ _ _ Hv Hl Hl _ _) | unfold I, N; sy].
    + exact (wk2ty (ext Hl (wft_empty _ _ _ _ Hv HΓN Hl)) HI).
    + eapply wf_tm_retype; [refine (wf_app _ _ _ _ _ _ _ _ _ Hv Hl Hl HI1 (wft_empty _ _ _ _ Hv (ext Hl HI1) Hl) _ (wktm HΓN Hr)) | reflexivity].
      apply (cl_tm Hl). eapply wf_tm_retype; [exact (var0 HΓN) | unfold I, N; sy].
Qed.

Lemma fcase_wf {Γ l T u v r s} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] r : tyId l T u v @ l ] ->
  [ G ; Γ ⊢[ lD ] s : SumI l T u v @ lmax l l ] ->
  [ G ; Γ ⊢[ lD ] fcase l T u v r s : tyId l T u v @ l ].
Proof.
  intros Hl HT Hu Hv' Hr Hs. pose proof (id_wf Hl HT Hu Hv') as HI.
  destruct (fcase_prem Hl HT Hu Hv' Hr) as (HM & H1 & H2).
  eapply wf_tm_retype; [exact (wf_case _ _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl Hl HI (neg_wf Hl HI) HM H1 H2 Hs) | sy].
Qed.

(** At [inl e], the collapse is [e]: [case]-β. *)
Lemma fcase_inl {Γ l T u v r e} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] r : tyId l T u v @ l ] ->
  [ G ; Γ ⊢[ lD ] e : tyId l T u v @ l ] ->
  [ G ; Γ ⊢[ lD ] fcase l T u v r (tmInl l l (tyId l T u v) (tyNeg l (tyId l T u v)) e) ≅ e : tyId l T u v @ l ].
Proof.
  intros Hl HT Hu Hv' Hr He. pose proof (id_wf Hl HT Hu Hv') as HI.
  destruct (fcase_prem Hl HT Hu Hv' Hr) as (HM & H1 & H2).
  eapply eq_tm_retype; [exact (eqtm_case_inl _ _ _ _ _ _ _ _ _ _ _ _ compt_D Hl Hl Hl HI (neg_wf Hl HI) HM H1 H2 He) | sy].
Qed.

Lemma Fv_wf {Γ l T dec u v r} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] ->
  [ G ; Γ ⊢[ lD ] u : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] r : tyId l T u v @ l ] ->
  [ G ; Γ ⊢[ lD ] Fv l T dec u v r : tyId l T u v @ l ].
Proof. intros Hl HT Hdec Hu Hv' Hr. exact (fcase_wf Hl HT Hu Hv' Hr (decapp_wf Hl HT Hdec Hu Hv')). Qed.

Lemma gpath_wf {Γ l T dec x v t} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] ->
  [ G ; Γ ⊢[ lD ] x : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] t : tyId l T x v @ l ] ->
  [ G ; Γ ⊢[ lD ] gpath l T dec x v t : tyId l T x v @ l ].
Proof.
  intros Hl HT Hdec Hx Hv' Ht. pose proof (wf_idrefl _ _ _ _ _ _ Hv Hl HT Hx) as Hr.
  exact (pcat_wf Hl HT Hx Hx Hv' (pinv_wf Hl HT Hx Hx (Fv_wf Hl HT Hdec Hx Hx Hr)) Ht).
Qed.

(** *** [r = g(f(r))] *)

(** The leaves of [J]'s motive context, weakened. *)
Lemma jleaves {Γ l T dec a A} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] ->
  [ G ; Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ lD ] ] ->
  [ G ; Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ lD ] T⟨↑⟩⟨↑⟩ @ l ] /\
  [ G ; Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ lD ] dec⟨↑⟩⟨↑⟩ : DecEq l T⟨↑⟩⟨↑⟩ @ l ].
Proof. intros Hl HT Hdec HM. split; [exact (wk2ty HM HT) | eapply wf_tm_retype; [exact (wk2tm HM Hdec) | sy]]. Qed.

Lemma key_wf {Γ l T dec x v r} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] ->
  [ G ; Γ ⊢[ lD ] x : T @ l ] -> [ G ; Γ ⊢[ lD ] v : T @ l ] -> [ G ; Γ ⊢[ lD ] r : tyId l T x v @ l ] ->
  [ G ; Γ ⊢[ lD ] key l T dec x v r : tyId l (tyId l T x v) r (gpath l T dec x v (Fv l T dec x v r)) @ l ].
Proof.
  intros Hl HT Hdec Hx Hv' Hr. destruct (jctx Hl HT Hx) as [HI HM].
  destruct (jleaves (a := x) Hl HT Hdec HM) as [HT2 Hdec2].
  pose proof (wk2tm HM Hx) as Hx2. pose proof (var1 HM) as Hy. pose proof (jvar0 HM) as Hp.
  eapply wf_tm_retype; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl HT Hx HI _ _ Hv' Hr) | apply Mkey_at; nf_tac].
  - apply wft_id; [exact Hv | exact Hl | exact (id_wf Hl HT2 Hx2 Hy) | exact Hp |].
    exact (gpath_wf Hl HT2 Hdec2 Hx2 Hy (Fv_wf Hl HT2 Hdec2 Hx2 Hy Hp)).
  - rewrite Mkey_at by nf_tac.
    pose proof (wf_idrefl _ _ _ _ _ _ Hv Hl HT Hx) as Hrx.
    pose proof (Fv_wf Hl HT Hdec Hx Hx Hrx) as Hc.
    exact (pinv_wf Hl (id_wf Hl HT Hx Hx) (gpath_wf Hl HT Hdec Hx Hx Hc) Hrx (linv_wf Hl HT Hx Hx Hc)).
Qed.

(** *** [f(p) = f(q)] *)

Lemma const_wf {Γ l T dec x y p q} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] ->
  [ G ; Γ ⊢[ lD ] x : T @ l ] -> [ G ; Γ ⊢[ lD ] y : T @ l ] ->
  [ G ; Γ ⊢[ lD ] p : tyId l T x y @ l ] -> [ G ; Γ ⊢[ lD ] q : tyId l T x y @ l ] ->
  [ G ; Γ ⊢[ lD ] const l T dec x y p q : tyId l (tyId l T x y) (Fv l T dec x y p) (Fv l T dec x y q) @ l ].
Proof.
  intros Hl HT Hdec Hx Hy Hp Hq. pose proof (id_wf Hl HT Hx Hy) as HI. pose proof (neg_wf Hl HI) as HN.
  (* the leaves under one binder [B], at the pushed spelling *)
  assert (Lv : forall B k, [ G ; Γ ,, B @ k ⊢[ lD ] ] ->
    [ G ; Γ ,, B @ k ⊢[ lD ] T⟨↑⟩ @ l ] /\ [ G ; Γ ,, B @ k ⊢[ lD ] x⟨↑⟩ : T⟨↑⟩ @ l ] /\
    [ G ; Γ ,, B @ k ⊢[ lD ] y⟨↑⟩ : T⟨↑⟩ @ l ] /\
    [ G ; Γ ,, B @ k ⊢[ lD ] p⟨↑⟩ : tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ @ l ] /\
    [ G ; Γ ,, B @ k ⊢[ lD ] q⟨↑⟩ : tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ @ l ] /\
    [ G ; Γ ,, B @ k ⊢[ lD ] tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ @ l ]).
  { intros B k H. pose proof (wkty H HT) as HT1. pose proof (wktm H Hx) as Hx1. pose proof (wktm H Hy) as Hy1.
    repeat split; try assumption; [eapply wf_tm_retype; [exact (wktm H Hp) | sy] | eapply wf_tm_retype; [exact (wktm H Hq) | sy] | exact (id_wf Hl HT1 Hx1 Hy1)]. }
  pose proof (ext (l := lmax l l) (conj Hl Hl) (sumI_wf Hl HT Hx Hy)) as HS.
  pose proof (ext Hl HI) as HΓI. pose proof (ext Hl HN) as HΓN.
  eapply wf_tm_retype; [refine (wf_case _ _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl Hl HI HN _ _ _ (decapp_wf Hl HT Hdec Hx Hy)) | unfold Fv; sy].
  - destruct (Lv _ _ HS) as (HT1 & Hx1 & Hy1 & Hp1 & Hq1 & HI1).
    assert (Hz : [ G ; Γ ,, SumI l T x y @ lmax l l ⊢[ lD ] var 0 : SumI l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ @ lmax l l ])
      by (eapply wf_tm_retype; [exact (var0 HS) | sy]).
    apply wft_id; [exact Hv | exact Hl | exact HI1 | exact (fcase_wf Hl HT1 Hx1 Hy1 Hp1 Hz) | exact (fcase_wf Hl HT1 Hx1 Hy1 Hq1 Hz)].
  - destruct (Lv _ _ HΓI) as (HT1 & Hx1 & Hy1 & Hp1 & Hq1 & HI1).
    assert (He : [ G ; Γ ,, tyId l T x y @ l ⊢[ lD ] var 0 : tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ @ l ])
      by (eapply wf_tm_retype; [exact (var0 HΓI) | sy]).
    set (I1 := tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩).
    eapply (wf_tm_retype _ _ _ _ _ (tyId l I1 (fcase l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ p⟨↑⟩ (tmInl l l I1 (tyNeg l I1) (var 0)))
                                      (fcase l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ q⟨↑⟩ (tmInl l l I1 (tyNeg l I1) (var 0))))); [| unfold I1; sy].
    eapply wf_conv; [exact (wf_idrefl _ _ _ _ _ _ Hv Hl HI1 He) |].
    apply eqty_id; [exact Hv | exact (lequiv_refl _ _ Hl) | exact HI1 | exact (eqty_refl _ _ _ _ _ HI1)
                   | exact (fcase_inl Hl HT1 Hx1 Hy1 Hp1 He) | exact (fcase_inl Hl HT1 Hx1 Hy1 Hq1 He)].
  - destruct (Lv _ _ HΓN) as (HT1 & Hx1 & Hy1 & Hp1 & Hq1 & HI1).
    pose proof (neg_wf Hl HI1) as HN1.
    assert (Hz : [ G ; Γ ,, tyNeg l (tyId l T x y) @ l ⊢[ lD ] tmInr l l (tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩) (tyNeg l (tyId l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩)) (var 0)
                   : SumI l T⟨↑⟩ x⟨↑⟩ y⟨↑⟩ @ lmax l l ]).
    { apply wf_inr; [exact Hv | exact Hl | exact Hl | exact HI1 | exact HN1 |]. eapply wf_tm_retype; [exact (var0 HΓN) | sy]. }
    assert (HMi : [ G ; Γ ,, tyNeg l (tyId l T x y) @ l ⊢[ lD ] Mconst_inr l T x y p q @ l ]).
    { apply wft_id; [exact Hv | exact Hl | exact HI1 | exact (fcase_wf Hl HT1 Hx1 Hy1 Hp1 Hz) | exact (fcase_wf Hl HT1 Hx1 Hy1 Hq1 Hz)]. }
    eapply wf_tm_retype; [refine (wf_elimEmpty _ _ _ _ _ _ _ Hv Hl Hl _ _) | rewrite shift_single_ty by exact (wf_ty_nf HMi); sy].
    + exact (wkty (ext Hl (wft_empty _ _ _ _ Hv HΓN Hl)) HMi).
    + eapply wf_tm_retype; [refine (wf_app _ _ _ _ _ _ _ _ _ Hv Hl Hl HI1 (wft_empty _ _ _ _ Hv (ext Hl HI1) Hl) _ Hp1) | reflexivity].
      apply (cl_tm Hl). eapply wf_tm_retype; [exact (var0 HΓN) | sy].
Qed.

(** *** [ap g] *)

Lemma apg_wf {Γ l T dec x y p q e} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] ->
  [ G ; Γ ⊢[ lD ] x : T @ l ] -> [ G ; Γ ⊢[ lD ] y : T @ l ] ->
  [ G ; Γ ⊢[ lD ] p : tyId l T x y @ l ] -> [ G ; Γ ⊢[ lD ] q : tyId l T x y @ l ] ->
  [ G ; Γ ⊢[ lD ] e : tyId l (tyId l T x y) (Fv l T dec x y p) (Fv l T dec x y q) @ l ] ->
  [ G ; Γ ⊢[ lD ] apg l T dec x y p q e
      : tyId l (tyId l T x y) (gpath l T dec x y (Fv l T dec x y p)) (gpath l T dec x y (Fv l T dec x y q)) @ l ].
Proof.
  intros Hl HT Hdec Hx Hy Hp Hq He. pose proof (id_wf Hl HT Hx Hy) as HI.
  pose proof (Fv_wf Hl HT Hdec Hx Hy Hp) as HFp. pose proof (Fv_wf Hl HT Hdec Hx Hy Hq) as HFq.
  destruct (jctx Hl HI HFp) as [HJ HM].
  destruct (jleaves (a := Fv l T dec x y p) Hl HT Hdec HM) as [HT2 Hdec2].
  pose proof (wk2tm HM Hx) as Hx2. pose proof (wk2tm HM Hy) as Hy2.
  assert (Hp2 : [ G ; _ ⊢[ lD ] p⟨↑⟩⟨↑⟩ : tyId l T⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ y⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wf_tm_retype; [exact (wk2tm HM Hp) | sy]).
  assert (Ht : [ G ; _ ⊢[ lD ] var 1 : tyId l T⟨↑⟩⟨↑⟩ x⟨↑⟩⟨↑⟩ y⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wf_tm_retype; [exact (var1 HM) | sy]).
  eapply wf_tm_retype; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl HI HFp HJ _ _ HFq He) | sy].
  - apply wft_id; [exact Hv | exact Hl | exact (id_wf Hl HT2 Hx2 Hy2) | |].
    + exact (gpath_wf Hl HT2 Hdec2 Hx2 Hy2 (Fv_wf Hl HT2 Hdec2 Hx2 Hy2 Hp2)).
    + exact (gpath_wf Hl HT2 Hdec2 Hx2 Hy2 Ht).
  - eapply wf_tm_retype; [apply wf_idrefl; [exact Hv | exact Hl | exact HI | exact (gpath_wf Hl HT Hdec Hx Hy HFp)] | sy].
Qed.

(** *** [p = q] *)

Lemma body_wf {Γ l T dec x y p q} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] ->
  [ G ; Γ ⊢[ lD ] x : T @ l ] -> [ G ; Γ ⊢[ lD ] y : T @ l ] ->
  [ G ; Γ ⊢[ lD ] p : tyId l T x y @ l ] -> [ G ; Γ ⊢[ lD ] q : tyId l T x y @ l ] ->
  [ G ; Γ ⊢[ lD ] body l T dec x y p q : tyId l (tyId l T x y) p q @ l ].
Proof.
  intros Hl HT Hdec Hx Hy Hp Hq. pose proof (id_wf Hl HT Hx Hy) as HI.
  pose proof (gpath_wf Hl HT Hdec Hx Hy (Fv_wf Hl HT Hdec Hx Hy Hp)) as Hgp.
  pose proof (gpath_wf Hl HT Hdec Hx Hy (Fv_wf Hl HT Hdec Hx Hy Hq)) as Hgq.
  pose proof (key_wf Hl HT Hdec Hx Hy Hp) as Kp. pose proof (key_wf Hl HT Hdec Hx Hy Hq) as Kq.
  pose proof (apg_wf Hl HT Hdec Hx Hy Hp Hq (const_wf Hl HT Hdec Hx Hy Hp Hq)) as Ha.
  exact (pcat_wf Hl HI Hp Hgq Hq (pcat_wf Hl HI Hp Hgp Hgq Kp Ha) (pinv_wf Hl HI Hq Hgq Kq)).
Qed.

(** ** Hedberg's theorem *)

Theorem hedberg_wf {Γ l T dec} : lwf (gL G) l -> [ G ; Γ ⊢[ lD ] T @ l ] -> [ G ; Γ ⊢[ lD ] dec : DecEq l T @ l ] ->
  [ G ; Γ ⊢[ lD ] hedberg l T dec : uipT l T @ uipL l ].
Proof.
  intros Hl HT Hdec.
  pose proof (ext Hl HT) as H1. pose proof (wkty H1 HT) as HT1. pose proof (ext Hl HT1) as H2.
  pose proof (wkty H2 HT1) as HT2.
  assert (HI0 : [ G ; Γ ,, T @ l ,, T⟨↑⟩ @ l ⊢[ lD ] tyId l T⟨↑⟩⟨↑⟩ (var 1) (var 0) @ l ])
    by exact (id_wf Hl HT2 (var1 H2) (var0 H2)).
  pose proof (ext Hl HI0) as H3. pose proof (wkty H3 HI0) as HI0'. pose proof (ext Hl HI0') as H4.
  pose proof (wkty H3 HT2) as HT3. pose proof (wkty H4 HT3) as HT4.
  assert (Hdec4 : [ G ; _ ⊢[ lD ] dec⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ : DecEq l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wf_tm_retype; [exact (wktm H4 (wktm H3 (wktm H2 (wktm H1 Hdec)))) | sy]).
  pose proof (wf_var _ lD _ _ _ _ H4 (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_here _ _ _))))) as Hx.
  pose proof (wf_var _ lD _ _ _ _ H4 (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_here _ _ _)))) as Hy.
  assert (Hp : [ G ; _ ⊢[ lD ] var 1 : tyId l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 3) (var 2) @ l ])
    by (eapply wf_tm_retype; [exact (var1 H4) | sy]).
  assert (Hq : [ G ; _ ⊢[ lD ] var 0 : tyId l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 3) (var 2) @ l ])
    by (eapply wf_tm_retype; [exact (var0 H4) | sy]).
  pose proof (body_wf Hl HT4 Hdec4 Hx Hy Hp Hq) as Hb.
  unfold hedberg, uipT, uipL, uip_pt.
  apply wf_lam; [exact Hv | exact Hl | exact (conj Hl (conj Hl (conj Hl Hl))) | exact HT |].
  apply wf_lam; [exact Hv | exact Hl | exact (conj Hl (conj Hl Hl)) | exact HT1 |].
  apply wf_lam; [exact Hv | exact Hl | exact (conj Hl Hl) | exact HI0 |].
  apply wf_lam; [exact Hv | exact Hl | exact Hl | exact HI0' |].
  eapply wf_tm_retype; [exact Hb | sy].
Qed.

(** *** The internal statement *)

Theorem hedbergU_wf {Γ l} : [ G ; Γ ⊢[ lD ] ] -> lwf (gL G) l ->
  [ G ; Γ ⊢[ lD ] hedbergU l : HedbergT l @ lmax (lsuc l) (lmax l (uipL l)) ].
Proof.
  intros HΓ Hl. pose proof (wft_U _ _ _ _ Hv HΓ Hl) as HU. pose proof (ext (l := lsuc l) Hl HU) as H1.
  assert (HEl : [ G ; Γ ,, tyU l @ lsuc l ⊢[ lD ] tyEl l (var 0) @ l ]) by exact (wft_El _ _ _ _ _ Hv Hl (var0 H1)).
  pose proof (deceq_wf Hl HEl) as HD. pose proof (ext Hl HD) as H2.
  assert (HEl1 : [ G ; _ ⊢[ lD ] tyEl l (var 1) @ l ]) by exact (wft_El _ _ _ _ _ Hv Hl (var1 H2)).
  assert (Hd : [ G ; _ ⊢[ lD ] var 0 : DecEq l (tyEl l (var 1)) @ l ]) by (eapply wf_tm_retype; [exact (var0 H2) | sy]).
  assert (HL : lwf (gL G) (uipL l)) by (repeat split; exact Hl).
  unfold hedbergU, HedbergT.
  apply wf_lam; [exact Hv | exact Hl | exact (conj Hl HL) | exact HU |].
  apply wf_lam; [exact Hv | exact Hl | exact HL | exact HD |].
  exact (hedberg_wf Hl HEl1 Hd).
Qed.

(** *** [Bool] *)

Section Bool.
Context {l : lvl} (Hl : lwf (gL G) l).

Lemma u_wf {Δ} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] tyUnit l @ l ].
Proof. intros H. exact (wft_unit _ _ _ _ Hv H Hl). Qed.
Lemma b_wf {Δ} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] tyBool l @ l ].
Proof. intros H. apply (lc_ty Hl), wft_sum; [exact Hv | exact Hl | exact Hl | exact (u_wf H) | exact (u_wf H)]. Qed.
Lemma binl_wf {Δ e} : [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] -> [ G ; Δ ⊢[ lD ] binl l e : tyBool l @ l ].
Proof.
  intros He. pose proof (ctx_of_wf_tm eq_refl He) as H.
  apply (lc_tm Hl), wf_inl; [exact Hv | exact Hl | exact Hl | exact (u_wf H) | exact (u_wf H) | exact He].
Qed.
Lemma binr_wf {Δ e} : [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] -> [ G ; Δ ⊢[ lD ] binr l e : tyBool l @ l ].
Proof.
  intros He. pose proof (ctx_of_wf_tm eq_refl He) as H.
  apply (lc_tm Hl), wf_inr; [exact Hv | exact Hl | exact Hl | exact (u_wf H) | exact (u_wf H) | exact He].
Qed.

(** [Disc] is a type, and decodes at either injection. *)
Lemma disc_prem {Δ c1 c2} : [ G ; Δ ⊢[ lD ] ] -> (c1 = tmUnit l \/ c1 = tmEmpty l) -> (c2 = tmUnit l \/ c2 = tmEmpty l) ->
  [ G ; Δ ,, tySum l l (tyUnit l) (tyUnit l) @ lmax l l ⊢[ lD ] tyU l @ lsuc l ] /\
  [ G ; Δ ,, tyUnit l @ l ⊢[ lD ] c1 : (tyU l)⟨rlift ↑⟩[lsingle (tmInl l l (tyUnit l)⟨↑⟩ (tyUnit l)⟨↑⟩ (var 0))] @ lsuc l ] /\
  [ G ; Δ ,, tyUnit l @ l ⊢[ lD ] c2 : (tyU l)⟨rlift ↑⟩[lsingle (tmInr l l (tyUnit l)⟨↑⟩ (tyUnit l)⟨↑⟩ (var 0))] @ lsuc l ].
Proof.
  intros H E1 E2. pose proof (ext (l := lmax l l) (conj Hl Hl) (wft_sum _ _ _ _ _ _ _ Hv Hl Hl (u_wf H) (u_wf H))) as HS.
  pose proof (ext Hl (u_wf H)) as HU.
  split; [exact (wft_U _ _ _ _ Hv HS Hl) | split].
  - destruct E1 as [-> | ->]; [exact (wf_code_unit _ _ _ _ Hv HU Hl) | exact (wf_code_empty _ _ _ _ Hv HU Hl)].
  - destruct E2 as [-> | ->]; [exact (wf_code_unit _ _ _ _ Hv HU Hl) | exact (wf_code_empty _ _ _ _ Hv HU Hl)].
Qed.

Lemma disc_wf {Δ c1 c2 s} : (c1 = tmUnit l \/ c1 = tmEmpty l) -> (c2 = tmUnit l \/ c2 = tmEmpty l) ->
  [ G ; Δ ⊢[ lD ] s : tyBool l @ l ] -> [ G ; Δ ⊢[ lD ] Disc l c1 c2 s @ l ].
Proof.
  intros E1 E2 Hs. pose proof (ctx_of_wf_tm eq_refl Hs) as H. destruct (disc_prem H E1 E2) as (HM & H1 & H2).
  apply wft_El; [exact Hv | exact Hl |].
  exact (wf_case _ _ _ _ _ (lsuc l) _ _ _ _ _ _ Hv Hl Hl Hl (u_wf H) (u_wf H) HM H1 H2 (cl_tm Hl Hs)).
Qed.

Lemma disc_inl {Δ c1 c2 e} : (c1 = tmUnit l \/ c1 = tmEmpty l) -> (c2 = tmUnit l \/ c2 = tmEmpty l) ->
  [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] -> [ G ; Δ ⊢[ lD ] Disc l c1 c2 (binl l e) ≅ tyEl l c1 @ l ].
Proof.
  intros E1 E2 He. pose proof (ctx_of_wf_tm eq_refl He) as H.
  destruct (disc_prem H E1 E2) as (HM & H1 & H2). destruct E1 as [-> | ->], E2 as [-> | ->].
  all: apply eqty_El; [exact Hv | exact (lequiv_refl _ _ Hl) |].
  all: exact (eqtm_case_inl _ _ _ _ _ (lsuc l) _ _ _ _ _ _ compt_D Hl Hl Hl (u_wf H) (u_wf H) HM H1 H2 He).
Qed.
Lemma disc_inr {Δ c1 c2 e} : (c1 = tmUnit l \/ c1 = tmEmpty l) -> (c2 = tmUnit l \/ c2 = tmEmpty l) ->
  [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] -> [ G ; Δ ⊢[ lD ] Disc l c1 c2 (binr l e) ≅ tyEl l c2 @ l ].
Proof.
  intros E1 E2 He. pose proof (ctx_of_wf_tm eq_refl He) as H.
  destruct (disc_prem H E1 E2) as (HM & H1 & H2). destruct E1 as [-> | ->], E2 as [-> | ->].
  all: apply eqty_El; [exact Hv | exact (lequiv_refl _ _ Hl) |].
  all: exact (eqtm_case_inr _ _ _ _ _ (lsuc l) _ _ _ _ _ _ compt_D Hl Hl Hl (u_wf H) (u_wf H) HM H1 H2 He).
Qed.

(** Disjointness: from [a = w] with [Disc(a)] inhabited and [Disc(w)] empty. *)
Lemma disj_wf {Δ c1 c2 a w n} : (c1 = tmUnit l \/ c1 = tmEmpty l) -> (c2 = tmUnit l \/ c2 = tmEmpty l) ->
  [ G ; Δ ⊢[ lD ] a : tyBool l @ l ] -> [ G ; Δ ⊢[ lD ] w : tyBool l @ l ] ->
  [ G ; Δ ⊢[ lD ] tyUnit l ≅ Disc l c1 c2 a @ l ] -> [ G ; Δ ⊢[ lD ] tyEmpty l ≅ Disc l c1 c2 w @ l ] ->
  [ G ; Δ ⊢[ lD ] n : tyId l (tyBool l) a w @ l ] ->
  [ G ; Δ ⊢[ lD ] disj l c1 c2 a w n : tyEmpty l @ l ].
Proof.
  intros E1 E2 Ha Hw Ea Ew Hn. pose proof (ctx_of_wf_tm eq_refl Ha) as H. pose proof (b_wf H) as HB.
  destruct (jctx Hl HB Ha) as [HI HM]. pose proof (disc_wf E1 E2 (var1 HM)) as HD.
  destruct E1 as [-> | ->], E2 as [-> | ->].
  all: eapply wf_conv; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl HB Ha HI HD _ Hw Hn) | exact Ew].
  all: eapply wf_conv; [exact (wf_triv _ _ _ _ Hv H Hl) | exact (eqty_sym _ _ _ _ _ _ Ea)].
Qed.

Lemma dec_diff_wf {Δ a w c1 c2} : (c1 = tmUnit l \/ c1 = tmEmpty l) -> (c2 = tmUnit l \/ c2 = tmEmpty l) ->
  [ G ; Δ ⊢[ lD ] a : tyBool l @ l ] -> [ G ; Δ ⊢[ lD ] w : tyBool l @ l ] ->
  [ G ; Δ ,, tyId l (tyBool l) a w @ l ⊢[ lD ] tyUnit l ≅ Disc l c1 c2 a⟨↑⟩ @ l ] ->
  [ G ; Δ ,, tyId l (tyBool l) a w @ l ⊢[ lD ] tyEmpty l ≅ Disc l c1 c2 w⟨↑⟩ @ l ] ->
  [ G ; Δ ⊢[ lD ] dec_diff l a w c1 c2 : SumI l (tyBool l) a w @ lmax l l ].
Proof.
  intros E1 E2 Ha Hw Ea Ew. pose proof (ctx_of_wf_tm eq_refl Ha) as H. pose proof (b_wf H) as HB.
  pose proof (id_wf Hl HB Ha Hw) as HI. pose proof (ext Hl HI) as H1.
  apply wf_inr; [exact Hv | exact Hl | exact Hl | exact HI | exact (neg_wf Hl HI) |].
  apply (lc_tm Hl), wf_lam; [exact Hv | exact Hl | exact Hl | exact HI |].
  apply (disj_wf E1 E2 (wktm H1 Ha) (wktm H1 Hw) Ea Ew).
  eapply wf_tm_retype; [exact (var0 H1) | sy].
Qed.

Lemma dec_same_wf {Δ s s'} : [ G ; Δ ⊢[ lD ] s : tyBool l @ l ] -> [ G ; Δ ⊢[ lD ] s ≅ s' : tyBool l @ l ] ->
  [ G ; Δ ⊢[ lD ] tmInl l l (tyId l (tyBool l) s s') (tyNeg l (tyId l (tyBool l) s s')) (tmRefl l (tyBool l) s)
      : SumI l (tyBool l) s s' @ lmax l l ].
Proof.
  intros Hs Es. pose proof (ctx_of_wf_tm eq_refl Hs) as H. pose proof (b_wf H) as HB.
  pose proof (id_wf Hl HB Hs (eqtm_wf_r eq_refl Es)) as HI.
  apply wf_inl; [exact Hv | exact Hl | exact Hl | exact HI | exact (neg_wf Hl HI) |].
  eapply wf_conv; [exact (wf_idrefl _ _ _ _ _ _ Hv Hl HB Hs) |].
  apply eqty_id; [exact Hv | exact (lequiv_refl _ _ Hl) | exact HB | exact (eqty_refl _ _ _ _ _ HB) | exact (eqtm_refl _ _ _ _ _ _ Hs) | exact (eqtm_sym _ _ _ _ _ _ _ Es)].
Qed.

Lemma unit_inl_eq {Δ e e'} : [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] -> [ G ; Δ ⊢[ lD ] e' : tyUnit l @ l ] ->
  [ G ; Δ ⊢[ lD ] binl l e ≅ binl l e' : tyBool l @ l ].
Proof.
  intros He He'. pose proof (ctx_of_wf_tm eq_refl He) as H. pose proof (eqty_refl _ _ _ _ _ (u_wf H)) as EU.
  apply (eqtm_lconv _ _ _ _ _ _ _ _ (eqtm_inl _ _ _ _ _ _ _ _ _ _ _ _ _ Hv (lequiv_refl _ _ Hl) (lequiv_refl _ _ Hl) EU EU
           (eqtm_unit_eta _ _ _ _ _ _ compt_D Hl He He'))).
  exact (lequiv_sym _ _ _ (lmax_idem _ _ Hl)).
Qed.
Lemma unit_inr_eq {Δ e e'} : [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] -> [ G ; Δ ⊢[ lD ] e' : tyUnit l @ l ] ->
  [ G ; Δ ⊢[ lD ] binr l e ≅ binr l e' : tyBool l @ l ].
Proof.
  intros He He'. pose proof (ctx_of_wf_tm eq_refl He) as H. pose proof (eqty_refl _ _ _ _ _ (u_wf H)) as EU.
  apply (eqtm_lconv _ _ _ _ _ _ _ _ (eqtm_inr _ _ _ _ _ _ _ _ _ _ _ _ _ Hv (lequiv_refl _ _ Hl) (lequiv_refl _ _ Hl) EU EU
           (eqtm_unit_eta _ _ _ _ _ _ compt_D Hl He He'))).
  exact (lequiv_sym _ _ _ (lmax_idem _ _ Hl)).
Qed.

(** [Disc] at an injection of a unit, decoded. *)
Lemma disc_unit_l {Δ e c2} : (c2 = tmUnit l \/ c2 = tmEmpty l) -> [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] ->
  [ G ; Δ ⊢[ lD ] tyUnit l ≅ Disc l (tmUnit l) c2 (binl l e) @ l ].
Proof.
  intros E2 He. pose proof (ctx_of_wf_tm eq_refl He) as H.
  exact (eqty_trans _ _ _ _ _ _ _ (eqty_El_unit _ _ _ _ compt_D H Hl) (eqty_sym _ _ _ _ _ _ (disc_inl (or_introl eq_refl) E2 He))).
Qed.
Lemma disc_unit_r {Δ e c1} : (c1 = tmUnit l \/ c1 = tmEmpty l) -> [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] ->
  [ G ; Δ ⊢[ lD ] tyUnit l ≅ Disc l c1 (tmUnit l) (binr l e) @ l ].
Proof.
  intros E1 He. pose proof (ctx_of_wf_tm eq_refl He) as H.
  exact (eqty_trans _ _ _ _ _ _ _ (eqty_El_unit _ _ _ _ compt_D H Hl) (eqty_sym _ _ _ _ _ _ (disc_inr E1 (or_introl eq_refl) He))).
Qed.
Lemma disc_empty_l {Δ e c2} : (c2 = tmUnit l \/ c2 = tmEmpty l) -> [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] ->
  [ G ; Δ ⊢[ lD ] tyEmpty l ≅ Disc l (tmEmpty l) c2 (binl l e) @ l ].
Proof.
  intros E2 He. pose proof (ctx_of_wf_tm eq_refl He) as H.
  exact (eqty_trans _ _ _ _ _ _ _ (eqty_El_empty _ _ _ _ compt_D H Hl) (eqty_sym _ _ _ _ _ _ (disc_inl (or_intror eq_refl) E2 He))).
Qed.
Lemma disc_empty_r {Δ e c1} : (c1 = tmUnit l \/ c1 = tmEmpty l) -> [ G ; Δ ⊢[ lD ] e : tyUnit l @ l ] ->
  [ G ; Δ ⊢[ lD ] tyEmpty l ≅ Disc l c1 (tmEmpty l) (binr l e) @ l ].
Proof.
  intros E1 He. pose proof (ctx_of_wf_tm eq_refl He) as H.
  exact (eqty_trans _ _ _ _ _ _ _ (eqty_El_empty _ _ _ _ compt_D H Hl) (eqty_sym _ _ _ _ _ _ (disc_inr E1 (or_intror eq_refl) He))).
Qed.

Theorem decBool_wf {Γ} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] decBool l : DecEq l (tyBool l) @ l ].
Proof.
  intros HΓ. pose proof (b_wf HΓ) as HB. pose proof (ext Hl HB) as H1. pose proof (ext Hl (b_wf H1)) as H2.
  pose proof (ext Hl (u_wf H2)) as H3. pose proof (ext Hl (u_wf H3)) as H4.
  assert (HS : forall Δ, [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ,, tySum l l (tyUnit l) (tyUnit l) @ lmax l l ⊢[ lD ] ])
    by (intros Δ H; exact (ext (l := lmax l l) (conj Hl Hl) (wft_sum _ _ _ _ _ _ _ Hv Hl Hl (u_wf H) (u_wf H)))).
  (* the case variable, as a boolean *)
  assert (Hz : forall Δ, [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ,, tySum l l (tyUnit l) (tyUnit l) @ lmax l l ⊢[ lD ] var 0 : tyBool l @ l ])
    by (intros Δ H; apply (lc_tm Hl); exact (var0 (HS _ H))).
  (* [e] and [e'] in [Γ, x, y, e, e'], and [e] in [Γ, x, y, e, z] *)
  pose proof (var1 H4) as He1. pose proof (var0 H4) as He0.
  pose proof (var1 (HS _ H3)) as He1z.
  (* [e] and [e'] one binder further, under [n : Id(…)] *)
  assert (Wn : forall A k, [ G ; _ ,, A @ k ⊢[ lD ] ] ->
     [ G ; _ ,, A @ k ⊢[ lD ] var 2 : tyUnit l @ l ] /\ [ G ; _ ,, A @ k ⊢[ lD ] var 1 : tyUnit l @ l ])
    by (intros A k H; split; [exact (wktm H He1) | exact (wktm H He0)]).
  unfold decBool.
  apply (lc_tm Hl), wf_lam; [exact Hv | exact Hl | exact Hl | exact HB |].
  apply (lc_tm Hl), wf_lam; [exact Hv | exact Hl | exact Hl | exact (b_wf H1) |].
  eapply wf_tm_retype; [refine (wf_case _ _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl Hl (u_wf H2) (u_wf H2) _ _ _ (cl_tm Hl (var1 H2))) | unfold DecB; sy].
  - apply (lc_ty Hl). exact (sumI_wf Hl (b_wf (HS _ H2)) (Hz _ H2) (var1 (HS _ H2))).
  - (* [x = inl e] *)
    eapply wf_tm_retype; [refine (wf_case _ _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl Hl (u_wf H3) (u_wf H3) _ _ _ (cl_tm Hl (var1 H3))) | sy].
    + apply (lc_ty Hl). exact (sumI_wf Hl (b_wf (HS _ H3)) (binl_wf He1z) (Hz _ H3)).
    + eapply wf_tm_retype; [apply (lc_tm Hl), dec_same_wf; [exact (binl_wf He1) | exact (unit_inl_eq He1 He0)] | sy].
    + eapply wf_tm_retype; [apply (lc_tm Hl), dec_diff_wf; [left; reflexivity | right; reflexivity | exact (binl_wf He1) | exact (binr_wf He0) | |] | sy].
      * pose proof (id_wf Hl (b_wf H4) (binl_wf He1) (binr_wf He0)) as HI. destruct (Wn _ _ (ext Hl HI)) as [Hf2 Hf1].
        exact (disc_unit_l (or_intror eq_refl) Hf2).
      * pose proof (id_wf Hl (b_wf H4) (binl_wf He1) (binr_wf He0)) as HI. destruct (Wn _ _ (ext Hl HI)) as [Hf2 Hf1].
        exact (disc_empty_r (or_introl eq_refl) Hf1).
  - (* [x = inr e] *)
    eapply wf_tm_retype; [refine (wf_case _ _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hl Hl (u_wf H3) (u_wf H3) _ _ _ (cl_tm Hl (var1 H3))) | sy].
    + apply (lc_ty Hl). exact (sumI_wf Hl (b_wf (HS _ H3)) (binr_wf He1z) (Hz _ H3)).
    + eapply wf_tm_retype; [apply (lc_tm Hl), dec_diff_wf; [right; reflexivity | left; reflexivity | exact (binr_wf He1) | exact (binl_wf He0) | |] | sy].
      * pose proof (id_wf Hl (b_wf H4) (binr_wf He1) (binl_wf He0)) as HI. destruct (Wn _ _ (ext Hl HI)) as [Hf2 Hf1].
        exact (disc_unit_r (or_intror eq_refl) Hf2).
      * pose proof (id_wf Hl (b_wf H4) (binr_wf He1) (binl_wf He0)) as HI. destruct (Wn _ _ (ext Hl HI)) as [Hf2 Hf1].
        exact (disc_empty_l (or_introl eq_refl) Hf1).
    + eapply wf_tm_retype; [apply (lc_tm Hl), dec_same_wf; [exact (binr_wf He1) | exact (unit_inr_eq He1 He0)] | sy].
Qed.

(** UIP at [Bool], as Hedberg's theorem predicts. *)
Theorem uip_bool_wf {Γ} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] uip_bool l : uipT l (tyBool l) @ uipL l ].
Proof. intros HΓ. exact (hedberg_wf Hl (b_wf HΓ) (decBool_wf HΓ)). Qed.

End Bool.

(** *** [Nat] *)

Section NatDec.
Let I0 : lwf (gL G) lzero := I.

Lemma n_wf {Δ} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] tyNat @ lzero ].
Proof. intros H. exact (wft_nat _ _ _ Hv H). Qed.

Lemma pred_prem {Δ} : [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ,, tyNat @ lzero ⊢[ lD ] tyNat @ lzero ] /\ [ G ; Δ ⊢[ lD ] zero : tyNat[lsingle zero] @ lzero ] /\
  [ G ; Δ ,, tyNat @ lzero ,, tyNat @ lzero ⊢[ lD ] var 1 : tyNat[lsucc] @ lzero ].
Proof.
  intros H. pose proof (ext I0 (n_wf H)) as H1. pose proof (ext I0 (n_wf H1)) as H2.
  split; [exact (n_wf H1) | split; [exact (wf_zero _ _ _ Hv H) | exact (var1 H2)]].
Qed.
Lemma pred_wf {Δ t} : [ G ; Δ ⊢[ lD ] t : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] pred t : tyNat @ lzero ].
Proof.
  intros Ht. destruct (pred_prem (ctx_of_wf_tm eq_refl Ht)) as (HM & Hs & Hz).
  exact (wf_natrec _ _ _ _ _ _ _ _ Hv I0 HM Hs Hz Ht).
Qed.
Lemma pred_succ {Δ t} : [ G ; Δ ⊢[ lD ] t : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] pred (succ t) ≅ t : tyNat @ lzero ].
Proof.
  intros Ht. destruct (pred_prem (ctx_of_wf_tm eq_refl Ht)) as (HM & Hs & Hz).
  exact (eqtm_natrec_succ _ _ _ _ _ _ _ _ compt_D I0 HM Hs Hz Ht).
Qed.

Lemma apsucc_wf {Δ a b e} : [ G ; Δ ⊢[ lD ] a : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] b : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ lD ] e : tyId lzero tyNat a b @ lzero ] ->
  [ G ; Δ ⊢[ lD ] apsucc a b e : tyId lzero tyNat (succ a) (succ b) @ lzero ].
Proof.
  intros Ha Hb He. pose proof (ctx_of_wf_tm eq_refl Ha) as H. pose proof (n_wf H) as HN.
  destruct (jctx I0 HN Ha) as [HI HM].
  eapply wf_tm_retype; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv I0 I0 HN Ha HI _ _ Hb He) | sy].
  - apply wft_id; [exact Hv | exact I0 | exact (n_wf HM) | exact (wf_succ _ _ _ _ Hv (wk2tm HM Ha)) | exact (wf_succ _ _ _ _ Hv (var1 HM))].
  - eapply wf_tm_retype; [exact (wf_idrefl _ _ _ _ _ _ Hv I0 HN (wf_succ _ _ _ _ Hv Ha)) | sy].
Qed.

Lemma predap_wf {Δ a b p} : [ G ; Δ ⊢[ lD ] a : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] b : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ lD ] p : tyId lzero tyNat (succ a) (succ b) @ lzero ] ->
  [ G ; Δ ⊢[ lD ] predap a b p : tyId lzero tyNat a b @ lzero ].
Proof.
  intros Ha Hb Hp. pose proof (ctx_of_wf_tm eq_refl Ha) as H. pose proof (n_wf H) as HN.
  pose proof (wf_succ _ _ _ _ Hv Ha) as Hsa. pose proof (wf_succ _ _ _ _ Hv Hb) as Hsb.
  destruct (jctx I0 HN Hsa) as [HI HM].
  (* [Id(a; pred(succ c)) ≅ Id(a; c)] *)
  assert (E : forall c, [ G ; Δ ⊢[ lD ] c : tyNat @ lzero ] ->
            [ G ; Δ ⊢[ lD ] tyId lzero tyNat a c ≅ tyId lzero tyNat a (pred (succ c)) @ lzero ]).
  { intros c Hc. apply eqty_id; [exact Hv | exact (lequiv_refl _ _ I0) | exact HN | exact (eqty_refl _ _ _ _ _ HN)
                               | exact (eqtm_refl _ _ _ _ _ _ Ha) | exact (eqtm_sym _ _ _ _ _ _ _ (pred_succ Hc))]. }
  eapply wf_conv; [eapply wf_tm_retype; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv I0 I0 HN Hsa HI _ _ Hsb Hp) | sy] | exact (E _ Hb)].
  - apply wft_id; [exact Hv | exact I0 | exact (n_wf HM) | exact (wk2tm HM Ha) | exact (pred_wf (var1 HM))].
  - eapply wf_tm_retype; [eapply wf_conv; [exact (wf_idrefl _ _ _ _ _ _ Hv I0 HN Ha) | exact (eqty_sym _ _ _ _ _ _ (E _ Ha))] | sy].
Qed.

(** The discriminator decodes at [zero] and at a successor. *)
Lemma discN_prem {Δ c1 c2} : [ G ; Δ ⊢[ lD ] ] -> (c1 = tmUnit lzero \/ c1 = tmEmpty lzero) -> (c2 = tmUnit lzero \/ c2 = tmEmpty lzero) ->
  [ G ; Δ ,, tyNat @ lzero ⊢[ lD ] tyU lzero @ lsuc lzero ] /\
  [ G ; Δ ⊢[ lD ] c1 : (tyU lzero)[lsingle zero] @ lsuc lzero ] /\
  [ G ; Δ ,, tyNat @ lzero ,, tyU lzero @ lsuc lzero ⊢[ lD ] c2 : (tyU lzero)[lsucc] @ lsuc lzero ].
Proof.
  intros H E1 E2. pose proof (ext I0 (n_wf H)) as H1. pose proof (ext (l := lsuc lzero) I0 (wft_U _ _ _ _ Hv H1 I0)) as H2.
  split; [exact (wft_U _ _ _ _ Hv H1 I0) | split].
  - destruct E1 as [-> | ->]; [exact (wf_code_unit _ _ _ _ Hv H I0) | exact (wf_code_empty _ _ _ _ Hv H I0)].
  - destruct E2 as [-> | ->]; [exact (wf_code_unit _ _ _ _ Hv H2 I0) | exact (wf_code_empty _ _ _ _ Hv H2 I0)].
Qed.
Lemma discN_wf {Δ c1 c2 s} : (c1 = tmUnit lzero \/ c1 = tmEmpty lzero) -> (c2 = tmUnit lzero \/ c2 = tmEmpty lzero) ->
  [ G ; Δ ⊢[ lD ] s : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] DiscN c1 c2 s @ lzero ].
Proof.
  intros E1 E2 Hs. destruct (discN_prem (ctx_of_wf_tm eq_refl Hs) E1 E2) as (HM & H1 & H2).
  apply wft_El; [exact Hv | exact I0 | exact (wf_natrec _ _ _ (lsuc lzero) _ _ _ _ Hv I0 HM H1 H2 Hs)].
Qed.
Lemma discN_zero {Δ c1 c2} : [ G ; Δ ⊢[ lD ] ] -> (c1 = tmUnit lzero \/ c1 = tmEmpty lzero) -> (c2 = tmUnit lzero \/ c2 = tmEmpty lzero) ->
  [ G ; Δ ⊢[ lD ] DiscN c1 c2 zero ≅ tyEl lzero c1 @ lzero ].
Proof.
  intros H E1 E2. destruct (discN_prem H E1 E2) as (HM & H1 & H2).
  apply eqty_El; [exact Hv | exact (lequiv_refl _ _ I0) | exact (eqtm_natrec_zero _ _ _ (lsuc lzero) _ _ _ compt_D I0 HM H1 H2)].
Qed.
Lemma discN_succ {Δ c1 c2 t} : (c1 = tmUnit lzero \/ c1 = tmEmpty lzero) -> (c2 = tmUnit lzero \/ c2 = tmEmpty lzero) ->
  [ G ; Δ ⊢[ lD ] t : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] DiscN c1 c2 (succ t) ≅ tyEl lzero c2 @ lzero ].
Proof.
  intros E1 E2 Ht. destruct (discN_prem (ctx_of_wf_tm eq_refl Ht) E1 E2) as (HM & H1 & H2).
  destruct E2 as [-> | ->].
  all: apply eqty_El; [exact Hv | exact (lequiv_refl _ _ I0) | exact (eqtm_natrec_succ _ _ _ (lsuc lzero) _ _ _ _ compt_D I0 HM H1 H2 Ht)].
Qed.

(** [El(⌜Unit⌝) ≅ Unit] and [El(⌜Empty⌝) ≅ Empty], composed with the above. *)
Lemma el_unit {Δ D} : [ G ; Δ ⊢[ lD ] D ≅ tyEl lzero (tmUnit lzero) @ lzero ] -> [ G ; Δ ⊢[ lD ] tyUnit lzero ≅ D @ lzero ].
Proof.
  intros E. exact (eqty_trans _ _ _ _ _ _ _ (eqty_El_unit _ _ _ _ compt_D (ctx_of_eqty eq_refl E) I0) (eqty_sym _ _ _ _ _ _ E)).
Qed.
Lemma el_empty {Δ D} : [ G ; Δ ⊢[ lD ] D ≅ tyEl lzero (tmEmpty lzero) @ lzero ] -> [ G ; Δ ⊢[ lD ] tyEmpty lzero ≅ D @ lzero ].
Proof.
  intros E. exact (eqty_trans _ _ _ _ _ _ _ (eqty_El_empty _ _ _ _ compt_D (ctx_of_eqty eq_refl E) I0) (eqty_sym _ _ _ _ _ _ E)).
Qed.

Lemma disjN_wf {Δ c1 c2 a w n} : (c1 = tmUnit lzero \/ c1 = tmEmpty lzero) -> (c2 = tmUnit lzero \/ c2 = tmEmpty lzero) ->
  [ G ; Δ ⊢[ lD ] a : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] w : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ lD ] tyUnit lzero ≅ DiscN c1 c2 a @ lzero ] -> [ G ; Δ ⊢[ lD ] tyEmpty lzero ≅ DiscN c1 c2 w @ lzero ] ->
  [ G ; Δ ⊢[ lD ] n : tyId lzero tyNat a w @ lzero ] ->
  [ G ; Δ ⊢[ lD ] disjN c1 c2 a w n : tyEmpty lzero @ lzero ].
Proof.
  intros E1 E2 Ha Hw Ea Ew Hn. pose proof (ctx_of_wf_tm eq_refl Ha) as H. pose proof (n_wf H) as HN.
  destruct (jctx I0 HN Ha) as [HI HM]. pose proof (discN_wf E1 E2 (var1 HM)) as HD.
  destruct E1 as [-> | ->], E2 as [-> | ->].
  all: eapply wf_conv; [refine (wf_J _ _ _ _ _ _ _ _ _ _ _ Hv I0 I0 HN Ha HI HD _ Hw Hn) | exact Ew].
  all: eapply wf_conv; [exact (wf_triv _ _ _ _ Hv H I0) | exact (eqty_sym _ _ _ _ _ _ Ea)].
Qed.

Lemma diffN_wf {Δ a w c1 c2} : (c1 = tmUnit lzero \/ c1 = tmEmpty lzero) -> (c2 = tmUnit lzero \/ c2 = tmEmpty lzero) ->
  [ G ; Δ ⊢[ lD ] a : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] w : tyNat @ lzero ] ->
  [ G ; Δ ,, tyId lzero tyNat a w @ lzero ⊢[ lD ] tyUnit lzero ≅ DiscN c1 c2 a⟨↑⟩ @ lzero ] ->
  [ G ; Δ ,, tyId lzero tyNat a w @ lzero ⊢[ lD ] tyEmpty lzero ≅ DiscN c1 c2 w⟨↑⟩ @ lzero ] ->
  [ G ; Δ ⊢[ lD ] diffN a w c1 c2 : SumI lzero tyNat a w @ lmax lzero lzero ].
Proof.
  intros E1 E2 Ha Hw Ea Ew. pose proof (ctx_of_wf_tm eq_refl Ha) as H. pose proof (n_wf H) as HN.
  pose proof (id_wf I0 HN Ha Hw) as HI. pose proof (ext I0 HI) as H1.
  apply wf_inr; [exact Hv | exact I0 | exact I0 | exact HI | exact (neg_wf I0 HI) |].
  apply (lc_tm I0), wf_lam; [exact Hv | exact I0 | exact I0 | exact HI |].
  apply (disjN_wf E1 E2 (wktm H1 Ha) (wktm H1 Hw) Ea Ew).
  eapply wf_tm_retype; [exact (var0 H1) | sy].
Qed.

Lemma sameN_wf {Δ s} : [ G ; Δ ⊢[ lD ] s : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] sameN s : SumI lzero tyNat s s @ lmax lzero lzero ].
Proof.
  intros Hs. pose proof (n_wf (ctx_of_wf_tm eq_refl Hs)) as HN. pose proof (id_wf I0 HN Hs Hs) as HI.
  apply wf_inl; [exact Hv | exact I0 | exact I0 | exact HI | exact (neg_wf I0 HI) | exact (wf_idrefl _ _ _ _ _ _ Hv I0 HN Hs)].
Qed.

Lemma stepSS_wf {Δ n m h} : [ G ; Δ ⊢[ lD ] n : tyNat @ lzero ] -> [ G ; Δ ⊢[ lD ] m : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ lD ] h : tyPi lzero lzero tyNat (SumI lzero tyNat n⟨↑⟩ (var 0)) @ lzero ] ->
  [ G ; Δ ⊢[ lD ] stepSS n m h : SumI lzero tyNat (succ n) (succ m) @ lzero ].
Proof.
  intros Hn Hm Hh. pose proof (ctx_of_wf_tm eq_refl Hn) as H. pose proof (n_wf H) as HN.
  pose proof (id_wf I0 HN Hn Hm) as HI. pose proof (neg_wf I0 HI) as HNI.
  pose proof (wf_succ _ _ _ _ Hv Hn) as Hsn. pose proof (wf_succ _ _ _ _ Hv Hm) as Hsm.
  pose proof (ext (l := lmax lzero lzero) (conj I0 I0) (sumI_wf I0 HN Hn Hm)) as HS.
  pose proof (ext I0 HI) as HΓI. pose proof (ext I0 HNI) as HΓN.
  assert (Lv : forall A k, [ G ; Δ ,, A @ k ⊢[ lD ] ] ->
     [ G ; Δ ,, A @ k ⊢[ lD ] n⟨↑⟩ : tyNat @ lzero ] /\ [ G ; Δ ,, A @ k ⊢[ lD ] m⟨↑⟩ : tyNat @ lzero ])
    by (intros A k H'; split; [exact (wktm H' Hn) | exact (wktm H' Hm)]).
  eapply wf_tm_retype; [refine (wf_case _ _ _ _ _ _ _ _ _ _ _ _ Hv I0 I0 I0 HI HNI _ _ _ _) | sy].
  - exact (wkty HS (lc_ty I0 (sumI_wf I0 HN Hsn Hsm))).
  - destruct (Lv _ _ HΓI) as [Hn1 Hm1]. pose proof (n_wf HΓI) as HN1.
    pose proof (id_wf I0 HN1 (wf_succ _ _ _ _ Hv Hn1) (wf_succ _ _ _ _ Hv Hm1)) as HJ.
    eapply wf_tm_retype; [apply (lc_tm I0), wf_inl; [exact Hv | exact I0 | exact I0 | exact HJ | exact (neg_wf I0 HJ) |] | sy].
    apply (apsucc_wf Hn1 Hm1). eapply wf_tm_retype; [exact (var0 HΓI) | sy].
  - destruct (Lv _ _ HΓN) as [Hn1 Hm1]. pose proof (n_wf HΓN) as HN1.
    pose proof (id_wf I0 HN1 (wf_succ _ _ _ _ Hv Hn1) (wf_succ _ _ _ _ Hv Hm1)) as HJ.
    pose proof (ext I0 HJ) as H2.
    pose proof (wktm H2 Hn1) as Hn2. pose proof (wktm H2 Hm1) as Hm2. pose proof (n_wf H2) as HN2.
    pose proof (id_wf I0 HN2 Hn2 Hm2) as HI2.
    eapply wf_tm_retype; [apply (lc_tm I0), wf_inr; [exact Hv | exact I0 | exact I0 | exact HJ | exact (neg_wf I0 HJ) |] | sy].
    apply (lc_tm I0), wf_lam; [exact Hv | exact I0 | exact I0 | exact HJ |].
    eapply wf_tm_retype; [refine (wf_app _ _ _ _ _ _ _ _ _ Hv I0 I0 HI2 (wft_empty _ _ _ _ Hv (ext I0 HI2) I0) _ _) | reflexivity].
    + apply (cl_tm I0). eapply wf_tm_retype; [exact (var1 H2) | sy].
    + apply (predap_wf Hn2 Hm2). eapply wf_tm_retype; [exact (var0 H2) | sy].
  - apply (cl_tm I0). eapply wf_tm_retype;
      [exact (wf_app _ _ _ _ _ _ _ _ _ Hv I0 I0 HN (lc_ty I0 (sumI_wf I0 (n_wf (ext I0 HN)) (wktm (ext I0 HN) Hn) (var0 (ext I0 HN)))) (cl_tm I0 Hh) Hm) | sy].
Qed.

Theorem decNat_wf {Γ} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] decNat : DecEq lzero tyNat @ lzero ].
Proof.
  intros HΓ. pose proof (n_wf HΓ) as HN.
  (* contexts: [x], then the outer [natrec]'s motive, zero case and successor case *)
  pose proof (ext I0 HN) as Hx. pose proof (ext I0 (n_wf Hx)) as Hxw.
  set (Mx := tyPi lzero lzero tyNat (SumI lzero tyNat (var 1) (var 0))).
  assert (HMx : [ G ; Γ ,, tyNat @ lzero ,, tyNat @ lzero ⊢[ lD ] Mx @ lzero ]).
  { pose proof (ext I0 (n_wf Hxw)) as H. apply (lc_ty I0), wft_pi; [exact Hv | exact I0 | exact I0 | exact (n_wf Hxw) |].
    exact (lc_ty I0 (sumI_wf I0 (n_wf H) (var1 H) (var0 H))). }
  unfold decNat. fold Mx.
  apply (lc_tm I0), wf_lam; [exact Hv | exact I0 | exact I0 | exact HN |].
  eapply wf_tm_retype; [refine (wf_natrec _ _ _ _ _ _ _ _ Hv I0 HMx _ _ (var0 Hx)) | unfold Mx, DecB; sy].
  - (* [x = zero]: [natrec] on [y] *)
    eapply (wf_tm_retype _ _ _ _ _ (tyPi lzero lzero tyNat (SumI lzero tyNat zero (var 0)))); [| unfold Mx; sy].
    apply (lc_tm I0), wf_lam; [exact Hv | exact I0 | exact I0 | exact (n_wf Hx) |].
    pose proof (ext I0 (n_wf Hx)) as Hy. pose proof (ext I0 (n_wf Hy)) as Hyw.
    assert (HM : [ G ; _ ⊢[ lD ] SumI lzero tyNat zero (var 0) @ lzero ])
      by exact (lc_ty I0 (sumI_wf I0 (n_wf Hyw) (wf_zero _ _ _ Hv Hyw) (var0 Hyw))).
    eapply wf_tm_retype; [refine (wf_natrec _ _ _ _ _ _ _ _ Hv I0 HM _ _ (var0 Hy)) | sy].
    + eapply wf_tm_retype; [exact (lc_tm I0 (sameN_wf (wf_zero _ _ _ Hv Hy))) | sy].
    + pose proof (ext I0 HM) as Hz. pose proof (wf_succ _ _ _ _ Hv (var1 Hz)) as Hsm.
      eapply wf_tm_retype; [apply (lc_tm I0), diffN_wf; [left; reflexivity | right; reflexivity | exact (wf_zero _ _ _ Hv Hz) | exact Hsm | |] | sy].
      * pose proof (id_wf I0 (n_wf Hz) (wf_zero _ _ _ Hv Hz) Hsm) as HI. pose proof (ext I0 HI) as H'.
        exact (el_unit (discN_zero H' (or_introl eq_refl) (or_intror eq_refl))).
      * pose proof (id_wf I0 (n_wf Hz) (wf_zero _ _ _ Hv Hz) Hsm) as HI. pose proof (ext I0 HI) as H'.
        exact (el_empty (discN_succ (or_introl eq_refl) (or_intror eq_refl) (wktm H' (var1 Hz)))).
  - (* [x = succ n], with [ih : Π y. n = y + n ≠ y] *)
    pose proof (ext I0 HMx) as Hn.
    eapply (wf_tm_retype _ _ _ _ _ (tyPi lzero lzero tyNat (SumI lzero tyNat (succ (var 2)) (var 0)))); [| unfold Mx; sy].
    apply (lc_tm I0), wf_lam; [exact Hv | exact I0 | exact I0 | exact (n_wf Hn) |].
    pose proof (ext I0 (n_wf Hn)) as Hy. pose proof (ext I0 (n_wf Hy)) as Hyw.
    assert (HM : [ G ; _ ⊢[ lD ] SumI lzero tyNat (succ (var 3)) (var 0) @ lzero ])
      by exact (lc_ty I0 (sumI_wf I0 (n_wf Hyw) (wf_succ _ _ _ _ Hv (wf_var _ lD _ _ _ _ Hyw (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_here _ _ _)))))) (var0 Hyw))).
    eapply wf_tm_retype; [refine (wf_natrec _ _ _ _ _ _ _ _ Hv I0 HM _ _ (var0 Hy)) | sy].
    + pose proof (wf_succ _ _ _ _ Hv (wf_var _ lD _ _ _ _ Hy (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_here _ _ _))))) as Hsn.
      eapply wf_tm_retype; [apply (lc_tm I0), diffN_wf; [right; reflexivity | left; reflexivity | exact Hsn | exact (wf_zero _ _ _ Hv Hy) | |] | sy].
      * pose proof (id_wf I0 (n_wf Hy) Hsn (wf_zero _ _ _ Hv Hy)) as HI. pose proof (ext I0 HI) as H'.
        exact (el_unit (discN_succ (or_intror eq_refl) (or_introl eq_refl) (wktm H' (wf_var _ lD _ _ _ _ Hy (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_here _ _ _))))))).
      * pose proof (id_wf I0 (n_wf Hy) Hsn (wf_zero _ _ _ Hv Hy)) as HI. pose proof (ext I0 HI) as H'.
        exact (el_empty (discN_zero H' (or_intror eq_refl) (or_introl eq_refl))).
    + pose proof (ext I0 HM) as Hz.
      eapply wf_tm_retype; [apply stepSS_wf | sy].
      * exact (wf_var _ lD _ _ _ _ Hz (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_here _ _ _)))))).
      * exact (var1 Hz).
      * eapply wf_tm_retype; [exact (wf_var _ lD _ _ _ _ Hz (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_there _ _ _ _ _ _ (in_here _ _ _))))) | unfold Mx; sy].
Qed.

(** UIP at [Nat], as Hedberg's theorem predicts. *)
Theorem uip_nat_wf {Γ} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] uip_nat : uipT lzero tyNat @ uipL lzero ].
Proof. intros HΓ. exact (hedberg_wf (l := lzero) I (n_wf HΓ) (decNat_wf HΓ)). Qed.

End NatDec.

End Hedberg.
