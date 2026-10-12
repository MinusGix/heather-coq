(** * The recursor bundle and the β reducts of the code recursors (M3)

    [elim_Typ^{l₁,l₂} M⃗ b⃗ l Δ t] and [elim_Trm^{l₁,l₂} M⃗ b⃗ l Δ T t]
    (04:816) carry a bundle [rb] of two motives and [nbr] branches
    (M3_DESIGN.md E2). A component with binders is wrapped in single-step
    markers, levels outermost, then globals, then locals, in the paper's
    binding order (so the last-bound variable is index 0):
    - [MT = ℓ; g; x_T. M_Typ]:          [bindU (bindG (bindL (tmTy MT)))]
    - [Mt = ℓ; g, U_T; x_t. M_Trm]:     [bindU (bindG (bindG (bindL (tmTy Mt))))]
    - branch [k] with arity [(nu, ng, nl)] (table [br_ar]).

    A β reduct instantiates a branch by peeling its binders one at a time
    with the single substitutions [usingle], [gsingle], [lsingle]
    (M3_DESIGN.md E4). *)
From DeLaM.Syntax Require Export Term.

(** ** The bundle *)

Fixpoint tup_nth (t : tm) (k : nat) {struct k} : tm :=
  match t with
  | tmTup a r => match k with 0 => a | S k => tup_nth r k end
  | _ => tmErr
  end.

Fixpoint wrapU (n : nat) (b : tm) : tm := match n with 0 => b | S n => bindU (wrapU n b) end.
Fixpoint wrapG (n : nat) (b : tm) : tm := match n with 0 => b | S n => bindG (wrapG n b) end.
Fixpoint wrapL (n : nat) (b : tm) : tm := match n with 0 => b | S n => bindL (wrapL n b) end.
Definition wrap (nu ng nl : nat) (b : tm) : tm := wrapU nu (wrapG ng (wrapL nl b)).

(** The number of branches, and the branch-indexed case split: [br_all t]
    runs [t] [nbr] times, as [do nbr t] would (M8_DESIGN.md J2, S0). *)
Notation nbr := 51 (only parsing).
Ltac br_do n tac := lazymatch n with O => idtac | S ?m => tac; br_do m tac end.
Ltac br_all tac := br_do constr:(nbr) tac.

(** Branch indices, in the paper's order (04:822–831). *)
Definition bNat := 0.   Definition bPi := 1.    Definition bU := 2.     Definition bEl := 3.
Definition bVar := 4.   Definition bNat' := 5.  Definition bPi' := 6.   Definition bU' := 7.
Definition bZero := 8.  Definition bSucc := 9.  Definition bNatrec := 10.
Definition bLam := 11.  Definition bApp := 12.
(** Heather's extension branches (M8_DESIGN.md L2), after ch. 04's, in
    Heather's order ([rec.rs] [branch_specs]) among the formers we have. *)
Definition bSig := 13.  Definition bUnit := 14.  Definition bSig' := 15.  Definition bPair := 16.
Definition bFst := 17.  Definition bSnd := 18.  Definition bUnit' := 19. Definition bTriv := 20.
(** The identity type's (M11b): Heather's [t_Id], [t'_Id], [t_refl], [t_J]. *)
Definition bId := 21.   Definition bId' := 22.   Definition bRefl := 23.  Definition bJ := 24.
(** Strict equality's (M10c): Heather's [t_sEq], [t'_sEq], [t_sEmpty], [t'_sEmpty],
    [t_srefl], [t_elim_sE] ([t_transp] is removed with [transp]). *)
Definition bSEq := 25.  Definition bSEq' := 26.  Definition bSEmpty := 27. Definition bSEmpty' := 28.
Definition bSrefl := 29. Definition bElimSEmpty := 30.
(** The empty type's and binary sums' (M12c): Heather's [t_Empty], [t'_Empty],
    [t_elimE], [t_+], [t'_+], [t_inl], [t_inr], [t_case]. *)
Definition bEmpty := 31. Definition bEmpty' := 32. Definition bElimEmpty := 33.
Definition bSum := 34.   Definition bSum' := 35.   Definition bInl := 36.   Definition bInr := 37.
Definition bCase := 38.
(** W-types' (M13b): Heather's [t_W], [t'_W], [t_sup], [t_elimW]. *)
Definition bW := 39.     Definition bW' := 40.     Definition bSup := 41.   Definition bElimW := 42.
(** Length-indexed tuples' and finite indices' (M14b): Heather's [t_Vec],
    [t'_Vec], [t_Fin], [t'_Fin]. *)
Definition bVec := 43.   Definition bVec' := 44.   Definition bFin := 45.   Definition bFin' := 46.
(** Finitary well-founded trees' (M15b): Heather's [t_Wf], [t'_Wf],
    [t_supf], [t_elimWf]. *)
Definition bWf := 47.    Definition bWf' := 48.    Definition bSupf := 49.  Definition bElimWf := 50.

(** The arity [(levels, globals, locals)] of branch [k]. *)
Definition br_ar (k : nat) : nat * nat * nat :=
  match k with
  | 0 => (0, 1, 0)        (* g. t_Nat *)
  | 1 => (2, 3, 2)        (* ℓ ℓ'; g U_S U_T; x_S x_T. t_Π *)
  | 2 => (1, 1, 0)        (* ℓ; g. t_Ty *)
  | 3 => (1, 2, 1)        (* ℓ; g u_t; x_t. t_El *)
  | 4 => (1, 3, 0)        (* ℓ; g U_T u_x. t_x *)
  | 5 => (0, 1, 0)        (* g. t'_Nat *)
  | 6 => (2, 3, 2)        (* ℓ ℓ'; g u_s u_t; x_s x_t. t'_Π *)
  | 7 => (1, 1, 0)        (* ℓ; g. t'_Ty *)
  | 8 => (0, 1, 0)        (* g. t_zero *)
  | 9 => (0, 2, 1)        (* g u_t; x_t. t_succ *)
  | 10 => (1, 5, 4)       (* ℓ; g U_M u_s u_s' u_t; x_M x_s x_s' x_t. t_elimN *)
  | 11 => (2, 4, 2)       (* ℓ ℓ'; g U_S U_T u_t; x_S x_t. t_λ *)
  | 12 => (2, 5, 4)       (* ℓ ℓ'; g U_S U_T u_t u_s; x_S x_T x_t x_s. t_app *)
  | 13 => (2, 3, 2)       (* ℓ ℓ'; g U_S U_T; x_S x_T. t_Σ *)
  | 14 => (1, 1, 0)       (* ℓ; g. t_Unit *)
  | 15 => (2, 3, 2)       (* ℓ ℓ'; g u_s u_t; x_s x_t. t'_Σ *)
  | 16 => (2, 5, 4)       (* ℓ ℓ'; g U_S U_T u_a u_b; x_S x_T x_a x_b. t_pair *)
  | 17 => (2, 4, 3)       (* ℓ ℓ'; g U_S U_T u_p; x_S x_T x_p. t_fst *)
  | 18 => (2, 4, 3)       (* ℓ ℓ'; g U_S U_T u_p; x_S x_T x_p. t_snd *)
  | 19 => (1, 1, 0)       (* ℓ; g. t'_Unit *)
  | 20 => (1, 1, 0)       (* ℓ; g. t_triv *)
  | 21 => (1, 4, 3)       (* ℓ; g U_S u_t u_u; x_S x_t x_u. t_Id *)
  | 22 => (1, 4, 3)       (* ℓ; g u_S u_t u_u; x_S x_t x_u. t'_Id *)
  | 23 => (1, 3, 2)       (* ℓ; g U_S u_t; x_S x_t. t_refl *)
  | 24 => (2, 7, 6)       (* ℓ ℓ'; g U_S u_a U_M u_c u_r u_e; x_S x_a x_M x_c x_r x_e. t_J *)
  | 25 => (1, 4, 3)       (* ℓ; g U_S u_t u_u; x_S x_t x_u. t_sEq *)
  | 26 => (1, 4, 3)       (* ℓ; g u_S u_t u_u; x_S x_t x_u. t'_sEq *)
  | 27 => (1, 1, 0)       (* ℓ; g. t_sEmpty *)
  | 28 => (1, 1, 0)       (* ℓ; g. t'_sEmpty *)
  | 29 => (1, 3, 2)       (* ℓ; g U_S u_t; x_S x_t. t_srefl *)
  | 30 => (2, 3, 2)       (* ℓ ℓ'; g U_M u_t; x_M x_t. t_elim_sE *)
  | 31 => (1, 1, 0)       (* ℓ; g. t_Empty *)
  | 32 => (1, 1, 0)       (* ℓ; g. t'_Empty *)
  | 33 => (2, 3, 2)       (* ℓ ℓ'; g U_M u_t; x_M x_t. t_elimE *)
  | 34 => (2, 3, 2)       (* ℓ ℓ'; g U_A U_B; x_A x_B. t_+ *)
  | 35 => (2, 3, 2)       (* ℓ ℓ'; g u_a u_b; x_a x_b. t'_+ *)
  | 36 => (2, 4, 3)       (* ℓ ℓ'; g U_A U_B u_a; x_A x_B x_a. t_inl *)
  | 37 => (2, 4, 3)       (* ℓ ℓ'; g U_A U_B u_b; x_A x_B x_b. t_inr *)
  | 38 => (3, 7, 6)       (* ℓ ℓ' ℓ''; g U_A U_B U_M u_l u_r u_t; x_A x_B x_M x_l x_r x_t. t_case *)
  | 39 => (2, 3, 2)       (* ℓ ℓ'; g U_S U_T; x_S x_T. t_W *)
  | 40 => (2, 3, 2)       (* ℓ ℓ'; g u_s u_t; x_s x_t. t'_W *)
  | 41 => (2, 5, 4)       (* ℓ ℓ'; g U_S U_T u_a u_f; x_S x_T x_a x_f. t_sup *)
  | 42 => (3, 6, 5)       (* ℓ ℓ' ℓ''; g U_S U_T U_M u_s u_t; x_S x_T x_M x_s x_t. t_elimW *)
  | 43 => (1, 3, 2)       (* ℓ; g U_T u_k; x_T x_k. t_Vec *)
  | 44 => (1, 3, 2)       (* ℓ; g u_t u_k; x_t x_k. t'_Vec *)
  | 45 => (0, 2, 1)       (* g u_k; x_k. t_Fin *)
  | 46 => (0, 2, 1)       (* g u_k; x_k. t'_Fin *)
  | 47 => (1, 3, 2)       (* ℓ; g U_S u_n; x_S x_n. t_Wf *)
  | 48 => (1, 3, 2)       (* ℓ; g u_s u_n; x_s x_n. t'_Wf *)
  | 49 => (1, 5, 4)       (* ℓ; g U_S u_n u_a u_cs; x_S x_n x_a x_cs. t_supf *)
  | 50 => (2, 6, 5)       (* ℓ ℓ'; g U_S u_n U_M u_s u_t; x_S x_n x_M x_s x_t. t_elimWf *)
  | _ => (0, 0, 0)
  end.

(** Whether branch [k] is a type branch (typed at [l₁], recursing on
    [elim_Typ]) or a term branch. *)
Definition br_isT (k : nat) : bool :=
  match k with 0 | 1 | 2 | 3 | 13 | 14 | 21 | 25 | 27 | 31 | 34 | 39 | 43 | 45 | 47 => true | _ => false end.

Definition wrapMT (MT : ty) : tm := bindU (bindG (bindL (tmTy MT))).
Definition wrapMt (Mt : ty) : tm := bindU (bindG (bindG (bindL (tmTy Mt)))).

(** The bundle built from its components: branch bodies [bs k], wrapped. *)
Fixpoint tup_from (f : nat -> tm) (k n : nat) : tm :=
  match n with 0 => tmErr | S n => tmTup (f k) (tup_from f (S k) n) end.
Definition mkrb (MT Mt : ty) (bs : nat -> tm) : tm :=
  tmTup (wrapMT MT) (tmTup (wrapMt Mt)
    (tup_from (fun k => let '(nu, ng, nl) := br_ar k in wrap nu ng nl (bs k)) 0 nbr)).

(** [mkrb] is injective. Proved through [tup_nth] and the wrappers'
    injectivity: [injection] on two [mkrb]s unfolds the whole block, which
    cost seconds per use (and as much again at [Qed]). *)
Lemma tup_nth_from f i n j : j < n -> tup_nth (tup_from f i n) j = f (i + j).
Proof.
  revert i j; induction n as [|n IH]; intros i [|j] Hj; cbn [tup_from tup_nth].
  1, 2: exfalso; inversion Hj.
  - now rewrite Nat.add_0_r.
  - rewrite IH by (apply PeanoNat.lt_S_n, Hj). now rewrite Nat.add_succ_r.
Qed.
Lemma wrapU_inj n b b' : wrapU n b = wrapU n b' -> b = b'.
Proof. induction n; cbn [wrapU]; intros H; [exact H | injection H; auto]. Qed.
Lemma wrapG_inj n b b' : wrapG n b = wrapG n b' -> b = b'.
Proof. induction n; cbn [wrapG]; intros H; [exact H | injection H; auto]. Qed.
Lemma wrapL_inj n b b' : wrapL n b = wrapL n b' -> b = b'.
Proof. induction n; cbn [wrapL]; intros H; [exact H | injection H; auto]. Qed.
Lemma wrap_inj nu ng nl b b' : wrap nu ng nl b = wrap nu ng nl b' -> b = b'.
Proof. unfold wrap; intros H; apply wrapU_inj, wrapG_inj, wrapL_inj in H; exact H. Qed.

Lemma mkrb_inj {MT Mt bs MT' Mt' bs'} : mkrb MT Mt bs = mkrb MT' Mt' bs' ->
  MT = MT' /\ Mt = Mt' /\ forall k, k < nbr -> bs k = bs' k.
Proof.
  intros H; split; [|split].
  - pose proof (f_equal (fun t => tup_nth t 0) H) as E; cbn [tup_nth mkrb wrapMT] in E.
    injection E as E; exact E.
  - pose proof (f_equal (fun t => tup_nth t 1) H) as E; cbn [tup_nth mkrb wrapMt] in E.
    injection E as E; exact E.
  - intros k Hk. pose proof (f_equal (fun t => tup_nth t (S (S k))) H) as E.
    cbn [tup_nth mkrb] in E. rewrite !tup_nth_from in E by exact Hk. cbv beta in E.
    destruct (br_ar (0 + k)) as [[nu ng] nl]. exact (wrap_inj _ _ _ _ _ E).
Qed.

Definition rb_br (rb : tm) (k : nat) : tm := tup_nth rb (2 + k).

(** ** Peeling one binder *)

Definition peelU (b : tm) (l : lvl) : tm :=
  match b with bindU b => usubst_tm b (usingle l) | _ => tmErr end.
Definition peelG (b : tm) (o : gobj) : tm :=
  match b with bindG b => gsubst_tm b (gsingle o) | _ => tmErr end.
Definition peelL (b : tm) (a : tm) : tm :=
  match b with bindL b => subst_tm b (lsingle a) | _ => tmErr end.

(** ** β reducts

    Recursive calls are recursors on the sub-structures, with the levels,
    contexts and indices the paper's premises give them (04:1146–1300). *)

Section Reducts.
Context (l1 l2 : lvl) (rb : tm).

Definition recT (l : lvl) (Δ : ctx) (c : ty) : tm := elimT l1 l2 rb l Δ (boxT c).
Definition rect (l : lvl) (Δ : ctx) (T : ty) (c : tm) : tm := elimt l1 l2 rb l Δ T (boxt c).

Definition redT (l : lvl) (Δ : ctx) (c : ty) : option tm :=
  match c with
  | tyNat => Some (peelG (rb_br rb bNat) (GCtx Δ))
  | tyPi k k' A B =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bPi) k) k')
              (GCtx Δ)) (GTy A)) (GTy B))
              (recT k Δ A)) (recT k' (cext Δ A k) B))
  | tyU k => Some (peelG (peelU (rb_br rb bU) k) (GCtx Δ))
  | tyEl k t =>
      Some (peelL (peelG (peelG (peelU (rb_br rb bEl) k) (GCtx Δ)) (GTm t))
              (rect (lsuc k) Δ (tyU k) t))
  | tySig k k' A B =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bSig) k) k')
              (GCtx Δ)) (GTy A)) (GTy B))
              (recT k Δ A)) (recT k' (cext Δ A k) B))
  | tyUnit k => Some (peelG (peelU (rb_br rb bUnit) k) (GCtx Δ))
  | tyId k A a b =>
      Some (peelL (peelL (peelL (peelG (peelG (peelG (peelG (peelU (rb_br rb bId) k)
              (GCtx Δ)) (GTy A)) (GTm a)) (GTm b))
              (recT k Δ A)) (rect k Δ A a)) (rect k Δ A b))
  | tySEq k A a b =>
      Some (peelL (peelL (peelL (peelG (peelG (peelG (peelG (peelU (rb_br rb bSEq) k)
              (GCtx Δ)) (GTy A)) (GTm a)) (GTm b))
              (recT k Δ A)) (rect k Δ A a)) (rect k Δ A b))
  | tySEmpty k => Some (peelG (peelU (rb_br rb bSEmpty) k) (GCtx Δ))
  | tyEmpty k => Some (peelG (peelU (rb_br rb bEmpty) k) (GCtx Δ))
  | tySum k k' A B =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bSum) k) k')
              (GCtx Δ)) (GTy A)) (GTy B))
              (recT k Δ A)) (recT k' Δ B))
  (* W-types (M13b), as [Σ] *)
  | tyW k k' A B =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bW) k) k')
              (GCtx Δ)) (GTy A)) (GTy B))
              (recT k Δ A)) (recT k' (cext Δ A k) B))
  (* length-indexed tuples and finite indices (M14b): the length's call
     is a term call at [Nat] *)
  | tyVec k A n =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (rb_br rb bVec) k)
              (GCtx Δ)) (GTy A)) (GTm n))
              (recT k Δ A)) (rect lzero Δ tyNat n))
  | tyFin n =>
      Some (peelL (peelG (peelG (rb_br rb bFin) (GCtx Δ)) (GTm n)) (rect lzero Δ tyNat n))
  (* finitary well-founded trees (M15b): the arity's call is a term call at
     [Nat] under the shape *)
  | tyWf k A N =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (rb_br rb bWf) k)
              (GCtx Δ)) (GTy A)) (GTm N))
              (recT k Δ A)) (rect lzero (cext Δ A k) tyNat N))
  | _ => None
  end.

(** [T] is the recursor's index; only the [λ] case reads it (its codomain
    is not stored in the code, 04:1273). *)
Definition redt (l : lvl) (Δ : ctx) (T : ty) (c : tm) : option tm :=
  match c with
  | var n =>
      Some (peelG (peelG (peelG (peelU (rb_br rb bVar) l) (GCtx Δ)) (GTy T)) (GTm (var n)))
  | tmNat => Some (peelG (rb_br rb bNat') (GCtx Δ))
  | tmPi k k' s t =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bPi') k) k')
              (GCtx Δ)) (GTm s)) (GTm t))
              (rect (lsuc k) Δ (tyU k) s)) (rect (lsuc k') (cext Δ (tyEl k s) k) (tyU k') t))
  | tmU k => Some (peelG (peelU (rb_br rb bU') k) (GCtx Δ))
  | zero => Some (peelG (rb_br rb bZero) (GCtx Δ))
  | succ t =>
      Some (peelL (peelG (peelG (rb_br rb bSucc) (GCtx Δ)) (GTm t)) (rect lzero Δ tyNat t))
  | natrec k M s z t =>
      Some (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelU (rb_br rb bNatrec) k)
                 (GCtx Δ)) (GTy M)) (GTm s)) (GTm z)) (GTm t))
              (recT k (cext Δ tyNat lzero) M))
              (rect k Δ (subst_ty M (lsingle zero)) s))
              (rect k (cext (cext Δ tyNat lzero) M k) (subst_ty M lsucc) z))
              (rect lzero Δ tyNat t))
  | lam k k' A b =>
      match T with
      | tyPi _ _ _ B =>
          Some (peelL (peelL (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bLam) k) k')
                  (GCtx Δ)) (GTy A)) (GTy B)) (GTm b))
                  (recT k Δ A)) (rect k' (cext Δ A k) B b))
      | _ => None
      end
  | app f k k' A B a =>
      Some (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bApp) k) k')
                 (GCtx Δ)) (GTy A)) (GTy B)) (GTm f)) (GTm a))
              (recT k Δ A))
              (recT k' (cext Δ A k) B))
              (rect (lmax k k') Δ (tyPi k k' A B) f))
              (rect k Δ A a))
  | tmSig k k' s t =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bSig') k) k')
              (GCtx Δ)) (GTm s)) (GTm t))
              (rect (lsuc k) Δ (tyU k) s)) (rect (lsuc k') (cext Δ (tyEl k s) k) (tyU k') t))
  | tmPair k k' A B a b =>
      Some (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bPair) k) k')
                 (GCtx Δ)) (GTy A)) (GTy B)) (GTm a)) (GTm b))
              (recT k Δ A))
              (recT k' (cext Δ A k) B))
              (rect k Δ A a))
              (rect k' Δ (subst_ty B (lsingle a)) b))
  | tmFst k k' A B p =>
      Some (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bFst) k) k')
                 (GCtx Δ)) (GTy A)) (GTy B)) (GTm p))
              (recT k Δ A))
              (recT k' (cext Δ A k) B))
              (rect (lmax k k') Δ (tySig k k' A B) p))
  | tmSnd k k' A B p =>
      Some (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bSnd) k) k')
                 (GCtx Δ)) (GTy A)) (GTy B)) (GTm p))
              (recT k Δ A))
              (recT k' (cext Δ A k) B))
              (rect (lmax k k') Δ (tySig k k' A B) p))
  | tmUnit k => Some (peelG (peelU (rb_br rb bUnit') k) (GCtx Δ))
  | tmTriv k => Some (peelG (peelU (rb_br rb bTriv) k) (GCtx Δ))
  | tmId k s t u =>
      Some (peelL (peelL (peelL (peelG (peelG (peelG (peelG (peelU (rb_br rb bId') k)
              (GCtx Δ)) (GTm s)) (GTm t)) (GTm u))
              (rect (lsuc k) Δ (tyU k) s)) (rect k Δ (tyEl k s) t)) (rect k Δ (tyEl k s) u))
  | tmRefl k A a =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (rb_br rb bRefl) k)
              (GCtx Δ)) (GTy A)) (GTm a))
              (recT k Δ A)) (rect k Δ A a))
  | tmJ k k' A a M c u e =>
      Some (peelL (peelL (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bJ) k) k')
                 (GCtx Δ)) (GTy A)) (GTm a)) (GTy M)) (GTm c)) (GTm u)) (GTm e))
              (recT k Δ A))
              (rect k Δ A a))
              (recT k' (cext (cext Δ A k) (tyId k A⟨↑⟩ a⟨↑⟩ (var 0)) k) M))
              (rect k' Δ (subst_ty M (lsingle2 a (tmRefl k A a))) c))
              (rect k Δ A u))
              (rect k Δ (tyId k A a u) e))
  | tmSEq k s t u =>
      Some (peelL (peelL (peelL (peelG (peelG (peelG (peelG (peelU (rb_br rb bSEq') k)
              (GCtx Δ)) (GTm s)) (GTm t)) (GTm u))
              (rect (lsuc k) Δ (tyU k) s)) (rect k Δ (tyEl k s) t)) (rect k Δ (tyEl k s) u))
  | tmSEmpty k => Some (peelG (peelU (rb_br rb bSEmpty') k) (GCtx Δ))
  | srefl k A a =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (rb_br rb bSrefl) k)
              (GCtx Δ)) (GTy A)) (GTm a))
              (recT k Δ A)) (rect k Δ A a))
  (* the motive's level is the branch's first, as in Heather's [t_elim_sE] *)
  | elimSEmpty k k' M e =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bElimSEmpty) k') k)
              (GCtx Δ)) (GTy M)) (GTm e))
              (recT k' Δ M)) (rect k Δ (tySEmpty k) e))
  (* the empty type and binary sums (M12c) *)
  | tmEmpty k => Some (peelG (peelU (rb_br rb bEmpty') k) (GCtx Δ))
  (* the motive's level first, as [elimEmpty]'s and Heather's [t_elimE] *)
  | elimEmpty k k' M t =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bElimEmpty) k) k')
              (GCtx Δ)) (GTy M)) (GTm t))
              (recT k (cext Δ (tyEmpty k') k') M)) (rect k' Δ (tyEmpty k') t))
  | tmSum k k' s t =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bSum') k) k')
              (GCtx Δ)) (GTm s)) (GTm t))
              (rect (lsuc k) Δ (tyU k) s)) (rect (lsuc k') Δ (tyU k') t))
  | tmInl k k' A B a =>
      Some (peelL (peelL (peelL (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bInl) k) k')
              (GCtx Δ)) (GTy A)) (GTy B)) (GTm a))
              (recT k Δ A)) (recT k' Δ B)) (rect k Δ A a))
  | tmInr k k' A B b =>
      Some (peelL (peelL (peelL (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bInr) k) k')
              (GCtx Δ)) (GTy A)) (GTy B)) (GTm b))
              (recT k Δ A)) (recT k' Δ B)) (rect k' Δ B b))
  | tmCase k k' k'' A B M c1 c2 t =>
      Some (peelL (peelL (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelG (peelG
                 (peelU (peelU (peelU (rb_br rb bCase) k) k') k'')
                 (GCtx Δ)) (GTy A)) (GTy B)) (GTy M)) (GTm c1)) (GTm c2)) (GTm t))
              (recT k Δ A))
              (recT k' Δ B))
              (recT k'' (cext Δ (tySum k k' A B) (lmax k k')) M))
              (rect k'' (cext Δ A k) (subst_ty M⟨rlift ↑⟩ (lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0)))) c1))
              (rect k'' (cext Δ B k') (subst_ty M⟨rlift ↑⟩ (lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0)))) c2))
              (rect (lmax k k') Δ (tySum k k' A B) t))
  (* W-types (M13b) *)
  | tmW k k' s t =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (peelU (rb_br rb bW') k) k')
              (GCtx Δ)) (GTm s)) (GTm t))
              (rect (lsuc k) Δ (tyU k) s)) (rect (lsuc k') (cext Δ (tyEl k s) k) (tyU k') t))
  | tmSup k k' A B a f =>
      Some (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelU (peelU (rb_br rb bSup) k) k')
                 (GCtx Δ)) (GTy A)) (GTy B)) (GTm a)) (GTm f))
              (recT k Δ A))
              (recT k' (cext Δ A k) B))
              (rect k Δ A a))
              (rect (lmax k' (lmax k k')) Δ (tyPi k' (lmax k k') (subst_ty B (lsingle a)) (tyW k k' A B)⟨↑⟩) f))
  | tmElimW k k' k'' A B M c t =>
      Some (peelL (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelG
                 (peelU (peelU (peelU (rb_br rb bElimW) k) k') k'')
                 (GCtx Δ)) (GTy A)) (GTy B)) (GTy M)) (GTm c)) (GTm t))
              (recT k Δ A))
              (recT k' (cext Δ A k) B))
              (recT k'' (cext Δ (tyW k k' A B) (lmax k k')) M))
              (rect k'' (cext (cext (cext Δ A k) (wfty k k' A B) (lmax k' (lmax k k')))
                 (wihty k k' k'' A B M) (lmax k' k'')) (wstepty k k' A B M) c))
              (rect (lmax k k') Δ (tyW k k' A B) t))
  (* the codes of [Vec] and [Fin] (M14b) *)
  | tmVec k s n =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (rb_br rb bVec') k)
              (GCtx Δ)) (GTm s)) (GTm n))
              (rect (lsuc k) Δ (tyU k) s)) (rect lzero Δ tyNat n))
  | tmFin n =>
      Some (peelL (peelG (peelG (rb_br rb bFin') (GCtx Δ)) (GTm n)) (rect lzero Δ tyNat n))
  (* finitary well-founded trees (M15b) *)
  | tmWf k s n =>
      Some (peelL (peelL (peelG (peelG (peelG (peelU (rb_br rb bWf') k)
              (GCtx Δ)) (GTm s)) (GTm n))
              (rect (lsuc k) Δ (tyU k) s)) (rect lzero (cext Δ (tyEl k s) k) tyNat n))
  | tmSupf k A N a cs =>
      Some (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelU (rb_br rb bSupf) k)
                 (GCtx Δ)) (GTy A)) (GTm N)) (GTm a)) (GTm cs))
              (recT k Δ A))
              (rect lzero (cext Δ A k) tyNat N))
              (rect k Δ A a))
              (rect k Δ (tyVec k (tyWf k A N) (subst_tm N (lsingle a))) cs))
  | tmElimWf k k' A N M c t =>
      Some (peelL (peelL (peelL (peelL (peelL
              (peelG (peelG (peelG (peelG (peelG (peelG
                 (peelU (peelU (rb_br rb bElimWf) k) k')
                 (GCtx Δ)) (GTy A)) (GTm N)) (GTy M)) (GTm c)) (GTm t))
              (recT k Δ A))
              (rect lzero (cext Δ A k) tyNat N))
              (recT k' (cext Δ (tyWf k A N) k) M))
              (rect k' (cext (cext (cext Δ A k) (wfcsty k A N) k) (wfihty k k' A N M) (lmax lzero k'))
                 (wfstepty k A N M) c))
              (rect k Δ (tyWf k A N) t))
  | _ => None
  end.

End Reducts.

(** Read a reduct off [redT … = Some r]. [injection] (and [inversion])
    would build a projection whose default value is a copy of the whole
    unfolded reduct, which then dominates the proof and its [Qed]. *)
Lemma Some_inj {A} {a b : A} : Some a = Some b -> a = b.
Proof. now intros [= ->]. Qed.

(** Case on [redt]'s index where it is read (the λ case), after [cbn [redt]]:
    a blanket [destruct c; destruct T] is quadratic in the formers. *)
Ltac redt_case T := try lazymatch goal with
  | |- context [match T with _ => _ end] => destruct T; cbn beta iota
  | H : context [match T with _ => _ end] |- _ => destruct T; cbn beta iota in H
  end.
