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
From DeLaM.Syntax Require Export Universe.

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
Notation nbr := 21 (only parsing).
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
  | _ => (0, 0, 0)
  end.

(** Whether branch [k] is a type branch (typed at [l₁], recursing on
    [elim_Typ]) or a term branch. *)
Definition br_isT (k : nat) : bool :=
  match k with 0 | 1 | 2 | 3 | 13 | 14 => true | _ => false end.

Definition wrapMT (MT : ty) : tm := bindU (bindG (bindL (tmTy MT))).
Definition wrapMt (Mt : ty) : tm := bindU (bindG (bindG (bindL (tmTy Mt)))).

(** The bundle built from its components: branch bodies [bs k], wrapped. *)
Fixpoint tup_from (f : nat -> tm) (k n : nat) : tm :=
  match n with 0 => tmErr | S n => tmTup (f k) (tup_from f (S k) n) end.
Definition mkrb (MT Mt : ty) (bs : nat -> tm) : tm :=
  tmTup (wrapMT MT) (tmTup (wrapMt Mt)
    (tup_from (fun k => let '(nu, ng, nl) := br_ar k in wrap nu ng nl (bs k)) 0 nbr)).

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
  | _ => None
  end.

End Reducts.

(** Case on [redt]'s index where it is read (the λ case), after [cbn [redt]]:
    a blanket [destruct c; destruct T] is quadratic in the formers. *)
Ltac redt_case T := try lazymatch goal with
  | |- context [match T with _ => _ end] => destruct T; cbn beta iota
  | H : context [match T with _ => _ end] |- _ => destruct T; cbn beta iota in H
  end.
