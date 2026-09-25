(** * The recursor bundle and the β reducts of the code recursors (M3)

    [elim_Typ^{l₁,l₂} M⃗ b⃗ l Δ t] and [elim_Trm^{l₁,l₂} M⃗ b⃗ l Δ T t]
    (04:816) carry a bundle [rb] of two motives and 13 branches
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

(** Branch indices, in the paper's order (04:822–831). *)
Definition bNat := 0.   Definition bPi := 1.    Definition bU := 2.     Definition bEl := 3.
Definition bVar := 4.   Definition bNat' := 5.  Definition bPi' := 6.   Definition bU' := 7.
Definition bZero := 8.  Definition bSucc := 9.  Definition bNatrec := 10.
Definition bLam := 11.  Definition bApp := 12.

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
  | _ => (0, 0, 0)
  end.

Definition wrapMT (MT : ty) : tm := bindU (bindG (bindL (tmTy MT))).
Definition wrapMt (Mt : ty) : tm := bindU (bindG (bindG (bindL (tmTy Mt)))).

(** The bundle built from its components: branch bodies [bs k], wrapped. *)
Fixpoint tup_from (f : nat -> tm) (k n : nat) : tm :=
  match n with 0 => tmErr | S n => tmTup (f k) (tup_from f (S k) n) end.
Definition mkrb (MT Mt : ty) (bs : nat -> tm) : tm :=
  tmTup (wrapMT MT) (tmTup (wrapMt Mt)
    (tup_from (fun k => let '(nu, ng, nl) := br_ar k in wrap nu ng nl (bs k)) 0 13)).

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
  | _ => None
  end.

End Reducts.

(** ** Recursor-free syntax (M3_DESIGN.md E8) *)

Fixpoint norec_ty (T : ty) : Prop :=
  match T with
  | tyErr | tyNat | tyU _ => True
  | tyPi _ _ A B => norec_ty A /\ norec_ty B
  | tyEl _ t => norec_tm t
  | tyGvar _ d => norec_l d
  | tyCTyp Δ _ => norec_ctx Δ
  | tyCTrm Δ T _ => norec_ctx Δ /\ norec_ty T
  end
with norec_tm (t : tm) : Prop :=
  match t with
  | var _ | tmErr | tmNat | tmU _ | zero => True
  | tmPi _ _ s t => norec_tm s /\ norec_tm t
  | succ t => norec_tm t
  | natrec _ M s z t => norec_ty M /\ norec_tm s /\ norec_tm z /\ norec_tm t
  | lam _ _ A t => norec_ty A /\ norec_tm t
  | app t _ _ A B s => norec_tm t /\ norec_ty A /\ norec_ty B /\ norec_tm s
  | gvar _ d => norec_l d
  | boxT T => norec_ty T
  | boxt t => norec_tm t
  | letboxT _ _ Δ M t' t => norec_ctx Δ /\ norec_ty M /\ norec_tm t' /\ norec_tm t
  | letboxt _ _ Δ T M t' t => norec_ctx Δ /\ norec_ty T /\ norec_ty M /\ norec_tm t' /\ norec_tm t
  | tmTy T => norec_ty T
  | tmTup s t => norec_tm s /\ norec_tm t
  | bindU b | bindG b | bindL b => norec_tm b
  | elimT _ _ _ _ _ _ | elimt _ _ _ _ _ _ _ => False
  end
with norec_ctx (Γ : ctx) : Prop :=
  match Γ with cnil | cvar _ => True | cext Γ A _ => norec_ctx Γ /\ norec_ty A end
with norec_l (d : lsub) : Prop :=
  match d with lshift _ => True | lcons d t => norec_l d /\ norec_tm t end.

Lemma norec_llk d n : norec_l d -> norec_tm (llk d n).
Proof. revert n; induction d as [k|d IH t]; intros [|n] H; cbn in *; try tauto; apply IH; tauto. Qed.
