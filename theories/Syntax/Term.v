(** * Syntax of DeLaM: the MLTT fragment, Tarski-style (ch. 4 §"Syntax")

    Types [ty] and terms [tm] are separate.  Terms contain the type codes
    [tmNat], [tmPi], [tmU], decoded by [tyEl].  Constructs carry the level
    and type annotations the paper puts on them (needed later by the
    recursion principle for code).

    Local variables are de Bruijn.  A local substitution [lsub] is a finite
    cons-list ending in a shift (see SYNTAX_SPIKE.md): it is stored inside
    [u^δ] / [U^δ].  Contexts are syntax (they may end in a context variable
    [g]) and are never traversed by local operations.

    Modal formers are added by later milestones as additional constructors. *)
From Coq Require Import Arith Lia.
From DeLaM.Syntax Require Export Level.

(** ** Syntax *)

Inductive ty : Type :=
| tyErr                                   (* junk: ill-sorted global lookup *)
| tyNat
| tyPi (l l' : lvl) (A : ty) (B : ty)     (* Π^{l,l'} x:A. B      B: +1 *)
| tyU (l : lvl)                           (* Ty l *)
| tyEl (l : lvl) (t : tm)                 (* El l t *)
| tyGvar (U : nat) (d : lsub)             (* U^δ *)
| tyCTyp (Δ : ctx) (l : lvl)              (* □(Δ ⊢ @l): code of types *)
| tyCTrm (Δ : ctx) (T : ty) (l : lvl)     (* □(Δ ⊢ T @l): code of terms; T in Δ *)
| tyUPi (n : nat) (l : lvl) (T : ty)      (* UΠ ℓ⃗. T @ l, |ℓ⃗| = n   l, T: +n levels *)
(* meta-functions (M5): the body binds one global variable *)
| tyCPi (l : lvl) (T : ty)                (* CΠ g. T @ l,  g : Ctx        T: +1 global *)
| tyTPi (Δ : ctx) (l l' : lvl) (T : ty)   (* TΠ U[Δ]. T @ l', U : (Δ ⊢_P @l)   T: +1 global *)
(* dependent pairs (M8) *)
| tySig (l l' : lvl) (A : ty) (B : ty)    (* Σ^{l,l'} x:A. B      B: +1 *)
(* the unit type (M8c), level-indexed *)
| tyUnit (l : lvl)                        (* Unit^l @ l *)
(* strict equality and the irrelevant empty type (M10a), level-indexed *)
| tySEq (l : lvl) (A : ty) (a b : tm)     (* sEq^l(A; a; b) @ l *)
| tySEmpty (l : lvl)                      (* sEmpty^l @ l *)
(* the identity type (M11a), at the carrier's level *)
| tyId (l : lvl) (A : ty) (a b : tm)      (* Id^l(A; a; b) @ l *)
(* the empty type (M12a), level-indexed *)
| tyEmpty (l : lvl)                       (* Empty^l @ l *)
(* binary sums (M12b), non-dependent *)
| tySum (l l' : lvl) (A B : ty)           (* A +^{l,l'} B @ l ⊔ l' *)
(* well-founded trees (M13a): shapes [A], positions [B] at each shape *)
| tyW (l l' : lvl) (A B : ty)             (* W^{l,l'}(x : A). B @ l ⊔ l'      B: +1 *)
with tm : Type :=
| var (n : nat)
| tmErr
| tmNat
| tmPi (l l' : lvl) (s : tm) (t : tm)     (* code of Π           t: +1 *)
| tmU (l : lvl)                           (* code of Ty l *)
| zero
| succ (t : tm)
| natrec (l : lvl) (M : ty) (s z : tm) (t : tm)
    (* elimN^l (x.M) s (x,y.z) t          M: +1, z: +2 *)
| lam (l l' : lvl) (A : ty) (t : tm)      (* λ^{l,l'} x:A. t      t: +1 *)
| app (t : tm) (l l' : lvl) (A : ty) (B : ty) (s : tm)
    (* t ^{l,l'}_{x:A.B} s                B: +1 *)
| gvar (u : nat) (d : lsub)               (* u^δ *)
| boxT (T : ty)                           (* box T: own local scope *)
| boxt (t : tm)                           (* box t: own local scope *)
| letboxT (l' l : lvl) (Δ : ctx) (M : ty) (t' : tm) (t : tm)
    (* letbox_Typ^{l',l}_Δ (x_T.M) (U.t') t   M: +1 local, t': +1 global *)
| letboxt (l' l : lvl) (Δ : ctx) (T : ty) (M : ty) (t' : tm) (t : tm)
    (* letbox_Trm^{l',l}_Δ T (x_t.M) (u.t') t  T in Δ; M: +1 local, t': +1 global *)
(* The recursor bundle (M3_DESIGN E2): junk nodes, never typed on their own *)
| tmTy (T : ty)                           (* a type (motive) inside the bundle *)
| tmTup (s t : tm)                        (* pairing *)
| bindU (b : tm)                          (* binds one level variable *)
| bindG (b : tm)                          (* binds one global variable *)
| bindL (b : tm)                          (* binds one local variable *)
(* the recursors on code; [rb] bundles the two motives and [nbr] branches *)
| elimT (l1 l2 : lvl) (rb : tm) (l : lvl) (Δ : ctx) (t : tm)
    (* elim_Typ^{l1,l2} M⃗ b⃗ l Δ t *)
| elimt (l1 l2 : lvl) (rb : tm) (l : lvl) (Δ : ctx) (T : ty) (t : tm)
    (* elim_Trm^{l1,l2} M⃗ b⃗ l Δ T t        T in Δ *)
(* universe polymorphism (M4) *)
| ulam (n : nat) (l : lvl) (T : ty) (t : tm)  (* Λ^l ℓ⃗. t : T, |ℓ⃗| = n   l, T, t: +n levels *)
| uapp (t : tm) (ls : list lvl)           (* t $ l⃗ *)
(* meta-functions (M5) *)
| clam (l : lvl) (T : ty) (t : tm)        (* Λ^l g. t : T             T, t: +1 global *)
| capp (t : tm) (Δ : ctx)                 (* t Δ *)
| tlam (Δ : ctx) (l l' : lvl) (T : ty) (t : tm)  (* Λ^{l,l'} U[Δ]. t : T   T, t: +1 global *)
| tapp (t : tm) (T : ty)                  (* t T                      T in U's context *)
(* dependent pairs (M8), annotated as [app] *)
| tmSig (l l' : lvl) (s : tm) (t : tm)    (* code of Σ           t: +1 *)
| tmPair (l l' : lvl) (A : ty) (B : ty) (a b : tm)  (* (a, b)^{l,l'}_{x:A.B}   B: +1 *)
| tmFst (l l' : lvl) (A : ty) (B : ty) (p : tm)     (* fst^{l,l'}_{x:A.B} p     B: +1 *)
| tmSnd (l l' : lvl) (A : ty) (B : ty) (p : tm)     (* snd^{l,l'}_{x:A.B} p     B: +1 *)
(* the unit type (M8c) *)
| tmUnit (l : lvl)                        (* code of Unit^l : Ty l *)
| tmTriv (l : lvl)                        (* ⟨⟩^l : Unit^l *)
(* strict equality (M10a) *)
| srefl (l : lvl) (A : ty) (a : tm)       (* srefl^l(A; a) : sEq^l(A; a; a) *)
| elimSEmpty (l l' : lvl) (M : ty) (e : tm)  (* elim_sEmpty^{l,l'}(M; e) : M, e : sEmpty^l *)
(* the identity type (M11a): refl, and based path induction *)
| tmRefl (l : lvl) (A : ty) (a : tm)      (* refl^l(A; a) : Id^l(A; a; a) *)
| tmId (l : lvl) (s t u : tm)            (* code of Id^l(El s; t; u) : Ty l (M11b) *)
| tmSEq (l : lvl) (s t u : tm)           (* code of sEq^l(El s; t; u) : Ty l (M10c) *)
| tmSEmpty (l : lvl)                     (* code of sEmpty^l : Ty l (M10c) *)
| tmEmpty (l : lvl)                      (* code of Empty^l : Ty l (M12c) *)
| tmSum (l l' : lvl) (s t : tm)          (* code of s + t : Ty (l ⊔ l') (M12c) *)
| tmW (l l' : lvl) (s t : tm)            (* code of W(x : El s). El t : Ty (l ⊔ l') (M13b)   t: +1 *)
(* the empty type's eliminator (M12a): the motive's level first *)
| elimEmpty (l l' : lvl) (M : ty) (t : tm)
    (* elim_Empty^{l,l'}(x. M; t) : M[t/x] @ l, t : Empty^{l'}      M: +1 *)
(* binary sums (M12b): the injections carry both summands *)
| tmInl (l l' : lvl) (A B : ty) (a : tm)  (* inl^{l,l'}(A; B; a) *)
| tmInr (l l' : lvl) (A B : ty) (b : tm)  (* inr^{l,l'}(A; B; b) *)
| tmCase (l l' l'' : lvl) (A B : ty) (M : ty) (cl cr t : tm)
    (* case^{l,l',l''}(A; B; z. M; x. cl; y. cr; t) : M[t/z] @ l''      M, cl, cr: +1 *)
(* well-founded trees (M13a): [sup] carries the shapes and positions; the
   eliminator's step binds the shape [a], the children [f] and the induction
   hypothesis [ih], innermost last *)
| tmSup (l l' : lvl) (A B : ty) (a f : tm)
    (* sup^{l,l'}(x : A. B; a; f)      B: +1 *)
| tmElimW (l l' l'' : lvl) (A B : ty) (M : ty) (c t : tm)
    (* elim_W^{l,l',l''}(x : A. B; z. M; a f ih. c; t) : M[t/z] @ l''      B, M: +1, c: +3 *)
| tmJ (l l' : lvl) (A : ty) (a : tm) (M : ty) (c u e : tm)
    (* J^{l,l'}(A; a; y p. M; c; u; e) : M[u/y, e/p]      M: +2 (y, then p) *)
(* a defined global u^δ carrying its body t (M9_DESIGN.md, fork (b)); t lives in
   the definition's local context, so local operations leave it alone *)
| gdef (u : nat) (t : tm) (d : lsub)
with ctx : Type :=
| cnil
| cvar (g : nat)
| cext (G : ctx) (T : ty) (l : lvl)       (* Γ, x : T @ l *)
with lsub : Type :=
| lshift (k : nat)
| lcons (d : lsub) (t : tm).

Scheme ty_ind' := Induction for ty Sort Prop
  with tm_ind' := Induction for tm Sort Prop
  with ctx_ind' := Induction for ctx Sort Prop
  with lsub_ind' := Induction for lsub Sort Prop.
Combined Scheme syn_ind from ty_ind', tm_ind', ctx_ind', lsub_ind'.

(** ** Renamings (entries are indices) *)

Inductive rsub : Type := rshift (k : nat) | rcons (r : rsub) (n : nat).

Fixpoint rlk (r : rsub) (n : nat) : nat :=
  match r with
  | rshift k => n + k
  | rcons r m => match n with 0 => m | S n => rlk r n end
  end.

Fixpoint rdrop (k : nat) (r : rsub) : rsub :=
  match k, r with
  | 0, r => r
  | S k, rcons r _ => rdrop k r
  | S k, rshift m => rshift (S k + m)
  end.

Fixpoint rup (r : rsub) : rsub :=                   (* r ; ↑ *)
  match r with rshift k => rshift (S k) | rcons r m => rcons (rup r) (S m) end.

Definition rlift (r : rsub) : rsub := rcons (rup r) 0.
Definition rshift1 : rsub := rshift 1.

(** ** Local substitutions: lookup, canonicalising constructor, drop *)

Fixpoint llk (d : lsub) (n : nat) : tm :=
  match d with
  | lshift k => var (n + k)
  | lcons d t => match n with 0 => t | S n => llk d n end
  end.

(** Absorbs a redundant trailing variable, so that operation outputs are
    canonical: normal local substitutions are equal iff their lookups are. *)
Definition lcons' (d : lsub) (t : tm) : lsub :=
  match d, t with
  | lshift (S k), var m => if Nat.eqb m k then lshift k else lcons d t
  | _, _ => lcons d t
  end.

Fixpoint lnorm (d : lsub) : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (lnorm d) t end.

Fixpoint ldrop (k : nat) (d : lsub) : lsub :=
  match k, d with
  | 0, d => d
  | S k, lcons d _ => ldrop k d
  | S k, lshift m => lshift (S k + m)
  end.

Fixpoint r2l (r : rsub) : lsub :=
  match r with rshift k => lshift k | rcons r m => lcons' (r2l r) (var m) end.

(** ** Local renaming *)

Fixpoint ren_ty (T : ty) (r : rsub) {struct T} : ty :=
  match T with
  | tyErr => tyErr | tyNat => tyNat
  | tyPi l l' A B => tyPi l l' (ren_ty A r) (ren_ty B (rlift r))
  | tyU l => tyU l
  | tyEl l t => tyEl l (ren_tm t r)
  | tyGvar U d => tyGvar U (lren d r)
  | tyCTyp Δ l => tyCTyp Δ l
  | tyCTrm Δ T l => tyCTrm Δ T l
  | tyUPi n l T => tyUPi n l (ren_ty T r)
  | tyCPi l T => tyCPi l (ren_ty T r)
  | tyTPi Δ l l' T => tyTPi Δ l l' (ren_ty T r)
  | tySig l l' A B => tySig l l' (ren_ty A r) (ren_ty B (rlift r))
  | tyUnit l => tyUnit l
  | tySEq l A a b => tySEq l (ren_ty A r) (ren_tm a r) (ren_tm b r)
  | tySEmpty l => tySEmpty l
  | tyId l A a b => tyId l (ren_ty A r) (ren_tm a r) (ren_tm b r)
  | tyEmpty l => tyEmpty l
  | tySum l l' A B => tySum l l' (ren_ty A r) (ren_ty B r)
  | tyW l l' A B => tyW l l' (ren_ty A r) (ren_ty B (rlift r))
  end
with ren_tm (t : tm) (r : rsub) {struct t} : tm :=
  match t with
  | var n => var (rlk r n)
  | tmErr => tmErr | tmNat => tmNat | tmU l => tmU l | zero => zero
  | tmPi l l' s t => tmPi l l' (ren_tm s r) (ren_tm t (rlift r))
  | succ t => succ (ren_tm t r)
  | natrec l M s z t =>
      natrec l (ren_ty M (rlift r)) (ren_tm s r) (ren_tm z (rlift (rlift r))) (ren_tm t r)
  | lam l l' A t => lam l l' (ren_ty A r) (ren_tm t (rlift r))
  | app t l l' A B s => app (ren_tm t r) l l' (ren_ty A r) (ren_ty B (rlift r)) (ren_tm s r)
  | gvar u d => gvar u (lren d r)
  | boxT T => boxT T
  | boxt t => boxt t
  | letboxT l' l Δ M t' t => letboxT l' l Δ (ren_ty M (rlift r)) (ren_tm t' r) (ren_tm t r)
  | letboxt l' l Δ T M t' t => letboxt l' l Δ T (ren_ty M (rlift r)) (ren_tm t' r) (ren_tm t r)
  | tmTy T => tmTy (ren_ty T r)
  | tmTup s t => tmTup (ren_tm s r) (ren_tm t r)
  | bindU b => bindU (ren_tm b r)
  | bindG b => bindG (ren_tm b r)
  | bindL b => bindL (ren_tm b (rlift r))
  | elimT l1 l2 rb l Δ t => elimT l1 l2 (ren_tm rb r) l Δ (ren_tm t r)
  | elimt l1 l2 rb l Δ T t => elimt l1 l2 (ren_tm rb r) l Δ T (ren_tm t r)
  | ulam n l T t => ulam n l (ren_ty T r) (ren_tm t r)
  | uapp t ls => uapp (ren_tm t r) ls
  | clam l T t => clam l (ren_ty T r) (ren_tm t r)
  | capp t Δ => capp (ren_tm t r) Δ
  | tlam Δ l l' T t => tlam Δ l l' (ren_ty T r) (ren_tm t r)
  | tapp t T => tapp (ren_tm t r) T
  | tmSig l l' s t => tmSig l l' (ren_tm s r) (ren_tm t (rlift r))
  | tmPair l l' A B a b => tmPair l l' (ren_ty A r) (ren_ty B (rlift r)) (ren_tm a r) (ren_tm b r)
  | tmFst l l' A B p => tmFst l l' (ren_ty A r) (ren_ty B (rlift r)) (ren_tm p r)
  | tmSnd l l' A B p => tmSnd l l' (ren_ty A r) (ren_ty B (rlift r)) (ren_tm p r)
  | tmUnit l => tmUnit l
  | tmTriv l => tmTriv l
  | srefl l A a => srefl l (ren_ty A r) (ren_tm a r)
  | elimSEmpty l l' M e => elimSEmpty l l' (ren_ty M r) (ren_tm e r)
  | tmRefl l A a => tmRefl l (ren_ty A r) (ren_tm a r)
  | tmId l s t u => tmId l (ren_tm s r) (ren_tm t r) (ren_tm u r)
  | tmSEq l s t u => tmSEq l (ren_tm s r) (ren_tm t r) (ren_tm u r)
  | tmSEmpty l => tmSEmpty l
  | tmEmpty l => tmEmpty l
  | tmSum l l' s t => tmSum l l' (ren_tm s r) (ren_tm t r)
  | tmW l l' s t => tmW l l' (ren_tm s r) (ren_tm t (rlift r))
  | elimEmpty l l' M t => elimEmpty l l' (ren_ty M (rlift r)) (ren_tm t r)
  | tmInl l l' A B a => tmInl l l' (ren_ty A r) (ren_ty B r) (ren_tm a r)
  | tmInr l l' A B a => tmInr l l' (ren_ty A r) (ren_ty B r) (ren_tm a r)
  | tmCase l l' l'' A B M c1 c2 t =>
      tmCase l l' l'' (ren_ty A r) (ren_ty B r) (ren_ty M (rlift r)) (ren_tm c1 (rlift r)) (ren_tm c2 (rlift r)) (ren_tm t r)
  | tmSup l l' A B a f => tmSup l l' (ren_ty A r) (ren_ty B (rlift r)) (ren_tm a r) (ren_tm f r)
  | tmElimW l l' l'' A B M c t =>
      tmElimW l l' l'' (ren_ty A r) (ren_ty B (rlift r)) (ren_ty M (rlift r)) (ren_tm c (rlift (rlift (rlift r)))) (ren_tm t r)
  | tmJ l l' A a M c u e =>
      tmJ l l' (ren_ty A r) (ren_tm a r) (ren_ty M (rlift (rlift r))) (ren_tm c r) (ren_tm u r) (ren_tm e r)
  | gdef u b d => gdef u b (lren d r)
  end
with lren (d : lsub) (r : rsub) {struct d} : lsub :=
  match d with
  | lshift k => r2l (rdrop k r)
  | lcons d t => lcons' (lren d r) (ren_tm t r)
  end.

Definition llift (d : lsub) : lsub := lcons' (lren d rshift1) (var 0).

(** ** Global renaming

    Global variables are de Bruijn in one index space (the paper's single
    [Ψ]).  Local operations never touch the global dimension, except that
    a local substitution passing under a global binder must be globally
    shifted ([gwk]). *)

Definition gupr (ξ : nat -> nat) : nat -> nat :=
  fun n => match n with 0 => 0 | S n => S (ξ n) end.

Fixpoint gren_ty (T : ty) (ξ : nat -> nat) {struct T} : ty :=
  match T with
  | tyErr => tyErr | tyNat => tyNat
  | tyPi l l' A B => tyPi l l' (gren_ty A ξ) (gren_ty B ξ)
  | tyU l => tyU l
  | tyEl l t => tyEl l (gren_tm t ξ)
  | tyGvar U d => tyGvar (ξ U) (glren d ξ)
  | tyCTyp Δ l => tyCTyp (gcren Δ ξ) l
  | tyCTrm Δ T l => tyCTrm (gcren Δ ξ) (gren_ty T ξ) l
  | tyUPi n l T => tyUPi n l (gren_ty T ξ)
  | tyCPi l T => tyCPi l (gren_ty T (gupr ξ))
  | tyTPi Δ l l' T => tyTPi (gcren Δ ξ) l l' (gren_ty T (gupr ξ))
  | tySig l l' A B => tySig l l' (gren_ty A ξ) (gren_ty B ξ)
  | tyUnit l => tyUnit l
  | tySEq l A a b => tySEq l (gren_ty A ξ) (gren_tm a ξ) (gren_tm b ξ)
  | tySEmpty l => tySEmpty l
  | tyId l A a b => tyId l (gren_ty A ξ) (gren_tm a ξ) (gren_tm b ξ)
  | tyEmpty l => tyEmpty l
  | tySum l l' A B => tySum l l' (gren_ty A ξ) (gren_ty B ξ)
  | tyW l l' A B => tyW l l' (gren_ty A ξ) (gren_ty B ξ)
  end
with gren_tm (t : tm) (ξ : nat -> nat) {struct t} : tm :=
  match t with
  | var n => var n
  | tmErr => tmErr | tmNat => tmNat | tmU l => tmU l | zero => zero
  | tmPi l l' s t => tmPi l l' (gren_tm s ξ) (gren_tm t ξ)
  | succ t => succ (gren_tm t ξ)
  | natrec l M s z t => natrec l (gren_ty M ξ) (gren_tm s ξ) (gren_tm z ξ) (gren_tm t ξ)
  | lam l l' A t => lam l l' (gren_ty A ξ) (gren_tm t ξ)
  | app t l l' A B s => app (gren_tm t ξ) l l' (gren_ty A ξ) (gren_ty B ξ) (gren_tm s ξ)
  | gvar u d => gvar (ξ u) (glren d ξ)
  | boxT T => boxT (gren_ty T ξ)
  | boxt t => boxt (gren_tm t ξ)
  | letboxT l' l Δ M t' t =>
      letboxT l' l (gcren Δ ξ) (gren_ty M ξ) (gren_tm t' (gupr ξ)) (gren_tm t ξ)
  | letboxt l' l Δ T M t' t =>
      letboxt l' l (gcren Δ ξ) (gren_ty T ξ) (gren_ty M ξ) (gren_tm t' (gupr ξ)) (gren_tm t ξ)
  | tmTy T => tmTy (gren_ty T ξ)
  | tmTup s t => tmTup (gren_tm s ξ) (gren_tm t ξ)
  | bindU b => bindU (gren_tm b ξ)
  | bindG b => bindG (gren_tm b (gupr ξ))
  | bindL b => bindL (gren_tm b ξ)
  | elimT l1 l2 rb l Δ t => elimT l1 l2 (gren_tm rb ξ) l (gcren Δ ξ) (gren_tm t ξ)
  | elimt l1 l2 rb l Δ T t => elimt l1 l2 (gren_tm rb ξ) l (gcren Δ ξ) (gren_ty T ξ) (gren_tm t ξ)
  | ulam n l T t => ulam n l (gren_ty T ξ) (gren_tm t ξ)
  | uapp t ls => uapp (gren_tm t ξ) ls
  | clam l T t => clam l (gren_ty T (gupr ξ)) (gren_tm t (gupr ξ))
  | capp t Δ => capp (gren_tm t ξ) (gcren Δ ξ)
  | tlam Δ l l' T t => tlam (gcren Δ ξ) l l' (gren_ty T (gupr ξ)) (gren_tm t (gupr ξ))
  | tapp t T => tapp (gren_tm t ξ) (gren_ty T ξ)
  | tmSig l l' s t => tmSig l l' (gren_tm s ξ) (gren_tm t ξ)
  | tmPair l l' A B a b => tmPair l l' (gren_ty A ξ) (gren_ty B ξ) (gren_tm a ξ) (gren_tm b ξ)
  | tmFst l l' A B p => tmFst l l' (gren_ty A ξ) (gren_ty B ξ) (gren_tm p ξ)
  | tmSnd l l' A B p => tmSnd l l' (gren_ty A ξ) (gren_ty B ξ) (gren_tm p ξ)
  | tmUnit l => tmUnit l
  | tmTriv l => tmTriv l
  | srefl l A a => srefl l (gren_ty A ξ) (gren_tm a ξ)
  | elimSEmpty l l' M e => elimSEmpty l l' (gren_ty M ξ) (gren_tm e ξ)
  | tmRefl l A a => tmRefl l (gren_ty A ξ) (gren_tm a ξ)
  | tmId l s t u => tmId l (gren_tm s ξ) (gren_tm t ξ) (gren_tm u ξ)
  | tmSEq l s t u => tmSEq l (gren_tm s ξ) (gren_tm t ξ) (gren_tm u ξ)
  | tmSEmpty l => tmSEmpty l
  | tmEmpty l => tmEmpty l
  | tmSum l l' s t => tmSum l l' (gren_tm s ξ) (gren_tm t ξ)
  | tmW l l' s t => tmW l l' (gren_tm s ξ) (gren_tm t ξ)
  | elimEmpty l l' M t => elimEmpty l l' (gren_ty M ξ) (gren_tm t ξ)
  | tmInl l l' A B a => tmInl l l' (gren_ty A ξ) (gren_ty B ξ) (gren_tm a ξ)
  | tmInr l l' A B a => tmInr l l' (gren_ty A ξ) (gren_ty B ξ) (gren_tm a ξ)
  | tmCase l l' l'' A B M c1 c2 t =>
      tmCase l l' l'' (gren_ty A ξ) (gren_ty B ξ) (gren_ty M ξ) (gren_tm c1 ξ) (gren_tm c2 ξ) (gren_tm t ξ)
  | tmSup l l' A B a f => tmSup l l' (gren_ty A ξ) (gren_ty B ξ) (gren_tm a ξ) (gren_tm f ξ)
  | tmElimW l l' l'' A B M c t =>
      tmElimW l l' l'' (gren_ty A ξ) (gren_ty B ξ) (gren_ty M ξ) (gren_tm c ξ) (gren_tm t ξ)
  | tmJ l l' A a M c u e =>
      tmJ l l' (gren_ty A ξ) (gren_tm a ξ) (gren_ty M ξ) (gren_tm c ξ) (gren_tm u ξ) (gren_tm e ξ)
  | gdef u b d => gdef (ξ u) (gren_tm b ξ) (glren d ξ)
  end
with gcren (Γ : ctx) (ξ : nat -> nat) {struct Γ} : ctx :=
  match Γ with
  | cnil => cnil | cvar g => cvar (ξ g) | cext Γ A l => cext (gcren Γ ξ) (gren_ty A ξ) l
  end
with glren (d : lsub) (ξ : nat -> nat) {struct d} : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (glren d ξ) (gren_tm t ξ) end.

(** A local substitution moved under one global binder. *)
Definition gwk (d : lsub) : lsub := glren d S.

(** ** Universe renaming (M3)

    Traverses everything, box contents included; only level positions
    change. *)

Fixpoint uren_ty (T : ty) (ρ : nat -> nat) {struct T} : ty :=
  match T with
  | tyErr => tyErr | tyNat => tyNat
  | tyPi l l' A B => tyPi (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ)
  | tyU l => tyU (lvren l ρ)
  | tyEl l t => tyEl (lvren l ρ) (uren_tm t ρ)
  | tyGvar U d => tyGvar U (ulren d ρ)
  | tyCTyp Δ l => tyCTyp (ucren Δ ρ) (lvren l ρ)
  | tyCTrm Δ T l => tyCTrm (ucren Δ ρ) (uren_ty T ρ) (lvren l ρ)
  | tyUPi n l T => tyUPi n (lvren l (uuprn n ρ)) (uren_ty T (uuprn n ρ))
  | tyCPi l T => tyCPi (lvren l ρ) (uren_ty T ρ)
  | tyTPi Δ l l' T => tyTPi (ucren Δ ρ) (lvren l ρ) (lvren l' ρ) (uren_ty T ρ)
  | tySig l l' A B => tySig (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ)
  | tyUnit l => tyUnit (lvren l ρ)
  | tySEq l A a b => tySEq (lvren l ρ) (uren_ty A ρ) (uren_tm a ρ) (uren_tm b ρ)
  | tySEmpty l => tySEmpty (lvren l ρ)
  | tyId l A a b => tyId (lvren l ρ) (uren_ty A ρ) (uren_tm a ρ) (uren_tm b ρ)
  | tyEmpty l => tyEmpty (lvren l ρ)
  | tySum l l' A B => tySum (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ)
  | tyW l l' A B => tyW (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ)
  end
with uren_tm (t : tm) (ρ : nat -> nat) {struct t} : tm :=
  match t with
  | var n => var n
  | tmErr => tmErr | tmNat => tmNat | zero => zero
  | tmU l => tmU (lvren l ρ)
  | tmPi l l' s t => tmPi (lvren l ρ) (lvren l' ρ) (uren_tm s ρ) (uren_tm t ρ)
  | succ t => succ (uren_tm t ρ)
  | natrec l M s z t =>
      natrec (lvren l ρ) (uren_ty M ρ) (uren_tm s ρ) (uren_tm z ρ) (uren_tm t ρ)
  | lam l l' A t => lam (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_tm t ρ)
  | app t l l' A B s =>
      app (uren_tm t ρ) (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_tm s ρ)
  | gvar u d => gvar u (ulren d ρ)
  | boxT T => boxT (uren_ty T ρ)
  | boxt t => boxt (uren_tm t ρ)
  | letboxT l' l Δ M t' t =>
      letboxT (lvren l' ρ) (lvren l ρ) (ucren Δ ρ) (uren_ty M ρ) (uren_tm t' ρ) (uren_tm t ρ)
  | letboxt l' l Δ T M t' t =>
      letboxt (lvren l' ρ) (lvren l ρ) (ucren Δ ρ) (uren_ty T ρ) (uren_ty M ρ)
        (uren_tm t' ρ) (uren_tm t ρ)
  | tmTy T => tmTy (uren_ty T ρ)
  | tmTup s t => tmTup (uren_tm s ρ) (uren_tm t ρ)
  | bindU b => bindU (uren_tm b (uupr ρ))
  | bindG b => bindG (uren_tm b ρ)
  | bindL b => bindL (uren_tm b ρ)
  | elimT l1 l2 rb l Δ t =>
      elimT (lvren l1 ρ) (lvren l2 ρ) (uren_tm rb ρ) (lvren l ρ) (ucren Δ ρ) (uren_tm t ρ)
  | elimt l1 l2 rb l Δ T t =>
      elimt (lvren l1 ρ) (lvren l2 ρ) (uren_tm rb ρ) (lvren l ρ) (ucren Δ ρ) (uren_ty T ρ)
        (uren_tm t ρ)
  | ulam n l T t => ulam n (lvren l (uuprn n ρ)) (uren_ty T (uuprn n ρ)) (uren_tm t (uuprn n ρ))
  | uapp t ls => uapp (uren_tm t ρ) (map (fun l => lvren l ρ) ls)
  | clam l T t => clam (lvren l ρ) (uren_ty T ρ) (uren_tm t ρ)
  | capp t Δ => capp (uren_tm t ρ) (ucren Δ ρ)
  | tlam Δ l l' T t => tlam (ucren Δ ρ) (lvren l ρ) (lvren l' ρ) (uren_ty T ρ) (uren_tm t ρ)
  | tapp t T => tapp (uren_tm t ρ) (uren_ty T ρ)
  | tmSig l l' s t => tmSig (lvren l ρ) (lvren l' ρ) (uren_tm s ρ) (uren_tm t ρ)
  | tmPair l l' A B a b =>
      tmPair (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_tm a ρ) (uren_tm b ρ)
  | tmFst l l' A B p => tmFst (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_tm p ρ)
  | tmSnd l l' A B p => tmSnd (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_tm p ρ)
  | tmUnit l => tmUnit (lvren l ρ)
  | tmTriv l => tmTriv (lvren l ρ)
  | srefl l A a => srefl (lvren l ρ) (uren_ty A ρ) (uren_tm a ρ)
  | elimSEmpty l l' M e => elimSEmpty (lvren l ρ) (lvren l' ρ) (uren_ty M ρ) (uren_tm e ρ)
  | tmRefl l A a => tmRefl (lvren l ρ) (uren_ty A ρ) (uren_tm a ρ)
  | tmId l s t u => tmId (lvren l ρ) (uren_tm s ρ) (uren_tm t ρ) (uren_tm u ρ)
  | tmSEq l s t u => tmSEq (lvren l ρ) (uren_tm s ρ) (uren_tm t ρ) (uren_tm u ρ)
  | tmSEmpty l => tmSEmpty (lvren l ρ)
  | tmEmpty l => tmEmpty (lvren l ρ)
  | tmSum l l' s t => tmSum (lvren l ρ) (lvren l' ρ) (uren_tm s ρ) (uren_tm t ρ)
  | tmW l l' s t => tmW (lvren l ρ) (lvren l' ρ) (uren_tm s ρ) (uren_tm t ρ)
  | elimEmpty l l' M t => elimEmpty (lvren l ρ) (lvren l' ρ) (uren_ty M ρ) (uren_tm t ρ)
  | tmInl l l' A B a => tmInl (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_tm a ρ)
  | tmInr l l' A B a => tmInr (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_tm a ρ)
  | tmCase l l' l'' A B M c1 c2 t =>
      tmCase (lvren l ρ) (lvren l' ρ) (lvren l'' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_ty M ρ) (uren_tm c1 ρ) (uren_tm c2 ρ) (uren_tm t ρ)
  | tmSup l l' A B a f => tmSup (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_tm a ρ) (uren_tm f ρ)
  | tmElimW l l' l'' A B M c t =>
      tmElimW (lvren l ρ) (lvren l' ρ) (lvren l'' ρ) (uren_ty A ρ) (uren_ty B ρ) (uren_ty M ρ) (uren_tm c ρ) (uren_tm t ρ)
  | tmJ l l' A a M c u e =>
      tmJ (lvren l ρ) (lvren l' ρ) (uren_ty A ρ) (uren_tm a ρ) (uren_ty M ρ) (uren_tm c ρ) (uren_tm u ρ) (uren_tm e ρ)
  | gdef u b d => gdef u (uren_tm b ρ) (ulren d ρ)
  end
with ucren (Γ : ctx) (ρ : nat -> nat) {struct Γ} : ctx :=
  match Γ with
  | cnil => cnil | cvar g => cvar g
  | cext Γ A l => cext (ucren Γ ρ) (uren_ty A ρ) (lvren l ρ)
  end
with ulren (d : lsub) (ρ : nat -> nat) {struct d} : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (ulren d ρ) (uren_tm t ρ) end.

(** A local substitution moved under one level binder, and under [n]. *)
Definition uwk (d : lsub) : lsub := ulren d S.
Definition uwkn (n : nat) (d : lsub) : lsub := Nat.iter n uwk d.

(** ** Local substitution *)

Fixpoint subst_ty (T : ty) (d : lsub) {struct T} : ty :=
  match T with
  | tyErr => tyErr | tyNat => tyNat
  | tyPi l l' A B => tyPi l l' (subst_ty A d) (subst_ty B (llift d))
  | tyU l => tyU l
  | tyEl l t => tyEl l (subst_tm t d)
  | tyGvar U d' => tyGvar U (lcomp d' d)
  | tyCTyp Δ l => tyCTyp Δ l
  | tyCTrm Δ T l => tyCTrm Δ T l
  | tyUPi n l T => tyUPi n l (subst_ty T (uwkn n d))
  | tyCPi l T => tyCPi l (subst_ty T (gwk d))
  | tyTPi Δ l l' T => tyTPi Δ l l' (subst_ty T (gwk d))
  | tySig l l' A B => tySig l l' (subst_ty A d) (subst_ty B (llift d))
  | tyUnit l => tyUnit l
  | tySEq l A a b => tySEq l (subst_ty A d) (subst_tm a d) (subst_tm b d)
  | tySEmpty l => tySEmpty l
  | tyId l A a b => tyId l (subst_ty A d) (subst_tm a d) (subst_tm b d)
  | tyEmpty l => tyEmpty l
  | tySum l l' A B => tySum l l' (subst_ty A d) (subst_ty B d)
  | tyW l l' A B => tyW l l' (subst_ty A d) (subst_ty B (llift d))
  end
with subst_tm (t : tm) (d : lsub) {struct t} : tm :=
  match t with
  | var n => llk d n
  | tmErr => tmErr | tmNat => tmNat | tmU l => tmU l | zero => zero
  | tmPi l l' s t => tmPi l l' (subst_tm s d) (subst_tm t (llift d))
  | succ t => succ (subst_tm t d)
  | natrec l M s z t =>
      natrec l (subst_ty M (llift d)) (subst_tm s d) (subst_tm z (llift (llift d))) (subst_tm t d)
  | lam l l' A t => lam l l' (subst_ty A d) (subst_tm t (llift d))
  | app t l l' A B s =>
      app (subst_tm t d) l l' (subst_ty A d) (subst_ty B (llift d)) (subst_tm s d)
  | gvar u d' => gvar u (lcomp d' d)
  | boxT T => boxT T
  | boxt t => boxt t
  | letboxT l' l Δ M t' t =>
      letboxT l' l Δ (subst_ty M (llift d)) (subst_tm t' (gwk d)) (subst_tm t d)
  | letboxt l' l Δ T M t' t =>
      letboxt l' l Δ T (subst_ty M (llift d)) (subst_tm t' (gwk d)) (subst_tm t d)
  | tmTy T => tmTy (subst_ty T d)
  | tmTup s t => tmTup (subst_tm s d) (subst_tm t d)
  | bindU b => bindU (subst_tm b (uwk d))
  | bindG b => bindG (subst_tm b (gwk d))
  | bindL b => bindL (subst_tm b (llift d))
  | elimT l1 l2 rb l Δ t => elimT l1 l2 (subst_tm rb d) l Δ (subst_tm t d)
  | elimt l1 l2 rb l Δ T t => elimt l1 l2 (subst_tm rb d) l Δ T (subst_tm t d)
  | ulam n l T t => ulam n l (subst_ty T (uwkn n d)) (subst_tm t (uwkn n d))
  | uapp t ls => uapp (subst_tm t d) ls
  | clam l T t => clam l (subst_ty T (gwk d)) (subst_tm t (gwk d))
  | capp t Δ => capp (subst_tm t d) Δ
  | tlam Δ l l' T t => tlam Δ l l' (subst_ty T (gwk d)) (subst_tm t (gwk d))
  | tapp t T => tapp (subst_tm t d) T
  | tmSig l l' s t => tmSig l l' (subst_tm s d) (subst_tm t (llift d))
  | tmPair l l' A B a b =>
      tmPair l l' (subst_ty A d) (subst_ty B (llift d)) (subst_tm a d) (subst_tm b d)
  | tmFst l l' A B p => tmFst l l' (subst_ty A d) (subst_ty B (llift d)) (subst_tm p d)
  | tmSnd l l' A B p => tmSnd l l' (subst_ty A d) (subst_ty B (llift d)) (subst_tm p d)
  | tmUnit l => tmUnit l
  | tmTriv l => tmTriv l
  | srefl l A a => srefl l (subst_ty A d) (subst_tm a d)
  | elimSEmpty l l' M e => elimSEmpty l l' (subst_ty M d) (subst_tm e d)
  | tmRefl l A a => tmRefl l (subst_ty A d) (subst_tm a d)
  | tmId l s t u => tmId l (subst_tm s d) (subst_tm t d) (subst_tm u d)
  | tmSEq l s t u => tmSEq l (subst_tm s d) (subst_tm t d) (subst_tm u d)
  | tmSEmpty l => tmSEmpty l
  | tmEmpty l => tmEmpty l
  | tmSum l l' s t => tmSum l l' (subst_tm s d) (subst_tm t d)
  | tmW l l' s t => tmW l l' (subst_tm s d) (subst_tm t (llift d))
  | elimEmpty l l' M t => elimEmpty l l' (subst_ty M (llift d)) (subst_tm t d)
  | tmInl l l' A B a => tmInl l l' (subst_ty A d) (subst_ty B d) (subst_tm a d)
  | tmInr l l' A B a => tmInr l l' (subst_ty A d) (subst_ty B d) (subst_tm a d)
  | tmCase l l' l'' A B M c1 c2 t =>
      tmCase l l' l'' (subst_ty A d) (subst_ty B d) (subst_ty M (llift d)) (subst_tm c1 (llift d)) (subst_tm c2 (llift d)) (subst_tm t d)
  | tmSup l l' A B a f => tmSup l l' (subst_ty A d) (subst_ty B (llift d)) (subst_tm a d) (subst_tm f d)
  | tmElimW l l' l'' A B M c t =>
      tmElimW l l' l'' (subst_ty A d) (subst_ty B (llift d)) (subst_ty M (llift d)) (subst_tm c (llift (llift (llift d)))) (subst_tm t d)
  | tmJ l l' A a M c u e =>
      tmJ l l' (subst_ty A d) (subst_tm a d) (subst_ty M (llift (llift d))) (subst_tm c d) (subst_tm u d) (subst_tm e d)
  | gdef u b d' => gdef u b (lcomp d' d)
  end
with lcomp (d' : lsub) (d : lsub) {struct d'} : lsub :=       (* d' ∘ d *)
  match d' with
  | lshift k => lnorm (ldrop k d)
  | lcons d' t => lcons' (lcomp d' d) (subst_tm t d)
  end.

(** ** Overloaded notations *)

Class Ren (X : Type) := ren : X -> rsub -> X.
Class Subst (X : Type) := subst : X -> lsub -> X.
#[export] Instance Ren_ty : Ren ty := ren_ty.
#[export] Instance Ren_tm : Ren tm := ren_tm.
#[export] Instance Ren_lsub : Ren lsub := lren.
#[export] Instance Subst_ty : Subst ty := subst_ty.
#[export] Instance Subst_tm : Subst tm := subst_tm.
#[export] Instance Subst_lsub : Subst lsub := lcomp.
Arguments ren {_ _} !_ _ /.
Arguments subst {_ _} !_ _ /.

Notation "x ⟨ r ⟩" := (ren x r) (at level 5, format "x ⟨ r ⟩").
Notation "x [ d ]" := (subst x d) (at level 5, format "x [ d ]").

(** [a/x], the single substitution of β-rules. *)
Definition lsingle (a : tm) : lsub := lcons (lshift 0) a.
(** [z[t/x, r/y]] for the successor branch of [elimN] (x = 1, y = 0). *)
Definition lsingle2 (t r : tm) : lsub := lcons (lcons (lshift 0) t) r.
(** The substitution in the successor branch of [elimN]: in context
    [Γ, x : Nat, y : M], the type [M[succ x/x]]. *)
Definition lsucc : lsub := lcons (lshift 2) (succ (var 1)).
(** [↑]: weakening by one local variable. *)
Notation "↑" := rshift1.

(** [c[a/a, f/f, h/ih]], for the step of [elim_W] (M13a). *)
Definition lsingle3 (a f h : tm) : lsub := lcons (lsingle2 a f) h.
(** [elim_W]'s synthesized induction hypothesis (M13_DESIGN.md):
    [λ^{l',l''}(y : B[a/x]). elim_W(A↑; B↑; M↑; c↑; app(f↑; l', l ⊔ l'; B[a/x]↑; W↑; y))],
    the application annotated with the child function's type weakened
    past [y]. *)
Definition wIH (l l' l'' : lvl) (A B M : ty) (c a f : tm) : tm :=
  lam l' l'' B[lsingle a]
    (tmElimW l l' l'' A⟨↑⟩ B⟨rlift ↑⟩ M⟨rlift ↑⟩ c⟨rlift (rlift (rlift ↑))⟩
       (app f⟨↑⟩ l' (lmax l l') B[lsingle a]⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨rlift ↑⟩ (var 0))).
(** The step telescope of [elim_W] (M13_DESIGN.md), as abbreviations so that
    the operations' normalizers see through them: the children's type in
    [Γ, a : A], the induction hypothesis's in [Γ, a, f], and the step's in
    [Γ, a, f, ih]. *)
Notation wfty l l' A B := (tyPi l' (lmax l l') B (tyW l l' A B)⟨↑⟩⟨↑⟩).
Notation wihty l l' l'' A B M :=
  (tyPi l' l'' B⟨↑⟩ M⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle
     (app (var 1) l' (lmax l l') B⟨↑⟩⟨↑⟩ (tyW l l' A B)⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 0))]).
Notation wstepty l l' A B M :=
  (M⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle
     (tmSup l l' A⟨↑⟩⟨↑⟩⟨↑⟩ B⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ (var 2) (var 1))]).

(** ** Global substitution

    A global substitution is a meta-level function to global objects.
    [GId j] (the variable [j] itself) makes identity and renaming
    sort-agnostic; a lookup of the wrong sort is junk ([tyErr], [tmErr],
    [cnil]) and never arises for typed substitutions. *)

Inductive gobj : Type := GId (j : nat) | GCtx (Γ : ctx) | GTy (T : ty) | GTm (t : tm).
Definition gsub := nat -> gobj.

Definition goren (o : gobj) (ξ : nat -> nat) : gobj :=
  match o with
  | GId j => GId (ξ j) | GCtx Γ => GCtx (gcren Γ ξ)
  | GTy T => GTy (gren_ty T ξ) | GTm t => GTm (gren_tm t ξ)
  end.

Definition gup (σ : gsub) : gsub :=
  fun n => match n with 0 => GId 0 | S n => goren (σ n) S end.

Definition gouren (o : gobj) (ρ : nat -> nat) : gobj :=
  match o with
  | GId j => GId j | GCtx Γ => GCtx (ucren Γ ρ)
  | GTy T => GTy (uren_ty T ρ) | GTm t => GTm (uren_tm t ρ)
  end.

(** A global substitution moved under one level binder, and under [n]. *)
Definition guwk (σ : gsub) : gsub := fun n => gouren (σ n) S.
Definition guwkn (n : nat) (σ : gsub) : gsub := Nat.iter n guwk σ.

(** Instantiation at a use site: [U^δ[σ] = σ(U)[δ[σ]]], [g[σ] = σ(g)]. *)
Definition pty (o : gobj) (d : lsub) : ty :=
  match o with GId j => tyGvar j d | GTy T => subst_ty T d | _ => tyErr end.
Definition ptm (o : gobj) (d : lsub) : tm :=
  match o with GId j => gvar j d | GTm t => subst_tm t d | _ => tmErr end.
(** A defined global's instance: renamed with its (substituted) body. A
    well-formed substitution sends a defined global to a defined one
    (M9_DESIGN.md); the other case only makes the function total. *)
Definition pdef (o : gobj) (b : tm) (d : lsub) : tm :=
  match o with GId j => gdef j b d | _ => ptm o d end.
Definition pctx (o : gobj) : ctx :=
  match o with GId j => cvar j | GCtx Γ => Γ | _ => cnil end.

Fixpoint gsubst_ty (T : ty) (σ : gsub) {struct T} : ty :=
  match T with
  | tyErr => tyErr | tyNat => tyNat
  | tyPi l l' A B => tyPi l l' (gsubst_ty A σ) (gsubst_ty B σ)
  | tyU l => tyU l
  | tyEl l t => tyEl l (gsubst_tm t σ)
  | tyGvar U d => pty (σ U) (glsubst d σ)
  | tyCTyp Δ l => tyCTyp (gcsubst Δ σ) l
  | tyCTrm Δ T l => tyCTrm (gcsubst Δ σ) (gsubst_ty T σ) l
  | tyUPi n l T => tyUPi n l (gsubst_ty T (guwkn n σ))
  | tyCPi l T => tyCPi l (gsubst_ty T (gup σ))
  | tyTPi Δ l l' T => tyTPi (gcsubst Δ σ) l l' (gsubst_ty T (gup σ))
  | tySig l l' A B => tySig l l' (gsubst_ty A σ) (gsubst_ty B σ)
  | tyUnit l => tyUnit l
  | tySEq l A a b => tySEq l (gsubst_ty A σ) (gsubst_tm a σ) (gsubst_tm b σ)
  | tySEmpty l => tySEmpty l
  | tyId l A a b => tyId l (gsubst_ty A σ) (gsubst_tm a σ) (gsubst_tm b σ)
  | tyEmpty l => tyEmpty l
  | tySum l l' A B => tySum l l' (gsubst_ty A σ) (gsubst_ty B σ)
  | tyW l l' A B => tyW l l' (gsubst_ty A σ) (gsubst_ty B σ)
  end
with gsubst_tm (t : tm) (σ : gsub) {struct t} : tm :=
  match t with
  | var n => var n
  | tmErr => tmErr | tmNat => tmNat | tmU l => tmU l | zero => zero
  | tmPi l l' s t => tmPi l l' (gsubst_tm s σ) (gsubst_tm t σ)
  | succ t => succ (gsubst_tm t σ)
  | natrec l M s z t => natrec l (gsubst_ty M σ) (gsubst_tm s σ) (gsubst_tm z σ) (gsubst_tm t σ)
  | lam l l' A t => lam l l' (gsubst_ty A σ) (gsubst_tm t σ)
  | app t l l' A B s => app (gsubst_tm t σ) l l' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_tm s σ)
  | gvar u d => ptm (σ u) (glsubst d σ)
  | boxT T => boxT (gsubst_ty T σ)
  | boxt t => boxt (gsubst_tm t σ)
  | letboxT l' l Δ M t' t =>
      letboxT l' l (gcsubst Δ σ) (gsubst_ty M σ) (gsubst_tm t' (gup σ)) (gsubst_tm t σ)
  | letboxt l' l Δ T M t' t =>
      letboxt l' l (gcsubst Δ σ) (gsubst_ty T σ) (gsubst_ty M σ) (gsubst_tm t' (gup σ)) (gsubst_tm t σ)
  | tmTy T => tmTy (gsubst_ty T σ)
  | tmTup s t => tmTup (gsubst_tm s σ) (gsubst_tm t σ)
  | bindU b => bindU (gsubst_tm b (guwk σ))
  | bindG b => bindG (gsubst_tm b (gup σ))
  | bindL b => bindL (gsubst_tm b σ)
  | elimT l1 l2 rb l Δ t => elimT l1 l2 (gsubst_tm rb σ) l (gcsubst Δ σ) (gsubst_tm t σ)
  | elimt l1 l2 rb l Δ T t =>
      elimt l1 l2 (gsubst_tm rb σ) l (gcsubst Δ σ) (gsubst_ty T σ) (gsubst_tm t σ)
  | ulam n l T t => ulam n l (gsubst_ty T (guwkn n σ)) (gsubst_tm t (guwkn n σ))
  | uapp t ls => uapp (gsubst_tm t σ) ls
  | clam l T t => clam l (gsubst_ty T (gup σ)) (gsubst_tm t (gup σ))
  | capp t Δ => capp (gsubst_tm t σ) (gcsubst Δ σ)
  | tlam Δ l l' T t => tlam (gcsubst Δ σ) l l' (gsubst_ty T (gup σ)) (gsubst_tm t (gup σ))
  | tapp t T => tapp (gsubst_tm t σ) (gsubst_ty T σ)
  | tmSig l l' s t => tmSig l l' (gsubst_tm s σ) (gsubst_tm t σ)
  | tmPair l l' A B a b =>
      tmPair l l' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_tm a σ) (gsubst_tm b σ)
  | tmFst l l' A B p => tmFst l l' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_tm p σ)
  | tmSnd l l' A B p => tmSnd l l' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_tm p σ)
  | tmUnit l => tmUnit l
  | tmTriv l => tmTriv l
  | srefl l A a => srefl l (gsubst_ty A σ) (gsubst_tm a σ)
  | elimSEmpty l l' M e => elimSEmpty l l' (gsubst_ty M σ) (gsubst_tm e σ)
  | tmRefl l A a => tmRefl l (gsubst_ty A σ) (gsubst_tm a σ)
  | tmId l s t u => tmId l (gsubst_tm s σ) (gsubst_tm t σ) (gsubst_tm u σ)
  | tmSEq l s t u => tmSEq l (gsubst_tm s σ) (gsubst_tm t σ) (gsubst_tm u σ)
  | tmSEmpty l => tmSEmpty l
  | tmEmpty l => tmEmpty l
  | tmSum l l' s t => tmSum l l' (gsubst_tm s σ) (gsubst_tm t σ)
  | tmW l l' s t => tmW l l' (gsubst_tm s σ) (gsubst_tm t σ)
  | elimEmpty l l' M t => elimEmpty l l' (gsubst_ty M σ) (gsubst_tm t σ)
  | tmInl l l' A B a => tmInl l l' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_tm a σ)
  | tmInr l l' A B a => tmInr l l' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_tm a σ)
  | tmCase l l' l'' A B M c1 c2 t =>
      tmCase l l' l'' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_ty M σ) (gsubst_tm c1 σ) (gsubst_tm c2 σ) (gsubst_tm t σ)
  | tmSup l l' A B a f => tmSup l l' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_tm a σ) (gsubst_tm f σ)
  | tmElimW l l' l'' A B M c t =>
      tmElimW l l' l'' (gsubst_ty A σ) (gsubst_ty B σ) (gsubst_ty M σ) (gsubst_tm c σ) (gsubst_tm t σ)
  | tmJ l l' A a M c u e =>
      tmJ l l' (gsubst_ty A σ) (gsubst_tm a σ) (gsubst_ty M σ) (gsubst_tm c σ) (gsubst_tm u σ) (gsubst_tm e σ)
  | gdef u b d => pdef (σ u) (gsubst_tm b σ) (glsubst d σ)
  end
with gcsubst (Γ : ctx) (σ : gsub) {struct Γ} : ctx :=
  match Γ with
  | cnil => cnil | cvar g => pctx (σ g) | cext Γ A l => cext (gcsubst Γ σ) (gsubst_ty A σ) l
  end
with glsubst (d : lsub) (σ : gsub) {struct d} : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (glsubst d σ) (gsubst_tm t σ) end.

Definition gosubst (o : gobj) (τ : gsub) : gobj :=
  match o with
  | GId j => τ j | GCtx Γ => GCtx (gcsubst Γ τ)
  | GTy T => GTy (gsubst_ty T τ) | GTm t => GTm (gsubst_tm t τ)
  end.

(** ** Universe substitution (M3) *)

Fixpoint usubst_ty (T : ty) (φ : nat -> lvl) {struct T} : ty :=
  match T with
  | tyErr => tyErr | tyNat => tyNat
  | tyPi l l' A B => tyPi (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ)
  | tyU l => tyU (lvsubst l φ)
  | tyEl l t => tyEl (lvsubst l φ) (usubst_tm t φ)
  | tyGvar U d => tyGvar U (ulsubst d φ)
  | tyCTyp Δ l => tyCTyp (ucsubst Δ φ) (lvsubst l φ)
  | tyCTrm Δ T l => tyCTrm (ucsubst Δ φ) (usubst_ty T φ) (lvsubst l φ)
  | tyUPi n l T => tyUPi n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ))
  | tyCPi l T => tyCPi (lvsubst l φ) (usubst_ty T φ)
  | tyTPi Δ l l' T => tyTPi (ucsubst Δ φ) (lvsubst l φ) (lvsubst l' φ) (usubst_ty T φ)
  | tySig l l' A B => tySig (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ)
  | tyUnit l => tyUnit (lvsubst l φ)
  | tySEq l A a b => tySEq (lvsubst l φ) (usubst_ty A φ) (usubst_tm a φ) (usubst_tm b φ)
  | tySEmpty l => tySEmpty (lvsubst l φ)
  | tyId l A a b => tyId (lvsubst l φ) (usubst_ty A φ) (usubst_tm a φ) (usubst_tm b φ)
  | tyEmpty l => tyEmpty (lvsubst l φ)
  | tySum l l' A B => tySum (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ)
  | tyW l l' A B => tyW (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ)
  end
with usubst_tm (t : tm) (φ : nat -> lvl) {struct t} : tm :=
  match t with
  | var n => var n
  | tmErr => tmErr | tmNat => tmNat | zero => zero
  | tmU l => tmU (lvsubst l φ)
  | tmPi l l' s t => tmPi (lvsubst l φ) (lvsubst l' φ) (usubst_tm s φ) (usubst_tm t φ)
  | succ t => succ (usubst_tm t φ)
  | natrec l M s z t =>
      natrec (lvsubst l φ) (usubst_ty M φ) (usubst_tm s φ) (usubst_tm z φ) (usubst_tm t φ)
  | lam l l' A t => lam (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_tm t φ)
  | app t l l' A B s =>
      app (usubst_tm t φ) (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ)
        (usubst_tm s φ)
  | gvar u d => gvar u (ulsubst d φ)
  | boxT T => boxT (usubst_ty T φ)
  | boxt t => boxt (usubst_tm t φ)
  | letboxT l' l Δ M t' t =>
      letboxT (lvsubst l' φ) (lvsubst l φ) (ucsubst Δ φ) (usubst_ty M φ) (usubst_tm t' φ)
        (usubst_tm t φ)
  | letboxt l' l Δ T M t' t =>
      letboxt (lvsubst l' φ) (lvsubst l φ) (ucsubst Δ φ) (usubst_ty T φ) (usubst_ty M φ)
        (usubst_tm t' φ) (usubst_tm t φ)
  | tmTy T => tmTy (usubst_ty T φ)
  | tmTup s t => tmTup (usubst_tm s φ) (usubst_tm t φ)
  | bindU b => bindU (usubst_tm b (uup φ))
  | bindG b => bindG (usubst_tm b φ)
  | bindL b => bindL (usubst_tm b φ)
  | elimT l1 l2 rb l Δ t =>
      elimT (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm rb φ) (lvsubst l φ) (ucsubst Δ φ)
        (usubst_tm t φ)
  | elimt l1 l2 rb l Δ T t =>
      elimt (lvsubst l1 φ) (lvsubst l2 φ) (usubst_tm rb φ) (lvsubst l φ) (ucsubst Δ φ)
        (usubst_ty T φ) (usubst_tm t φ)
  | ulam n l T t => ulam n (lvsubst l (uupn n φ)) (usubst_ty T (uupn n φ)) (usubst_tm t (uupn n φ))
  | uapp t ls => uapp (usubst_tm t φ) (map (fun l => lvsubst l φ) ls)
  | clam l T t => clam (lvsubst l φ) (usubst_ty T φ) (usubst_tm t φ)
  | capp t Δ => capp (usubst_tm t φ) (ucsubst Δ φ)
  | tlam Δ l l' T t => tlam (ucsubst Δ φ) (lvsubst l φ) (lvsubst l' φ) (usubst_ty T φ) (usubst_tm t φ)
  | tapp t T => tapp (usubst_tm t φ) (usubst_ty T φ)
  | tmSig l l' s t => tmSig (lvsubst l φ) (lvsubst l' φ) (usubst_tm s φ) (usubst_tm t φ)
  | tmPair l l' A B a b =>
      tmPair (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_tm a φ) (usubst_tm b φ)
  | tmFst l l' A B p =>
      tmFst (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_tm p φ)
  | tmSnd l l' A B p =>
      tmSnd (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_tm p φ)
  | tmUnit l => tmUnit (lvsubst l φ)
  | tmTriv l => tmTriv (lvsubst l φ)
  | srefl l A a => srefl (lvsubst l φ) (usubst_ty A φ) (usubst_tm a φ)
  | elimSEmpty l l' M e => elimSEmpty (lvsubst l φ) (lvsubst l' φ) (usubst_ty M φ) (usubst_tm e φ)
  | tmRefl l A a => tmRefl (lvsubst l φ) (usubst_ty A φ) (usubst_tm a φ)
  | tmId l s t u => tmId (lvsubst l φ) (usubst_tm s φ) (usubst_tm t φ) (usubst_tm u φ)
  | tmSEq l s t u => tmSEq (lvsubst l φ) (usubst_tm s φ) (usubst_tm t φ) (usubst_tm u φ)
  | tmSEmpty l => tmSEmpty (lvsubst l φ)
  | tmEmpty l => tmEmpty (lvsubst l φ)
  | tmSum l l' s t => tmSum (lvsubst l φ) (lvsubst l' φ) (usubst_tm s φ) (usubst_tm t φ)
  | tmW l l' s t => tmW (lvsubst l φ) (lvsubst l' φ) (usubst_tm s φ) (usubst_tm t φ)
  | elimEmpty l l' M t => elimEmpty (lvsubst l φ) (lvsubst l' φ) (usubst_ty M φ) (usubst_tm t φ)
  | tmInl l l' A B a => tmInl (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_tm a φ)
  | tmInr l l' A B a => tmInr (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_tm a φ)
  | tmCase l l' l'' A B M c1 c2 t =>
      tmCase (lvsubst l φ) (lvsubst l' φ) (lvsubst l'' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_ty M φ) (usubst_tm c1 φ) (usubst_tm c2 φ) (usubst_tm t φ)
  | tmSup l l' A B a f => tmSup (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_tm a φ) (usubst_tm f φ)
  | tmElimW l l' l'' A B M c t =>
      tmElimW (lvsubst l φ) (lvsubst l' φ) (lvsubst l'' φ) (usubst_ty A φ) (usubst_ty B φ) (usubst_ty M φ) (usubst_tm c φ) (usubst_tm t φ)
  | tmJ l l' A a M c u e =>
      tmJ (lvsubst l φ) (lvsubst l' φ) (usubst_ty A φ) (usubst_tm a φ) (usubst_ty M φ) (usubst_tm c φ) (usubst_tm u φ) (usubst_tm e φ)
  | gdef u b d => gdef u (usubst_tm b φ) (ulsubst d φ)
  end
with ucsubst (Γ : ctx) (φ : nat -> lvl) {struct Γ} : ctx :=
  match Γ with
  | cnil => cnil | cvar g => cvar g
  | cext Γ A l => cext (ucsubst Γ φ) (usubst_ty A φ) (lvsubst l φ)
  end
with ulsubst (d : lsub) (φ : nat -> lvl) {struct d} : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (ulsubst d φ) (usubst_tm t φ) end.

Definition gousubst (o : gobj) (φ : nat -> lvl) : gobj :=
  match o with
  | GId j => GId j | GCtx Γ => GCtx (ucsubst Γ φ)
  | GTy T => GTy (usubst_ty T φ) | GTm t => GTm (usubst_tm t φ)
  end.

(** [o/u], the single global substitution of the letbox β-rules, and the
    instances [T[Δ/g]], [T[T₂/U]] of the meta-functions (M5). *)
Definition gsingle (o : gobj) : gsub := fun i => match i with 0 => o | S i => GId i end.

(** Overloaded notations for the global operations. *)
Class GRen (X : Type) := gren : X -> (nat -> nat) -> X.
Class GSubst (X : Type) := gsubst : X -> gsub -> X.
#[export] Instance GRen_ty : GRen ty := gren_ty.
#[export] Instance GRen_tm : GRen tm := gren_tm.
#[export] Instance GRen_ctx : GRen ctx := gcren.
#[export] Instance GRen_lsub : GRen lsub := glren.
#[export] Instance GSubst_ty : GSubst ty := gsubst_ty.
#[export] Instance GSubst_tm : GSubst tm := gsubst_tm.
#[export] Instance GSubst_ctx : GSubst ctx := gcsubst.
#[export] Instance GSubst_lsub : GSubst lsub := glsubst.
Arguments gren {_ _} !_ _ /.
Arguments gsubst {_ _} !_ _ /.

Notation "x ⟪ ξ ⟫" := (gren x ξ) (at level 5, format "x ⟪ ξ ⟫").
Notation "x ⦃ σ ⦄" := (gsubst x σ) (at level 5, format "x ⦃ σ ⦄").

Class URen (X : Type) := uren : X -> (nat -> nat) -> X.
Class USubst (X : Type) := usubst : X -> (nat -> lvl) -> X.
#[export] Instance URen_lvl : URen lvl := lvren.
#[export] Instance URen_ty : URen ty := uren_ty.
#[export] Instance URen_tm : URen tm := uren_tm.
#[export] Instance URen_ctx : URen ctx := ucren.
#[export] Instance URen_lsub : URen lsub := ulren.
#[export] Instance USubst_lvl : USubst lvl := lvsubst.
#[export] Instance USubst_ty : USubst ty := usubst_ty.
#[export] Instance USubst_tm : USubst tm := usubst_tm.
#[export] Instance USubst_ctx : USubst ctx := ucsubst.
#[export] Instance USubst_lsub : USubst lsub := ulsubst.
Arguments uren {_ _} !_ _ /.
Arguments usubst {_ _} !_ _ /.

Notation "x ⟨ ρ ⟩ᵤ" := (uren x ρ) (at level 5, format "x ⟨ ρ ⟩ᵤ").
Notation "x [ φ ]ᵤ" := (usubst x φ) (at level 5, format "x [ φ ]ᵤ").
