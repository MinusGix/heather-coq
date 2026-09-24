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
  end
with gcren (Γ : ctx) (ξ : nat -> nat) {struct Γ} : ctx :=
  match Γ with
  | cnil => cnil | cvar g => cvar (ξ g) | cext Γ A l => cext (gcren Γ ξ) (gren_ty A ξ) l
  end
with glren (d : lsub) (ξ : nat -> nat) {struct d} : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (glren d ξ) (gren_tm t ξ) end.

(** A local substitution moved under one global binder. *)
Definition gwk (d : lsub) : lsub := glren d S.

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

(** Instantiation at a use site: [U^δ[σ] = σ(U)[δ[σ]]], [g[σ] = σ(g)]. *)
Definition pty (o : gobj) (d : lsub) : ty :=
  match o with GId j => tyGvar j d | GTy T => subst_ty T d | _ => tyErr end.
Definition ptm (o : gobj) (d : lsub) : tm :=
  match o with GId j => gvar j d | GTm t => subst_tm t d | _ => tmErr end.
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

(** [o/u], the single global substitution of the letbox β-rules. *)
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
