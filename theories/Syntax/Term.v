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
  end
with lren (d : lsub) (r : rsub) {struct d} : lsub :=
  match d with
  | lshift k => r2l (rdrop k r)
  | lcons d t => lcons' (lren d r) (ren_tm t r)
  end.

Definition llift (d : lsub) : lsub := lcons' (lren d rshift1) (var 0).

(** ** Local substitution *)

Fixpoint subst_ty (T : ty) (d : lsub) {struct T} : ty :=
  match T with
  | tyErr => tyErr | tyNat => tyNat
  | tyPi l l' A B => tyPi l l' (subst_ty A d) (subst_ty B (llift d))
  | tyU l => tyU l
  | tyEl l t => tyEl l (subst_tm t d)
  | tyGvar U d' => tyGvar U (lcomp d' d)
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
