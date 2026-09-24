(** * Weak-head normal and neutral forms (ch. 6 §"Weak Head Normal Forms")

    [W ::= Nat | Π | Ty l | V]         [V ::= U^δ | El l ν]
    [w ::= ν | Nat | Π | Ty l | 0 | succ t | λ]
    [ν ::= x | u^δ | elimN … ν | app ν …] *)
From DeLaM.Syntax Require Export Subst.

Inductive whne : tm -> Prop :=
| whne_var n : whne (var n)
| whne_gvar u d : whne (gvar u d)
| whne_natrec l M s z t : whne t -> whne (natrec l M s z t)
| whne_app t l l' A B s : whne t -> whne (app t l l' A B s).

Inductive whnf : tm -> Prop :=
| whnf_ne t : whne t -> whnf t
| whnf_tmNat : whnf tmNat
| whnf_tmPi l l' s t : whnf (tmPi l l' s t)
| whnf_tmU l : whnf (tmU l)
| whnf_zero : whnf zero
| whnf_succ t : whnf (succ t)
| whnf_lam l l' A t : whnf (lam l l' A t).

Inductive whne_ty : ty -> Prop :=
| whne_tyGvar U d : whne_ty (tyGvar U d)
| whne_tyEl l t : whne t -> whne_ty (tyEl l t).

Inductive whnf_ty : ty -> Prop :=
| whnf_ty_ne T : whne_ty T -> whnf_ty T
| whnf_tyNat : whnf_ty tyNat
| whnf_tyPi l l' A B : whnf_ty (tyPi l l' A B)
| whnf_tyU l : whnf_ty (tyU l).

#[export] Hint Constructors whne whnf whne_ty whnf_ty : whnf.

(** ** Stability under renaming *)

Lemma whne_ren t r : whne t -> whne t⟨r⟩.
Proof. induction 1; cbn; constructor; auto. Qed.
Lemma whnf_ren t r : whnf t -> whnf t⟨r⟩.
Proof. destruct 1; cbn; auto using whne_ren with whnf. Qed.
Lemma whne_ty_ren T r : whne_ty T -> whne_ty T⟨r⟩.
Proof. destruct 1; cbn; constructor; auto using whne_ren. Qed.
Lemma whnf_ty_ren T r : whnf_ty T -> whnf_ty T⟨r⟩.
Proof. destruct 1; cbn; auto using whne_ty_ren with whnf. Qed.

(** ** Canonical shapes *)

Lemma whne_not_zero : ~ whne zero.
Proof. inversion 1. Qed.
Lemma whne_not_succ t : ~ whne (succ t).
Proof. inversion 1. Qed.
Lemma whne_not_lam l l' A t : ~ whne (lam l l' A t).
Proof. inversion 1. Qed.
Lemma whne_not_code_nat : ~ whne tmNat.
Proof. inversion 1. Qed.
Lemma whne_not_code_pi l l' s t : ~ whne (tmPi l l' s t).
Proof. inversion 1. Qed.
Lemma whne_not_code_U l : ~ whne (tmU l).
Proof. inversion 1. Qed.
Lemma whne_ty_not_nat : ~ whne_ty tyNat.
Proof. inversion 1. Qed.
Lemma whne_ty_not_pi l l' A B : ~ whne_ty (tyPi l l' A B).
Proof. inversion 1. Qed.
Lemma whne_ty_not_U l : ~ whne_ty (tyU l).
Proof. inversion 1. Qed.
