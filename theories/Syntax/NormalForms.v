(** * Weak-head normal and neutral forms (ch. 6 §"Weak Head Normal Forms")

    [W ::= Nat | Π | Ty l | □ | UΠ | CΠ | TΠ | V]         [V ::= U^δ | El l ν]
    [w ::= ν | Nat | Π | Ty l | 0 | succ t | λ | box | Λ | Λg | ΛU]
    [ν ::= x | u^δ | elimN … ν | app ν … | letbox … ν | ν $ l⃗ | ν Δ | ν T
         | elim_Typ … ν | elim_Typ … (box U^δ) | elim_Trm … ν | elim_Trm … (box u^δ)] *)
From DeLaM.Syntax Require Export LevelEq.

Inductive whne : tm -> Prop :=
| whne_var n : whne (var n)
| whne_gvar u d : whne (gvar u d)
| whne_natrec l M s z t : whne t -> whne (natrec l M s z t)
| whne_app t l l' A B s : whne t -> whne (app t l l' A B s)
| whne_letboxT l' l Δ M t' t : whne t -> whne (letboxT l' l Δ M t' t)
| whne_letboxt l' l Δ T M t' t : whne t -> whne (letboxt l' l Δ T M t' t)
(* recursors on code: a neutral scrutinee, or a boxed global variable (07:371) *)
| whne_elimT l1 l2 rb l Δ t : whne t -> whne (elimT l1 l2 rb l Δ t)
| whne_elimT_gvar l1 l2 rb l Δ U d : whne (elimT l1 l2 rb l Δ (boxT (tyGvar U d)))
| whne_elimt l1 l2 rb l Δ T t : whne t -> whne (elimt l1 l2 rb l Δ T t)
| whne_elimt_gvar l1 l2 rb l Δ T u d : whne (elimt l1 l2 rb l Δ T (boxt (gvar u d)))
(* a boxed defined global blocks it too: code does not unfold (M9) *)
| whne_elimt_gdef l1 l2 rb l Δ T u b d : whne (elimt l1 l2 rb l Δ T (boxt (gdef u b d)))
| whne_uapp t ls : whne t -> whne (uapp t ls)
| whne_capp t Δ : whne t -> whne (capp t Δ)
| whne_tapp t T : whne t -> whne (tapp t T)
| whne_fst l l' A B p : whne p -> whne (tmFst l l' A B p)
| whne_snd l l' A B p : whne p -> whne (tmSnd l l' A B p).

Inductive whnf : tm -> Prop :=
| whnf_ne t : whne t -> whnf t
| whnf_tmNat : whnf tmNat
| whnf_tmPi l l' s t : whnf (tmPi l l' s t)
| whnf_tmU l : whnf (tmU l)
| whnf_zero : whnf zero
| whnf_succ t : whnf (succ t)
| whnf_lam l l' A t : whnf (lam l l' A t)
| whnf_boxT T : whnf (boxT T)
| whnf_boxt t : whnf (boxt t)
| whnf_ulam n l T t : whnf (ulam n l T t)
| whnf_clam l T t : whnf (clam l T t)
| whnf_tlam Δ l l' T t : whnf (tlam Δ l l' T t)
| whnf_tmSig l l' s t : whnf (tmSig l l' s t)
| whnf_pair l l' A B a b : whnf (tmPair l l' A B a b)
| whnf_tmUnit l : whnf (tmUnit l)
| whnf_triv l : whnf (tmTriv l).

Inductive whne_ty : ty -> Prop :=
| whne_tyGvar U d : whne_ty (tyGvar U d)
| whne_tyEl l t : whne t -> whne_ty (tyEl l t).

Inductive whnf_ty : ty -> Prop :=
| whnf_ty_ne T : whne_ty T -> whnf_ty T
| whnf_tyNat : whnf_ty tyNat
| whnf_tyPi l l' A B : whnf_ty (tyPi l l' A B)
| whnf_tyU l : whnf_ty (tyU l)
| whnf_tyCTyp Δ l : whnf_ty (tyCTyp Δ l)
| whnf_tyCTrm Δ T l : whnf_ty (tyCTrm Δ T l)
| whnf_tyUPi n l T : whnf_ty (tyUPi n l T)
| whnf_tyCPi l T : whnf_ty (tyCPi l T)
| whnf_tyTPi Δ l l' T : whnf_ty (tyTPi Δ l l' T)
| whnf_tySig l l' A B : whnf_ty (tySig l l' A B)
| whnf_tyUnit l : whnf_ty (tyUnit l).

#[export] Hint Constructors whne whnf whne_ty whnf_ty : whnf.

(** A boxed global blocks the term recursor: a global variable, or a
    defined global, which code does not unfold (M9). *)
Definition boxed_global (c : tm) : Prop := match c with gvar _ _ | gdef _ _ _ => True | _ => False end.

Lemma whne_elimt_glob l1 l2 rb l Δ T c : boxed_global c -> whne (elimt l1 l2 rb l Δ T (boxt c)).
Proof. destruct c; cbn; try contradiction; intros _; first [apply whne_elimt_gvar | apply whne_elimt_gdef]. Qed.
#[export] Hint Resolve whne_elimt_glob : whnf.
Lemma boxed_global_leq c c' : boxed_global c -> tm_leq c c' -> boxed_global c'.
Proof. destruct c; cbn; try contradiction; intros _; destruct c'; cbn; tauto. Qed.
Lemma boxed_global_gren c ξ : boxed_global c -> boxed_global c⟪ξ⟫.
Proof. destruct c; cbn; tauto. Qed.
Lemma boxed_global_ren c r : boxed_global c -> boxed_global c⟨r⟩.
Proof. destruct c; cbn; tauto. Qed.
Lemma boxed_global_subst c d : boxed_global c -> boxed_global c[d].
Proof. destruct c; cbn; tauto. Qed.
Lemma boxed_global_uren c ρ : boxed_global c -> boxed_global (uren_tm c ρ).
Proof. destruct c; cbn; tauto. Qed.
Lemma boxed_global_usubst c φ : boxed_global c -> boxed_global (usubst_tm c φ).
Proof. destruct c; cbn; tauto. Qed.
#[export] Hint Resolve boxed_global_leq boxed_global_gren boxed_global_ren boxed_global_subst
  boxed_global_uren boxed_global_usubst : whnf.

(** ** Stability under renaming *)

Ltac whne_step := first [ apply whne_elimT_gvar | apply whne_elimt_gvar | apply whne_elimt_gdef | constructor; auto ].

Lemma whne_ren t r : whne t -> whne t⟨r⟩.
Proof. induction 1; cbn; whne_step. Qed.
Lemma whnf_ren t r : whnf t -> whnf t⟨r⟩.
Proof. destruct 1; cbn; auto using whne_ren with whnf. Qed.
Lemma whne_ty_ren T r : whne_ty T -> whne_ty T⟨r⟩.
Proof. destruct 1; cbn; constructor; auto using whne_ren. Qed.
Lemma whnf_ty_ren T r : whnf_ty T -> whnf_ty T⟨r⟩.
Proof. destruct 1; cbn; auto using whne_ty_ren with whnf. Qed.

(** ** Stability under global renaming *)

Lemma whne_gren t ξ : whne t -> whne t⟪ξ⟫.
Proof. induction 1; cbn; whne_step. Qed.
Lemma whnf_gren t ξ : whnf t -> whnf t⟪ξ⟫.
Proof. destruct 1; cbn; auto using whne_gren with whnf. Qed.
Lemma whne_ty_gren T ξ : whne_ty T -> whne_ty T⟪ξ⟫.
Proof. destruct 1; cbn; constructor; auto using whne_gren. Qed.
Lemma whnf_ty_gren T ξ : whnf_ty T -> whnf_ty T⟪ξ⟫.
Proof. destruct 1; cbn; auto using whne_ty_gren with whnf. Qed.

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
Lemma whne_not_boxT T : ~ whne (boxT T).
Proof. inversion 1. Qed.
Lemma whne_not_boxt t : ~ whne (boxt t).
Proof. inversion 1. Qed.
Lemma whne_ty_not_CTyp Δ l : ~ whne_ty (tyCTyp Δ l).
Proof. inversion 1. Qed.
Lemma whne_ty_not_CTrm Δ T l : ~ whne_ty (tyCTrm Δ T l).
Proof. inversion 1. Qed.
Lemma whne_not_ulam n l T t : ~ whne (ulam n l T t).
Proof. inversion 1. Qed.
Lemma whne_ty_not_UPi n l T : ~ whne_ty (tyUPi n l T).
Proof. inversion 1. Qed.
Lemma whne_not_clam l T t : ~ whne (clam l T t).
Proof. inversion 1. Qed.
Lemma whne_not_tlam Δ l l' T t : ~ whne (tlam Δ l l' T t).
Proof. inversion 1. Qed.
Lemma whne_ty_not_CPi l T : ~ whne_ty (tyCPi l T).
Proof. inversion 1. Qed.
Lemma whne_ty_not_TPi Δ l l' T : ~ whne_ty (tyTPi Δ l l' T).
Proof. inversion 1. Qed.
Lemma whne_ty_not_Sig l l' A B : ~ whne_ty (tySig l l' A B).
Proof. inversion 1. Qed.
Lemma whne_not_code_sig l l' s t : ~ whne (tmSig l l' s t).
Proof. inversion 1. Qed.
Lemma whne_not_pair l l' A B a b : ~ whne (tmPair l l' A B a b).
Proof. inversion 1. Qed.
Lemma whne_ty_not_Unit l : ~ whne_ty (tyUnit l).
Proof. inversion 1. Qed.
Lemma whne_not_code_unit l : ~ whne (tmUnit l).
Proof. inversion 1. Qed.
Lemma whne_not_triv l : ~ whne (tmTriv l).
Proof. inversion 1. Qed.
Lemma whne_not_gdef u b d : ~ whne (gdef u b d).
Proof. inversion 1. Qed.
