(** * Untyped weak-head reduction (ch. 6 §"Reduction Relations")

    Deliberate deviation: the paper's redexes repeat level/type annotations
    ([El (l⊔l') (Π^{l,l'} …)], [app (λ^{l,l'} x:S. t) l l' S …]).  Typing
    only fixes annotations up to [≈] and conversion, so matching them
    syntactically would leave well-typed redexes stuck.  Reduction here
    ignores annotations, as annotations never affect computation. *)
From Coq Require Import Relations Lia.
From DeLaM.Syntax Require Export NormalForms.

(** [z[t/x, r/y]] for the successor branch of [elimN] (x = 1, y = 0). *)
Definition lsingle2 (t r : tm) : lsub := lcons (lcons (lshift 0) t) r.

Inductive red : tm -> tm -> Prop :=
| red_natrec_zero l M s z : red (natrec l M s z zero) s
| red_natrec_succ l M s z t :
    red (natrec l M s z (succ t)) (z[lsingle2 t (natrec l M s z t)])
| red_beta l l' A b l1 l2 A' B s :
    red (app (lam l l' A b) l1 l2 A' B s) (b[lsingle s])
| red_natrec l M s z t t' : red t t' -> red (natrec l M s z t) (natrec l M s z t')
| red_app t t' l l' A B s : red t t' -> red (app t l l' A B s) (app t' l l' A B s).

Inductive red_ty : ty -> ty -> Prop :=
| red_El_nat l : red_ty (tyEl l tmNat) tyNat
| red_El_U l l0 : red_ty (tyEl l (tmU l0)) (tyU l0)
| red_El_pi l l1 l2 s t :
    red_ty (tyEl l (tmPi l1 l2 s t)) (tyPi l1 l2 (tyEl l1 s) (tyEl l2 t))
| red_El l t t' : red t t' -> red_ty (tyEl l t) (tyEl l t').

Definition reds := clos_refl_trans_1n tm red.
Definition reds_ty := clos_refl_trans_1n ty red_ty.

#[export] Hint Constructors red red_ty : red.

(** ** Normal forms do not reduce *)

Lemma whne_no_red t v : whne t -> ~ red t v.
Proof.
  intros H; revert v; induction H; intros v Hr; inversion Hr; subst.
  all: try solve [eapply IHwhne; eauto].
  all: match goal with Hw : whne _ |- _ => inversion Hw end.
Qed.
Lemma whnf_no_red t v : whnf t -> ~ red t v.
Proof. destruct 1; intros Hr; try (inversion Hr; fail). eapply whne_no_red; eauto. Qed.
Lemma whnf_ty_no_red T U : whnf_ty T -> ~ red_ty T U.
Proof.
  destruct 1 as [T [|l t Ht]| | |]; intros Hr; inversion Hr; subst;
    try (inversion Ht; fail). eapply whne_no_red; eauto.
Qed.

(** ** Determinacy *)

Lemma red_det t u u' : red t u -> red t u' -> u = u'.
Proof.
  intros H; revert u'; induction H; intros u' H'; inversion H'; subst; auto;
    try match goal with
        | Hr : red zero _ |- _ => inversion Hr
        | Hr : red (succ _) _ |- _ => inversion Hr
        | Hr : red (lam _ _ _ _) _ |- _ => inversion Hr
        end;
    try (f_equal; auto).
Qed.

Lemma red_ty_det T U U' : red_ty T U -> red_ty T U' -> U = U'.
Proof.
  intros H; revert U'; destruct H; intros U' H'; inversion H'; subst; auto.
  all: try solve [f_equal; eauto using red_det].
  all: match goal with Hr : red _ _ |- _ => inversion Hr end.
Qed.

Lemma reds_whnf_det t w w' : reds t w -> reds t w' -> whnf w -> whnf w' -> w = w'.
Proof.
  intros H; revert w'; induction H as [t|t u w Htu Huw IH]; intros w' H' Hw Hw'.
  - destruct H' as [|y z Hr Hrs]; auto. exfalso; exact (whnf_no_red _ _ Hw Hr).
  - destruct H' as [|y z Hr Hrs].
    + exfalso; exact (whnf_no_red _ _ Hw' Htu).
    + apply IH; auto. now rewrite (red_det _ _ _ Htu Hr).
Qed.

Lemma reds_ty_whnf_det T W W' : reds_ty T W -> reds_ty T W' -> whnf_ty W -> whnf_ty W' -> W = W'.
Proof.
  intros H; revert W'; induction H as [T|T U W Htu Huw IH]; intros W' H' Hw Hw'.
  - destruct H' as [|Y Z Hr Hrs]; auto. exfalso; exact (whnf_ty_no_red _ _ Hw Hr).
  - destruct H' as [|Y Z Hr Hrs].
    + exfalso; exact (whnf_ty_no_red _ _ Hw' Htu).
    + apply IH; auto. now rewrite (red_ty_det _ _ _ Htu Hr).
Qed.

(** ** Multi-step congruences *)

Lemma reds_trans t u v : reds t u -> reds u v -> reds t v.
Proof. unfold reds, reds_ty; intros H1 H2; induction H1; auto; econstructor; eauto. Qed.
Lemma reds_ty_trans T U V : reds_ty T U -> reds_ty U V -> reds_ty T V.
Proof. unfold reds, reds_ty; intros H1 H2; induction H1; auto; econstructor; eauto. Qed.

Lemma reds_natrec l M s z t t' : reds t t' -> reds (natrec l M s z t) (natrec l M s z t').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_app t t' l l' A B s : reds t t' -> reds (app t l l' A B s) (app t' l l' A B s).
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_El l t t' : reds t t' -> reds_ty (tyEl l t) (tyEl l t').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.

(** ** Stability under renaming *)

Lemma lsingle_ren (b s : tm) r : b[lsingle s]⟨r⟩ = b⟨rlift r⟩[lsingle s⟨r⟩].
Proof.
  rewrite (subst_ren _ _ (lcons (r2l r) s⟨r⟩)), (ren_subst _ _ _ (lcons (r2l r) s⟨r⟩)); auto.
  all: intros [|n]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; auto; f_equal; lia.
Qed.

Lemma lsingle2_ren (z t q : tm) r :
  z[lsingle2 t q]⟨r⟩ = z⟨rlift (rlift r)⟩[lsingle2 t⟨r⟩ q⟨r⟩].
Proof.
  rewrite (subst_ren _ _ (lcons (lcons (r2l r) t⟨r⟩) q⟨r⟩)),
          (ren_subst _ _ _ (lcons (lcons (r2l r) t⟨r⟩) q⟨r⟩)); auto.
  all: intros [|[|n]]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; rewrite ?rlk_rup; cbn;
    auto; f_equal; lia.
Qed.

Lemma red_ren t u r : red t u -> red t⟨r⟩ u⟨r⟩.
Proof.
  induction 1; cbn.
  - constructor.
  - change (ren_tm ?x ?r) with x⟨r⟩. rewrite lsingle2_ren. constructor.
  - change (ren_tm ?x ?r) with x⟨r⟩. rewrite lsingle_ren. constructor.
  - now constructor.
  - now constructor.
Qed.
Lemma red_ty_ren T U r : red_ty T U -> red_ty T⟨r⟩ U⟨r⟩.
Proof. destruct 1; cbn; constructor; auto using red_ren. Qed.
Lemma reds_ren t u r : reds t u -> reds t⟨r⟩ u⟨r⟩.
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto using red_ren]. Qed.
Lemma reds_ty_ren T U r : reds_ty T U -> reds_ty T⟨r⟩ U⟨r⟩.
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto using red_ty_ren]. Qed.
