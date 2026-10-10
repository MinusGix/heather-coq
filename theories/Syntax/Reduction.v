(** * Untyped weak-head reduction (ch. 6 §"Reduction Relations")

    Deliberate deviation: the paper's redexes repeat level/type annotations
    ([El (l⊔l') (Π^{l,l'} …)], [app (λ^{l,l'} x:S. t) l l' S …]).  Typing
    only fixes annotations up to [≈] and conversion, so matching them
    syntactically would leave well-typed redexes stuck.  Reduction here
    ignores annotations, as annotations never affect computation. *)
From Coq Require Import Relations Lia.
From DeLaM.Syntax Require Export NormalForms.

Inductive red : tm -> tm -> Prop :=
| red_natrec_zero l M s z : red (natrec l M s z zero) s
| red_natrec_succ l M s z t :
    red (natrec l M s z (succ t)) (z[lsingle2 t (natrec l M s z t)])
| red_beta l l' A b l1 l2 A' B s :
    red (app (lam l l' A b) l1 l2 A' B s) (b[lsingle s])
| red_natrec l M s z t t' : red t t' -> red (natrec l M s z t) (natrec l M s z t')
| red_app t t' l l' A B s : red t t' -> red (app t l l' A B s) (app t' l l' A B s)
| red_letboxT_beta l' l Δ M t' T :
    red (letboxT l' l Δ M t' (boxT T)) (t'⦃gsingle (GTy T)⦄)
| red_letboxt_beta l' l Δ T M t' t :
    red (letboxt l' l Δ T M t' (boxt t)) (t'⦃gsingle (GTm t)⦄)
| red_letboxT l' l Δ M t' t t0 : red t t0 -> red (letboxT l' l Δ M t' t) (letboxT l' l Δ M t' t0)
| red_letboxt l' l Δ T M t' t t0 : red t t0 ->
    red (letboxt l' l Δ T M t' t) (letboxt l' l Δ T M t' t0)
(* recursors on code (M3_DESIGN.md E4): β by the reduct functions; the
   index of [elim_Trm] is reduced only under a boxed [λ], the one head
   whose reduct reads it *)
| red_elimT_beta l1 l2 rb l Δ c r :
    redT l1 l2 rb l Δ c = Some r -> red (elimT l1 l2 rb l Δ (boxT c)) r
| red_elimT l1 l2 rb l Δ t t' : red t t' -> red (elimT l1 l2 rb l Δ t) (elimT l1 l2 rb l Δ t')
| red_elimt_beta l1 l2 rb l Δ T c r :
    redt l1 l2 rb l Δ T c = Some r -> red (elimt l1 l2 rb l Δ T (boxt c)) r
| red_elimt l1 l2 rb l Δ T t t' : red t t' -> red (elimt l1 l2 rb l Δ T t) (elimt l1 l2 rb l Δ T t')
| red_elimt_idx l1 l2 rb l Δ T T' k k' A b : red_ty T T' ->
    red (elimt l1 l2 rb l Δ T (boxt (lam k k' A b))) (elimt l1 l2 rb l Δ T' (boxt (lam k k' A b)))
(* universe polymorphism (M4); as for [app], the annotation is ignored. The
   arity check makes β commute with universe substitution *)
| red_ubeta n l T b ls : length ls = n -> red (uapp (ulam n l T b) ls) b[uext ls lvar]ᵤ
| red_uapp t t' ls : red t t' -> red (uapp t ls) (uapp t' ls)
(* meta-functions (M5): β instantiates the global binder *)
| red_cbeta l T b Δ : red (capp (clam l T b) Δ) b⦃gsingle (GCtx Δ)⦄
| red_capp t t' Δ : red t t' -> red (capp t Δ) (capp t' Δ)
| red_tbeta Δ l l' B b T : red (tapp (tlam Δ l l' B b) T) b⦃gsingle (GTy T)⦄
| red_tapp t t' T : red t t' -> red (tapp t T) (tapp t' T)
(* dependent pairs (M8): projections of a pair, and in the scrutinee *)
| red_fst_beta l l' A B a b k k' A' B' : red (tmFst k k' A' B' (tmPair l l' A B a b)) a
| red_snd_beta l l' A B a b k k' A' B' : red (tmSnd k k' A' B' (tmPair l l' A B a b)) b
| red_fst l l' A B p p' : red p p' -> red (tmFst l l' A B p) (tmFst l l' A B p')
| red_snd l l' A B p p' : red p p' -> red (tmSnd l l' A B p) (tmSnd l l' A B p')
(* definitions (M9): δ unfolds a defined global to its body's instance. Reduction
   is used at the computing layers only and never enters a box, so code keeps
   the global (M9_DESIGN.md) *)
| red_delta u b d : red (gdef u b d) (b[d])
(* the irrelevant empty type (M10a): no β, only its scrutinee reduces *)
| red_elimSEmpty l l' M e e' : red e e' -> red (elimSEmpty l l' M e) (elimSEmpty l l' M e')
| red_elimEmpty l l' M e e' : red e e' -> red (elimEmpty l l' M e) (elimEmpty l l' M e')
(* [case] (M12b): β at either injection, whatever its annotations; the
   scrutinee reduces *)
| red_case_inl l l' l'' A B M c1 c2 k k' C D a :
    red (tmCase l l' l'' A B M c1 c2 (tmInl k k' C D a)) (c1[lsingle a])
| red_case_inr l l' l'' A B M c1 c2 k k' C D b :
    red (tmCase l l' l'' A B M c1 c2 (tmInr k k' C D b)) (c2[lsingle b])
| red_case l l' l'' A B M c1 c2 t t' : red t t' -> red (tmCase l l' l'' A B M c1 c2 t) (tmCase l l' l'' A B M c1 c2 t')
(* well-founded trees (M13a): β at a [sup] of any annotations instantiates the
   step at the shape, the children and the synthesized induction hypothesis;
   the scrutinee reduces *)
| red_elimW_sup l l' l'' A B M c k k' C D a f :
    red (tmElimW l l' l'' A B M c (tmSup k k' C D a f)) (c[lsingle3 a f (wIH l l' l'' A B M c a f)])
| red_elimW l l' l'' A B M c t t' : red t t' -> red (tmElimW l l' l'' A B M c t) (tmElimW l l' l'' A B M c t')
(* finitary well-founded trees (M15a): β at a [sup_f] of any annotations
   instantiates the step at the shape, the children and the synthesized
   induction hypothesis; the scrutinee reduces *)
| red_elimWf_supf l l' A N M c k C D a cs :
    red (tmElimWf l l' A N M c (tmSupf k C D a cs)) (c[lsingle3 a cs (wfIH l l' A N M c a cs)])
| red_elimWf l l' A N M c t t' : red t t' -> red (tmElimWf l l' A N M c t) (tmElimWf l l' A N M c t')
(* the identity type (M11a): J computes on refl, ignoring the annotations and
   the right endpoint as the other β rules do; otherwise its proof reduces *)
| red_J_refl l l' A a M c u k B b : red (tmJ l l' A a M c u (tmRefl k B b)) c
| red_J l l' A a M c u e e' : red e e' -> red (tmJ l l' A a M c u e) (tmJ l l' A a M c u e')

with red_ty : ty -> ty -> Prop :=
| red_El_nat l : red_ty (tyEl l tmNat) tyNat
| red_El_U l l0 : red_ty (tyEl l (tmU l0)) (tyU l0)
| red_El_pi l l1 l2 s t :
    red_ty (tyEl l (tmPi l1 l2 s t)) (tyPi l1 l2 (tyEl l1 s) (tyEl l2 t))
| red_El l t t' : red t t' -> red_ty (tyEl l t) (tyEl l t')
| red_El_sig l l1 l2 s t :
    red_ty (tyEl l (tmSig l1 l2 s t)) (tySig l1 l2 (tyEl l1 s) (tyEl l2 t))
| red_El_unit l l0 : red_ty (tyEl l (tmUnit l0)) (tyUnit l0)
| red_El_id l l0 s t u : red_ty (tyEl l (tmId l0 s t u)) (tyId l0 (tyEl l0 s) t u)
| red_El_seq l l0 s t u : red_ty (tyEl l (tmSEq l0 s t u)) (tySEq l0 (tyEl l0 s) t u)
| red_El_sempty l l0 : red_ty (tyEl l (tmSEmpty l0)) (tySEmpty l0)
(* the codes of Empty and + (M12c) *)
| red_El_empty l l0 : red_ty (tyEl l (tmEmpty l0)) (tyEmpty l0)
| red_El_sum l l1 l2 s t : red_ty (tyEl l (tmSum l1 l2 s t)) (tySum l1 l2 (tyEl l1 s) (tyEl l2 t))
(* the code of W (M13b) *)
| red_El_W l l1 l2 s t : red_ty (tyEl l (tmW l1 l2 s t)) (tyW l1 l2 (tyEl l1 s) (tyEl l2 t))
(* the codes of Vec and Fin (M14b): the length rides across *)
| red_El_vec l l0 s n : red_ty (tyEl l (tmVec l0 s n)) (tyVec l0 (tyEl l0 s) n)
| red_El_fin l n : red_ty (tyEl l (tmFin n)) (tyFin n)
(* the code of Wf (M15b): the arity rides across under the shape's binder *)
| red_El_wf l l0 s n : red_ty (tyEl l (tmWf l0 s n)) (tyWf l0 (tyEl l0 s) n)
(* length-indexed tuples and finite indices (M14a): compute on the length *)
| red_vec_zero l A : red_ty (tyVec l A zero) (tyUnit l)
| red_vec_succ l A n : red_ty (tyVec l A (succ n)) (tySig l l A (tyVec l A⟨↑⟩ n⟨↑⟩))
| red_vec l A n n' : red n n' -> red_ty (tyVec l A n) (tyVec l A n')
| red_fin_zero : red_ty (tyFin zero) (tyEmpty lzero)
| red_fin_succ n : red_ty (tyFin (succ n)) (tySum lzero lzero (tyUnit lzero) (tyFin n))
| red_fin n n' : red n n' -> red_ty (tyFin n) (tyFin n').

Scheme red_mut := Induction for red Sort Prop
  with red_ty_mut := Induction for red_ty Sort Prop.
Combined Scheme red_both from red_mut, red_ty_mut.

Definition reds := clos_refl_trans_1n tm red.
Definition reds_ty := clos_refl_trans_1n ty red_ty.

#[export] Hint Constructors red red_ty : red.

(** ** Normal forms do not reduce *)

Lemma whne_no_red t v : whne t -> ~ red t v.
Proof.
  intros H; revert v; induction H; intros v Hr; inversion Hr; subst.
  all: try solve [eapply IHwhne; eauto].
  all: try match goal with Hw : whne _ |- _ => inversion Hw end.
  all: match goal with
       | Hr : red (boxT _) _ |- _ => inversion Hr
       | Hr : red (boxt _) _ |- _ => inversion Hr
       | He : _ = Some _ |- _ => discriminate He
       end.
Qed.
Lemma whnf_no_red t v : whnf t -> ~ red t v.
Proof. destruct 1; intros Hr; try (inversion Hr; fail). eapply whne_no_red; eauto. Qed.
Lemma whnf_ty_no_red T U : whnf_ty T -> ~ red_ty T U.
Proof.
  intros HW Hr; inversion Hr; subst; inversion HW; subst;
    match goal with HT : whne_ty _ |- _ => inversion HT; subst end;
    try solve [match goal with Hw : whne _ |- _ => inversion Hw end].
  all: eapply whne_no_red; eauto.
Qed.

(** ** Determinacy *)

Lemma red_det_both :
  (forall t u, red t u -> forall u', red t u' -> u = u') /\
  (forall T U, red_ty T U -> forall U', red_ty T U' -> U = U').
Proof.
  apply red_both; intros; match goal with H' : _ |- _ => inversion H' end;
    subst; auto;
    try match goal with
        | Hr : red zero _ |- _ => inversion Hr
        | Hr : red (succ _) _ |- _ => inversion Hr
        | Hr : red (lam _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (ulam _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (clam _ _ _) _ |- _ => inversion Hr
        | Hr : red (tlam _ _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (boxT _) _ |- _ => inversion Hr
        | Hr : red (boxt _) _ |- _ => inversion Hr
        | Hr : red tmNat _ |- _ => inversion Hr
        | Hr : red (tmU _) _ |- _ => inversion Hr
        | Hr : red (tmPi _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmSig _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmPair _ _ _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmUnit _) _ |- _ => inversion Hr
        | Hr : red (tmRefl _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmId _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmSEq _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmSEmpty _) _ |- _ => inversion Hr
        | Hr : red (tmEmpty _) _ |- _ => inversion Hr
        | Hr : red (tmSum _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmW _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmVec _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmFin _) _ |- _ => inversion Hr
        | Hr : red (tmWf _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmInl _ _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmInr _ _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmSup _ _ _ _ _ _) _ |- _ => inversion Hr
        | Hr : red (tmSupf _ _ _ _ _) _ |- _ => inversion Hr
        | Hr : red_ty (tyPi _ _ _ _) _ |- _ => inversion Hr
        end;
    try congruence; try (f_equal; eauto).
  (* the λ-index rule against β: β needs a Π index, which does not reduce *)
  all: match goal with
       | He : redt _ _ _ _ _ ?T _ = Some _, Hr : red_ty ?T _ |- _ =>
           destruct T; cbn in He; try discriminate; inversion Hr
       end.
Qed.

Lemma red_det t u u' : red t u -> red t u' -> u = u'.
Proof. intros H; now apply red_det_both. Qed.
Lemma red_ty_det T U U' : red_ty T U -> red_ty T U' -> U = U'.
Proof. intros H; now apply red_det_both. Qed.

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
Lemma reds_letboxT l' l Δ M t' t t0 : reds t t0 -> reds (letboxT l' l Δ M t' t) (letboxT l' l Δ M t' t0).
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_letboxt l' l Δ T M t' t t0 : reds t t0 ->
  reds (letboxt l' l Δ T M t' t) (letboxt l' l Δ T M t' t0).
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_uapp t t' ls : reds t t' -> reds (uapp t ls) (uapp t' ls).
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_capp t t' Δ : reds t t' -> reds (capp t Δ) (capp t' Δ).
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_tapp t t' T : reds t t' -> reds (tapp t T) (tapp t' T).
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_fst l l' A B p p' : reds p p' -> reds (tmFst l l' A B p) (tmFst l l' A B p').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_snd l l' A B p p' : reds p p' -> reds (tmSnd l l' A B p) (tmSnd l l' A B p').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_elimSEmpty l l' M e e' : reds e e' -> reds (elimSEmpty l l' M e) (elimSEmpty l l' M e').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_elimEmpty l l' M e e' : reds e e' -> reds (elimEmpty l l' M e) (elimEmpty l l' M e').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_case l l' l'' A B M c1 c2 t t' : reds t t' -> reds (tmCase l l' l'' A B M c1 c2 t) (tmCase l l' l'' A B M c1 c2 t').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_elimW l l' l'' A B M c t t' : reds t t' -> reds (tmElimW l l' l'' A B M c t) (tmElimW l l' l'' A B M c t').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_J l l' A a M c u e e' : reds e e' -> reds (tmJ l l' A a M c u e) (tmJ l l' A a M c u e').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_elimWf l l' A N M c t t' : reds t t' -> reds (tmElimWf l l' A N M c t) (tmElimWf l l' A N M c t').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_El l t t' : reds t t' -> reds_ty (tyEl l t) (tyEl l t').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_vec l A n n' : reds n n' -> reds_ty (tyVec l A n) (tyVec l A n').
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto with red]. Qed.
Lemma reds_fin n n' : reds n n' -> reds_ty (tyFin n) (tyFin n').
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

Lemma lsingle2_ren_ty (M : ty) t q r :
  M[lsingle2 t q]⟨r⟩ = M⟨rlift (rlift r)⟩[lsingle2 t⟨r⟩ q⟨r⟩].
Proof.
  rewrite (subst_ren_ty _ _ (lcons (lcons (r2l r) t⟨r⟩) q⟨r⟩)),
          (ren_subst_ty _ _ _ (lcons (lcons (r2l r) t⟨r⟩) q⟨r⟩)); auto.
  all: intros [|[|n]]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; rewrite ?rlk_rup; cbn;
    auto; f_equal; lia.
Qed.

(** The reducts commute with local renaming (which does not enter the
    code, [Δ] or the index). *)
Lemma tup_nth_ren t k r : tup_nth t⟨r⟩ k = (tup_nth t k)⟨r⟩.
Proof. revert t; induction k; intros []; cbn; auto. Qed.
Lemma peelU_ren b l r : peelU b⟨r⟩ l = (peelU b l)⟨r⟩.
Proof. destruct b; cbn; auto. apply usubst_ren. Qed.
Lemma peelG_ren b o r : peelG b⟨r⟩ o = (peelG b o)⟨r⟩.
Proof. destruct b; cbn; auto. apply gsubst_ren. Qed.
Lemma peelL_ren b a r : peelL b⟨r⟩ a⟨r⟩ = (peelL b a)⟨r⟩.
Proof. destruct b; cbn; auto. symmetry; apply lsingle_ren. Qed.

Ltac peel_push r :=
  repeat first [ rewrite <- peelL_ren | rewrite <- peelG_ren | rewrite <- peelU_ren ];
  unfold rb_br; rewrite tup_nth_ren; reflexivity.

Lemma redT_ren l1 l2 rb l Δ c v r : redT l1 l2 rb l Δ c = Some v ->
  redT l1 l2 rb⟨r⟩ l Δ c = Some v⟨r⟩.
Proof. destruct c; cbn [redT]; intros [= <-]; f_equal; peel_push r. Qed.
Lemma redt_ren l1 l2 rb l Δ T c v r : redt l1 l2 rb l Δ T c = Some v ->
  redt l1 l2 rb⟨r⟩ l Δ T c = Some v⟨r⟩.
Proof.
  destruct c; cbn [redt]; redt_case T; intros E; inversion E; subst; f_equal; peel_push r.
Qed.

Lemma red_ubeta_ren n l T b ls r : length ls = n -> red (uapp (ulam n l T⟨r⟩ b⟨r⟩) ls) b[uext ls lvar]ᵤ⟨r⟩.
Proof. intros; rewrite <- usubst_ren. now constructor. Qed.

(** [elim_W]'s β (M13a): the step's instance and the synthesized induction
    hypothesis commute with renaming. *)
Lemma lsingle_ren_ty (T : ty) s r : T[lsingle s]⟨r⟩ = T⟨rlift r⟩[lsingle s⟨r⟩].
Proof.
  rewrite (subst_ren_ty _ _ (lcons (r2l r) s⟨r⟩)), (ren_subst_ty _ _ _ (lcons (r2l r) s⟨r⟩)); auto.
  all: intros [|n]; cbn; rewrite ?llk_r2l, ?rlk_rup; cbn; auto; f_equal; lia.
Qed.
Lemma lsingle3_ren (c a f h : tm) r :
  c[lsingle3 a f h]⟨r⟩ = c⟨rlift (rlift (rlift r))⟩[lsingle3 a⟨r⟩ f⟨r⟩ h⟨r⟩].
Proof.
  rewrite (subst_ren _ _ (lcons (lcons (lcons (r2l r) a⟨r⟩) f⟨r⟩) h⟨r⟩)),
          (ren_subst _ _ _ (lcons (lcons (lcons (r2l r) a⟨r⟩) f⟨r⟩) h⟨r⟩)); auto.
  all: intros [|[|[|n]]]; cbn; rlk_simpl; rewrite ?llk_r2l; cbn; rlk_simpl; auto; f_equal; lia.
Qed.
Lemma ren_swap_ty (T : ty) r1 r2 r1' r2' :
  (forall n, rlk r2 (rlk r1 n) = rlk r2' (rlk r1' n)) -> T⟨r1⟩⟨r2⟩ = T⟨r1'⟩⟨r2'⟩.
Proof. intros H; rewrite !ren_ren_comp_ty; apply ren_ext_ty; intros; rewrite !rlk_rcomp; apply H. Qed.
Lemma ren_swap (t : tm) r1 r2 r1' r2' :
  (forall n, rlk r2 (rlk r1 n) = rlk r2' (rlk r1' n)) -> t⟨r1⟩⟨r2⟩ = t⟨r1'⟩⟨r2'⟩.
Proof. intros H; rewrite !ren_ren_comp; apply ren_ext_tm; intros; rewrite !rlk_rcomp; apply H. Qed.
Lemma wIH_ren l l' l'' A B M c a f r :
  (wIH l l' l'' A B M c a f)⟨r⟩ =
  wIH l l' l'' A⟨r⟩ B⟨rlift r⟩ M⟨rlift r⟩ c⟨rlift (rlift (rlift r))⟩ a⟨r⟩ f⟨r⟩.
Proof.
  unfold wIH. change (ren (lam ?l1 ?l2 ?X ?Y) ?r0) with (lam l1 l2 X⟨r0⟩ Y⟨rlift r0⟩).
  rewrite lsingle_ren_ty. f_equal.
  change (ren (tmElimW ?k1 ?k2 ?k3 ?X ?Y ?Z ?u ?v) ?r0)
    with (tmElimW k1 k2 k3 X⟨r0⟩ Y⟨rlift r0⟩ Z⟨rlift r0⟩ u⟨rlift (rlift (rlift r0))⟩ v⟨r0⟩).
  change (ren (app ?u ?k1 ?k2 ?X ?Y ?v) ?r0) with (app u⟨r0⟩ k1 k2 X⟨r0⟩ Y⟨rlift r0⟩ v⟨r0⟩).
  change (tyW ?k1 ?k2 ?X⟨?r0⟩ ?Y⟨rlift ?r0⟩) with (tyW k1 k2 X Y)⟨r0⟩.
  f_equal.
  all: try (apply ren_swap_ty; intros [|[|[|[|n]]]]; rlk_simpl; reflexivity).
  all: try (apply ren_swap; intros [|[|[|[|n]]]]; rlk_simpl; reflexivity).
  f_equal.
  all: try (apply ren_swap; intros [|[|[|[|n]]]]; rlk_simpl; reflexivity).
  - rewrite <- lsingle_ren_ty. apply ren_swap_ty; intros [|n]; rlk_simpl; reflexivity.
  - rewrite !ren_ren_comp_ty. apply ren_ext_ty; intros [|[|n]]; rlk_simpl; reflexivity.
Qed.

(** [nth] and [elim_Wf]'s induction hypothesis (M15a) commute with
    renaming: the shifts inside commute with the lifted renaming. *)
Ltac ren_comm := first [ reflexivity
  | rewrite ?ren_ren_comp_ty, ?ren_ren_comp; first [apply ren_ext_ty | apply ren_ext_tm];
    intros [|[|[|[|[|[|[|?n]]]]]]]; rlk_simpl; first [reflexivity | lia] ].
Lemma tmNth_ren l T k cs i r :
  (tmNth l T k cs i)⟨r⟩ = tmNth l T⟨r⟩ k⟨r⟩ cs⟨r⟩ i⟨r⟩.
Proof.
  unfold tmNth, nthMot, nthBase, nthStep; cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk].
  repeat f_equal; rewrite ?rlk_rlift, ?rlk_rup; cbn; try ren_comm.
Qed.
Lemma wfIH_ren l l' A N M c a cs r :
  (wfIH l l' A N M c a cs)⟨r⟩ =
  wfIH l l' A⟨r⟩ N⟨rlift r⟩ M⟨rlift r⟩ c⟨rlift (rlift (rlift r))⟩ a⟨r⟩ cs⟨r⟩.
Proof.
  unfold wfIH. change (ren (lam ?l1 ?l2 ?X ?Y) ?r0) with (lam l1 l2 X⟨r0⟩ Y⟨rlift r0⟩).
  change (ren (tyFin ?n) ?r0) with (tyFin n⟨r0⟩).
  rewrite lsingle_ren. f_equal.
  change (ren (tmElimWf ?k1 ?k2 ?X ?Y ?Z ?u ?v) ?r0)
    with (tmElimWf k1 k2 X⟨r0⟩ Y⟨rlift r0⟩ Z⟨rlift r0⟩ u⟨rlift (rlift (rlift r0))⟩ v⟨r0⟩).
  rewrite tmNth_ren. f_equal; try ren_comm.
  change (tyWf ?k1 ?X⟨?r0⟩ ?Y⟨rlift ?r0⟩) with (tyWf k1 X Y)⟨r0⟩.
  f_equal; try ren_comm.
  rewrite <- lsingle_ren. ren_comm.
Qed.

(** [Vec]'s successor step (M14a): the tail's shifts commute with renaming. *)
Lemma red_vec_succ_ren l A n r :
  red_ty (tyVec l A (succ n))⟨r⟩ (tySig l l A (tyVec l A⟨↑⟩ n⟨↑⟩))⟨r⟩.
Proof.
  change (red_ty (tyVec l A⟨r⟩ (succ n⟨r⟩)) (tySig l l A⟨r⟩ (tyVec l A⟨↑⟩⟨rlift r⟩ n⟨↑⟩⟨rlift r⟩))).
  rewrite (ren_swap_ty A ↑ (rlift r) r ↑), (ren_swap n ↑ (rlift r) r ↑) by (intros; rlk_simpl; lia).
  constructor.
Qed.

Lemma red_ren_both :
  (forall t u, red t u -> forall r, red t⟨r⟩ u⟨r⟩) /\
  (forall T U, red_ty T U -> forall r, red_ty T⟨r⟩ U⟨r⟩).
Proof.
  apply red_both; intros; cbn;
    first [ now constructor
          | now apply red_vec_succ_ren
          | now apply red_ubeta_ren
          | constructor; first [now apply redT_ren | now apply redt_ren]
          | cbn [ren_tm]; rewrite <- gsubst_ren; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩;
            first [rewrite lsingle2_ren | rewrite lsingle_ren]; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩; rewrite lsingle3_ren, wIH_ren; constructor
          | change (ren_tm ?x ?r) with x⟨r⟩; rewrite lsingle3_ren, wfIH_ren; constructor
          (* δ: the body's instance *)
          | erewrite subst_ren by (intros; apply llk_lren); constructor ].
Qed.

Lemma red_ren t u r : red t u -> red t⟨r⟩ u⟨r⟩.
Proof. intros H; now apply red_ren_both. Qed.
Lemma red_ty_ren T U r : red_ty T U -> red_ty T⟨r⟩ U⟨r⟩.
Proof. intros H; now apply red_ren_both. Qed.
Lemma reds_ren t u r : reds t u -> reds t⟨r⟩ u⟨r⟩.
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto using red_ren]. Qed.
Lemma reds_ty_ren T U r : reds_ty T U -> reds_ty T⟨r⟩ U⟨r⟩.
Proof. unfold reds, reds_ty; induction 1; [constructor|econstructor; eauto using red_ty_ren]. Qed.
