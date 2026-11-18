(** * Unfolding every definition (M9 follow-up: consistency at M)

    [unf] replaces every occurrence [gdef u b δ] of a defined global by the
    instance of its body, [b[δ]], everywhere: under binders, in types and
    inside code. It is not a reduction (reduction never enters [box]), but
    a syntactic translation: [Typing/Unfold.v] shows that it sends every
    judgment to one about the unfolded global context, and its outputs
    mention no defined global ([unf_gfree]). Consistency at M with
    definitions follows from consistency for definition-free terms
    ([Validity/ConsistencyDef.v]).

    This file: the translation, and its commutation with every operation
    (one mutual induction per law, as in [Subst.v]). With global
    substitution it commutes unconditionally because [pdef] inlines the
    carried body when a definition is sent to anything but a variable. *)
(* the laws of [≡ₗ] first: re-exporting them after this file's other
   imports would shadow later names (Context's [gwk_id] by Subst's) *)
From DeLaM.Syntax Require Export LevelEq.
From DeLaM.Syntax Require Export SubstCommute.

(** ** The translation *)

Fixpoint unf_ty (T : ty) {struct T} : ty :=
  match T with
  | tyErr => tyErr | tyNat => tyNat
  | tyPi l l' A B => tyPi l l' (unf_ty A) (unf_ty B)
  | tyU l => tyU l
  | tyEl l t => tyEl l (unf_tm t)
  | tyGvar U d => tyGvar U (unf_l d)
  | tyCTyp Δ l => tyCTyp (unf_ctx Δ) l
  | tyCTrm Δ T l => tyCTrm (unf_ctx Δ) (unf_ty T) l
  | tyUPi n l T => tyUPi n l (unf_ty T)
  | tyCPi l T => tyCPi l (unf_ty T)
  | tyTPi Δ l l' T => tyTPi (unf_ctx Δ) l l' (unf_ty T)
  | tySig l l' A B => tySig l l' (unf_ty A) (unf_ty B)
  | tyUnit l => tyUnit l
  | tySEq l A a b => tySEq l (unf_ty A) (unf_tm a) (unf_tm b)
  | tySEmpty l => tySEmpty l
  | tyId l A a b => tyId l (unf_ty A) (unf_tm a) (unf_tm b)
  | tyEmpty l => tyEmpty l
  | tySum l l' A B => tySum l l' (unf_ty A) (unf_ty B)
  | tyW l l' A B => tyW l l' (unf_ty A) (unf_ty B)
  | tyVec l A n => tyVec l (unf_ty A) (unf_tm n)
  | tyWf l A N => tyWf l (unf_ty A) (unf_tm N)
  | tySq l A => tySq l (unf_ty A)
  | tyDVec l n F => tyDVec l (unf_tm n) (unf_ty F)
  | tyIWf l li X A N Ot C m => tyIWf l li (unf_ty X) (unf_ty A) (unf_tm N) (unf_tm Ot) (unf_tm C) (unf_tm m)
  | tyM l l' li X A B C j => tyM l l' li (unf_ty X) (unf_ty A) (unf_ty B) (unf_tm C) (unf_tm j)
  | tyFin n => tyFin (unf_tm n)
  end
with unf_tm (t : tm) {struct t} : tm :=
  match t with
  | var n => var n
  | tmErr => tmErr | tmNat => tmNat | tmU l => tmU l | zero => zero
  | tmPi l l' s t => tmPi l l' (unf_tm s) (unf_tm t)
  | succ t => succ (unf_tm t)
  | natrec l M s z t => natrec l (unf_ty M) (unf_tm s) (unf_tm z) (unf_tm t)
  | lam l l' A t => lam l l' (unf_ty A) (unf_tm t)
  | app t l l' A B s => app (unf_tm t) l l' (unf_ty A) (unf_ty B) (unf_tm s)
  | gvar u d => gvar u (unf_l d)
  | boxT T => boxT (unf_ty T)
  | boxt t => boxt (unf_tm t)
  | letboxT l' l Δ M t' t =>
      letboxT l' l (unf_ctx Δ) (unf_ty M) (unf_tm t') (unf_tm t)
  | letboxt l' l Δ T M t' t =>
      letboxt l' l (unf_ctx Δ) (unf_ty T) (unf_ty M) (unf_tm t') (unf_tm t)
  | tmTy T => tmTy (unf_ty T)
  | tmTup s t => tmTup (unf_tm s) (unf_tm t)
  | bindU b => bindU (unf_tm b)
  | bindG b => bindG (unf_tm b)
  | bindL b => bindL (unf_tm b)
  | elimT l1 l2 rb l Δ t => elimT l1 l2 (unf_tm rb) l (unf_ctx Δ) (unf_tm t)
  | elimt l1 l2 rb l Δ T t =>
      elimt l1 l2 (unf_tm rb) l (unf_ctx Δ) (unf_ty T) (unf_tm t)
  | ulam n l T t => ulam n l (unf_ty T) (unf_tm t)
  | uapp t ls => uapp (unf_tm t) ls
  | clam l T t => clam l (unf_ty T) (unf_tm t)
  | capp t Δ => capp (unf_tm t) (unf_ctx Δ)
  | tlam Δ l l' T t => tlam (unf_ctx Δ) l l' (unf_ty T) (unf_tm t)
  | tapp t T => tapp (unf_tm t) (unf_ty T)
  | tmSig l l' s t => tmSig l l' (unf_tm s) (unf_tm t)
  | tmPair l l' A B a b =>
      tmPair l l' (unf_ty A) (unf_ty B) (unf_tm a) (unf_tm b)
  | tmFst l l' A B p => tmFst l l' (unf_ty A) (unf_ty B) (unf_tm p)
  | tmSnd l l' A B p => tmSnd l l' (unf_ty A) (unf_ty B) (unf_tm p)
  | tmUnit l => tmUnit l
  | tmTriv l => tmTriv l
  | srefl l A a => srefl l (unf_ty A) (unf_tm a)
  | elimSEmpty l l' M e => elimSEmpty l l' (unf_ty M) (unf_tm e)
  | tmRefl l A a => tmRefl l (unf_ty A) (unf_tm a)
  | tmId l s t u => tmId l (unf_tm s) (unf_tm t) (unf_tm u)
  | tmSEq l s t u => tmSEq l (unf_tm s) (unf_tm t) (unf_tm u)
  | tmSEmpty l => tmSEmpty l
  | tmEmpty l => tmEmpty l
  | tmSum l l' s t => tmSum l l' (unf_tm s) (unf_tm t)
  | tmW l l' s t => tmW l l' (unf_tm s) (unf_tm t)
  | tmVec l s n => tmVec l (unf_tm s) (unf_tm n)
  | tmFin n => tmFin (unf_tm n)
  | tmWf l s n => tmWf l (unf_tm s) (unf_tm n)
  | elimEmpty l l' M t => elimEmpty l l' (unf_ty M) (unf_tm t)
  | tmInl l l' A B a => tmInl l l' (unf_ty A) (unf_ty B) (unf_tm a)
  | tmInr l l' A B a => tmInr l l' (unf_ty A) (unf_ty B) (unf_tm a)
  | tmCase l l' l'' A B M c1 c2 t =>
      tmCase l l' l'' (unf_ty A) (unf_ty B) (unf_ty M) (unf_tm c1) (unf_tm c2) (unf_tm t)
  | tmSup l l' A B a f => tmSup l l' (unf_ty A) (unf_ty B) (unf_tm a) (unf_tm f)
  | tmElimW l l' l'' A B M c t =>
      tmElimW l l' l'' (unf_ty A) (unf_ty B) (unf_ty M) (unf_tm c) (unf_tm t)
  | tmSupf l A N a cs => tmSupf l (unf_ty A) (unf_tm N) (unf_tm a) (unf_tm cs)
  | tmElimWf l l' A N M c t =>
      tmElimWf l l' (unf_ty A) (unf_tm N) (unf_ty M) (unf_tm c) (unf_tm t)
  | tmSq l A a => tmSq l (unf_ty A) (unf_tm a)
  | tmElimSq l l' A M c t => tmElimSq l l' (unf_ty A) (unf_ty M) (unf_tm c) (unf_tm t)
  | tmSqCode l s => tmSqCode l (unf_tm s)
  | tmDVec l n f => tmDVec l (unf_tm n) (unf_tm f)
  | tmIWf l li x s n o c m => tmIWf l li (unf_tm x) (unf_tm s) (unf_tm n) (unf_tm o) (unf_tm c) (unf_tm m)
  | tmSupi l li X A N Ot C a cs =>
      tmSupi l li (unf_ty X) (unf_ty A) (unf_tm N) (unf_tm Ot) (unf_tm C) (unf_tm a) (unf_tm cs)
  | tmElimIWf l li l' X A N Ot C M c m t =>
      tmElimIWf l li l' (unf_ty X) (unf_ty A) (unf_tm N) (unf_tm Ot) (unf_tm C) (unf_ty M) (unf_tm c) (unf_tm m) (unf_tm t)
  | tmCorec l l' li X A B C k Y c j y =>
      tmCorec l l' li (unf_ty X) (unf_ty A) (unf_ty B) (unf_tm C) k (unf_ty Y) (unf_tm c) (unf_tm j) (unf_tm y)
  | tmOut l l' li X A B C j m => tmOut l l' li (unf_ty X) (unf_ty A) (unf_ty B) (unf_tm C) (unf_tm j) (unf_tm m)
  | tmUnsq l t => tmUnsq l (unf_tm t)
  | tmJ l l' A a M c u e =>
      tmJ l l' (unf_ty A) (unf_tm a) (unf_ty M) (unf_tm c) (unf_tm u) (unf_tm e)
  | gdef u b d => subst_tm (unf_tm b) (unf_l d)
  end
with unf_ctx (Γ : ctx) {struct Γ} : ctx :=
  match Γ with
  | cnil => cnil | cvar g => cvar g | cext Γ A l => cext (unf_ctx Γ) (unf_ty A) l
  end
with unf_l (d : lsub) {struct d} : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (unf_l d) (unf_tm t) end.

Definition unf_o (o : gobj) : gobj :=
  match o with
  | GId j => GId j | GCtx Γ => GCtx (unf_ctx Γ) | GTy T => GTy (unf_ty T) | GTm t => GTm (unf_tm t)
  end.

(** ** Lookups *)

Lemma llk_unf d n : llk (unf_l d) n = unf_tm (llk d n).
Proof.
  revert n; induction d as [k | d IH t]; intros n; cbn [unf_l].
  - reflexivity.
  - rewrite llk_lcons'. destruct n; cbn; auto.
Qed.

Lemma nf_unf_l d : nf_l (unf_l d).
Proof. induction d; cbn [unf_l]; [exact I | apply nf_lcons'; assumption]. Qed.
#[export] Hint Resolve nf_unf_l : nf.

(** Two substitutions agree with [unf] lookup-wise: equal (outputs are normal). *)
Lemma unf_l_canon d e : nf_l e -> (forall n, unf_tm (llk d n) = llk e n) -> unf_l d = e.
Proof. intros He H. apply l_canon; [apply nf_unf_l | exact He | intros n; rewrite llk_unf; apply H]. Qed.

Ltac unf_lsub :=
  apply unf_l_canon; [auto with nf | intros ?n];
  repeat first [ rewrite llk_lren | rewrite llk_lcomp | rewrite llk_glren | rewrite llk_glsubst
               | rewrite llk_ulren | rewrite llk_ulsubst | rewrite llk_unf ].

(** ** Local renaming *)

Lemma unf_ren_all :
  let Pty T := forall r, unf_ty (ren_ty T r) = ren_ty (unf_ty T) r in
  let Ptm t := forall r, unf_tm (ren_tm t r) = ren_tm (unf_tm t) r in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases; cbn [unf_ty unf_tm ren_ty ren_tm]; try solve [f_equal; eauto].
  all: try (f_equal; unf_lsub; symmetry; solve [auto]).
  (* gdef *)
  rewrite (proj1 (proj2 subst_ren_all) _ _ (lren (unf_l d) r) r) by (intros; apply llk_lren).
  f_equal. unf_lsub. symmetry; auto.
Qed.
Lemma unf_ren_ty (T : ty) r : unf_ty T⟨r⟩ = (unf_ty T)⟨r⟩.
Proof. apply (proj1 unf_ren_all). Qed.
Lemma unf_ren (t : tm) r : unf_tm t⟨r⟩ = (unf_tm t)⟨r⟩.
Proof. apply (proj1 (proj2 unf_ren_all)). Qed.
Lemma unf_lren d r : unf_l (lren d r) = lren (unf_l d) r.
Proof. unf_lsub. apply unf_ren. Qed.

(** ** Global renaming *)

Lemma unf_gren_all :
  let Pty T := forall ξ, unf_ty (gren_ty T ξ) = gren_ty (unf_ty T) ξ in
  let Ptm t := forall ξ, unf_tm (gren_tm t ξ) = gren_tm (unf_tm t) ξ in
  let Pctx Γ := forall ξ, unf_ctx (gcren Γ ξ) = gcren (unf_ctx Γ) ξ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn [unf_ty unf_tm unf_ctx gren_ty gren_tm gcren]; try solve [f_equal; eauto].
  all: try (f_equal; unf_lsub; symmetry; solve [auto]).
  (* gdef *)
  rewrite (proj1 (proj2 gren_subst_all) _ _ (glren (unf_l d) ξ) ξ) by (intros; apply llk_glren).
  f_equal; [solve [auto] |]. unf_lsub. symmetry; auto.
Qed.
Lemma unf_gren_ty (T : ty) ξ : unf_ty (gren_ty T ξ) = gren_ty (unf_ty T) ξ.
Proof. apply (proj1 unf_gren_all). Qed.
Lemma unf_gren (t : tm) ξ : unf_tm (gren_tm t ξ) = gren_tm (unf_tm t) ξ.
Proof. apply (proj1 (proj2 unf_gren_all)). Qed.
Lemma unf_gren_ctx (Γ : ctx) ξ : unf_ctx (gcren Γ ξ) = gcren (unf_ctx Γ) ξ.
Proof. apply (proj1 (proj2 (proj2 unf_gren_all))). Qed.
Lemma unf_glren d ξ : unf_l (glren d ξ) = glren (unf_l d) ξ.
Proof. unf_lsub. apply unf_gren. Qed.

(** ** Universe renaming and substitution *)

Lemma unf_uren_all :
  let Pty T := forall ρ, unf_ty (uren_ty T ρ) = uren_ty (unf_ty T) ρ in
  let Ptm t := forall ρ, unf_tm (uren_tm t ρ) = uren_tm (unf_tm t) ρ in
  let Pctx Γ := forall ρ, unf_ctx (ucren Γ ρ) = ucren (unf_ctx Γ) ρ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn [unf_ty unf_tm unf_ctx uren_ty uren_tm ucren]; try solve [f_equal; eauto].
  all: try (f_equal; unf_lsub; symmetry; solve [auto]).
  (* gdef *)
  rewrite (proj1 (proj2 uren_subst_all) _ _ (ulren (unf_l d) ρ) ρ) by (intros; apply llk_ulren).
  f_equal; [solve [auto] |]. unf_lsub. symmetry; auto.
Qed.
Lemma unf_uren_ty (T : ty) ρ : unf_ty (uren_ty T ρ) = uren_ty (unf_ty T) ρ.
Proof. apply (proj1 unf_uren_all). Qed.
Lemma unf_uren (t : tm) ρ : unf_tm (uren_tm t ρ) = uren_tm (unf_tm t) ρ.
Proof. apply (proj1 (proj2 unf_uren_all)). Qed.
Lemma unf_uren_ctx (Γ : ctx) ρ : unf_ctx (ucren Γ ρ) = ucren (unf_ctx Γ) ρ.
Proof. apply (proj1 (proj2 (proj2 unf_uren_all))). Qed.
Lemma unf_ulren d ρ : unf_l (ulren d ρ) = ulren (unf_l d) ρ.
Proof. unf_lsub. apply unf_uren. Qed.

Lemma unf_usubst_all :
  let Pty T := forall φ, unf_ty (usubst_ty T φ) = usubst_ty (unf_ty T) φ in
  let Ptm t := forall φ, unf_tm (usubst_tm t φ) = usubst_tm (unf_tm t) φ in
  let Pctx Γ := forall φ, unf_ctx (ucsubst Γ φ) = ucsubst (unf_ctx Γ) φ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn [unf_ty unf_tm unf_ctx usubst_ty usubst_tm ucsubst]; try solve [f_equal; eauto].
  all: try (f_equal; unf_lsub; symmetry; solve [auto]).
  (* gdef *)
  rewrite (proj1 (proj2 usubst_subst_all) _ _ (ulsubst (unf_l d) φ) φ) by (intros; apply llk_ulsubst).
  f_equal; [solve [auto] |]. unf_lsub. symmetry; auto.
Qed.
Lemma unf_usubst_ty (T : ty) φ : unf_ty (usubst_ty T φ) = usubst_ty (unf_ty T) φ.
Proof. apply (proj1 unf_usubst_all). Qed.
Lemma unf_usubst (t : tm) φ : unf_tm (usubst_tm t φ) = usubst_tm (unf_tm t) φ.
Proof. apply (proj1 (proj2 unf_usubst_all)). Qed.
Lemma unf_usubst_ctx (Γ : ctx) φ : unf_ctx (ucsubst Γ φ) = ucsubst (unf_ctx Γ) φ.
Proof. apply (proj1 (proj2 (proj2 unf_usubst_all))). Qed.
Lemma unf_ulsubst d φ : unf_l (ulsubst d φ) = ulsubst (unf_l d) φ.
Proof. unf_lsub. apply unf_usubst. Qed.

(** ** Local substitution *)

Lemma llift_unf d d' : (forall n, llk d' n = unf_tm (llk d n)) ->
  forall n, llk (llift d') n = unf_tm (llk (llift d) n).
Proof. intros H [|n]; rewrite !llk_llift; [reflexivity |]. rewrite H; symmetry; apply unf_ren. Qed.
Lemma gwk_unf d d' : (forall n, llk d' n = unf_tm (llk d n)) ->
  forall n, llk (gwk d') n = unf_tm (llk (gwk d) n).
Proof. intros H n; unfold gwk; rewrite !llk_glren, H; symmetry; apply unf_gren. Qed.
Lemma uwk_unf d d' : (forall n, llk d' n = unf_tm (llk d n)) ->
  forall n, llk (uwk d') n = unf_tm (llk (uwk d) n).
Proof. intros H n; unfold uwk; rewrite !llk_ulren, H; symmetry; apply unf_uren. Qed.
Lemma uwkn_unf k d d' : (forall n, llk d' n = unf_tm (llk d n)) ->
  forall n, llk (uwkn k d') n = unf_tm (llk (uwkn k d) n).
Proof. intros H; unfold uwkn; induction k; cbn [Nat.iter]; [exact H | apply uwk_unf; exact IHk]. Qed.
#[export] Hint Resolve llift_unf gwk_unf uwk_unf uwkn_unf : unf.

Lemma unf_subst_all :
  let Pty T := forall d d', (forall n, llk d' n = unf_tm (llk d n)) ->
               unf_ty (subst_ty T d) = subst_ty (unf_ty T) d' in
  let Ptm t := forall d d', (forall n, llk d' n = unf_tm (llk d n)) ->
               unf_tm (subst_tm t d) = subst_tm (unf_tm t) d' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, LK Ptm d).
Proof.
  syn_start; try lk_cases; cbn [unf_ty unf_tm subst_ty subst_tm]; try solve [f_equal; eauto with unf].
  all: try (symmetry; solve [auto]).
  all: try (f_equal; unf_lsub; solve [auto]).
  (* gdef *)
  match goal with |- _ = subst_tm (subst_tm ?b ?e) ?d' =>
    rewrite (proj1 (proj2 subst_subst_all) b e d' (lcomp e d')) by (intros; apply llk_lcomp) end.
  f_equal. unf_lsub. auto.
Qed.
Lemma unf_subst_ty (T : ty) d : unf_ty (subst_ty T d) = subst_ty (unf_ty T) (unf_l d).
Proof. apply (proj1 unf_subst_all). intros; apply llk_unf. Qed.
Lemma unf_subst (t : tm) d : unf_tm (subst_tm t d) = subst_tm (unf_tm t) (unf_l d).
Proof. apply (proj1 (proj2 unf_subst_all)). intros; apply llk_unf. Qed.
Lemma unf_lcomp e d : unf_l (lcomp e d) = lcomp (unf_l e) (unf_l d).
Proof. unf_lsub. apply unf_subst. Qed.
Lemma unf_llift d : unf_l (llift d) = llift (unf_l d).
Proof. apply unf_l_canon; [auto with nf | intros n; symmetry; apply llift_unf; intros; apply llk_unf]. Qed.
Lemma unf_gwk d : unf_l (gwk d) = gwk (unf_l d).
Proof. apply unf_glren. Qed.
Lemma unf_uwk d : unf_l (uwk d) = uwk (unf_l d).
Proof. apply unf_ulren. Qed.
Lemma unf_uwkn k d : unf_l (uwkn k d) = uwkn k (unf_l d).
Proof.
  induction k; [reflexivity |].
  change (uwkn (S k) ?x) with (uwk (uwkn k x)). rewrite unf_uwk, IHk; reflexivity.
Qed.

(** ** Global substitution *)

Lemma unf_o_goren o ξ : unf_o (goren o ξ) = goren (unf_o o) ξ.
Proof. destruct o; cbn; f_equal; auto using unf_gren_ctx, unf_gren_ty, unf_gren. Qed.
Lemma unf_o_gouren o ρ : unf_o (gouren o ρ) = gouren (unf_o o) ρ.
Proof. destruct o; cbn; f_equal; auto using unf_uren_ctx, unf_uren_ty, unf_uren. Qed.
Lemma gup_unf σ σ' : (forall i, σ' i = unf_o (σ i)) -> forall i, gup σ' i = unf_o (gup σ i).
Proof. intros H [|i]; cbn; [reflexivity | rewrite H; symmetry; apply unf_o_goren]. Qed.
Lemma guwk_unf σ σ' : (forall i, σ' i = unf_o (σ i)) -> forall i, guwk σ' i = unf_o (guwk σ i).
Proof. intros H i; unfold guwk; rewrite H; symmetry; apply unf_o_gouren. Qed.
Lemma guwkn_unf k σ σ' : (forall i, σ' i = unf_o (σ i)) -> forall i, guwkn k σ' i = unf_o (guwkn k σ i).
Proof. intros H; unfold guwkn; induction k; cbn [Nat.iter]; [exact H | apply guwk_unf; exact IHk]. Qed.
#[export] Hint Resolve gup_unf guwk_unf guwkn_unf : unf.

Lemma unf_gsubst_all :
  let Pty T := forall σ σ', (forall i, σ' i = unf_o (σ i)) -> unf_ty (gsubst_ty T σ) = gsubst_ty (unf_ty T) σ' in
  let Ptm t := forall σ σ', (forall i, σ' i = unf_o (σ i)) -> unf_tm (gsubst_tm t σ) = gsubst_tm (unf_tm t) σ' in
  let Pctx Γ := forall σ σ', (forall i, σ' i = unf_o (σ i)) -> unf_ctx (gcsubst Γ σ) = gcsubst (unf_ctx Γ) σ' in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn [unf_ty unf_tm unf_ctx gsubst_ty gsubst_tm gcsubst]; try solve [f_equal; eauto with unf].
  all: try match goal with H : forall i, ?σ' i = unf_o (?σ i) |- context [?σ' ?u] => rewrite (H u) end.
  (* the instantiated globals: by the object's sort *)
  all: try match goal with |- context [unf_o (?σ ?u)] => destruct (σ u) end; cbn [unf_o pty ptm pdef pctx unf_ty unf_tm unf_ctx].
  all: try reflexivity.
  all: try (f_equal; unf_lsub; rewrite ?llk_unf; solve [auto]).
  all: try (rewrite unf_subst_ty || rewrite unf_subst); try (f_equal; unf_lsub; rewrite ?llk_unf; solve [auto]).
  (* gdef: renamed or inlined, the instance of the unfolded body *)
  match goal with |- unf_tm (pdef (?σ ?u) _ _) = _ => destruct (σ u) end;
    cbn [pdef]; rewrite ?unf_subst; cbn [unf_tm].
  all: match goal with |- _ = gsubst_tm (subst_tm ?b ?e) ?σ' =>
         rewrite (proj1 (proj2 gsubst_subst_all) b e σ' (glsubst e σ')) by (intros; apply llk_glsubst) end.
  all: f_equal; [solve [auto] | unf_lsub; solve [auto]].
Qed.
Lemma unf_gsubst_ty (T : ty) σ : unf_ty (gsubst_ty T σ) = gsubst_ty (unf_ty T) (fun i => unf_o (σ i)).
Proof. apply (proj1 unf_gsubst_all); reflexivity. Qed.
Lemma unf_gsubst (t : tm) σ : unf_tm (gsubst_tm t σ) = gsubst_tm (unf_tm t) (fun i => unf_o (σ i)).
Proof. apply (proj1 (proj2 unf_gsubst_all)); reflexivity. Qed.
Lemma unf_gsubst_ctx (Γ : ctx) σ : unf_ctx (gcsubst Γ σ) = gcsubst (unf_ctx Γ) (fun i => unf_o (σ i)).
Proof. apply (proj1 (proj2 (proj2 unf_gsubst_all))); reflexivity. Qed.
Lemma unf_glsubst d σ : unf_l (glsubst d σ) = glsubst (unf_l d) (fun i => unf_o (σ i)).
Proof. unf_lsub. apply unf_gsubst. Qed.

(** The single global substitutions of the β rules and the recursors' peels. *)
Lemma unf_gsingle_ty (T : ty) o : unf_ty (gsubst_ty T (gsingle o)) = gsubst_ty (unf_ty T) (gsingle (unf_o o)).
Proof. apply (proj1 unf_gsubst_all); intros [|i]; reflexivity. Qed.
Lemma unf_gsingle (t : tm) o : unf_tm (gsubst_tm t (gsingle o)) = gsubst_tm (unf_tm t) (gsingle (unf_o o)).
Proof. apply (proj1 (proj2 unf_gsubst_all)); intros [|i]; reflexivity. Qed.


(** ** Idempotence

    [unf] is a normal form: a second pass changes nothing. The model of
    Heather's [docs/no-uip-model.md] (§4) stores box values unfolded, and
    needs this to read a stored value as its own normal form. The [gdef]
    case is [unf_subst] and the induction hypothesis on the body; the
    local substitutions are equal lookup-wise ([unf_l_canon]: [unf_l]'s
    outputs are normal). *)

Lemma unf_l_idem_of d : LK (fun t => unf_tm (unf_tm t) = unf_tm t) d -> unf_l (unf_l d) = unf_l d.
Proof. intros H; apply unf_l_canon; [auto with nf | intros n; rewrite llk_unf; apply H]. Qed.

Lemma unf_idem_all :
  let Pty T := unf_ty (unf_ty T) = unf_ty T in
  let Ptm t := unf_tm (unf_tm t) = unf_tm t in
  let Pctx Γ := unf_ctx (unf_ctx Γ) = unf_ctx Γ in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, LK Ptm d).
Proof.
  syn_start3; try lk_cases; cbn [unf_ty unf_tm unf_ctx]; try solve [f_equal; auto using unf_l_idem_of].
  (* gdef *)
  rewrite unf_subst. f_equal; auto using unf_l_idem_of.
Qed.
Lemma unf_idem_ty (T : ty) : unf_ty (unf_ty T) = unf_ty T. Proof. apply (proj1 unf_idem_all). Qed.
Lemma unf_idem (t : tm) : unf_tm (unf_tm t) = unf_tm t. Proof. apply (proj1 (proj2 unf_idem_all)). Qed.
Lemma unf_idem_ctx (Γ : ctx) : unf_ctx (unf_ctx Γ) = unf_ctx Γ. Proof. apply (proj1 (proj2 (proj2 unf_idem_all))). Qed.
Lemma unf_l_idem d : unf_l (unf_l d) = unf_l d.
Proof. apply unf_l_idem_of; intros n; apply unf_idem. Qed.
Lemma unf_o_idem o : unf_o (unf_o o) = unf_o o.
Proof. destruct o; cbn; f_equal; auto using unf_idem_ctx, unf_idem_ty, unf_idem. Qed.

(** ** Normal forms and level equivalence *)

Lemma unf_dnf_all :
  let Pty T := dnfty T -> dnfty (unf_ty T) in
  let Ptm t := dnftm t -> dnftm (unf_tm t) in
  let Pctx Γ := dnfctx Γ -> dnfctx (unf_ctx Γ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, dnfl d -> dnfl (unf_l d)).
Proof.
  intros Pty Ptm Pctx; apply syn_ind; subst Pty Ptm Pctx; cbn beta; intros; try exact I;
    cbn [unf_ty unf_tm unf_ctx unf_l dnfty dnftm dnfctx dnfl] in *; try tauto.
  all: try (repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; auto; fail).
  - (* gdef *) destruct H1 as [Hb Hd]. apply subst_dnf; [exact (H Hb) | intros n; exact (dnfl_llk _ n (H0 Hd))].
  - (* lcons *) destruct H1 as (Hd & Ht & _). apply dnfl_lcons'; auto.
Qed.
Lemma unf_dnf_ty T : dnfty T -> dnfty (unf_ty T). Proof. apply (proj1 unf_dnf_all). Qed.
Lemma unf_dnf t : dnftm t -> dnftm (unf_tm t). Proof. apply (proj1 (proj2 unf_dnf_all)). Qed.
Lemma unf_dnf_ctx Γ : dnfctx Γ -> dnfctx (unf_ctx Γ). Proof. apply (proj1 (proj2 (proj2 unf_dnf_all))). Qed.
Lemma unf_dnfl d : dnfl d -> dnfl (unf_l d). Proof. apply (proj2 (proj2 (proj2 unf_dnf_all))). Qed.

Lemma unf_leq_all :
  let Pty T := forall T', ty_leq T T' -> ty_leq (unf_ty T) (unf_ty T') in
  let Ptm t := forall t', tm_leq t t' -> tm_leq (unf_tm t) (unf_tm t') in
  let Pctx Γ := forall Γ', ctx_leq Γ Γ' -> ctx_leq (unf_ctx Γ) (unf_ctx Γ') in
  let Pl d := forall d', lsub_leq d d' -> lsub_leq (unf_l d) (unf_l d') in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, Pl d).
Proof.
  leq_start; try leq_cases; cbn [unf_ty unf_tm unf_ctx unf_l] in *; cbn in *; try contradiction;
    intuition (subst; eauto using lcons'_leq with leq).
  apply (proj1 (proj2 leq_subst_all)); auto.
Qed.
Lemma unf_ty_leq T T' : ty_leq T T' -> ty_leq (unf_ty T) (unf_ty T'). Proof. apply (proj1 unf_leq_all). Qed.
Lemma unf_tm_leq t t' : tm_leq t t' -> tm_leq (unf_tm t) (unf_tm t'). Proof. apply (proj1 (proj2 unf_leq_all)). Qed.

(** ** Definition-free syntax *)

Fixpoint gfree_ty (T : ty) {struct T} : Prop :=
  match T with
  | tyErr => True | tyNat => True
  | tyPi l l' A B => gfree_ty A /\ gfree_ty B
  | tyU l => True
  | tyEl l t => gfree_tm t
  | tyGvar U d => gfree_l d
  | tyCTyp Δ l => gfree_ctx Δ
  | tyCTrm Δ T l => gfree_ctx Δ /\ gfree_ty T
  | tyUPi n l T => gfree_ty T
  | tyCPi l T => gfree_ty T
  | tyTPi Δ l l' T => gfree_ctx Δ /\ gfree_ty T
  | tySig l l' A B => gfree_ty A /\ gfree_ty B
  | tyUnit l => True
  | tySEq l A a b => gfree_ty A /\ gfree_tm a /\ gfree_tm b
  | tySEmpty l => True
  | tyId l A a b => gfree_ty A /\ gfree_tm a /\ gfree_tm b
  | tyEmpty l => True
  | tySum l l' A B => gfree_ty A /\ gfree_ty B
  | tyW l l' A B => gfree_ty A /\ gfree_ty B
  | tyVec l A n => gfree_ty A /\ gfree_tm n
  | tyWf l A N => gfree_ty A /\ gfree_tm N
  | tySq l A => gfree_ty A
  | tyDVec l n F => gfree_tm n /\ gfree_ty F
  | tyIWf l li X A N Ot C m => (gfree_ty X) /\ (gfree_ty A) /\ (gfree_tm N) /\ (gfree_tm Ot) /\ (gfree_tm C) /\ (gfree_tm m)
  | tyM l l' li X A B C j => gfree_ty X /\ gfree_ty A /\ gfree_ty B /\ gfree_tm C /\ gfree_tm j
  | tyFin n => gfree_tm n
  end
with gfree_tm (t : tm) {struct t} : Prop :=
  match t with
  | var n => True
  | tmErr => True | tmNat => True | tmU l => True | zero => True
  | tmPi l l' s t => gfree_tm s /\ gfree_tm t
  | succ t => gfree_tm t
  | natrec l M s z t => gfree_ty M /\ gfree_tm s /\ gfree_tm z /\ gfree_tm t
  | lam l l' A t => gfree_ty A /\ gfree_tm t
  | app t l l' A B s => gfree_tm t /\ gfree_ty A /\ gfree_ty B /\ gfree_tm s
  | gvar u d => gfree_l d
  | boxT T => gfree_ty T
  | boxt t => gfree_tm t
  | letboxT l' l Δ M t' t => gfree_ctx Δ /\ gfree_ty M /\ gfree_tm t' /\ gfree_tm t
  | letboxt l' l Δ T M t' t => gfree_ctx Δ /\ gfree_ty T /\ gfree_ty M /\ gfree_tm t' /\ gfree_tm t
  | tmTy T => gfree_ty T
  | tmTup s t => gfree_tm s /\ gfree_tm t
  | bindU b => gfree_tm b
  | bindG b => gfree_tm b
  | bindL b => gfree_tm b
  | elimT l1 l2 rb l Δ t => gfree_tm rb /\ gfree_ctx Δ /\ gfree_tm t
  | elimt l1 l2 rb l Δ T t => gfree_tm rb /\ gfree_ctx Δ /\ gfree_ty T /\ gfree_tm t
  | ulam n l T t => gfree_ty T /\ gfree_tm t
  | uapp t ls => gfree_tm t
  | clam l T t => gfree_ty T /\ gfree_tm t
  | capp t Δ => gfree_tm t /\ gfree_ctx Δ
  | tlam Δ l l' T t => gfree_ctx Δ /\ gfree_ty T /\ gfree_tm t
  | tapp t T => gfree_tm t /\ gfree_ty T
  | tmSig l l' s t => gfree_tm s /\ gfree_tm t
  | tmPair l l' A B a b => gfree_ty A /\ gfree_ty B /\ gfree_tm a /\ gfree_tm b
  | tmFst l l' A B p => gfree_ty A /\ gfree_ty B /\ gfree_tm p
  | tmSnd l l' A B p => gfree_ty A /\ gfree_ty B /\ gfree_tm p
  | tmUnit l => True
  | tmTriv l => True
  | srefl l A a => gfree_ty A /\ gfree_tm a
  | elimSEmpty l l' M e => gfree_ty M /\ gfree_tm e
  | tmRefl l A a => gfree_ty A /\ gfree_tm a
  | tmId l s t u => gfree_tm s /\ gfree_tm t /\ gfree_tm u
  | tmSEq l s t u => gfree_tm s /\ gfree_tm t /\ gfree_tm u
  | tmSEmpty l => True
  | tmEmpty l => True
  | tmSum l l' s t => gfree_tm s /\ gfree_tm t
  | tmW l l' s t => gfree_tm s /\ gfree_tm t
  | tmVec l s n => gfree_tm s /\ gfree_tm n
  | tmFin n => gfree_tm n
  | tmWf _ s n => gfree_tm s /\ gfree_tm n
  | elimEmpty l l' M t => gfree_ty M /\ gfree_tm t
  | tmInl l l' A B a => gfree_ty A /\ gfree_ty B /\ gfree_tm a
  | tmInr l l' A B a => gfree_ty A /\ gfree_ty B /\ gfree_tm a
  | tmCase l l' l'' A B M c1 c2 t => gfree_ty A /\ gfree_ty B /\ gfree_ty M /\ gfree_tm c1 /\ gfree_tm c2 /\ gfree_tm t
  | tmSup l l' A B a f => gfree_ty A /\ gfree_ty B /\ gfree_tm a /\ gfree_tm f
  | tmElimW l l' l'' A B M c t => gfree_ty A /\ gfree_ty B /\ gfree_ty M /\ gfree_tm c /\ gfree_tm t
  | tmSupf l A N a cs => gfree_ty A /\ gfree_tm N /\ gfree_tm a /\ gfree_tm cs
  | tmElimWf l l' A N M c t => gfree_ty A /\ gfree_tm N /\ gfree_ty M /\ gfree_tm c /\ gfree_tm t
  | tmSq l A a => gfree_ty A /\ gfree_tm a
  | tmElimSq l l' A M c t => gfree_ty A /\ gfree_ty M /\ gfree_tm c /\ gfree_tm t
  | tmSqCode _ s => gfree_tm s
  | tmDVec _ n f => gfree_tm n /\ gfree_tm f
  | tmIWf _ _ x s n o c m => gfree_tm x /\ gfree_tm s /\ gfree_tm n /\ gfree_tm o /\ gfree_tm c /\ gfree_tm m
  | tmSupi l li X A N Ot C a cs => (gfree_ty X) /\ (gfree_ty A) /\ (gfree_tm N) /\ (gfree_tm Ot) /\ (gfree_tm C) /\ (gfree_tm a) /\ (gfree_tm cs)
  | tmElimIWf l li l' X A N Ot C M c m t =>
      (gfree_ty X) /\ (gfree_ty A) /\ (gfree_tm N) /\ (gfree_tm Ot) /\ (gfree_tm C) /\ (gfree_ty M) /\ (gfree_tm c) /\ (gfree_tm m) /\ (gfree_tm t)
  | tmCorec l l' li X A B C k Y c j y =>
      gfree_ty X /\ gfree_ty A /\ gfree_ty B /\ gfree_tm C /\ gfree_ty Y /\ gfree_tm c /\ gfree_tm j /\ gfree_tm y
  | tmOut l l' li X A B C j m => gfree_ty X /\ gfree_ty A /\ gfree_ty B /\ gfree_tm C /\ gfree_tm j /\ gfree_tm m
  | tmUnsq l t => gfree_tm t
  | tmJ l l' A a M c u e => gfree_ty A /\ gfree_tm a /\ gfree_ty M /\ gfree_tm c /\ gfree_tm u /\ gfree_tm e
  | gdef u b d => False
  end
with gfree_ctx (Γ : ctx) {struct Γ} : Prop :=
  match Γ with
  | cnil => True | cvar g => True | cext Γ A l => gfree_ctx Γ /\ gfree_ty A
  end
with gfree_l (d : lsub) {struct d} : Prop :=
  match d with lshift _ => True | lcons d t => gfree_l d /\ gfree_tm t end.

Definition gfree_o (o : gobj) : Prop :=
  match o with GId _ => True | GCtx Γ => gfree_ctx Γ | GTy T => gfree_ty T | GTm t => gfree_tm t end.

(** A substitution is definition-free iff its lookups are (whatever its shape). *)
Lemma gfree_l_lk d : gfree_l d <-> LK gfree_tm d.
Proof.
  induction d as [k | d IH t]; cbn [gfree_l]; split.
  - intros _ n; exact I.
  - intros _; exact I.
  - intros [Hd Ht] [|n]; cbn; [exact Ht | exact (proj1 IH Hd n)].
  - intros H; split; [apply IH; intros n; exact (H (S n)) | exact (H 0)].
Qed.

Ltac gf_lsub := apply gfree_l_lk; intros ?n;
  repeat first [ rewrite llk_lren | rewrite llk_lcomp | rewrite llk_glren | rewrite llk_glsubst
               | rewrite llk_ulren | rewrite llk_ulsubst | rewrite llk_unf ].

Ltac gf_ih := match goal with IH : gfree_l ?d -> LK _ ?d, Hd : gfree_l ?d |- _ =>
  eapply (IH Hd); first [apply (proj1 (gfree_l_lk _) Hd) | eauto with unf] end.
Ltac gf_lcons := match goal with
  | IHd : gfree_l ?d -> LK _ ?d, IHt : _, Hd : gfree_l ?d |- LK _ (lcons ?d ?t) =>
      intros [|?n]; cbn [llk]; [exact IHt | exact (IHd Hd _)] end.

Ltac gf_auto := cbn in *; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat split; eauto with unf.

Lemma gfree_ren_all :
  let Pty T := gfree_ty T -> forall r, gfree_ty (ren_ty T r) in
  let Ptm t := gfree_tm t -> forall r, gfree_tm (ren_tm t r) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, gfree_l d -> LK Ptm d).
Proof.
  syn_start; gf_auto.
  all: try (gf_lsub; gf_ih).
  gf_lcons.
Qed.
Lemma gfree_ren_ty T r : gfree_ty T -> gfree_ty (ren_ty T r). Proof. intros H; exact (proj1 gfree_ren_all T H r). Qed.
Lemma gfree_ren t r : gfree_tm t -> gfree_tm (ren_tm t r). Proof. intros H; exact (proj1 (proj2 gfree_ren_all) t H r). Qed.
#[export] Hint Resolve gfree_ren_ty gfree_ren : unf.

Lemma gfree_gren_all :
  let Pty T := gfree_ty T -> forall ξ, gfree_ty (gren_ty T ξ) in
  let Ptm t := gfree_tm t -> forall ξ, gfree_tm (gren_tm t ξ) in
  let Pctx Γ := gfree_ctx Γ -> forall ξ, gfree_ctx (gcren Γ ξ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, gfree_l d -> LK Ptm d).
Proof. syn_start3; gf_auto. all: try (gf_lsub; gf_ih). gf_lcons. Qed.
Lemma gfree_gren_ty T ξ : gfree_ty T -> gfree_ty (gren_ty T ξ). Proof. intros H; exact (proj1 gfree_gren_all T H ξ). Qed.
Lemma gfree_gren t ξ : gfree_tm t -> gfree_tm (gren_tm t ξ). Proof. intros H; exact (proj1 (proj2 gfree_gren_all) t H ξ). Qed.
Lemma gfree_gren_ctx Γ ξ : gfree_ctx Γ -> gfree_ctx (gcren Γ ξ). Proof. intros H; exact (proj1 (proj2 (proj2 gfree_gren_all)) Γ H ξ). Qed.
#[export] Hint Resolve gfree_gren_ty gfree_gren gfree_gren_ctx : unf.

Lemma gfree_uren_all :
  let Pty T := gfree_ty T -> forall ρ, gfree_ty (uren_ty T ρ) in
  let Ptm t := gfree_tm t -> forall ρ, gfree_tm (uren_tm t ρ) in
  let Pctx Γ := gfree_ctx Γ -> forall ρ, gfree_ctx (ucren Γ ρ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, gfree_l d -> LK Ptm d).
Proof. syn_start3; gf_auto. all: try (gf_lsub; gf_ih). gf_lcons. Qed.
Lemma gfree_uren_ty T ρ : gfree_ty T -> gfree_ty (uren_ty T ρ). Proof. intros H; exact (proj1 gfree_uren_all T H ρ). Qed.
Lemma gfree_uren t ρ : gfree_tm t -> gfree_tm (uren_tm t ρ). Proof. intros H; exact (proj1 (proj2 gfree_uren_all) t H ρ). Qed.
Lemma gfree_uren_ctx Γ ρ : gfree_ctx Γ -> gfree_ctx (ucren Γ ρ). Proof. intros H; exact (proj1 (proj2 (proj2 gfree_uren_all)) Γ H ρ). Qed.
#[export] Hint Resolve gfree_uren_ty gfree_uren gfree_uren_ctx : unf.

Lemma gfree_usubst_all :
  let Pty T := gfree_ty T -> forall φ, gfree_ty (usubst_ty T φ) in
  let Ptm t := gfree_tm t -> forall φ, gfree_tm (usubst_tm t φ) in
  let Pctx Γ := gfree_ctx Γ -> forall φ, gfree_ctx (ucsubst Γ φ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, gfree_l d -> LK Ptm d).
Proof. syn_start3; gf_auto. all: try (gf_lsub; gf_ih). gf_lcons. Qed.
Lemma gfree_usubst_ty T φ : gfree_ty T -> gfree_ty (usubst_ty T φ). Proof. intros H; exact (proj1 gfree_usubst_all T H φ). Qed.
Lemma gfree_usubst t φ : gfree_tm t -> gfree_tm (usubst_tm t φ). Proof. intros H; exact (proj1 (proj2 gfree_usubst_all) t H φ). Qed.
#[export] Hint Resolve gfree_usubst_ty gfree_usubst : unf.

Lemma gfree_llift d : LK gfree_tm d -> LK gfree_tm (llift d).
Proof. intros H [|n]; rewrite llk_llift; [exact I | apply gfree_ren, H]. Qed.
Lemma gfree_gwk d : LK gfree_tm d -> LK gfree_tm (gwk d).
Proof. intros H n; unfold gwk; rewrite llk_glren; apply gfree_gren, H. Qed.
Lemma gfree_uwk d : LK gfree_tm d -> LK gfree_tm (uwk d).
Proof. intros H n; unfold uwk; rewrite llk_ulren; apply gfree_uren, H. Qed.
Lemma gfree_uwkn k d : LK gfree_tm d -> LK gfree_tm (uwkn k d).
Proof. intros H; induction k; [exact H | change (uwkn (S k) d) with (uwk (uwkn k d)); apply gfree_uwk, IHk]. Qed.
#[export] Hint Resolve gfree_llift gfree_gwk gfree_uwk gfree_uwkn : unf.

Lemma gfree_subst_all :
  let Pty T := gfree_ty T -> forall d, LK gfree_tm d -> gfree_ty (subst_ty T d) in
  let Ptm t := gfree_tm t -> forall d, LK gfree_tm d -> gfree_tm (subst_tm t d) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall G : ctx, True) /\ (forall d, gfree_l d -> LK Ptm d).
Proof.
  syn_start; gf_auto.
  all: try (gf_lsub; gf_ih).
  all: try gf_lcons.
  intros n _ d Hd; cbn; apply Hd.
Qed.
Lemma gfree_subst_ty T d : gfree_ty T -> LK gfree_tm d -> gfree_ty (subst_ty T d).
Proof. intros H; exact (proj1 gfree_subst_all T H d). Qed.
Lemma gfree_subst t d : gfree_tm t -> LK gfree_tm d -> gfree_tm (subst_tm t d).
Proof. intros H; exact (proj1 (proj2 gfree_subst_all) t H d). Qed.
#[export] Hint Resolve gfree_subst_ty gfree_subst : unf.

Lemma gfree_o_goren o ξ : gfree_o o -> gfree_o (goren o ξ).
Proof. destruct o; cbn; auto with unf. Qed.
Lemma gfree_o_gouren o ρ : gfree_o o -> gfree_o (gouren o ρ).
Proof. destruct o; cbn; auto with unf. Qed.
Lemma gfree_gup σ : (forall i, gfree_o (σ i)) -> forall i, gfree_o (gup σ i).
Proof. intros H [|i]; cbn; [exact I | apply gfree_o_goren, H]. Qed.
Lemma gfree_guwk σ : (forall i, gfree_o (σ i)) -> forall i, gfree_o (guwk σ i).
Proof. intros H i; apply gfree_o_gouren, H. Qed.
Lemma gfree_guwkn k σ : (forall i, gfree_o (σ i)) -> forall i, gfree_o (guwkn k σ i).
Proof. intros H; induction k; [exact H | apply gfree_guwk, IHk]. Qed.
#[export] Hint Resolve gfree_gup gfree_guwk gfree_guwkn : unf.

Lemma gfree_gsubst_all :
  let Pty T := gfree_ty T -> forall σ, (forall i, gfree_o (σ i)) -> gfree_ty (gsubst_ty T σ) in
  let Ptm t := gfree_tm t -> forall σ, (forall i, gfree_o (σ i)) -> gfree_tm (gsubst_tm t σ) in
  let Pctx Γ := gfree_ctx Γ -> forall σ, (forall i, gfree_o (σ i)) -> gfree_ctx (gcsubst Γ σ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, gfree_l d -> LK Ptm d).
Proof.
  syn_start3; gf_auto; try contradiction.
  all: try gf_lcons.
  all: match goal with Hs : forall i, gfree_o (?σ i) |- context [?σ ?u] =>
         pose proof (Hs u); destruct (σ u) end; cbn in *; try solve [contradiction | auto].
  all: first [ gf_lsub; gf_ih
             | (apply gfree_subst_ty || apply gfree_subst); [assumption | intros ?n; rewrite llk_glsubst; gf_ih] ].
Qed.
Lemma gfree_gsubst_ty T σ : gfree_ty T -> (forall i, gfree_o (σ i)) -> gfree_ty (gsubst_ty T σ).
Proof. intros H; exact (proj1 gfree_gsubst_all T H σ). Qed.
Lemma gfree_gsubst t σ : gfree_tm t -> (forall i, gfree_o (σ i)) -> gfree_tm (gsubst_tm t σ).
Proof. intros H; exact (proj1 (proj2 gfree_gsubst_all) t H σ). Qed.
Lemma gfree_gsingle o : gfree_o o -> forall i, gfree_o (gsingle o i).
Proof. intros H [|i]; [exact H | exact I]. Qed.
#[export] Hint Resolve gfree_gsubst_ty gfree_gsubst gfree_gsingle : unf.

(** The translation's outputs mention no definition. *)
Lemma unf_gfree_all :
  let Pty T := gfree_ty (unf_ty T) in
  let Ptm t := gfree_tm (unf_tm t) in
  let Pctx Γ := gfree_ctx (unf_ctx Γ) in
  (forall T, Pty T) /\ (forall t, Ptm t) /\ (forall Γ, Pctx Γ) /\ (forall d, gfree_l (unf_l d)).
Proof.
  intros Pty Ptm Pctx; apply syn_ind; subst Pty Ptm Pctx; cbn beta; intros;
    cbn [unf_ty unf_tm unf_ctx unf_l gfree_ty gfree_tm gfree_ctx gfree_l]; try tauto.
  - (* gdef *) apply gfree_subst; [assumption | apply gfree_l_lk; assumption].
  - (* lcons *) apply gfree_l_lk. intros n. rewrite llk_lcons'. destruct n; cbn; [assumption |].
    apply (proj1 (gfree_l_lk _)); assumption.
Qed.
Lemma unf_gfree_ty T : gfree_ty (unf_ty T). Proof. apply unf_gfree_all. Qed.
Lemma unf_gfree t : gfree_tm (unf_tm t). Proof. apply unf_gfree_all. Qed.
Lemma unf_gfree_ctx Γ : gfree_ctx (unf_ctx Γ). Proof. apply unf_gfree_all. Qed.

(** ** Reduction keeps syntax definition-free *)

Lemma gfree_tup_nth t k : gfree_tm t -> gfree_tm (tup_nth t k).
Proof. revert t; induction k; intros t H; destruct t; cbn in *; try exact I; try tauto; apply IHk; tauto. Qed.
Lemma gfree_rb_br rb k : gfree_tm rb -> gfree_tm (rb_br rb k).
Proof. apply gfree_tup_nth. Qed.
Lemma gfree_peelU b l : gfree_tm b -> gfree_tm (peelU b l).
Proof. destruct b; cbn; auto with unf. Qed.
Lemma gfree_peelG b o : gfree_tm b -> gfree_o o -> gfree_tm (peelG b o).
Proof. destruct b; cbn; auto with unf. Qed.
Lemma gfree_lsingle a : gfree_tm a -> LK gfree_tm (lsingle a).
Proof. intros H [|n]; cbn; auto. Qed.
Lemma gfree_lsingle2 a b : gfree_tm a -> gfree_tm b -> LK gfree_tm (lsingle2 a b).
Proof. intros Ha Hb [|[|n]]; cbn; auto. Qed.
Lemma gfree_lsingle3 a b c : gfree_tm a -> gfree_tm b -> gfree_tm c -> LK gfree_tm (lsingle3 a b c).
Proof. intros Ha Hb Hc [|[|[|n]]]; cbn; auto. Qed.
Lemma gfree_lsucc : LK gfree_tm lsucc.
Proof. intros [|n]; cbn; auto. Qed.
#[export] Hint Resolve gfree_lsingle gfree_lsingle2 gfree_lsingle3 gfree_lsucc : unf.
Lemma gfree_peelL b a : gfree_tm b -> gfree_tm a -> gfree_tm (peelL b a).
Proof. destruct b; cbn; auto using gfree_lsingle with unf. Qed.

Ltac gf_peel := repeat first
  (* by the goal's head: a failing [apply] of a peeling lemma unfolds its
     conclusion against the goal (85% of [gfree_redt], as in [redt_leq]) *)
  [ lazymatch goal with
    | |- gfree_tm (peelL _ _) => apply gfree_peelL
    | |- gfree_tm (peelG _ _) => apply gfree_peelG
    | |- gfree_tm (peelU _ _) => apply gfree_peelU
    | |- gfree_tm (rb_br _ _) => apply gfree_rb_br
    | |- gfree_ty (ren _ _) => apply gfree_ren_ty
    | |- gfree_ty (ren_ty _ _) => apply gfree_ren_ty
    | |- gfree_tm (ren _ _) => apply gfree_ren
    | |- gfree_tm (ren_tm _ _) => apply gfree_ren
    end
  | progress cbn [gfree_o gfree_tm gfree_ty gfree_ctx recT rect]
  | lazymatch goal with |- _ /\ _ => split end | assumption
  | apply gfree_subst_ty; [| repeat apply gfree_llift;
                              first [apply gfree_lsingle | apply gfree_lsingle2 | apply gfree_lsingle3 | apply gfree_lsucc]]
  | apply gfree_subst; [| repeat apply gfree_llift;
                           first [apply gfree_lsingle | apply gfree_lsingle2 | apply gfree_lsingle3 | apply gfree_lsucc]]
  | exact I
  (* a definition over the syntax (the telescopes' types, [dnth]): unfolded
     only here, as a bare [split] on every goal would (M17c: 71% of
     [gfree_redt]) *)
  | progress hnf ].

Lemma gfree_redT l1 l2 rb l Δ c r : redT l1 l2 rb l Δ c = Some r ->
  gfree_tm rb -> gfree_ctx Δ -> gfree_ty c -> gfree_tm r.
Proof.
  intros E Hrb HΔ Hc. destruct c; cbn [redT] in E; inversion E; subst; cbn in Hc;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; gf_peel.
Qed.
Lemma gfree_redt l1 l2 rb l Δ T c r : redt l1 l2 rb l Δ T c = Some r ->
  gfree_tm rb -> gfree_ctx Δ -> gfree_ty T -> gfree_tm c -> gfree_tm r.
Proof.
  intros E Hrb HΔ HT Hc. destruct c; cbn [redt] in E; redt_case T; first [discriminate E | apply Some_inj in E; subst r]; cbn in Hc, HT;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; gf_peel.
Qed.

Lemma gfree_red_both :
  (forall t t', red t t' -> gfree_tm t -> gfree_tm t') /\
  (forall T T', red_ty T T' -> gfree_ty T -> gfree_ty T').
Proof.
  apply red_both; intros; cbn in *; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try solve [eapply gfree_redT; eauto | eapply gfree_redt; eauto]; try tauto.
  all: try unfold wIH, wfIH, tmNth, nthMot, nthBase, nthStep,
    iwfIH, iwfFam, tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS;
    gf_peel; auto with unf.
Qed.
Lemma gfree_red t t' : red t t' -> gfree_tm t -> gfree_tm t'. Proof. apply gfree_red_both. Qed.
Lemma gfree_red_ty T T' : red_ty T T' -> gfree_ty T -> gfree_ty T'. Proof. apply gfree_red_both. Qed.
Lemma gfree_reds t t' : reds t t' -> gfree_tm t -> gfree_tm t'.
Proof. induction 1; eauto using gfree_red. Qed.
Lemma gfree_reds_ty T T' : reds_ty T T' -> gfree_ty T -> gfree_ty T'.
Proof. induction 1; eauto using gfree_red_ty. Qed.
