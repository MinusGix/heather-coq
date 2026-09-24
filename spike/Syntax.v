(** * Syntax spike: DeLaM's local + global substitution structure, by hand.

    Representative fragment (types are terms; levels/Tarski omitted -- both are
    orthogonal, plain structure):
    - local variables [var n] (de Bruijn), local binders [pi]/[lam];
    - global variables with a stored local substitution [gvar u δ]  (u^δ);
    - context variables [cvar g] in contexts; a global context binder [cpi]/[clam];
    - separate code scopes: [boxT Γ T], [quote c] are untouched by local subst;
    - [letbox Γ T M body t]: [M] under a local binder, [body] under a global one.

    Design (see SYNTAX_SPIKE.md):
    - A context variable is an unknown-length block of de Bruijn indices, so a
      local substitution is a finite cons-list ending in a shift [lshift k]
      (the paper's [·ᵏ] and [wkᵏ_g] tails are both "shift by k"; which one it is
      is typing information, not syntax).
    - Every operation builds its output with the smart constructor [lcons'],
      which absorbs redundant trailing variables, so OUTPUTS ARE CANONICAL.
      Substitution arguments are then only ever used through their lookups.
    - Global variables are de Bruijn in ONE index space (like the paper's single
      Ψ); a global substitution is a meta-level function to [gobj], whose [GId]
      makes identity/renaming sort-agnostic. *)

From Coq Require Import Arith Lia.
Set Implicit Arguments.

(** ** Syntax *)

Inductive rsub : Type := rshift (k : nat) | rcons (r : rsub) (n : nat).

Inductive tm : Type :=
| var (n : nat)
| err                                   (* junk: result of an ill-sorted global lookup *)
| tnat
| pi (A B : tm) | lam (A t : tm) | app (t u : tm)
| gvar (u : nat) (d : lsub)             (* u^δ *)
| cpi (T : tm) | clam (t : tm)          (* bind a global context variable *)
| capp (t : tm) (G : ctx)
| boxT (G : ctx) (T : tm)               (* □(Γ ⊢ T): separate local scope *)
| quote (c : tm)                        (* box c: separate local scope *)
| letbox (G : ctx) (T M body t : tm)    (* M: +1 local; body: +1 global *)
with ctx : Type := cnil | cvar (g : nat) | cext (G : ctx) (A : tm)
with lsub : Type := lshift (k : nat) | lcons (d : lsub) (t : tm).

Scheme tm_ind' := Induction for tm Sort Prop
  with ctx_ind' := Induction for ctx Sort Prop
  with lsub_ind' := Induction for lsub Sort Prop.
Combined Scheme syn_ind from tm_ind', ctx_ind', lsub_ind'.

(** ** Renamings (entries are indices; no term recursion needed) *)

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

Fixpoint rup (r : rsub) : rsub :=            (* r ; ↑ *)
  match r with rshift k => rshift (S k) | rcons r m => rcons (rup r) (S m) end.

Definition rlift (r : rsub) : rsub := rcons (rup r) 0.

(** ** Local substitutions: lookup, the canonicalising constructor, drop *)

Fixpoint llk (d : lsub) (n : nat) : tm :=
  match d with
  | lshift k => var (n + k)
  | lcons d t => match n with 0 => t | S n => llk d n end
  end.

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

Fixpoint ren (t : tm) (r : rsub) {struct t} : tm :=
  match t with
  | var n => var (rlk r n)
  | err => err | tnat => tnat
  | pi A B => pi (ren A r) (ren B (rlift r))
  | lam A b => lam (ren A r) (ren b (rlift r))
  | app t u => app (ren t r) (ren u r)
  | gvar u d => gvar u (lren d r)
  | cpi T => cpi (ren T r) | clam t => clam (ren t r)
  | capp t G => capp (ren t r) G
  | boxT G T => boxT G T | quote c => quote c
  | letbox G T M body t => letbox G T (ren M (rlift r)) (ren body r) (ren t r)
  end
with lren (d : lsub) (r : rsub) {struct d} : lsub :=
  match d with
  | lshift k => r2l (rdrop k r)
  | lcons d t => lcons' (lren d r) (ren t r)
  end.

Definition shift1 : rsub := rshift 1.
Definition llift (d : lsub) : lsub := lcons' (lren d shift1) (var 0).

(** ** Global renaming (needed by local substitution under global binders) *)

Inductive gobj : Type := GId (j : nat) | GCtx (G : ctx) | GTm (t : tm).

Definition gupr (ξ : nat -> nat) : nat -> nat :=
  fun n => match n with 0 => 0 | S n => S (ξ n) end.

Fixpoint gren (t : tm) (ξ : nat -> nat) {struct t} : tm :=
  match t with
  | var n => var n
  | err => err | tnat => tnat
  | pi A B => pi (gren A ξ) (gren B ξ)
  | lam A b => lam (gren A ξ) (gren b ξ)
  | app t u => app (gren t ξ) (gren u ξ)
  | gvar u d => gvar (ξ u) (glren d ξ)
  | cpi T => cpi (gren T (gupr ξ)) | clam t => clam (gren t (gupr ξ))
  | capp t G => capp (gren t ξ) (gcren G ξ)
  | boxT G T => boxT (gcren G ξ) (gren T ξ) | quote c => quote (gren c ξ)
  | letbox G T M body t =>
      letbox (gcren G ξ) (gren T ξ) (gren M ξ) (gren body (gupr ξ)) (gren t ξ)
  end
with gcren (G : ctx) (ξ : nat -> nat) {struct G} : ctx :=
  match G with cnil => cnil | cvar g => cvar (ξ g) | cext G A => cext (gcren G ξ) (gren A ξ) end
with glren (d : lsub) (ξ : nat -> nat) {struct d} : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (glren d ξ) (gren t ξ) end.

(** ** Local substitution *)

(** Under a GLOBAL binder, a local substitution's entries must be globally
    shifted: the one cross-dimension cost of de Bruijn globals. *)
Definition gwk (d : lsub) : lsub := glren d S.


Fixpoint subst (t : tm) (d : lsub) {struct t} : tm :=
  match t with
  | var n => llk d n
  | err => err | tnat => tnat
  | pi A B => pi (subst A d) (subst B (llift d))
  | lam A b => lam (subst A d) (subst b (llift d))
  | app t u => app (subst t d) (subst u d)
  | gvar u d' => gvar u (lcomp d' d)
  | cpi T => cpi (subst T (gwk d)) | clam t => clam (subst t (gwk d))
  | capp t G => capp (subst t d) G
  | boxT G T => boxT G T | quote c => quote c
  | letbox G T M body t => letbox G T (subst M (llift d)) (subst body (gwk d)) (subst t d)
  end
with lcomp (d' : lsub) (d : lsub) {struct d'} : lsub :=   (* d' ∘ d *)
  match d' with
  | lshift k => lnorm (ldrop k d)
  | lcons d' t => lcons' (lcomp d' d) (subst t d)
  end.

(** ** Global substitution *)

Definition goren (o : gobj) (ξ : nat -> nat) : gobj :=
  match o with GId j => GId (ξ j) | GCtx G => GCtx (gcren G ξ) | GTm t => GTm (gren t ξ) end.

Definition gup (σ : nat -> gobj) : nat -> gobj :=
  fun n => match n with 0 => GId 0 | S n => goren (σ n) S end.

(** Instantiate a global object at a use site [u^δ] / [g]. *)
Definition ptm (o : gobj) (d : lsub) : tm :=
  match o with GId j => gvar j d | GTm s => subst s d | GCtx _ => err end.
Definition pctx (o : gobj) : ctx :=
  match o with GId j => cvar j | GCtx G => G | GTm _ => cnil end.

Fixpoint gsubst (t : tm) (σ : nat -> gobj) {struct t} : tm :=
  match t with
  | var n => var n
  | err => err | tnat => tnat
  | pi A B => pi (gsubst A σ) (gsubst B σ)
  | lam A b => lam (gsubst A σ) (gsubst b σ)
  | app t u => app (gsubst t σ) (gsubst u σ)
  | gvar u d => ptm (σ u) (glsubst d σ)                (* σ(u)[δ[σ]] *)
  | cpi T => cpi (gsubst T (gup σ)) | clam t => clam (gsubst t (gup σ))
  | capp t G => capp (gsubst t σ) (gcsubst G σ)
  | boxT G T => boxT (gcsubst G σ) (gsubst T σ) | quote c => quote (gsubst c σ)
  | letbox G T M body t =>
      letbox (gcsubst G σ) (gsubst T σ) (gsubst M σ) (gsubst body (gup σ)) (gsubst t σ)
  end
with gcsubst (G : ctx) (σ : nat -> gobj) {struct G} : ctx :=
  match G with cnil => cnil | cvar g => pctx (σ g) | cext G A => cext (gcsubst G σ) (gsubst A σ) end
with glsubst (d : lsub) (σ : nat -> gobj) {struct d} : lsub :=
  match d with lshift k => lshift k | lcons d t => lcons' (glsubst d σ) (gsubst t σ) end.

Definition gosubst (o : gobj) (τ : nat -> gobj) : gobj :=
  match o with GId j => τ j | GCtx G => GCtx (gcsubst G τ) | GTm t => GTm (gsubst t τ) end.

(** ** Canonical form of local substitutions *)

Definition labsorb (d : lsub) (t : tm) : Prop :=
  match d, t with lshift (S k), var m => m = k | _, _ => False end.

Fixpoint nf_l (d : lsub) : Prop :=
  match d with lshift _ => True | lcons d t => nf_l d /\ ~ labsorb d t end.

Lemma llk_lcons' d t n : llk (lcons' d t) n = llk (lcons d t) n.
Proof.
  destruct d as [[|k]|]; destruct t; cbn; auto.
  destruct (Nat.eqb_spec n0 k) as [->|]; destruct n; cbn; f_equal; lia.
Qed.

Lemma nf_lcons' d t : nf_l d -> nf_l (lcons' d t).
Proof.
  destruct d as [[|k]|]; destruct t; cbn; try tauto.
  destruct (Nat.eqb_spec n k); cbn; auto.
Qed.

Lemma nf_lnorm d : nf_l (lnorm d).
Proof. induction d; cbn; auto using nf_lcons'. Qed.
Lemma llk_lnorm d n : llk (lnorm d) n = llk d n.
Proof.
  revert n; induction d; intros n; cbn; auto.
  rewrite llk_lcons'. destruct n; cbn; auto.
Qed.

(** Canonicity: normal local substitutions are equal iff their lookups are. *)
Lemma shift_canon d k : nf_l d -> (forall n, llk d n = var (n + k)) -> d = lshift k.
Proof.
  revert k; induction d as [k'|d IH t]; intros k Hnf H.
  - specialize (H 0); cbn in H. injection H as ->. reflexivity.
  - cbn in Hnf; destruct Hnf as [Hd Hab].
    pose proof (H 0) as Ht; cbn in Ht; subst t.
    assert (d = lshift (S k)) as ->.
    { apply IH; auto. intros n. specialize (H (S n)); cbn in H. rewrite H. f_equal; lia. }
    cbn in Hab. exfalso; auto.
Qed.

Lemma l_canon d1 d2 : nf_l d1 -> nf_l d2 -> (forall n, llk d1 n = llk d2 n) -> d1 = d2.
Proof.
  revert d2; induction d1 as [k1|d1 IH t1]; intros d2 N1 N2 H.
  - symmetry; apply shift_canon; auto. intros n; now rewrite <- H.
  - destruct d2 as [k2|d2 t2].
    + apply shift_canon; auto.
    + cbn in N1, N2; destruct N1, N2. f_equal.
      * apply IH; auto. intros n; exact (H (S n)).
      * exact (H 0).
Qed.

(** ** Lookup lemmas *)

Lemma rlk_rdrop k r n : rlk (rdrop k r) n = rlk r (k + n).
Proof. revert r; induction k; intros [m|r m]; cbn; auto; lia. Qed.
Lemma rlk_rup r n : rlk (rup r) n = S (rlk r n).
Proof. revert n; induction r as [k|r IH m]; intros [|n]; cbn; auto; lia. Qed.
Lemma rlk_rlift r n :
  rlk (rlift r) n = match n with 0 => 0 | S n => S (rlk r n) end.
Proof. destruct n; cbn; auto using rlk_rup. Qed.
Lemma llk_r2l r n : llk (r2l r) n = var (rlk r n).
Proof. revert n; induction r as [k|r IH m]; intros n; cbn; auto. rewrite llk_lcons'. destruct n; cbn; auto. Qed.
Lemma nf_r2l r : nf_l (r2l r).
Proof. induction r; cbn; auto using nf_lcons'. Qed.
Lemma llk_ldrop k d n : llk (ldrop k d) n = llk d (k + n).
Proof. revert d; induction k; intros [m|d t]; cbn; auto; f_equal; lia. Qed.

Lemma llk_lren d r n : llk (lren d r) n = ren (llk d n) r.
Proof.
  revert n; induction d as [k|d IH t]; intros n; cbn.
  - rewrite llk_r2l, rlk_rdrop. do 2 f_equal; lia.
  - rewrite llk_lcons'. destruct n; cbn; auto.
Qed.
Lemma nf_lren d r : nf_l (lren d r).
Proof. induction d; cbn; auto using nf_r2l, nf_lcons'. Qed.

Lemma llk_glren d ξ n : llk (glren d ξ) n = gren (llk d n) ξ.
Proof. revert n; induction d as [k|d IH t]; intros n; cbn; auto. rewrite llk_lcons'. destruct n; cbn; auto. Qed.
Lemma nf_glren d ξ : nf_l (glren d ξ).
Proof. induction d; cbn; auto using nf_lcons'. Qed.

Lemma llk_lcomp d' d n : llk (lcomp d' d) n = subst (llk d' n) d.
Proof.
  revert n; induction d' as [k|d' IH t]; intros n; cbn.
  - rewrite llk_lnorm, llk_ldrop. f_equal; lia.
  - rewrite llk_lcons'. destruct n; cbn; auto.
Qed.
Lemma nf_lcomp d' d : nf_l (lcomp d' d).
Proof. induction d'; cbn; auto using nf_lnorm, nf_lcons'. Qed.

Lemma llk_glsubst d σ n : llk (glsubst d σ) n = gsubst (llk d n) σ.
Proof. revert n; induction d as [k|d IH t]; intros n; cbn; auto. rewrite llk_lcons'. destruct n; cbn; auto. Qed.
Lemma nf_glsubst d σ : nf_l (glsubst d σ).
Proof. induction d; cbn; auto using nf_lcons'. Qed.

Lemma llk_llift d n :
  llk (llift d) n = match n with 0 => var 0 | S n => ren (llk d n) shift1 end.
Proof. unfold llift; rewrite llk_lcons'; destruct n; cbn; auto using llk_lren. Qed.
Lemma nf_llift d : nf_l (llift d).
Proof. apply nf_lcons', nf_lren. Qed.

#[export] Hint Resolve nf_lren nf_glren nf_lcomp nf_glsubst nf_llift nf_r2l nf_lnorm : nf.

(** Generic shape of every law: a statement about terms, lifted to local
    substitutions through their lookups (the [gvar] case uses canonicity). *)
Definition LK (P : tm -> Prop) (d : lsub) : Prop := forall n, P (llk d n).

Ltac lk_cases var_case :=
  match goal with
  | |- LK _ (lshift _) => intros ?n; cbn; intros; first [reflexivity | eapply var_case; eauto]
  | IHd : LK _ ?d |- LK _ (lcons ?d ?t) =>
      intros [|?n]; cbn; [assumption | exact (IHd _)]
  end.

(** Start a law: mutual induction, beta-reduce the motives, introduce. *)
Ltac syn_start := intros ?P; apply syn_ind; subst P; cbn beta; intros; try exact I.

(** Close an equation between two operation-built local substitutions. *)
Ltac lsub_eq :=
  apply l_canon; [auto with nf | auto with nf | intros ?n];
  repeat first [ rewrite llk_lren | rewrite llk_glren | rewrite llk_lcomp
               | rewrite llk_glsubst ].

(** Default handling of a term case: congruence, then (for [gvar]) canonicity. *)
Ltac law_auto :=
  cbn; try solve [eauto with subst | symmetry; eauto with subst];
  try solve [f_equal; eauto with subst];
  try solve [f_equal; try lsub_eq; eauto with subst].

(** ** Local renaming laws *)

Lemma ren_ext_var n r r' : (forall n, rlk r n = rlk r' n) -> ren (var n) r = ren (var n) r'.
Proof. intros H; cbn; now rewrite H. Qed.

Lemma rlift_ext r r' : (forall n, rlk r n = rlk r' n) -> forall n, rlk (rlift r) n = rlk (rlift r') n.
Proof. intros H [|n]; rewrite !rlk_rlift; auto. Qed.
#[export] Hint Resolve rlift_ext : subst.

Lemma ren_ext_all :
  let P t := forall r r', (forall n, rlk r n = rlk r' n) -> ren t r = ren t r' in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases ren_ext_var); law_auto. Qed.

Lemma ren_ren_var n r1 r2 r3 : (forall n, rlk r3 n = rlk r2 (rlk r1 n)) ->
  ren (ren (var n) r1) r2 = ren (var n) r3.
Proof. intros H; cbn; now rewrite H. Qed.
Lemma rlift_comp r1 r2 r3 : (forall n, rlk r3 n = rlk r2 (rlk r1 n)) ->
  forall n, rlk (rlift r3) n = rlk (rlift r2) (rlk (rlift r1) n).
Proof. intros H [|n]; rewrite !rlk_rlift; auto. Qed.
#[export] Hint Resolve rlift_comp : subst.

Lemma ren_ren_all :
  let P t := forall r1 r2 r3, (forall n, rlk r3 n = rlk r2 (rlk r1 n)) ->
             ren (ren t r1) r2 = ren t r3 in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases ren_ren_var); law_auto. all: now rewrite H. Qed.
Definition ren_ren t := proj1 ren_ren_all t.
Definition ren_ext t := proj1 ren_ext_all t.

(** ** Global renaming laws *)

Lemma gupr_ext ξ ζ : (forall i, ξ i = ζ i) -> forall i, gupr ξ i = gupr ζ i.
Proof. intros H [|i]; cbn; auto. Qed.
Lemma gupr_comp ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> forall i, gupr θ i = gupr ζ (gupr ξ i).
Proof. intros H [|i]; cbn; auto. Qed.
#[export] Hint Resolve gupr_ext gupr_comp : subst.

Lemma gren_ext_var n ξ ζ : (forall i, ξ i = ζ i) -> gren (var n) ξ = gren (var n) ζ.
Proof. reflexivity. Qed.
Lemma gren_ext_all :
  let P t := forall ξ ζ, (forall i, ξ i = ζ i) -> gren t ξ = gren t ζ in
  (forall t, P t) /\ (forall G, forall ξ ζ, (forall i, ξ i = ζ i) -> gcren G ξ = gcren G ζ)
  /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases gren_ext_var); law_auto. Qed.
Definition gren_ext t := proj1 gren_ext_all t.

Lemma gren_gren_var n ξ ζ θ : gren (gren (var n) ξ) ζ = gren (var n) θ.
Proof. reflexivity. Qed.
Lemma gren_gren_all :
  let P t := forall ξ ζ θ, (forall i, θ i = ζ (ξ i)) -> gren (gren t ξ) ζ = gren t θ in
  (forall t, P t) /\
  (forall G, forall ξ ζ θ, (forall i, θ i = ζ (ξ i)) -> gcren (gcren G ξ) ζ = gcren G θ)
  /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases (fun n => @gren_gren_var n)); law_auto. Qed.
Definition gren_gren t := proj1 gren_gren_all t.

(** Local renaming commutes with global renaming. *)
Lemma gren_ren_var n r ξ : gren (ren (var n) r) ξ = ren (gren (var n) ξ) r.
Proof. reflexivity. Qed.
Lemma gren_ren_all :
  let P t := forall r ξ, gren (ren t r) ξ = ren (gren t ξ) r in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases gren_ren_var); law_auto. Qed.
Definition gren_ren t := proj1 gren_ren_all t.

(** ** Local substitution laws *)

Lemma llift_ext d d' : (forall n, llk d n = llk d' n) -> forall n, llk (llift d) n = llk (llift d') n.
Proof. intros H [|n]; rewrite !llk_llift; auto. now rewrite H. Qed.
Lemma gwk_ext d d' : (forall n, llk d n = llk d' n) -> forall n, llk (gwk d) n = llk (gwk d') n.
Proof. intros H n; unfold gwk; rewrite !llk_glren; now rewrite H. Qed.
#[export] Hint Resolve llift_ext gwk_ext : subst.

Lemma subst_ext_all :
  let P t := forall d d', (forall n, llk d n = llk d' n) -> subst t d = subst t d' in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases (fun n d d' (H : forall n, llk d n = llk d' n) => H n)); law_auto. Qed.
Definition subst_ext t := proj1 subst_ext_all t.

Lemma llift_rcomp r d d' : (forall n, llk d' n = llk d (rlk r n)) ->
  forall n, llk (llift d') n = llk (llift d) (rlk (rlift r) n).
Proof. intros H [|n]; rewrite rlk_rlift, !llk_llift; auto. now rewrite H. Qed.
Lemma gwk_rcomp r d d' : (forall n, llk d' n = llk d (rlk r n)) ->
  forall n, llk (gwk d') n = llk (gwk d) (rlk r n).
Proof. intros H n; unfold gwk; rewrite !llk_glren; now rewrite H. Qed.
#[export] Hint Resolve llift_rcomp gwk_rcomp : subst.

Lemma ren_subst_all :
  let P t := forall r d d', (forall n, llk d' n = llk d (rlk r n)) -> subst (ren t r) d = subst t d' in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof.
  syn_start; try (lk_cases (fun n r d d' (H : forall n, llk d' n = llk d (rlk r n)) => eq_sym (H n)));
    law_auto.
  all: now rewrite H.
Qed.
Definition ren_subst t := proj1 ren_subst_all t.

(** Global renaming distributes over local substitution. *)
Lemma llift_gren d d' ξ : (forall n, llk d' n = gren (llk d n) ξ) ->
  forall n, llk (llift d') n = gren (llk (llift d) n) ξ.
Proof. intros H [|n]; rewrite !llk_llift; auto. rewrite H. symmetry; apply gren_ren. Qed.
Lemma gwk_gren d d' ξ : (forall n, llk d' n = gren (llk d n) ξ) ->
  forall n, llk (gwk d') n = gren (llk (gwk d) n) (gupr ξ).
Proof.
  intros H n; unfold gwk; rewrite !llk_glren, H.
  rewrite !(gren_gren _ _ _ (fun i => S (ξ i))); auto.
Qed.
#[export] Hint Resolve llift_gren gwk_gren : subst.

Lemma gren_subst_all :
  let P t := forall d d' ξ, (forall n, llk d' n = gren (llk d n) ξ) ->
             gren (subst t d) ξ = subst (gren t ξ) d' in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof.
  syn_start; try (lk_cases (fun n d d' ξ (H : forall n, llk d' n = gren (llk d n) ξ) => eq_sym (H n)));
    law_auto.
  all: now rewrite H.
Qed.
Definition gren_subst t := proj1 gren_subst_all t.

Lemma rup_shift_l r m : rlk (rup r) m = rlk shift1 (rlk r m).
Proof. rewrite rlk_rup; cbn; lia. Qed.
Lemma rup_shift_r r m : rlk (rup r) m = rlk (rlift r) (rlk shift1 m).
Proof. unfold shift1; cbn [rlk]; rewrite Nat.add_1_r, rlk_rlift, rlk_rup; reflexivity. Qed.

Lemma llift_ren r d d' : (forall n, llk d' n = ren (llk d n) r) ->
  forall n, llk (llift d') n = ren (llk (llift d) n) (rlift r).
Proof.
  intros H [|n]; rewrite !llk_llift; auto. rewrite H.
  rewrite (ren_ren _ _ _ _ (rup_shift_l r)), (ren_ren _ _ _ _ (rup_shift_r r)); reflexivity.
Qed.
Lemma gwk_ren r d d' : (forall n, llk d' n = ren (llk d n) r) ->
  forall n, llk (gwk d') n = ren (llk (gwk d) n) r.
Proof. intros H n; unfold gwk; rewrite !llk_glren, H. apply gren_ren. Qed.
#[export] Hint Resolve llift_ren gwk_ren : subst.

Lemma subst_ren_all :
  let P t := forall d d' r, (forall n, llk d' n = ren (llk d n) r) -> ren (subst t d) r = subst t d' in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof.
  syn_start; try (lk_cases (fun n d d' r (H : forall n, llk d' n = ren (llk d n) r) => eq_sym (H n)));
    law_auto.
  all: now rewrite H.
Qed.
Definition subst_ren t := proj1 subst_ren_all t.

Lemma llift_subst d d' d'' : (forall n, llk d'' n = subst (llk d n) d') ->
  forall n, llk (llift d'') n = subst (llk (llift d) n) (llift d').
Proof.
  intros H [|n]; rewrite !llk_llift; cbn [subst]; rewrite ?llk_llift; [reflexivity|].
  rewrite H, (subst_ren _ _ (lren d' shift1)) by (intros; apply llk_lren).
  symmetry; apply ren_subst. intros m.
  rewrite llk_lren; unfold shift1 at 2; cbn [rlk]; rewrite Nat.add_1_r, llk_llift; reflexivity.
Qed.
Lemma gwk_subst d d' d'' : (forall n, llk d'' n = subst (llk d n) d') ->
  forall n, llk (gwk d'') n = subst (llk (gwk d) n) (gwk d').
Proof.
  intros H n; unfold gwk; rewrite !llk_glren, H.
  apply gren_subst. intros m; apply llk_glren.
Qed.
#[export] Hint Resolve llift_subst gwk_subst : subst.

Lemma subst_subst_all :
  let P t := forall d d' d'', (forall n, llk d'' n = subst (llk d n) d') ->
             subst (subst t d) d' = subst t d'' in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof.
  syn_start; try (lk_cases (fun n d d' d'' (H : forall n, llk d'' n = subst (llk d n) d') => eq_sym (H n)));
    law_auto.
  all: now rewrite H.
Qed.
Definition subst_subst t := proj1 subst_subst_all t.

(** Composition as an equation on the stored syntax: [(t[δ])[ρ] = t[δ∘ρ]]. *)
Corollary subst_lcomp t d d' : subst (subst t d) d' = subst t (lcomp d d').
Proof. apply subst_subst. intros; apply llk_lcomp. Qed.

Print Assumptions subst_lcomp.

(** ** Identity laws: the only laws needing the input in normal form *)

Fixpoint nft (t : tm) : Prop :=
  match t with
  | var _ | err | tnat => True
  | pi A B | lam A B | app A B => nft A /\ nft B
  | gvar _ d => nfl d
  | cpi T | clam T | quote T => nft T
  | capp t G => nft t /\ nfc G
  | boxT G T => nfc G /\ nft T
  | letbox G T M b t => nfc G /\ nft T /\ nft M /\ nft b /\ nft t
  end
with nfc (G : ctx) : Prop :=
  match G with cnil | cvar _ => True | cext G A => nfc G /\ nft A end
with nfl (d : lsub) : Prop :=
  match d with lshift _ => True | lcons d t => nfl d /\ nft t /\ ~ labsorb d t end.

Lemma nfl_nf d : nfl d -> nf_l d.
Proof. induction d; cbn; tauto. Qed.
Lemma nfl_llk d n : nfl d -> nft (llk d n).
Proof. revert n; induction d as [k|d IH t]; intros [|n] H; cbn in *; try tauto. apply IH; tauto. Qed.
#[export] Hint Resolve nfl_nf nfl_llk : nf.

Lemma llift_id d : (forall n, llk d n = var n) -> forall n, llk (llift d) n = var n.
Proof. intros H [|n]; rewrite llk_llift; auto. rewrite H; cbn; f_equal; lia. Qed.
Lemma gwk_id d : (forall n, llk d n = var n) -> forall n, llk (gwk d) n = var n.
Proof. intros H n; unfold gwk; rewrite llk_glren, H; reflexivity. Qed.
#[export] Hint Resolve llift_id gwk_id : subst.

(** Lookup motive with a normal-form precondition. *)
Ltac lk_cases_nf :=
  match goal with
  | |- LK _ (lshift _) => intros ?n; cbn; intros; auto
  | Hn : nfl (lcons ?d ?t), IHd : nfl ?d -> LK _ ?d |- LK _ (lcons ?d ?t) =>
      cbn in Hn; destruct Hn as (?Hd & ?Ht & ?Ha);
      intros [|?n]; cbn; [assumption | exact (IHd ltac:(assumption) _)]
  end.

Lemma subst_id_all :
  let P t := nft t -> forall d, (forall n, llk d n = var n) -> subst t d = t in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, nfl d -> LK P d).
Proof.
  syn_start; try lk_cases_nf; cbn in *; try tauto;
    try solve [f_equal; intuition eauto with subst].
  (* gvar: canonicity against the (normal) stored substitution *)
  f_equal. apply l_canon; auto with nf. intros n. rewrite llk_lcomp.
  apply H; auto with nf.
Qed.
Definition subst_id t := proj1 subst_id_all t.

Lemma ren_as_subst_all :
  let P t := forall r d, (forall n, llk d n = var (rlk r n)) -> ren t r = subst t d in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof.
  assert (Hl : forall r d, (forall n, llk d n = var (rlk r n)) ->
            forall n, llk (llift d) n = var (rlk (rlift r) n)).
  { intros r d H [|n]; rewrite llk_llift, rlk_rlift; auto. rewrite H; cbn; f_equal; lia. }
  assert (Hg : forall r d, (forall n, llk d n = var (rlk r n)) ->
            forall n, llk (gwk d) n = var (rlk r n)).
  { intros r d H n; unfold gwk; rewrite llk_glren, H; reflexivity. }
  syn_start; try (lk_cases (fun n r d (H : forall n, llk d n = var (rlk r n)) => eq_sym (H n)));
    cbn; try solve [symmetry; auto]; try solve [f_equal; eauto].
  f_equal; lsub_eq; eauto.
Qed.
Definition ren_as_subst t := proj1 ren_as_subst_all t.

(** ** Global substitution laws *)

Lemma gup_ext σ τ : (forall i, σ i = τ i) -> forall i, gup σ i = gup τ i.
Proof. intros H [|i]; cbn; auto. now rewrite H. Qed.
Lemma gup_gupr ξ σ τ : (forall i, τ i = σ (ξ i)) -> forall i, gup τ i = gup σ (gupr ξ i).
Proof. intros H [|i]; cbn; auto. now rewrite H. Qed.
#[export] Hint Resolve gup_ext gup_gupr : subst.

Lemma gsubst_ext_all :
  let P t := forall σ τ, (forall i, σ i = τ i) -> gsubst t σ = gsubst t τ in
  (forall t, P t) /\ (forall G, forall σ τ, (forall i, σ i = τ i) -> gcsubst G σ = gcsubst G τ)
  /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases I); law_auto. Qed.
Definition gsubst_ext t := proj1 gsubst_ext_all t.

Lemma gsubst_gren_all :
  let P t := forall ξ σ τ, (forall i, τ i = σ (ξ i)) -> gsubst (gren t ξ) σ = gsubst t τ in
  (forall t, P t) /\
  (forall G, forall ξ σ τ, (forall i, τ i = σ (ξ i)) -> gcsubst (gcren G ξ) σ = gcsubst G τ)
  /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases I); law_auto. Qed.
Definition gsubst_gren t := proj1 gsubst_gren_all t.

Lemma goren_goren o ξ ζ θ : (forall i, θ i = ζ (ξ i)) -> goren (goren o ξ) ζ = goren o θ.
Proof.
  intros H; destruct o; cbn; f_equal; auto.
  - now apply (proj1 (proj2 gren_gren_all)).
  - now apply gren_gren.
Qed.

Lemma ptm_gren o e ξ : gren (ptm o e) ξ = ptm (goren o ξ) (glren e ξ).
Proof. destruct o; cbn; auto. apply gren_subst. intros; apply llk_glren. Qed.
Lemma pctx_gren o ξ : gcren (pctx o) ξ = pctx (goren o ξ).
Proof. destruct o; reflexivity. Qed.

Lemma gup_goren σ τ ξ : (forall i, τ i = goren (σ i) ξ) -> forall i, gup τ i = goren (gup σ i) (gupr ξ).
Proof.
  intros H [|i]; cbn; auto. rewrite H.
  rewrite !(goren_goren _ _ _ (fun j => S (ξ j))); auto.
Qed.
#[export] Hint Resolve gup_goren : subst.

Lemma gren_gsubst_all :
  let P t := forall σ ξ τ, (forall i, τ i = goren (σ i) ξ) -> gren (gsubst t σ) ξ = gsubst t τ in
  (forall t, P t) /\
  (forall G, forall σ ξ τ, (forall i, τ i = goren (σ i) ξ) -> gcren (gcsubst G σ) ξ = gcsubst G τ)
  /\ (forall d, LK P d).
Proof.
  syn_start; try (lk_cases I); cbn; rewrite ?ptm_gren, ?pctx_gren; law_auto.
Qed.
Definition gren_gsubst t := proj1 gren_gsubst_all t.

(** Global substitution commutes with local renaming ... *)
Lemma ptm_ren o e r : ren (ptm o e) r = ptm o (lren e r).
Proof. destruct o; cbn; auto. apply subst_ren. intros; apply llk_lren. Qed.

Lemma gsubst_ren_all :
  let P t := forall r σ, gsubst (ren t r) σ = ren (gsubst t σ) r in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases I); cbn; rewrite ?ptm_ren; law_auto. Qed.
Definition gsubst_ren t := proj1 gsubst_ren_all t.

(** ... and with local substitution: [(t[δ])[σ] = (t[σ])[δ[σ]]]. *)
Lemma ptm_subst o e d : subst (ptm o e) d = ptm o (lcomp e d).
Proof. destruct o; cbn; auto. apply subst_lcomp. Qed.

Lemma llift_gsubst d d' σ : (forall n, llk d' n = gsubst (llk d n) σ) ->
  forall n, llk (llift d') n = gsubst (llk (llift d) n) σ.
Proof. intros H [|n]; rewrite !llk_llift; auto. rewrite H; symmetry; apply gsubst_ren. Qed.
Lemma gwk_gsubst d d' σ : (forall n, llk d' n = gsubst (llk d n) σ) ->
  forall n, llk (gwk d') n = gsubst (llk (gwk d) n) (gup σ).
Proof.
  intros H n; unfold gwk; rewrite !llk_glren, H.
  rewrite (gren_gsubst _ _ _ (fun i => goren (σ i) S)) by auto.
  symmetry; apply gsubst_gren; auto.
Qed.
#[export] Hint Resolve llift_gsubst gwk_gsubst : subst.

Lemma gsubst_subst_all :
  let P t := forall d σ d', (forall n, llk d' n = gsubst (llk d n) σ) ->
             gsubst (subst t d) σ = subst (gsubst t σ) d' in
  (forall t, P t) /\ (forall G : ctx, True) /\ (forall d, LK P d).
Proof.
  syn_start; try (lk_cases (fun n d σ d' (H : forall n, llk d' n = gsubst (llk d n) σ) => eq_sym (H n)));
    cbn; rewrite ?ptm_subst; law_auto.
Qed.
Definition gsubst_subst t := proj1 gsubst_subst_all t.

Corollary gsubst_subst_eq t d σ : gsubst (subst t d) σ = subst (gsubst t σ) (glsubst d σ).
Proof. apply gsubst_subst. intros; apply llk_glsubst. Qed.

(** Composition of global substitutions. *)
Lemma ptm_gsubst o e τ : gsubst (ptm o e) τ = ptm (gosubst o τ) (glsubst e τ).
Proof. destruct o; cbn; auto. apply gsubst_subst_eq. Qed.
Lemma pctx_gsubst o τ : gcsubst (pctx o) τ = pctx (gosubst o τ).
Proof. destruct o; reflexivity. Qed.

Lemma goren_gosubst o τ : goren (gosubst o τ) S = gosubst (goren o S) (gup τ).
Proof.
  destruct o; cbn; auto; f_equal.
  - rewrite (proj1 (proj2 gren_gsubst_all) _ _ _ (fun i => goren (τ i) S)) by auto.
    symmetry; apply (proj1 (proj2 gsubst_gren_all)); auto.
  - rewrite (gren_gsubst _ _ _ (fun i => goren (τ i) S)) by auto.
    symmetry; apply gsubst_gren; auto.
Qed.
Lemma gup_gosubst σ τ θ : (forall i, θ i = gosubst (σ i) τ) -> forall i, gup θ i = gosubst (gup σ i) (gup τ).
Proof. intros H [|i]; cbn; auto. rewrite H. apply goren_gosubst. Qed.
#[export] Hint Resolve gup_gosubst : subst.

Lemma gsubst_gsubst_all :
  let P t := forall σ τ θ, (forall i, θ i = gosubst (σ i) τ) -> gsubst (gsubst t σ) τ = gsubst t θ in
  (forall t, P t) /\
  (forall G, forall σ τ θ, (forall i, θ i = gosubst (σ i) τ) -> gcsubst (gcsubst G σ) τ = gcsubst G θ)
  /\ (forall d, LK P d).
Proof. syn_start; try (lk_cases I); cbn; rewrite ?ptm_gsubst, ?pctx_gsubst; law_auto. Qed.
Definition gsubst_gsubst t := proj1 gsubst_gsubst_all t.

Lemma gsubst_id_all :
  let P t := nft t -> forall σ, (forall i, σ i = GId i) -> gsubst t σ = t in
  (forall t, P t) /\ (forall G, nfc G -> forall σ, (forall i, σ i = GId i) -> gcsubst G σ = G)
  /\ (forall d, nfl d -> LK P d).
Proof.
  assert (Hup : forall σ, (forall i, σ i = GId i) -> forall i, gup σ i = GId i).
  { intros σ H [|i]; cbn; auto. now rewrite H. }
  syn_start; try lk_cases_nf; cbn in *; try tauto;
    try solve [f_equal; intuition eauto].
  all: match goal with Hs : forall i, ?σ i = GId i |- context [?σ ?u] => rewrite Hs; cbn end;
    try reflexivity.
  f_equal. apply l_canon; auto with nf. intros n.
  rewrite llk_glsubst. match goal with IH : nfl ?d -> LK _ ?d |- _ => apply IH end; auto with nf.
Qed.
Definition gsubst_id t := proj1 gsubst_id_all t.

Print Assumptions gsubst_gsubst.
Print Assumptions gsubst_subst_eq.

(** ** Conformance with the paper's substitution equations (ch. 5) *)

(** The paper's [wkᵏ_Γ] (hence identity [id_Γ = wk⁰_Γ]) as stored syntax. *)
Fixpoint wkctx (k : nat) (G : ctx) : lsub :=
  match G with cnil | cvar _ => lshift k | cext G _ => lcons (wkctx (S k) G) (var k) end.

Lemma llk_wkctx G k n : llk (wkctx k G) n = var (n + k).
Proof.
  revert k n; induction G as [|g|G IH A]; intros k [|n]; cbn; auto.
  rewrite IH; f_equal; lia.
Qed.

(** [wkᵏ_g[σ] = wkᵏ_{σ(g)}]: the paper's expansion of a context variable is
    invisible to lookups, so substituting with either is the same. *)
Lemma wk_expand t k g σ :
  subst t (glsubst (lshift k) σ) = subst t (wkctx k (pctx (σ g))).
Proof. apply subst_ext. intros n; cbn; now rewrite llk_wkctx. Qed.

Lemma id_ctx t G : nft t -> subst t (wkctx 0 G) = t.
Proof. intros; apply subst_id; auto. intros; rewrite llk_wkctx; f_equal; lia. Qed.

(** [u^δ[σ] = σ(u)[δ[σ]]] -- contextual instantiation, by definition. *)
Lemma gvar_inst u d σ s : σ u = GTm s -> gsubst (gvar u d) σ = subst s (glsubst d σ).
Proof. intros H; cbn; now rewrite H. Qed.

(** ** Single substitutions (β-rules) *)

Definition lsingle (a : tm) : lsub := lcons (lshift 0) a.         (* a/x *)
Definition gsingle (o : gobj) : nat -> gobj :=                     (* o/u *)
  fun i => match i with 0 => o | S i => GId i end.

(** Local β under a substitution: [b[a/x][δ] = b[⇑δ][a[δ]/x]]. *)
Lemma subst_single b a d : nfl d ->
  subst (subst b (lsingle a)) d = subst (subst b (llift d)) (lsingle (subst a d)).
Proof.
  intros Hd.
  rewrite (subst_subst b _ _ (lcons' d (subst a d))),
          (subst_subst b _ _ (lcons' d (subst a d))); auto.
  - intros [|n]; rewrite llk_lcons', llk_llift; cbn; auto.
    assert (Hs : forall m, llk (lshift 0) m = llk (lsingle (subst a d)) (rlk shift1 m)).
    { intros m; unfold shift1; cbn [rlk]; rewrite Nat.add_1_r; cbn; f_equal; lia. }
    rewrite (ren_subst _ _ _ _ Hs). symmetry; apply subst_id; auto with nf.
    intros; cbn; f_equal; lia.
  - intros [|n]; rewrite llk_lcons'; cbn; auto.
Qed.

(** Global β (letbox) under a global substitution:
    [b[o/u][σ] = b[⇑σ][o[σ]/u]] when σ's objects are normal. *)
Definition nfo (o : gobj) : Prop :=
  match o with GId _ => True | GCtx G => nfc G | GTm t => nft t end.

Lemma gsubst_single b o σ : (forall i, nfo (σ i)) ->
  gsubst (gsubst b (gsingle o)) σ = gsubst (gsubst b (gup σ)) (gsingle (gosubst o σ)).
Proof.
  intros Hσ.
  rewrite (gsubst_gsubst b _ _ (fun i => match i with 0 => gosubst o σ | S i => σ i end)),
          (gsubst_gsubst b _ _ (fun i => match i with 0 => gosubst o σ | S i => σ i end));
    auto; intros [|i]; cbn; auto.
  specialize (Hσ i); destruct (σ i) as [j|G|t]; cbn in *; auto; f_equal.
  - rewrite (proj1 (proj2 gsubst_gren_all) _ _ _ (fun j => GId j)) by auto.
    symmetry; apply (proj1 (proj2 gsubst_id_all)); auto.
  - rewrite (gsubst_gren _ _ _ (fun j => GId j)) by auto.
    symmetry; apply gsubst_id; auto.
Qed.

(** ** The equation McTT's letbox attempt lacked

    The letbox rule types its body at [Ψ, u : …] with the local context
    globally shifted.  Weakening through it needs shifting and renaming to
    commute on contexts -- here an unconditional instance of [gren_gren]. *)
Lemma letbox_ctx_weaken G ξ : gcren (gcren G ξ) S = gcren (gcren G S) (gupr ξ).
Proof.
  rewrite !(proj1 (proj2 gren_gren_all) G _ _ (fun i => S (ξ i))); auto.
Qed.

Print Assumptions subst_single.
Print Assumptions gsubst_single.
Print Assumptions letbox_ctx_weaken.
