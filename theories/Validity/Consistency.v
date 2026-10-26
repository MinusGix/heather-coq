(** * Consistency (08:48; M7_DESIGN.md A1)

    The paper: no closed term of [Π (x : Ty ℓ). x]. Here, more generally,
    at D and M, for a global context of context variables only (at D also
    with definitions: [closed_ok], M9) and a local context of universe
    variables only:
    - no type variable [El l (var n)] is inhabited ([no_type_var_inhabitant]);
    - no term has type [Π^{l1,l2} (x : Ty l). El l' x] ([consistency]).

    A term of a type variable has a neutral whnf: completeness gives an
    algorithmic derivation, and at a neutral type only the neutral rule
    applies. A neutral in such a context has a universe type
    ([neutral_univ]): its head is a local variable, and each eliminator's
    scrutinee would need a type former other than a universe. A universe
    is not a type variable (head discrimination).

    The [_gen] forms also cover a definition-free term ([gfree_tm]) in a
    global context of context variables and definitions, at M too: then
    no stuck [elim(box(u^δ))] occurs. [ConsistencyDef.v] reduces every
    term to that case by unfolding. *)
From DeLaM.Syntax Require Import Unfold.
From DeLaM.Validity Require Export AlgComplete Consequences.

(** A local context whose entries are universes. *)
Definition univ_ctx (Γ : ctx) : Prop := forall n T k, in_ctx Γ n T k -> exists l, T = tyU l.

Lemma univ_ctx_nil : univ_ctx cnil.
Proof. intros n T k Hin; inversion Hin. Qed.

Lemma univ_ctx_ext {Γ l k} : univ_ctx Γ -> univ_ctx (Γ ,, tyU l @ k).
Proof.
  intros HΓ n T k' Hin. inversion Hin as [Γ1 A1 l1 | Γ1 A1 l1 B1 l1' m Hm]; subst.
  - exists l; reflexivity.
  - destruct (HΓ _ _ _ Hm) as (l0 & ->). exists l0; reflexivity.
Qed.

(** A whnf type other than a universe is not equal to one. *)
Lemma not_univ {G i Γ W l k} : compt i -> whnf_ty W -> ty_head W <> 2 -> ~ [ G ; Γ ⊢[ i ] W ≅ tyU l @ k ].
Proof. intros Hc Hw Hh E. exact (Hh (decl_head_c Hc E Hw (whnf_tyU _))). Qed.

(** The scrutinee inherits [closed_ok i G \/ gfree_tm ν] from the neutral. *)
Ltac sub_ok Hok := destruct Hok as [?|?]; [left; assumption | right; cbn [gfree_tm] in *; tauto].

Ltac scrutinee_clash IH Hok :=
  match goal with H : [ _ ; _ ⊢[ _ ] _ : ?W @ _ ] |- _ =>
    let l0 := fresh "l0" in let E := fresh "E" in
    destruct (IH ltac:(sub_ok Hok) _ _ H) as (l0 & E); exfalso;
    refine (not_univ (W := W) _ _ _ E); [eassumption | auto with whnf | cbn; discriminate] end.

(** In a universe context, with context variables and definitions only
    globally, a typed neutral has a universe type when it mentions no
    definition, or when the global context is [closed_ok] (context
    variables only, or the layer is D). *)
Lemma neutral_univ_gen {G i Γ} : compt i -> no_opaque G -> univ_ctx Γ ->
  forall ν, whne ν -> closed_ok i G \/ gfree_tm ν ->
  forall A k, [ G ; Γ ⊢[ i ] ν : A @ k ] -> exists l, [ G ; Γ ⊢[ i ] A ≅ tyU l @ k ].
Proof.
  intros Hc HG HΓ. pose proof (compt_typeof_self _ Hc) as Hi.
  induction 1 as [n | u d | l M s z t Hn IH | t l1 l2 A0 B s Hn IH | l1 l2 Δ M t1 t Hn IH
                  | l1 l2 Δ T M t1 t Hn IH | l1 l2 rb l Δ t Hn IH | l1 l2 rb l Δ U d
                  | l1 l2 rb l Δ T t Hn IH | l1 l2 rb l Δ T u d | l1 l2 rb l Δ T u b d | t ls Hn IH | t Δ Hn IH | t T Hn IH
                  | l1 l2 A0 B p Hn IH | l1 l2 A0 B p Hn IH | l1 l2 M e Hn IH | l1 l2 M e Hn IH
                  | l1 l2 l3 A0 B M c1 c2 e Hn IH | l1 l2 l3 A0 B M c e Hn IH
                  | l1 l2 A0 N0 M c e Hn IH | l1 l2 A0 M c e Hn IH
                  | l1 l2 l3 X0 A0 N0 O0 C0 M c m0 e Hn IH | l1 l2 l3 X0 A0 B0 C0 j0 e Hn IH
                  | l1 l2 A0 a0 M c u e Hn IH];
    intros Hok X k Hx.
  - destruct (inv_var Hi Hx) as (T0 & l0 & (_ & Hin) & _ & E).
    destruct (HΓ _ _ _ Hin) as (l & ->). exists l; exact E.
  - destruct (inv_gvar Hi Hx) as (Δ & i' & T0 & l0 & (_ & Hin & _) & _). destruct (no_opaque_gvar HG Hin).
  - destruct (inv_natrec Hi Hx) as ((_ & _ & _ & _ & _ & Ht) & _). scrutinee_clash IH Hok.
  - destruct (inv_app Hi Hx) as ((_ & _ & _ & _ & _ & Ht & _) & _). scrutinee_clash IH Hok.
  - destruct (inv_letboxT Hi Hx) as ((-> & _ & _ & _ & _ & _ & Ht) & _). scrutinee_clash IH Hok.
  - destruct (inv_letboxt Hi Hx) as ((-> & _ & _ & _ & _ & _ & _ & Ht) & _). scrutinee_clash IH Hok.
  - destruct (inv_elimT Hi Hx) as (MT & Mt & bs & (_ & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht) & _).
    scrutinee_clash IH Hok.
  - destruct (inv_elimT Hi Hx) as (MT & Mt & bs & (_ & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht) & _).
    destruct (boxT_inv Ht) as (? & ? & HT). destruct (tyGvar_decl HT) as (? & ? & ? & Hin).
    destruct (no_opaque_tyGvar HG Hin).
  - destruct (inv_elimt Hi Hx) as (MT & Mt & bs & (_ & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht) & _).
    scrutinee_clash IH Hok.
  - destruct (inv_elimt Hi Hx) as (MT & Mt & bs & (_ & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht) & _).
    destruct (boxt_inv Ht) as (? & ? & ? & Ht'). destruct (gvar_decl Ht') as (? & ? & ? & ? & Hin).
    destruct (no_opaque_gvar HG Hin).
  - destruct (inv_elimt Hi Hx) as (MT & Mt & bs & (_ & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht) & _).
    destruct (boxt_inv Ht) as (? & ? & ? & Ht'). destruct (gdef_decl Ht') as (? & ? & ? & ? & Hin).
    destruct Hok as [Hok | Hok]; [discriminate (closed_ok_M_ctx_only Hok _ _ Hin) | cbn in Hok; tauto].
  - destruct (inv_uapp Hi Hx) as (n & l & T0 & (-> & _ & _ & _ & _ & Ht) & _). scrutinee_clash IH Hok.
  - destruct (inv_capp Hi Hx) as (l & T0 & (-> & _ & _ & _ & Ht & _) & _). scrutinee_clash IH Hok.
  - destruct (inv_tapp Hi Hx) as (Δ0 & l & l' & T0 & (-> & Ht & _) & _). scrutinee_clash IH Hok.
  - destruct (inv_fst Hi Hx) as ((_ & _ & _ & _ & _ & Hp) & _). scrutinee_clash IH Hok.
  - destruct (inv_snd Hi Hx) as ((_ & _ & _ & _ & _ & Hp) & _). scrutinee_clash IH Hok.
  - destruct (inv_elimSEmpty Hi Hx) as ((_ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
  - destruct (inv_elimEmpty Hi Hx) as ((_ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
  - destruct (inv_case Hi Hx) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
  - destruct (inv_elimW Hi Hx) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
  - destruct (inv_elimWf Hi Hx) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
  - destruct (inv_elimSq Hi Hx) as ((_ & _ & _ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
  - destruct (inv_elimIWf Hi Hx)
      as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
  - destruct (inv_out Hi Hx) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
  - destruct (inv_J Hi Hx) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & He) & _). scrutinee_clash IH Hok.
Qed.

Lemma neutral_univ {G i Γ} : compt i -> closed_ok i G -> univ_ctx Γ ->
  forall ν, whne ν -> forall A k, [ G ; Γ ⊢[ i ] ν : A @ k ] -> exists l, [ G ; Γ ⊢[ i ] A ≅ tyU l @ k ].
Proof. intros Hc HG HΓ ν Hn. exact (neutral_univ_gen Hc (closed_ok_no_opaque HG) HΓ ν Hn (or_introl HG)). Qed.

(** ** No inhabitant of a type variable *)

Theorem no_type_var_inhabitant_gen {G i Γ t l n k} : compt i -> no_opaque G -> univ_ctx Γ ->
  closed_ok i G \/ gfree_tm t -> ~ [ G ; Γ ⊢[ i ] t : tyEl l (var n) @ k ].
Proof.
  intros Hc HG HΓ Hok Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (HV : whnf_ty (tyEl l (var n))) by (constructor; constructor; constructor).
  destruct (ainv_tm (ac_complete_tm Hc (eqtm_refl _ _ _ _ _ _ Ht)))
    as (W & w & w' & HrT & HwT & Hr & _ & Hw & _ & D).
  rewrite <- (reds_ty_whnf_det _ _ _ (Relation_Operators.rt1n_refl _ _ _) HrT HV HwT) in D.
  assert (Hn : whne w) by (inversion D; subst; exact (proj1 (ac_tmnee_whne ltac:(eassumption)))).
  pose proof (eqtm_wf_r Hi (red_tm_sound Hc Ht Hr Hw)) as Hw0.
  assert (Hokw : closed_ok i G \/ gfree_tm w) by (destruct Hok; [left | right; eapply gfree_reds]; eassumption).
  destruct (neutral_univ_gen Hc HG HΓ w Hn Hokw _ _ Hw0) as (l0 & E).
  exact (not_univ Hc HV ltac:(cbn; discriminate) E).
Qed.

Theorem no_type_var_inhabitant {G i Γ t l n k} : compt i -> closed_ok i G -> univ_ctx Γ ->
  ~ [ G ; Γ ⊢[ i ] t : tyEl l (var n) @ k ].
Proof. intros Hc HG HΓ. exact (no_type_var_inhabitant_gen Hc (closed_ok_no_opaque HG) HΓ (or_introl HG)). Qed.

(** ** Consistency *)

Theorem consistency_gen {G i Γ t l1 l2 l l' k} : compt i -> no_opaque G -> univ_ctx Γ ->
  closed_ok i G \/ gfree_tm t -> ~ [ G ; Γ ⊢[ i ] t : tyPi l1 l2 (tyU l) (tyEl l' (var 0)) @ k ].
Proof.
  intros Hc HG HΓ Hok Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi (wf_tm_ty Hi Ht)) as ((Hv & W1 & W2 & HA & HB) & Hk).
  refine (no_type_var_inhabitant_gen Hc HG (univ_ctx_ext HΓ) _
           (pre_eta_body Hi Hv W1 W2 HA HB (lvl_eq_tm' Hk Ht))).
  destruct Hok; [left; assumption | right; cbn; auto using gfree_ren, gfree_ren_ty].
Qed.

Theorem consistency {G i Γ t l1 l2 l l' k} : compt i -> closed_ok i G -> univ_ctx Γ ->
  ~ [ G ; Γ ⊢[ i ] t : tyPi l1 l2 (tyU l) (tyEl l' (var 0)) @ k ].
Proof. intros Hc HG HΓ. exact (consistency_gen Hc (closed_ok_no_opaque HG) HΓ (or_introl HG)). Qed.

(** The paper's statement: the empty local context. *)
Corollary consistency_closed {G i t l1 l2 l l' k} : compt i -> closed_ok i G ->
  ~ [ G ; cnil ⊢[ i ] t : tyPi l1 l2 (tyU l) (tyEl l' (var 0)) @ k ].
Proof. intros Hc HG. exact (consistency Hc HG univ_ctx_nil). Qed.
