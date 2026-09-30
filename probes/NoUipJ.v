(** * [Id] and Paulin-Mohring's [J] in the groupoid model

    Heather's [docs/no-uip-model.md] §2 and §4.5 cite Hofmann and
    Streicher for [Id] and [J]. This file mechanizes the construction for
    [J] as the development states it ([wf_J], [Typing/Declarative.v]),
    with the left endpoint fixed:

    - [IdF A a]: [Id(a↑; var 0)] over the comprehension [Γ.A], a split
      family whose fibre at [(g, y)] is the discrete set [A(g)(a(g), y)].
      A morphism [(α, f)] acts by [p ↦ f ∘ A(α)(p) ∘ a(α)⁻¹]. Its functor
      laws are [IdAct_id] and [IdAct_comp].
    - [IdT A a b]: [Id(a; b)] over [Γ], and [reflS]: [refl], the identity.
    - [J]: given a motive [M] over [Γ.A.Id(a↑; var 0)], a base case [c]
      over [⟨a, refl⟩], and [u] with [e : Id(a; u)], a section of [M]
      over [⟨u, e⟩], which is the rule's result type [M[u/y, e/p]]. At
      [g] it is [M]'s action on [c(g)] along [ι(g) = (id, e(g))]. Its
      morphism component is [c]'s, moved along [ι]. The one fact it needs
      is the [square], which is [e]'s section law: an equation, because
      the [Id] fibres are discrete. Both of [J]'s functor laws are proved
      ([J_sec_id], [J_sec_comp]).
    - β on the nose: at [u := a] and [e := refl], [ι] is the identity
      ([ι_refl]), so [J]'s objects are [c]'s ([J_beta_ob]) and its
      morphisms are [c]'s up to those equations ([J_beta_hom]).
    - Stability under a substitution [σ : Δ → Γ]: [J(M; c; u; e)[σ] =
      J(M[σ⁺⁺]; c[σ]; u[σ]; e[σ])], on objects ([J_stab_ob]) and on
      morphisms up to those equations ([J_stab_hom]). Here [σ⁺ = liftA]
      and [σ⁺⁺ = liftJ] lift [σ] through [Γ.A] and [Γ.A.Id], and [subS]
      reindexes sections. [Id] and [refl] are stable by conversion
      ([IdF_stab_fib], [IdF_stab_act], [refl_stab]). The one
      non-definitional step is [ι_stab]: [σ⁺⁺(ι(d)) = ι(σ(d))], from
      [σ]'s identity law.

    Groupoids here carry their laws, and their objects and morphisms form
    sets ([ob_set], [hom_set]), as in the set-theoretic model. This is what
    makes any two equations of the same objects give the same morphism
    ([eqh_irr]). A family is split: its functor laws hold on the nose. A
    section has its functor laws. The comprehensions are used only as
    category data: a family over them states its laws against their
    composition, and [J] needs none of their own laws. The context's
    unit laws are used, in [square].

    [refl]'s morphism component ([reflS_hom]) is transparent, so that
    [σ⁺⁺ ∘ ⟨a[σ], refl⟩] and [⟨a, refl⟩ ∘ σ] agree by conversion, and
    [c[σ]] is [c]'s components verbatim. [J_example] instantiates
    everything at the one-point context, which checks that the hypotheses
    are satisfiable. *)
From Coq Require Import Eqdep_dec PeanoNat.
Set Primitive Projections.
Set Implicit Arguments.

(** ** Groupoids, as sets with structure *)

Record Gpd := {
  ob : Type;
  hom : ob -> ob -> Type;
  idm : forall x, hom x x;
  comp : forall {x y z}, hom y z -> hom x y -> hom x z;
  inv : forall {x y}, hom x y -> hom y x;
  comp_idl : forall x y (f : hom x y), comp (idm y) f = f;
  comp_idr : forall x y (f : hom x y), comp f (idm x) = f;
  comp_assoc : forall w x y z (f : hom w x) (g : hom x y) (h : hom y z),
      comp h (comp g f) = comp (comp h g) f;
  inv_l : forall x y (f : hom x y), comp (inv f) f = idm x;
  inv_r : forall x y (f : hom x y), comp f (inv f) = idm y;
  ob_set : forall (x y : ob) (p q : x = y), p = q;
  hom_set : forall x y (f g : hom x y) (p q : f = g), p = q }.
Arguments idm {_} x.
Arguments comp {_ _ _ _} _ _.
Arguments inv {_ _ _} _.
Arguments comp_idl {_ _ _} _.
Arguments comp_idr {_ _ _} _.
Arguments comp_assoc {_ _ _ _ _} _ _ _.
Arguments inv_l {_ _ _} _.
Arguments inv_r {_ _ _} _.
Arguments ob_set {_ _ _} _ _.
Arguments hom_set {_ _ _ _ _} _ _.

Section G.
Context {G : Gpd}.

(** An equation of objects, as a morphism. *)
Definition eqh {x y : ob G} (E : x = y) : hom G x y := match E with eq_refl => idm x end.

Lemma eqh_irr {x y : ob G} (E1 E2 : x = y) : eqh E1 = eqh E2.
Proof. rewrite (ob_set E1 E2). reflexivity. Qed.
Lemma eqh_trans {x y z : ob G} (E1 : x = y) (E2 : y = z) : comp (eqh E2) (eqh E1) = eqh (eq_trans E1 E2).
Proof. destruct E2, E1. apply comp_idl. Qed.
Lemma inv_eqh {x y : ob G} (E : x = y) : inv (eqh E) = eqh (eq_sym E).
Proof. destruct E. cbn. rewrite <- (comp_idl (inv (idm x))). apply inv_r. Qed.

(** Right-associated normal forms, with cancellation. *)
Lemma comp_assoc_r {w x y z : ob G} (f : hom G w x) (g : hom G x y) (h : hom G y z) :
  comp (comp h g) f = comp h (comp g f).
Proof. symmetry; apply comp_assoc. Qed.
Lemma cancel_l {x y z : ob G} (f : hom G x y) (g : hom G z x) : comp (inv f) (comp f g) = g.
Proof. rewrite comp_assoc, inv_l. apply comp_idl. Qed.
Lemma cancel_r {x y z : ob G} (f : hom G y x) (g : hom G z x) : comp f (comp (inv f) g) = g.
Proof. rewrite comp_assoc, inv_r. apply comp_idl. Qed.
Lemma inv_unique {x y : ob G} (f : hom G x y) (h : hom G y x) : comp h f = idm x -> h = inv f.
Proof. intros H. rewrite <- (comp_idr h), <- (inv_r f), comp_assoc, H, comp_idl. reflexivity. Qed.
Lemma inv_comp {x y z : ob G} (f : hom G x y) (g : hom G y z) : inv (comp g f) = comp (inv f) (inv g).
Proof. symmetry; apply inv_unique. rewrite comp_assoc_r, cancel_l. apply inv_l. Qed.
Lemma inv_inv {x y : ob G} (f : hom G x y) : inv (inv f) = f.
Proof. symmetry; apply inv_unique, inv_r. Qed.
Lemma eqh_merge {x y z w : ob G} (E1 : x = y) (E2 : y = z) (h : hom G w x) :
  comp (eqh E2) (comp (eqh E1) h) = comp (eqh (eq_trans E1 E2)) h.
Proof. rewrite comp_assoc, eqh_trans. reflexivity. Qed.
End G.

(** A set as a discrete groupoid: morphisms are equations. *)
Lemma prop_set {P : Type} (h : forall p q : P, p = q) : forall (p q : P) (r s : p = q), r = s.
Proof.
  intros p q.
  assert (N : forall r : p = q, r = eq_trans (eq_sym (h p p)) (h p q)).
  { intros r. destruct r. destruct (h p p). reflexivity. }
  intros r s. rewrite (N r), (N s). reflexivity.
Qed.

Definition disc (X : Type) (Xset : forall (x y : X) (p q : x = y), p = q) : Gpd.
Proof.
  refine {| ob := X; hom := fun x y => x = y; idm := fun x => eq_refl;
            comp := fun x y z q p => eq_trans p q; inv := fun x y p => eq_sym p |}.
  all: intros; try apply Xset.
  apply prop_set, Xset.
Defined.

(** ** Contexts, families, sections, substitutions *)

(** A category's data.  Contexts of the model are groupoids ([gcat]); the
    comprehensions below are only needed as data, because a family states
    its functor laws against its base's composition, and [J] uses no law
    of the comprehensions themselves. *)
Record Cat := {
  cob : Type;
  chom : cob -> cob -> Type;
  cid : forall g, chom g g;
  ccomp : forall {g1 g2 g3}, chom g2 g3 -> chom g1 g2 -> chom g1 g3 }.
Arguments cid {_} g.
Arguments ccomp {_ _ _ _} _ _.

Definition gcat (G : Gpd) : Cat :=
  {| cob := ob G; chom := hom G; cid := @idm G; ccomp := fun _ _ _ => @comp G _ _ _ |}.

(** A split family: a functor into groupoids, with its laws on the nose. *)
Record Fam (C : Cat) := {
  fib : cob C -> Gpd;
  act : forall {g g'}, chom C g g' -> ob (fib g) -> ob (fib g');
  acth : forall {g g'} (f : chom C g g') {x y}, hom (fib g) x y -> hom (fib g') (act f x) (act f y);
  act_id : forall g x, act (cid g) x = x;
  act_comp : forall {g1 g2 g3} (f1 : chom C g1 g2) (f2 : chom C g2 g3) x,
      act (ccomp f2 f1) x = act f2 (act f1 x);
  acth_idm : forall g g' (f : chom C g g') x, acth f (idm x) = idm (act f x);
  acth_comp : forall g g' (f : chom C g g') x y z (h : hom (fib g) x y) (k : hom (fib g) y z),
      acth f (comp k h) = comp (acth f k) (acth f h);
  acth_id : forall g x y (h : hom (fib g) x y),
      comp (eqh (act_id g y)) (acth (cid g) h) = comp h (eqh (act_id g x));
  acth_ccomp : forall g1 g2 g3 (f1 : chom C g1 g2) (f2 : chom C g2 g3) x y (h : hom (fib g1) x y),
      comp (eqh (act_comp f1 f2 y)) (acth (ccomp f2 f1) h) = comp (acth f2 (acth f1 h)) (eqh (act_comp f1 f2 x)) }.
Arguments act {_} _ {_ _} _ _.
Arguments acth {_} _ {_ _} _ {_ _} _.
Arguments act_id {_} _ _ _.
Arguments act_comp {_} _ {_ _ _} _ _ _.

(** A term: a section, with its functor laws. *)
Record Sec C (A : Fam C) := {
  sob : forall g, ob (fib A g);
  shom : forall {g g'} (f : chom C g g'), hom (fib A g') (act A f (sob g)) (sob g');
  sec_id : forall g, shom (cid g) = eqh (act_id A g (sob g));
  sec_comp : forall g1 g2 g3 (f1 : chom C g1 g2) (f2 : chom C g2 g3),
      shom (ccomp f2 f1) = comp (shom f2) (comp (acth A f2 (shom f1)) (eqh (act_comp A f1 f2 (sob g1)))) }.
Arguments sob {_ _} _ _.
Arguments shom {_ _} _ {_ _} _.

Section FamLemmas.
Context {C : Cat} (A : Fam C).

Lemma acth_eqh {g g'} (f : chom C g g') {x y} (E : x = y) : acth A f (eqh E) = eqh (f_equal (act A f) E).
Proof. destruct E. apply acth_idm. Qed.
Lemma acth_inv {g g'} (f : chom C g g') {x y} (h : hom (fib A g) x y) : acth A f (inv h) = inv (acth A f h).
Proof. apply inv_unique. rewrite <- acth_comp, inv_l. apply acth_idm. Qed.
(** A family's action along equal morphisms. *)
Lemma acth_along {g g'} (m m' : chom C g g') (E : m = m') {x y} (h : hom (fib A g) x y) :
  comp (eqh (f_equal (fun n => act A n y) E)) (acth A m h) = comp (acth A m' h) (eqh (f_equal (fun n => act A n x) E)).
Proof. destruct E. cbn. rewrite comp_idl, comp_idr. reflexivity. Qed.
(** The two square laws, right-associated and solved for the composite. *)
Lemma acth_id_r g x y z (h : hom (fib A g) x y) (k : hom (fib A g) z (act A (cid g) x)) :
  comp (eqh (act_id A g y)) (comp (acth A (cid g) h) k) = comp h (comp (eqh (act_id A g x)) k).
Proof. rewrite !comp_assoc, acth_id. reflexivity. Qed.
Lemma acth_acth {g1 g2 g3} (f1 : chom C g1 g2) (f2 : chom C g2 g3) {x y} (h : hom (fib A g1) x y) :
  acth A f2 (acth A f1 h) =
  comp (eqh (act_comp A f1 f2 y)) (comp (acth A (ccomp f2 f1) h) (eqh (eq_sym (act_comp A f1 f2 x)))).
Proof.
  rewrite comp_assoc, acth_ccomp, comp_assoc_r, eqh_trans.
  rewrite (eqh_irr _ eq_refl). cbn. symmetry. apply comp_idr.
Qed.
End FamLemmas.

(** A substitution: a functor between bases. *)
Record Sub (D C : Cat) := {
  so : cob D -> cob C;
  sh : forall {d d'}, chom D d d' -> chom C (so d) (so d');
  sh_id : forall d, sh (cid d) = cid (so d);
  sh_comp : forall d1 d2 d3 (f1 : chom D d1 d2) (f2 : chom D d2 d3), sh (ccomp f2 f1) = ccomp (sh f2) (sh f1) }.
Arguments so {_ _} _ _.
Arguments sh {_ _} _ {_ _} _.

(** Reindexing a family: precomposition, strict. *)
Definition subF {D C} (s : Sub D C) (A : Fam C) : Fam D.
Proof.
  refine {| fib := fun d => fib A (so s d);
            act := fun d d' f => act A (sh s f);
            acth := fun d d' f x y h => acth A (sh s f) h;
            act_id := fun d x => eq_trans (f_equal (fun m => act A m x) (sh_id s d)) (act_id A _ x);
            act_comp := fun d1 d2 d3 f1 f2 x =>
              eq_trans (f_equal (fun m => act A m x) (sh_comp s _ _ _ f1 f2)) (act_comp A _ _ x) |}.
  - intros; apply acth_idm.
  - intros; apply acth_comp.
  - intros d x y h. rewrite <- !eqh_trans, comp_assoc_r, acth_along, comp_assoc, acth_id, comp_assoc_r.
    reflexivity.
  - intros d1 d2 d3 f1 f2 x y h. rewrite <- !eqh_trans, comp_assoc_r, acth_along, comp_assoc, acth_ccomp.
    rewrite comp_assoc_r. reflexivity.
Defined.

(** ** The comprehension [Γ.A] *)

Section Ext.
Context {C : Cat} (A : Fam C).

Record eob := mk_eob { eb : cob C; ey : ob (fib A eb) }.
Record ehom (o o' : eob) := mk_ehom {
  ea : chom C (eb o) (eb o');
  ef : hom (fib A (eb o')) (act A ea (ey o)) (ey o') }.

Definition ext : Cat := {|
  cob := eob; chom := ehom;
  cid := fun o => mk_ehom o o (cid (eb o)) (eqh (act_id A (eb o) (ey o)));
  ccomp := fun o1 o2 o3 m2 m1 => mk_ehom o1 o3 (ccomp (ea m2) (ea m1))
    (comp (ef m2) (comp (acth A (ea m2) (ef m1)) (eqh (act_comp A (ea m1) (ea m2) (ey o1))))) |}.

Lemma ehom_eq {o o'} (m1 m2 : ehom o o') (E : ea m1 = ea m2) :
  ef m1 = comp (ef m2) (eqh (f_equal (fun a => act A a (ey o)) E)) -> m1 = m2.
Proof. destruct m1 as [a1 f1], m2 as [a2 f2]. cbn in *. destruct E. cbn. rewrite comp_idr. intros ->. reflexivity. Qed.

(** Over a family whose fibres have at most one morphism between two
    objects (a discrete [Id] fibre), only the base component counts. *)
Lemma ehom_eq_prop (Ap : forall g x y (p q : hom (fib A g) x y), p = q) {o o'} (m1 m2 : ehom o o') :
  ea m1 = ea m2 -> m1 = m2.
Proof. intros E. apply (ehom_eq m1 m2 E), Ap. Qed.

(** A section as a substitution into the comprehension: [⟨id, a⟩]. *)
Definition pair0 (a : Sec A) : Sub C ext.
Proof.
  refine (Build_Sub C ext (fun g => mk_eob g (sob a g))
            (fun g g' f => mk_ehom (mk_eob g (sob a g)) (mk_eob g' (sob a g')) f (shom a f)) _ _).
  - intros g. cbn. rewrite (sec_id a g). reflexivity.
  - intros g1 g2 g3 f1 f2. cbn. rewrite (sec_comp a _ _ _ f1 f2). reflexivity.
Defined.
End Ext.
Arguments mk_eob {_ _} _ _.
Arguments eb {_ _} _.
Arguments ey {_ _} _.
Arguments mk_ehom {_ _ _ _} _ _.
Arguments ea {_ _ _ _} _.
Arguments ef {_ _ _ _} _.

(** [⟨s, b⟩] into a comprehension by a family with discrete fibres. *)
Definition pairP {D C} (s : Sub D C) (B : Fam C) (Bp : forall g x y (p q : hom (fib B g) x y), p = q)
  (b : Sec (subF s B)) : Sub D (ext B).
Proof.
  refine (Build_Sub D (ext B) (fun d => mk_eob (so s d) (sob b d))
            (fun d d' f => @mk_ehom _ B (mk_eob (so s d) (sob b d)) (mk_eob (so s d') (sob b d')) (sh s f) (shom b f)) _ _).
  - intros d. apply (ehom_eq_prop Bp). apply sh_id.
  - intros d1 d2 d3 f1 f2. apply (ehom_eq_prop Bp). apply sh_comp.
Defined.

(** ** More normal-form lemmas *)

Lemma eqh_cancel {G : Gpd} {x y z : ob G} (E : x = y) (k : hom G z y) : comp (eqh E) (comp (eqh (eq_sym E)) k) = k.
Proof. destruct E. cbn. rewrite !comp_idl. reflexivity. Qed.

Lemma acth_ccomp_r {C : Cat} (A : Fam C) {g1 g2 g3} (f1 : chom C g1 g2) (f2 : chom C g2 g3) {x y z}
  (h : hom (fib A g1) x y) (k : hom (fib A g3) z (act A (ccomp f2 f1) x)) :
  comp (eqh (act_comp A f1 f2 y)) (comp (acth A (ccomp f2 f1) h) k) =
  comp (acth A f2 (acth A f1 h)) (comp (eqh (act_comp A f1 f2 x)) k).
Proof. rewrite !comp_assoc, acth_ccomp. reflexivity. Qed.

Lemma acth_along_r {C : Cat} (A : Fam C) {g g'} (m m' : chom C g g') (E : m = m') {x y z}
  (h : hom (fib A g) x y) (k : hom (fib A g') z (act A m x)) :
  comp (eqh (f_equal (fun n => act A n y) E)) (comp (acth A m h) k) =
  comp (acth A m' h) (comp (eqh (f_equal (fun n => act A n x) E)) k).
Proof. rewrite !comp_assoc, acth_along. reflexivity. Qed.

Lemma acth_along' {C : Cat} (A : Fam C) {g g'} (m m' : chom C g g') (E : m = m') {x y}
  (h : hom (fib A g) x y) :
  acth A m h = comp (eqh (eq_sym (f_equal (fun n => act A n y) E))) (comp (acth A m' h) (eqh (f_equal (fun n => act A n x) E))).
Proof. destruct E. cbn. rewrite comp_idl, comp_idr. reflexivity. Qed.

(** Any two morphisms made from equations of the same objects agree. *)
Ltac eqh_unify :=
  repeat match goal with
  | |- context [@eqh _ _ _ ?E1] => match goal with
      | |- context [@eqh _ _ _ ?E2] => lazymatch E2 with E1 => fail | _ => rewrite (eqh_irr E1 E2) end
      end
  end.
Ltac eqh_norm := rewrite ?comp_assoc_r; repeat (rewrite ?eqh_merge, ?eqh_trans).

(** ** [Id(a↑; var 0)] over [Γ.A], and [refl] *)

Unset Implicit Arguments.

Section Id.
Context {C : Cat} (A : Fam C) (a : Sec A).

(** The fibre over [(g, y)] is the discrete set [A(g)(a(g), y)]. A morphism
    [(α, f) : (g, y) → (g', y')] acts by [p ↦ f ∘ A(α)(p) ∘ a(α)⁻¹]. *)
Definition IdFib (o : eob A) : Gpd :=
  disc (fun (f g : hom (fib A (eb o)) (sob a (eb o)) (ey o)) (p q : f = g) => hom_set p q).

Definition IdAct {o o' : eob A} (m : @ehom _ A o o') (p : hom (fib A (eb o)) (sob a (eb o)) (ey o)) :
  hom (fib A (eb o')) (sob a (eb o')) (ey o') :=
  comp (ef m) (comp (acth A (ea m) p) (inv (shom a (ea m)))).

Lemma IdAct_id o p : IdAct (@cid (ext A) o) p = p.
Proof.
  unfold IdAct; cbn. rewrite (sec_id a), inv_eqh, acth_id_r, eqh_trans.
  rewrite (eqh_irr _ eq_refl). apply comp_idr.
Qed.

Lemma IdAct_comp o1 o2 o3 (m1 : @ehom _ A o1 o2) (m2 : @ehom _ A o2 o3) p :
  IdAct (@ccomp (ext A) _ _ _ m2 m1) p = IdAct m2 (IdAct m1 p).
Proof.
  unfold IdAct; cbn. rewrite (sec_comp a), !inv_comp, !acth_comp, acth_inv, inv_eqh, !comp_assoc_r.
  rewrite acth_ccomp_r, eqh_cancel. reflexivity.
Qed.

Definition IdF : Fam (ext A).
Proof.
  refine (Build_Fam (ext A) IdFib (fun o o' m p => IdAct m p) (fun o o' m p q E => f_equal (IdAct m) E)
            IdAct_id (fun o1 o2 o3 m1 m2 p => IdAct_comp o1 o2 o3 m1 m2 p) _ _ _ _).
  all: intros; apply hom_set.
Defined.

(** The fibres of [Id] are discrete: at most one morphism. *)
Lemma IdF_prop : forall o x y (p q : hom (fib IdF o) x y), p = q.
Proof. intros o x y p q. apply hom_set. Qed.

(** [Id(a; b)] over the base, for a section [b]. *)
Definition IdT (b : Sec A) : Fam C := subF (pair0 b) IdF.

(** [refl]: the identity morphism. *)
Lemma reflS_hom {g g'} (f : chom C g g') :
  hom (fib (IdT a) g') (act (IdT a) f (idm (sob a g))) (idm (sob a g')).
Proof. cbn. unfold IdAct; cbn. rewrite acth_idm, comp_idl. apply inv_r. Defined.

Definition reflS : Sec (IdT a).
Proof.
  refine (Build_Sec (IdT a) (fun g => idm (sob a g)) (@reflS_hom) _ _).
  all: intros; apply hom_set.
Defined.
End Id.

(** ** [J], Paulin-Mohring's, over a groupoid context *)

Section J.
Context {Γ : Gpd} (A : Fam (gcat Γ)) (a : Sec A).

(** The motive's context [Γ.A.Id(a↑; var 0)]. *)
Definition JC : Cat := ext (IdF A a).
(** [⟨a, refl⟩ : Γ → Γ.A.Id]. *)
Definition ar : Sub (gcat Γ) JC := @pairP _ _ (pair0 a) (IdF A a) (IdF_prop A a) (reflS A a).

Context (M : Fam JC) (c : Sec (subF ar M)) (u : Sec A) (e : Sec (IdT A a u)).

(** [⟨u, e⟩ : Γ → Γ.A.Id]; [J]'s type is [M] reindexed along it. *)
Definition ue : Sub (gcat Γ) JC := @pairP _ _ (pair0 u) (IdF A a) (IdF_prop A a) e.

(** The morphism [(id, e(g)) : (g, a(g), id) → (g, u(g), e(g))]. *)
Lemma ι_pf g : IdAct A a (@mk_ehom _ A (mk_eob g (sob a g)) (mk_eob g (sob u g)) (@cid (gcat Γ) g)
                            (comp (sob e g) (eqh (act_id A g (sob a g))))) (idm (sob a g)) = sob e g.
Proof.
  unfold IdAct; cbn -[gcat]. rewrite (sec_id a g), acth_idm, comp_idl, inv_eqh, comp_assoc_r, eqh_trans.
  rewrite (eqh_irr _ eq_refl). apply comp_idr.
Qed.

Definition ι g : chom JC (so ar g) (so ue g) :=
  @mk_ehom _ (IdF A a) (so ar g) (so ue g)
    (@mk_ehom _ A (mk_eob g (sob a g)) (mk_eob g (sob u g)) (@cid (gcat Γ) g) (comp (sob e g) (eqh (act_id A g (sob a g)))))
    (ι_pf g).

(** The square: [⟨u, e⟩(f) ∘ ι(g) = ι(g') ∘ ⟨a, refl⟩(f)].  It is [e]'s
    section law, since the [Id] fibres are discrete. *)
Lemma square {g g'} (f : hom Γ g g') : @ccomp JC _ _ _ (sh ue f) (ι g) = @ccomp JC _ _ _ (ι g') (sh ar f).
Proof.
  apply (ehom_eq_prop (IdF_prop A a)). cbn -[gcat].
  match goal with |- ?m1 = ?m2 =>
    apply (ehom_eq m1 m2 (eq_trans (comp_idr f) (eq_sym (comp_idl f)) : ea m1 = ea m2)) end. cbn -[gcat].
  pose proof (shom e f) as Ee. cbn -[gcat] in Ee. unfold IdAct in Ee; cbn -[gcat] in Ee. rewrite <- Ee.
  rewrite acth_comp, acth_eqh, !comp_assoc_r, (acth_id_r A), cancel_l.
  eqh_norm. eqh_unify. reflexivity.
Qed.

Definition J_ob g : ob (fib M (so ue g)) := act M (ι g) (sob c g).

Definition Esq {g g'} (f : hom Γ g g') :
  act M (sh ue f) (J_ob g) = act M (ι g') (act M (sh ar f) (sob c g)) :=
  eq_trans (eq_sym (act_comp M (ι g) (sh ue f) (sob c g)))
    (eq_trans (f_equal (fun m => act M m (sob c g)) (square f)) (act_comp M (sh ar f) (ι g') (sob c g))).

(** [J]'s morphism component: [c]'s, moved along [ι]. *)
Definition J_hom {g g'} (f : hom Γ g g') : hom (fib M (so ue g')) (act M (sh ue f) (J_ob g)) (J_ob g') :=
  comp (acth M (ι g') (shom c f)) (eqh (Esq f)).

Lemma J_sec_id g : J_hom (@cid (gcat Γ) g) = eqh (act_id (subF ue M) g (J_ob g)).
Proof. unfold J_hom. rewrite (sec_id c g). cbn -[gcat]. rewrite acth_eqh, eqh_trans. apply eqh_irr. Qed.

Lemma J_sec_comp g1 g2 g3 (f1 : hom Γ g1 g2) (f2 : hom Γ g2 g3) :
  J_hom (@ccomp (gcat Γ) _ _ _ f2 f1) =
  comp (J_hom f2) (comp (acth (subF ue M) f2 (J_hom f1)) (eqh (act_comp (subF ue M) f1 f2 (J_ob g1)))).
Proof.
  unfold J_hom. rewrite (sec_comp c). cbn [subF fib act acth act_comp].
  rewrite !acth_comp, !acth_eqh, !(acth_acth M).
  rewrite (acth_along' M (square f2) (shom c f1 : hom (fib M (so ar g2)) (act M (sh ar f1) (sob c g1)) (sob c g2))).
  eqh_norm. eqh_unify. reflexivity.
Qed.

(** [J(y p. M; c; u; e) : M[u/y, e/p]], a term of the model. *)
Definition J : Sec (subF ue M) := Build_Sec (subF ue M) J_ob (@J_hom) J_sec_id J_sec_comp.
End J.

(** ** β, on the nose *)

Section Beta.
Context {Γ : Gpd} (A : Fam (gcat Γ)) (a : Sec A) (M : Fam (JC A a)) (c : Sec (subF (ar A a) M)).

(** At [u := a], [e := refl], [J]'s type is [c]'s ([ue] is [ar]), and [ι] is
    the identity. *)
Lemma ι_refl g : ι A a a (reflS A a) g = @cid (JC A a) (so (ar A a) g).
Proof.
  apply (ehom_eq_prop (IdF_prop A a)). cbn -[gcat].
  match goal with |- ?m1 = ?m2 => apply (ehom_eq m1 m2 (eq_refl : ea m1 = ea m2)) end. cbn -[gcat]. rewrite comp_idl, comp_idr. reflexivity.
Qed.

Lemma J_beta_ob g : sob (J A a M c a (reflS A a)) g = sob c g.
Proof. exact (eq_trans (f_equal (fun m => act M m (sob c g)) (ι_refl g)) (act_id M _ (sob c g))). Defined.

Lemma J_beta_hom {g g'} (f : hom Γ g g') :
  comp (eqh (J_beta_ob g')) (shom (J A a M c a (reflS A a)) f) =
  comp (shom c f) (eqh (f_equal (act M (sh (ar A a) f)) (J_beta_ob g))).
Proof.
  cbn -[gcat]. unfold J_hom, J_beta_ob. rewrite <- eqh_trans, comp_assoc_r, (acth_along_r M (ι_refl g') (shom c f : hom (fib M (so (ar A a) g')) (act M (sh (ar A a) f) (sob c g)) (sob c g'))), (acth_id_r M).
  eqh_norm. eqh_unify. reflexivity.
Qed.
End Beta.

(** ** Stability of [J] under substitution *)

(** A section's morphism component at a morphism equal to an identity or
    a composite. *)
Section Along.
Context {C : Cat} (A : Fam C) (x : Sec A).

Lemma shom_along_id {g} (m : chom C g g) (E : m = cid g) :
  shom x m = eqh (eq_trans (f_equal (fun n => act A n (sob x g)) E) (act_id A g (sob x g))).
Proof. subst m. rewrite (sec_id x g). apply eqh_irr. Qed.

Lemma shom_along_comp {g1 g2 g3} (m : chom C g1 g3) (f1 : chom C g1 g2) (f2 : chom C g2 g3)
  (E : m = ccomp f2 f1) :
  shom x m = comp (shom x f2) (comp (acth A f2 (shom x f1))
    (eqh (eq_trans (f_equal (fun n => act A n (sob x g1)) E) (act_comp A f1 f2 (sob x g1))))).
Proof. subst m. rewrite (sec_comp x). eqh_unify. reflexivity. Qed.
End Along.

(** Reindexing a section: precomposition. *)
Definition subS {D C : Cat} (s : Sub D C) (A : Fam C) (x : Sec A) : Sec (subF s A) :=
  Build_Sec (subF s A) (fun d => sob x (so s d)) (fun d d' f => shom x (sh s f))
    (fun d => shom_along_id A x (sh s (cid d)) (sh_id s d))
    (fun d1 d2 d3 f1 f2 => shom_along_comp A x (sh s (ccomp f2 f1)) (sh s f1) (sh s f2) (sh_comp s _ _ _ f1 f2)).

(** [σ⁺ : Δ.A[σ] → Γ.A]. *)
Definition liftA {D C : Cat} (s : Sub D C) (A : Fam C) : Sub (ext (subF s A)) (ext A).
Proof.
  refine (Build_Sub (ext (subF s A)) (ext A) (fun o => mk_eob (so s (eb o)) (ey o))
            (fun o o' m => @mk_ehom _ A (mk_eob (so s (eb o)) (ey o)) (mk_eob (so s (eb o')) (ey o')) (sh s (ea m)) (ef m))
            _ _).
  - intros o. match goal with |- ?m1 = ?m2 => apply (ehom_eq m1 m2 (sh_id s (eb o) : ea m1 = ea m2)) end.
    cbn. rewrite eqh_trans. apply eqh_irr.
  - intros o1 o2 o3 m1 m2.
    match goal with |- ?n1 = ?n2 => apply (ehom_eq n1 n2 (sh_comp s _ _ _ (ea m1) (ea m2) : ea n1 = ea n2)) end.
    cbn. rewrite !comp_assoc_r, eqh_trans. eqh_unify. reflexivity.
Defined.

Section Stab.
Context {Γ Δ : Gpd} (σ : Sub (gcat Δ) (gcat Γ)) (A : Fam (gcat Γ)) (a : Sec A).

Definition A' : Fam (gcat Δ) := subF σ A.
Definition a' : Sec A' := subS σ A a.

(** [σ⁺⁺ : Δ.A[σ].Id(a[σ]↑; var 0) → Γ.A.Id(a↑; var 0)]: the [Id] fibres
    and actions agree by conversion. *)
Definition liftJ : Sub (JC A' a') (JC A a).
Proof.
  refine (Build_Sub (JC A' a') (JC A a)
            (fun o => @mk_eob _ (IdF A a) (so (liftA σ A) (eb o)) (ey o))
            (fun o o' m => @mk_ehom _ (IdF A a) (@mk_eob _ (IdF A a) (so (liftA σ A) (eb o)) (ey o))
                              (@mk_eob _ (IdF A a) (so (liftA σ A) (eb o')) (ey o')) (sh (liftA σ A) (ea m)) (ef m))
            _ _).
  - intros o. apply (ehom_eq_prop (IdF_prop A a)). apply (sh_id (liftA σ A)).
  - intros o1 o2 o3 m1 m2. apply (ehom_eq_prop (IdF_prop A a)). apply (sh_comp (liftA σ A)).
Defined.

 (** [Id] and [refl] are stable on the nose: their fibres, actions and
    points agree by conversion. *)
Lemma IdF_stab_fib o : fib (IdF A' a') o = fib (IdF A a) (so (liftA σ A) o).
Proof. reflexivity. Qed.
Lemma IdF_stab_act {o o'} (m : chom (ext A') o o') p :
  act (IdF A' a') m p = act (IdF A a) (sh (liftA σ A) m) p.
Proof. reflexivity. Qed.
Lemma refl_stab d : sob (reflS A' a') d = sob (reflS A a) (so σ d).
Proof. reflexivity. Qed.

Context (M : Fam (JC A a)) (c : Sec (subF (ar A a) M)) (u : Sec A) (e : Sec (IdT A a u)).

Definition M' : Fam (JC A' a') := subF liftJ M.
Definition u' : Sec A' := subS σ A u.

(** [e[σ]]: its laws are equations in discrete fibres. *)
Definition e' : Sec (IdT A' a' u').
Proof.
  refine (Build_Sec (IdT A' a' u') (fun d => sob e (so σ d)) (fun d d' f => shom e (sh σ f)) _ _).
  all: intros; apply hom_set.
Defined.

(** [c[σ]]: [⟨a, refl⟩ ∘ σ] and [σ⁺⁺ ∘ ⟨a[σ], refl⟩] agree by conversion. *)
Definition c' : Sec (subF (ar A' a') M').
Proof.
  refine (Build_Sec (subF (ar A' a') M') (fun d => sob c (so σ d)) (fun d d' f => shom c (sh σ f)) _ _).
  - intros d. rewrite (shom_along_id _ c _ (sh_id σ d)). apply eqh_irr.
  - intros d1 d2 d3 f1 f2. rewrite (shom_along_comp _ c _ _ _ (sh_comp σ _ _ _ f1 f2)). eqh_unify. reflexivity.
Defined.

(** [ι] commutes with [σ]. *)
Lemma ι_stab d : sh liftJ (ι A' a' u' e' d) = ι A a u e (so σ d).
Proof.
  apply (ehom_eq_prop (IdF_prop A a)). cbn -[gcat].
  match goal with |- ?m1 = ?m2 => apply (ehom_eq m1 m2 (sh_id σ d : ea m1 = ea m2)) end.
  cbn -[gcat]. rewrite !comp_assoc_r, eqh_trans. eqh_unify. reflexivity.
Qed.

Definition J_stab_ob d : sob (J A' a' M' c' u' e') d = sob (J A a M c u e) (so σ d) :=
  f_equal (fun m => act M m (sob c (so σ d))) (ι_stab d).

(** [J(M; c; u; e)[σ] = J(M[σ⁺⁺]; c[σ]; u[σ]; e[σ])]: objects, and
    morphisms up to those equations. *)
Lemma J_stab_hom {d d'} (f : hom Δ d d') :
  comp (eqh (J_stab_ob d')) (shom (J A' a' M' c' u' e') f) =
  comp (shom (J A a M c u e) (sh σ f)) (eqh (f_equal (act M (sh (ue A a u e) (sh σ f))) (J_stab_ob d))).
Proof.
  cbn -[gcat]. unfold J_hom, J_stab_ob. rewrite comp_assoc_r.
  rewrite (acth_along_r M (ι_stab d')
             (shom c (sh σ f) : hom (fib M (so (ar A a) (so σ d'))) (act M (sh (ar A a) (sh σ f)) (sob c (so σ d)))
                                   (sob c (so σ d')))).
  eqh_norm. eqh_unify. reflexivity.
Qed.
End Stab.

(** ** The hypotheses are satisfiable *)

(** A constant family, over any base. *)
Definition constF (C : Cat) (F : Gpd) : Fam C.
Proof.
  refine (Build_Fam C (fun _ => F) (fun _ _ _ x => x) (fun _ _ _ _ _ h => h)
            (fun _ _ => eq_refl) (fun _ _ _ _ _ _ => eq_refl) _ _ _ _).
  all: intros; cbn; rewrite ?comp_idl, ?comp_idr; reflexivity.
Defined.

Definition constS (C : Cat) (F : Gpd) (x : ob F) : Sec (constF C F).
Proof.
  refine (Build_Sec (constF C F) (fun _ => x) (fun _ _ _ => idm x) _ _).
  all: intros; cbn; rewrite ?comp_idl; reflexivity.
Defined.

(** A constant section of a reindexed constant family. *)
Definition constSs {D C : Cat} (s : Sub D C) (F : Gpd) (x : ob F) : Sec (subF s (constF C F)).
Proof.
  refine (Build_Sec (subF s (constF C F)) (fun _ => x) (fun _ _ _ => idm x) _ _).
  - intros g. cbn. rewrite (eqh_irr _ eq_refl). reflexivity.
  - intros. cbn. rewrite (eqh_irr _ eq_refl). cbn. rewrite !comp_idl. reflexivity.
Defined.

Definition natG : Gpd := disc (UIP_dec Nat.eq_dec).
Definition unitG : Gpd := disc (UIP_dec (fun x y : unit => left (match x, y return x = y with tt, tt => eq_refl end))).

(** [J] over the one-point context, at the constant family [ℕ], with a
    constant motive. *)
Definition J_example : Sec (subF (ue (constF (gcat unitG) natG) (constS _ natG 0) (constS _ natG 0)
                                    (reflS _ (constS _ natG 0))) (constF _ natG)) :=
  J (constF (gcat unitG) natG) (constS _ natG 0) (constF _ natG) (constSs _ natG 7)
    (constS _ natG 0) (reflS _ (constS _ natG 0)).

Print Assumptions J.
Print Assumptions J_beta_ob.
Print Assumptions J_beta_hom.
Print Assumptions IdF.
Print Assumptions J_example.
Print Assumptions J_stab_ob.
Print Assumptions J_stab_hom.
