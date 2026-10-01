(** * The components lemma of Heather's [docs/no-uip-model.md] §3

    In the groupoid model, a strict proposition ([sEq], [Squash],
    [sEmpty]) is interpreted as a union of connected components of the
    context: a fibre is one point where the two sections are isomorphic
    (resp. where the type is inhabited), empty elsewhere.  This file checks:

    - the components lemma: connectedness of two sections is transported
      along every morphism of the context ([conn_transport]), so the
      strict families are families;
    - strict stability under substitution ([sEq_subst], by [eq_refl]);
    - definitional irrelevance of sections of a strict family
      ([sec_irrelevant], a conversion check);
    - [srefl], [elim_sEmpty], [ElimSquash];
    - [transp] at a strict motive exists ([transp_strict]);
    - [transp] at a relevant motive does not ([no_relevant_transp]), and
      UIP at [Ty 0] fails ([no_uip0]), in the concrete groupoid of types
      and bijections.

    Strict propositions are modelled by [SProp], whose definitional
    irrelevance is exactly what the model's strictly unique fibre elements
    provide.

    What the lemmas use: of a context, only its morphisms and identities (a
    reflexive graph); of a fibre, only composition and inverses.  No
    groupoid law is used, so the statements hold for every groupoid, and
    groupoid laws are not recorded. *)

Set Primitive Projections.
Set Implicit Arguments.

(** ** Fibres, contexts, families, sections *)

(** A fibre: a groupoid's data (the laws are never used). *)
Record Gpd := {
  ob : Type;
  hom : ob -> ob -> Type;
  idm : forall x, hom x x;
  comp : forall x y z, hom y z -> hom x y -> hom x z;
  inv : forall x y, hom x y -> hom y x }.
Arguments comp {g x y z}.
Arguments inv {g x y}.

(** A context: a reflexive graph (a groupoid, forgetting what is unused). *)
Record Ctx := {
  cob : Type;
  chom : cob -> cob -> Type;
  cid : forall g, chom g g }.

(** A family over a context: a split family, as data, with its action on
    identities (used once, by [transp_strict]). *)
Record Fam (G : Ctx) := {
  fib : cob G -> Gpd;
  act : forall g g', chom G g g' -> ob (fib g) -> ob (fib g');
  acth : forall g g' (f : chom G g g') x y,
      hom (fib g) x y -> hom (fib g') (act _ _ f x) (act _ _ f y);
  act_id : forall g x, act _ _ (cid G g) x = x }.
Arguments act {G} f {g g'} _ _ : rename.
Arguments acth {G} f {g g'} _ {x y} _ : rename.

(** A term: a section, with its morphism components. *)
Record Sec G (A : Fam G) := {
  sob : forall g, ob (fib A g);
  shom : forall g g' (f : chom G g g'), hom (fib A g') (act A f (sob g)) (sob g') }.
Arguments sob {G A} s g.
Arguments shom {G A} s {g g'} f.

(** A strict family: fibres are strict propositions.  Its groupoid
    structure is the trivial one, so the data is a predicate and its
    transport along morphisms. *)
Record SFam (G : Ctx) := {
  sfib : cob G -> SProp;
  sact : forall g g', chom G g g' -> sfib g -> sfib g' }.

(** Sections of a strict family: an [SProp], hence definitionally
    irrelevant as a whole (the morphism components are trivial). *)
Definition SSec G (P : SFam G) : SProp := forall g, sfib P g.

Inductive sSquash (A : Type) : SProp := ssquash : A -> sSquash A.
Inductive sEmpty : SProp := .

(** ** The components lemma *)

Section Components.
  Context {G : Ctx} {A : Fam G} (a b : Sec A).

  (** [γ ∈ Γ_{a~b}]: the two sections are isomorphic at [g]. *)
  Definition conn (g : cob G) : SProp :=
    sSquash (hom (fib A g) (sob a g) (sob b g)).

  (** The lemma: [Γ_{a~b}] is closed under the context's morphisms.  The
      witness at [g'] is [b(α) ∘ A(α)(h) ∘ a(α)⁻¹]. *)
  Lemma conn_transport {g g'} (f : chom G g g') : conn g -> conn g'.
  Proof.
    intros [h]. constructor.
    exact (comp (shom b f) (comp (acth A f h) (inv (shom a f)))).
  Qed.

  (** [⟦sEq(A; a; b)⟧]. *)
  Definition sEqF : SFam G := {| sfib := conn; sact := @conn_transport |}.
End Components.

(** [srefl]: the identity witnesses [Γ_{a~a}]. *)
Definition srefl G (A : Fam G) (a : Sec A) : SSec (sEqF a a) :=
  fun g => ssquash (idm _ (sob a g)).

(** Definitional irrelevance: any two sections of a strict family are
    convertible (this typechecks by conversion alone). *)
Definition sec_irrelevant G (P : SFam G) (s1 s2 : SSec P)
  (Q : SSec P -> Type) (q : Q s1) : Q s2 := q.

(** ** Substitution *)

(** A substitution: a morphism of contexts. *)
Record Sub (D G : Ctx) := {
  so : cob D -> cob G;
  sh : forall d d', chom D d d' -> chom G (so d) (so d');
  sh_id : forall d, sh _ _ (cid D d) = cid G (so d) }.
Arguments sh {D G} s {d d'} f.

Definition subF D G (s : Sub D G) (A : Fam G) : Fam D.
Proof.
  refine {| fib := fun d => fib A (so s d);
            act := fun d d' f => act A (sh s f);
            acth := fun d d' f x y h => acth A (sh s f) h |}.
  intros d x. cbn. rewrite (sh_id s d). apply act_id.
Defined.

Definition subS D G (s : Sub D G) (A : Fam G) (a : Sec A) : Sec (subF s A) :=
  @Build_Sec D (subF s A) (fun d => sob a (so s d)) (fun d d' f => shom a (sh s f)).

(** Strict stability: [⟦sEq⟧[σ] = ⟦sEq[σ]⟧] fibrewise, on the nose. *)
Lemma sEq_subst D G (s : Sub D G) (A : Fam G) (a b : Sec A) (d : cob D) :
  sfib (sEqF (subS s a) (subS s b)) d = sfib (sEqF a b) (so s d).
Proof. reflexivity. Qed.

(** ** [sEmpty] and [Squash] *)

Definition sEmptyF G : SFam G := {| sfib := fun _ => sEmpty; sact := fun _ _ _ e => e |}.

(** [elim_sEmpty]: over [x : sEmpty] any family has a section. *)
Definition elim_sEmpty G (A : Fam G) (g : cob G) (e : sfib (sEmptyF G) g) : ob (fib A g) :=
  match e with end.

Definition sSquashF G (A : Fam G) : SFam G.
Proof.
  refine {| sfib := fun g => sSquash (ob (fib A g)) |}.
  intros g g' f [x]. exact (ssquash (act A f x)).
Defined.

(** A strict proposition over a context extended by a strict proposition. *)
Record sPair (X : Type) (P : X -> SProp) := spair { sfst : X; ssnd : P sfst }.

Definition extS G (P : SFam G) : Ctx :=
  {| cob := sPair (sfib P);
     chom := fun p q => chom G (sfst p) (sfst q);
     cid := fun p => cid G (sfst p) |}.

(** [ElimSquash]: from a case at [squash x] for every [x], a section at
    every [z : ∥A∥].  No choice has to be natural: the target is strict. *)
Definition ElimSquash G (A : Fam G) (B : SFam (extS (sSquashF A)))
  (case : forall g (x : ob (fib A g)), sfib B (spair (sfib (sSquashF A)) g (ssquash x)))
  : SSec B.
Proof. intros [g [x]]. exact (case g x). Defined.

(** ** [transp] at a strict motive exists *)

(** The context extended by a type (the comprehension, as a reflexive
    graph). *)
Definition extG G (A : Fam G) : Ctx :=
  {| cob := {g : cob G & ob (fib A g)};
     chom := fun p q => {f : chom G (projT1 p) (projT1 q) &
                          hom (fib A (projT1 q)) (act A f (projT2 p)) (projT2 q)};
     cid := fun p => existT _ (cid G (projT1 p))
       (eq_rect_r (fun z => hom (fib A (projT1 p)) z (projT2 p))
                  (idm _ (projT2 p)) (act_id A (projT1 p) (projT2 p))) |}.

(** [transp(z. P; a; b; e; t)] for [P] a strict family over [Γ.A]: along
    [(id, h) : (g, a g) → (g, b g)], where [h] witnesses [conn a b g]. *)
Definition transp_strict G (A : Fam G) (P : SFam (extG A)) (a b : Sec A)
  (e : SSec (sEqF a b))
  (t : forall g, sfib P (existT _ g (sob a g)))
  : forall g, sfib P (existT _ g (sob b g)).
Proof.
  intros g. destruct (e g) as [h].
  refine (sact P (existT _ g (sob a g)) (existT _ g (sob b g))
                 (existT _ (cid G g) _) (t g)). cbn.
  rewrite act_id. exact h.
Defined.

(** ** [Ty 0] as types and bijections: relevant [transp] and UIP fail *)

Record bij (X Y : Type) := {
  fw : X -> Y;
  bw : Y -> X;
  bf : forall x, bw (fw x) = x;
  fb : forall y, fw (bw y) = y }.

Definition bij_id X : bij X X := {| fw := fun x => x; bw := fun x => x;
  bf := fun _ => eq_refl; fb := fun _ => eq_refl |}.
Definition bij_inv X Y (f : bij X Y) : bij Y X :=
  {| fw := bw f; bw := fw f; bf := fb f; fb := bf f |}.
Definition bij_comp X Y Z (g : bij Y Z) (f : bij X Y) : bij X Z.
Proof.
  refine {| fw := fun x => fw g (fw f x); bw := fun z => bw f (bw g z) |}.
  - intros x. rewrite (bf g). apply bf.
  - intros z. rewrite (fb f). apply fb.
Defined.

(** [Ty 0]: types and bijections. *)
Definition Ty0 : Gpd := {| ob := Type; hom := bij; idm := bij_id;
  comp := fun X Y Z => @bij_comp X Y Z; inv := fun X Y => @bij_inv X Y |}.

(** A type as a discrete groupoid (the fibre of [El]). *)
Definition disc (X : Type) : Gpd := {| ob := X; hom := fun x y => x = y;
  idm := fun x => eq_refl; comp := fun x y z q p => eq_trans p q;
  inv := fun x y p => eq_sym p |}.

(** [UIP₀]: [Id^1(Ty 0; Bool; Bool)] is the hom-set of [Ty 0], [Id] over it
    is equality of bijections, and [id ≠ swap]. *)
Lemma negb_negb (b : bool) : negb (negb b) = b.
Proof. now destruct b. Qed.
Definition swap : bij bool bool := {| fw := negb; bw := negb;
  bf := negb_negb; fb := negb_negb |}.

Lemma no_uip0 : (forall p q : hom Ty0 bool bool, p = q) -> False.
Proof.
  intros H. pose proof (f_equal (fun p => fw p true) (H (idm Ty0 bool) swap)) as E.
  discriminate E.
Qed.

(** The development's M11 statement ([UIP0_nat], [theories/Validity/Uip.v])
    took [⌜Nat⌝] for [⌜Bool⌝], from before the development had sums; since
    M12 its [UIP0] is at [⌜Bool⌝], which [no_uip0] refutes. At the empty
    context [UIP0_nat]'s interpretation is [∀ p q : hom Ty0 nat nat, p = q],
    and the transposition of [0] and [1] refutes it. *)
Definition swap01 (n : nat) : nat := match n with 0 => 1 | 1 => 0 | n => n end.
Lemma swap01_inv n : swap01 (swap01 n) = n.
Proof. now destruct n as [|[|n]]. Qed.
Definition swapN : bij nat nat := {| fw := swap01; bw := swap01; bf := swap01_inv; fb := swap01_inv |}.

Lemma no_uip0_nat : (forall p q : hom Ty0 nat nat, p = q) -> False.
Proof.
  intros H. pose proof (f_equal (fun p => fw p 0) (H (idm Ty0 nat) swapN)) as E.
  discriminate E.
Qed.

(** The context [X Y : Ty 0, e : sEq(Ty 0; X; Y), t : El X]. *)
Definition Γ1 : Ctx := {| cob := (Type * Type)%type;
  chom := fun p q => (bij (fst p) (fst q) * bij (snd p) (snd q))%type;
  cid := fun p => (bij_id _, bij_id _) |}.

(** The constant family [Ty 0] over [Γ1] and its two projections. *)
Definition TyF : Fam Γ1 := {| fib := fun _ => Ty0; act := fun _ _ _ X => X;
  acth := fun _ _ _ _ _ h => h; act_id := fun _ _ => eq_refl |}.
Definition π1 : Sec TyF := @Build_Sec Γ1 TyF (fun p : Type * Type => fst p)
  (fun p q (f : chom Γ1 p q) => fst f).
Definition π2 : Sec TyF := @Build_Sec Γ1 TyF (fun p : Type * Type => snd p)
  (fun p q (f : chom Γ1 p q) => snd f).

Definition Γ2 : Ctx := extS (sEqF π1 π2).

(** [El X] over [Γ2]. *)
Definition ElX : Fam Γ2 := @Build_Fam Γ2
  (fun p : cob Γ2 => disc (fst (sfst p)))
  (fun p q (f : chom Γ2 p q) (x : fst (sfst p)) => fw (fst f) x)
  (fun p q (f : chom Γ2 p q) x y (h : x = y) => f_equal (fw (fst f)) h)
  (fun _ _ => eq_refl).

Definition Γ3 : Ctx := extG ElX.

(** [El Y] over [Γ3], the type of [transp(z. El z; X; Y; e; t)]. *)
Definition ElY : Fam Γ3 := @Build_Fam Γ3
  (fun o : cob Γ3 => disc (snd (sfst (projT1 o))))
  (fun o o' (m : chom Γ3 o o') (y : snd (sfst (projT1 o))) => fw (snd (projT1 m)) y)
  (fun o o' (m : chom Γ3 o o') x y (h : x = y) => f_equal (fw (snd (projT1 m))) h)
  (fun _ _ => eq_refl).

(** No section: at [X = Y = Bool], the morphism [(id, swap)] fixes [t] and
    would force [r = negb r]. *)
Lemma no_relevant_transp : Sec ElY -> False.
Proof.
  intros r.
  pose (p := spair (sfib (sEqF π1 π2)) (@pair Type Type bool bool) (ssquash (bij_id bool))).
  pose (o := existT (fun p => ob (fib ElX p)) p true).
  pose (m := existT (fun f : chom Γ2 p p => hom (fib ElX p) (act ElX f true) true)
                    ((bij_id bool, swap) : chom Γ2 p p) eq_refl).
  pose proof (shom r (g := o) (g' := o) m) as E. cbn in E.
  destruct (sob r o); discriminate E.
Qed.

Print Assumptions sec_irrelevant.
Print Assumptions transp_strict.
Print Assumptions no_relevant_transp.
Print Assumptions no_uip0.
Print Assumptions no_uip0_nat.
