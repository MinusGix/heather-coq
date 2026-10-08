(** * Squash's term relation: a probe (Heather [issues/metatheory-ch07-squash.md])

    Heather's [docs/metatheory-ch07-extensions.md] §27 proposes a
    "normalizing-total" relation at [∥A∥]: two terms are related when both
    weak-head normalize, with no relation between the normal forms or
    between the payloads of two [squash]es. This file checks a refinement of
    that clause against the development's logical relation, without adding
    [Squash] to the syntax: the new former's type and constructor are
    section variables, and the two generic laws the round would add (the
    congruence of [∥·∥] and proof irrelevance at it) are hypotheses.
    [Squash_hyps_unit] shows the hypotheses are satisfiable, by [Unit].

    The clause (as [Empty]'s for the shape, as [+]'s for the carrier):
    - [SqNf]: a weak-head normal form at [∥A∥] is good alone when it is a
      [squash] whose payload is related {e to itself} by [A]'s relation, or
      a neutral related to itself;
    - [SqU]: a term is good when it reduces to a good whnf at [∥A∥];
    - [SqRel t t'] is [SqU t /\ SqU t']: a product of two unary predicates.
      Nothing about [t] is compared with anything about [t'];
    - [SqTy]: the type clause keeps [A]'s derivation and relation [RA], as
      [LRsum] keeps its summands', and [R] is equivalent to [SqRel].

    The refinement over §27 is the payload's self-relation [RA a a]. The
    eliminator needs it: in [ind(squash a; z.B; x.b) ⤳ b[a/x]], the
    fundamental theorem's hypothesis for [b] is instantiated at a related
    argument, and the well-typedness of [a] does not give one. Neutrals are
    kept self-related for the same reason as at [Empty]: [ind] is neutral
    on a neutral scrutinee, and its neutral law needs [ν ~ ν].

    The normalization requirement itself is not new here. The development's
    [UnitRel] and [SEqRel] already keep both sides' whnfs (as logrel-coq's
    [UnitRedTm] does; [LogRel/Def.v], the Unit section), unlike the
    pen-and-paper relations that §27 contrasts with.

    Checked below: the relation is a PER and reflexive on each side
    ([SqRel_sym], [SqRel_trans], [SqRel_refl_l], [SqRel_refl_r]); escape for
    types and terms ([SqTy_escape_ty], [SqTy_escape_tm]); symmetry of the
    type clause ([SqTy_sym]) and its reflexivity ([SqTy_refl_l]), each
    from the carrier's; the change of carrier along an equal type and
    equivalent level, reading only the diagonal of the carrier's relation
    ([SqRel_conv]); irrelevance of the derivation ([SqTy_irrel]); closure
    under typed weak-head expansion ([SqTy_red_ty], [SqTy_red_tm]); and the
    eliminator's case split, one side at a time ([SqU_cases]).

    Not checked (the round's work, with no new kind of argument): the
    syntax and its substitution lemmas, weakening, transitivity across
    three types, level inversion, the code layer, and the fundamental
    theorem's [ind] case. [HEATHER.md], Findings, has the verdict and the
    round's size. *)
From DeLaM.LogRel Require Import Transitivity Reduction.

Section Squash.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** The new former, abstractly *)

(** [tySq l A] is [Squash^l A]; [tmSq k C a] is [squash] with its
    annotations. *)
Variable tySq : lvl -> ty -> ty.
Variable tmSq : lvl -> ty -> tm -> tm.

(** The generic laws the round adds: the congruence of [∥·∥], and proof
    irrelevance (as [geq_tm_seq_irr]). *)
Hypothesis geq_ty_sq : forall G Γ l l' A A', lequiv (gL G) l l' ->
  [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] -> [ G ; Γ ⊢ tySq l A ≈ tySq l' A' @ l ].
Hypothesis geq_tm_sq_irr : forall G Γ l A t t', lwf (gL G) l ->
  [ G ; Γ ⊢g t : tySq l A @ l ] -> [ G ; Γ ⊢g t' : tySq l A @ l ] ->
  [ G ; Γ ⊢ t ≈ t' : tySq l A @ l ].

(** ** The relation *)

Inductive SqNf (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (RA : tm -> tm -> Prop) : tm -> Prop :=
| sqnf_sq k C a :
    lequiv (gL G) k l -> [ G ; Γ ⊢ A ≈ C @ l ] -> RA a a -> SqNf G Γ l A RA (tmSq k C a)
| sqnf_ne ν : [ G ; Γ ⊢ ν ~ ν : tySq l A @ l ] -> SqNf G Γ l A RA ν.

Definition SqU (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (RA : tm -> tm -> Prop) (t : tm) : Prop :=
  exists w, [ G ; Γ ⊢g t ⤳* w : tySq l A @ l ] /\ SqNf G Γ l A RA w.

Definition SqRel (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (RA : tm -> tm -> Prop) : tm -> tm -> Prop :=
  fun t t' => SqU G Γ l A RA t /\ SqU G Γ l A RA t'.

(** The clause [LRsq] would add to [LR], stated over the same stage. *)
Inductive SqTy (n : nat) (rec : lvl -> RedRel) (G : gctx) (Γ : ctx) (T T' : ty) (l : lvl)
    (R : tm -> tm -> Prop) : Prop :=
| sqty l1 l2 A A' RA :
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tySq l1 A @ l ] -> [ G ; Γ ⊢g T' ⤳* tySq l2 A' @ l ] ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    LR n rec G Γ A A' l1 RA ->
    (forall x y, RA x y -> RA y x) -> (forall x y z, RA x y -> RA y z -> RA x z) ->
    releq R (SqRel G Γ l1 A RA) ->
    SqTy n rec G Γ T T' l R.

(** ** Reflexivity, symmetry, transitivity: free, since nothing is compared *)

Lemma SqRel_sym {G Γ l A RA t t'} : SqRel G Γ l A RA t t' -> SqRel G Γ l A RA t' t.
Proof. intros [H H']; exact (conj H' H). Qed.

Lemma SqRel_trans {G Γ l A RA t1 t2 t3} :
  SqRel G Γ l A RA t1 t2 -> SqRel G Γ l A RA t2 t3 -> SqRel G Γ l A RA t1 t3.
Proof. intros [H1 _] [_ H3]; exact (conj H1 H3). Qed.

Lemma SqRel_refl_l {G Γ l A RA t t'} : SqRel G Γ l A RA t t' -> SqRel G Γ l A RA t t.
Proof. intros [H _]; exact (conj H H). Qed.

Lemma SqRel_refl_r {G Γ l A RA t t'} : SqRel G Γ l A RA t t' -> SqRel G Γ l A RA t' t'.
Proof. intros [_ H]; exact (conj H H). Qed.

Lemma SqRel_wf {G Γ l A RA t t'} : SqRel G Γ l A RA t t' ->
  [ G ; Γ ⊢g t : tySq l A @ l ] /\ [ G ; Γ ⊢g t' : tySq l A @ l ].
Proof.
  intros [(w & Hw & _) (w' & Hw' & _)].
  exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')).
Qed.

(** ** Changing the carrier

    Along an equal carrier and an equivalent level, the relation reads only
    the diagonal of the carrier's relation. This is what symmetry,
    irrelevance and level inversion consume. *)

Lemma SqU_conv {G Γ l l' A A' RA RA' t} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
  (forall a, RA a a -> RA' a a) ->
  SqU G Γ l A RA t -> SqU G Γ l' A' RA' t.
Proof.
  intros Hl HA HAA HR (w & Hw & Hn).
  pose proof (lequiv_sym _ _ _ Hl) as Hl'.
  assert (HV : [ G ; Γ ⊢g tySq l A ≅ tySq l' A' @ l ]) by exact (geq_ty_sound (geq_ty_sq _ _ _ _ _ _ Hl HA HAA)).
  exists w. split.
  - eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw | exact HV] | exact Hl'].
  - destruct Hn as [k C a Hk HC Ha | ν Hν].
    + apply sqnf_sq; [exact (lequiv_trans _ _ _ _ Hk Hl) | | exact (HR _ Ha)].
      eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HC] | exact Hl'].
    + apply sqnf_ne. eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν | exact HV] | exact Hl'].
Qed.

Lemma SqRel_conv {G Γ l l' A A' RA RA'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
  (forall a, RA a a <-> RA' a a) ->
  releq (SqRel G Γ l A RA) (SqRel G Γ l' A' RA').
Proof.
  intros Hl HA HAA HR.
  pose proof (lequiv_sym _ _ _ Hl) as Hl'.
  assert (HA' : [ G ; Γ ⊢g A' @ l' ]) by exact (lconv_ty (eqty_wf_r ge_typeof (geq_ty_sound HAA)) Hl).
  assert (HA'A : [ G ; Γ ⊢ A' ≈ A @ l' ]) by exact (geq_ty_lconv (geq_ty_sym HAA) Hl').
  intros t t'; split; intros [H H']; split.
  all: first [ eapply (SqU_conv Hl HA HAA); [intros a; apply HR | assumption]
             | eapply (SqU_conv Hl' HA' HA'A); [intros a; apply HR | assumption] ].
Qed.

(** ** Escape *)

Lemma SqTy_escape_ty {n rec G Γ T T' l R} : SqTy n rec G Γ T T' l R ->
  [ G ; Γ ⊢g T @ l ] /\ [ G ; Γ ⊢g T' @ l ] /\ [ G ; Γ ⊢ T ≈ T' @ l ].
Proof.
  intros [l1 l2 A A' RA Hl Hl2 Hw HT HT' HA HAA HRA Hs Ht HR].
  refine (conj (tyred_wf _ _ _ _ _ _ HT) (conj (tyred_wf _ _ _ _ _ _ HT') _)).
  eapply geq_ty_exp; [exact HT | exact HT' |].
  eapply geq_ty_lconv; [|exact Hl]. exact (geq_ty_sq _ _ _ _ _ _ (lequiv_sym _ _ _ Hl2) HA HAA).
Qed.

(** As at [Unit] and [sEq], escape for terms is proof irrelevance. *)
Lemma SqTy_escape_tm {n rec G Γ T T' l R} : SqTy n rec G Γ T T' l R -> forall t t', R t t' ->
  [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ] /\ [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof.
  intros [l1 l2 A A' RA Hl Hl2 Hw HT HT' HA HAA HRA Hs Ht HR] t t' Htt.
  apply HR in Htt. destruct (SqRel_wf Htt) as [H1 H1'].
  assert (HTS : [ G ; Γ ⊢g T ≅ tySq l1 A @ l ]) by exact (tyred_eq _ _ _ _ _ _ HT).
  repeat split.
  - eapply conv_tm; [exact H1 | exact HTS | exact Hl].
  - eapply conv_tm; [exact H1' | exact HTS | exact Hl].
  - eapply conv_geq_tm; [exact (geq_tm_sq_irr _ _ _ _ _ _ Hw H1 H1') | apply eqty_sym, HTS | exact Hl].
Qed.

(** ** Symmetry and reflexivity of the type clause, from the carrier's *)

Lemma SqTy_sym {n rec G Γ T T' l R} :
  (forall A A' l1 RA, LR n rec G Γ A A' l1 RA -> LR n rec G Γ A' A l1 (flipR RA)) ->
  SqTy n rec G Γ T T' l R -> SqTy n rec G Γ T' T l (flipR R).
Proof.
  intros IH [l1 l2 A A' RA Hl Hl2 Hw HT HT' HA HAA HRA Hs Ht HR].
  pose proof (lequiv_sym _ _ _ Hl2) as Hl2'.
  assert (HA' : [ G ; Γ ⊢g A' @ l2 ]) by exact (lconv_ty (eqty_wf_r ge_typeof (geq_ty_sound HAA)) Hl2').
  assert (HAA' : [ G ; Γ ⊢ A' ≈ A @ l2 ]) by exact (geq_ty_lconv (geq_ty_sym HAA) Hl2).
  apply (sqty n rec G Γ T' T l (flipR R) l2 l1 A' A (flipR RA)).
  - exact (lequiv_trans _ _ _ _ Hl Hl2').
  - exact Hl2'.
  - exact (lequiv_wf_l _ _ _ Hl2).
  - exact HT'.
  - exact HT.
  - exact HA'.
  - exact HAA'.
  - exact (LR_lconv _ _ _ _ _ _ _ _ _ (IH _ _ _ _ HRA) Hl2).
  - unfold flipR; intros x y H; exact (Hs _ _ H).
  - unfold flipR; intros x y z H1 H2; exact (Ht _ _ _ H2 H1).
  - intros t t'; unfold flipR at 1; rewrite (HR t' t).
    rewrite (SqRel_conv (RA := RA) (RA' := flipR RA) Hl2' HA HAA (fun a => iff_refl _) t' t).
    split; apply SqRel_sym.
Qed.

Lemma SqTy_refl_l {n rec G Γ T T' l R} :
  (forall A A' l1 RA, LR n rec G Γ A A' l1 RA -> LR n rec G Γ A A l1 RA) ->
  SqTy n rec G Γ T T' l R -> SqTy n rec G Γ T T l R.
Proof.
  intros IH [l1 l2 A A' RA Hl Hl2 Hw HT HT' HA HAA HRA Hs Ht HR].
  apply (sqty n rec G Γ T T l R l1 l1 A A RA); try assumption.
  - exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Hl2) Hl2).
  - exact (geq_ty_trans HAA (geq_ty_sym HAA)).
  - exact (IH _ _ _ _ HRA).
Qed.

(** ** Irrelevance of the derivation

    Two clauses for the same left type have equivalent relations, given the
    carrier's irrelevance. The round's [LR_irrel] needs the former to be a
    whnf and injective, which a constructor is. *)

Lemma SqTy_irrel {n rec G Γ T T' T'' l R R'} :
  (forall l1 A, whnf_ty (tySq l1 A)) ->
  (forall l1 l2 A A0, tySq l1 A = tySq l2 A0 -> l1 = l2 /\ A = A0) ->
  (forall A A' A'' l1 RA RA', LR n rec G Γ A A' l1 RA -> LR n rec G Γ A A'' l1 RA' -> releq RA RA') ->
  SqTy n rec G Γ T T' l R -> SqTy n rec G Γ T T'' l R' -> releq R R'.
Proof.
  intros Hwh Hinj IH [l1 l2 A A' RA Hl Hl2 Hw HT HT' HA HAA HRA Hs Ht HR]
    [m1 m2 C C' RC Hm Hm2 Hmw HC HC' HCw HCC HRC Hs' Ht' HR'].
  assert (E1 : tySq l1 A = tySq m1 C) by exact (red_whnf_agree HT HC (Hwh _ _) (Hwh _ _)).
  destruct (Hinj _ _ _ _ E1) as [<- <-].
  intros t t'. rewrite (HR t t'), (HR' t t').
  apply (SqRel_conv (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Hl) Hl) HA
           (geq_ty_trans HAA (geq_ty_sym HAA))).
  intros a. exact (IH _ _ _ _ _ _ HRA HRC a a).
Qed.

(** ** Closure under typed weak-head expansion *)

Lemma SqTy_red_ty {n rec G Γ T T' l R T1 T1'} : SqTy n rec G Γ T T' l R ->
  [ G ; Γ ⊢g T1 ⤳* T @ l ] -> [ G ; Γ ⊢g T1' ⤳* T' @ l ] -> SqTy n rec G Γ T1 T1' l R.
Proof.
  intros [l1 l2 A A' RA Hl Hl2 Hw HT HT' HA HAA HRA Hs Ht HR] H1 H1'.
  eapply sqty; eauto using tyred_trans.
Qed.

Lemma SqTy_red_tm {n rec G Γ T T' l R} : SqTy n rec G Γ T T' l R -> forall t t' t1 t1', R t t' ->
  [ G ; Γ ⊢g t1 ⤳* t : T @ l ] -> [ G ; Γ ⊢g t1' ⤳* t' : T' @ l ] -> R t1 t1'.
Proof.
  intros [l1 l2 A A' RA Hl Hl2 Hw HT HT' HA HAA HRA Hs Ht HR] t t' t1 t1' Htt H1 H1'.
  apply HR in Htt; apply HR. destruct Htt as [(w & Hr & Hn) (w' & Hr' & Hn')]. split.
  - exists w. split; [| exact Hn].
    eapply tmred_trans; [| exact Hr]. eapply tmred_along; [exact H1 | exact HT | now apply lequiv_sym].
  - exists w'. split; [| exact Hn'].
    eapply tmred_trans; [| exact Hr'].
    eapply tmred_conv; [apply ge_typeof | eapply tmred_along; [exact H1' | exact HT' | now apply lequiv_sym] |].
    apply geq_ty_sound, geq_ty_sym.
    exact (geq_ty_sq _ _ _ _ _ _ (lequiv_sym _ _ _ Hl2) HA HAA).
Qed.

(** ** The eliminator's case split

    Each scrutinee is analysed alone: a [squash] whose payload is related to
    itself (β, then [b]'s hypothesis at [a]), or a self-related neutral (the
    neutral law). The result relation is again [SqRel], a product, so the
    two results need not be compared either. *)

Lemma SqU_cases {G Γ l A RA t} : SqU G Γ l A RA t ->
  (exists k C a, [ G ; Γ ⊢g t ⤳* tmSq k C a : tySq l A @ l ] /\
     lequiv (gL G) k l /\ [ G ; Γ ⊢ A ≈ C @ l ] /\ RA a a) \/
  (exists ν, [ G ; Γ ⊢g t ⤳* ν : tySq l A @ l ] /\ [ G ; Γ ⊢ ν ~ ν : tySq l A @ l ]).
Proof.
  intros (w & Hw & Hn). revert Hw.
  destruct Hn as [k C a Hk HC Ha | ν Hν]; intros Hw.
  - left. exists k, C, a. exact (conj Hw (conj Hk (conj HC Ha))).
  - right. exists ν. exact (conj Hw Hν).
Qed.

End Squash.

(** ** The hypotheses are satisfiable

    By [Unit], forgetting the carrier: [tySq l A := Unit^l],
    [tmSq k C a := tt^k]. *)
Lemma Squash_hyps_unit `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} :
  (forall G Γ l l' A A', lequiv (gL G) l l' ->
     [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] -> [ G ; Γ ⊢ tyUnit l ≈ tyUnit l' @ l ]) /\
  (forall G Γ l (A : ty) t t', lwf (gL G) l ->
     [ G ; Γ ⊢g t : tyUnit l @ l ] -> [ G ; Γ ⊢g t' : tyUnit l @ l ] -> [ G ; Γ ⊢ t ≈ t' : tyUnit l @ l ]).
Proof.
  split.
  - intros G Γ l l' A A' Hl HA _. exact (geq_ty_unit (ctx_of_ty HA) Hl).
  - intros G Γ l A t t' Hw Ht Ht'. exact (geq_tm_unit_eta Hw Ht Ht').
Qed.
