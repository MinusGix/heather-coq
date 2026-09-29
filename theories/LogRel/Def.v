(** * The Kripke logical relation for MLTT (ch. 7 §"Kripke Logical Relations
    for MLTT", j = prog)

    [Prop]-valued, as required by the universe hierarchy (see
    logrel-coq-spike/SPIKE_UNIVERSES.md).  A type relation carries its term
    relation as an index: [LR n rec G Γ T T' l R] says that [T] and [T'] are
    related at level [l] and [R] relates their terms.

    Staging.  Π relates its domain at a level [l1 ≤ l1 ⊔ l2], so levels
    cannot be the recursion index.  Stage [n] is a single inductive family
    over all levels; only the universe case refers to earlier stages, for a
    level [l0] of measure below [n] (via [rec]).  [LogRel l] uses stage
    [lmeasure l]; stages are related by cumulativity.

    Level equivalences are folded into each case (the paper's separate
    level-conversion case becomes a lemma).  The universe case is indexed
    by the level read off the left type's normal form, so that two
    derivations for the same type have syntactically the same relation.
    The Π case records the generic equality of domains and codomains (the
    paper records it for the whole Π type, which is derivable). *)
From DeLaM.Typing Require Export Generic.

(** ** Parameters of the layered relation (M2_DESIGN.md, D5)

    [lr_j] is the paper's [j]: at [jM] the relation also has the cases of
    contextual types.  Those cases refer to the [j = P] relation at both
    typing layers ([⊩^{≥P}_P]) and to the static-code payload, never back
    to the relation being defined, so they are parameters ([VParam]),
    instantiated once the [j = P] relation exists.  Proofs about the
    [□] cases use only [VPLaws]. *)

Inductive ljay := jP | jM.

Record VParam := {
  vp_ctx : gctx -> ctx -> ctx -> Prop ;                  (* [⊩^{≥P}_P Δ ≈ Δ'] *)
  vp_ty : gctx -> ctx -> ty -> ty -> lvl -> Prop ;       (* [Δ ⊩^{≥P}_P T ≈ T' @ l] *)
  vp_tyc : gctx -> ctx -> ty -> ty -> lvl -> Prop ;      (* payload of [box T], [box T'] *)
  vp_tmc : gctx -> ctx -> ty -> tm -> tm -> lvl -> Prop  (* payload of [box t], [box t'] *)
}.

Class LRParams := { lr_j : ljay ; lr_vp : VParam }.

Class VPLaws (vp : VParam) := {
  vpl_ctx_sym {G Δ Δ'} : vp_ctx vp G Δ Δ' -> vp_ctx vp G Δ' Δ ;
  vpl_ctx_trans {G Δ1 Δ2 Δ3} : vp_ctx vp G Δ1 Δ2 -> vp_ctx vp G Δ2 Δ3 -> vp_ctx vp G Δ1 Δ3 ;
  vpl_ty_sym {G Δ T T' l} : vp_ty vp G Δ T T' l -> vp_ty vp G Δ T' T l ;
  vpl_ty_trans {G Δ T1 T2 T3 l} : vp_ty vp G Δ T1 T2 l -> vp_ty vp G Δ T2 T3 l -> vp_ty vp G Δ T1 T3 l ;
  vpl_tyc_sym {G Δ T T' l} : vp_tyc vp G Δ T T' l -> vp_tyc vp G Δ T' T l ;
  vpl_tyc_trans {G Δ T1 T2 T3 l} :
    vp_tyc vp G Δ T1 T2 l -> vp_tyc vp G Δ T2 T3 l -> vp_tyc vp G Δ T1 T3 l ;
  vpl_tmc_sym {G Δ T t t' l} : vp_tmc vp G Δ T t t' l -> vp_tmc vp G Δ T t' t l ;
  vpl_tmc_trans {G Δ T t1 t2 t3 l} :
    vp_tmc vp G Δ T t1 t2 l -> vp_tmc vp G Δ T t2 t3 l -> vp_tmc vp G Δ T t1 t3 l ;
  (* conversion along related contexts, types and levels *)
  vpl_ty_ctx {G Δ Δ' T T' l} : vp_ctx vp G Δ Δ' -> vp_ty vp G Δ T T' l -> vp_ty vp G Δ' T T' l ;
  vpl_tyc_ctx {G Δ Δ' T T' l} : vp_ctx vp G Δ Δ' -> vp_tyc vp G Δ T T' l -> vp_tyc vp G Δ' T T' l ;
  vpl_tmc_ctx {G Δ Δ' T t t' l} :
    vp_ctx vp G Δ Δ' -> vp_tmc vp G Δ T t t' l -> vp_tmc vp G Δ' T t t' l ;
  vpl_tmc_ty {G Δ T T' t t' l} : vp_ty vp G Δ T T' l -> vp_tmc vp G Δ T t t' l -> vp_tmc vp G Δ T' t t' l ;
  vpl_ty_lconv {G Δ T T' l l'} : lequiv (gL G) l l' -> vp_ty vp G Δ T T' l -> vp_ty vp G Δ T T' l' ;
  vpl_tyc_lconv {G Δ T T' l l'} : lequiv (gL G) l l' -> vp_tyc vp G Δ T T' l -> vp_tyc vp G Δ T T' l' ;
  vpl_tmc_lconv {G Δ T t t' l l'} :
    lequiv (gL G) l l' -> vp_tmc vp G Δ T t t' l -> vp_tmc vp G Δ T t t' l' ;
  (* level equivalence of syntax (M3_DESIGN.md E6'): [≡ₗ]-related
     syntax, each side related to itself, is related *)
  vpl_ctx_leq {G Δ Δ'} : vp_ctx vp G Δ Δ -> vp_ctx vp G Δ' Δ' -> ctx_leq Δ Δ' -> vp_ctx vp G Δ Δ' ;
  vpl_ty_leq {G Δ T T' l} : vp_ty vp G Δ T T l -> vp_ty vp G Δ T' T' l -> ty_leq T T' -> vp_ty vp G Δ T T' l ;
  vpl_tyc_leq {G Δ T T' l} :
    vp_tyc vp G Δ T T l -> vp_tyc vp G Δ T' T' l -> ty_leq T T' -> vp_tyc vp G Δ T T' l ;
  vpl_tmc_leq {G Δ A t t' l} :
    vp_tmc vp G Δ A t t l -> vp_tmc vp G Δ A t' t' l -> tm_leq t t' -> vp_tmc vp G Δ A t t' l ;
  (* global weakening *)
  vpl_ctx_gwk {γ G' G Δ Δ'} : gwk_ok γ G' G -> [ ⊢ G' ] ->
    vp_ctx vp G Δ Δ' -> vp_ctx vp G' Δ⟦γ⟧ Δ'⟦γ⟧ ;
  vpl_ty_gwk {γ G' G Δ T T' l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
    vp_ty vp G Δ T T' l -> vp_ty vp G' Δ⟦γ⟧ T⟦γ⟧ T'⟦γ⟧ l ;
  vpl_tyc_gwk {γ G' G Δ T T' l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
    vp_tyc vp G Δ T T' l -> vp_tyc vp G' Δ⟦γ⟧ T⟦γ⟧ T'⟦γ⟧ l ;
  vpl_tmc_gwk {γ G' G Δ T t t' l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
    vp_tmc vp G Δ T t t' l -> vp_tmc vp G' Δ⟦γ⟧ T⟦γ⟧ t⟦γ⟧ t'⟦γ⟧ l
}.

(** The empty parameter, for relations at [jP] (the [□] cases are then
    unreachable anyway). *)
Definition vp_empty : VParam :=
  {| vp_ctx := fun _ _ _ => False ; vp_ty := fun _ _ _ _ _ => False ;
     vp_tyc := fun _ _ _ _ _ => False ; vp_tmc := fun _ _ _ _ _ _ => False |}.

#[export] Instance vp_empty_laws : VPLaws vp_empty.
Proof. constructor; cbn; tauto. Qed.

(** The parameters of the [j = P] relation. *)
Definition LR_P : LRParams := {| lr_j := jP ; lr_vp := vp_empty |}.
#[export] Instance LR_P_laws : VPLaws (@lr_vp LR_P) := vp_empty_laws.

Section LRDef.
Context `{E : GenericEq} `{LP : LRParams}.

Definition RedRel := gctx -> ctx -> ty -> ty -> lvl -> (tm -> tm -> Prop) -> Prop.

(** Equivalence of term relations.  Every case of the relation accepts any
    term relation equivalent to its canonical one ("saturation"), so that
    constructions like symmetry can name their term relations explicitly
    (e.g. [flip domR]) without choice or extensionality axioms. *)
Definition releq (R R' : tm -> tm -> Prop) := forall t t', R t t' <-> R' t t'.

(** ** Natural numbers *)

Inductive NatRel (G : gctx) (Γ : ctx) : tm -> tm -> Prop :=
| natrel t t' w w' :
    [ G ; Γ ⊢g t ⤳* w : tyNat @ lzero ] -> [ G ; Γ ⊢g t' ⤳* w' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ w ≈ w' : tyNat @ lzero ] -> NatNf G Γ w w' -> NatRel G Γ t t'
with NatNf (G : gctx) (Γ : ctx) : tm -> tm -> Prop :=
| natnf_zero : NatNf G Γ zero zero
| natnf_succ t t' : NatRel G Γ t t' -> NatNf G Γ (succ t) (succ t')
| natnf_ne ν ν' : [ G ; Γ ⊢ ν ~ ν' : tyNat @ lzero ] -> NatNf G Γ ν ν'.

Scheme NatRel_mut := Induction for NatRel Sort Prop
  with NatNf_mut := Induction for NatNf Sort Prop.

(** ** Universes: codes whose decodings are related one stage down

    As for the annotations of applications in the Π case, the decodings
    are related for every choice of equivalent annotations on [El]. *)

Definition URel (rec : lvl -> RedRel) (G : gctx) (Γ : ctx) (l0 : lvl) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyU l0 @ lsuc l0 ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyU l0 @ lsuc l0 ] /\
    whnf w /\ whnf w' /\ [ G ; Γ ⊢ w ≈ w' : tyU l0 @ lsuc l0 ] /\
    forall la lb, lequiv (gL G) la l0 -> lequiv (gL G) lb l0 ->
      exists R, rec l0 G Γ (tyEl la w) (tyEl lb w') l0 R.

(** ** Neutral types *)

Definition NeRel (G : gctx) (Γ : ctx) (V V' : ty) (l : lvl) : tm -> tm -> Prop :=
  fun t t' => exists ν ν',
    [ G ; Γ ⊢g t ⤳* ν : V @ l ] /\ [ G ; Γ ⊢g t' ⤳* ν' : V' @ l ] /\
    [ G ; Γ ⊢ ν ~ ν' : V @ l ] /\ [ G ; Γ ⊢ ν ~ ν' : V' @ l ].

(** ** Kripke weakenings

    [ρ : (G', Δ) ≤ (G, Γ)]: a global weakening [γ : G' ≤ G] followed by a
    local one [r : Δ ≤ Γ⟦γ⟧] (OPE data for both, closed under
    composition).  The generic laws take the underlying renamings.  With
    [γ] the identity, the action on syntax is literally the local one. *)

Record kwk (G : gctx) (Γ : ctx) : Type := mkKwk {
  kw_G : gctx ;
  kw_Δ : ctx ;
  kw_γ : gweak ;
  kw_r : wk ;
  kw_gok : gwk_ok kw_γ kw_G G ;
  kw_wf : kw_r : kw_Δ ≤ Γ⟦kw_γ⟧ ;
  kw_ctx : [ kw_G ; kw_Δ ⊢g ]
}.
Arguments kw_G {G Γ}. Arguments kw_Δ {G Γ}. Arguments kw_γ {G Γ}. Arguments kw_r {G Γ}.
Arguments kw_gok {G Γ}. Arguments kw_wf {G Γ}. Arguments kw_ctx {G Γ}.

Definition kty {G Γ} (ρ : kwk G Γ) (T : ty) : ty := T⟦kw_γ ρ⟧⟨kw_r ρ⟩.
Definition ktm {G Γ} (ρ : kwk G Γ) (t : tm) : tm := t⟦kw_γ ρ⟧⟨kw_r ρ⟩.
(** Under one local binder. *)
Definition ktyl {G Γ} (ρ : kwk G Γ) (T : ty) : ty := T⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.
Definition ktml {G Γ} (ρ : kwk G Γ) (t : tm) : tm := t⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.

(** A purely local weakening. *)
Definition kw_loc {G Γ Δ} (r : wk) (Hr : r : Δ ≤ Γ) (HΔ : [ G ; Δ ⊢g ]) : kwk G Γ :=
  {| kw_G := G ; kw_Δ := Δ ; kw_γ := gwk_id ; kw_r := r ;
     kw_gok := gwk_ok_id G ; kw_wf := Hr ; kw_ctx := HΔ |}.

(** Composition: first [ρ], then [ρ']. *)
Lemma kw_comp_wf {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) :
  wk_comp (kw_r ρ') (kw_r ρ) : kw_Δ ρ' ≤ Γ⟦gwk_comp (kw_γ ρ') (kw_γ ρ)⟧.
Proof.
  rewrite <- gwa_comp_ctx. eapply wk_comp_wf; [exact (kw_wf ρ') | apply wk_wf_gwa, kw_wf].
Qed.

Definition kw_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) : kwk G Γ :=
  {| kw_G := kw_G ρ' ; kw_Δ := kw_Δ ρ' ; kw_γ := gwk_comp (kw_γ ρ') (kw_γ ρ) ;
     kw_r := wk_comp (kw_r ρ') (kw_r ρ) ; kw_gok := gwk_ok_comp (kw_gok ρ') (kw_gok ρ) ;
     kw_wf := kw_comp_wf ρ ρ' ; kw_ctx := kw_ctx ρ' |}.

(** ** Dependent functions

    Kripke quantification is over [kwk]. *)

Definition DomRel (G : gctx) (Γ : ctx) := kwk G Γ -> tm -> tm -> Prop.
Definition CodRel (G : gctx) (Γ : ctx) (domR : DomRel G Γ) :=
  forall (ρ : kwk G Γ) a a', domR ρ a a' -> tm -> tm -> Prop.

(** Related functions: reduce to related weak-head normal forms whose
    applications to related arguments are related, in every weakening, for
    every choice of (equivalent) annotations on the application. *)
Definition PiRel (G : gctx) (Γ : ctx) (l1 l2 l3 l4 : lvl) (A B A' B' : ty)
    (domR : DomRel G Γ) (codR : CodRel G Γ domR) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyPi l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢g t' ⤳* w' : tyPi l3 l4 A' B' @ lmax l1 l2 ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tyPi l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢ w ≈ w' : tyPi l3 l4 A' B' @ lmax l1 l2 ] /\
    forall (ρ : kwk G Γ) a a' (ha : domR ρ a a') la lb la' lb' A1 B1 A1' B1',
      lequiv (gL G) la l1 -> lequiv (gL G) lb l2 ->
      lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
      [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ A1 @ l1 ] ->
      [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ B1 @ l2 ] ->
      [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A' ≈ A1' @ l1 ] ->
      [ kw_G ρ ; kw_Δ ρ ,, kty ρ A' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ] ->
      codR ρ a a' ha (app (ktm ρ w) la lb A1 B1 a) (app (ktm ρ w') la' lb' A1' B1' a').

(** ** Dependent pairs (M8_DESIGN.md I6)

    Related pairs reduce to related weak-head normal forms whose
    projections are related, in every weakening and for every choice of
    (equivalent) annotations on the projections: the first projections by
    the domain relation, the second ones by the codomain relation at that
    relation's proof. *)
Definition SigRel (G : gctx) (Γ : ctx) (l1 l2 l3 l4 : lvl) (A B A' B' : ty)
    (domR : DomRel G Γ) (codR : CodRel G Γ domR) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tySig l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢g t' ⤳* w' : tySig l3 l4 A' B' @ lmax l1 l2 ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tySig l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢ w ≈ w' : tySig l3 l4 A' B' @ lmax l1 l2 ] /\
    forall (ρ : kwk G Γ) la lb la' lb' A1 B1 A1' B1',
      lequiv (gL G) la l1 -> lequiv (gL G) lb l2 ->
      lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
      [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ A1 @ l1 ] ->
      [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ B1 @ l2 ] ->
      [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A' ≈ A1' @ l1 ] ->
      [ kw_G ρ ; kw_Δ ρ ,, kty ρ A' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ] ->
      exists h : domR ρ (tmFst la lb A1 B1 (ktm ρ w)) (tmFst la' lb' A1' B1' (ktm ρ w')),
        codR ρ _ _ h (tmSnd la lb A1 B1 (ktm ρ w)) (tmSnd la' lb' A1' B1' (ktm ρ w')).

(** ** The unit type (M8_DESIGN.md K5)

    Proof irrelevant: any two terms with weak-head normal forms at [Unit]
    are related, whatever the forms. Escape comes from the generic law
    [geq_tm_unit_eta]. The normal forms are kept (as logrel-coq's
    [UnitRedTm] does, unlike Heather's pen-and-paper relation) so that
    typed terms still normalize, which the algorithmic instance needs. *)
Definition UnitRel (G : gctx) (Γ : ctx) (l : lvl) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyUnit l @ l ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyUnit l @ l ] /\ whnf w /\ whnf w'.

(** ** The type-level data of a binder former

    [Π] and [Σ] (and later formers of the same shape) share it: both sides
    reduce to the former, the domains and families are well formed and
    generically equal, and the levels agree. Only the term relation
    differs between them. *)
Record PolyFacts (G : gctx) (Γ : ctx) (F : lvl -> lvl -> ty -> ty -> ty) (T T' : ty)
    (l l1 l2 l3 l4 : lvl) (A B A' B' : ty) : Prop := {
  pf_lvl : lequiv (gL G) l (lmax l1 l2) ;
  pf_l3 : lequiv (gL G) l3 l1 ;
  pf_l4 : lequiv (gL G) l4 l2 ;
  pf_w1 : lwf (gL G) l1 ;
  pf_w2 : lwf (gL G) l2 ;
  pf_red : [ G ; Γ ⊢g T ⤳* F l1 l2 A B @ l ] ;
  pf_red' : [ G ; Γ ⊢g T' ⤳* F l3 l4 A' B' @ l ] ;
  pf_A : [ G ; Γ ⊢g A @ l1 ] ;
  pf_A' : [ G ; Γ ⊢g A' @ l1 ] ;
  pf_B : [ G ; Γ ,, A @ l1 ⊢g B @ l2 ] ;
  pf_B' : [ G ; Γ ,, A' @ l1 ⊢g B' @ l2 ] ;
  pf_AA : [ G ; Γ ⊢ A ≈ A' @ l1 ] ;
  pf_BB : [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ]
}.

(** ** Contextual types (07a:686–765), [j = M] only

    A weak-head normal form of [□] is a [box] of static code, related by
    the payload, or a neutral.  Normal forms are related at the contexts
    (and annotations) of both sides, which makes symmetry immediate. *)

Inductive CTypNf (G : gctx) (Γ Δ : ctx) (k : lvl) : tm -> tm -> Prop :=
| ctyn_box T1 T1' : vp_tyc lr_vp G Δ T1 T1' k -> CTypNf G Γ Δ k (boxT T1) (boxT T1')
| ctyn_ne ν ν' : [ G ; Γ ⊢ ν ~ ν' : tyCTyp Δ k @ lzero ] -> CTypNf G Γ Δ k ν ν'.

Inductive CTrmNf (G : gctx) (Γ Δ : ctx) (A : ty) (k : lvl) : tm -> tm -> Prop :=
| ctrn_box t1 t1' : vp_tmc lr_vp G Δ A t1 t1' k -> CTrmNf G Γ Δ A k (boxt t1) (boxt t1')
| ctrn_ne ν ν' : [ G ; Γ ⊢ ν ~ ν' : tyCTrm Δ A k @ lzero ] -> CTrmNf G Γ Δ A k ν ν'.

Definition CTypRel (G : gctx) (Γ Δ Δ' : ctx) (k k' : lvl) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyCTyp Δ k @ lzero ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyCTyp Δ' k' @ lzero ] /\
    [ G ; Γ ⊢ w ≈ w' : tyCTyp Δ k @ lzero ] /\ [ G ; Γ ⊢ w ≈ w' : tyCTyp Δ' k' @ lzero ] /\
    CTypNf G Γ Δ k w w' /\ CTypNf G Γ Δ' k' w w'.

Definition CTrmRel (G : gctx) (Γ Δ Δ' : ctx) (A A' : ty) (k k' : lvl) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyCTrm Δ A k @ lzero ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyCTrm Δ' A' k' @ lzero ] /\
    [ G ; Γ ⊢ w ≈ w' : tyCTrm Δ A k @ lzero ] /\ [ G ; Γ ⊢ w ≈ w' : tyCTrm Δ' A' k' @ lzero ] /\
    CTrmNf G Γ Δ A k w w' /\ CTrmNf G Γ Δ' A' k' w w'.

Inductive ModRel (G : gctx) (Γ : ctx) : ty -> ty -> lvl -> (tm -> tm -> Prop) -> Prop :=
| MRctyp T T' l Δ Δ' k k' R :
    lequiv (gL G) l lzero -> lequiv (gL G) k k' ->
    [ G ; Γ ⊢g T ⤳* tyCTyp Δ k @ l ] -> [ G ; Γ ⊢g T' ⤳* tyCTyp Δ' k' @ l ] ->
    vp_ctx lr_vp G Δ Δ' ->
    [ G ; Γ ⊢ tyCTyp Δ k ≈ tyCTyp Δ' k' @ lzero ] ->
    releq R (CTypRel G Γ Δ Δ' k k') ->
    ModRel G Γ T T' l R
| MRctrm T T' l Δ Δ' A A' k k' R :
    lequiv (gL G) l lzero -> lequiv (gL G) k k' ->
    [ G ; Γ ⊢g T ⤳* tyCTrm Δ A k @ l ] -> [ G ; Γ ⊢g T' ⤳* tyCTrm Δ' A' k' @ l ] ->
    vp_ctx lr_vp G Δ Δ' -> vp_ty lr_vp G Δ A A' k -> vp_ty lr_vp G Δ' A' A k' ->
    [ G ; Γ ⊢ tyCTrm Δ A k ≈ tyCTrm Δ' A' k' @ lzero ] ->
    releq R (CTrmRel G Γ Δ Δ' A A' k k') ->
    ModRel G Γ T T' l R.

(** ** Meta-functions (07a:766–845, M5_DESIGN.md G3), [j = M] only

    The body lives under one global binder. A Kripke world moves it under
    [⇑γ] and then its local renaming ([kbody]); the binder is then
    instantiated at related contexts ([CΠ]) or related types of layer P
    ([TΠ]). The domains are the [j = P] relation, the parameters [vp_ctx]
    and [vp_ty], so the instances stay at stage [n]. As for Π, the
    instances are quantified at the left domain only. *)

(** [⇑γ], with the identity weakening kept literally the identity. *)
Definition gwk_up' (γ : gweak) : gweak := match γ with gwk_id => gwk_id | _ => gwk_up γ end.
(** The binding moved along [γ], likewise. *)
Definition gdecl_gwa (γ : gweak) (D : gdecl) : gdecl :=
  match γ with gwk_id => D | _ => gdecl_ren D γ end.

Lemma gdecl_gwa_ctx γ : gdecl_gwa γ gdCtx = gdCtx.
Proof. now destruct γ. Qed.
Lemma gdecl_gwa_ty γ Δ i l : gdecl_gwa γ (gdTy Δ i l) = gdTy Δ⟦γ⟧ i l.
Proof. now destruct γ. Qed.

Lemma gwa_up'_shift (Γ : ctx) γ : Γ⟪S⟫⟦gwk_up' γ⟧ = Γ⟦γ⟧⟪S⟫.
Proof.
  destruct γ as [|γ0|γ0]; cbn [gwk_up' gwa]; [reflexivity | ..].
  - exact (gcren_shift_up Γ (gwk_fn (gwk_step γ0))).
  - exact (gcren_shift_up Γ (gwk_fn (gwk_up γ0))).
Qed.

Definition kbody {G Γ} (ρ : kwk G Γ) (T : ty) : ty := T⟦gwk_up' (kw_γ ρ)⟧⟨kw_r ρ⟩.
Definition kbodyt {G Γ} (ρ : kwk G Γ) (t : tm) : tm := t⟦gwk_up' (kw_γ ρ)⟧⟨kw_r ρ⟩.

Definition CInstRel (G : gctx) (Γ : ctx) :=
  forall (ρ : kwk G Γ) Δ Δ', vp_ctx lr_vp (kw_G ρ) Δ Δ' -> tm -> tm -> Prop.
Definition TInstRel (G : gctx) (Γ : ctx) (Δ1 : ctx) (l1 : lvl) :=
  forall (ρ : kwk G Γ) A A', vp_ty lr_vp (kw_G ρ) Δ1⟦kw_γ ρ⟧ A A' l1 -> tm -> tm -> Prop.

Definition CPiRel (G : gctx) (Γ : ctx) (l1 l2 : lvl) (T1 T1' : ty) (instR : CInstRel G Γ) :
    tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyCPi l1 T1 @ l1 ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyCPi l2 T1' @ l1 ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tyCPi l1 T1 @ l1 ] /\ [ G ; Γ ⊢ w ≈ w' : tyCPi l2 T1' @ l1 ] /\
    forall (ρ : kwk G Γ) Δ Δ' (h : vp_ctx lr_vp (kw_G ρ) Δ Δ'),
      instR ρ Δ Δ' h (capp (ktm ρ w) Δ) (capp (ktm ρ w') Δ').

Definition TPiRel (G : gctx) (Γ : ctx) (Δ1 Δ1' : ctx) (l1 l2 l3 l4 : lvl) (T1 T1' : ty)
    (instR : TInstRel G Γ Δ1 l1) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyTPi Δ1 l1 l2 T1 @ l2 ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyTPi Δ1' l3 l4 T1' @ l2 ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tyTPi Δ1 l1 l2 T1 @ l2 ] /\ [ G ; Γ ⊢ w ≈ w' : tyTPi Δ1' l3 l4 T1' @ l2 ] /\
    forall (ρ : kwk G Γ) A A' (h : vp_ty lr_vp (kw_G ρ) Δ1⟦kw_γ ρ⟧ A A' l1),
      instR ρ A A' h (tapp (ktm ρ w) A) (tapp (ktm ρ w') A').

(** ** The relation, stage [n] *)

Inductive LR (n : nat) (rec : lvl -> RedRel) : RedRel :=
| LRnat G Γ T T' l R :
    lequiv (gL G) l lzero ->
    [ G ; Γ ⊢g T ⤳* tyNat @ l ] -> [ G ; Γ ⊢g T' ⤳* tyNat @ l ] ->
    releq R (NatRel G Γ) ->
    LR n rec G Γ T T' l R
| LRU G Γ T T' l l1 l2 R :
    lequiv (gL G) l (lsuc l1) -> lequiv (gL G) l2 l1 -> lmeasure l1 < n ->
    [ G ; Γ ⊢g T ⤳* tyU l1 @ l ] -> [ G ; Γ ⊢g T' ⤳* tyU l2 @ l ] ->
    releq R (URel rec G Γ l1) ->
    LR n rec G Γ T T' l R
| LRne G Γ T T' l V V' R :
    [ G ; Γ ⊢g T ⤳* V @ l ] -> [ G ; Γ ⊢g T' ⤳* V' @ l ] -> [ G ; Γ ⊢ V ~ V' @ l ] ->
    releq R (NeRel G Γ V V' l) ->
    LR n rec G Γ T T' l R
| LRpi G Γ T T' l l1 l2 l3 l4 A B A' B'
    (domR : DomRel G Γ) (codR : CodRel G Γ domR) R :
    PolyFacts G Γ tyPi T T' l l1 l2 l3 l4 A B A' B' ->
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A') l1 (domR ρ)) ->
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ B)[lsingle a] (ktyl ρ B')[lsingle a'] l2
           (codR ρ a a' ha)) ->
    releq R (PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR) ->
    LR n rec G Γ T T' l R
| LRmod G Γ T T' l R :
    lr_j = jM -> ModRel G Γ T T' l R ->
    LR n rec G Γ T T' l R
| LRcpi G Γ T T' l l1 l2 T1 T1' (instR : CInstRel G Γ) R :
    lr_j = jM ->
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tyCPi l1 T1 @ l ] -> [ G ; Γ ⊢g T' ⤳* tyCPi l2 T1' @ l ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢g T1 @ l1 ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢g T1' @ l1 ] ->
    [ G ; Γ ⊢ tyCPi l1 T1 ≈ tyCPi l2 T1' @ l1 ] ->
    (forall (ρ : kwk G Γ) Δ Δ' (h : vp_ctx lr_vp (kw_G ρ) Δ Δ'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (kbody ρ T1)⦃gsingle (GCtx Δ)⦄ (kbody ρ T1')⦃gsingle (GCtx Δ')⦄
           l1 (instR ρ Δ Δ' h)) ->
    releq R (CPiRel G Γ l1 l2 T1 T1' instR) ->
    LR n rec G Γ T T' l R
| LRtpi G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' (instR : TInstRel G Γ Δ1 l1) R :
    lr_j = jM ->
    lequiv (gL G) l l2 -> lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
    lwf (gL G) l1 -> lwf (gL G) l2 ->
    [ G ; Γ ⊢g T ⤳* tyTPi Δ1 l1 l2 T1 @ l ] -> [ G ; Γ ⊢g T' ⤳* tyTPi Δ1' l3 l4 T1' @ l ] ->
    vp_ctx lr_vp G Δ1 Δ1' ->
    [ gext G (gdTy Δ1 lD l1) ; Γ⟪S⟫ ⊢g T1 @ l2 ] -> [ gext G (gdTy Δ1' lD l3) ; Γ⟪S⟫ ⊢g T1' @ l4 ] ->
    [ G ; Γ ⊢ tyTPi Δ1 l1 l2 T1 ≈ tyTPi Δ1' l3 l4 T1' @ l2 ] ->
    (forall (ρ : kwk G Γ) A A' (h : vp_ty lr_vp (kw_G ρ) Δ1⟦kw_γ ρ⟧ A A' l1),
        LR n rec (kw_G ρ) (kw_Δ ρ) (kbody ρ T1)⦃gsingle (GTy A)⦄ (kbody ρ T1')⦃gsingle (GTy A')⦄
           l2 (instR ρ A A' h)) ->
    releq R (TPiRel G Γ Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR) ->
    LR n rec G Γ T T' l R
| LRsig G Γ T T' l l1 l2 l3 l4 A B A' B'
    (domR : DomRel G Γ) (codR : CodRel G Γ domR) R :
    PolyFacts G Γ tySig T T' l l1 l2 l3 l4 A B A' B' ->
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A') l1 (domR ρ)) ->
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ B)[lsingle a] (ktyl ρ B')[lsingle a'] l2
           (codR ρ a a' ha)) ->
    releq R (SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR) ->
    LR n rec G Γ T T' l R
| LRunit G Γ T T' l l1 l2 R :
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tyUnit l1 @ l ] -> [ G ; Γ ⊢g T' ⤳* tyUnit l2 @ l ] ->
    releq R (UnitRel G Γ l1) ->
    LR n rec G Γ T T' l R.

(** ** Stages *)

Fixpoint LRbelow (n : nat) : lvl -> RedRel :=
  match n with
  | 0 => fun _ _ _ _ _ _ _ => False
  | S n => fun l0 => if Nat.eqb (lmeasure l0) n then LR n (LRbelow n) else LRbelow n l0
  end.

(** The relation for types at level [l]. *)
Definition LogRel (l : lvl) : RedRel := LR (lmeasure l) (LRbelow (lmeasure l)).

Lemma LRbelow_spec n l0 : lmeasure l0 < n -> LRbelow n l0 = LogRel l0.
Proof.
  induction n as [|n IH]; intros Hlt; [lia|]. cbn.
  destruct (Nat.eqb_spec (lmeasure l0) n) as [<-|Hne]; [reflexivity|]. apply IH; lia.
Qed.

End LRDef.

Arguments pf_lvl {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_l3 {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_l4 {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_w1 {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_w2 {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_red {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_red' {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_A {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_A' {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_B {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_B' {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_AA {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.
Arguments pf_BB {E G Γ F T T' l l1 l2 l3 l4 A B A' B'}.

(** Expose the facts of every [PolyFacts] hypothesis. *)
Ltac open_poly :=
  repeat match goal with P : PolyFacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct P end.

Arguments mkKwk {E G Γ}.
Arguments kw_G {E G Γ}. Arguments kw_Δ {E G Γ}. Arguments kw_γ {E G Γ}. Arguments kw_r {E G Γ}.
Arguments kw_gok {E G Γ}. Arguments kw_wf {E G Γ}. Arguments kw_ctx {E G Γ}.
