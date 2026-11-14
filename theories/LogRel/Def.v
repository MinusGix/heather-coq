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
From DeLaM.Typing Require Import PresupIWf PresupIWi.

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

(** [M]'s children's type [M(σ)(C[j, s, p])], in [Γ, s, p] for [j] in
    [Γ]: the codomain of [out]'s [Π] ([mOutTy], M18b). *)
Notation mKidTy l l' li X A B C j :=
  (tyM l l' li X⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
     C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C[llift (llift (lsingle j))]).

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
    local one [r : Δ ≤ Γ⟦γ⟧] (OPE data for both).  The generic laws take
    the underlying renamings.  With [γ] the identity, the action on syntax
    is literally the local one.

    Composition is associative, and the identity world a unit, by
    [eq_refl] (heather-coq#61, M18_DESIGN.md "Associative worlds"). A world
    stores its weakenings as what they do to a later one ([kw_gk γ0] is
    [γ0] after [γ], [kw_rk r0] is [r0] after [r]) and its two
    well-formedness proofs as what they do to a later one's
    ([kw_gokk], [kw_wfk]), so that composition is function composition in
    every field. That the stored maps are composition with [γ] and [r]
    ([kw_gcoh], [kw_rcoh]) is in [SProp]: any two proofs are convertible,
    and the equations, decidable, come back out ([kw_gk_coh]). The record
    has primitive projections, so a world is its own η-expansion. [kw_γ],
    [kw_r], [kw_gok] and [kw_wf] are the plain data and proofs, and
    [kw_mk] builds a world from them. *)

(** A proposition squashed into [SProp]. *)
Inductive SBox (P : Prop) : SProp := sbox : P -> SBox P.
Arguments sbox {P}.
Inductive sEmpty : SProp := .

Definition sunbox {P : Prop} (d : {P} + {~ P}) (b : SBox P) : P :=
  match d with
  | left p => p
  | right n => sEmpty_rect (fun _ => P) (match b with sbox p => False_sind sEmpty (n p) end)
  end.

Definition gweak_eq_dec (γ γ' : gweak) : {γ = γ'} + {γ <> γ'}.
Proof. decide equality. Defined.
Definition wk_eq_dec (r r' : wk) : {r = r'} + {r <> r'}.
Proof. decide equality. Defined.

Lemma wk_comp_assoc (r'' r' r : wk) : wk_comp r'' (wk_comp r' r) = wk_comp (wk_comp r'' r') r.
Proof using .
  revert r' r; induction r'' as [|r'' IH|r'' IH]; intros r' r; [reflexivity | cbn; now rewrite IH |].
  destruct r' as [|r'|r']; [reflexivity | cbn; now rewrite IH |].
  destruct r as [|r|r]; cbn; now rewrite ?IH.
Qed.
Lemma gwk_comp_assoc (γ'' γ' γ : gweak) : gwk_comp γ'' (gwk_comp γ' γ) = gwk_comp (gwk_comp γ'' γ') γ.
Proof using .
  revert γ' γ; induction γ'' as [|γ'' IH|γ'' IH]; intros γ' γ; [reflexivity | cbn; now rewrite IH |].
  destruct γ' as [|γ'|γ']; [reflexivity | cbn; now rewrite IH |].
  destruct γ as [|γ|γ]; cbn; now rewrite ?IH.
Qed.
Lemma wk_comp_id_r (r : wk) : wk_comp r wk_id = r.
Proof using . induction r; cbn; congruence. Qed.

#[projections(primitive)]
Record kwk (G : gctx) (Γ : ctx) : Type := mkKwk {
  kw_G : gctx ;
  kw_Δ : ctx ;
  kw_gk : gweak -> gweak ;
  kw_rk : wk -> wk ;
  kw_gcoh : forall γ0, SBox (kw_gk γ0 = gwk_comp γ0 (kw_gk gwk_id)) ;
  kw_rcoh : forall r0, SBox (kw_rk r0 = wk_comp r0 (kw_rk wk_id)) ;
  kw_gokk : forall γ0 G', gwk_ok γ0 G' kw_G -> gwk_ok (kw_gk γ0) G' G ;
  kw_wfk : forall γ0 Ξ r0, r0 : Ξ ≤ kw_Δ⟦γ0⟧ -> kw_rk r0 : Ξ ≤ Γ⟦kw_gk γ0⟧ ;
  kw_ctx : [ kw_G ; kw_Δ ⊢g ]
}.
Arguments kw_G {G Γ}. Arguments kw_Δ {G Γ}. Arguments kw_gk {G Γ}. Arguments kw_rk {G Γ}.
Arguments kw_gcoh {G Γ}. Arguments kw_rcoh {G Γ}. Arguments kw_gokk {G Γ}. Arguments kw_wfk {G Γ}.
Arguments kw_ctx {G Γ}.

(** The plain data and proofs. *)
Definition kw_γ {G Γ} (ρ : kwk G Γ) : gweak := kw_gk ρ gwk_id.
Definition kw_r {G Γ} (ρ : kwk G Γ) : wk := kw_rk ρ wk_id.
Definition kw_gok {G Γ} (ρ : kwk G Γ) : gwk_ok (kw_γ ρ) (kw_G ρ) G :=
  kw_gokk ρ gwk_id (kw_G ρ) (gwk_ok_id _).
Definition kw_wf {G Γ} (ρ : kwk G Γ) : kw_r ρ : kw_Δ ρ ≤ Γ⟦kw_γ ρ⟧ :=
  kw_wfk ρ gwk_id (kw_Δ ρ) wk_id (wkwf_id _).

Definition kty {G Γ} (ρ : kwk G Γ) (T : ty) : ty := T⟦kw_γ ρ⟧⟨kw_r ρ⟩.
Definition ktm {G Γ} (ρ : kwk G Γ) (t : tm) : tm := t⟦kw_γ ρ⟧⟨kw_r ρ⟩.
(** Under one local binder. *)
Definition ktyl {G Γ} (ρ : kwk G Γ) (T : ty) : ty := T⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.
Definition ktml {G Γ} (ρ : kwk G Γ) (t : tm) : tm := t⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.
(** Under two local binders ([IWf]'s child index, M17b). *)
Definition ktmll {G Γ} (ρ : kwk G Γ) (t : tm) : tm := t⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩.
Definition ktyll {G Γ} (ρ : kwk G Γ) (T : ty) : ty := T⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩.
(** Under three ([M]'s child index, M18b). *)
Definition ktmlll {G Γ} (ρ : kwk G Γ) (t : tm) : tm := t⟦kw_γ ρ⟧⟨rlift (rlift (rlift (kw_r ρ)))⟩.

Lemma kw_gk_coh {G Γ} (ρ : kwk G Γ) γ0 : kw_gk ρ γ0 = gwk_comp γ0 (kw_γ ρ).
Proof using . exact (sunbox (gweak_eq_dec _ _) (kw_gcoh ρ γ0)). Qed.
Lemma kw_rk_coh {G Γ} (ρ : kwk G Γ) r0 : kw_rk ρ r0 = wk_comp r0 (kw_r ρ).
Proof using . exact (sunbox (wk_eq_dec _ _) (kw_rcoh ρ r0)). Qed.

(** A world from its data. At the identity the maps are the data by
    [match], so that [kw_γ] and [kw_r] of a world built here compute to
    the data under [cbn [kw_γ kw_gk kw_r kw_rk kw_mk]]. *)
Definition kw_mk_gk (γ : gweak) (γ0 : gweak) : gweak :=
  match γ0 with gwk_id => γ | _ => gwk_comp γ0 γ end.
Definition kw_mk_rk (r : wk) (r0 : wk) : wk :=
  match r0 with wk_id => r | _ => wk_comp r0 r end.
Lemma kw_mk_gk_eq γ γ0 : kw_mk_gk γ γ0 = gwk_comp γ0 γ.
Proof using . now destruct γ0. Qed.
Lemma kw_mk_rk_eq r r0 : kw_mk_rk r r0 = wk_comp r0 r.
Proof using . now destruct r0. Qed.

Lemma kw_mk_wfk {Γ Δ γ r} (Hr : r : Δ ≤ Γ⟦γ⟧) γ0 Ξ r0 :
  r0 : Ξ ≤ Δ⟦γ0⟧ -> kw_mk_rk r r0 : Ξ ≤ Γ⟦kw_mk_gk γ γ0⟧.
Proof using .
  intros H. rewrite kw_mk_rk_eq, kw_mk_gk_eq, <- gwa_comp_ctx.
  eapply wk_comp_wf; [exact H | apply wk_wf_gwa, Hr].
Qed.

Definition kw_mk {G Γ} (G' : gctx) (Δ : ctx) (γ : gweak) (r : wk)
    (Hγ : gwk_ok γ G' G) (Hr : r : Δ ≤ Γ⟦γ⟧) (HΔ : [ G' ; Δ ⊢g ]) : kwk G Γ :=
  {| kw_G := G' ; kw_Δ := Δ ;
     kw_gk := fun γ0 => match γ0 with gwk_id => γ | _ => gwk_comp γ0 γ end ;
     kw_rk := fun r0 => match r0 with wk_id => r | _ => wk_comp r0 r end ;
     kw_gcoh := fun γ0 => sbox (kw_mk_gk_eq γ γ0) ; kw_rcoh := fun r0 => sbox (kw_mk_rk_eq r r0) ;
     kw_gokk := fun γ0 G'' H => eq_ind _ (fun γ1 => gwk_ok γ1 G'' G) (gwk_ok_comp H Hγ) _ (eq_sym (kw_mk_gk_eq γ γ0)) ;
     kw_wfk := kw_mk_wfk Hr ; kw_ctx := HΔ |}.

(** A purely local weakening. Under [unfold kw_loc], [cbn [kw_γ kw_gk kw_r kw_rk kw_mk]]
    computes its data. *)
Lemma kw_loc_wfk {Γ Δ r} (Hr : r : Δ ≤ Γ) γ0 Ξ r0 :
  r0 : Ξ ≤ Δ⟦γ0⟧ -> kw_mk_rk r r0 : Ξ ≤ Γ⟦γ0⟧.
Proof using .
  intros H. rewrite kw_mk_rk_eq. eapply wk_comp_wf; [exact H | apply wk_wf_gwa, Hr].
Qed.

Definition kw_loc {G Γ Δ} (r : wk) (Hr : r : Δ ≤ Γ) (HΔ : [ G ; Δ ⊢g ]) : kwk G Γ :=
  {| kw_G := G ; kw_Δ := Δ ; kw_gk := fun γ0 => γ0 ;
     kw_rk := fun r0 => match r0 with wk_id => r | _ => wk_comp r0 r end ;
     kw_gcoh := fun γ0 => sbox (eq_sym (gwk_comp_id_r γ0)) ; kw_rcoh := fun r0 => sbox (kw_mk_rk_eq r r0) ;
     kw_gokk := fun γ0 G' H => H ; kw_wfk := kw_loc_wfk Hr ; kw_ctx := HΔ |}.

(** The identity world: a unit of [kw_comp] on both sides by [eq_refl]. *)
Definition kw_id {G Γ} (HΓ : [ G ; Γ ⊢g ]) : kwk G Γ :=
  {| kw_G := G ; kw_Δ := Γ ; kw_gk := fun γ0 => γ0 ; kw_rk := fun r0 => r0 ;
     kw_gcoh := fun γ0 => sbox (eq_sym (gwk_comp_id_r γ0)) ;
     kw_rcoh := fun r0 => sbox (eq_sym (wk_comp_id_r r0)) ;
     kw_gokk := fun γ0 G' H => H ; kw_wfk := fun γ0 Ξ r0 H => H ; kw_ctx := HΓ |}.

(** Composition: first [ρ], then [ρ']. *)
Lemma kw_comp_gcoh {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) γ0 :
  kw_gk ρ (kw_gk ρ' γ0) = gwk_comp γ0 (kw_gk ρ (kw_gk ρ' gwk_id)).
Proof using .
  change (kw_gk ρ' gwk_id) with (kw_γ ρ').
  rewrite (kw_gk_coh ρ (kw_gk ρ' γ0)), (kw_gk_coh ρ' γ0), (kw_gk_coh ρ (kw_γ ρ')). symmetry; apply gwk_comp_assoc.
Qed.
Lemma kw_comp_rcoh {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) r0 :
  kw_rk ρ (kw_rk ρ' r0) = wk_comp r0 (kw_rk ρ (kw_rk ρ' wk_id)).
Proof using .
  change (kw_rk ρ' wk_id) with (kw_r ρ').
  rewrite (kw_rk_coh ρ (kw_rk ρ' r0)), (kw_rk_coh ρ' r0), (kw_rk_coh ρ (kw_r ρ')). symmetry; apply wk_comp_assoc.
Qed.

Definition kw_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) : kwk G Γ :=
  {| kw_G := kw_G ρ' ; kw_Δ := kw_Δ ρ' ;
     kw_gk := fun γ0 => kw_gk ρ (kw_gk ρ' γ0) ; kw_rk := fun r0 => kw_rk ρ (kw_rk ρ' r0) ;
     kw_gcoh := fun γ0 => sbox (kw_comp_gcoh ρ ρ' γ0) ;
     kw_rcoh := fun r0 => sbox (kw_comp_rcoh ρ ρ' r0) ;
     kw_gokk := fun γ0 G' H => kw_gokk ρ (kw_gk ρ' γ0) G' (kw_gokk ρ' γ0 G' H) ;
     kw_wfk := fun γ0 Ξ r0 H => kw_wfk ρ (kw_gk ρ' γ0) Ξ (kw_rk ρ' r0) (kw_wfk ρ' γ0 Ξ r0 H) ;
     kw_ctx := kw_ctx ρ' |}.

(** The laws, by [eq_refl]. *)
Lemma kw_comp_assoc {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) (ρ'' : kwk (kw_G ρ') (kw_Δ ρ')) :
  kw_comp (kw_comp ρ ρ') ρ'' = kw_comp ρ (kw_comp ρ' ρ'').
Proof using . reflexivity. Qed.
Lemma kw_comp_id_l {G Γ} (HΓ : [ G ; Γ ⊢g ]) (ρ : kwk G Γ) : kw_comp (kw_id HΓ) ρ = ρ.
Proof using . reflexivity. Qed.
Lemma kw_comp_id_r {G Γ} (ρ : kwk G Γ) : kw_comp ρ (kw_id (kw_ctx ρ)) = ρ.
Proof using . reflexivity. Qed.

(** The data of a composite. *)
Lemma kw_γ_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) :
  kw_γ (kw_comp ρ ρ') = gwk_comp (kw_γ ρ') (kw_γ ρ).
Proof using . exact (kw_gk_coh ρ (kw_γ ρ')). Qed.
Lemma kw_r_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) :
  kw_r (kw_comp ρ ρ') = wk_comp (kw_r ρ') (kw_r ρ).
Proof using . exact (kw_rk_coh ρ (kw_r ρ')). Qed.

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

(** ** Strict equality (M10_DESIGN.md, M10a)

    [sEq] is proof irrelevant like [Unit]: any two terms with weak-head
    normal forms at the (left) [sEq] type are related, and escape comes from
    [geq_tm_seq_irr]. The type relation keeps only the generic equality of
    the components: no term relation reads the carrier's relation, so none
    is stored (a deviation from Heather's [Id]-shaped rule, MX §18).
    [sEmpty]'s terms reduce to neutrals, each related to itself and never
    to each other: the eliminator's neutral law needs neutral scrutinees
    and compares nothing else. *)
Definition SEqRel (G : gctx) (Γ : ctx) (V : ty) (l : lvl) : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : V @ l ] /\ [ G ; Γ ⊢g t' ⤳* w' : V @ l ] /\ whnf w /\ whnf w'.

Definition SEmptyRel (G : gctx) (Γ : ctx) (l : lvl) : tm -> tm -> Prop :=
  fun t t' => exists ν ν',
    [ G ; Γ ⊢g t ⤳* ν : tySEmpty l @ l ] /\ [ G ; Γ ⊢g t' ⤳* ν' : tySEmpty l @ l ] /\
    [ G ; Γ ⊢ ν ~ ν : tySEmpty l @ l ] /\ [ G ; Γ ⊢ ν' ~ ν' : tySEmpty l @ l ].

(** ** The identity type (M11_DESIGN.md, M11a)

    As logrel-coq's [IdRedTy]: the type relation keeps the carrier's
    relation [RA] at [Γ] (not in every weakening: the weakening lemma
    recurses into it), and the endpoints are related by it. Terms reduce to
    related weak-head normal forms: two [refl]s whose carriers are the
    [Id] type's and whose points are related to both endpoints, or two
    related neutrals. No [refl] is related to a neutral: that would be K.
    The annotation levels of the [refl]s are recorded, since [J]'s β reads
    them before injectivity of [Id] is available. *)
Inductive IdNf (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (a b : tm) (RA : tm -> tm -> Prop)
  : tm -> tm -> Prop :=
| idnf_refl k k' C C' c c' :
    lequiv (gL G) k l -> lequiv (gL G) k' l ->
    [ G ; Γ ⊢ A ≈ C @ l ] -> [ G ; Γ ⊢ A ≈ C' @ l ] ->
    RA a c -> RA a c' -> RA b c -> RA b c' ->
    IdNf G Γ l A a b RA (tmRefl k C c) (tmRefl k' C' c')
| idnf_ne ν ν' : [ G ; Γ ⊢ ν ~ ν' : tyId l A a b @ l ] -> IdNf G Γ l A a b RA ν ν'.

Definition IdRel (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (a b : tm) (RA : tm -> tm -> Prop)
  : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyId l A a b @ l ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyId l A a b @ l ] /\
    [ G ; Γ ⊢ w ≈ w' : tyId l A a b @ l ] /\ IdNf G Γ l A a b RA w w'.

(** ** The empty type (M12_DESIGN.md, M12a)

    Proof irrelevant, as [sEmpty]: terms reduce to neutrals, each related
    to itself and never to each other (logrel-coq's [EmptyRedTm] keeps the
    neutrals; the comparison is dropped). Escape comes from
    [geq_tm_empty_irr]. The neutrals are kept, rather than any normal
    forms as at [Unit], because the eliminator is neutral only on a
    neutral scrutinee: its neutral law needs them and compares nothing
    else. *)
Definition EmptyRel (G : gctx) (Γ : ctx) (l : lvl) : tm -> tm -> Prop :=
  fun t t' => exists ν ν',
    [ G ; Γ ⊢g t ⤳* ν : tyEmpty l @ l ] /\ [ G ; Γ ⊢g t' ⤳* ν' : tyEmpty l @ l ] /\
    [ G ; Γ ⊢ ν ~ ν : tyEmpty l @ l ] /\ [ G ; Γ ⊢ ν' ~ ν' : tyEmpty l @ l ].

(** ** Binary sums (M12_DESIGN.md, M12b)

    As [Id]'s: the summands' relations [RA], [RB] are kept at [Γ] (not in
    every weakening). Terms reduce to related weak-head normal forms: two
    [inl]s with related payloads, two [inr]s, or two related neutrals.
    Nothing else is related: [+] has no η. The injections' annotations are
    recorded against the sum type's, as [refl]'s are against [Id]'s, since
    [case]'s β reads them before injectivity of [+] is available. *)
Inductive SumNf (G : gctx) (Γ : ctx) (l l' : lvl) (A B : ty) (RA RB : tm -> tm -> Prop)
  : tm -> tm -> Prop :=
| sumnf_inl k1 k2 k1' k2' C D C' D' a a' :
    lequiv (gL G) k1 l -> lequiv (gL G) k2 l' -> lequiv (gL G) k1' l -> lequiv (gL G) k2' l' ->
    [ G ; Γ ⊢ A ≈ C @ l ] -> [ G ; Γ ⊢ A ≈ C' @ l ] -> [ G ; Γ ⊢ B ≈ D @ l' ] -> [ G ; Γ ⊢ B ≈ D' @ l' ] ->
    RA a a' -> SumNf G Γ l l' A B RA RB (tmInl k1 k2 C D a) (tmInl k1' k2' C' D' a')
| sumnf_inr k1 k2 k1' k2' C D C' D' b b' :
    lequiv (gL G) k1 l -> lequiv (gL G) k2 l' -> lequiv (gL G) k1' l -> lequiv (gL G) k2' l' ->
    [ G ; Γ ⊢ A ≈ C @ l ] -> [ G ; Γ ⊢ A ≈ C' @ l ] -> [ G ; Γ ⊢ B ≈ D @ l' ] -> [ G ; Γ ⊢ B ≈ D' @ l' ] ->
    RB b b' -> SumNf G Γ l l' A B RA RB (tmInr k1 k2 C D b) (tmInr k1' k2' C' D' b')
| sumnf_ne ν ν' : [ G ; Γ ⊢ ν ~ ν' : tySum l l' A B @ lmax l l' ] -> SumNf G Γ l l' A B RA RB ν ν'.

Definition SumRel (G : gctx) (Γ : ctx) (l l' : lvl) (A B : ty) (RA RB : tm -> tm -> Prop)
  : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tySum l l' A B @ lmax l l' ] /\ [ G ; Γ ⊢g t' ⤳* w' : tySum l l' A B @ lmax l l' ] /\
    [ G ; Γ ⊢ w ≈ w' : tySum l l' A B @ lmax l l' ] /\ SumNf G Γ l l' A B RA RB w w'.

(** ** Propositional truncation (M16_DESIGN.md, M16a)

    The probe's clause ([probes/SquashProbe.v]): a whnf at [∥A∥] is good
    alone when it is a [squash] whose payload is related to itself by the
    carrier's relation, or a neutral related to itself (as at [Empty]).
    Two terms are related when each is good: [SqRel] is a product of two
    unary predicates, and nothing about one side is compared with the
    other. The payload's self-relation is what the eliminator's β needs. *)
Inductive SqNf (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (RA : tm -> tm -> Prop) : tm -> Prop :=
| sqnf_sq k C a :
    lequiv (gL G) k l -> [ G ; Γ ⊢ A ≈ C @ l ] -> RA a a -> SqNf G Γ l A RA (tmSq k C a)
| sqnf_ne ν : [ G ; Γ ⊢ ν ~ ν : tySq l A @ l ] -> SqNf G Γ l A RA ν.

Definition SqU (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (RA : tm -> tm -> Prop) (t : tm) : Prop :=
  exists w, [ G ; Γ ⊢g t ⤳* w : tySq l A @ l ] /\ SqNf G Γ l A RA w.

Definition SqRel (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (RA : tm -> tm -> Prop) : tm -> tm -> Prop :=
  fun t t' => SqU G Γ l A RA t /\ SqU G Γ l A RA t'.

(** Two terms reducing to whnfs related generically: the first clauses of
    [PiRel], without the Kripke one. *)
Definition WhRel (G : gctx) (Γ : ctx) (T : ty) (l : lvl) (t t' : tm) : Prop :=
  exists w w', [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ [ G ; Γ ⊢g t' ⤳* w' : T @ l ] /\
    whnf w /\ whnf w' /\ [ G ; Γ ⊢ w ≈ w' : T @ l ].

(** ** Well-founded trees (M13_DESIGN.md, M13a)

    MX §5's [NfEqW]: an inductive family whose recursive premise sits under
    the Kripke quantifier, so the context, the shape and position types and
    the shape and position relations are all indices. A [sup] pair is
    related when its shapes are related in every weakening and, in every
    weakening and at related positions, the children's applications (for
    every choice of equivalent annotations, as [PiRel]'s) are related at
    [W] there, with the data composed with the weakening. The shapes'
    relation is Kripke as [SigRel]'s first projections, so no identity
    weakening is needed; the children's premise takes any proof of the
    shapes' relation, so the definition needs no weakening of [domR].
    The children's functions reduce, in every weakening, to whnfs related
    generically (the first clauses of [PiRel]), so that they are related
    as functions where [elimW]'s step takes them.
    Neutrals are related generically. The [sup]s' annotations are recorded
    against the type's, as the injections' are. *)
Inductive WRel : forall (G : gctx) (Γ : ctx) (l1 l2 : lvl) (A B : ty)
    (domR : DomRel G Γ) (codR : CodRel G Γ domR), tm -> tm -> Prop :=
| wrel G Γ l1 l2 A B domR codR t t' w w' :
    [ G ; Γ ⊢g t ⤳* w : tyW l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢g t' ⤳* w' : tyW l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢ w ≈ w' : tyW l1 l2 A B @ lmax l1 l2 ] ->
    WNf G Γ l1 l2 A B domR codR w w' -> WRel G Γ l1 l2 A B domR codR t t'
with WNf : forall (G : gctx) (Γ : ctx) (l1 l2 : lvl) (A B : ty)
    (domR : DomRel G Γ) (codR : CodRel G Γ domR), tm -> tm -> Prop :=
| wnf_sup G Γ l1 l2 A B domR codR k1 k2 k1' k2' C D C' D' a a' f f' :
    lequiv (gL G) k1 l1 -> lequiv (gL G) k2 l2 -> lequiv (gL G) k1' l1 -> lequiv (gL G) k2' l2 ->
    [ G ; Γ ⊢ A ≈ C @ l1 ] -> [ G ; Γ ⊢ A ≈ C' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ B ≈ D @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢ B ≈ D' @ l2 ] ->
    (forall ρ : kwk G Γ, domR ρ (ktm ρ a) (ktm ρ a')) ->
    (forall ρ : kwk G Γ, WhRel (kw_G ρ) (kw_Δ ρ)
       (tyPi l2 (lmax l1 l2) (ktyl ρ B)[lsingle (ktm ρ a)] (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩)
       (lmax l2 (lmax l1 l2)) (ktm ρ f) (ktm ρ f')) ->
    (forall (ρ : kwk G Γ) (ha : domR ρ (ktm ρ a) (ktm ρ a')) b b', codR ρ (ktm ρ a) (ktm ρ a') ha b b' ->
       forall la lb A1 B1 la' lb' A1' B1',
       lequiv (gL G) la l2 -> lequiv (gL G) lb (lmax l1 l2) ->
       lequiv (gL G) la' l2 -> lequiv (gL G) lb' (lmax l1 l2) ->
       [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle (ktm ρ a)] ≈ A1 @ l2 ] ->
       [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B)[lsingle (ktm ρ a)] @ l2
           ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ B1 @ lmax l1 l2 ] ->
       [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle (ktm ρ a)] ≈ A1' @ l2 ] ->
       [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B)[lsingle (ktm ρ a)] @ l2
           ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ B1' @ lmax l1 l2 ] ->
       WRel (kw_G ρ) (kw_Δ ρ) l1 l2 (kty ρ A) (ktyl ρ B)
         (fun ρ' => domR (kw_comp ρ ρ')) (fun ρ' x x' h => codR (kw_comp ρ ρ') x x' h)
         (app (ktm ρ f) la lb A1 B1 b) (app (ktm ρ f') la' lb' A1' B1' b')) ->
    WNf G Γ l1 l2 A B domR codR (tmSup k1 k2 C D a f) (tmSup k1' k2' C' D' a' f')
| wnf_ne G Γ l1 l2 A B domR codR ν ν' :
    [ G ; Γ ⊢ ν ~ ν' : tyW l1 l2 A B @ lmax l1 l2 ] -> WNf G Γ l1 l2 A B domR codR ν ν'.

Scheme WRel_mut := Induction for WRel Sort Prop
  with WNf_mut := Induction for WNf Sort Prop.

(** ** Finitary well-founded trees (M15_DESIGN.md, M15a)

    MX §12's [NfEqWf], with [W]'s shape relation and a finite spine of
    children in place of [W]'s child function. Three mutual families,
    indexed (as [WRel]) by the context, the level, the left side's shape
    type [A] and arity [N] (under the shape binder), and the shapes'
    relation:
    - [WfRel]: both sides reduce, at the left [Wf], to whnfs related
      generically and by [WfNf];
    - [WfNf]: two [sup_f]s whose annotations agree with the type's, whose
      shapes are related in every weakening and whose children are related
      in every weakening by the spine at the left arity [N[a/x]]; or two
      neutrals;
    - [VecSp k]: the term relation at [Vec(Wf; k)] spelled out, by cases
      on how the length reduces: [Unit]'s at [0]; at a successor [Σ]'s,
      its first projections by [WfRel] and its second by the spine at the
      predecessor (at the spine's own world, for every choice of
      equivalent annotations); at a neutral length [NeRel] at the neutral
      [Vec] type. Both sides are typed at the left [Vec], as both sides
      of [WRel] are at the left [W]. *)
Inductive WfRel : forall (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (N : tm)
    (domR : DomRel G Γ), tm -> tm -> Prop :=
| wfrel G Γ l A N domR t t' w w' :
    [ G ; Γ ⊢g t ⤳* w : tyWf l A N @ l ] -> [ G ; Γ ⊢g t' ⤳* w' : tyWf l A N @ l ] ->
    [ G ; Γ ⊢ w ≈ w' : tyWf l A N @ l ] ->
    WfNf G Γ l A N domR w w' -> WfRel G Γ l A N domR t t'
with WfNf : forall (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (N : tm)
    (domR : DomRel G Γ), tm -> tm -> Prop :=
| wfnf_sup G Γ l A N domR k k' C C' M M' a a' cs cs' :
    lequiv (gL G) k l -> lequiv (gL G) k' l ->
    [ G ; Γ ⊢ A ≈ C @ l ] -> [ G ; Γ ⊢ A ≈ C' @ l ] ->
    [ G ; Γ ,, A @ l ⊢ N ≈ M : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢ N ≈ M' : tyNat @ lzero ] ->
    (forall ρ : kwk G Γ, domR ρ (ktm ρ a) (ktm ρ a')) ->
    (forall ρ : kwk G Γ,
       VecSp (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => domR (kw_comp ρ ρ'))
         (ktml ρ N)[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')) ->
    WfNf G Γ l A N domR (tmSupf k C M a cs) (tmSupf k' C' M' a' cs')
| wfnf_ne G Γ l A N domR ν ν' :
    [ G ; Γ ⊢ ν ~ ν' : tyWf l A N @ l ] -> WfNf G Γ l A N domR ν ν'
with VecSp : forall (G : gctx) (Γ : ctx) (l : lvl) (A : ty) (N : tm)
    (domR : DomRel G Γ), tm -> tm -> tm -> Prop :=
| vsp_zero G Γ l A N domR k cs cs' :
    [ G ; Γ ⊢g k ⤳* zero : tyNat @ lzero ] ->
    UnitRel G Γ l cs cs' -> VecSp G Γ l A N domR k cs cs'
| vsp_succ G Γ l A N domR k m cs cs' w w' :
    [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
    [ G ; Γ ⊢g cs ⤳* w : tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ lmax l l ] ->
    [ G ; Γ ⊢g cs' ⤳* w' : tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ lmax l l ] ->
    whnf w -> whnf w' ->
    [ G ; Γ ⊢ w ≈ w' : tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩) @ lmax l l ] ->
    (forall la lb A1 B1 la' lb' A1' B1',
       lequiv (gL G) la l -> lequiv (gL G) lb l -> lequiv (gL G) la' l -> lequiv (gL G) lb' l ->
       [ G ; Γ ⊢ tyWf l A N ≈ A1 @ l ] ->
       [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1 @ l ] ->
       [ G ; Γ ⊢ tyWf l A N ≈ A1' @ l ] ->
       [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1' @ l ] ->
       WfRel G Γ l A N domR (tmFst la lb A1 B1 w) (tmFst la' lb' A1' B1' w')) ->
    (forall la lb A1 B1 la' lb' A1' B1',
       lequiv (gL G) la l -> lequiv (gL G) lb l -> lequiv (gL G) la' l -> lequiv (gL G) lb' l ->
       [ G ; Γ ⊢ tyWf l A N ≈ A1 @ l ] ->
       [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1 @ l ] ->
       [ G ; Γ ⊢ tyWf l A N ≈ A1' @ l ] ->
       [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ B1' @ l ] ->
       VecSp G Γ l A N domR m (tmSnd la lb A1 B1 w) (tmSnd la' lb' A1' B1' w')) ->
    VecSp G Γ l A N domR k cs cs'
| vsp_ne G Γ l A N domR k ν cs cs' :
    [ G ; Γ ⊢g k ⤳* ν : tyNat @ lzero ] -> [ G ; Γ ⊢ ν ~ ν : tyNat @ lzero ] ->
    NeRel G Γ (tyVec l (tyWf l A N) ν) (tyVec l (tyWf l A N) ν) l cs cs' ->
    VecSp G Γ l A N domR k cs cs'.

Scheme WfRel_mut := Induction for WfRel Sort Prop
  with WfNf_mut := Induction for WfNf Sort Prop
  with VecSp_mut := Induction for VecSp Sort Prop.
Combined Scheme WfRel_comb from WfRel_mut, WfNf_mut, VecSp_mut.

(** ** Indexed W-types (M17_DESIGN.md, M17b)

    [Wf]'s three families with the index an index of the families: each
    child sits at its own index. The families are indexed, besides [Wf]'s
    data, by the index type [X], the output index [Ot] (under the shape
    binder) and the child index [C] (under the shape and position
    binders), and by the index relation [idxR] (the relation at [X] in
    every world):
    - [IWfRel m]: both sides reduce, at the left [IWf(m)], to whnfs related
      generically and by [IWfNf m];
    - [IWfNf m]: two [sup_i]s whose annotations agree with the type's,
      whose shapes are related in every world, whose output index [Ot[a]]
      is related to [m] at [X] in every world (the constructor is at its
      result index, read through conversion), and whose children are
      related in every world by the spine at the family of child indices
      [C[a, i]]; or two neutrals;
    - [DVecISp c k]: the relation at [DVec(k; i. IWf(c))] spelled out, as
      [VecSp], for a family [c] of indices under the position binder: at a
      successor its first projections are related by [IWfRel] at the
      head's index [c[inl ⟨⟩]] and its second by the spine at the moved
      family [c[inr j]] ([posMv]).
    Unlike [Wf]'s, the agreement of the annotations ([IWfEq]) is a
    declarative equation: symmetry moves it into the other side's
    contexts, two binders deep for [C], and the generic laws convert only
    the last context entry. The projections' annotations are generic, as
    [Wf]'s: the spine of a [sup_i] comes from [Σ]'s relation, which
    relates the projections only at generic annotations. *)

(** The type family of the children at a family of child indices [c]
    (under the position binder). *)
Definition iwfFamT (l li : lvl) (X A : ty) (N Ot C c : tm) : ty :=
  tyIWf l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ c.
(** The head position of [Fin (S k)], and a family moved to the tail. *)
Definition posHd (k : tm) : tm := tmInl lzero lzero (tyUnit lzero) (tyFin k) (tmTriv lzero).
Definition posTl (k p : tm) : tm := tmInr lzero lzero (tyUnit lzero) (tyFin k) p.
Definition posMv (k c : tm) : tm := c⟨rlift ↑⟩[lsingle (posTl k⟨↑⟩ (var 0))].

Inductive IWfRel : forall (G : gctx) (Γ : ctx) (l li : lvl) (X A : ty) (N Ot C : tm)
    (idxR domR : DomRel G Γ), tm -> tm -> tm -> Prop :=
| iwfrel G Γ l li X A N Ot C idxR domR m t t' w w' :
    [ G ; Γ ⊢g t ⤳* w : tyIWf l li X A N Ot C m @ lmax l li ] ->
    [ G ; Γ ⊢g t' ⤳* w' : tyIWf l li X A N Ot C m @ lmax l li ] ->
    [ G ; Γ ⊢ w ≈ w' : tyIWf l li X A N Ot C m @ lmax l li ] ->
    IWfNf G Γ l li X A N Ot C idxR domR m w w' -> IWfRel G Γ l li X A N Ot C idxR domR m t t'
with IWfNf : forall (G : gctx) (Γ : ctx) (l li : lvl) (X A : ty) (N Ot C : tm)
    (idxR domR : DomRel G Γ), tm -> tm -> tm -> Prop :=
| iwfnf_sup G Γ l li X A N Ot C idxR domR m k ki k' ki' X1 A1 N1 O1 C1 X1' A1' N1' O1' C1' a a' cs cs' :
    IWfEq (G := G) (i := ge_layer) Γ l li k ki X X1 A A1 N N1 Ot O1 C C1 ->
    IWfEq (G := G) (i := ge_layer) Γ l li k' ki' X X1' A A1' N N1' Ot O1' C C1' ->
    (forall ρ : kwk G Γ, domR ρ (ktm ρ a) (ktm ρ a')) ->
    (forall ρ : kwk G Γ, idxR ρ (ktml ρ Ot)[lsingle (ktm ρ a)] (ktm ρ m)) ->
    (forall ρ : kwk G Γ,
       DVecISp (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C)
         (fun ρ' => idxR (kw_comp ρ ρ')) (fun ρ' => domR (kw_comp ρ ρ'))
         (ktmll ρ C)[llift (lsingle (ktm ρ a))] (ktml ρ N)[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')) ->
    IWfNf G Γ l li X A N Ot C idxR domR m (tmSupi k ki X1 A1 N1 O1 C1 a cs) (tmSupi k' ki' X1' A1' N1' O1' C1' a' cs')
| iwfnf_ne G Γ l li X A N Ot C idxR domR m ν ν' :
    [ G ; Γ ⊢ ν ~ ν' : tyIWf l li X A N Ot C m @ lmax l li ] -> IWfNf G Γ l li X A N Ot C idxR domR m ν ν'
with DVecISp : forall (G : gctx) (Γ : ctx) (l li : lvl) (X A : ty) (N Ot C : tm)
    (idxR domR : DomRel G Γ), tm -> tm -> tm -> tm -> Prop :=
| visp_zero G Γ l li X A N Ot C idxR domR c k cs cs' :
    [ G ; Γ ⊢g k ⤳* zero : tyNat @ lzero ] ->
    UnitRel G Γ (lmax l li) cs cs' -> DVecISp G Γ l li X A N Ot C idxR domR c k cs cs'
| visp_succ G Γ l li X A N Ot C idxR domR c k m cs cs' w w' :
    [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
    [ G ; Γ ⊢g cs ⤳* w : tySig (lmax l li) (lmax l li) (dvecHd m (iwfFamT l li X A N Ot C c))
                            (dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c)) @ lmax (lmax l li) (lmax l li) ] ->
    [ G ; Γ ⊢g cs' ⤳* w' : tySig (lmax l li) (lmax l li) (dvecHd m (iwfFamT l li X A N Ot C c))
                            (dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c)) @ lmax (lmax l li) (lmax l li) ] ->
    whnf w -> whnf w' ->
    [ G ; Γ ⊢ w ≈ w' : tySig (lmax l li) (lmax l li) (dvecHd m (iwfFamT l li X A N Ot C c))
                         (dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c)) @ lmax (lmax l li) (lmax l li) ] ->
    (forall la lb A2 B2 la' lb' A2' B2',
       lequiv (gL G) la (lmax l li) -> lequiv (gL G) lb (lmax l li) ->
       lequiv (gL G) la' (lmax l li) -> lequiv (gL G) lb' (lmax l li) ->
       [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ A2 @ lmax l li ] ->
       [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
           ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ B2 @ lmax l li ] ->
       [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ A2' @ lmax l li ] ->
       [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
           ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ B2' @ lmax l li ] ->
       IWfRel G Γ l li X A N Ot C idxR domR c[lsingle (posHd m)]
         (tmFst la lb A2 B2 w) (tmFst la' lb' A2' B2' w')) ->
    (forall la lb A2 B2 la' lb' A2' B2',
       lequiv (gL G) la (lmax l li) -> lequiv (gL G) lb (lmax l li) ->
       lequiv (gL G) la' (lmax l li) -> lequiv (gL G) lb' (lmax l li) ->
       [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ A2 @ lmax l li ] ->
       [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
           ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ B2 @ lmax l li ] ->
       [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ A2' @ lmax l li ] ->
       [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
           ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ B2' @ lmax l li ] ->
       DVecISp G Γ l li X A N Ot C idxR domR (posMv m c) m
         (tmSnd la lb A2 B2 w) (tmSnd la' lb' A2' B2' w')) ->
    DVecISp G Γ l li X A N Ot C idxR domR c k cs cs'
| visp_ne G Γ l li X A N Ot C idxR domR c k ν cs cs' :
    [ G ; Γ ⊢g k ⤳* ν : tyNat @ lzero ] -> [ G ; Γ ⊢ ν ~ ν : tyNat @ lzero ] ->
    NeRel G Γ (tyDVec (lmax l li) ν (iwfFamT l li X A N Ot C c)) (tyDVec (lmax l li) ν (iwfFamT l li X A N Ot C c))
      (lmax l li) cs cs' ->
    DVecISp G Γ l li X A N Ot C idxR domR c k cs cs'.

Scheme IWfRel_mut := Induction for IWfRel Sort Prop
  with IWfNf_mut := Induction for IWfNf Sort Prop
  with DVecISp_mut := Induction for DVecISp Sort Prop.
Combined Scheme IWfRel_comb from IWfRel_mut, IWfNf_mut, DVecISp_mut.

(** Related positions of [Fin k] and [Fin k']: the canonical ones, [posHd]
    and [posTl] at the lengths' predecessors, and neutrals. They are what
    the children's spine reaches, and what the child index premise of
    [LRiwf] quantifies over (the relation at [Fin] cannot occur there: it
    is the relation being defined). The neutrals are what makes the child
    indices generically equal under a position binder (at the variable),
    which the spine's generic annotations need at a neutral length. *)
Inductive PosRel (G : gctx) (Γ : ctx) : tm -> tm -> tm -> tm -> Prop :=
| pos_hd k k' m m' :
    [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g k' ⤳* succ m' : tyNat @ lzero ] ->
    NatRel G Γ m m' -> PosRel G Γ k k' (posHd m) (posHd m')
| pos_tl k k' m m' p p' :
    [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g k' ⤳* succ m' : tyNat @ lzero ] ->
    PosRel G Γ m m' p p' -> PosRel G Γ k k' (posTl m p) (posTl m' p')
| pos_ne k k' p p' :
    [ G ; Γ ⊢g k ≅ k' : tyNat @ lzero ] -> [ G ; Γ ⊢ p ~ p' : tyFin k @ lzero ] -> PosRel G Γ k k' p p'.

(** ** Indexed families with infinitary children (M19_DESIGN.md, M19b)

    [IWf]'s three families with [W]'s children premise per field. Besides
    [IWf]'s data and relations, the families are indexed by the domain
    family [D] (under the shape and position binders) and by the domains'
    relation [pdR]: [pdR ρ a a' p p'] is the relation at [D[a, p]] against
    the right type's [D'[a', p']], for related shapes and related positions
    ([PosRel]), in every world. It is indexed by both sides' shapes and
    positions and does not depend on proofs of their relations, as [M]'s
    [MPosRel], so that symmetry is a flip of its arguments.
    - [IWiRel m]: both sides reduce, at the left [IWi(m)], to whnfs related
      generically and by [IWiNf m];
    - [IWiNf m]: two [sup]s whose annotations agree with the type's
      ([IWiEq]), whose shapes are related in every world, whose output
      index [Ot[a]] is related to [m], and whose children are related in
      every world by the spine; or two neutrals;
    - [DVecWSp yR d c k]: the relation at [DVec(k; i. Π(y : d). IWi(c))],
      [DVecISp]'s with its head clause [W]'s children premise: the head
      reduces to a whnf related generically at the field's [Π] (where
      [elim_IWi]'s induction hypothesis takes it as a function), and its
      applications to arguments related by [yR] at the head position (for
      every choice of equivalent annotations, on the projection as
      [DVecISp]'s and on the application as [WNf]'s) are related by
      [IWiRel] at the child index [c[inl ⟨⟩, y]]. The tail is the spine
      at the moved families ([posMvT], [posMv2]) and the relation [yR] at
      the moved positions.
    In a [sup]'s spine [yR p] is [pdR] at the [sup]s' shapes and the left
    position, against some right position: the right type's positions are
    not data of the families (the right type is not), and [pdR] is empty
    off related positions ([LRiwi]'s premise), so the right position is
    one related to [p]. *)
Definition IPosDomRel (G : gctx) (Γ : ctx) := kwk G Γ -> tm -> tm -> tm -> tm -> tm -> tm -> Prop.

(** A field's codomain at a family of child indices [c] (under the
    position and domain binders), and its type at a domain family [d]
    (under the position binder): [iwiFam a] is [iwiFamT] at [D[a]] and
    [C[a]], syntactically. *)
Definition iwiFamCodT (l lp li : lvl) (X A : ty) (N : tm) (D : ty) (Ot C c : tm) : ty :=
  tyIWi l lp li X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
    Ot⟨rlift ↑⟩⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ c.
Definition iwiFamT (l lp li : lvl) (X A : ty) (N : tm) (D : ty) (Ot C : tm) (d : ty) (c : tm) : ty :=
  tyPi lp (iwiL l lp li) d (iwiFamCodT l lp li X A N D Ot C c).

Lemma iwiFam_T l lp li X A N D Ot C a :
  iwiFam l lp li X A N D Ot C a = iwiFamT l lp li X A N D Ot C D[llift (lsingle a)] C[llift (llift (lsingle a))].
Proof using . reflexivity. Qed.

(** A domain family, and a family of child indices (under the position and
    domain binders), moved to the tail. *)
Definition posMvT (k : tm) (d : ty) : ty := d⟨rlift ↑⟩[lsingle (posTl k⟨↑⟩ (var 0))].
Definition posMv2 (k c : tm) : tm := c⟨rlift (rlift ↑)⟩[llift (lsingle (posTl k⟨↑⟩ (var 0)))].

Inductive IWiRel : forall (G : gctx) (Γ : ctx) (l lp li : lvl) (X A : ty) (N : tm) (D : ty) (Ot C : tm)
    (idxR domR : DomRel G Γ) (pdR : IPosDomRel G Γ), tm -> tm -> tm -> Prop :=
| iwirel G Γ l lp li X A N D Ot C idxR domR pdR m t t' w w' :
    [ G ; Γ ⊢g t ⤳* w : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
    [ G ; Γ ⊢g t' ⤳* w' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
    [ G ; Γ ⊢ w ≈ w' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
    IWiNf G Γ l lp li X A N D Ot C idxR domR pdR m w w' -> IWiRel G Γ l lp li X A N D Ot C idxR domR pdR m t t'
with IWiNf : forall (G : gctx) (Γ : ctx) (l lp li : lvl) (X A : ty) (N : tm) (D : ty) (Ot C : tm)
    (idxR domR : DomRel G Γ) (pdR : IPosDomRel G Γ), tm -> tm -> tm -> Prop :=
| iwinf_sup G Γ l lp li X A N D Ot C idxR domR pdR m k kp ki k' kp' ki'
    X1 A1 N1 D1 O1 C1 X1' A1' N1' D1' O1' C1' a a' cs cs' :
    IWiEq (G := G) (i := ge_layer) Γ l lp li k kp ki X X1 A A1 N N1 D D1 Ot O1 C C1 ->
    IWiEq (G := G) (i := ge_layer) Γ l lp li k' kp' ki' X X1' A A1' N N1' D D1' Ot O1' C C1' ->
    (forall ρ : kwk G Γ, domR ρ (ktm ρ a) (ktm ρ a')) ->
    (forall ρ : kwk G Γ, idxR ρ (ktml ρ Ot)[lsingle (ktm ρ a)] (ktm ρ m)) ->
    (forall ρ : kwk G Γ,
       DVecWSp (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
         (fun ρ' => idxR (kw_comp ρ ρ')) (fun ρ' => domR (kw_comp ρ ρ')) (fun ρ' => pdR (kw_comp ρ ρ'))
         (fun p y y' => exists p', pdR ρ (ktm ρ a) (ktm ρ a') p p' y y')
         (ktyll ρ D)[llift (lsingle (ktm ρ a))] (ktmlll ρ C)[llift (llift (lsingle (ktm ρ a)))]
         (ktml ρ N)[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')) ->
    IWiNf G Γ l lp li X A N D Ot C idxR domR pdR m
      (tmSupii k kp ki X1 A1 N1 D1 O1 C1 a cs) (tmSupii k' kp' ki' X1' A1' N1' D1' O1' C1' a' cs')
| iwinf_ne G Γ l lp li X A N D Ot C idxR domR pdR m ν ν' :
    [ G ; Γ ⊢ ν ~ ν' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
    IWiNf G Γ l lp li X A N D Ot C idxR domR pdR m ν ν'
with DVecWSp : forall (G : gctx) (Γ : ctx) (l lp li : lvl) (X A : ty) (N : tm) (D : ty) (Ot C : tm)
    (idxR domR : DomRel G Γ) (pdR : IPosDomRel G Γ), (tm -> tm -> tm -> Prop) -> ty -> tm -> tm -> tm -> tm -> Prop :=
| wsp_zero G Γ l lp li X A N D Ot C idxR domR pdR yR d c k cs cs' :
    [ G ; Γ ⊢g k ⤳* zero : tyNat @ lzero ] ->
    UnitRel G Γ (iwiL l lp li) cs cs' -> DVecWSp G Γ l lp li X A N D Ot C idxR domR pdR yR d c k cs cs'
| wsp_succ G Γ l lp li X A N D Ot C idxR domR pdR yR d c k m cs cs' w w' :
    [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
    [ G ; Γ ⊢g cs ⤳* w : tySig (iwiL l lp li) (iwiL l lp li) (dvecHd m (iwiFamT l lp li X A N D Ot C d c))
          (dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c)) @ lmax (iwiL l lp li) (iwiL l lp li) ] ->
    [ G ; Γ ⊢g cs' ⤳* w' : tySig (iwiL l lp li) (iwiL l lp li) (dvecHd m (iwiFamT l lp li X A N D Ot C d c))
          (dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c)) @ lmax (iwiL l lp li) (iwiL l lp li) ] ->
    whnf w -> whnf w' ->
    [ G ; Γ ⊢ w ≈ w' : tySig (iwiL l lp li) (iwiL l lp li) (dvecHd m (iwiFamT l lp li X A N D Ot C d c))
          (dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c)) @ lmax (iwiL l lp li) (iwiL l lp li) ] ->
    (* the head, a function *)
    (forall la lb A2 B2 la' lb' A2' B2',
       lequiv (gL G) la (iwiL l lp li) -> lequiv (gL G) lb (iwiL l lp li) ->
       lequiv (gL G) la' (iwiL l lp li) -> lequiv (gL G) lb' (iwiL l lp li) ->
       [ G ; Γ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A2 @ iwiL l lp li ] ->
       [ G ; Γ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
           ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B2 @ iwiL l lp li ] ->
       [ G ; Γ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A2' @ iwiL l lp li ] ->
       [ G ; Γ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
           ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B2' @ iwiL l lp li ] ->
       WhRel G Γ (dvecHd m (iwiFamT l lp li X A N D Ot C d c)) (iwiL l lp li)
         (tmFst la lb A2 B2 w) (tmFst la' lb' A2' B2' w')) ->
    (* the head's applications to related arguments *)
    (forall la lb A2 B2 la' lb' A2' B2',
       lequiv (gL G) la (iwiL l lp li) -> lequiv (gL G) lb (iwiL l lp li) ->
       lequiv (gL G) la' (iwiL l lp li) -> lequiv (gL G) lb' (iwiL l lp li) ->
       [ G ; Γ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A2 @ iwiL l lp li ] ->
       [ G ; Γ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
           ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B2 @ iwiL l lp li ] ->
       [ G ; Γ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A2' @ iwiL l lp li ] ->
       [ G ; Γ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
           ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B2' @ iwiL l lp li ] ->
       forall y y', yR (posHd m) y y' ->
       forall la2 lb2 A3 B3 la2' lb2' A3' B3',
       lequiv (gL G) la2 lp -> lequiv (gL G) lb2 (iwiL l lp li) ->
       lequiv (gL G) la2' lp -> lequiv (gL G) lb2' (iwiL l lp li) ->
       [ G ; Γ ⊢ d[lsingle (posHd m)] ≈ A3 @ lp ] ->
       [ G ; Γ ,, d[lsingle (posHd m)] @ lp
           ⊢ (iwiFamCodT l lp li X A N D Ot C c)[llift (lsingle (posHd m))] ≈ B3 @ iwiL l lp li ] ->
       [ G ; Γ ⊢ d[lsingle (posHd m)] ≈ A3' @ lp ] ->
       [ G ; Γ ,, d[lsingle (posHd m)] @ lp
           ⊢ (iwiFamCodT l lp li X A N D Ot C c)[llift (lsingle (posHd m))] ≈ B3' @ iwiL l lp li ] ->
       IWiRel G Γ l lp li X A N D Ot C idxR domR pdR c[lsingle2 (posHd m) y]
         (app (tmFst la lb A2 B2 w) la2 lb2 A3 B3 y) (app (tmFst la' lb' A2' B2' w') la2' lb2' A3' B3' y')) ->
    (* the tail *)
    (forall la lb A2 B2 la' lb' A2' B2',
       lequiv (gL G) la (iwiL l lp li) -> lequiv (gL G) lb (iwiL l lp li) ->
       lequiv (gL G) la' (iwiL l lp li) -> lequiv (gL G) lb' (iwiL l lp li) ->
       [ G ; Γ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A2 @ iwiL l lp li ] ->
       [ G ; Γ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
           ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B2 @ iwiL l lp li ] ->
       [ G ; Γ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A2' @ iwiL l lp li ] ->
       [ G ; Γ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
           ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B2' @ iwiL l lp li ] ->
       DVecWSp G Γ l lp li X A N D Ot C idxR domR pdR (fun p => yR (posTl m p)) (posMvT m d) (posMv2 m c) m
         (tmSnd la lb A2 B2 w) (tmSnd la' lb' A2' B2' w')) ->
    DVecWSp G Γ l lp li X A N D Ot C idxR domR pdR yR d c k cs cs'
| wsp_ne G Γ l lp li X A N D Ot C idxR domR pdR yR d c k ν cs cs' :
    [ G ; Γ ⊢g k ⤳* ν : tyNat @ lzero ] -> [ G ; Γ ⊢ ν ~ ν : tyNat @ lzero ] ->
    NeRel G Γ (tyDVec (iwiL l lp li) ν (iwiFamT l lp li X A N D Ot C d c))
      (tyDVec (iwiL l lp li) ν (iwiFamT l lp li X A N D Ot C d c)) (iwiL l lp li) cs cs' ->
    DVecWSp G Γ l lp li X A N D Ot C idxR domR pdR yR d c k cs cs'.

Scheme IWiRel_mut := Induction for IWiRel Sort Prop
  with IWiNf_mut := Induction for IWiNf Sort Prop
  with DVecWSp_mut := Induction for DVecWSp Sort Prop.
Combined Scheme IWiRel_comb from IWiRel_mut, IWiNf_mut, DVecWSp_mut.

(** ** Heather's indexed [M] (M18_DESIGN.md, Q1 and M18b)

    The probe's ω-intersection ([probes/MRelProbe.v]) at the
    development's annotations: [MR := ∀ n, MRn n], [MRn] by recursion on
    the depth. At every depth both sides reduce to whnfs related
    generically ([MGen], [PiRel]'s first clauses: the observations alone
    would relate two [corec]s conversion separates). At depth [n + 1],
    for every choice of equivalent annotations on [out] ([MAnn]), the two
    [out]s are related by [Σ]'s relation at [out]'s type: their shapes by
    the shapes' relation at the index, their children's functions by
    [Π]'s relation over the positions' relation, at depth [n] at the child
    index. Using [SigRel] and [PiRel] themselves is what gives every
    observation its annotation variants, and makes [out]'s validity a
    matter of moving the depth inside them.

    The relation is two-sided, as [PiRel]: both signatures and both
    indices are arguments, and the shapes' and positions' relations are
    indexed by both sides' indices and shapes ([MShRel], [MPosRel]), so
    that symmetry is a flip of the arguments. The relations do not depend
    on proofs of the index's or shapes' relation (unlike [CodRel]): the
    validity's canonical relations ([LRrel]) do not. The index's
    relation is not an argument: only [LRm]'s premises use it. *)
Definition MShRel (G : gctx) (Γ : ctx) := kwk G Γ -> tm -> tm -> tm -> tm -> Prop.
Definition MPosRel (G : gctx) (Γ : ctx) := kwk G Γ -> tm -> tm -> tm -> tm -> tm -> tm -> Prop.

(** Annotations [σ1; j1] declaratively equal to a signature and index
    ([out]'s annotations are compared declaratively, [gne_tm_out]). *)
Definition MAnn (G : gctx) (Γ : ctx) (l l' li : lvl) (X A B : ty) (C j : tm)
    (k k' ki : lvl) (X1 A1 B1 : ty) (C1 j1 : tm) : Prop :=
  lequiv (gL G) k l /\ lequiv (gL G) k' l' /\ lequiv (gL G) ki li /\
  [ G ; Γ ⊢g X ≅ X1 @ li ] /\ [ G ; Γ ,, X @ li ⊢g A ≅ A1 @ l ] /\
  [ G ; Γ ,, X @ li ,, A @ l ⊢g B ≅ B1 @ l' ] /\
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g C ≅ C1 : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] /\
  [ G ; Γ ⊢g j ≅ j1 : X @ li ].

(** Both sides reduce to whnfs related generically at both types. *)
Definition MGen (G : gctx) (Γ : ctx) (l1 l2 li : lvl) (X A B : ty) (C : tm)
    (r1 r2 ri : lvl) (X' A' B' : ty) (C' : tm) (m m' t t' : tm) : Prop :=
  exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyM l1 l2 li X A B C m @ mlvl l1 l2 li ] /\
    [ G ; Γ ⊢g t' ⤳* w' : tyM r1 r2 ri X' A' B' C' m' @ mlvl l1 l2 li ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tyM l1 l2 li X A B C m @ mlvl l1 l2 li ] /\
    [ G ; Γ ⊢ w ≈ w' : tyM r1 r2 ri X' A' B' C' m' @ mlvl l1 l2 li ].

(** The relation's type, for [MObs]'s recursive argument. *)
Definition MRelTy : Type := forall (G : gctx) (Γ : ctx), lvl -> lvl -> lvl -> ty -> ty -> ty -> tm ->
  lvl -> lvl -> lvl -> ty -> ty -> ty -> tm -> MShRel G Γ -> MPosRel G Γ -> tm -> tm -> tm -> tm -> Prop.

(** [out]'s observations in one context, the children by [MRec]: for
    every choice of equivalent annotations on the two [out]s, [Σ]'s
    relation at [out]'s type. *)
Definition MObs (MRec : MRelTy) (G : gctx) (Γ : ctx) (l1 l2 li : lvl) (X A B : ty) (C : tm)
    (r1 r2 ri : lvl) (X' A' B' : ty) (C' : tm)
    (shR : MShRel G Γ) (posR : MPosRel G Γ) (m m' t t' : tm) : Prop :=
  forall k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1',
  MAnn G Γ l1 l2 li X A B C m k1 k2 ki X1 A1 B1 C1 j1 ->
  MAnn G Γ r1 r2 ri X' A' B' C' m' k1' k2' ki' X1' A1' B1' C1' j1' ->
  SigRel G Γ l1 (mlvl l1 l2 li) r1 (mlvl r1 r2 ri)
    A[lsingle m] (tyPi l2 (mlvl l1 l2 li) B[llift (lsingle m)] (mKidTy l1 l2 li X A B C m))
    A'[lsingle m'] (tyPi r2 (mlvl r1 r2 ri) B'[llift (lsingle m')] (mKidTy r1 r2 ri X' A' B' C' m'))
    (fun ρ => shR ρ (ktm ρ m) (ktm ρ m'))
    (fun ρ a a' _ =>
       PiRel (kw_G ρ) (kw_Δ ρ) l2 (mlvl l1 l2 li) r2 (mlvl r1 r2 ri)
         (ktyl ρ B[llift (lsingle m)])[lsingle a] (ktyll ρ (mKidTy l1 l2 li X A B C m))[llift (lsingle a)]
         (ktyl ρ B'[llift (lsingle m')])[lsingle a'] (ktyll ρ (mKidTy r1 r2 ri X' A' B' C' m'))[llift (lsingle a')]
         (fun ρ' => posR (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' a'))
         (fun ρ' p p' _ =>
            MRec (kw_G ρ') (kw_Δ ρ')
              l1 l2 li (kty (kw_comp ρ ρ') X) (ktyl (kw_comp ρ ρ') A) (ktyll (kw_comp ρ ρ') B)
              (ktmlll (kw_comp ρ ρ') C)
              r1 r2 ri (kty (kw_comp ρ ρ') X') (ktyl (kw_comp ρ ρ') A') (ktyll (kw_comp ρ ρ') B')
              (ktmlll (kw_comp ρ ρ') C')
              (fun ρ'' => shR (kw_comp (kw_comp ρ ρ') ρ''))
              (fun ρ'' => posR (kw_comp (kw_comp ρ ρ') ρ''))
              (ktmlll (kw_comp ρ ρ') C)[lsingle3 (ktm (kw_comp ρ ρ') m) (ktm ρ' a) p]
              (ktmlll (kw_comp ρ ρ') C')[lsingle3 (ktm (kw_comp ρ ρ') m') (ktm ρ' a') p']))
    (tmOut k1 k2 ki X1 A1 B1 C1 j1 t) (tmOut k1' k2' ki' X1' A1' B1' C1' j1' t').

(** The observations are made in every world, with the annotations in
    the world's context: a weakened tree's [out] may carry annotations
    that are no weakening, and moving [Σ]'s relation from one [out]'s
    annotations to another's at a neutral scrutinee would need the
    neutrals' reflection, which comes after weakening. *)
Fixpoint MRn (n : nat) (G : gctx) (Γ : ctx) (l1 l2 li : lvl) (X A B : ty) (C : tm)
    (r1 r2 ri : lvl) (X' A' B' : ty) (C' : tm)
    (shR : MShRel G Γ) (posR : MPosRel G Γ) (m m' t t' : tm) {struct n} : Prop :=
  MGen G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' m m' t t' /\
  match n with
  | 0 => True
  | S n =>
      forall ρ : kwk G Γ,
      MObs (MRn n) (kw_G ρ) (kw_Δ ρ) l1 l2 li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C)
        r1 r2 ri (kty ρ X') (ktyl ρ A') (ktyll ρ B') (ktmlll ρ C')
        (fun ρ' => shR (kw_comp ρ ρ')) (fun ρ' => posR (kw_comp ρ ρ'))
        (ktm ρ m) (ktm ρ m') (ktm ρ t) (ktm ρ t')
  end.

Definition MR (G : gctx) (Γ : ctx) (l1 l2 li : lvl) (X A B : ty) (C : tm)
    (r1 r2 ri : lvl) (X' A' B' : ty) (C' : tm)
    (shR : MShRel G Γ) (posR : MPosRel G Γ) (m m' : tm) : tm -> tm -> Prop :=
  fun t t' => forall n, MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t'.

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
Proof using . now destruct γ. Qed.
Lemma gdecl_gwa_ty γ Δ i l : gdecl_gwa γ (gdTy Δ i l) = gdTy Δ⟦γ⟧ i l.
Proof using . now destruct γ. Qed.

Lemma gwa_up'_shift (Γ : ctx) γ : Γ⟪S⟫⟦gwk_up' γ⟧ = Γ⟦γ⟧⟪S⟫.
Proof using .
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
    LR n rec G Γ T T' l R
| LRseq G Γ T T' l l1 l2 A A' a a' b b' R :
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tySEq l1 A a b @ l ] -> [ G ; Γ ⊢g T' ⤳* tySEq l2 A' a' b' @ l ] ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ⊢ a ≈ a' : A @ l1 ] -> [ G ; Γ ⊢ b ≈ b' : A @ l1 ] ->
    releq R (SEqRel G Γ (tySEq l1 A a b) l1) ->
    LR n rec G Γ T T' l R
| LRsempty G Γ T T' l l1 l2 R :
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tySEmpty l1 @ l ] -> [ G ; Γ ⊢g T' ⤳* tySEmpty l2 @ l ] ->
    releq R (SEmptyRel G Γ l1) ->
    LR n rec G Γ T T' l R
| LRid G Γ T T' l l1 l2 A A' a a' b b' RA R :
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tyId l1 A a b @ l ] -> [ G ; Γ ⊢g T' ⤳* tyId l2 A' a' b' @ l ] ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ⊢ a ≈ a' : A @ l1 ] -> [ G ; Γ ⊢ b ≈ b' : A @ l1 ] ->
    LR n rec G Γ A A' l1 RA -> RA a a' -> RA b b' ->
    (* the carrier's term relation is a PER (logrel-coq's [tyPER]): symmetry
       and transitivity at [Id] need it before they are proven *)
    (forall x y, RA x y -> RA y x) -> (forall x y z, RA x y -> RA y z -> RA x z) ->
    releq R (IdRel G Γ l1 A a b RA) ->
    LR n rec G Γ T T' l R
| LRempty G Γ T T' l l1 l2 R :
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tyEmpty l1 @ l ] -> [ G ; Γ ⊢g T' ⤳* tyEmpty l2 @ l ] ->
    releq R (EmptyRel G Γ l1) ->
    LR n rec G Γ T T' l R
| LRsum G Γ T T' l l1 l2 l3 l4 A A' B B' RA RB R :
    lequiv (gL G) l (lmax l1 l2) -> lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
    lwf (gL G) l1 -> lwf (gL G) l2 ->
    [ G ; Γ ⊢g T ⤳* tySum l1 l2 A B @ l ] -> [ G ; Γ ⊢g T' ⤳* tySum l3 l4 A' B' @ l ] ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢g B @ l2 ] -> [ G ; Γ ⊢ B ≈ B' @ l2 ] ->
    LR n rec G Γ A A' l1 RA -> LR n rec G Γ B B' l2 RB ->
    (* the summands' term relations are PERs, as [LRid]'s carrier's *)
    (forall x y, RA x y -> RA y x) -> (forall x y z, RA x y -> RA y z -> RA x z) ->
    (forall x y, RB x y -> RB y x) -> (forall x y z, RB x y -> RB y z -> RB x z) ->
    releq R (SumRel G Γ l1 l2 A B RA RB) ->
    LR n rec G Γ T T' l R
| LRw G Γ T T' l l1 l2 l3 l4 A B A' B'
    (domR : DomRel G Γ) (codR : CodRel G Γ domR) R :
    PolyFacts G Γ tyW T T' l l1 l2 l3 l4 A B A' B' ->
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A') l1 (domR ρ)) ->
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ B)[lsingle a] (ktyl ρ B')[lsingle a'] l2
           (codR ρ a a' ha)) ->
    releq R (WRel G Γ l1 l2 A B domR codR) ->
    LR n rec G Γ T T' l R
| LRwf G Γ T T' l l1 l2 A A' N N' (domR : DomRel G Γ) R :
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tyWf l1 A N @ l ] -> [ G ; Γ ⊢g T' ⤳* tyWf l2 A' N' @ l ] ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢g A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A' @ l1 ⊢g N' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ N ≈ N' : tyNat @ lzero ] ->
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A') l1 (domR ρ)) ->
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a']) ->
    releq R (WfRel G Γ l1 A N domR) ->
    LR n rec G Γ T T' l R
| LRsq G Γ T T' l l1 l2 A A' RA R :
    lequiv (gL G) l l1 -> lequiv (gL G) l2 l1 -> lwf (gL G) l1 ->
    [ G ; Γ ⊢g T ⤳* tySq l1 A @ l ] -> [ G ; Γ ⊢g T' ⤳* tySq l2 A' @ l ] ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    LR n rec G Γ A A' l1 RA ->
    (* the carrier's relation is a PER, as [LRsum]'s summands' *)
    (forall x y, RA x y -> RA y x) -> (forall x y z, RA x y -> RA y z -> RA x z) ->
    releq R (SqRel G Γ l1 A RA) ->
    LR n rec G Γ T T' l R
| LRiwf G Γ T T' l l1 li1 l2 li2 X X' A A' N N' Ot Ot' C C' m m' (idxR domR : DomRel G Γ) R :
    lequiv (gL G) l (lmax l1 li1) -> lequiv (gL G) l2 l1 -> lequiv (gL G) li2 li1 ->
    lwf (gL G) l1 -> lwf (gL G) li1 ->
    [ G ; Γ ⊢g T ⤳* tyIWf l1 li1 X A N Ot C m @ l ] -> [ G ; Γ ⊢g T' ⤳* tyIWf l2 li2 X' A' N' Ot' C' m' @ l ] ->
    [ G ; Γ ⊢g X @ li1 ] -> [ G ; Γ ⊢g X' @ li1 ] -> [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢g A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A' @ l1 ⊢g N' : tyNat @ lzero ] ->
    [ G ; Γ ,, A @ l1 ⊢g Ot : X⟨↑⟩ @ li1 ] -> [ G ; Γ ,, A' @ l1 ⊢g Ot' : X'⟨↑⟩ @ li1 ] ->
    [ G ; Γ ,, A @ l1 ,, tyFin N @ lzero ⊢g C : X⟨↑⟩⟨↑⟩ @ li1 ] ->
    [ G ; Γ ,, A' @ l1 ,, tyFin N' @ lzero ⊢g C' : X'⟨↑⟩⟨↑⟩ @ li1 ] ->
    [ G ; Γ ⊢g m : X @ li1 ] -> [ G ; Γ ⊢g m' : X' @ li1 ] ->
    [ G ; Γ ⊢ X ≈ X' @ li1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ N ≈ N' : tyNat @ lzero ] ->
    [ G ; Γ ,, A @ l1 ⊢ Ot ≈ Ot' : X⟨↑⟩ @ li1 ] ->
    [ G ; Γ ,, A @ l1 ,, tyFin N @ lzero ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩ @ li1 ] ->
    [ G ; Γ ⊢ m ≈ m' : X @ li1 ] ->
    (* the index type, in every world; its relation is a PER, as [LRid]'s
       carrier's (symmetry moves the output index along it) *)
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ X) (kty ρ X') li1 (idxR ρ)) ->
    (forall (ρ : kwk G Γ) x y, idxR ρ x y -> idxR ρ y x) ->
    (forall (ρ : kwk G Γ) x y z, idxR ρ x y -> idxR ρ y z -> idxR ρ x z) ->
    (* the shapes, the arity and the output and child indices at related shapes *)
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A') l1 (domR ρ)) ->
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a']) ->
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        idxR ρ (ktml ρ Ot)[lsingle a] (ktml ρ Ot')[lsingle a']) ->
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p',
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
        idxR ρ (ktmll ρ C)[lsingle2 a p] (ktmll ρ C')[lsingle2 a' p']) ->
    (* the index *)
    (forall ρ : kwk G Γ, idxR ρ (ktm ρ m) (ktm ρ m')) ->
    releq R (IWfRel G Γ l1 li1 X A N Ot C idxR domR m) ->
    LR n rec G Γ T T' l R
| LRm G Γ T T' l l1 l2 li r1 r2 ri X X' A A' B B' C C' m m'
    (idxR : DomRel G Γ) (shR : MShRel G Γ) (posR : MPosRel G Γ) R :
    lequiv (gL G) l (mlvl l1 l2 li) ->
    lequiv (gL G) r1 l1 -> lequiv (gL G) r2 l2 -> lequiv (gL G) ri li ->
    lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) li ->
    [ G ; Γ ⊢g T ⤳* tyM l1 l2 li X A B C m @ l ] -> [ G ; Γ ⊢g T' ⤳* tyM r1 r2 ri X' A' B' C' m' @ l ] ->
    [ G ; Γ ⊢g X @ li ] -> [ G ; Γ ⊢g X' @ li ] ->
    [ G ; Γ ,, X @ li ⊢g A @ l1 ] -> [ G ; Γ ,, X' @ li ⊢g A' @ l1 ] ->
    [ G ; Γ ,, X @ li ,, A @ l1 ⊢g B @ l2 ] -> [ G ; Γ ,, X' @ li ,, A' @ l1 ⊢g B' @ l2 ] ->
    [ G ; Γ ,, X @ li ,, A @ l1 ,, B @ l2 ⊢g C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ,, X' @ li ,, A' @ l1 ,, B' @ l2 ⊢g C' : X'⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ⊢g m : X @ li ] -> [ G ; Γ ⊢g m' : X' @ li ] ->
    [ G ; Γ ⊢ X ≈ X' @ li ] -> [ G ; Γ ,, X @ li ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, X @ li ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ,, X @ li ,, A @ l1 ,, B @ l2 ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ⊢ m ≈ m' : X @ li ] ->
    (* the index type, in every world *)
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ X) (kty ρ X') li (idxR ρ)) ->
    (* the shapes at related indices, the positions at related shapes, and
       the child index at related positions *)
    (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ A)[lsingle x] (ktyl ρ A')[lsingle x'] l1 (shR ρ x x')) ->
    (forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyll ρ B)[lsingle2 x a] (ktyll ρ B')[lsingle2 x' a'] l2
          (posR ρ x x' a a')) ->
    (forall (ρ : kwk G Γ) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' -> posR ρ x x' a a' p p' ->
        idxR ρ (ktmlll ρ C)[lsingle3 x a p] (ktmlll ρ C')[lsingle3 x' a' p']) ->
    (* the signature's families at related indices and shapes, generically
       equal under their remaining binders (generic equality is not closed
       under substitution, and the observations' annotations live there) *)
    (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
        [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A)[lsingle x] @ l1
            ⊢ (ktyll ρ B)[llift (lsingle x)] ≈ (ktyll ρ B')[llift (lsingle x')] @ l2 ]) ->
    (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
        [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A)[lsingle x] @ l1 ,, (ktyll ρ B)[llift (lsingle x)] @ l2
            ⊢ (ktmlll ρ C)[llift (llift (lsingle x))] ≈ (ktmlll ρ C')[llift (llift (lsingle x'))]
            : (kty ρ X)⟨↑⟩⟨↑⟩ @ li ]) ->
    (forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
        [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ B)[lsingle2 x a] @ l2
            ⊢ (ktmlll ρ C)[llift (lsingle2 x a)] ≈ (ktmlll ρ C')[llift (lsingle2 x' a')] : (kty ρ X)⟨↑⟩ @ li ]) ->
    (* the three relations are Kripke-monotone (a consequence of weakening,
       which the relation's metatheory proves only after irrelevance needs
       it at [MRn]'s later worlds) *)
    (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x', idxR ρ x x' ->
        idxR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x')) ->
    (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
        shR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a')) ->
    (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' ->
        posR ρ x x' a a' p p' ->
        posR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a') (ktm ρ' p) (ktm ρ' p')) ->
    (* the index *)
    (forall ρ : kwk G Γ, idxR ρ (ktm ρ m) (ktm ρ m')) ->
    releq R (MR G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m') ->
    LR n rec G Γ T T' l R
| LRiwi G Γ T T' l l1 lp1 li1 l2 lp2 li2 X X' A A' N N' D D' Ot Ot' C C' m m'
    (idxR domR : DomRel G Γ) (pdR : IPosDomRel G Γ) R :
    lequiv (gL G) l (iwiL l1 lp1 li1) ->
    lequiv (gL G) l2 l1 -> lequiv (gL G) lp2 lp1 -> lequiv (gL G) li2 li1 ->
    lwf (gL G) l1 -> lwf (gL G) lp1 -> lwf (gL G) li1 ->
    [ G ; Γ ⊢g T ⤳* tyIWi l1 lp1 li1 X A N D Ot C m @ l ] ->
    [ G ; Γ ⊢g T' ⤳* tyIWi l2 lp2 li2 X' A' N' D' Ot' C' m' @ l ] ->
    [ G ; Γ ⊢g X @ li1 ] -> [ G ; Γ ⊢g X' @ li1 ] -> [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢g A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A' @ l1 ⊢g N' : tyNat @ lzero ] ->
    [ G ; Γ ,, A @ l1 ,, tyFin N @ lzero ⊢g D @ lp1 ] -> [ G ; Γ ,, A' @ l1 ,, tyFin N' @ lzero ⊢g D' @ lp1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g Ot : X⟨↑⟩ @ li1 ] -> [ G ; Γ ,, A' @ l1 ⊢g Ot' : X'⟨↑⟩ @ li1 ] ->
    [ G ; Γ ,, A @ l1 ,, tyFin N @ lzero ,, D @ lp1 ⊢g C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li1 ] ->
    [ G ; Γ ,, A' @ l1 ,, tyFin N' @ lzero ,, D' @ lp1 ⊢g C' : X'⟨↑⟩⟨↑⟩⟨↑⟩ @ li1 ] ->
    [ G ; Γ ⊢g m : X @ li1 ] -> [ G ; Γ ⊢g m' : X' @ li1 ] ->
    [ G ; Γ ⊢ X ≈ X' @ li1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ N ≈ N' : tyNat @ lzero ] ->
    [ G ; Γ ,, A @ l1 ,, tyFin N @ lzero ⊢ D ≈ D' @ lp1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ Ot ≈ Ot' : X⟨↑⟩ @ li1 ] ->
    [ G ; Γ ,, A @ l1 ,, tyFin N @ lzero ,, D @ lp1 ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li1 ] ->
    [ G ; Γ ⊢ m ≈ m' : X @ li1 ] ->
    (* the index type, in every world, a PER (as [LRiwf]'s) *)
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ X) (kty ρ X') li1 (idxR ρ)) ->
    (forall (ρ : kwk G Γ) x y, idxR ρ x y -> idxR ρ y x) ->
    (forall (ρ : kwk G Γ) x y z, idxR ρ x y -> idxR ρ y z -> idxR ρ x z) ->
    (* the shapes, the arity and the output index at related shapes *)
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A') l1 (domR ρ)) ->
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a']) ->
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        idxR ρ (ktml ρ Ot)[lsingle a] (ktml ρ Ot')[lsingle a']) ->
    (* the domains at related shapes and positions, their relation empty
       off related positions, and the child index at related arguments *)
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p',
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyll ρ D)[lsingle2 a p] (ktyll ρ D')[lsingle2 a' p'] lp1 (pdR ρ a a' p p')) ->
    (forall (ρ : kwk G Γ) a a' p p' y y', pdR ρ a a' p p' y y' ->
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a'] p p') ->
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p' y y', pdR ρ a a' p p' y y' ->
        idxR ρ (ktmlll ρ C)[lsingle3 a p y] (ktmlll ρ C')[lsingle3 a' p' y']) ->
    (* the child index at related shapes and positions, generically equal
       under the domain's binder (generic equality is not closed under
       substitution, and the field types are compared there; as [LRm]'s) *)
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p',
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
        [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ D)[lsingle2 a p] @ lp1
            ⊢ (ktmlll ρ C)[llift (lsingle2 a p)] ≈ (ktmlll ρ C')[llift (lsingle2 a' p')] : (kty ρ X)⟨↑⟩ @ li1 ]) ->
    (* the index *)
    (forall ρ : kwk G Γ, idxR ρ (ktm ρ m) (ktm ρ m')) ->
    releq R (IWiRel G Γ l1 lp1 li1 X A N D Ot C idxR domR pdR m) ->
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
Proof using .
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
Arguments kw_G {E G Γ}. Arguments kw_Δ {E G Γ}. Arguments kw_gk {E G Γ}. Arguments kw_rk {E G Γ}.
Arguments kw_gcoh {E G Γ}. Arguments kw_rcoh {E G Γ}. Arguments kw_gokk {E G Γ}. Arguments kw_wfk {E G Γ}.
Arguments kw_ctx {E G Γ}.
