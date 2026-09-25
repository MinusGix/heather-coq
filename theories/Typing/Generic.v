(** * Generic equivalence (ch. 7 §"Generic Equivalence")

    The logical relation is parameterised by four relations (neutral types,
    types, neutral terms, terms) satisfying the laws below.  It is
    instantiated twice: with declarative equality (for normalisation and
    injectivity) and, in a later milestone, with algorithmic convertibility
    (for decidability).  Typing itself stays declarative, as in the paper.

    An instance fixes one computing layer [ge_layer] ([compt]: D or M). *)
From DeLaM.Typing Require Export TypedRed Presupposition StaticCode.

Class GenericEq := {
  ge_layer : layer ;
  ge_compt : compt ge_layer ;

  gne_ty : gctx -> ctx -> ty -> ty -> lvl -> Prop ;
  geq_ty : gctx -> ctx -> ty -> ty -> lvl -> Prop ;
  gne_tm : gctx -> ctx -> tm -> tm -> ty -> lvl -> Prop ;
  geq_tm : gctx -> ctx -> tm -> tm -> ty -> lvl -> Prop
}.

Notation "[ G ; Γ ⊢ V ~ V' @ l ]" := (gne_ty G Γ V V' l)
  (at level 0, G, Γ, V, V', l at level 50).
Notation "[ G ; Γ ⊢ T ≈ T' @ l ]" := (geq_ty G Γ T T' l)
  (at level 0, G, Γ, T, T', l at level 50).
Notation "[ G ; Γ ⊢ t ~ t' : T @ l ]" := (gne_tm G Γ t t' T l)
  (at level 0, G, Γ, t, t', T, l at level 50).
Notation "[ G ; Γ ⊢ t ≈ t' : T @ l ]" := (geq_tm G Γ t t' T l)
  (at level 0, G, Γ, t, t', T, l at level 50).

(** Declarative judgments at the instance's layer. *)
Notation "[ G ; Γ ⊢g ]" := (wf_ctx G ge_layer Γ) (at level 0, G, Γ at level 50).
Notation "[ G ; Γ ⊢g T @ l ]" := (wf_ty G ge_layer Γ T l)
  (at level 0, G, Γ, T, l at level 50).
Notation "[ G ; Γ ⊢g t : T @ l ]" := (wf_tm G ge_layer Γ t T l)
  (at level 0, G, Γ, t, T, l at level 50).
Notation "[ G ; Γ ⊢g T ≅ T' @ l ]" := (eq_ty G ge_layer Γ T T' l)
  (at level 0, G, Γ, T, T', l at level 50).
Notation "[ G ; Γ ⊢g t ≅ t' : T @ l ]" := (eq_tm G ge_layer Γ t t' T l)
  (at level 0, G, Γ, t, t', T, l at level 50).
Notation "[ G ; Γ ⊢g T ⤳* W @ l ]" := (tyred G ge_layer Γ T W l)
  (at level 0, G, Γ, T, W, l at level 50).
Notation "[ G ; Γ ⊢g t ⤳* w : T @ l ]" := (tmred G ge_layer Γ t w T l)
  (at level 0, G, Γ, t, w, T, l at level 50).

(** Relations induced on local contexts and local substitutions (07:68).
    Substitutions carry what the declarative rules for global variables
    need: tails, deep normality, typing of both sides, and pairwise
    relatedness of the entries. *)
Inductive geq_ctx `{GenericEq} (G : gctx) : ctx -> ctx -> Prop :=
| gqc_nil : [ ⊢ G ] -> geq_ctx G cnil cnil
| gqc_var g : [ ⊢ G ] -> gctx_var G g -> geq_ctx G (cvar g) (cvar g)
| gqc_ext Γ Γ' A A' l l' : geq_ctx G Γ Γ' -> [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    lequiv (gL G) l l' -> geq_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').

Record geq_lsub `{GenericEq} G Γ d d' Δ : Prop := {
  gls_ctx : [ G ; Γ ⊢g ] ;
  gls_tail_l : lsub_tail d Δ Γ ;
  gls_dnf_l : dnfl d ;
  gls_tail_r : lsub_tail d' Δ Γ ;
  gls_dnf_r : dnfl d' ;
  gls_wf_l : forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢g llk d n : A[d] @ k ] ;
  gls_wf_r : forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢g llk d' n : A[d'] @ k ] ;
  gls_eq : forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ llk d n ≈ llk d' n : A[d] @ k ]
}.

Class GenericEqLaws `{GenericEq} := {
  (** Subsumption *)
  gne_ty_geq {G Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Γ ⊢ V ≈ V' @ l ] ;
  geq_ty_sound {G Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Γ ⊢g T ≅ T' @ l ] ;
  gne_tm_geq {G Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Γ ⊢ t ≈ t' : T @ l ] ;
  geq_tm_sound {G Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢g t ≅ t' : T @ l ] ;

  (** Neutral relations relate neutral forms *)
  gne_ty_whne_l {G Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> whne_ty V ;
  gne_ty_whne_r {G Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> whne_ty V' ;
  gne_tm_whne_l {G Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] -> whne t ;
  gne_tm_whne_r {G Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] -> whne t' ;

  (** PER *)
  gne_ty_sym {G Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Γ ⊢ V' ~ V @ l ] ;
  gne_ty_trans {G Γ V V' V'' l} :
    [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Γ ⊢ V' ~ V'' @ l ] -> [ G ; Γ ⊢ V ~ V'' @ l ] ;
  geq_ty_sym {G Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Γ ⊢ T' ≈ T @ l ] ;
  geq_ty_trans {G Γ T T' T'' l} :
    [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Γ ⊢ T' ≈ T'' @ l ] -> [ G ; Γ ⊢ T ≈ T'' @ l ] ;
  gne_tm_sym {G Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Γ ⊢ t' ~ t : T @ l ] ;
  gne_tm_trans {G Γ t t' t'' T l} :
    [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Γ ⊢ t' ~ t'' : T @ l ] -> [ G ; Γ ⊢ t ~ t'' : T @ l ] ;
  geq_tm_sym {G Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢ t' ≈ t : T @ l ] ;
  geq_tm_trans {G Γ t t' t'' T l} :
    [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢ t' ≈ t'' : T @ l ] -> [ G ; Γ ⊢ t ≈ t'' : T @ l ] ;

  (** Level equivalence of syntax (M3_DESIGN.md E6'): [≡ₗ]-related
      syntax, each side related to itself, is related *)
  gne_ty_leq {G Γ V V' l} :
    [ G ; Γ ⊢ V ~ V @ l ] -> [ G ; Γ ⊢ V' ~ V' @ l ] -> ty_leq V V' -> [ G ; Γ ⊢ V ~ V' @ l ] ;
  geq_ty_leq {G Γ T T' l} :
    [ G ; Γ ⊢ T ≈ T @ l ] -> [ G ; Γ ⊢ T' ≈ T' @ l ] -> ty_leq T T' -> [ G ; Γ ⊢ T ≈ T' @ l ] ;
  gne_tm_leq {G Γ t t' T l} :
    [ G ; Γ ⊢ t ~ t : T @ l ] -> [ G ; Γ ⊢ t' ~ t' : T @ l ] -> tm_leq t t' -> [ G ; Γ ⊢ t ~ t' : T @ l ] ;
  geq_tm_leq {G Γ t t' T l} :
    [ G ; Γ ⊢ t ≈ t : T @ l ] -> [ G ; Γ ⊢ t' ≈ t' : T @ l ] -> tm_leq t t' -> [ G ; Γ ⊢ t ≈ t' : T @ l ] ;

  (** Type conversion (and level conversion) *)
  gne_tm_conv {G Γ t t' T T' l} :
    [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Γ ⊢g T ≅ T' @ l ] -> [ G ; Γ ⊢ t ~ t' : T' @ l ] ;
  geq_tm_conv {G Γ t t' T T' l} :
    [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢g T ≅ T' @ l ] -> [ G ; Γ ⊢ t ≈ t' : T' @ l ] ;
  gne_ty_lconv {G Γ V V' l l'} :
    [ G ; Γ ⊢ V ~ V' @ l' ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢ V ~ V' @ l ] ;
  geq_ty_lconv {G Γ T T' l l'} :
    [ G ; Γ ⊢ T ≈ T' @ l' ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢ T ≈ T' @ l ] ;
  gne_tm_lconv {G Γ t t' T l l'} :
    [ G ; Γ ⊢ t ~ t' : T @ l' ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢ t ~ t' : T @ l ] ;
  geq_tm_lconv {G Γ t t' T l l'} :
    [ G ; Γ ⊢ t ≈ t' : T @ l' ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢ t ≈ t' : T @ l ] ;

  (** Weakening *)
  gne_ty_wk {G Γ Δ r V V' l} : wkr r Δ Γ -> [ G ; Δ ⊢g ] ->
    [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Δ ⊢ V⟨r⟩ ~ V'⟨r⟩ @ l ] ;
  geq_ty_wk {G Γ Δ r T T' l} : wkr r Δ Γ -> [ G ; Δ ⊢g ] ->
    [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Δ ⊢ T⟨r⟩ ≈ T'⟨r⟩ @ l ] ;
  gne_tm_wk {G Γ Δ r t t' T l} : wkr r Δ Γ -> [ G ; Δ ⊢g ] ->
    [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Δ ⊢ t⟨r⟩ ~ t'⟨r⟩ : T⟨r⟩ @ l ] ;
  geq_tm_wk {G Γ Δ r t t' T l} : wkr r Δ Γ -> [ G ; Δ ⊢g ] ->
    [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Δ ⊢ t⟨r⟩ ≈ t'⟨r⟩ : T⟨r⟩ @ l ] ;

  (** Context conversion of the last entry (also changing its level
      annotation to an equivalent one) *)
  gne_ty_ctxconv {G Γ A A' la la' V V' l} :
    [ G ; Γ ⊢g A ≅ A' @ la ] -> lequiv (gL G) la la' -> [ G ; Γ ,, A' @ la' ⊢g ] ->
    [ G ; Γ ,, A @ la ⊢ V ~ V' @ l ] -> [ G ; Γ ,, A' @ la' ⊢ V ~ V' @ l ] ;
  geq_ty_ctxconv {G Γ A A' la la' T T' l} :
    [ G ; Γ ⊢g A ≅ A' @ la ] -> lequiv (gL G) la la' -> [ G ; Γ ,, A' @ la' ⊢g ] ->
    [ G ; Γ ,, A @ la ⊢ T ≈ T' @ l ] -> [ G ; Γ ,, A' @ la' ⊢ T ≈ T' @ l ] ;
  gne_tm_ctxconv {G Γ A A' la la' t t' T l} :
    [ G ; Γ ⊢g A ≅ A' @ la ] -> lequiv (gL G) la la' -> [ G ; Γ ,, A' @ la' ⊢g ] ->
    [ G ; Γ ,, A @ la ⊢ t ~ t' : T @ l ] -> [ G ; Γ ,, A' @ la' ⊢ t ~ t' : T @ l ] ;
  geq_tm_ctxconv {G Γ A A' la la' t t' T l} :
    [ G ; Γ ⊢g A ≅ A' @ la ] -> lequiv (gL G) la la' -> [ G ; Γ ,, A' @ la' ⊢g ] ->
    [ G ; Γ ,, A @ la ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ,, A' @ la' ⊢ t ≈ t' : T @ l ] ;

  (** Weak head closure *)
  geq_ty_exp {G Γ T T' W W' l} :
    [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g T' ⤳* W' @ l ] ->
    [ G ; Γ ⊢ W ≈ W' @ l ] -> [ G ; Γ ⊢ T ≈ T' @ l ] ;
  geq_tm_exp {G Γ t t' w w' T l} :
    [ G ; Γ ⊢g t ⤳* w : T @ l ] -> [ G ; Γ ⊢g t' ⤳* w' : T @ l ] ->
    [ G ; Γ ⊢ w ≈ w' : T @ l ] -> [ G ; Γ ⊢ t ≈ t' : T @ l ] ;

  (** Type constructors *)
  geq_ty_nat {G Γ} : [ G ; Γ ⊢g ] -> [ G ; Γ ⊢ tyNat ≈ tyNat @ lzero ] ;
  geq_ty_U {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢ tyU l ≈ tyU l' @ lsuc l ] ;
  geq_ty_pi {G Γ l1 l2 l3 l4 A A' B B'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ tyPi l1 l2 A B ≈ tyPi l3 l4 A' B' @ lmax l1 l2 ] ;
  geq_tm_code_nat {G Γ} : [ G ; Γ ⊢g ] ->
    [ G ; Γ ⊢ tmNat ≈ tmNat : tyU lzero @ lsuc lzero ] ;
  geq_tm_code_U {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢ tmU l ≈ tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ] ;
  geq_tm_code_pi {G Γ l1 l2 l3 l4 s s' t t'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢ s ≈ s' : tyU l1 @ lsuc l1 ] ->
    [ G ; Γ ,, tyEl l1 s @ l1 ⊢ t ≈ t' : tyU l2 @ lsuc l2 ] ->
    [ G ; Γ ⊢ tmPi l1 l2 s t ≈ tmPi l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] ;

  (** Neutral types *)
  gne_ty_El {G Γ l l' ν ν'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢ ν ~ ν' : tyU l @ lsuc l ] -> [ G ; Γ ⊢ tyEl l ν ~ tyEl l' ν' @ l ] ;

  (** Term congruences *)
  geq_tm_zero {G Γ} : [ G ; Γ ⊢g ] -> [ G ; Γ ⊢ zero ≈ zero : tyNat @ lzero ] ;
  geq_tm_succ {G Γ t t'} : [ G ; Γ ⊢ t ≈ t' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ succ t ≈ succ t' : tyNat @ lzero ] ;
  geq_tm_funext {G Γ l l' A B t t'} : lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
    [ G ; Γ ⊢g t : tyPi l l' A B @ lmax l l' ] -> [ G ; Γ ⊢g t' : tyPi l l' A B @ lmax l l' ] ->
    [ G ; Γ ,, A @ l ⊢ app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)
                     ≈ app t'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0) : B @ l' ] ->
    [ G ; Γ ⊢ t ≈ t' : tyPi l l' A B @ lmax l l' ] ;

  (** Neutral congruences *)
  gne_tm_var {G Γ n T l} : [ G ; Γ ⊢g var n : T @ l ] -> [ G ; Γ ⊢ var n ~ var n : T @ l ] ;
  gne_tm_natrec {G Γ l l' M M' s s' z z' ν ν'} : lequiv (gL G) l l' ->
    [ G ; Γ ,, tyNat @ lzero ⊢g M @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ⊢ M ≈ M' @ l ] ->
    [ G ; Γ ⊢ s ≈ s' : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢ z ≈ z' : M[lsucc] @ l ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ natrec l M s z ν ~ natrec l' M' s' z' ν' : M[lsingle ν] @ l ] ;
  gne_tm_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyPi l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢ s ≈ s' : A @ l1 ] ->
    [ G ; Γ ⊢ app ν l1 l2 A B s ~ app ν' l3 l4 A' B' s' : B[lsingle s] @ l2 ] ;

  (** Global weakening ([γ : G' ≤ G]) *)
  gne_ty_gwk {G G' γ Γ V V' l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
    [ G ; Γ ⊢ V ~ V' @ l ] -> [ G' ; Γ⟪γ⟫ ⊢ V⟪γ⟫ ~ V'⟪γ⟫ @ l ] ;
  geq_ty_gwk {G G' γ Γ T T' l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
    [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G' ; Γ⟪γ⟫ ⊢ T⟪γ⟫ ≈ T'⟪γ⟫ @ l ] ;
  gne_tm_gwk {G G' γ Γ t t' T l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
    [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G' ; Γ⟪γ⟫ ⊢ t⟪γ⟫ ~ t'⟪γ⟫ : T⟪γ⟫ @ l ] ;
  geq_tm_gwk {G G' γ Γ t t' T l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
    [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G' ; Γ⟪γ⟫ ⊢ t⟪γ⟫ ≈ t'⟪γ⟫ : T⟪γ⟫ @ l ] ;

  (** Universe substitution ([φ : L' ⇒ gL G], M3_DESIGN.md E14) *)
  gne_ty_us {G Γ V V' l L' φ} : usub_ok φ L' (gL G) -> [ G ; Γ ⊢ V ~ V' @ l ] ->
    [ G_us G L' φ ; ucsubst Γ φ ⊢ usubst_ty V φ ~ usubst_ty V' φ @ lvsubst l φ ] ;
  geq_ty_us {G Γ T T' l L' φ} : usub_ok φ L' (gL G) -> [ G ; Γ ⊢ T ≈ T' @ l ] ->
    [ G_us G L' φ ; ucsubst Γ φ ⊢ usubst_ty T φ ≈ usubst_ty T' φ @ lvsubst l φ ] ;
  gne_tm_us {G Γ t t' T l L' φ} : usub_ok φ L' (gL G) -> [ G ; Γ ⊢ t ~ t' : T @ l ] ->
    [ G_us G L' φ ; ucsubst Γ φ ⊢ usubst_tm t φ ~ usubst_tm t' φ : usubst_ty T φ @ lvsubst l φ ] ;
  geq_tm_us {G Γ t t' T l L' φ} : usub_ok φ L' (gL G) -> [ G ; Γ ⊢ t ≈ t' : T @ l ] ->
    [ G_us G L' φ ; ucsubst Γ φ ⊢ usubst_tm t φ ≈ usubst_tm t' φ : usubst_ty T φ @ lvsubst l φ ] ;

  (** Neutral global variables (07:268, 07:290) *)
  gne_ty_gvar {G Γ U Δ i' l d d'} : in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' ge_layer ->
    geq_lsub G Γ d d' Δ -> [ G ; Γ ⊢ tyGvar U d ~ tyGvar U d' @ l ] ;
  gne_tm_gvar {G Γ u Δ i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' ge_layer ->
    geq_lsub G Γ d d' Δ -> [ G ; Γ ⊢ gvar u d ~ gvar u d' : T[d] @ l ]
}.

Lemma geq_ctx_sound `{GenericEqLaws} {G Γ Γ'} : geq_ctx G Γ Γ' -> [ G ⊢[ ge_layer ] Γ ≅ Γ' ].
Proof.
  induction 1; [now apply eqc_nil | now apply eqc_var |].
  apply eqc_ext; auto using geq_ty_sound.
Qed.

(** The recursors' common premises for the neutral recursion laws: levels,
    index contexts, both sides' motives and branches (typed, and related by
    the generic equivalence at M). *)
Record ElimPrem (EP EM : GenericEq) G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' : Prop := {
  ep_l1 : lequiv (gL G) l1 l1' ;
  ep_l2 : lequiv (gL G) l2 l2' ;
  ep_l : lequiv (gL G) l l' ;
  ep_Δ : @geq_ctx EP G Δ Δ' ;
  ep_MT : [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ;
  ep_MTeq : @geq_ty EM (recGT G) (recΓT Γ) MT MT' (lvren l1 (ush 1)) ;
  ep_MT' : [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ;
  ep_Mt : [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ;
  ep_Mteq : @geq_ty EM (recGt G) (recΓt Γ) Mt Mt' (lvren l2 (ush 1)) ;
  ep_Mt' : [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ;
  ep_brctx : forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ] ;
  ep_brctx' : forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ] ;
  ep_br : forall k, k < 13 -> @geq_tm EM (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                                (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt)) (brLv k l1 l2) ;
  ep_br' : forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                                bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]
}.

(** * Laws at layer M (07:299–369)

    They relate an instance [EM] at M with an instance [EP] at P: the
    contexts and types of contextual types are related at P.  [box]
    relates code that is declaratively equal at C, which by the Static
    Code Lemma is syntactic equality up to level equivalence. *)
Class GenericEqM (EP EM : GenericEq) := {
  gm_layer_P : @ge_layer EP = lD ;
  gm_layer_M : @ge_layer EM = lM ;

  geq_ty_CTyp {G Γ Δ Δ' l l'} : [ G ; Γ ⊢[ lM ] ] -> @geq_ctx EP G Δ Δ' -> lequiv (gL G) l l' ->
    @geq_ty EM G Γ (tyCTyp Δ l) (tyCTyp Δ' l') lzero ;
  geq_ty_CTrm {G Γ Δ Δ' T T' l l'} : [ G ; Γ ⊢[ lM ] ] -> @geq_ctx EP G Δ Δ' ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> @geq_ty EP G Δ T T' l -> lequiv (gL G) l l' ->
    @geq_ty EM G Γ (tyCTrm Δ T l) (tyCTrm Δ' T' l') lzero ;

  (* boxed code is compared up to level equivalence (05:1055, E11) *)
  geq_tm_boxT {G Γ Δ T T' l} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Δ ⊢[ lC ] T' @ l ] -> [ G ; Δ ⊢[ lC ] T ≅ T' @ l ] -> ty_leq T T' ->
    @geq_tm EM G Γ (boxT T) (boxT T') (tyCTyp Δ l) lzero ;
  geq_tm_boxt {G Γ Δ t t' T l} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] -> [ G ; Δ ⊢[ lC ] t' : T @ l ] ->
    [ G ; Δ ⊢[ lC ] t ≅ t' : T @ l ] -> tm_leq t t' ->
    @geq_tm EM G Γ (boxt t) (boxt t') (tyCTrm Δ T l) lzero ;

  gne_tm_letboxT {G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> @geq_ctx EP G Δ Δ' ->
    [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M @ l1 ] ->
    @geq_ty EM G (Γ ,, tyCTyp Δ l2 @ lzero) M M' l1 ->
    [ G ; Γ ,, tyCTyp Δ' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
    @geq_tm EM (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2
      (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) l1 ->
    [ gext G (gdTy Δ' lC l4) ; Γ⟪S⟫ ⊢[ lM ] t2
        : M'⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l3 ] ->
    @gne_tm EM G Γ ν ν' (tyCTyp Δ l2) lzero ->
    @gne_tm EM G Γ (letboxT l1 l2 Δ M t1 ν) (letboxT l3 l4 Δ' M' t2 ν') (M[lsingle ν]) l1 ;
  gne_tm_letboxt {G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> @geq_ctx EP G Δ Δ' ->
    [ G ; Δ ⊢[ lD ] T @ l2 ] -> @geq_ty EP G Δ T T' l2 ->
    [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M @ l1 ] ->
    @geq_ty EM G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' l1 ->
    [ G ; Γ ,, tyCTrm Δ' T' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
    @geq_tm EM (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t2
      (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) l1 ->
    [ gext G (gdTm Δ' lC T' l4) ; Γ⟪S⟫ ⊢[ lM ] t2
        : M'⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l3 ] ->
    @gne_tm EM G Γ ν ν' (tyCTrm Δ T l2) lzero ->
    @gne_tm EM G Γ (letboxt l1 l2 Δ T M t1 ν) (letboxt l3 l4 Δ' T' M' t2 ν') (M[lsingle ν]) l1 ;

  (* neutral recursion on code (07:371–400): the scrutinee is neutral or
     a boxed global variable. The motives and branches are related by the
     generic equivalence at M; the instances' equation is declarative
     (M3_DESIGN.md E10) *)
  gne_tm_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ν ν'} :
    [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ ν ≅ motT (wrapMT MT') l' Δ' ν' @ l1 ] ->
    ElimPrem EP EM G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ->
    @gne_tm EM G Γ ν ν' (tyCTyp Δ l) lzero ->
    @gne_tm EM G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν')
      (motT (wrapMT MT) l Δ ν) l1 ;
  (* the boxed variables are compared up to level equivalence (E11) *)
  gne_tm_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' U d d'} :
    [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ (boxT (tyGvar U d))
                  ≅ motT (wrapMT MT') l' Δ' (boxT (tyGvar U d')) @ l1 ] ->
    ElimPrem EP EM G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ->
    [ G ; Γ ⊢[ lM ] boxT (tyGvar U d) ≅ boxT (tyGvar U d') : tyCTyp Δ l @ lzero ] ->
    @gne_tm EM G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d)))
      (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' (boxT (tyGvar U d')))
      (motT (wrapMT MT) l Δ (boxT (tyGvar U d))) l1 ;
  gne_tm_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' ν ν'} :
    [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T ν ≅ mott (wrapMt Mt') l' Δ' T' ν' @ l2 ] ->
    ElimPrem EP EM G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ' ⊢[ lD ] T' @ l' ] -> @geq_ty EP G Δ T T' l ->
    @gne_tm EM G Γ ν ν' (tyCTrm Δ T l) lzero ->
    @gne_tm EM G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' ν')
      (mott (wrapMt Mt) l Δ T ν) l2 ;
  gne_tm_elimt_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' u d d'} :
    [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T (boxt (gvar u d))
                  ≅ mott (wrapMt Mt') l' Δ' T' (boxt (gvar u d')) @ l2 ] ->
    ElimPrem EP EM G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ' ⊢[ lD ] T' @ l' ] -> @geq_ty EP G Δ T T' l ->
    [ G ; Γ ⊢[ lM ] boxt (gvar u d) ≅ boxt (gvar u d') : tyCTrm Δ T l @ lzero ] ->
    @gne_tm EM G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt (gvar u d)))
      (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' (boxt (gvar u d')))
      (mott (wrapMt Mt) l Δ T (boxt (gvar u d))) l2
}.
