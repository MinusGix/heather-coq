(** * Generic equivalence (ch. 7 §"Generic Equivalence")

    The logical relation is parameterised by four relations (neutral types,
    types, neutral terms, terms) satisfying the laws below.  It is
    instantiated twice: with declarative equality (for normalisation and
    injectivity) and, in a later milestone, with algorithmic convertibility
    (for decidability).  Typing itself stays declarative, as in the paper.

    An instance fixes one computing layer [ge_layer] ([compt]: D or M). *)
From DeLaM.Typing Require Export TypedRed.

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
  (** and of the second-to-last entry, for [IWf]'s child family (M17b) *)
  geq_tm_ctxconv2 {G Γ A A' la la' B lb t t' T l} :
    [ G ; Γ ⊢g A ≅ A' @ la ] -> lequiv (gL G) la la' -> [ G ; Γ ,, A' @ la' ,, B @ lb ⊢g ] ->
    [ G ; Γ ,, A @ la ,, B @ lb ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ,, A' @ la' ,, B @ lb ⊢ t ≈ t' : T @ l ] ;

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
    geq_lsub G Γ d d' Δ -> [ G ; Γ ⊢ gvar u d ~ gvar u d' : T[d] @ l ] ;

  (** Dependent pairs (M8_DESIGN.md I5): congruences, extensionality by
      the projections (η), neutral projections *)
  geq_ty_sig {G Γ l1 l2 l3 l4 A A' B B'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ tySig l1 l2 A B ≈ tySig l3 l4 A' B' @ lmax l1 l2 ] ;
  geq_tm_code_sig {G Γ l1 l2 l3 l4 s s' t t'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢ s ≈ s' : tyU l1 @ lsuc l1 ] ->
    [ G ; Γ ,, tyEl l1 s @ l1 ⊢ t ≈ t' : tyU l2 @ lsuc l2 ] ->
    [ G ; Γ ⊢ tmSig l1 l2 s t ≈ tmSig l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] ;
  geq_tm_sig_ext {G Γ l l' A B p p'} : lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
    [ G ; Γ ⊢g p : tySig l l' A B @ lmax l l' ] -> [ G ; Γ ⊢g p' : tySig l l' A B @ lmax l l' ] ->
    [ G ; Γ ⊢ tmFst l l' A B p ≈ tmFst l l' A B p' : A @ l ] ->
    [ G ; Γ ⊢ tmSnd l l' A B p ≈ tmSnd l l' A B p' : B[lsingle (tmFst l l' A B p)] @ l' ] ->
    [ G ; Γ ⊢ p ≈ p' : tySig l l' A B @ lmax l l' ] ;
  gne_tm_fst {G Γ l1 l2 l3 l4 A A' B B' ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ ν ~ ν' : tySig l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢ tmFst l1 l2 A B ν ~ tmFst l3 l4 A' B' ν' : A @ l1 ] ;
  gne_tm_snd {G Γ l1 l2 l3 l4 A A' B B' ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ ν ~ ν' : tySig l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢ tmSnd l1 l2 A B ν ~ tmSnd l3 l4 A' B' ν' : B[lsingle (tmFst l1 l2 A B ν)] @ l2 ] ;

  (** The unit type (M8_DESIGN.md K4): congruences, and η as proof
      irrelevance, which is where escape at [Unit] comes from *)
  geq_ty_unit {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢ tyUnit l ≈ tyUnit l' @ l ] ;
  geq_tm_code_unit {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢ tmUnit l ≈ tmUnit l' : tyU l @ lsuc l ] ;
  geq_tm_unit_eta {G Γ l t t'} : lwf (gL G) l ->
    [ G ; Γ ⊢g t : tyUnit l @ l ] -> [ G ; Γ ⊢g t' : tyUnit l @ l ] ->
    [ G ; Γ ⊢ t ≈ t' : tyUnit l @ l ] ;

  (** Strict equality (M10_DESIGN.md, M10a): congruences, proof irrelevance
      at [sEq] and [sEmpty] (where escape comes from, as at [Unit]), and the
      neutral eliminator of [sEmpty], whose scrutinees are only required to
      be neutral: they are never compared *)
  geq_ty_seq {G Γ l l' A A' a a' b b'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    [ G ; Γ ⊢ a ≈ a' : A @ l ] -> [ G ; Γ ⊢ b ≈ b' : A @ l ] ->
    [ G ; Γ ⊢ tySEq l A a b ≈ tySEq l' A' a' b' @ l ] ;
  geq_ty_sempty {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢ tySEmpty l ≈ tySEmpty l' @ l ] ;
  geq_tm_seq_irr {G Γ l A a b p p'} : lwf (gL G) l ->
    [ G ; Γ ⊢g p : tySEq l A a b @ l ] -> [ G ; Γ ⊢g p' : tySEq l A a b @ l ] ->
    [ G ; Γ ⊢ p ≈ p' : tySEq l A a b @ l ] ;
  geq_tm_sempty_irr {G Γ l p p'} : lwf (gL G) l ->
    [ G ; Γ ⊢g p : tySEmpty l @ l ] -> [ G ; Γ ⊢g p' : tySEmpty l @ l ] ->
    [ G ; Γ ⊢ p ≈ p' : tySEmpty l @ l ] ;
  gne_tm_elimSEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g M @ l2 ] -> [ G ; Γ ⊢ M ≈ M' @ l2 ] ->
    [ G ; Γ ⊢ ν ~ ν : tySEmpty l1 @ l1 ] -> [ G ; Γ ⊢ ν' ~ ν' : tySEmpty l1 @ l1 ] ->
    [ G ; Γ ⊢ elimSEmpty l1 l2 M ν ~ elimSEmpty l3 l4 M' ν' : M @ l2 ] ;

  (** The identity type (M11_DESIGN.md, M11a): congruences of [Id] and
      [refl] ([refl]'s compares the carrier and the point), and the neutral
      [J], whose motive lives under the [Id] premise's type *)
  geq_ty_id {G Γ l l' A A' a a' b b'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    [ G ; Γ ⊢ a ≈ a' : A @ l ] -> [ G ; Γ ⊢ b ≈ b' : A @ l ] ->
    [ G ; Γ ⊢ tyId l A a b ≈ tyId l' A' a' b' @ l ] ;
  geq_tm_idrefl {G Γ l l' A A' a a'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] -> [ G ; Γ ⊢ a ≈ a' : A @ l ] ->
    [ G ; Γ ⊢ tmRefl l A a ≈ tmRefl l' A' a' : tyId l A a a @ l ] ;
  gne_tm_J {G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢ a ≈ a' : A @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ] ->
    [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢g M @ l2 ] ->
    [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢ M ≈ M' @ l2 ] ->
    [ G ; Γ ⊢ c ≈ c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ] ->
    [ G ; Γ ⊢ u ≈ u' : A @ l1 ] -> [ G ; Γ ⊢ ν ~ ν' : tyId l1 A a u @ l1 ] ->
    [ G ; Γ ⊢ tmJ l1 l2 A a M c u ν ~ tmJ l3 l4 A' a' M' c' u' ν' : M[lsingle2 u ν] @ l2 ] ;
  (** its code (M11b) *)
  geq_tm_code_id {G Γ l l' s s' t t' u u'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ⊢ s ≈ s' : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢ t ≈ t' : tyEl l s @ l ] -> [ G ; Γ ⊢ u ≈ u' : tyEl l s @ l ] ->
    [ G ; Γ ⊢ tmId l s t u ≈ tmId l' s' t' u' : tyU l @ lsuc l ] ;
  (** strict equality's codes (M10c) *)
  geq_tm_code_seq {G Γ l l' s s' t t' u u'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ⊢ s ≈ s' : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢ t ≈ t' : tyEl l s @ l ] -> [ G ; Γ ⊢ u ≈ u' : tyEl l s @ l ] ->
    [ G ; Γ ⊢ tmSEq l s t u ≈ tmSEq l' s' t' u' : tyU l @ lsuc l ] ;
  geq_tm_code_sempty {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢ tmSEmpty l ≈ tmSEmpty l' : tyU l @ lsuc l ] ;
  (** the empty type (M12a): its congruence, proof irrelevance (as at
      [sEmpty]), and its eliminator is neutral on neutral scrutinees, which,
      as [sEmpty]'s, are never compared *)
  geq_ty_empty {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢ tyEmpty l ≈ tyEmpty l' @ l ] ;
  geq_tm_empty_irr {G Γ l t t'} : lwf (gL G) l ->
    [ G ; Γ ⊢g t : tyEmpty l @ l ] -> [ G ; Γ ⊢g t' : tyEmpty l @ l ] ->
    [ G ; Γ ⊢ t ≈ t' : tyEmpty l @ l ] ;
  gne_tm_elimEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ,, tyEmpty l2 @ l2 ⊢g M @ l1 ] -> [ G ; Γ ,, tyEmpty l2 @ l2 ⊢ M ≈ M' @ l1 ] ->
    [ G ; Γ ⊢ ν ~ ν : tyEmpty l2 @ l2 ] -> [ G ; Γ ⊢ ν' ~ ν' : tyEmpty l2 @ l2 ] ->
    [ G ; Γ ⊢ elimEmpty l1 l2 M ν ~ elimEmpty l3 l4 M' ν' : M[lsingle ν] @ l1 ] ;
  (** binary sums (M12b): the congruences of [+] and the injections, and
      [case] is neutral on a neutral scrutinee *)
  geq_ty_sum {G Γ l1 l2 l3 l4 A A' B B'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ tySum l1 l2 A B ≈ tySum l3 l4 A' B' @ lmax l1 l2 ] ;
  geq_tm_inl {G Γ l1 l2 l3 l4 A A' B B' a a'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢ B ≈ B' @ l2 ] -> [ G ; Γ ⊢ a ≈ a' : A @ l1 ] ->
    [ G ; Γ ⊢ tmInl l1 l2 A B a ≈ tmInl l3 l4 A' B' a' : tySum l1 l2 A B @ lmax l1 l2 ] ;
  geq_tm_inr {G Γ l1 l2 l3 l4 A A' B B' b b'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢ B ≈ B' @ l2 ] -> [ G ; Γ ⊢ b ≈ b' : B @ l2 ] ->
    [ G ; Γ ⊢ tmInr l1 l2 A B b ≈ tmInr l3 l4 A' B' b' : tySum l1 l2 A B @ lmax l1 l2 ] ;
  gne_tm_case {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' ν ν'} :
    lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ⊢g B @ l2 ] -> [ G ; Γ ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢g M @ l3 ] ->
    [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢ M ≈ M' @ l3 ] ->
    [ G ; Γ ,, A @ l1 ⊢ c1 ≈ c1' : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
    [ G ; Γ ,, B @ l2 ⊢ c2 ≈ c2' : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
    [ G ; Γ ⊢ ν ~ ν' : tySum l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢ tmCase l1 l2 l3 A B M c1 c2 ν ~ tmCase l4 l5 l6 A' B' M' c1' c2' ν' : M[lsingle ν] @ l3 ] ;
  (** the codes of [Empty] and [+] (M12c) *)
  geq_tm_code_empty {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢ tmEmpty l ≈ tmEmpty l' : tyU l @ lsuc l ] ;
  geq_tm_code_sum {G Γ l1 l2 l3 l4 s s' t t'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢ s ≈ s' : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢ t ≈ t' : tyU l2 @ lsuc l2 ] ->
    [ G ; Γ ⊢ tmSum l1 l2 s t ≈ tmSum l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] ;
  (** well-founded trees (M13a): the congruences of [W] and [sup], and
      [elim_W] is neutral on a neutral scrutinee *)
  geq_ty_W {G Γ l1 l2 l3 l4 A A' B B'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ tyW l1 l2 A B ≈ tyW l3 l4 A' B' @ lmax l1 l2 ] ;
  geq_tm_sup {G Γ l1 l2 l3 l4 A A' B B' a a' f f'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ⊢ a ≈ a' : A @ l1 ] ->
    [ G ; Γ ⊢ f ≈ f' : tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩ @ lmax l2 (lmax l1 l2) ] ->
    [ G ; Γ ⊢ tmSup l1 l2 A B a f ≈ tmSup l3 l4 A' B' a' f' : tyW l1 l2 A B @ lmax l1 l2 ] ;
  gne_tm_elimW {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c c' ν ν'} :
    lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g B @ l2 ] -> [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
    [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢g M @ l3 ] ->
    [ G ; Γ ,, tyW l1 l2 A B @ lmax l1 l2 ⊢ M ≈ M' @ l3 ] ->
    [ G ; Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
        ⊢ c ≈ c' : wstepty l1 l2 A B M @ l3 ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyW l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢ tmElimW l1 l2 l3 A B M c ν ~ tmElimW l4 l5 l6 A' B' M' c' ν' : M[lsingle ν] @ l3 ] ;
  (** the code of [W] (M13b) *)
  geq_tm_code_W {G Γ l1 l2 l3 l4 s s' t t'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢ s ≈ s' : tyU l1 @ lsuc l1 ] ->
    [ G ; Γ ,, tyEl l1 s @ l1 ⊢ t ≈ t' : tyU l2 @ lsuc l2 ] ->
    [ G ; Γ ⊢ tmW l1 l2 s t ≈ tmW l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ] ;
  (** length-indexed tuples and finite indices at neutral lengths (M14a, MX
      §10.2): the first neutral-type law with a type premise *)
  gne_ty_vec {G Γ l l' A A' ν ν'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyNat @ lzero ] -> [ G ; Γ ⊢ tyVec l A ν ~ tyVec l' A' ν' @ l ] ;
  gne_ty_fin {G Γ ν ν'} :
    [ G ; Γ ⊢ ν ~ ν' : tyNat @ lzero ] -> [ G ; Γ ⊢ tyFin ν ~ tyFin ν' @ lzero ] ;
  (** the codes of [Vec] and [Fin] (M14b) *)
  geq_tm_code_vec {G Γ l l' s s' n n'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢ s ≈ s' : tyU l @ lsuc l ] -> [ G ; Γ ⊢ n ≈ n' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ tmVec l s n ≈ tmVec l' s' n' : tyU l @ lsuc l ] ;
  geq_tm_code_fin {G Γ n n'} :
    [ G ; Γ ⊢ n ≈ n' : tyNat @ lzero ] -> [ G ; Γ ⊢ tmFin n ≈ tmFin n' : tyU lzero @ lsuc lzero ] ;
  (** finitary well-founded trees (M15a): the congruences of [Wf] and
      [sup_f], and [elim_Wf] is neutral on a neutral scrutinee *)
  geq_ty_wf {G Γ l l' A A' N N'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    [ G ; Γ ,, A @ l ⊢ N ≈ N' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ tyWf l A N ≈ tyWf l' A' N' @ l ] ;
  geq_tm_supf {G Γ l l' A A' N N' a a' cs cs'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢ N ≈ N' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ a ≈ a' : A @ l ] ->
    [ G ; Γ ⊢ cs ≈ cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ] ->
    [ G ; Γ ⊢ tmSupf l A N a cs ≈ tmSupf l' A' N' a' cs' : tyWf l A N @ l ] ;
  gne_tm_elimWf {G Γ l1 l2 l3 l4 A A' N N' M M' c c' ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l1 ⊢ N ≈ N' : tyNat @ lzero ] ->
    [ G ; Γ ,, tyWf l1 A N @ l1 ⊢g M @ l2 ] ->
    [ G ; Γ ,, tyWf l1 A N @ l1 ⊢ M ≈ M' @ l2 ] ->
    [ G ; Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
        ⊢ c ≈ c' : wfstepty l1 A N M @ l2 ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyWf l1 A N @ l1 ] ->
    [ G ; Γ ⊢ tmElimWf l1 l2 A N M c ν ~ tmElimWf l3 l4 A' N' M' c' ν' : M[lsingle ν] @ l2 ] ;
  (** the code of [Wf] (M15b) *)
  geq_tm_code_wf {G Γ l l' s s' n n'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ⊢ s ≈ s' : tyU l @ lsuc l ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢ n ≈ n' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ tmWf l s n ≈ tmWf l' s' n' : tyU l @ lsuc l ] ;
  (** propositional truncation (M16a): the congruence of [∥·∥], proof
      irrelevance (where escape comes from, as at [Empty]), and [ind_∥∥] is
      neutral on neutral scrutinees, which, as [Empty]'s, are each related
      to themselves and never to each other *)
  geq_ty_sq {G Γ l l' A A'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    [ G ; Γ ⊢ tySq l A ≈ tySq l' A' @ l ] ;
  geq_tm_sq_irr {G Γ l A t t'} : lwf (gL G) l ->
    [ G ; Γ ⊢g t : tySq l A @ l ] -> [ G ; Γ ⊢g t' : tySq l A @ l ] ->
    [ G ; Γ ⊢ t ≈ t' : tySq l A @ l ] ;
  gne_tm_elimSq {G Γ l1 l2 l3 l4 A A' M M' c c' ν ν'} :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] ->
    [ G ; Γ ,, tySq l1 A @ l1 ⊢g M @ l2 ] -> [ G ; Γ ,, tySq l1 A @ l1 ⊢ M ≈ M' @ l2 ] ->
    [ G ; Γ ,, A @ l1 ⊢ c ≈ c' : tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))] @ l2 ] ->
    [ G ; Γ ⊢ ν ~ ν : tySq l1 A @ l1 ] -> [ G ; Γ ⊢ ν' ~ ν' : tySq l1 A @ l1 ] ->
    [ G ; Γ ⊢ tmElimSq l1 l2 A M c ν ~ tmElimSq l3 l4 A' M' c' ν' : tySq l2 M[lsingle ν] @ l2 ] ;
  (** the code of [∥·∥] (M16b) *)
  geq_tm_code_sq {G Γ l l' s s'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢ s ≈ s' : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢ tmSqCode l s ≈ tmSqCode l' s' : tyU l @ lsuc l ] ;
  (** dependent tuples at a neutral length (M17a): [Vec]'s law, with the
      family under the index *)
  gne_ty_dvec {G Γ l l' ν ν' F F'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢ ν ~ ν' : tyNat @ lzero ] ->
    [ G ; Γ ,, tyFin ν @ lzero ⊢g F @ l ] -> [ G ; Γ ,, tyFin ν @ lzero ⊢ F ≈ F' @ l ] ->
    [ G ; Γ ⊢ tyDVec l ν F ~ tyDVec l' ν' F' @ l ] ;
  (** indexed W-types (M17b): the congruences of [IWf] and [sup_i], and
      [elim_IWf] is neutral on a neutral scrutinee. The induction
      hypothesis's types are compared as [eqtm_elimIWf] states them
      (M17_DESIGN.md); the motive's and the children's types are well formed
      from the signature's typings *)
  geq_ty_iwf {G Γ l li k ki X X' A A' N N' Ot Ot' C C' m m'} :
    lequiv (gL G) l k -> lequiv (gL G) li ki ->
    [ G ; Γ ⊢g X @ li ] -> [ G ; Γ ⊢ X ≈ X' @ li ] ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢ N ≈ N' : tyNat @ lzero ] ->
    [ G ; Γ ,, A @ l ⊢g Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢ Ot ≈ Ot' : X⟨↑⟩ @ li ] ->
    [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g C : X⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ⊢ m ≈ m' : X @ li ] ->
    [ G ; Γ ⊢ tyIWf l li X A N Ot C m ≈ tyIWf k ki X' A' N' Ot' C' m' @ lmax l li ] ;
  (* the annotations of [sup_i] agree declaratively, as the relation's
     [IWfEq] states them: the algorithm compares only the shapes and the
     children ([actmnf_supf]'s convention) *)
  geq_tm_supi {G Γ l li k ki X X' A A' N N' Ot Ot' C C' a a' cs cs'} :
    lequiv (gL G) l k -> lequiv (gL G) li ki ->
    [ G ; Γ ⊢g X @ li ] -> [ G ; Γ ⊢g X ≅ X' @ li ] ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢g A ≅ A' @ l ] ->
    [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢g N ≅ N' : tyNat @ lzero ] ->
    [ G ; Γ ,, A @ l ⊢g Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢g Ot ≅ Ot' : X⟨↑⟩ @ li ] ->
    [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g C : X⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g C ≅ C' : X⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ⊢ a ≈ a' : A @ l ] ->
    [ G ; Γ ⊢ cs ≈ cs' : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
    [ G ; Γ ⊢ tmSupi l li X A N Ot C a cs ≈ tmSupi k ki X' A' N' Ot' C' a' cs'
        : tyIWf l li X A N Ot C Ot[lsingle a] @ lmax l li ] ;
  gne_tm_elimIWf {G Γ l li l' k ki k' X X' A A' N N' Ot Ot' C C' M M' c c' m m' ν ν'} :
    lequiv (gL G) l k -> lequiv (gL G) li ki -> lequiv (gL G) l' k' ->
    [ G ; Γ ⊢g X @ li ] -> [ G ; Γ ⊢ X ≈ X' @ li ] ->
    [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
    [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢ N ≈ N' : tyNat @ lzero ] ->
    [ G ; Γ ,, A @ l ⊢g Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ⊢ Ot ≈ Ot' : X⟨↑⟩ @ li ] ->
    [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g C : X⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢g M @ l' ] ->
    [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢ M ≈ M' @ l' ] ->
    [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢
        iwfihty l li l' X A N Ot C M ≈ iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
    [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
        ⊢ c ≈ c' : iwfstepty l li X A N Ot C M @ l' ] ->
    [ G ; Γ ⊢ m ≈ m' : X @ li ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyIWf l li X A N Ot C m @ lmax l li ] ->
    [ G ; Γ ⊢ tmElimIWf l li l' X A N Ot C M c m ν ~ tmElimIWf k ki k' X' A' N' Ot' C' M' c' m' ν'
        : M[lsingle2 m ν] @ l' ] ;
  (** the codes of [DVec] and [IWf] (M17c), as [Wf]'s *)
  geq_tm_code_dvec {G Γ l l' n n' f f'} : lequiv (gL G) l l' ->
    [ G ; Γ ⊢g n : tyNat @ lzero ] -> [ G ; Γ ⊢ n ≈ n' : tyNat @ lzero ] ->
    [ G ; Γ ,, tyFin n @ lzero ⊢ f ≈ f' : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢ tmDVec l n f ≈ tmDVec l' n' f' : tyU l @ lsuc l ] ;
  geq_tm_code_iwf {G Γ l li k ki x x' s s' n n' o o' c c' m m'} :
    lequiv (gL G) l k -> lequiv (gL G) li ki ->
    [ G ; Γ ⊢g x : tyU li @ lsuc li ] -> [ G ; Γ ⊢ x ≈ x' : tyU li @ lsuc li ] ->
    [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ⊢ s ≈ s' : tyU l @ lsuc l ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢g n : tyNat @ lzero ] -> [ G ; Γ ,, tyEl l s @ l ⊢ n ≈ n' : tyNat @ lzero ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢ o ≈ o' : tyEl li x⟨↑⟩ @ li ] ->
    [ G ; Γ ,, tyEl l s @ l ,, tyFin n @ lzero ⊢ c ≈ c' : tyEl li x⟨↑⟩⟨↑⟩ @ li ] ->
    [ G ; Γ ⊢ m ≈ m' : tyEl li x @ li ] ->
    [ G ; Γ ⊢ tmIWf l li x s n o c m ≈ tmIWf k ki x' s' n' o' c' m' : tyU (lmax l li) @ lsuc (lmax l li) ]
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
  ep_brctx : forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ] ;
  ep_brctx' : forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ] ;
  ep_br : forall k, k < nbr -> @geq_tm EM (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                                (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt)) (brLv k l1 l2) ;
  ep_br' : forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
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
  (* on a boxed global: a global variable, or a definition (M9) *)
  gne_tm_elimt_glob {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' c c'} :
    boxed_global c -> boxed_global c' ->
    [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T (boxt c)
                  ≅ mott (wrapMt Mt') l' Δ' T' (boxt c') @ l2 ] ->
    ElimPrem EP EM G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ' ⊢[ lD ] T' @ l' ] -> @geq_ty EP G Δ T T' l ->
    [ G ; Γ ⊢[ lM ] boxt c ≅ boxt c' : tyCTrm Δ T l @ lzero ] ->
    @gne_tm EM G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c))
      (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' (boxt c'))
      (mott (wrapMt Mt) l Δ T (boxt c)) l2 ;

  (* universe polymorphism (07:296–342, M4_DESIGN.md F4): congruence of
     [UΠ], extensionality at the bound variables, neutral application *)
  geq_ty_upi {G Γ n l l' T T'} : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lequiv (n + gL G) l l' ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] -> @geq_ty EM (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' l ->
    @geq_ty EM G Γ (tyUPi n l T) (tyUPi n l' T') lomega ;
  geq_tm_uext {G Γ n l T t t'} : 0 < n -> lwf (n + gL G) l ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] t : tyUPi n l T @ lomega ] -> [ G ; Γ ⊢[ lM ] t' : tyUPi n l T @ lomega ] ->
    @geq_tm EM (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp t⟨ush n⟩ᵤ (ubvars n)) (uapp t'⟨ush n⟩ᵤ (ubvars n)) T l ->
    @geq_tm EM G Γ t t' (tyUPi n l T) lomega ;
  gne_tm_uapp {G Γ n l T ν ν' ls ls'} : lwf (n + gL G) l ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] -> length ls = n -> Forall2 (lequiv (gL G)) ls ls' ->
    @gne_tm EM G Γ ν ν' (tyUPi n l T) lomega ->
    @gne_tm EM G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ (lvsubst l (uext ls lvar)) ;

  (* meta-functions (07:296–350, M5_DESIGN.md G4): congruences of [CΠ] and
     [TΠ], extensionality at the bound variable, neutral applications. As
     for the rules, the right body of [TΠ] and the applications' instance
     equations are declarative premises (G2) *)
  geq_ty_cpi {G Γ l l' T T'} : [ G ; Γ ⊢[ lM ] ] -> lequiv (gL G) l l' ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] -> @geq_ty EM (gext G gdCtx) Γ⟪S⟫ T T' l ->
    @geq_ty EM G Γ (tyCPi l T) (tyCPi l' T') l ;
  geq_ty_tpi {G Γ Δ Δ' l1 l2 l3 l4 T T'} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] ->
    @geq_ctx EP G Δ Δ' -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T @ l2 ] -> @geq_ty EM (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T' l2 ->
    [ gext G (gdTy Δ' lD l3) ; Γ⟪S⟫ ⊢[ lM ] T' @ l4 ] ->
    @geq_ty EM G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ' l3 l4 T') l2 ;
  geq_tm_cext {G Γ l T t t'} : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] t : tyCPi l T @ l ] -> [ G ; Γ ⊢[ lM ] t' : tyCPi l T @ l ] ->
    @geq_tm EM (gext G gdCtx) Γ⟪S⟫ (capp t⟪S⟫ (cvar 0)) (capp t'⟪S⟫ (cvar 0)) T l ->
    @geq_tm EM G Γ t t' (tyCPi l T) l ;
  geq_tm_text {G Γ Δ l l' T t t'} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
    [ G ; Γ ⊢[ lM ] t : tyTPi Δ l l' T @ l' ] -> [ G ; Γ ⊢[ lM ] t' : tyTPi Δ l l' T @ l' ] ->
    @geq_tm EM (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp t⟪S⟫ (tyGvar 0 (lshift 0))) (tapp t'⟪S⟫ (tyGvar 0 (lshift 0))) T l' ->
    @geq_tm EM G Γ t t' (tyTPi Δ l l' T) l' ;
  gne_tm_capp {G Γ l T ν ν' Δ Δ'} : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ G ; Δ ⊢[ lD ] ] -> @geq_ctx EP G Δ Δ' ->
    [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ)⦄ ≅ T⦃gsingle (GCtx Δ')⦄ @ l ] ->
    @gne_tm EM G Γ ν ν' (tyCPi l T) l ->
    @gne_tm EM G Γ (capp ν Δ) (capp ν' Δ') T⦃gsingle (GCtx Δ)⦄ l ;
  gne_tm_tapp {G Γ Δ l l' T ν ν' A A'} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
    [ G ; Δ ⊢[ lD ] A @ l ] -> @geq_ty EP G Δ A A' l ->
    [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A)⦄ ≅ T⦃gsingle (GTy A')⦄ @ l' ] ->
    @gne_tm EM G Γ ν ν' (tyTPi Δ l l' T) l' ->
    @gne_tm EM G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄ l'
}.
