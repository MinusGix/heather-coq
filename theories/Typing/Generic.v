(** * Generic equivalence (ch. 7 §"Generic Equivalence")

    The logical relation is parameterised by four relations (neutral types,
    types, neutral terms, terms) satisfying the laws below.  It is
    instantiated twice: with declarative equality (for normalisation and
    injectivity) and, in a later milestone, with algorithmic convertibility
    (for decidability).  Typing itself stays declarative, as in the paper.

    An instance fixes one computing layer [ge_layer] ([compt]: D or M). *)
From DeLaM.Typing Require Export TypedRed Presupposition.

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
    [ G ; Γ ⊢ app ν l1 l2 A B s ~ app ν' l3 l4 A' B' s' : B[lsingle s] @ l2 ]
}.
