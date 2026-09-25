(** * Declarative typing: the MLTT fragment (ch. 4 §"Typing and Equivalence
    Judgments" and §"Computation Rules")

    All judgments are [Prop]-valued and indexed by the global context
    [G = (L, Ψ)], the layer [i] and (except contexts) a universe level.

    Layer gating, as in the paper:
    - layer [V] admits only the variable rule and the conversion rules, so
      every other rule carries [i <> lV];
    - contexts and types of a layer-[i] judgment live at [typeof i];
    - β/η rules require [compt i] (layers D and M).

    Deviations (all admissible in the paper's system): explicit reflexivity
    rules, and well-formedness premises on some congruences (as logrel-coq
    does), which simplify the metatheory. *)
From DeLaM.Typing Require Export RecSpec.

Reserved Notation "[ ⊢ G ]" (at level 0, G at level 50).
Reserved Notation "[ G ; Γ ⊢[ i ] ]" (at level 0, G, Γ, i at level 50).
Reserved Notation "[ G ; Γ ⊢[ i ] T @ l ]" (at level 0, G, Γ, i, T, l at level 50).
Reserved Notation "[ G ; Γ ⊢[ i ] t : T @ l ]" (at level 0, G, Γ, i, t, T, l at level 50).
Reserved Notation "[ G ; Γ ⊢[ i ] T ≅ T' @ l ]" (at level 0, G, Γ, i, T, T', l at level 50).
Reserved Notation "[ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]" (at level 0, G, Γ, i, t, t', T, l at level 50).
Reserved Notation "[ G ⊢[ i ] Γ ≅ Γ' ]" (at level 0, G, i, Γ, Γ' at level 50).

Inductive wf_glob : gctx -> Prop :=
| wfg_nil L : [ ⊢ mkG L nil ]
| wfg_ctx L Ψ : [ ⊢ mkG L Ψ ] -> [ ⊢ mkG L (gdCtx :: Ψ) ]
| wfg_ty L Ψ Δ i l : [ ⊢ mkG L Ψ ] -> [ mkG L Ψ ; Δ ⊢[ lD ] ] -> (i = lC \/ i = lD) ->
    lwf L l -> [ ⊢ mkG L (gdTy Δ i l :: Ψ) ]
| wfg_tm L Ψ Δ i T l : [ ⊢ mkG L Ψ ] -> [ mkG L Ψ ; Δ ⊢[ lD ] T @ l ] -> (i = lV \/ i = lC) ->
    lwf L l -> [ ⊢ mkG L (gdTm Δ i T l :: Ψ) ]

with wf_ctx : gctx -> layer -> ctx -> Prop :=
| wfc_nil G i : [ ⊢ G ] -> [ G ; cnil ⊢[ i ] ]
| wfc_var G i g : [ ⊢ G ] -> gctx_var G g -> [ G ; cvar g ⊢[ i ] ]
| wfc_ext G i Γ A l :
    [ G ; Γ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢[ i ] ]

with wf_ty : gctx -> layer -> ctx -> ty -> lvl -> Prop :=
| wft_nat G i Γ : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] tyNat @ lzero ]
| wft_pi G i Γ l l' A B : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] tyPi l l' A B @ lmax l l' ]
| wft_U G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tyU l @ lsuc l ]
| wft_El G i Γ l t : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] tyEl l t @ l ]
| wft_lconv G i Γ T l l' : [ G ; Γ ⊢[ i ] T @ l' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] T @ l ]
(* global type variables, with their local substitution typed by lookups *)
| wft_gvar G i Γ U Δ i' l d : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' i -> lsub_tail d Δ Γ -> dnfl d ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    [ G ; Γ ⊢[ i ] tyGvar U d @ l ]
(* contextual types (layer M only) *)
| wft_CTyp G Γ Δ l : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ lM ] tyCTyp Δ l @ lzero ]
| wft_CTrm G Γ Δ T l : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ lM ] tyCTrm Δ T l @ lzero ]

with wf_tm : gctx -> layer -> ctx -> tm -> ty -> lvl -> Prop :=
| wf_var G i Γ n T l : [ G ; Γ ⊢[ typeof i ] ] -> in_ctx Γ n T l ->
    [ G ; Γ ⊢[ i ] var n : T @ l ]
| wf_code_nat G i Γ : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] ->
    [ G ; Γ ⊢[ i ] tmNat : tyU lzero @ lsuc lzero ]
| wf_code_U G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tmU l : tyU (lsuc l) @ lsuc (lsuc l) ]
| wf_code_pi G i Γ l l' s t : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢[ i ] t : tyU l' @ lsuc l' ] ->
    [ G ; Γ ⊢[ i ] tmPi l l' s t : tyU (lmax l l') @ lsuc (lmax l l') ]
| wf_zero G i Γ : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]
| wf_succ G i Γ t : i <> lV -> [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] ->
    [ G ; Γ ⊢[ i ] succ t : tyNat @ lzero ]
| wf_natrec G i Γ l M s z t : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] ->
    [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] ->
    [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] ->
    [ G ; Γ ⊢[ i ] natrec l M s z t : M[lsingle t] @ l ]
| wf_lam G i Γ l l' A B t : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] t : B @ l' ] ->
    [ G ; Γ ⊢[ i ] lam l l' A t : tyPi l l' A B @ lmax l l' ]
| wf_app G i Γ l l' A B t s : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] -> [ G ; Γ ⊢[ i ] s : A @ l ] ->
    [ G ; Γ ⊢[ i ] app t l l' A B s : B[lsingle s] @ l' ]
| wf_conv G i Γ t T T' l : [ G ; Γ ⊢[ i ] t : T' @ l ] -> [ G ; Γ ⊢[ typeof i ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢[ i ] t : T @ l ]
| wf_lconv G i Γ t T l l' : [ G ; Γ ⊢[ i ] t : T @ l' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] t : T @ l ]
(* global term variables: every layer from the binding's upward, incl. V *)
| wf_gvar G i Γ u Δ i' T l d : [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i -> lsub_tail d Δ Γ -> dnfl d ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    [ G ; Γ ⊢[ i ] gvar u d : T[d] @ l ]
(* code (layer M only; the code itself lives at layer C) *)
| wf_boxT G Γ Δ T l : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] boxT T : tyCTyp Δ l @ lzero ]
| wf_boxt G Γ Δ t T l : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] ->
    [ G ; Δ ⊢[ lC ] t : T @ l ] ->
    [ G ; Γ ⊢[ lM ] boxt t : tyCTrm Δ T l @ lzero ]
| wf_letboxT G Γ l' l Δ M t' t : lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] ->
    [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] ->
    [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
    [ G ; Γ ⊢[ lM ] letboxT l' l Δ M t' t : M[lsingle t] @ l' ]
| wf_letboxt G Γ l' l Δ T M t' t : lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Δ ⊢[ lD ] T @ l ] ->
    [ G ; Γ ,, tyCTrm Δ T l @ lzero ⊢[ lM ] M @ l' ] ->
    [ gext G (gdTm Δ lC T l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] ->
    [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l @ lzero ] ->
    [ G ; Γ ⊢[ lM ] letboxt l' l Δ T M t' t : M[lsingle t] @ l' ]
(* the recursors on code (04:1127–1310; branch scopes in RecSpec). The
   branch contexts' well-formedness is a premise: their entries are motive
   instances, and weakening/substitution need them as induction hypotheses.
   The result type (a motive instance) is a premise too, as are the
   congruences' instance equation and the β reducts' typing: the
   metatheory needs them before global substitution (M3_DESIGN.md E10) *)
| wf_elimT G Γ l1 l2 MT Mt bs l Δ t :
    [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t @ l1 ] ->
    lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
    [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : motT (wrapMT MT) l Δ t @ l1 ]
| wf_elimt G Γ l1 l2 MT Mt bs l Δ T t :
    [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t @ l2 ] ->
    lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    [ G ; Δ ⊢[ lD ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l @ lzero ] ->
    [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t : mott (wrapMt Mt) l Δ T t @ l2 ]

with eq_ty : gctx -> layer -> ctx -> ty -> ty -> lvl -> Prop :=
| eqty_refl G i Γ T l : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T @ l ]
| eqty_sym G i Γ T T' l : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T' ≅ T @ l ]
| eqty_trans G i Γ T T' T'' l : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T' ≅ T'' @ l ] ->
    [ G ; Γ ⊢[ i ] T ≅ T'' @ l ]
| eqty_pi G i Γ l1 l2 l3 l4 A A' B B' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢[ i ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ]
| eqty_U G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tyU l ≅ tyU l' @ lsuc l ]
| eqty_El G i Γ l l' t t' : i <> lV -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] t ≅ t' : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] tyEl l t ≅ tyEl l' t' @ l ]
| eqty_El_nat G i Γ : compt i -> [ G ; Γ ⊢[ typeof i ] ] ->
    [ G ; Γ ⊢[ i ] tyNat ≅ tyEl lzero tmNat @ lzero ]
| eqty_El_U G i Γ l : compt i -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tyU l ≅ tyEl (lsuc l) (tmU l) @ lsuc l ]
| eqty_El_pi G i Γ l l' s t : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢[ i ] t : tyU l' @ lsuc l' ] ->
    [ G ; Γ ⊢[ i ] tyPi l l' (tyEl l s) (tyEl l' t) ≅ tyEl (lmax l l') (tmPi l l' s t) @ lmax l l' ]
| eqty_lconv G i Γ T T' l l' : [ G ; Γ ⊢[ i ] T ≅ T' @ l' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] T ≅ T' @ l ]
| eqty_gvar G i Γ U Δ i' l d d' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' i ->
    lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
    [ G ; Γ ⊢[ i ] tyGvar U d ≅ tyGvar U d' @ l ]
(* level equivalence at layer M: admissible below M (StaticCode), a rule
   here, validated by the relation's level invariance (M3_DESIGN.md E12) *)
| eqty_leq G Γ T T' l : [ G ; Γ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] T' @ l ] -> ty_leq T T' ->
    [ G ; Γ ⊢[ lM ] T ≅ T' @ l ]
| eqty_CTyp G Γ Δ Δ' l l' : [ G ; Γ ⊢[ lM ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ lM ] tyCTyp Δ l ≅ tyCTyp Δ' l' @ lzero ]
| eqty_CTrm G Γ Δ Δ' T T' l l' : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ lM ] tyCTrm Δ T l ≅ tyCTrm Δ' T' l' @ lzero ]

with eq_tm : gctx -> layer -> ctx -> tm -> tm -> ty -> lvl -> Prop :=
| eqtm_refl G i Γ t T l : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t ≅ t : T @ l ]
| eqtm_sym G i Γ t t' T l : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t' ≅ t : T @ l ]
| eqtm_trans G i Γ t t' t'' T l :
    [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t' ≅ t'' : T @ l ] ->
    [ G ; Γ ⊢[ i ] t ≅ t'' : T @ l ]
| eqtm_code_U G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tmU l ≅ tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ]
| eqtm_code_pi G i Γ l1 l2 l3 l4 s s' t t' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] ->
    [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
    [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
    [ G ; Γ ⊢[ i ] tmPi l1 l2 s t ≅ tmPi l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ]
| eqtm_succ G i Γ t t' : i <> lV -> [ G ; Γ ⊢[ i ] t ≅ t' : tyNat @ lzero ] ->
    [ G ; Γ ⊢[ i ] succ t ≅ succ t' : tyNat @ lzero ]
| eqtm_natrec G i Γ l l' M M' s s' z z' t t' : i <> lV -> lequiv (gL G) l l' ->
    [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M ≅ M' @ l ] ->
    [ G ; Γ ⊢[ i ] s ≅ s' : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z ≅ z' : M[lsucc] @ l ] ->
    [ G ; Γ ⊢[ i ] t ≅ t' : tyNat @ lzero ] ->
    [ G ; Γ ⊢[ i ] natrec l M s z t ≅ natrec l' M' s' z' t' : M[lsingle t] @ l ]
| eqtm_lam G i Γ l1 l2 l3 l4 A A' B t t' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] t ≅ t' : B @ l2 ] ->
    [ G ; Γ ⊢[ i ] lam l1 l2 A t ≅ lam l3 l4 A' t' : tyPi l1 l2 A B @ lmax l1 l2 ]
| eqtm_app G i Γ l1 l2 l3 l4 A A' B B' t t' s s' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢[ i ] t ≅ t' : tyPi l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢[ i ] s ≅ s' : A @ l1 ] ->
    [ G ; Γ ⊢[ i ] app t l1 l2 A B s ≅ app t' l3 l4 A' B' s' : B[lsingle s] @ l2 ]
| eqtm_conv G i Γ t t' T T' l : [ G ; Γ ⊢[ i ] t ≅ t' : T' @ l ] ->
    [ G ; Γ ⊢[ typeof i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]
| eqtm_lconv G i Γ t t' T l l' : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]
| eqtm_gvar G i Γ u Δ i' T l d d' : [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i ->
    lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
    [ G ; Γ ⊢[ i ] gvar u d ≅ gvar u d' : T[d] @ l ]
| eqtm_leq G Γ t t' T l : [ G ; Γ ⊢[ lM ] t : T @ l ] -> [ G ; Γ ⊢[ lM ] t' : T @ l ] -> tm_leq t t' ->
    [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ]
(* [box] congruence: code up to level equivalence (the Static Code Lemma,
   05:1055; M3_DESIGN.md E11), with its C-equation *)
| eqtm_boxT G Γ Δ T T' l : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Δ ⊢[ lC ] T' @ l ] -> [ G ; Δ ⊢[ lC ] T ≅ T' @ l ] -> ty_leq T T' ->
    [ G ; Γ ⊢[ lM ] boxT T ≅ boxT T' : tyCTyp Δ l @ lzero ]
| eqtm_boxt G Γ Δ t t' T l : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] -> [ G ; Δ ⊢[ lC ] t' : T @ l ] ->
    [ G ; Δ ⊢[ lC ] t ≅ t' : T @ l ] -> tm_leq t t' ->
    [ G ; Γ ⊢[ lM ] boxt t ≅ boxt t' : tyCTrm Δ T l @ lzero ]
| eqtm_letboxT G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 t t0 :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
    [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M @ l1 ] ->
    [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
    [ G ; Γ ,, tyCTyp Δ' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
    [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t1 ≅ t2
        : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ] ->
    [ gext G (gdTy Δ' lC l4) ; Γ⟪S⟫ ⊢[ lM ] t2
        : M'⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l3 ] ->
    [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTyp Δ l2 @ lzero ] ->
    [ G ; Γ ⊢[ lM ] letboxT l1 l2 Δ M t1 t ≅ letboxT l3 l4 Δ' M' t2 t0 : M[lsingle t] @ l1 ]
| eqtm_letboxt G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 t t0 :
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
    [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    [ G ; Δ ⊢[ lD ] T @ l2 ] -> [ G ; Δ' ⊢[ lD ] T' @ l4 ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l2 ] ->
    [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M @ l1 ] ->
    [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
    [ G ; Γ ,, tyCTrm Δ' T' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
    [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] t1 ≅ t2
        : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ] ->
    [ gext G (gdTm Δ' lC T' l4) ; Γ⟪S⟫ ⊢[ lM ] t2
        : M'⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l3 ] ->
    [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTrm Δ T l2 @ lzero ] ->
    [ G ; Γ ⊢[ lM ] letboxt l1 l2 Δ T M t1 t ≅ letboxt l3 l4 Δ' T' M' t2 t0 : M[lsingle t] @ l1 ]
| eqtm_elimT G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' t t' :
    [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t ≅ motT (wrapMT MT') l' Δ' t' @ l1 ] ->
    lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> lequiv (gL G) l l' ->
    [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k ≅ bs' k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                           bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]) ->
    [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTyp Δ l @ lzero ] ->
    [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t ≅ elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' t'
                  : motT (wrapMT MT) l Δ t @ l1 ]
| eqtm_elimt G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' t t' :
    [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t ≅ mott (wrapMt Mt') l' Δ' T' t' @ l2 ] ->
    lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> lequiv (gL G) l l' ->
    [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ' ⊢[ lD ] T' @ l' ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k ≅ bs' k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                           bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]) ->
    [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTrm Δ T l @ lzero ] ->
    [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t ≅ elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' t'
                  : mott (wrapMt Mt) l Δ T t @ l2 ]
(* the schematic β rules (M3_DESIGN.md E4); the reduct's typing is a premise (E10) *)
| eqtm_elimT_beta G Γ l1 l2 rb l Δ c T k r :
    [ G ; Γ ⊢[ lM ] elimT l1 l2 rb l Δ (boxT c) : T @ k ] -> redT l1 l2 rb l Δ c = Some r ->
    [ G ; Γ ⊢[ lM ] r : T @ k ] ->
    [ G ; Γ ⊢[ lM ] elimT l1 l2 rb l Δ (boxT c) ≅ r : T @ k ]
| eqtm_elimt_beta G Γ l1 l2 rb l Δ T0 c T k r :
    [ G ; Γ ⊢[ lM ] elimt l1 l2 rb l Δ T0 (boxt c) : T @ k ] -> redt l1 l2 rb l Δ T0 c = Some r ->
    [ G ; Γ ⊢[ lM ] r : T @ k ] ->
    [ G ; Γ ⊢[ lM ] elimt l1 l2 rb l Δ T0 (boxt c) ≅ r : T @ k ]
(* computation rules: layers D and M only *)
| eqtm_natrec_zero G i Γ l M s z : compt i -> lwf (gL G) l ->
    [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] ->
    [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] ->
    [ G ; Γ ⊢[ i ] natrec l M s z zero ≅ s : M[lsingle zero] @ l ]
| eqtm_natrec_succ G i Γ l M s z t : compt i -> lwf (gL G) l ->
    [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] ->
    [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] ->
    [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] ->
    [ G ; Γ ⊢[ i ] natrec l M s z (succ t) ≅ z[lsingle2 t (natrec l M s z t)]
                  : M[lsingle (succ t)] @ l ]
| eqtm_beta G i Γ l l' A B t s : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ,, A @ l ⊢[ i ] t : B @ l' ] -> [ G ; Γ ⊢[ i ] s : A @ l ] ->
    [ G ; Γ ⊢[ i ] app (lam l l' A t) l l' A B s ≅ t[lsingle s] : B[lsingle s] @ l' ]
| eqtm_eta G i Γ l l' A B t : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] ->
    [ G ; Γ ⊢[ i ] lam l l' A (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) ≅ t
                  : tyPi l l' A B @ lmax l l' ]
| eqtm_letboxT_beta G Γ l' l Δ M t' T : lwf (gL G) l' -> lwf (gL G) l ->
    [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] T @ l ] ->
    [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] ->
    [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] ->
    [ G ; Γ ⊢[ lM ] letboxT l' l Δ M t' (boxT T) ≅ t'⦃gsingle (GTy T)⦄ : M[lsingle (boxT T)] @ l' ]
| eqtm_letboxt_beta G Γ l' l Δ T M t' t : lwf (gL G) l' -> lwf (gL G) l ->
    [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] -> [ G ; Δ ⊢[ lD ] T @ l ] ->
    [ G ; Γ ,, tyCTrm Δ T l @ lzero ⊢[ lM ] M @ l' ] ->
    [ gext G (gdTm Δ lC T l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] ->
    [ G ; Γ ⊢[ lM ] letboxt l' l Δ T M t' (boxt t) ≅ t'⦃gsingle (GTm t)⦄ : M[lsingle (boxt t)] @ l' ]

(** Context equivalence ([Ψ ⊢ᵢ Γ ≈ Δ], used by the congruences of [□]). *)
with eq_ctx : gctx -> layer -> ctx -> ctx -> Prop :=
| eqc_nil G i : [ ⊢ G ] -> [ G ⊢[ i ] cnil ≅ cnil ]
| eqc_var G i g : [ ⊢ G ] -> gctx_var G g -> [ G ⊢[ i ] cvar g ≅ cvar g ]
| eqc_ext G i Γ Γ' A A' l l' : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G ; Γ ⊢[ i ] A @ l ] ->
    [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> lequiv (gL G) l l' -> [ G ⊢[ i ] Γ ,, A @ l ≅ Γ' ,, A' @ l' ]

where "[ ⊢ G ]" := (wf_glob G)
  and "[ G ; Γ ⊢[ i ] ]" := (wf_ctx G i Γ)
  and "[ G ; Γ ⊢[ i ] T @ l ]" := (wf_ty G i Γ T l)
  and "[ G ; Γ ⊢[ i ] t : T @ l ]" := (wf_tm G i Γ t T l)
  and "[ G ; Γ ⊢[ i ] T ≅ T' @ l ]" := (eq_ty G i Γ T T' l)
  and "[ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]" := (eq_tm G i Γ t t' T l)
  and "[ G ⊢[ i ] Γ ≅ Γ' ]" := (eq_ctx G i Γ Γ').

Scheme wf_glob_mut := Induction for wf_glob Sort Prop
  with wf_ctx_mut := Induction for wf_ctx Sort Prop
  with wf_ty_mut := Induction for wf_ty Sort Prop
  with wf_tm_mut := Induction for wf_tm Sort Prop
  with eq_ty_mut := Induction for eq_ty Sort Prop
  with eq_tm_mut := Induction for eq_tm Sort Prop
  with eq_ctx_mut := Induction for eq_ctx Sort Prop.
Combined Scheme typing_mut from wf_glob_mut, wf_ctx_mut, wf_ty_mut, wf_tm_mut, eq_ty_mut, eq_tm_mut,
  eq_ctx_mut.
