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
(* a definition: its body checked at layer C, the binding's own (M9, Heather's wf-def) *)
| wfg_def L Ψ Δ T l t : [ ⊢ mkG L Ψ ] -> [ mkG L Ψ ; Δ ⊢[ lD ] T @ l ] -> lwf L l ->
    [ mkG L Ψ ; Δ ⊢[ lC ] t : T @ l ] -> [ ⊢ mkG L (gdDef Δ T l t :: Ψ) ]

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
(* universe polymorphism (layer M only; M4_DESIGN.md F2): the body lives
   under [n] fresh levels, in the universe-weakened scope; [UΠ] lives at ω *)
| wft_upi G Γ n l T : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lwf (n + gL G) l ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] tyUPi n l T @ lomega ]
(* meta-functions (layer M only; M5_DESIGN.md G2): the body lives under one
   global binder, a context variable or a type variable at layer P *)
| wft_cpi G Γ l T : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] tyCPi l T @ l ]
| wft_tpi G Γ Δ l l' T : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
    [ G ; Γ ⊢[ lM ] tyTPi Δ l l' T @ l' ]
(* dependent pairs (every layer but V: code since M8d, M8_DESIGN.md L1) *)
| wft_sig G i Γ l l' A B : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] tySig l l' A B @ lmax l l' ]
(* the unit type (every layer but V since M8d; M8_DESIGN.md K2, L1) *)
| wft_unit G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tyUnit l @ l ]
(* strict equality and the irrelevant empty type (M10_DESIGN.md): every layer but V since M10c *)
| wft_seq G i Γ l A a b : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] b : A @ l ] ->
    [ G ; Γ ⊢[ i ] tySEq l A a b @ l ]
| wft_sempty G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tySEmpty l @ l ]
(* the identity type (M11_DESIGN.md): every layer but V since M11b *)
| wft_id G i Γ l A a b : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] b : A @ l ] ->
    [ G ; Γ ⊢[ i ] tyId l A a b @ l ]
(* the empty type (M12a; every layer but V since M12c), level-indexed *)
| wft_empty G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tyEmpty l @ l ]
(* binary sums (M12b; every layer but V since M12c), non-dependent *)
| wft_sum G i Γ l l' A B : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] tySum l l' A B @ lmax l l' ]

(* the generic rules last: [econstructor]-based dispatchers ([any_rule])
   try the rules in order, and these unify with every goal *)
| wft_lconv G i Γ T l l' : [ G ; Γ ⊢[ i ] T @ l' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] T @ l ]
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
(* global term variables: every layer from the binding's upward, incl. V *)
| wf_gvar G i Γ u Δ i' T l d : [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i -> lsub_tail d Δ Γ -> dnfl d ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    [ G ; Γ ⊢[ i ] gvar u d : T[d] @ l ]
(* a defined global carries its body, typed at the use's layer (M9_DESIGN.md N1),
   level-equivalent to the declared one, as code is compared (N2) *)
| wf_gdef G i Γ u Δ T l t0 t d : [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t -> lle lC i -> lsub_tail d Δ Γ -> dnfl d ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    [ G ; Δ ⊢[ i ] t : T @ l ] ->
    [ G ; Γ ⊢[ i ] gdef u t d : T[d] @ l ]
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
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
    [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : motT (wrapMT MT) l Δ t @ l1 ]
| wf_elimt G Γ l1 l2 MT Mt bs l Δ T t :
    [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t @ l2 ] ->
    lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    [ G ; Δ ⊢[ lD ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l @ lzero ] ->
    [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t : mott (wrapMt Mt) l Δ T t @ l2 ]
| wf_ulam G Γ n l T t : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lwf (n + gL G) l ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t : T @ l ] ->
    [ G ; Γ ⊢[ lM ] ulam n l T t : tyUPi n l T @ lomega ]
| wf_uapp G Γ n l T t ls : lwf (n + gL G) l ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    length ls = n -> Forall (lwf (gL G)) ls ->
    [ G ; Γ ⊢[ lM ] t : tyUPi n l T @ lomega ] ->
    [ G ; Γ ⊢[ lM ] uapp t ls : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ]
| wf_clam G Γ l T t : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] ->
    [ G ; Γ ⊢[ lM ] clam l T t : tyCPi l T @ l ]
(* the applications carry their result type, as the recursors do (M3 E10) *)
| wf_capp G Γ l T t Δ : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ G ; Δ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lM ] t : tyCPi l T @ l ] ->
    [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ)⦄ @ l ] ->
    [ G ; Γ ⊢[ lM ] capp t Δ : T⦃gsingle (GCtx Δ)⦄ @ l ]
| wf_tlam G Γ Δ l l' T t : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] ->
    [ G ; Γ ⊢[ lM ] tlam Δ l l' T t : tyTPi Δ l l' T @ l' ]
(* the function's typing first: it fixes [U]'s level, absent from the conclusion *)
| wf_tapp G Γ Δ l l' T t A : [ G ; Γ ⊢[ lM ] t : tyTPi Δ l l' T @ l' ] ->
    [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> [ G ; Δ ⊢[ lD ] A @ l ] ->
    [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A)⦄ @ l' ] ->
    [ G ; Γ ⊢[ lM ] tapp t A : T⦃gsingle (GTy A)⦄ @ l' ]
(* dependent pairs (layers D and M) *)
| wf_code_sig G i Γ l l' s t : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢[ i ] t : tyU l' @ lsuc l' ] ->
    [ G ; Γ ⊢[ i ] tmSig l l' s t : tyU (lmax l l') @ lsuc (lmax l l') ]
| wf_pair G i Γ l l' A B a b : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] b : B[lsingle a] @ l' ] ->
    [ G ; Γ ⊢[ i ] tmPair l l' A B a b : tySig l l' A B @ lmax l l' ]
| wf_fst G i Γ l l' A B p : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] ->
    [ G ; Γ ⊢[ i ] tmFst l l' A B p : A @ l ]
| wf_snd G i Γ l l' A B p : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] ->
    [ G ; Γ ⊢[ i ] tmSnd l l' A B p : B[lsingle (tmFst l l' A B p)] @ l' ]
(* the unit type (every layer but V since M8d) *)
| wf_code_unit G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tmUnit l : tyU l @ lsuc l ]
| wf_triv G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tmTriv l : tyUnit l @ l ]
(* strict equality (every layer but V since M10c): [srefl], and [sEmpty]'s eliminator (no β) *)
| wf_srefl G i Γ l A a : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
    [ G ; Γ ⊢[ i ] srefl l A a : tySEq l A a a @ l ]
| wf_elimSEmpty G i Γ l l' M e : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] M @ l' ] -> [ G ; Γ ⊢[ i ] e : tySEmpty l @ l ] ->
    [ G ; Γ ⊢[ i ] elimSEmpty l l' M e : M @ l' ]
(* the identity type (every layer but V since M11b): [refl], and based path induction; the
   motive binds [y : A] and [p : Id(A; a; y)]. The [Id] type of the motive's
   context is a premise (a presupposition, as for the recursors, M3 E10): its
   induction hypothesis supplies the extended context under every operation *)
| wf_idrefl G i Γ l A a : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
    [ G ; Γ ⊢[ i ] tmRefl l A a : tyId l A a a @ l ]
| wf_J G i Γ l l' A a M c u e : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
    [ G ; Γ ,, A @ l ⊢[ i ] tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ] ->
    [ G ; Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ i ] M @ l' ] ->
    [ G ; Γ ⊢[ i ] c : M[lsingle2 a (tmRefl l A a)] @ l' ] ->
    [ G ; Γ ⊢[ i ] u : A @ l ] -> [ G ; Γ ⊢[ i ] e : tyId l A a u @ l ] ->
    [ G ; Γ ⊢[ i ] tmJ l l' A a M c u e : M[lsingle2 u e] @ l' ]
(* the identity type's code (M11b) *)
| wf_code_id G i Γ l s t u : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u : tyEl l s @ l ] ->
    [ G ; Γ ⊢[ i ] tmId l s t u : tyU l @ lsuc l ]
(* strict equality's codes (M10c) *)
| wf_code_seq G i Γ l s t u : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u : tyEl l s @ l ] ->
    [ G ; Γ ⊢[ i ] tmSEq l s t u : tyU l @ lsuc l ]
| wf_code_sempty G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tmSEmpty l : tyU l @ lsuc l ]
(* the empty type's eliminator (M12a; every layer but V since M12c): the motive binds the
   scrutinee, and its level [l] is independent of the scrutinee's [l']; no β *)
| wf_elimEmpty G i Γ l l' M t : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ,, tyEmpty l' @ l' ⊢[ i ] M @ l ] -> [ G ; Γ ⊢[ i ] t : tyEmpty l' @ l' ] ->
    [ G ; Γ ⊢[ i ] elimEmpty l l' M t : M[lsingle t] @ l ]
(* binary sums (M12b; every layer but V since M12c): the injections carry both summands;
   [case]'s motive binds the scrutinee, and each branch's type is the motive
   at the injection of the branch's variable *)
| wf_inl G i Γ l l' A B a : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
    [ G ; Γ ⊢[ i ] tmInl l l' A B a : tySum l l' A B @ lmax l l' ]
| wf_inr G i Γ l l' A B b : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] -> [ G ; Γ ⊢[ i ] b : B @ l' ] ->
    [ G ; Γ ⊢[ i ] tmInr l l' A B b : tySum l l' A B @ lmax l l' ]
| wf_case G i Γ l l' l'' A B M c1 c2 t : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] ->
    [ G ; Γ ,, tySum l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
    [ G ; Γ ,, A @ l ⊢[ i ] c1 : M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
    [ G ; Γ ,, B @ l' ⊢[ i ] c2 : M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
    [ G ; Γ ⊢[ i ] t : tySum l l' A B @ lmax l l' ] ->
    [ G ; Γ ⊢[ i ] tmCase l l' l'' A B M c1 c2 t : M[lsingle t] @ l'' ]
(* the codes of [Empty] and [+] (M12c; every layer but V) *)
| wf_code_empty G i Γ l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tmEmpty l : tyU l @ lsuc l ]
| wf_code_sum G i Γ l l' s t : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] t : tyU l' @ lsuc l' ] ->
    [ G ; Γ ⊢[ i ] tmSum l l' s t : tyU (lmax l l') @ lsuc (lmax l l') ]

(* the generic rules last: [econstructor]-based dispatchers ([any_rule])
   try the rules in order, and these unify with every goal *)
| wf_conv G i Γ t T T' l : [ G ; Γ ⊢[ i ] t : T' @ l ] -> [ G ; Γ ⊢[ typeof i ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢[ i ] t : T @ l ]
| wf_lconv G i Γ t T l l' : [ G ; Γ ⊢[ i ] t : T @ l' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] t : T @ l ]
with eq_ty : gctx -> layer -> ctx -> ty -> ty -> lvl -> Prop :=
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
| eqty_gvar G i Γ U Δ i' l d d' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' i ->
    lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
    [ G ; Γ ⊢[ i ] tyGvar U d ≅ tyGvar U d' @ l ]
| eqty_CTyp G Γ Δ Δ' l l' : [ G ; Γ ⊢[ lM ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ lM ] tyCTyp Δ l ≅ tyCTyp Δ' l' @ lzero ]
| eqty_CTrm G Γ Δ Δ' T T' l l' : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ lM ] tyCTrm Δ T l ≅ tyCTrm Δ' T' l' @ lzero ]
| eqty_upi G Γ n l l' T T' : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lequiv (n + gL G) l l' ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢[ lM ] tyUPi n l T ≅ tyUPi n l' T' @ lomega ]
| eqty_cpi G Γ l l' T T' : [ G ; Γ ⊢[ lM ] ] -> lequiv (gL G) l l' ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyCPi l' T' @ l ]
(* the right side's body is a premise, as for letbox (M5_DESIGN.md G2) *)
| eqty_tpi G Γ Δ Δ' l1 l2 l3 l4 T T' : [ G ; Γ ⊢[ lM ] ] ->
    [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T @ l2 ] ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ] ->
    [ gext G (gdTy Δ' lD l3) ; Γ⟪S⟫ ⊢[ lM ] T' @ l4 ] ->
    [ G ; Γ ⊢[ lM ] tyTPi Δ l1 l2 T ≅ tyTPi Δ' l3 l4 T' @ l2 ]
(* dependent pairs (layers D and M) *)
| eqty_sig G i Γ l1 l2 l3 l4 A A' B B' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢[ i ] tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ lmax l1 l2 ]
| eqty_El_sig G i Γ l l' s t : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢[ i ] t : tyU l' @ lsuc l' ] ->
    [ G ; Γ ⊢[ i ] tySig l l' (tyEl l s) (tyEl l' t) ≅ tyEl (lmax l l') (tmSig l l' s t) @ lmax l l' ]
(* the unit type (every layer but V since M8d) *)
| eqty_unit G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tyUnit l ≅ tyUnit l' @ l ]
| eqty_El_unit G i Γ l : compt i -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tyUnit l ≅ tyEl l (tmUnit l) @ l ]
(* strict equality (layers D and M) *)
| eqty_seq G i Γ l l' A A' a a' b b' : i <> lV -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
    [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] b ≅ b' : A @ l ] ->
    [ G ; Γ ⊢[ i ] tySEq l A a b ≅ tySEq l' A' a' b' @ l ]
| eqty_sempty G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tySEmpty l ≅ tySEmpty l' @ l ]
(* the identity type (every layer but V; El decoding at the computing layers) *)
| eqty_id G i Γ l l' A A' a a' b b' : i <> lV -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
    [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] -> [ G ; Γ ⊢[ i ] b ≅ b' : A @ l ] ->
    [ G ; Γ ⊢[ i ] tyId l A a b ≅ tyId l' A' a' b' @ l ]
| eqty_El_id G i Γ l s t u : compt i -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u : tyEl l s @ l ] ->
    [ G ; Γ ⊢[ i ] tyId l (tyEl l s) t u ≅ tyEl l (tmId l s t u) @ l ]
(* strict equality's codes (M10c) *)
| eqty_El_seq G i Γ l s t u : compt i -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u : tyEl l s @ l ] ->
    [ G ; Γ ⊢[ i ] tySEq l (tyEl l s) t u ≅ tyEl l (tmSEq l s t u) @ l ]
| eqty_El_sempty G i Γ l : compt i -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tySEmpty l ≅ tyEl l (tmSEmpty l) @ l ]
(* the empty type (M12a; every layer but V since M12c) *)
| eqty_empty G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tyEmpty l ≅ tyEmpty l' @ l ]
(* binary sums (M12b; every layer but V since M12c) *)
| eqty_sum G i Γ l1 l2 l3 l4 A A' B B' : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢[ i ] tySum l1 l2 A B ≅ tySum l3 l4 A' B' @ lmax l1 l2 ]
(* the codes of [Empty] and [+] decode (M12c; layers D and M) *)
| eqty_El_empty G i Γ l : compt i -> [ G ; Γ ⊢[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] tyEmpty l ≅ tyEl l (tmEmpty l) @ l ]
| eqty_El_sum G i Γ l l' s t : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] t : tyU l' @ lsuc l' ] ->
    [ G ; Γ ⊢[ i ] tySum l l' (tyEl l s) (tyEl l' t) ≅ tyEl (lmax l l') (tmSum l l' s t) @ lmax l l' ]

(* the generic rules last: [econstructor]-based dispatchers ([any_rule])
   try the rules in order, and these unify with every goal *)
| eqty_refl G i Γ T l : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T @ l ]
| eqty_sym G i Γ T T' l : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T' ≅ T @ l ]
| eqty_trans G i Γ T T' T'' l : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T' ≅ T'' @ l ] ->
    [ G ; Γ ⊢[ i ] T ≅ T'' @ l ]
| eqty_lconv G i Γ T T' l l' : [ G ; Γ ⊢[ i ] T ≅ T' @ l' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] T ≅ T' @ l ]
(* level equivalence at layer M: admissible below M (StaticCode), a rule
   here, validated by the relation's level invariance (M3_DESIGN.md E12) *)
| eqty_leq G Γ T T' l : [ G ; Γ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] T' @ l ] -> ty_leq T T' ->
    [ G ; Γ ⊢[ lM ] T ≅ T' @ l ]
with eq_tm : gctx -> layer -> ctx -> tm -> tm -> ty -> lvl -> Prop :=
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
| eqtm_gvar G i Γ u Δ i' T l d d' : [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i ->
    lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
    [ G ; Γ ⊢[ i ] gvar u d ≅ gvar u d' : T[d] @ l ]
| eqtm_gdef G i Γ u Δ T l t0 t t' d d' : [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t -> tm_leq t0 t' -> lle lC i ->
    lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
    [ G ; Δ ⊢[ i ] t ≅ t' : T @ l ] ->
    [ G ; Γ ⊢[ i ] gdef u t d ≅ gdef u t' d' : T[d] @ l ]
(* δ, at the computing layers only: code keeps the global (M9_DESIGN.md) *)
| eqtm_delta G i Γ u Δ T l t0 t d : compt i -> [ G ; Γ ⊢[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t -> lsub_tail d Δ Γ -> dnfl d ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
    [ G ; Δ ⊢[ i ] t : T @ l ] ->
    [ G ; Γ ⊢[ i ] gdef u t d ≅ t[d] : T[d] @ l ]
(* [box] congruence: the code's C-equation, as in the paper (06:534). The
   code is then [≡ₗ]-related (the Static Code Lemma, M7_DESIGN.md A3) *)
| eqtm_boxT G Γ Δ T T' l : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Δ ⊢[ lC ] T @ l ] -> [ G ; Δ ⊢[ lC ] T' @ l ] -> [ G ; Δ ⊢[ lC ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢[ lM ] boxT T ≅ boxT T' : tyCTyp Δ l @ lzero ]
| eqtm_boxt G Γ Δ t t' T l : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] -> [ G ; Δ ⊢[ lC ] t' : T @ l ] ->
    [ G ; Δ ⊢[ lC ] t ≅ t' : T @ l ] ->
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
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k ≅ bs' k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
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
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs k ≅ bs' k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
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
(* universe polymorphism: congruences, β, η *)
| eqtm_ulam G Γ n l l' T T' t t' : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lequiv (n + gL G) l l' ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T ≅ T' @ l ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t ≅ t' : T @ l ] ->
    [ G ; Γ ⊢[ lM ] ulam n l T t ≅ ulam n l' T' t' : tyUPi n l T @ lomega ]
| eqtm_uapp G Γ n l T t t' ls ls' : lwf (n + gL G) l ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    length ls = n -> Forall2 (lequiv (gL G)) ls ls' ->
    [ G ; Γ ⊢[ lM ] t ≅ t' : tyUPi n l T @ lomega ] ->
    [ G ; Γ ⊢[ lM ] uapp t ls ≅ uapp t' ls' : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ]
| eqtm_ubeta G Γ n l T t ls : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lwf (n + gL G) l ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t : T @ l ] ->
    length ls = n -> Forall (lwf (gL G)) ls ->
    [ G ; Γ ⊢[ lM ] uapp (ulam n l T t) ls ≅ t[uext ls lvar]ᵤ
                  : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ]
| eqtm_ueta G Γ n l T t : 0 < n -> lwf (n + gL G) l ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] t : tyUPi n l T @ lomega ] ->
    [ G ; Γ ⊢[ lM ] ulam n l T (uapp t⟨ush n⟩ᵤ (ubvars n)) ≅ t : tyUPi n l T @ lomega ]
(* meta-functions: congruences, β, η. The applications' instance equation
   and the right side of [ΛU]'s body are premises (M5_DESIGN.md G2) *)
| eqtm_clam G Γ l l' T T' t t' : [ G ; Γ ⊢[ lM ] ] -> lequiv (gL G) l l' ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t ≅ t' : T @ l ] ->
    [ G ; Γ ⊢[ lM ] clam l T t ≅ clam l' T' t' : tyCPi l T @ l ]
| eqtm_capp G Γ l T t t' Δ Δ' : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ)⦄ ≅ T⦃gsingle (GCtx Δ')⦄ @ l ] ->
    [ G ; Γ ⊢[ lM ] t ≅ t' : tyCPi l T @ l ] ->
    [ G ; Γ ⊢[ lM ] capp t Δ ≅ capp t' Δ' : T⦃gsingle (GCtx Δ)⦄ @ l ]
| eqtm_tlam G Γ Δ Δ' l1 l2 l3 l4 T T' t t' : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T @ l2 ] ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ] ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] t ≅ t' : T @ l2 ] ->
    [ gext G (gdTy Δ' lD l3) ; Γ⟪S⟫ ⊢[ lM ] T' @ l4 ] ->
    [ gext G (gdTy Δ' lD l3) ; Γ⟪S⟫ ⊢[ lM ] t' : T' @ l4 ] ->
    [ G ; Γ ⊢[ lM ] tlam Δ l1 l2 T t ≅ tlam Δ' l3 l4 T' t' : tyTPi Δ l1 l2 T @ l2 ]
| eqtm_tapp G Γ Δ l l' T t t' A A' : [ G ; Γ ⊢[ lM ] t ≅ t' : tyTPi Δ l l' T @ l' ] ->
    [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
    [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Δ ⊢[ lD ] A ≅ A' @ l ] ->
    [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A)⦄ ≅ T⦃gsingle (GTy A')⦄ @ l' ] ->
    [ G ; Γ ⊢[ lM ] tapp t A ≅ tapp t' A' : T⦃gsingle (GTy A)⦄ @ l' ]
| eqtm_cbeta G Γ l T t Δ : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> [ G ; Δ ⊢[ lD ] ] ->
    [ G ; Γ ⊢[ lM ] capp (clam l T t) Δ ≅ t⦃gsingle (GCtx Δ)⦄ : T⦃gsingle (GCtx Δ)⦄ @ l ]
| eqtm_tbeta G Γ Δ l l' T t A : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] -> [ G ; Δ ⊢[ lD ] A @ l ] ->
    [ G ; Γ ⊢[ lM ] tapp (tlam Δ l l' T t) A ≅ t⦃gsingle (GTy A)⦄ : T⦃gsingle (GTy A)⦄ @ l' ]
| eqtm_ceta G Γ l T t : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
    [ G ; Γ ⊢[ lM ] t : tyCPi l T @ l ] ->
    [ G ; Γ ⊢[ lM ] clam l T (capp t⟪S⟫ (cvar 0)) ≅ t : tyCPi l T @ l ]
| eqtm_teta G Γ Δ l l' T t : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
    [ G ; Γ ⊢[ lM ] t : tyTPi Δ l l' T @ l' ] ->
    [ G ; Γ ⊢[ lM ] tlam Δ l l' T (tapp t⟪S⟫ (tyGvar 0 (lshift 0))) ≅ t : tyTPi Δ l l' T @ l' ]
(* dependent pairs (layers D and M): congruences, β, η as surjective pairing *)
| eqtm_code_sig G i Γ l1 l2 l3 l4 s s' t t' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] s : tyU l1 @ lsuc l1 ] ->
    [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
    [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
    [ G ; Γ ⊢[ i ] tmSig l1 l2 s t ≅ tmSig l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ]
| eqtm_pair G i Γ l1 l2 l3 l4 A A' B B' a a' b b' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] -> [ G ; Γ ⊢[ i ] b ≅ b' : B[lsingle a] @ l2 ] ->
    [ G ; Γ ⊢[ i ] tmPair l1 l2 A B a b ≅ tmPair l3 l4 A' B' a' b' : tySig l1 l2 A B @ lmax l1 l2 ]
| eqtm_fst G i Γ l1 l2 l3 l4 A A' B B' p p' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢[ i ] p ≅ p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢[ i ] tmFst l1 l2 A B p ≅ tmFst l3 l4 A' B' p' : A @ l1 ]
| eqtm_snd G i Γ l1 l2 l3 l4 A A' B B' p p' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢[ i ] p ≅ p' : tySig l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢[ i ] tmSnd l1 l2 A B p ≅ tmSnd l3 l4 A' B' p' : B[lsingle (tmFst l1 l2 A B p)] @ l2 ]
| eqtm_fst_beta G i Γ l l' A B a b : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] b : B[lsingle a] @ l' ] ->
    [ G ; Γ ⊢[ i ] tmFst l l' A B (tmPair l l' A B a b) ≅ a : A @ l ]
| eqtm_snd_beta G i Γ l l' A B a b : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] b : B[lsingle a] @ l' ] ->
    [ G ; Γ ⊢[ i ] tmSnd l l' A B (tmPair l l' A B a b) ≅ b : B[lsingle a] @ l' ]
| eqtm_sig_eta G i Γ l l' A B p : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
    [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] ->
    [ G ; Γ ⊢[ i ] tmPair l l' A B (tmFst l l' A B p) (tmSnd l l' A B p) ≅ p
                  : tySig l l' A B @ lmax l l' ]
(* the unit type: the code's and [⟨⟩]'s congruences (every layer but V),
   and η as proof irrelevance (computing layers only, M8_DESIGN.md L1) *)
| eqtm_code_unit G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tmUnit l ≅ tmUnit l' : tyU l @ lsuc l ]
| eqtm_triv G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tmTriv l ≅ tmTriv l' : tyUnit l @ l ]
| eqtm_unit_eta G i Γ l t t' : compt i -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] t : tyUnit l @ l ] -> [ G ; Γ ⊢[ i ] t' : tyUnit l @ l ] ->
    [ G ; Γ ⊢[ i ] t ≅ t' : tyUnit l @ l ]
(* strict equality: the congruences (every layer but V since M10c), and proof
   irrelevance at [sEq] and [sEmpty] (the computing layers). Irrelevance subsumes [srefl]'s congruence; it is a
   rule anyway, as [⟨⟩]'s is, so that the substitution lemmas need no
   conversion of [srefl]'s type *)
| eqtm_srefl G i Γ l l' A A' a a' : i <> lV -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
    [ G ; Γ ⊢[ i ] srefl l A a ≅ srefl l' A' a' : tySEq l A a a @ l ]
| eqtm_elimSEmpty G i Γ l1 l2 l3 l4 M M' e e' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] M @ l2 ] -> [ G ; Γ ⊢[ i ] M ≅ M' @ l2 ] ->
    [ G ; Γ ⊢[ i ] e ≅ e' : tySEmpty l1 @ l1 ] ->
    [ G ; Γ ⊢[ i ] elimSEmpty l1 l2 M e ≅ elimSEmpty l3 l4 M' e' : M @ l2 ]
| eqtm_seq_irr G i Γ l A a b p q : compt i -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] p : tySEq l A a b @ l ] -> [ G ; Γ ⊢[ i ] q : tySEq l A a b @ l ] ->
    [ G ; Γ ⊢[ i ] p ≅ q : tySEq l A a b @ l ]
| eqtm_sempty_irr G i Γ l p q : compt i -> lwf (gL G) l ->
    [ G ; Γ ⊢[ i ] p : tySEmpty l @ l ] -> [ G ; Γ ⊢[ i ] q : tySEmpty l @ l ] ->
    [ G ; Γ ⊢[ i ] p ≅ q : tySEmpty l @ l ]
(* the identity type (every layer but V; β at the computing layers): the congruences ([refl]'s compares the
   carrier and the point) and β; no η, which is the absence of K *)
| eqtm_idrefl G i Γ l l' A A' a a' : i <> lV -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
    [ G ; Γ ⊢[ i ] tmRefl l A a ≅ tmRefl l' A' a' : tyId l A a a @ l ]
| eqtm_J G i Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' e e' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ] ->
    [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M @ l2 ] ->
    [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M ≅ M' @ l2 ] ->
    [ G ; Γ ⊢[ i ] c ≅ c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ] ->
    [ G ; Γ ⊢[ i ] u ≅ u' : A @ l1 ] -> [ G ; Γ ⊢[ i ] e ≅ e' : tyId l1 A a u @ l1 ] ->
    [ G ; Γ ⊢[ i ] tmJ l1 l2 A a M c u e ≅ tmJ l3 l4 A' a' M' c' u' e' : M[lsingle2 u e] @ l2 ]
| eqtm_J_beta G i Γ l l' A a M c : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
    [ G ; Γ ,, A @ l ⊢[ i ] tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ] ->
    [ G ; Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ i ] M @ l' ] ->
    [ G ; Γ ⊢[ i ] c : M[lsingle2 a (tmRefl l A a)] @ l' ] ->
    [ G ; Γ ⊢[ i ] tmJ l l' A a M c a (tmRefl l A a) ≅ c : M[lsingle2 a (tmRefl l A a)] @ l' ]
| eqtm_code_id G i Γ l l' s s' t t' u u' : i <> lV -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢[ i ] t ≅ t' : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u ≅ u' : tyEl l s @ l ] ->
    [ G ; Γ ⊢[ i ] tmId l s t u ≅ tmId l' s' t' u' : tyU l @ lsuc l ]
(* strict equality's codes (M10c) *)
| eqtm_code_seq G i Γ l l' s s' t t' u u' : i <> lV -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] -> [ G ; Γ ⊢[ i ] s ≅ s' : tyU l @ lsuc l ] ->
    [ G ; Γ ⊢[ i ] t ≅ t' : tyEl l s @ l ] -> [ G ; Γ ⊢[ i ] u ≅ u' : tyEl l s @ l ] ->
    [ G ; Γ ⊢[ i ] tmSEq l s t u ≅ tmSEq l' s' t' u' : tyU l @ lsuc l ]
| eqtm_code_sempty G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tmSEmpty l ≅ tmSEmpty l' : tyU l @ lsuc l ]
(* the empty type's eliminator (M12a; every layer but V since M12c) *)
| eqtm_elimEmpty G i Γ l1 l2 l3 l4 M M' t t' : i <> lV ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M @ l1 ] -> [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] M ≅ M' @ l1 ] ->
    [ G ; Γ ⊢[ i ] t ≅ t' : tyEmpty l2 @ l2 ] ->
    [ G ; Γ ⊢[ i ] elimEmpty l1 l2 M t ≅ elimEmpty l3 l4 M' t' : M[lsingle t] @ l1 ]
(* binary sums (M12b): the congruences (every layer but V since M12c), and β at either
   injection; no η *)
| eqtm_inl G i Γ l1 l2 l3 l4 A A' B B' a a' : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l1 ] ->
    [ G ; Γ ⊢[ i ] tmInl l1 l2 A B a ≅ tmInl l3 l4 A' B' a' : tySum l1 l2 A B @ lmax l1 l2 ]
| eqtm_inr G i Γ l1 l2 l3 l4 A A' B B' b b' : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] -> [ G ; Γ ⊢[ i ] b ≅ b' : B @ l2 ] ->
    [ G ; Γ ⊢[ i ] tmInr l1 l2 A B b ≅ tmInr l3 l4 A' B' b' : tySum l1 l2 A B @ lmax l1 l2 ]
| eqtm_case G i Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' t t' : i <> lV ->
    lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
    [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ⊢[ i ] B @ l2 ] -> [ G ; Γ ⊢[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M @ l3 ] ->
    [ G ; Γ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢[ i ] M ≅ M' @ l3 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] c1 ≅ c1' : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
    [ G ; Γ ,, B @ l2 ⊢[ i ] c2 ≅ c2' : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
    [ G ; Γ ⊢[ i ] t ≅ t' : tySum l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢[ i ] tmCase l1 l2 l3 A B M c1 c2 t ≅ tmCase l4 l5 l6 A' B' M' c1' c2' t' : M[lsingle t] @ l3 ]
| eqtm_case_inl G i Γ l l' l'' A B M c1 c2 a : compt i -> lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] ->
    [ G ; Γ ,, tySum l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
    [ G ; Γ ,, A @ l ⊢[ i ] c1 : M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
    [ G ; Γ ,, B @ l' ⊢[ i ] c2 : M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
    [ G ; Γ ⊢[ i ] a : A @ l ] ->
    [ G ; Γ ⊢[ i ] tmCase l l' l'' A B M c1 c2 (tmInl l l' A B a) ≅ c1[lsingle a]
        : M[lsingle (tmInl l l' A B a)] @ l'' ]
| eqtm_case_inr G i Γ l l' l'' A B M c1 c2 b : compt i -> lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
    [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] ->
    [ G ; Γ ,, tySum l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
    [ G ; Γ ,, A @ l ⊢[ i ] c1 : M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
    [ G ; Γ ,, B @ l' ⊢[ i ] c2 : M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
    [ G ; Γ ⊢[ i ] b : B @ l' ] ->
    [ G ; Γ ⊢[ i ] tmCase l l' l'' A B M c1 c2 (tmInr l l' A B b) ≅ c2[lsingle b]
        : M[lsingle (tmInr l l' A B b)] @ l'' ]
(* the codes of [Empty] and [+] (M12c; every layer but V) *)
| eqtm_code_empty G i Γ l l' : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] tmEmpty l ≅ tmEmpty l' : tyU l @ lsuc l ]
| eqtm_code_sum G i Γ l1 l2 l3 l4 s s' t t' : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
    [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
    [ G ; Γ ⊢[ i ] tmSum l1 l2 s t ≅ tmSum l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ]

(* the generic rules last: [econstructor]-based dispatchers ([any_rule])
   try the rules in order, and these unify with every goal *)
| eqtm_refl G i Γ t T l : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t ≅ t : T @ l ]
| eqtm_sym G i Γ t t' T l : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t' ≅ t : T @ l ]
| eqtm_trans G i Γ t t' t'' T l :
    [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t' ≅ t'' : T @ l ] ->
    [ G ; Γ ⊢[ i ] t ≅ t'' : T @ l ]
| eqtm_conv G i Γ t t' T T' l : [ G ; Γ ⊢[ i ] t ≅ t' : T' @ l ] ->
    [ G ; Γ ⊢[ typeof i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]
| eqtm_lconv G i Γ t t' T l l' : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l' ] -> lequiv (gL G) l l' ->
    [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]
| eqtm_leq G Γ t t' T l : [ G ; Γ ⊢[ lM ] t : T @ l ] -> [ G ; Γ ⊢[ lM ] t' : T @ l ] -> tm_leq t t' ->
    [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ]
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

(** Try every rule of the goal's judgment in turn, closing its premises with
    [tac]. New rules need no entry in per-lemma rule lists (M8_DESIGN.md,
    cost log). *)
Ltac any_rule tac := solve [econstructor; tac].
