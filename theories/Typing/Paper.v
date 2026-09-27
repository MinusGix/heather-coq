(** * The paper's rule set, over our syntax (M7_DESIGN.md C3 K4)

    The judgments of ch. 4 (04:479–1600) as a second inductive family,
    written P in the design notes (ours, [Declarative.v], is O). The
    representation is ours (K1 items 1–5: de Bruijn indices, canonical
    local substitutions with lookup premises, schematic recursors, the
    annotated abstractions); the rules are the paper's:
    - no reflexivity: a congruence rule per former, including the ones O
      gets from reflexivity ([Nat ≈ Nat], [x ≈ x], [0 ≈ 0], the codes);
    - congruences with the paper's premises only (left-hand, no
      well-formedness of either side unless the paper lists it);
    - no instance premises (recursor result types, application result
      types, their equations, β reducts' typing), no branch-context
      premises, no [≡ₗ] rule;
    - the paper's context equivalence (04:520);
    - level equivalence by the paper's axioms ([leqP], LevelAx.v).

    Gaps and typos in the paper settled here (K1):
    - the recursor congruences, unwritten ("propagate inwards"): every
      component's equation, typed in the left scope;
    - the recursor β rules, listed selectively: one schematic rule per
      recursor, the reduct computed by [redT]/[redt] (as O);
    - the [letbox] scrutinee is typed at level [0] (the paper has [1+l]
      and [l]), the [Π] β of [elim_Typ] concludes at [M_Typ], the [UΠ]
      body is at layer M (the paper has "1");
    - the [El] decoding rules (04:620) are computation rules: [compt i],
      as O (at C they would contradict the Static Code Lemma);
    - the [UΠ] and [ULAM] congruences take [⊢ Γ], which the paper's
      formation and introduction rules have and its congruences omit;
    - the abstractions carry their former (C1b): the congruences of
      [ulam]/[clam]/[tlam] take the former's equation too, and [tlam]'s
      the domain context's;
    - the [λ] congruence's type is [Π^{l₁,l₂}] (the paper writes [l, l']). *)
From DeLaM.Syntax Require Export LevelAx.
From DeLaM.Typing Require Export RecSpec.

Reserved Notation "[ ⊢ₚ G ]" (at level 0, G at level 50).
Reserved Notation "[ G ; Γ ⊢ₚ[ i ] ]" (at level 0, G, Γ, i at level 50).
Reserved Notation "[ G ; Γ ⊢ₚ[ i ] T @ l ]" (at level 0, G, Γ, i, T, l at level 50).
Reserved Notation "[ G ; Γ ⊢ₚ[ i ] t : T @ l ]" (at level 0, G, Γ, i, t, T, l at level 50).
Reserved Notation "[ G ; Γ ⊢ₚ[ i ] T ≅ T' @ l ]" (at level 0, G, Γ, i, T, T', l at level 50).
Reserved Notation "[ G ; Γ ⊢ₚ[ i ] t ≅ t' : T @ l ]" (at level 0, G, Γ, i, t, t', T, l at level 50).
Reserved Notation "[ G ⊢ₚ[ i ] Γ ≅ Γ' ]" (at level 0, G, i, Γ, Γ' at level 50).

Inductive pwf_glob : gctx -> Prop :=
| pwfg_nil L : [ ⊢ₚ mkG L nil ]
| pwfg_ctx L Ψ : [ ⊢ₚ mkG L Ψ ] -> [ ⊢ₚ mkG L (gdCtx :: Ψ) ]
| pwfg_ty L Ψ Δ i l : [ ⊢ₚ mkG L Ψ ] -> [ mkG L Ψ ; Δ ⊢ₚ[ lD ] ] -> (i = lC \/ i = lD) ->
    lwf L l -> [ ⊢ₚ mkG L (gdTy Δ i l :: Ψ) ]
| pwfg_tm L Ψ Δ i T l : [ ⊢ₚ mkG L Ψ ] -> [ mkG L Ψ ; Δ ⊢ₚ[ lD ] T @ l ] -> (i = lV \/ i = lC) ->
    lwf L l -> [ ⊢ₚ mkG L (gdTm Δ i T l :: Ψ) ]

with pwf_ctx : gctx -> layer -> ctx -> Prop :=
| pwfc_nil G i : [ ⊢ₚ G ] -> [ G ; cnil ⊢ₚ[ i ] ]
| pwfc_var G i g : [ ⊢ₚ G ] -> gctx_var G g -> [ G ; cvar g ⊢ₚ[ i ] ]
| pwfc_ext G i Γ A l :
    [ G ; Γ ⊢ₚ[ i ] ] -> [ G ; Γ ⊢ₚ[ i ] A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢ₚ[ i ] ]

with pwf_ty : gctx -> layer -> ctx -> ty -> lvl -> Prop :=
| pwft_nat G i Γ : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] -> [ G ; Γ ⊢ₚ[ i ] tyNat @ lzero ]
| pwft_pi G i Γ l l' A B : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢ₚ[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢ₚ[ i ] B @ l' ] ->
    [ G ; Γ ⊢ₚ[ i ] tyPi l l' A B @ lmax l l' ]
| pwft_El G i Γ l t : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ⊢ₚ[ i ] t : tyU l @ lsuc l ] -> [ G ; Γ ⊢ₚ[ i ] tyEl l t @ l ]
| pwft_U G i Γ l : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢ₚ[ i ] tyU l @ lsuc l ]
| pwft_upi G Γ n l T : [ G ; Γ ⊢ₚ[ lM ] ] -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] T @ l ] ->
    0 < n -> lwf (n + gL G) l -> [ G ; Γ ⊢ₚ[ lM ] tyUPi n l T @ lomega ]
| pwft_lconv G i Γ T l l' : [ G ; Γ ⊢ₚ[ i ] T @ l' ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ i ] T @ l ]
(* 04:1025 *)
| pwft_gvar G i Γ U Δ i' l d : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' i -> lsub_tail d Δ Γ -> dnfl d ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ₚ[ i ] llk d n : A[d] @ k ]) ->
    [ G ; Γ ⊢ₚ[ i ] tyGvar U d @ l ]
| pwft_cpi G Γ l T : [ G ; Γ ⊢ₚ[ lM ] ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢ₚ[ lM ] T @ l ] -> lwf (gL G) l ->
    [ G ; Γ ⊢ₚ[ lM ] tyCPi l T @ l ]
| pwft_tpi G Γ Δ l l' T : [ G ; Γ ⊢ₚ[ lM ] ] -> [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢ₚ[ lM ] T @ l' ] ->
    lwf (gL G) l -> lwf (gL G) l' -> [ G ; Γ ⊢ₚ[ lM ] tyTPi Δ l l' T @ l' ]
| pwft_CTyp G Γ Δ l : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ; Δ ⊢ₚ[ lD ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢ₚ[ lM ] tyCTyp Δ l @ lzero ]
| pwft_CTrm G Γ Δ T l : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ; Δ ⊢ₚ[ lD ] T @ l ] -> lwf (gL G) l ->
    [ G ; Γ ⊢ₚ[ lM ] tyCTrm Δ T l @ lzero ]

with pwf_tm : gctx -> layer -> ctx -> tm -> ty -> lvl -> Prop :=
| pwf_var G i Γ n T l : [ G ; Γ ⊢ₚ[ typeof i ] ] -> in_ctx Γ n T l ->
    [ G ; Γ ⊢ₚ[ i ] var n : T @ l ]
| pwf_code_nat G i Γ : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    [ G ; Γ ⊢ₚ[ i ] tmNat : tyU lzero @ lsuc lzero ]
| pwf_code_pi G i Γ l l' s t : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢ₚ[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢ₚ[ i ] t : tyU l' @ lsuc l' ] ->
    [ G ; Γ ⊢ₚ[ i ] tmPi l l' s t : tyU (lmax l l') @ lsuc (lmax l l') ]
| pwf_code_U G i Γ l : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] -> lwf (gL G) l ->
    [ G ; Γ ⊢ₚ[ i ] tmU l : tyU (lsuc l) @ lsuc (lsuc l) ]
| pwf_zero G i Γ : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] -> [ G ; Γ ⊢ₚ[ i ] zero : tyNat @ lzero ]
| pwf_succ G i Γ t : i <> lV -> [ G ; Γ ⊢ₚ[ i ] t : tyNat @ lzero ] ->
    [ G ; Γ ⊢ₚ[ i ] succ t : tyNat @ lzero ]
| pwf_natrec G i Γ l M s z t : i <> lV -> lwf (gL G) l ->
    [ G ; Γ ,, tyNat @ lzero ⊢ₚ[ i ] M @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] s : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢ₚ[ i ] z : M[lsucc] @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] t : tyNat @ lzero ] ->
    [ G ; Γ ⊢ₚ[ i ] natrec l M s z t : M[lsingle t] @ l ]
| pwf_lam G i Γ l l' A B t : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢ₚ[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢ₚ[ i ] t : B @ l' ] ->
    [ G ; Γ ⊢ₚ[ i ] lam l l' A t : tyPi l l' A B @ lmax l l' ]
| pwf_app G i Γ l l' A B t s : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢ₚ[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢ₚ[ i ] B @ l' ] ->
    [ G ; Γ ⊢ₚ[ i ] t : tyPi l l' A B @ lmax l l' ] -> [ G ; Γ ⊢ₚ[ i ] s : A @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] app t l l' A B s : B[lsingle s] @ l' ]
| pwf_ulam G Γ n l T t : [ G ; Γ ⊢ₚ[ lM ] ] -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] t : T @ l ] ->
    0 < n -> lwf (n + gL G) l ->
    [ G ; Γ ⊢ₚ[ lM ] ulam n l T t : tyUPi n l T @ lomega ]
| pwf_uapp G Γ n l T t ls : [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] t : tyUPi n l T @ lomega ] ->
    length ls = n -> 0 < n -> Forall (lwf (gL G)) ls ->
    [ G ; Γ ⊢ₚ[ lM ] uapp t ls : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ]
| pwf_conv G i Γ t T T' l : [ G ; Γ ⊢ₚ[ i ] t : T' @ l ] -> [ G ; Γ ⊢ₚ[ typeof i ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] t : T @ l ]
| pwf_lconv G i Γ t T l l' : [ G ; Γ ⊢ₚ[ i ] t : T @ l' ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ i ] t : T @ l ]
(* 04:1060 *)
| pwf_gvar G i Γ u Δ i' T l d : [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i -> lsub_tail d Δ Γ -> dnfl d ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ₚ[ i ] llk d n : A[d] @ k ]) ->
    [ G ; Γ ⊢ₚ[ i ] gvar u d : T[d] @ l ]
| pwf_clam G Γ l T t : [ G ; Γ ⊢ₚ[ lM ] ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢ₚ[ lM ] t : T @ l ] ->
    lwf (gL G) l -> [ G ; Γ ⊢ₚ[ lM ] clam l T t : tyCPi l T @ l ]
| pwf_capp G Γ l T t Δ : [ gext G gdCtx ; Γ⟪S⟫ ⊢ₚ[ lM ] T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] t : tyCPi l T @ l ] -> [ G ; Δ ⊢ₚ[ lD ] ] ->
    [ G ; Γ ⊢ₚ[ lM ] capp t Δ : T⦃gsingle (GCtx Δ)⦄ @ l ]
| pwf_tlam G Γ Δ l l' T t : [ G ; Γ ⊢ₚ[ lM ] ] -> [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢ₚ[ lM ] t : T @ l' ] ->
    lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢ₚ[ lM ] tlam Δ l l' T t : tyTPi Δ l l' T @ l' ]
| pwf_tapp G Γ Δ l l' T t A : [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢ₚ[ lM ] T @ l' ] ->
    [ G ; Γ ⊢ₚ[ lM ] t : tyTPi Δ l l' T @ l' ] -> [ G ; Δ ⊢ₚ[ lD ] A @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] tapp t A : T⦃gsingle (GTy A)⦄ @ l' ]
| pwf_boxT G Γ Δ T l : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ; Δ ⊢ₚ[ lC ] T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] boxT T : tyCTyp Δ l @ lzero ]
| pwf_boxt G Γ Δ t T l : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ; Δ ⊢ₚ[ lC ] t : T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] boxt t : tyCTrm Δ T l @ lzero ]
(* 04:1107; the scrutinee at level 0 *)
| pwf_letboxT G Γ l' l Δ M t' t : lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢ₚ[ lD ] ] ->
    [ G ; Γ ⊢ₚ[ lM ] t : tyCTyp Δ l @ lzero ] ->
    [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢ₚ[ lM ] M @ l' ] ->
    [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢ₚ[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] ->
    [ G ; Γ ⊢ₚ[ lM ] letboxT l' l Δ M t' t : M[lsingle t] @ l' ]
| pwf_letboxt G Γ l' l Δ T M t' t : lwf (gL G) l' -> lwf (gL G) l -> [ G ; Δ ⊢ₚ[ lD ] ] ->
    [ G ; Δ ⊢ₚ[ lD ] T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] t : tyCTrm Δ T l @ lzero ] ->
    [ G ; Γ ,, tyCTrm Δ T l @ lzero ⊢ₚ[ lM ] M @ l' ] ->
    [ gext G (gdTm Δ lC T l) ; Γ⟪S⟫ ⊢ₚ[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] ->
    [ G ; Γ ⊢ₚ[ lM ] letboxt l' l Δ T M t' t : M[lsingle t] @ l' ]
(* 04:1310: the groups G_M, G_Typ, G_Trm (branch scopes in RecSpec) *)
| pwf_elimT G Γ l1 l2 MT Mt bs l Δ t :
    lwf (gL G) l1 -> lwf (gL G) l2 ->
    [ recGT G ; recΓT Γ ⊢ₚ[ lM ] MT @ lvren l1 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢ₚ[ lM ] Mt @ lvren l2 (ush 1) ] ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢ₚ[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    lwf (gL G) l -> [ G ; Δ ⊢ₚ[ lD ] ] -> [ G ; Γ ⊢ₚ[ lM ] t : tyCTyp Δ l @ lzero ] ->
    [ G ; Γ ⊢ₚ[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t : motT (wrapMT MT) l Δ t @ l1 ]
| pwf_elimt G Γ l1 l2 MT Mt bs l Δ T t :
    lwf (gL G) l1 -> lwf (gL G) l2 ->
    [ recGT G ; recΓT Γ ⊢ₚ[ lM ] MT @ lvren l1 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢ₚ[ lM ] Mt @ lvren l2 (ush 1) ] ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢ₚ[ lM ]
                           bs k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    lwf (gL G) l -> [ G ; Δ ⊢ₚ[ lD ] ] -> [ G ; Δ ⊢ₚ[ lD ] T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] t : tyCTrm Δ T l @ lzero ] ->
    [ G ; Γ ⊢ₚ[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t : mott (wrapMt Mt) l Δ T t @ l2 ]

with peq_ty : gctx -> layer -> ctx -> ty -> ty -> lvl -> Prop :=
| peqty_sym G i Γ T T' l : [ G ; Γ ⊢ₚ[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢ₚ[ i ] T' ≅ T @ l ]
| peqty_trans G i Γ T T' T'' l : [ G ; Γ ⊢ₚ[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢ₚ[ i ] T' ≅ T'' @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] T ≅ T'' @ l ]
| peqty_nat G i Γ : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] -> [ G ; Γ ⊢ₚ[ i ] tyNat ≅ tyNat @ lzero ]
| peqty_pi G i Γ l1 l2 l3 l4 A A' B B' : i <> lV ->
    leqP (gL G) l1 l3 -> leqP (gL G) l2 l4 ->
    [ G ; Γ ⊢ₚ[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ₚ[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢ₚ[ i ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ]
| peqty_El G i Γ l l' t t' : i <> lV -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ i ] t ≅ t' : tyU l @ lsuc l ] -> [ G ; Γ ⊢ₚ[ i ] tyEl l t ≅ tyEl l' t' @ l ]
| peqty_U G i Γ l l' : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ i ] tyU l ≅ tyU l' @ lsuc l ]
| peqty_upi G Γ n l l' T T' : [ G ; Γ ⊢ₚ[ lM ] ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] T @ l ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] T ≅ T' @ l ] ->
    0 < n -> leqP (n + gL G) l l' ->
    [ G ; Γ ⊢ₚ[ lM ] tyUPi n l T ≅ tyUPi n l' T' @ lomega ]
| peqty_lconv G i Γ T T' l l' : [ G ; Γ ⊢ₚ[ i ] T ≅ T' @ l' ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ i ] T ≅ T' @ l ]
(* decoding (04:620), computation rules *)
| peqty_El_nat G i Γ : compt i -> [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    [ G ; Γ ⊢ₚ[ i ] tyNat ≅ tyEl lzero tmNat @ lzero ]
| peqty_El_U G i Γ l : compt i -> lwf (gL G) l -> [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    [ G ; Γ ⊢ₚ[ i ] tyU l ≅ tyEl (lsuc l) (tmU l) @ lsuc l ]
| peqty_El_pi G i Γ l l' s t : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢ₚ[ i ] s : tyU l @ lsuc l ] ->
    [ G ; Γ ,, tyEl l s @ l ⊢ₚ[ i ] t : tyU l' @ lsuc l' ] ->
    [ G ; Γ ⊢ₚ[ i ] tyPi l l' (tyEl l s) (tyEl l' t) ≅ tyEl (lmax l l') (tmPi l l' s t) @ lmax l l' ]
(* 04:1042 *)
| peqty_gvar G i Γ U Δ i' l d d' : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' i ->
    lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ₚ[ i ] llk d n : A[d] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ₚ[ i ] llk d' n : A[d'] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ₚ[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
    [ G ; Γ ⊢ₚ[ i ] tyGvar U d ≅ tyGvar U d' @ l ]
| peqty_cpi G Γ l l' T T' : [ G ; Γ ⊢ₚ[ lM ] ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢ₚ[ lM ] T ≅ T' @ l ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ lM ] tyCPi l T ≅ tyCPi l' T' @ l ]
| peqty_tpi G Γ Δ Δ' l1 l2 l3 l4 T T' : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢ₚ[ lM ] T ≅ T' @ l2 ] ->
    leqP (gL G) l1 l3 -> leqP (gL G) l2 l4 ->
    [ G ; Γ ⊢ₚ[ lM ] tyTPi Δ l1 l2 T ≅ tyTPi Δ' l3 l4 T' @ l2 ]
| peqty_CTyp G Γ Δ Δ' l l' : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ lM ] tyCTyp Δ l ≅ tyCTyp Δ' l' @ lzero ]
| peqty_CTrm G Γ Δ Δ' T T' l l' : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] ->
    [ G ; Δ ⊢ₚ[ lD ] T ≅ T' @ l ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ lM ] tyCTrm Δ T l ≅ tyCTrm Δ' T' l' @ lzero ]

with peq_tm : gctx -> layer -> ctx -> tm -> tm -> ty -> lvl -> Prop :=
| peqtm_sym G i Γ t t' T l : [ G ; Γ ⊢ₚ[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢ₚ[ i ] t' ≅ t : T @ l ]
| peqtm_trans G i Γ t t' t'' T l :
    [ G ; Γ ⊢ₚ[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢ₚ[ i ] t' ≅ t'' : T @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] t ≅ t'' : T @ l ]
| peqtm_var G i Γ n T l : [ G ; Γ ⊢ₚ[ typeof i ] ] -> in_ctx Γ n T l ->
    [ G ; Γ ⊢ₚ[ i ] var n ≅ var n : T @ l ]
| peqtm_code_nat G i Γ : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    [ G ; Γ ⊢ₚ[ i ] tmNat ≅ tmNat : tyU lzero @ lsuc lzero ]
| peqtm_code_pi G i Γ l1 l2 l3 l4 s s' t t' : i <> lV ->
    leqP (gL G) l1 l3 -> leqP (gL G) l2 l4 ->
    [ G ; Γ ⊢ₚ[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
    [ G ; Γ ,, tyEl l1 s @ l1 ⊢ₚ[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
    [ G ; Γ ⊢ₚ[ i ] tmPi l1 l2 s t ≅ tmPi l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ]
| peqtm_code_U G i Γ l l' : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ i ] tmU l ≅ tmU l' : tyU (lsuc l) @ lsuc (lsuc l) ]
| peqtm_zero G i Γ : i <> lV -> [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    [ G ; Γ ⊢ₚ[ i ] zero ≅ zero : tyNat @ lzero ]
| peqtm_succ G i Γ t t' : i <> lV -> [ G ; Γ ⊢ₚ[ i ] t ≅ t' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ₚ[ i ] succ t ≅ succ t' : tyNat @ lzero ]
| peqtm_natrec G i Γ l l' M M' s s' z z' t t' : i <> lV -> leqP (gL G) l l' ->
    [ G ; Γ ,, tyNat @ lzero ⊢ₚ[ i ] M ≅ M' @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] s ≅ s' : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢ₚ[ i ] z ≅ z' : M[lsucc] @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] t ≅ t' : tyNat @ lzero ] ->
    [ G ; Γ ⊢ₚ[ i ] natrec l M s z t ≅ natrec l' M' s' z' t' : M[lsingle t] @ l ]
| peqtm_lam G i Γ l1 l2 l3 l4 A A' B t t' : i <> lV ->
    leqP (gL G) l1 l3 -> leqP (gL G) l2 l4 ->
    [ G ; Γ ⊢ₚ[ i ] A @ l1 ] -> [ G ; Γ ⊢ₚ[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ₚ[ i ] t ≅ t' : B @ l2 ] ->
    [ G ; Γ ⊢ₚ[ i ] lam l1 l2 A t ≅ lam l3 l4 A' t' : tyPi l1 l2 A B @ lmax l1 l2 ]
| peqtm_app G i Γ l1 l2 l3 l4 A A' B B' t t' s s' : i <> lV ->
    leqP (gL G) l1 l3 -> leqP (gL G) l2 l4 ->
    [ G ; Γ ⊢ₚ[ i ] A @ l1 ] -> [ G ; Γ ⊢ₚ[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢ₚ[ i ] B ≅ B' @ l2 ] ->
    [ G ; Γ ⊢ₚ[ i ] t ≅ t' : tyPi l1 l2 A B @ lmax l1 l2 ] ->
    [ G ; Γ ⊢ₚ[ i ] s ≅ s' : A @ l1 ] ->
    [ G ; Γ ⊢ₚ[ i ] app t l1 l2 A B s ≅ app t' l3 l4 A' B' s' : B[lsingle s] @ l2 ]
| peqtm_ulam G Γ n l l' T T' t t' : [ G ; Γ ⊢ₚ[ lM ] ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] T ≅ T' @ l ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] t ≅ t' : T @ l ] ->
    0 < n -> leqP (n + gL G) l l' ->
    [ G ; Γ ⊢ₚ[ lM ] ulam n l T t ≅ ulam n l' T' t' : tyUPi n l T @ lomega ]
| peqtm_uapp G Γ n l T t t' ls ls' : [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] t ≅ t' : tyUPi n l T @ lomega ] ->
    length ls = n -> 0 < n -> Forall2 (leqP (gL G)) ls ls' ->
    [ G ; Γ ⊢ₚ[ lM ] uapp t ls ≅ uapp t' ls' : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ]
| peqtm_conv G i Γ t t' T T' l : [ G ; Γ ⊢ₚ[ i ] t ≅ t' : T' @ l ] ->
    [ G ; Γ ⊢ₚ[ typeof i ] T ≅ T' @ l ] -> [ G ; Γ ⊢ₚ[ i ] t ≅ t' : T @ l ]
| peqtm_lconv G i Γ t t' T l l' : [ G ; Γ ⊢ₚ[ i ] t ≅ t' : T @ l' ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ i ] t ≅ t' : T @ l ]
(* 04:1360 *)
| peqtm_gvar G i Γ u Δ i' T l d d' : [ G ; Γ ⊢ₚ[ typeof i ] ] ->
    in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i ->
    lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ₚ[ i ] llk d n : A[d] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ₚ[ i ] llk d' n : A[d'] @ k ]) ->
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢ₚ[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
    [ G ; Γ ⊢ₚ[ i ] gvar u d ≅ gvar u d' : T[d] @ l ]
| peqtm_clam G Γ l l' T T' t t' : [ G ; Γ ⊢ₚ[ lM ] ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢ₚ[ lM ] T ≅ T' @ l ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢ₚ[ lM ] t ≅ t' : T @ l ] -> leqP (gL G) l l' ->
    [ G ; Γ ⊢ₚ[ lM ] clam l T t ≅ clam l' T' t' : tyCPi l T @ l ]
| peqtm_capp G Γ l T t t' Δ Δ' : [ G ; Γ ⊢ₚ[ lM ] t ≅ t' : tyCPi l T @ l ] ->
    [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] ->
    [ G ; Γ ⊢ₚ[ lM ] capp t Δ ≅ capp t' Δ' : T⦃gsingle (GCtx Δ)⦄ @ l ]
| peqtm_tlam G Γ Δ Δ' l1 l2 l3 l4 T T' t t' : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢ₚ[ lM ] T ≅ T' @ l2 ] ->
    [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢ₚ[ lM ] t ≅ t' : T @ l2 ] ->
    leqP (gL G) l1 l3 -> leqP (gL G) l2 l4 ->
    [ G ; Γ ⊢ₚ[ lM ] tlam Δ l1 l2 T t ≅ tlam Δ' l3 l4 T' t' : tyTPi Δ l1 l2 T @ l2 ]
| peqtm_tapp G Γ Δ l l' T t t' A A' : [ G ; Γ ⊢ₚ[ lM ] t ≅ t' : tyTPi Δ l l' T @ l' ] ->
    [ G ; Δ ⊢ₚ[ lD ] A ≅ A' @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] tapp t A ≅ tapp t' A' : T⦃gsingle (GTy A)⦄ @ l' ]
(* 04:1383 *)
| peqtm_boxT G Γ Δ T T' l : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ; Δ ⊢ₚ[ lC ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] boxT T ≅ boxT T' : tyCTyp Δ l @ lzero ]
| peqtm_boxt G Γ Δ t t' T l : [ G ; Γ ⊢ₚ[ lM ] ] -> [ G ; Δ ⊢ₚ[ lC ] t ≅ t' : T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] boxt t ≅ boxt t' : tyCTrm Δ T l @ lzero ]
| peqtm_letboxT G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 t t0 : [ G ; Γ ⊢ₚ[ lM ] ] ->
    leqP (gL G) l1 l3 -> leqP (gL G) l2 l4 -> [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] ->
    [ G ; Γ ⊢ₚ[ lM ] t ≅ t0 : tyCTyp Δ l2 @ lzero ] ->
    [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢ₚ[ lM ] M ≅ M' @ l1 ] ->
    [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢ₚ[ lM ] t1 ≅ t2
        : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ] ->
    [ G ; Γ ⊢ₚ[ lM ] letboxT l1 l2 Δ M t1 t ≅ letboxT l3 l4 Δ' M' t2 t0 : M[lsingle t] @ l1 ]
| peqtm_letboxt G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 t t0 : [ G ; Γ ⊢ₚ[ lM ] ] ->
    leqP (gL G) l1 l3 -> leqP (gL G) l2 l4 -> [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] ->
    [ G ; Δ ⊢ₚ[ lD ] T ≅ T' @ l2 ] ->
    [ G ; Γ ⊢ₚ[ lM ] t ≅ t0 : tyCTrm Δ T l2 @ lzero ] ->
    [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢ₚ[ lM ] M ≅ M' @ l1 ] ->
    [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢ₚ[ lM ] t1 ≅ t2
        : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ] ->
    [ G ; Γ ⊢ₚ[ lM ] letboxt l1 l2 Δ T M t1 t ≅ letboxt l3 l4 Δ' T' M' t2 t0 : M[lsingle t] @ l1 ]
(* the recursors' congruences (unwritten, 04:1412): every component *)
| peqtm_elimT G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' t t' :
    leqP (gL G) l1 l1' -> leqP (gL G) l2 l2' ->
    [ recGT G ; recΓT Γ ⊢ₚ[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢ₚ[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢ₚ[ lM ]
                           bs k ≅ bs' k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    leqP (gL G) l l' -> [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] ->
    [ G ; Γ ⊢ₚ[ lM ] t ≅ t' : tyCTyp Δ l @ lzero ] ->
    [ G ; Γ ⊢ₚ[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t ≅ elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' t'
                  : motT (wrapMT MT) l Δ t @ l1 ]
| peqtm_elimt G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' t t' :
    leqP (gL G) l1 l1' -> leqP (gL G) l2 l2' ->
    [ recGT G ; recΓT Γ ⊢ₚ[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
    [ recGt G ; recΓt Γ ⊢ₚ[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
    (forall k, k < 13 -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢ₚ[ lM ]
                           bs k ≅ bs' k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
    leqP (gL G) l l' -> [ G ⊢ₚ[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢ₚ[ lD ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] t ≅ t' : tyCTrm Δ T l @ lzero ] ->
    [ G ; Γ ⊢ₚ[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t ≅ elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' t'
                  : mott (wrapMt Mt) l Δ T t @ l2 ]
(* computation rules (04:1414) *)
| peqtm_natrec_zero G i Γ l M s z : compt i -> lwf (gL G) l ->
    [ G ; Γ ,, tyNat @ lzero ⊢ₚ[ i ] M @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] s : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢ₚ[ i ] z : M[lsucc] @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] s ≅ natrec l M s z zero : M[lsingle zero] @ l ]
| peqtm_natrec_succ G i Γ l M s z t : compt i -> lwf (gL G) l ->
    [ G ; Γ ,, tyNat @ lzero ⊢ₚ[ i ] M @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] s : M[lsingle zero] @ l ] ->
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢ₚ[ i ] z : M[lsucc] @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] t : tyNat @ lzero ] ->
    [ G ; Γ ⊢ₚ[ i ] z[lsingle2 t (natrec l M s z t)] ≅ natrec l M s z (succ t)
                  : M[lsingle (succ t)] @ l ]
| peqtm_beta G i Γ l l' A B t s : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢ₚ[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢ₚ[ i ] B @ l' ] ->
    [ G ; Γ ,, A @ l ⊢ₚ[ i ] t : B @ l' ] -> [ G ; Γ ⊢ₚ[ i ] s : A @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] t[lsingle s] ≅ app (lam l l' A t) l l' A B s : B[lsingle s] @ l' ]
| peqtm_eta G i Γ l l' A B t : compt i -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Γ ⊢ₚ[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢ₚ[ i ] B @ l' ] ->
    [ G ; Γ ⊢ₚ[ i ] t : tyPi l l' A B @ lmax l l' ] ->
    [ G ; Γ ⊢ₚ[ i ] lam l l' A (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) ≅ t
                  : tyPi l l' A B @ lmax l l' ]
| peqtm_ubeta G Γ n l T t ls : [ G ; Γ ⊢ₚ[ lM ] ] ->
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢ₚ[ lM ] t : T @ l ] -> lwf (n + gL G) l ->
    length ls = n -> 0 < n -> Forall (lwf (gL G)) ls ->
    [ G ; Γ ⊢ₚ[ lM ] t[uext ls lvar]ᵤ ≅ uapp (ulam n l T t) ls
                  : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ]
| peqtm_ueta G Γ n l T t : [ G ; Γ ⊢ₚ[ lM ] t : tyUPi n l T @ lomega ] ->
    [ G ; Γ ⊢ₚ[ lM ] ulam n l T (uapp t⟨ush n⟩ᵤ (ubvars n)) ≅ t : tyUPi n l T @ lomega ]
| peqtm_cbeta G Γ l T t Δ : [ G ; Γ ⊢ₚ[ lM ] ] ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢ₚ[ lM ] t : T @ l ] -> lwf (gL G) l -> [ G ; Δ ⊢ₚ[ lD ] ] ->
    [ G ; Γ ⊢ₚ[ lM ] t⦃gsingle (GCtx Δ)⦄ ≅ capp (clam l T t) Δ : T⦃gsingle (GCtx Δ)⦄ @ l ]
| peqtm_ceta G Γ l T t : [ G ; Γ ⊢ₚ[ lM ] t : tyCPi l T @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] clam l T (capp t⟪S⟫ (cvar 0)) ≅ t : tyCPi l T @ l ]
| peqtm_tbeta G Γ Δ l l' T t A : [ G ; Γ ⊢ₚ[ lM ] ] ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢ₚ[ lM ] t : T @ l' ] -> lwf (gL G) l -> lwf (gL G) l' ->
    [ G ; Δ ⊢ₚ[ lD ] A @ l ] ->
    [ G ; Γ ⊢ₚ[ lM ] t⦃gsingle (GTy A)⦄ ≅ tapp (tlam Δ l l' T t) A : T⦃gsingle (GTy A)⦄ @ l' ]
| peqtm_teta G Γ Δ l l' T t : [ G ; Γ ⊢ₚ[ lM ] t : tyTPi Δ l l' T @ l' ] ->
    [ G ; Γ ⊢ₚ[ lM ] tlam Δ l l' T (tapp t⟪S⟫ (tyGvar 0 (lshift 0))) ≅ t : tyTPi Δ l l' T @ l' ]
| peqtm_letboxT_beta G Γ l' l Δ M t' T : [ G ; Γ ⊢ₚ[ lM ] ] -> lwf (gL G) l' -> lwf (gL G) l ->
    [ G ; Δ ⊢ₚ[ lD ] ] -> [ G ; Δ ⊢ₚ[ lC ] T @ l ] ->
    [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢ₚ[ lM ] M @ l' ] ->
    [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢ₚ[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] ->
    [ G ; Γ ⊢ₚ[ lM ] t'⦃gsingle (GTy T)⦄ ≅ letboxT l' l Δ M t' (boxT T) : M[lsingle (boxT T)] @ l' ]
| peqtm_letboxt_beta G Γ l' l Δ T M t' t : [ G ; Γ ⊢ₚ[ lM ] ] -> lwf (gL G) l' -> lwf (gL G) l ->
    [ G ; Δ ⊢ₚ[ lD ] ] -> [ G ; Δ ⊢ₚ[ lD ] T @ l ] -> [ G ; Δ ⊢ₚ[ lC ] t : T @ l ] ->
    [ G ; Γ ,, tyCTrm Δ T l @ lzero ⊢ₚ[ lM ] M @ l' ] ->
    [ gext G (gdTm Δ lC T l) ; Γ⟪S⟫ ⊢ₚ[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] ->
    [ G ; Γ ⊢ₚ[ lM ] t'⦃gsingle (GTm t)⦄ ≅ letboxt l' l Δ T M t' (boxt t) : M[lsingle (boxt t)] @ l' ]
(* the recursors' β (04:1480, selectively listed there): the redex typed
   by the recursor rule (G_A, the scrutinee), its reduct by [redT]/[redt] *)
| peqtm_elimT_beta G Γ l1 l2 rb l Δ c T k r :
    [ G ; Γ ⊢ₚ[ lM ] elimT l1 l2 rb l Δ (boxT c) : T @ k ] -> redT l1 l2 rb l Δ c = Some r ->
    [ G ; Γ ⊢ₚ[ lM ] r ≅ elimT l1 l2 rb l Δ (boxT c) : T @ k ]
| peqtm_elimt_beta G Γ l1 l2 rb l Δ T0 c T k r :
    [ G ; Γ ⊢ₚ[ lM ] elimt l1 l2 rb l Δ T0 (boxt c) : T @ k ] -> redt l1 l2 rb l Δ T0 c = Some r ->
    [ G ; Γ ⊢ₚ[ lM ] r ≅ elimt l1 l2 rb l Δ T0 (boxt c) : T @ k ]

(* 04:520: both sides typed and equal in both contexts *)
with peq_ctx : gctx -> layer -> ctx -> ctx -> Prop :=
| peqc_nil G i : [ ⊢ₚ G ] -> [ G ⊢ₚ[ i ] cnil ≅ cnil ]
| peqc_var G i g : [ ⊢ₚ G ] -> gctx_var G g -> [ G ⊢ₚ[ i ] cvar g ≅ cvar g ]
| peqc_ext G i Γ Δ T T' l l' : [ G ⊢ₚ[ i ] Γ ≅ Δ ] ->
    [ G ; Γ ⊢ₚ[ i ] T ≅ T' @ l ] -> [ G ; Δ ⊢ₚ[ i ] T ≅ T' @ l ] ->
    [ G ; Γ ⊢ₚ[ i ] T @ l ] -> [ G ; Δ ⊢ₚ[ i ] T' @ l' ] -> leqP (gL G) l l' ->
    [ G ⊢ₚ[ i ] Γ ,, T @ l ≅ Δ ,, T' @ l' ]

where "[ ⊢ₚ G ]" := (pwf_glob G)
  and "[ G ; Γ ⊢ₚ[ i ] ]" := (pwf_ctx G i Γ)
  and "[ G ; Γ ⊢ₚ[ i ] T @ l ]" := (pwf_ty G i Γ T l)
  and "[ G ; Γ ⊢ₚ[ i ] t : T @ l ]" := (pwf_tm G i Γ t T l)
  and "[ G ; Γ ⊢ₚ[ i ] T ≅ T' @ l ]" := (peq_ty G i Γ T T' l)
  and "[ G ; Γ ⊢ₚ[ i ] t ≅ t' : T @ l ]" := (peq_tm G i Γ t t' T l)
  and "[ G ⊢ₚ[ i ] Γ ≅ Γ' ]" := (peq_ctx G i Γ Γ').

Scheme pwf_glob_mut := Induction for pwf_glob Sort Prop
  with pwf_ctx_mut := Induction for pwf_ctx Sort Prop
  with pwf_ty_mut := Induction for pwf_ty Sort Prop
  with pwf_tm_mut := Induction for pwf_tm Sort Prop
  with peq_ty_mut := Induction for peq_ty Sort Prop
  with peq_tm_mut := Induction for peq_tm Sort Prop
  with peq_ctx_mut := Induction for peq_ctx Sort Prop.
Combined Scheme ptyping_mut from pwf_glob_mut, pwf_ctx_mut, pwf_ty_mut, pwf_tm_mut, peq_ty_mut,
  peq_tm_mut, peq_ctx_mut.
