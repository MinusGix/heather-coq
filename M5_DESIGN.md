# Milestone 5 (the planned M2b): meta-functions `CΠ` and `TΠ`

Goal: extend M4 with the meta-functions over local contexts and over
layer-P types. That means `CΠ g. T` / `Λg. t` / `t Δ` and
`TΠ U[Δ]. T` / `ΛU. t` / `t T`, with their β and η rules, two new cases
of the relation at `j = M`, and the FT at M with the new rules.

Paper references: 04:810–900 (syntax), 04:1020–1035 (formation),
04:1058–1066 (type congruence), 04:1080–1096 (typing), 04:1365–1380
(congruence), 04:1470–1485 (β, η), 05:25–26, 05:51–54, 05:123–146,
05:228–264 (the operations), 06:21–33, 06:77–79, 06:114–118 (whnf,
reduction), 06:434–438, 06:518–523, 06:590–595 (algorithmic conversion),
07:296–350 (generic laws), 07a:766–845 (the relation), 07b:1552–1630
(the semantic rules), 08:33–36 (injectivity).

## Scope

| Stage | Contents |
|---|---|
| **M5** (this doc) | `CΠ`/`TΠ` (syntax, operations, typing, metatheory), their relation cases, the semantic rules, the FT at M, consequences |

## Observations that shape the design

- **Both are M-only and live at a well-formed level.** `CΠ g. T` lives
  at the level `l` of `T`. `TΠ U[Δ]. T` lives at the level `l'` of `T`,
  whatever the level `l` of `U`. Neither is code, so no recursor inspects
  them, and the C and P layers (`static_code`, `FundamentalS`) are
  vacuous on the new rules.
- **The relation cases recurse at the same stage.** The instances
  `T[Δ/g]` and `T[T₂/U]` are at the type's own level, so the recursive
  occurrences are positive and at stage `n`, as for Π's codomain. The
  domains are the `j = P` relation, which the `jM` relation already has as
  its parameters: `vp_ctx` (for `Δ ≈ Δ'`) and `vp_ty` (for
  `T₂ ≈ T₂' @ l`). The level of `U` never enters the stage: that is the
  paper's remark that meta-functions over open types need not care about
  the types' levels (04:1044).
- **Unlike ω, these are real constructors of `LR`.** `CΠ` and `TΠ` can
  be Π domains, universe elements (at M), and instances of `UΠ`, so the
  relation must be able to see them at every stage (M2_DESIGN.md scope
  table).
- **The global-substitution machinery is already general.** `gobj` has
  context and type images (`GCtx`, `GTy`), `gsingle` builds `Δ/g` and
  `T₂/U`, the substitution lemma handles context variables sent to
  contexts (M3 E9, "tail expansion"), and related global substitutions
  already relate `U : DTyp^P` images by P-validity (`GObjRel`). Global
  bindings `gdTy Δ lD l` are already well-formed (`wfg_ty`).
- **The arguments live in their own scopes.** In `t Δ` and `t T`, `Δ` is a
  context and `T` is a type in `Δ`, not in the ambient `Γ`. Local
  operations leave them alone (05:144, 05:146), as for `box`.

## Decisions

### G1. Syntax: as in the paper, annotations only where the paper has them

- New `ty`: `tyCPi (l : lvl) (T : ty)` (`T` binds one global variable,
  a context variable), and `tyTPi (Δ : ctx) (l l' : lvl) (T : ty)` (`T`
  binds one global variable, `U : (Δ ⊢_P @l)`; `Δ` is outside the
  binder).
- New `tm`: `clam (l : lvl) (t : tm)`, `capp (t : tm) (Δ : ctx)`,
  `tlam (l l' : lvl) (t : tm)`, `tapp (t : tm) (T : ty)`. `t` binds one
  global variable in `clam`/`tlam`. As in the paper, `tlam` does not
  carry `Δ`, and the applications carry no type annotations (they are not
  code, M4 F1).
- Operations:
  - local renaming passes under the global binder unchanged;
  - local substitution passes as `gwk d` (as for `letbox`'s body);
  - both leave `Δ` and the `tapp` argument alone;
  - global renaming and substitution go under the binder with
    `gupr`/`gup`, and act on `Δ` and the `tapp` argument;
  - universe renaming and substitution act everywhere.
- Instantiation: `T[Δ/g] := T⦃gsingle (GCtx Δ)⦄`,
  `T[T₂/U] := T⦃gsingle (GTy T₂)⦄`. The identity instance of `U` is
  `U^id := tyGvar 0 (lshift 0)`, in the scope `Δ⟪S⟫`.
- Untyped reduction: `capp (clam l t) Δ ⤳ t[Δ/g]`,
  `tapp (tlam l l' t) T ⤳ t[T/U]`, and the congruences in the head.
  `clam`/`tlam` and `tyCPi`/`tyTPi` are whnf. `capp ν Δ` and `tapp ν T`
  are neutral.

### G2. Typing: sixteen M-only rules

With `G_g := gext G gdCtx` and `G_U := gext G (gdTy Δ lD l)`, the body
scope is `G_•; Γ⟪S⟫`. The rules, all at `lM`, follow 04 and carry the
presuppositions the metatheory needs before substitution (M3 E10, as the
UΠ rules do):

- `wft_cpi`: `⊢ Γ`, `lwf l`, `[G_g; Γ⟪S⟫ ⊢ T @ l]` ⇒
  `[G; Γ ⊢ tyCPi l T @ l]`.
- `wft_tpi`: `⊢ Γ`, `[G; Δ ⊢_D]`, `lwf l`, `lwf l'`,
  `[G_U; Γ⟪S⟫ ⊢ T @ l']` ⇒ `[G; Γ ⊢ tyTPi Δ l l' T @ l']`.
- `eqty_cpi`, `eqty_tpi`: the congruences (`Δ ≅ Δ'` at D, `lequiv` for
  the annotations).
- `wf_clam`, `wf_tlam`: body typed at `G_•; Γ⟪S⟫`.
- `wf_capp`: `[G_g; Γ⟪S⟫ ⊢ T @ l]`, `t : tyCPi l T @ l`, `[G; Δ ⊢_D]` ⇒
  `capp t Δ : T[Δ/g] @ l`.
- `wf_tapp`: `[G_U; Γ⟪S⟫ ⊢ T' @ l']`, `t : tyTPi Δ l l' T' @ l'`,
  `[G; Δ ⊢_D T @ l]` ⇒ `tapp t T : T'[T/U] @ l'`.
- `eqtm_clam`, `eqtm_capp`, `eqtm_tlam`, `eqtm_tapp`: congruences.
- `eqtm_cbeta`, `eqtm_tbeta`: `capp (clam l t) Δ ≅ t[Δ/g]`,
  `tapp (tlam l l' t) T ≅ t[T/U]`.
- `eqtm_ceta`: `clam l (capp t⟪S⟫ (cvar 0)) ≅ t : tyCPi l T`.
- `eqtm_teta`: `tlam l l' (tapp t⟪S⟫ U^id) ≅ t : tyTPi Δ l l' T`.

Metatheory: every typing lemma gains these cases, in the pattern of
`letbox`'s global binder. That covers weakening, global weakening,
local/global/universe substitution, universe permutation, context
conversion, presupposition, static code, typed deep normal forms,
typed reduction, lifting and functionality.

Premises beyond the paper's (implemented). Each is admissible there and
follows M3 E10: rules carry what the metatheory needs before the global
substitution lemma exists, since `Functionality` precedes
`GSubstitution`.
- `wf_capp`, `wf_tapp`: the result type `T[Δ/g]` / `T[A/U]` is
  well-formed.
- `eqtm_capp`, `eqtm_tapp`: the instance equation
  `T[Δ/g] ≅ T[Δ'/g]` / `T[A/U] ≅ T[A'/U]`. The paper derives it by
  functionality of global substitutions, which we do not have.
- `eqty_tpi`: the right body `T'` at `U : (Δ' ⊢_P @l3)`. `eqtm_tlam`:
  the right body (type and term) at `U : (Δ ⊢_P @l3)`. Moving a body
  between equal bindings would need a global-context conversion lemma;
  `letbox` avoids it the same way.
- `wf_tapp`, `eqtm_tapp` list the function's typing first. It fixes `U`'s
  level, which is absent from the conclusion, so `eapply … ; eauto` picks
  the right one.

Supporting facts (implemented):
- `Typing/MInst.v`: instantiation of a body at `Δ/g` or `A/U` (the global
  substitution lemma at `gsingle`), the η identities, and the
  presuppositions of the new rules.
- The η body's type is `T⟪⇑S⟫[g/g]` (resp. `[U^id/U]`). It equals `T` on
  typed `T` by `GStatic.equiv_gsubst`, whose `obj_equiv` now also relates
  `GId j` and `GCtx (cvar j)` at a context binding.

### G3. The relation: `LRcpi` and `LRtpi` at `j = M`

Instances under a Kripke world `ρ` (global weakening `γ`, then local
renaming `r`). The body is moved under the binder, then instantiated:
`kbody ρ T := T⟦gwk_up γ⟧⟨r⟩`.

```
CPiRel G Γ l1 T1 l2 T1' instR : tm -> tm -> Prop :=
  t, t' reduce to whnfs w, w' at both CΠ types, w ≈ w' at both, and
  ∀ ρ Δ Δ' (h : vp_ctx (kw_G ρ) Δ Δ'),
    instR ρ Δ Δ' h (capp (ktm ρ w) Δ) (capp (ktm ρ w') Δ')

LRcpi: lr_j = jM, l ≡ l1, l2 ≡ l1, lwf l1,
  T ⤳* tyCPi l1 T1 @ l, T' ⤳* tyCPi l2 T1' @ l,
  T1, T1' well-formed at G_g; Γ⟪S⟫,
  tyCPi l1 T1 ≈ tyCPi l2 T1' @ l1,
  ∀ ρ Δ Δ' h, LR n rec (kw_G ρ) (kw_Δ ρ)
                (kbody ρ T1)[Δ/g] (kbody ρ T1')[Δ'/g] l1 (instR ρ Δ Δ' h),
  releq R (CPiRel …)
```

`LRtpi` is the same with `tyTPi Δ1 l1 l2 T1` / `tyTPi Δ1' l3 l4 T1'`,
`vp_ctx G Δ1 Δ1'`, and instances over
`h : vp_ty (kw_G ρ) Δ1⟦γ⟧ T2 T2' l1`, at `(kbody ρ T1)[T2/U]` and
`(kbody ρ T1')[T2'/U]`, level `l2`. Its term relation uses `tapp`.

**One-sided domains, not the paper's E₁/E₂.** The paper's `TΠ` case
carries two symmetric instance families (07a:808–815) so that symmetry is
immediate. We quantify over the left context `Δ1` only, as `LRpi`
quantifies over one domain relation. Symmetry flips the argument
(`vpl_ty_sym`), moves it to `Δ1` (`vpl_ty_ctx` along `vp_ctx`), and
applies the induction hypothesis. This is the Π pattern, and it keeps
one family per case.

**Escape** is direct. The case carries the whole type's generic
equality, and `CPiRel`/`TPiRel` carry `w ≈ w'` (as M4's ω tier does).
The body equalities come from the instance at the growth world. For
injectivity (G6) the world is `gwk_step gwk_id` into `G_g` with
`Δ = Δ' = cvar 0`; that instance is the body itself.

**Neutral reflection** needs `capp ν Δ ~ capp ν' Δ'` for vp-related
contexts, and likewise for `tapp`. The laws (G4) take P-generic
premises, but `LR` knows only the parameter. A class over `(E, vp)`
bridges the two:

```
Class VPNe (vp : VParam) := {
  vpn_capp : lr_j = jM -> ν ~ ν' : tyCPi l T @ l -> vp_ctx vp G Δ Δ' ->
             capp ν Δ ~ capp ν' Δ' : T[Δ/g] @ l ;
  vpn_tapp : … vp_ty vp G Δ T2 T2' l -> tapp ν T2 ~ tapp ν' T2' : T''[T2/U] @ l' }
```

It holds vacuously at `jP`. At `jM` it follows from `GenericEqM` and the
escape of `vpM`'s P-validity (`CtxRel_escape`, the P FT's escape).

The other properties need no new parameter laws. They use `VPLaws`
(sym/trans/ctx conversion/level conversion/`≡ₗ`/global weakening) and
`VPPerm`:
- irrelevance, symmetry, transitivity;
- Kripke weakening (worlds compose; `vpl_*_gwk` moves the domains);
- anti-reduction, escape, level invariance;
- permutations: `vpp_ctx`, `vpp_ty`;
- layering: the cases are `jM` only.

### G4. Generic laws

Added to `GenericEqM` (07:299–350):
- `geq_ty_cpi`, `geq_ty_tpi`: the congruences (the `TΠ` domain context by
  `geq_ctx EP`);
- `geq_tm_cext`, `geq_tm_text`: extensionality at the bound variable
  (`capp t⟪S⟫ (cvar 0)`, `tapp t⟪S⟫ U^id`);
- `gne_tm_capp` (`geq_ctx EP Δ Δ'`), `gne_tm_tapp` (`geq_ty EP` in `Δ`).

The declarative instance proves extensionality by η, as for `UΠ`.

### G5. Semantic rules and the FT at M (07b:1552–1630)

- **Formation and congruence:** the instance at `ρ` and `Δ, Δ'` (or
  `T2, T2'`) is the body's validity at the extended related global
  substitutions `(σ⟦γ⟧, Δ/g)` and `(σ'⟦γ⟧, Δ'/g)`. `vp_ctx`/`vp_ty` are
  exactly `GObjRel`'s image condition for `gdCtx`/`gdTy _ lD _`. The
  syntactic side is the commutation of `kbody`, `gup σ`, `gwk δ` and the
  single substitution.
- **`Λ` and its congruence:** likewise. The whnf equality comes from
  extensionality (`geq_tm_cext`/`geq_tm_text`) at the growth instance.
- **Application and its congruence:** instantiate the term relation at
  the identity world.
- **β:** anti-reduction to the body's instance. **η:** at every
  instance, `capp (clam l (capp t⟪S⟫ (cvar 0))) Δ` β-reduces to
  `capp t Δ`, which the validity of `t` relates.
- The FT's two-part motive is unchanged. The new rules conclude at a
  well-formed level, so their ω half is absurd (`w_absurd`).

### G6. Consequences (08:33–36)

- normalization at the new types;
- injectivity: `tyCPi l T ≅ tyCPi l' T'` gives `l ≡ l'` and `T ≅ T'` at
  `G_g; Γ⟪S⟫`; `tyTPi` also gives `Δ ≅ Δ'` at D;
- discrimination of `CΠ`/`TΠ` against the other type formers.

The existing consequences keep their statements.

## Order of work

1. Syntax (G1): constructors, every operation and law, `≡ₗ`, deep
   normal forms, whnf and neutral forms, untyped reduction.
2. Typing (G2): the sixteen rules and every metatheory lemma.
3. Generic laws (G4) and the declarative instance.
4. The relation (G3): the two cases, `VPNe`, and every `LR` property.
5. Semantic rules and the FT at M (G5).
6. Consequences (G6), README, agent notes.

## Gotchas known up front

- `tapp`'s argument is a type in `Δ`. It is not in `Γ`, so no local
  operation touches it, but global ones do.
- The binder is global, so under it the local context is `Γ⟪S⟫`, and a
  local substitution is `gwk d`, not `d`.
- `TΠ`'s level is `l'` (the body's), not `lmax l l'`.

## Status

In progress.
- Step 1 (syntax) done.
- Step 2 (typing and metatheory) done. The FT at M admits its `CΠ`/`TΠ`
  cases, flagged in `fundamentalM_us`, until step 5. Nothing else is
  admitted.
