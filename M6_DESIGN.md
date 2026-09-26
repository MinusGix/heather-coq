# Milestone 6: algorithmic convertibility and its decidability

Goal: the paper's second instantiation of the generic equivalence. That is
the convertibility-checking judgments, their soundness and completeness
with respect to declarative equality, and the decidability of convertibility
of well-typed types and terms at the computing layers D and M. With M1–M5
this completes the paper's development. The user's extensions (more layers,
2D structure, local computation rules) come after it.

Paper references: 06:351–723 (the judgments, soundness), 08:73–372 (the
instance, the conversion lemma, PER, convertibility, decidability). The
proof follows Abel, Öhman and Vezzosi 2017, as does logrel-coq's
`AlgorithmicConvProperties`/`Decidability`.

## Scope

| Stage | Contents |
|---|---|
| **M6** (this doc) | decision procedure for `lequiv`/`≡ₗ`; the algorithmic judgments at D and M; soundness; the algorithmic instance of `GenericEqLaws` (D and M) and `GenericEqM`; completeness via the FT and escape; decidability |
| later | the user's extensions |

## Decisions

### H1. Decidability is stated in `Prop`

The theorem is `A \/ ~A` for the algorithmic (equivalently the
declarative) judgment, proved constructively with no axioms beyond the
design's. The proof goes by induction on reflexive algorithmic derivations
(08:236), which live in `Prop`, so a `sumbool` would need `Type`-valued
derivations throughout. An executable checker (logrel-coq's fuel-based one)
is a possible follow-up, not part of M6.

### H2. One family of judgments, with neither layer nor level

The paper's nine judgments are one mutual inductive, `ac_* G Γ …`, with
the paper's names:

| Coq | paper | meaning |
|---|---|---|
| `ac_ty` | `⊢ T ⇔ T'` | types (reduce to whnf, then compare) |
| `ac_tynf` | `⊢ W ⇔nf W'` | whnf types |
| `ac_tyne` | `⊢ V ⇔ne V'` | neutral types |
| `ac_ctx` | `⊢ Γ ⇔ Δ` | local contexts (pairwise) |
| `ac_tm` | `⊢ t ⇔ t' : T` | terms (reduce type and terms, compare) |
| `ac_tmnf` | `⊢ w ⇔nf w' : W` | whnf terms at a whnf type |
| `ac_tmne` | `⊢ ν ⇔ne ν' ▷ T` | neutral terms, type inferred |
| `ac_tmnee` | `⊢ ν ⇔ne ν' ▷ W` | neutral terms, inferred type reduced |
| `ac_sub` | `⊢ δ ⇔ δ' : Δ` | local substitutions (pointwise) |

The `ac_` prefix avoids the existing `conv_tm` (Escape.v).

The judgments carry no layer and no level. The instances bundle
declarative typing at their layer and level (H4), so:

- level annotations are compared with the semantic `leqv`, which agrees
  with `lequiv (gL G)` on well-formed levels (bundled typing gives
  well-formedness). No level-conversion rules are needed, so derivations
  are syntax-directed;
- a layer-M rule never fires on inputs typed at D: typing inversion at D
  rules the head out.

The algorithm keeps `G` and `Γ` for the inferred types of variables and
global variables. Binders extend them as the typing rules do (`Γ ,, A @ l`,
`gctx_uwk n G`/`Γ⟨ush n⟩ᵤ`, `gext G _`/`Γ⟪S⟫`).

Other departures from the paper's rules (06:381–700):

- the reductions are untyped, and their targets are required to be whnf;
- neutral terms reach `⇔nf` only at a *positive* whnf type (`Nat`, `U`,
  a neutral type, `CTyp`, `CTrm`). The paper forgets `U`. At function
  types (`Π`, `UΠ`, `CΠ`, `TΠ`) only the η rule applies;
- where the paper checks the inferred type of a neutral head against a
  fixed shape (`El`, `app`, `natrec`, `letbox`, the recursors), the rule
  ignores it (as the paper says for `app`). Soundness gets the right type
  from the bundled typing and neutral type uniqueness (H7). `uapp`,
  `capp` and `tapp` read their result type from the inferred `UΠ`/`CΠ`/`TΠ`;
- `succ` compares its argument with `⇔`, not `⇔nf` (06:447 is a typo);
- `ac_sub` is pointwise over `in_ctx Δ`. The tails of two typed
  substitutions between the same contexts agree (`lsub_tail`), so the
  entries suffice. The premise `forall n A k, in_ctx Δ n A k -> ac_tm …`
  is strictly positive, and Δ is finite, so decidability is unaffected.

### H3. Levels up to `leqv`, boxes up to `≡ₗ`

`leqv` is semantic (equal evaluation under every valuation), so M6 needs a
decision procedure. A level evaluates to `max(c, max_x (v x + k_x))` with
`c` its value at the zero valuation and `k_x` the offset of the variable
`x` (`leval_split`). Two levels are equivalent iff they have the same `c`
and the same offsets (`leqv_iff`: take `v` large at one variable and 0
elsewhere). Only finitely many variables occur, so this is decidable.
Boxed code is compared by `ty_leq`/`tm_leq` (E11: the Static Code Lemma
gives syntactic equality up to `≡ₗ`), which is structurally decidable given
`leqv`. Soundness of the box rules is `eqtm_leq` at M.

### H4. The instance is bundled

As in logrel-coq, the generic relations carry declarative well-formedness
beside the algorithmic derivation:

- `geq_ty` := `ac_ty` ∧ `⊢ Γ` ∧ both types well-formed;
- `geq_tm` := `ac_tm` ∧ both terms typed at `T`;
- `gne_ty` := `ac_tyne` ∧ both types well-formed;
- `gne_tm t t' T` := `∃ T'`, `ac_tmne t t' ▷ T'` ∧ `T ≅ T'` declaratively ∧
  both typed at `T`.

The last is the paper's "hide a syntactic equivalence judgment inside"
(08:195). It removes the left bias of inference, which makes symmetry,
transitivity and type conversion provable (08:199).

### H5. The recursor neutrals

The algorithm compares the motives, the thirteen branches, `l`, `Δ` (and
`T`) and the scrutinees (`ac_tmnee`, or `tm_leq` for boxed global variables).
It never uses a declarative premise. The interface's declarative motive
instance equation (E10) is a premise of the law, so the bundled instance
has it anyway.

### H6. Soundness through normalization

The algorithm uses untyped reduction, and soundness needs its equation.
For a well-typed input, normalization (`decl_whnf_normalization_*`,
`declM_whnf_normalization_*`) gives a typed reduction to some whnf, and
untyped reduction to whnf is deterministic (`reds_whnf_det`), so it is
the algorithm's whnf. Soundness is proved after the declarative
consequences, which the order of the proofs allows: soundness is only
needed by the algorithmic instance.

### H7. Typing inversion and neutral type uniqueness

The paper's neutral soundness uses that "ν and ν′ are well-typed so the
type annotations must be equivalent" (06:589). This needs typing
inversion for every head (`var`, `gvar`, `natrec`, `app`, `letbox`, the
recursors, `uapp`, `capp`, `tapp`). It also needs neutral type
uniqueness: a whne term's types are equal, at equivalent levels. The only
generic typing rules are `wf_conv` and `wf_lconv`, so inversion is by
induction on typing. Inversion is new metatheory (`Typing/Inversion.v`),
proved before soundness.

### H8. What soundness needs beyond inversion

Several typing rules take instance equations and right-hand typings as
premises (M3 E10, M5 G2), and the algorithm checks none of them. So
soundness must derive them:

- **Global functionality** (`declM_inst_c_eq`, `declM_inst_t_eq`):
  `T⦃Δ/g⦄ ≅ T⦃Δ'/g⦄` for `Δ ≅ Δ'`, and likewise for a type object. These
  are consequences of the FT (two-sided instance validity
  `VTyS_inst_c2`/`_t2`/`_ct2`, then escape at the identity). They show
  that the G2 premises are admissible.
- **Motive instances** (`declM_motT_eq`, `declM_mott_eq`): the E10
  equation from its ingredients. It is the motives' equation instantiated
  (`motT_eq_inst`), the levels by `≡ₗ` (`motT_leq`), the context and type
  objects by global functionality in the motive's scope, and the
  scrutinees by local functionality.
- **Global-binding conversion** (`gbind_ty`, `gbind_tm`): a judgment under
  `gext G D'` holds under `gext G D` for equal declarations (the new
  binding goes to its identity instance, and typed syntax is unchanged).
  It is needed for the right-hand bodies of `letbox` and `TΠ`.
- **Branch conversion** (todo): the right recursor's branches are typed in
  their own branch contexts (built from `MT'`). Comparing them with the
  left ones needs the branch contexts and result types to be equal. The
  entries are motive instances at fixed objects (`motT (wkb …) lv g c`).
  So they follow from the motives' equation weakened into the branch scope
  (universe `uup`, global `gup`, local `rlift`) and instantiated, which
  needs each object `c` typed in its branch scope.
- **Substitutions** (todo): `ac_sub` is pointwise, but the right entries
  are typed at `A[d']`. Their conversion to `A[d]` needs the deeper
  entries' equations first (induction on `Δ`).

### H9. Neutrals at function types: the lift, and `app` without annotations

The relation's reflection of neutrals (`LR_neutral`) uses `gne_tm_geq` at
`Π`, `CΠ`, `TΠ` types too. So the algorithmic instance must relate neutral
pairs at function types: it η-expands them (`app ν↑ … (var 0)`, `capp ν↑
(cvar 0)`, `tapp ν↑ (U₀^id)`, `uapp ν↑ ℓ⃗`). This is a *lift* lemma by
induction on the declarative relation's reducibility of the type, as in
Abel et al. (their `lift~toConv`). The bound variable is itself lifted at
the domain (the recursion), and the relation's instance at the
bound-variable world gives the codomain's reducibility.

The lift must not need self-conversion of types, which would mean
self-conversion of arbitrary terms (the arguments inside a neutral type),
i.e. completeness, a cycle. And the conversion lemma (08:94) changes the
η-expanded applications' annotations when it converts `Π A B` to `Π A₂ B₂`,
which the paper passes over. So the algorithm's `app` rule inspects no
annotations at all, levels included. The argument is compared at the domain
of the function's inferred `Π`, and the result type is that `Π`'s codomain,
as for `uapp`/`capp`/`tapp`. Soundness recovers the annotations' equalities
from `Π` injectivity. For that, `S_ne` relates the two sides at independent
levels, and a type's level is unique up to equivalence (`ty_lvl_uniq`).
`capp`/`tapp` compare their arguments (the lift uses `cvar 0`, and `U₀^id`
whose identity substitution is lifted entrywise). `uapp` compares levels
only.

## Order of the proofs

1. **Levels** (`Syntax/LevelDec.v`): `leqv`, `lequiv`, `ty_leq`, `tm_leq`,
   `ctx_leq`, `lsub_leq` decidable.
2. **Judgments** (`Typing/Algorithmic.v`), **typing inversion and
   neutral type uniqueness** (`Typing/Inversion.v`), **soundness**
   (`Validity/AlgSound.v`): algorithmic ⇒ declarative, for well-typed
   inputs.
3. **Structural properties**: weakening (local, global, universe
   substitution), `≡ₗ` closure, closure under reduction (for `geq_*_exp`
   and the extensionality laws), whnf ⇒ general.
4. **Conversion lemma and PER** (08:94–229), using the declarative
   consequences: injectivity of every type former, discrimination, whnf
   determinism (`tyred_whnf_det`, `tmred_whnf_det`).
5. **The lift and the instances** (`AlgInstance.v`): the lift of neutrals
   (H9), then `GenericEqLaws` at D and M and `GenericEqM`. Completeness
   follows by `fundamental`/`fundamentalM` with the algorithmic pair and
   escape.
6. **Decidability** (08:236–372), by induction on one reflexive derivation
   and inversion of the other. The final theorem decides declarative
   equality of two well-typed types or terms.

## Status

- Step 1 done (`LevelDec.v`).
- Step 2 in progress: the judgments (`Algorithmic.v`) and typing inversion
  (`Inversion.v`, with `lvl_eq`: equal or equivalent levels) are done.
  Of the H8 prerequisites, global functionality, the motive-instance
  equations, global-binding conversion, branch conversion and the
  substitution induction are done (`DeclConsequences.v`, `RecEq.v`,
  `AlgPrereq.v`), as are the typed normalization forms (`decl_whnf_tyred`
  etc.).
- Step 2 done: soundness (`AlgSound.v`, `ac_sound_all`, closed under the
  global context). The `app` rule compares no type annotations (H9).
