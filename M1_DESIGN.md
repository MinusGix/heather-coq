# Milestone 1: the MLTT core, normalization through the fundamental theorem

Goal: DeLaM's MLTT fragment (ch. 4 §"Typing and Equivalence Judgments" and
the MLTT computation rules) with a `Prop`-valued Kripke logical relation
(ch. 7 §"Kripke Logical Relations for MLTT", j = prog), proved in
logrel-coq's architecture, up to the fundamental theorem and its immediate
consequences (normalization, canonicity, injectivity of type constructors).

M1 must be in the **final shape**: later milestones add constructors and
rules, not new judgment parameters.

## Fixed now, to avoid a later big-bang

| Choice | M1 decision | Why now |
|---|---|---|
| Judgment shape | `G ; Γ ⊢[i] t : T @ l`. `G` bundles the universe context `L` and the global context `Ψ`, and is unchanged by every MLTT rule. | The paper's judgments carry all four. Adding parameters later touches every file (McTT's S2b experience). |
| Layers | Full `V < C < D < M` with `typeof`. MLTT rules gated as in the paper: V only for variables and conversion; computation (β/η) only at D and M. | Same. |
| Tarski | Separate `ty` / `tm` syntax, `El l t`, type codes in `tm`. | DeLaM is Tarski. Russell was McTT's root problem for `bc_gvar`. |
| Level-annotated judgments | `@ l` on every judgment, level-conversion rule, `Π^{l,l'}`, `λ^{l,l'} x:S.t`, and `app` carrying `l, l', S, T` as in the paper. | Annotations are sub-structure the code-recursion principle needs later. Adding them is a constructor-arity change everywhere. |
| Levels | Syntax `ℓ \| 0 \| 1+l \| l ⊔ l' \| ω`, de Bruijn level variables. Well-formedness means variables < \|L\| and no ω. **Equivalence is semantic: equal under every valuation.** | See below. |
| Global context | `Ψ` is present and syntactically complete (`g : Ctx`, `U : (Δ ⊢ᵢ @l)`, `u : (Δ ⊢ᵢ T @l)`), but M1 only *uses* `g : Ctx`, for contexts ending in `g`. `u^δ`/`U^δ` are in the syntax and have no typing rules yet. | The logical relation's context case and neutral laws already mention them. |
| Syntax | The `spike/Syntax.v` design, extended with the Tarski split and a level sort. Modal formers (`□`, `box`, `letbox`, `CΠ`, `TΠ`, code recursors) arrive later as *additive* constructors. | Tests the spike's "adding constructors is cheap" claim when it matters. |

### Level equivalence

The paper axiomatises `≈` as an idempotent commutative monoid with successor
laws, following Bezem et al., and notes it is decidable. M1 *defines* `l ≈ l'`
as equality of evaluations under all valuations of the level variables, and
the order by the same means. This is the intended model. It makes every
algebraic rule a lemma, keeps typing proofs free of level algebra, and gives
the logical relation a well-founded measure: evaluation with all variables at
0. A decision procedure (normal forms) is only needed by the checker, a later
milestone.

## Deliberately NOT in M1

- Kripke quantification over *global* and *universe* weakenings. The paper's
  weakening triple is ψ = (θ, γ, τ). M1's relation is Kripke in local
  weakenings only: renamings `r` with `wkr r Δ Γ` (`Typing/Properties.v`).
  Adding θ/γ changes the Kripke quantifier in `LRpi`/`PiRel` and the
  weakening lemmas, not the other cases.
- `UΠ` / level binders and ω's semantics (checked in the universe spike).
- The algorithmic instance and checkers.
- Layers C and V in the fundamental theorem: M1 proves it for the computing
  layers `i ∈ {D, M}`. MLTT derivations at those layers never leave the layer.

## Module plan (logrel-coq counterpart in brackets)

1. `Syntax/`: `Level` (syntax, evaluation, `≈`, `<`), `Term` (spike + Tarski),
   `Subst` (the spike's laws), `NormalForms` (whnf / whne for types and
   terms), `Reduction` (untyped weak-head reduction), `Commute`
   (per-constructor push equations and commutation lemmas), `Weakening`
   (order-preserving embeddings). [`Syntax/*`, `AutoSubst/*`]
2. `Typing/`: `Context` (layers, `gctx`, lookup), `Declarative` (the
   judgments, `Prop`), `Properties` (context extraction, weakening),
   `TypedRed`, `Generic` (the paper's four generic equivalences plus the
   laws of §7.1), then `DeclInstance`.
   [`DeclarativeTyping`, `GenericTyping`, `TypingProperties/*`,
   `DeclarativeInstance`]
3. `LogRel/`: `Def` (all cases in one inductive), `Escape`, `Basics`
   (stages, level conversion), then Irrelevance, Symmetry, Transitivity,
   Weakening, Neutral, Reduction. [`LogicalRelation/*`]
3. `Validity/` and `Fundamental`. [`Validity/*`, `Fundamental`]
5. `Consequences`: normalization, canonicity, Π/U injectivity.
   [`LogRelConsequences`]

## Process

- Green build at every checkpoint; commit per module.
- Proofs use named hypotheses and shape-matching, not positional selectors
  (inversion naming shifts whenever a constructor is added).
- No global hint-DB search in hot proofs. Build time is tracked per module.

## Deviations from the paper (all admissible or harmless)

- **Level equivalence is semantic** (see above).
- **Reduction ignores annotations** (`Syntax/Reduction.v`). The paper's
  redexes repeat annotations (`El (l⊔l') (Π^{l,l'} …)`,
  `app (λ^{l,l'} x:S. t) l l' S …`). Typing fixes them only up to `≈` and
  conversion, so syntactic matching would leave well-typed redexes stuck.
- **Typed reduction includes its equation** (`Typing/TypedRed.v`), as in
  logrel-coq: `[T ⤳* W]` = source typed, untyped reduction, and `T ≅ W`.
  The paper uses typing plus untyped reduction and proves soundness via
  preservation. Its β case silently needs Π-injectivity, which only comes
  from the logical relation.
- **Explicit reflexivity rules** and some extra well-formedness premises on
  congruences (as in logrel-coq).
- **The logical relation is staged by the level measure** (`LogRel/Def.v`).
  Π relates its domain at a level not strictly below its own, so levels
  can't be the recursion index. Stage `n` is one inductive over all levels,
  and only the universe case refers to earlier stages. `LogRel l` uses stage
  `lmeasure l`; `cumul_up`/`cumul_down` relate stages. Level equivalences are
  folded into each case, so the paper's level-conversion case is a lemma
  (`LR_lconv`).
- **Term relations depend on both sides' types** (the paper's symmetric
  presentation: `NeRel V V'`, `PiRel … A B A' B'`, duplicated premises).
  Consequently the relation is determined up to `⇔` only for a fixed pair
  `(T, T')`. Irrelevance (changing the right-hand type) must go through
  conversion, not syntactic equality.

## Status (2026-09-24)

About 2.2k lines, 16 files, **no admits, no axioms**. Every proved theorem
prints "Closed under the global context". The slowest file
(`Typing/Properties.v`) takes 3.7 s.

| File | Contents |
|---|---|
| `Syntax/Level.v` | levels, semantic `≈`/`<`, algebraic rules as lemmas, measure |
| `Syntax/Term.v` | Tarski `ty`/`tm`, `ctx`, `lsub`; local renaming and substitution; `lsingle`, `lsingle2`, `lsucc` |
| `Syntax/Subst.v` | the substitution algebra (spike laws for three sorts) |
| `Syntax/NormalForms.v`, `Reduction.v` | whnf/whne; annotation-agnostic weak-head reduction, determinacy, renaming stability |
| `Syntax/Commute.v` | `push_ren`/`push_subst` constructor equations; commutations for single substitutions; renaming outputs are normal |
| `Syntax/Weakening.v` | OPE data `wk`, `wk_wf`, composition |
| `Typing/Context.v` | layers + `typeof`/`compt`, `gdecl`/`gctx`, `in_ctx` |
| `Typing/Declarative.v` | the six mutual judgments with layer gating; `typing_mut` scheme |
| `Typing/Properties.v` | `ctx_extract` (all layers); `wkr` renaming-weakenings; `weakening_r` for `typeof i = i` |
| `Typing/TypedRed.v` | `tyred`/`tmred`, refl/trans/conv/lconv, weakening, whnf determinacy |
| `Typing/Generic.v` | `GenericEq` (fixed computing layer) + `GenericEqLaws` |
| `Typing/DeclInstance.v` | `DeclEq i Hi` / `DeclEqLaws`: the declarative instance at a computing layer `i` (neutral = both `whne` + `≅`) |
| `LogRel/Def.v` | `NatRel`/`NatNf`, `URel`, `NeRel`, `PiRel`, staged `LR`, `LogRel` |
| `LogRel/Escape.v` | `escape_ty`, `escape_tm`; conversion helpers |
| `LogRel/Basics.v` | `cumul_up`, `cumul_down`, `LogRel_stage`, `LR_lconv` |

## Next steps (in order)

1. **Irrelevance**: for a fixed `(T, T')`, two derivations give `⇔`
   relations. This is the crux spike's `LRN_det` (whnf determinacy of typed
   reduction + shape discrimination). Then the right-hand-type change, via
   conversion. `canon`/packs (crux spike) are needed where a `Type`-level
   pack must be built from a `Prop` fact, notably decoding universe terms.
   That will add propext + funext (the spike's only axioms).
2. Symmetry, transitivity, weakening of the relation (`wkr`), neutral
   reflection (variables and neutrals are related), closure under typed
   anti-reduction.
3. `Validity/` (contexts as lists of related types stable under
   substitution, logrel-coq style), per-former introduction lemmas,
   `Fundamental`. The per-former files are independent and could run as
   parallel agents if the user opts into a workflow.
4. Consequences: normalization (typed reduction to whnf), canonicity for
   `Nat`, injectivity of Π and U.

## Proof-engineering gotchas (learned the hard way)

- `constructor` on a declarative equality goal happily applies `eqty_sym`
  / `eqtm_sym` (always unifiable). Apply the intended rule by name.
- **Never `cbn` the mutual substitution fixpoints.** It exposes raw `fix`
  bodies. Use `push_ren`/`push_subst` (rewriting with per-constructor
  equations in notation form), then the commutation lemmas (`wk_rewrite`
  in `Typing/Properties.v`).
- Notation-form (`x⟨r⟩`, `x[d]`) and raw (`ren_ty x r`) forms are
  convertible but not syntactically equal. State lemmas in notation form;
  `fold_subst` folds back if raw forms appear.
- Annotate the sort in lemma statements (`(T : ty)`): typeclass resolution
  otherwise picks an arbitrary instance.
- Weakening proofs quantify over renamings satisfying `wkr`, not `wk` data:
  `eauto` cannot invert `wk_ren ?ρ = rlift …`.
- `repeat split` also splits single-constructor `Prop` records (`tyred`,
  `tmred`). Use explicit `conj` chains.
- `eauto` does not unfold definitions like `reds`; unfold first.
- Apply `LRU`/`LRpi` with explicit level arguments; otherwise levels not in
  the conclusion stay as evars.
- `Definition` cannot be a module or section name.
- Induction on the mutual judgments leaves hypotheses named `H`, `H0`, ….
  Select IHs by shape (`match goal with IH : _ |- LR … => eapply IH`), never
  by number.
- Per-case constructor search (`wk_step` in `Typing/Properties.v`, trying
  each constructor under `solve`) is robust and fast. Use it instead of
  `econstructor`, which commits to the first unifying constructor.
