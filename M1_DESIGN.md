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
  Irrelevance (`LR_irrel`: same left type, any right types) goes through
  conversion.
- **Saturation** (`LogRel/Def.v`). Every case accepts any term relation
  `R` with `releq R canonical`. Symmetry must build the Π derivation with
  the flipped domain relation, but the induction hypothesis only yields
  `∃R', … ∧ R' ⇔ flip domR`, and a `Prop` existential can't be turned into
  a function. Saturation makes `flip domR` itself acceptable
  (`LR_releq`). This replaces the crux spike's canon/packs (propext +
  funext): **the logical relation's metatheory is axiom-free so far.**
- **The universe case is indexed by the level read off the left type's
  normal form** (`URel rec G Γ l1` for `T ⤳* U l1`), so two derivations for
  the same left type have literally the same relation.
- **`URel` quantifies over equivalent `El` annotations**: decodings
  `El la w` / `El lb w'` are related for all `la, lb ≈ l`. This is the same
  device as the paper's application annotations in the Π case. It makes
  symmetry and level conversion of the universe case go through, since
  otherwise they need an "annotation irrelevance" for `El`. The fundamental
  theorem can provide it, because `El` reduction ignores annotations.
- **`LRpi` records the generic equality of domains and codomains**
  (`A ≈ A'`, and `B ≈ B'` under the left domain) instead of the whole Π
  types (derivable by `geq_ty_pi`). Needed by irrelevance and
  transitivity, which otherwise need Π-injectivity of the generic
  equivalence.
- **Generic laws include context conversion** of the last entry (with a
  level change), as the paper uses in right irrelevance. The declarative
  instance gets it from stability.
- **Syntactic metatheory before the relation** (as in the paper's ch. 5,
  unlike logrel-coq): substitution, stability, functionality and
  presupposition are proved directly for the declarative system, for layers
  with `typeof i = i`. Typed local substitutions are defined extensionally,
  by lookups, and carry `LK nftm d` (normal forms of the entries) for the
  identity laws.

## Status (2026-09-24, session 2)

About 4.5k lines, 25 files, **no admits, no axioms** (every proved theorem
prints "Closed under the global context"). The full build takes about 20 s.
The slowest files are `Typing/Functionality.v` (3.7 s),
`Typing/Properties.v` (3.7 s) and `Typing/Substitution.v` (about 3 s).

| File | Contents |
|---|---|
| `Syntax/Level.v` | levels, semantic `≈`/`<`, algebraic rules as lemmas, measure |
| `Syntax/Term.v` | Tarski `ty`/`tm`, `ctx`, `lsub`; local renaming and substitution; `lsingle`, `lsingle2`, `lsucc` |
| `Syntax/Subst.v` | the substitution algebra (spike laws for three sorts) |
| `Syntax/NormalForms.v`, `Reduction.v` | whnf/whne; annotation-agnostic weak-head reduction, determinacy, renaming stability |
| `Syntax/Commute.v` | `push_ren`/`push_subst` constructor equations; commutations for single substitutions; renaming outputs are normal |
| `Syntax/SubstCommute.v` | substitution preserves normal forms; an arbitrary substitution commutes with the rules' own substitutions |
| `Syntax/Weakening.v` | OPE data `wk`, `wk_wf`, composition |
| `Typing/Context.v` | layers + `typeof`/`compt`, `gdecl`/`gctx`, `in_ctx` |
| `Typing/Declarative.v` | the six mutual judgments with layer gating; `typing_mut` scheme |
| `Typing/Properties.v` | `ctx_extract` (all layers); `wkr` renaming-weakenings; `weakening_r` for `typeof i = i` |
| `Typing/Substitution.v` | typed terms are normal (`typed_nf`); typed local substitutions `[Δ ⊢ d : Γ]` by lookups; `substitution` |
| `Typing/Functionality.v` | single substitutions; stability (`stab_*`, last entry, with level change); `functionality` |
| `Typing/Presupposition.v` | `presupposition` + named corollaries (`wf_tm_ty`, `eqty_wf_l/r`, `eqtm_wf_l/r/ty`) |
| `Typing/TypedRed.v` | `tyred`/`tmred`, refl/trans/conv/lconv, weakening, whnf determinacy |
| `Typing/Generic.v` | `GenericEq` (fixed computing layer) + `GenericEqLaws` (incl. context conversion) |
| `Typing/DeclInstance.v` | `DeclEq i Hi` / `DeclEqLaws`: the declarative instance at a computing layer `i` |
| `LogRel/Def.v` | `releq`, `NatRel`/`NatNf`, `URel`, `NeRel`, `PiRel`, staged saturated `LR`, `LogRel` |
| `LogRel/Escape.v` | `escape_ty`, `escape_tm`; conversion helpers |
| `LogRel/Basics.v` | `cumul_up`, `cumul_down`, `LogRel_stage`, `LR_releq`, `LR_lconv` |
| `LogRel/Irrelevance.v` | `LR_irrel` (right irrelevance, as `releq`); inversion by the left normal form (`LR_inv_nat/U/ne/pi`) |
| `LogRel/Symmetry.v` | `LR_sym` (`flipR`), by strong induction on the stage |
| `LogRel/Transitivity.v` | `LR_irrel_left`, `LR_trans`, `LR_refl_l/r`, `LR_tm_refl_l` |

## Next steps (in order)

1. Weakening of the relation (`wkr`), neutral reflection (variables and
   neutrals are related), closure under typed anti-reduction. Paper ch. 7
   §"Properties for Logical Relations When j = prog".
2. `Validity/`: contexts as lists of related types stable under
   substitution (logrel-coq style), per-former introduction lemmas,
   `Fundamental`. The per-former files are independent and could run as
   parallel agents if the user opts into a workflow. The El/U cases must
   produce the annotation-quantified `URel`.
3. Consequences: normalization (typed reduction to whnf), canonicity for
   `Nat`, injectivity of Π and U.

## Proof-engineering gotchas (learned the hard way)

- `constructor` on a declarative equality goal happily applies `eqty_sym`
  / `eqtm_sym` (always unifiable). Apply the intended rule by name. Since
  saturation, the same holds for `LR`: every constructor's conclusion is
  `LR … R` with `R` a variable, so `econstructor` always picks `LRnat`.
- Section-local lemmas with explicit section hypotheses (`Hi`, `Hv`) keep
  only the ones they use, so their arity varies. Pass arguments by name
  (`(lemma (x := …))`) or with `eapply … ; eassumption`.
- `match goal with IH : _ |- _ => exact (IH …) end`: an ill-typed
  application raises an error that `match` doesn't backtrack on. Filter the
  hypothesis by shape first (`IH : _ = _ -> _`) or use `eapply`.
- A section `Context` hypothesis about the indices (e.g. `H : LR … T …`)
  blocks `destruct H` from substituting into other hypotheses. `revert`
  them first (see `LR_inv_*`).
- Avoid broad `Hint Extern` on `eq_ty (subst _ _) (subst _ _)`-like goals.
  One such hint made `Functionality.v` search for over 100 s. Prefer
  per-case manual steps with pre-asserted facts.
- Probe goals in a scratch file under the session scratchpad:
  `coqc -Q theories DeLaM file.v` inside `nix develop`, with `Show.` before
  `Admitted.`
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
