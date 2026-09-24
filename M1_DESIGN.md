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
  weakenings only, packaged behind an abstract weakening type so that adding
  θ/γ extends the type rather than the relation's definition.
- `UΠ` / level binders and ω's semantics (checked in the universe spike).
- The algorithmic instance and checkers.
- Layers C and V in the fundamental theorem: M1 proves it for the computing
  layers `i ∈ {D, M}`. MLTT derivations at those layers never leave the layer.

## Module plan (logrel-coq counterpart in brackets)

1. `Syntax/`: `Level` (syntax, evaluation, `≈`, `<`), `Term` (spike + Tarski),
   `Subst` (the spike's laws), `Weakening` (well-formed renamings),
   `NormalForms` (whnf / whne for types and terms), `Reduction` (untyped
   weak-head reduction). [`Syntax/*`, `AutoSubst/*`]
2. `Typing/`: `Declarative` (the judgments, `Prop`), `Generic` (the paper's
   four generic equivalences plus the laws of §7.1), `DeclarativeProperties`
   (weakening, substitution, typed reduction), `DeclarativeInstance`.
   [`DeclarativeTyping`, `GenericTyping`, `TypingProperties/*`,
   `DeclarativeInstance`]
3. `LogRel/`: `Definition` (one file per case: Nat, U, Π, neutral, level
   conversion), then Escape, Reflexivity, Irrelevance, Symmetry, Transitivity,
   Weakening, Neutral, Reduction, Induction. [`LogicalRelation/*`]
4. `Validity/` and `Fundamental`. [`Validity/*`, `Fundamental`]
5. `Consequences`: normalization, canonicity, Π/U injectivity.
   [`LogRelConsequences`]

## Process

- Green build at every checkpoint; commit per module.
- Proofs use named hypotheses and shape-matching, not positional selectors
  (inversion naming shifts whenever a constructor is added).
- No global hint-DB search in hot proofs. Build time is tracked per module.
