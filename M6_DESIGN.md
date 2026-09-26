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

### H2. One family of judgments, indexed by the layer

The paper's nine judgments are one mutual inductive, indexed by a
computing layer `i` (`compt i`), with the paper's names:

| Coq | paper | meaning |
|---|---|---|
| `ac_ty` | `⊢ T ⇔ T'` | types (reduce, then compare whnfs) |
| `ac_tynf` | `⊢ W ⇔nf W'` | whnf types |
| `ac_tyne` | `⊢ V ⇔ne V'` | neutral types |
| `ac_ctx` | `⊢ Γ ⇔ Δ` | local contexts (pairwise) |
| `ac_tm` | `⊢ t ⇔ t' : T` | terms (reduce type and terms, compare) |
| `ac_tmnf` | `⊢ w ⇔nf w' : W` | whnf terms at a whnf type |
| `ac_tmne` | `⊢ ν ⇔ne ν' ▷ T` | neutral terms, type inferred |
| `ac_tmnee` | `⊢ ν ⇔ne ν' ▷ W` | neutral terms, inferred type reduced |
| `ac_sub` | `⊢ δ ⇔ δ' : Δ` | local substitutions (pointwise) |

The `ac_` prefix avoids the existing `conv_tm` (Escape.v). The layer-M
rules (`UΠ`, `CΠ`, `TΠ`, `CTyp`, `CTrm`, `box`, `letbox`, the recursors, the
three applications and three η checks) fix `i = lM`. The paper's remark
that at P the terms need not be P-typed (06:363) doesn't arise: `EP` is
fixed at `lD` by `GenericEqM`.

`ac_sub` mirrors `geq_lsub` (tails, deep normality, pointwise entries over
`in_ctx Δ`) instead of the paper's cons-list rules. The entries are a
strictly positive `forall n A k, in_ctx Δ n A k -> ac_tm …` premise, and Δ
is finite, so decidability is unaffected.

Inference in `ac_tmne` is syntactic, as the syntax is fully annotated
(`app`, `natrec`, `letbox`, `elim`, `capp`, `tapp`, `uapp` carry their
types or levels).

### H3. Levels up to `lequiv`, boxes up to `≡ₗ`

As in the paper, level annotations are compared with `lequiv (gL G)`.
`lequiv` is semantic (equal evaluation under every valuation), so M6 needs
a decision procedure. A level evaluates to `max(c, max_x (v x + k_x))`, and
two such normal forms agree for every valuation iff the offsets agree
per variable and the constants agree after absorption (`c` counts only when
it exceeds every `k_x`). Boxed code is compared by `ty_leq`/`tm_leq`
(E11: the Static Code Lemma gives syntactic equality up to `≡ₗ`), which is
structurally decidable given `leqv`.

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

## Order of the proofs

1. **Levels** (`Syntax/LevelDec.v`): `leqv`, `lequiv`, `ty_leq`, `tm_leq`,
   `ctx_leq`, `lsub_leq` decidable.
2. **Judgments and soundness** (`Typing/Algorithmic.v`,
   `Typing/AlgSound.v`): algorithmic ⇒ declarative, under the bundled
   well-typedness of the inputs.
3. **Structural properties**: weakening (local, global, universe
   substitution), `≡ₗ` closure, whnf ⇒ general, reflexivity of neutrals.
4. **Conversion lemma and PER** (08:94–229), using the declarative
   consequences: injectivity of every type former, discrimination, whnf
   determinism (`tyred_whnf_det`, `tmred_whnf_det`).
5. **The instances** (`AlgInstance.v`): `GenericEqLaws` at D and M,
   `GenericEqM`; completeness by `fundamental`/`fundamentalM` with the
   algorithmic pair and escape.
6. **Decidability** (08:236–372), by induction on one reflexive derivation
   and inversion of the other. The final theorem decides declarative
   equality of two well-typed types or terms.

## Status

Design only.
