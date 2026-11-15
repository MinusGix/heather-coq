# Design notes

One note per milestone, plus a few cross-cutting notes. Each records the
decisions taken, where the formalization departs from the paper or from
Heather and why, and the outcome. The theories' comments cite these notes
by bare file name (`M3_DESIGN.md E11`, `M8_DESIGN.md K5`, …), so the
names are stable.

Read `M1_DESIGN.md` first: it fixes the shape every later milestone builds
on (the judgment form, the four layers, Tarski universes, semantic level
equivalence) and lists the deviations from the paper. Then read the note
for whichever former you are about to change.

## Index

| Note | Subject | Status |
|---|---|---|
| [`M1_DESIGN.md`](M1_DESIGN.md) | The MLTT core: shape decisions, the logical relation, fundamental theorem | done |
| [`M2_DESIGN.md`](M2_DESIGN.md) | The modal core: global variables, contextual types, `box`, `letbox`, global substitutions | done |
| [`M3_DESIGN.md`](M3_DESIGN.md) | Universe substitutions and the code recursors `elim_Typ` / `elim_Trm` | done |
| [`M4_DESIGN.md`](M4_DESIGN.md) | Universe polymorphism: `UΠ`, `Λ`, `$`, the level ω | done |
| [`M5_DESIGN.md`](M5_DESIGN.md) | Meta-functions over contexts and types: `CΠ`, `TΠ` | done |
| [`M6_DESIGN.md`](M6_DESIGN.md) | Algorithmic convertibility and its decidability | done |
| [`M7_DESIGN.md`](M7_DESIGN.md) | Strengthening the base: consistency, Static Code, canonicity, type checking, the paper's own rule set | done |
| [`M8_DESIGN.md`](M8_DESIGN.md) | Σ and Unit with η; the genericity work that made a new former cheap | done |
| [`M9_DESIGN.md`](M9_DESIGN.md) | Bodied globals (definitions, δ-reduction) | done, open items listed |
| [`M10_DESIGN.md`](M10_DESIGN.md) | Strict equality `sEq`, `sEmpty`; why `transp` was removed from Heather | done |
| [`M11_DESIGN.md`](M11_DESIGN.md) | The identity type `Id`, `refl`, `J` | done |
| [`M12_DESIGN.md`](M12_DESIGN.md) | `Empty` and binary sums; Hedberg's theorem in the syntax | done |
| [`M13_DESIGN.md`](M13_DESIGN.md) | Well-founded trees `W` | done |
| [`M14_DESIGN.md`](M14_DESIGN.md) | Length-indexed `Vec` and finite indices `Fin` | done |
| [`M15_DESIGN.md`](M15_DESIGN.md) | Finitary well-founded trees `Wf`; recursor branches derived from their scopes | done |
| [`M16_DESIGN.md`](M16_DESIGN.md) | Propositional truncation `∥A∥` | done |
| [`M17_DESIGN.md`](M17_DESIGN.md) | Dependent vectors `DVec`, indexed finitary trees `IWf` | done |
| [`M18_DESIGN.md`](M18_DESIGN.md) | The indexed coinductive former `M` (`corec`, `out`) | M18a–b done, M18c (codes) waits on Heather |
| [`ELIM_CONGRUENCE.md`](ELIM_CONGRUENCE.md) | Typed eliminator congruence: which annotations conversion need not compare | done |
| [`SYNTAX_SPIKE.md`](SYNTAX_SPIKE.md) | Why the syntax is hand-written rather than generated (spike: `spike/Syntax.v`) | done |
| [`LAYER_STRUCTURE.md`](LAYER_STRUCTURE.md) | Side conditions on layer structures, by counterexample (`probes/LayerStructure.v`) | probe done |

What Heather's kernel adds to DeLaM, what this repository checks of it and
what comes next is in [`../../HEATHER.md`](../../HEATHER.md).
Proof-engineering and build-time lessons are in
[`../gotchas.md`](../gotchas.md).

## Milestones in detail

The status of each milestone, with the results it proved. The top-level
`README.md` has the one-line version.

### M1: the MLTT core, and M2: the modal core

Complete. M2 has:
- the syntax (global variables, contextual types, `box`, `letbox`);
- the declarative metatheory at every layer;
- the layered logical relation (`j ∈ {P, M}`, Kripke over global
  weakenings);
- the fundamental theorem with related global substitutions at layers
  C, P and M (`FundamentalS`, `FundamentalM`), which shows the Layering
  Restriction on the way;
- the consequences at P and M for arbitrary global contexts:
  - weak-head normalization;
  - injectivity and discrimination of type formers, including `□`;
  - canonicity for `Nat` and for contextual types.

(The paper's layer P, for programs, is `lD` in the theories.)

### M3: universe substitutions and the code recursors

Complete:
- universe renaming and substitution, and the universe substitution lemma;
- validity quantified over universe substitutions;
- the recursors `elim_Typ`/`elim_Trm`, with their schematic β rules and
  the neutral recursion laws;
- the recursion lemmas and the fundamental theorem at M with the
  recursors. The consequences at M above still hold with the recursors
  included.

### M4: universe polymorphism

`UΠ`, `Λ`, `$` and the level ω. Complete; see `M4_DESIGN.md`:
- the n-ary level binder, its β and η rules, and the typing metatheory;
- the relation at ω, a top tier over the finite relation;
- the fundamental theorem at M, with a finite half and an ω half;
- consequences at ω: normalization, injectivity of `UΠ` (bodies
  included), and discrimination of `UΠ` against the other type formers.

### M5: the meta-functions `CΠ` and `TΠ`

Abstraction over local contexts and over layer-P types. Complete; see
`M5_DESIGN.md`:
- the syntax, the sixteen typing rules (β and η included) and the typing
  metatheory;
- two new cases of the relation at `j = M`, with every property;
- the semantic rules and the fundamental theorem at M;
- consequences: normalization, injectivity of `CΠ`/`TΠ` (bodies
  included), and discrimination against the other type formers.

### M6: algorithmic convertibility

Complete; see `M6_DESIGN.md`:
- the convertibility-checking judgments and their soundness;
- their structural properties, the conversion lemma, symmetry and
  transitivity;
- the lift of neutrals and the algorithmic instance of the generic
  equivalence, hence completeness through the fundamental theorems;
- decidability of algorithmic and of declarative equality of well-typed
  types and terms at D and M.

### M7: strengthening the base

Complete; see `M7_DESIGN.md`: consistency, the paper's direction of
Static Code, canonicity at every type former, soundness of reduction and
preservation, uniform statements over D and M, and decidability of type
checking for all terms at every layer (the meta-level abstractions now
carry their formers, a deviation from the paper recorded in
`M1_DESIGN.md`), with uniqueness of synthesized types and the recursor
rules without their scope premises.

### From M8 on: Heather's extensions

From M8 on, the milestones check the extensions of Heather's kernel
(`HEATHER.md`).

- **M8**: Σ with η and `Unit` with η, as types and as code (eight
  new recursor branches), and the genericity work that made a new former
  cheap (shared generic laws, recursor branches through one lemma, rule
  lists); see `M8_DESIGN.md`.
- **M9**: bodied globals (definitions, δ at the computing layers);
  see `M9_DESIGN.md`, which also lists its open items. Its follow-up
  checks that closed canonicity fails at M with definitions and proves
  consistency with them at D and M.
- **M10**: strict equality. `sEq`, `srefl`, `sEmpty`, its
  eliminator and proof irrelevance are done. Heather removed `transp` and
  the strip rule after this formalization found that a computing
  `transp` gives UIP and that the strip's normalization is open. Since
  M10c the rules hold at every layer but V (irrelevance at D and M), with
  codes for `sEq` and `sEmpty` and six recursor branches. See
  `M10_DESIGN.md`.
- **M11**: the identity type. `Id`, `refl` and `J` hold at every
  layer but V, with β and no η at D and M, and closed canonicity at
  `Id`. `Id` has a code, and the code recursor has its four branches
  (`t_Id`, `t'_Id`, `t_refl`, `t_J`). See `M11_DESIGN.md`.
- **M12**: the empty type and binary sums. `Empty` with its
  eliminator, and `+` with `inl`, `inr` and `case`, hold at every layer
  but V, with β and no η at D and M, except that `Empty` has η as proof
  irrelevance at D and M (added 2026-10-06). Closed canonicity gives no
  closed term of `Empty` and the disjunction property at `+`. Both have codes,
  and the code recursor has their eight branches (`t_Empty`, `t'_Empty`,
  `t_elimE`, `t_+`, `t'_+`, `t_inl`, `t_inr`, `t_case`). With them the
  no-UIP model's `UIP₀` is stated at `⌜Bool⌝` as the model writes it, and
  Hedberg's theorem is proved in the syntax: a schema, a closed internal
  statement, and UIP at `Bool` and at `Nat` (`Validity/Hedberg.v`). See
  `M12_DESIGN.md`.
- **M13a**: well-founded trees. `W`, `sup` and the dependent
  eliminator `elim_W` hold at layers D and M, with β (whose right-hand
  side synthesizes the induction hypothesis as a λ) and no η. The term
  relation is an inductive family whose children's premise is Kripke
  quantified, and `elim_W` is valid by induction on it. Closed canonicity
  gives a `sup` at `W` (`closed_W_canonicity`). See `M13_DESIGN.md`.
- **M13b**: `W` has a code, its formers lift to the code layer, and
  the code recursor has its four branches (`t_W`, `t'_W`, `t_sup`,
  `t_elimW`, the last over the step telescope `a, f, ih`). See
  `M13_DESIGN.md`.
- **M14a**: length-indexed tuples and finite indices. `Vec^l(A; n)`
  and `Fin(n)` hold at layers D and M, the first types whose weak-head
  normal form a term chooses: `Vec` reduces to `Unit` at `0` and to `Σ`
  at a successor, `Fin` to `Empty` and to `Unit + Fin`, and both are
  neutral at a neutral length. The relation gains no case: validity
  builds it by induction on the length. Type-level preservation holds at
  `Vec^l(A; 0) ⇝ Unit^l`, at the same level. See `M14_DESIGN.md`.
- **M14b**: `Vec` and `Fin` have codes (`El` carries the length
  across unchanged), their formers and codes lift to the code layer, and
  the code recursor has their four branches (`t_Vec`, `t'_Vec`, `t_Fin`,
  `t'_Fin`), whose length call is a term call at `Nat`. The scopes agree
  with Heather's `rec.rs`. See `M14_DESIGN.md`.
- **M15a**: finitary well-founded trees. `Wf^l(A; N)`, `sup_f` and
  `elim_Wf` hold at layers D and M; a node's children are a `Vec` of
  length `N[a]`, and the eliminator's step gets one induction hypothesis
  per child as `nth` over that `Vec`. The branch telescopes are derived
  from the semantics, β holds, and validity builds the relation by
  induction on the tree (the index lemma relates `nth` at related `Fin`
  indices). See `M15_DESIGN.md`.
- **M15b**: `Wf`'s code `Wf^l(x : s). n : Ty l`, the lift of `Wf`,
  `sup_f`, `elim_Wf` and the code to the code layer (`nth` and the step
  telescope typed at every layer but V), and the code recursor's four
  branches 47–50, whose scopes are derived from the typing rules and agree
  with Heather's `rec.rs`. The recursive calls are derived from the scopes
  and checked against the written table. See `M15_DESIGN.md`.
- **M16a**: propositional truncation. `∥A∥^l`, `squash^l(A; a)` and
  `ind_∥∥` hold at layers D and M, with definitional proof irrelevance
  and a squash-headed eliminator (its result is again a squash), β at a
  `squash` of any annotations, and canonicity (a closed term at `∥A∥`
  computes to a `squash`). The relation is the probe's: each side is good
  alone, a `squash` whose payload is related to itself or a neutral
  related to itself. The algorithm compares neither scrutinees nor steps.
  See `M16_DESIGN.md`.
- **M16b**: `∥·∥`'s code `∥s∥ : Ty l`, the lift of `∥A∥`, `squash`
  and `ind_∥∥` to every layer but V (the computing rules, β and proof
  irrelevance stay at D and M), and the code recursor's four branches
  51–54, whose scopes agree with Heather's `rec.rs`. See `M16_DESIGN.md`.
- **M17a**: dependent vectors. `DVec^l(k; i. F)` (a `Vec` whose
  element type depends on the position `i : Fin k`) holds at layers D
  and M through the relation, validity and the algorithm, computing to
  `Unit` at `0` and to a `Σ` at a successor. The derived projection
  `dnth` (Heather's `IWf` design, its §3) is typed and valid (`V_dnth`),
  including the Unit-η and β conversions its typing crosses, and a
  neutral tuple projects by reduction. See `M17_DESIGN.md`.
- **M17b**: indexed finitary trees. `IWf^{l,li}(I; x:S. n; x. o;
  x i. c)(m)`, `sup_i` and `elim_IWf` hold at layers D and M through the
  relation, validity, the algorithm, decidability, the type checker and
  the consequences. A node sits at its output index `o[a]` and its
  children, a `DVec`, at their child indices `c[a, i]`; the eliminator's
  induction hypothesis reaches each child through `dnth`, and β fires at
  a `sup_i` at any index. Canonicity: a closed term at `IWf` computes to
  a `sup_i`. See `M17_DESIGN.md`.
- **M17c**: the codes of `DVec` and `IWf`, the lift of the two
  formers, `sup_i` and `elim_IWf` to every layer but V (the computing
  rules and β stay at D and M), and the code recursor's six branches
  55–60, whose scopes are derived from the layer-C rules ahead of
  Heather's `rec.rs`. See `M17_DESIGN.md`.
- **M18a**: Heather's indexed coinductive former `M` (`corec`,
  `out`), checked before it enters the theories, by two standalone
  probes: the rules in a Rocq model with the bridge to finite
  approximations (`probes/MCoind.v`), and the relation at `M` with the
  fundamental theorem's `corec` case (`probes/MRelProbe.v`). No kernel
  rule needed a change. See `M18_DESIGN.md`.
- **M18b**: the indexed coinductive former in-tree.
  `M^{l,l',li}(I; S; P; o)(j)`, `corec` and `out` hold at layers D and M
  through the relation (`LRm`: the ω-intersection of the depth
  approximations `MRn`, with the generic clause at every depth),
  validity (`corec`'s by induction on the depth), the fundamental
  theorem, the algorithm, decidability, the type checker and the
  consequences. β fires only under `out`, at a `corec` of any
  annotations. A closed term at `M` computes to a `corec`. No kernel rule
  needed a change. See `M18_DESIGN.md`.
- **M18c** (planned): `M`'s codes and recursor branches, once Heather's
  codes round has them.

No admits, no axioms (`make assumptions` checks it; see
`checks/Assumptions.v`).
