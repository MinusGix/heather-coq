# DeLaM formalization

A Coq formalization of DeLaM (Hu & Pientka, *A Dependent Layered Modal Type
Theory for Meta-programming*), following the paper's own normalization proof:
a Kripke logical relation over reduction with a generic equivalence
instantiated twice (Abel, Öhman & Vezzosi 2017), in the architecture of
[logrel-coq](https://github.com/CoqHott/logrel-coq), made `Prop`-valued so
the universe hierarchy and level polymorphism fit (see
`../logrel-coq-spike/SPIKE_UNIVERSES.md`).

Status: **Milestones 1 (MLTT core) and 2 (modal core) complete.** M2 has:
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

Milestone 3 (universe substitutions and the code recursors) is also
complete:
- universe renaming and substitution, and the universe substitution lemma;
- validity quantified over universe substitutions;
- the recursors `elim_Typ`/`elim_Trm`, with their schematic β rules and
  the neutral recursion laws;
- the recursion lemmas and the fundamental theorem at M with the
  recursors. The consequences at M above still hold with the recursors
  included.

Milestone 4 (universe polymorphism: `UΠ`, `Λ`, `$` and the level ω) is
complete; see `M4_DESIGN.md`:
- the n-ary level binder, its β and η rules, and the typing metatheory;
- the relation at ω, a top tier over the finite relation;
- the fundamental theorem at M, with a finite half and an ω half;
- consequences at ω: normalization, injectivity of `UΠ` (bodies
  included), and discrimination of `UΠ` against the other type formers.

Milestone 5 (the meta-functions `CΠ` and `TΠ`: abstraction over local
contexts and over layer-P types) is complete; see `M5_DESIGN.md`:
- the syntax, the sixteen typing rules (β and η included) and the typing
  metatheory;
- two new cases of the relation at `j = M`, with every property;
- the semantic rules and the fundamental theorem at M;
- consequences: normalization, injectivity of `CΠ`/`TΠ` (bodies
  included), and discrimination against the other type formers.

Milestone 6 (algorithmic convertibility) is complete; see `M6_DESIGN.md`:
- the convertibility-checking judgments and their soundness;
- their structural properties, the conversion lemma, symmetry and
  transitivity;
- the lift of neutrals and the algorithmic instance of the generic
  equivalence, hence completeness through the fundamental theorems;
- decidability of algorithmic and of declarative equality of well-typed
  types and terms at D and M.

Milestone 7 (strengthening the base) is complete; see `M7_DESIGN.md`:
consistency, the paper's direction of Static Code, canonicity at every
type former, soundness of reduction and preservation, uniform statements
over D and M, and decidability of type checking for all terms at every
layer (the meta-level abstractions now carry their formers, a deviation
from the paper recorded in `M1_DESIGN.md`), with uniqueness of
synthesized types and the recursor rules without their scope premises.

From M8 on, the milestones check the extensions of Heather's kernel
(`HEATHER.md`):
- Milestone 8: Σ with η and `Unit` with η, as types and as code (eight
  new recursor branches), and the genericity work that made a new former
  cheap (shared generic laws, recursor branches through one lemma, rule
  lists); see `M8_DESIGN.md`.
- Milestone 9: bodied globals (definitions, δ at the computing layers);
  see `M9_DESIGN.md`, which also lists its open items. Its follow-up
  checks that closed canonicity fails at M with definitions and proves
  consistency with them at D and M.
- Milestone 10: strict equality. `sEq`, `srefl`, `sEmpty`, its
  eliminator and proof irrelevance are done. Heather removed `transp` and
  the strip rule after this formalization found that a computing
  `transp` gives UIP and that the strip's normalization is open. Since
  M10c the rules hold at every layer but V (irrelevance at D and M), with
  codes for `sEq` and `sEmpty` and six recursor branches. See
  `M10_DESIGN.md`.
- Milestone 11: the identity type. `Id`, `refl` and `J` hold at every
  layer but V, with β and no η at D and M, and closed canonicity at
  `Id`. `Id` has a code, and the code recursor has its four branches
  (`t_Id`, `t'_Id`, `t_refl`, `t_J`). See `M11_DESIGN.md`.
- Milestone 12: the empty type and binary sums. `Empty` with its
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
- Milestone 13a: well-founded trees. `W`, `sup` and the dependent
  eliminator `elim_W` hold at layers D and M, with β (whose right-hand
  side synthesizes the induction hypothesis as a λ) and no η. The term
  relation is an inductive family whose children's premise is Kripke
  quantified, and `elim_W` is valid by induction on it. Closed canonicity
  gives a `sup` at `W` (`closed_W_canonicity`). See `M13_DESIGN.md`.
- Milestone 13b: `W` has a code, its formers lift to the code layer, and
  the code recursor has its four branches (`t_W`, `t'_W`, `t_sup`,
  `t_elimW`, the last over the step telescope `a, f, ih`). See
  `M13_DESIGN.md`.
- Milestone 14a: length-indexed tuples and finite indices. `Vec^l(A; n)`
  and `Fin(n)` hold at layers D and M, the first types whose weak-head
  normal form a term chooses: `Vec` reduces to `Unit` at `0` and to `Σ`
  at a successor, `Fin` to `Empty` and to `Unit + Fin`, and both are
  neutral at a neutral length. The relation gains no case: validity
  builds it by induction on the length. Type-level preservation holds at
  `Vec^l(A; 0) ⇝ Unit^l`, at the same level. See `M14_DESIGN.md`.
- Milestone 14b: `Vec` and `Fin` have codes (`El` carries the length
  across unchanged), their formers and codes lift to the code layer, and
  the code recursor has their four branches (`t_Vec`, `t'_Vec`, `t_Fin`,
  `t'_Fin`), whose length call is a term call at `Nat`. The scopes agree
  with Heather's `rec.rs`. See `M14_DESIGN.md`.
- Milestone 15a: finitary well-founded trees. `Wf^l(A; N)`, `sup_f` and
  `elim_Wf` hold at layers D and M; a node's children are a `Vec` of
  length `N[a]`, and the eliminator's step gets one induction hypothesis
  per child as `nth` over that `Vec`. The branch telescopes are derived
  from the semantics, β holds, and validity builds the relation by
  induction on the tree (the index lemma relates `nth` at related `Fin`
  indices). See `M15_DESIGN.md`.
- Milestone 15b: `Wf`'s code `Wf^l(x : s). n : Ty l`, the lift of `Wf`,
  `sup_f`, `elim_Wf` and the code to the code layer (`nth` and the step
  telescope typed at every layer but V), and the code recursor's four
  branches 47–50, whose scopes are derived from the typing rules and agree
  with Heather's `rec.rs`. The recursive calls are derived from the scopes
  and checked against the written table. See `M15_DESIGN.md`.
- Milestone 16a: propositional truncation. `∥A∥^l`, `squash^l(A; a)` and
  `ind_∥∥` hold at layers D and M, with definitional proof irrelevance
  and a squash-headed eliminator (its result is again a squash), β at a
  `squash` of any annotations, and canonicity (a closed term at `∥A∥`
  computes to a `squash`). The relation is the probe's: each side is good
  alone, a `squash` whose payload is related to itself or a neutral
  related to itself. The algorithm compares neither scrutinees nor steps.
  See `M16_DESIGN.md`.
- Milestone 16b: `∥·∥`'s code `∥s∥ : Ty l`, the lift of `∥A∥`, `squash`
  and `ind_∥∥` to every layer but V (the computing rules, β and proof
  irrelevance stay at D and M), and the code recursor's four branches
  51–54, whose scopes agree with Heather's `rec.rs`. See `M16_DESIGN.md`.

- Milestone 17a: dependent vectors. `DVec^l(k; i. F)` (a `Vec` whose
  element type depends on the position `i : Fin k`) holds at layers D
  and M through the relation, validity and the algorithm, computing to
  `Unit` at `0` and to a `Σ` at a successor. The derived projection
  `dnth` (Heather's `IWf` design, its §3) is typed and valid (`V_dnth`),
  including the Unit-η and β conversions its typing crosses, and a
  neutral tuple projects by reduction. See `M17_DESIGN.md`.
- Milestone 17b: indexed finitary trees. `IWf^{l,li}(I; x:S. n; x. o;
  x i. c)(m)`, `sup_i` and `elim_IWf` hold at layers D and M through the
  relation, validity, the algorithm, decidability, the type checker and
  the consequences. A node sits at its output index `o[a]` and its
  children, a `DVec`, at their child indices `c[a, i]`; the eliminator's
  induction hypothesis reaches each child through `dnth`, and β fires at
  a `sup_i` at any index. Canonicity: a closed term at `IWf` computes to
  a `sup_i`. See `M17_DESIGN.md`.
- Milestone 17c: the codes of `DVec` and `IWf`, the lift of the two
  formers, `sup_i` and `elim_IWf` to every layer but V (the computing
  rules and β stay at D and M), and the code recursor's six branches
  55–60, whose scopes are derived from the layer-C rules ahead of
  Heather's `rec.rs`. See `M17_DESIGN.md`.
- Milestone 18a: Heather's indexed coinductive former `M` (`corec`,
  `out`), checked before it enters the theories, by two standalone
  probes: the rules in a Rocq model with the bridge to finite
  approximations (`probes/MCoind.v`), and the relation at `M` with the
  fundamental theorem's `corec` case (`probes/MRelProbe.v`). No kernel
  rule needed a change. See `M18_DESIGN.md`.

No admits, no axioms.

Documents:

- `HEATHER.md`: what Heather's kernel adds to DeLaM, what this repo
  checks of it, and the order of the coming milestones.
- `docs/design/`: one design doc per milestone (`M1_DESIGN.md` to
  `M18_DESIGN.md`) with its decisions, deviations from the paper and
  outcome, plus `ELIM_CONGRUENCE.md` (typed eliminator congruence) and
  `SYNTAX_SPIKE.md` (why the syntax is hand-written; the spike is
  `spike/Syntax.v`). `M1_DESIGN.md` holds the shape decisions and the
  deviations from the paper that the later milestones build on. The
  text above and the theories' comments cite these docs by file name.
- `docs/gotchas.md`: proof-engineering and build-time gotchas.
- `probes/README.md`: the standalone probes.
- `../logrel-coq-spike/SPIKE_UNIVERSES.md`: why the logical relation must
  be `Prop`-valued.

Build: `nix develop path:. --command make` (main tree), spikes via the command
in each write-up.
